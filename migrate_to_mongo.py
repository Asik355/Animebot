import dns.resolver
dns.resolver.default_resolver = dns.resolver.Resolver(configure=False)
dns.resolver.default_resolver.nameservers = ['8.8.8.8', '1.1.1.1']


#!/usr/bin/env python3
"""
migrate_to_mongo.py - one-time import of bot_database.db + JSON registries into MongoDB Atlas.

Run it LOCALLY (where your real bot_database.db lives), with MONGO_URI set in .env or the shell:

    python migrate_to_mongo.py --dry-run          # read + transform + report, no MongoDB needed
    python migrate_to_mongo.py                    # real import (refuses if data already exists)
    python migrate_to_mongo.py --force            # re-run / overwrite by key (idempotent upserts)
    python migrate_to_mongo.py --wipe --yes       # drop migrated collections first, then import

Mapping
-------
Core tables (reshaped for the refactored bot):
    users_v2                     -> users          (_id = user_id; includes guess_* game fields)
    characters_v2                -> characters     (+ recruit_names[] and discontinued flag embedded)
    character_recruit_names_v2   -> characters.recruit_names (ordered by old id)
    discontinued_characters_v2   -> characters.discontinued/_at/_by
    collections_v2               -> collections    (one doc per copy; old id kept as legacy_id)
    favorites_v2                 -> favorites      (_id = user_id)
JSON files:
    approved_groups.json, auto_spawn_groups.json, bot_groups.json, bot_group_state.json,
    gstats_hidden_groups.json                                    -> groups (one doc per chat)
    notification_settings.json   -> notification_settings
    restrictions.json            -> restrictions
    character_spawn_cooldowns.json -> character_spawn_cooldowns (_id = character code,
                                    last_spawned_at kept verbatim as the original ISO string)
Every other SQLite table is copied 1:1 into a collection with the SAME NAME (for the later
refactor phases): AUTOINCREMENT `id` becomes `_id`, other primary keys get unique indexes,
and `counters` is seeded so new ids continue where SQLite left off.

The script is idempotent (upserts by key) and never modifies the SQLite file or JSON files.
"""

import argparse
import json
from datetime import datetime
import sqlite3
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

CORE_TABLES = {
    "users_v2", "characters_v2", "character_recruit_names_v2",
    "discontinued_characters_v2", "collections_v2", "favorites_v2",
}
SKIP_TABLES = {"sqlite_sequence"}
MIGRATED_CORE_COLLECTIONS = ["users", "characters", "collections", "favorites",
                             "groups", "notification_settings", "restrictions",
                             "character_spawn_cooldowns", "orphan_recruit_names"]


# --------------------------------------------------------------------------
# Reading
# --------------------------------------------------------------------------
def open_sqlite(path):
    if not Path(path).exists():
        sys.exit(f"SQLite file not found: {path}")
    conn = sqlite3.connect(str(path))  # this script only ever SELECTs from it
    conn.row_factory = sqlite3.Row
    return conn


def table_names(conn):
    return [r[0] for r in conn.execute(
        "SELECT name FROM sqlite_master WHERE type='table' AND name NOT LIKE 'sqlite_%' ORDER BY name")]


def read_table(conn, name):
    return [dict(r) for r in conn.execute(f'SELECT * FROM "{name}"')]


def pk_columns(conn, name):
    info = conn.execute(f'PRAGMA table_info("{name}")').fetchall()
    pks = sorted((r["pk"], r["name"]) for r in info if r["pk"] > 0)
    return [c for _, c in pks]


def read_json(path, default):
    p = Path(path)
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception as exc:
        print(f"  ! could not parse {p.name}: {exc}")
        return default


# --------------------------------------------------------------------------
# Pure transforms (no MongoDB needed - used by --dry-run too)
# --------------------------------------------------------------------------
def build_users(rows):
    docs = []
    for r in rows:
        docs.append({
            "_id": int(r["user_id"]),
            "username": r.get("username") or "",
            "first_name": r.get("first_name") or "",
            "last_name": r.get("last_name") or "",
            "coins": int(r.get("coins") or 0),
            "last_daily": r.get("last_daily"),
            "guess_day": r.get("guess_day"),
            "guess_attempts": int(r.get("guess_attempts") or 0),
            "guess_secret": r.get("guess_secret"),
            "guess_active": int(r.get("guess_active") or 0),
            "guess_reward_total": int(r.get("guess_reward_total") or 0),
        })
    return docs


def build_characters(chars, recruit_rows, discontinued_rows):
    recruit = {}
    for r in sorted(recruit_rows, key=lambda x: x["id"]):
        recruit.setdefault(str(r["character_code"]), []).append(r["recruit_name"])
    disc = {str(r["character_code"]): r for r in discontinued_rows}
    docs, orphan_recruit, orphan_disc = [], set(recruit), set(disc)
    for r in chars:
        code = str(r["code"])
        orphan_recruit.discard(code)
        orphan_disc.discard(code)
        name = r.get("name")
        doc = {
            "code": code,
            "code_int": int(code) if code.isdigit() else 0,
            "name": name,
            "name_ci": str(name).casefold() if name else None,
            "anime": r.get("anime"),
            "rarity": r.get("rarity"),
            "worth": int(r.get("worth") or 0),
            "photo_file_id": r.get("photo_file_id"),
            "recruit_names": recruit.get(code, []),
        }
        if code in disc:
            doc["discontinued"] = True
            doc["discontinued_at"] = disc[code].get("discontinued_at")
            doc["discontinued_by"] = disc[code].get("discontinued_by")
        docs.append(doc)
    return docs, sorted(orphan_recruit), sorted(orphan_disc)


def build_collections(rows):
    return [{
        "legacy_id": int(r["id"]),
        "user_id": int(r["user_id"]),
        "character_code": str(r["character_code"]),
        "caught_at": r.get("caught_at"),
    } for r in rows]


def build_favorites(rows):
    return [{"_id": int(r["user_id"]), "character_code": str(r["character_code"]), "set_at": r.get("set_at")}
            for r in rows]


def _id_list(data):
    """Accept a list of ids, or a dict {id: bool}; return {int_id: bool}."""
    out = {}
    if isinstance(data, list):
        for x in data:
            if str(x).lstrip("-").isdigit():
                out[int(x)] = True
    elif isinstance(data, dict):
        for k, v in data.items():
            if str(k).lstrip("-").isdigit():
                out[int(k)] = bool(v)
    return out


def build_groups(json_dir):
    """Merge every group-related JSON file into {chat_id: fields}."""
    groups = {}

    def touch(cid):
        return groups.setdefault(cid, {})

    approved = read_json(json_dir / "approved_groups.json", [])
    for cid in _id_list(approved or []):
        touch(cid)["approved"] = True

    auto = read_json(json_dir / "auto_spawn_groups.json", [])
    for cid in _id_list(auto or []):
        touch(cid)["auto_spawn"] = True

    hidden = read_json(json_dir / "gstats_hidden_groups.json", [])
    for cid in _id_list(hidden or []):
        touch(cid)["gstats_hidden"] = True

    state = read_json(json_dir / "bot_group_state.json", {})
    for cid, val in _id_list(state or {}).items():
        touch(cid)["bot_enabled"] = val

    info = read_json(json_dir / "bot_groups.json", {})
    if isinstance(info, dict):
        for k, v in info.items():
            if str(k).lstrip("-").isdigit() and isinstance(v, dict):
                d = touch(int(k))
                d.update({"registered": True, "title": v.get("title"),
                          "type": v.get("type"), "username": v.get("username")})

    # make absent booleans explicit so queries are uniform
    for d in groups.values():
        for flag in ("approved", "auto_spawn", "registered", "gstats_hidden"):
            d.setdefault(flag, False)
    return groups


def build_notifications(json_dir):
    data = read_json(json_dir / "notification_settings.json", {}) or {}
    users = data.get("users", {}) if isinstance(data, dict) else {}
    return [{"_id": int(k), "enabled": bool(v)} for k, v in users.items() if str(k).lstrip("-").isdigit()]


def build_restrictions(json_dir):
    data = read_json(json_dir / "restrictions.json", {}) or {}
    docs = []
    if isinstance(data, dict):
        for k, v in data.items():
            if not str(k).lstrip("-").isdigit():
                continue
            entry = dict(v) if isinstance(v, dict) else {"expiry": int(v)}
            entry["_id"] = int(k)
            docs.append(entry)
    return docs


def build_spawn_cooldowns(json_dir):
    """
    character_spawn_cooldowns.json: {character_code: "ISO timestamp of last spawn"}.
    Returns (docs, bad_entries). Timestamps are stored exactly as in the file (string), so
    nothing about the cooldown clock changes; unparseable entries are reported, not silently dropped.
    """
    data = read_json(json_dir / "character_spawn_cooldowns.json", {}) or {}
    docs, bad = [], []
    if not isinstance(data, dict):
        return docs, [f"top level is {type(data).__name__}, expected an object {{code: timestamp}}"]
    for k, v in data.items():
        code = str(k).strip()
        if not code:
            bad.append(f"empty character code (value={v!r})")
            continue
        try:
            datetime.fromisoformat(str(v))
        except Exception:
            bad.append(f"character {code}: invalid timestamp {v!r}")
            continue
        docs.append({"_id": code, "character_code": code, "last_spawned_at": str(v)})
    return docs, bad


# --------------------------------------------------------------------------
# Pre-flight validation (pure, no MongoDB needed) - runs in --dry-run AND before every real import
# --------------------------------------------------------------------------
# unique indexes that mongo_db.ensure_indexes() creates on migrated collections
UNIQUE_KEYS = {
    "group_character_spawn_v1": ["chat_id", "character_code", "day_key"],
    "event_claims_v2": ["event_id", "user_id"],
    "redeem_claims_v2": ["code", "user_id"],
    "shop_v3": ["user_id", "slot"],
    "transfer_blocks_v2": ["user_id_1", "user_id_2"],
}


def _walk_values(doc):
    for v in doc.values():
        if isinstance(v, dict):
            yield from _walk_values(v)
        elif isinstance(v, (list, tuple)):
            for x in v:
                if isinstance(x, dict):
                    yield from _walk_values(x)
                else:
                    yield x
        else:
            yield v


def validate_documents(named_docs, unique_specs):
    """
    named_docs:   {collection: [doc, ...]}
    unique_specs: {collection: [[field, ...], ...]}   (each list is one unique index)
    Returns a list of human-readable problems (empty list = every record will import cleanly).
    Checks: duplicate _id, duplicate values for each unique index, BSON-encodable values,
    integers inside the signed 64-bit range, and (when pymongo's bson is installed) a real BSON encode.
    """
    problems = []
    try:
        import bson  # shipped with pymongo
    except Exception:  # pragma: no cover
        bson = None
    for coll, docs in named_docs.items():
        seen_id = {}
        specs, _dedup = [], set()
        for sp in [["_id"]] + [list(x) for x in unique_specs.get(coll, [])]:
            if tuple(sp) not in _dedup:  # the same index can be declared twice (UNIQUE_KEYS + primary key)
                _dedup.add(tuple(sp))
                specs.append(sp)
        seen = {tuple(sp): {} for sp in specs}
        for i, d in enumerate(docs):
            for sp in specs:
                if any(f not in d or d[f] is None for f in sp):
                    continue  # partial/sparse behaviour: missing keys are not indexed
                key = tuple(d[f] for f in sp)
                if key in seen[tuple(sp)]:
                    problems.append(f"{coll}: duplicate unique key {sp}={key} (docs #{seen[tuple(sp)][key]} and #{i})")
                else:
                    seen[tuple(sp)][key] = i
            for v in _walk_values(d):
                if isinstance(v, bool) or v is None or isinstance(v, (str, float)):
                    if isinstance(v, float) and v != v:
                        problems.append(f"{coll}: NaN value in doc #{i}")
                    continue
                if isinstance(v, int) and not (-2 ** 63 <= v < 2 ** 63):
                    problems.append(f"{coll}: integer out of 64-bit range in doc #{i}: {v}")
                elif isinstance(v, bytes):
                    continue
                elif not isinstance(v, int):
                    problems.append(f"{coll}: unsupported value type {type(v).__name__} in doc #{i}")
            if bson is not None:
                try:
                    bson.encode(d)
                except Exception as exc:
                    problems.append(f"{coll}: BSON encode failed for doc #{i}: {exc}")
    return problems


# --------------------------------------------------------------------------
# Writing (MongoDB)
# --------------------------------------------------------------------------
def chunked(seq, n=1000):
    for i in range(0, len(seq), n):
        yield seq[i:i + n]


def bulk_upsert(collection, docs, key):
    """Upsert docs by `key` (a field name, or list of field names). Returns count written."""
    from pymongo import ReplaceOne
    keys = [key] if isinstance(key, str) else list(key)
    total = 0
    for batch in chunked(docs):
        ops = [ReplaceOne({k: d[k] for k in keys}, d, upsert=True) for d in batch]
        if ops:
            collection.bulk_write(ops, ordered=False)
            total += len(ops)
    return total


def migrate(args):
    conn = open_sqlite(args.db)
    json_dir = Path(args.json_dir)
    tables = table_names(conn)
    print(f"SQLite: {args.db}  ({len(tables)} tables)")
    print(f"JSON dir: {json_dir}\n")

    # ---- read + transform --------------------------------------------------
    users = build_users(read_table(conn, "users_v2")) if "users_v2" in tables else []
    recruit_rows = read_table(conn, "character_recruit_names_v2") if "character_recruit_names_v2" in tables else []
    disc_rows = read_table(conn, "discontinued_characters_v2") if "discontinued_characters_v2" in tables else []
    chars, orphan_recruit, orphan_disc = build_characters(
        read_table(conn, "characters_v2") if "characters_v2" in tables else [],
        recruit_rows,
        disc_rows,
    )
    orphan_recruit_rows = [dict(r, _id=r["id"]) for r in recruit_rows if str(r["character_code"]) in set(orphan_recruit)]
    colls = build_collections(read_table(conn, "collections_v2")) if "collections_v2" in tables else []
    favs = build_favorites(read_table(conn, "favorites_v2")) if "favorites_v2" in tables else []
    groups = build_groups(json_dir)
    notifs = build_notifications(json_dir)
    restr = build_restrictions(json_dir)
    cooldowns, cooldown_bad = build_spawn_cooldowns(json_dir)

    generic = {}
    for t in tables:
        if t in CORE_TABLES or t in SKIP_TABLES:
            continue
        generic[t] = read_table(conn, t)
    seq = {}
    if conn.execute("SELECT 1 FROM sqlite_master WHERE name='sqlite_sequence'").fetchone():
        seq = {r["name"]: int(r["seq"]) for r in conn.execute("SELECT name, seq FROM sqlite_sequence")}

    json_files = ["approved_groups.json", "auto_spawn_groups.json", "bot_groups.json",
                  "bot_group_state.json", "gstats_hidden_groups.json",
                  "notification_settings.json", "restrictions.json",
                  "character_spawn_cooldowns.json"]
    missing_json = [f for f in json_files if not (json_dir / f).exists()]

    known_codes = {c["code"] for c in chars}
    missing_chars = sorted({c["character_code"] for c in colls if c["character_code"] not in known_codes})
    known_users = {u["_id"] for u in users}
    ownerless = sorted({c["user_id"] for c in colls if c["user_id"] not in known_users})

    if missing_json:
        print("WARNING: these JSON files were not found in the JSON dir, so their data will NOT be migrated:")
        for f in missing_json:
            print(f"    - {f}")
        print()
    print("Source summary")
    print(f"  users: {len(users)} (total coins {sum(u['coins'] for u in users)})")
    print(f"  characters: {len(chars)}   collection copies: {len(colls)}   favorites: {len(favs)}")
    print(f"  groups: {len(groups)}   notification settings: {len(notifs)}   restrictions: {len(restr)}")
    print(f"  character spawn cooldowns: {len(cooldowns)}")
    print(f"  other tables: {len(generic)} ({sum(len(v) for v in generic.values())} rows)")
    if orphan_recruit:
        print(f"  note: recruit names of deleted characters {orphan_recruit} are kept in `orphan_recruit_names` (nothing is dropped)")
    if orphan_disc:
        print(f"  note: discontinued flags of deleted characters {orphan_disc} cannot be attached to a character and are not migrated")
    cd_unknown = sorted(c["_id"] for c in cooldowns if c["_id"] not in known_codes)
    if cd_unknown:
        print(f"  note: cooldowns for characters not in characters_v2 (still migrated): {cd_unknown}")
    if missing_chars:
        print(f"  note: collection copies pointing at missing characters (still migrated): {missing_chars}")
    if ownerless:
        print(f"  note: collection owners with no users row (still migrated): {ownerless}")

    # ---- pre-flight validation: every record must import without a unique-key / BSON error ----
    named = {"users": users, "characters": chars, "collections": colls, "favorites": favs,
             "orphan_recruit_names": orphan_recruit_rows, "notification_settings": notifs,
             "restrictions": restr, "character_spawn_cooldowns": cooldowns}
    for t, rows in generic.items():
        pk = pk_columns(conn, t)
        docs = []
        for r in rows:
            d = dict(r)
            if len(pk) == 1:
                d["_id"] = d[pk[0]]
            docs.append(d)
        named[t] = docs
    unique_specs = {
        "characters": [["code"], ["name_ci"]],
        "collections": [["legacy_id"]],
    }
    for t, cols in UNIQUE_KEYS.items():
        if t in named:
            unique_specs[t] = [cols]
    for t in generic:
        pk = pk_columns(conn, t)
        if len(pk) > 1:
            unique_specs.setdefault(t, []).append(pk)
    problems_pre = validate_documents(named, unique_specs)
    problems_pre += [f"character_spawn_cooldowns.json: {m}" for m in cooldown_bad]
    total_docs = sum(len(v) for v in named.values()) + len(groups)
    print(f"\nPre-flight validation: {total_docs} documents checked across {len(named) + 1} collections "
          f"-> {len(problems_pre)} problem(s)")
    for line in problems_pre[:25]:
        print("  !", line)
    if len(problems_pre) > 25:
        print(f"  ... and {len(problems_pre) - 25} more")

    if args.dry_run:
        print("\nDRY RUN: nothing written. Generic tables that would be copied:")
        for t, rows in generic.items():
            pk = pk_columns(conn, t)
            print(f"  {t:34s} rows={len(rows):5d}  pk={pk}")
        if problems_pre:
            print("\nDRY RUN RESULT: NOT READY - fix the problems above first.")
            return 1
        print("\nDRY RUN RESULT: OK - every record passed validation.")
        return 0

    if problems_pre:
        sys.exit("\nRefusing to import: pre-flight validation found problems (see above). Nothing was written.")

    # ---- connect -------------------------------------------------------------
    import mongo_db
    try:
        mongo_db.init_mongo()
    except Exception as exc:
        sys.exit(f"\nCould not connect to MongoDB: {exc}\n"
                 "Check MONGO_URI in .env and that your current IP is allowed under Atlas -> Network Access.")
    db = mongo_db.get_db()

    if args.wipe:
        if not args.yes:
            sys.exit("--wipe drops collections; re-run with --yes to confirm.")
        for name in MIGRATED_CORE_COLLECTIONS + list(generic) + ["counters"]:
            db[name].drop()
        print("\nWiped target collections.")
    elif not args.force and db["users"].estimated_document_count() > 0:
        sys.exit("\nTarget `users` collection already has data. Refusing to overwrite.\n"
                 "Use --force to upsert over it, or --wipe --yes to start clean.")

    print("\nCreating indexes ...")
    mongo_db.ensure_indexes()
    db["collections"].create_index("legacy_id", unique=True, partialFilterExpression={"legacy_id": {"$type": "int"}})

    # ---- write -----------------------------------------------------------------
    print("Writing core collections ...")
    bulk_upsert(db["users"], users, "_id")
    bulk_upsert(db["characters"], chars, "code")
    bulk_upsert(db["collections"], colls, "legacy_id")
    bulk_upsert(db["favorites"], favs, "_id")
    if orphan_recruit_rows:  # nothing is thrown away: rows whose character no longer exists
        bulk_upsert(db["orphan_recruit_names"], orphan_recruit_rows, "_id")

    from pymongo import UpdateOne
    ops = [UpdateOne({"_id": cid}, {"$set": fields}, upsert=True) for cid, fields in groups.items()]
    for batch in chunked(ops):
        db["groups"].bulk_write(batch, ordered=False)
    bulk_upsert(db["notification_settings"], notifs, "_id")
    bulk_upsert(db["restrictions"], restr, "_id")
    bulk_upsert(db["character_spawn_cooldowns"], cooldowns, "_id")

    print("Writing remaining tables (kept for later phases) ...")
    for t, rows in generic.items():
        pk = pk_columns(conn, t)
        if not rows:
            continue
        if len(pk) == 1:
            docs = []
            for r in rows:
                d = dict(r)
                d["_id"] = d[pk[0]]  # original column is kept too
                docs.append(d)
            bulk_upsert(db[t], docs, "_id")
        else:
            db[t].create_index([(c, 1) for c in pk], unique=True, name="pk_" + "_".join(pk))
            bulk_upsert(db[t], [dict(r) for r in rows], pk)
        # counters so next_sequence() continues the AUTOINCREMENT series
        if "id" in pk and len(pk) == 1:
            top = max([int(r["id"]) for r in rows] + [seq.get(t, 0)])
            db["counters"].update_one({"_id": t}, {"$max": {"seq": top}}, upsert=True)
    for t, v in seq.items():
        if t in generic or t in {"collections_v2"}:
            db["counters"].update_one({"_id": t}, {"$max": {"seq": v}}, upsert=True)

    # ---- verify ----------------------------------------------------------------
    print("\nVerification")
    problems = []

    def check(label, expected, actual):
        ok = expected == actual
        if ok and isinstance(expected, dict):
            print(f"  [OK] {label}: {len(expected)} entries identical")
        else:
            print(f"  [{'OK' if ok else 'MISMATCH'}] {label}: sqlite/json={expected}  mongo={actual}")
        if not ok:
            problems.append(label)

    check("users", len(users), db["users"].count_documents({}))
    agg = list(db["users"].aggregate([{"$group": {"_id": None, "c": {"$sum": "$coins"}}}]))
    check("total coins", sum(u["coins"] for u in users), agg[0]["c"] if agg else 0)
    check("characters", len(chars), db["characters"].count_documents({}))
    check("collection copies", len(colls), db["collections"].count_documents({}))
    check("favorites", len(favs), db["favorites"].count_documents({}))
    embedded = sum(len(d.get("recruit_names", [])) for d in db["characters"].find({}, {"recruit_names": 1}))
    check("character_recruit_names_v2 (embedded + orphans)", len(recruit_rows),
          embedded + db["orphan_recruit_names"].count_documents({}))
    check("discontinued_characters_v2", len(disc_rows) - len(orphan_disc), db["characters"].count_documents({"discontinued": True}))
    check("groups", len(groups), db["groups"].count_documents({}))
    check("notification settings", len(notifs), db["notification_settings"].count_documents({}))
    check("restrictions", len(restr), db["restrictions"].count_documents({}))
    check("character spawn cooldowns", len(cooldowns), db["character_spawn_cooldowns"].count_documents({}))
    check("cooldown timestamps", {c["_id"]: c["last_spawned_at"] for c in cooldowns},
          {d["_id"]: d.get("last_spawned_at") for d in db["character_spawn_cooldowns"].find({})})
    for t, rows in generic.items():
        check(t, len(rows), db[t].count_documents({}))

    per_user_src = {}
    for c in colls:
        per_user_src[c["user_id"]] = per_user_src.get(c["user_id"], 0) + 1
    per_user_dst = {d["_id"]: d["n"] for d in db["collections"].aggregate(
        [{"$group": {"_id": "$user_id", "n": {"$sum": 1}}}])}
    check("per-user collection sizes", per_user_src, per_user_dst)

    n_core = len(CORE_TABLES & set(tables))
    print(f"\n  {n_core + len(generic)} of {len(tables)} SQLite tables verified against MongoDB "
          f"({n_core} core + {len(generic)} copied 1:1)")
    if problems:
        print(f"\nFINISHED WITH MISMATCHES: {problems}")
        return 1
    print("\nMigration complete and verified. Keep bot_database.db and the JSON files as your backup.")
    return 0


def main():
    default_db = "bot_database.db"
    ap = argparse.ArgumentParser(description="Migrate bot_database.db + JSON files to MongoDB Atlas")
    ap.add_argument("--db", default=str(HERE / default_db), help="path to SQLite file")
    ap.add_argument("--json-dir", default=str(HERE), help="folder containing the JSON files")
    ap.add_argument("--dry-run", action="store_true", help="read/transform/report only; no MongoDB access")
    ap.add_argument("--force", action="store_true", help="upsert even if target already has data")
    ap.add_argument("--wipe", action="store_true", help="drop target collections before importing")
    ap.add_argument("--yes", action="store_true", help="confirm destructive --wipe")
    sys.exit(migrate(ap.parse_args()))


if __name__ == "__main__":
    main()
