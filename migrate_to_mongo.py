import dns.resolver

dns.resolver.default_resolver = dns.resolver.Resolver(configure=False)
dns.resolver.default_resolver.nameservers = ["8.8.8.8"]

"""
MongoDB (Atlas) for the bot - the ONLY file that talks to the database driver.

  * the bot imports this module as its data layer   ->  import migrate_to_mongo as store
  * run it directly to move an existing SQLite file ->  python migrate_to_mongo.py [rose_clone.db]
        --dry-run   show what would be copied, write nothing
        --force     copy again even though a migration was already recorded

Environment:  MONGO_URI (required)   MONGO_DB (optional, default "telegram_bot")

Collections (same names as the old SQLite tables, so nothing is lost in translation):
  settings, warn_log, notes, filters, blocklist, setlog_pending, super_admins, approved, allowlist,
  captcha_pending, roast_profiles, roast_battles, roast_results, roast_votes, court_cases,
  court_votes, court_verdicts, modlog (new: per-group moderation history)  (+ counters for auto-increment ids, meta for the migration marker)

Speed: the bot reads settings / approvals / allowlist / blocklist / filters / notes / super admins
on almost every message, so those are cached in memory and the cache is updated on every write
(one bot instance = one process, so the cache can't go stale).
"""
import logging
import os
import shutil
import sys
import tempfile
import threading
import time
from collections import defaultdict
from datetime import datetime, timedelta, timezone

import certifi
from pymongo import ASCENDING, DESCENDING, MongoClient, ReplaceOne, ReturnDocument
from pymongo.errors import ConfigurationError, DuplicateKeyError, PyMongoError

log = logging.getLogger("mongo")
DBError = PyMongoError  # what callers catch for "the database failed"


class StoreError(RuntimeError):
    """Startup problem with a readable message (bad URI, unreachable cluster, ...)."""


# ------------------------------------------------------------------ connection
_client = None
_db = None
_lock = threading.RLock()


def _wants_tls(uri):
    u = uri.lower()
    return u.startswith("mongodb+srv://") or "tls=true" in u or "ssl=true" in u


def connect(uri=None):
    """Connect to MongoDB Atlas (mongodb+srv:// is fine), create the indexes, return the database."""
    global _client, _db
    if _db is not None:
        return _db
    uri = (uri or os.getenv("MONGO_URI") or "").strip()
    if not uri:
        raise StoreError("MONGO_URI is not set.")
    kwargs = dict(serverSelectionTimeoutMS=10000, connectTimeoutMS=10000, socketTimeoutMS=30000,
                  retryWrites=True, appname="telegram-group-bot")
    if _wants_tls(uri):
        kwargs["tlsCAFile"] = certifi.where()  # current CA bundle: TLS verification just works
    try:
        client = MongoClient(uri, **kwargs)
        client.admin.command("ping")
    except ConfigurationError as e:
        raise StoreError(f"MONGO_URI is not valid: {e}. If the password has special characters "
                         "(@ : / ? # %), URL-encode them.") from e
    except PyMongoError as e:
        raise StoreError(
            f"Could not reach MongoDB ({type(e).__name__}: {e}). Check: (1) MONGO_URI is correct, "
            "(2) the database user/password are right, (3) Atlas > Network Access allows this "
            "machine (Render: add 0.0.0.0/0), (4) the cluster isn't paused.") from e
    name = (os.getenv("MONGO_DB") or "").strip()
    if not name:
        try:
            name = client.get_default_database().name  # a database named inside the URI
        except (ConfigurationError, PyMongoError):
            name = "telegram_bot"
    _client, _db = client, client[name]
    _ensure_indexes()
    log.info("MongoDB connected (database: %s).", name)
    return _db


def col(name):
    if _db is None:
        raise StoreError("Database not connected: call connect() first.")
    return _db[name]


def next_id(name):
    """Auto-increment id (the old AUTOINCREMENT columns), atomic on the server."""
    doc = col("counters").find_one_and_update(
        {"_id": name}, {"$inc": {"seq": 1}}, upsert=True, return_document=ReturnDocument.AFTER)
    return int(doc["seq"])


def _clean(doc):
    if doc is not None:
        doc.pop("_id", None)
    return doc


UNIQUE_INDEXES = {
    "settings": ["chat_id", "key"], "notes": ["chat_id", "name"], "filters": ["chat_id", "keyword"],
    "blocklist": ["chat_id", "word"], "approved": ["chat_id", "user_id"],
    "allowlist": ["chat_id", "kind", "value"], "captcha_pending": ["chat_id", "user_id"],
    "setlog_pending": ["channel_id"], "super_admins": ["user_id"], "warn_log": ["id"],
    "roast_profiles": ["chat_id", "user_id"], "roast_battles": ["id"], "roast_results": ["id"],
    "roast_votes": ["battle_id", "voter_id"], "court_cases": ["id"],
    "court_votes": ["case_id", "voter_id"], "court_verdicts": ["id"],
    "modlog": ["id"], "notice_pending": ["chat_id", "message_id"],
}
PLAIN_INDEXES = {
    "warn_log": [["chat_id", "user_id"]], "captcha_pending": [["expires"]],
    "roast_battles": [["chat_id"]], "roast_profiles": [["chat_id", "points"]],
    "court_cases": [["chat_id", "case_no"], ["chat_id", "defendant_id"]], "court_verdicts": [["case_id"]],
    "modlog": [["chat_id", "id"]], "notice_pending": [["delete_at"]],
}
# MongoDB deletes a document by itself once its "expire_at" date has passed (no bot code involved).
# Documents without an expire_at (the old modlog rows) are never touched by this.
TTL_INDEXES = ("modlog", "notice_pending")


def _ensure_indexes():
    for name, keys in UNIQUE_INDEXES.items():
        try:
            col(name).create_index([(k, ASCENDING) for k in keys], unique=True)
        except PyMongoError as e:
            log.warning("Couldn't create the unique index on %s%s: %s", name, keys, e)
    for name, groups in PLAIN_INDEXES.items():
        for keys in groups:
            try:
                col(name).create_index([(k, ASCENDING) for k in keys])
            except PyMongoError as e:
                log.warning("Couldn't create an index on %s%s: %s", name, keys, e)
    for name in TTL_INDEXES:
        try:
            col(name).create_index("expire_at", expireAfterSeconds=0)
        except PyMongoError as e:
            log.warning("Couldn't create the automatic-cleanup index on %s: %s", name, e)


# ------------------------------------------------------------------ settings
_S = {}  # chat_id -> {key: value}


def _settings(chat_id):
    d = _S.get(chat_id)
    if d is None:
        d = {r["key"]: r["value"] for r in col("settings").find({"chat_id": chat_id})}
        if len(_S) > 5000:
            _S.clear()
        _S[chat_id] = d
    return d


def get_setting(chat_id, key, default=None):
    with _lock:
        return _settings(int(chat_id)).get(key, default)


def set_setting(chat_id, key, value):
    chat_id, value = int(chat_id), str(value)
    with _lock:
        col("settings").update_one({"chat_id": chat_id, "key": key}, {"$set": {"value": value}}, upsert=True)
        _settings(chat_id)[key] = value


def del_setting(chat_id, key):
    chat_id = int(chat_id)
    with _lock:
        col("settings").delete_one({"chat_id": chat_id, "key": key})
        _settings(chat_id).pop(key, None)


def del_setting_everywhere(key):
    with _lock:
        col("settings").delete_many({"key": key})
        _S.clear()


def settings_with_prefix(chat_id, prefix):
    with _lock:
        return {k: v for k, v in _settings(int(chat_id)).items() if k.startswith(prefix)}


# ------------------------------------------------------------------ approved users
_APP = {}  # chat_id -> {user_id: True} (insertion ordered)


def _approved(chat_id):
    d = _APP.get(chat_id)
    if d is None:
        d = {r["user_id"]: True for r in col("approved").find({"chat_id": chat_id})}
        if len(_APP) > 5000:
            _APP.clear()
        _APP[chat_id] = d
    return d


def is_approved(chat_id, user_id):
    with _lock:
        return int(user_id) in _approved(int(chat_id))


def approve(chat_id, user_id):
    chat_id, user_id = int(chat_id), int(user_id)
    with _lock:
        col("approved").update_one({"chat_id": chat_id, "user_id": user_id},
                                   {"$set": {"chat_id": chat_id, "user_id": user_id}}, upsert=True)
        _approved(chat_id)[user_id] = True


def unapprove(chat_id, user_id):
    chat_id, user_id = int(chat_id), int(user_id)
    with _lock:
        col("approved").delete_one({"chat_id": chat_id, "user_id": user_id})
        _approved(chat_id).pop(user_id, None)


def approved_ids(chat_id):
    with _lock:
        return list(_approved(int(chat_id)))


def approved_count(chat_id):
    with _lock:
        return len(_approved(int(chat_id)))


def unapprove_all(chat_id):
    chat_id = int(chat_id)
    with _lock:
        n = col("approved").delete_many({"chat_id": chat_id}).deleted_count
        _APP[chat_id] = {}
        return n


# ------------------------------------------------------------------ allowlist
_ALLOW = {}  # chat_id -> {kind: set(values)}


def _allow(chat_id):
    d = _ALLOW.get(chat_id)
    if d is None:
        d = defaultdict(set)
        for r in col("allowlist").find({"chat_id": chat_id}):
            d[r["kind"]].add(r["value"])
        if len(_ALLOW) > 5000:
            _ALLOW.clear()
        _ALLOW[chat_id] = d
    return d


def allow_load(chat_id):
    with _lock:
        out = defaultdict(set)
        for kind, values in _allow(int(chat_id)).items():
            out[kind] = set(values)
        return out


def allow_count(chat_id):
    with _lock:
        return sum(len(v) for v in _allow(int(chat_id)).values())


def allow_add(chat_id, kind, value):
    """True if it was new, False if it was already on the list."""
    chat_id = int(chat_id)
    with _lock:
        try:
            col("allowlist").insert_one({"chat_id": chat_id, "kind": kind, "value": value})
        except DuplicateKeyError:
            _allow(chat_id)[kind].add(value)
            return False
        _allow(chat_id)[kind].add(value)
        return True


def allow_remove(chat_id, kind, value):
    chat_id = int(chat_id)
    with _lock:
        n = col("allowlist").delete_one({"chat_id": chat_id, "kind": kind, "value": value}).deleted_count
        _allow(chat_id)[kind].discard(value)
        return bool(n)


def allow_clear(chat_id):
    chat_id = int(chat_id)
    with _lock:
        n = col("allowlist").delete_many({"chat_id": chat_id}).deleted_count
        _ALLOW[chat_id] = defaultdict(set)
        return n


# ------------------------------------------------------------------ blocklist
_BLOCK = {}  # chat_id -> [words]


def _block(chat_id):
    d = _BLOCK.get(chat_id)
    if d is None:
        d = [r["word"] for r in col("blocklist").find({"chat_id": chat_id})]
        if len(_BLOCK) > 5000:
            _BLOCK.clear()
        _BLOCK[chat_id] = d
    return d


def block_words(chat_id):
    with _lock:
        return list(_block(int(chat_id)))


def block_add(chat_id, word):
    chat_id = int(chat_id)
    with _lock:
        col("blocklist").update_one({"chat_id": chat_id, "word": word},
                                    {"$set": {"chat_id": chat_id, "word": word}}, upsert=True)
        words = _block(chat_id)
        if word not in words:
            words.append(word)


def block_remove(chat_id, word):
    chat_id = int(chat_id)
    with _lock:
        n = col("blocklist").delete_one({"chat_id": chat_id, "word": word}).deleted_count
        words = _block(chat_id)
        if word in words:
            words.remove(word)
        return bool(n)


# ------------------------------------------------------------------ filters
_FILT = {}  # chat_id -> {keyword: reply}


def _filters(chat_id):
    d = _FILT.get(chat_id)
    if d is None:
        d = {r["keyword"]: r["reply"] for r in col("filters").find({"chat_id": chat_id})}
        if len(_FILT) > 5000:
            _FILT.clear()
        _FILT[chat_id] = d
    return d


def filter_rows(chat_id):
    with _lock:
        return list(_filters(int(chat_id)).items())


def filter_add(chat_id, keyword, reply):
    chat_id = int(chat_id)
    with _lock:
        col("filters").update_one({"chat_id": chat_id, "keyword": keyword}, {"$set": {"reply": reply}},
                                  upsert=True)
        _filters(chat_id)[keyword] = reply


def filter_remove(chat_id, keyword):
    chat_id = int(chat_id)
    with _lock:
        n = col("filters").delete_one({"chat_id": chat_id, "keyword": keyword}).deleted_count
        _filters(chat_id).pop(keyword, None)
        return bool(n)


# ------------------------------------------------------------------ notes
_NOTES = {}  # chat_id -> {name: content}


def _notes(chat_id):
    d = _NOTES.get(chat_id)
    if d is None:
        d = {r["name"]: r["content"] for r in col("notes").find({"chat_id": chat_id})}
        if len(_NOTES) > 2000:
            _NOTES.clear()
        _NOTES[chat_id] = d
    return d


def note_get(chat_id, name):
    with _lock:
        return _notes(int(chat_id)).get(name)


def note_set(chat_id, name, content):
    chat_id = int(chat_id)
    with _lock:
        col("notes").update_one({"chat_id": chat_id, "name": name}, {"$set": {"content": content}}, upsert=True)
        _notes(chat_id)[name] = content


def note_names(chat_id):
    with _lock:
        return list(_notes(int(chat_id)))


def note_del(chat_id, name):
    chat_id = int(chat_id)
    with _lock:
        n = col("notes").delete_one({"chat_id": chat_id, "name": name}).deleted_count
        _notes(chat_id).pop(name, None)
        return bool(n)


# ------------------------------------------------------------------ warnings
def warn_add(chat_id, user_id, reason, ts):
    col("warn_log").insert_one({"id": next_id("warn_log"), "chat_id": int(chat_id), "user_id": int(user_id),
                                "reason": reason, "ts": int(ts)})


def warn_active(chat_id, user_id, expiry=0):
    """Unexpired warnings, oldest first, as (id, reason, ts). Expired ones are deleted first."""
    chat_id, user_id = int(chat_id), int(user_id)
    if expiry:
        col("warn_log").delete_many({"chat_id": chat_id, "ts": {"$lt": int(time.time()) - int(expiry)}})
    rows = col("warn_log").find({"chat_id": chat_id, "user_id": user_id}, sort=[("id", ASCENDING)])
    return [(r["id"], r.get("reason"), r.get("ts")) for r in rows]


def warn_delete(warn_id, chat_id=None):
    """Delete one warning. Pass chat_id so a warning id can only ever be removed from its own group."""
    flt = {"id": warn_id}
    if chat_id is not None:
        flt["chat_id"] = int(chat_id)
    col("warn_log").delete_one(flt)


def warn_clear(chat_id, user_id):
    col("warn_log").delete_many({"chat_id": int(chat_id), "user_id": int(user_id)})


# ------------------------------------------------------------------ captcha
def captcha_put(chat_id, user_id, msg_id, answer, attempts, expires, mention):
    chat_id, user_id = int(chat_id), int(user_id)
    col("captcha_pending").replace_one(
        {"chat_id": chat_id, "user_id": user_id},
        {"chat_id": chat_id, "user_id": user_id, "msg_id": msg_id, "answer": answer,
         "attempts": attempts, "expires": int(expires), "mention": mention}, upsert=True)


def captcha_get(chat_id, user_id):
    """(msg_id, answer, attempts, mention) or None."""
    r = col("captcha_pending").find_one({"chat_id": int(chat_id), "user_id": int(user_id)})
    return (r["msg_id"], r["answer"], r.get("attempts", 0), r.get("mention")) if r else None


def captcha_delete(chat_id, user_id):
    col("captcha_pending").delete_one({"chat_id": int(chat_id), "user_id": int(user_id)})


def captcha_set_attempts(chat_id, user_id, attempts):
    col("captcha_pending").update_one({"chat_id": int(chat_id), "user_id": int(user_id)},
                                      {"$set": {"attempts": attempts}})


def captcha_pop(chat_id, user_id):
    """msg_id of the pending challenge (or None); the record is removed."""
    r = col("captcha_pending").find_one_and_delete({"chat_id": int(chat_id), "user_id": int(user_id)})
    return r["msg_id"] if r else None


def captcha_pop_chat(chat_id):
    """[(user_id, msg_id)] for everyone still waiting in this chat; all records removed."""
    chat_id = int(chat_id)
    rows = [(r["user_id"], r["msg_id"]) for r in col("captcha_pending").find({"chat_id": chat_id})]
    col("captcha_pending").delete_many({"chat_id": chat_id})
    return rows


def captcha_take_expired(now):
    """[(chat_id, user_id, msg_id, mention)] whose time ran out; removed. Each one is claimed
    atomically, so even two overlapping sweeps can't fail the same member twice."""
    out = []
    for r in list(col("captcha_pending").find({"expires": {"$lte": int(now)}})):
        if col("captcha_pending").delete_one({"chat_id": r["chat_id"], "user_id": r["user_id"]}).deleted_count:
            out.append((r["chat_id"], r["user_id"], r["msg_id"], r.get("mention")))
    return out


# ------------------------------------------------------------------ log-channel handshake
def setlog_put(channel_id, message_id, ts):
    channel_id = int(channel_id)
    col("setlog_pending").replace_one({"channel_id": channel_id},
                                      {"channel_id": channel_id, "message_id": message_id, "ts": int(ts)},
                                      upsert=True)


def setlog_get(channel_id):
    """(message_id, ts) or None."""
    r = col("setlog_pending").find_one({"channel_id": int(channel_id)})
    return (r["message_id"], r["ts"]) if r else None


def setlog_del(channel_id):
    col("setlog_pending").delete_one({"channel_id": int(channel_id)})


# ------------------------------------------------------------------ super admins (bot moderators)
_SA = None  # {user_id: (username, ts)} - small, loaded once


def _super_admins():
    global _SA
    if _SA is None:
        _SA = {r["user_id"]: (r.get("username"), r.get("ts") or 0) for r in col("super_admins").find({})}
    return _SA


def sa_rows():
    with _lock:
        items = sorted(_super_admins().items(), key=lambda kv: (kv[1][1], kv[0]))
        return [(uid, username) for uid, (username, _) in items]


def is_super_admin(user_id):
    with _lock:
        return int(user_id) in _super_admins()


def sa_add(user_id, username, added_by, ts):
    user_id = int(user_id)
    with _lock:
        col("super_admins").replace_one(
            {"user_id": user_id},
            {"user_id": user_id, "username": username, "added_by": added_by, "ts": int(ts)}, upsert=True)
        _super_admins()[user_id] = (username, int(ts))


def sa_remove(user_id):
    """Removes the Super Admin; returns the username that was stored (or None)."""
    user_id = int(user_id)
    with _lock:
        stored = (_super_admins().get(user_id) or (None, 0))[0]
        col("super_admins").delete_one({"user_id": user_id})
        _super_admins().pop(user_id, None)
        return stored


def sa_set_username(user_id, username):
    user_id = int(user_id)
    with _lock:
        col("super_admins").update_one({"user_id": user_id}, {"$set": {"username": username}})
        if user_id in _super_admins():
            _super_admins()[user_id] = (username, _super_admins()[user_id][1])


# ------------------------------------------------------------------ per-group moderation log
# One row per moderation event, always stored under the chat_id of the group it happened in.
# (The optional Telegram log channel still works exactly as before; this is the stored history.)
MODLOG_KEEP = 1000  # newest rows kept per group (safety cap on top of the time limit below)
HISTORY_KEEP_DAYS = 15  # action history rows are deleted automatically by MongoDB after this many days
_MODLOG_PRUNE_EVERY = 50


def modlog_add(chat_id, category, text, ts):
    chat_id = int(chat_id)
    row_id = next_id("modlog")
    col("modlog").insert_one({"id": row_id, "chat_id": chat_id, "category": str(category),
                              "text": str(text)[:2000], "ts": int(ts),
                              "expire_at": datetime.fromtimestamp(int(ts), timezone.utc) + timedelta(days=HISTORY_KEEP_DAYS)})
    if row_id % _MODLOG_PRUNE_EVERY == 0:  # keep the history bounded, one group at a time
        cutoff = list(col("modlog").find({"chat_id": chat_id}, {"id": 1}, sort=[("id", DESCENDING)],
                                         skip=MODLOG_KEEP, limit=1))
        if cutoff:
            col("modlog").delete_many({"chat_id": chat_id, "id": {"$lte": cutoff[0]["id"]}})


def modlog_recent(chat_id, limit=20, category=None):
    """Newest first: [{id, category, text, ts}] for THIS group only."""
    flt = {"chat_id": int(chat_id)}
    if category:
        flt["category"] = category
    rows = col("modlog").find(flt, sort=[("id", DESCENDING)], limit=max(1, min(int(limit), 200)))
    return [{"id": r["id"], "category": r.get("category"), "text": r.get("text", ""), "ts": r.get("ts", 0)}
            for r in rows]


def modlog_count(chat_id):
    return col("modlog").count_documents({"chat_id": int(chat_id)})


# ------------------------------------------------------------------ action notices that delete themselves later
# One row per bot notice that must disappear after NOTICE_LIFETIME. The row lives only until the notice is deleted
# (notice_take_due removes it); "expire_at" is a safety net so an unprocessed row can never stay longer than
# HISTORY_KEEP_DAYS after its delete time.
NOTICE_LIFETIME = 24 * 60 * 60  # a notice is deleted 1 day after it was sent


def notice_schedule(chat_id, message_id, delete_at=None):
    chat_id, message_id = int(chat_id), int(message_id)
    delete_at = int(delete_at or (time.time() + NOTICE_LIFETIME))
    col("notice_pending").replace_one(
        {"chat_id": chat_id, "message_id": message_id},
        {"chat_id": chat_id, "message_id": message_id, "delete_at": delete_at,
         "expire_at": datetime.fromtimestamp(delete_at, timezone.utc) + timedelta(days=HISTORY_KEEP_DAYS)},
        upsert=True)


def notice_take_due(now, limit=50):
    """[(chat_id, message_id)] whose time has come; each row is removed atomically as it is claimed, so two
    overlapping sweeps can never delete the same notice twice."""
    out = []
    for r in list(col("notice_pending").find({"delete_at": {"$lte": int(now)}}).limit(int(limit))):
        if col("notice_pending").delete_one({"_id": r["_id"]}).deleted_count:
            out.append((r["chat_id"], r["message_id"]))
    return out


# ------------------------------------------------------------------ owner-chosen defaults for NEW groups
# {setting key: value} for every default the Bot Owner changed in the 👑 Owner panel. One small document for the
# whole bot; loaded once and kept in step with every write (one bot process, so it cannot go stale).
_OWNER_DEF = None


def owner_defaults():
    global _OWNER_DEF
    with _lock:
        if _OWNER_DEF is None:
            _OWNER_DEF = dict((col("meta").find_one({"_id": "new_group_defaults"}) or {}).get("values") or {})
        return dict(_OWNER_DEF)


def set_owner_default(key, value):
    with _lock:
        owner_defaults()
        col("meta").update_one({"_id": "new_group_defaults"}, {"$set": {f"values.{key}": value}}, upsert=True)
        _OWNER_DEF[key] = value


def del_owner_default(key):
    """Back to the original value for this setting."""
    with _lock:
        owner_defaults()
        col("meta").update_one({"_id": "new_group_defaults"}, {"$unset": {f"values.{key}": ""}})
        _OWNER_DEF.pop(key, None)


# ------------------------------------------------------------------ read-only inspection (Bot Owner panel)
HIDDEN_SETTING_PREFIXES = ("uname:", "lastname:")  # per-member bookkeeping, not group configuration


def settings_snapshot(chat_id):
    """A copy of one group's settings (member bookkeeping hidden). Never touches another group."""
    with _lock:
        return {k: v for k, v in _settings(int(chat_id)).items() if not k.startswith(HIDDEN_SETTING_PREFIXES)}


def chat_overview(chat_id):
    """Row counts of every group-specific collection for ONE group (read-only)."""
    chat_id = int(chat_id)
    out = {}
    for name in CHAT_COLLECTIONS:
        out[name] = col(name).count_documents({"chat_id": chat_id})
    return out


def warn_recent(chat_id, limit=10):
    """Newest warnings recorded in ONE group: [(user_id, reason, ts)]."""
    rows = col("warn_log").find({"chat_id": int(chat_id)}, sort=[("id", DESCENDING)], limit=int(limit))
    return [(r["user_id"], r.get("reason"), r.get("ts")) for r in rows]


# ------------------------------------------------------------------ group -> supergroup migration
CHAT_COLLECTIONS = ("settings", "warn_log", "notes", "filters", "blocklist", "approved", "allowlist",
                    "captcha_pending", "roast_profiles", "roast_battles", "roast_results", "roast_votes",
                    "court_cases", "court_votes", "court_verdicts", "modlog")


def migrate_chat(old_id, new_id):
    """A basic group became a supergroup (new chat id): move every saved record across."""
    old_id, new_id = int(old_id), int(new_id)
    with _lock:
        for name in CHAT_COLLECTIONS:
            c = col(name)
            for doc in list(c.find({"chat_id": old_id})):
                try:
                    c.update_one({"_id": doc["_id"]}, {"$set": {"chat_id": new_id}})
                except DuplicateKeyError:  # the new id already has that record: the old one wins
                    key = {k: doc[k] for k in UNIQUE_INDEXES.get(name, []) if k != "chat_id" and k in doc}
                    c.delete_one({"chat_id": new_id, **key})
                    c.update_one({"_id": doc["_id"]}, {"$set": {"chat_id": new_id}})
        for cache in (_S, _APP, _ALLOW, _BLOCK, _FILT, _NOTES):
            cache.pop(old_id, None)
            cache.pop(new_id, None)


# ------------------------------------------------------------------ SQLite -> MongoDB migration
# table -> (key columns used to upsert, ordered columns)
TABLES = {
    "settings": (["chat_id", "key"], ["chat_id", "key", "value"]),
    "warn_log": (["id"], ["id", "chat_id", "user_id", "reason", "ts"]),
    "notes": (["chat_id", "name"], ["chat_id", "name", "content"]),
    "filters": (["chat_id", "keyword"], ["chat_id", "keyword", "reply"]),
    "blocklist": (["chat_id", "word"], ["chat_id", "word"]),
    "setlog_pending": (["channel_id"], ["channel_id", "message_id", "ts"]),
    "super_admins": (["user_id"], ["user_id", "username", "added_by", "ts"]),
    "approved": (["chat_id", "user_id"], ["chat_id", "user_id"]),
    "allowlist": (["chat_id", "kind", "value"], ["chat_id", "kind", "value"]),
    "captcha_pending": (["chat_id", "user_id"],
                        ["chat_id", "user_id", "msg_id", "answer", "attempts", "expires", "mention"]),
    "roast_profiles": (["chat_id", "user_id"],
                       ["chat_id", "user_id", "name", "points", "wins", "losses", "draws", "streak",
                        "best_streak", "roasts_given", "roasts_received"]),
    "roast_battles": (["id"], ["id", "chat_id", "challenger_id", "challenger_name", "opponent_id",
                               "opponent_name", "status", "text_a", "text_b", "algo_a", "algo_b",
                               "created", "deadline", "message_id"]),
    "roast_results": (["id"], ["id", "battle_id", "chat_id", "winner_id", "loser_id", "final_a", "final_b",
                               "votes_a", "votes_b", "outcome", "ts"]),
    "roast_votes": (["battle_id", "voter_id"], ["battle_id", "chat_id", "voter_id", "choice", "ts"]),
    "court_cases": (["id"], ["id", "chat_id", "case_no", "defendant_id", "defendant_name", "opened_by",
                             "opened_by_name", "charge", "evidence", "plea", "status", "bail", "sentence",
                             "appeals", "message_id", "opened", "closes"]),
    "court_votes": (["case_id", "voter_id"], ["case_id", "chat_id", "voter_id", "vote", "ts"]),
    "court_verdicts": (["id"], ["id", "case_id", "chat_id", "defendant_id", "verdict", "guilty_votes",
                               "innocent_votes", "plea", "sentence", "ts"]),
}
AUTO_ID_TABLES = ("warn_log", "roast_battles", "roast_results", "court_cases", "court_verdicts")
SKIP_SETTING_KEYS = {"purgefrom"}  # leftovers of an old purge module; the bot deletes them anyway


def _read_sqlite(path):
    """Read every table of the SQLite file (a private copy, so the original isn't touched)."""
    import sqlite3
    tmp = tempfile.mkdtemp(prefix="sqlite_copy_")
    try:
        for ext in ("", "-wal", "-shm"):
            if os.path.exists(path + ext):
                shutil.copy(path + ext, os.path.join(tmp, "db" + ext))
        conn = sqlite3.connect(os.path.join(tmp, "db"))
        have = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        data = {}
        for table, (_, cols) in TABLES.items():
            if table not in have:
                data[table] = []
                continue
            present = [r[1] for r in conn.execute(f"PRAGMA table_info({table})")]
            use = [c for c in cols if c in present]
            rows = conn.execute(f"SELECT {', '.join(use)} FROM {table}").fetchall()
            data[table] = [dict(zip(use, r)) for r in rows]
        conn.close()
        return data
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def migrate_sqlite(path, dry_run=False, force=False, log_fn=print):
    """Copy the SQLite file into MongoDB. Safe to re-run with --force (upserts by natural key)."""
    if not os.path.exists(path):
        raise StoreError(f"SQLite file not found: {path}")
    data = _read_sqlite(path)
    if not dry_run:
        connect()
        marker = col("meta").find_one({"_id": "sqlite_migration"})
        if marker and not force:
            raise StoreError("A migration was already recorded on "
                             f"{time.ctime(marker.get('ts', 0))}. Re-running could overwrite newer data; "
                             "use --force if you really want to copy again.")
    log_fn(f"{'DRY RUN - ' if dry_run else ''}Source: {path}")
    copied = {}
    for table, (keys, cols) in TABLES.items():
        rows = data[table]
        if table == "settings":
            rows = [r for r in rows if r.get("key") not in SKIP_SETTING_KEYS]
        if not dry_run and rows:
            ops = [ReplaceOne({k: r[k] for k in keys}, r, upsert=True) for r in rows]
            for i in range(0, len(ops), 500):
                col(table).bulk_write(ops[i:i + 500], ordered=False)
        copied[table] = len(rows)
        log_fn(f"  {table:<16} {len(rows):>6} rows")
    if not dry_run:
        for table in AUTO_ID_TABLES:
            top = max((r["id"] for r in data[table]), default=0)
            if top:
                col("counters").update_one({"_id": table}, {"$max": {"seq": top}}, upsert=True)
        problems = []
        for table, n in copied.items():
            have = col(table).count_documents({})
            if have < n:
                problems.append(f"{table}: copied {n} but found {have}")
        if problems:
            raise StoreError("Verification failed: " + "; ".join(problems))
        col("meta").replace_one({"_id": "sqlite_migration"},
                                {"_id": "sqlite_migration", "ts": time.time(), "source": os.path.basename(path),
                                 "rows": copied}, upsert=True)
        log_fn("Done. Every table was copied and verified in MongoDB.")
    return copied


def auto_seed(path="rose_clone.db"):
    """Called at bot startup: if an old SQLite file sits next to the code and the Mongo database is
    still empty, import it once. Does nothing otherwise (never overwrites a live database)."""
    path = os.getenv("SQLITE_SEED_PATH", path)
    if not os.path.exists(path):
        return False
    if col("meta").find_one({"_id": "sqlite_migration"}) or col("settings").count_documents({}) > 0:
        return False
    log.info("MongoDB is empty and %s exists: importing it once.", path)
    migrate_sqlite(path, log_fn=log.info)
    return True


def _cli(argv):
    args = [a for a in argv if not a.startswith("--")]
    path = args[0] if args else "rose_clone.db"
    try:
        from dotenv import load_dotenv
        load_dotenv()
    except ImportError:
        pass
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    try:
        migrate_sqlite(path, dry_run="--dry-run" in argv, force="--force" in argv)
    except StoreError as e:
        sys.exit(f"ERROR: {e}")


if __name__ == "__main__":
    _cli(sys.argv[1:])
