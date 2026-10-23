"""
Badge system + Banner system for the Anime Character Catcher bot.

EVERYTHING lives in this file: business rules, MongoDB access, validation, command handlers, callbacks,
guided admin flows, help-page text, keyboards and the /mystats section.  bot.py only
  * imports this module,
  * calls  badge_banner.bind(...)  and  badge_banner.register(app)  in main()   (same pattern as fusion.py / theme.py),
  * adds the command names / help page this module exports to its tables,
  * hands the finished /mystats text to  badge_banner.send_mystats(...),
  * lists this module's collections in the delete / restore / move-user helpers.
bot.py is never imported here (no circular import): everything it owns is injected through bind().

BADGES   /badges  /claimbadge <code/name>
         Tiers (single table below): Silver 2, Gold 3, Platinum 4, Diamond 5 copies.  /claimbadge claims the HIGHEST tier
         the user qualifies for.  Claims are permanent records (never removed when copies are lost, never downgraded;
         a unique index on user + character + tier makes double claims impossible).
BANNERS  /banner  /usebanner <code>             (everyone)
         /addbanner /editbanner /delbanner /listbanners   (Owner + Executive only, checked again inside every handler)
         A banner is unlocked only while the user owns ALL of its required characters (always computed from CURRENT
         ownership).  An equipped banner whose requirements are no longer met is unequipped the next time it is read.

Collections (created lazily, indexes are idempotent):
  badge_claims_v1  {user_id, character_code, tier, copies_at_claim, claimed_at}   unique (user_id, character_code, tier)
  banners_v1       {_id: "001", code, name, photo_file_id, required_codes[], created_by, created_at, updated_at}
  user_banners_v1  {_id: user_id, banner_code, equipped_at}                        (one equipped banner per user)
"""
import asyncio
import logging
import re
import secrets
import threading
from datetime import datetime, timedelta, timezone
from html import escape as _esc

import mongo_db
from pymongo import ASCENDING
from pymongo.errors import DuplicateKeyError
from telegram import InlineKeyboardButton, InlineKeyboardMarkup

logger = logging.getLogger(__name__)

IST = timezone(timedelta(hours=5, minutes=30))

# ==========================================================================
# CONFIGURATION (single source of truth)
# ==========================================================================
# Lowest tier first. "copies" = copies of ONE character the user must own right now to claim that tier.
BADGE_TIERS = (
    {"key": "silver", "emoji": "🥈", "name": "Silver", "copies": 2},
    {"key": "gold", "emoji": "🥇", "name": "Gold", "copies": 3},
    {"key": "platinum", "emoji": "🔰", "name": "Platinum", "copies": 4},
    {"key": "diamond", "emoji": "💎", "name": "Diamond", "copies": 5},
)
TIER_BY_KEY = {t["key"]: t for t in BADGE_TIERS}
TIER_RANK = {t["key"]: i for i, t in enumerate(BADGE_TIERS)}

BADGE_CLAIMS = "badge_claims_v1"
BANNERS = "banners_v1"
USER_BANNERS = "user_banners_v1"

BANNER_NAME_MAX = 40
BANNER_MAX_CHARACTERS = 10
PICKER_MAX = 10
CAPTION_LIMIT = 1024          # Telegram photo caption limit
MYSTATS_TIER_NAMES_MAX = 12   # names shown per tier inside /mystats (the full list is behind 🏅 View Badges)

# Exported to bot.py's tables
COMMAND_DESCRIPTIONS = {
    "badges": "View badge tiers and your badges",
    "claimbadge": "Claim a character badge (/claimbadge <code/name>)",
    "banner": "View your banners",
    "usebanner": "Equip a banner (/usebanner <code>)",
    "addbanner": "Staff: create a banner (guided, PM only)",
    "editbanner": "Staff: edit a banner (/editbanner <code>)",
    "delbanner": "Staff: delete a banner (/delbanner <code>)",
    "listbanners": "Staff: list all banners",
}
PUBLIC_COMMANDS = {"badges", "claimbadge", "banner", "usebanner"}
STAFF_COMMANDS = {"addbanner", "editbanner", "delbanner", "listbanners"}   # Owner + Executive (role gate + in-handler check)

# Telegram accepts at most 100 commands per menu (a longer list is rejected completely). The Owner menu lists every
# command, so when a menu is too long these are left OUT of the menu (least essential first). They all keep working
# when typed, and they stay in /help. Only the first entries needed to get down to the limit are ever dropped.
MENU_LIMIT = 100
MENU_TRIM_ORDER = ("listbanners", "delbanner", "editbanner", "addbanner", "scout", "logmappings")


def fit_command_menu(commands, limit=MENU_LIMIT):
    """`commands` = list of BotCommand. Returns the list shortened to `limit` by dropping MENU_TRIM_ORDER names in order."""
    commands = list(commands)
    for name in MENU_TRIM_ORDER:
        if len(commands) <= limit:
            break
        commands = [c for c in commands if c.command != name]
    return commands


# User-owned collections: (collection, field that holds the user id). Used by /deleteuser, /restoreuser, /moveuser.
USER_DATA_SPEC = ((BADGE_CLAIMS, "user_id"), (USER_BANNERS, "_id"))

DENIED_TEXT = "⚠️ Access Denied: You do not have permission to perform this action."
NOT_YOURS_TEXT = "⚠️ This isn't yours. Run the command yourself to get your own buttons."

# ==========================================================================
# Dependency injection (bot.py helpers) - never import bot.py
# ==========================================================================
_deps = {
    "is_owner": lambda uid: False,
    "is_executive": lambda uid: False,
    "conv_timeout": None,
    "safe_reply": None,        # async safe_reply_text(message, text, **kw)  (adds the 👤 header, splits long texts)
    "cancel_all": None,        # bot.cancel_conversation: universal /cancel (clears everything, replies, returns END)
    "mark_success": None,      # mark_success(update) for the log pipeline
    "items_per_page": 5,
}


def bind(**kwargs):
    """Inject bot.py helpers: is_owner, is_executive, conv_timeout, safe_reply, cancel_all, mark_success, items_per_page."""
    _deps.update({k: v for k, v in kwargs.items() if v is not None})


def _is_staff(uid):
    """Owner or Executive - the only roles allowed to manage banners (reuses bot.py's role checks)."""
    try:
        return bool(_deps["is_owner"](uid) or _deps["is_executive"](uid))
    except Exception:
        return False


def _per_page():
    try:
        return max(1, int(_deps.get("items_per_page") or 5))
    except (TypeError, ValueError):
        return 5


# ==========================================================================
# Database helpers (all synchronous; handlers call them through asyncio.to_thread)
# ==========================================================================
_idx_lock = threading.Lock()
_idx_done = False


def ensure_indexes():
    """Idempotent. Called from register() and lazily before the first query."""
    global _idx_done
    with _idx_lock:
        if _idx_done:
            return
        mongo_db.col(BADGE_CLAIMS).create_index(
            [("user_id", ASCENDING), ("character_code", ASCENDING), ("tier", ASCENDING)],
            unique=True, name="uniq_user_char_tier")
        mongo_db.col(BADGE_CLAIMS).create_index([("user_id", ASCENDING)], name="user_id")
        mongo_db.col(BANNERS).create_index([("code", ASCENDING)], unique=True, name="uniq_banner_code")
        mongo_db.col(USER_BANNERS).create_index([("banner_code", ASCENDING)], name="banner_code")
        _idx_done = True


def _col(name):
    if not _idx_done:
        try:
            ensure_indexes()
        except Exception as e:      # the query itself will surface a real database problem
            logger.warning("badge_banner index creation failed: %s", e)
    return mongo_db.col(name)


def _stamp():
    return datetime.now(IST).replace(tzinfo=None).isoformat(timespec="seconds")


def normalize_char_code(value):
    """'1001' -> '1001', '7' -> '0007'; anything else -> None."""
    v = str(value or "").strip()
    if v.isdigit() and 1 <= int(v) <= 9999:
        return v.zfill(4)
    return None


def normalize_banner_code(value):
    """'1' -> '001', '001' -> '001'; anything else -> None."""
    v = str(value or "").strip()
    if v.isdigit() and int(v) >= 1:
        return str(int(v)).zfill(3)
    return None


def owned_codes(uid):
    """Set of character codes the user owns RIGHT NOW (one document per copy in `collections`)."""
    return {str(c) for c in mongo_db.col(mongo_db.COLLECTIONS).distinct("character_code", {"user_id": int(uid)})}


def _names(codes):
    codes = list(codes)
    if not codes:
        return {}
    try:
        return mongo_db.get_character_names(codes)
    except Exception as e:
        logger.warning("character name lookup failed: %s", e)
        return {}


def _label(code, names):
    return f"{_esc(str(names.get(code) or 'Unknown'))} ({code})"


# ---------------- badges ----------------
def eligible_tier(copies):
    """Highest tier whose copy requirement is met, or None."""
    best = None
    for t in BADGE_TIERS:
        if copies >= t["copies"]:
            best = t
    return best


def get_claims(uid):
    return list(_col(BADGE_CLAIMS).find({"user_id": int(uid)}))


def highest_by_character(claims):
    """{character_code: tier_key} using only the HIGHEST claimed tier of each character."""
    best = {}
    for c in claims:
        key = c.get("tier")
        if key not in TIER_RANK:
            continue
        code = str(c.get("character_code"))
        if code not in best or TIER_RANK[key] > TIER_RANK[best[code]]:
            best[code] = key
    return best


def badge_groups(uid):
    """[(tier, [display names])] from the highest tier down; only tiers that have at least one character."""
    best = highest_by_character(get_claims(uid))
    names = _names(best)
    groups = []
    for t in reversed(BADGE_TIERS):
        codes = sorted(c for c, k in best.items() if k == t["key"])
        if codes:
            groups.append((t, [str(names.get(c) or f"Unknown ({c})") for c in codes]))
    return groups


def _character_row(code):
    try:
        return mongo_db.get_character_by_code(code)
    except Exception:
        return None


def resolve_candidates(uid, query):
    """[(row, copies)] for every character matching a code or name (exact name/first/last/recruit name)."""
    rows, seen = [], set()

    def add(row):
        if row and row[0] not in seen:
            seen.add(row[0])
            rows.append(row)

    code = normalize_char_code(query)
    if code:
        add(_character_row(code))
    if not rows:
        for row in mongo_db.find_characters_by_name_parts(query):
            add(row)
        add(mongo_db.find_character_by_recruit_name(query))
    return [(row, mongo_db.count_user_copies(uid, row[0])) for row in rows]


def claim_badge(uid, code):
    """Claim the HIGHEST eligible tier for `code`. Returns a status dict (see claimbadge texts)."""
    row = _character_row(code)
    if not row:
        return {"status": "no_char", "code": code}
    name = row[1]
    copies = mongo_db.count_user_copies(uid, code)
    if copies <= 0:
        return {"status": "not_owned", "code": code, "name": name}
    tier = eligible_tier(copies)
    if tier is None:
        return {"status": "too_few", "code": code, "name": name, "copies": copies}
    held = [c.get("tier") for c in _col(BADGE_CLAIMS).find({"user_id": int(uid), "character_code": str(code)})]
    held_rank = max([TIER_RANK[k] for k in held if k in TIER_RANK], default=-1)
    if held_rank >= TIER_RANK[tier["key"]]:
        return {"status": "already", "code": code, "name": name, "copies": copies,
                "tier": BADGE_TIERS[held_rank], "eligible": tier}
    try:
        _col(BADGE_CLAIMS).insert_one({
            "user_id": int(uid), "character_code": str(code), "tier": tier["key"],
            "copies_at_claim": int(copies), "claimed_at": _stamp()})
    except DuplicateKeyError:        # a concurrent identical claim won the race: same outcome as "already claimed"
        return {"status": "already", "code": code, "name": name, "copies": copies, "tier": tier, "eligible": tier}
    return {"status": "ok", "code": code, "name": name, "copies": copies, "tier": tier}


def tiers_table():
    return "\n".join(f"{t['emoji']} {t['name']} — {t['copies']} copies" for t in BADGE_TIERS)


def claim_text(res):
    s = res["status"]
    who = f"{_esc(str(res.get('name')))} [{res['code']}]" if res.get("name") else f"[{res['code']}]"
    lowest = BADGE_TIERS[0]
    if s == "ok":
        t = res["tier"]
        return (f"✅ {t['emoji']} {t['name']} badge claimed for {who}!\n"
                f"You owned {res['copies']} copies. Badges are permanent: they stay even if you later sell or lose copies.")
    if s == "no_char":
        return "❌ That character does not exist. Use a 4-digit code or a character name."
    if s == "not_owned":
        return f"❌ You don't own {who}. Catch or collect it first."
    if s == "too_few":
        return (f"❌ You need at least {lowest['copies']} copies of {who} to claim a badge "
                f"(you have {res['copies']}).\n\n{tiers_table()}")
    if s == "already":
        t = res["tier"]
        return (f"ℹ️ You already hold the {t['emoji']} {t['name']} badge for {who}.\n"
                f"With {res['copies']} copies you qualify for {res['eligible']['emoji']} {res['eligible']['name']}, "
                f"which you already have. Collect more copies to reach the next tier.")
    return "❌ Could not claim the badge. Please try again."


def badges_overview_html(groups):
    lines = ["🏅 Character Badges", "",
             "Own several copies of the same character to claim a badge:", tiers_table(), "",
             _esc("Use /claimbadge <code/name> - it claims the highest tier you qualify for."), "",
             "📜 Your badges"]
    if not groups:
        lines.append("No badges yet.")
    for t, names in groups:
        lines.append(f"{t['emoji']} {', '.join(_esc(n) for n in names)}")
    return "\n".join(lines)


def badge_section_html(groups):
    """Short section for /mystats."""
    lines = ["🏅 Character Badges"]
    if not groups:
        lines.append("No badges yet. Use /badges to see how to earn them.")
    for t, names in groups:
        shown = [_esc(n) for n in names[:MYSTATS_TIER_NAMES_MAX]]
        extra = len(names) - len(shown)
        tail = f" +{extra} more" if extra > 0 else ""
        lines.append(f"{t['emoji']} {', '.join(shown)}{tail}")
    return "\n".join(lines)


# ---------------- banners ----------------
def _banner_sort_key(d):
    code = str(d.get("_id"))
    return (len(code), code)


def all_banners():
    return sorted(_col(BANNERS).find({}), key=_banner_sort_key)


def get_banner(code):
    return _col(BANNERS).find_one({"_id": str(code)})


def is_unlocked(banner, owned):
    req = [str(c) for c in banner.get("required_codes") or []]
    return bool(req) and all(c in owned for c in req)


def banner_rows(uid):
    """[(banner, unlocked, owned_set, names)] for every banner; computed from CURRENT ownership."""
    owned = owned_codes(uid)
    banners = all_banners()
    names = _names({str(c) for b in banners for c in b.get("required_codes") or []})
    equipped = _col(USER_BANNERS).find_one({"_id": int(uid)})
    eq_code = equipped.get("banner_code") if equipped else None
    rows = []
    for b in banners:
        rows.append({"banner": b, "unlocked": is_unlocked(b, owned), "owned": owned, "names": names,
                     "equipped": eq_code == b["_id"] and is_unlocked(b, owned)})
    return rows


def get_equipped(uid):
    """(banner or None, dropped_banner_name or None). Lazily validates: if the equipped banner was deleted or its
    requirements are no longer met, the user is unequipped (the banner itself is untouched)."""
    doc = _col(USER_BANNERS).find_one({"_id": int(uid)})
    if not doc:
        return None, None
    banner = get_banner(doc.get("banner_code"))
    if banner is not None and is_unlocked(banner, owned_codes(uid)):
        return banner, None
    _col(USER_BANNERS).delete_one({"_id": int(uid), "banner_code": doc.get("banner_code")})
    return None, (banner.get("name") if banner else None)


def equip_banner(uid, code):
    banner = get_banner(code)
    if banner is None:
        return {"status": "no_banner", "code": code}
    owned = owned_codes(uid)
    if not is_unlocked(banner, owned):
        missing = [str(c) for c in banner.get("required_codes") or [] if str(c) not in owned]
        return {"status": "locked", "banner": banner, "names": _names(missing), "missing": missing}
    current = _col(USER_BANNERS).find_one({"_id": int(uid)})
    if current and current.get("banner_code") == banner["_id"]:
        return {"status": "already", "banner": banner}
    _col(USER_BANNERS).update_one({"_id": int(uid)},
                                  {"$set": {"banner_code": banner["_id"], "equipped_at": _stamp()}}, upsert=True)
    return {"status": "ok", "banner": banner}


def unequip_banner(uid):
    return _col(USER_BANNERS).delete_one({"_id": int(uid)}).deleted_count > 0


def parse_character_codes(text):
    """Validate a comma/space separated list of character codes against the database.
    Returns {"codes": [...], "problems": [str]}; problems is empty only if every code is valid and unique."""
    tokens = [t for t in re.split(r"[,\s]+", str(text or "").strip()) if t]
    problems, codes, seen = [], [], set()
    if not tokens:
        return {"codes": [], "problems": ["Send at least one character code."]}
    bad, dup, missing = [], [], []
    for tok in tokens:
        code = normalize_char_code(tok)
        if code is None:
            bad.append(tok)
            continue
        if code in seen:
            dup.append(code)
            continue
        seen.add(code)
        codes.append(code)
    for code in codes:
        if _character_row(code) is None:
            missing.append(code)
    if bad:
        problems.append("Not a valid character code: " + ", ".join(_esc(b) for b in bad))
    if dup:
        problems.append("Duplicate codes: " + ", ".join(sorted(set(dup))))
    if missing:
        problems.append("Character not found: " + ", ".join(missing))
    if len(codes) > BANNER_MAX_CHARACTERS:
        problems.append(f"At most {BANNER_MAX_CHARACTERS} characters per banner.")
    return {"codes": codes, "problems": problems}


def create_banner(draft, creator_id):
    """Revalidate and insert. Returns {"status": "ok", "code"} / {"status": "invalid", "problems"} / {"status": "error"}."""
    check = parse_character_codes(",".join(draft.get("codes") or []))
    if check["problems"] or not draft.get("photo") or not draft.get("name"):
        return {"status": "invalid", "problems": check["problems"] or ["The banner draft is incomplete."]}
    now = _stamp()
    for _ in range(8):
        n = mongo_db.next_sequence(BANNERS)         # atomic counter: a code is never handed out twice or reused
        code = str(n).zfill(3)
        try:
            _col(BANNERS).insert_one({
                "_id": code, "code": code, "name": draft["name"], "photo_file_id": draft["photo"],
                "required_codes": list(check["codes"]), "created_by": int(creator_id),
                "created_at": now, "updated_at": now})
            return {"status": "ok", "code": code}
        except DuplicateKeyError:
            continue
    return {"status": "error"}


def drop_invalid_equips(code):
    """Unequip every user of banner `code` who no longer owns all its characters. Returns the number unequipped."""
    banner = get_banner(code)
    removed = 0
    for doc in list(_col(USER_BANNERS).find({"banner_code": str(code)})):
        uid = doc["_id"]
        if banner is None or not is_unlocked(banner, owned_codes(uid)):
            removed += _col(USER_BANNERS).delete_one({"_id": uid, "banner_code": str(code)}).deleted_count
    return removed


def update_banner(code, fields):
    """Returns (found, unequipped_count). Changing the requirements immediately re-checks everyone who has it equipped."""
    fields = dict(fields, updated_at=_stamp())
    res = _col(BANNERS).update_one({"_id": str(code)}, {"$set": fields})
    if not res.matched_count:
        return False, 0
    removed = drop_invalid_equips(code) if "required_codes" in fields else 0
    return True, removed


def delete_banner(code):
    """Idempotent: (deleted, unequipped). A second call returns (False, 0)."""
    deleted = _col(BANNERS).delete_one({"_id": str(code)}).deleted_count > 0
    removed = _col(USER_BANNERS).delete_many({"banner_code": str(code)}).deleted_count
    return deleted, removed


# ---------------- user data hooks for /deleteuser /restoreuser /moveuser ----------------
def purge_user(uid, session=None):
    """Called inside bot.py's purge transaction."""
    mongo_db.col(BADGE_CLAIMS).delete_many({"user_id": int(uid)}, session=session)
    mongo_db.col(USER_BANNERS).delete_one({"_id": int(uid)}, session=session)


def move_user_data(data, new, session, inserted):
    """Copy-only transfer used by /moveuser. `data` is the validated {collection: [docs]} plan, `inserted` collects
    (collection, _id) pairs so bot.py can undo them without transactions. Never overwrites what the new account has."""
    new = int(new)
    for d in data.get(BADGE_CLAIMS, []):
        nd = {k: v for k, v in d.items() if k != "_id"}
        nd["user_id"] = new
        flt = {"user_id": new, "character_code": nd.get("character_code"), "tier": nd.get("tier")}
        if mongo_db.col(BADGE_CLAIMS).find_one(flt, {"_id": 1}, session=session) is None:   # check first: a duplicate key would abort a transaction
            res = mongo_db.col(BADGE_CLAIMS).insert_one(nd, session=session)
            inserted.append((BADGE_CLAIMS, res.inserted_id))
    for d in data.get(USER_BANNERS, []):
        if mongo_db.col(USER_BANNERS).find_one({"_id": new}, {"_id": 1}, session=session) is None:
            nd = {k: v for k, v in d.items() if k != "_id"}
            nd["_id"] = new
            mongo_db.col(USER_BANNERS).insert_one(nd, session=session)
            inserted.append((USER_BANNERS, new))


# ==========================================================================
# Messaging helpers
# ==========================================================================
async def _reply(msg, text, **kw):
    fn = _deps.get("safe_reply")
    if fn:
        return await fn(msg, text, **kw)
    return await msg.reply_text(text, **kw)


def _chunks(text, limit=4000):
    out, cur = [], ""
    for line in str(text).split("\n"):
        while len(line) > limit:
            if cur:
                out.append(cur)
                cur = ""
            out.append(line[:limit])
            line = line[limit:]
        if len(cur) + len(line) + 1 > limit and cur:
            out.append(cur)
            cur = line
        else:
            cur = f"{cur}\n{line}" if cur else line
    if cur:
        out.append(cur)
    return out or [""]


async def _send_new(message, text, **kw):
    """New message beside a callback's message (works in groups/topics, no 👤 header)."""
    parts = _chunks(text)
    kb = kw.pop("reply_markup", None)
    for i, part in enumerate(parts):
        await message.reply_text(part, reply_markup=kb if i == len(parts) - 1 else None, **kw)


async def _edit(q, text, kb=None):
    try:
        if q.message is not None and getattr(q.message, "photo", None):
            await q.edit_message_caption(caption=text[:CAPTION_LIMIT], parse_mode="HTML", reply_markup=kb)
        else:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception as e:
        if "not modified" not in str(e).lower():
            logger.info("badge_banner edit skipped: %s", e)


def _ok(update):
    fn = _deps.get("mark_success")
    if fn:
        try:
            fn(update)
        except Exception:
            pass


def _btn(label, data):
    return InlineKeyboardButton(label, callback_data=data)


def mystats_keyboard(uid):
    return InlineKeyboardMarkup([[_btn("🏅 View Badges", f"bb:gv:{uid}"), _btn("🎌 View Banners", f"bb:bv:{uid}")]])


def _pager(prefix, uid, page, pages):
    if pages <= 1:
        return None
    row = []
    if page > 0:
        row.append(_btn("◀️ Prev", f"{prefix}:{uid}:{page - 1}"))
    row.append(_btn(f"{page + 1}/{pages}", "bb:noop"))
    if page < pages - 1:
        row.append(_btn("Next ▶️", f"{prefix}:{uid}:{page + 1}"))
    return InlineKeyboardMarkup([row])


# ==========================================================================
# /mystats integration
# ==========================================================================
def _mystats_data(uid):
    groups = badge_groups(uid)
    banner, _dropped = get_equipped(uid)
    return groups, banner


async def send_mystats(update, context, stats_html):
    """Send the finished /mystats text (HTML) with the badge section, the two buttons and, when one is equipped,
    the banner photo on top. Falls back to the plain stats if anything here fails - /mystats must never break."""
    msg = update.effective_message
    uid = update.effective_user.id
    try:
        groups, banner = await asyncio.to_thread(_mystats_data, uid)
        text = f"{stats_html}\n\n{badge_section_html(groups)}"
        kb = mystats_keyboard(uid)
    except Exception as e:
        logger.warning("mystats badge/banner data failed: %s", e)
        await _reply(msg, stats_html, parse_mode="HTML")
        return
    thread = msg.message_thread_id if getattr(msg, "is_topic_message", False) else None
    if banner and banner.get("photo_file_id"):
        try:
            if len(text) <= CAPTION_LIMIT:
                await context.bot.send_photo(chat_id=msg.chat_id, photo=banner["photo_file_id"], caption=text,
                                             parse_mode="HTML", reply_markup=kb, message_thread_id=thread)
                return
            # too long for a caption: photo first, then the full text carrying the buttons
            await context.bot.send_photo(chat_id=msg.chat_id, photo=banner["photo_file_id"], message_thread_id=thread)
        except Exception as e:
            logger.warning("banner photo send failed: %s", e)
    await _reply(msg, text, parse_mode="HTML", reply_markup=kb)


# ==========================================================================
# Badge commands
# ==========================================================================
async def badges_command(update, context):
    uid = update.effective_user.id
    try:
        groups = await asyncio.to_thread(badge_groups, uid)
    except Exception as e:
        logger.error("badges failed: %s", e)
        await _reply(update.effective_message, "❌ Could not load your badges right now. Please try again.")
        return
    await _reply(update.effective_message, badges_overview_html(groups), parse_mode="HTML")
    _ok(update)


async def claimbadge_command(update, context):
    msg, uid = update.effective_message, update.effective_user.id
    query = " ".join(context.args or []).strip()
    if not query:
        await _reply(msg, "Usage: /claimbadge <code or character name>\nExample: /claimbadge 1001\n\n" + tiers_table())
        return
    try:
        cands = await asyncio.to_thread(resolve_candidates, uid, query)
        if not cands:
            await _reply(msg, "❌ Character not found. Use a 4-digit code, first name, last name or full name.")
            return
        owned = [(r, c) for r, c in cands if c > 0]
        if not owned:
            if len(cands) == 1:
                await _reply(msg, claim_text({"status": "not_owned", "code": cands[0][0][0], "name": cands[0][0][1]}),
                             parse_mode="HTML")
            else:
                await _reply(msg, f"❌ You don't own any character matching “{_esc(query)}”.", parse_mode="HTML")
            return
        if len(owned) > 1:
            shown = owned[:PICKER_MAX]
            rows = [[_btn(f"{r[1]} [{r[0]}] ×{c}"[:60], f"bb:pick:{uid}:{r[0]}")] for r, c in shown]
            more = "\n(Showing the first %d - search with a code or the full name to narrow it down.)" % PICKER_MAX \
                if len(owned) > PICKER_MAX else ""
            await _reply(msg, f"🔎 Several characters you own match “{_esc(query)}”. Pick one:{more}",
                         parse_mode="HTML", reply_markup=InlineKeyboardMarkup(rows))
            return
        result = await asyncio.to_thread(claim_badge, uid, owned[0][0][0])
    except Exception as e:
        logger.error("claimbadge failed: %s", e)
        await _reply(msg, "❌ Could not claim the badge right now. Please try again.")
        return
    await _reply(msg, claim_text(result), parse_mode="HTML")
    if result["status"] == "ok":
        _ok(update)


# ==========================================================================
# Banner commands (everyone)
# ==========================================================================
def _banner_page_html(rows, page, uid, dropped=None):
    per = _per_page()
    pages = max(1, -(-len(rows) // per))
    page = min(max(page, 0), pages - 1)
    lines = [f"🎌 Banners (page {page + 1}/{pages})", ""]
    if dropped:
        lines += [f"⚠️ Your banner “{_esc(dropped)}” was unequipped: you no longer own all its characters.", ""]
    if not rows:
        lines.append("No banners exist yet.")
    for i, r in enumerate(rows[page * per:(page + 1) * per], page * per + 1):
        b = r["banner"]
        state = "🔓 Unlocked" if r["unlocked"] else "🔒 Locked"
        eq = "  ⭐ EQUIPPED" if r["equipped"] else ""
        lines.append(f"{i}. {_esc(b['name'])} — {b['_id']}\n   {state}{eq}")
        req = []
        for c in b.get("required_codes") or []:
            mark = "✅" if str(c) in r["owned"] else "❌"
            req.append(f"{mark} {_label(str(c), r['names'])}")
        lines.append("   Needs: " + (", ".join(req) or "—"))
        lines.append("")
    lines.append("Equip an unlocked banner with /usebanner <code>.")
    return "\n".join(lines), _pager("bb:bp", uid, page, pages)


def _banner_view(uid, page, dropped=None):
    rows = banner_rows(uid)
    return _banner_page_html(rows, page, uid, dropped)


def _banner_view_with_check(uid, page):
    _banner, dropped = get_equipped(uid)       # applies the lazy auto-unequip before the list is drawn
    return _banner_view(uid, page, dropped)


async def banner_command(update, context):
    uid = update.effective_user.id
    try:
        text, kb = await asyncio.to_thread(_banner_view_with_check, uid, 0)
    except Exception as e:
        logger.error("banner list failed: %s", e)
        await _reply(update.effective_message, "❌ Could not load banners right now. Please try again.")
        return
    await _reply(update.effective_message, text, parse_mode="HTML", reply_markup=kb)
    _ok(update)


async def usebanner_command(update, context):
    msg, uid = update.effective_message, update.effective_user.id
    arg = (context.args[0] if context.args else "").strip()
    if not arg:
        await _reply(msg, "Usage: /usebanner <banner code>   (see /banner)\n/usebanner off - remove your banner")
        return
    try:
        if arg.lower() in ("off", "none", "remove"):
            gone = await asyncio.to_thread(unequip_banner, uid)
            await _reply(msg, "✅ Banner removed." if gone else "ℹ️ You have no banner equipped.")
            return
        code = normalize_banner_code(arg)
        if code is None:
            await _reply(msg, "❌ Invalid banner code. Use the code shown in /banner, e.g. /usebanner 001")
            return
        res = await asyncio.to_thread(equip_banner, uid, code)
    except Exception as e:
        logger.error("usebanner failed: %s", e)
        await _reply(msg, "❌ Could not equip the banner right now. Please try again.")
        return
    s = res["status"]
    if s == "no_banner":
        await _reply(msg, "❌ No banner with that code. See /banner.")
    elif s == "locked":
        need = ", ".join(_label(c, res["names"]) for c in res["missing"])
        await _reply(msg, f"🔒 “{_esc(res['banner']['name'])}” is locked. You still need: {need}", parse_mode="HTML")
    elif s == "already":
        await _reply(msg, f"ℹ️ “{_esc(res['banner']['name'])}” is already equipped.", parse_mode="HTML")
    else:
        await _reply(msg, f"✅ Banner “{_esc(res['banner']['name'])}” ({res['banner']['_id']}) equipped. "
                          f"It now shows on top of /mystats.", parse_mode="HTML")
        _ok(update)


# ==========================================================================
# Staff: guards
# ==========================================================================
async def _guard_staff(update):
    """Server-side role check (in addition to bot.py's role gate). Replies and returns False when denied."""
    user = update.effective_user
    if user is None or not _is_staff(user.id):
        msg = update.effective_message
        if msg is not None:
            await _reply(msg, DENIED_TEXT)
        elif update.callback_query is not None:
            try:
                await update.callback_query.answer(DENIED_TEXT, show_alert=True)
            except Exception:
                pass
        return False
    return True


async def _guard_private(update):
    chat = update.effective_chat
    if chat is None or chat.type != "private":
        await _reply(update.effective_message, "❌ Use this command in your private chat with the bot.")
        return False
    return True


def _staff_required_lines(banner, names):
    req = [f"• {_label(str(c), names)}" for c in banner.get("required_codes") or []]
    return "\n".join(req) or "• —"


# ==========================================================================
# /addbanner (guided: photo -> name -> character codes -> preview -> confirm)
# ==========================================================================
B_PHOTO, B_NAME, B_CODES, B_CONFIRM = range(4)
_DRAFT = "bb_new"


async def addbanner_start(update, context):
    if not await _guard_staff(update) or not await _guard_private(update):
        return -1
    context.user_data[_DRAFT] = {}
    await _reply(update.effective_message,
                 "🎌 New banner - step 1/3\nSend the banner PHOTO.\n\nSend /cancel to stop.")
    return B_PHOTO


async def addbanner_photo(update, context):
    if not await _guard_staff(update):
        return -1
    msg = update.effective_message
    if not msg.photo:
        await _reply(msg, "❌ Please send the banner as a photo (not a file).")
        return B_PHOTO
    context.user_data.setdefault(_DRAFT, {})["photo"] = msg.photo[-1].file_id
    await _reply(msg, f"✅ Photo saved.\n\nStep 2/3 - send the banner NAME (max {BANNER_NAME_MAX} characters).")
    return B_NAME


def _clean_name(text):
    name = " ".join(str(text or "").split())
    if not name or len(name) > BANNER_NAME_MAX:
        return None
    return name


async def addbanner_name(update, context):
    if not await _guard_staff(update):
        return -1
    name = _clean_name(update.effective_message.text)
    if not name:
        await _reply(update.effective_message, f"❌ The name must be 1-{BANNER_NAME_MAX} characters. Send it again.")
        return B_NAME
    context.user_data.setdefault(_DRAFT, {})["name"] = name
    await _reply(update.effective_message,
                 "✅ Name saved.\n\nStep 3/3 - send the REQUIRED character codes, separated by commas.\n"
                 "Users need ALL of them to unlock the banner.\nExample: 1001, 1002, 1003")
    return B_CODES


def _preview_html(draft, names):
    lines = ["🎌 Banner preview", "",
             f"Name: {_esc(draft['name'])}",
             "Code: assigned automatically when you press Create",
             "Required characters (users need ALL):"]
    lines += [f"• {_label(c, names)}" for c in draft["codes"]]
    return "\n".join(lines)


async def addbanner_codes(update, context):
    if not await _guard_staff(update):
        return -1
    msg = update.effective_message
    draft = context.user_data.get(_DRAFT)
    if not draft or "photo" not in draft or "name" not in draft:
        await _reply(msg, "❌ This setup expired. Run /addbanner again.")
        return -1
    check = await asyncio.to_thread(parse_character_codes, msg.text)
    if check["problems"]:
        await _reply(msg, "❌ " + "\n❌ ".join(check["problems"]) + "\n\nSend the codes again.", parse_mode="HTML")
        return B_CODES
    draft["codes"] = check["codes"]
    draft["token"] = secrets.token_hex(4)
    names = await asyncio.to_thread(_names, check["codes"])
    kb = InlineKeyboardMarkup([[_btn("✅ Create Banner", f"bb:ac:{update.effective_user.id}:{draft['token']}:ok"),
                                _btn("❌ Cancel", f"bb:ac:{update.effective_user.id}:{draft['token']}:no")]])
    await context.bot.send_photo(chat_id=msg.chat_id, photo=draft["photo"], caption=_preview_html(draft, names)[:CAPTION_LIMIT],
                                 parse_mode="HTML", reply_markup=kb)
    return B_CONFIRM


async def addbanner_confirm(update, context):
    q = update.callback_query
    parts = q.data.split(":")            # bb:ac:<uid>:<token>:<ok|no>
    if q.from_user.id != int(parts[2]):
        await q.answer(NOT_YOURS_TEXT, show_alert=True)
        return B_CONFIRM
    if not _is_staff(q.from_user.id):
        await q.answer(DENIED_TEXT, show_alert=True)
        return -1
    draft = context.user_data.get(_DRAFT)
    if not draft or draft.get("token") != parts[3]:
        await q.answer("This preview has expired.", show_alert=True)
        return -1
    context.user_data.pop(_DRAFT, None)  # single use: a second click can never create a second banner
    if parts[4] == "no":
        await q.answer("Cancelled.")
        await _edit(q, "❌ Banner creation cancelled. Nothing was saved.")
        return -1
    await q.answer("Creating…")
    try:
        res = await asyncio.to_thread(create_banner, draft, q.from_user.id)
    except Exception as e:
        logger.error("create banner failed: %s", e)
        await _edit(q, "❌ Database error. Nothing was created. Run /addbanner again.")
        return -1
    if res["status"] == "ok":
        await _edit(q, f"✅ Banner created\nName: {_esc(draft['name'])}\nCode: {res['code']}")
    elif res["status"] == "invalid":
        await _edit(q, "❌ Nothing was created - the data is no longer valid:\n" + "\n".join(res["problems"]) +
                    "\n\nRun /addbanner again.")
    else:
        await _edit(q, "❌ Could not allocate a banner code. Nothing was created. Please try again.")
    return -1


async def _cancel_flow(update, context):
    for key in (_DRAFT, "bb_edit"):
        context.user_data.pop(key, None)
    fn = _deps.get("cancel_all")
    if fn:
        return await fn(update, context)
    await _reply(update.effective_message, "❌ Cancelled.")
    return -1


# ==========================================================================
# /editbanner <code>  (name, photo, requirements)
# ==========================================================================
E_MENU, E_NAME, E_PHOTO, E_REQ = range(10, 14)
_EDIT = "bb_edit"


def _edit_menu(uid, code):
    return InlineKeyboardMarkup([
        [_btn("✏️ Name", f"bb:ed:{uid}:{code}:name"), _btn("🖼 Photo", f"bb:ed:{uid}:{code}:photo")],
        [_btn("🧩 Characters", f"bb:ed:{uid}:{code}:req"), _btn("✔️ Done", f"bb:ed:{uid}:{code}:done")],
    ])


def _banner_summary(code):
    b = get_banner(code)
    if b is None:
        return None, None
    return b, _names(b.get("required_codes") or [])


def _banner_summary_html(b, names):
    return (f"🎌 Banner {b['_id']}\nName: {_esc(b['name'])}\nRequired characters:\n{_staff_required_lines(b, names)}")


async def _show_edit_menu(context, chat_id, uid, code):
    b, names = await asyncio.to_thread(_banner_summary, code)
    if b is None:
        await context.bot.send_message(chat_id=chat_id, text="❌ That banner no longer exists.")
        context.user_data.pop(_EDIT, None)
        return -1
    text = _banner_summary_html(b, names) + "\n\nWhat do you want to change?"
    if b.get("photo_file_id"):
        try:
            await context.bot.send_photo(chat_id=chat_id, photo=b["photo_file_id"], caption=text[:CAPTION_LIMIT],
                                         parse_mode="HTML", reply_markup=_edit_menu(uid, code))
            return E_MENU
        except Exception as e:
            logger.info("edit menu photo failed: %s", e)
    await context.bot.send_message(chat_id=chat_id, text=text, parse_mode="HTML", reply_markup=_edit_menu(uid, code))
    return E_MENU


async def editbanner_start(update, context):
    if not await _guard_staff(update) or not await _guard_private(update):
        return -1
    msg = update.effective_message
    code = normalize_banner_code(context.args[0]) if context.args else None
    if code is None:
        await _reply(msg, "Usage: /editbanner <banner code>   (codes: /listbanners)")
        return -1
    exists = await asyncio.to_thread(get_banner, code)
    if exists is None:
        await _reply(msg, "❌ No banner with that code. See /listbanners.")
        return -1
    context.user_data[_EDIT] = {"code": code}
    return await _show_edit_menu(context, msg.chat_id, update.effective_user.id, code)


async def editbanner_menu(update, context):
    q = update.callback_query
    parts = q.data.split(":")            # bb:ed:<uid>:<code>:<action>
    if q.from_user.id != int(parts[2]):
        await q.answer(NOT_YOURS_TEXT, show_alert=True)
        return E_MENU
    if not _is_staff(q.from_user.id):
        await q.answer(DENIED_TEXT, show_alert=True)
        return -1
    state = context.user_data.get(_EDIT)
    if not state or state.get("code") != parts[3]:
        await q.answer("This menu has expired. Run /editbanner again.", show_alert=True)
        return -1
    action = parts[4]
    await q.answer()
    chat_id = q.message.chat_id
    if action == "done":
        context.user_data.pop(_EDIT, None)
        await context.bot.send_message(chat_id=chat_id, text="✅ Finished editing.")
        return -1
    prompts = {"name": (E_NAME, f"✏️ Send the new NAME (max {BANNER_NAME_MAX} characters)."),
               "photo": (E_PHOTO, "🖼 Send the new PHOTO."),
               "req": (E_REQ, "🧩 Send the new REQUIRED character codes, separated by commas.\n"
                              "Users who no longer own all of them will have the banner unequipped.")}
    nxt, text = prompts[action]
    await context.bot.send_message(chat_id=chat_id, text=text + "\n\nSend /cancel to stop.")
    return nxt


async def _apply_edit(update, context, fields, ok_text):
    state = context.user_data.get(_EDIT)
    if not state:
        await _reply(update.effective_message, "❌ This edit expired. Run /editbanner again.")
        return -1
    found, removed = await asyncio.to_thread(update_banner, state["code"], fields)
    if not found:
        context.user_data.pop(_EDIT, None)
        await _reply(update.effective_message, "❌ That banner no longer exists. Nothing was changed.")
        return -1
    extra = f"\n{removed} user(s) no longer meet the requirements and were unequipped." if removed else ""
    await _reply(update.effective_message, ok_text + extra)
    return await _show_edit_menu(context, update.effective_message.chat_id, update.effective_user.id, state["code"])


async def editbanner_name(update, context):
    if not await _guard_staff(update):
        return -1
    name = _clean_name(update.effective_message.text)
    if not name:
        await _reply(update.effective_message, f"❌ The name must be 1-{BANNER_NAME_MAX} characters. Send it again.")
        return E_NAME
    return await _apply_edit(update, context, {"name": name}, "✅ Name updated.")


async def editbanner_photo(update, context):
    if not await _guard_staff(update):
        return -1
    msg = update.effective_message
    if not msg.photo:
        await _reply(msg, "❌ Please send the banner as a photo (not a file).")
        return E_PHOTO
    return await _apply_edit(update, context, {"photo_file_id": msg.photo[-1].file_id}, "✅ Photo updated.")


async def editbanner_req(update, context):
    if not await _guard_staff(update):
        return -1
    check = await asyncio.to_thread(parse_character_codes, update.effective_message.text)
    if check["problems"]:
        await _reply(update.effective_message, "❌ " + "\n❌ ".join(check["problems"]) + "\n\nSend the codes again.",
                     parse_mode="HTML")
        return E_REQ
    return await _apply_edit(update, context, {"required_codes": check["codes"]}, "✅ Required characters updated.")


# ==========================================================================
# /delbanner <code> and /listbanners
# ==========================================================================
async def delbanner_command(update, context):
    if not await _guard_staff(update):
        return
    msg = update.effective_message
    code = normalize_banner_code(context.args[0]) if context.args else None
    if code is None:
        await _reply(msg, "Usage: /delbanner <banner code>   (codes: /listbanners)")
        return
    b = await asyncio.to_thread(get_banner, code)
    if b is None:
        await _reply(msg, "❌ No banner with that code. See /listbanners.")
        return
    uid = update.effective_user.id
    kb = InlineKeyboardMarkup([[_btn("🗑 Delete", f"bb:dl:{uid}:{code}:ok"), _btn("↩️ Cancel", f"bb:dl:{uid}:{code}:no")]])
    await _reply(msg, f"⚠️ Delete banner “{_esc(b['name'])}” ({code})?\n"
                      f"It will be unequipped from every user who has it. This cannot be undone.",
                 parse_mode="HTML", reply_markup=kb)


def _list_page_html(page):
    banners = all_banners()
    names = _names({str(c) for b in banners for c in b.get("required_codes") or []})
    per = _per_page()
    pages = max(1, -(-len(banners) // per))
    page = min(max(page, 0), pages - 1)
    lines = [f"🎌 All banners (page {page + 1}/{pages})", ""]
    if not banners:
        lines.append("No banners yet. Create one with /addbanner.")
    for b in banners[page * per:(page + 1) * per]:
        lines.append(f"{b['_id']} — {_esc(b['name'])}")
        lines.append(_staff_required_lines(b, names))
        lines.append("")
    return "\n".join(lines), page, pages


async def listbanners_command(update, context):
    if not await _guard_staff(update):
        return
    try:
        text, page, pages = await asyncio.to_thread(_list_page_html, 0)
    except Exception as e:
        logger.error("listbanners failed: %s", e)
        await _reply(update.effective_message, "❌ Could not load banners right now. Please try again.")
        return
    await _reply(update.effective_message, text, parse_mode="HTML",
                 reply_markup=_pager("bb:lb", update.effective_user.id, page, pages))


# ==========================================================================
# Callback router (bb:...). Conversation buttons (bb:ac / bb:ed) are handled inside their conversations;
# anything of those that reaches the router is a stale / already-used button.
# ==========================================================================
async def bb_callback(update, context):
    q = update.callback_query
    if q is None or q.from_user is None or not q.data:
        return
    parts = q.data.split(":")
    kind = parts[1] if len(parts) > 1 else ""
    try:
        if kind == "noop":
            await q.answer()
            return
        uid = int(parts[2])
        if q.from_user.id != uid:
            await q.answer(NOT_YOURS_TEXT, show_alert=True)
            return
        if kind == "gv":                                    # 🏅 View Badges (new message under /mystats)
            groups = await asyncio.to_thread(badge_groups, uid)
            await q.answer()
            await _send_new(q.message, badges_overview_html(groups), parse_mode="HTML")
        elif kind == "hp":                                  # /help -> 🏅 Badges & Banners (members)
            await q.answer()
            await _send_new(q.message, member_help_text())
        elif kind == "bv":                                  # 🎌 View Banners
            text, kb = await asyncio.to_thread(_banner_view_with_check, uid, 0)
            await q.answer()
            await _send_new(q.message, text, parse_mode="HTML", reply_markup=kb)
        elif kind == "bp":                                  # banner list pagination (edits in place)
            text, kb = await asyncio.to_thread(_banner_view_with_check, uid, int(parts[3]))
            await q.answer()
            await _edit(q, text, kb)
        elif kind == "pick":                                # character picker for /claimbadge
            result = await asyncio.to_thread(claim_badge, uid, parts[3])
            await q.answer()
            await _edit(q, claim_text(result))
        elif kind == "lb":                                  # staff: /listbanners pagination
            if not _is_staff(uid):
                await q.answer(DENIED_TEXT, show_alert=True)
                return
            text, page, pages = await asyncio.to_thread(_list_page_html, int(parts[3]))
            await q.answer()
            await _edit(q, text, _pager("bb:lb", uid, page, pages))
        elif kind == "dl":                                  # staff: /delbanner confirmation
            await _delete_callback(q, uid, parts[3], parts[4])
        elif kind in ("ac", "ed"):
            await q.answer("This button has already been used or has expired.", show_alert=True)
        else:
            await q.answer()
    except Exception as e:
        logger.error("badge_banner callback failed (%s): %s", q.data, e)
        try:
            await q.answer("❌ Something went wrong. Please try again.", show_alert=True)
        except Exception:
            pass


async def _delete_callback(q, uid, code, action):
    if not _is_staff(uid):
        await q.answer(DENIED_TEXT, show_alert=True)
        return
    if action == "no":
        await q.answer("Cancelled.")
        await _edit(q, "↩️ Deletion cancelled. The banner was kept.")
        return
    deleted, removed = await asyncio.to_thread(delete_banner, code)
    if not deleted:
        await q.answer("Already deleted.", show_alert=True)
        await _edit(q, f"ℹ️ Banner {code} no longer exists.")
        return
    await q.answer("Deleted.")
    tail = f"\n{removed} user(s) were unequipped." if removed else ""
    await _edit(q, f"🗑 Banner {code} deleted.{tail}")


# ==========================================================================
# Help text (owned by this module)
# ==========================================================================
HELP_KEY = "badgebanner"
HELP_LABEL = "🏅 Badges"        # short on purpose: the 3-column help grid truncates long labels

PUBLIC_HELP_SECTION = (
    "🏅 Badges & Banners\n"
    "/badges — View badge tiers and your badges\n"
    "/claimbadge <code/name> — Claim the highest badge you qualify for\n"
    "/banner — View your banners\n"
    "/usebanner <code> — Equip a banner you have unlocked\n\n"
)


def help_page_text():
    entries = [
        ("/addbanner", "Create a banner (guided, PM only): photo, name, required character codes, preview, ✅ Create"),
        ("/editbanner <code>", "Edit a banner's name, photo or required characters (PM only). "
                               "Users who no longer qualify are unequipped"),
        ("/delbanner <code>", "Delete a banner (asks to confirm; unequips everyone who has it)"),
        ("/listbanners", "List every banner with its code and required characters (paginated)"),
        ("/badges", "Badge tiers and your own badges (public)"),
        ("/claimbadge <code/name>", "Claim the highest badge you qualify for (public)"),
        ("/banner", "Your banners: locked / unlocked / equipped (public)"),
        ("/usebanner <code>", "Equip an unlocked banner; /usebanner off removes it (public)"),
    ]
    lines = ["🏅 Badges & Banners (Owner & Executive)", "", "📌 Overview",
             "Badges reward owning several copies of one character; banners are profile images that unlock when a "
             "user owns ALL of their required characters and show on top of /mystats.",
             "", "⌨️ Commands & usage"]
    for n, (syntax, desc) in enumerate(entries, 1):
        lines.append(f"{n}. {syntax} - {desc}")
    lines += ["", "🏅 Tiers: " + ", ".join(f"{t['emoji']} {t['name']} {t['copies']}" for t in BADGE_TIERS) + " copies."]
    return "\n".join(lines)


def member_help_text():
    """Page opened by the 🏅 Badges & Banners button of /help (for every member)."""
    return "\n".join([
        "🏅 Badges & Banners", "",
        "🏅 Badges",
        "Own several copies of the same character, then claim a badge for it:",
        tiers_table(),
        "• /badges - tiers and your badges",
        "• /claimbadge <code/name> - claims the highest tier you qualify for",
        "Badges are permanent, even if you later sell or trade the copies.", "",
        "🎌 Banners",
        "A banner is a profile picture that unlocks when you own ALL of its required characters.",
        "• /banner - see every banner, what it needs and what is unlocked",
        "• /usebanner <code> - equip an unlocked banner (/usebanner off removes it)",
        "Your banner shows on top of /mystats. If you lose a required character it is unequipped, "
        "and it comes back when you own the character again.", "",
        "📊 /mystats shows your badges and has 🏅 View Badges / 🎌 View Banners buttons."])


def help_button_row(uid):
    """One full-width button row for bot.py's /help keyboard."""
    return [_btn("🏅 Badges & Banners", f"bb:hp:{uid}")]


def help_module():
    """(key, label, text) in the shape of bot.py's HELP_MODULES entries."""
    return (HELP_KEY, HELP_LABEL, help_page_text())


# ==========================================================================
# Registration
# ==========================================================================
def register(app):
    """Attach every badge/banner handler. Call bind(...) first. Safe to call once at start-up."""
    from telegram.ext import CallbackQueryHandler, CommandHandler, ConversationHandler, MessageHandler, filters
    try:
        ensure_indexes()
    except Exception as e:          # never block the bot from starting; indexes are retried on first use
        logger.warning("badge_banner: index creation deferred (%s)", e)
    text = filters.TEXT & ~filters.COMMAND
    timeout = _deps.get("conv_timeout")

    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("addbanner", addbanner_start)],
        states={
            B_PHOTO: [MessageHandler(filters.PHOTO, addbanner_photo), MessageHandler(text, addbanner_photo)],
            B_NAME: [MessageHandler(text, addbanner_name)],
            B_CODES: [MessageHandler(text, addbanner_codes)],
            B_CONFIRM: [CallbackQueryHandler(addbanner_confirm, pattern=r"^bb:ac:\d+:[0-9a-f]{8}:(ok|no)$")],
        },
        fallbacks=[CommandHandler("cancel", _cancel_flow)],
        allow_reentry=True,
        conversation_timeout=timeout,
    ))
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("editbanner", editbanner_start)],
        states={
            E_MENU: [CallbackQueryHandler(editbanner_menu, pattern=r"^bb:ed:\d+:\d+:(name|photo|req|done)$")],
            E_NAME: [MessageHandler(text, editbanner_name)],
            E_PHOTO: [MessageHandler(filters.PHOTO, editbanner_photo), MessageHandler(text, editbanner_photo)],
            E_REQ: [MessageHandler(text, editbanner_req)],
        },
        fallbacks=[CommandHandler("cancel", _cancel_flow)],
        allow_reentry=True,
        conversation_timeout=timeout,
    ))
    for name, callback in (("badges", badges_command), ("claimbadge", claimbadge_command),
                           ("banner", banner_command), ("usebanner", usebanner_command),
                           ("delbanner", delbanner_command), ("listbanners", listbanners_command)):
        app.add_handler(CommandHandler(name, callback))
    app.add_handler(CallbackQueryHandler(bb_callback, pattern=r"^bb:"))
