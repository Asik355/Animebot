"""
Festival system for the Anime Character Catcher bot: timed festivals (Diwali, Independence Day, Christmas, ...)
with owner-made QUESTS whose rewards can be Berrys, Special Stones, a hidden EVENT CARD and a hidden EVENT BANNER.

EVERYTHING lives in this file (same pattern as badge_banner.py / fusion.py / theme.py). bot.py only
  * imports this module,
  * calls  festival.bind(...)  and  festival.register(app)  in main(),
  * adds the command names / help text this module exports to its tables,
  * calls  await festival.record(...)  after a real catch / /daily,
  * filters hidden event cards out of its character lists / searches with  festival.filter_hidden(...),
  * lists this module's user collections in the delete / restore / move-user helpers.
bot.py is never imported here: everything it owns is injected through bind().

HOW IT WORKS
  Festival   name, wish phrase (e.g. "Happy Diwali"), start and end (IST). Quests only count inside this window.
  Quest      type + target + rewards. Types:
               wish_send     reply to N DIFFERENT people with the festival phrase
               wish_receive  receive the phrase (as a reply) from N DIFFERENT people
               catch         catch N characters (optionally only one rarity)
               daily         claim /daily N times
               wish_pay      PER-WISH PAYOUT: every wish to a different person pays Berrys / Stones right away
                             (e.g. 100 Berrys per "Happy Diwali" reply), up to a per-player cap; the wished person can
                             be paid too. Like a redeem code you can use many times, but one payout per person.
             Reward = any mix of Berrys, Special Stones, one card (character code), one banner (photo + name).
  /addtempchar  creates a TEMPORARY event character (hidden from every list from the first second, only given by quests).
  Temporary  A quest can only be completed while its festival is live. Everything already earned is PERMANENT.
  Hidden     The event card is hidden from the character list, shop, spawns and name searches; it only shows in the
             collection of the people who earned it. The event banner is hidden from the public banner list; it only
             shows in the banner list of the people who earned it (see the small hooks in badge_banner.py).

Collections (created lazily, indexes are idempotent):
  festivals_v1          {_id: "001", name, phrase, phrase_norm, start_at, end_at, created_by, created_at, updated_at}
  festival_quests_v1    {_id: "Q001", festival_id, qtype, target, rarity|None, reward{berrys,stones,card,banner}, ...}
  festival_progress_v1  {_id: "<uid>:<qid>", user_id, quest_id, festival_id, count}      (catch / daily counters)
  festival_wishes_v1    {festival_id, sender_id, receiver_id, at}   unique (festival, sender, receiver)
  festival_claims_v1    {_id: "<uid>:<qid>", user_id, quest_id, claimed_at}   (one reward claim per quest: _id is unique)
  festival_paid_v1      {_id: "<uid>:<qid>:<s|r>:<other uid>", user_id, quest_id, side}   (wish_pay payouts, one per person)
  festival_grants_v1    {_id: "<uid>:<token>", user_id, kind: "banner", token: "FB<code>", quest_id, at}  (permanent)
  festival_cards_v1     {_id: "<character code>", festival_id, at}                (cards hidden from the public lists)
  banners_v1            event banners are stored here with  festival_id  and  required_codes [["FB<code>"]]
"""
import asyncio
import logging
import random
import re
import secrets
import threading
import time
from datetime import datetime, timedelta, timezone
from html import escape as _esc, unescape as _unesc
from urllib.parse import quote as _urlquote

import mongo_db
from pymongo import ASCENDING
from pymongo.errors import DuplicateKeyError
from telegram import InlineKeyboardButton, InlineKeyboardMarkup

logger = logging.getLogger(__name__)

IST = timezone(timedelta(hours=5, minutes=30))

# ==========================================================================
# CONFIGURATION
# ==========================================================================
FESTIVALS = "festivals_v1"
QUESTS = "festival_quests_v1"
PROGRESS = "festival_progress_v1"
WISHES = "festival_wishes_v1"
CLAIMS = "festival_claims_v1"
GRANTS = "festival_grants_v1"
PAID = "festival_paid_v1"
SETTINGS = "festival_settings_v1"       # {_id: "special_tier", symbol}
FBANNER_SEQ = "festival_banners_v1"     # counter name of the special banner series (01, 02, ...)
SPECIAL = "Special"                     # name of the special rarity tier
SYMBOL_MAX = 8
FBANNER_MAX = 99
CARDS = "festival_cards_v1"
BANNERS = "banners_v1"          # badge_banner.py's collection (event banners are stored there, flagged festival_id)
REF_SETTINGS = "referral_settings_v1"   # {_id: "config", enabled, tiers: {bronze: {...}, ...}}  (Owner settings from /boxes)
REFERRALS = "referrals_v1"              # {_id: invitee user id, inviter, token, ts}  one row per new member, never counted twice
REF_LINKS = "referral_links_v1"         # {_id: link token, user_id, ts}  a member can generate new links; old ones keep working
REF_CLAIMS = "referral_claims_v1"       # {_id: "<user id>:<tier>", user_id, tier, boxes, ...}  unique id = one claim per tier
REF_OPENS = "referral_opens_v1"         # {user_id, tier, text, ts}  history of opened boxes

NAME_MAX = 40
PHRASE_MIN, PHRASE_MAX = 2, 40
TARGET_MAX = 1000
BERRYS_MAX = 1_000_000
STONES_MAX = 10_000
CAPTION_LIMIT = 1024
BANNER_MAX_CODE = 999

# quest type -> (emoji, button label)
QUEST_TYPES = {
    "wish_send": ("🪔", "Wish people"),
    "wish_receive": ("💌", "Receive wishes"),
    "catch": ("🎯", "Catch characters"),
    "daily": ("📅", "Claim /daily"),
    "wish_pay": ("💰", "Pay per wish"),
}
COUNTED_TYPES = ("catch", "daily")          # progress comes from  festival.record(...)  calls made by bot.py
DEFAULT_RARITIES = ("Common", "Rare", "Epic", "Legendary", "Mythical", "Celestial")

COMMAND_DESCRIPTIONS = {
    "quests": "View festival quests and your progress",
    "invite": "Your invite link, progress and Mystery Boxes",
    "boxes": "Owner: invite system and Mystery Box settings (buttons)",
    "special": "See every special festival character and banner",
    "specialtier": "Owner: set the symbol of the Special tier",
    "festival": "Owner: open the Festival Manager (buttons)",
    "addfestival": "Owner: create a festival (guided, PM only)",
    "festivals": "See running and upcoming festivals",
    "editfestival": "Owner: edit a festival (/editfestival <code>)",
    "delfestival": "Owner: delete a festival (/delfestival <code>)",
    "addtempchar": "Owner: create a temporary event character (hidden card)",
    "addquest": "Owner: add a quest (/addquest <festival code>)",
    "editquest": "Owner: edit a quest (/editquest <quest id>)",
    "delquest": "Owner: delete a quest (/delquest <quest id>)",
}
PUBLIC_COMMANDS = {"quests", "special", "festivals", "invite"}
OWNER_COMMANDS = {"boxes", "festival", "specialtier", "addfestival", "editfestival", "delfestival", "addtempchar", "addquest", "editquest", "delquest"}

# User-owned collections: (collection, field holding the user id). Used by /deleteuser, /restoreuser, /moveuser.
USER_DATA_SPEC = ((PROGRESS, "user_id"), (CLAIMS, "user_id"), (GRANTS, "user_id"), (PAID, "user_id"),
                  (REFERRALS, "inviter"), (REF_LINKS, "user_id"), (REF_CLAIMS, "user_id"), (REF_OPENS, "user_id"))

DENIED_TEXT = "⚠️ Access Denied: You do not have permission to perform this action."
NOT_YOURS_TEXT = "⚠️ This isn't yours. Run the command yourself to get your own buttons."

# ==========================================================================
# Dependency injection (bot.py helpers) - never import bot.py
# ==========================================================================
_deps = {
    "is_owner": lambda uid: False,
    "conv_timeout": None,
    "safe_reply": None,         # async safe_reply_text(message, text, **kw)
    "cancel_all": None,         # bot.cancel_conversation (universal /cancel)
    "mark_success": None,
    "save_user": None,          # async save_user_async(telegram_user) - makes sure the sender has a profile row
    "timestamp": None,          # bot.timestamp() - the stamp format add_collection expects
    "rarities": DEFAULT_RARITIES,
    "symbols": None,            # bot.SYMBOL (the rarity -> symbol dict); festival adds / removes the "Special" entry
    "items_per_page": 5,
}


def bind(**kwargs):
    """Inject bot.py helpers: is_owner, conv_timeout, safe_reply, cancel_all, mark_success, save_user, timestamp, rarities,
    symbols (bot.SYMBOL), items_per_page."""
    _deps.update({k: v for k, v in kwargs.items() if v is not None})


def _is_owner(uid):
    try:
        return bool(_deps["is_owner"](uid))
    except Exception:
        return False


def _rarities():
    try:
        return tuple(str(r) for r in _deps.get("rarities") or DEFAULT_RARITIES)
    except Exception:
        return DEFAULT_RARITIES


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
        mongo_db.col(WISHES).create_index(
            [("festival_id", ASCENDING), ("sender_id", ASCENDING), ("receiver_id", ASCENDING)],
            unique=True, name="uniq_festival_pair")
        mongo_db.col(WISHES).create_index([("festival_id", ASCENDING), ("receiver_id", ASCENDING)], name="festival_receiver")
        mongo_db.col(QUESTS).create_index([("festival_id", ASCENDING)], name="festival_id")
        mongo_db.col(PROGRESS).create_index([("user_id", ASCENDING)], name="user_id")
        mongo_db.col(CLAIMS).create_index([("user_id", ASCENDING)], name="user_id")
        mongo_db.col(GRANTS).create_index([("user_id", ASCENDING)], name="user_id")
        mongo_db.col(PAID).create_index([("user_id", ASCENDING), ("quest_id", ASCENDING), ("side", ASCENDING)], name="user_quest_side")
        mongo_db.col(REFERRALS).create_index([("inviter", ASCENDING)], name="inviter")
        mongo_db.col(REF_LINKS).create_index([("user_id", ASCENDING)], name="user_id")
        mongo_db.col(REF_CLAIMS).create_index([("user_id", ASCENDING)], name="user_id")
        mongo_db.col(REF_OPENS).create_index([("user_id", ASCENDING), ("ts", ASCENDING)], name="user_ts")
        _idx_done = True


def _col(name):
    if not _idx_done:
        try:
            ensure_indexes()
        except Exception as e:      # the query itself will surface a real database problem
            logger.warning("festival index creation failed: %s", e)
    return mongo_db.col(name)


def _now():
    return datetime.now(IST).replace(tzinfo=None)


def _iso(dt):
    return dt.isoformat(timespec="seconds")


def _stamp():
    return _iso(_now())


def _grant_stamp():
    fn = _deps.get("timestamp")
    if fn:
        try:
            return fn()
        except Exception:
            pass
    return _stamp()


_DATE_RE = re.compile(r"^\s*(\d{1,2})\D+(\d{1,2})\D+(\d{4}|\d{2})\D+(\d{1,2})\D+(\d{2})\s*(?:([ap])\.?\s*m\.?)?\s*$", re.I)


def parse_when(text, allow_now=False):
    """'DD-MM-YY h:mm am/pm' (e.g. 10-11-26 4:30am) or 24-hour 'DD-MM-YYYY HH:MM' (IST; any separators, 2- or 4-digit year) -> ISO string, or None. 'now' only if allowed."""
    t = str(text or "").strip()
    if allow_now and t.casefold() == "now":
        return _stamp()
    m = _DATE_RE.match(t)
    if not m:
        return None
    d, mo, y, h, mi = (int(x) for x in m.groups()[:5])
    ampm = (m.group(6) or "").lower()
    if y < 100:
        y += 2000
    if ampm:
        if not 1 <= h <= 12:
            return None
        h = h % 12 + (12 if ampm == "p" else 0)
    try:
        return _iso(datetime(y, mo, d, h, mi))
    except ValueError:
        return None


def fmt_when(iso):
    try:
        return datetime.fromisoformat(iso).strftime("%d %b %Y, %I:%M %p") + " IST"
    except (TypeError, ValueError):
        return str(iso)


def normalize_fcode(value):
    v = str(value or "").strip()
    return str(int(v)).zfill(3) if v.isdigit() and 1 <= int(v) <= 999 else None


def normalize_qid(value):
    v = str(value or "").strip().upper().lstrip("Q")
    return "Q" + str(int(v)).zfill(3) if v.isdigit() and int(v) >= 1 else None


def normalize_char_code(value):
    v = str(value or "").strip()
    return v.zfill(4) if v.isdigit() and 1 <= int(v) <= 9999 else None


def normalize_banner_code(value):
    v = str(value or "").strip()
    return str(int(v)).zfill(3) if v.isdigit() and 1 <= int(v) <= BANNER_MAX_CODE else None


def banner_token(code):
    """The pseudo character code a user 'owns' when they earned banner `code` (see badge_banner.owned_codes)."""
    return "FB" + str(code)


def _norm(text):
    """casefold + remove punctuation + collapse spaces: 'Happy  Diwali!!' -> 'happy diwali'."""
    t = re.sub(r"[^\w\s]|_", " ", str(text or "").casefold())
    return " ".join(t.split())


def phrase_in(text_norm, phrase_norm):
    return bool(phrase_norm) and f" {phrase_norm} " in f" {text_norm} "


def status_of(f, now_iso=None):
    now_iso = now_iso or _stamp()
    if now_iso < f.get("start_at", ""):
        return "upcoming"
    if now_iso >= f.get("end_at", ""):
        return "ended"
    return "live"


def _character_row(code):
    try:
        return mongo_db.get_character_by_code(code)
    except Exception:
        return None


# ---------------- Special tier symbol ----------------
_sym = {"ts": 0.0, "val": None}


def special_symbol():
    """The Special tier's symbol, or None until the owner has sent one (cached; never raises)."""
    if _sym["ts"] and time.monotonic() - _sym["ts"] < 30:
        return _sym["val"]
    try:
        doc = _col(SETTINGS).find_one({"_id": "special_tier"})
    except Exception as e:
        logger.warning("festival symbol lookup failed: %s", e)
        return _sym["val"]
    _sym["val"], _sym["ts"] = ((doc or {}).get("symbol") or None), time.monotonic()
    return _sym["val"]


def apply_symbol():
    """Put the Special tier into bot.SYMBOL (so every rarity label shows its symbol) or take it out if unset."""
    syms = _deps.get("symbols")
    if syms is None:
        return
    sym = special_symbol()
    if sym:
        syms[SPECIAL] = sym
    else:
        syms.pop(SPECIAL, None)


def set_special_symbol(sym):
    _col(SETTINGS).update_one({"_id": "special_tier"}, {"$set": {"symbol": sym, "updated_at": _stamp()}}, upsert=True)
    _sym["ts"] = 0.0
    apply_symbol()


def _clean_symbol(text):
    t = str(text or "").strip()
    if not t or len(t) > SYMBOL_MAX or any(ch.isspace() for ch in t) or t.startswith("/"):
        return None
    return t


# ---------------- festivals / quests ----------------
def get_festival(code):
    return _col(FESTIVALS).find_one({"_id": str(code)})


def all_festivals():
    return sorted(_col(FESTIVALS).find({}), key=lambda f: (f.get("start_at", ""), f["_id"]))


def _qkey(q):
    return (len(q["_id"]), q["_id"])


def quests_of(festival_id):
    return sorted(_col(QUESTS).find({"festival_id": str(festival_id)}), key=_qkey)


def get_quest(qid):
    return _col(QUESTS).find_one({"_id": str(qid)})


_live = {"ts": 0.0, "val": []}
_LIVE_TTL = 5.0


def invalidate():
    _live["ts"] = 0.0


def live_festivals():
    """[(festival, [quests])] of festivals whose window is open right now (cached a few seconds)."""
    if _live["ts"] and time.monotonic() - _live["ts"] < _LIVE_TTL:
        return _live["val"]
    now = _stamp()
    out = []
    for f in _col(FESTIVALS).find({}):
        if status_of(f, now) == "live":
            qs = quests_of(f["_id"])
            if qs:
                out.append((f, qs))
    _live["val"], _live["ts"] = out, time.monotonic()
    return out


def create_festival(draft, creator_id):
    n = mongo_db.next_sequence(FESTIVALS)
    if n > 999:
        return None
    now = _stamp()
    code = str(n).zfill(3)
    _col(FESTIVALS).insert_one({
        "_id": code, "code": code, "name": draft["name"], "phrase": draft["phrase"], "phrase_norm": _norm(draft["phrase"]),
        "start_at": draft["start"], "end_at": draft["end"], "created_by": int(creator_id),
        "created_at": now, "updated_at": now})
    invalidate()
    return code


def update_festival(code, fields):
    fields = dict(fields, updated_at=_stamp())
    if "phrase" in fields:
        fields["phrase_norm"] = _norm(fields["phrase"])
    res = _col(FESTIVALS).update_one({"_id": str(code)}, {"$set": fields})
    invalidate()
    return bool(res.matched_count)


def delete_festival(code):
    """Removes the festival, its quests, progress and wishes. Claims, grants, banners and cards that people already
    earned are NOT touched (earned things are permanent)."""
    code = str(code)
    qids = [q["_id"] for q in _col(QUESTS).find({"festival_id": code}, {"_id": 1})]
    deleted = _col(FESTIVALS).delete_one({"_id": code}).deleted_count > 0
    _col(QUESTS).delete_many({"festival_id": code})
    if qids:
        _col(PROGRESS).delete_many({"quest_id": {"$in": qids}})
        _col(PAID).delete_many({"quest_id": {"$in": qids}})
    _col(WISHES).delete_many({"festival_id": code})
    invalidate()
    return deleted, len(qids)


def delete_quest(qid):
    qid = str(qid)
    deleted = _col(QUESTS).delete_one({"_id": qid}).deleted_count > 0
    _col(PROGRESS).delete_many({"quest_id": qid})
    _col(PAID).delete_many({"quest_id": qid})
    invalidate()
    return deleted


# ---------------- hidden event cards ----------------
_hidden = {"ts": 0.0, "val": frozenset()}
_HIDDEN_TTL = 15.0


def hidden_codes():
    """Character codes of event cards (hidden from every public list). Cached; never raises."""
    if _hidden["ts"] and time.monotonic() - _hidden["ts"] < _HIDDEN_TTL:
        return _hidden["val"]
    try:
        val = frozenset(str(d["_id"]) for d in _col(CARDS).find({}, {"_id": 1}))
    except Exception as e:
        logger.warning("festival hidden-card lookup failed: %s", e)
        return _hidden["val"]
    _hidden["val"], _hidden["ts"] = val, time.monotonic()
    return val


def is_hidden(code):
    return str(code) in hidden_codes()


def filter_hidden(rows):
    """rows = character tuples (code first). Returns the list without event cards."""
    hide = hidden_codes()
    rows = list(rows or [])
    return [r for r in rows if str(r[0]) not in hide] if hide else rows


def register_card(code, festival_id):
    _col(CARDS).update_one({"_id": str(code)}, {"$set": {"festival_id": str(festival_id or ""), "at": _stamp()}}, upsert=True)
    _hidden["ts"] = 0.0


# ---------------- event banners ----------------
def create_festival_banner(name, photo, festival_id, creator_id):
    """Insert a SPECIAL banner into badge_banner's collection with its own 2-digit code series 01, 02, ... (normal
    banners always have 3 digits, 001-999). Returns its code, or None when the 99 special codes ran out."""
    now = _stamp()
    for _ in range(8):
        n = mongo_db.next_sequence(FBANNER_SEQ)
        if n > FBANNER_MAX:
            return None
        code = str(n).zfill(2)
        try:
            _col(BANNERS).insert_one({
                "_id": code, "code": code, "name": name, "photo_file_id": photo,
                "required_codes": [[banner_token(code)]], "festival_id": str(festival_id),
                "created_by": int(creator_id), "created_at": now, "updated_at": now})
            return code
        except DuplicateKeyError:
            continue
    return None


def get_banner(code):
    return _col(BANNERS).find_one({"_id": str(code)})


# ---------------- quests: labels, progress, rewards ----------------
def quest_label(f, q):
    t, n = q["qtype"], int(q["target"])
    phrase = _esc(str(f.get("phrase") or ""))
    emoji = QUEST_TYPES.get(t, ("🎁", ""))[0]
    if t == "wish_send":
        return f"{emoji} Wish “{phrase}” to {n} " + ("person" if n == 1 else "different people") + " (reply to them)"
    if t == "wish_receive":
        return f"{emoji} Get “{phrase}” wishes from {n} " + ("person" if n == 1 else "different people")
    if t == "catch":
        return f"{emoji} Catch {n} " + (f"{_esc(q['rarity'])} " if q.get("rarity") else "") + "characters"
    if t == "daily":
        return f"{emoji} Claim /daily {n} time" + ("" if n == 1 else "s")
    if t == "wish_pay":
        return f"{emoji} Wish “{phrase}” to different people - paid for every wish (up to {n} wishes)"
    return f"{emoji} {t} ×{n}"


def reward_lines(reward):
    r = reward or {}
    lines = []
    if r.get("berrys"):
        lines.append(f"🪙 {int(r['berrys'])} Berrys")
    if r.get("stones"):
        n = int(r["stones"])
        lines.append(f"💎 {n} Special Stone" + ("" if n == 1 else "s"))
    if r.get("card"):
        row = _character_row(r["card"])
        lines.append(f"🎭 {_esc(str(row[1]))} [{r['card']}]" if row else f"🎭 Character [{r['card']}]")
    if r.get("banner"):
        b = get_banner(r["banner"])
        lines.append(f"🎌 Banner “{_esc(str((b or {}).get('name') or '?'))}” ({r['banner']}) - equip with /usebanner {r['banner']}")
    return lines


def quest_rewards_text(q):
    """One-line reward text for lists. wish_pay rewards are 'per wish'."""
    lines = reward_lines(q.get("reward"))
    if q["qtype"] == "wish_pay":
        parts = [", ".join(lines) + " per wish"] if lines else []
        rb = int(q.get("receiver_berrys") or 0)
        if rb:
            parts.append(f"🪙 {rb} Berrys to the person you wish")
        return "; ".join(parts) or "-"
    return ", ".join(lines) or "-"


def reward_short_lines(reward):
    """Compact reward lines for lists (no pictures, no commands)."""
    r = reward or {}
    lines = []
    if r.get("berrys"):
        lines.append(f"🪙 {int(r['berrys'])} Berrys")
    if r.get("stones"):
        n = int(r["stones"])
        lines.append(f"💎 {n} Special Stone" + ("" if n == 1 else "s"))
    if r.get("card"):
        row = _character_row(r["card"])
        lines.append(f"🎭 {_esc(str(row[1]))}" if row else f"🎭 [{r['card']}]")
    if r.get("banner"):
        b = get_banner(r["banner"])
        lines.append(f"🎌 {_esc(str((b or {}).get('name') or r['banner']))}")
    return lines


def quest_rewards_short(q):
    lines = reward_short_lines(q.get("reward"))
    if q["qtype"] == "wish_pay":
        parts = [", ".join(lines) + " per wish"] if lines else []
        rb = int(q.get("receiver_berrys") or 0)
        if rb:
            parts.append(f"🪙 {rb} Berrys to the person you wish")
        return "; ".join(parts) or "-"
    return ", ".join(lines) or "-"


def festival_reward_lines(qs):
    """'🎁 ...' lines of every reward of a festival (no quest text), duplicates removed."""
    out, seen = [], set()
    for q in qs:
        t = quest_rewards_short(q)
        if t and t != "-" and t not in seen:
            seen.add(t)
            out.append("🎁 " + t)
    return out


def progress_line(uid, f, q):
    """'🪔 Diwali Quest: 2/20' (capped at the target)."""
    target = int(q["target"])
    n = min(quest_count(uid, f, q), target)
    label = {"wish_send": "🪔 Sent", "wish_receive": "💌 Received", "wish_pay": "💰 Paid wishes"}.get(q["qtype"])
    if label:
        return f"{label} {n}/{target}"
    return f"{QUEST_TYPES.get(q['qtype'], ('🎁',))[0]} {_esc(str(f['name']))} Quest: {n}/{target}"


def progress_lines(uid, hits, skip_ids=()):
    """Progress lines for [(festival, quest)] hits, leaving out quests that just completed or were already paid out."""
    out = []
    for f, q in hits:
        if q["_id"] in skip_ids:
            continue
        if q["qtype"] != "wish_pay" and is_claimed(uid, q["_id"]):
            continue
        out.append(progress_line(uid, f, q))
    return out


def quest_count(uid, f, q):
    uid = int(uid)
    t = q["qtype"]
    if t == "wish_send":
        return _col(WISHES).count_documents({"festival_id": f["_id"], "sender_id": uid})
    if t == "wish_receive":
        return _col(WISHES).count_documents({"festival_id": f["_id"], "receiver_id": uid})
    if t == "wish_pay":
        return _col(PAID).count_documents({"user_id": uid, "quest_id": q["_id"], "side": "s"})
    doc = _col(PROGRESS).find_one({"_id": f"{uid}:{q['_id']}"})
    return int((doc or {}).get("count") or 0)


def is_claimed(uid, qid):
    return _col(CLAIMS).find_one({"_id": f"{int(uid)}:{qid}"}, {"_id": 1}) is not None


def claim_quest(uid, q):
    """All-or-nothing reward grant. Returns ('ok', [reward lines]) / ('already', None) / ('failed', None).
    The claim document is inserted first (its _id is unique), so a quest can never pay out twice; if any part of the
    grant fails everything already given is taken back and the claim is removed so it can be retried."""
    uid = int(uid)
    claims = _col(CLAIMS)
    try:
        claims.insert_one({"_id": f"{uid}:{q['_id']}", "user_id": uid, "quest_id": q["_id"], "claimed_at": _stamp()})
    except DuplicateKeyError:
        return "already", None
    r = q.get("reward") or {}
    undo = []                       # callables that take back what was already given
    try:
        if r.get("berrys"):
            n = int(r["berrys"])
            if not mongo_db.add_coins(uid, n):
                raise RuntimeError("reward user missing")
            undo.append(lambda n=n: mongo_db.add_coins(uid, -n))
        if r.get("stones"):
            n = int(r["stones"])
            if not mongo_db.add_special_stones(uid, n):
                raise RuntimeError("reward user missing")
            undo.append(lambda n=n: mongo_db.add_special_stones(uid, -n))
        if r.get("card"):
            if not _character_row(r["card"]):
                raise RuntimeError("event card character no longer exists")
            gid = mongo_db.add_collection(uid, r["card"], _grant_stamp())
            undo.append(lambda gid=gid: mongo_db.delete_collection_by_id(gid))
        if r.get("banner"):
            token = banner_token(r["banner"])
            gid = f"{uid}:{token}"
            try:
                _col(GRANTS).insert_one({"_id": gid, "user_id": uid, "kind": "banner", "token": token,
                                         "quest_id": q["_id"], "at": _stamp()})
                undo.append(lambda gid=gid: _col(GRANTS).delete_one({"_id": gid}))
            except DuplicateKeyError:
                pass                # already owns this banner
    except Exception as e:
        logger.warning("festival reward failed for %s / %s: %s", uid, q.get("_id"), e)
        for fn in reversed(undo):
            try:
                fn()
            except Exception as undo_err:
                logger.warning("festival reward undo failed: %s", undo_err)
        try:
            claims.delete_one({"_id": f"{uid}:{q['_id']}"})
        except Exception as undo_err:
            logger.warning("festival claim undo failed: %s", undo_err)
        return "failed", None
    return "ok", reward_lines(r)


def evaluate(uid, only_types=None):
    """Claim every completed, not yet claimed quest of a festival that is open RIGHT NOW.
    Returns [(festival, quest, reward_lines)] for the quests that paid out."""
    uid = int(uid)
    done = []
    now = _stamp()
    for f, qs in live_festivals():
        if status_of(f, now) != "live":
            continue
        for q in qs:
            if q["qtype"] == "wish_pay":            # paid per wish by pay_wish(), never claimed as one reward
                continue
            if only_types and q["qtype"] not in only_types:
                continue
            if is_claimed(uid, q["_id"]):
                continue
            if quest_count(uid, f, q) < int(q["target"]):
                continue
            status, lines = claim_quest(uid, q)
            if status == "ok":
                done.append((f, q, lines))
    return done


def _bump(uid, kind, rarity):
    """+1 on every live quest of this kind. Returns the [(festival, quest)] that counted it."""
    hits = []
    for f, qs in live_festivals():
        for q in qs:
            if q["qtype"] != kind or is_claimed(uid, q["_id"]):
                continue
            if q.get("rarity") and q["rarity"] != rarity:
                continue
            _col(PROGRESS).update_one(
                {"_id": f"{int(uid)}:{q['_id']}"},
                {"$inc": {"count": 1}, "$setOnInsert": {"user_id": int(uid), "quest_id": q["_id"], "festival_id": f["_id"]}},
                upsert=True)
            hits.append((f, q))
    return hits


def _pay_once(q, uid, side, other_id, berrys, stones, cap):
    """Pay ONE wish payout (idempotent per person: the ledger _id is unique). Returns reward lines ([] = nothing paid)."""
    uid = int(uid)
    paid = _col(PAID)
    if not (berrys or stones):
        return []
    if paid.count_documents({"user_id": uid, "quest_id": q["_id"], "side": side}) >= cap:
        return []                                       # this player reached the cap of this quest
    ledger = f"{uid}:{q['_id']}:{side}:{int(other_id)}"
    try:
        paid.insert_one({"_id": ledger, "user_id": uid, "quest_id": q["_id"], "side": side, "at": _stamp()})
    except DuplicateKeyError:
        return []
    undo = []
    try:
        if berrys:
            if not mongo_db.add_coins(uid, int(berrys)):
                raise RuntimeError("reward user missing")
            undo.append(lambda: mongo_db.add_coins(uid, -int(berrys)))
        if stones:
            if not mongo_db.add_special_stones(uid, int(stones)):
                raise RuntimeError("reward user missing")
            undo.append(lambda: mongo_db.add_special_stones(uid, -int(stones)))
    except Exception as e:
        logger.warning("festival wish payout failed for %s / %s: %s", uid, q.get("_id"), e)
        for fn in reversed(undo):
            try:
                fn()
            except Exception as undo_err:
                logger.warning("festival payout undo failed: %s", undo_err)
        try:
            paid.delete_one({"_id": ledger})
        except Exception:
            pass
        return []
    lines = []
    if berrys:
        lines.append(f"🪙 {int(berrys)} Berrys")
    if stones:
        lines.append(f"💎 {int(stones)} Special Stone" + ("" if int(stones) == 1 else "s"))
    return lines


def pay_wish(quests, sender_id, receiver_id):
    """Pay every wish_pay quest for ONE new wish. Returns (sender_lines, receiver_lines)."""
    s_lines, r_lines = [], []
    for q in quests:
        if q["qtype"] != "wish_pay":
            continue
        cap = int(q["target"])
        r = q.get("reward") or {}
        s_lines += _pay_once(q, sender_id, "s", receiver_id, r.get("berrys", 0), r.get("stones", 0), cap)
        r_lines += _pay_once(q, receiver_id, "r", sender_id, q.get("receiver_berrys", 0), 0, cap)
    return s_lines, r_lines


def add_wish(festival_id, sender_id, receiver_id):
    """Record one wish. True only the FIRST time this sender wished this receiver in this festival."""
    try:
        _col(WISHES).insert_one({"festival_id": str(festival_id), "sender_id": int(sender_id),
                                 "receiver_id": int(receiver_id), "at": _stamp()})
        return True
    except DuplicateKeyError:
        return False


# ---------------- user data hooks for /deleteuser /restoreuser /moveuser ----------------
def purge_user(uid, session=None):
    """Called inside bot.py's purge transaction."""
    uid = int(uid)
    for name, key in USER_DATA_SPEC:
        mongo_db.col(name).delete_many({key: uid}, session=session)
    mongo_db.col(WISHES).delete_many({"$or": [{"sender_id": uid}, {"receiver_id": uid}]}, session=session)
    mongo_db.col(REFERRALS).delete_many({"_id": uid}, session=session)       # the row that says who invited this member


def move_user_data(data, new, session, inserted):
    """Copy-only transfer used by /moveuser (never overwrites what the new account already has)."""
    new = int(new)
    for name, _key in USER_DATA_SPEC:
        for d in data.get(name, []):
            old_id = str(d.get("_id", ""))
            if ":" not in old_id:
                continue
            nd = {k: v for k, v in d.items() if k != "_id"}
            nd["user_id"] = new
            nd["_id"] = f"{new}:{old_id.split(':', 1)[1]}"
            if mongo_db.col(name).find_one({"_id": nd["_id"]}, {"_id": 1}, session=session) is None:
                mongo_db.col(name).insert_one(nd, session=session)
                inserted.append((name, nd["_id"]))


# ==========================================================================
# Messaging helpers
# ==========================================================================
def _unhtml(text):
    return _unesc(re.sub(r"</?[a-z]+[^>]*>", "", str(text)))


async def _reply(msg, text, **kw):
    """Send through bot.py's safe_reply_text; if Telegram rejects the HTML, resend as plain text."""
    fn = _deps.get("safe_reply")
    send = fn if fn else (lambda m, t, **k: m.reply_text(t, **k))
    try:
        return await send(msg, text, **kw)
    except Exception as e:
        if kw.get("parse_mode") and "parse entities" in str(e).lower():
            logger.warning("festival: HTML rejected, resending as plain text: %s", e)
            plain = dict(kw)
            plain.pop("parse_mode", None)
            return await send(msg, _unhtml(text), **plain)
        raise


async def _edit(q, text, kb=None):
    try:
        if q.message is not None and getattr(q.message, "photo", None):
            await q.edit_message_caption(caption=text[:CAPTION_LIMIT], parse_mode="HTML", reply_markup=kb)
        else:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception as e:
        if "not modified" not in str(e).lower():
            logger.info("festival edit skipped: %s", e)


def _ok(update):
    fn = _deps.get("mark_success")
    if fn:
        try:
            fn(update)
        except Exception:
            pass


def _btn(label, data):
    return InlineKeyboardButton(label, callback_data=data)


def _mention(uid, name):
    return f'<a href="tg://user?id={int(uid)}">{_esc(str(name or "Player"))}</a>'


async def _send(bot, chat_id, text, thread=None, reply_to=None):
    try:
        if reply_to is not None:
            await reply_to.reply_text(text[:4000], parse_mode="HTML")
        else:
            await bot.send_message(chat_id=chat_id, text=text[:4000], parse_mode="HTML", message_thread_id=thread)
        return True
    except Exception as e:
        logger.info("festival message failed (%s): %s", chat_id, e)
        return False


async def _announce(bot, uid, chat_id, name, done, thread=None):
    """'Quest completed' message for each paid-out quest, in the chat where it happened (DM if no chat)."""
    for f, q, lines in done:
        text = (f"🎉 {_mention(uid, name)}, your {_esc(str(f['name']))} quest is complete!\n"
                f"{progress_line(uid, f, q)}\n"
                f"🎁 Reward: " + ", ".join(lines or ["-"]) + "\n"
                "✅ Your reward has been added to your account.")
        if not await _send(bot, chat_id or uid, text, thread if chat_id else None) and chat_id:
            await _send(bot, uid, text)          # last resort: DM


async def _announce_wish(bot, chat_id, sender, receiver, s_pay, r_pay, s_prog, r_prog, thread=None, reply_to=None):
    """ONE reply per wish: payouts (only if something was paid), then 'Sent n/t' and the receiver's 'Received n/t'."""
    sname = sender.full_name if hasattr(sender, "full_name") else sender.first_name
    rname = receiver.full_name if hasattr(receiver, "full_name") else receiver.first_name
    if not (s_pay or r_pay or s_prog or r_prog):
        return
    lines = []
    if s_pay or r_pay:
        lines.append(f"🪔 {_mention(sender.id, sname)} wished {_mention(receiver.id, rname)}!" + ("  🎁 " + ", ".join(s_pay) if s_pay else ""))
    if r_pay:
        lines.append(f"🎁 {_mention(receiver.id, rname)} received " + ", ".join(r_pay))
    lines += s_prog
    for x in r_prog:
        emoji, _sp, rest = x.partition(" ")
        lines.append(f"{emoji} {_mention(receiver.id, rname)}: {rest}")
    await _send(bot, chat_id, "\n".join(lines), thread, reply_to)


# ==========================================================================
# Hooks used by bot.py
# ==========================================================================
async def record(bot, uid, kind, rarity=None, chat_id=None, name=None):
    """Called by bot.py after a REAL action ('catch' with its rarity, or 'daily'). Never raises."""
    try:
        if kind not in COUNTED_TYPES:
            return
        live = await asyncio.to_thread(live_festivals)
        if not live:
            return
        hits = await asyncio.to_thread(_bump, uid, kind, rarity)
        if not hits:
            return
        done = await asyncio.to_thread(evaluate, uid, {kind})
        lines = await asyncio.to_thread(progress_lines, uid, hits, {q["_id"] for _f, q, _l in done})
        if lines:
            await _send(bot, chat_id or uid, _mention(uid, name) + "\n" + "\n".join(lines))
        if done:
            await _announce(bot, uid, chat_id, name, done)
    except Exception as e:
        logger.warning("festival record failed: %s", e)


async def wish_handler(update, context):
    """A reply that contains a live festival's phrase counts as one wish from the sender to the replied-to person."""
    msg = update.effective_message
    sender = update.effective_user
    if msg is None or not msg.text or sender is None or sender.is_bot or msg.reply_to_message is None:
        return
    target = msg.reply_to_message.from_user
    if target is None or target.is_bot or target.id == sender.id:
        return
    try:
        live = await asyncio.to_thread(live_festivals)
        if not live:
            return
        text = _norm(msg.text)
        matched = [f for f, _qs in live if phrase_in(text, f.get("phrase_norm"))]
        if not matched:
            return
        save = _deps.get("save_user")
        if save:
            try:
                await save(sender)
            except Exception as e:
                logger.info("festival save_user failed: %s", e)
        quests_by_festival = {f["_id"]: qs for f, qs in live}
        fresh = []
        for f in matched:
            if await asyncio.to_thread(add_wish, f["_id"], sender.id, target.id):
                fresh.append(f)
        if not fresh:
            return
        thread = msg.message_thread_id if getattr(msg, "is_topic_message", False) else None
        s_pay, r_pay, s_hits, r_hits = [], [], [], []
        for f in fresh:                                   # per-wish payouts happen immediately
            qs = quests_by_festival[f["_id"]]
            sl, rl = await asyncio.to_thread(pay_wish, qs, sender.id, target.id)
            s_pay += sl
            r_pay += rl
            s_hits += [(f, q) for q in qs if q["qtype"] in ("wish_send", "wish_pay")]
            r_hits += [(f, q) for q in qs if q["qtype"] == "wish_receive"]
        sent = await asyncio.to_thread(evaluate, sender.id, {"wish_send"})
        got = await asyncio.to_thread(evaluate, target.id, {"wish_receive"})
        s_prog = await asyncio.to_thread(progress_lines, sender.id, s_hits, {q["_id"] for _f, q, _l in sent})
        r_prog = await asyncio.to_thread(progress_lines, target.id, r_hits, {q["_id"] for _f, q, _l in got})
        await _announce_wish(context.bot, msg.chat_id, sender, target, s_pay, r_pay, s_prog, r_prog, thread=thread, reply_to=msg)
        sname = sender.full_name if hasattr(sender, "full_name") else sender.first_name
        tname = target.full_name if hasattr(target, "full_name") else target.first_name
        if sent:
            await _announce(context.bot, sender.id, msg.chat_id, sname, sent, thread=thread)
        if got:
            await _announce(context.bot, target.id, msg.chat_id, tname, got, thread=thread)
    except Exception as e:
        logger.warning("festival wish handler failed: %s", e)


# ==========================================================================
# /quests (everyone)
# ==========================================================================
def _quests_text(uid):
    """Each quest in words (what to do), then its reward and the player's progress."""
    now = _stamp()
    blocks = []
    for f in all_festivals():
        st = status_of(f, now)
        if st == "ended":
            continue
        qs = quests_of(f["_id"])
        if not qs:
            continue
        head = (f"🪔 {_esc(f['name'])} - starts {fmt_when(f['start_at'])}" if st == "upcoming"
                else f"🪔 {_esc(f['name'])} - ends {fmt_when(f['end_at'])}")
        lines = [head]
        if st == "live" and any(q["qtype"] in ("wish_send", "wish_receive", "wish_pay") for q in qs):
            lines.append(f"💡 Reply “{_esc(f['phrase'])}” to someone to wish them.")
        lines.append("")
        for q in qs:
            target = int(q["target"])
            if q["qtype"] != "wish_pay" and is_claimed(uid, q["_id"]):
                prog = "Done ✅"
            elif st == "live":
                prog = f"{min(quest_count(uid, f, q), target)}/{target}" + (" paid" if q["qtype"] == "wish_pay" else "")
            else:
                prog = f"0/{target}"
            lines.append(f"{quest_label(f, q)}\n↳ {quest_rewards_short(q)}  ·  {prog}")
        blocks.append("\n".join(lines))
    if not blocks:
        return "🪔 No festival quests are running right now.\n\nSee past and upcoming special rewards with /special."
    return "\n\n".join(blocks) + "\n\nRewards are added to your account automatically. See every special reward with /special."


async def quests_command(update, context):
    uid = update.effective_user.id
    msg = update.effective_message
    try:
        done = await asyncio.to_thread(evaluate, uid)       # also pays out anything finished but not yet paid
        text = await asyncio.to_thread(_quests_text, uid)
    except Exception as e:
        logger.error("quests failed: %s", e)
        await _reply(msg, "❌ Could not load quests right now. Please try again.")
        return
    await _reply(msg, text, parse_mode="HTML")
    if done:
        thread = msg.message_thread_id if getattr(msg, "is_topic_message", False) else None
        await _announce(context.bot, uid, msg.chat_id, update.effective_user.first_name, done, thread=thread)
    _ok(update)


# ==========================================================================
# Owner: guards + helpers
# ==========================================================================
async def _guard_owner(update):
    user = update.effective_user
    if user is None or not _is_owner(user.id):
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


def _clean_name(text, limit=NAME_MAX):
    name = " ".join(str(text or "").split())
    return name if name and len(name) <= limit else None


def _clean_phrase(text):
    p = " ".join(str(text or "").split())
    if not (PHRASE_MIN <= len(p) <= PHRASE_MAX) or not _norm(p):
        return None
    return p


def _to_int(text, lo, hi):
    t = str(text or "").strip().replace(",", "")
    if not t.lstrip("-").isdigit():
        return None
    n = int(t)
    return n if lo <= n <= hi else None


def _is_none_word(text):
    return str(text or "").strip().casefold() in ("0", "no", "none", "skip", "-", "n")


def _festival_summary(f, with_quests=True):
    """Festival details + its REWARDS only (the quests themselves are behind the 🎯 Quests button)."""
    st = status_of(f)
    icon = {"live": "🟢 LIVE", "upcoming": "🕒 Upcoming", "ended": "🔴 Ended"}[st]
    lines = [f"🪔 {_esc(f['name'])}  [{f['_id']}]  {icon}",
             f"Phrase: “{_esc(f['phrase'])}”",
             f"Starts: {fmt_when(f['start_at'])}", f"Ends: {fmt_when(f['end_at'])}"]
    if with_quests:
        qs = quests_of(f["_id"])
        if not qs:
            lines.append("No rewards yet - add a quest to this festival.")
        else:
            lines.append("")
            lines += festival_reward_lines(qs)
    return "\n".join(lines)


async def _cancel_flow(update, context):
    for key in ("fs_new", "fs_ef", "fs_q", "fs_eq", "fs_tc"):
        context.user_data.pop(key, None)
    fn = _deps.get("cancel_all")
    if fn:
        return await fn(update, context)
    await _reply(update.effective_message, "❌ Cancelled.")
    return -1


# ==========================================================================
# /festivals, /delfestival, /delquest
# ==========================================================================
async def festivals_command(update, context):
    user = update.effective_user
    owner = user is not None and _is_owner(user.id)         # everyone can see the festivals; only the owner sees the manage commands
    try:
        fests = await asyncio.to_thread(all_festivals)
        texts = [await asyncio.to_thread(_festival_summary, f) for f in fests]
    except Exception as e:
        logger.error("festivals failed: %s", e)
        await _reply(update.effective_message, "❌ Could not load festivals right now.")
        return
    if not texts:
        await _reply(update.effective_message, "No festivals yet." + (" Create one with /addfestival (private chat)." if owner else ""))
        return
    body = "\n\n".join(texts)
    manage = ("\n\nManage: /addfestival, /editfestival &lt;code&gt;, /delfestival &lt;code&gt;, "
              "/addquest &lt;code&gt;, /editquest &lt;id&gt;, /delquest &lt;id&gt;") if owner else ""
    await _reply(update.effective_message, "🎉 Festivals\n\n" + body + manage, parse_mode="HTML")
    _ok(update)


async def delfestival_command(update, context):
    if not await _guard_owner(update):
        return
    msg = update.effective_message
    code = normalize_fcode(context.args[0]) if context.args else None
    f = await asyncio.to_thread(get_festival, code) if code else None
    if f is None:
        await _reply(msg, "Usage: /delfestival <festival code>   (codes: /festivals)")
        return
    uid = update.effective_user.id
    kb = InlineKeyboardMarkup([[_btn("🗑 Delete", f"fs:df:{uid}:{code}:ok"), _btn("↩️ Cancel", f"fs:df:{uid}:{code}:no")]])
    await _reply(msg, f"⚠️ Delete festival “{_esc(f['name'])}” ({code}) with all its quests and progress?\n"
                      f"Cards and banners people already earned are kept. This cannot be undone.",
                 parse_mode="HTML", reply_markup=kb)


async def delquest_command(update, context):
    if not await _guard_owner(update):
        return
    msg = update.effective_message
    qid = normalize_qid(context.args[0]) if context.args else None
    q = await asyncio.to_thread(get_quest, qid) if qid else None
    if q is None:
        await _reply(msg, "Usage: /delquest <quest id>   (ids: /festivals, example Q001)")
        return
    f = await asyncio.to_thread(get_festival, q["festival_id"]) or {"name": "?", "phrase": ""}
    uid = update.effective_user.id
    kb = InlineKeyboardMarkup([[_btn("🗑 Delete", f"fs:dq:{uid}:{qid}:ok"), _btn("↩️ Cancel", f"fs:dq:{uid}:{qid}:no")]])
    await _reply(msg, f"⚠️ Delete quest {qid}?\n{quest_label(f, q)}\nProgress is removed. Rewards already earned are kept.",
                 parse_mode="HTML", reply_markup=kb)


async def fs_callback(update, context):
    """Router for the fs:... buttons that are not inside a conversation (delete confirmations)."""
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
        if kind in ("df", "dq"):
            if not _is_owner(uid):
                await q.answer(DENIED_TEXT, show_alert=True)
                return
            target, action = parts[3], parts[4]
            back = InlineKeyboardMarkup([[_btn("🪔 Festival Manager", f"fs:hub:{uid}")]])
            if action == "no":
                await q.answer("Cancelled.")
                await _edit(q, "↩️ Deletion cancelled. Nothing was removed.", back)
                return
            if kind == "df":
                deleted, nq = await asyncio.to_thread(delete_festival, target)
                await q.answer("Deleted." if deleted else "Already deleted.", show_alert=not deleted)
                await _edit(q, f"🗑 Festival {target} deleted ({nq} quest(s) removed)." if deleted
                            else f"ℹ️ Festival {target} no longer exists.", back)
            else:
                deleted = await asyncio.to_thread(delete_quest, target)
                await q.answer("Deleted." if deleted else "Already deleted.", show_alert=not deleted)
                await _edit(q, f"🗑 Quest {target} deleted." if deleted else f"ℹ️ Quest {target} no longer exists.", back)
        elif kind == "sp":                                   # /special screens (public, edited in place)
            page = int(parts[4]) if len(parts) > 4 and parts[4].isdigit() else 0
            text, kb = await asyncio.to_thread(_special_panel, parts[3] if len(parts) > 3 else "h", page, uid)
            await q.answer()
            await _edit(q, text, kb)
        elif kind == "sd":                                   # picture + details of one special item (new message)
            msg = q.message
            thread = msg.message_thread_id if msg is not None and getattr(msg, "is_topic_message", False) else None
            await q.answer()
            await _send_special_detail(context.bot, msg.chat_id, thread, parts[3], parts[4], uid)
        elif kind in PANEL_KINDS:
            if not _is_owner(uid):
                await q.answer(DENIED_TEXT, show_alert=True)
                return
            chat = q.message.chat if q.message else None
            if chat is not None and chat.type != "private":
                await q.answer("Open /help in my private chat to use the Festival Manager.", show_alert=True)
                return
            await q.answer()
            text, kb = await asyncio.to_thread(_panel, kind, parts, uid)
            await _edit(q, text, kb)
        elif kind in ("af", "ef", "qt", "qc", "eq"):
            await q.answer("This button has already been used or has expired.", show_alert=True)
        else:
            await q.answer()
    except Exception as e:
        logger.error("festival callback failed (%s): %s", q.data, e)
        try:
            await q.answer("❌ Something went wrong. Please try again.", show_alert=True)
        except Exception:
            pass


# ==========================================================================
# /addfestival  (name -> phrase -> start -> end -> preview -> confirm)
# ==========================================================================
AF_NAME, AF_PHRASE, AF_START, AF_END, AF_CONFIRM = range(20, 25)
_NEW = "fs_new"
_WHEN_HELP = ("Format: DD-MM-YY h:mm am/pm (India time).\n"
              "Example: 10-11-26 4:30am  (10 Nov 2026, 4:30 AM)\n"
              "Example: 25-12-26 11:00pm\n"
              "24-hour also works: 20-10-2026 18:00")


async def addfestival_start(update, context):
    if not await _guard_owner(update) or not await _guard_private(update):
        return -1
    context.user_data[_NEW] = {}
    await _reply(update.effective_message, f"🪔 New festival - step 1/4\nSend the festival NAME (max {NAME_MAX} characters), "
                                           f"for example Diwali.\n\nSend /cancel to stop.")
    return AF_NAME


async def addfestival_name(update, context):
    if not await _guard_owner(update):
        return -1
    name = _clean_name(update.effective_message.text)
    if not name:
        await _reply(update.effective_message, f"❌ The name must be 1-{NAME_MAX} characters. Send it again.")
        return AF_NAME
    context.user_data.setdefault(_NEW, {})["name"] = name
    await _reply(update.effective_message, "✅ Saved.\n\nStep 2/4 - send the WISH PHRASE players reply with, for example: "
                                           "Happy Diwali\n(Capital letters and punctuation do not matter.)")
    return AF_PHRASE


async def addfestival_phrase(update, context):
    if not await _guard_owner(update):
        return -1
    phrase = _clean_phrase(update.effective_message.text)
    if not phrase:
        await _reply(update.effective_message, f"❌ The phrase must be {PHRASE_MIN}-{PHRASE_MAX} characters. Send it again.")
        return AF_PHRASE
    context.user_data.setdefault(_NEW, {})["phrase"] = phrase
    await _reply(update.effective_message, f"✅ Saved.\n\nStep 3/4 - send the START date and time, or send now.\n{_WHEN_HELP}")
    return AF_START


async def addfestival_start_time(update, context):
    if not await _guard_owner(update):
        return -1
    when = parse_when(update.effective_message.text, allow_now=True)
    if not when:
        await _reply(update.effective_message, f"❌ I could not read that date.\n{_WHEN_HELP}\nOr send now.")
        return AF_START
    context.user_data.setdefault(_NEW, {})["start"] = when
    await _reply(update.effective_message, f"✅ Starts {fmt_when(when)}.\n\nStep 4/4 - send the END date and time.\n{_WHEN_HELP}")
    return AF_END


async def addfestival_end_time(update, context):
    if not await _guard_owner(update):
        return -1
    msg = update.effective_message
    draft = context.user_data.get(_NEW)
    if not draft or "start" not in draft:
        await _reply(msg, "❌ This setup expired. Run /addfestival again.")
        return -1
    when = parse_when(msg.text)
    if not when:
        await _reply(msg, f"❌ I could not read that date.\n{_WHEN_HELP}")
        return AF_END
    if when <= draft["start"] or when <= _stamp():
        await _reply(msg, "❌ The end must be after the start and in the future. Send the END date and time again.")
        return AF_END
    draft["end"] = when
    draft["token"] = secrets.token_hex(4)
    uid = update.effective_user.id
    kb = InlineKeyboardMarkup([[_btn("✅ Create Festival", f"fs:af:{uid}:{draft['token']}:ok"),
                                _btn("❌ Cancel", f"fs:af:{uid}:{draft['token']}:no")]])
    await _reply(msg, "🪔 Festival preview\n\n"
                      f"Name: {_esc(draft['name'])}\nPhrase: “{_esc(draft['phrase'])}”\n"
                      f"Starts: {fmt_when(draft['start'])}\nEnds: {fmt_when(draft['end'])}\n\n"
                      "Quests are added afterwards with /addquest.", parse_mode="HTML", reply_markup=kb)
    return AF_CONFIRM


async def addfestival_confirm(update, context):
    q = update.callback_query
    parts = q.data.split(":")            # fs:af:<uid>:<token>:<ok|no>
    if q.from_user.id != int(parts[2]):
        await q.answer(NOT_YOURS_TEXT, show_alert=True)
        return AF_CONFIRM
    if not _is_owner(q.from_user.id):
        await q.answer(DENIED_TEXT, show_alert=True)
        return -1
    draft = context.user_data.get(_NEW)
    if not draft or draft.get("token") != parts[3]:
        await q.answer("This preview has expired.", show_alert=True)
        return -1
    context.user_data.pop(_NEW, None)       # single use
    if parts[4] == "no":
        await q.answer("Cancelled.")
        await _edit(q, "❌ Festival creation cancelled. Nothing was saved.")
        return -1
    await q.answer("Creating…")
    try:
        code = await asyncio.to_thread(create_festival, draft, q.from_user.id)
    except Exception as e:
        logger.error("create festival failed: %s", e)
        await _edit(q, "❌ Database error. Nothing was created. Run /addfestival again.")
        return -1
    if not code:
        await _edit(q, "❌ All festival codes are used.")
        return -1
    uid = q.from_user.id
    await _edit(q, f"✅ Festival created: {_esc(draft['name'])}\nCode: {code}\n\n"
                   f"Next: add quests with the button below.",
                InlineKeyboardMarkup([[_btn("➕ Add Quest", f"fs:go:{uid}:addquest:{code}")],
                                      [_btn("🪔 Festival Manager", f"fs:hub:{uid}")]]))
    return -1


# ==========================================================================
# /editfestival <code>   (name, phrase, start, end)
# ==========================================================================
EF_MENU, EF_INPUT = 30, 31
_EF = "fs_ef"


def _ef_menu(uid, code):
    return InlineKeyboardMarkup([
        [_btn("✏️ Name", f"fs:ef:{uid}:{code}:name"), _btn("💬 Phrase", f"fs:ef:{uid}:{code}:phrase")],
        [_btn("🕒 Start", f"fs:ef:{uid}:{code}:start"), _btn("⏰ End", f"fs:ef:{uid}:{code}:end")],
        [_btn("✔️ Done", f"fs:ef:{uid}:{code}:done")]])


async def _show_ef_menu(context, chat_id, uid, code):
    f = await asyncio.to_thread(get_festival, code)
    if f is None:
        await context.bot.send_message(chat_id=chat_id, text="❌ That festival no longer exists.")
        context.user_data.pop(_EF, None)
        return -1
    text = (await asyncio.to_thread(_festival_summary, f)) + "\n\nWhat do you want to change?"
    await context.bot.send_message(chat_id=chat_id, text=text, parse_mode="HTML", reply_markup=_ef_menu(uid, code))
    return EF_MENU


async def editfestival_start(update, context, code=None):
    if not await _guard_owner(update) or not await _guard_private(update):
        return -1
    msg = update.effective_message
    code = code or (normalize_fcode(context.args[0]) if context.args else None)
    if code is None or await asyncio.to_thread(get_festival, code) is None:
        await _reply(msg, "Usage: /editfestival <festival code>   (codes: /festivals)")
        return -1
    context.user_data[_EF] = {"code": code}
    return await _show_ef_menu(context, msg.chat_id, update.effective_user.id, code)


async def editfestival_menu(update, context):
    q = update.callback_query
    parts = q.data.split(":")            # fs:ef:<uid>:<code>:<action>
    if q.from_user.id != int(parts[2]):
        await q.answer(NOT_YOURS_TEXT, show_alert=True)
        return EF_MENU
    if not _is_owner(q.from_user.id):
        await q.answer(DENIED_TEXT, show_alert=True)
        return -1
    state = context.user_data.get(_EF)
    if not state or state.get("code") != parts[3]:
        await q.answer("This menu has expired. Run /editfestival again.", show_alert=True)
        return -1
    action = parts[4]
    await q.answer()
    if action == "done":
        context.user_data.pop(_EF, None)
        await context.bot.send_message(chat_id=q.message.chat_id, text="✅ Finished editing.",
                                       reply_markup=InlineKeyboardMarkup([[_btn("🪔 Festival Manager", f"fs:hub:{q.from_user.id}")]]))
        return -1
    state["field"] = action
    prompts = {"name": f"✏️ Send the new NAME (max {NAME_MAX} characters).",
               "phrase": "💬 Send the new WISH PHRASE. Wishes already counted stay counted.",
               "start": f"🕒 Send the new START date and time (or now).\n{_WHEN_HELP}",
               "end": f"⏰ Send the new END date and time.\n{_WHEN_HELP}"}
    await context.bot.send_message(chat_id=q.message.chat_id, text=prompts[action] + "\n\nSend /cancel to stop.")
    return EF_INPUT


async def editfestival_input(update, context):
    if not await _guard_owner(update):
        return -1
    msg = update.effective_message
    state = context.user_data.get(_EF)
    if not state or "field" not in state:
        await _reply(msg, "❌ This edit expired. Run /editfestival again.")
        return -1
    field, code = state["field"], state["code"]
    f = await asyncio.to_thread(get_festival, code)
    if f is None:
        context.user_data.pop(_EF, None)
        await _reply(msg, "❌ That festival no longer exists. Nothing was changed.")
        return -1
    if field == "name":
        value = _clean_name(msg.text)
        fields = {"name": value}
        err = f"❌ The name must be 1-{NAME_MAX} characters. Send it again."
    elif field == "phrase":
        value = _clean_phrase(msg.text)
        fields = {"phrase": value}
        err = f"❌ The phrase must be {PHRASE_MIN}-{PHRASE_MAX} characters. Send it again."
    else:
        value = parse_when(msg.text, allow_now=(field == "start"))
        fields = {"start_at" if field == "start" else "end_at": value}
        err = f"❌ I could not read that date.\n{_WHEN_HELP}"
        if value:
            start = value if field == "start" else f["start_at"]
            end = value if field == "end" else f["end_at"]
            if end <= start:
                value, err = None, "❌ The end must be after the start. Send it again."
    if not value:
        await _reply(msg, err)
        return EF_INPUT
    if not await asyncio.to_thread(update_festival, code, fields):
        context.user_data.pop(_EF, None)
        await _reply(msg, "❌ That festival no longer exists. Nothing was changed.")
        return -1
    state.pop("field", None)
    await _reply(msg, "✅ Updated.")
    return await _show_ef_menu(context, msg.chat_id, update.effective_user.id, code)


# ==========================================================================
# /addquest <festival code>
#   type -> target -> (rarity) -> berrys -> stones -> card -> (banner photo -> banner name) -> preview -> confirm
# ==========================================================================
AQ_INPUT = 40
_Q = "fs_q"


def _type_keyboard(uid, token):
    rows = [[_btn(f"{emoji} {label}", f"fs:qt:{uid}:{token}:{key}")] for key, (emoji, label) in QUEST_TYPES.items()]
    return InlineKeyboardMarkup(rows)


async def addquest_start(update, context, code=None):
    if not await _guard_owner(update) or not await _guard_private(update):
        return -1
    msg = update.effective_message
    code = code or (normalize_fcode(context.args[0]) if context.args else None)
    f = await asyncio.to_thread(get_festival, code) if code else None
    if f is None:
        await _reply(msg, "Usage: /addquest <festival code>   (codes: /festivals)")
        return -1
    token = secrets.token_hex(4)
    context.user_data[_Q] = {"fid": f["_id"], "step": "type", "token": token, "reward": {}}
    await _reply(msg, f"🎯 New quest for {_esc(f['name'])} - choose the quest type:\n\nSend /cancel to stop.",
                 parse_mode="HTML", reply_markup=_type_keyboard(update.effective_user.id, token))
    return AQ_INPUT


async def addquest_type(update, context):
    q = update.callback_query
    parts = q.data.split(":")            # fs:qt:<uid>:<token>:<type>
    if q.from_user.id != int(parts[2]):
        await q.answer(NOT_YOURS_TEXT, show_alert=True)
        return AQ_INPUT
    if not _is_owner(q.from_user.id):
        await q.answer(DENIED_TEXT, show_alert=True)
        return -1
    st = context.user_data.get(_Q)
    if not st or st.get("token") != parts[3] or st.get("step") != "type":
        await q.answer("This button has expired. Run /addquest again.", show_alert=True)
        return -1
    st["qtype"] = parts[4]
    st["step"] = "target"
    await q.answer()
    label = QUEST_TYPES[parts[4]][1]
    await _edit(q, f"✅ Type: {_esc(label)}")
    if parts[4] == "wish_pay":
        prompt = (f"Send the MAX number of paid wishes per player (1-{TARGET_MAX}). After that many wishes the player is "
                  f"not paid any more.\nExample: 20")
    else:
        prompt = f"Send the TARGET number (1-{TARGET_MAX}).\nExample: 20"
    await context.bot.send_message(chat_id=q.message.chat_id, text=prompt)
    return AQ_INPUT


def _aq_preview_text(st, f):
    q = {"qtype": st["qtype"], "target": st["target"], "rarity": st.get("rarity"),
         "reward": {k: v for k, v in st["reward"].items() if v}, "receiver_berrys": st.get("receiver_berrys", 0)}
    lines = ["🎯 Quest preview", "", f"Festival: {_esc(f['name'])}", quest_label(f, q), ""]
    if st["qtype"] == "wish_pay":
        lines.append("Pays right away for every wish to a different person:")
        lines.append("🎁 " + quest_rewards_text(q))
        return "\n".join(lines)
    lines.append("Rewards:")
    r = st["reward"]
    if r.get("berrys"):
        lines.append(f"🪙 {r['berrys']} Berrys")
    if r.get("stones"):
        lines.append(f"💎 {r['stones']} Special Stones")
    if r.get("card"):
        row = _character_row(r["card"])
        lines.append(f"🎭 {_esc(str(row[1]))} [{r['card']}] (event card: hidden from all lists)" if row else f"🎭 [{r['card']}]")
    if st.get("banner_name"):
        lines.append(f"🎌 Banner “{_esc(st['banner_name'])}” (event banner: hidden from the banner list)")
    return "\n".join(lines)


def _aq_berrys_prompt(st):
    if st.get("qtype") == "wish_pay":
        return "🪙 Send the BERRYS paid for EACH wish (example: 100, or 0 for none)."
    return "🪙 Send the BERRYS reward (0 for none)."


async def _aq_ask(update, context, step, text):
    context.user_data[_Q]["step"] = step
    await _reply(update.effective_message, text)
    return AQ_INPUT


async def _aq_show_preview(update, context, st):
    f = await asyncio.to_thread(get_festival, st["fid"])
    if f is None:
        context.user_data.pop(_Q, None)
        await _reply(update.effective_message, "❌ That festival no longer exists. Nothing was saved.")
        return -1
    if not any(st["reward"].values()) and not st.get("banner_name") and not st.get("receiver_berrys"):
        st["reward"] = {}
        return await _aq_ask(update, context, "berrys",
                             "❌ A quest needs at least one reward. Start again: send the BERRYS reward (0 for none).")
    st["step"] = "confirm"
    uid = update.effective_user.id
    kb = InlineKeyboardMarkup([[_btn("✅ Save Quest", f"fs:qc:{uid}:{st['token']}:ok"),
                                _btn("❌ Cancel", f"fs:qc:{uid}:{st['token']}:no")]])
    text = _aq_preview_text(st, f)
    if st.get("banner_photo"):
        await context.bot.send_photo(chat_id=update.effective_message.chat_id, photo=st["banner_photo"],
                                     caption=text[:CAPTION_LIMIT], parse_mode="HTML", reply_markup=kb)
    else:
        await _reply(update.effective_message, text, parse_mode="HTML", reply_markup=kb)
    return AQ_INPUT


async def addquest_input(update, context):
    if not await _guard_owner(update):
        return -1
    msg = update.effective_message
    st = context.user_data.get(_Q)
    if not st:
        await _reply(msg, "❌ This setup expired. Run /addquest again.")
        return -1
    step = st["step"]
    if step in ("type", "confirm"):
        await _reply(msg, "Please use the buttons above, or /cancel.")
        return AQ_INPUT
    text = msg.text or ""
    if step == "target":
        n = _to_int(text, 1, TARGET_MAX)
        if n is None:
            await _reply(msg, f"❌ Send a whole number from 1 to {TARGET_MAX}.")
            return AQ_INPUT
        st["target"] = n
        if st["qtype"] == "catch":
            return await _aq_ask(update, context, "rarity",
                                 "Only count one rarity? Send it (" + ", ".join(_rarities()) + ") or send any.")
        return await _aq_ask(update, context, "berrys", _aq_berrys_prompt(st))
    if step == "rarity":
        if text.strip().casefold() in ("any", "skip", "all", "0", "none", "-"):
            st["rarity"] = None
        else:
            match = next((r for r in _rarities() if r.casefold() == text.strip().casefold()), None)
            if not match:
                await _reply(msg, "❌ Send one of: " + ", ".join(_rarities()) + " - or send any.")
                return AQ_INPUT
            st["rarity"] = match
        return await _aq_ask(update, context, "berrys", _aq_berrys_prompt(st))
    if step == "berrys":
        n = _to_int(text, 0, BERRYS_MAX)
        if n is None:
            await _reply(msg, f"❌ Send a number from 0 to {BERRYS_MAX}.")
            return AQ_INPUT
        st["reward"]["berrys"] = n
        return await _aq_ask(update, context, "stones", "💎 Send the SPECIAL STONES reward (0 for none).")
    if step == "stones":
        n = _to_int(text, 0, STONES_MAX)
        if n is None:
            await _reply(msg, f"❌ Send a number from 0 to {STONES_MAX}.")
            return AQ_INPUT
        st["reward"]["stones"] = n
        if st["qtype"] == "wish_pay":
            return await _aq_ask(update, context, "rberrys",
                                 "👥 Send the BERRYS the PERSON WHO IS WISHED also gets for each wish (0 for none).")
        return await _aq_ask(update, context, "card",
                             "🎭 Send the EVENT CARD character code, or 0 for none.\n"
                             "Create it first with /addtempchar (temporary event character). Once it is a quest reward it is hidden from "
                             "the character list, shop, spawns and searches; only people who earn it see it in their collection.")
    if step == "rberrys":
        n = _to_int(text, 0, BERRYS_MAX)
        if n is None:
            await _reply(msg, f"❌ Send a number from 0 to {BERRYS_MAX}.")
            return AQ_INPUT
        st["receiver_berrys"] = n
        return await _aq_show_preview(update, context, st)
    if step == "card":
        if _is_none_word(text):
            st["reward"]["card"] = None
        else:
            code = normalize_char_code(text)
            row = await asyncio.to_thread(_character_row, code) if code else None
            if not row:
                await _reply(msg, "❌ No character with that code. Send a 4-digit code, or 0 for none.")
                return AQ_INPUT
            st["reward"]["card"] = code
        return await _aq_ask(update, context, "banner_photo", "🎌 Send the event BANNER photo, or 0 for no banner.")
    if step == "banner_photo":
        if msg.photo:
            st["banner_photo"] = msg.photo[-1].file_id
            return await _aq_ask(update, context, "banner_name", f"Send the banner NAME (max {NAME_MAX} characters).")
        if _is_none_word(text):
            st.pop("banner_photo", None)
            st.pop("banner_name", None)
            return await _aq_show_preview(update, context, st)
        await _reply(msg, "❌ Send the banner as a photo (not a file), or 0 for no banner.")
        return AQ_INPUT
    if step == "banner_name":
        name = _clean_name(text)
        if not name:
            await _reply(msg, f"❌ The name must be 1-{NAME_MAX} characters. Send it again.")
            return AQ_INPUT
        st["banner_name"] = name
        return await _aq_show_preview(update, context, st)
    return AQ_INPUT


def _save_quest(st, creator_id):
    """Create the banner (if any), register the card as hidden, insert the quest. Returns (qid, problem)."""
    f = get_festival(st["fid"])
    if f is None:
        return None, "That festival no longer exists."
    reward = {k: v for k, v in (st.get("reward") or {}).items() if v}
    receiver_berrys = int(st.get("receiver_berrys") or 0) if st["qtype"] == "wish_pay" else 0
    banner_code = None
    if st["qtype"] != "wish_pay" and st.get("banner_photo") and st.get("banner_name"):
        banner_code = create_festival_banner(st["banner_name"], st["banner_photo"], st["fid"], creator_id)
        if banner_code is None:
            return None, "All banner codes are used."
        reward["banner"] = banner_code
    if not reward and not receiver_berrys:
        return None, "A quest needs at least one reward."
    try:
        n = mongo_db.next_sequence(QUESTS)
        qid = "Q" + str(n).zfill(3)
        _col(QUESTS).insert_one({
            "_id": qid, "festival_id": st["fid"], "qtype": st["qtype"], "target": int(st["target"]),
            "rarity": st.get("rarity"), "reward": reward, "receiver_berrys": receiver_berrys,
            "created_by": int(creator_id), "created_at": _stamp()})
    except Exception:
        if banner_code:
            try:
                _col(BANNERS).delete_one({"_id": banner_code})
            except Exception:
                pass
        raise
    if reward.get("card"):
        register_card(reward["card"], st["fid"])
    invalidate()
    return qid, None


async def addquest_confirm(update, context):
    q = update.callback_query
    parts = q.data.split(":")            # fs:qc:<uid>:<token>:<ok|no>
    if q.from_user.id != int(parts[2]):
        await q.answer(NOT_YOURS_TEXT, show_alert=True)
        return AQ_INPUT
    if not _is_owner(q.from_user.id):
        await q.answer(DENIED_TEXT, show_alert=True)
        return -1
    st = context.user_data.get(_Q)
    if not st or st.get("token") != parts[3] or st.get("step") != "confirm":
        await q.answer("This preview has expired.", show_alert=True)
        return -1
    context.user_data.pop(_Q, None)        # single use
    if parts[4] == "no":
        await q.answer("Cancelled.")
        await _edit(q, "❌ Quest creation cancelled. Nothing was saved.")
        return -1
    await q.answer("Saving…")
    try:
        qid, problem = await asyncio.to_thread(_save_quest, st, q.from_user.id)
    except Exception as e:
        logger.error("save quest failed: %s", e)
        await _edit(q, "❌ Database error. Nothing was saved. Run /addquest again.")
        return -1
    if problem:
        await _edit(q, f"❌ Nothing was saved: {_esc(problem)}")
        return -1
    uid = q.from_user.id
    await _edit(q, f"✅ Quest saved: {qid}",
                InlineKeyboardMarkup([[_btn("➕ Add Another Quest", f"fs:go:{uid}:addquest:{st['fid']}")],
                                      [_btn("🪔 Festival Manager", f"fs:hub:{uid}")]]))
    return -1


# ==========================================================================
# /editquest <quest id>   (target, berrys, stones, card, banner photo, banner name)
# ==========================================================================
EQ_MENU, EQ_INPUT = 50, 51
_EQ = "fs_eq"


def _eq_menu(uid, qid):
    return InlineKeyboardMarkup([
        [_btn("🎯 Target", f"fs:eq:{uid}:{qid}:target"), _btn("🪙 Berrys", f"fs:eq:{uid}:{qid}:berrys")],
        [_btn("💎 Stones", f"fs:eq:{uid}:{qid}:stones"), _btn("🎭 Card", f"fs:eq:{uid}:{qid}:card")],
        [_btn("🖼 Banner photo", f"fs:eq:{uid}:{qid}:bphoto"), _btn("🎌 Banner name", f"fs:eq:{uid}:{qid}:bname")],
        [_btn("👥 Wished person's Berrys", f"fs:eq:{uid}:{qid}:rberrys")],
        [_btn("✔️ Done", f"fs:eq:{uid}:{qid}:done")]])


async def _show_eq_menu(context, chat_id, uid, qid):
    q = await asyncio.to_thread(get_quest, qid)
    f = await asyncio.to_thread(get_festival, q["festival_id"]) if q else None
    if q is None or f is None:
        await context.bot.send_message(chat_id=chat_id, text="❌ That quest no longer exists.")
        context.user_data.pop(_EQ, None)
        return -1
    text = (f"🎯 Quest {qid} ({_esc(f['name'])})\n{quest_label(f, q)}\n🎁 " + await asyncio.to_thread(quest_rewards_text, q) +
            "\n\nWhat do you want to change?")
    await context.bot.send_message(chat_id=chat_id, text=text, parse_mode="HTML", reply_markup=_eq_menu(uid, qid))
    return EQ_MENU


async def editquest_start(update, context, qid=None):
    if not await _guard_owner(update) or not await _guard_private(update):
        return -1
    msg = update.effective_message
    qid = qid or (normalize_qid(context.args[0]) if context.args else None)
    if qid is None or await asyncio.to_thread(get_quest, qid) is None:
        await _reply(msg, "Usage: /editquest <quest id>   (ids: /festivals, example Q001)")
        return -1
    context.user_data[_EQ] = {"qid": qid}
    return await _show_eq_menu(context, msg.chat_id, update.effective_user.id, qid)


async def editquest_menu(update, context):
    q = update.callback_query
    parts = q.data.split(":")            # fs:eq:<uid>:<qid>:<action>
    if q.from_user.id != int(parts[2]):
        await q.answer(NOT_YOURS_TEXT, show_alert=True)
        return EQ_MENU
    if not _is_owner(q.from_user.id):
        await q.answer(DENIED_TEXT, show_alert=True)
        return -1
    state = context.user_data.get(_EQ)
    if not state or state.get("qid") != parts[3]:
        await q.answer("This menu has expired. Run /editquest again.", show_alert=True)
        return -1
    action = parts[4]
    await q.answer()
    if action == "done":
        context.user_data.pop(_EQ, None)
        await context.bot.send_message(chat_id=q.message.chat_id, text="✅ Finished editing.",
                                       reply_markup=InlineKeyboardMarkup([[_btn("🪔 Festival Manager", f"fs:hub:{q.from_user.id}")]]))
        return -1
    quest = await asyncio.to_thread(get_quest, state["qid"])
    has_banner = bool(quest and (quest.get("reward") or {}).get("banner"))
    is_pay = bool(quest and quest["qtype"] == "wish_pay")
    if is_pay and action in ("card", "bphoto", "bname"):
        await context.bot.send_message(chat_id=q.message.chat_id,
                                       text="ℹ️ A pay-per-wish quest only pays Berrys / Stones. It has no card or banner.")
        return EQ_MENU
    if not is_pay and action == "rberrys":
        await context.bot.send_message(chat_id=q.message.chat_id,
                                       text="ℹ️ Only pay-per-wish quests pay the wished person.")
        return EQ_MENU
    if action == "bname" and not has_banner:
        await context.bot.send_message(chat_id=q.message.chat_id,
                                       text="ℹ️ This quest has no banner yet. Use 🖼 Banner photo to add one.")
        return EQ_MENU
    state["field"] = action
    prompts = {"rberrys": "👥 Send the BERRYS the wished person gets for each wish (0 for none).",
               "target": f"🎯 Send the new TARGET (1-{TARGET_MAX}). People who already passed it are paid at their next action.",
               "berrys": "🪙 Send the new BERRYS reward (0 for none).",
               "stones": "💎 Send the new SPECIAL STONES reward (0 for none).",
               "card": "🎭 Send the new EVENT CARD character code (0 to remove). It will be hidden from all lists.",
               "bphoto": "🖼 Send the banner PHOTO." + ("" if has_banner else " (This adds a new event banner.)"),
               "bname": f"🎌 Send the new banner NAME (max {NAME_MAX} characters)."}
    await context.bot.send_message(chat_id=q.message.chat_id, text=prompts[action] + "\n\nSend /cancel to stop.")
    return EQ_INPUT


def _apply_quest_edit(qid, field, value, extra, creator_id):
    """Returns (ok, problem). Never leaves a quest without a reward."""
    q = get_quest(qid)
    if q is None:
        return False, "That quest no longer exists."
    reward = dict(q.get("reward") or {})
    updates = {}
    if field == "target":
        updates["target"] = int(value)
    elif field in ("berrys", "stones"):
        if value:
            reward[field] = int(value)
        else:
            reward.pop(field, None)
    elif field == "rberrys":
        updates["receiver_berrys"] = int(value)
    elif field == "card":
        if value:
            reward["card"] = value
        else:
            reward.pop("card", None)
    elif field == "bphoto":
        if reward.get("banner"):
            _col(BANNERS).update_one({"_id": reward["banner"]}, {"$set": {"photo_file_id": value, "updated_at": _stamp()}})
        else:
            code = create_festival_banner(extra["name"], value, q["festival_id"], creator_id)
            if code is None:
                return False, "All banner codes are used."
            reward["banner"] = code
    elif field == "bname":
        if not reward.get("banner"):
            return False, "This quest has no banner."
        _col(BANNERS).update_one({"_id": reward["banner"]}, {"$set": {"name": value, "updated_at": _stamp()}})
    receiver = int(updates.get("receiver_berrys", q.get("receiver_berrys") or 0))
    if not reward and not (q["qtype"] == "wish_pay" and receiver > 0):
        return False, "A quest needs at least one reward. Change it to something else instead."
    updates["reward"] = reward
    _col(QUESTS).update_one({"_id": str(qid)}, {"$set": updates})
    if field == "card" and value:
        register_card(value, q["festival_id"])
    invalidate()
    return True, None


async def editquest_input(update, context):
    if not await _guard_owner(update):
        return -1
    msg = update.effective_message
    state = context.user_data.get(_EQ)
    if not state or "field" not in state:
        await _reply(msg, "❌ This edit expired. Run /editquest again.")
        return -1
    field, qid = state["field"], state["qid"]
    text = msg.text or ""
    value, extra, err = None, {}, None
    if field == "target":
        value = _to_int(text, 1, TARGET_MAX)
        err = f"❌ Send a whole number from 1 to {TARGET_MAX}."
    elif field in ("berrys", "rberrys"):
        value = _to_int(text, 0, BERRYS_MAX)
        err = f"❌ Send a number from 0 to {BERRYS_MAX}."
    elif field == "stones":
        value = _to_int(text, 0, STONES_MAX)
        err = f"❌ Send a number from 0 to {STONES_MAX}."
    elif field == "card":
        if _is_none_word(text):
            value = 0
        else:
            code = normalize_char_code(text)
            row = await asyncio.to_thread(_character_row, code) if code else None
            value = code if row else None
        err = "❌ No character with that code. Send a 4-digit code, or 0 to remove."
    elif field == "bphoto":
        if msg.photo:
            value = msg.photo[-1].file_id
            quest = await asyncio.to_thread(get_quest, qid)
            if quest and not (quest.get("reward") or {}).get("banner"):
                state["pending_photo"] = value          # a brand-new banner also needs a name
                state["field"] = "bnew"
                await _reply(msg, f"✅ Photo received. Now send the banner NAME (max {NAME_MAX} characters).")
                return EQ_INPUT
        err = "❌ Send the banner as a photo (not a file)."
    elif field == "bnew":
        name = _clean_name(text)
        if not name:
            await _reply(msg, f"❌ The name must be 1-{NAME_MAX} characters. Send it again.")
            return EQ_INPUT
        field, value, extra = "bphoto", state.pop("pending_photo", None), {"name": name}
        if not value:
            await _reply(msg, "❌ This edit expired. Run /editquest again.")
            return -1
    elif field == "bname":
        value = _clean_name(text)
        err = f"❌ The name must be 1-{NAME_MAX} characters. Send it again."
    if value is None:
        await _reply(msg, err or "❌ Invalid value.")
        return EQ_INPUT
    try:
        ok, problem = await asyncio.to_thread(_apply_quest_edit, qid, field, value, extra, update.effective_user.id)
    except Exception as e:
        logger.error("edit quest failed: %s", e)
        await _reply(msg, "❌ Database error. Nothing was changed.")
        return EQ_INPUT
    if not ok:
        await _reply(msg, "❌ " + (problem or "Could not change that."))
        if problem and "no longer exists" in problem:
            context.user_data.pop(_EQ, None)
            return -1
        return EQ_INPUT
    state.pop("field", None)
    await _reply(msg, "✅ Quest updated.")
    return await _show_eq_menu(context, msg.chat_id, update.effective_user.id, qid)


# ==========================================================================
# 🪔 Festival Manager (button panel). Opened from  /help -> Owner Commands -> 🪔 Festival  or with /festival.
# Callback data (<= 64 bytes):  fs:<kind>:<owner id>[:args]
#   hub (home) | ls:<page> (festival list) | fm:<code> (festival menu) | ql:<code> (its quests) | qm:<qid> (quest menu)
#   hp (command help) | dfa:<code> / dqa:<qid> (ask before deleting) | go:<action>[:<arg>] (start a guided flow)
# ==========================================================================
PANEL_KINDS = ("hub", "ls", "fm", "ql", "qm", "hp", "dfa", "dqa")
PANEL_PAGE = 8
PANEL_TEXT_LIMIT = 3900


def _short(text, n=34):
    t = " ".join(_unhtml(text).split())
    return t if len(t) <= n else t[:n - 1] + "…"


def _panel_cut(text):
    return text if len(text) <= PANEL_TEXT_LIMIT else text[:PANEL_TEXT_LIMIT - 20] + "\n…(cut)"


def _hub_kb(uid):
    return InlineKeyboardMarkup([
        [_btn("➕ New Festival", f"fs:go:{uid}:addfestival"), _btn("🎭 New Special Character", f"fs:go:{uid}:addtempchar")],
        [_btn("📋 Festivals & Quests", f"fs:ls:{uid}:0"), _btn("✨ Special Tier Symbol", f"fs:go:{uid}:specialtier")],
        [_btn("📖 Command Help", f"fs:hp:{uid}"), _btn("« Owner Commands", f"help:{uid}:owner")]])


def _hub_text():
    now = _stamp()
    counts = {"live": 0, "upcoming": 0, "ended": 0}
    for f in all_festivals():
        counts[status_of(f, now)] += 1
    return ("🪔 Festival Manager\n\n"
            f"🟢 Live: {counts['live']}    🕒 Upcoming: {counts['upcoming']}    🔴 Ended: {counts['ended']}\n\n"
            "Create festivals, quests, temporary event characters and banners with the buttons below. "
            "Everything is asked step by step, so there are no commands to remember.\n\n"
            "Typical order:\n1️⃣ 🎭 New Special Character (the first time it asks for the Special tier symbol)\n"
            "2️⃣ ➕ New Festival\n3️⃣ open the festival → ➕ Add Quest (card, banner, pay per wish)\n\n"
            "Everyone can see all special characters and banners with /special.")


def _panel(kind, parts, uid):
    """(HTML text, keyboard) for one panel screen. Synchronous (database); call through asyncio.to_thread."""
    arg = parts[3] if len(parts) > 3 else ""
    home = [_btn("🪔 Festival Manager", f"fs:hub:{uid}")]
    if kind == "hub":
        return _hub_text(), _hub_kb(uid)
    if kind == "hp":
        return _panel_cut(_esc(help_page_text())), InlineKeyboardMarkup([home])
    if kind == "ls":
        page = int(arg) if arg.isdigit() else 0
        fests = list(reversed(all_festivals()))                 # newest first
        pages = max(1, -(-len(fests) // PANEL_PAGE))
        page = min(max(page, 0), pages - 1)
        chunk = fests[page * PANEL_PAGE:(page + 1) * PANEL_PAGE]
        icon = {"live": "🟢", "upcoming": "🕒", "ended": "🔴"}
        rows = [[_btn(f"{icon[status_of(f)]} {f['_id']} · {_short(f['name'], 24)}", f"fs:fm:{uid}:{f['_id']}")] for f in chunk]
        nav = []
        if page > 0:
            nav.append(_btn("‹ Prev", f"fs:ls:{uid}:{page - 1}"))
        if page < pages - 1:
            nav.append(_btn("Next ›", f"fs:ls:{uid}:{page + 1}"))
        if nav:
            rows.append(nav)
        rows.append([_btn("➕ New Festival", f"fs:go:{uid}:addfestival")])
        rows.append(home)
        text = "📋 Festivals\n\nTap a festival to manage it." if fests else "📋 No festivals yet.\n\nTap ➕ New Festival to create the first one."
        return text + (f"\n\nPage {page + 1}/{pages}" if pages > 1 else ""), InlineKeyboardMarkup(rows)
    if kind in ("fm", "ql", "dfa"):
        f = get_festival(arg)
        if f is None:
            return "ℹ️ That festival no longer exists.", InlineKeyboardMarkup([[_btn("« Festivals", f"fs:ls:{uid}:0")], home])
        if kind == "dfa":
            return (f"⚠️ Delete festival “{_esc(f['name'])}” ({f['_id']}) with all its quests and progress?\n"
                    f"Cards and banners people already earned are kept. This cannot be undone."), InlineKeyboardMarkup([
                [_btn("🗑 Delete", f"fs:df:{uid}:{f['_id']}:ok"), _btn("↩️ Cancel", f"fs:fm:{uid}:{f['_id']}")]])
        qs = quests_of(f["_id"])
        if kind == "fm":
            text = _panel_cut(_festival_summary(f))
            rows = [[_btn("➕ Add Quest", f"fs:go:{uid}:addquest:{f['_id']}"), _btn("✏️ Edit Festival", f"fs:go:{uid}:editfestival:{f['_id']}")],
                    [_btn(f"🎯 Quests ({len(qs)})", f"fs:ql:{uid}:{f['_id']}")],
                    [_btn("🗑 Delete Festival", f"fs:dfa:{uid}:{f['_id']}")],
                    [_btn("« Festivals", f"fs:ls:{uid}:0"), _btn("🏠 Home", f"fs:hub:{uid}")]]
            return text, InlineKeyboardMarkup(rows)
        rows = [[_btn(f"{q['_id']} · {_short(quest_label(f, q), 30)}", f"fs:qm:{uid}:{q['_id']}")] for q in qs]
        rows.append([_btn("➕ Add Quest", f"fs:go:{uid}:addquest:{f['_id']}")])
        rows.append([_btn("« Festival", f"fs:fm:{uid}:{f['_id']}"), _btn("🏠 Home", f"fs:hub:{uid}")])
        return (f"🎯 Quests of {_esc(f['name'])}\n\n" + ("Tap a quest to edit or delete it." if qs else "No quests yet.")), InlineKeyboardMarkup(rows)
    if kind in ("qm", "dqa"):
        q = get_quest(arg)
        f = get_festival(q["festival_id"]) if q else None
        if q is None or f is None:
            return "ℹ️ That quest no longer exists.", InlineKeyboardMarkup([[_btn("« Festivals", f"fs:ls:{uid}:0")], home])
        if kind == "dqa":
            return (f"⚠️ Delete quest {q['_id']}?\n{quest_label(f, q)}\n"
                    f"Progress is removed. Rewards already earned are kept."), InlineKeyboardMarkup([
                [_btn("🗑 Delete", f"fs:dq:{uid}:{q['_id']}:ok"), _btn("↩️ Cancel", f"fs:qm:{uid}:{q['_id']}")]])
        text = (f"🎯 Quest {q['_id']} · {_esc(f['name'])}\n\n{quest_label(f, q)}\n🎁 {quest_rewards_text(q)}")
        return _panel_cut(text), InlineKeyboardMarkup([
            [_btn("✏️ Edit Quest", f"fs:go:{uid}:editquest:{q['_id']}"), _btn("🗑 Delete Quest", f"fs:dqa:{uid}:{q['_id']}")],
            [_btn("« Quests", f"fs:ql:{uid}:{f['_id']}"), _btn("🏠 Home", f"fs:hub:{uid}")]])
    return "ℹ️ Unknown screen.", InlineKeyboardMarkup([home])


async def festival_command(update, context):
    """/festival - open the Festival Manager in the owner's private chat."""
    if not await _guard_owner(update) or not await _guard_private(update):
        return
    uid = update.effective_user.id
    await _reply(update.effective_message, await asyncio.to_thread(_hub_text), reply_markup=_hub_kb(uid))
    _ok(update)


async def _go_entry(update, context, expected):
    """Entry point of a guided flow started from a panel button (fs:go:<uid>:<action>[:<arg>])."""
    q = update.callback_query
    parts = (q.data or "").split(":")
    if len(parts) < 4 or q.from_user.id != int(parts[2]):
        await q.answer(NOT_YOURS_TEXT, show_alert=True)
        return -1
    if not _is_owner(q.from_user.id):
        await q.answer(DENIED_TEXT, show_alert=True)
        return -1
    await q.answer()
    arg = parts[4] if len(parts) > 4 else None
    if expected == "addfestival":
        return await addfestival_start(update, context)
    if expected == "addtempchar":
        return await addtempchar_start(update, context)
    if expected == "specialtier":
        return await specialtier_start(update, context)
    if expected == "addquest":
        return await addquest_start(update, context, code=arg)
    if expected == "editfestival":
        return await editfestival_start(update, context, code=arg)
    return await editquest_start(update, context, qid=arg)


def _go_handler(action):
    async def entry(update, context):
        return await _go_entry(update, context, action)
    entry.__name__ = f"go_{action}"
    return entry


def _go_pattern(action, arg=""):
    return rf"^fs:go:\d+:{action}{arg}$"


# ==========================================================================
# /special (everyone): catalog of every special festival character and banner (past, live and upcoming)
#   /special            -> two buttons: 🎭 Characters / 🎌 Banners, then lists in the same style as /banner
#   /special <name|code> -> straight to one item (picture + details); several matches -> selection buttons
# Callback data:  fs:sp:<uid>:<h|c|b>[:<page>]  (screens)   fs:sd:<uid>:<c|b>:<code>  (picture + details)
# ==========================================================================
def _special_sym():
    syms = _deps.get("symbols") or {}
    return syms.get(SPECIAL) or special_symbol() or "✨"


def _festival_names():
    return {f["_id"]: f for f in _col(FESTIVALS).find({})}


def special_cards():
    """Event cards that are the reward of some quest (a temp character that no quest uses yet stays secret)."""
    fests = _festival_names()
    out, seen = [], set()
    for q in sorted(_col(QUESTS).find({}), key=_qkey):
        code = (q.get("reward") or {}).get("card")
        if not code or str(code) in seen:
            continue
        row = _character_row(code)
        if not row:
            continue
        seen.add(str(code))
        out.append({"code": str(code), "row": row, "festival": fests.get(q["festival_id"])})
    return out


def special_banners():
    fests = _festival_names()
    banners = [b for b in _col(BANNERS).find({}) if b.get("festival_id")]
    banners.sort(key=lambda b: (len(str(b["_id"])), str(b["_id"])))
    for b in banners:
        b["_festival"] = fests.get(b.get("festival_id"))
    return banners


def _owned_for(uid):
    """Character codes the user owns + 'FB<code>' tokens of the special banners they earned."""
    uid = int(uid)
    owned = {str(c) for c in mongo_db.col(mongo_db.COLLECTIONS).distinct("character_code", {"user_id": uid})}
    owned |= {str(t) for t in _col(GRANTS).distinct("token", {"user_id": uid, "kind": "banner"})}
    return owned


def _equipped_banner(uid):
    doc = mongo_db.col("user_banners_v1").find_one({"_id": int(uid)})
    return (doc or {}).get("banner_code")


def _special_per_page():
    try:
        return max(1, int(_deps.get("items_per_page") or 5))
    except (TypeError, ValueError):
        return 5


def _special_home(uid):
    cards, banners = special_cards(), special_banners()
    text = ("✨ Special Collection\n\n"
            "Characters and banners you can win in festival events - past ones and coming ones.\n\n"
            f"🎭 Characters: {len(cards)}    🎌 Banners: {len(banners)}")
    return text, InlineKeyboardMarkup([[_btn("🎭 Characters", f"fs:sp:{uid}:c:0"), _btn("🎌 Banners", f"fs:sp:{uid}:b:0")]])


def _special_list(kind, page, uid):
    """Same look as the /banner list: numbered lines, 🔓/🔒 state, page buttons - plus number buttons to open an item."""
    cards = kind == "c"
    items = special_cards() if cards else special_banners()
    owned = _owned_for(uid)
    eq = None if cards else _equipped_banner(uid)
    per = _special_per_page()
    pages = max(1, -(-len(items) // per))
    page = min(max(page, 0), pages - 1)
    lines = [("🎭 Special Characters" if cards else "🎌 Special Banners") + f" (page {page + 1}/{pages})", ""]
    if not items:
        lines.append("Nothing here yet - watch for the next festival!")
    nums = []
    for i, it in enumerate(items[page * per:(page + 1) * per], page * per + 1):
        if cards:
            code, name = it["code"], str(it["row"][1])
            lines.append(f"{i}. {_esc(name)} — {code} {_special_sym()} " + ("✅" if code in owned else "🔒"))
        else:
            code, name = str(it["_id"]), str(it.get("name"))
            unlocked = banner_token(code) in owned
            lines.append(f"{i}. {_esc(name)} — {code} " + ("🔓" if unlocked else "🔒") + (" ⭐" if unlocked and eq == code else ""))
        nums.append(_btn(str(i), f"fs:sd:{uid}:{kind}:{code}"))
    if items:
        lines += ["", "Tap a number to see the picture and details.",
                  "✅/🔓 = you own it    🔒 = not earned yet"]
    rows = [nums[k:k + 5] for k in range(0, len(nums), 5)]
    if pages > 1:
        nav = []
        if page > 0:
            nav.append(_btn("◀️ Prev", f"fs:sp:{uid}:{kind}:{page - 1}"))
        nav.append(_btn(f"{page + 1}/{pages}", "fs:noop"))
        if page < pages - 1:
            nav.append(_btn("Next ▶️", f"fs:sp:{uid}:{kind}:{page + 1}"))
        rows.append(nav)
    rows.append([_btn("« Back", f"fs:sp:{uid}:h")])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


def _special_panel(arg, page, uid):
    return _special_home(uid) if arg == "h" else _special_list("b" if arg == "b" else "c", page, uid)


def special_detail(kind, code, uid):
    """(caption HTML, photo file id) of one special item, or (None, None) when it is not a special item."""
    owned = _owned_for(uid)
    if kind == "c":
        it = next((c for c in special_cards() if c["code"] == str(code)), None)
        if it is None:
            return None, None
        row, fest = it["row"], it["festival"]
        lines = [f"🎭 {_esc(str(row[1]))}"]
        if row[2]:
            lines.append(f"🎬 {_esc(str(row[2]))}")
        lines.append(f"🏷 {_esc(_special_sym())} {SPECIAL}")
        lines.append(f"🔢 Code: {it['code']}")
        if fest:
            lines.append(f"🪔 From: {_esc(str(fest['name']))}")
        lines.append("✅ You own this character." if it["code"] in owned else "🔒 You don't own this character yet.")
        return "\n".join(lines), (row[5] if len(row) > 5 else None)
    b = next((x for x in special_banners() if str(x["_id"]) == str(code)), None)
    if b is None:
        return None, None
    unlocked = banner_token(b["_id"]) in owned
    equipped = unlocked and _equipped_banner(uid) == b["_id"]
    lines = [f"🎌 {_esc(str(b['name']))}", f"Code: {b['_id']}"]
    if b.get("_festival"):
        lines.append(f"🪔 From: {_esc(str(b['_festival']['name']))}")
    lines.append("Status: " + ("🔓 Unlocked" if unlocked else "🔒 Not earned yet") + ("  ⭐ EQUIPPED" if equipped else ""))
    if unlocked and not equipped:
        lines += ["", f"Equip it with /usebanner {b['_id']}"]
    return "\n".join(lines), b.get("photo_file_id")


def _special_search(arg):
    """[(kind, code, label)] of special items whose code or name matches."""
    q = " ".join(str(arg).split()).casefold()
    out = []
    raw = str(arg).strip()
    two = raw.isdigit() and len(raw) == 2 and 1 <= int(raw) <= 99        # exactly 2 digits = a special banner code
    code4 = normalize_char_code(raw) if raw.isdigit() and not two else None
    scode = raw if two else None
    for c in special_cards():
        name = str(c["row"][1])
        if (code4 and c["code"] == code4) or (not code4 and q in name.casefold()):
            out.append(("c", c["code"], name))
    for b in special_banners():
        name = str(b.get("name"))
        if (scode and str(b["_id"]) == scode) or (not scode and not code4 and q in name.casefold()):
            out.append(("b", str(b["_id"]), name))
    return out


async def _send_special_detail(bot, chat_id, thread, kind, code, uid):
    caption, photo = await asyncio.to_thread(special_detail, kind, code, uid)
    if caption is None:
        await _send(bot, chat_id, "❌ That special item no longer exists. See /special.", thread)
        return
    if photo and len(caption) <= CAPTION_LIMIT:
        try:
            await bot.send_photo(chat_id=chat_id, photo=photo, caption=caption, parse_mode="HTML", message_thread_id=thread)
            return
        except Exception as e:
            logger.info("special photo failed: %s", e)
    await _send(bot, chat_id, caption, thread)


async def special_command(update, context):
    msg, uid = update.effective_message, update.effective_user.id
    arg = " ".join(context.args or []).strip()
    thread = msg.message_thread_id if getattr(msg, "is_topic_message", False) else None
    try:
        if not arg:
            text, kb = await asyncio.to_thread(_special_home, uid)
            await _reply(msg, text, reply_markup=kb)
            _ok(update)
            return
        matches = await asyncio.to_thread(_special_search, arg)
    except Exception as e:
        logger.error("special failed: %s", e)
        await _reply(msg, "❌ Could not load the special collection right now. Please try again.")
        return
    if not matches:
        await _reply(msg, "❌ No special character or banner matches that. See /special.")
        return
    if len(matches) == 1:
        await _send_special_detail(context.bot, msg.chat_id, thread, matches[0][0], matches[0][1], uid)
        _ok(update)
        return
    rows = [[_btn(f"{'🎭' if k == 'c' else '🎌'} {_short(name, 30)} ({code})", f"fs:sd:{uid}:{k}:{code}")]
            for k, code, name in matches[:10]]
    await _reply(msg, "Several special items match. Tap the one you want:", reply_markup=InlineKeyboardMarkup(rows))
    _ok(update)


# ==========================================================================
# /specialtier  (owner): set / change the Special tier symbol
# ==========================================================================
ST_INPUT = 70


async def specialtier_start(update, context):
    if not await _guard_owner(update) or not await _guard_private(update):
        return -1
    cur = await asyncio.to_thread(special_symbol)
    await _reply(update.effective_message,
                 "✨ Special tier\n\n" + (f"Current symbol: {cur}\n\n" if cur else "The Special tier has no symbol yet.\n\n") +
                 "Send the SYMBOL for the Special tier (one emoji or a short symbol, like 💠 is for Celestial).\n\n"
                 "Send /cancel to stop.")
    return ST_INPUT


async def specialtier_input(update, context):
    if not await _guard_owner(update):
        return -1
    sym = _clean_symbol(update.effective_message.text)
    if not sym:
        await _reply(update.effective_message, f"❌ Send one symbol (max {SYMBOL_MAX} characters, no spaces).")
        return ST_INPUT
    try:
        await asyncio.to_thread(set_special_symbol, sym)
    except Exception as e:
        logger.error("set special symbol failed: %s", e)
        await _reply(update.effective_message, "❌ Database error. Nothing was saved.")
        return -1
    await _reply(update.effective_message, f"✅ Special tier symbol saved: {sym}\nSpecial characters now show as “{sym} {SPECIAL}”.",
                 reply_markup=InlineKeyboardMarkup([[_btn("🪔 Festival Manager", f"fs:hub:{update.effective_user.id}")]]))
    return -1


# ==========================================================================
# /addtempchar  (name -> anime -> worth -> code -> photo)  [first time: the Special symbol]
# Creates a character in the SPECIAL tier that is registered as an EVENT CARD from the first second: it never shows in the
# character list, shop, spawns or searches. Only quests give it out (use its code in /addquest).
# ==========================================================================
TC_NAME, TC_ANIME, TC_WORTH, TC_CODE, TC_PHOTO, TC_SYMBOL = range(60, 66)
_TC = "fs_tc"


async def addtempchar_start(update, context):
    if not await _guard_owner(update) or not await _guard_private(update):
        return -1
    context.user_data[_TC] = {}
    if not await asyncio.to_thread(special_symbol):
        await _reply(update.effective_message,
                     "✨ The Special tier has no symbol yet.\nSend the SYMBOL for the Special tier (one emoji or a short "
                     "symbol, like 💠 is for Celestial).\n\nSend /cancel to stop.")
        return TC_SYMBOL
    await _reply(update.effective_message,
                 "🎭 New TEMPORARY special character - step 1/5\nSend the character NAME.\n\n"
                 "It is hidden from every list from the start and is only given out by festival quests.\n"
                 "Send /cancel to stop.")
    return TC_NAME


async def addtempchar_symbol(update, context):
    if not await _guard_owner(update):
        return -1
    sym = _clean_symbol(update.effective_message.text)
    if not sym:
        await _reply(update.effective_message, f"❌ Send one symbol (max {SYMBOL_MAX} characters, no spaces).")
        return TC_SYMBOL
    await asyncio.to_thread(set_special_symbol, sym)
    await _reply(update.effective_message, f"✅ Special tier symbol saved: {sym}\n\n🎭 Step 1/5 - send the character NAME.")
    return TC_NAME


async def addtempchar_name(update, context):
    if not await _guard_owner(update):
        return -1
    name = _clean_name(update.effective_message.text, 60)
    if not name:
        await _reply(update.effective_message, "❌ Send a valid name (max 60 characters).")
        return TC_NAME
    context.user_data.setdefault(_TC, {})["name"] = name
    await _reply(update.effective_message, "2/5 - Send the ANIME name, or send skip.")
    return TC_ANIME


async def addtempchar_anime(update, context):
    if not await _guard_owner(update):
        return -1
    text = " ".join((update.effective_message.text or "").split())
    context.user_data.setdefault(_TC, {})["anime"] = "" if _is_none_word(text) or len(text) > 80 else text
    await _reply(update.effective_message, "3/5 - Send the WORTH in Berrys (a number).")
    return TC_WORTH


async def addtempchar_worth(update, context):
    if not await _guard_owner(update):
        return -1
    n = _to_int(update.effective_message.text, 0, 100_000_000)
    if n is None:
        await _reply(update.effective_message, "❌ Worth must be a number.")
        return TC_WORTH
    context.user_data.setdefault(_TC, {})["worth"] = n
    await _reply(update.effective_message, "4/5 - Send a unique 4-digit CODE (0001-9999).")
    return TC_CODE


async def addtempchar_code(update, context):
    if not await _guard_owner(update):
        return -1
    code = normalize_char_code(update.effective_message.text)
    if not code or len(str(update.effective_message.text).strip()) != 4:
        await _reply(update.effective_message, "❌ The code must be exactly 4 digits (0001-9999).")
        return TC_CODE
    if await asyncio.to_thread(_character_row, code):
        await _reply(update.effective_message, "❌ That code already exists. Send another code.")
        return TC_CODE
    context.user_data.setdefault(_TC, {})["code"] = code
    await _reply(update.effective_message, "5/5 - Send the character PHOTO, or send skip.")
    return TC_PHOTO


def _create_temp_character(d):
    mongo_db.insert_character(d["code"], d["name"], d["anime"], SPECIAL, d["worth"], d.get("photo"), [])
    register_card(d["code"], None)                  # hidden immediately, even before any quest uses it


async def addtempchar_photo(update, context):
    if not await _guard_owner(update):
        return -1
    msg = update.effective_message
    d = context.user_data.get(_TC)
    if not d or "code" not in d:
        await _reply(msg, "❌ This setup expired. Run /addtempchar again.")
        return -1
    if msg.photo:
        d["photo"] = msg.photo[-1].file_id
    elif _is_none_word(msg.text or ""):
        d["photo"] = None
    else:
        await _reply(msg, "❌ Send a photo (not a file), or send skip.")
        return TC_PHOTO
    context.user_data.pop(_TC, None)
    try:
        await asyncio.to_thread(_create_temp_character, d)
    except Exception as e:
        if type(e).__name__ == "DuplicateKeyError":
            await _reply(msg, "❌ That name or code already exists. Nothing was created.")
        else:
            logger.error("temp character failed: %s", e)
            await _reply(msg, "❌ Could not create the character. Nothing was created.")
        return -1
    await _reply(msg, f"✅ Special character created!\n🎭 {_esc(d['name'])}\n🏷 {_esc(_special_sym())} {SPECIAL}\n"
                      f"💰 {d['worth']}\n🔢 {d['code']}\n\n"
                      f"It is hidden from the normal lists. Give it out as an event card in a quest (card code {d['code']}).",
                 parse_mode="HTML",
                 reply_markup=InlineKeyboardMarkup([[_btn("🪔 Festival Manager", f"fs:hub:{update.effective_user.id}")]]))
    return -1


# ==========================================================================
# Help text (owned by this module)
# ==========================================================================
HELP_KEY = "festival"
HELP_LABEL = "🪔 Festival"

PUBLIC_HELP_SECTION = (
    "🪔 Festival Quests\n"
    "/quests — See festival rewards and your progress\n"
    "/festivals — See running and upcoming festivals\n"
    "/special — See special festival characters and banners\n\n"
    "🎁 Invite & Mystery Boxes\n"
    "/invite — Get your invite link and earn Mystery Boxes\n\n"
)


def help_page_text():
    entries = [
        ("/festival", "Open the Festival Manager (buttons for everything)"),
        ("/addfestival", "Create a festival (guided, PM only): name, wish phrase, start and end time (India time)"),
        ("/festivals", "List every festival with its code, status and quests (everyone can use it; the manage commands show only to you)"),
        ("/editfestival <code>", "Change a festival's name, wish phrase, start or end"),
        ("/delfestival <code>", "Delete a festival and its quests (earned cards and banners are kept)"),
        ("/addtempchar", "Create a SPECIAL-tier event character (hidden from the normal lists; only quests give it out)"),
        ("/specialtier", "Set or change the symbol of the Special tier (asked once, the first time)"),
        ("/addquest <code>", "Add a quest (guided, PM only): type, target, rewards (Berrys, Stones, event card, event banner)"),
        ("/editquest <id>", "Change a quest's target or rewards"),
        ("/delquest <id>", "Delete a quest"),
        ("/quests", "Players: festival rewards and progress (public)"),
        ("/special", "Everyone: catalog of all special characters and banners (public)"),
        ("/boxes", "Invite system and Mystery Box settings (buttons): invite rewards, invites needed, what each box gives, on/off"),
        ("/invite", "Everyone: invite link, progress, claim and open Mystery Boxes (public)"),
    ]
    lines = ["🪔 Festival Quests (Owner)", "", "👉 Easiest: /help -> Owner Commands -> 🪔 Festival (or /festival) opens the "
             "Festival Manager with buttons for everything below.", "", "📌 Overview",
             "A festival is a timed event. Quests only count while it is live; what people earn stays forever. "
             "Event cards are hidden from every character list, the shop and spawns and only show in the collection of "
             "the people who earned them. Event banners (2-digit codes 01, 02, ...) are hidden from the normal banner list "
             "and only show in /banner for the people who earned them. Everyone can browse them in /special.",
             "", "🎯 Quest types: " + ", ".join(f"{e} {l}" for e, l in QUEST_TYPES.values()),
             "", "⌨️ Commands & usage"]
    for n, (syntax, desc) in enumerate(entries, 1):
        lines.append(f"{n}. {syntax} - {desc}")
    lines += ["", "💡 Players wish each other by REPLYING to a message with the festival phrase (any capitals).",
              "💰 Pay-per-wish quest: every wish to a different person pays at once (example: 100 Berrys per \"Happy Diwali\"), "
              "up to a per-player cap. The wished person can be paid too.",
              "🎭 Typical setup: /addtempchar -> /addfestival -> /addquest (card + banner) and /addquest (pay per wish)."]
    return "\n".join(lines)


def help_module():
    """(key, label, text) in the shape of bot.py's HELP_MODULES entries."""
    return (HELP_KEY, HELP_LABEL, help_page_text())


# ==========================================================================
# Registration
# ==========================================================================
def register(app):
    """Attach every festival handler. Call bind(...) first. Safe to call once at start-up."""
    from telegram.ext import CallbackQueryHandler, CommandHandler, ConversationHandler, MessageHandler, filters
    try:
        ensure_indexes()
    except Exception as e:          # never block the bot from starting; indexes are retried on first use
        logger.warning("festival: index creation deferred (%s)", e)
    try:
        apply_symbol()              # puts the saved Special tier symbol into bot.SYMBOL
    except Exception as e:
        logger.warning("festival: special symbol not loaded (%s)", e)
    text = filters.TEXT & ~filters.COMMAND
    timeout = _deps.get("conv_timeout")
    fallbacks = [CommandHandler("cancel", _cancel_flow)]

    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("addfestival", addfestival_start),
                      CallbackQueryHandler(_go_handler("addfestival"), pattern=_go_pattern("addfestival"))],
        states={
            AF_NAME: [MessageHandler(text, addfestival_name)],
            AF_PHRASE: [MessageHandler(text, addfestival_phrase)],
            AF_START: [MessageHandler(text, addfestival_start_time)],
            AF_END: [MessageHandler(text, addfestival_end_time)],
            AF_CONFIRM: [CallbackQueryHandler(addfestival_confirm, pattern=r"^fs:af:\d+:[0-9a-f]{8}:(ok|no)$")],
        },
        fallbacks=fallbacks, allow_reentry=True, conversation_timeout=timeout))
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("editfestival", editfestival_start),
                      CallbackQueryHandler(_go_handler("editfestival"), pattern=_go_pattern("editfestival", r":\d{3}"))],
        states={
            EF_MENU: [CallbackQueryHandler(editfestival_menu, pattern=r"^fs:ef:\d+:\d{3}:(name|phrase|start|end|done)$")],
            EF_INPUT: [MessageHandler(text, editfestival_input)],
        },
        fallbacks=fallbacks, allow_reentry=True, conversation_timeout=timeout))
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("addtempchar", addtempchar_start),
                      CallbackQueryHandler(_go_handler("addtempchar"), pattern=_go_pattern("addtempchar"))],
        states={
            TC_SYMBOL: [MessageHandler(text, addtempchar_symbol)],
            TC_NAME: [MessageHandler(text, addtempchar_name)],
            TC_ANIME: [MessageHandler(text, addtempchar_anime)],
            TC_WORTH: [MessageHandler(text, addtempchar_worth)],
            TC_CODE: [MessageHandler(text, addtempchar_code)],
            TC_PHOTO: [MessageHandler(filters.PHOTO, addtempchar_photo), MessageHandler(text, addtempchar_photo)],
        },
        fallbacks=fallbacks, allow_reentry=True, conversation_timeout=timeout))
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("specialtier", specialtier_start),
                      CallbackQueryHandler(_go_handler("specialtier"), pattern=_go_pattern("specialtier"))],
        states={ST_INPUT: [MessageHandler(text, specialtier_input)]},
        fallbacks=fallbacks, allow_reentry=True, conversation_timeout=timeout))
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("addquest", addquest_start),
                      CallbackQueryHandler(_go_handler("addquest"), pattern=_go_pattern("addquest", r":\d{3}"))],
        states={
            AQ_INPUT: [
                CallbackQueryHandler(addquest_type, pattern=r"^fs:qt:\d+:[0-9a-f]{8}:(wish_send|wish_receive|catch|daily|wish_pay)$"),
                CallbackQueryHandler(addquest_confirm, pattern=r"^fs:qc:\d+:[0-9a-f]{8}:(ok|no)$"),
                MessageHandler(filters.PHOTO, addquest_input),
                MessageHandler(text, addquest_input),
            ],
        },
        fallbacks=fallbacks, allow_reentry=True, conversation_timeout=timeout))
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("editquest", editquest_start),
                      CallbackQueryHandler(_go_handler("editquest"), pattern=_go_pattern("editquest", r":Q\d+"))],
        states={
            EQ_MENU: [CallbackQueryHandler(editquest_menu, pattern=r"^fs:eq:\d+:Q\d+:(target|berrys|stones|card|bphoto|bname|rberrys|done)$")],
            EQ_INPUT: [MessageHandler(filters.PHOTO, editquest_input), MessageHandler(text, editquest_input)],
        },
        fallbacks=fallbacks, allow_reentry=True, conversation_timeout=timeout))
    for name, callback in (("quests", quests_command), ("special", special_command), ("festival", festival_command),
                           ("festivals", festivals_command),
                           ("delfestival", delfestival_command), ("delquest", delquest_command)):
        app.add_handler(CommandHandler(name, callback))
    app.add_handler(CallbackQueryHandler(fs_callback, pattern=r"^fs:"))
    # Wishes: a reply in a group that contains the phrase. Own group + block=False: never delays or replaces another handler.
    app.add_handler(MessageHandler(text & filters.REPLY & filters.ChatType.GROUPS, wish_handler, block=False), group=47)
    register_referrals(app)         # /invite + owner /boxes + referral tracking on /start ref_<code>


# ==========================================================================
# INVITE / REFERRAL SYSTEM + MYSTERY BOXES
#   /invite  (everyone)  link, invites, progress, claim + open boxes     /boxes  (Owner)  every setting, with buttons
#   Boxes live in users.items.box_<tier> so /item (fusion.py) can show them: rewards.item_lines(user_doc)
# ==========================================================================
TIER_ORDER = ("bronze", "gold", "platinum", "diamond")
TIER_META = {"bronze": ("🥉", "Bronze"), "gold": ("🥇", "Gold"), "platinum": ("🥈", "Platinum"), "diamond": ("🔷", "Diamond")}
# Starting values only - the Owner changes every one of them from /boxes (nothing here needs a code edit).
DEFAULT_TIERS = {
    "bronze":   {"enabled": True, "invites": 10,  "boxes": 1, "chars": 0, "rarity": "Rare",      "b_min": 50,  "b_max": 200,  "s_min": 0, "s_max": 0},
    "gold":     {"enabled": True, "invites": 25,  "boxes": 1, "chars": 1, "rarity": "Rare",      "b_min": 100, "b_max": 300,  "s_min": 1, "s_max": 3},
    "platinum": {"enabled": True, "invites": 50,  "boxes": 1, "chars": 1, "rarity": "Epic",      "b_min": 200, "b_max": 500,  "s_min": 2, "s_max": 6},
    "diamond":  {"enabled": True, "invites": 100, "boxes": 1, "chars": 1, "rarity": "Legendary", "b_min": 500, "b_max": 1000, "s_min": 5, "s_max": 10},
}
INVITES_MAX, BOXES_MAX, CHARS_MAX = 100_000, 100, 20
RF_INPUT = 9101


def _tier_label(tier):
    emoji, name = TIER_META[tier]
    return f"{emoji} {name}"


def _box_field(tier):
    return f"items.box_{tier}"


def _dotted_int(doc, path):
    cur = doc
    for part in path.split("."):
        if not isinstance(cur, dict) or part not in cur:
            return 0
        cur = cur[part]
    try:
        return int(cur or 0)
    except (TypeError, ValueError):
        return 0


def item_lines(user_doc):
    """Lines for /item (fusion.py): one per Mystery Box type the user owns. Boxes are only listed, never opened there."""
    lines = []
    for tier in TIER_ORDER:
        n = _dotted_int(user_doc or {}, _box_field(tier))
        if n > 0:
            lines.append(f"{TIER_META[tier][0]} {TIER_META[tier][1]} Mystery Box: {n}")
    return lines


# ---------------- settings ----------------
def get_config():
    doc = _col(REF_SETTINGS).find_one({"_id": "config"}) or {}
    saved = doc.get("tiers") or {}
    tiers = {}
    for tier in TIER_ORDER:
        merged = dict(DEFAULT_TIERS[tier])
        merged.update(saved.get(tier) or {})
        tiers[tier] = merged
    return {"enabled": bool(doc.get("enabled", True)), "tiers": tiers}


def set_system_enabled(value):
    _col(REF_SETTINGS).update_one({"_id": "config"}, {"$set": {"enabled": bool(value)}}, upsert=True)


def set_tier_fields(tier, fields):
    _col(REF_SETTINGS).update_one({"_id": "config"}, {"$set": {f"tiers.{tier}.{k}": v for k, v in fields.items()}}, upsert=True)


def _fmt_range(lo, hi):
    if hi <= 0:
        return "off"
    return str(hi) if lo == hi else f"{lo}-{hi}"


def _parse_range(text, cap):
    s = (text or "").strip().lower()
    if s in ("0", "off", "none", "no"):
        return 0, 0
    m = re.fullmatch(r"(\d+)\s*(?:-|–|—|to)\s*(\d+)", s)
    if m:
        lo, hi = int(m.group(1)), int(m.group(2))
    elif s.isdigit():
        lo = hi = int(s)
    else:
        return None
    if lo > hi or hi < 1 or hi > cap:
        return None
    return lo, hi


def apply_edit_sync(tier, field, text):
    """Validate and save one Owner edit. Returns (ok, message)."""
    s = (text or "").strip()
    label = _tier_label(tier)
    if field in ("invites", "boxes", "chars"):
        low = 0 if field == "chars" else 1
        high = {"invites": INVITES_MAX, "boxes": BOXES_MAX, "chars": CHARS_MAX}[field]
        if not (s.isascii() and s.isdigit()) or not low <= int(s) <= high:
            return False, f"❌ Send a whole number from {low} to {high}."
        set_tier_fields(tier, {field: int(s)})
        word = {"invites": "Invites needed", "boxes": "Boxes per claim", "chars": "Characters per box"}[field]
        return True, f"{label}: {word} is now {int(s)}."
    if field == "rarity":
        match = next((r for r in _rarities() if r.lower() == s.lower()), None)
        if not match:
            return False, "❌ Unknown rarity. Choose one of: " + ", ".join(_rarities())
        set_tier_fields(tier, {"rarity": match})
        return True, f"{label}: characters now come from {match}."
    if field in ("berrys", "stones"):
        cap = BERRYS_MAX if field == "berrys" else STONES_MAX
        rng = _parse_range(s, cap)
        if rng is None:
            return False, f"❌ Send a range like 50-500 (minimum can't be above maximum, top is {cap}), one number, or 0 to turn it off."
        key = "b" if field == "berrys" else "s"
        set_tier_fields(tier, {f"{key}_min": rng[0], f"{key}_max": rng[1]})
        return True, f"{label}: {field.capitalize()} is now {_fmt_range(*rng)}."
    return False, "❌ Unknown setting."


# ---------------- invite links and referrals ----------------
def new_token(uid):
    for _ in range(6):
        token = secrets.token_hex(4)
        try:
            _col(REF_LINKS).insert_one({"_id": token, "user_id": int(uid), "ts": time.time()})
            return token
        except DuplicateKeyError:
            continue
    raise RuntimeError("could not create an invite token")


def current_token(uid):
    doc = _col(REF_LINKS).find_one({"user_id": int(uid)}, sort=[("ts", -1)])
    return doc["_id"] if doc else new_token(uid)


def resolve_token(token):
    """Inviter's user id for a link token (old links keep working after a new one is generated); plain ids are accepted too."""
    token = (token or "").strip().lower()
    if not token or len(token) > 32:
        return None
    if token.isdigit():
        return int(token)
    doc = _col(REF_LINKS).find_one({"_id": token})
    return int(doc["user_id"]) if doc else None


def record_referral_sync(invitee, inviter, token):
    """Returns the inviter's new total when a NEW referral was stored, otherwise None.
    Only a brand-new user counts: existing members, self-referrals and repeats are ignored (the invitee id is the unique key)."""
    invitee, inviter = int(invitee), int(inviter)
    if invitee == inviter:
        return None
    if mongo_db.get_user(invitee) is not None:      # already a member - runs before /start saves the profile
        return None
    if mongo_db.get_user(inviter) is None:
        return None
    try:
        _col(REFERRALS).insert_one({"_id": invitee, "inviter": inviter, "token": token, "ts": time.time()})
    except DuplicateKeyError:
        return None
    return _col(REFERRALS).count_documents({"inviter": inviter})


async def ref_start_handler(update, context):
    """/start ref_<token>: runs before the main /start handler (group -97) and never raises or stops it."""
    user, args = update.effective_user, context.args
    if user is None or user.is_bot or not args or not args[0].lower().startswith("ref_"):
        return
    token = args[0][4:]
    try:
        cfg = await asyncio.to_thread(get_config)
        if not cfg["enabled"]:
            return
        inviter = await asyncio.to_thread(resolve_token, token)
        if not inviter:
            return
        total = await asyncio.to_thread(record_referral_sync, user.id, inviter, token.lower())
        if not total:
            return
        lines = [f"🎉 <b>{_esc(user.first_name or 'A new member')}</b> joined using your invite link!", f"👥 Total invites: <b>{total}</b>"]
        for tier in TIER_ORDER:
            c = cfg["tiers"][tier]
            if c["enabled"] and c["invites"] == total:
                lines.append(f"🎁 You unlocked the {_tier_label(tier)} Mystery Box! Open /invite to claim it.")
        await context.bot.send_message(chat_id=inviter, text="\n".join(lines), parse_mode="HTML")
    except Exception as e:
        logger.warning("referral: could not process %r: %s", token, e)


# ---------------- claiming and opening boxes ----------------
def claim_sync(uid, tier):
    """('ok', boxes) | ('low', invites_missing) | ('dup', None) | ('off', None). A tier can be claimed once per user (unique id)."""
    uid = int(uid)
    cfg = get_config()
    c = cfg["tiers"].get(tier)
    if not cfg["enabled"] or not c or not c["enabled"]:
        return "off", None
    total = _col(REFERRALS).count_documents({"inviter": uid})
    if total < c["invites"]:
        return "low", c["invites"] - total
    claim_id = f"{uid}:{tier}"
    try:
        _col(REF_CLAIMS).insert_one({"_id": claim_id, "user_id": uid, "tier": tier, "boxes": c["boxes"], "invites": total, "ts": time.time()})
    except DuplicateKeyError:
        return "dup", None
    try:
        res = mongo_db.col(mongo_db.USERS).update_one({"_id": uid}, {"$inc": {_box_field(tier): int(c["boxes"])}})
        if res.matched_count == 0:
            raise RuntimeError("user row missing")
    except Exception:
        _col(REF_CLAIMS).delete_one({"_id": claim_id})      # nothing was given, so the claim must stay available
        raise
    return "ok", int(c["boxes"])


def open_box_sync(uid, tier):
    """Open one box. The box is taken atomically, so two taps can never open the same box. Returns a result dict, or None."""
    uid = int(uid)
    users = mongo_db.col(mongo_db.USERS)
    field = _box_field(tier)
    before = users.find_one_and_update({"_id": uid, field: {"$gte": 1}}, {"$inc": {field: -1}})
    if before is None:
        return None
    left = _dotted_int(before, field) - 1
    c = get_config()["tiers"][tier]
    undo = []
    try:
        picks = []
        if c["chars"] > 0:
            pool = filter_hidden(mongo_db.get_characters_by_rarity(c["rarity"]))
            picks = random.sample(pool, min(int(c["chars"]), len(pool)))
        berrys = random.randint(int(c["b_min"]), int(c["b_max"])) if c["b_max"] > 0 else 0
        stones = random.randint(int(c["s_min"]), int(c["s_max"])) if c["s_max"] > 0 else 0
        if berrys:
            if not mongo_db.add_coins(uid, berrys):
                raise RuntimeError("could not pay Berrys")
            undo.append(lambda n=berrys: mongo_db.add_coins(uid, -n))
        if stones:
            if not mongo_db.add_special_stones(uid, stones):
                raise RuntimeError("could not pay Stones")
            undo.append(lambda n=stones: mongo_db.add_special_stones(uid, -n))
        got = []
        for row in picks:
            copy_id = mongo_db.add_collection(uid, row[0], _grant_stamp())
            undo.append(lambda cid=copy_id: mongo_db.delete_collection_by_id(cid))
            got.append((row[0], row[1], row[3]))
    except Exception:
        for fn in reversed(undo):       # take back anything already paid, then give the box back
            try:
                fn()
            except Exception as e:
                logger.warning("referral: undo failed: %s", e)
        users.update_one({"_id": uid}, {"$inc": {field: 1}})
        raise
    symbols = _deps.get("symbols") or {}
    parts = [f"{symbols.get(r, '🎭')} {n} [{code}]" for code, n, r in got]
    if berrys:
        parts.append(f"🪙 +{berrys} Berrys")
    if stones:
        parts.append(f"💎 +{stones} Stones")
    try:
        _col(REF_OPENS).insert_one({"user_id": uid, "tier": tier, "text": " · ".join(parts) or "empty box", "ts": time.time()})
    except Exception as e:
        logger.warning("referral: open log failed: %s", e)
    return {"chars": got, "berrys": berrys, "stones": stones, "left": max(left, 0)}


# ---------------- /invite ----------------
def _invite_state_sync(uid):
    uid = int(uid)
    cfg = get_config()
    total = _col(REFERRALS).count_documents({"inviter": uid})
    claims = {d["tier"]: d for d in _col(REF_CLAIMS).find({"user_id": uid})}
    udoc = mongo_db.get_user(uid) or {}
    boxes = {t: _dotted_int(udoc, _box_field(t)) for t in TIER_ORDER}
    recent = list(_col(REF_OPENS).find({"user_id": uid}).sort("ts", -1).limit(3))
    return cfg, total, claims, boxes, current_token(uid), recent


def _invite_page(uid, bot_username, state):
    cfg, total, claims, boxes, token, recent = state
    link = f"https://t.me/{bot_username}?start=ref_{token}"
    lines = ["🎁 <b>INVITE &amp; EARN</b>", ""]
    if not cfg["enabled"]:
        lines += ["⚠️ The invite system is turned off right now.", ""]
    lines += ["🔗 Your invite link (tap it to copy):", f"<code>{_esc(link)}</code>", "", f"👥 Total invites: <b>{total}</b>"]
    live = sorted(((t, cfg["tiers"][t]) for t in TIER_ORDER if cfg["tiers"][t]["enabled"]), key=lambda x: x[1]["invites"])
    nxt = next(((t, c) for t, c in live if c["invites"] > total), None)
    if nxt:
        need = nxt[1]["invites"]
        filled = min(10, total * 10 // need)
        lines += [f"📈 Progress: {total}/{need}  " + "▰" * filled + "▱" * (10 - filled),
                  f"🎯 Next invite reward: {_tier_label(nxt[0])} Mystery Box at {need} invites"]
    elif live:
        lines.append("🏁 You have reached every invite reward!")
    claimable = []
    if live:
        lines += ["", "🏆 <b>Invite Rewards</b>"]
    for tier, c in live:
        if tier in claims:
            mark, note = "✅", "claimed"
        elif total >= c["invites"]:
            mark, note = "🎁", "ready to claim!"
            claimable.append((tier, c["boxes"]))
        else:
            mark, note = "🔒", f"{c['invites'] - total} more to go"
        times = f" ×{c['boxes']}" if c["boxes"] > 1 else ""
        lines.append(f"{mark} {_tier_label(tier)} Box{times} - {c['invites']} invites · {note}")
    owned = [(t, n) for t, n in boxes.items() if n > 0]
    if owned:
        lines += ["", "📦 <b>Your Mystery Boxes</b>", "  ".join(f"{_tier_label(t)} ×{n}" for t, n in owned), "They also show in /item."]
    if recent:
        lines += ["", "🎲 <b>Recent openings</b>"] + [f"{TIER_META.get(d['tier'], ('📦',))[0]} {_esc(d.get('text', ''))}" for d in recent]
    lines += ["", "💡 Share your link. When someone new starts the bot with it, it counts as an invite."]
    share = ("https://t.me/share/url?url=" + _urlquote(link, safe="") + "&text="
             + _urlquote("Join me on this anime bot - catch rare characters and build your collection! 🎌", safe=""))
    rows = [[InlineKeyboardButton("📤 Share Link", url=share), InlineKeyboardButton("🔄 New Link", callback_data=f"rf:u:{uid}:gen")]]
    for tier, n in claimable:
        rows.append([InlineKeyboardButton(f"🎁 Claim {_tier_label(tier)} Box" + (f" ×{n}" if n > 1 else ""), callback_data=f"rf:u:{uid}:claim:{tier}")])
    if owned:
        rows.append([InlineKeyboardButton("📦 Open a Mystery Box", callback_data=f"rf:u:{uid}:open")])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


async def invite_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return
    fn = _deps.get("save_user")
    if fn:
        try:
            await fn(user)
        except Exception as e:
            logger.warning("referral: save_user failed: %s", e)
    state = await asyncio.to_thread(_invite_state_sync, user.id)
    text, kb = _invite_page(user.id, context.bot.username, state)
    await _reply(msg, text, parse_mode="HTML", reply_markup=kb)


async def _show_invite(q, context, uid):
    state = await asyncio.to_thread(_invite_state_sync, uid)
    text, kb = _invite_page(uid, context.bot.username, state)
    await _edit(q, text, kb)


async def rf_user_callback(update, context):
    q = update.callback_query
    parts = (q.data or "").split(":")           # rf:u:<user id>:<action>[:<tier>]
    try:
        uid, action = int(parts[2]), parts[3]
    except (IndexError, ValueError):
        await q.answer()
        return
    if q.from_user.id != uid:
        await q.answer(NOT_YOURS_TEXT, show_alert=True)
        return
    tier = parts[4] if len(parts) > 4 else None
    if tier is not None and tier not in TIER_ORDER:
        await q.answer()
        return
    note = None
    try:
        if action == "gen":
            await asyncio.to_thread(new_token, uid)
            note = "🔄 New invite link created. Your old links still work."
        elif action == "claim" and tier:
            status, val = await asyncio.to_thread(claim_sync, uid, tier)
            note = {"ok": f"🎁 Claimed! {val} × {_tier_label(tier)} Mystery Box added. See /item.",
                    "low": f"🔒 You need {val} more invite(s) for this box.",
                    "dup": "✅ You already claimed this box.",
                    "off": "⚠️ This reward is not available right now."}[status]
        elif action == "open":
            state = await asyncio.to_thread(_invite_state_sync, uid)
            owned = [(t, n) for t, n in state[3].items() if n > 0]
            await q.answer()
            if not owned:
                await _show_invite(q, context, uid)
                return
            rows = [[InlineKeyboardButton(f"{_tier_label(t)} ×{n}", callback_data=f"rf:u:{uid}:do:{t}")] for t, n in owned]
            rows.append([InlineKeyboardButton("⬅️ Back", callback_data=f"rf:u:{uid}:home")])
            await _edit(q, "📦 <b>OPEN A MYSTERY BOX</b>\n\nPick a box to open. The rewards go straight to your account.",
                        InlineKeyboardMarkup(rows))
            return
        elif action == "do" and tier:
            result = await asyncio.to_thread(open_box_sync, uid, tier)
            await q.answer()
            if result is None:
                await _show_invite(q, context, uid)
                return
            lines = [f"🎉 <b>{_tier_label(tier)} Mystery Box opened!</b>", ""]
            lines += [f"{(_deps.get('symbols') or {}).get(r, '🎭')} {_esc(n)} [{code}] ({_esc(r)})" for code, n, r in result["chars"]]
            if result["berrys"]:
                lines.append(f"🪙 +{result['berrys']} Berrys")
            if result["stones"]:
                lines.append(f"💎 +{result['stones']} Special Stones")
            if len(lines) == 2:
                lines.append("The box was empty. Ask the Owner to check the box settings.")
            rows = []
            if result["left"] > 0:
                rows.append([InlineKeyboardButton(f"📦 Open another ({result['left']} left)", callback_data=f"rf:u:{uid}:do:{tier}")])
            rows.append([InlineKeyboardButton("⬅️ Back", callback_data=f"rf:u:{uid}:home")])
            await _edit(q, "\n".join(lines), InlineKeyboardMarkup(rows))
            return
    except Exception as e:
        logger.warning("referral callback %s failed: %s", action, e)
        note = "❌ Something went wrong. Please try again."
    await q.answer(note or "")
    await _show_invite(q, context, uid)


# ---------------- /boxes (Owner) ----------------
def _hub_page(cfg):
    lines = ["🎁 <b>INVITE &amp; BOX SETTINGS</b>", "",
             f"Invite system: {'ON ✅' if cfg['enabled'] else 'OFF 🔴'}", "",
             "Tap a box to change what it gives and how many invites it needs.", ""]
    rows = [[InlineKeyboardButton("🔴 Turn invite system OFF" if cfg["enabled"] else "🟢 Turn invite system ON", callback_data="rf:o:sys")]]
    for tier in TIER_ORDER:
        c = cfg["tiers"][tier]
        lines.append(f"{_tier_label(tier)} - {c['invites']} invites · {c['boxes']} box · {'ON' if c['enabled'] else 'OFF'}")
        rows.append([InlineKeyboardButton(f"{_tier_label(tier)} · {c['invites']} invites", callback_data=f"rf:o:t:{tier}")])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


def _tier_page(cfg, tier):
    c = cfg["tiers"][tier]
    chars = f"{c['chars']} × {c['rarity']} (random)" if c["chars"] > 0 else "none"
    lines = [f"{_tier_label(tier)} <b>MYSTERY BOX</b>", "",
             f"Status: {'ON ✅' if c['enabled'] else 'OFF 🔴'}",
             f"📨 Invites needed: <b>{c['invites']}</b>",
             f"🎁 Boxes given per claim: <b>{c['boxes']}</b>",
             f"🎭 Characters per box: <b>{chars}</b>",
             f"🪙 Berrys: <b>{_fmt_range(c['b_min'], c['b_max'])}</b> (random amount in the range)",
             f"💎 Stones: <b>{_fmt_range(c['s_min'], c['s_max'])}</b> (random amount in the range)",
             "", "Set Characters to 0, or a range to 0, to leave that part out of the box."]
    e = f"rf:o:e:{tier}:"
    rows = [[InlineKeyboardButton("🔴 Turn OFF" if c["enabled"] else "🟢 Turn ON", callback_data=f"rf:o:tg:{tier}")],
            [InlineKeyboardButton("✏️ Invites", callback_data=e + "invites"), InlineKeyboardButton("✏️ Boxes", callback_data=e + "boxes")],
            [InlineKeyboardButton("✏️ Characters", callback_data=e + "chars"), InlineKeyboardButton("✏️ Rarity", callback_data=e + "rarity")],
            [InlineKeyboardButton("✏️ Berrys", callback_data=e + "berrys"), InlineKeyboardButton("✏️ Stones", callback_data=e + "stones")],
            [InlineKeyboardButton("⬅️ Back", callback_data="rf:o:hub")]]
    return "\n".join(lines), InlineKeyboardMarkup(rows)


RF_PROMPTS = {
    "invites": "✏️ How many invites are needed for the {tier} box? Send a whole number, for example 10.",
    "boxes": "✏️ How many {tier} boxes does one claim give? Send a whole number, for example 1.",
    "chars": "✏️ How many characters inside one {tier} box? Send a number (0 = no character), for example 1.",
    "rarity": "✏️ Which rarity are the characters in the {tier} box? Send one of: {rarities}",
    "berrys": "✏️ Berrys inside the {tier} box. Send a range like 50-500 (random amount), one fixed number, or 0 to turn Berrys off.",
    "stones": "✏️ Stones inside the {tier} box. Send a range like 1-10 (random amount), one fixed number, or 0 to turn Stones off.",
}


async def boxes_command(update, context):
    msg = update.effective_message
    if update.effective_user is None or msg is None:
        return
    if not _is_owner(update.effective_user.id):
        await _reply(msg, DENIED_TEXT)
        return
    text, kb = _hub_page(await asyncio.to_thread(get_config))
    await _reply(msg, text, parse_mode="HTML", reply_markup=kb)


async def rf_owner_callback(update, context):
    q = update.callback_query
    if not _is_owner(q.from_user.id):
        await q.answer(DENIED_TEXT, show_alert=True)
        return
    parts = (q.data or "").split(":")           # rf:o:<hub|sys|t|tg>[:<tier>]
    action = parts[2] if len(parts) > 2 else ""
    tier = parts[3] if len(parts) > 3 else None
    if tier is not None and tier not in TIER_ORDER:
        await q.answer()
        return
    try:
        cfg = await asyncio.to_thread(get_config)
        if action == "sys":
            await asyncio.to_thread(set_system_enabled, not cfg["enabled"])
        elif action == "tg" and tier:
            await asyncio.to_thread(set_tier_fields, tier, {"enabled": not cfg["tiers"][tier]["enabled"]})
        cfg = await asyncio.to_thread(get_config)
        text, kb = _tier_page(cfg, tier) if action in ("t", "tg") and tier else _hub_page(cfg)
    except Exception as e:
        logger.warning("referral settings failed: %s", e)
        await q.answer("❌ Could not load the settings. Try again.", show_alert=True)
        return
    await q.answer()
    await _edit(q, text, kb)


async def rf_edit_entry(update, context):
    q = update.callback_query
    if not _is_owner(q.from_user.id):
        await q.answer(DENIED_TEXT, show_alert=True)
        return -1
    _r, _o, _e, tier, field = (q.data or "").split(":")
    context.user_data["rf_edit"] = {"tier": tier, "field": field}
    await q.answer()
    await _reply(q.message, RF_PROMPTS[field].format(tier=_tier_label(tier), rarities=", ".join(_rarities())) + "\nSend /cancel to stop.")
    return RF_INPUT


async def rf_edit_input(update, context):
    msg = update.effective_message
    st = context.user_data.get("rf_edit")
    if msg is None or not st or not _is_owner(update.effective_user.id):
        return -1
    ok, note = await asyncio.to_thread(apply_edit_sync, st["tier"], st["field"], msg.text or "")
    if not ok:
        await _reply(msg, note + "\nTry again, or send /cancel.")
        return RF_INPUT
    context.user_data.pop("rf_edit", None)
    text, kb = _tier_page(await asyncio.to_thread(get_config), st["tier"])
    await _reply(msg, f"✅ {_esc(note)}\n\n{text}", parse_mode="HTML", reply_markup=kb)
    return -1


async def _rf_cancel(update, context):
    context.user_data.pop("rf_edit", None)
    return await _cancel_flow(update, context)


def register_referrals(app):
    from telegram.ext import CallbackQueryHandler, CommandHandler, ConversationHandler, MessageHandler, filters
    text = filters.TEXT & ~filters.COMMAND
    # Counts a referral BEFORE the main /start saves the new member's profile; it never replaces or delays the normal /start.
    app.add_handler(CommandHandler("start", ref_start_handler, filters=filters.ChatType.PRIVATE), group=-97)
    app.add_handler(ConversationHandler(
        entry_points=[CallbackQueryHandler(rf_edit_entry, pattern=r"^rf:o:e:(bronze|gold|platinum|diamond):(invites|boxes|chars|rarity|berrys|stones)$")],
        states={RF_INPUT: [MessageHandler(text, rf_edit_input)]},
        fallbacks=[CommandHandler("cancel", _rf_cancel)], allow_reentry=True, conversation_timeout=_deps.get("conv_timeout")))
    app.add_handler(CallbackQueryHandler(rf_owner_callback, pattern=r"^rf:o:(hub|sys|t:[a-z]+|tg:[a-z]+)$"))
    app.add_handler(CallbackQueryHandler(rf_user_callback, pattern=r"^rf:u:\d+:"))
    app.add_handler(CommandHandler("invite", invite_command))
    app.add_handler(CommandHandler("boxes", boxes_command))
