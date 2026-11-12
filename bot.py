import dns.resolver
dns.resolver.default_resolver = dns.resolver.Resolver(configure=False)
dns.resolver.default_resolver.nameservers = ['8.8.8.8', '1.1.1.1']


"""
Anime Character Telegram Bot  -  single entry point:  python bot.py

Project layout
    bot.py               the bot (all commands, jobs, settings, health-check server)
    mongo_db.py          MongoDB Atlas data layer (connection, retries, indexes, queries)
    migrate_to_mongo.py  one-time import of the old SQLite/JSON data into MongoDB
    requirements.txt     dependencies

Environment variables (set in a local .env file or in Render -> Environment)
    TELEGRAM_BOT_TOKEN      required  BotFather token
    MONGO_URI               required  mongodb+srv://user:password@cluster.mongodb.net/...
    MONGO_DB_NAME           optional  default "anime_bot"
    PORT                    set by Render; the built-in health-check server listens on it
    RENDER_EXTERNAL_URL     set by Render; the keep-alive ping calls this URL every 10 minutes
    KEEPALIVE_URL / KEEPALIVE_INTERVAL   optional: other ping URL (or "off") / seconds between pings (60-840)
    MONGO_MAX_POOL / MONGO_MIN_POOL / MONGO_CONNECT_RETRIES /
    MONGO_CHAR_CACHE_TTL / MONGO_GROUP_CACHE_TTL    optional tuning (see mongo_db.py)

Run only ONE instance at a time (Telegram polling and the quota logic assume it).
"""
import asyncio
import logging
import os
import warnings
from html import escape as html_escape
import random
import re
import time
import unicodedata
import uuid
from types import SimpleNamespace as _NS
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone, time as dt_time

# All daily resets (/daily, shop, spawn quotas, event/redeem expiry) are defined in India time.
# Render servers run in UTC, so pin the process clock to IST BEFORE any datetime.now() is used.
# Naive timestamps written by this bot (and migrated from the old SQLite data) are IST.
os.environ["TZ"] = "Asia/Kolkata"  # forced (not setdefault): an inherited TZ=UTC would shift every reset by 5h30m
if hasattr(time, "tzset"):  # not available on Windows
    time.tzset()

from dotenv import load_dotenv
from telegram import (
    Update,
    BotCommand,
    BotCommandScopeAllPrivateChats,
    BotCommandScopeChat,
    BotCommandScopeDefault,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputMediaPhoto,
    MessageEntity,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
)
from telegram.error import BadRequest, ChatMigrated, Forbidden, RetryAfter, TelegramError
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CommandHandler,
    ConversationHandler,
    MessageHandler,
    ContextTypes,
    CallbackQueryHandler,
    ChatMemberHandler,
    filters,
)
from telegram import InlineKeyboardMarkup as _TGInlineKeyboardMarkup

INLINE_MAX_PER_ROW = 3


def _wrap_inline_rows(rows, per_row=INLINE_MAX_PER_ROW):
    """Any row with more than `per_row` buttons is wrapped onto the next row (1-2 button rows are untouched)."""
    out = []
    for row in rows or []:
        row = list(row)
        if len(row) <= per_row:
            out.append(row)
        else:
            out.extend(row[i:i + per_row] for i in range(0, len(row), per_row))
    return out


class InlineKeyboardMarkup(_TGInlineKeyboardMarkup):
    """Drop-in replacement: guarantees the project-wide rule 'maximum 3 inline buttons per row'."""
    __slots__ = ()

    def __init__(self, inline_keyboard, *args, **kwargs):
        super().__init__(_wrap_inline_rows(inline_keyboard), *args, **kwargs)

# ---------------------------------------------------------------------------
# Settings (formerly config.py). Secrets are NOT stored here: the bot token and
# MongoDB URI come from environment variables (see the header of this file).
# ---------------------------------------------------------------------------
# First ID is treated as the bot owner.
ADMIN_IDS = [5675165124]

# Executive staff IDs (additional executives are stored in MongoDB via /addexec).
EXECUTIVE_IDS = []

DAILY_COINS = 100
DAILY_RESET_HOUR = 4

# Collection page size.
ITEMS_PER_PAGE = 5

import mongo_db
import fusion  # Special Stone Daily Task System
import theme   # Bot Theme Customization (Owner: /help -> Owner Commands -> 🎨 Customize Bot)
import badge_banner  # Character badges + profile banners (all logic lives in badge_banner.py)
import security  # Security: banned groups / banned users / special access (all logic lives in security.py)
import rewards  # Rewards: festivals with timed quests + hidden event card/banner (all logic lives in rewards.py)


def _mc(name):
    """Shortcut for a MongoDB collection."""
    return mongo_db.col(name)


# One professional denial message for every unauthorized command attempt or button tap (all role levels).
UNAUTHORIZED_TEXT = "⚠️ Access Denied: You do not have permission to perform this action."


# --------------------------------------------------------------------------
# Latency tuning (hot path = every incoming update)
#   DB_THREADS           worker threads for blocking MongoDB calls (keep <= MONGO_MAX_POOL)
#   CONCURRENT_UPDATES   how many updates may be processed at once
#   UPDATE_ORDERING      "chat" = concurrent across chats, in order within a chat (default, safest)
#                        "none" = fully concurrent
# --------------------------------------------------------------------------
DB_THREADS = int(os.getenv("DB_THREADS", "20"))
CONCURRENT_UPDATES = int(os.getenv("CONCURRENT_UPDATES", "128"))
UPDATE_ORDERING = os.getenv("UPDATE_ORDERING", "chat").strip().lower()


def _groups_cache_warm():
    """True while mongo_db's group-registry cache is fresh (reading it then costs no DB round-trip)."""
    try:
        cache = mongo_db._group_cache
        return (cache["docs"] is not None
                and time.monotonic() - cache["ts"] < mongo_db.GROUP_CACHE_TTL - 1.0)
    except Exception:
        return False


def _chat_title(chat):
    return getattr(chat, "title", None) or getattr(chat, "username", None) or "Unknown"


def _register_needed(chat):
    """False when the stored registry row already matches this chat (the upsert would be a no-op)."""
    try:
        info = mongo_db.load_bot_groups().get(str(int(chat.id)))
    except Exception:
        return True
    return (info is None
            or info.get("title") != _chat_title(chat)
            or info.get("type") != getattr(chat, "type", "group")
            or info.get("username") != getattr(chat, "username", None))


def _group_gate_sync(chat):
    """(approved, enabled) for a group; writes the registry row only if it changed."""
    register_bot_group(chat)
    cid = int(chat.id)
    return cid in mongo_db.load_approved_groups(), mongo_db.is_bot_enabled(cid)


async def group_gate(chat):
    """
    Per-message group check. While the registry cache is warm and the chat's stored info is unchanged this is pure
    memory (no thread hop, no DB); otherwise one worker-thread call. Never writes to the DB on an unchanged chat.
    """
    if _groups_cache_warm() and not _register_needed(chat):
        cid = int(chat.id)
        return cid in mongo_db.load_approved_groups(), mongo_db.is_bot_enabled(cid)
    return await asyncio.to_thread(_group_gate_sync, chat)


try:
    from telegram.ext import SimpleUpdateProcessor as _BaseUpdateProcessor
except ImportError:  # python-telegram-bot older than 20.4
    _BaseUpdateProcessor = None

if _BaseUpdateProcessor is not None:
    class ChatOrderedUpdateProcessor(_BaseUpdateProcessor):
        """
        Concurrent update handling that keeps updates of the SAME chat in arrival order.
        Different chats run in parallel; one slow or flooded chat cannot hold up the others, and the
        per-chat lock is taken before a concurrency slot so a flooded chat cannot starve the rest.
        """

        def __init__(self, max_concurrent_updates):
            super().__init__(max_concurrent_updates)
            self._chat_locks = {}

        @staticmethod
        def _key(update):
            chat = getattr(update, "effective_chat", None)
            if chat is not None:
                return chat.id
            user = getattr(update, "effective_user", None)
            return ("user", user.id) if user is not None else None

        async def process_update(self, update, coroutine):
            key = self._key(update)
            if key is None:
                await super().process_update(update, coroutine)
                return
            entry = self._chat_locks.get(key)
            if entry is None:
                entry = self._chat_locks[key] = [asyncio.Lock(), 0]
            entry[1] += 1
            try:
                async with entry[0]:
                    await super().process_update(update, coroutine)
            finally:
                entry[1] -= 1
                if entry[1] == 0 and self._chat_locks.get(key) is entry:
                    del self._chat_locks[key]
else:
    ChatOrderedUpdateProcessor = None


def _day_floor(day_key, days_back=1):
    """YYYY-MM-DD string `days_back` days before day_key (cheap string pre-filter margin)."""
    return (datetime.strptime(day_key, "%Y-%m-%d") - timedelta(days=days_back)).strftime("%Y-%m-%d")


def log_character_action(code, name, user, action):
    """Audit row for /addcharacter and /editcharacter (never raises)."""
    try:
        mongo_db.insert_with_id("character_additions_v2", {
            "character_code": str(code), "character_name": name, "added_by": user.id,
            "added_username": user.username or "", "added_first_name": user.first_name or "",
            "added_last_name": user.last_name or "", "added_at": india_timestamp(), "action": action,
        })
    except Exception as e:
        print("Character action log error:", e)


def get_character_adder_text(code):
    """'Name (@username)' of whoever first added this character, or 'Unknown' when no record exists."""
    try:
        docs = [d for d in _mc("character_additions_v2").find({"character_code": str(code)})
                if (d.get("action") or "add") == "add"]
        if not docs:
            return "Unknown"
        d = min(docs, key=lambda x: str(x.get("added_at") or "9999"))
        name = " ".join(v for v in [d.get("added_first_name"), d.get("added_last_name")] if v).strip()
        username = (d.get("added_username") or "").strip()
        handle = f"@{username}" if username else "No username"
        if not name:
            return html_escape(handle) if username else "Unknown"
        return f"{html_escape(name)} ({html_escape(handle)})"
    except Exception as e:
        print("Character adder lookup error:", e)
        return "Unknown"


def _swap_shop_rows(user_id, docs):
    """Replace a user's 4 shop rows atomically (delete + insert in one transaction)."""
    def _work(session):
        _mc("shop_v3").delete_many({"user_id": int(user_id)}, session=session)
        _mc("shop_v3").insert_many(docs, session=session)
    mongo_db.run_transaction(_work)


def _staff_role_rows():
    """[(user_id, role)] for every stored executive/scout."""
    return [(d["_id"], d.get("role")) for d in _mc("staff_roles_v2").find({"role": {"$in": ["executive", "scout"]}})]


load_dotenv(Path(__file__).with_name(".env"))
logger = logging.getLogger(__name__)
BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")

warnings.filterwarnings(
    "ignore",
    message=r"If 'per_message=False', 'CallbackQueryHandler' will not be tracked.*",
    category=UserWarning,
)



def _mongo_safe(fn, *args):
    """Run a MongoDB registry write; log instead of raising (mirrors the old JSON save helpers)."""
    try:
        result = fn(*args)
        return True if result is None else result
    except Exception as e:
        print(f"MongoDB registry write error ({getattr(fn, '__name__', fn)}): {e}")
        return False

def load_auto_spawn_groups():
    return mongo_db.load_auto_spawn_groups()

def register_auto_spawn_group(chat_id):
    try:
        if int(chat_id) in mongo_db.load_auto_spawn_groups():
            return  # already enabled: skip the write (it would also wipe the group cache)
    except Exception:
        pass
    _mongo_safe(mongo_db.set_auto_spawn_group, int(chat_id), True)

def unregister_auto_spawn_group(chat_id):
    _mongo_safe(mongo_db.set_auto_spawn_group, int(chat_id), False)

def load_bot_groups():
    return mongo_db.load_bot_groups()

def save_bot_groups(groups):
    return _mongo_safe(mongo_db.replace_bot_groups, groups)

def load_gstats_hidden_groups():
    return mongo_db.load_gstats_hidden_groups()

def hide_gstats_group(chat_id):
    return _mongo_safe(mongo_db.hide_gstats_group, int(chat_id))

def unhide_gstats_group(chat_id):
    return _mongo_safe(mongo_db.unhide_gstats_group, int(chat_id))

def register_bot_group(chat):
    if not chat or not getattr(chat, "id", None):
        return
    if not _register_needed(chat):
        return  # stored row already matches: no DB write, and the group cache is not wiped
    _mongo_safe(
        mongo_db.register_bot_group_info,
        int(chat.id),
        _chat_title(chat),
        getattr(chat, "type", "group"),
        getattr(chat, "username", None),
    )

def unregister_bot_group(chat_id):
    _mongo_safe(mongo_db.unregister_bot_group, int(chat_id))

async def cleanup_left_group(chat_id, context=None):
    chat_id = int(chat_id)
    # one atomic update: forget registration, auto-spawn, approval and enable-state
    await asyncio.to_thread(_mongo_safe, mongo_db.cleanup_left_group, chat_id)

    if context is not None:
        context.application.bot_data.setdefault("active_chats", set()).discard(chat_id)
        active = context.application.bot_data.setdefault("active_spawns", {})
        active.pop(chat_id, None)

def get_daily_random_spawn_counts(chat_id=None, app=None):
    counts = {}
    today = get_today_key()
    for code, caught_at, _chat in mongo_db.sh_caught_random_rows(_day_floor(today)):
        try:
            dt = datetime.fromisoformat(str(caught_at))
            if dt.tzinfo is None: dt = dt.replace(tzinfo=INDIA_TZ)
            quota_day = dt - timedelta(days=1) if dt.astimezone(INDIA_TZ).hour < DAILY_RESET_HOUR else dt
            if quota_day.astimezone(INDIA_TZ).strftime("%Y-%m-%d") == today:
                counts[str(code)] = counts.get(str(code), 0) + 1
        except (TypeError, ValueError):
            continue
    return counts

def get_daily_random_spawn_limited_codes(chat_id=None, app=None, limit=None):
    if limit is None:
        limit = MAX_CHARACTER_SUCCESSFUL_ADDS_GLOBAL
    return {
        code for code, count in get_daily_random_spawn_counts(chat_id, app).items()
        if count >= limit
    }

def reserve_random_spawn(app, chat_id, character_code):
    today = india_today_key()
    if app.bot_data.get("random_spawn_reservation_day") != today:
        app.bot_data["random_spawn_reservations"] = {}
        app.bot_data["random_spawn_reservation_day"] = today
    key = (int(chat_id), str(character_code))
    reservations = app.bot_data.setdefault("random_spawn_reservations", {})
    reservations[key] = reservations.get(key, 0) + 1

def release_random_spawn_reservation(app, chat_id, character_code):
    key = (int(chat_id), str(character_code))
    reservations = app.bot_data.setdefault("random_spawn_reservations", {})
    count = reservations.get(key, 0) - 1
    if count > 0:
        reservations[key] = count
    else:
        reservations.pop(key, None)

_GCS = "group_character_spawn_v1"

def _gcs_totals(code, today):
    spawned = pending = 0
    for d in _mc(_GCS).find({"character_code": code, "day_key": today}, {"spawn_count": 1, "pending_count": 1}):
        spawned += int(d.get("spawn_count") or 0)
        pending += int(d.get("pending_count") or 0)
    return spawned, pending

def reserve_daily_character_spawn(chat_id, character_code):
    code = str(character_code)
    today = get_today_key()
    used, pending = _gcs_totals(code, today)
    if used + pending >= MAX_CHARACTER_SUCCESSFUL_ADDS_GLOBAL:
        return False
    _mc(_GCS).update_one(
        {"chat_id": int(chat_id), "character_code": code, "day_key": today},
        {"$inc": {"pending_count": 1}, "$set": {"updated_at": india_timestamp()},
         "$setOnInsert": {"spawn_count": 0}},
        upsert=True,
    )
    return True

def finalize_daily_character_spawn(chat_id, character_code):
    code = str(character_code); today = get_today_key()
    used, _ = _gcs_totals(code, today)
    if used >= MAX_CHARACTER_SUCCESSFUL_ADDS_GLOBAL:
        return False
    res = _mc(_GCS).update_one(
        {"chat_id": int(chat_id), "character_code": code, "day_key": today, "pending_count": {"$gt": 0}},
        {"$inc": {"pending_count": -1, "spawn_count": 1}, "$set": {"updated_at": india_timestamp()}},
    )
    return res.modified_count == 1

def release_daily_character_spawn(chat_id, character_code):
    code = str(character_code); today = get_today_key()
    res = _mc(_GCS).update_one(
        {"chat_id": int(chat_id), "character_code": code, "day_key": today, "pending_count": {"$gt": 0}},
        {"$inc": {"pending_count": -1}, "$set": {"updated_at": india_timestamp()}},
    )
    if res.modified_count == 1:
        _mc(_GCS).delete_one({"chat_id": int(chat_id), "character_code": code, "day_key": today,
                              "spawn_count": 0, "pending_count": 0})

def reconcile_group_character_spawn_counts():
    today = get_today_key()
    coll = _mc(_GCS)
    coll.delete_many({})

    totals = {}
    for code, caught_at, chat_id in mongo_db.sh_caught_random_rows(_day_floor(today)):
        s = str(caught_at)
        try:
            hour = int(s[11:13])
            day = s[:10]
            if hour < DAILY_RESET_HOUR:
                day = _day_floor(day)
        except ValueError:
            continue
        if day == today:
            key = (int(chat_id), str(code))
            totals[key] = totals.get(key, 0) + 1
    now = india_timestamp()
    docs = [{"chat_id": c, "character_code": k, "day_key": today, "spawn_count": n,
             "pending_count": 0, "updated_at": now} for (c, k), n in totals.items()]
    if docs:
        coll.insert_many(docs)

    cutoff = (datetime.now(timezone.utc) - timedelta(seconds=SPAWN_LIFETIME)).astimezone(INDIA_TZ).isoformat()
    for chat_id, code, count in mongo_db.sh_uncaught_random_counts(cutoff):
        coll.update_one(
            {"chat_id": int(chat_id), "character_code": str(code), "day_key": today},
            {"$inc": {"pending_count": min(1, int(count))}, "$set": {"updated_at": now},
             "$setOnInsert": {"spawn_count": 0}},
            upsert=True,
        )

def save_approved_groups(groups):
    return _mongo_safe(mongo_db.replace_approved_groups, groups)

def load_approved_groups():
    return mongo_db.load_approved_groups()

async def is_group_approved(chat_id):
    try:
        cid = int(chat_id)
    except (TypeError, ValueError):
        return False
    if _groups_cache_warm():
        return cid in mongo_db.load_approved_groups()  # memory only
    return cid in await asyncio.to_thread(mongo_db.load_approved_groups)


def load_bot_group_states():
    return mongo_db.load_bot_group_states()

def save_bot_group_states(states):
    return _mongo_safe(mongo_db.replace_bot_group_states, states)

def is_bot_enabled(chat_id):
    return mongo_db.is_bot_enabled(int(chat_id))

def set_bot_enabled(chat_id, enabled):
    _mongo_safe(mongo_db.set_bot_enabled, int(chat_id), bool(enabled))
    return bool(enabled)


def notifications_enabled_for(user_id):
    return mongo_db.notifications_enabled_for(int(user_id))

def set_notifications_enabled_for(user_id, enabled):
    _mongo_safe(mongo_db.set_notifications_enabled_for, int(user_id), bool(enabled))

_RESTRICTION_CACHE = {}
_RESTRICTION_TTL = 5.0

# A restricted member is blocked ONLY from these commands (and from the Accept buttons of transfers / exchanges).
RESTRICTED_COMMANDS = {"spawn", "add", "transfer", "berrytransfer", "exchange"}
RESTRICTED_CALLBACK_PREFIXES = ("tr_accept:", "ex_accept:")

def load_restrictions():
    return mongo_db.load_restrictions()

def save_restrictions(data):
    _RESTRICTION_CACHE.clear()
    return _mongo_safe(mongo_db.replace_restrictions, data)

def _restriction_lookup(user_id):
    """(expiry, entry) of the user's active restriction, or (None, None). Short per-user cache (cleared on every write)."""
    now_mono = time.monotonic()
    cached = _RESTRICTION_CACHE.get(user_id)
    if cached and now_mono - cached[0] < _RESTRICTION_TTL:
        return cached[1], cached[2]
    entry = mongo_db.get_restriction(user_id)
    expiry, info = None, None
    if entry:
        value = int(entry.get("expiry", 0))
        if value <= int(datetime.now().timestamp()):
            mongo_db.remove_restriction(user_id)
        else:
            expiry, info = value, entry
            if "reason" not in info:       # make sure the full saved record (reason, duration, who) is available
                try:
                    full = load_restrictions().get(str(user_id))
                    if isinstance(full, dict):
                        info = full
                except Exception:
                    pass
    _RESTRICTION_CACHE[user_id] = (now_mono, expiry, info)
    return expiry, info

def get_restriction_expiry(user_id):
    # Called on many updates, so keep a very short per-user cache (cleared on every write).
    return _restriction_lookup(user_id)[0]

def format_remaining(seconds):
    seconds = max(0, int(seconds))
    days, seconds = divmod(seconds, 86400)
    hours, seconds = divmod(seconds, 3600)
    minutes, seconds = divmod(seconds, 60)
    parts = []
    if days: parts.append(f"{days}d")
    if hours: parts.append(f"{hours}h")
    if minutes: parts.append(f"{minutes}m")
    if not parts: parts.append(f"{seconds}s")
    return " ".join(parts)

def restriction_notice(expiry, info):
    reason = str((info or {}).get("reason") or "").strip() if isinstance(info, dict) else ""
    return (
        "🚫 You are restricted.\n"
        f"📝 Reason: {reason or 'Not provided'}\n"
        f"⏳ {format_remaining(expiry - int(datetime.now().timestamp()))} left\n"
        "Think it's a mistake? Use /appeal"
    )

def restricted_by_label(info):
    """What the restricted person sees as 'Restricted by': Anonymous when the Owner did it."""
    info = info if isinstance(info, dict) else {}
    try:
        by_id = int(info.get("restricted_by") or 0)
    except (TypeError, ValueError):
        by_id = 0
    if by_id and is_owner(by_id):
        return "Anonymous"
    return info.get("restricted_by_name") or "Unknown"

def _duration_seconds(text):
    import re as _re
    m = _re.fullmatch(r"([1-9]\d{0,3})([hd])", str(text or "").lower())
    return int(m.group(1)) * (3600 if m.group(2) == "h" else 86400) if m else None

async def notify_restricted_user(context, user_id, text):
    """PM the restricted person. False when Telegram refuses (they never pressed Start, or blocked the bot)."""
    try:
        await context.bot.send_message(int(user_id), text)
        return True
    except Exception as e:
        print("Restriction PM error:", e)
        return False

async def get_restricted_message(update):
    user = getattr(update, "effective_user", None)
    if not user or is_owner(user.id):
        return None
    cached = _RESTRICTION_CACHE.get(user.id)
    if cached and time.monotonic() - cached[0] < _RESTRICTION_TTL:
        expiry, info = cached[1], cached[2]
    else:
        expiry, info = await asyncio.to_thread(_restriction_lookup, user.id)
    if not expiry:
        return None
    return restriction_notice(expiry, info)

def has_group_approval_permission(user_id):
    if is_owner(user_id):
        return True
    if not is_executive(user_id):
        return False
    try:
        return _mc("group_approval_permissions_v2").find_one({"_id": int(user_id)}, {"_id": 1}) is not None
    except Exception as e:
        print("Group approval permission check error:", e)
        return False

async def add_group_approval_permission(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    if len(context.args) != 1 or not context.args[0].isdigit():
        await safe_reply_text(update.effective_message, "Usage: /addgroupapprove <executive_user_id>")
        return
    uid = int(context.args[0])
    if uid not in EXECUTIVE_IDS:
        await safe_reply_text(update.effective_message, "❌ That user is not an Executive.")
        return
    try:
        (await asyncio.to_thread(_mc("group_approval_permissions_v2").update_one,
            {"_id": uid}, {"$setOnInsert": {"user_id": uid, "granted_at": timestamp()}}, upsert=True))
    except Exception as e:
        print("addgroupapprove error:", e)
        await safe_reply_text(update.effective_message, "❌ Could not grant group approval permission.")
        return
    await refresh_command_menu(context.bot, uid)
    await safe_reply_text(update.effective_message, f"✅ Group approval permission granted to Executive {uid}.\n\nThey can now use /approve and /removeapprove.")

async def remove_group_approval_permission(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    if len(context.args) != 1 or not context.args[0].isdigit():
        await safe_reply_text(update.effective_message, "Usage: /removegroupapprove <executive_user_id>")
        return
    uid = int(context.args[0])
    try:
        removed = (await asyncio.to_thread(_mc("group_approval_permissions_v2").delete_one, {"_id": uid})).deleted_count > 0
    except Exception as e:
        print("removegroupapprove error:", e)
        await safe_reply_text(update.effective_message, "❌ Could not remove group approval permission.")
        return
    await refresh_command_menu(context.bot, uid)
    if removed:
        await safe_reply_text(update.effective_message, f"✅ Group approval permission removed from Executive {uid}.")
    else:
        await safe_reply_text(update.effective_message, "❌ That Executive does not have group approval permission.")

GROUP_APPROVED_TEXT = (
    "✅ Group Approved\n\n"
    "This group has been approved successfully.\n\n"
    "🤖 The bot is now fully active in this group.\n"
    "All commands and features are now available and will work normally."
)


async def send_group_approved_confirmation(context, chat_id):
    """Post the approval confirmation into the approved group. Never raises: approval stays valid if this fails."""
    try:
        await context.bot.send_message(chat_id=chat_id, text=GROUP_APPROVED_TEXT)
        return True
    except Exception as e:
        print(f"Group approval confirmation error for {chat_id}:", e)
        return False


async def apply_group_approval(context, chat_id):
    """The approval steps shared by /approve and Auto Approve. Returns True when the approval was saved.
    Uses a one-group write (not the whole-set replace), so several groups approved at once cannot undo each other."""
    chat_id = int(chat_id)
    saved = await asyncio.to_thread(_mongo_safe, mongo_db.set_group_approved, chat_id, True)
    await asyncio.to_thread(set_bot_enabled, chat_id, True)
    await asyncio.to_thread(register_auto_spawn_group, chat_id)
    context.application.bot_data.setdefault("active_chats", set()).add(chat_id)
    context.application.bot_data.setdefault("unapproved_notified", set()).discard(chat_id)
    return saved is not False


async def approve_group(update, context):
    uid = update.effective_user.id
    if not (await asyncio.to_thread(has_group_approval_permission, uid)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    chat = update.effective_chat
    if chat.type in ("group", "supergroup"):
        if len(context.args) > 1 or (context.args and not context.args[0].lstrip("-").isdigit()):
            await safe_reply_text(update.message, "Usage: /approve  or  /approve <group_chat_id>")
            return
        chat_id = int(context.args[0]) if context.args else chat.id
    else:
        if len(context.args) != 1 or not context.args[0].lstrip("-").isdigit():
            await safe_reply_text(update.message, "Usage in Owner DM: /approve <group_chat_id>")
            return
        chat_id = int(context.args[0])

    saved = await apply_group_approval(context, chat_id)
    # Confirmation goes to the exact group that was just approved, only after the approval was saved.
    group_notified = saved and (await send_group_approved_confirmation(context, chat_id))
    if chat.type in ("group", "supergroup"):
        if chat_id != chat.id:
            await safe_reply_text(update.message, f"✅ Group {chat_id} successfully approved.")
        elif not group_notified:  # the confirmation above already answers in the group; fall back to the old reply
            await safe_reply_text(update.message, "✅ Group successfully approved by the Owner.\n🤖 The bot is now active in this group.")
    else:
        dm_text = f"✅ Group {chat_id} successfully approved.\n🤖 The bot is now active in that group."
        if not group_notified:
            dm_text += "\n⚠️ Could not post the confirmation in that group (the bot may no longer be a member). The approval itself is saved."
        await safe_reply_text(update.message, dm_text)

    await notify_staff_action(
        context,
        f"✅ GROUP APPROVED\n🆔 Group ID: {chat_id}\n👤 Approved by: {display_user(update.effective_user)}",
        actor_id=update.effective_user.id,
    )

async def approve_group_button(update, context):
    """'✅ Approve Group' under an approval request: same as /approve <group id> (Owner, or Executive with permission)."""
    query = update.callback_query
    uid = query.from_user.id
    if not (await asyncio.to_thread(has_group_approval_permission, uid)):
        await query.answer(UNAUTHORIZED_TEXT, show_alert=True)
        return
    try:
        chat_id = int((query.data or "").split(":", 1)[1])
    except Exception:
        await query.answer()
        return
    saved = await apply_group_approval(context, chat_id)
    if not saved:
        await query.answer("❌ Could not save the approval. Try /approve " + str(chat_id), show_alert=True)
        return
    group_notified = await send_group_approved_confirmation(context, chat_id)
    await query.answer("✅ Group approved.")
    note = "\n\n✅ Approved" + ("" if group_notified else " (could not post the confirmation in the group)")
    try:
        link_row = [row for row in (query.message.reply_markup.inline_keyboard if query.message.reply_markup else [])
                    if not any((b.callback_data or "").startswith("apvg:") for b in row)]
        await query.edit_message_text((query.message.text_html or "") + note, parse_mode="HTML",
                                      reply_markup=InlineKeyboardMarkup(link_row) if link_row else None)
    except Exception as e:
        print("Approve button message update error:", e)
    await notify_staff_action(
        context,
        f"✅ GROUP APPROVED\n🆔 Group ID: {chat_id}\n👤 Approved by: {display_user(query.from_user)}",
        actor_id=uid,
    )


def _spawncooldown_line(minutes):
    return f"{minutes} minutes" if minutes else "1 hour (normal)"


async def spawncooldown_command(update, context):
    """Owner: the personal /spawn cooldown of members and Scouts in ONE group. Owner and Executives keep 30 minutes everywhere."""
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    msg, chat = update.effective_message, update.effective_chat
    args = list(context.args or [])
    in_group = chat.type in ("group", "supergroup")

    def parse_gid(text):
        t = str(text).strip()
        return int(t) if t.lstrip("-").isdigit() and t.startswith("-") else None

    if not args:
        if in_group:
            m = await asyncio.to_thread(group_personal_cooldown_minutes, chat.id)
            await safe_reply_text(msg, f"⏳ /spawn cooldown for members and Scouts in this group: {_spawncooldown_line(m)}\n"
                                       "Owner and Executives: 30 minutes everywhere.\n\n"
                                       "Change: /spawncooldown <minutes>   Back to normal: /spawncooldown reset")
            return
        await asyncio.to_thread(group_personal_cooldown_minutes, 0)          # refresh the cache
        groups = (await asyncio.to_thread(load_bot_groups)) or {}
        lines = ["⏳ Personal /spawn cooldown (members and Scouts)", "Normal: 1 hour. Owner and Executives: 30 minutes everywhere.", ""]
        if _GCD["map"]:
            for gid, minutes in sorted(_GCD["map"].items()):
                title = (groups.get(gid) or {}).get("title") if isinstance(groups.get(gid), dict) else None
                lines.append(f"• {html_escape(title or 'Group')} <code>{gid}</code>: {minutes} minutes")
        else:
            lines.append("No group has its own cooldown.")
        lines += ["", "Set: /spawncooldown &lt;minutes&gt; &lt;group id&gt;", "Reset: /spawncooldown reset &lt;group id&gt;"]
        await safe_reply_text(msg, "\n".join(lines), parse_mode="HTML")
        return

    reset = args[0].lower() == "reset"
    rest = args[1:] if reset else args
    if reset:
        gid = parse_gid(rest[0]) if rest else (chat.id if in_group else None)
    else:
        if not args[0].isdigit() or not (1 <= int(args[0]) <= 720):
            await safe_reply_text(msg, "Usage: /spawncooldown <minutes 1-720> [group_id]  or  /spawncooldown reset [group_id]")
            return
        gid = parse_gid(rest[1]) if len(rest) > 1 else (chat.id if in_group else None)
    if gid is None:
        await safe_reply_text(msg, "❌ Give the group id (it starts with -), or run this command inside the group.")
        return
    coll = _mc(GROUP_PERSONAL_CD_COLL)
    try:
        if reset:
            await asyncio.to_thread(coll.delete_one, {"_id": int(gid)})
            result = f"✅ Group {gid}: the /spawn cooldown for members and Scouts is back to 1 hour."
        else:
            minutes = int(args[0])
            await asyncio.to_thread(coll.update_one, {"_id": int(gid)}, {"$set": {"minutes": minutes}}, upsert=True)
            result = f"✅ Group {gid}: members and Scouts now wait {minutes} minutes between /spawn.\nOwner and Executives stay at 30 minutes."
    except Exception as e:
        print("spawncooldown error:", e)
        await safe_reply_text(msg, "❌ Could not save that. Nothing was changed.")
        return
    _GCD["ts"] = 0.0                                                          # re-read right away
    mark_success(update)
    await safe_reply_text(msg, result)


# ---------------------------------------------------------------------------------------------------
# AUTO APPROVE (Owner only). While ON, a group the bot is added to is approved automatically, as long as it has
# at least the minimum number of members the Owner set (0 = no limit). Smaller groups wait in "Pending".
# Opened from /help -> Owner Commands -> ✅ Auto Approve (next to 🎨 Customize Bot), or with /autoapprove.
# ---------------------------------------------------------------------------------------------------
AA_PAGE_SIZE = 8
AA_INPUT_TIMEOUT = 300                # seconds the bot waits for the minimum-members number
AA_MAX_MIN_MEMBERS = 1000000
_aa_waiting_min = {}                  # owner id -> expiry (time.monotonic) while the bot waits for the number


async def get_auto_approve_settings(fresh=False):
    """{enabled, min_members, ...}, or None when the setting cannot be read."""
    try:
        return await asyncio.to_thread(mongo_db.get_auto_approve, fresh)
    except Exception as e:
        print("Auto-approve lookup error:", e)
        return None


async def is_auto_approve_on():
    """Fails closed: if the setting cannot be read, Auto Approve counts as OFF (the normal manual flow applies)."""
    s = await get_auto_approve_settings()
    return bool(s and s.get("enabled"))


async def group_member_count(bot, chat_id):
    try:
        return int(await bot.get_chat_member_count(chat_id))
    except Exception as e:
        print(f"Member count error for {chat_id}:", e)
        return None


async def check_group_size(bot, chat_id, minimum):
    """(ok, member_count, note). No limit -> ok. A limit is set but the count is unknown -> not ok (fails closed)."""
    if minimum <= 0:
        return True, None, None
    count = await group_member_count(bot, chat_id)
    if count is None:
        return False, None, f"👥 Members could not be checked (minimum {minimum})"
    if count < minimum:
        return False, count, f"👥 Members: {count} (minimum {minimum})"
    return True, count, None


async def auto_approve_group(context, chat, added_by=None):
    """Approve one group because Auto Approve is ON and it is big enough.
    Returns (approved, note). `note` explains why a group was NOT auto-approved (shown to the Owner in the approval request)."""
    s = await get_auto_approve_settings()
    if not s or not s.get("enabled"):
        return False, None
    cid = int(chat.id)
    inflight = context.application.bot_data.setdefault("auto_approve_inflight", set())
    if cid in inflight:
        return True, None                 # another update is already approving this group
    inflight.add(cid)
    try:
        if cid in await asyncio.to_thread(mongo_db.load_approved_groups):
            return True, None
        minimum = int(s.get("min_members") or 0)
        ok, count, note = await check_group_size(context.bot, cid, minimum)
        if not ok:
            return False, "🤖 Auto Approve is ON but did not approve this group.\n" + note
        if not await apply_group_approval(context, cid):
            return False, None
        await send_group_approved_confirmation(context, cid)
        owner_id = ADMIN_IDS[0] if ADMIN_IDS else None
        if owner_id:
            try:
                who = code_ids_html(html_escape(display_user(added_by))) if added_by else "Unknown"
                members = f"👥 Members: {count}\n" if count is not None else ""
                group_link = await get_group_link(context.bot, context.application, cid, chat)
                await context.bot.send_message(
                    chat_id=owner_id,
                    reply_markup=open_group_markup(group_link, cid),
                    text=(
                        "🤖 GROUP AUTO-APPROVED\n"
                        f"🏷 Group: {html_escape(_chat_title(chat))}\n"
                        f"🆔 Group ID: {group_id_html(cid)}\n"
                        f"{members}"
                        f"👤 Added by: {who}\n\n"
                        "Auto Approve is ON. Change it from /help → Owner Commands → ✅ Auto Approve"
                        + ("" if group_link else f"\n\n{html_escape(GROUP_NO_LINK_NOTE)}")
                    ),
                    parse_mode="HTML",
                )
            except Exception as e:
                print("Owner auto-approve notification error:", e)
        return True, None
    except Exception as e:
        print(f"Auto approve error for {cid}:", e)
        return False, None
    finally:
        inflight.discard(cid)


async def sweep_pending_groups(context, minimum):
    """Approve the waiting groups that have enough members. Returns (approved, below_minimum, failed)."""
    pending = await asyncio.to_thread(mongo_db.load_pending_groups)
    approved = below = failed = 0
    for cid, _title in pending:
        try:
            ok, _count, note = await check_group_size(context.bot, cid, minimum)
            if not ok:
                if _count is None:
                    failed += 1                # member count could not be read
                else:
                    below += 1
            elif await apply_group_approval(context, cid):
                approved += 1
                await send_group_approved_confirmation(context, cid)     # never raises
            else:
                failed += 1
        except Exception as e:
            failed += 1
            print(f"Pending group approval error for {cid}:", e)
        await asyncio.sleep(0.2)          # stay well under Telegram's flood limits when many groups are waiting
    return approved, below, failed


def sweep_result_text(approved, below, failed):
    lines = [f"📦 Waiting groups approved: {approved}"]
    if below:
        lines.append(f"👥 Below the minimum, still pending: {below}")
    if failed:
        lines.append(f"⚠️ Could not check/approve: {failed} (use /approve <group_chat_id>)")
    return "\n".join(lines)


def auto_approve_status_text(enabled, minimum):
    return ("🤖 Auto Approve: " + ("✅ ON" if enabled else "❌ OFF") + "\n"
            "👥 Minimum members: " + (str(minimum) if minimum > 0 else "no limit"))


async def _aa_edit(query, text, markup, html=False):
    try:
        await query.edit_message_text(text, reply_markup=markup, parse_mode="HTML" if html else None)
    except Exception as e:
        if "not modified" not in str(e).lower():
            print("Auto approve edit error:", e)


async def auto_approve_hub(owner_id, extra=""):
    """(text, keyboard) of the Auto Approve page."""
    back = [InlineKeyboardButton("« Back", callback_data=f"help:{owner_id}:owner")]
    s = await get_auto_approve_settings(True)
    if s is None:
        return "⚠️ Could not read the Auto Approve setting. Please try again.", InlineKeyboardMarkup([back])
    enabled, minimum = bool(s.get("enabled")), int(s.get("min_members") or 0)
    try:
        pending = len(await asyncio.to_thread(mongo_db.load_pending_groups))
    except Exception as e:
        print("Pending groups read error:", e)
        pending = None
    text = ("✅ Auto Approve\n\n" + auto_approve_status_text(enabled, minimum) +
            f"\n📋 Groups waiting: {pending if pending is not None else '?'}\n\n"
            "When ON, a group the bot is added to is approved by itself if it has at least the minimum members. "
            "Smaller groups wait in Pending until you use /approve.")
    if extra:
        text += "\n\n" + extra
    rows = [
        [_module_button("Auto: " + ("✅ ON" if enabled else "❌ OFF"), f"aa:{owner_id}:tog"),
         _module_button("👥 Min: " + (str(minimum) if minimum > 0 else "Off"), f"aa:{owner_id}:min")],
        [_module_button(f"📋 Pending ({pending if pending is not None else '?'})", f"aa:{owner_id}:pend:0")],
        back,
    ]
    return text, InlineKeyboardMarkup(rows)


async def auto_approve_pending_page(context, owner_id, page):
    """(html_text, keyboard) of the Pending list: every group the bot is in that is not approved yet."""
    pending = await asyncio.to_thread(mongo_db.load_pending_groups)
    total = len(pending)
    pages = max(1, -(-total // AA_PAGE_SIZE))
    page = max(0, min(page, pages - 1))
    chunk = pending[page * AA_PAGE_SIZE:(page + 1) * AA_PAGE_SIZE]
    counts = await asyncio.gather(*[group_member_count(context.bot, cid) for cid, _t in chunk])
    lines = [f"📋 <b>Pending groups</b> ({total})"]
    if not chunk:
        lines.append("\nNo group is waiting for approval. ✅")
    for (cid, title), n in zip(chunk, counts):
        lines.append(f"\n• <b>{html_escape(str(title or 'Unknown'))}</b>\n"
                     f"  🆔 {group_id_html(cid)}\n  👥 {n if n is not None else '?'} members")
    if chunk:
        lines.append("\nApprove one with " + html_escape("/approve <group_chat_id>"))
        if pages > 1:
            lines.append(f"Page {page + 1}/{pages}")
    nav = []
    if page > 0:
        nav.append(_module_button("‹ Prev", f"aa:{owner_id}:pend:{page - 1}"))
    if page < pages - 1:
        nav.append(_module_button("Next ›", f"aa:{owner_id}:pend:{page + 1}"))
    rows = ([nav] if nav else []) + [
        [_module_button("🔄 Refresh", f"aa:{owner_id}:pend:{page}")],
        [InlineKeyboardButton("« Back", callback_data=f"aa:{owner_id}:hub")],
    ]
    return "\n".join(lines), InlineKeyboardMarkup(rows)


async def auto_approve_callback(update, context):
    """Buttons of the Auto Approve page. Callback data: aa:<menu_owner_id>:<hub|tog|min|pend>[:<page>]. Owner only."""
    query = update.callback_query
    parts = (query.data or "").split(":")
    uid = query.from_user.id
    try:
        if len(parts) < 3 or not parts[1].isdigit():
            await query.answer(HELP_STALE_TEXT, show_alert=True)
            return
        menu_owner, action = int(parts[1]), parts[2]
        arg = parts[3] if len(parts) > 3 else ""
        if uid != menu_owner:
            await query.answer(NOT_YOURS_TEXT, show_alert=True)
            return
        if not is_owner(uid):
            await deny_callback(query)
            return

        if action == "hub":
            await query.answer()
            text, markup = await auto_approve_hub(uid)
            await _aa_edit(query, text, markup)
        elif action == "tog":
            s = await get_auto_approve_settings(True)
            if s is None:
                await query.answer("⚠️ Could not read the setting. Nothing was changed.", show_alert=True)
                return
            want = not bool(s.get("enabled"))
            try:
                await asyncio.to_thread(mongo_db.set_auto_approve, want, uid, india_timestamp())
            except Exception as e:
                print("Auto approve toggle error:", repr(e))
                await query.answer("⚠️ Could not change Auto Approve. Nothing was changed.", show_alert=True)
                return
            try:
                await query.answer("🤖 Auto Approve is now " + ("ON ✅" if want else "OFF ❌"))
            except Exception:
                pass
            extra = ""
            if want:
                extra = sweep_result_text(*(await sweep_pending_groups(context, int(s.get("min_members") or 0))))
            text, markup = await auto_approve_hub(uid, extra)
            await _aa_edit(query, text, markup)
        elif action == "min":
            s = await get_auto_approve_settings()
            current = int((s or {}).get("min_members") or 0)
            _aa_waiting_min[uid] = time.monotonic() + AA_INPUT_TIMEOUT
            await query.answer("Send the number in the chat")
            chat = query.message.chat if query.message else None
            if chat is not None:
                await context.bot.send_message(
                    chat_id=chat.id,
                    text=("👥 Minimum members\n"
                          f"Current: {current if current > 0 else 'no limit'}\n\n"
                          "Send the number now (0 = no limit). Send /cancel to stop."))
        elif action == "pend":
            await query.answer()
            page = int(arg) if arg.isdigit() else 0
            text, markup = await auto_approve_pending_page(context, uid, page)
            await _aa_edit(query, text, markup, html=True)
        else:
            await query.answer()
    except Exception as e:
        print("Auto approve callback error:", repr(e))
        try:
            await query.answer("⚠️ Something went wrong. Please try again.", show_alert=True)
        except Exception:
            pass


async def auto_approve_min_input(update, context):
    """The Owner's reply (a number) after tapping 👥 Min. Does nothing unless the bot is waiting for it."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or user.id not in _aa_waiting_min:
        return
    if not is_owner(user.id) or time.monotonic() > _aa_waiting_min[user.id]:
        _aa_waiting_min.pop(user.id, None)
        return
    text = (msg.text or "").strip()
    if not re.fullmatch(r"[0-9]{1,7}", text) or int(text) > AA_MAX_MIN_MEMBERS:
        await safe_reply_text(msg, f"⚠️ Send a whole number from 0 to {AA_MAX_MIN_MEMBERS} (0 = no limit), or /cancel.")
        return
    try:
        value = await asyncio.to_thread(mongo_db.set_auto_approve_min_members, int(text), user.id, india_timestamp())
    except Exception as e:
        print("Auto approve min save error:", e)
        await safe_reply_text(msg, "⚠️ Could not save the number. Please send it again, or /cancel.")
        return
    _aa_waiting_min.pop(user.id, None)
    await safe_reply_text(msg, "✅ Minimum members set to " + (str(value) if value > 0 else "no limit (0)") + ".")
    hub_text, hub_markup = await auto_approve_hub(user.id)
    await safe_reply_text(msg, hub_text, reply_markup=hub_markup)


async def autoapprove_command(update, context):
    """/autoapprove [on|off|min <number>] - Owner only."""
    user = update.effective_user
    msg = update.effective_message
    if not user or not is_owner(user.id):
        await safe_reply_text(msg, UNAUTHORIZED_TEXT)
        return
    args = [a.lower() for a in (context.args or [])]
    usage = "Usage: /autoapprove on | off | min <number>\nSend /autoapprove alone to see the status."
    s = await get_auto_approve_settings(True)
    if s is None:
        await safe_reply_text(msg, "⚠️ Could not read the Auto Approve setting. Nothing was changed. Please try again.")
        return
    current, minimum = bool(s.get("enabled")), int(s.get("min_members") or 0)
    if not args:
        await safe_reply_text(msg, auto_approve_status_text(current, minimum) +
                              "\n\nChange it with /autoapprove on, /autoapprove off or /autoapprove min 50.\n"
                              "Or open /help → Owner Commands → ✅ Auto Approve.")
        return
    if args[0] == "min":
        if len(args) != 2 or not re.fullmatch(r"[0-9]{1,7}", args[1]) or int(args[1]) > AA_MAX_MIN_MEMBERS:
            await safe_reply_text(msg, f"Usage: /autoapprove min <number>   (0 to {AA_MAX_MIN_MEMBERS}, 0 = no limit)")
            return
        try:
            value = await asyncio.to_thread(mongo_db.set_auto_approve_min_members, int(args[1]), user.id, india_timestamp())
        except Exception as e:
            print("autoapprove min write error:", e)
            await safe_reply_text(msg, "⚠️ Could not save the number. Nothing was changed. Please try again.")
            return
        await safe_reply_text(msg, "✅ Minimum members set to " + (str(value) if value > 0 else "no limit (0)") + ".")
        return
    if len(args) != 1 or args[0] not in ("on", "off"):
        await safe_reply_text(msg, usage)
        return
    want = args[0] == "on"
    if want == current:
        await safe_reply_text(msg, auto_approve_status_text(current, minimum) + "\n\nNo change was needed.")
        return
    try:
        await asyncio.to_thread(mongo_db.set_auto_approve, want, user.id, india_timestamp())
    except Exception as e:
        print("autoapprove write error:", e)
        await safe_reply_text(msg, "⚠️ Could not save the Auto Approve setting. Nothing was changed. Please try again.")
        return
    if not want:
        await safe_reply_text(msg, "🤖 Auto Approve: ❌ OFF\nGroups that are already approved stay approved. New groups wait for /approve again.")
        return
    await safe_reply_text(msg, "🤖 Auto Approve: ✅ ON\nApproving the groups that are waiting now...")
    await safe_reply_text(msg, sweep_result_text(*(await sweep_pending_groups(context, minimum))))


async def leave_group(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return

    chat = update.effective_chat
    if chat and chat.type in ("group", "supergroup"):
        if context.args:
            await safe_reply_text(update.effective_message, "Usage: /leavegroup")
            return
        chat_id = chat.id
    else:
        if len(context.args) != 1 or not context.args[0].lstrip("-").isdigit():
            await safe_reply_text(
                update.effective_message,
                "Usage in Owner DM: /leavegroup <group_chat_id>",
            )
            return
        chat_id = int(context.args[0])

        if chat_id >= 0:
            await safe_reply_text(
                update.effective_message,
                "❌ That ID is not a valid group ID. Please send the Group ID (for example: -1001234567890).",
            )
            return

        try:
            target_chat = await context.bot.get_chat(chat_id)
        except Exception as e:
            print(f"/leavegroup target lookup error for {chat_id}:", e)
            await safe_reply_text(
                update.effective_message,
                "❌ That group does not exist or Telegram could not access it. No changes were made.",
            )
            return

        if getattr(target_chat, "type", "") not in ("group", "supergroup"):
            await safe_reply_text(
                update.effective_message,
                "❌ That ID belongs to a non-group chat. Please send a Group/Supergroup ID. No changes were made.",
            )
            return

    groups = (await asyncio.to_thread(load_approved_groups))
    groups.discard(chat_id)
    (await asyncio.to_thread(save_approved_groups, groups))
    (await asyncio.to_thread(unregister_auto_spawn_group, chat_id))
    (await asyncio.to_thread(set_bot_enabled, chat_id, False))
    (await asyncio.to_thread(unregister_bot_group, chat_id))

    states = (await asyncio.to_thread(load_bot_group_states))
    states.pop(str(int(chat_id)), None)
    (await asyncio.to_thread(save_bot_group_states, states))

    context.application.bot_data.setdefault("active_chats", set()).discard(chat_id)
    context.application.bot_data.setdefault("bot_off_warning_sent", set()).discard(chat_id)

    active = context.application.bot_data.setdefault("active_spawns", {})
    removed_spawn = active.pop(chat_id, None)
    if removed_spawn:
        await cancel_spawn_expiry_task(removed_spawn)
        await safe_delete_message(context.bot, chat_id, removed_spawn.get("message_id"))

    try:
        await context.bot.leave_chat(chat_id)
    except Exception as e:
        await safe_reply_text(
            update.effective_message,
            f"⚠️ Group cleanup completed, but the bot could not leave the group.\n🆔 Group ID: {chat_id}\nError: {e}",
        )
        return

    (await asyncio.to_thread(unregister_bot_group, chat_id))
    (await asyncio.to_thread(unregister_auto_spawn_group, chat_id))
    groups = (await asyncio.to_thread(load_approved_groups))
    groups.discard(chat_id)
    (await asyncio.to_thread(save_approved_groups, groups))

    await safe_reply_text(
        update.effective_message,
        f"🚪 Bot left the group successfully.\n🆔 Group ID: {chat_id}\n🧹 Removed from /gstats registry.",
    )

async def remove_approval(update, context):
    if not (await asyncio.to_thread(has_group_approval_permission, update.effective_user.id)):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    chat = update.effective_chat
    if chat.type in ("group", "supergroup"):
        if context.args:
            await safe_reply_text(update.effective_message, "Usage: /removeapprove")
            return
        chat_id = chat.id
    else:
        if len(context.args) != 1 or not context.args[0].lstrip("-").isdigit():
            await safe_reply_text(update.effective_message, "Usage in Owner DM: /removeapprove <group_chat_id>")
            return
        chat_id = int(context.args[0])
    groups = (await asyncio.to_thread(load_approved_groups))
    groups.discard(chat_id)
    (await asyncio.to_thread(save_approved_groups, groups))
    (await asyncio.to_thread(set_bot_enabled, chat_id, False))
    (await asyncio.to_thread(unregister_auto_spawn_group, chat_id))
    context.application.bot_data.setdefault("active_chats", set()).discard(chat_id)
    active = context.application.bot_data.setdefault("active_spawns", {})
    removed_spawn = active.pop(chat_id, None)
    if removed_spawn:
        await cancel_spawn_expiry_task(removed_spawn)
        await safe_delete_message(context.bot, chat_id, removed_spawn.get("message_id"))
    if chat.type in ("group", "supergroup"):
        await safe_reply_text(update.effective_message,
            "🚫 Group approval removed.\n"
            "🔴 Bot is now OFF in this group.\n"
            "👑 The Owner must use /approve again to activate it."
        )
    else:
        await safe_reply_text(update.effective_message,
            f"🚫 Group {chat_id} approval removed.\n"
            "🔴 Bot is now OFF in that group."
        )
    await notify_staff_action(context, f"🚫 GROUP APPROVAL REMOVED\n🆔 Group ID: {chat_id}\n👤 Removed by: {display_user(update.effective_user)}", actor_id=update.effective_user.id)

async def _get_toggle_target_chat(update, context, command_name):
    chat = update.effective_chat
    if chat.type in ("group", "supergroup"):
        if context.args:
            await safe_reply_text(update.effective_message, f"Usage: /{command_name}")
            return None
        return int(chat.id)

    if len(context.args) != 1 or not context.args[0].lstrip("-").isdigit():
        await safe_reply_text(
            update.effective_message,
            f"Usage in Owner/Executive DM: /{command_name} <group_chat_id>",
        )
        return None
    return int(context.args[0])

# ---- per-group switches: manual /spawn and automatic spawning (separate from /boton /botoff) ----
GROUP_SPAWN_FLAGS = "group_spawn_flags_v1"            # {_id: chat_id, spawn_off: bool, auto_off: bool}
_GROUP_FLAGS = {"ts": 0.0, "val": {}}
_GROUP_FLAGS_TTL = 15.0

def group_spawn_flag(chat_id, key):
    """True when `key` ('spawn_off' / 'auto_off') is set for this group. Cached for a few seconds."""
    c = _GROUP_FLAGS
    if time.monotonic() - c["ts"] > _GROUP_FLAGS_TTL:
        try:
            c["val"] = {int(d["_id"]): d for d in _mc(GROUP_SPAWN_FLAGS).find({})}
        except Exception as e:
            print("Group spawn flags load error:", e)
        c["ts"] = time.monotonic()
    return bool((c["val"].get(int(chat_id)) or {}).get(key))

def set_group_spawn_flag(chat_id, key, value):
    _mc(GROUP_SPAWN_FLAGS).update_one({"_id": int(chat_id)}, {"$set": {key: bool(value)}}, upsert=True)
    _GROUP_FLAGS["ts"] = 0.0                           # reload on the next check

_SPAWN_SWITCH_TEXT = {
    # command: (flag, turn_off, what, other)
    "spawnoff": ("spawn_off", True, "The /spawn command", "Automatic spawning and the rest of the bot keep working."),
    "spawnon": ("spawn_off", False, "The /spawn command", "Automatic spawning and the rest of the bot keep working."),
    "autooff": ("auto_off", True, "Automatic spawning", "The /spawn command and the rest of the bot keep working."),
    "autoon": ("auto_off", False, "Automatic spawning", "The /spawn command and the rest of the bot keep working."),
}

async def _group_spawn_switch(update, context, command_name):
    uid = update.effective_user.id
    if not (is_owner(uid) or is_executive(uid)):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    chat_id = await _get_toggle_target_chat(update, context, command_name)
    if chat_id is None:
        return
    if not await is_group_approved(chat_id):
        await safe_reply_text(update.effective_message, "⚠️ This group is not approved. Use /approve first.")
        return
    flag, turn_off, what, other = _SPAWN_SWITCH_TEXT[command_name]
    try:
        await asyncio.to_thread(set_group_spawn_flag, chat_id, flag, turn_off)
    except Exception as e:
        print("Group spawn switch error:", e)
        await safe_reply_text(update.effective_message, "❌ Could not save the setting. Please try again.")
        return
    if flag == "auto_off":
        context.application.bot_data.setdefault("next_auto_spawn_at", {}).pop(chat_id, None)   # fresh timer when turned back on
    back = command_name.replace("off", "on") if turn_off else command_name.replace("on", "off")
    state = "OFF" if turn_off else "ON"
    await safe_reply_text(
        update.effective_message,
        f"{'🔴' if turn_off else '🟢'} {what} is now {state} in this group.\n🆔 Group ID: {chat_id}\n\n"
        f"Other groups are not affected.\n{other}\n"
        f"👑 Owner/Executive can turn it {'ON' if turn_off else 'OFF'} with /{back}.",
    )
    await notify_staff_action(
        context,
        f"{'🔴' if turn_off else '🟢'} {what.upper()} TURNED {state}\n🆔 Group ID: {chat_id}\n👤 By: {display_user(update.effective_user)}",
        actor_id=uid,
    )

async def spawn_off_command(update, context):
    await _group_spawn_switch(update, context, "spawnoff")

async def spawn_on_command(update, context):
    await _group_spawn_switch(update, context, "spawnon")

async def auto_off_command(update, context):
    await _group_spawn_switch(update, context, "autooff")

async def auto_on_command(update, context):
    await _group_spawn_switch(update, context, "autoon")

async def bot_off(update, context):
    if not (is_owner(update.effective_user.id) or is_executive(update.effective_user.id)):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return

    chat_id = await _get_toggle_target_chat(update, context, "botoff")
    if chat_id is None:
        return

    if not await is_group_approved(chat_id):
        await safe_reply_text(update.effective_message, "⚠️ This group is not approved. Use /approve first.")
        return

    (await asyncio.to_thread(set_bot_enabled, chat_id, False))
    context.application.bot_data.setdefault("active_chats", set()).discard(chat_id)
    context.application.bot_data.setdefault("bot_off_warning_sent", set()).discard(chat_id)

    active = context.application.bot_data.setdefault("active_spawns", {})
    removed_spawn = active.pop(chat_id, None)
    if removed_spawn:
        await cancel_spawn_expiry_task(removed_spawn)
        await safe_delete_message(context.bot, chat_id, removed_spawn.get("message_id"))

    await safe_reply_text(
        update.effective_message,
        f"🔴 Bot is now OFF in this group.\n🆔 Group ID: {chat_id}\n\n"
        "Other groups are not affected.\n"
        "👑 Owner/Executive can turn this group ON with /boton.",
    )
    await notify_staff_action(
        context,
        f"🔴 BOT TURNED OFF\n🆔 Group ID: {chat_id}\n👤 By: {display_user(update.effective_user)}",
        actor_id=update.effective_user.id,
    )

async def bot_on(update, context):
    if not (is_owner(update.effective_user.id) or is_executive(update.effective_user.id)):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return

    chat_id = await _get_toggle_target_chat(update, context, "boton")
    if chat_id is None:
        return

    if not await is_group_approved(chat_id):
        await safe_reply_text(update.effective_message, "⚠️ This group is not approved. Use /approve first.")
        return

    (await asyncio.to_thread(set_bot_enabled, chat_id, True))
    (await asyncio.to_thread(register_auto_spawn_group, chat_id))
    context.application.bot_data.setdefault("active_chats", set()).add(chat_id)
    context.application.bot_data.setdefault("bot_off_warning_sent", set()).discard(chat_id)

    await safe_reply_text(
        update.effective_message,
        f"🟢 Bot is now ON in this group.\n🆔 Group ID: {chat_id}\n\n"
        "Other groups are not affected.\n"
        "🤖 Bot functions and automatic spawning are active.",
    )
    await notify_staff_action(
        context,
        f"🟢 BOT TURNED ON\n🆔 Group ID: {chat_id}\n👤 By: {display_user(update.effective_user)}",
        actor_id=update.effective_user.id,
    )

async def track_group_chat(update, context):
    chat = getattr(update, "effective_chat", None)
    if not chat or chat.type not in ("group", "supergroup"):
        return

    user = getattr(update, "effective_user", None)
    if user and not getattr(user, "is_bot", False):
        context.application.bot_data.setdefault("last_group_member_activity", {})[chat.id] = datetime.now()

    approved, enabled = await group_gate(chat)
    if approved and enabled:
        cid = int(chat.id)
        if not _groups_cache_warm() or cid not in mongo_db.load_auto_spawn_groups():
            await asyncio.to_thread(register_auto_spawn_group, cid)
        context.application.bot_data.setdefault("active_chats", set()).add(chat.id)

OWNER_CONTACT_TTL = 60  # seconds: owner username is re-read from Telegram at most once a minute


def group_id_html(chat_id):
    """Group ID as tap-to-copy text (Telegram <code> entity). Always the real chat id passed in."""
    return f"<code>{html_escape(str(chat_id))}</code>"


async def get_group_link(bot, app, chat_id, chat=None, allow_fetch=True):
    """
    Best link that opens a group, or None. Order: public @username -> link remembered earlier ->
    the group's existing invite link -> a newly created invite link (never revokes an existing one).
    allow_fetch=False skips Telegram calls (used after the bot was removed: it can no longer ask).
    """
    try:
        cid = int(chat_id)
        cache = app.bot_data.setdefault("group_links", {})
        username = getattr(chat, "username", None) if chat is not None else None
        if username:
            cache[cid] = f"https://t.me/{username}"
            return cache[cid]
        if cache.get(cid):
            return cache[cid]
        if not allow_fetch:
            return None
        link = None
        try:
            info = await bot.get_chat(cid)
            link = f"https://t.me/{info.username}" if getattr(info, "username", None) else getattr(info, "invite_link", None)
            if not link:
                link = (await bot.create_chat_invite_link(cid)).invite_link
        except Exception as e:
            print(f"Group invite link unavailable for {chat_id}:", e)
        if link:
            cache[cid] = link
            return link
        return None  # private group and the bot has no invite right: no usable link exists
    except Exception as e:
        print(f"Group link error for {chat_id}:", e)
        return None


GROUP_NO_LINK_NOTE = ("⚠️ No join link yet. The bot is not an admin, or the group has no link the bot can use. "
                      "No characters spawn in this group until the bot is an admin.")

# Characters spawn only in groups where the bot is an admin. Set to False to turn this rule off.
REQUIRE_BOT_ADMIN_FOR_SPAWN = True
BOT_JOIN_ADMIN_TEXT = "🤖 Thanks for adding me! I need <b>admin</b> rights to work properly. Please promote me."
BOT_ADMIN_SPAWN_TEXT = ("❌ Make me an admin in this group first. "
                        "Characters spawn only where the bot is an admin.")


# Promo for our other bot: sent as its own message, ONCE per join (cleared when the bot leaves, so a re-add sends it once again).
PROMO_BOT_USERNAME = "GroupRealmBot"
PROMO_BOT_TEXT = (
    "🤖 Looking for a smarter way to manage your group?\n\n"
    "Try our group management bot with AI-powered smart features. "
    "It helps keep your group organized, safe and active.\n\n"
    f"👇 Tap the username to copy it, then add the bot to your group:\n<code>@{PROMO_BOT_USERNAME}</code>"
)
PROMO_SENT_COLL = "promo_sent_groups"


async def send_group_promo_once(bot, chat_id):
    """Send the promo message once for the current join. Safe against double join updates; a new join after the bot
    left or was removed sends it again (see clear_group_promo)."""
    cid = int(chat_id)
    try:
        res = await asyncio.to_thread(_mc(PROMO_SENT_COLL).update_one, {"_id": cid},
                                      {"$setOnInsert": {"sent_at": datetime.now(IST).isoformat()}}, True)
        if res.upserted_id is None:
            return                                   # already sent for this join
    except Exception as e:
        print(f"Promo check error for {cid}:", e)
        return                                       # when unsure, do not send
    try:
        await bot.send_message(
            chat_id=cid, text=PROMO_BOT_TEXT, parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(
                "➕ Invite Bot", url=f"https://t.me/{PROMO_BOT_USERNAME}?startgroup=true")]]))
    except Exception as e:
        print(f"Promo message error for {cid}:", e)


async def clear_group_promo(chat_id):
    """The bot left / was removed: forget the promo marker so the next join sends it once again."""
    try:
        await asyncio.to_thread(_mc(PROMO_SENT_COLL).delete_one, {"_id": int(chat_id)})
    except Exception as e:
        print(f"Promo reset error for {chat_id}:", e)


def approval_markup(link, cid):
    """Owner's approval request: '✅ Approve Group' (one tap) above '🔗 Open Group' / '🔄 Get Link'."""
    rows = [[InlineKeyboardButton("✅ Approve Group", callback_data=f"apvg:{int(cid)}")]]
    rows.extend(open_group_markup(link, cid).inline_keyboard if open_group_markup(link, cid) else [])
    return InlineKeyboardMarkup(rows)


def open_group_markup(link, cid=None):
    """'🔗 Open Group' when a link exists; else '🔄 Get Link' (retry) if cid is given; else no button."""
    if link:
        return InlineKeyboardMarkup([[InlineKeyboardButton("🔗 Open Group", url=link)]])
    if cid is not None:
        return InlineKeyboardMarkup([[InlineKeyboardButton("🔄 Get Link", callback_data=f"gl:{int(cid)}")]])
    return None


ADMIN_REQUIRED_COLL = "admin_required_groups"   # groups the bot was added to after this rule started


async def mark_admin_required(app, chat_id):
    """Remember that this is a NEW group: spawns there need the bot to be admin. Older groups are never added."""
    cid = int(chat_id)
    app.bot_data.setdefault("admin_required_cache", {"ids": set(), "ts": 0.0})["ids"].add(cid)
    try:
        await asyncio.to_thread(_mc(ADMIN_REQUIRED_COLL).update_one, {"_id": cid}, {"$set": {"added_at": datetime.now(IST).isoformat()}}, True)
    except Exception as e:
        print(f"Could not save new-group admin rule for {cid}:", e)


async def _admin_required(app, chat_id):
    cache = app.bot_data.setdefault("admin_required_cache", {"ids": set(), "ts": 0.0})
    now = time.monotonic()
    if now - cache["ts"] > 120:
        try:
            docs = await asyncio.to_thread(lambda: list(_mc(ADMIN_REQUIRED_COLL).find({}, {"_id": 1})))
            cache["ids"] = {int(d["_id"]) for d in docs} | cache["ids"]
            cache["ts"] = now
        except Exception as e:
            print("Admin-required list error:", e)
            cache["ts"] = now - 90          # retry in 30 s; until then keep what is already known
    return int(chat_id) in cache["ids"]


async def bot_is_group_admin(bot, app, chat_id):
    """True when spawning is allowed here: the bot is an admin (the 'Add users' right is not required).
    Applies to EVERY group, old and new, and to every kind of spawn.
    Short cache (30 s while not allowed, 5 min once allowed).
    If Telegram can't be asked, this returns True so a temporary error never stops spawns."""
    if not REQUIRE_BOT_ADMIN_FOR_SPAWN:
        return True
    cid = int(chat_id)
    if cid > 0:
        return True                                   # private chat, not a group
    cache = app.bot_data.setdefault("bot_admin_cache", {})
    now = time.monotonic()
    hit = cache.get(cid)
    if hit and now - hit[1] < (300 if hit[0] else 30):
        return hit[0]
    try:
        member = await bot.get_chat_member(cid, bot.id)
        if member.status == "creator":
            ok = True
        else:
            ok = member.status == "administrator"      # any admin is enough; the 'Add users' right is NOT required
    except Exception as e:
        print(f"Bot admin check error for {cid}:", e)
        return True
    cache[cid] = (ok, now)
    return ok


async def group_link_callback(update, context):
    """Owner taps '🔄 Get Link': try again to get a join link for that group."""
    query = update.callback_query
    if not query or not query.from_user or query.from_user.id not in ADMIN_IDS:
        if query:
            await query.answer("Owner only.", show_alert=True)
        return
    try:
        cid = int((query.data or "").split(":", 1)[1])
    except Exception:
        await query.answer()
        return
    link = await get_group_link(context.bot, context.application, cid)
    if not link:
        await query.answer("Still no link. Make sure the bot is an admin, then tap again.",
                           show_alert=True)
        return
    await query.answer("Link ready.")
    has_approve = any((b.callback_data or "").startswith("apvg:")
                      for row in ((query.message.reply_markup.inline_keyboard if query.message and query.message.reply_markup else []))
                      for b in row)
    new_markup = approval_markup(link, cid) if has_approve else open_group_markup(link)
    try:
        text = re.sub(r"\n{3,}", "\n\n", (query.message.text_html or "").replace(html_escape(GROUP_NO_LINK_NOTE), "")).rstrip()
        await query.edit_message_text(text, parse_mode="HTML", reply_markup=new_markup)
    except Exception:
        try:
            await query.edit_message_reply_markup(reply_markup=new_markup)
        except Exception as e:
            print("Group link button update error:", e)


async def get_owner_contact_html(bot, app=None):
    """
    Bot Owner's CURRENT @username, read live from Telegram for the configured owner (ADMIN_IDS[0]).
    A changed username is picked up automatically (cached for OWNER_CONTACT_TTL seconds only).
    Falls back to a clickable name/mention if the owner has no username or Telegram can't be reached.
    """
    owner_id = ADMIN_IDS[0] if ADMIN_IDS else None
    if not owner_id:
        return "Not configured"
    cache = app.bot_data.setdefault("owner_contact_cache", {}) if app is not None else {}
    cached = cache.get(owner_id)
    now = time.monotonic()
    if cached and now - cached[0] < OWNER_CONTACT_TTL:
        return cached[1]
    try:
        owner_chat = await bot.get_chat(owner_id)
        username = getattr(owner_chat, "username", None)
        if username:
            result = f"@{html_escape(username)}"
        else:
            name = " ".join(p for p in ((getattr(owner_chat, "first_name", "") or "").strip(),
                                        (getattr(owner_chat, "last_name", "") or "").strip()) if p) or "Owner"
            result = f'<a href="tg://user?id={int(owner_id)}">{html_escape(name)}</a>'
        cache[owner_id] = (now, result)
        return result
    except Exception as e:
        print("Owner username lookup error:", e)
        if cached:
            return cached[1]  # stale value is better than nothing
        return f'<a href="tg://user?id={int(owner_id)}">Bot Owner</a>'


async def build_unapproved_group_text(bot, app, chat_id, header=None):
    owner = await get_owner_contact_html(bot, app)
    head = header or ("🚫 This group is not approved yet.\n"
                      "👑 Contact the bot owner to approve this group.")
    return f"{head}\n👤 Bot Owner: {owner}\n🆔 Group ID: {group_id_html(chat_id)}"


async def track_bot_membership(update, context):
    chat = getattr(update, "effective_chat", None)
    member_update = getattr(update, "my_chat_member", None)
    if not chat or chat.type not in ("group", "supergroup") or not member_update:
        return

    status = member_update.new_chat_member.status
    if status in ("member", "administrator"):
        (await asyncio.to_thread(register_bot_group, chat))
        if getattr(member_update.old_chat_member, "status", None) in ("left", "kicked"):
            (await asyncio.to_thread(unhide_gstats_group, chat.id))        # re-added: show it in /gstats again
        if (status == "member"
                and getattr(member_update.old_chat_member, "status", None) in ("left", "kicked")):
            await mark_admin_required(context.application, chat.id)    # new group: spawns need the bot as admin
            try:   # newly added as a normal member: ask the group to promote the bot (sent once per join)
                await context.bot.send_message(chat_id=chat.id, text=BOT_JOIN_ADMIN_TEXT, parse_mode="HTML")
            except Exception as e:
                print(f"Admin request message error for {chat.id}:", e)
        if getattr(member_update.old_chat_member, "status", None) in ("left", "kicked"):
            await send_group_promo_once(context.bot, chat.id)             # new group: promo message, once only
        if await is_group_approved(chat.id):
            (await asyncio.to_thread(register_auto_spawn_group, chat.id))
            context.application.bot_data.setdefault("active_chats", set()).add(chat.id)
            return

        aa_note = None
        if await is_auto_approve_on():
            approved_now, aa_note = await auto_approve_group(context, chat, getattr(member_update, "from_user", None))
            if approved_now:
                return
            # not approved (too few members / failed): fall through to the normal manual-approval flow below

        notified = context.application.bot_data.setdefault("unapproved_notified", set())
        if chat.id not in notified:
            notified.add(chat.id)
            try:
                await context.bot.send_message(
                    chat_id=chat.id,
                    text=await build_unapproved_group_text(context.bot, context.application, chat.id),
                    parse_mode="HTML",
                )
            except Exception as e:
                print(f"Unapproved group notice error for {chat.id}:", e)
            owner_id = ADMIN_IDS[0] if ADMIN_IDS else None
            if owner_id:
                try:
                    added_by = getattr(member_update, "from_user", None)
                    added_by_text = display_user(added_by) if added_by else "Unknown"
                    group_link = await get_group_link(context.bot, context.application, chat.id, chat)
                    await context.bot.send_message(
                        chat_id=owner_id,
                        reply_markup=approval_markup(group_link, chat.id),
                        text=(
                            "🔔 New Group Approval Request\n"
                            f"🏷 Group: {html_escape(chat.title or 'Unknown')}\n"
                            f"🆔 Group ID: {group_id_html(chat.id)}\n"
                            f"👤 Requested by: {code_ids_html(html_escape(added_by_text))}\n"
                            + (f"{html_escape(aa_note)}\n" if aa_note else "") +
                            ("" if group_link else f"\n{html_escape(GROUP_NO_LINK_NOTE)}\n") +
                            f"\nApprove with: /approve <code>{html_escape(str(chat.id))}</code>"
                        ),
                        parse_mode="HTML",
                    )
                except Exception as e:
                    print("Owner group-approval notification error:", e)
        (await asyncio.to_thread(unregister_auto_spawn_group, chat.id))
        context.application.bot_data.setdefault("active_chats", set()).discard(chat.id)
    elif status in ("left", "kicked"):
        await clear_group_promo(chat.id)                       # next join sends the promo once again
        (await asyncio.to_thread(unregister_bot_group, chat.id))
        (await asyncio.to_thread(unregister_auto_spawn_group, chat.id))
        context.application.bot_data.setdefault("active_chats", set()).discard(chat.id)
        # Bot removed/kicked by someone: tell the owner (PM) and the linked log channel who did it.
        try:
            remover = getattr(member_update, "from_user", None)
            recent = context.application.bot_data.setdefault("bot_removed_notified", {})
            now_mono = time.monotonic()
            if remover and remover.id != context.bot.id and now_mono - recent.get(chat.id, -999.0) > 30:
                recent[chat.id] = now_mono
                notice = (
                    "🚪 Bot removed from a group\n"
                    f"🏷 Group: {chat.title or 'Unknown'}\n"
                    f"🆔 Group ID: {chat.id}\n"
                    f"👤 Removed by: {display_user(remover)}\n"
                    f"🕒 {log_time_text()}"
                )
                owner_id = ADMIN_IDS[0] if ADMIN_IDS else None
                if owner_id:
                    try:
                        group_link = await get_group_link(context.bot, context.application, chat.id, chat, allow_fetch=False)
                        await context.bot.send_message(chat_id=owner_id, text=notice, entities=copyable_ids(notice),
                                                       reply_markup=open_group_markup(group_link))
                    except Exception as e:
                        print("Owner bot-removed notification error:", e)
                cfg = await get_log_config()
                if cfg and cfg.get("chat_id") is not None:
                    enqueue_log_routed(context.application, cfg, notice)
        except Exception as e:
            print("Bot-removed notification error:", e)

SPAWN_LIFETIME = 20 * 60  # 20 minutes
PENDING_EXPIRY_CHECK_SECONDS = 30       # how often missed "character is gone" notices are looked for
STALE_EXPIRY_NOTICE_SECONDS = 60 * 60   # an expiry notice older than this (after the spawn ended) is closed without sending
AUTO_SPAWN_INTERVAL = 30 * 60  # 30 minutes
PERSONAL_SPAWN_COOLDOWN = 3600  # 1 hour: Scouts and general members
STAFF_SPAWN_COOLDOWN = 1800     # 30 minutes: Owner and Executive
GROUP_SPAWN_COOLDOWN = 70       # 70 seconds
SYMBOL = {
    "Common": "⚪",
    "Rare": "🔵",
    "Epic": "🟣",
    "Legendary": "💎",
    "Mythical": "🔮",
    "Celestial": "💠",
    "Heavenly": "🧿",   # fusion-only tier: never spawns, only /addevo and /editevo may use it
}

WORTH = {
    "Common": 50,
    "Rare": 100,
    "Epic": 250,
    "Legendary": 500,
    "Mythical": 750,
    "Celestial": 1000,
}

CHANCES = [
    ("Common", 43),
    ("Rare", 27),
    ("Epic", 23),
    ("Legendary", 5),
    ("Mythical", 1.8),
    ("Celestial", 0.2),
]

# High-rank characters keep strict daily limits; spacing restrictions are fixed at 20/20/50.
LEGENDARY_DAILY_LIMIT = 6
MYTHICAL_DAILY_LIMIT = 2
CELESTIAL_DAILY_LIMIT = 1
HIGH_RARITY_GAP_MIN = 20
HIGH_RARITY_GAP_MAX = 20
CELESTIAL_GAP_TARGET = 50

MAX_CHARACTER_SUCCESSFUL_ADDS_GLOBAL = 2  # per character, per India-time day

POPULAR_RARITY_OVERRIDES = {
    "Naruto": "Mythical",
    "Kakashi": "Legendary",
    "Itachi": "Legendary",
    "Madara": "Mythical",
    "Naruto Baryon Mode": "Mythical",
    "Luffy": "Mythical",
    "Zoro": "Legendary",
    "Law": "Legendary",
    "Shanks": "Mythical",
    "Gol D. Roger": "Mythical",
    "Goku": "Mythical",
    "Vegeta": "Legendary",
    "Gohan": "Legendary",
    "Broly": "Mythical",
    "Ultra Instinct Goku": "Mythical",
    "Gojo Satoru": "Mythical",
    "Sukuna": "Mythical",
    "Tanjiro Kamado": "Legendary",
    "Kyojuro Rengoku": "Legendary",
    "Yoriichi": "Mythical",
    "Eren Yeager": "Legendary",
    "Mikasa Ackerman": "Legendary",
    "Levi Ackerman": "Mythical",
    "Founding Titan Eren": "Mythical",
}

CHARACTERS = [
    ("Naruto", "Naruto", "Rare"),
    ("Sakura", "Naruto", "Common"),
    ("Kakashi", "Naruto", "Rare"),
    ("Itachi", "Naruto", "Epic"),
    ("Madara", "Naruto", "Mythical"),
    ("Naruto Baryon Mode", "Naruto", "Legendary"),
    ("Luffy", "One Piece", "Legendary"),
    ("Nami", "One Piece", "Common"),
    ("Zoro", "One Piece", "Rare"),
    ("Sanji", "One Piece", "Rare"),
    ("Law", "One Piece", "Epic"),
    ("Shanks", "One Piece", "Legendary"),
    ("Gol D. Roger", "One Piece", "Mythical"),
    ("Goku", "Dragon Ball", "Mythical"),
    ("Vegeta", "Dragon Ball", "Epic"),
    ("Piccolo", "Dragon Ball", "Rare"),
    ("Gohan", "Dragon Ball", "Epic"),
    ("Broly", "Dragon Ball", "Legendary"),
    ("Ultra Instinct Goku", "Dragon Ball", "Mythical"),
    ("Yuji Itadori", "Jujutsu Kaisen", "Common"),
    ("Nobara Kugisaki", "Jujutsu Kaisen", "Common"),
    ("Megumi Fushiguro", "Jujutsu Kaisen", "Rare"),
    ("Maki Zenin", "Jujutsu Kaisen", "Epic"),
    ("Gojo Satoru", "Jujutsu Kaisen", "Mythical"),
    ("Sukuna", "Jujutsu Kaisen", "Legendary"),
    ("Tanjiro Kamado", "Demon Slayer", "Common"),
    ("Zenitsu Agatsuma", "Demon Slayer", "Common"),
    ("Inosuke Hashibira", "Demon Slayer", "Rare"),
    ("Giyu Tomioka", "Demon Slayer", "Epic"),
    ("Kyojuro Rengoku", "Demon Slayer", "Legendary"),
    ("Yoriichi", "Demon Slayer", "Mythical"),
    ("Eren Yeager", "Attack on Titan", "Common"),
    ("Mikasa Ackerman", "Attack on Titan", "Rare"),
    ("Armin Arlert", "Attack on Titan", "Rare"),
    ("Levi Ackerman", "Attack on Titan", "Legendary"),
    ("Erwin Smith", "Attack on Titan", "Epic"),
    ("Founding Titan Eren", "Attack on Titan", "Mythical"),
]

# (SQLite removed: all persistent data now lives in MongoDB - see mongo_db.py)

def setup_database():
    """MongoDB bootstrap: indexes, singleton documents, built-in characters, staff cache."""
    mongo_db.ensure_indexes()

    today_key = get_high_rank_today_key()
    spacing = _mc("high_rarity_spacing_v1")
    spacing.update_one(
        {"_id": 1},
        {"$setOnInsert": {"id": 1, "high_target": HIGH_RARITY_GAP_MIN,
                          "celestial_target": CELESTIAL_GAP_TARGET, "day_key": today_key}},
        upsert=True,
    )
    spacing.update_one(
        {"_id": 1, "day_key": {"$ne": today_key}},
        {"$set": {"high_target": HIGH_RARITY_GAP_MIN, "celestial_target": CELESTIAL_GAP_TARGET, "day_key": today_key}},
    )
    _mc("spawn_limits_global_v1").update_one(
        {"_id": 1},
        {"$setOnInsert": {"id": 1, "day_key": today_key, "legendary_count": 0, "mythical_count": 0,
                          "celestial_count": 0, "legendary_pending": 0, "mythical_pending": 0,
                          "celestial_pending": 0}},
        upsert=True,
    )

    # Built-in characters: insert any that are missing (never overwrites existing rows/photos).
    mongo_db.seed_characters(CHARACTERS, WORTH, POPULAR_RARITY_OVERRIDES, first_code=1001)

    # Staff roles -> in-memory ID lists
    roles = _mc("staff_roles_v2")
    for stored_id, role in _staff_role_rows():
        if role == "executive" and stored_id not in EXECUTIVE_IDS:
            EXECUTIVE_IDS.append(stored_id)
    for stored_id, role in _staff_role_rows():
        if role == "scout" and stored_id not in EXECUTIVE_IDS and stored_id not in SCOUT_IDS:
            SCOUT_IDS.append(stored_id)

    if EXECUTIVE_IDS and SCOUT_IDS:
        conflicting = set(EXECUTIVE_IDS) & set(SCOUT_IDS)
        for conflicting_id in conflicting:
            roles.delete_one({"_id": conflicting_id, "role": "scout"})
        SCOUT_IDS[:] = [uid for uid in SCOUT_IDS if uid not in conflicting]

    for executive_id in EXECUTIVE_IDS:
        roles.update_one(
            {"_id": int(executive_id)},
            {"$set": {"user_id": int(executive_id), "role": "executive"}, "$setOnInsert": {"added_at": timestamp()}},
            upsert=True,
        )

_SAVED_USERS = {}

def save_user(u):
    """Upsert the Telegram profile. Skips the DB round-trip if nothing changed in the last 10 min."""
    key = (u.username or "", u.first_name or "", u.last_name or "")
    now_mono = time.monotonic()
    last = _SAVED_USERS.get(u.id)
    if last and last[0] == key and now_mono - last[1] < 600:
        return
    mongo_db.save_user(u.id, *key)
    _SAVED_USERS[u.id] = (key, now_mono)

async def save_user_async(u):
    """save_user() without a thread hop when the profile was saved in the last 10 minutes."""
    key = (u.username or "", u.first_name or "", u.last_name or "")
    last = _SAVED_USERS.get(u.id)
    if last and last[0] == key and time.monotonic() - last[1] < 600:
        return
    await asyncio.to_thread(save_user, u)

def get_recruit_names(character_code):
    return mongo_db.get_recruit_names(character_code)

def set_recruit_names(character_code, names):
    return mongo_db.set_recruit_names(character_code, names)

def find_character_by_recruit_name(value):
    row = mongo_db.find_character_by_recruit_name(value)
    return None if row and rewards.is_hidden(row[0]) else row      # festival event cards never show in searches

def find_characters_by_recruit_name_partial(value):
    return mongo_db.find_characters_by_recruit_name_partial(value)

def find_characters_by_name_parts(query):
    return rewards.filter_hidden(mongo_db.find_characters_by_name_parts(query))

def get_character(value):
    value = str(value).strip()
    if not value:
        return None
    if value.isdigit() and 1 <= int(value) <= 9999:
        return get_character_by_code(value)
    rows = find_characters_by_name_parts(value)
    if len(rows) == 1:
        return rows[0]
    if len(rows) > 1:
        return None
    recruit = find_character_by_recruit_name(value)
    return recruit

def get_character_by_code(code):
    code = str(code).strip()
    if not (code.isdigit() and 1 <= int(code) <= 9999):
        return None
    return mongo_db.get_character_by_code(code.zfill(4))

def get_all_characters():
    return rewards.filter_hidden(mongo_db.get_all_characters())     # festival event cards stay out of /characters

def get_characters_by_rarity(rarity):
    return rewards.filter_hidden(mongo_db.get_characters_by_rarity(rarity))     # spawns, /daily and shops never pick event cards

def is_character_discontinued(code):
    return mongo_db.is_character_discontinued(code)

def discontinue_character(code, user_id):
    mongo_db.discontinue_character(code, user_id, timestamp())

def continue_character(code):
    return mongo_db.continue_character(code)

def is_owner(user_id):
    return bool(ADMIN_IDS) and user_id == ADMIN_IDS[0]

def is_executive(user_id):
    return user_id in EXECUTIVE_IDS

SCOUT_IDS = []

def is_scout(user_id):
    if user_id in SCOUT_IDS:
        return True
    try:
        found = _mc("staff_roles_v2").find_one({"_id": int(user_id), "role": "scout"}, {"_id": 1}) is not None
        if found and user_id not in SCOUT_IDS and user_id not in EXECUTIVE_IDS and not is_owner(user_id):
            SCOUT_IDS.append(user_id)
        return found
    except Exception as e:
        print("Scout role lookup error:", e)
        return False

def can_manage_characters(user_id):
    return is_owner(user_id) or is_executive(user_id) or is_scout(user_id)

def staff_role(user_id):
    if is_owner(user_id):
        return "Owner"
    if is_executive(user_id):
        return "Executive"
    if is_scout(user_id):
        return "Scout"
    return "User"

def skip_keyboard():
    return ReplyKeyboardMarkup([["⏭ Skip"]], resize_keyboard=True, one_time_keyboard=True)

def is_skip_text(text):
    return (text or "").strip().lower() in ("/skip", "⏭ skip")

# ---------------------------------------------------------------------------------------------------
# DEFAULT WORTH PER RARITY. The WORTH table above is the built-in default; Owner/Executive can change each
# rarity's default from /help -> Add & Edit -> 💰 Change Worth. Changes are saved in MongoDB (they survive
# restarts) and are used by /addcharacter and /edit. Characters that already exist keep their saved worth.
# ---------------------------------------------------------------------------------------------------
DEFAULT_WORTH_COLLECTION = "default_worth_v1"
DEFAULT_WORTH_MAX = 10000000
CW_RARITIES = ("Common", "Rare", "Epic", "Legendary", "Mythical", "Celestial")
CW_INPUT_TIMEOUT = 300                # seconds the bot waits for the new worth number
_cw_waiting = {}                      # user id -> (rarity, role, expiry time.monotonic)
_worth_defaults_cache = None          # {rarity: worth} saved by Owner/Executive; None = not loaded yet


def _load_worth_overrides():
    """Saved defaults {rarity: worth}, or None when MongoDB cannot be read (the WORTH table is used then)."""
    try:
        doc = _mc(DEFAULT_WORTH_COLLECTION).find_one({"_id": "worth"}) or {}
        out = {}
        for rarity, value in (doc.get("values") or {}).items():
            if rarity in WORTH and isinstance(value, (int, float)) and int(value) >= 0:
                out[rarity] = int(value)
        return out
    except Exception as e:
        print("Default worth load error:", repr(e))
        return None


def default_worth(rarity):
    """Default worth of a rarity (saved value, else the WORTH table); None for a rarity that has no default."""
    global _worth_defaults_cache
    if rarity not in WORTH:
        return None
    if _worth_defaults_cache is None:
        loaded = _load_worth_overrides()
        if loaded is None:
            return WORTH[rarity]
        _worth_defaults_cache = loaded
    return _worth_defaults_cache.get(rarity, WORTH[rarity])


async def default_worth_async(rarity):
    return await asyncio.to_thread(default_worth, rarity)


def set_default_worth(rarity, value, user_id):
    global _worth_defaults_cache
    _mc(DEFAULT_WORTH_COLLECTION).update_one(
        {"_id": "worth"},
        {"$set": {f"values.{rarity}": int(value), "updated_by": int(user_id), "updated_at": india_timestamp()}},
        upsert=True)
    _worth_defaults_cache = None        # reloaded from MongoDB on the next read

def format_duration(seconds):
    seconds = max(0, int(seconds))
    hours, rem = divmod(seconds, 3600)
    minutes, seconds = divmod(rem, 60)
    return (
        f"{hours} hour" + ("s" if hours != 1 else "") + ", "
        f"{minutes} minute" + ("s" if minutes != 1 else "") + " and "
        f"{seconds} second" + ("s" if seconds != 1 else "")
    )

def spawn_name_matches(spawn_name, entered_parts):
    parts = [str(p).strip().casefold() for p in entered_parts if str(p).strip()]
    if not parts:
        return False
    name_parts = [p.casefold() for p in str(spawn_name).split() if p.strip()]
    if not name_parts:
        return False
    if len(parts) == 1 and parts[0] in {name_parts[0], name_parts[-1]}:
        return True
    return ''.join(parts) == ''.join(name_parts) or sorted(parts) == sorted(name_parts)

def _number_commands(text):
    """'/cmd — desc' lines become '1. /cmd - desc' (one per line); numbering restarts under every heading."""
    out, n = [], 0
    for line in text.split("\n"):
        if line.startswith("/"):
            n += 1
            out.append(f"{n}. " + line.replace(" — ", " - ", 1))
        else:
            if not line.strip() or not line.startswith(" "):
                n = 0
            out.append(line)
    return "\n".join(out)


def build_help_text():
    return theme.decorate_help_text(_number_commands(_build_help_text_raw()))


def _build_help_text_raw():
    return (
        "🎮 Anime Character Catcher — Command List\n\n"
        "👤 Profile & Collection\n"
        "/start — Register / start the bot\n"
        "/help — Show this command list\n"
        "/reply — Message the bot staff (private chat only)\n"
        "/mycollection — View your collection\n"
        "/see <user_id or @username> — View another user's collection\n"
        "/myfav <code/name> — Set your favourite character\n"
        "/mystats — See your stats and progress\n"
        "/characters [tier] — List all characters, or one tier\n"
        "/view <code/name> — See a character's details and image\n"
        "/check <code/name> — See a character's details and owners\n"
        "/addlist — See who added and edited the most characters\n\n"
        "🎯 Catching & Rewards\n"
        "/spawn — Spawn a character in the group\n"
        "/add — Catch the spawned character\n"
        "/daily — Claim your daily reward\n"
        "/dailytask — Do daily missions to earn Berrys\n"
        "/sell <code/name> [quantity] — Sell a character for Berrys\n"
        "/rem [number] — Delete the bot's messages\n"
        "/transfer <code/name> — Give a character to a user (reply to them)\n"
        "/exchange <your_code> <their_code> — Swap same-tier characters (reply to a user)\n\n"
        "🎮 Games\n"
        "/guess_num — Start a Guess the Number game\n"
        "/nguess <number> — Guess a number from 1 to 100\n\n"
        "🫐 Berrys\n"
        "/berrytransfer <amount> — Give Berrys to a user (reply to them)\n"
        "/berry — See how many Berrys you can still send today\n\n"
        "🎪 Events & Redeem\n"
        "/event — View the active event\n"
        "/redeem <code> — Redeem a code\n\n"
        "🛒 Shop\n"
        "/shop — Buy characters from your personal shop\n\n"
        "🌟💫 Evolution\n"
        "/evolution — See all evolution recipes\n"
        "/evolve [code/name] — Evolve a character into a stronger one\n\n"
        "💎 Stones & Items\n"
        "/stonetask — Do daily tasks to earn stones\n"
        "/claimstone — Collect stones from finished tasks\n"
        "/stone — Stone leaderboard\n"
        "/item — See your items and Mystery Boxes\n\n"
        + badge_banner.PUBLIC_HELP_SECTION + rewards.PUBLIC_HELP_SECTION +
        "📜 Rules\n"
        "/rules — Read the bot rules\n\n"
        "👥 Staff\n"
        "/executives — See the Executive list\n"
        "/scouts — See the Scout list\n\n"
        "📝 Support\n"
        "/issue — Report an issue\n"
        "/idea — Send a suggestion\n"
        "/restrictions — See why you are restricted\n"
        "/appeal — Appeal a restriction\n"
        "/about — About this bot\n"
        "/cancel — Cancel the current action\n\n"
    )

# ==========================================================================
# ROLE-BASED HELP (restricted roles only: 3-column module grids with detail views)
#   General users keep the plain text help (build_help_text) and never see these menus.
#   Visibility is hierarchical: Owner -> Owner+Executive+Scout, Executive -> Executive+Scout, Scout -> Scout.
# ==========================================================================
def _help_page(title, overview, entries, note=None):
    lines = [title, "", "📌 Overview", overview, "", "⌨️ Commands & usage"]
    for number, (syntax, desc) in enumerate(entries, 1):
        lines.append(f"{number}. {syntax} - {desc}")
    if note:
        lines.extend(["", note])
    return "\n".join(lines)


def _addedit_page(role):
    """Add & Edit page: Owner sees /addevo, /editevo, /delevo; Executive sees /addevo, /editevo; Scout sees none of them."""
    staff_evo = role in ("owner", "executive")
    entries = [
        ("/addcharacter", "Add a character (guided)"),
        ("/editphoto <name/code>", "Edit a normal character's photo" + (" (Evolution photos: use /editevo)" if staff_evo else "")),
        ("/editcharacter <code/name>",
         "Edit a normal character: name, anime, rank/rarity, worth, 4-digit code, recruitment/search names (short form: /edit)"
         + (". Evolution characters can't be edited here - use /editevo" if staff_evo else "")),
    ]
    if staff_evo:
        entries.append(("/editcode <code/name> <new code>",
                        "Change a normal character's 4-digit code directly (PM only). Same checks as /edit, including the anime's code range"))
        entries.append(("/addevo", "Add an Evolution (guided, PM only): choose 🌟 Same Card (copies of one card) or 💫 Different Card (two different cards), then the cards, quantities, name, anime, rarity, worth, "
                                   "Evolution Stones (min 10), Berrys cost, code, photo"))
        entries.append(("/editevo <code/name>", "Edit an Evolution character AND its recipe (guided, PM only): name, anime, rarity, "
                                                "worth, photo, code, base character, quantity, Evolution Stones, Berrys cost. "
                                                "Normal characters use /edit"))
    if role == "owner":
        entries.append(("/delevo <code>", "Delete an Evolution recipe (Owner only). Evolution characters users already own are kept"))
    return _help_page(
        "🎴 Add & Edit Characters (Owner, Executive & Scout)",
        "Add and maintain characters. The editor also changes recruitment/search names.",
        entries)


HELP_ROLE_TITLES = {"owner": "👑 Owner Commands", "executive": "⚡ Executive Commands", "scout": "🔭 Scout Commands"}

HELP_MODULES = {
    "owner": [
        ("logchannel", "📡 Log Channel", _help_page(
            "📡 Log Channel (Owner only)",
            "Posts bot activity to a private Telegram channel.\nSetup: 1) add me to the channel as Administrator  "
            "2) send /setlog in the channel  3) forward that message to me in private chat.",
            [("/setlog", "Link a log channel (follow the setup steps above). Repeat it to link more channels (max 10); the first one is the default"),
             ("/setlog <chat_id>", "Alternative if forwarding is blocked, e.g. /setlog -1001234567890"),
             ("/unsetlog [chat_id|all]", "Unlink one log channel (no id is enough when only one is linked) or all of them"),
             ("/logchannel", "Show every linked log channel, the default (⭐) and how many routes each has"),
             ("/logdefault <chat_id>", "Choose the default channel (gets everything that has no route)")],
            "🔀 Routing: Member, Scout and Executive commands are posted automatically after they succeed. "
            "Your character commands (/spawn, /addcharacter, /gift ...) are posted automatically; "
            "/callcharacter is never logged. Your other commands ask you in PM "
            "\"Do you want to upload this action log to the log channel?\" with Yes / No.")),
        ("logcats", "📂 Log Categories", _help_page(
            "📂 Log Categories (Owner only)",
            "Categories group log events. Built-in and custom categories can be switched on or off.",
            [("/logcategories", "List every category with Enabled/Disabled and its description"),
             ("/log <category|all>", "Enable a category"),
             ("/nolog <category|all>", "Disable a category"),
             ("/addcategory <name> <description>", "Add a custom category (lowercase letters, digits, _ ; e.g. guild, shop_v2). Enabled by default"),
             ("/removecategory <name>", "Delete a custom category; its command mappings are removed too")])),
        ("logroute", "🧭 Log Routing", _help_page(
            "🧭 Log Routing (Owner only)",
            "Send different logs to different channels. Order: command route > category route > default channel.",
            [("/logroute <category> <chat_id>", "Whole category to a channel, e.g. /logroute economy -1001234567890"),
             ("/logroute /<command> <chat_id>", "One command to a channel, e.g. /logroute /daily -1001234567890"),
             ("/logroute <category|/command> default", "Back to the default channel"),
             ("/unlogroute <category|/command>", "Remove a route"),
             ("/logroutes", "Show the default channel and all routes")],
            "Extra category: security (unauthorized attempts). A leading / means a command, no slash means a category.")),
        ("logmap", "🗺 Log Mapping", _help_page(
            "🗺 Log Mapping (Owner only)",
            "Decide which log category a command is logged under, without editing code. A mapping beats the built-in default.",
            [("/logmap <command> <category>", "e.g. /logmap /craft shop_v2 (leading / optional). The category must exist. "
                                               "Overwrites an old mapping and tells you; warns if the command is not registered"),
             ("/unlogmap <command>", "Remove a mapping; the command goes back to its default category"),
             ("/logmappings", "List all mapped commands and their categories")])),
        ("staff", "👔 Staff Roles", _help_page(
            "👔 Staff Roles (Owner only)",
            "Manage Executives, Scouts and who may approve groups.",
            [("/addexec <user_id>", "Add an Executive"),
             ("/removeexec <user_id>", "Remove an Executive"),
             ("/addscout <user_id>", "Add a Scout"),
             ("/removescout <user_id>", "Remove a Scout"),
             ("/scouts", "View the Scout list (public: every user can run it)"),
             ("/addgroupapprove <executive_user_id>", "Let an Executive approve/remove groups"),
             ("/removegroupapprove <executive_user_id>", "Take that permission away")],
            "The Executive and Scout lists are public: /executives and /scouts.")),
        ("groups", "🏘 Groups", _help_page(
            "🏘 Groups",
            "Approve groups, remove them, and check the bot's state.",
            [("/approve", "In a group: approve it. In PM: /approve <group_chat_id> (Owner, or an Executive with permission)"),
             ("/removeapprove", "In PM: /removeapprove <group_chat_id>"),
             ("/leavegroup", "In PM: /leavegroup <group_chat_id> — remove the group and leave it"),
             ("/status", "Bot status and active spawns"),
             ("/gstats", "View bot group statistics"),
             ("/cooldown", "View character cooldowns for a group (in PM: all groups, or /cooldown <group_id>)"),
             ("/spawncooldown", "Personal /spawn cooldown for members and Scouts in ONE group: /spawncooldown <minutes> [group_id] (inside the group the id is optional), /spawncooldown reset [group_id], or /spawncooldown alone to view. Owner and Executives always keep 30 minutes. Main group -1003379716050 starts at 45 minutes; every other group stays at 1 hour")],
            "✅ Approval requests sent to you have an Approve Group button (same as /approve). Characters spawn only in a group where the bot is an admin (any kind of spawn, old and new groups).")),
        ("characters", "🎴 Characters", _help_page(
            "🎴 Characters (Owner only)",
            "Spawn, gift, discontinue and delete characters.",
            [("/callcharacter", "Spawn a specific character: I ask for the character, then the Group ID (no cooldown)"),
             ("/gift", "Reply to a user with /gift <character code or name>"),
             ("/removechar <user_id> <code/name> [quantity]", "Remove characters from any user's collection"),
             ("/discontinue <code or name>", "Stop a character from spawning"),
             ("/continue <code or name>", "Allow a discontinued character again"),
             ("/delete <name or code>", "Delete a character")])),
        ("events", "🎉 Events & Codes", _help_page(
            "🎉 Events & Redeem Codes (Owner only)",
            "Run a timed event with a trigger word and reward, and manage redeem codes (members use /redeem <code>).",
            [("/addevent", "Guided setup: name, code, rewards (Berrys + Stones + character), trigger text, claims per user, end date and time"),
             ("/endevent", "End the active event"),
             ("/addredeem", "Guided setup: type, reward, claim limit, expiry, code"),
             ("/deleteredeem CODE", "Disable a code"),
             ("/redeems", "List active codes")])),
        ("history", "📊 History", _help_page(
            "📊 History (Owner only)",
            "Look back at what the bot has been doing.",
            [("/history [1-50]", "Recent spawn history")])),
        ("data", "🗂 Data", _help_page(
            "🗂 Data (Owner only)",
            "Delete, back up, restore and transfer a user's game data. Use the commands in private chat.",
            [("/finduser <name or @username>", "Find a user's ID from part of a saved name or username (lists all matches, tap an ID to copy)"),
             ("/deleteuser <user_id>", "Preview what would be deleted, then press 🗑 Delete Data (private chat) to permanently delete that user's data. A backup file is sent to your PM first (nothing is stored on the bot)"),
             ("/restoreuser <user_id>", "Show the latest backup of a deleted user, then press ✅ Confirm Restore (private chat). Refused if the user already has data or the backup was already transferred. You can also reply to a backup file the bot sent you with /restoreuser (no ID needed)"),
             ("/moveuser <old_id> <new_id>", "Show a preview of copying a deleted account's data to the same person's NEW account (it must have pressed /start first), then press ✅ Confirm Transfer. The old data or backup is kept and cannot be transferred twice"),
             ("/exportdb [collection ...]", "Send the WHOLE database (every collection, not only user data) to your PM as zip file(s) of JSON files, in private chat. Add collection names to export only those. Nothing is stored on the bot"),
             ("/importdb [collection ...]", "Restore the database from the zip files made by /exportdb, in private chat: send all the parts, tap Done to see what they contain, then choose ➕ Add missing only (safe) or ♻ Replace (a safety copy is sent first and you must type REPLACE). Add collection names to restore only those"),
             ("/removechar <user_id> <code/name> [quantity]", "Remove characters from a user's collection (also listed under Characters)")],
            "🔔 Deleted-account notices: when the bot thinks an account may be deleted it sends you a notice with "
            "🗑️ Delete Data and ❌ Keep Data. Delete Data asks for a second confirmation and saves a backup first; "
            "nothing is ever deleted automatically.")),
    ],
    "executive": [
        ("restrict", "🚫 Restrictions", _help_page(
            "🚫 Restrictions (Owner & Executive)",
            "Temporarily stop a user from spawning, catching, transferring and exchanging characters (durations: 1h, 10h, 1d up to 365d; they expire automatically), or stop character transfers between two specific users.",
            [("/restrict <duration> [reason]", "Reply to the user (run it again on a restricted user to change the duration; the old reason is kept if you add none)"),
             ("/restrict <user_id> <duration> [reason]", "By user ID"),
             ("/unrestrict", "Reply to the user to lift the restriction"),
             ("/unrestrict <user_id>", "Lift by user ID"),
             ("/restrictions", "View all active restrictions (members see only their own)"),
             ("/btransfer <user_id_1> <user_id_2>", "Block character transfers between the pair"),
             ("/unbtransfer <user_id_1> <user_id_2>", "Remove the transfer block")])),
        ("groupctl", "🤖 Group Control", _help_page(
            "🤖 Group Control (Owner & Executive)",
            "Switch the bot, the /spawn command or automatic spawning on or off per group, and fix spawns that got stuck.",
            [("/boton [group_chat_id]", "Turn the bot ON in a group (PM supported)"),
             ("/botoff [group_chat_id]", "Turn the bot OFF in a group (PM supported)"),
             ("/spawnon [group_chat_id]", "Turn the /spawn command ON in a group (PM supported)"),
             ("/spawnoff [group_chat_id]", "Turn the /spawn command OFF in a group; automatic spawning keeps running (PM supported)"),
             ("/autoon [group_chat_id]", "Turn automatic spawning ON in a group (PM supported)"),
             ("/autooff [group_chat_id]", "Turn automatic spawning OFF in a group; /spawn keeps working (PM supported)"),
             ("/clearspawn", "Clear a stuck active spawn (group only)")])),
        ("broadcast", "📣 Broadcast", "📣 Broadcast"),                       # opens the Broadcast / DM menu (bc:h)
        ("scouts", "🔭 Scout Mgmt", _help_page(
            "🔭 Scout Management (Owner & Executive)",
            "Add or remove Scouts, the staff who manage characters.",
            [("/addscout <user_id>", "Add a Scout"),
             ("/removescout <user_id>", "Remove a Scout"),
             ("/scouts", "View the Scout list (public: every user can run it)")])),
        ("botrules", "📜 Bot Rules", _help_page(
            "📜 Bot Rules (Owner & Executive)",
            "Only the Owner and Executives manage the bot rules; everyone can read them.",
            [("/setrules <text>", "Set the rules (private chat only; Markdown supported). "
                                  "Tip: reply to a message in PM with /setrules to use that message"),
             ("/resetrules", "Clear all rules (private chat only)"),
             ("/rules", "View the rules (everyone, groups and PM)"),
             ("/rules noformat", "Raw markdown text for copying")])),
    ],
    "scout": [
        ("addedit", "🎴 Add & Edit", _addedit_page("scout")),
        ("spawntools", "🛠 Spawn Tools", _help_page(
            "🛠 Spawn Tools (Owner, Executive & Scout)",
            "Fix spawns that got stuck.",
            [("/clearspawn", "Clear a stuck active spawn (group only)")])),
        ("notifs", "🔔 Notifications", _help_page(
            "🔔 Staff Notifications (Owner, Executive & Scout)",
            "Your personal staff PM notifications.",
            [("/notifications", "View your notification status"),
             ("/notificationon", "Turn YOUR notifications ON"),
             ("/notificationoff", "Turn YOUR notifications OFF"),
             ("/notificationhistory", "View YOUR notification history")])),
    ],
}


HELP_BUTTON_STYLE = os.getenv("HELP_BUTTON_STYLE", "success").strip().lower()   # "success" = green; "" = off


def _module_button(label, callback_data):
    """Green module button (Bot API 9.4 button styles). Falls back to a plain button on older PTB/clients."""
    if HELP_BUTTON_STYLE:
        for kwargs in ({"style": HELP_BUTTON_STYLE}, {"api_kwargs": {"style": HELP_BUTTON_STYLE}}):
            try:
                return InlineKeyboardButton(label, callback_data=callback_data, **kwargs)
            except TypeError:
                continue
    return InlineKeyboardButton(label, callback_data=callback_data)


# Add & Edit shows in all three role menus; the Owner and Executive pages also list the Evolution commands.
HELP_MODULES["owner"].append(("addedit", "🎴 Add & Edit", _addedit_page("owner")))
HELP_MODULES["executive"].append(("addedit", "🎴 Add & Edit", _addedit_page("executive")))

# 📏 Range (Owner + Executive only, each in its own role menu): per-anime code ranges. Opens two buttons:
# Range Commands (the command list) and Range Panel (the same actions as guided buttons, one tab).
RANGE_HELP_TEXT = (
    "📏 Range\n\n"
    "📌 Overview\n"
    "Give every anime its own block of 4-digit codes (Naruto 0001-0200, Bleach 0201-0400), see which codes are "
    "used or free, and find the next free code.\n\n"
    "Tap Range Commands for the command list, or Range Panel to do everything with buttons - no typing commands."
)
RANGE_COMMANDS_TEXT = (
    "📏 Range Commands\n\n"
    "1. /setrange - set or update an anime's code range\n"
    "2. /delrange - delete an anime's range\n"
    "3. /range - show all ranges, or /range <anime> for one anime\n"
    "4. /freecode - show used and free codes (all anime, or one)\n"
    "5. /nextcode - show the next free code (all anime, or one)\n"
    "6. /fillranges - move every character into the range of its anime\n"
    "7. /undocodes - undo the last /fillranges or range shift"
)
HELP_MODULES["owner"].append(("range", "📏 Range", RANGE_HELP_TEXT))
HELP_MODULES["executive"].append(("range", "📏 Range", RANGE_HELP_TEXT))
HELP_MODULES["executive"].append(badge_banner.help_module())      # 🏅 Badges (copied into the Owner menu by the loop below)
HELP_MODULES["owner"].append(rewards.help_module())              # 🪔 Festival (Owner only)

NOT_YOURS_TEXT = "⚠️ This isn't yours. Please run /help to open your own menu."
# Executive and Scout modules stay in their own menus AND are copied (same text) into the Owner menu.
_owner_keys = {k for k, _l, _t in HELP_MODULES["owner"]}
for _role in ("executive", "scout"):
    for _module in HELP_MODULES[_role]:
        if _module[0] not in _owner_keys:
            HELP_MODULES["owner"].append(_module)
            _owner_keys.add(_module[0])
HELP_MODULES["owner"].append(("customize", "🎨 Customize Bot", "🎨 Customize Bot"))    # Owner only (opens theme.py's hub)
HELP_MODULES["owner"].append(("autoapprove", "✅ Auto Approve", "✅ Auto Approve"))     # Owner only (opens the Auto Approve page)
INVITES_HELP_TEXT = (
    "🎁 Invites (Owner)\n\n"
    "📌 Overview\n"
    "Invite links, Mystery Boxes and friend tasks. Members share their invite link, new members who join "
    "through it count as invites, and invites unlock Mystery Boxes.\n\n"
    "Tap Boxes to manage the settings, or Commands to see the command list."
)
_INVITE_CMD_ORDER = ("invite", "openbox", "myinvites", "topinvites", "boxes")


def invites_commands_text():
    """Every invite / Mystery Box command the bot has (read from rewards.py, so a new one shows up here by itself)."""
    desc = getattr(rewards, "COMMAND_DESCRIPTIONS", {}) or {}
    owner_cmds = set(getattr(rewards, "OWNER_COMMANDS", ()) or ())
    related = [n for n in desc if "invite" in n or "box" in n]
    names = [n for n in _INVITE_CMD_ORDER if n in related] + sorted(n for n in related if n not in _INVITE_CMD_ORDER)
    lines, number = ["📋 Invite Commands", "", "⌨️ Commands & usage"], 0
    for title, group in (("👥 Everyone", [n for n in names if n not in owner_cmds]), ("👑 Owner", [n for n in names if n in owner_cmds])):
        if not group:
            continue
        lines += ["", title]
        for n in group:
            number += 1
            lines.append(f"{number}. /{n} - {str(desc[n]).removeprefix('Owner: ')}")
    return "\n".join(lines)
HELP_MODULES["owner"].append(("invites", "🎁 Invites", INVITES_HELP_TEXT))                  # Owner only: page with 📦 Boxes (opens the manager) and 📋 Commands
HELP_MODULES["owner"].append(security.help_module())                                        # 🛡 Security (Owner only), right after Invites
HELP_STALE_TEXT = "⚠️ This menu is outdated. Please run /help to open your own menu."
HELP_PM_START_TEXT = ("📩 I couldn't message you privately. Open a private chat with me, press Start, "
                      "then run /help again.")
# Callback data format (<= 64 bytes): help:<menu_owner_id>:<action>[:<module>]
#   action = open | back | owner | executive | scout        (menu_owner_id = the user who ran /help or /start)


def _help_module_visible(key, user_id):
    """Spawn Tools is for Scouts only (Owner/Executive use /clearspawn from Group Control);
    Scout Mgmt is hidden from the Owner (who has the commands in Staff Roles)."""
    try:
        uid = int(user_id)
    except (TypeError, ValueError):
        return True
    if key == "spawntools" and (is_owner(uid) or is_executive(uid)):
        return False
    if key == "scouts" and is_owner(uid):
        return False
    if key in ("customize", "autoapprove", "festival", "invites", "security") and not is_owner(uid):
        return False
    if key == "range" and not (is_owner(uid) or is_executive(uid)):
        return False
    return True


def help_grid_keyboard(role, owner_id):
    """LAYER 2: module buttons in a strict 3-column grid + « Back to Layer 1 (main help)."""
    def _target(key):
        if key == "customize":
            return f"theme:{owner_id}:hub:open"
        if key == "autoapprove":
            return f"aa:{owner_id}:hub"
        if key == "festival":
            return f"fs:hub:{owner_id}"          # 🪔 Festival Manager (rewards.py)
        if key == "broadcast":
            return "bc:h"
        return f"help:{owner_id}:{role}:{key}"
    buttons = [_module_button(label, _target(key))
               for key, label, _text in HELP_MODULES[role] if _help_module_visible(key, owner_id)]
    rows = [buttons[i:i + 3] for i in range(0, len(buttons), 3)]
    rows.append([InlineKeyboardButton("« Back", callback_data=f"help:{owner_id}:back")])
    return InlineKeyboardMarkup(rows)


def help_grid_text(role):
    return f"{HELP_ROLE_TITLES[role]}\n\nChoose a module to see its overview and command syntax."


def help_detail(role, key, owner_id):
    """LAYER 3: (text, keyboard) for one module, or None for an unknown key. « Back returns to Layer 2."""
    if key == "invitecmds" and _help_module_visible("invites", owner_id):          # 📋 Commands page of 🎁 Invites
        return invites_commands_text(), InlineKeyboardMarkup(
            [[InlineKeyboardButton("« Back", callback_data=f"help:{owner_id}:{role}:invites")]])
    if key == "rangecmds" and role in ("owner", "executive") and _help_module_visible("range", owner_id):
        return RANGE_COMMANDS_TEXT, InlineKeyboardMarkup(
            [[InlineKeyboardButton("« Back", callback_data=f"help:{owner_id}:{role}:range")]])
    for k, _label, text in HELP_MODULES[role]:
        if k == key and _help_module_visible(k, owner_id):
            if k == "range" and role in ("owner", "executive"):
                return text, InlineKeyboardMarkup([
                    [_module_button("Range Commands", f"help:{owner_id}:{role}:rangecmds"),     # the only 2-button row
                     _module_button("Range Panel", f"rg:{owner_id}:p:{role[0]}")],
                    [InlineKeyboardButton("« Back", callback_data=f"help:{owner_id}:{role}")]])
            if k == "invites":
                return text, InlineKeyboardMarkup([
                    [_module_button("📦 Boxes", "rf:o:hub"),               # the Invite & Mystery Box manager (Owner check inside)
                     _module_button("📋 Commands", f"help:{owner_id}:{role}:invitecmds")],
                    [InlineKeyboardButton("« Back", callback_data=f"help:{owner_id}:{role}")]])
            if k == "addedit" and role in ("owner", "executive"):
                return text, InlineKeyboardMarkup([
                    [_module_button("💰 Change Worth", f"cw:{owner_id}:{role}:hub")],
                    [InlineKeyboardButton("« Back", callback_data=f"help:{owner_id}:{role}")]])
            return text, InlineKeyboardMarkup(
                [[InlineKeyboardButton("« Back", callback_data=f"help:{owner_id}:{role}")]])
    return None


async def help_role_allowed(role, user_id):
    """Verified role for the panel: owner -> Owner; executive -> Owner/Executive; scout -> Owner/Executive/Scout."""
    if is_owner(user_id):
        return True
    if role == "owner":
        return False
    if is_executive(user_id):
        return True
    if role == "scout":
        return bool(await asyncio.to_thread(is_scout, user_id))
    return False


def staff_help_keyboard(user_id):
    """LAYER 1 buttons. Restricted role buttons exist ONLY for users who really hold that role
    (normal users get no keyboard at all). Every button is bound to `user_id` (menu ownership)."""
    rows = []
    if is_owner(user_id):
        rows.append([_module_button("👑 Owner Commands", f"help:{user_id}:owner")])
        rows.append([_module_button("⚡ Executive Commands", f"help:{user_id}:executive")])
        rows.append([_module_button("🔭 Scout Commands", f"help:{user_id}:scout")])
    elif is_executive(user_id):
        rows.append([_module_button("⚡ Executive Commands", f"help:{user_id}:executive")])
        rows.append([_module_button("🔭 Scout Commands", f"help:{user_id}:scout")])
    elif is_scout(user_id):
        rows.append([_module_button("🔭 Scout Commands", f"help:{user_id}:scout")])
    rows.append(badge_banner.help_button_row(user_id))      # 🏅 Badges & Banners: every member gets this button
    return InlineKeyboardMarkup(rows)

def start_help_keyboard(user_id):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📖 Help", callback_data=f"help:{user_id}:open")]
    ])

def rarity_text(rarity):
    if not rarity:
        return "— Not set"
    return f"{SYMBOL.get(rarity, '⭐')} {rarity}"

def timestamp():
    """Naive IST timestamp (the format already stored in the database), independent of the host timezone."""
    return datetime.now(timezone(timedelta(hours=5, minutes=30))).replace(tzinfo=None).isoformat(timespec="seconds")

def log_time_text():
    """Log-channel timestamp: time first (12-hour, AM/PM), then date, e.g. '02:37:34 PM 04-10-2026 IST'."""
    return datetime.now(timezone(timedelta(hours=5, minutes=30))).strftime("%I:%M:%S %p %d-%m-%Y") + " IST"

def india_timestamp():
    ist = timezone(timedelta(hours=5, minutes=30))
    return datetime.now(timezone.utc).astimezone(ist).isoformat(timespec="seconds")

def india_today_key():
    ist = timezone(timedelta(hours=5, minutes=30))
    return datetime.now(timezone.utc).astimezone(ist).date().isoformat()

# User IDs (after "ID: ") and group IDs ("(-100…)") become tap-to-copy in plain-text messages.
_COPY_ID_RE = re.compile(r"(?<=ID: )-?\d{5,}|(?<=\()-100\d{5,}(?=\))")

def copyable_ids(text):
    """'code' entities for the IDs in `text`, to pass as entities=/caption_entities= (no parse_mode needed)."""
    return [MessageEntity(MessageEntity.CODE, len(text[:m.start()].encode("utf-16-le")) // 2,
                          len(m.group().encode("utf-16-le")) // 2) for m in _COPY_ID_RE.finditer(text)]

def code_ids_html(escaped_text):
    """The same for HTML messages: wrap each user ID in <code>."""
    return re.sub(r"(?<=ID: )-?\d{5,}", lambda m: f"<code>{m.group()}</code>", escaped_text)

def display_user(user):
    username = f"@{user.username}" if user.username else "No username"
    first = (user.first_name or "").strip()
    last = (user.last_name or "").strip()
    name = " ".join(part for part in (first, last) if part) or "Unknown"
    return f"{name} | ID: {user.id} | {username}"

def berry_display_name(user):
    first = (user.first_name or "").strip()
    last = (user.last_name or "").strip()
    return " ".join(part for part in (first, last) if part) or "Unknown"

GROUP_PERSONAL_CD_COLL = "group_personal_cooldown_v1"      # {_id: chat_id, minutes} - Owner-set /spawn cooldown of one group
DEFAULT_GROUP_PERSONAL_COOLDOWNS = {-1003379716050: 45}    # main group: members and Scouts wait 45 min. Saved once at the first
                                                            # start; after that only /spawncooldown changes it (also "reset").
_GCD = {"ts": 0.0, "map": {}}


def _load_group_cooldowns_sync():
    coll = _mc(GROUP_PERSONAL_CD_COLL)
    if coll.find_one({"_id": "_seeded"}) is None:
        for gid, minutes in DEFAULT_GROUP_PERSONAL_COOLDOWNS.items():
            coll.update_one({"_id": int(gid)}, {"$setOnInsert": {"minutes": int(minutes)}}, upsert=True)
        coll.update_one({"_id": "_seeded"}, {"$set": {"v": 1}}, upsert=True)
    return {int(d["_id"]): int(d["minutes"]) for d in coll.find({"minutes": {"$gt": 0}}) if isinstance(d["_id"], int)}


def group_personal_cooldown_minutes(chat_id):
    """Minutes set for this group with /spawncooldown, or None (= the normal 1 hour). Cached for 60 s."""
    now = time.monotonic()
    if now - _GCD["ts"] > 60:
        try:
            _GCD["map"] = _load_group_cooldowns_sync()
            _GCD["ts"] = now
        except Exception as e:
            print("Group cooldown load error:", e)
            _GCD["ts"] = now - 50                       # retry in 10 s, keep what is known
    try:
        return _GCD["map"].get(int(chat_id))
    except Exception:
        return None


def personal_spawn_cooldown(user_id, chat_id=None):
    """/spawn cooldown in seconds. Owner and Executive: 30 minutes everywhere. Scouts and general members: 1 hour, or the
    minutes the Owner set for THIS group with /spawncooldown (main group: 45)."""
    try:
        if is_owner(user_id) or is_executive(user_id):
            return STAFF_SPAWN_COOLDOWN
    except Exception:
        pass
    if chat_id is not None:
        minutes = group_personal_cooldown_minutes(chat_id)
        if minutes:
            return int(minutes) * 60
    return PERSONAL_SPAWN_COOLDOWN


def get_active_event():
    d = _mc("events_v2").find_one({"active": 1}, sort=[("created_at", -1), ("_id", -1)])
    if not d:
        return None
    row = (d["_id"], d.get("name"), d.get("description"), d.get("reward_type"),
           d.get("reward_value"), d.get("end_at"), d.get("created_at"))
    try:
        if datetime.fromisoformat(row[5]) <= datetime.now():
            _mc("events_v2").update_one({"_id": row[0]}, {"$set": {"active": 0}})
            return None
    except (ValueError, TypeError):
        pass
    return row

_EVENT_CACHE = {"ts": 0.0, "val": None}
_EVENT_CACHE_TTL = 5.0

async def _active_event_cached():
    """(row, trigger_text) of the active event, cached for a few seconds (None row = no event)."""
    c = _EVENT_CACHE
    if c["val"] is not None and time.monotonic() - c["ts"] < _EVENT_CACHE_TTL:
        return c["val"]
    def _load():
        row = get_active_event()
        if not row:
            return (None, None)
        ev = _mc("events_v2").find_one({"_id": row[0]})
        return (row, (ev or {}).get("trigger_text"))
    val = await asyncio.to_thread(_load)
    c["val"], c["ts"] = val, time.monotonic()
    return val

def format_reward(reward_type, reward_value):
    if reward_type == "coins":
        return f"🪙 {reward_value} Berrys"
    if reward_type == "stones":
        return f"💎 {reward_value} Special Stone" + ("" if str(reward_value) == "1" else "s")
    if reward_type == "character":
        character = get_character_by_code(str(reward_value))
        if character:
            return f"🎭 {character[1]} [{character[0]}]"
        return f"🎭 Character code {reward_value}"
    return str(reward_value)

def event_rewards(ev):
    """{'berrys': n, 'stones': n, 'card': code} of an event; old single-reward events are converted."""
    ev = ev or {}
    if ev.get("rewards"):
        return ev["rewards"]
    k = {"coins": "berrys", "stones": "stones", "character": "card"}.get(ev.get("reward_type"))
    return {k: ev["reward_value"]} if k else {}

MAX_REWARD_CHARACTERS = 20

def _reward_cards(v):
    """Character reward as a list of codes (old events/codes stored a single code)."""
    if v is None or v == "":
        return []
    return list(v) if isinstance(v, (list, tuple)) else [v]

def format_event_rewards(rw):
    parts = [format_reward("character", c) for c in _reward_cards(rw.get("card"))]
    if rw.get("berrys"):
        parts.append(format_reward("coins", rw["berrys"]))
    if rw.get("stones"):
        parts.append(format_reward("stones", rw["stones"]))
    return " + ".join(parts)

def redeem_rewards_of(doc):
    """{'coins': n, 'stones': n, 'character': [codes]} of a redeem code; old single-reward codes are converted."""
    doc = doc or {}
    if doc.get("rewards"):
        return doc["rewards"]
    t, v = doc.get("reward_type"), doc.get("reward_value")
    if t == "character":
        return {"character": [v]}
    if t in ("coins", "stones"):
        return {t: v}
    return {}

def format_redeem_rewards(rw):
    parts = [format_reward("character", c) for c in _reward_cards(rw.get("character"))]
    if rw.get("coins"):
        parts.append(format_reward("coins", rw["coins"]))
    if rw.get("stones"):
        parts.append(format_reward("stones", rw["stones"]))
    return " + ".join(parts) or "—"

def parse_character_list(text, limit=MAX_REWARD_CHARACTERS):
    """One or more characters (code or name) separated by commas / new lines -> (codes, error)."""
    parts = [p.strip() for p in re.split(r"[,;\n]+", text or "") if p.strip()]
    if not parts:
        return None, "❌ Send at least one character."
    codes, bad = [], []
    for p in parts:
        ch = get_character(p)
        if not ch:
            bad.append(p)
            continue
        c = int(ch[0])
        if c not in codes:
            codes.append(c)
    if bad:
        return None, ("❌ Character not found: " + ", ".join(bad) +
                      ". Use a 4-digit code, first name, last name, or full name. Send the whole list again.")
    if len(codes) > limit:
        return None, f"❌ Maximum {limit} characters. Send a shorter list."
    return codes, None

def get_spawn_lock(app):
    lock = app.bot_data.get("spawn_lock")
    if lock is None:
        lock = asyncio.Lock()
        app.bot_data["spawn_lock"] = lock
    return lock

INDIA_TZ = timezone(timedelta(hours=5, minutes=30))

def get_today_key():
    now = datetime.now(INDIA_TZ)
    if now.hour < DAILY_RESET_HOUR:
        now -= timedelta(days=1)
    return now.strftime("%Y-%m-%d")

def get_high_rank_today_key():
    # High-rank limits and spacing reset at exactly 12:00 AM IST.
    return datetime.now(INDIA_TZ).strftime("%Y-%m-%d")


def _successful_global_quota_counts(cursor=None, today_key=None):
    today_key = today_key or get_high_rank_today_key()
    counts = {"Legendary": 0, "Mythical": 0, "Celestial": 0}
    for rarity, spawned_at in mongo_db.sh_rarity_rows(_day_floor(today_key), ("Legendary", "Mythical", "Celestial")):
        try:
            dt = datetime.fromisoformat(str(spawned_at))
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=INDIA_TZ)
            dt = dt.astimezone(INDIA_TZ)
            if dt.strftime("%Y-%m-%d") == today_key:
                counts[str(rarity)] += 1
        except (TypeError, ValueError):
            continue
    return counts

def _sync_global_quota_consumed(cursor, today_key):
    gl = _mc("spawn_limits_global_v1")
    zero = {"legendary_count": 0, "mythical_count": 0, "celestial_count": 0,
            "legendary_pending": 0, "mythical_pending": 0, "celestial_pending": 0}
    doc = gl.find_one({"_id": 1})
    if not doc:
        try:
            gl.insert_one(dict(zero, _id=1, id=1, day_key=today_key))
        except mongo_db.DuplicateKeyError:
            pass
    elif doc.get("day_key") != today_key:
        gl.update_one({"_id": 1}, {"$set": dict(zero, day_key=today_key)})
    counts = _successful_global_quota_counts(None, today_key)
    gl.update_one({"_id": 1, "day_key": today_key},
                  {"$set": {"legendary_count": counts["Legendary"], "mythical_count": counts["Mythical"],
                            "celestial_count": counts["Celestial"]}})
    return counts

def reserve_rarity(chat_id, rarity):
    limits = {"Legendary": LEGENDARY_DAILY_LIMIT, "Mythical": MYTHICAL_DAILY_LIMIT, "Celestial": CELESTIAL_DAILY_LIMIT}
    if rarity in ("Common", "Rare", "Epic"):
        return True, ""
    if rarity not in limits:
        return False, "❌ Invalid rarity."
    today_key = get_high_rank_today_key()
    count_col = {"Legendary": "legendary_count", "Mythical": "mythical_count", "Celestial": "celestial_count"}[rarity]
    pending_col = {"Legendary": "legendary_pending", "Mythical": "mythical_pending", "Celestial": "celestial_pending"}[rarity]
    _sync_global_quota_consumed(None, today_key)
    # atomic: only increments pending while (count + pending) is still under the daily limit
    res = _mc("spawn_limits_global_v1").update_one(
        {"_id": 1, "day_key": today_key,
         "$expr": {"$lt": [{"$add": ["$" + count_col, "$" + pending_col]}, limits[rarity]]}},
        {"$inc": {pending_col: 1}},
    )
    if res.modified_count != 1:
        return False, f"Today's global {rarity} character limit ({limits[rarity]}) has been reached."
    return True, ""

def finalize_rarity_success(rarity):
    if rarity in ("Common", "Rare", "Epic"):
        return True
    limits = {"Legendary": LEGENDARY_DAILY_LIMIT, "Mythical": MYTHICAL_DAILY_LIMIT, "Celestial": CELESTIAL_DAILY_LIMIT}
    if rarity not in limits:
        return False
    today_key = get_high_rank_today_key()
    pending_col = {"Legendary": "legendary_pending", "Mythical": "mythical_pending", "Celestial": "celestial_pending"}[rarity]
    gl = _mc("spawn_limits_global_v1")
    _sync_global_quota_consumed(None, today_key)
    res = gl.update_one({"_id": 1, "day_key": today_key, pending_col: {"$gt": 0}}, {"$inc": {pending_col: -1}})
    if res.modified_count != 1:
        return False
    counts = _successful_global_quota_counts(None, today_key)
    if counts[rarity] > limits[rarity]:
        gl.update_one({"_id": 1}, {"$inc": {pending_col: 1}})  # undo the decrement
        return False
    gl.update_one({"_id": 1, "day_key": today_key},
                  {"$set": {"legendary_count": counts["Legendary"], "mythical_count": counts["Mythical"],
                            "celestial_count": counts["Celestial"]}})
    return True

def rollback_rarity_reservation(chat_id, rarity):
    if rarity in ("Common", "Rare", "Epic"):
        return
    pending_col = {"Legendary": "legendary_pending", "Mythical": "mythical_pending", "Celestial": "celestial_pending"}.get(rarity)
    if not pending_col:
        return
    _sync_global_quota_consumed(None, get_high_rank_today_key())
    _mc("spawn_limits_global_v1").update_one({"_id": 1, pending_col: {"$gt": 0}}, {"$inc": {pending_col: -1}})

def _get_high_rarity_spacing_targets():
    today_key = get_high_rank_today_key()
    spacing = _mc("high_rarity_spacing_v1")
    doc = spacing.find_one({"_id": 1})
    targets = (HIGH_RARITY_GAP_MIN, CELESTIAL_GAP_TARGET)
    if (not doc or doc.get("day_key") != today_key
            or int(doc.get("high_target") or 0) != targets[0]
            or int(doc.get("celestial_target") or 0) != targets[1]):
        spacing.replace_one(
            {"_id": 1},
            {"id": 1, "high_target": targets[0], "celestial_target": targets[1], "day_key": today_key},
            upsert=True,
        )
    return targets

def _set_high_rarity_spacing_target(rarity):
    column = "high_target" if rarity in ("Legendary", "Mythical") else "celestial_target"
    if rarity not in ("Legendary", "Mythical", "Celestial"):
        return
    target = HIGH_RARITY_GAP_MIN if rarity in ("Legendary", "Mythical") else CELESTIAL_GAP_TARGET
    _mc("high_rarity_spacing_v1").update_one({"_id": 1}, {"$set": {column: target}})

def _get_random_spawn_high_rarity_gaps(app=None):
    high_gap = None
    celestial_gap = None
    try:
        # The spacing restriction resets at 12:00 AM IST every day.
        today_start = datetime.now(INDIA_TZ).replace(hour=0, minute=0, second=0, microsecond=0).isoformat()
        high_row = mongo_db.sh_last_spawn(("Legendary", "Mythical", "Celestial"), today_start)
        celestial_row = mongo_db.sh_last_spawn(("Celestial",), today_start)

        def count_spawns_after(row):
            if not row:
                return None
            history_id, spawned_at = row
            try:
                datetime.fromisoformat(str(spawned_at))
            except (TypeError, ValueError):
                return 0
            return mongo_db.sh_count_random_after(today_start, str(spawned_at), history_id)

        # If no high-rank/celestial spawn has happened today, the gap starts from today's
        # total random/manual spawns; after one, its gap resets to 0 and counts later spawns.
        today_spawn_total = mongo_db.sh_count_random_since(today_start)
        high_gap = count_spawns_after(high_row) if high_row else today_spawn_total
        celestial_gap = count_spawns_after(celestial_row) if celestial_row else today_spawn_total
    except Exception as e:
        print("High-rarity spacing lookup error:", e)
    return high_gap, celestial_gap

def reserve_high_rarity_spacing(app, rarity):
    if rarity in ("Legendary", "Mythical", "Celestial"):
        app.bot_data["high_rarity_spacing_reservation"] = app.bot_data.get("high_rarity_spacing_reservation", 0) + 1

def release_high_rarity_spacing(app, rarity):
    if rarity in ("Legendary", "Mythical", "Celestial"):
        key = "high_rarity_spacing_reservation"
        count = app.bot_data.get(key, 0) - 1
        if count > 0:
            app.bot_data[key] = count
        else:
            app.bot_data.pop(key, None)

def get_recent_global_spawn_codes(exclude_chat_id=None, minutes=None):
    minutes = int(minutes or (SPAWN_LIFETIME / 60))
    cutoff = (datetime.now(INDIA_TZ) - timedelta(minutes=minutes)).isoformat()
    return mongo_db.sh_recent_codes(cutoff)

# ---------------------------------------------------------------------------------------------------------------
# Characters without an uploaded photo cannot spawn.
#   * The first time such a character is picked, that spawn attempt fails with SPAWN_PHOTO_MISSING_TEXT (manual
#     /spawn only) and the character is restricted.
#   * A restricted character is silently skipped by every picker (manual and automatic), so spawning simply
#     continues with other characters. Only that character is affected.
#   * As soon as its photo exists (/addphoto, /editcharacter, ...) the restriction disappears by itself.
# The restricted codes are kept in MongoDB (collection spawn_photo_restricted_v1) so a restart does not repeat the notice.
# ---------------------------------------------------------------------------------------------------------------
import threading as _threading
SPAWN_PHOTO_MISSING_TEXT = ("Character spawn failed because the character photo has not been uploaded. "
                            "Please try again.")
_PHOTO_RESTRICTED = {"codes": None}
_PHOTO_RESTRICTED_LOCK = _threading.RLock()      # re-entrant: restrict/clear call the lazy loader while holding it


def _photo_restricted_codes():
    codes = _PHOTO_RESTRICTED["codes"]
    if codes is not None:
        return codes
    with _PHOTO_RESTRICTED_LOCK:
        if _PHOTO_RESTRICTED["codes"] is None:
            loaded = set()
            try:
                doc = _mc("spawn_photo_restricted_v1").find_one({"_id": 1}) or {}
                loaded = {str(c) for c in (doc.get("codes") or [])}
            except Exception as e:
                print("Photo restriction load error:", e)
            _PHOTO_RESTRICTED["codes"] = loaded
        return _PHOTO_RESTRICTED["codes"]


def _persist_photo_restricted():
    try:
        _mc("spawn_photo_restricted_v1").update_one(
            {"_id": 1}, {"$set": {"codes": sorted(_photo_restricted_codes())}}, upsert=True)
    except Exception as e:
        print("Photo restriction save error:", e)


def spawn_photo_ok(row):
    """May this character row be picked for a spawn? True when it has a photo, or has not been restricted yet."""
    code = str(row[0])
    codes = _photo_restricted_codes()
    if row[5]:
        if codes and code in codes:                      # photo uploaded since: lift the restriction automatically
            with _PHOTO_RESTRICTED_LOCK:
                codes.discard(code)
            _persist_photo_restricted()
        return True
    return code not in codes


def restrict_character_photo(code):
    """Restrict a photo-less character. Returns True only the FIRST time (that is when the notice is shown)."""
    code = str(code)
    with _PHOTO_RESTRICTED_LOCK:
        codes = _photo_restricted_codes()
        if code in codes:
            return False
        codes.add(code)
    _persist_photo_restricted()
    return True


def clear_photo_restriction(code):
    code = str(code)
    with _PHOTO_RESTRICTED_LOCK:
        codes = _photo_restricted_codes()
        if code not in codes:
            return False
        codes.discard(code)
    _persist_photo_restricted()
    return True


# ---------------------------------------------------------------------------------------------------------------
# Balanced spawn mix + per-group cooldown
#   * Old/new mix: the available characters are split by code into an OLDER half and a NEWER half. Every spawn
#     picks one half at random (50/50), then a random character from it -> a fair mix, never mostly old or new.
#   * Cooldown: after a Common/Rare/Epic character spawns in a group it cannot spawn again in THAT group for a
#     random 36-48 hours (1.5-2 days). When the time is over it is simply back in the normal random pool, with no
#     priority. If every character of a rarity is cooling down in a group, the one that finishes soonest is used,
#     so spawning never stops. Legendary / Mythical / Celestial are exempt: their rules are unchanged.
#     Stored in MongoDB (group_spawn_cooldown_v1), so restarts keep it.
# ---------------------------------------------------------------------------------------------------------------
_GROUP_COOLDOWN_COLL = "group_spawn_cooldown_v1"
_HIGH_RARITIES = ("Legendary", "Mythical", "Celestial")
_COOLDOWN_MIN_HOURS = 36
_COOLDOWN_MAX_HOURS = 48


def _group_cooldowns(chat_id):
    """{code: cooldown_end_epoch} for this group; finished cooldowns are cleaned up."""
    if chat_id is None:
        return {}
    try:
        import time as _t
        now = _t.time()
        doc = _mc(_GROUP_COOLDOWN_COLL).find_one({"_id": int(chat_id)}) or {}
        until = doc.get("until") or {}
        active = {str(c): float(u) for c, u in until.items() if float(u) > now}
        expired = [c for c, u in until.items() if float(u) <= now]
        if expired:
            _mc(_GROUP_COOLDOWN_COLL).update_one({"_id": int(chat_id)}, {"$unset": {f"until.{c}": "" for c in expired}})
        return active
    except Exception as e:
        print("Group spawn cooldown load error:", e)
        return {}


def _group_cooldown_add(chat_id, character):
    """Start the 1.5-2 day cooldown for a spawned Common/Rare/Epic character in this group."""
    try:
        if str(character[3]) in _HIGH_RARITIES:
            return
        import time as _t
        end = _t.time() + random.uniform(_COOLDOWN_MIN_HOURS, _COOLDOWN_MAX_HOURS) * 3600
        _mc(_GROUP_COOLDOWN_COLL).update_one({"_id": int(chat_id)}, {"$set": {f"until.{character[0]}": end}}, upsert=True)
    except Exception as e:
        print("Group spawn cooldown save error:", e)


def _apply_group_cooldown(rows, cooldowns):
    """Rows not cooling down; if all are, only the one whose cooldown ends soonest."""
    free = [r for r in rows if str(r[0]) not in cooldowns]
    if free or not rows:
        return free
    return [min(rows, key=lambda r: cooldowns.get(str(r[0]), 0))]


def _pick_old_new_mix(rows):
    """Random old/new mix: pick the older or the newer half with equal chance, then a random character from it."""
    if len(rows) < 2:
        return random.choice(rows)
    ordered = sorted(rows, key=lambda r: int(r[0]) if str(r[0]).isdigit() else 0)
    mid = len(ordered) // 2
    return random.choice(random.choice([ordered[:mid], ordered[mid:]]))


def _choose_unlimited_fallback_character(excluded_codes=None, chat_id=None, allow_recent=False, require_photo=False):
    """Emergency picker: always prefer an unused Common/Rare/Epic character."""
    excluded = {str(code) for code in (excluded_codes or set())}
    if not allow_recent:
        try:
            excluded.update(get_recent_global_spawn_codes(chat_id))
        except Exception as e:
            print("Fallback recent-spawn lookup error:", e)
    rows = [row for rarity in ("Common", "Rare", "Epic")
            for row in get_characters_by_rarity(rarity)
            if str(row[0]) not in excluded and (not require_photo or spawn_photo_ok(row))]
    if not rows and not allow_recent:
        return _choose_unlimited_fallback_character(excluded_codes, chat_id, True, require_photo)
    if not rows:
        return None
    try:
        rows = _apply_group_cooldown(rows, _group_cooldowns(chat_id)) or rows
    except Exception as e:
        print("Fallback group-cooldown error:", e)
    return _pick_old_new_mix(rows)

def choose_character(chat_id, excluded_codes=None, app=None, respect_daily_limit=True, require_photo=False):
    excluded = {str(code) for code in (excluded_codes or set())}
    if respect_daily_limit:
        excluded.update(get_daily_random_spawn_limited_codes(chat_id, app))
    excluded.update(get_recent_global_spawn_codes(chat_id))
    cooldowns = _group_cooldowns(chat_id)

    def available_rows(rarity):
        rows = [row for row in get_characters_by_rarity(rarity) if str(row[0]) not in excluded and (not require_photo or spawn_photo_ok(row))]
        if rarity in _HIGH_RARITIES:
            return rows
        return _apply_group_cooldown(rows, cooldowns)

    available = [(r, w) for r, w in CHANCES if available_rows(r)]

    if available:
        high_gap, celestial_gap = _get_random_spawn_high_rarity_gaps(app)
        high_target, celestial_target = _get_high_rarity_spacing_targets()
        pending_high = app.bot_data.get("high_rarity_spacing_reservation", 0) if app else 0
        if pending_high or (high_gap is not None and high_gap < high_target):
            available = [(r, w) for r, w in available if r in ("Common", "Rare", "Epic")]
        elif celestial_gap is not None and celestial_gap < celestial_target:
            available = [(r, w) for r, w in available if r != "Celestial"]

        if available:
            rarity = random.choices([r for r, _ in available], weights=[w for _, w in available], k=1)[0]
            rows = available_rows(rarity)
            if rows:
                return _pick_old_new_mix(rows)

    return _choose_unlimited_fallback_character(excluded, chat_id, require_photo=require_photo)

async def cancel_spawn_expiry_task(spawn):
    if not isinstance(spawn, dict):
        return
    task = spawn.get("expiry_task")
    if task is None or task.done():
        return
    if task is asyncio.current_task():
        return
    task.cancel()

async def expire_spawn_after_delay(app, chat_id, expected_code):
    try:
        await asyncio.sleep(SPAWN_LIFETIME)
        now_dt = datetime.now()
        lock = get_spawn_lock(app)
        async with lock:
            active = app.bot_data.setdefault("active_spawns", {})
            spawn = active.get(chat_id)
            if not spawn or str(spawn.get("code")) != str(expected_code):
                return
            removed = expire_active_spawn_locked(app, chat_id, now_dt)
        if removed:
            await send_expiry_notice(app, chat_id, removed)
    except asyncio.CancelledError:
        raise
    except Exception as e:
        print(f"Per-spawn expiry timer error for {chat_id}: {e}")

async def send_spawn(chat_id, context, character):
    code, name, anime, rarity, worth, photo = character
    app = getattr(context, "application", context)
    bot = getattr(context, "bot", None) or app.bot
    active = app.bot_data.setdefault("active_spawns", {})
    active.setdefault(chat_id, {
        "code": code, "name": name, "anime": anime, "rarity": rarity,
        "worth": worth, "photo": photo,
        "expires_at": datetime.now() + timedelta(seconds=SPAWN_LIFETIME),
    })
    caption = (f"A {rarity} {SYMBOL.get(rarity, '⭐')} character has appeared...\n\n"
               "Use /add to catch them!")
    text_fallback = (f"A {html_escape(str(rarity))} {SYMBOL.get(rarity, '⭐')} character has appeared...\n\n"
                     "Use /add to catch them!")
    sent_message = None
    last_error = None
    for attempt in range(5):
        if photo:
            try:
                sent_message = await bot.send_photo(chat_id=chat_id, photo=photo, caption=caption)
            except Exception as e:
                last_error = e
                print(f"Spawn photo send failed for {chat_id} (attempt {attempt + 1}/5):", e)
        if sent_message is None:
            try:
                sent_message = await bot.send_message(chat_id=chat_id, text=text_fallback, parse_mode="HTML")
            except Exception as e:
                last_error = e
                print(f"Spawn text send failed for {chat_id} (attempt {attempt + 1}/5):", e)
        if sent_message is not None:
            break
        await asyncio.sleep(min(2 + attempt, 5))
    if sent_message is None:
        failed_spawn = active.pop(chat_id, None)
        if failed_spawn:
            await cancel_spawn_expiry_task(failed_spawn)
        raise RuntimeError(f"Spawn message could not be delivered: {last_error}")

    active_spawn = active.get(chat_id)
    if active_spawn is not None:
        active_spawn["message_id"] = sent_message.message_id
        active_spawn["expires_at"] = datetime.now() + timedelta(seconds=SPAWN_LIFETIME)
        old_task = active_spawn.get("expiry_task")
        if old_task is not None and not old_task.done():
            old_task.cancel()
        active_spawn["expiry_task"] = asyncio.create_task(
            expire_spawn_after_delay(app, chat_id, str(code)),
            name=f"spawn-expiry-{chat_id}-{code}",
        )
    app.bot_data.setdefault("chat_spawn_cooldowns", {})[chat_id] = (
        datetime.now() + timedelta(seconds=GROUP_SPAWN_COOLDOWN)
    )
    app.bot_data.setdefault("next_auto_spawn_at", {}).pop(chat_id, None)

async def spawn_reserved(chat_id, context, character, spawned_by="manual"):
    app = getattr(context, "application", context)
    if not await bot_is_group_admin(app.bot, app, chat_id):
        return False, BOT_ADMIN_SPAWN_TEXT
    lock = get_spawn_lock(app)

    random_spawn = spawned_by in ("auto_spawn", "manual_spawn")
    character_code = None
    forced_reuse = False
    history_id = None

    async with lock:
        active = app.bot_data.setdefault("active_spawns", {})
        if chat_id in active:
            return False, "❌ A character is already spawned in this chat."

        # Owner /callcharacter cannot exceed the daily high-rank limit (the gap is not checked; it resets after the call).
        if spawned_by == "owner_callchar" and character is not None and character[3] in ("Legendary", "Mythical", "Celestial"):
            _lims = {"Legendary": LEGENDARY_DAILY_LIMIT, "Mythical": MYTHICAL_DAILY_LIMIT, "Celestial": CELESTIAL_DAILY_LIMIT}
            _counts = await asyncio.to_thread(_successful_global_quota_counts, None, get_high_rank_today_key())
            if _counts.get(character[3], 0) >= _lims[character[3]]:
                return False, (f"❌ Today's global {character[3]} limit ({_lims[character[3]]}) has been reached.\n"
                               "Call character is not possible until the 12:00 AM IST reset.")

        # Evolution characters are obtained ONLY by evolving: never spawn one (checked by character type, not name/code).
        if character is not None and await asyncio.to_thread(mongo_db.is_evolution_character, character[0]):
            if not random_spawn:
                return False, "❌ Evolution characters cannot be spawned. They are only obtained by evolving."
            character = None   # random spawn: fall through and pick a normal character instead

        if random_spawn:
            excluded_for_random = (await asyncio.to_thread(get_daily_random_spawn_limited_codes, chat_id, app))
            # A photo-less character was handed in: restrict it. Manual /spawn fails this attempt (the caller sends
            # the one-time notice); automatic spawns silently continue with another character below.
            if character is not None and not character[5] and str(character[0]) not in excluded_for_random:
                newly_restricted = await asyncio.to_thread(restrict_character_photo, character[0])
                if spawned_by == "manual_spawn":
                    return False, (SPAWN_PHOTO_MISSING_TEXT if newly_restricted else "")
                excluded_for_random.add(str(character[0]))
                character = None
            # Both /spawn and auto-spawn use the same picker. This enforces
            # recent-character protection and the high-rarity spacing rule.
            if character is None or str(character[0]) in excluded_for_random or not character[5]:
                character = (await asyncio.to_thread(choose_character,
                    chat_id, excluded_codes=excluded_for_random, app=app, require_photo=True
                ))
            else:
                high_gap, celestial_gap = (await asyncio.to_thread(_get_random_spawn_high_rarity_gaps, app))
                high_target, celestial_target = (await asyncio.to_thread(_get_high_rarity_spacing_targets))
                pending_high = app.bot_data.get("high_rarity_spacing_reservation", 0)
                high_blocked = pending_high or (
                    high_gap is not None and high_gap < high_target
                )
                celestial_blocked = (
                    celestial_gap is not None and celestial_gap < celestial_target
                )
                recent_codes = (await asyncio.to_thread(get_recent_global_spawn_codes, chat_id))
                if (str(character[0]) in recent_codes or
                    (high_blocked and character[3] in ("Legendary", "Mythical", "Celestial")) or
                    (celestial_blocked and character[3] == "Celestial")):
                    character = (await asyncio.to_thread(choose_character,
                        chat_id,
                        excluded_codes=excluded_for_random | {str(character[0])},
                        app=app,
                        require_photo=True,
                    ))

            if character is None:
                character = (await asyncio.to_thread(_choose_unlimited_fallback_character, excluded_for_random, chat_id, require_photo=True))
            # The re-pick above may itself land on a photo-less character: restrict it and pick again.
            for _photo_guard in range(25):
                if character is None or character[5]:
                    break
                newly_restricted = await asyncio.to_thread(restrict_character_photo, character[0])
                if spawned_by == "manual_spawn":
                    return False, (SPAWN_PHOTO_MISSING_TEXT if newly_restricted else "")
                excluded_for_random.add(str(character[0]))
                character = (await asyncio.to_thread(choose_character,
                    chat_id, excluded_codes=excluded_for_random, app=app, require_photo=True))
                if character is None:
                    character = (await asyncio.to_thread(_choose_unlimited_fallback_character, excluded_for_random, chat_id, require_photo=True))
            if character is None:
                return False, "❌ No eligible character is available in the character list."

            character_code = str(character[0])

            rarity_reserved = False

            if not forced_reuse and not (await asyncio.to_thread(reserve_daily_character_spawn, chat_id, character_code)):
                excluded_for_random = (await asyncio.to_thread(get_daily_random_spawn_limited_codes, chat_id, app))
                excluded_for_random.add(character_code)
                replacement = (await asyncio.to_thread(choose_character,
                    chat_id, excluded_codes=excluded_for_random, app=app, require_photo=True
                ))
                if replacement is None:
                    replacement = (await asyncio.to_thread(_choose_unlimited_fallback_character, excluded_for_random, chat_id, require_photo=True))
                if replacement is None:
                    replacement = (await asyncio.to_thread(_choose_unlimited_fallback_character, chat_id=chat_id, require_photo=True))
                if replacement is None:
                    return False, "❌ No Common/Rare/Epic character is configured in the character list."
                character = replacement
                character_code = str(character[0])
                if not (await asyncio.to_thread(reserve_daily_character_spawn, chat_id, character_code)):
                    character = (await asyncio.to_thread(_choose_unlimited_fallback_character, chat_id=chat_id, require_photo=True))
                    if character is None:
                        return False, ""
                    character_code = str(character[0])
                    forced_reuse = True

            if not forced_reuse:
                rarity_ok, rarity_reason = (await asyncio.to_thread(reserve_rarity, chat_id, character[3]))
                if not rarity_ok:
                    excluded_for_random = (await asyncio.to_thread(get_daily_random_spawn_limited_codes, chat_id, app))
                    excluded_for_random.add(character_code)
                    replacement = (await asyncio.to_thread(choose_character, chat_id, excluded_codes=excluded_for_random, app=app, require_photo=True))
                    if replacement is None:
                        replacement = (await asyncio.to_thread(_choose_unlimited_fallback_character, excluded_for_random, chat_id, require_photo=True))
                    if replacement is None:
                        return False, rarity_reason
                    character = replacement
                    character_code = str(character[0])
                    if not (await asyncio.to_thread(reserve_daily_character_spawn, chat_id, character_code)):
                        return False, rarity_reason
                    rarity_ok, rarity_reason = (await asyncio.to_thread(reserve_rarity, chat_id, character[3]))
                    if not rarity_ok:
                        (await asyncio.to_thread(release_daily_character_spawn, chat_id, character_code))
                        return False, rarity_reason
                rarity_reserved = character[3] in ("Legendary", "Mythical", "Celestial")

            reserve_random_spawn(app, chat_id, character_code)
            reserve_high_rarity_spacing(app, character[3])

        active[chat_id] = {
            "code": character[0], "name": character[1], "anime": character[2],
            "rarity": character[3], "worth": character[4], "photo": character[5],
            "recruit_names": (await asyncio.to_thread(get_recruit_names, character[0])),
            "spawned_by": spawned_by,
            "forced_reuse": forced_reuse,
            "expires_at": datetime.now() + timedelta(seconds=SPAWN_LIFETIME),
        }
        history_id = (await asyncio.to_thread(record_spawn_history, chat_id, character, spawned_by))
        active[chat_id]["history_id"] = history_id

    try:
        await send_spawn(chat_id, context, character)
    except Exception:
        async with lock:
            removed_failed_spawn = app.bot_data.setdefault("active_spawns", {}).pop(chat_id, None)
            if removed_failed_spawn:
                await cancel_spawn_expiry_task(removed_failed_spawn)
            if history_id:
                try:
                    (await asyncio.to_thread(mongo_db.sh_delete_uncaught, history_id))
                except Exception as e:
                    print("Spawn history cleanup error:", e)
            if random_spawn:
                if not forced_reuse:
                    (await asyncio.to_thread(release_daily_character_spawn, chat_id, character_code))
                    if rarity_reserved:
                        (await asyncio.to_thread(rollback_rarity_reservation, chat_id, character[3]))
                release_random_spawn_reservation(app, chat_id, character_code)
                release_high_rarity_spacing(app, character[3])
        raise

    if random_spawn:
        if character[3] in ("Legendary", "Mythical", "Celestial") and rarity_reserved:
            (await asyncio.to_thread(finalize_rarity_success, character[3]))
        if character[3] in ("Legendary", "Mythical", "Celestial"):
            (await asyncio.to_thread(_set_high_rarity_spacing_target, character[3]))
        release_high_rarity_spacing(app, character[3])
        release_random_spawn_reservation(app, chat_id, character_code)
    elif spawned_by == "owner_callchar" and character[3] in ("Legendary", "Mythical", "Celestial"):
        # Owner-called high-rank spawns count in daily totals (via history) and reset the gap like a normal one.
        try:
            (await asyncio.to_thread(_set_high_rarity_spacing_target, character[3]))
        except Exception as e:
            print("Owner call spacing error:", e)
    return True, ""

async def safe_delete_message(bot, chat_id, message_id):
    if not message_id:
        return False
    try:
        await asyncio.wait_for(
            bot.delete_message(chat_id=chat_id, message_id=message_id),
            timeout=15,
        )
        return True
    except Exception as e:
        print(f"Safe message delete error for {chat_id}/{message_id}: {e}")
        return False

def add_display_name_header(message, text):
    text = str(text or "")
    if not text.strip():
        return text
    sender = getattr(message, "from_user", None)
    if sender is None:
        return text
    if text.lstrip().startswith("👤"):
        return text
    first = (getattr(sender, "first_name", None) or "").strip()
    last = (getattr(sender, "last_name", None) or "").strip()
    display_name = " ".join(part for part in (first, last) if part) or "Unknown"
    return f"👤 {html_escape(display_name)}\n\n{text}"

# (chat_id, message_id) of COMMAND messages -> monotonic time. command_outcome_hook reads and clears them.
#   _CMD_FAILED : the command answered with an error (or crashed)       -> never logged
#   _CMD_OK     : the handler called mark_success(update)               -> required for EXPLICIT_SUCCESS_COMMANDS
_CMD_FAILED = {}
_CMD_OK = {}
_FAIL_PREFIXES = ("❌", "⚠️", "⚠", "🚫", "⛔", "ℹ️", "ℹ", "🔴", "⏳", "usage:")
_CMD_STATE_TTL = 600.0


def _purge_cmd_state():
    now = time.monotonic()
    for d in (_CMD_FAILED, _CMD_OK):
        if len(d) > 50:
            for key in [k for k, t in d.items() if now - t > _CMD_STATE_TTL]:
                d.pop(key, None)
        if len(d) > 2000:                                   # hard cap under a flood
            for key in sorted(d, key=d.get)[:len(d) - 1000]:
                d.pop(key, None)


def _command_key(message):
    try:
        if message is None or not str(getattr(message, "text", "") or "").startswith("/"):
            return None
        return (message.chat_id, message.message_id)
    except Exception:
        return None


def _mark_command_failed(message):
    key = _command_key(message)
    if key is not None:
        _purge_cmd_state()
        _CMD_FAILED[key] = time.monotonic()


def mark_success(update):
    """Handlers call this when a command really did its job (used by the log pipeline)."""
    try:
        key = _command_key(update.effective_message)
        if key is not None:
            _purge_cmd_state()
            _CMD_OK[key] = time.monotonic()
    except Exception:
        pass


_SKIP_KB_CHATS = set()      # chats where the "⏭ Skip" reply keyboard is on screen right now

async def _drop_skip_keyboard(bot, chat_id):
    """A reply keyboard can only be removed by a message that carries ReplyKeyboardRemove (an inline-button message cannot):
    send a tiny one and delete it straight away."""
    _SKIP_KB_CHATS.discard(chat_id)
    try:
        gone = await bot.send_message(chat_id=chat_id, text="⌨️", reply_markup=ReplyKeyboardRemove())
        await gone.delete()
    except Exception as e:
        print("Skip keyboard cleanup failed:", e)

async def safe_reply_text(message, text, **kwargs):
    if message is None:
        return None
    text = str(text or "")
    if text.lstrip().lower().startswith(_FAIL_PREFIXES):
        _mark_command_failed(message)
    if text == UNAUTHORIZED_TEXT:
        _security_log_from_message(message)      # every unauthorized command attempt is logged centrally
    if not text.strip():
        print("Safe reply skipped: empty message text")
        return None

    # The Skip button only lives on the step that asks for it. The next normal reply in that chat clears it
    # (❌ validation messages keep it, because the same step is still waiting for an answer).
    markup = kwargs.get("reply_markup")
    if isinstance(markup, ReplyKeyboardMarkup):
        _SKIP_KB_CHATS.add(message.chat_id)
    elif message.chat_id in _SKIP_KB_CHATS:
        if isinstance(markup, ReplyKeyboardRemove):
            _SKIP_KB_CHATS.discard(message.chat_id)
        elif not text.lstrip().startswith("❌"):
            if markup is None:
                kwargs["reply_markup"] = ReplyKeyboardRemove()
                _SKIP_KB_CHATS.discard(message.chat_id)
            else:
                await _drop_skip_keyboard(message.get_bot(), message.chat_id)

    text = add_display_name_header(message, text)
    try:
        if len(text) <= 4000:
            return await message.get_bot().send_message(chat_id=message.chat_id, text=text, **kwargs)
    except Exception as e:
        if "Message to be replied not found" in str(e) or "message to be replied not found" in str(e).lower():
            try:
                return await message.get_bot().send_message(chat_id=message.chat_id, text=text, **kwargs)
            except Exception as fallback_error:
                print("Safe reply fallback error:", fallback_error)
                return None
        if "Flood control exceeded" in str(e) or "RetryAfter" in type(e).__name__:
            print("Telegram rate limit while sending reply; skipped.")
            return None
        raise

    chunks = []
    remaining = text
    while len(remaining) > 4000:
        cut = remaining.rfind("\n\n", 0, 4000)
        if cut < 1000:
            cut = remaining.rfind("\n", 0, 4000)
        if cut < 1000:
            cut = 4000
        chunks.append(remaining[:cut].rstrip())
        remaining = remaining[cut:].lstrip()
    if remaining:
        chunks.append(remaining)

    last = len(chunks) - 1
    results = []
    for i, chunk in enumerate(chunks):
        call_kwargs = dict(kwargs)
        if i != last:
            call_kwargs.pop("reply_markup", None)
        results.append(await message.get_bot().send_message(chat_id=message.chat_id, text=chunk, **call_kwargs))
    return results[-1] if results else None

GUESS_MIN_NUMBER, GUESS_MAX_NUMBER = 1, 100
GUESS_MAX_ATTEMPTS, GUESS_REWARD_BERRYS, GUESS_REWARD_CAP = 10, 150, 700

def get_guess_state(user_id):
    return mongo_db.get_guess_state(user_id)

def save_guess_state(user_id, attempts, secret=None, active=False):
    mongo_db.save_guess_state(user_id, attempts, secret, active)

async def guess_num_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user, message = update.effective_user, update.effective_message
    if not user or not message: return
    (await save_user_async(user)); user_id = user.id
    name = html_escape(user.full_name or user.username or "Player")
    header = f"👤 {name}\n\n"; _, _, active = (await asyncio.to_thread(get_guess_state, user_id))
    if active:
        await safe_reply_text(message, header + "⚠️ You already have an active game. Finish it first.", parse_mode="HTML"); return
    secret = random.randint(GUESS_MIN_NUMBER, GUESS_MAX_NUMBER)
    (await asyncio.to_thread(save_guess_state, user_id, 0, secret, True))
    await safe_reply_text(message, header + "🎯 Guess the Number Game Started!\n\n🤫 I have chosen a secret number between 1 and 100.\n🔢 Use `/nguess &lt;number&gt;` to make a guess.\n❤️ You have 10 attempts.\n\n🎁 Guess the correct number to win 150 Berrys!", parse_mode="HTML")

async def guess_number(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user, message = update.effective_user, update.effective_message
    if not user or not message: return
    (await save_user_async(user)); user_id = user.id
    name = html_escape(user.full_name or user.username or "Player")
    header = f"👤 {name}\n\n"
    attempts, secret, active = (await asyncio.to_thread(get_guess_state, user_id))
    if not active or secret is None:
        await safe_reply_text(message, header + "❌ No active Number Guessing game here!\nStart one with /guess_num", parse_mode="HTML"); return
    if len(context.args) != 1:
        await safe_reply_text(message, header + "❌ Please enter only one number.\nExample: `/nguess 60`", parse_mode="HTML"); return
    try: guess = int(context.args[0].strip())
    except (TypeError, ValueError):
        await safe_reply_text(message, header + "❌ Invalid number. Please enter a whole number from 1 to 100.\nExample: `/nguess 60`", parse_mode="HTML"); return
    if not GUESS_MIN_NUMBER <= guess <= GUESS_MAX_NUMBER:
        await safe_reply_text(message, header + "❌ The number must be between 1 and 100.", parse_mode="HTML"); return
    attempt = attempts + 1; secret = int(secret)
    if guess == secret:
        try:
            reward = (await asyncio.to_thread(mongo_db.finish_guess_win, user_id, attempt, GUESS_REWARD_BERRYS, GUESS_REWARD_CAP))
        except Exception as e:
            print("Guess reward error:", e)
            await safe_reply_text(message, header + "❌ You guessed correctly, but the reward could not be added. Please try again later.", parse_mode="HTML"); return

        reward_text = f"+{reward} Berrys" if reward else "0 Berrys (reward cap reached)"
        await safe_reply_text(message, header + f"🎉 Correct! You guessed the number!\n\n🎯 Secret number: {secret}\n🔢 Attempts: {attempt}/10\n🎁 Reward: {reward_text}", parse_mode="HTML"); return
    (await asyncio.to_thread(save_guess_state, user_id, attempt, None, False)) if attempt >= GUESS_MAX_ATTEMPTS else (await asyncio.to_thread(save_guess_state, user_id, attempt, secret, True))
    if attempt >= GUESS_MAX_ATTEMPTS:
        await safe_reply_text(message, header + f"⛔ Game ended!\n\n❌ 10 attempts completed.\n🎯 You could not guess the number.\n🤫 The secret number was {secret}.\n🎁 Reward: 0 Berrys\n\nStart a new game with /guess_num", parse_mode="HTML")
    else:
        hint = "⬆️ The number is HIGHER!" if guess < secret else "⬇️ The number is LOWER!"
        await safe_reply_text(message, header + f"{hint}\n🔢 Attempts: {attempt}/10", parse_mode="HTML")

START_TEXT = (
    "🎮 Welcome to Anime Character Catcher!\n\n"
    "Catch characters, build your collection, earn Berrys, and enjoy the game.\n\n"
    "📖 Use /help to see all available commands."
)


# ---- START FIRST: a NEW member must open the bot's PM before the bot reacts to them in groups ----------------------------
# Blocked: commands (one short notice, at most once a minute per person), button taps (pop-up). Everything else (normal
# messages, catching by typing a name) is ignored silently, like Bot OFF. /start and staff are never blocked.
_START_OK = set()                 # users known to be allowed (cached for the life of the process)
_START_BLOCKED = {}               # user id -> monotonic time of the last DB check that said "blocked"
_START_NOTICE_LAST = {}           # user id -> monotonic time of the last "start the bot first" notice
START_RECHECK, START_NOTICE_GAP = 60, 60

async def _start_blocked(user_id):
    """True when this user has to open the bot's PM first. A database problem never blocks anybody."""
    if user_id in _START_OK:
        return False
    now = time.monotonic()
    last = _START_BLOCKED.get(user_id)
    if last is not None and now - last < START_RECHECK:
        return True
    try:
        if is_owner(user_id) or is_executive(user_id) or await asyncio.to_thread(is_scout, user_id) \
                or await asyncio.to_thread(mongo_db.has_started, user_id):
            _START_OK.add(user_id)
            _START_BLOCKED.pop(user_id, None)
            return False
    except Exception as e:
        print("Start-first check error:", e)
        return False
    if len(_START_BLOCKED) > 5000:
        _START_BLOCKED.clear()
    _START_BLOCKED[user_id] = now
    return True

async def start_first_gate(update, context):
    msg, user = update.effective_message, update.effective_user
    if msg is None or user is None or user.is_bot or not await _start_blocked(user.id):
        return
    command_name, _args = _parse_command(msg.text or "", getattr(context.bot, "username", None))
    if command_name == "start":
        return                                                      # /start always works
    if command_name and command_name in _known_command_names(context.application):
        now = time.monotonic()
        if now - _START_NOTICE_LAST.get(user.id, -1e9) >= START_NOTICE_GAP and getattr(context.bot, "username", None):
            if len(_START_NOTICE_LAST) > 5000:
                _START_NOTICE_LAST.clear()
            _START_NOTICE_LAST[user.id] = now
            try:
                await safe_reply_text(
                    msg, "⚠️ Please start the bot first.\n\nTap the button below, then press Start in the private chat.",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(
                        "▶️ Start Bot", url=f"https://t.me/{context.bot.username}?start=go")]]))
            except Exception as e:
                print("Start-first notice error:", e)
    elif command_name is None and (msg.text or "").startswith("/"):
        return                                                      # a command for another bot: not ours, never blocked
    elif command_name:
        return                                                      # not one of our commands: nothing to block
    raise ApplicationHandlerStop                                    # normal messages and blocked commands: nothing runs

async def start_first_callback_gate(update, context):
    q = update.callback_query
    if q is None or q.message is None or q.message.chat.type not in ("group", "supergroup"):
        return
    user = q.from_user
    if user is None or user.is_bot or not await _start_blocked(user.id):
        return
    try:
        await q.answer("⚠️ Please start the bot first: open my private chat and press Start.", show_alert=True)
    except Exception:
        pass
    raise ApplicationHandlerStop

async def mark_started_private(update, context):
    """Any message in the bot's PM = the user opened the chat, so the bot may react to them in groups (and DM them)."""
    user = update.effective_user
    if user is None or user.is_bot or user.id in _START_OK:
        return
    try:
        await asyncio.to_thread(mongo_db.mark_started, user.id)
    except Exception as e:
        print("Mark started error:", e)
        return
    _START_OK.add(user.id)
    _START_BLOCKED.pop(user.id, None)


async def _rules_button_rows(context, chat, user_id):
    """[[📜 View Rules]] for a NEW member (created after the update, rules not opened yet) who presses /start in a group.
    The button opens the bot's PM with /start rules (which also starts the bot). A new member who has not started the bot and
    has no rules to read gets ▶️ Start Bot instead. None for everyone else (old members, PM)."""
    if chat is None or chat.type not in ("group", "supergroup") or not getattr(context.bot, "username", None):
        return None
    try:
        if await asyncio.to_thread(mongo_db.needs_rules_prompt, user_id):
            return [[InlineKeyboardButton("📜 View Rules", url=f"https://t.me/{context.bot.username}?start=rules")]]
        if await _start_blocked(user_id):
            return [[InlineKeyboardButton("▶️ Start Bot", url=f"https://t.me/{context.bot.username}?start=go")]]
    except Exception as e:
        print("Rules button check error:", e)
    return None


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    (await save_user_async(update.effective_user))
    if update.effective_chat and update.effective_chat.type in ("group", "supergroup"):
        (await asyncio.to_thread(register_bot_group, update.effective_chat))
    user_id = update.effective_user.id

    private = update.effective_chat.type == "private"
    if private:
        await refresh_command_menu(context.bot, user_id)
    else:
        await refresh_group_command_menu(context.bot, update.effective_chat.id, user_id)

    rules_rows = await _rules_button_rows(context, update.effective_chat, user_id)
    if not await theme.send_start(update, context, extra_rows=rules_rows):     # only acts when the Owner saved a customization
        keyboard = start_help_keyboard(update.effective_user.id)
        if rules_rows:
            keyboard = InlineKeyboardMarkup(list(keyboard.inline_keyboard) + rules_rows)
        await safe_reply_text(update.message,
            START_TEXT,
            reply_markup=keyboard,
        )

    if private:       # the rules follow the welcome message: for a new member's first /start, or when they tapped 📜 View Rules
        try:
            explicit = bool(context.args) and context.args[0].lower() == "rules"
            if explicit or await asyncio.to_thread(mongo_db.needs_rules_prompt, user_id):
                if await _send_rules(update.message):
                    await asyncio.to_thread(mongo_db.mark_rules_seen, user_id)
        except Exception as e:
            print("Start rules error:", e)

async def help_command(update, context):
    (await save_user_async(update.effective_user))
    user_id = update.effective_user.id

    help_text = build_help_text()

    if update.effective_chat.type == "private":
        await safe_reply_text(update.message,
            help_text,
            reply_markup=(await asyncio.to_thread(staff_help_keyboard, user_id)),
        )
    else:
        await refresh_group_command_menu(context.bot, update.effective_chat.id, user_id)
        await safe_reply_text(update.message,
            help_text,
            reply_markup=(await asyncio.to_thread(staff_help_keyboard, user_id)),
        )

async def _edit_help_message(query, text, reply_markup=None):
    text = str(text or "")
    try:
        if len(text) <= 4000:
            await query.edit_message_text(text, reply_markup=reply_markup)
            return
    except Exception as e:
        print("Help edit error:", e)

    try:
        msg = query.message
        if msg is not None:
            await safe_reply_text(msg, text, reply_markup=reply_markup)
    except Exception as e:
        print("Help fallback send error:", e)

# ---------------------------------------------------------------------------------------------------
# ANIME CODE RANGES (Owner + Executive). Every anime owns a reserved block of 4-digit codes.
# Typed commands (/setrange /delrange /range /freecode /nextcode) and the 📏 Range Panel buttons use the SAME
# functions below and the same mongo_db functions, so their results are always identical.
# Callback data: rg:<user_id>:<action>[:args]  (<= 64 bytes; anime are referenced by a short hash).
#   l:<kind>:<page> numbered list (r range / f free / n next)      v:<mode>:<hash>:<count> one anime (r / f / n / d)
#   p:<o|e> open panel   sa/sp/ss/se/sy set-range flow   dl/fl/nl pickers   q search   dd delete   sr set range   x cancel
# ---------------------------------------------------------------------------------------------------
RANGE_PAGE_SIZE = 12                  # lines per page of a numbered list / anime buttons per picker page
RANGE_PICK_MAX = 24                   # anime buttons shown when a typed name matches several anime
RANGE_PANEL_TTL = 300                 # a panel flow expires after 5 minutes without a tap or message
RANGE_MSG_LIMIT = 3800                # a longer answer is split into several messages
RANGE_MAX_NEXT = 50                   # /nextcode <anime> <count> maximum
_rg_state = {}                        # user id -> panel flow state {role, step, anime, start, end, chat, msg, exp}
_RG_TEXT_STEPS = ("sa", "ss", "se", "q")      # panel steps that wait for a typed message


def _rg_allowed(user_id):
    return is_owner(user_id) or is_executive(user_id)


def _rg_fc(n):
    return mongo_db.fmt_code(n)


def _rg_span(s, e):
    return f"{_rg_fc(s)}-{_rg_fc(e)}"


def _rg_span_sp(s, e):
    return f"{_rg_fc(s)} - {_rg_fc(e)}"


def _rg_btn(label, data):
    return InlineKeyboardButton(label, callback_data=data)


def _rg_grid(buttons, per_row=3):
    return [buttons[i:i + per_row] for i in range(0, len(buttons), per_row)]


def _rg_nav_row(uid, back_data):
    return [_rg_btn("⬅ Back", back_data), _rg_btn("❌ Cancel", f"rg:{uid}:x")]


def _rg_page_row(uid, prefix, page, pages):
    noop = f"rg:{uid}:noop"
    return [_rg_btn("◀ Previous", f"{prefix}:{page - 1}" if page > 0 else noop),
            _rg_btn(f"{page + 1}/{pages}", noop),
            _rg_btn("Next ▶", f"{prefix}:{page + 1}" if page < pages - 1 else noop)]


def _rg_slice(items, page, size=RANGE_PAGE_SIZE):
    pages = max(1, -(-len(items) // size))
    page = min(max(int(page), 0), pages - 1)
    return items[page * size:(page + 1) * size], page, pages, page * size


def _rg_split_line(line, limit):
    if len(line) <= limit:
        return [line]
    out, cur = [], ""
    for piece in line.split(", "):
        if cur and len(cur) + 2 + len(piece) + 1 > limit:
            out.append(cur + ",")
            cur = piece
        else:
            cur = piece if not cur else cur + ", " + piece
    if cur:
        out.append(cur)
    return out


def rg_chunks(lines, limit=RANGE_MSG_LIMIT):
    """Lines -> messages no longer than Telegram allows (a very long line is cut between its commas)."""
    pieces = []
    for line in lines:
        pieces.extend(_rg_split_line(str(line), limit))
    chunks, cur = [], ""
    for piece in pieces:
        if cur and len(cur) + 1 + len(piece) > limit:
            chunks.append(cur)
            cur = piece
        else:
            cur = piece if not cur else cur + "\n" + piece
    if cur:
        chunks.append(cur)
    return chunks or [""]


async def log_range_change(context, user, chat, command, args):
    """Executive range change (set/delete) -> the Yes/No log prompt, called only AFTER the whole action succeeded.
    Owner actions are never logged or prompted; read-only range commands never come here."""
    try:
        role = await _role_label(user.id)
        if role != "Executive":
            return
        cfg = await get_log_config()
        if not cfg or cfg.get("chat_id") is None:
            return
        category = resolve_log_category(command, cfg)
        if category in set(cfg.get("disabled_categories") or []):
            return
        text = build_log_text(category, role, user, chat, command, args)
        await _send_log_prompt(context, user.id, text, category, command, chat.id if chat else user.id)
    except Exception as e:
        print("Range log prompt error:", repr(e))


# ---- views shared by the typed commands and the Range Panel -------------------------------------------
async def rg_list_view(kind, page, uid, back=None):
    """(text, markup) of the numbered single-column list: kind r = /range, f = /freecode, n = /nextcode."""
    if kind == "r":
        rows = await asyncio.to_thread(mongo_db.get_ranges)
        lines_all = [f"{r['anime_name']}: {_rg_span_sp(r['start_code'], r['end_code'])}" for r in rows]
        title = "📏 Code ranges"
    else:
        sts = await asyncio.to_thread(mongo_db.all_range_status)
        lines_all = []
        for st in sts:
            if kind == "f":
                if st["free_count"] == 0:
                    lines_all.append(f"{st['name']}: full ({_rg_span(st['start'], st['end'])})")
                else:
                    runs = st["free_runs"]
                    shown = mongo_db.format_runs(runs[:3]) + (", …" if len(runs) > 3 else "")
                    lines_all.append(f"{st['name']}: {st['free_count']} free ({shown})")
            else:
                lines_all.append(f"{st['name']}: " + (_rg_fc(st["free_runs"][0][0]) if st["free_count"] else "range is full"))
        title = "🆓 Free codes" if kind == "f" else "➡️ Next free codes"
    markup_rows = []
    if not lines_all:
        text = f"{title}\n\nNo ranges are set yet.\nUse /setrange <anime> <start> <end>, or the Range Panel."
    else:
        part, page, pages, offset = _rg_slice(lines_all, page)
        body = "\n".join(f"{offset + i}. {line}" for i, line in enumerate(part, 1))
        text = f"{title} ({len(lines_all)})\n\n{body}"
        if pages > 1:
            markup_rows.append(_rg_page_row(uid, f"rg:{uid}:l:{kind}", page, pages))
    if back:
        markup_rows.append(_rg_nav_row(uid, back))
    return text, (InlineKeyboardMarkup(markup_rows) if markup_rows else None)


async def rg_detail_view(mode, name, uid, count=1, back=None):
    """([message texts], [button rows]) for ONE anime. mode r = /range <anime>, f = /freecode <anime>,
    n = /nextcode <anime> [count], d = the delete confirmation. back = callback of the panel's Back button."""
    h = mongo_db.anime_hash(name)
    if mode == "n":
        info = await asyncio.to_thread(mongo_db.next_free_codes, name, count)
        st = None if info is None else {"name": info["name"], "start": info["start"], "end": info["end"]}
    else:
        st = await asyncio.to_thread(mongo_db.range_status, name)
    rows = []
    if st is None:
        chunks = [f"No range set for {name}"]
        rows.append([_rg_btn("📏 Set Range", f"rg:{uid}:sr:{h}")])
    elif mode == "r":
        lines = [st["name"], f"Range: {_rg_span_sp(st['start'], st['end'])}",
                 f"Used: {st['used_count']} | Free: {st['free_count']} | Total: {st['total']}",
                 "Used codes: " + (mongo_db.format_runs(st["used_runs"]) or "none"),
                 "Free codes: " + (mongo_db.format_runs(st["free_runs"]) or "none")]
        chunks = rg_chunks(lines)
        rows.append([_rg_btn("🆓 Free", f"rg:{uid}:v:f:{h}:1"), _rg_btn("➡️ Next", f"rg:{uid}:v:n:{h}:1"),
                     _rg_btn("📋 All", f"rg:{uid}:l:r:0")])
    elif mode == "f":
        lines = [st["name"], f"Range: {_rg_span_sp(st['start'], st['end'])}",
                 f"Used: {st['used_count']} | Free: {st['free_count']} | Total: {st['total']}",
                 "Free codes: " + (mongo_db.format_runs(st["free_runs"]) or "none (the range is full)")]
        chunks = rg_chunks(lines)
        rows.append([_rg_btn("📏 Range", f"rg:{uid}:v:r:{h}:1"), _rg_btn("➡️ Next", f"rg:{uid}:v:n:{h}:1"),
                     _rg_btn("📋 All", f"rg:{uid}:l:f:0")])
    elif mode == "n":
        span = _rg_span(info["start"], info["end"])
        if info["full"]:
            chunks = [f"{info['name']} range is full ({span})\n"
                      f"Extend it with /setrange {info['name']} {_rg_fc(info['start'])} <new end>"]
        elif count <= 1:
            chunks = [f"{info['name']}: next free code is {_rg_fc(info['codes'][0])} (range {span})"]
        else:
            codes = ", ".join(_rg_fc(c) for c in info["codes"])
            text = f"{info['name']}: next {len(info['codes'])} free codes: {codes} (range {span})"
            if len(info["codes"]) < count:
                text += f"\nOnly {len(info['codes'])} free code(s) are left in this range."
            chunks = rg_chunks([text])
        rows.append([_rg_btn("📏 Range", f"rg:{uid}:v:r:{h}:1"), _rg_btn("🆓 Free", f"rg:{uid}:v:f:{h}:1"),
                     _rg_btn("📋 All", f"rg:{uid}:l:n:0")])
    else:                                                      # d: delete confirmation
        chunks = [f"🗑 Delete the range of {st['name']}?\n\n{st['name']}: {_rg_span_sp(st['start'], st['end'])}\n"
                  f"{st['used_count']} characters use codes in it. Characters are never deleted or changed; "
                  "only the reserved range is removed."]
        middle = _rg_btn("⬅ Back", back) if back else _rg_btn("📏 Range", f"rg:{uid}:v:r:{h}:1")
        rows.append([_rg_btn("✅ Delete", f"rg:{uid}:dd:{h}"), middle, _rg_btn("❌ Cancel", f"rg:{uid}:x")])
        return chunks, rows
    if back:
        rows.append(_rg_nav_row(uid, back))
    return chunks, rows


async def rg_lookup_view(mode, query, uid, count=1, back=None):
    """Name matching shared by every range command and button: exact or single partial match -> the answer;
    several -> buttons to pick; none -> 'No range found' + the 3 closest names as buttons."""
    res = await asyncio.to_thread(mongo_db.resolve_anime, query)
    if res["status"] in ("exact", "one"):
        return await rg_detail_view(mode, res["name"], uid, count, back)
    if res["status"] == "multi":
        names = res["names"]
        buttons = [_rg_btn(n, f"rg:{uid}:v:{mode}:{mongo_db.anime_hash(n)}:{count}") for n in names[:RANGE_PICK_MAX]]
        text = f"'{query}' matches {len(names)} anime. Pick one:"
        if len(names) > RANGE_PICK_MAX:
            text += f"\n(Showing the first {RANGE_PICK_MAX}. Type more of the name to narrow it down.)"
    else:
        names = res["closest"]
        buttons = [_rg_btn(n, f"rg:{uid}:v:{mode}:{mongo_db.anime_hash(n)}:{count}") for n in names]
        text = f"No range found for '{query}'" + ("\nDid you mean:" if buttons else "")
    rows = _rg_grid(buttons, 3)
    if back:
        rows.append(_rg_nav_row(uid, back))
    return [text], rows


def _rg_move_rows(uid, h, old_start, old_end, decided=False):
    """The 'change codes or keep them' buttons shown after an existing range moved."""
    tail = f"{h}:{old_start}:{old_end}"
    if decided:
        return [[_rg_btn("✋ Keep codes", f"rg:{uid}:mk:{tail}")]]
    return [[_rg_btn("✅ Change codes", f"rg:{uid}:mc:{tail}"), _rg_btn("👁 Preview", f"rg:{uid}:mp:{tail}"),
             _rg_btn("✋ Keep codes", f"rg:{uid}:mk:{tail}")]]


async def rg_do_set(context, user, chat, name, start, end):
    """Create/update a range (typed /setrange and the panel's Confirm). Returns (ok, text, rows).
    When an EXISTING range moved (e.g. 0001-0300 -> 5000-5300) and characters use codes in the old range, `rows` holds
    the Change codes / Preview / Keep codes buttons; the log prompt then waits for that decision."""
    result = await asyncio.to_thread(mongo_db.set_range, name, start, end, user.id)
    if not result["ok"]:
        if result["error"] == "overlap":
            offer = await rg_extend_offer(user.id, name, start, end)
            if offer:
                return False, offer[0], offer[1]
        return False, "❌ " + result["message"], None
    r, prev = result["range"], result["previous"]
    anime = r["anime_name"]
    span = _rg_span_sp(r["start_code"], r["end_code"])
    total = r["end_code"] - r["start_code"] + 1
    if prev is None:
        text = f"✅ Range created\n{anime}: {span} ({total} codes)"
    else:
        text = f"✅ Range updated\n{anime}: {_rg_span_sp(prev['start_code'], prev['end_code'])} → {span} ({total} codes)"
    rows = None
    try:
        if prev is not None and prev["start_code"] != r["start_code"]:
            plan = await asyncio.to_thread(mongo_db.plan_code_move, anime, prev["start_code"], prev["end_code"],
                                           r["start_code"], r["end_code"])
            if plan["error"]:
                text += f"\n\n⚠️ {plan['error']}\nNothing was moved: the existing characters keep their codes."
            elif plan["moves"]:
                lo = min(m[0] for m in plan["moves"])
                text += (f"\n\n🔄 {len(plan['moves'])} existing {anime} character(s) have codes in the old range "
                         f"({_rg_span_sp(prev['start_code'], prev['end_code'])}).\n"
                         f"Change their codes to the new range (their position is kept: {_rg_fc(lo)} → {_rg_fc(lo + plan['shift'])}), "
                         "or keep them as they are?")
                rows = _rg_move_rows(user.id, mongo_db.anime_hash(anime), prev["start_code"], prev["end_code"])
        if rows is None:
            outside = await asyncio.to_thread(mongo_db.outside_count, anime)
            if outside:
                text += f"\n⚠️ {outside} existing {anime} character(s) have codes outside this range."
    except Exception as e:
        print("Range move-plan error:", repr(e))
    if rows is None:
        await log_range_change(context, user, chat, "setrange", f"{anime} {_rg_fc(r['start_code'])} {_rg_fc(r['end_code'])}")
    return True, text, rows


async def rg_move_decision(query, context, user, chat, act, h, old_start, old_end):
    """The buttons after a range moved: mp = preview, mc = change the codes, mk = keep them."""
    name = await asyncio.to_thread(mongo_db.anime_by_hash, h)
    cur = await asyncio.to_thread(mongo_db.get_range, name) if name else None
    if not name or cur is None:
        await _rg_edit(query, "That range no longer exists, so there is nothing to move.")
        return
    uid = user.id
    plan = await asyncio.to_thread(mongo_db.plan_code_move, name, old_start, old_end, cur["start_code"], cur["end_code"])
    new_span = _rg_span(cur["start_code"], cur["end_code"])
    base = f"{name}: {_rg_span(old_start, old_end)} → {new_span}"
    if not plan["moves"]:                                    # an old button: nothing left to decide
        await _rg_edit(query, f"ℹ️ Nothing to move for {name}: no characters use codes in the old range "
                              f"({_rg_span(old_start, old_end)}) anymore.")
        return
    if act == "mk":
        await _rg_edit(query, f"✅ Codes kept\n{base}\nThe characters keep their current codes. The range check "
                              "(check_code_ranges.py) lists the ones outside the new range.")
        await log_range_change(context, user, chat, "setrange",
                               f"{name} {_rg_fc(cur['start_code'])} {_rg_fc(cur['end_code'])} (codes kept)")
        return
    if plan["error"]:
        await _rg_edit(query, f"⚠️ {plan['error']}\nNothing was moved.", _rg_move_rows(uid, h, old_start, old_end, True))
        return
    moves = plan["moves"]
    if act == "mp":
        shown = sorted(moves)[:6]
        lines = [f"👁 Preview — {base}", f"{len(moves)} character(s) would move (position kept):"]
        lines += [f"{_rg_fc(o)} → {_rg_fc(n)}  {nm}" for o, n, nm in shown]
        if len(moves) > len(shown):
            lines.append(f"… and {len(moves) - len(shown)} more")
        if plan["evolution_left"]:
            lines.append(f"{plan['evolution_left']} Evolution character(s) keep their codes (use /editevo).")
        await _rg_edit(query, "\n".join(lines), _rg_move_rows(uid, h, old_start, old_end))
        return
    active = context.application.bot_data.setdefault("active_spawns", {})
    spawned = {str(sp.get("code")) for sp in active.values()}
    busy = [_rg_fc(o) for o, _n, _nm in moves if _rg_fc(o) in spawned]
    if busy:
        await _rg_edit(query, "❌ These characters are spawned in a group right now: " + ", ".join(busy[:10]) +
                       "\nCatch or expire the spawns first, then tap Change codes again. Nothing was moved.",
                       _rg_move_rows(uid, h, old_start, old_end))
        return
    try:
        moved = await asyncio.to_thread(mongo_db.apply_code_move, moves)
    except Exception as e:
        print("Range code move error:", repr(e))
        await _rg_edit(query, "❌ The codes could not be changed. Nothing was moved. Please try again.",
                       _rg_move_rows(uid, h, old_start, old_end))
        return
    text = f"✅ Codes changed\n{base}\n{moved} character(s) moved to the new range (position kept)."
    if plan["evolution_left"]:
        text += f"\n{plan['evolution_left']} Evolution character(s) keep their codes (use /editevo)."
    await _rg_edit(query, text)
    await log_range_change(context, user, chat, "setrange",
                           f"{name} {_rg_fc(cur['start_code'])} {_rg_fc(cur['end_code'])} (codes moved: {moved})")


async def rg_do_delete(context, user, chat, name):
    """Delete a range (typed /delrange after Confirm, and the panel). Returns text."""
    old = await asyncio.to_thread(mongo_db.get_range, name)
    if old is None:
        return f"No range set for {name}"
    if not await asyncio.to_thread(mongo_db.delete_range, name):
        return f"No range set for {name}"
    await log_range_change(context, user, chat, "delrange", old["anime_name"])
    return f"✅ Range deleted\n{old['anime_name']}: {_rg_span_sp(old['start_code'], old['end_code'])}"


async def rg_code_problem(anime, code, exclude_code=None):
    """Add/edit validation of a code against the anime's range: the error text, or None when the code is fine
    (also when the anime has no range yet - nothing is enforced then)."""
    chk = await asyncio.to_thread(mongo_db.check_code_for_anime, anime, code, exclude_code)
    if chk["status"] == "outside":
        return f"❌ Code {code} is outside {chk['name']}'s range ({_rg_span(chk['start'], chk['end'])})."
    if chk["status"] == "taken":
        if chk["suggestions"]:
            tail = "Next free codes: " + ", ".join(_rg_fc(c) for c in chk["suggestions"]) + "."
        else:
            tail = f"{chk['name']}'s range is full ({_rg_span(chk['start'], chk['end'])}). Extend it with /setrange."
        return f"❌ Code {code} is already used by {chk['owner']}.\n{tail}"
    return None


async def rg_free_codes_markup(user_id, anime):
    """The '🔢 Show Free Codes' button of the Add Character flow (only when the anime has a range)."""
    if not (anime or "").strip() or await asyncio.to_thread(mongo_db.get_range, anime) is None:
        return None
    return InlineKeyboardMarkup([[_rg_btn("🔢 Show Free Codes", f"rg:{user_id}:fa:a")]])


# ---- sending ------------------------------------------------------------------------------------------
async def rg_reply(message, chunks, rows):
    """Typed command answer: every chunk is a message, the buttons go under the last one."""
    for i, chunk in enumerate(chunks):
        last = i == len(chunks) - 1
        await safe_reply_text(message, chunk, reply_markup=InlineKeyboardMarkup(rows) if (last and rows) else None)


async def _rg_edit(query, text, rows=None):
    """Edit the tapped message in place (one tab). 'Message is not modified' is ignored; any other failure
    falls back to one new message."""
    markup = InlineKeyboardMarkup(rows) if rows else None
    try:
        await query.edit_message_text(text, reply_markup=markup)
    except BadRequest as e:
        if "not modified" in str(e).lower():
            return
        print("Range edit error:", repr(e))
        try:
            await safe_reply_text(query.message, text, reply_markup=markup)
        except Exception as e2:
            print("Range edit fallback error:", repr(e2))
    except Exception as e:
        print("Range edit error:", repr(e))


async def rg_show(query, context, chunks, rows):
    """Callback answer: the first chunk edits the tapped message; extra chunks (very long results) follow as
    new messages, with the buttons under the last one."""
    if len(chunks) == 1:
        await _rg_edit(query, chunks[0], rows)
        return
    await _rg_edit(query, chunks[0], None)
    chat_id = query.message.chat_id
    for i, chunk in enumerate(chunks[1:], 1):
        last = i == len(chunks) - 1
        await context.bot.send_message(chat_id=chat_id, text=chunk,
                                       reply_markup=InlineKeyboardMarkup(rows) if (last and rows) else None)


# ---- typed commands -----------------------------------------------------------------------------------
async def range_command(update, context):
    """/range [anime]  (alias /ranges). Owner + Executive (the role gate already answered anyone else)."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not _rg_allowed(user.id):
        return
    query = " ".join(context.args or []).strip()
    if not query:
        text, markup = await rg_list_view("r", 0, user.id)
        await safe_reply_text(msg, text, reply_markup=markup)
        return
    chunks, rows = await rg_lookup_view("r", query, user.id)
    await rg_reply(msg, chunks, rows)


async def freecode_command(update, context):
    """/freecode [anime]  (alias /freecodes)."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not _rg_allowed(user.id):
        return
    query = " ".join(context.args or []).strip()
    if not query:
        text, markup = await rg_list_view("f", 0, user.id)
        await safe_reply_text(msg, text, reply_markup=markup)
        return
    chunks, rows = await rg_lookup_view("f", query, user.id)
    await rg_reply(msg, chunks, rows)


async def nextcode_command(update, context):
    """/nextcode [anime] [count]."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not _rg_allowed(user.id):
        return
    args = list(context.args or [])
    if not args:
        text, markup = await rg_list_view("n", 0, user.id)
        await safe_reply_text(msg, text, reply_markup=markup)
        return
    query, count = " ".join(args).strip(), 1
    if len(args) >= 2 and args[-1].isdigit():                  # /nextcode Naruto 5  (a name that ends in a number still works)
        name_part = " ".join(args[:-1])
        if (await asyncio.to_thread(mongo_db.resolve_anime, name_part))["status"] != "none":
            query, count = name_part, max(1, min(int(args[-1]), RANGE_MAX_NEXT))
    chunks, rows = await rg_lookup_view("n", query, user.id, count)
    await rg_reply(msg, chunks, rows)


async def setrange_command(update, context):
    """/setrange <anime> <start> <end> - create or update a range."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not _rg_allowed(user.id):
        return
    args = list(context.args or [])
    usage = "Usage: /setrange <anime> <start> <end>\nExample: /setrange Naruto 0001 0200"
    if len(args) < 3:
        await safe_reply_text(msg, usage)
        return
    name = " ".join(args[:-2])
    ok, text, rows = await rg_do_set(context, user, update.effective_chat, name, args[-2], args[-1])
    await safe_reply_text(msg, text if (ok or rows) else text + "\n\n" + usage,
                          reply_markup=InlineKeyboardMarkup(rows) if rows else None)


async def delrange_command(update, context):
    """/delrange <anime> - delete a range (asks for confirmation first)."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not _rg_allowed(user.id):
        return
    query = " ".join(context.args or []).strip()
    if not query:
        await safe_reply_text(msg, "Usage: /delrange <anime>\nExample: /delrange Naruto")
        return
    chunks, rows = await rg_lookup_view("d", query, user.id)
    await rg_reply(msg, chunks, rows)


def _rg_spawned(context):
    """Codes of the characters spawned in groups right now (they must not be renumbered at this moment)."""
    active = context.application.bot_data.get("active_spawns", {}) or {}
    return {int(str(sp.get("code"))) for sp in active.values() if str(sp.get("code")).isdigit()}


async def rg_fill_view(uid, context, only_name=None, back=None):
    """([texts], [button rows]) of the /fillranges preview: what would move where. Nothing is changed here."""
    plan = await asyncio.to_thread(mongo_db.plan_fill_ranges, _rg_spawned(context), only_name)
    h = mongo_db.anime_hash(only_name) if only_name else ""
    arg = f":{h}" if h else ""
    lines = ["🧩 Fill ranges — preview" + (f" ({only_name})" if only_name else ""), ""]
    if not plan["per_anime"]:
        lines.append("No ranges are set yet. Set them first with /setrange.")
    elif plan["moving"] == 0:
        lines.append("✅ Nothing to move: every character is already inside its anime's range.")
    else:
        lines.append(f"Characters to move into their anime's range: {plan['moving']}")
        lines.append(f"Already inside their range (they keep their codes): {plan['inside']}")
    lines.append("")
    n = 0
    for e in plan["per_anime"]:
        n += 1
        span = _rg_span(e["start"], e["end"])
        if e["status"] == "too_small":
            lines.append(f"{n}. {e['name']}: skipped - needs {e['need']} free codes, the range {span} has {e['slots']}. Extend it first")
        elif e["status"] == "moves":
            lines.append(f"{n}. {e['name']}: {e['moving']} to move (range {span})")
        else:
            lines.append(f"{n}. {e['name']}: nothing to move ✓")
    if plan["samples"]:
        lines += ["", "Examples:"] + [f"{_rg_fc(o)} → {_rg_fc(nw)}  {nm}" for o, nw, nm in plan["samples"]]
    notes = []
    if plan["evolution"]:
        notes.append(f"{plan['evolution']} Evolution character(s) (use /editevo)")
    if plan["unranged"]:
        notes.append(f"{sum(plan['unranged'].values())} character(s) of anime without a range ("
                     + ", ".join(list(plan["unranged"])[:5]) + (", …" if len(plan["unranged"]) > 5 else "") + ")")
    if plan["deferred"]:
        notes.append(f"{plan['deferred']} spawned in a group right now (run it again later)")
    if notes:
        lines += ["", "Not moved: " + "; ".join(notes)]
    rows = []
    if plan["moving"]:
        rows.append([_rg_btn("✅ Apply", f"rg:{uid}:fy{arg}"), _rg_btn("🔄 Refresh", f"rg:{uid}:fv{arg}"),
                     _rg_btn("❌ Cancel", f"rg:{uid}:x")])
    if back:
        rows.append(_rg_nav_row(uid, back))
    return rg_chunks(lines), rows


async def rg_run_job(query, context, job_id, title):
    """Run a saved move job to the end in small batches, with progress in the same message. Returns True when finished.
    A stop halfway leaves everything consistent: the Continue button resumes the same job."""
    uid = query.from_user.id
    lock = context.application.bot_data.setdefault("code_job_lock", asyncio.Lock())
    if lock.locked():
        await _rg_edit(query, "⏳ Another code move is running right now. Wait for it to finish, then try again.")
        return False
    async with lock:
        info = await asyncio.to_thread(mongo_db.get_move_job, job_id)
        total = info["total"] if info else 0
        await _rg_edit(query, f"⏳ {title}…\n{info['done'] if info else 0}/{total} characters moved. Please wait.")
        while True:
            try:
                res = await asyncio.to_thread(mongo_db.run_move_job, job_id, 40)
            except Exception as e:
                print("Move job error:", repr(e))
                now = await asyncio.to_thread(mongo_db.get_move_job, job_id)
                await _rg_edit(query, f"❌ Stopped: {e}\n{now['done'] if now else '?'}/{total} characters were moved. "
                                      "Nothing is broken; tap Continue to carry on.",
                               [[_rg_btn("🔁 Continue", f"rg:{uid}:jr:{job_id}"), _rg_btn("📋 Ranges", f"rg:{uid}:l:r:0"),
                                 _rg_btn("❌ Close", f"rg:{uid}:x")]])
                return False
            if res["finished"]:
                return True
            await _rg_edit(query, f"⏳ {title}…\n{res['done']}/{res['total']} characters moved. Please wait.")


async def rg_fill_apply(query, context, user, chat, h):
    """Apply /fillranges (the ✅ Apply button): re-plan with the current data, save the job, run it."""
    only = await asyncio.to_thread(mongo_db.anime_by_hash, h) if h else None
    plan = await asyncio.to_thread(mongo_db.plan_fill_ranges, _rg_spawned(context), only)
    if not plan["steps"]:
        await _rg_edit(query, "✅ Nothing to move: every character is already inside its anime's range.")
        return
    job_id = await asyncio.to_thread(mongo_db.create_move_job, "fill", plan["steps"], [], user.id)
    if not await rg_run_job(query, context, job_id, "Filling ranges"):
        return
    text = f"✅ Ranges filled\n{plan['moving']} character(s) moved into their anime's range."
    if plan["skipped"]:
        text += "\nSkipped (range too small): " + ", ".join(plan["skipped"]) + ". Extend them, then run /fillranges again."
    if plan["deferred"]:
        text += f"\n{plan['deferred']} spawned character(s) were skipped; run /fillranges again later."
    await _rg_edit(query, text)
    await log_range_change(context, user, chat, "fillranges", f"{plan['moving']} characters moved into their ranges")


async def rg_extend_offer(uid, name, start, end):
    """A range that grows into the next one: ([text], rows) offering to shift the following ranges, or None when this is
    not an extension of an existing range."""
    plan = await asyncio.to_thread(mongo_db.plan_range_extend, name, start, end)
    cur = await asyncio.to_thread(mongo_db.get_range, name)
    s_, e_ = mongo_db.parse_code(start), mongo_db.parse_code(end)
    if cur is None or s_ is None or e_ is None or s_ != cur["start_code"] or e_ <= cur["end_code"]:
        return None                                    # only a range that keeps its start and grows its end can shift the next ones
    head = f"❌ {cur['anime_name']} {_rg_span(s_, e_)} runs into the next range."
    if not plan["ok"]:
        return head + "\n⚠️ " + plan["error"], None
    lines = [head, "Shift the following ranges up so everything still fits? Their characters keep their position:"]
    for i, sh in enumerate(plan["shifts"], 1):
        lines.append(f"{i}. {sh['name']}: {_rg_span(*sh['old'])} → {_rg_span(*sh['new'])} (+{sh['shift']}, {sh['chars']} characters)")
    lines.append(f"Characters to move: {plan['moving']}")
    h = mongo_db.anime_hash(cur["anime_name"])
    rows = [[_rg_btn("✅ Shift & move", f"rg:{uid}:xs:{h}:{s_}:{e_}"), _rg_btn("📋 Ranges", f"rg:{uid}:l:r:0"),
             _rg_btn("❌ Cancel", f"rg:{uid}:x")]]
    return "\n".join(lines), rows


async def rg_extend_apply(query, context, user, chat, h, new_start, new_end):
    """Apply a range extension with shifting (the ✅ Shift & move button)."""
    name = await asyncio.to_thread(mongo_db.anime_by_hash, h)
    plan = await asyncio.to_thread(mongo_db.plan_range_extend, name, new_start, new_end, _rg_spawned(context)) if name else None
    if not plan or not plan["ok"]:
        await _rg_edit(query, "❌ " + ((plan or {}).get("error") or "That range no longer exists.") + "\nNothing was changed.")
        return
    job_id = await asyncio.to_thread(mongo_db.create_move_job, "extend", plan["steps"], plan["ranges_after"], user.id)
    if not await rg_run_job(query, context, job_id, "Shifting ranges"):
        return
    lines = [f"✅ Range extended\n{name}: now {_rg_span_sp(new_start, new_end)}"]
    lines += [f"{sh['name']}: {_rg_span(*sh['old'])} → {_rg_span(*sh['new'])}" for sh in plan["shifts"]]
    lines.append(f"{plan['moving']} character(s) moved with their ranges.")
    await _rg_edit(query, "\n".join(lines))
    await log_range_change(context, user, chat, "setrange", f"{name} {_rg_fc(new_start)} {_rg_fc(new_end)} (following ranges shifted)")


async def rg_resume_job(query, context, user, chat, job_id):
    """The 🔁 Continue button after a stopped job."""
    info = await asyncio.to_thread(mongo_db.get_move_job, job_id)
    if info is None:
        await _rg_edit(query, "That job no longer exists.")
        return
    if info["status"] == "done":
        await _rg_edit(query, "✅ That job is already finished.")
        return
    if not await rg_run_job(query, context, job_id, "Continuing"):
        return
    await _rg_edit(query, f"✅ Finished\n{info['total']} characters were moved.")
    await log_range_change(context, user, chat,
                           {"fill": "fillranges", "undo": "undocodes"}.get(info["kind"], "setrange"),
                           f"code move finished ({info['total']} characters)")


async def fillranges_command(update, context):
    """/fillranges [anime] - preview, then move every character into the range of its anime (PM only)."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not _rg_allowed(user.id):
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(msg, "⚠️ /fillranges can only be used in the bot's PM (private chat).")
        return
    query = " ".join(context.args or []).strip()
    only = None
    if query:
        res = await asyncio.to_thread(mongo_db.resolve_anime, query)
        if res["status"] not in ("exact", "one"):
            chunks, rows = await rg_lookup_view("r", query, user.id)
            await rg_reply(msg, chunks, rows)
            return
        only = res["name"]
    chunks, rows = await rg_fill_view(user.id, context, only)
    await rg_reply(msg, chunks, rows)


async def rg_undo_view(uid, back=None):
    """([text], rows) of the 'undo the last code move' screen."""
    last = await asyncio.to_thread(mongo_db.get_last_move_job)
    lines = ["↩ Undo last code move", ""]
    rows = []
    if last is None:
        lines.append("No code move has been run yet.")
    elif not last["can_undo"]:
        lines.append(last["reason"])
    else:
        what = {"fill": "Fill ranges", "extend": "Range shift"}.get(last["kind"], str(last["kind"]))
        when = str(last["created_at"] or "").replace("T", " ")[:16]
        state = "finished" if last["status"] == "done" else "stopped halfway"
        lines += [f"Last move: {what} ({when}, {state})",
                  f"Characters moved: {last['done']} of {last['total']}", "",
                  "Undo puts those characters back on their old codes and restores the ranges as they were. "
                  "It only works if nobody changed those characters in the meantime."]
        rows.append([_rg_btn("↩ Undo it", f"rg:{uid}:uy:{last['id']}"), _rg_btn("🔄 Refresh", f"rg:{uid}:uv"),
                     _rg_btn("❌ Cancel", f"rg:{uid}:x")])
    if back:
        rows.append(_rg_nav_row(uid, back))
    return "\n".join(lines), rows


async def rg_undo_apply(query, context, user, chat, job_id):
    """The ↩ Undo it button: only the latest move can be undone, and only once."""
    last = await asyncio.to_thread(mongo_db.get_last_move_job)
    if not last or last["id"] != job_id or not last["can_undo"]:
        await _rg_edit(query, "That code move can no longer be undone (a newer move exists, or it was already undone).")
        return
    undo_id = await asyncio.to_thread(mongo_db.create_undo_job, job_id, user.id)
    if not await rg_run_job(query, context, undo_id, "Undoing the code move"):
        return
    await _rg_edit(query, f"✅ Undone\n{last['done']} character(s) are back on their old codes and the ranges were restored.")
    await log_range_change(context, user, chat, "undocodes", f"undid the last code move ({last['done']} characters)")


async def undocodes_command(update, context):
    """/undocodes - undo the last /fillranges or range shift (PM only, with a confirmation button)."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not _rg_allowed(user.id):
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(msg, "⚠️ /undocodes can only be used in the bot's PM (private chat).")
        return
    text, rows = await rg_undo_view(user.id)
    await safe_reply_text(msg, text, reply_markup=InlineKeyboardMarkup(rows) if rows else None)


async def exportdb_command(update, context):
    """/exportdb [collection ...] - Owner only, PM only: the whole database (or the named collections) as zip file(s) of
    JSON files, sent to your PM. Nothing is stored on the bot."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not is_owner(user.id):
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(msg, "⚠️ /exportdb can only be used in the bot's PM (private chat).")
        return
    lock = context.application.bot_data.setdefault("export_lock", asyncio.Lock())
    if lock.locked():
        await safe_reply_text(msg, "⏳ An export is already running. Please wait for it to finish.")
        return
    import shutil
    import tempfile
    only = list(context.args or []) or None
    async with lock:
        await safe_reply_text(msg, "⏳ Exporting the database… this can take a minute. Please wait.")
        tmp = tempfile.mkdtemp(prefix="exportdb_")
        try:
            result = await asyncio.to_thread(mongo_db.export_database, tmp, only)
            if not result["collections"]:
                await safe_reply_text(msg, "❌ No collection matches those names. Nothing was exported.")
                return
            parts = result["parts"]
            db_name = os.getenv("MONGO_DB_NAME", "anime_bot")
            stamp = datetime.now(IST).strftime("%Y-%m-%d_%H-%M")
            for i, path in enumerate(parts, 1):
                caption = (f"Database backup {i}/{len(parts)} ({db_name}, {stamp} IST). Keep these files private and "
                           "save them outside Telegram too (for example Google Drive).")
                with open(path, "rb") as fh:
                    await context.bot.send_document(chat_id=user.id, document=fh,
                                                    filename=f"{db_name}_{stamp}_part{i}of{len(parts)}.zip",
                                                    caption=caption, write_timeout=300, read_timeout=300)
            lines = [f"✅ Export finished: {result['docs']} documents in {len(result['collections'])} collection(s), "
                     f"sent as {len(parts)} file(s).", ""]
            lines += [f"{name}: {count}" for name, count in result["collections"].items()]
            lines += ["", "The files are JSON (one document per line), so they can be read or restored later. "
                          "Save all parts before you run /fillranges."]
            for chunk in rg_chunks(lines):
                await safe_reply_text(msg, chunk)
        except Exception as e:
            print("exportdb error:", repr(e))
            await safe_reply_text(msg, "❌ The export failed. Please try again (open a private chat with me and press Start "
                                       "if you have not yet). Nothing was changed.")
        finally:
            shutil.rmtree(tmp, ignore_errors=True)


# ---------------------------------------------------------------------------------------------------
# /importdb (Owner, PM): restore from the zip parts that /exportdb produced.
#   1. /importdb [collection ...]   2. send every zip part   3. ✅ Done -> preview (nothing changed yet)
#   4. ➕ Add missing only (safe) or ♻ Replace (sends a safety copy first, then needs the word REPLACE)
# ---------------------------------------------------------------------------------------------------
IMPORT_TTL = 1800                       # the restore session expires after 30 minutes
IMPORT_MAX_DOWNLOAD = 20 * 1024 * 1024  # a bot can only download files up to 20 MB (exports are split below that)
_imp_state = {}                         # owner id -> {dir, files, only, step, exp}


def _imp_cleanup(uid):
    import shutil
    st = _imp_state.pop(uid, None)
    if st:
        shutil.rmtree(st["dir"], ignore_errors=True)


def _imp_live(uid):
    st = _imp_state.get(uid)
    if st and time.monotonic() > st["exp"]:
        _imp_cleanup(uid)
        return None
    if st:
        st["exp"] = time.monotonic() + IMPORT_TTL
    return st


def _imp_rows(uid, files):
    row = [_rg_btn("✅ Done", f"imp:{uid}:d"), _rg_btn("🗑 Clear files", f"imp:{uid}:c"), _rg_btn("❌ Cancel", f"imp:{uid}:x")]
    return [row] if files else [[_rg_btn("❌ Cancel", f"imp:{uid}:x")]]


async def importdb_command(update, context):
    """/importdb [collection ...] - Owner only, PM only. Starts a restore session; nothing changes until you confirm."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not is_owner(user.id):
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(msg, "⚠️ /importdb can only be used in the bot's PM (private chat).")
        return
    import tempfile
    _imp_cleanup(user.id)
    only = list(context.args or []) or None
    _imp_state[user.id] = {"dir": tempfile.mkdtemp(prefix="importdb_"), "files": [], "only": only, "step": "collect",
                           "exp": time.monotonic() + IMPORT_TTL, "inspected": None}
    scope = ("only: " + ", ".join(only)) if only else "every collection in the backup"
    await safe_reply_text(
        msg,
        "📥 Restore the database\n\n"
        f"Restoring {scope}.\n"
        "Send the backup .zip file(s) from /exportdb here, one after another (all parts, any order). "
        "Then tap Done. I will show what they contain before anything changes.\n\n"
        "Files must be the parts made by /exportdb (each is at most 15 MB).",
        reply_markup=InlineKeyboardMarkup(_imp_rows(user.id, False)))


async def importdb_file(update, context):
    """A .zip sent while a restore session waits for backup files."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not msg.document:
        return
    st = _imp_live(user.id)
    if not st or st["step"] != "collect" or not is_owner(user.id):
        return
    doc = msg.document
    if not (doc.file_name or "").lower().endswith(".zip"):
        await safe_reply_text(msg, "⚠️ Send the .zip files made by /exportdb.")
        return
    if doc.file_size and doc.file_size > IMPORT_MAX_DOWNLOAD:
        await safe_reply_text(msg, "⚠️ That file is bigger than 20 MB, which a bot cannot download. Export again with "
                                   "the current /exportdb (its parts are small enough).")
        return
    import zipfile
    path = os.path.join(st["dir"], f"{len(st['files']) + 1:03d}.zip")
    try:
        tg_file = await context.bot.get_file(doc.file_id)
        await tg_file.download_to_drive(path)
        if not zipfile.is_zipfile(path):
            raise ValueError("not a zip")
    except Exception as e:
        print("importdb download error:", repr(e))
        await safe_reply_text(msg, "⚠️ I could not read that file. Please send it again.")
        return
    st["files"].append(path)
    await safe_reply_text(
        msg, f"📦 Received {len(st['files'])} file(s). Send the next part, or tap Done when you have sent them all.",
        reply_markup=InlineKeyboardMarkup(_imp_rows(user.id, True)))


async def _imp_preview(query, uid, st):
    inspected = await asyncio.to_thread(mongo_db.inspect_backup, st["files"], st["only"])
    st["inspected"] = inspected
    lines = ["📥 Backup check (nothing has been changed yet)", ""]
    man = inspected["manifest"]
    if man:
        lines.append(f"Database: {man.get('database')} - exported {man.get('exported_at_ist')} IST")
    lines.append(f"Files received: {len(st['files'])}")
    lines.append("")
    if inspected["collections"]:
        lines += [f"{n}: {c} documents" for n, c in sorted(inspected["collections"].items())]
    else:
        lines.append("No collections found in these files.")
    if inspected["problems"]:
        lines += ["", "⚠️ Problems:"] + [f"- {p}" for p in inspected["problems"][:10]]
        lines += ["", "Send the missing parts (or tap Clear files and start again), then tap Done."]
        await _rg_edit(query, "\n".join(lines), _imp_rows(uid, True))
        return
    st["step"] = "mode"
    lines += ["", "Choose how to restore:",
              "➕ Add missing only: puts back documents that are gone; everything that exists stays untouched (safe).",
              "♻ Replace: makes these collections exactly like the backup. A safety copy of the current data is sent "
              "to your PM first."]
    await _rg_edit(query, "\n".join(lines),
                   [[_rg_btn("➕ Add missing only", f"imp:{uid}:m"), _rg_btn("♻ Replace", f"imp:{uid}:r"),
                     _rg_btn("❌ Cancel", f"imp:{uid}:x")]])


async def _imp_run(context, user, mode, status_edit):
    """Restore every collection of the inspected backup. status_edit(text) updates the status message."""
    st = _imp_state.get(user.id)
    inspected = st["inspected"]
    lock = context.application.bot_data.setdefault("import_lock", asyncio.Lock())
    job_lock = context.application.bot_data.get("code_job_lock")
    if lock.locked() or (job_lock is not None and job_lock.locked()):
        await status_edit("⏳ Another restore or code move is running. Wait for it to finish, then try again.")
        return
    async with lock:
        names = sorted(inspected["collections"])
        results = {}
        try:
            if mode == "replace":
                import shutil
                import tempfile
                await status_edit("⏳ Saving a safety copy of the current data first…")
                tmp = tempfile.mkdtemp(prefix="safety_")
                try:
                    safety = await asyncio.to_thread(mongo_db.export_database, tmp, names)
                    for i, path in enumerate(safety["parts"], 1):
                        with open(path, "rb") as fh:
                            await context.bot.send_document(
                                chat_id=user.id, document=fh, filename=f"safety_copy_before_restore_part{i}of{len(safety['parts'])}.zip",
                                caption="Safety copy of the current data, made before the restore. Keep it.",
                                write_timeout=300, read_timeout=300)
                finally:
                    shutil.rmtree(tmp, ignore_errors=True)
            for i, name in enumerate(names, 1):
                await status_edit(f"⏳ Restoring… {i}/{len(names)}: {name}")
                results[name] = await asyncio.to_thread(mongo_db.import_collection, name, inspected["members"][name], mode)
        except Exception as e:
            print("importdb error:", repr(e))
            done = ", ".join(results) or "none"
            await status_edit(f"❌ The restore stopped: {e}\nCollections finished: {done}.\n"
                              "Nothing else was changed. You can run /importdb again (Add missing only is safe to repeat).")
            _imp_cleanup(user.id)
            return
        lines = ["✅ Restore finished" + (" (replace)" if mode == "replace" else " (add missing only)"), ""]
        for name, r in results.items():
            lines.append(f"{name}: {r['inserted']} restored" + (f", {r['skipped']} already existed" if r["skipped"] else ""))
        lines += ["", "Restart the bot on Render now so it reloads the restored data, then check /range and a few characters."]
        await status_edit("\n".join(lines))
        _imp_cleanup(user.id)


async def importdb_callback(update, context):
    """Buttons of /importdb (Owner only, session owner only)."""
    query = update.callback_query
    user = query.from_user
    parts = (query.data or "").split(":")
    try:
        if len(parts) < 3 or not parts[1].isdigit():
            await query.answer(HELP_STALE_TEXT, show_alert=True)
            return
        uid, act = int(parts[1]), parts[2]
        if user.id != uid:
            await query.answer(NOT_YOURS_TEXT, show_alert=True)
            return
        if not is_owner(uid):
            await deny_callback(query)
            return
        st = _imp_live(uid)
        if act == "x":
            _imp_cleanup(uid)
            await query.answer()
            await _rg_edit(query, "❌ Cancelled. Nothing was changed.")
            return
        if st is None:
            await query.answer("⌛ This restore session expired. Run /importdb again.", show_alert=True)
            return
        await query.answer()
        if act == "c":
            import shutil
            shutil.rmtree(st["dir"], ignore_errors=True)
            os.makedirs(st["dir"], exist_ok=True)
            st.update(files=[], step="collect", inspected=None)
            await _rg_edit(query, "🗑 Files cleared. Send the backup .zip file(s) again.", _imp_rows(uid, False))
        elif act == "d":
            if not st["files"]:
                await _rg_edit(query, "Send the backup .zip file(s) first.", _imp_rows(uid, False))
                return
            await _rg_edit(query, "⏳ Checking the backup files…")
            await _imp_preview(query, uid, st)
        elif act == "m" and st["step"] == "mode":
            await _imp_run(context, user, "merge", lambda text: _rg_edit(query, text))
        elif act == "r" and st["step"] == "mode":
            st["step"] = "confirm"
            names = ", ".join(sorted(st["inspected"]["collections"]))
            await _rg_edit(query,
                           f"⚠️ Replace will EMPTY these collections and fill them from the backup:\n{names}\n\n"
                           "A safety copy of the current data is sent to your PM first.\n"
                           "To continue, send the word REPLACE now. Any other message is ignored - tap Cancel to stop.",
                           [[_rg_btn("❌ Cancel", f"imp:{uid}:x")]])
            st["status_msg"] = (query.message.chat_id, query.message.message_id)
        else:
            await _rg_edit(query, "That step is no longer available. Run /importdb again.")
    except Exception as e:
        print("importdb callback error:", repr(e))
        try:
            await query.answer("⚠️ Something went wrong. Please try again.", show_alert=True)
        except Exception:
            pass


async def importdb_confirm_text(update, context):
    """The word REPLACE after choosing Replace."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user:
        return
    st = _imp_state.get(user.id)
    if not st or st["step"] != "confirm":
        return
    if not is_owner(user.id) or _imp_live(user.id) is None:
        return
    if (msg.text or "").strip() != "REPLACE":
        await safe_reply_text(msg, "Send exactly REPLACE to continue, or tap Cancel.")
        return
    chat_id, message_id = st["status_msg"]
    st["step"] = "running"

    async def _status(text):
        try:
            await context.bot.edit_message_text(chat_id=chat_id, message_id=message_id, text=text)
        except Exception as e:
            if "not modified" not in str(e).lower():
                print("importdb status error:", repr(e))

    await _imp_run(context, user, "replace", _status)


async def editcode_command(update, context):
    """/editcode <current code or name> <new code> - change one normal character's code directly. Same checks as /edit
    (4 digits, the anime's code range, not already used, not spawned) and the same re-pointing of collections, favorites,
    Evolution recipes and the shop."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or not _rg_allowed(user.id):
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(msg, "⚠️ /editcode can only be used in the bot's PM (private chat).")
        return
    args = list(context.args or [])
    usage = "Usage: /editcode <current code or name> <new 4-digit code>\nExample: /editcode 0010 5001"
    if len(args) < 2:
        await safe_reply_text(msg, usage)
        return
    new_code, query = args[-1], " ".join(args[:-1]).strip()
    if not (new_code.isdigit() and len(new_code) == 4 and 1 <= int(new_code) <= 9999):
        await safe_reply_text(msg, "❌ The new code must be exactly 4 digits (0001-9999).\n\n" + usage)
        return
    character = await asyncio.to_thread(get_character, query)
    if not character:
        matches = await asyncio.to_thread(find_characters_by_name_parts, query)
        normal = [m for m in matches if not mongo_db.is_evolution_character(m[0])]
        if matches and not normal:
            await safe_reply_text(msg, "This is an Evolution character. Evolution characters are edited with /editevo.")
            return
        if len(normal) == 1:
            character = normal[0]
        elif len(normal) > 1:
            lines = [f"{m[0]} - {m[1]}" for m in normal[:10]]
            await safe_reply_text(msg, "❓ Several characters match. Use the character's code instead:\n" + "\n".join(lines))
            return
    if not character:
        await safe_reply_text(msg, "❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
        return
    old_code, name, anime = str(character[0]), character[1], character[2]
    if mongo_db.is_evolution_character(old_code):
        await safe_reply_text(msg, "This is an Evolution character. Evolution characters are edited with /editevo.")
        return
    if new_code == old_code:
        await safe_reply_text(msg, f"❌ {name} already has the code {old_code}.")
        return
    problem = await rg_code_problem(anime, new_code, exclude_code=old_code)
    if problem:
        await safe_reply_text(msg, problem)
        return
    existing = await asyncio.to_thread(get_character_by_code, new_code)
    if existing:
        await safe_reply_text(msg, f"❌ The code {new_code} is already used by {existing[1]}.")
        return
    active = context.application.bot_data.setdefault("active_spawns", {})
    if any(str(spawn.get("code")) == old_code for spawn in active.values()):
        await safe_reply_text(msg, "❌ This character is currently spawned in a group. Catch/expire that spawn before changing its code.")
        return
    try:
        changed = await asyncio.to_thread(mongo_db.change_character_code, old_code, new_code)
    except mongo_db.DuplicateKeyError:
        await safe_reply_text(msg, "❌ Update failed: that code may already exist.")
        return
    except Exception as e:
        print("Edit code error:", repr(e))
        await safe_reply_text(msg, "❌ Update failed. Please try again.")
        return
    if not changed:
        await safe_reply_text(msg, "❌ Update failed: the character no longer exists, or it is an Evolution character (use /editevo).")
        return
    try:
        await asyncio.to_thread(log_character_action, new_code, name, user, "edit")
    except Exception as e:
        print("Edit code bookkeeping error:", repr(e))
    await safe_reply_text(msg, f"✅ Code changed\n\n🎭 {name}\n📺 {anime or 'Not set'}\n🔁 {old_code} → {new_code}")
    await notify_staff_action(
        context,
        f"✏️ CHARACTER UPDATED\n🎭 {name} [{new_code}]\n📺 Anime: {anime or 'Not set'}\n🔁 Old code: {old_code}\n"
        f"👤 By: {display_user(user)}",
        actor_id=user.id,
    )
    mark_success(update)


# ---- Range Panel (button flows inside ONE message) ----------------------------------------------------
def _rg_touch(st):
    st["exp"] = time.monotonic() + RANGE_PANEL_TTL


def _rg_panel_state(query):
    """The live panel state for the tapped message, or None (expired / replaced by a newer panel / never opened)."""
    st = _rg_state.get(query.from_user.id)
    if st and query.message and st.get("msg") == query.message.message_id and time.monotonic() <= st["exp"]:
        _rg_touch(st)
        return st
    return None


def _rg_home_view(uid, st):
    role = "owner" if st["role"] == "o" else "executive"
    st["step"] = None
    text = "📏 Range Panel\n\nPick an action. Everything happens in this one message."
    buttons = [_rg_btn("➕ Set Range", f"rg:{uid}:sa:0"), _rg_btn("🗑 Delete Range", f"rg:{uid}:dl:0"),
               _rg_btn("📋 View Ranges", f"rg:{uid}:l:r:0"), _rg_btn("🔍 Search Anime", f"rg:{uid}:q"),
               _rg_btn("🆓 Free Codes", f"rg:{uid}:fl:0"), _rg_btn("➡️ Next Code", f"rg:{uid}:nl:0"),
               _rg_btn("🧩 Fill Ranges", f"rg:{uid}:fv"), _rg_btn("↩ Undo Moves", f"rg:{uid}:uv")]
    rows = _rg_grid(buttons, 4)
    rows.append(_rg_nav_row(uid, f"help:{uid}:{role}:range"))
    return text, rows


async def rg_picker_view(kind, page, uid, st):
    """Anime buttons (3 per row, paginated): sa = every anime for Set Range, dl/fl/nl = anime that have a range."""
    home = f"rg:{uid}:p:{st['role']}"
    if kind == "sa":
        names = await asyncio.to_thread(mongo_db.all_anime_names)
        title = "➕ Set Range\n\nStep 1/3: Which anime?\nPick one below, or send the anime name."
        st["step"] = "sa"
        pick = lambda h: f"rg:{uid}:sp:{h}"
    else:
        ranges = await asyncio.to_thread(mongo_db.get_ranges)
        names = sorted((r["anime_name"] for r in ranges), key=lambda n: n.casefold())
        title = {"dl": "🗑 Delete Range\n\nPick the anime:", "fl": "🆓 Free Codes\n\nPick the anime:",
                 "nl": "➡️ Next Code\n\nPick the anime:"}[kind]
        mode = {"dl": "d", "fl": "f", "nl": "n"}[kind]
        st["step"] = None
        pick = lambda h, mode=mode: f"rg:{uid}:v:{mode}:{h}:1"
    rows = []
    if not names:
        title += "\n\n" + ("No anime found yet." if kind == "sa" else "No ranges are set yet.")
    else:
        part, page, pages, _off = _rg_slice(names, page)
        rows = _rg_grid([_rg_btn(n, pick(mongo_db.anime_hash(n))) for n in part], 3)
        if pages > 1:
            rows.append(_rg_page_row(uid, f"rg:{uid}:{kind}", page, pages))
    rows.append(_rg_nav_row(uid, home))
    return title, rows


async def rg_step_view(step, st, uid, warn=""):
    """(text, rows) of the Set Range steps: ss = starting code, se = ending code, sk = confirmation."""
    anime = st["anime"]
    if step == "ss":
        cur = await asyncio.to_thread(mongo_db.get_range, anime)
        cur_line = (f"Current range: {_rg_span_sp(cur['start_code'], cur['end_code'])}\n" if cur else "No range set yet.\n")
        text = f"➕ Set Range — {anime}\n{cur_line}\nStep 2/3: Send the starting code (0001-9999)."
        back = f"rg:{uid}:sa:0"
    elif step == "se":
        text = f"➕ Set Range — {anime}\nStarting code: {_rg_fc(st['start'])}\n\nStep 3/3: Send the ending code."
        back = f"rg:{uid}:ss"
    else:
        total = st["end"] - st["start"] + 1
        text = f"➕ Set Range — please confirm\n\n{anime}: {_rg_span_sp(st['start'], st['end'])}\n({total} codes)"
        st["step"] = None
        if warn:
            text = f"{warn}\n\n{text}"
        return text, [[_rg_btn("✅ Confirm", f"rg:{uid}:sy"), _rg_btn("⬅ Back", f"rg:{uid}:se"),
                       _rg_btn("❌ Cancel", f"rg:{uid}:x")]]
    st["step"] = step
    if warn:
        text = f"{warn}\n\n{text}"
    return text, [_rg_nav_row(uid, back)]


async def rg_start_set_flow(query, uid, st, anime):
    st["anime"] = anime
    text, rows = await rg_step_view("ss", st, uid)
    await _rg_edit(query, text, rows)


async def _rg_free_codes_in_flow(query, context, uid):
    """'🔢 Show Free Codes' inside /addcharacter: the free codes of the anime chosen in this flow."""
    if not await asyncio.to_thread(can_manage_characters, uid):
        await deny_callback(query)
        return
    anime = (context.user_data.get("anime") or "").strip()
    if not anime:
        await query.answer("No anime is chosen in this flow.", show_alert=True)
        return
    chunks, _rows = await rg_detail_view("f", anime, uid, 1, None)
    await query.answer()
    for chunk in chunks:
        await context.bot.send_message(chat_id=query.message.chat_id, text=chunk)


async def range_callback(update, context):
    """Every 📏 Range button. Only the person the buttons belong to can use them; the role is checked on every tap."""
    query = update.callback_query
    user = query.from_user
    parts = (query.data or "").split(":")
    try:
        if len(parts) < 3 or not parts[1].isdigit():
            await query.answer(HELP_STALE_TEXT, show_alert=True)
            return
        uid, act = int(parts[1]), parts[2]
        if user.id != uid:
            await query.answer(NOT_YOURS_TEXT, show_alert=True)
            return
        if act == "noop":
            await query.answer()
            return
        if act == "fa":                                          # Add Character flow button (not a range feature)
            await _rg_free_codes_in_flow(query, context, uid)
            return
        if not _rg_allowed(uid):
            await deny_callback(query)
            return
        chat = query.message.chat if query.message else None
        arg = parts[3] if len(parts) > 3 else ""

        if act == "p":                                           # open the Range Panel
            if chat is None or chat.type != "private":
                await query.answer("Open the Range Panel in a private chat with the bot.", show_alert=True)
                return
            st = {"role": arg if arg in ("o", "e") else ("o" if is_owner(uid) else "e"), "step": None, "anime": "",
                  "start": None, "end": None, "chat": chat.id, "msg": query.message.message_id}
            _rg_touch(st)
            _rg_state[uid] = st
            await query.answer()
            text, rows = _rg_home_view(uid, st)
            await _rg_edit(query, text, rows)
            return

        if act == "x":                                           # Cancel
            _rg_state.pop(uid, None)
            await query.answer()
            await _rg_edit(query, "❌ Cancelled.")
            return

        if act == "sr":                                          # 'Set Range' button under 'No range set for X'
            if chat is None or chat.type != "private":
                await query.answer("Use the Range Panel in a private chat with the bot to set a range.", show_alert=True)
                return
            name = await asyncio.to_thread(mongo_db.anime_by_hash, arg)
            if name is None:
                await query.answer("That anime no longer exists.", show_alert=True)
                return
            st = {"role": "o" if is_owner(uid) else "e", "step": None, "anime": name, "start": None, "end": None,
                  "chat": chat.id, "msg": query.message.message_id}
            _rg_touch(st)
            _rg_state[uid] = st
            await query.answer()
            await rg_start_set_flow(query, uid, st, name)
            return

        if act in ("sa", "sp", "ss", "se", "sy", "q", "dl", "fl", "nl"):     # steps that need a live panel
            st = _rg_panel_state(query)
            if st is None:
                await query.answer("⌛ This panel expired or was replaced. Open it again from /help → Range.", show_alert=True)
                return
            await query.answer()
            if act in ("sa", "dl", "fl", "nl"):
                text, rows = await rg_picker_view(act, int(arg) if arg.isdigit() else 0, uid, st)
                await _rg_edit(query, text, rows)
            elif act == "sp":
                name = await asyncio.to_thread(mongo_db.anime_by_hash, arg)
                if name is None:
                    await _rg_edit(query, "That anime no longer exists.", [_rg_nav_row(uid, f"rg:{uid}:sa:0")])
                    return
                await rg_start_set_flow(query, uid, st, name)
            elif act in ("ss", "se"):
                if act == "se" and st.get("start") is None:
                    act = "ss"
                text, rows = await rg_step_view(act, st, uid)
                await _rg_edit(query, text, rows)
            elif act == "q":
                st["step"] = "q"
                await _rg_edit(query, "🔍 Search Anime\n\nSend the anime name (or part of it).",
                               [_rg_nav_row(uid, f"rg:{uid}:p:{st['role']}")])
            elif act == "sy":
                if not (st.get("anime") and st.get("start") and st.get("end")):
                    await _rg_edit(query, "⚠️ Something is missing. Please start again.", [_rg_nav_row(uid, f"rg:{uid}:sa:0")])
                    return
                ok, text, rows = await rg_do_set(context, user, chat, st["anime"], st["start"], st["end"])
                if ok:
                    st["step"] = None
                    await _rg_edit(query, text, rows or [[_rg_btn("📏 Panel", f"rg:{uid}:p:{st['role']}")]])
                else:
                    await _rg_edit(query, text, rows or [_rg_nav_row(uid, f"rg:{uid}:se")])
            return

        if act == "l":                                           # numbered list page: l:<kind>:<page>
            kind = arg if arg in ("r", "f", "n") else "r"
            page = int(parts[4]) if len(parts) > 4 and parts[4].isdigit() else 0
            st = _rg_panel_state(query)
            text, markup = await rg_list_view(kind, page, uid, f"rg:{uid}:p:{st['role']}" if st else None)
            await query.answer()
            await _rg_edit(query, text, [list(r) for r in markup.inline_keyboard] if markup else None)
            return

        if act == "v":                                           # one anime: v:<mode>:<hash>:<count>
            mode = arg if arg in ("r", "f", "n", "d") else "r"
            name = await asyncio.to_thread(mongo_db.anime_by_hash, parts[4] if len(parts) > 4 else "")
            if name is None:
                await query.answer("That anime no longer exists.", show_alert=True)
                return
            count = int(parts[5]) if len(parts) > 5 and parts[5].isdigit() else 1
            st = _rg_panel_state(query)
            back = None
            if st:
                back = {"f": f"rg:{uid}:fl:0", "n": f"rg:{uid}:nl:0", "d": f"rg:{uid}:dl:0", "r": f"rg:{uid}:q"}[mode]
            chunks, rows = await rg_detail_view(mode, name, uid, count, back)
            await query.answer()
            await rg_show(query, context, chunks, rows)
            return

        if act == "dd":                                          # confirmed delete: dd:<hash>
            name = await asyncio.to_thread(mongo_db.anime_by_hash, arg)
            st = _rg_panel_state(query)
            if name is None:
                await query.answer("That anime no longer exists.", show_alert=True)
                return
            text = await rg_do_delete(context, user, chat, name)
            await query.answer()
            await _rg_edit(query, text, [[_rg_btn("⬅ Back", f"rg:{uid}:dl:0")]] if st else None)
            return

        if act in ("fv", "fy"):                                  # /fillranges preview and apply: fv|fy[:<anime hash>]
            if chat is None or chat.type != "private":
                await query.answer("Use Fill Ranges in a private chat with the bot.", show_alert=True)
                return
            await query.answer()
            if act == "fv":
                only = await asyncio.to_thread(mongo_db.anime_by_hash, arg) if arg else None
                st = _rg_panel_state(query)
                chunks, rows = await rg_fill_view(uid, context, only, f"rg:{uid}:p:{st['role']}" if st else None)
                await rg_show(query, context, chunks, rows)
            else:
                await rg_fill_apply(query, context, user, chat, arg)
            return

        if act == "xs":                                          # shift the following ranges: xs:<hash>:<start>:<end>
            if len(parts) < 6 or not (parts[4].isdigit() and parts[5].isdigit()):
                await query.answer(HELP_STALE_TEXT, show_alert=True)
                return
            await query.answer()
            await rg_extend_apply(query, context, user, chat, arg, int(parts[4]), int(parts[5]))
            return

        if act in ("uv", "uy"):                                  # undo the last code move: uv = view, uy:<job id> = undo it
            if chat is None or chat.type != "private":
                await query.answer("Use Undo in a private chat with the bot.", show_alert=True)
                return
            await query.answer()
            if act == "uv":
                st = _rg_panel_state(query)
                text, rows = await rg_undo_view(uid, f"rg:{uid}:p:{st['role']}" if st else None)
                await _rg_edit(query, text, rows)
            else:
                await rg_undo_apply(query, context, user, chat, arg)
            return

        if act == "jr":                                          # continue a stopped job
            await query.answer()
            await rg_resume_job(query, context, user, chat, arg)
            return

        if act in ("mp", "mc", "mk"):                            # after a range moved: mp:<hash>:<old start>:<old end>
            if len(parts) < 6 or not (parts[4].isdigit() and parts[5].isdigit()):
                await query.answer(HELP_STALE_TEXT, show_alert=True)
                return
            await query.answer()
            await rg_move_decision(query, context, user, chat, act, arg, int(parts[4]), int(parts[5]))
            return

        await query.answer(HELP_STALE_TEXT, show_alert=True)
    except Exception as e:
        print("Range callback error:", repr(e))
        try:
            await query.answer("⚠️ Something went wrong. Please try again.", show_alert=True)
        except Exception:
            pass


async def range_panel_input(update, context):
    """A typed message while the Range Panel waits for one (anime name, starting code, ending code, search).
    Does nothing unless this user's panel is waiting; the message is deleted again so the panel stays one tab."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user:
        return
    st = _rg_state.get(user.id)
    if not st or st.get("step") not in _RG_TEXT_STEPS:
        return
    if time.monotonic() > st["exp"] or not _rg_allowed(user.id):
        _rg_state.pop(user.id, None)
        return
    uid, step = user.id, st["step"]
    _rg_touch(st)
    text = " ".join((msg.text or "").split())
    warn, view = "", None
    if step == "sa":
        if not text or len(text) > 60:
            warn, view = "⚠️ Send an anime name (up to 60 characters).", await rg_picker_view("sa", 0, uid, st)
        else:
            st["anime"] = await asyncio.to_thread(mongo_db.canonical_anime_name, text)
            view = await rg_step_view("ss", st, uid)
    elif step == "ss":
        code = mongo_db.parse_code(text)
        if code is None:
            view = await rg_step_view("ss", st, uid, "⚠️ Send a code from 0001 to 9999.")
        else:
            st["start"] = code
            view = await rg_step_view("se", st, uid)
    elif step == "se":
        code = mongo_db.parse_code(text)
        if code is None:
            view = await rg_step_view("se", st, uid, "⚠️ Send a code from 0001 to 9999.")
        elif code < st["start"]:
            view = await rg_step_view("se", st, uid, f"⚠️ The ending code must not be smaller than {_rg_fc(st['start'])}.")
        else:
            other = await asyncio.to_thread(mongo_db.find_overlap, st["anime"], st["start"], code)
            existing = await asyncio.to_thread(mongo_db.get_range, st["anime"])
            if other and existing is not None and st["start"] == existing["start_code"] and code > existing["end_code"]:
                other = None                                   # extending an existing range: the shift is offered at Confirm
            if other:
                view = await rg_step_view("se", st, uid,
                                          f"⚠️ {_rg_span(st['start'], code)} overlaps with {other['anime_name']} "
                                          f"({_rg_span(other['start_code'], other['end_code'])}).")
            else:
                st["end"] = code
                view = await rg_step_view("sk", st, uid)
    else:                                                          # q: search
        if not text:
            return
        st["step"] = None
        chunks, rows = await rg_lookup_view("r", text, uid, 1, f"rg:{uid}:q")
        view = ("\n".join(chunks), rows)
        st["step"] = "q"
    if warn and view:
        view = (f"{warn}\n\n{view[0]}", view[1])
    try:
        await msg.delete()
    except Exception:
        pass
    if view is None:
        return
    try:
        await context.bot.edit_message_text(chat_id=st["chat"], message_id=st["msg"], text=view[0],
                                            reply_markup=InlineKeyboardMarkup(view[1]) if view[1] else None)
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            print("Range panel edit error:", repr(e))
            sent = await safe_reply_text(msg, view[0], reply_markup=InlineKeyboardMarkup(view[1]) if view[1] else None)
            if sent is not None and getattr(sent, "message_id", None):
                st["msg"] = sent.message_id


async def _cw_hub(role, uid):
    """(text, keyboard) of the 💰 Change Worth screen: every rarity with its current default worth."""
    values = await asyncio.to_thread(lambda: {r: default_worth(r) for r in CW_RARITIES})
    lines = ["💰 Change Worth", "", "Default worth of each rarity (used by /addcharacter and /edit):"]
    lines += [f"{SYMBOL[r]} {r}: {values[r]}" for r in CW_RARITIES]
    lines += ["", "Tap a rarity to change its default.", "Characters that already exist keep their current worth."]
    buttons = [InlineKeyboardButton(f"{SYMBOL[r]} {r}", callback_data=f"cw:{uid}:{role}:r:{r}") for r in CW_RARITIES]
    rows = [buttons[i:i + 3] for i in range(0, len(buttons), 3)]
    rows.append([InlineKeyboardButton("« Back", callback_data=f"help:{uid}:{role}:addedit")])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


async def change_worth_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Buttons of 💰 Change Worth (Owner and Executive only; the role is checked again on every tap)."""
    query = update.callback_query
    parts = (query.data or "").split(":")
    user = query.from_user
    try:
        if len(parts) < 4 or not parts[1].isdigit():
            await query.answer(HELP_STALE_TEXT, show_alert=True)
            return
        menu_owner, role, action = int(parts[1]), parts[2], parts[3]
        if user.id != menu_owner:
            await query.answer(NOT_YOURS_TEXT, show_alert=True)
            return
        if role not in ("owner", "executive") or not await help_role_allowed(role, user.id):
            await deny_callback(query)
            return
        if action == "hub":
            await query.answer()
            _cw_waiting.pop(user.id, None)
            text, markup = await _cw_hub(role, user.id)
            await _edit_help_message(query, text, markup)
        elif action == "r" and len(parts) > 4 and parts[4] in CW_RARITIES:
            rarity = parts[4]
            current = await default_worth_async(rarity)
            _cw_waiting[user.id] = (rarity, role, time.monotonic() + CW_INPUT_TIMEOUT)
            await query.answer("Send the number in the chat")
            await context.bot.send_message(
                chat_id=user.id,
                text=(f"💰 The current default worth of {rarity} is {current}.\n\n"
                      "Send the new default worth now (a whole number). Send /cancel to stop."))
        else:
            await query.answer()
    except Exception as e:
        print("Change worth callback error:", repr(e))
        try:
            await query.answer("⚠️ Something went wrong. Please try again.", show_alert=True)
        except Exception:
            pass


async def change_worth_input(update, context):
    """The number sent after choosing a rarity in 💰 Change Worth. Does nothing unless the bot is waiting for it."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user or user.id not in _cw_waiting:
        return
    rarity, role, expiry = _cw_waiting[user.id]
    if time.monotonic() > expiry or not await help_role_allowed(role, user.id):
        _cw_waiting.pop(user.id, None)
        return
    text = (msg.text or "").strip()
    if not re.fullmatch(r"[0-9]{1,8}", text) or int(text) > DEFAULT_WORTH_MAX:
        await safe_reply_text(msg, f"⚠️ Send a whole number from 0 to {DEFAULT_WORTH_MAX}, or /cancel.")
        return
    value = int(text)
    try:
        await asyncio.to_thread(set_default_worth, rarity, value, user.id)
    except Exception as e:
        print("Change worth save error:", repr(e))
        await safe_reply_text(msg, "⚠️ Could not save the number. Please send it again, or /cancel.")
        return
    _cw_waiting.pop(user.id, None)
    await safe_reply_text(msg, f"✅ The default worth of {rarity} is now {value}.\nCharacters that already exist keep their current worth.")
    hub_text, hub_markup = await _cw_hub(role, user.id)
    await safe_reply_text(msg, hub_text, reply_markup=hub_markup)


async def help_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    parts = (query.data or "").split(":")
    user_id = query.from_user.id

    try:
        # Old-format buttons (no owner id) can no longer be attributed to anyone.
        if len(parts) < 3 or not parts[1].isdigit():
            await query.answer(HELP_STALE_TEXT, show_alert=True)
            return
        menu_owner, action = int(parts[1]), parts[2]
        key = parts[3] if len(parts) > 3 else ""

        # Menu ownership: only the user who ran /help may press its buttons.
        if user_id != menu_owner:
            if action in HELP_MODULES:               # someone else poking at a restricted panel: security log
                await log_security_denial(context.application, query.from_user,
                                          query.message.chat if query.message else None,
                                          "restricted button", f"help:{action}{(':' + key) if key else ''} (not menu owner)")
            await query.answer(NOT_YOURS_TEXT, show_alert=True)
            return

        if action in ("open", "back"):
            await query.answer()
            await _edit_help_message(query, build_help_text(), (await asyncio.to_thread(staff_help_keyboard, user_id)))
            return

        if action in HELP_MODULES:
            # Role is verified again on every tap: a stale button must never open a panel the user cannot use.
            if not await help_role_allowed(action, user_id):
                await deny_callback(query)
                return
            detail = help_detail(action, key, user_id) if key else None
            if detail is None:                       # panel grid (also used for old numeric page buttons)
                text, markup = help_grid_text(action), help_grid_keyboard(action, user_id)
            else:
                text, markup = detail
            chat = query.message.chat if query.message else None
            if chat is not None and chat.type != "private":
                # Restricted panels never open in a group: they are sent to the user's private chat instead.
                try:
                    await context.bot.send_message(chat_id=user_id, text=text[:4000], reply_markup=markup)
                except (Forbidden, BadRequest):     # user never pressed Start / blocked the bot
                    await query.answer(HELP_PM_START_TEXT, show_alert=True)
                    return
                await query.answer("📩 Opened in your private chat.")
                return
            await query.answer()
            await _edit_help_message(query, text, markup)
            return
        await query.answer(HELP_STALE_TEXT, show_alert=True)     # unknown action = outdated menu
    except Exception as e:
        print("Help button error:", repr(e))
        try:
            await query.answer("⚠️ Help could not be opened. Please use /help.", show_alert=True)
        except Exception:
            pass

def is_group_chat(update):
    chat = getattr(update, "effective_chat", None)
    return bool(chat and chat.type in ("group", "supergroup"))

async def require_group_spawn(update):
    if is_group_chat(update):
        return True
    if getattr(update, "message", None):
        await safe_reply_text(update.message,
            "🚫 Character spawning works only in groups.\n"
            "➜ Add me to a group and use /spawn there."
        )
    return False

async def spawn(update, context):
    (await save_user_async(update.effective_user))
    if not await require_group_spawn(update):
        return
    chat_id = update.effective_chat.id
    user_id = update.effective_user.id
    if await asyncio.to_thread(group_spawn_flag, chat_id, "spawn_off"):
        await safe_reply_text(update.message, "🚫 The /spawn command is turned off in this group.")
        return
    active = context.application.bot_data.setdefault("active_spawns", {})

    if chat_id in active:
        await safe_reply_text(
            update.message,
            "❌ A character is already spawned in this chat.\nUse /add to catch it first.",
        )
        return

    if not await bot_is_group_admin(context.bot, context.application, chat_id):
        warned = context.application.bot_data.setdefault("admin_spawn_warned", {})
        if time.monotonic() - warned.get(chat_id, -9999.0) > 600:      # at most one reminder per group per 10 minutes
            warned[chat_id] = time.monotonic()
            await safe_reply_text(update.message, BOT_ADMIN_SPAWN_TEXT)
        return

    now_dt = datetime.now()
    last_calls = context.application.bot_data.setdefault("last_calls", {})
    personal_remaining = personal_spawn_cooldown(user_id, chat_id) - (now_dt - last_calls[user_id]).total_seconds() if user_id in last_calls else 0
    if personal_remaining > 0:
        await safe_reply_text(
            update.message,
            f"⏳ Your /spawn cooldown is active.\nTry again in <b>{format_duration(personal_remaining)}</b>.",
            parse_mode="HTML",
        )
        return

    group_cooldowns = context.application.bot_data.setdefault("chat_spawn_cooldowns", {})
    group_remaining = ((group_cooldowns[chat_id] - now_dt).total_seconds()
                       if chat_id in group_cooldowns else 0)
    if group_remaining > 0:
        await safe_reply_text(
            update.message,
            f"⏳ This chat's /spawn cooldown is active.\nTry again in <b>{format_duration(group_remaining)}</b>.",
            parse_mode="HTML",
        )
        return

    character = (await asyncio.to_thread(choose_character, chat_id, app=context.application, require_photo=True))
    if character is None:
        character = (await asyncio.to_thread(_choose_unlimited_fallback_character, chat_id=chat_id, require_photo=True))
    if character is None:
        await safe_reply_text(update.message, "❌ No character with a photo is available to spawn right now.")
        return

    success = False
    photo_failed = False
    excluded = set()
    for _ in range(5):
        try:
            success, spawn_msg = await spawn_reserved(chat_id, context, character, "manual_spawn")
            if success:
                break
            if spawn_msg == SPAWN_PHOTO_MISSING_TEXT:      # first failure for this character: tell the user once
                photo_failed = True
                await safe_reply_text(update.message, SPAWN_PHOTO_MISSING_TEXT)
                break
        except Exception as e:
            print("Manual spawn error:", e)
        excluded.add(str(character[0]))
        character = (await asyncio.to_thread(choose_character, chat_id, excluded_codes=excluded, app=context.application, require_photo=True))
        if character is None:
            character = (await asyncio.to_thread(_choose_unlimited_fallback_character, excluded, chat_id, require_photo=True))
        if character is None:
            break
        await asyncio.sleep(0.3)
    else:
        success = False

    if photo_failed:
        return                                              # nothing else is sent; no cooldown is consumed
    if not success:
        await safe_reply_text(update.message, "❌ The spawn could not be completed. Please try again.")
        return
    mark_success(update)
    await rewards.task_hook(context.bot, user_id, "spawn", name=berry_display_name(update.effective_user))     # invite friend task (never raises)

    last_calls = context.application.bot_data.setdefault("last_calls", {})
    last_calls[user_id] = datetime.now()
    context.application.bot_data.setdefault("active_chats", set()).add(chat_id)
    context.application.bot_data.setdefault("next_auto_spawn_at", {})[chat_id] = (
        datetime.now() + timedelta(seconds=AUTO_SPAWN_INTERVAL)
    )

async def build_cooldown_text(app, chat_id, user_id, title=None, personal=True):
    now_dt = datetime.now()

    # Current character life for this exact group.
    active = app.bot_data.setdefault("active_spawns", {}).get(chat_id)
    life_text = "No character currently spawned"
    if active:
        expires = active.get("expires_at")
        try:
            sec = max(0, (expires - now_dt).total_seconds())
            life_text = f"{html_escape(str(active.get('name', active.get('code', 'Unknown'))))} — {format_duration(sec)} remaining"
        except Exception:
            life_text = "Character currently spawned"

    # Personal and group /spawn cooldowns.
    last_calls = app.bot_data.setdefault("last_calls", {})
    personal_remaining = (personal_spawn_cooldown(user_id, chat_id) - (now_dt - last_calls[user_id]).total_seconds()
                          if user_id in last_calls else 0)
    personal_text = format_duration(personal_remaining) if personal_remaining > 0 else "Ready"

    group_until = app.bot_data.setdefault("chat_spawn_cooldowns", {}).get(chat_id)
    group_remaining = (group_until - now_dt).total_seconds() if group_until else 0
    group_text = format_duration(group_remaining) if group_remaining > 0 else "Ready"

    # Next auto-spawn for this exact group.
    next_auto = app.bot_data.setdefault("next_auto_spawn_at", {}).get(chat_id)
    if next_auto is None:
        auto_text = "not scheduled yet"
    else:
        try:
            auto_text = format_duration(max(0, (next_auto - now_dt).total_seconds()))
        except Exception:
            auto_text = "not scheduled yet"

    recent = []
    try:
        _recent_rows = (await asyncio.to_thread(mongo_db.sh_chat_recent, chat_id, 10))
        _recent_names = (await asyncio.to_thread(mongo_db.get_character_names, [r[0] for r in _recent_rows]))
        recent = [(code, _recent_names.get(str(code)), rarity, spawned_at) for code, rarity, spawned_at in _recent_rows]
    except Exception as e:
        print("Cooldown character lookup error:", e)

    rows = []
    for code, name, rarity, spawned_at in recent:
        try:
            dt = datetime.fromisoformat(str(spawned_at))
            if dt.tzinfo is None and now_dt.tzinfo is not None:
                dt = dt.replace(tzinfo=now_dt.tzinfo)
            sec = (dt + timedelta(seconds=SPAWN_LIFETIME) - now_dt).total_seconds()
            if sec > 0:
                rows.append(f"• {html_escape(str(name or code))} [{html_escape(str(rarity or 'Unknown'))}] — <b>free in {format_duration(sec)}</b>")
        except Exception:
            continue

    text = (f"⏳ <b>{html_escape(title) if title else 'Spawn Cooldown'}</b>\n\n"
            f"🤖 Auto Spawn: <b>{auto_text}</b>\n"
            f"❤️ Character Life: <b>{html_escape(life_text)}</b>\n"
            + (f"👤 Your /spawn: <b>{personal_text}</b>\n" if personal else "")
            + f"🏠 Group /spawn: <b>{group_text}</b>\n\n"
            "🎴 <b>Character Cooldowns</b>\n")
    text += "\n".join(rows) if rows else "• No character is currently on cooldown. All characters are eligible."
    return text

SILENT_OWNER_COMMANDS = {"cooldown", "cd"}   # Owner only; anyone else is ignored completely (no reply at all)


def cooldown_refresh_markup(target):
    return InlineKeyboardMarkup([[InlineKeyboardButton("🔄 Refresh", callback_data=f"cd:r:{target}")]])


async def build_cooldown_chunks(app, user_id, target):
    """HTML text chunks for /cooldown. target = 'all' (PM overview) or a group chat id."""
    if target != "all":
        return [await build_cooldown_text(app, int(target), user_id)]
    # PM overview: your own /spawn cooldown + the cooldowns and character life of groups with an active spawn.
    groups = (await asyncio.to_thread(load_bot_groups)) or {}
    now_dt = datetime.now()
    last = app.bot_data.setdefault("last_calls", {}).get(user_id)
    rem = (personal_spawn_cooldown(user_id) - (now_dt - last).total_seconds()) if last else 0
    blocks = [f"⏳ <b>All Cooldowns</b>\n\n👤 Your /spawn: <b>{format_duration(rem) if rem > 0 else 'Ready'}</b>"]
    if not groups:
        blocks.append("No groups registered yet.")
    active_spawns = app.bot_data.setdefault("active_spawns", {})
    shown = 0
    for gid, info in groups.items():
        if not str(gid).lstrip("-").isdigit():
            continue
        if int(gid) not in active_spawns:
            continue  # only groups with an active spawned character
        shown += 1
        gtitle = (info or {}).get("title") or (info or {}).get("username") or f"Group {gid}"
        try:
            blocks.append(await build_cooldown_text(app, int(gid), user_id, title=f"{gtitle} ({gid})", personal=False))
        except Exception as e:
            print("Cooldown overview error:", e)
    if groups and not shown:
        blocks.append("No group has an active character spawn right now.")
    chunks = []
    chunk = ""
    for block in blocks:
        if chunk and len(chunk) + len(block) + 2 > 3900:
            chunks.append(chunk)
            chunk = ""
        chunk = f"{chunk}\n\n{block}" if chunk else block
    if chunk:
        chunks.append(chunk)
    return chunks


async def cooldown(update, context):
    """Show a group's auto-spawn/life state and character cooldowns (/cooldown or /cd; Owner only, anyone else is ignored)."""
    if not is_owner(update.effective_user.id):
        return
    user_id = update.effective_user.id
    if is_group_chat(update):
        target = str(update.effective_chat.id)
    else:
        arg = (context.args[0] if getattr(context, "args", None) else "").strip()
        target = str(int(arg)) if arg.lstrip("-").isdigit() else "all"
    chunks = await build_cooldown_chunks(context.application, user_id, target)
    for i, chunk in enumerate(chunks):
        await safe_reply_text(update.message, chunk, parse_mode="HTML",
                              reply_markup=cooldown_refresh_markup(target) if i == len(chunks) - 1 else None)


async def cooldown_refresh_callback(update, context):
    """🔄 Refresh button of /cooldown: rebuilds the status in place. Anyone but the Owner is ignored silently."""
    query = update.callback_query
    if not is_owner(query.from_user.id):
        try:
            await query.answer()
        except Exception:
            pass
        return
    target = (query.data or "")[len("cd:r:"):]
    try:
        chunks = await build_cooldown_chunks(context.application, query.from_user.id, target)
        if len(chunks) != 1:
            await query.answer("Too many groups to refresh in one message. Send /cooldown again.", show_alert=True)
            return
        first = (getattr(query.from_user, "first_name", None) or "").strip()
        last = (getattr(query.from_user, "last_name", None) or "").strip()
        name = " ".join(p for p in (first, last) if p) or "Unknown"
        await query.edit_message_text(f"👤 {html_escape(name)}\n\n{chunks[0]}", parse_mode="HTML",
                                      reply_markup=cooldown_refresh_markup(target))
        await query.answer("🔄 Refreshed")
    except BadRequest as e:
        if "not modified" in str(e).lower():
            await query.answer("✅ Already up to date")
        else:
            print("Cooldown refresh error:", e)
            await query.answer("⚠️ Could not refresh. Send /cooldown again.", show_alert=True)
    except Exception as e:
        print("Cooldown refresh error:", e)
        try:
            await query.answer("⚠️ Could not refresh. Send /cooldown again.", show_alert=True)
        except Exception:
            pass

async def clearspawn(update, context):
    (await save_user_async(update.effective_user))
    if not await require_group_spawn(update):
        return

    if not (is_owner(update.effective_user.id) or is_executive(update.effective_user.id) or (await asyncio.to_thread(is_scout, update.effective_user.id))):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return

    chat_id = update.effective_chat.id
    lock = get_spawn_lock(context.application)
    async with lock:
        active = context.application.bot_data.setdefault("active_spawns", {})
        spawn = active.pop(chat_id, None)
        if not spawn:
            await safe_reply_text(update.message, "ℹ️ There is no active character spawn in this group.")
            return
        await cancel_spawn_expiry_task(spawn)
        await asyncio.to_thread(mark_spawn_expiry_notified, spawn.get("history_id"))

    await safe_delete_message(context.bot, chat_id, spawn.get("message_id"))
    context.application.bot_data.setdefault("next_auto_spawn_at", {})[chat_id] = (
        datetime.now() + timedelta(seconds=AUTO_SPAWN_INTERVAL)
    )
    await safe_reply_text(update.message,
        "🧹 Active character spawn cleared successfully.\n"
        f"🎭 Character: {spawn.get('name', 'Unknown')}\n"
        "⏳ Next automatic character will spawn after 30 minutes."
    )

CALLCHAR_CHARACTER, CALLCHAR_GROUP = range(600, 602)

def character_selection_keyboard(user_id, action, rows):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(f"{name} [{code}]", callback_data=f"charselect:{action}:{user_id}:{code}")]
        for code, name, anime, rarity, worth, photo in list(rows)[:99]   # Telegram allows at most 100 buttons
    ])

ANIME_PAGE_SIZE = 20
_ANIME_PAGES = {}   # token -> {"uid", "action", "rows", "title"}; kept in memory, oldest dropped first

def parse_anime_query(query):
    """'(Naruto)' or '[Naruto]' -> 'Naruto'.  Anything else -> None (normal character-name search)."""
    m = re.fullmatch(r"\s*[\(\[]\s*(.+?)\s*[\)\]]\s*", query or "")
    return m.group(1) if m else None

def anime_page_markup(token, page):
    data = _ANIME_PAGES.get(token)
    if not data:
        return None
    rows, uid, action = data["rows"], data["uid"], data["action"]
    pages = max(1, (len(rows) + ANIME_PAGE_SIZE - 1) // ANIME_PAGE_SIZE)
    page = max(0, min(page, pages - 1))
    chunk = rows[page * ANIME_PAGE_SIZE:(page + 1) * ANIME_PAGE_SIZE]
    keyboard = [
        [InlineKeyboardButton(f"{name} [{code}]", callback_data=f"charselect:{action}:{uid}:{code}")]
        for code, name, anime, rarity, worth, photo in chunk
    ]
    if pages > 1:
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton("⬅️ Back", callback_data=f"charpage:{token}:{page - 1}"))
        nav.append(InlineKeyboardButton(f"{page + 1}/{pages}", callback_data=f"charpage:{token}:{page}"))
        if page < pages - 1:
            nav.append(InlineKeyboardButton("Next ➡️", callback_data=f"charpage:{token}:{page + 1}"))
        keyboard.append(nav)
    return InlineKeyboardMarkup(keyboard)

def _owned_character_codes(user_id):
    return {str(c) for c in mongo_db.col(mongo_db.COLLECTIONS).distinct("character_code", {"user_id": int(user_id)})}

async def reply_anime_character_list(update, action, anime_query, owned_only=False):
    """Handles /check (Anime) and /view (Anime). Returns the single character if only one matches, else None.
    owned_only=True (/view): list only the characters the user owns."""
    rows = list(await asyncio.to_thread(mongo_db.find_characters_by_anime, anime_query))
    if not rows:
        await safe_reply_text(update.message, "❌ Anime not found.")
        return None
    if owned_only:
        owned = await asyncio.to_thread(_owned_character_codes, update.effective_user.id)
        rows = [r for r in rows if str(r[0]) in owned]
        if not rows:
            await safe_reply_text(update.message, "❌ You don't own any characters from this anime.")
            return None
    if len(rows) == 1:
        return rows[0]
    token = uuid.uuid4().hex[:8]
    _ANIME_PAGES[token] = {"uid": update.effective_user.id, "action": action, "rows": rows}
    while len(_ANIME_PAGES) > 300:
        _ANIME_PAGES.pop(next(iter(_ANIME_PAGES)))
    await safe_reply_text(
        update.message,
        f"📺 {len(rows)} characters found for \"{anime_query}\". Select one:",
        reply_markup=anime_page_markup(token, 0),
    )
    return None

async def character_page_callback(update, context):
    query = update.callback_query
    parts = (query.data or "").split(":")
    if len(parts) != 3 or parts[0] != "charpage":
        await query.answer()
        return
    token = parts[1]
    data = _ANIME_PAGES.get(token)
    if not data:
        await query.answer("⚠️ This list is outdated. Please run the command again.", show_alert=True)
        return
    if query.from_user.id != data["uid"]:
        await query.answer("❌ This selection belongs to another user.", show_alert=True)
        return
    try:
        page = int(parts[2])
    except ValueError:
        await query.answer()
        return
    await query.answer()
    try:
        await query.edit_message_reply_markup(reply_markup=anime_page_markup(token, page))
    except Exception:
        pass   # same page tapped again: Telegram says "message is not modified"

async def character_selection_callback(update, context):
    query = update.callback_query
    parts = (query.data or "").split(":", 3)
    if len(parts) != 4 or parts[0] != "charselect":
        await query.answer()
        return
    try:
        action, owner_id, code = parts[1], int(parts[2]), parts[3]
    except ValueError:
        await query.answer("⚠️ This selection is outdated. Please run the command again.", show_alert=True)
        return
    if query.from_user.id != owner_id:
        await query.answer("❌ This selection belongs to another user.", show_alert=True)
        return
    character = (await asyncio.to_thread(get_character_by_code, code))
    if not character:
        await query.answer("❌ Character no longer exists.", show_alert=True)
        return
    # Re-check the role at tap time: the menu may have been opened before the user's role was revoked.
    if action == "callchar" and not is_owner(query.from_user.id):
        await deny_callback(query)
        return
    if action == "edit" and not (await asyncio.to_thread(can_manage_characters, query.from_user.id)):
        await deny_callback(query)
        return
    await query.answer()
    if action == "callchar":
        context.user_data["callchar_character_query"] = code
        await query.edit_message_text("2️⃣ Send the target Group ID:")
        return CALLCHAR_GROUP
    if action == "check":
        await send_character_check_result(context.bot, query.message.chat_id, character, query.message)
        return
    if action == "view":
        # header should show the person who tapped, not the bot that owns the button message
        who = _NS(from_user=query.from_user)
        await send_character_view_result(context.bot, query.message.chat_id, query.from_user.id, character, who)
        return
    if action == "edit":
        if await asyncio.to_thread(mongo_db.is_evolution_character, code):   # normal characters only
            await query.edit_message_text(f"{mongo_db.evolution_mark(code)} This is an Evolution character. Evolution characters are edited with /editevo.")
            return ConversationHandler.END
        context.user_data["edit_code_original"] = code
        context.user_data["edit_character"] = character
        await query.edit_message_text(
            f"✏️ Editing {character[1]} [{character[0]}]\n\n"
            "1️⃣ Send new character name, or tap ⏭ Skip to keep current."
            f"\nCurrent: {character[1]}",
            reply_markup=skip_keyboard(),
        )
        return EDIT_NAME

async def callchar_start(update, context):
    (await save_user_async(update.effective_user))
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return ConversationHandler.END
    if update.effective_chat.type in ("group", "supergroup"):
        return await callchar(update, context)
    if context.args:
        context.user_data["callchar_character_query"] = " ".join(context.args).strip()
        await safe_reply_text(update.effective_message, "2️⃣ Send the target Group ID:")
        return CALLCHAR_GROUP
    await safe_reply_text(update.effective_message, "1️⃣ Send character 4-digit code or character name:")
    return CALLCHAR_CHARACTER

async def callchar_character_step(update, context):
    if not is_owner(update.effective_user.id):
        return ConversationHandler.END
    text = (update.effective_message.text or "").strip()
    if not text:
        await safe_reply_text(update.effective_message, "❌ Send a character code or name:")
        return CALLCHAR_CHARACTER
    matches = (await asyncio.to_thread(find_characters_by_name_parts, text))
    if len(matches) > 1:
        await safe_reply_text(
            update.effective_message,
            "❓ Multiple characters found. Select one:",
            reply_markup=character_selection_keyboard(update.effective_user.id, "callchar", matches),
        )
        return CALLCHAR_CHARACTER
    if not matches:
        recruit_matches = (await asyncio.to_thread(find_characters_by_recruit_name_partial, text))
        if len(recruit_matches) > 1:
            await safe_reply_text(
                update.effective_message,
                "❓ Multiple characters found. Select one:",
                reply_markup=character_selection_keyboard(update.effective_user.id, "callchar", recruit_matches),
            )
            return CALLCHAR_CHARACTER
    context.user_data["callchar_character_query"] = text
    await safe_reply_text(update.effective_message, "2️⃣ Send the target Group ID:")
    return CALLCHAR_GROUP

async def callchar_group_step(update, context):
    if not is_owner(update.effective_user.id):
        return ConversationHandler.END
    text = (update.effective_message.text or "").strip()
    if not re.fullmatch(r"-?\d+", text):
        await safe_reply_text(update.effective_message, "❌ Group ID must be numeric (example: -1001234567890). Send it again:")
        return CALLCHAR_GROUP
    group_id = int(text)
    character_query = context.user_data.get("callchar_character_query", "")
    character = (await asyncio.to_thread(get_character, character_query))
    if not character:
        matches = (await asyncio.to_thread(find_characters_by_name_parts, character_query))
        if len(matches) > 1:
            await safe_reply_text(
                update.effective_message,
                "❓ Multiple characters found. Select one:",
                reply_markup=character_selection_keyboard(update.effective_user.id, "callchar", matches),
            )
            return CALLCHAR_GROUP
        recruit_matches = (await asyncio.to_thread(find_characters_by_recruit_name_partial, character_query))
        if len(recruit_matches) > 1:
            await safe_reply_text(
                update.effective_message,
                "❓ Multiple characters found. Select one:",
                reply_markup=character_selection_keyboard(update.effective_user.id, "callchar", recruit_matches),
            )
            return CALLCHAR_GROUP
        await safe_reply_text(update.effective_message, "❌ Character not found. Start /callcharacter again.")
        context.user_data.pop("callchar_character_query", None)
        return ConversationHandler.END
    try:
        chat = await context.bot.get_chat(group_id)
        if chat.type not in ("group", "supergroup"):
            await safe_reply_text(update.effective_message, "❌ That ID is not a group/supergroup. Send the Group ID again:")
            return CALLCHAR_GROUP
        if not await is_group_approved(group_id) or not (await asyncio.to_thread(is_bot_enabled, group_id)):
            await safe_reply_text(update.effective_message, "❌ That group is not approved or the bot is OFF there.")
            return ConversationHandler.END
        active = context.application.bot_data.setdefault("active_spawns", {})
        if group_id in active:
            await safe_reply_text(update.effective_message, "❌ A character is already spawned in that group.")
            return ConversationHandler.END
        await callchar_ask_confirm(update.effective_message, context, group_id, character, update.effective_user.id)
    except Exception as e:
        print("PM callchar error:", e)
        await safe_reply_text(update.effective_message, "❌ Could not call the character to that group. Check the Group ID and bot permissions.")
    finally:
        context.user_data.pop("callchar_character_query", None)
    return ConversationHandler.END

async def callchar(update, context):
    (await save_user_async(update.effective_user))
    if not await require_group_spawn(update):
        return ConversationHandler.END
    chat_id = update.effective_chat.id

    async def tell(text):
        await context.bot.send_message(
            chat_id=chat_id,
            text=add_display_name_header(update.effective_message, text),
            parse_mode="HTML",
        )

    if not is_owner(update.effective_user.id):
        await tell(UNAUTHORIZED_TEXT)
        return

    if not context.args:
        await tell(
            "Usage: /callcharacter <4-digit code or character name>\n\nExamples:\n/callcharacter 1001\n/callcharacter Yuji Itadori"
        )
        return

    active = context.application.bot_data.setdefault("active_spawns", {})
    if chat_id in active:
        await tell("❌ A character is already spawned in this chat.\nUse /add to catch it first.")
        return

    character_query = " ".join(context.args).strip()
    character = (await asyncio.to_thread(get_character, character_query))
    if not character:
        await tell("❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
        return

    try:
        await callchar_ask_confirm(update.effective_message, context, chat_id, character, update.effective_user.id)
    except Exception as e:
        print("Callchar confirm prompt error:", e)
        await tell("⚠️ Could not open the confirmation. Please try again.")
    return ConversationHandler.END

async def callchar_ask_confirm(message, context, group_id, character, owner_id):
    """Ask the Owner to confirm before an owner call actually spawns the character."""
    import uuid as _uuid
    token = _uuid.uuid4().hex[:8]
    pending = context.application.bot_data.setdefault("callchar_pending", {})
    if len(pending) > 50:
        pending.pop(next(iter(pending)), None)
    pending[token] = {"group_id": int(group_id), "code": str(character[0]), "owner_id": int(owner_id)}
    keyboard = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Confirm", callback_data=f"cc:{token}:y"),
        InlineKeyboardButton("❌ Cancel", callback_data=f"cc:{token}:n"),
    ]])
    await safe_reply_text(
        message,
        f"⚠️ Call this character?\n🎭 {character[1]} [{character[0]}] — {character[3]}\n🆔 Group ID: {group_id}\n\nPress Confirm to spawn it, or Cancel to stop.",
        reply_markup=keyboard,
    )

async def callchar_confirm_callback(update, context):
    query = update.callback_query
    if not is_owner(query.from_user.id):
        await deny_callback(query)
        return
    try:
        _, token, choice = query.data.split(":")
    except ValueError:
        await query.answer()
        return
    info = context.application.bot_data.setdefault("callchar_pending", {}).pop(token, None)
    if not info:
        await query.answer("This request has expired. Use /callcharacter again.", show_alert=True)
        try:
            await query.edit_message_text("⌛ This call request has expired.")
        except Exception:
            pass
        return
    if choice != "y":
        await query.answer("Cancelled")
        try:
            await query.edit_message_text("❌ Call cancelled. Nothing was spawned.")
        except Exception:
            pass
        return
    await query.answer("Calling…")
    group_id = info["group_id"]
    character = await asyncio.to_thread(get_character, info["code"])
    if not character:
        await query.edit_message_text("❌ Character not found.")
        return
    active = context.application.bot_data.setdefault("active_spawns", {})
    if group_id in active:
        await query.edit_message_text("❌ A character is already spawned in that group.")
        return
    try:
        success, reason = await spawn_reserved(group_id, context, character, "owner_callchar")
    except Exception as e:
        print("Callchar spawn error:", e)
        await query.edit_message_text("⚠️ Character could not be delivered. Please try again.")
        return
    if not success:
        await query.edit_message_text(reason or "⚠️ Character could not be delivered. Please try again.")
        return
    context.application.bot_data.setdefault("active_chats", set()).add(group_id)
    try:
        await query.edit_message_text(f"✅ Character called successfully.\n🎭 {character[1]} [{character[0]}]\n🆔 Group ID: {group_id}")
    except Exception:
        pass

async def add(update, context):
    (await save_user_async(update.effective_user))
    if not is_group_chat(update) or not context.args:
        return

    chat_id = update.effective_chat.id
    user_id = update.effective_user.id
    lock = get_spawn_lock(context.application)
    expired_spawn = None
    caught_spawn = None

    async with lock:
        active = context.application.bot_data.setdefault("active_spawns", {})
        spawn = active.get(chat_id)
        if not spawn:
            no_active = True
        else:
            no_active = False
            expired_spawn = expire_active_spawn_locked(
                context.application, chat_id, datetime.now()
            )
            if expired_spawn:
                spawn = None

            if spawn:
                entered = [part for part in context.args if part.strip()]
                entered_text = " ".join(entered).strip()
                valid_code = (
                    entered_text.isdigit()
                    and len(entered_text) == 4
                    and entered_text == str(spawn["code"])
                )
                valid_name = spawn_name_matches(spawn["name"], entered)
                if not valid_name:
                    for recruit_name in spawn.get("recruit_names", []):
                        if spawn_name_matches(recruit_name, entered):
                            valid_name = True
                            break

                if not (valid_code or valid_name):
                    no_active = False
                    invalid_name = True
                else:
                    invalid_name = False
                    history_id = spawn.get("history_id")
                    if history_id:
                        history_row = (await asyncio.to_thread(mongo_db.sh_spawn_row, history_id))

                        if history_row:
                            history_spawned_at, history_caught_by = history_row
                            if history_caught_by is not None:
                                invalid_name = True
                            else:
                                try:
                                    history_dt = datetime.fromisoformat(str(history_spawned_at))
                                    if history_dt.tzinfo is None:
                                        history_dt = history_dt.replace(tzinfo=INDIA_TZ)
                                    age = datetime.now(timezone.utc) - history_dt.astimezone(timezone.utc)
                                    if age >= timedelta(seconds=SPAWN_LIFETIME):
                                        expired_spawn = active.pop(chat_id, None)
                                        if expired_spawn:
                                            context.application.bot_data.setdefault("next_auto_spawn_at", {})[chat_id] = (
                                                datetime.now() + timedelta(seconds=AUTO_SPAWN_INTERVAL)
                                            )
                                        spawn = None
                                except (TypeError, ValueError):
                                    pass

                    if spawn and not invalid_name:
                        # Claim the spawn atomically, then grant the copy; undo the claim if the grant fails.
                        claimed = False
                        granted_id = None
                        try:
                            if history_id:
                                claimed = (await asyncio.to_thread(mongo_db.sh_claim_catch, history_id, user_id, india_timestamp()))
                                if not claimed:
                                    invalid_name = True
                            if not invalid_name:
                                granted_id = (await asyncio.to_thread(mongo_db.add_collection, user_id, spawn["code"], timestamp()))
                        except Exception as e:
                            if granted_id is not None:
                                try:
                                    (await asyncio.to_thread(mongo_db.delete_collection_by_id, granted_id))
                                except Exception as undo_err:
                                    print("Catch undo error:", undo_err)
                            if claimed:
                                try:
                                    (await asyncio.to_thread(mongo_db.sh_release_catch, history_id))
                                except Exception as undo_err:
                                    print("Catch undo error:", undo_err)
                            print("Catch transaction error:", e)
                            invalid_name = True

                        if not invalid_name:
                            caught_spawn = active.pop(chat_id, None)
                            if caught_spawn:
                                await cancel_spawn_expiry_task(caught_spawn)
                            if caught_spawn and not history_id:
                                (await asyncio.to_thread(mark_spawn_caught, caught_spawn.get("history_id"), user_id))

                            if caught_spawn and caught_spawn.get("spawned_by") in ("auto_spawn", "manual_spawn"):
                                if not caught_spawn.get("forced_reuse"):
                                    if not (await asyncio.to_thread(finalize_daily_character_spawn, chat_id, caught_spawn.get("code"))):
                                        print("Group character catch quota finalization warning:", chat_id, caught_spawn.get("code"))
                                    if caught_spawn.get("rarity") in ("Legendary", "Mythical", "Celestial"):
                                        if not (await asyncio.to_thread(finalize_rarity_success, caught_spawn.get("rarity"))):
                                            print("High-rank daily limit finalization warning:", chat_id, caught_spawn.get("rarity"))

    if no_active:
        await safe_reply_text(update.message, "❌ There is no active character in this chat.")
        return

    if expired_spawn:
        await send_expiry_notice(context.application, chat_id, expired_spawn)
        await safe_reply_text(update.message, "❌ There is no active character in this chat.")
        return

    if not caught_spawn:
        return

    context.application.bot_data.setdefault("next_auto_spawn_at", {})[chat_id] = (
        datetime.now() + timedelta(seconds=AUTO_SPAWN_INTERVAL)
    )
    mark_success(update)
    caught_rarity = caught_spawn["rarity"]
    caught_symbol = SYMBOL.get(caught_rarity, "⭐")
    await fusion.record_catch(user_id, caught_rarity, caught_spawn["code"])  # stone task progress (never raises)
    await safe_reply_text(
        update.message,
        f"🌸 Recruiter: {berry_display_name(update.effective_user)}\n\n"
        "🎉 Congratulations! Character added to your collection!\n\n"
        f"Name: {caught_spawn['name']}\n"
        f"Code: {caught_spawn['code']}\n"
        f"Tier: {caught_rarity} {caught_symbol}\n"
        f"Worth: {caught_spawn['worth']} Berrys\n"
    )
    _who = berry_display_name(update.effective_user)
    await fusion.stone_remind(user_id, chat_id=chat_id, name=_who)  # "stone task complete - claim it" message (never raises)
    await fusion.dt_record_catch(
        user_id, caught_rarity, caught_spawn["code"],
        event_id=(f"catch:{caught_spawn['history_id']}" if caught_spawn.get("history_id") else None),
        chat_id=chat_id, name=_who)  # daily mission progress + "mission complete - claim it" message (never raises)
    await rewards.record(context.bot, user_id, "catch", rarity=caught_rarity, chat_id=chat_id, name=_who)   # festival quests (never raises)

async def get_collection_rows(user_id, sort_mode="tier", rarity=None):
    rows = (await asyncio.to_thread(mongo_db.get_collection_summary, user_id))
    if rarity:      # tier filter from the Tier menu: only this tier's characters
        rows = [r for r in rows if r[3] == rarity]

    rarity_order = {
        "Special": -1,          # festival special characters: their own tier at the top of the collection
        "Heavenly": 0,
        "Celestial": 1,
        "Mythical": 2,
        "Legendary": 3,
        "Epic": 4,
        "Rare": 5,
        "Common": 6,
    }

    if sort_mode == "time":
        rows.sort(key=lambda r: r[6] or "", reverse=True)
    elif sort_mode == "name":
        rows.sort(key=lambda r: r[1].lower())
    elif sort_mode == "qty":
        rows.sort(key=lambda r: (-r[5], r[1].lower()))
    else:
        rows.sort(key=lambda r: (rarity_order.get(r[3], 99), r[1].lower()))

    rows.sort(key=lambda r: r[3] != "Special")      # festival special characters always first, in every sort (stable)
    return rows

def get_favorite_code(user_id):
    return mongo_db.get_favorite_code(user_id)

def set_favorite(user_id, character_code):
    mongo_db.set_favorite(user_id, character_code, timestamp())

def clear_favorite(user_id):
    mongo_db.clear_favorite(user_id)

# Tier menu (🔹 Tier button): highest tier first. Callback mode format: <sort>[~<Rarity>], e.g. "name~Epic".
COLLECTION_TIERS = ("Special", "Heavenly", "Celestial", "Mythical", "Legendary", "Epic", "Rare", "Common")
COLLECTION_SORTS = {"tier", "time", "name", "qty"}


def _parse_coll_mode(value):
    """'name~Epic' -> ('name', 'Epic'); unknown tier names are ignored (-> None)."""
    action, _sep, tier = str(value).partition("~")
    return action, (tier if tier in COLLECTION_TIERS else None)


def collection_tier_keyboard(user_id, prefix="coll"):
    """The tier menu shown after tapping 🔹 Tier: one tier per row, then Back to the full collection."""
    rows = [[InlineKeyboardButton(rarity_text(r), callback_data=f"{prefix}:{user_id}:tier~{r}:0")]
            for r in COLLECTION_TIERS if r != "Special" or "Special" in SYMBOL]      # Special tier only exists once the owner set its symbol
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data=f"{prefix}:{user_id}:tier:0")])
    return InlineKeyboardMarkup(rows)


def _coll_private(user_id):
    """True when the user turned 🔒 Privacy ON (only the bot owner can then see their collection with /see)."""
    doc = _mc(mongo_db.USERS).find_one({"_id": int(user_id)}, {"collection_private": 1}) or {}
    return bool(doc.get("collection_private"))


def collection_keyboard(user_id, page, total_pages, sort_mode, favorite_code, rarity=None, viewer=False, private=False):
    """viewer=True is the read-only /see version: paging and sorting only (no Sell, Favourite or Privacy)."""
    p = "cv" if viewer else "coll"
    suffix = f"~{rarity}" if rarity else ""          # the tier filter travels inside the button data
    buttons = []
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅️", callback_data=f"{p}:{user_id}:{sort_mode}{suffix}:{page-1}"))
    nav.append(InlineKeyboardButton(f"📖 {page+1}/{total_pages}", callback_data=f"{p}:{user_id}:nochange:0"))
    if page < total_pages - 1:
        nav.append(InlineKeyboardButton("➡️", callback_data=f"{p}:{user_id}:{sort_mode}{suffix}:{page+1}"))
    buttons.append(nav)

    buttons.append([
        InlineKeyboardButton("🔹 Tier", callback_data=f"{p}:{user_id}:tiermenu:0"),
        InlineKeyboardButton("🔤 Name", callback_data=f"{p}:{user_id}:name{suffix}:0"),
    ])
    last = [InlineKeyboardButton("🔢 Quantity", callback_data=f"{p}:{user_id}:qty{suffix}:0")]
    if not viewer:
        last.append(InlineKeyboardButton("🔒 Privacy: ON" if private else "🔓 Privacy: OFF",
                                         callback_data=f"coll:{user_id}:privacy:0"))
    buttons.append(last)
    if viewer:
        return InlineKeyboardMarkup(buttons)

    if favorite_code:
        buttons.append([
            InlineKeyboardButton("⭐ Favourite", callback_data=f"{p}:{user_id}:nochange:0"),
            InlineKeyboardButton("❌ Clear Favourite", callback_data=f"{p}:{user_id}:clearfav{suffix}:0"),
        ])
    buttons.append([InlineKeyboardButton("💰 Sell", callback_data=f"{p}:{user_id}:sell:0")])
    return InlineKeyboardMarkup(buttons)

def build_collection_text(rows, page, per_page, sort_mode, favorite_code, total_copies, owner_name="Player", tier_filter=None):
    total_pages = max(1, (len(rows) + per_page - 1) // per_page)
    page = max(0, min(page, total_pages - 1))
    page_rows = rows[page * per_page:(page + 1) * per_page]

    text = (
        "━━━━━━━━━━━━━━━━━━\n"
        f"❀• {owner_name} •❀'s crew  ➜  Page {page + 1}/{total_pages}\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        + (f"📚 {rarity_text(tier_filter)} collection: {sum(r[5] for r in rows)} total | {len(rows)} unique\n" if tier_filter
           else f"📚 Collection: {total_copies} total | {len(rows)} unique\n")
    )

    current_rarity = None
    for code, name, anime, rarity, photo, qty, last_caught in page_rows:
        if rarity != current_rarity:
            text += f"\n➜ {rarity_text(rarity)}\n"
            current_rarity = rarity
        star = "⭐ " if code == favorite_code else ""
        text += f"{star}|{code}| {name} {qty}X\n"

    text += "\n━━━━━━━━━━━━━━━━━━"
    labels = {"tier": "🔹 Sorted by Tier", "time": "🕒 Sorted by Recent", "name": "🔤 Sorted by Name", "qty": "🔢 Sorted by Quantity"}
    if tier_filter:      # tier view: "Tier: Epic" (plus the sort when it is not the default tier sort)
        text += f"\n🔹 Tier: {rarity_text(tier_filter)}" + ("" if sort_mode == "tier" else f" | {labels.get(sort_mode, '')}")
    else:
        text += "\n" + labels.get(sort_mode, "🔹 Sorted by Tier")
    if favorite_code:
        fav = next((r for r in rows if r[0] == favorite_code), None)
        if fav:
            text += f"\n⭐ Favourite: {fav[1]} [{fav[0]}]"
    return text, total_pages, page

async def send_collection(update_or_query, context, user_id, page=0, sort_mode="tier", edit=False, owner_name=None, rarity=None,
                          viewer=False):
    rows = await get_collection_rows(user_id, sort_mode, rarity)
    if not rows and rarity:      # the last copy of that tier was sold/moved meanwhile: fall back to the full collection
        rarity = None
        rows = await get_collection_rows(user_id, sort_mode)
    sender_message = getattr(update_or_query, "message", None)
    if sender_message is None and hasattr(update_or_query, "effective_message"):
        sender_message = update_or_query.effective_message
    if sender_message is None and hasattr(update_or_query, "message"):
        sender_message = update_or_query.message
    if not rows:
        message = (f"📭 {html_escape(owner_name or 'This user')} has no characters yet." if viewer else
                   add_display_name_header(sender_message, "📚 Your collection is empty. Catch a character with /spawn then use /add."))
        if edit:
            await update_or_query.edit_message_text(message)
        else:
            await context.bot.send_message(chat_id=update_or_query.message.chat_id, text=message, parse_mode="HTML")
        return

    total_copies = (await asyncio.to_thread(mongo_db.count_user_collection, user_id))

    favorite_code = (await asyncio.to_thread(get_favorite_code, user_id))
    per_page = max(1, ITEMS_PER_PAGE)
    if owner_name is None:
        owner_name = (
            update_or_query.from_user.first_name
            if hasattr(update_or_query, "from_user")
            else "Player"
        ) or "Player"
    text, total_pages, page = build_collection_text(
        rows, page, per_page, sort_mode, favorite_code, total_copies, owner_name, rarity
    )
    text = add_display_name_header(sender_message, text)
    private = False if viewer else await asyncio.to_thread(_coll_private, user_id)
    keyboard = collection_keyboard(user_id, page, total_pages, sort_mode, favorite_code, rarity, viewer, private)

    photo = None
    if favorite_code:
        for row in rows:
            if row[0] == favorite_code:
                photo = row[4]
                break
    if not photo:
        page_rows = rows[page * per_page:(page + 1) * per_page]
        if page_rows:
            photo = page_rows[0][4]

    if edit:
        message = update_or_query.message
        if photo and message.photo:
            try:
                await message.edit_media(
                    media=InputMediaPhoto(media=photo, caption=text),
                    reply_markup=keyboard,
                )
                return
            except Exception:
                try:
                    await message.delete()
                    await context.bot.send_photo(
                        chat_id=message.chat_id,
                        photo=photo,
                        caption=text,
                        reply_markup=keyboard,
                    )
                    return
                except Exception:
                    pass
        if message.photo and not photo:
            try:
                await message.delete()
                await context.bot.send_message(
                    chat_id=message.chat_id,
                    text=text + "\n📷 No saved photo available.",
                    reply_markup=keyboard,
                )
                return
            except Exception:
                pass
        if photo and not message.photo:
            try:
                await message.delete()
                await context.bot.send_photo(
                    chat_id=message.chat_id,
                    photo=photo,
                    caption=text,
                    reply_markup=keyboard,
                )
                return
            except Exception:
                pass
        try:
            await update_or_query.edit_message_text(text=text, reply_markup=keyboard)
            return
        except Exception:
            pass

    if photo:
        await context.bot.send_photo(
            chat_id=update_or_query.message.chat_id, photo=photo, caption=text, reply_markup=keyboard
        )
    else:
        await context.bot.send_message(
            chat_id=update_or_query.message.chat_id, text=text + "\n📷 No saved photo available.", reply_markup=keyboard
        )

async def mycollection(update, context):
    (await save_user_async(update.effective_user))
    await send_collection(
        update, context, update.effective_user.id, 0, "tier",
        edit=False, owner_name=update.effective_user.first_name or "Player"
    )

async def removechar(update, context):
    actor = update.effective_user
    if not is_owner(actor.id):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    (await save_user_async(actor))
    args = list(context.args)
    target_id = actor.id
    reply = update.message.reply_to_message if update.message else None
    if reply and reply.from_user and args:
        target_id = reply.from_user.id
    elif len(args) >= 2 and args[0].lstrip("-").isdigit():
        target_id, args = int(args[0]), args[1:]
    if not args:
        usage = "/removechar <user_id> <code/name> [quantity] or reply to a user"
        await safe_reply_text(update.message, f"Usage: {usage}")
        return
    quantity = 1
    if len(args) > 1 and args[-1].isdigit():
        quantity, args = int(args[-1]), args[:-1]
    if quantity <= 0:
        await safe_reply_text(update.message, "❌ Quantity must be at least 1.")
        return
    character = (await asyncio.to_thread(get_character, " ".join(args).strip()))
    if not character:
        await safe_reply_text(update.message, "❌ Character not found or name matches multiple characters. Use the 4-digit code.")
        return
    code, name = character[:2]
    try:
        ok, available = (await asyncio.to_thread(mongo_db.remove_copies, target_id, code, quantity))
    except Exception as e:
        print("removechar error:", e)
        await safe_reply_text(update.message, "❌ Could not remove the character. Please try again.")
        return
    if not ok:
        await safe_reply_text(update.message, f"❌ User has only {available} copy/copies of {name}.")
        return
    owner_note = " from user's collection" if target_id != actor.id else " from your collection"
    await safe_reply_text(update.message, f"🗑 Removed {name} [{code}] x{quantity}{owner_note}.")

async def myfav(update, context):
    (await save_user_async(update.effective_user))
    user_id = update.effective_user.id

    if not context.args:
        current = (await asyncio.to_thread(get_favorite_code, user_id))
        if current:
            character = (await asyncio.to_thread(get_character, current))
            if character:
                await safe_reply_text(update.message,
                    f"⭐ Your favourite is {character[1]} [{character[0]}].\n\n"
                    "Use /myfav <code or character name> to change it, or /myfav off to remove it."
                )
                return
        await safe_reply_text(update.message,
            "⭐ No favourite set.\n\n"
            "Use /myfav <4-digit code or character name>\n"
            "Example: /myfav 1001"
        )
        return

    value = " ".join(context.args).strip()
    if value.lower() in {"off", "remove", "none"}:
        (await asyncio.to_thread(clear_favorite, user_id))
        await safe_reply_text(update.message, "❌ Favourite removed.")
        return

    character = (await asyncio.to_thread(get_character, value))
    if not character:
        await safe_reply_text(update.message, "❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
        return

    code, name, anime, rarity, worth, photo = character

    owned = (await asyncio.to_thread(mongo_db.user_owns, user_id, code))

    if not owned:
        await safe_reply_text(update.message,
            f"❌ You don't own {name} [{code}] yet. Catch it first, then set it as favourite."
        )
        return

    (await asyncio.to_thread(set_favorite, user_id, code))
    await safe_reply_text(update.message,
        f"⭐ Favourite set!\n\n"
        f"🎭 {name} [{code}]\n"
        f"🏷 {rarity_text(rarity)}\n\n"
        "Use /mycollection to see it highlighted."
    )

async def collection_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query

    parts = (query.data or "").split(":")
    if len(parts) != 4 or parts[0] != "coll":
        await query.answer()
        return

    try:
        owner_id = int(parts[1])
        page = int(parts[3])
    except ValueError:
        await query.answer()
        return

    user_id = query.from_user.id
    if user_id != owner_id:
        await query.answer("❌ This collection belongs to another user.", show_alert=True)
        return

    action, rarity = _parse_coll_mode(parts[2])      # e.g. "name~Epic" -> ("name", "Epic")
    if action == "nochange":
        await query.answer()
        return
    if action == "privacy":                          # 🔒 Privacy: flip it and update just that button
        now_private = not await asyncio.to_thread(_coll_private, user_id)
        await asyncio.to_thread(_mc(mongo_db.USERS).update_one, {"_id": user_id}, {"$set": {"collection_private": now_private}})
        await query.answer("🔒 Privacy ON. Only the owner can see your collection." if now_private else
                           "🔓 Privacy OFF. Anyone can see your collection with /see.", show_alert=True)
        label = "🔒 Privacy: ON" if now_private else "🔓 Privacy: OFF"
        rows = [[InlineKeyboardButton(label, callback_data=b.callback_data) if (b.callback_data or "").endswith(":privacy:0") else b
                 for b in row] for row in query.message.reply_markup.inline_keyboard]
        try:
            await query.edit_message_reply_markup(reply_markup=InlineKeyboardMarkup(rows))
        except Exception as e:
            print("Privacy button update error:", e)
        return
    if action == "tiermenu":                         # 🔹 Tier: swap the buttons for the tier list (text stays)
        await query.answer()
        try:
            await query.edit_message_reply_markup(reply_markup=collection_tier_keyboard(user_id))
        except Exception as e:
            print("Tier menu error:", e)
        return
    if action == "sell":                             # 💰 Sell: send the how-to guide and wait for the list
        await query.answer()
        try:
            await _sell_send_guide(context, query.message.chat_id, user_id)
        except Exception as e:
            print("Sell guide error:", e)
        return
    if rarity and not await get_collection_rows(user_id, "tier", rarity):
        await query.answer(f"❌ You have no {rarity} characters.", show_alert=True)   # nothing changes on screen
        return

    await query.answer()
    if action == "clearfav":
        (await asyncio.to_thread(clear_favorite, user_id))
        page = 0
        action = "tier"

    if action not in COLLECTION_SORTS:
        action = "tier"

    await send_collection(
        query, context, user_id, page, action, edit=True,
        owner_name=query.from_user.first_name or "Player", rarity=rarity
    )

async def see_command(update, context):
    """/see <user_id or @username>  or reply to someone's message with /see: view their collection (read only)."""
    msg, viewer = update.effective_message, update.effective_user
    await save_user_async(viewer)
    reply = msg.reply_to_message
    if context.args:
        uid = await _dm_target(context.args[0])
    elif reply and reply.from_user:
        uid = reply.from_user.id
    else:
        await safe_reply_text(msg, "Usage: /see <user_id or @username>, or reply to someone's message with /see")
        return
    if uid is None:
        await safe_reply_text(msg, DM_UNKNOWN_TEXT)
        return
    if uid != viewer.id and not is_owner(viewer.id) and await asyncio.to_thread(_coll_private, uid):
        await safe_reply_text(msg, "🔒 This collection is private.")
        return
    await send_collection(update, context, uid, 0, "tier", edit=False, owner_name=await _dm_name(uid), viewer=True)

async def collview_callback(update, context):
    """Buttons of a /see collection: paging and sorting only. Re-checks privacy on every tap."""
    query, parts = update.callback_query, (update.callback_query.data or "").split(":")
    if len(parts) != 4 or not parts[1].lstrip("-").isdigit() or not parts[3].isdigit():
        await query.answer()
        return
    owner_id, page, viewer_id = int(parts[1]), int(parts[3]), query.from_user.id
    if viewer_id != owner_id and not is_owner(viewer_id) and await asyncio.to_thread(_coll_private, owner_id):
        await query.answer("🔒 This collection is private.", show_alert=True)
        return
    action, rarity = _parse_coll_mode(parts[2])
    if action == "nochange":
        await query.answer()
        return
    if action == "tiermenu":
        await query.answer()
        try:
            await query.edit_message_reply_markup(reply_markup=collection_tier_keyboard(owner_id, "cv"))
        except Exception as e:
            print("Tier menu error:", e)
        return
    if rarity and not await get_collection_rows(owner_id, "tier", rarity):
        await query.answer(f"❌ No {rarity} characters.", show_alert=True)
        return
    await query.answer()
    await send_collection(query, context, owner_id, page, action if action in COLLECTION_SORTS else "tier", edit=True,
                          owner_name=await _dm_name(owner_id), rarity=rarity, viewer=True)

async def mystats(update, context):
    (await save_user_async(update.effective_user))

    coins = (await asyncio.to_thread(mongo_db.get_coins, update.effective_user.id)) or 0
    count = (await asyncio.to_thread(mongo_db.count_user_collection, update.effective_user.id))

    favorite = (await asyncio.to_thread(get_favorite_code, update.effective_user.id))
    fav_text = "None"
    if favorite:
        fav = (await asyncio.to_thread(get_character_by_code, favorite))
        if fav:
            fav_text = f"{fav[1]} [{fav[0]}]"
    unique_c = len(await get_collection_rows(update.effective_user.id, "tier"))

    sent_today, received_today = (await asyncio.to_thread(berry_transfer_stats, update.effective_user.id))
    berry_day = berry_transfer_day()
    transfers_today = (await asyncio.to_thread(_mc("berry_transfers_v2").count_documents, {"sender_id": update.effective_user.id, "transfer_day": berry_day}))
    send_remaining = max(0, BERRY_TRANSFER_DAILY_SEND_LIMIT - int(sent_today or 0))
    receive_remaining = max(0, BERRY_TRANSFER_DAILY_RECEIVE_LIMIT - int(received_today or 0))

    guess_doc = (await asyncio.to_thread(_mc(mongo_db.USERS).find_one, {"_id": update.effective_user.id}, {"guess_reward_total": 1, "guess_reward_day": 1})) or {}
    guess_earned = int(guess_doc.get("guess_reward_total") or 0) if guess_doc.get("guess_reward_day") == shop_rotation_key() else 0
    guess_remaining = max(0, GUESS_REWARD_CAP - guess_earned)

    await badge_banner.send_mystats(update, context,
        f"👤 {update.effective_user.first_name}\n\n"
        f"🛡 Role: {(await asyncio.to_thread(staff_role, update.effective_user.id))}\n"
        f"💰 Berrys: {coins}\n"
        f"🎭 Characters: {count} copies / {unique_c} unique\n"
        f"⭐ Favourite: {fav_text}\n\n"
        f"🫐 Today's Berry Stats\n"
        f"📤 Sent today: {int(sent_today or 0)} ⦵\n"
        f"📥 Received today: {int(received_today)} ⦵\n"
        f"📊 Send remaining: {send_remaining} ⦵\n"
        f"📊 Receive remaining: {receive_remaining} ⦵\n"
        f"🔄 Transfers today: {int(transfers_today or 0)}\n\n"
        f"🎯 Number Guess (daily cap)\n"
        f"🎁 Earned today: {guess_earned} ⦵\n"
        f"📊 Remaining: {guess_remaining} ⦵"
    )

SHOP_RARITIES = ("Common", "Rare", "Epic", "Legendary", "Mythical")      # one shop page per rarity, in this order
SHOP_REFRESH_COST = 100
SHOP_PRICE_MULTIPLIER = 5
SHOP_CHEAP_RARITIES = ("Common", "Rare", "Epic")        # these cost worth x3, every other rarity worth x5
def shop_price(worth, rarity):
    return int(worth) * (3 if rarity in SHOP_CHEAP_RARITIES else SHOP_PRICE_MULTIPLIER)
# Buying one of these rarities from the shop earns 1 FREE refresh (0 ⦵). Credits stack and never expire.
SHOP_FREE_REFRESH_RARITIES = ("Legendary", "Mythical")

def get_free_refresh_credits(user_id):
    doc = _mc("shop_free_refresh_v1").find_one({"_id": int(user_id)}, {"credits": 1})
    return int((doc or {}).get("credits", 0) or 0)

def grant_free_refresh(user_id, amount=1, session=None):
    _mc("shop_free_refresh_v1").update_one(
        {"_id": int(user_id)}, {"$inc": {"credits": int(amount)}}, upsert=True, session=session)

def consume_free_refresh(user_id):
    """Atomically use 1 credit. True only if a credit was really available."""
    res = _mc("shop_free_refresh_v1").update_one(
        {"_id": int(user_id), "credits": {"$gt": 0}}, {"$inc": {"credits": -1}})
    return res.modified_count == 1
IST = timezone(timedelta(hours=5, minutes=30))

def shop_rotation_key(dt=None):
    if dt is None:
        dt = datetime.now(IST)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=IST)
    if dt.hour < 4:
        dt = dt - timedelta(days=1)
    return dt.date().isoformat()

def choose_shop_characters(exclude_codes=None, cursor=None):
    # `cursor` is kept only so existing call sites keep working; characters now live in MongoDB.
    exclude = set(str(v) for v in (exclude_codes or []))
    chosen = []
    for rarity in SHOP_RARITIES:
        taken = exclude | {str(row[0]) for row in chosen}
        pool = [
            r for r in rewards.filter_hidden(mongo_db.get_characters_by_rarity(rarity))
            if r[3] != "Celestial" and str(r[0]) not in taken
        ]
        if not pool:
            return None
        chosen.append(random.choice(pool))
    return chosen

def replace_user_shop_rotation(user_id, rotation_key=None, exclude_codes=None):
    user_id = int(user_id)
    exclude = set(str(v) for v in (exclude_codes or []))
    day_key = shop_rotation_key()
    if rotation_key is None:
        rotation_key = f"{day_key}:{user_id}:{time.time_ns()}"

    exclude.update(str(d["character_code"]) for d in
                   _mc("shop_v3").find({"shop_day": day_key, "user_id": {"$ne": user_id}}, {"character_code": 1}))
    rows = choose_shop_characters(exclude_codes=exclude)
    if not rows or len(rows) != len(SHOP_RARITIES):
        return False

    stamp = india_timestamp()
    docs = [{"user_id": user_id, "slot": slot, "character_code": row[0], "rotation_key": rotation_key,
             "shop_day": day_key, "refreshed_at": stamp} for slot, row in enumerate(rows)]
    _swap_shop_rows(user_id, docs)
    return True

def ensure_shop_rotation(user_id, force=False):
    user_id = int(user_id)
    key = shop_rotation_key()
    docs = list(_mc("shop_v3").find({"user_id": user_id}, {"shop_day": 1}))
    count = len(docs)
    current_day = max((d.get("shop_day") for d in docs if d.get("shop_day")), default=None)
    if not force and count == len(SHOP_RARITIES) and current_day == key:
        return True
    return replace_user_shop_rotation(user_id, exclude_codes=[])

def get_shop_rows(user_id):
    key = shop_rotation_key()
    shop = _mc("shop_v3").find({"user_id": int(user_id), "shop_day": key}).sort("slot", 1)
    rows = []
    for d in shop:
        ch = mongo_db.get_character_by_code(d["character_code"])
        if ch:
            rows.append((d["slot"], ch[0], ch[1], ch[2], ch[3], ch[4], ch[5], d.get("rotation_key")))
    return rows

def shop_keyboard(user_id, page, price, bought=False, total=len(SHOP_RARITIES), free_credits=0):
    prev_page = (page - 1) % total
    next_page = (page + 1) % total
    buy_label = "✅ BOUGHT" if bought else f"🛒 BUY FOR {price} ⦵"
    buy_action = "bought" if bought else "buy"
    refresh_label = (f"🎁 FREE REFRESH — 0 ⦵ (x{free_credits})" if free_credits > 0
                     else f"🔄 REFRESH — {SHOP_REFRESH_COST} ⦵")
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("◀️ BACK", callback_data=f"shop:page:{user_id}:{prev_page}"),
            InlineKeyboardButton("▶️ NEXT", callback_data=f"shop:page:{user_id}:{next_page}"),
        ],
        [InlineKeyboardButton(refresh_label, callback_data=f"shop:refresh:{user_id}:0")],
        [InlineKeyboardButton(buy_label, callback_data=f"shop:{buy_action}:{user_id}:{page}")],
    ])

def build_shop_caption(row, page, total=len(SHOP_RARITIES), free_credits=0):
    _, code, name, anime, rarity, worth, photo, _rotation_key = row
    price = shop_price(worth, rarity)
    return (
        "🛒 CHARACTER SHOP\n\n"
        f"🎭 {name}\n"
        f"📺 Anime: {anime}\n"
        f"{rarity_text(rarity)}\n"
        f"💎 Worth: {worth} ⦵\n"
        f"🪙 Buy Price: {price} ⦵\n\n"
        f"📦 Shop: {page + 1}/{total}\n"
        "🕓 Daily reset: 4:00 AM IST\n"
        + (f"🎁 Free refreshes: {free_credits} (earned from Legendary/Mythical buys)" if free_credits > 0
           else f"🔄 Manual refresh: {SHOP_REFRESH_COST} ⦵")
    )

async def render_shop(target, context, user_id, page=0, edit=False):
    try:
        if not (await asyncio.to_thread(ensure_shop_rotation, user_id)):
            raise RuntimeError("shop rotation could not be created")
        rows = (await asyncio.to_thread(get_shop_rows, user_id))
        if len(rows) != len(SHOP_RARITIES):
            (await asyncio.to_thread(ensure_shop_rotation, user_id, force=True))
            rows = (await asyncio.to_thread(get_shop_rows, user_id))
        if len(rows) != len(SHOP_RARITIES):
            text = "❌ Shop is temporarily unavailable. Please try again later."
            if edit:
                try:
                    await target.edit_message_text(text=text)
                except Exception:
                    pass
            else:
                await safe_reply_text(target.message, text)
            return

        page = int(page) % len(SHOP_RARITIES)
        row = rows[page]
        free_credits = (await asyncio.to_thread(get_free_refresh_credits, user_id))
        caption = add_display_name_header(target.message, build_shop_caption(row, page, len(SHOP_RARITIES), free_credits))
        price = shop_price(row[5], row[4])
        bought = (await asyncio.to_thread(_mc("shop_purchases_v2").find_one, {"user_id": int(user_id), "rotation_key": row[7], "slot": row[0]})) is not None
        keyboard = shop_keyboard(user_id, page, price, bought=bought, free_credits=free_credits)
        photo = row[6]

        if edit:
            message = target.message
            try:
                if photo and message.photo:
                    await message.edit_media(
                        media=InputMediaPhoto(media=photo, caption=caption),
                        reply_markup=keyboard,
                    )
                elif photo:
                    await message.delete()
                    await context.bot.send_photo(
                        chat_id=message.chat_id, photo=photo,
                        caption=caption, reply_markup=keyboard,
                    )
                else:
                    if message.photo:
                        await message.delete()
                        await context.bot.send_message(
                            chat_id=message.chat_id, text=caption,
                            reply_markup=keyboard,
                        )
                    else:
                        await message.edit_text(text=caption, reply_markup=keyboard)
                return
            except Exception as e:
                print("Shop message update error:", e)
                try:
                    await message.delete()
                except Exception:
                    pass
                if photo:
                    await context.bot.send_photo(
                        chat_id=message.chat_id, photo=photo,
                        caption=caption, reply_markup=keyboard,
                    )
                else:
                    await context.bot.send_message(
                        chat_id=message.chat_id, text=caption,
                        reply_markup=keyboard,
                    )
                return

        if photo:
            await context.bot.send_photo(chat_id=target.message.chat_id, photo=photo, caption=caption, reply_markup=keyboard)
        else:
            await safe_reply_text(target.message, caption, reply_markup=keyboard)
    except Exception as e:
        print("Shop render error:", e)
        if edit:
            try:
                await target.edit_message_text(text="❌ Shop could not be loaded. Please try again.")
            except Exception:
                pass
        else:
            await safe_reply_text(target.message, "❌ Shop could not be loaded. Please try again.")

async def shop(update, context):
    (await save_user_async(update.effective_user))
    await render_shop(update, context, update.effective_user.id, 0, edit=False)

async def shop_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    parts = (query.data or "").split(":")
    if len(parts) != 4 or parts[0] != "shop":
        await query.answer()
        return
    try:
        action = parts[1]
        owner_id = int(parts[2])
        page = int(parts[3])
    except (ValueError, TypeError):
        await query.answer("❌ Invalid shop action.", show_alert=True)
        return

    if query.from_user.id != owner_id:
        await query.answer("❌ This shop belongs to another user.", show_alert=True)
        return

    if action == "page":
        await query.answer()
        await render_shop(query, context, owner_id, page, edit=True)
        return

    if action == "refresh":
        spent = False
        used_free = False
        try:
            balance = (await asyncio.to_thread(mongo_db.get_coins, owner_id))
            if balance is None:
                await query.answer("❌ Your account could not be found.", show_alert=True)
                return
            has_free = (await asyncio.to_thread(get_free_refresh_credits, owner_id)) > 0
            if not has_free and int(balance or 0) < SHOP_REFRESH_COST:
                await query.answer("❌ You need 100 ⦵ to refresh the shop.", show_alert=True)
                return

            day_key = shop_rotation_key()
            shop = _mc("shop_v3")
            _own_docs, _other_docs = await asyncio.to_thread(lambda: (
                list(shop.find({"user_id": owner_id, "shop_day": day_key})),
                list(shop.find({"shop_day": day_key, "user_id": {"$ne": owner_id}}))))
            current_codes = {str(d["character_code"]) for d in _own_docs}
            other_user_codes = {str(d["character_code"]) for d in _other_docs}
            new_rows = (await asyncio.to_thread(choose_shop_characters, exclude_codes=current_codes | other_user_codes))
            if not new_rows or len(new_rows) != len(SHOP_RARITIES):
                await query.answer(
                    "❌ I couldn't find enough unused characters for your new shop. Nothing was deducted.",
                    show_alert=True,
                )
                return

            new_codes = {str(row[0]) for row in new_rows}
            if current_codes & new_codes:
                await query.answer(
                    "❌ New shop still contains an old character. Nothing was deducted.",
                    show_alert=True,
                )
                return

            # atomic conditional deduct, then swap the 4 shop rows in one transaction
            # a free-refresh credit is used first (0 ⦵); otherwise pay the normal cost
            if (await asyncio.to_thread(consume_free_refresh, owner_id)):
                used_free = True
            elif not (await asyncio.to_thread(mongo_db.spend_coins, owner_id, SHOP_REFRESH_COST)):
                await query.answer("❌ You need 100 ⦵ to refresh the shop.", show_alert=True)
                return
            spent = True
            stamp = india_timestamp()
            rotation_key = f"{day_key}:{owner_id}:{time.time_ns()}"
            (await asyncio.to_thread(_swap_shop_rows, owner_id, [
                {"user_id": owner_id, "slot": slot, "character_code": shop_row[0], "rotation_key": rotation_key,
                 "shop_day": day_key, "refreshed_at": stamp}
                for slot, shop_row in enumerate(new_rows)
            ]))
        except Exception as e:
            if spent:
                try:
                    if used_free:
                        (await asyncio.to_thread(grant_free_refresh, owner_id, 1))
                    else:
                        (await asyncio.to_thread(mongo_db.add_coins, owner_id, SHOP_REFRESH_COST))
                except Exception as undo_err:
                    print("Shop refresh refund error:", undo_err)
            print("Shop refresh error:", e)
            await query.answer("❌ Refresh failed. Nothing was deducted.", show_alert=True)
            return

        await query.answer("✅ Free refresh used! -0 ⦵" if used_free else "✅ Shop refreshed! -100 ⦵")
        await render_shop(query, context, owner_id, 0, edit=True)
        return

    if action == "buy":
        rows = (await asyncio.to_thread(get_shop_rows, owner_id))
        if len(rows) != len(SHOP_RARITIES) or page < 0 or page >= len(rows):
            await query.answer("❌ Shop is unavailable. Try again.", show_alert=True)
            return
        row = rows[page]
        _, code, name, anime, rarity, worth, photo, rotation_key = row
        price = shop_price(worth, rarity)
        try:
            balance = (await asyncio.to_thread(mongo_db.get_coins, owner_id)) or 0
            if balance < price:
                await query.answer(f"❌ Need {price} ⦵ to buy {name}.", show_alert=True)
                return
            key = rotation_key
            if (await asyncio.to_thread(_mc("shop_purchases_v2").find_one, {"user_id": owner_id, "rotation_key": key, "slot": page})):
                await query.answer("ℹ️ You already bought this shop character.", show_alert=True)
                return

            def _buy(session):
                # coins, the new copy and the purchase record commit together or not at all
                if not mongo_db.spend_coins(owner_id, price, session=session):
                    return False
                mongo_db.add_collection(owner_id, code, india_timestamp(), session=session)
                if rarity in SHOP_FREE_REFRESH_RARITIES:
                    grant_free_refresh(owner_id, 1, session=session)
                mongo_db.insert_with_id("shop_purchases_v2", {
                    "user_id": owner_id, "rotation_key": key, "slot": page, "character_code": code,
                    "price": price, "purchased_at": india_timestamp(),
                }, session=session)
                return True

            if not (await asyncio.to_thread(mongo_db.run_transaction, _buy)):
                await query.answer(f"❌ Need {price} ⦵ to buy {name}.", show_alert=True)
                return
        except Exception as e:
            print("Shop purchase error:", e)
            await query.answer("❌ Purchase failed. Your ⦵ were not deducted.", show_alert=True)
            return

        got_free = rarity in SHOP_FREE_REFRESH_RARITIES
        await query.answer(f"✅ {name} bought for {price} ⦵" + ("\n🎁 You earned a FREE shop refresh!" if got_free else ""),
                           show_alert=got_free)
        free_credits = (await asyncio.to_thread(get_free_refresh_credits, owner_id))
        keyboard = shop_keyboard(owner_id, page, price, bought=True, free_credits=free_credits)
        try:
            await query.message.edit_reply_markup(reply_markup=keyboard)
        except Exception as e:
            print("Shop bought-button update error:", e)
        await fusion.dt_record_purchase(
            owner_id, rarity, 1, event_id=f"shop:{key}:{page}",
            chat_id=query.message.chat_id if query.message else None,
            name=berry_display_name(query.from_user))  # daily mission progress (never raises)
        return

    if action == "bought":
        await query.answer("ℹ️ This shop character was already bought. Refresh for a new shop.", show_alert=True)
        return

    await query.answer("❌ Unknown shop action.", show_alert=True)

async def daily_shop_reset_job(_context):
    try:
        current_day = shop_rotation_key(datetime.now(IST))
        deleted = (await asyncio.to_thread(_mc("shop_v3").delete_many, {"shop_day": {"$ne": current_day}})).deleted_count
        cutoff = notification_history_cutoff().isoformat()
        history_deleted = (await asyncio.to_thread(_mc("notification_history_v2").delete_many, {"created_at": {"$lt": cutoff}})).deleted_count
        print(f"🛒 Daily shop reset complete for {deleted} shop rows.")
        print(f"🔔 Notification history reset complete for {history_deleted} old rows.")
    except Exception as e:
        print("Daily shop reset error:", e)
    await dm_cleanup()      # also drop DM messages older than 5 days

def _match_rarity(text):
    """'legendary' / 'Mythcal' / 'cel' -> the real tier name, or None."""
    import difflib
    t = (text or "").strip().lower()
    names = list(SYMBOL.keys())
    for n in names:
        if n.lower() == t:
            return n
    pref = [n for n in names if t and n.lower().startswith(t)]
    if len(pref) == 1:
        return pref[0]
    close = difflib.get_close_matches(t, [n.lower() for n in names], n=1, cutoff=0.7)
    return next((n for n in names if n.lower() == close[0]), None) if close else None

async def characters(update, context):
    header = "🎭 Character List"
    if context.args:
        tier = _match_rarity(" ".join(context.args))
        if not tier:
            await safe_reply_text(update.message,
                "❌ Unknown tier. Use: " + ", ".join(SYMBOL.keys()) + "\nExample: /characters legendary")
            return
        rows = [r for r in (await asyncio.to_thread(get_all_characters)) if r[3] == tier]   # full list, not just the spawn pool
        header = f"🎭 {SYMBOL[tier]} {tier} Characters ({len(rows or [])})"
        if not rows:
            await safe_reply_text(update.message, f"❌ No {tier} characters found.")
            return
    else:
        rows = (await asyncio.to_thread(get_all_characters))
        if not rows:
            await safe_reply_text(update.message, "❌ No characters found.")
            return

    # Group by anime: bold anime name on top, its characters below (sorted by code).
    def _code_key(c):
        c = str(c)
        return (0, int(c)) if c.isdigit() else (1, c)
    groups, order = {}, []
    for row in sorted(rows, key=lambda r: _code_key(r[0])):
        anime = (row[2] or "").strip()
        key = anime.lower() if anime and anime.lower() not in ("not set", "none", "-") else ""
        if key not in groups:
            groups[key] = (anime if key else "Not set", [])
            order.append(key)
        groups[key][1].append(row)
    order.sort(key=lambda k: (k == "",))          # "Not set" always last (stable: others keep first-code order)

    def _anime_head(name, cont=False):
        return f"📺 <b>Anime: {html_escape(name)}</b>" + (" <i>(continued)</i>" if cont else "")

    blocks = []                                    # list of (anime_name, [lines])
    number = 0                                     # one running number over the whole list (never restarts per anime)
    for key in order:
        name, members = groups[key]
        block_lines = []
        for (code, cname, _a, r, _w, _p) in members:
            number += 1
            block_lines.append(f"{number}. {rarity_text(r)} {html_escape(str(cname))} [{html_escape(str(code))}]")
        blocks.append((name, block_lines))

    chunk = html_escape(header) + "\n\n"
    for name, block_lines in blocks:
        for idx, line in enumerate(block_lines):
            need_head = idx == 0 or chunk == ""
            head = (_anime_head(name, cont=idx > 0) + "\n") if need_head else ""
            if chunk and len(chunk) + len(head) + len(line) + 1 > 3700:
                await safe_reply_text(update.message, chunk.rstrip(), parse_mode="HTML")
                chunk = ""
                head = _anime_head(name, cont=idx > 0) + "\n"
            chunk += head + line + "\n"
        chunk += "\n"
    if chunk.strip():
        await safe_reply_text(update.message, chunk.rstrip(), parse_mode="HTML")

async def view(update, context):
    (await save_user_async(update.effective_user))
    if not context.args:
        await safe_reply_text(update.message,
            "Usage: /view <4-digit code, first name, last name, or full name>\n"
            "Examples: /view 1001, /view Yuji, /view Itadori, /view Yuji Itadori\n"
            "Anime list: /view (Naruto)"
        )
        return

    query = " ".join(context.args).strip()
    character = None
    anime_query = parse_anime_query(query)

    if anime_query:
        character = await reply_anime_character_list(update, "view", anime_query, owned_only=True)
        if not character:
            return
    elif query.isdigit():
        character = (await asyncio.to_thread(get_character_by_code, query))
    else:
        name_rows = (await asyncio.to_thread(find_characters_by_name_parts, query))
        if name_rows:
            owned = await asyncio.to_thread(_owned_character_codes, update.effective_user.id)
            name_rows = [r for r in name_rows if str(r[0]) in owned]   # /view: only characters in your collection
            if not name_rows:
                await safe_reply_text(update.message, "❌ You don't own any character matching that name.")
                return
        if len(name_rows) == 1:
            character = name_rows[0]
        elif len(name_rows) > 1:
            await safe_reply_text(update.message,
                "❓ Multiple characters found. Select one:",
                reply_markup=character_selection_keyboard(update.effective_user.id, "view", name_rows),
            )
            return

    if not character:
        await safe_reply_text(update.message, "❌ Character not found.")
        return

    await send_character_view_result(context.bot, update.message.chat_id, update.effective_user.id, character, update.message)

async def send_character_view_result(bot, chat_id, user_id, character, source_message=None):
    """The /view result for ONE character (used by /view and by the name-selection buttons)."""
    code, name, anime, rarity, worth, photo = character

    owned = (await asyncio.to_thread(mongo_db.user_owns, user_id, str(code)))
    if not owned:
        await bot.send_message(chat_id=chat_id, text="❌ This character is not in your collection.")
        return

    text = (
        f"🎭 {name}\n"
        f"📺 Anime: {anime or '—'}\n"
        f"🏷 Rarity: {rarity_text(rarity) if rarity else '— Not set'}\n"
        f"💰 Worth: {worth}\n"
        f"🔢 Code: {code}"
    )
    if (await asyncio.to_thread(is_character_discontinued, code)):
        text += "\n🚫 Discontinued — no longer spawns"

    if photo:
        await bot.send_photo(
            chat_id=chat_id,
            photo=photo,
            caption=add_display_name_header(source_message, text) if source_message else text,
            parse_mode="HTML",
        )
    else:
        text += "\n📷 Photo: Not added"
        await bot.send_message(chat_id=chat_id, text=add_display_name_header(source_message, text) if source_message else text)

# ---------------------------------------------------------------------------
# Broadcast (/help -> 📣 Broadcast): targets -> message -> pin -> summary -> Confirm.
# Owner and Executive, private chat only. The message is copied, so text, media and formatting all work.
# ---------------------------------------------------------------------------
BC_PAGE, BC_DELAY, BC_COLL = 8, 0.15, "broadcast_report"
_bc_state = {}   # user id -> the broadcast being prepared
_bc_job = None   # the broadcast that is sending now (one at a time)


def _bc_ok(uid):
    return is_owner(uid) or is_executive(uid)

def _bc_n(n):
    return f"{n} group{'' if n == 1 else 's'}"

def _bc_short(title, n=28):
    title = (title or "?").strip() or "?"
    return title if len(title) <= n else title[:n - 1] + "…"

def _bc_btn(label, data):
    return InlineKeyboardButton(label, callback_data=data)

def _bc_kb(*rows):
    return InlineKeyboardMarkup([list(r) for r in rows])

def _bc_step(st):
    if st["mode"] is None:
        return "target"
    if st["mode"] == "pick" and not st["done"]:
        return "pick"
    if st["msg"] is None or st["wait"]:
        return "msg"
    if st["pin"] is None or st["ask"]:
        return "pin"
    return "sum"

def _bc_who(st, long=False):
    if st["mode"] == "all":
        return f"All groups ({len(st['groups'])})" if long else f"all {_bc_n(len(st['groups']))}"
    names = [html_escape(_bc_short(t, 40)) for c, t in st["groups"] if c in st["sel"]]
    if not long:
        return f"{_bc_n(len(names))} selected"
    more = f"\n   …and {len(names) - 10} more" if len(names) > 10 else ""
    return f"{_bc_n(len(names))} selected:\n" + "\n".join(f"   • {n}" for n in names[:10]) + more

def _bc_panel(uid):
    text = ("<b>📣 Broadcast</b>\n\nSend one message to every group the bot is in, or only to the groups you choose."
            + ("\n\n⏳ A broadcast is sending right now." if _bc_job else ""))
    return text, _bc_kb([_bc_btn("✍️ New Broadcast", "bc:new")], [_bc_btn("📜 Last Report", "bc:last")],
                        [_bc_btn("🔙 Back", "bc:h")])

def _bc_hub(uid):
    role = "owner" if is_owner(uid) else "executive"
    rows = [[_bc_btn("📣 Broadcast", "bc:m")], [_bc_btn("💬 DM", "dm:m")]]      # same buttons for the owner and executives
    return "<b>📣 Broadcast & DM</b>\n\nChoose what you want to do.", _bc_kb(*rows, [_bc_btn("🔙 Back", f"help:{uid}:{role}")])

def _bc_screen(st):
    """(text, keyboard) for the step the broadcast is on."""
    step, n = _bc_step(st), len(st["groups"])
    cancel = _bc_btn("❌ Cancel", "bc:x")
    back = _bc_btn("🔙 Back to summary", "bc:sum") if st["snap"] else cancel
    if step == "sum" and st["menu"]:
        return "<b>✏️ What do you want to change?</b>", _bc_kb(
            [_bc_btn("🎯 Targets", "bc:et")], [_bc_btn("📝 Message", "bc:em")], [_bc_btn("📌 Pin", "bc:ep")],
            [_bc_btn("🔙 Back to summary", "bc:sum")])
    if step == "target":
        return (f"<b>📣 Broadcast: who gets it?</b>\n\nThe bot is in <b>{_bc_n(n)}</b>.\n"
                "Send it to all of them, or pick one or more groups."), _bc_kb(
            [_bc_btn(f"🌐 All groups ({n})", "bc:ta")], [_bc_btn("🎯 Specific groups", "bc:tp")], [back])
    if step == "pick":
        pages = max(1, -(-n // BC_PAGE))
        st["page"] = min(max(st["page"], 0), pages - 1)
        first = st["page"] * BC_PAGE
        rows = [[_bc_btn(("✅ " if st["groups"][i][0] in st["sel"] else "⬜ ") + _bc_short(st["groups"][i][1]), f"bc:g:{i}")]
                for i in range(first, min(first + BC_PAGE, n))]
        if pages > 1:
            rows.append([_bc_btn("◀", f"bc:pg:{st['page'] - 1}"), _bc_btn(f"{st['page'] + 1}/{pages}", "bc:noop"),
                         _bc_btn("▶", f"bc:pg:{st['page'] + 1}")])
        rows += [[_bc_btn("☑️ Select all", "bc:sa"), _bc_btn("🧹 Clear", "bc:cl")],
                 [_bc_btn(f"✅ Done ({len(st['sel'])})", "bc:dn")],
                 [_bc_btn("🔙 Back", "bc:bk"), cancel]]
        return (f"<b>🎯 Pick the groups</b>\n\nTap a group to select or unselect it. "
                f"Selected: <b>{len(st['sel'])}</b> of {n}."), _bc_kb(*rows)
    if step == "msg":
        return (f"<b>📝 Send the message</b>\n\nTargets: <b>{html_escape(_bc_who(st))}</b>\n\n"
                "Now send me the message you want to broadcast, here in this chat. Text, photo, video or a file all "
                "work, and the formatting is kept."), _bc_kb([back])
    if step == "pin":
        return ("<b>📌 Pin the message?</b>\n\nShould the bot pin it in each group? A group where the bot has no pin "
                "right still gets the message, just not pinned."), _bc_kb(
            [_bc_btn("✅ Yes, pin it", "bc:py"), _bc_btn("❌ No", "bc:pn")], [back])
    info = st["msg"]
    preview = html_escape(info["text"][:120]) + ("…" if len(info["text"]) > 120 else "")
    return (f"<b>📋 Broadcast summary</b>\n\n🎯 <b>Groups:</b> {_bc_who(st, True)}\n\n"
            f"📝 <b>Message:</b> {info['kind']}" + (f"\n<i>{preview}</i>" if preview else "") + "\n\n"
            f"📌 <b>Pin:</b> {'ON' if st['pin'] else 'OFF'}\n\nCheck everything, then confirm."), _bc_kb(
        [_bc_btn("✅ Confirm", "bc:ok")], [_bc_btn("✏️ Edit", "bc:ed"), cancel])

async def _bc_render(context, uid, q=None):
    """Show the current screen: edit the tapped message (q), or send a new one under the user's message."""
    st = _bc_state[uid]
    text, markup = _bc_screen(st)
    if q is not None:
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup, disable_web_page_preview=True)
        except TelegramError:
            pass                                    # unchanged (double tap) or too old to edit
        st["panel"] = (q.message.chat.id, q.message.message_id)
        return
    sent = await context.bot.send_message(st["panel"][0], text, parse_mode="HTML", reply_markup=markup,
                                          disable_web_page_preview=True)
    st["panel"] = (sent.chat_id, sent.message_id)

def _bc_report_text(rep):
    when = datetime.fromtimestamp(rep.get("time", 0), IST).strftime("%d %b %Y, %I:%M %p")
    lines = [f"<b>{'⏹ Broadcast stopped' if rep.get('stopped') else '📣 Broadcast finished'}</b>", f"🕒 {when} IST", "",
             f"✅ Sent: <b>{rep.get('sent', 0)}</b> of {rep.get('total', 0)}",
             f"❌ Failed: <b>{len(rep.get('failed', []))}</b>"]
    if rep.get("pin"):
        lines.append(f"📌 Pinned: <b>{rep.get('pinned', 0)}</b> (pin failed: {rep.get('pin_failed', 0)})")
    failed = rep.get("failed", [])
    if failed:
        lines += ["", "<b>Failed groups:</b>"] + [f"• {html_escape(_bc_short(t, 30))}: {html_escape(r)}" for t, r in failed[:10]]
        if len(failed) > 10:
            lines.append(f"…and {len(failed) - 10} more")
    return "\n".join(lines)

def _bc_wait(exc):
    value = getattr(exc, "retry_after", 1)
    return min(float(value.total_seconds() if hasattr(value, "total_seconds") else value) + 1, 60)

async def _bc_send_one(bot, job, cid, title):
    target = cid
    for _ in range(3):
        try:
            sent = await bot.copy_message(target, job["src_chat"], job["src_msg"])
            break
        except RetryAfter as e:
            await asyncio.sleep(_bc_wait(e))
        except ChatMigrated as e:
            target = e.new_chat_id
        except Forbidden:
            job["failed"].append((title, "bot was removed or can't write"))
            return
        except TelegramError as e:
            job["failed"].append((title, str(e)[:40] or type(e).__name__))
            return
    else:
        job["failed"].append((title, "Telegram asked to wait too often"))
        return
    job["sent"] += 1
    if job["pin"]:
        try:
            await bot.pin_chat_message(target, sent.message_id)
            job["pinned"] += 1
        except TelegramError:
            job["pin_failed"] += 1

async def _bc_progress(bot, job, force=False):
    if not force and time.monotonic() - job["edited"] < 4:
        return
    job["edited"] = time.monotonic()
    text = (f"<b>📤 Broadcasting…</b>\n\nDone: <b>{job['done']}</b> of {len(job['targets'])}\n"
            f"✅ Sent: {job['sent']}\n❌ Failed: {len(job['failed'])}"
            + (f"\n📌 Pinned: {job['pinned']}" if job["pin"] else ""))
    try:
        await bot.edit_message_text(text, chat_id=job["panel"][0], message_id=job["panel"][1], parse_mode="HTML",
                                    reply_markup=_bc_kb([_bc_btn("⏹ Stop", "bc:stop")]))
    except TelegramError:
        pass

async def _bc_run(bot, job):
    global _bc_job
    try:
        await _bc_progress(bot, job, force=True)
        for cid, title in job["targets"]:
            if job["stop"]:
                break
            await _bc_send_one(bot, job, cid, title)
            job["done"] += 1
            await _bc_progress(bot, job)
            await asyncio.sleep(BC_DELAY)
    except Exception as e:
        print("Broadcast stopped by an error:", e)
    finally:
        rep = {"time": int(time.time()), "total": len(job["targets"]), "sent": job["sent"],
               "failed": [[t, r] for t, r in job["failed"][:30]], "pin": job["pin"], "pinned": job["pinned"],
               "pin_failed": job["pin_failed"], "stopped": job["stop"] or job["done"] < len(job["targets"])}
        _bc_job = None
        try:
            await asyncio.to_thread(_mc(BC_COLL).replace_one, {"_id": "last"}, {"_id": "last", **rep}, True)
        except Exception as e:
            print("Broadcast report save error:", e)
        text, kb = _bc_report_text(rep), _bc_kb([_bc_btn("🔙 Back", "bc:m")])
        try:
            await bot.edit_message_text(text, chat_id=job["panel"][0], message_id=job["panel"][1],
                                        parse_mode="HTML", reply_markup=kb)
        except TelegramError:
            try:
                await bot.send_message(job["panel"][0], text, parse_mode="HTML", reply_markup=kb)
            except TelegramError:
                pass

async def _bc_groups():
    groups = await asyncio.to_thread(load_bot_groups) or {}
    return sorted(((int(c), (i or {}).get("title") or str(c)) for c, i in groups.items()), key=lambda g: g[1].lower())

async def bc_callback(update, context):
    global _bc_job
    q, uid = update.callback_query, update.callback_query.from_user.id
    if not _bc_ok(uid):
        await q.answer(UNAUTHORIZED_TEXT, show_alert=True)
        return
    chat = q.message.chat if q.message else None
    if chat is None or chat.type != "private":
        await q.answer("Open me in a private chat to broadcast: /help → Owner Commands → 📣 Broadcast.", show_alert=True)
        return
    parts = (q.data or "").split(":")
    act, arg = parts[1] if len(parts) > 1 else "m", parts[2] if len(parts) > 2 else ""

    async def show(text, markup):
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup)
        except TelegramError:
            pass

    if act == "noop":
        await q.answer()
        return
    if act == "h":
        await q.answer()
        await show(*_bc_hub(uid))
        return
    if act == "m":
        await q.answer()
        await show(*_bc_panel(uid))
        return
    if act == "last":
        rep = await asyncio.to_thread(_mc(BC_COLL).find_one, {"_id": "last"})
        await q.answer()
        await show(_bc_report_text(rep) if rep else "There is no broadcast report yet.", _bc_kb([_bc_btn("🔙 Back", "bc:m")]))
        return
    if act == "stop":
        if _bc_job:
            _bc_job["stop"] = True
        await q.answer("Stopping…" if _bc_job else "Nothing is sending right now.")
        return
    if act == "new":
        if _bc_job:
            await q.answer("A broadcast is already sending. Wait until it finishes.", show_alert=True)
            return
        groups = await _bc_groups()
        if not groups:
            await q.answer("The bot is not in any group yet.", show_alert=True)
            return
        _bc_state[uid] = {"groups": groups, "panel": (chat.id, q.message.message_id), "mode": None, "sel": set(),
                          "done": False, "page": 0, "msg": None, "pin": None, "wait": False, "ask": False,
                          "menu": False, "snap": None}
        await q.answer()
        await _bc_render(context, uid, q)
        return

    st = _bc_state.get(uid)
    if st is None:
        await q.answer("This broadcast is no longer active. Please start again.", show_alert=True)
        await show(*_bc_panel(uid))
        return
    if act == "x":
        _bc_state.pop(uid, None)
        await q.answer("Cancelled.")
        await show(*_bc_panel(uid))
        return
    st["menu"] = False
    if act == "ta":
        st["mode"] = "all"
    elif act == "tp":
        st["mode"], st["done"], st["page"] = "pick", False, 0
    elif act == "bk":
        st["mode"] = None
    elif act == "g" and arg.isdigit() and int(arg) < len(st["groups"]):
        st["sel"] ^= {st["groups"][int(arg)][0]}
    elif act == "pg" and arg.lstrip("-").isdigit():
        st["page"] = int(arg)
    elif act == "sa":
        st["sel"] = {c for c, _ in st["groups"]}
    elif act == "cl":
        st["sel"] = set()
    elif act == "dn":
        if not st["sel"]:
            await q.answer("Pick at least one group first.", show_alert=True)
            return
        st["done"] = True
    elif act in ("py", "pn"):
        st["pin"], st["ask"] = act == "py", False
    elif act == "ed":
        st["menu"] = True
    elif act in ("et", "em", "ep"):
        st["snap"] = (st["mode"], set(st["sel"]), st["done"], st["msg"], st["pin"])    # "Back to summary" restores it
        if act == "et":
            st["mode"], st["done"] = None, False
        else:
            st["wait" if act == "em" else "ask"] = True
    elif act == "sum":
        if st["snap"]:
            st["mode"], st["sel"], st["done"], st["msg"], st["pin"] = st["snap"]
        st["snap"], st["wait"], st["ask"] = None, False, False
    elif act == "ok":
        if _bc_step(st) != "sum":
            await q.answer("Please finish the steps first.", show_alert=True)
            return
        if _bc_job:
            await q.answer("A broadcast is already sending. Wait until it finishes.", show_alert=True)
            return
        targets = (st["groups"] if st["mode"] == "all" else [g for g in st["groups"] if g[0] in st["sel"]])
        _bc_job = {"targets": targets, "src_chat": st["msg"]["chat_id"], "src_msg": st["msg"]["message_id"],
                   "pin": bool(st["pin"]), "panel": (chat.id, q.message.message_id), "stop": False, "done": 0,
                   "sent": 0, "failed": [], "pinned": 0, "pin_failed": 0, "edited": 0.0}
        _bc_state.pop(uid, None)
        await q.answer("Sending…")
        asyncio.create_task(_bc_run(context.bot, _bc_job))
        return
    else:
        await q.answer()
        return
    if _bc_step(st) == "sum" and not st["menu"]:
        st["snap"] = None                       # the edit is finished
    await q.answer()
    await _bc_render(context, uid, q)

async def bc_message(update, context):
    """The message sent after 'Send the message'. Ignored unless a broadcast is waiting for it."""
    msg, user = update.effective_message, update.effective_user
    st = _bc_state.get(user.id) if msg and user else None
    if st is None or _bc_step(st) != "msg" or not _bc_ok(user.id):
        return
    kind = next((k for k in ("photo", "video", "animation", "document", "audio", "voice", "video_note", "sticker",
                             "poll") if getattr(msg, k, None)), "text")
    st["msg"] = {"chat_id": msg.chat_id, "message_id": msg.message_id, "kind": kind,
                 "text": (msg.text or msg.caption or "").strip()}
    st["wait"] = False
    if _bc_step(st) == "sum":
        st["snap"] = None
    await _bc_render(context, user.id)


# ---------------------------------------------------------------------------
# DM (/help -> 📣 Broadcast -> 💬 DM, Owner and Executives): message one user through the bot and read the chat.
# An executive's DM is copied automatically to the owner and the other executives. The owner's DM is copied to the executives
# only if the owner presses 📤 Send. Executives see in History only what is shared with them (rows with "vis"), and cannot 🗑 Remove chats.
# A user's message reaches the owner ONLY when they swipe-reply to one of the owner's DMs or use /reply. Everything is saved in dm_log.
# A user can only be messaged after they pressed Start in the bot (Telegram rule).
# ---------------------------------------------------------------------------
DM_COLL, DM_PAGE = "dm_log", 10
DM_KEEP, DM_COUNTER, DM_LIST_PAGE = 5 * 24 * 3600, "dm_counter", 10   # DM messages are kept for 5 days only
_dm_state = {}   # staff id -> {"step": "id" | "hist" | "msg" | "all" | "allc" (DM All), "to": user id, "ctx": Idea/Issue/Appeal, "ref": member message, "t": when}
DM_NOTIF, DM_STATE_TTL = "dm_notif", 600   # notification message -> what it belongs to (for swipe-reply); a pending "send your reply" expires after 10 min
_dm_shared = set()                          # (user id, message id) already copied to the executives
_DM_LABELS = {"photo": "📷 photo", "video": "🎬 video", "animation": "🎞 gif", "document": "📄 file", "audio": "🎵 audio",
              "voice": "🎤 voice", "video_note": "⏺ video note", "sticker": "🏷 sticker", "poll": "📊 poll"}

def _dm_kind(msg):
    return next((k for k in _DM_LABELS if getattr(msg, k, None)), "text")

async def _dm_name(uid):
    try:
        row = (await asyncio.to_thread(mongo_db.get_users_by_ids, [uid]) or {}).get(uid) or ("", "", "")
    except Exception:
        row = ("", "", "")
    return " ".join(p for p in row[:2] if p).strip() or f"User {uid}"

DM_UNKNOWN_TEXT = ("⚠️ I couldn't find that user. Send a numeric user ID, or the @username of someone who has used "
                   "the bot before.")

async def _dm_target(text):
    """User ID from '123456' or '@username'. A username must belong to exactly one person who used the bot."""
    text = (text or "").strip()
    if text.lstrip("-").isdigit():
        return int(text)
    name = text.lstrip("@")
    if not re.fullmatch(r"[A-Za-z0-9_]{4,32}", name):
        return None
    rows = await asyncio.to_thread(lambda: list(mongo_db.col(mongo_db.USERS).find(
        {"username": {"$regex": f"^{name}$", "$options": "i"}}, {"_id": 1}).limit(2)))
    return rows[0]["_id"] if len(rows) == 1 else None

def _dm_cutoff():
    return int(time.time()) - DM_KEEP

async def dm_cleanup():
    """Delete DM messages older than 5 days (runs at startup and every day)."""
    try:
        res = await asyncio.to_thread(_mc(DM_COLL).delete_many, {"t": {"$lt": _dm_cutoff()}})
        await asyncio.to_thread(_mc(DM_NOTIF).delete_many, {"t": {"$lt": _dm_cutoff()}})
        if res.deleted_count:
            print(f"💬 DM cleanup removed {res.deleted_count} old messages.")
    except Exception as e:
        print("DM cleanup error:", e)

def _dm_preview(m):
    """Short text of a Telegram message: its text/caption, or a label for media."""
    if m is None:
        return ""
    t = (getattr(m, "text", None) or getattr(m, "caption", None) or "").strip()
    if t:
        return t
    k = _dm_kind(m)
    return _DM_LABELS.get(k, "") if k != "text" else ""

async def _dm_next_n(uid):
    """Next message number (#1, #2, ...) in the chat with this user."""
    try:
        from pymongo import ReturnDocument
        doc = await asyncio.to_thread(lambda: _mc(DM_COUNTER).find_one_and_update(
            {"_id": uid}, {"$inc": {"n": 1}}, upsert=True, return_document=ReturnDocument.AFTER))
        return int(doc["n"])
    except Exception as e:
        print("DM counter error:", e)
        return None

async def _dm_log(uid, out, kind, text, mid=None, reply_n=None, reply_prev="", n=None, mid2=None, about=False,
                  by=None, byn="", ctx=None, vis=False):
    if n is None:
        n = await _dm_next_n(uid)
    row = {"uid": uid, "out": out, "kind": kind, "text": text[:500], "t": int(time.time())}
    if n is not None:
        row["n"] = n                          # message number in this chat
    if mid is not None:
        row["mid"] = mid                      # message id in the user's Telegram chat (used to match replies)
    if mid2 is not None:
        row["mid2"] = mid2                    # id of the small "#n" line sent after a sticker/poll/long message
    if reply_n is not None:
        row["rto"] = reply_n                  # number of YOUR message they replied to
    if reply_prev:
        row["rprev"] = reply_prev[:100]
    if about:
        row["rabout"] = True                  # they pointed at a normal bot message with /reply
    if by is not None:
        row["by"] = by                        # staff member who sent it (owner or executive)
        if byn:
            row["byn"] = byn                  # executive's display name
    if ctx:
        row["ctx"] = ctx                      # what it answered, e.g. "Idea #3"
    if vis:
        row["vis"] = True                     # executives may see this message in History
    try:
        await asyncio.to_thread(_mc(DM_COLL).insert_one, row)
    except Exception as e:
        print("DM log error:", e)
    return n

_DM_CAPTIONABLE = {"photo", "video", "animation", "document", "audio", "voice"}

def _dm_header(n, sender):
    """Top line of a staff message: the owner writes as Team Anime Bot, an executive as 'Replied by Executive <name>'."""
    if sender and sender.get("role") == "executive":
        who = f"Executive {sender.get('name') or ''}".strip()
        return f"📩 Replied by {who} · #{n}"
    return f"📩 Message from Team Anime Bot · #{n}"

def _dm_guide(n):
    return f"💬 How to reply\n\n1. Swipe-reply to this message\n\n2. Or send /reply {n} and then your message"

def _dm_re_block(ctx, ref):
    """'↩️ Re: your Idea #3' + a short quote of it, when the staff message answers something specific."""
    if ctx:
        label, prev = f"your {ctx['label']}", (ctx.get("text") or "")
    elif ref is not None and ref.get("n") is not None:
        label = f"your message #{ref['n']}"
        prev = (ref.get("text") or "").strip() or _DM_LABELS.get(ref.get("kind"), "")
    else:
        return ""
    prev = " ".join(prev.split())
    short = prev[:100] + ("…" if len(prev) > 100 else "")
    return f"↩️ Re: {label}" + (f'\n"{short}"' if short else "")

def _dm_u16(s):
    """Length in UTF-16 units (what Telegram uses for entity offsets)."""
    return len(s.encode("utf-16-le")) // 2

def _dm_shift(entities, delta):
    """The message's formatting entities moved `delta` units to the right (text was added in front). None if none/failed."""
    out = []
    try:
        from telegram import MessageEntity
        for e in entities or ():
            d = e.to_dict()
            d["offset"] = e.offset + delta
            out.append(MessageEntity.de_json(d, None))
    except Exception:
        return None
    return out or None

async def _dm_find_sent(uid, mid):
    """The owner's DM (log row) that has this message id in the user's chat, or None."""
    try:
        return await asyncio.to_thread(lambda: _mc(DM_COLL).find_one(
            {"uid": uid, "out": True, "t": {"$gte": _dm_cutoff()}, "$or": [{"mid": mid}, {"mid2": mid}]}))
    except Exception:
        return None

async def _dm_find_n(uid, n):
    """The owner's DM number `n` to this user, or None."""
    try:
        return await asyncio.to_thread(lambda: _mc(DM_COLL).find_one(
            {"uid": uid, "out": True, "n": n, "t": {"$gte": _dm_cutoff()}}))
    except Exception:
        return None

async def _exec_ids():
    """Executive user ids (fixed list + stored roles), without the owner."""
    ids = {int(u) for u in EXECUTIVE_IDS}
    try:
        for staff_id, role in await asyncio.to_thread(_staff_role_rows):
            if role == "executive":
                ids.add(int(staff_id))
    except Exception as e:
        print("Executive list error:", e)
    if ADMIN_IDS:
        ids.discard(int(ADMIN_IDS[0]))
    return ids

async def _is_exec(uid):
    return int(uid) in await _exec_ids()

async def _dm_find_in(uid, n):
    """The member's own message number `n` in the chat (log row), or None."""
    if n is None:
        return None
    try:
        return await asyncio.to_thread(lambda: _mc(DM_COLL).find_one(
            {"uid": uid, "out": False, "n": n, "t": {"$gte": _dm_cutoff()}}))
    except Exception:
        return None

async def _dm_note(staff_id, mids, uid, n=None, ctx=None):
    """Remember what these messages in a staff chat belong to (member message n, or Idea/Issue/Appeal like 'i3'),
    so swiping on them answers exactly that."""
    rows = [dict({"chat": staff_id, "mid": m, "uid": uid, "t": int(time.time())},
                 **({"n": n} if n is not None else {}), **({"ctx": ctx} if ctx else {})) for m in mids if m]
    if rows:
        try:
            await asyncio.to_thread(_mc(DM_NOTIF).insert_many, rows)
        except Exception as e:
            print("DM note error:", e)

async def _dm_note_find(staff_id, mid):
    try:
        return await asyncio.to_thread(lambda: _mc(DM_NOTIF).find_one({"chat": staff_id, "mid": mid}))
    except Exception:
        return None

async def _dm_item_ctx(uid, kind_letter, item_id):
    """{"label": "Idea #3", "text": ...} for an Idea (i) / Issue (s) / Appeal (a) that this member sent, or None."""
    spec = {"i": ("ideas_v2", "idea_text", "Idea"), "s": ("issues_v2", "issue_text", "Issue"),
            "a": ("appeals_v2", "appeal_text", "Appeal")}.get(kind_letter)
    if spec is None:
        return None
    try:
        row = await asyncio.to_thread(lambda: _mc(spec[0]).find_one({"_id": item_id}))
    except Exception:
        return None
    if not row or int(row.get("user_id", -1)) != int(uid):
        return None
    return {"label": f"{spec[2]} #{item_id}", "text": row.get(spec[1]) or ""}

async def _dm_send(context, uid, src=None, text=None, sender=None, ctx=None, ref=None):
    """Send a copy of message `src` (or plain `text`) to the member as:
        📩 Message from Team Anime Bot · #3  /  [↩️ Re: your Idea #3]  /  the message  /  💬 How to reply + steps
    (an executive's message says 'Replied by Executive <name>'). Returns {"mid", "mid2", "n"} = what the member
    received, or None if they never started the bot or blocked it."""
    sender = sender or {"id": ADMIN_IDS[0] if ADMIN_IDS else None, "role": "owner", "name": ""}
    n = await _dm_next_n(uid)
    kind = _dm_kind(src) if src is not None else "text"
    body = ((src.text or src.caption or "") if src is not None else text).strip()
    re_block = _dm_re_block(ctx, ref)
    head, guide = (_dm_header(n, sender), _dm_guide(n)) if n is not None else ("", "")
    pre = f"{head}\n\n" + (f"{re_block}\n\n" if re_block else "")
    sent = sent2 = None
    try:
        try:
            if head and (src is None or src.text):
                plain = src.text if src is not None else text
                full = f"{pre}{plain}\n\n\n{guide}"
                if len(full) <= 4096:
                    ents = _dm_shift(src.entities, _dm_u16(pre)) if src is not None else None
                    sent = await context.bot.send_message(uid, full, entities=ents)
            elif head and kind in _DM_CAPTIONABLE:
                cap_body = src.caption or ""
                cap = f"{pre}{cap_body}\n\n\n{guide}" if cap_body else f"{pre}{guide}"
                if len(cap) <= 1024:
                    ents = _dm_shift(src.caption_entities, _dm_u16(pre)) if cap_body else None
                    sent = await context.bot.copy_message(uid, src.chat_id, src.message_id, caption=cap, caption_entities=ents)
        except TelegramError:
            sent = None
        if sent is None:      # sticker, poll, video note, too long...: plain copy + a small message with the header and steps
            if src is not None:
                sent = await context.bot.copy_message(uid, src.chat_id, src.message_id)
            else:
                sent = await context.bot.send_message(uid, text)
            if head:
                try:
                    sent2 = await context.bot.send_message(uid, f"{pre}{guide}")
                except TelegramError:
                    sent2 = None
    except TelegramError:
        return None
    mid, mid2 = getattr(sent, "message_id", None), getattr(sent2, "message_id", None)
    is_exec = sender.get("role") == "executive"
    await _dm_log(uid, True, kind, body, mid=mid, n=n, mid2=mid2, by=sender.get("id"),
                  byn=(sender.get("name") or "Executive") if is_exec else "",
                  ctx=(ctx or {}).get("label"), reply_n=(ref or {}).get("n"), vis=is_exec)
    return {"mid": mid, "mid2": mid2, "n": n}

def _dm_staff_kb(rid, uid):
    """Buttons on a copy of a sent message: the owner gets everything, an executive only ✍️ Reply."""
    if is_owner(rid):
        return _bc_kb([_bc_btn("✍️ Reply", f"dm:r:{uid}"), _bc_btn("📜 History", f"dm:h:{uid}:0")],
                      [_bc_btn("🗑 Remove", f"dm:d:{uid}")])
    return _bc_kb([_bc_btn("✍️ Reply", f"dm:rm:{uid}:0")])

# What an executive may see in History: executives' own messages, owner DMs the owner shared (📤 Send), and members' messages
# that do not answer a hidden owner DM.
_DM_EXEC_VIS = {"$or": [{"vis": True}, {"byn": {"$exists": True}}]}

async def _dm_mark_visible(uid, row):
    """The owner pressed 📤 Send: executives may now see this DM and the member's replies to it in History."""
    try:
        await asyncio.to_thread(_mc(DM_COLL).update_one, {"_id": row["_id"]}, {"$set": {"vis": True}})
        if row.get("n") is not None:
            await asyncio.to_thread(_mc(DM_COLL).update_many, {"uid": uid, "out": False, "rto": row["n"]}, {"$set": {"vis": True}})
    except Exception as e:
        print("DM visibility error:", e)

async def _dm_staff_ok(uid):
    return is_owner(uid) or await _is_exec(uid)

async def _dm_share(context, uid, res, recipients):
    """Copy exactly what the member received to these staff ids, with a '📤 Sent to ...' line first."""
    name = await _dm_name(uid)
    failed = []
    for rid in recipients:
        try:
            await context.bot.send_message(rid, f"📤 Sent to {name} (ID {uid})")
            copy = await context.bot.copy_message(rid, uid, res["mid"], reply_markup=_dm_staff_kb(rid, uid))
            ids = [copy.message_id]
            if res.get("mid2"):
                ids.append((await context.bot.copy_message(rid, uid, res["mid2"])).message_id)
            await _dm_note(rid, ids, uid)
        except TelegramError as e:
            failed.append(rid)
            print(f"DM share error ({rid}):", e)
    return failed

async def _dm_share_alert(context, sender, uid, preview, failed):
    """An executive's DM could not be copied to everyone: tell the owner, with the message text, so nothing goes unseen."""
    if not ADMIN_IDS:
        return
    owner_id = int(ADMIN_IDS[0])
    name = html_escape(await _dm_name(uid))
    who = html_escape((sender.full_name or "").strip() or str(sender.id))
    lines = ["⚠️ <b>Copy failed</b>",
             f"Executive <b>{who}</b> (<code>{sender.id}</code>) sent a DM to <b>{name}</b> (<code>{uid}</code>)."]
    if owner_id in failed:
        lines.append("The copy to you did not arrive.")
    others = [i for i in failed if i != owner_id]
    if others:
        lines.append("Copy failed for: " + ", ".join(f"<code>{i}</code>" for i in others))
    if preview:
        lines.append("\nMessage:\n" + html_escape(preview[:600]))
    try:
        await context.bot.send_message(owner_id, "\n".join(lines), parse_mode="HTML")
    except TelegramError as e:
        print("DM share alert error:", e)

async def _dm_staff_send(msg, context, user, uid, src=None, text=None, ctx=None, ref=None):
    """The owner or an executive writes to member `uid`. Owner: then 📤 Send / 🚫 Don't send (copy to executives).
    Executive: the owner and the other executives get the same message automatically."""
    owner = is_owner(user.id)
    sender = {"id": user.id, "role": "owner" if owner else "executive", "name": (user.full_name or "").strip()}
    name = html_escape(await _dm_name(uid))
    res = await _dm_send(context, uid, src, text, sender=sender, ctx=ctx, ref=ref)
    if not res:
        await safe_reply_text(msg, f"❌ Couldn't send to <b>{name}</b>. They haven't pressed Start in the bot, or they blocked it.",
                              parse_mode="HTML")
        return
    execs = await _exec_ids()
    if owner:
        if execs and res.get("mid"):
            kb = _bc_kb([_bc_btn("📤 Send", f"dm:sy:{uid}:{res['mid']}"), _bc_btn("🚫 Don't send", f"dm:sn:{uid}:{res['mid']}")])
            await safe_reply_text(msg, f"✅ Sent to <b>{name}</b>.\n\nShow this reply to executives?", parse_mode="HTML", reply_markup=kb)
        else:
            await safe_reply_text(msg, f"✅ Sent to <b>{name}</b>.", parse_mode="HTML")
        return
    await safe_reply_text(msg, f"✅ Sent to <b>{name}</b>.", parse_mode="HTML")
    others = ([int(ADMIN_IDS[0])] if ADMIN_IDS else []) + sorted(execs - {user.id})
    failed = await _dm_share(context, uid, res, others)
    if failed:      # a copy did not arrive: alert the owner (with the message text) so an executive's DM never goes unseen
        await _dm_share_alert(context, user, uid, _dm_preview(src) if src is not None else (text or ""), failed)

async def _dm_history(uid, page, viewer=None):
    """(text, keyboard) with the chat, newest page first (10 messages per page, oldest at the top of each page).
    viewer = the staff member looking at it; an executive only sees what is shared with executives."""
    exec_view = viewer is not None and not is_owner(viewer)
    flt = {"uid": uid, "t": {"$gte": _dm_cutoff()}, **(_DM_EXEC_VIS if exec_view else {})}
    rows = await asyncio.to_thread(lambda: list(
        _mc(DM_COLL).find(flt).sort("t", -1).skip(page * DM_PAGE).limit(DM_PAGE + 1)))
    more, rows = len(rows) > DM_PAGE, rows[:DM_PAGE][::-1]
    name = html_escape(await _dm_name(uid))
    if rows:
        lines = []
        for r in rows:
            body = html_escape((r.get("text") or "")[:150])
            if r.get("kind", "text") != "text":
                body = (_DM_LABELS.get(r["kind"], r["kind"]) + " " + body).strip()
            num = f"#{r['n']} " if r.get("n") is not None else ""
            ref = ""
            if r.get("ctx"):
                ref = f" (↩️ {html_escape(r['ctx'])})"
            elif r.get("rto") is not None:
                ref = f" (↩️ #{r['rto']})"
            elif not r["out"] and r.get("rabout"):
                ref = " (↩️ bot msg)"
            elif not r["out"] and r.get("rprev"):
                ref = " (↩️ reply)"
            if not r["out"]:
                who = name
            elif r.get("byn"):
                who = "You" if exec_view and r.get("by") == viewer else f"Exec {html_escape(r['byn'])}"
            else:
                who = "Owner" if exec_view else "You"
            lines.append(f"🕒 {datetime.fromtimestamp(r['t'], IST).strftime('%d %b, %I:%M %p')}\n"
                         f"<b>{num}{who}</b>{ref}: {body}")
        text = f"<b>📜 Chat with {name}</b> (<code>{uid}</code>)\n\n" + "\n\n".join(lines)
    else:
        text = f"📜 No messages with <b>{name}</b> in the last 5 days."
    nav = ([_bc_btn("◀ Older", f"dm:h:{uid}:{page + 1}")] if more else []) + \
          ([_bc_btn("Newer ▶", f"dm:h:{uid}:{page - 1}")] if page else [])
    actions = [_bc_btn("✍️ Reply", f"dm:r:{uid}")] + ([_bc_btn("🗑 Remove", f"dm:dh:{uid}")] if rows and not exec_view else [])
    return text, _bc_kb(*([nav] if nav else []), actions, [_bc_btn("🔙 Back", "dm:l:0")])

def _dm_ago(t):
    d = max(0, int(time.time()) - int(t))
    if d < 60:
        return "just now"
    if d < 3600:
        return f"{d // 60} min ago"
    if d < 86400:
        return f"{d // 3600} h ago"
    return f"{d // 86400} d ago"

async def _dm_list(page, viewer=None):
    """(text, keyboard): everyone you messaged or who messaged you in the last 5 days, newest first.
    An executive only sees chats that have something shared with executives."""
    cutoff = _dm_cutoff()
    match = {"t": {"$gte": cutoff}, **(_DM_EXEC_VIS if viewer is not None and not is_owner(viewer) else {})}
    rows = await asyncio.to_thread(lambda: list(_mc(DM_COLL).aggregate([
        {"$match": match},
        {"$sort": {"t": -1}},
        {"$group": {"_id": "$uid", "t": {"$first": "$t"}, "out": {"$first": "$out"}}},
        {"$sort": {"t": -1}},
        {"$skip": page * DM_LIST_PAGE},
        {"$limit": DM_LIST_PAGE + 1},
    ])))
    more, rows = len(rows) > DM_LIST_PAGE, rows[:DM_LIST_PAGE]
    find_row = [_bc_btn("🔎 Find by ID/@username", "dm:hist")]
    back_row = [_bc_btn("🔙 Back", "dm:m")]
    if not rows:
        return ("<b>📜 DM History</b>\n\nNo chats in the last 5 days.", _bc_kb(find_row, back_row))
    try:
        names = await asyncio.to_thread(mongo_db.get_users_by_ids, [r["_id"] for r in rows]) or {}
    except Exception:
        names = {}
    buttons = []
    for r in rows:
        nm = " ".join(p for p in (names.get(r["_id"]) or ("", ""))[:2] if p).strip() or f"User {r['_id']}"
        buttons.append([_bc_btn(f"{'📤' if r['out'] else '📥'} {nm[:28]} · {_dm_ago(r['t'])}", f"dm:h:{r['_id']}:0")])
    nav = ([_bc_btn("◀ Newer", f"dm:l:{page - 1}")] if page else []) + ([_bc_btn("Older ▶", f"dm:l:{page + 1}")] if more else [])
    text = ("<b>📜 DM History</b>\n\nPeople you messaged or who messaged you (last 5 days, newest first).\n"
            "📤 your message was the latest · 📥 their message was the latest")
    return text, _bc_kb(*buttons, *([nav] if nav else []), find_row, back_row)

def _dm_panel(owner=False):
    rows = [[_bc_btn("✉️ New DM", "dm:new")], [_bc_btn("📜 History", "dm:l:0")]]
    if owner:
        rows.append([_bc_btn("📢 DM All", "dm:all")])              # Owner only: one message to every member's PM
    rows.append([_bc_btn("🔙 Back", "bc:h")])
    return ("<b>💬 DM</b>\n\nMessage one person through the bot and see everyone you have chatted with (last 5 days)."
            + ("\n📢 DM All sends one message to every member." if owner else ""),
            _bc_kb(*rows))


# ---- 📢 DM All (Owner only): one message to every member's PM -------------------
DM_ALL_PROMPT = ("📢 <b>DM All</b>\n\nSend the one message that every member will get in their PM. "
                 "Text, photo, video or a file all work.")
DM_ALL_PAUSE = 0.05            # seconds between members (about 20 a second, under Telegram's limit)
_dm_all_running = False
_dm_all_tasks = set()

async def _dm_all_confirm(target, uid):
    """The owner sent the message: show how many members it will reach and ask for confirmation."""
    total = await asyncio.to_thread(mongo_db.count_users)
    _dm_state[uid] = {"step": "allc", "chat": target.chat_id, "mid": target.message_id, "t": time.monotonic()}
    await target.reply_text(
        f"📢 Send this message to <b>{total}</b> members?\n"
        "Members who blocked the bot or never started it are skipped.",
        parse_mode="HTML", reply_markup=_bc_kb([_bc_btn("✅ Send to all", "dm:ay"), _bc_btn("❌ Cancel", "dm:cx")]))

async def _dm_all_run(bot, report_chat, src_chat, src_mid, owner_id):
    global _dm_all_running
    _dm_all_running = True
    sent = failed = total = 0
    try:
        ids = [i for i in await asyncio.to_thread(mongo_db.get_all_user_ids) if i != owner_id]
        total = len(ids)
        for rid in ids:
            for attempt in (1, 2):
                try:
                    await bot.copy_message(chat_id=rid, from_chat_id=src_chat, message_id=src_mid)
                    sent += 1
                    break
                except RetryAfter as e:                                 # Telegram asks us to slow down: wait, try once more
                    wait = getattr(e, "retry_after", 1)
                    await asyncio.sleep((wait.total_seconds() if hasattr(wait, "total_seconds") else float(wait)) + 1)
                    if attempt == 2:
                        failed += 1
                except TelegramError:                                    # blocked the bot / never started it / deleted account
                    failed += 1
                    break
            await asyncio.sleep(DM_ALL_PAUSE)
    except Exception as e:
        print("DM All error:", e)
    finally:
        _dm_all_running = False
    try:
        await bot.send_message(report_chat, f"✅ <b>DM All finished</b>\n\nSent: <b>{sent}</b>\n"
                               f"Failed: <b>{failed}</b> (blocked the bot or never opened a chat with it)\nTotal: {total}",
                               parse_mode="HTML")
    except TelegramError as e:
        print("DM All report error:", e)

async def dmall_command(update, context):
    """/dmall (Owner, PM): then send the one message.  Or reply to a message with /dmall to use that message."""
    msg, user = update.effective_message, update.effective_user
    if user is None or not is_owner(user.id):
        await safe_reply_text(msg, UNAUTHORIZED_TEXT)
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(msg, "⚠️ /dmall can only be used in the bot's PM.")
        return
    if msg.reply_to_message is not None:
        await _dm_all_confirm(msg.reply_to_message, user.id)
        return
    _dm_state[user.id] = {"step": "all", "t": time.monotonic()}
    await msg.reply_text(DM_ALL_PROMPT, parse_mode="HTML", reply_markup=_bc_kb([_bc_btn("❌ Cancel", "dm:cx")]))

async def dm_command(update, context):
    """/dm opens the DM menu.  /dm <user_id or @username> <message>   or reply to a message with /dm <user_id or @username>"""
    msg = update.effective_message
    if not await _dm_staff_ok(update.effective_user.id):
        await safe_reply_text(msg, UNAUTHORIZED_TEXT)
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(msg, "⚠️ /dm can only be used in the bot's PM.")
        return
    text = " ".join(context.args[1:]).strip()
    src = msg.reply_to_message
    if not context.args and not src:                 # plain /dm: shortcut to the 💬 DM menu
        text, markup = _dm_panel(is_owner(update.effective_user.id))
        await msg.reply_text(text, parse_mode="HTML", reply_markup=markup)
        return
    if not context.args or not (src or text):
        await safe_reply_text(msg, "Usage:\n/dm <user_id or @username> <message>\nOr reply to a message with /dm <user_id or @username>")
        return
    uid = await _dm_target(context.args[0])
    if uid is None:
        await safe_reply_text(msg, DM_UNKNOWN_TEXT)
        return
    await _dm_staff_send(msg, context, update.effective_user, uid, src if not text else None, text)

async def dmhistory_command(update, context):
    msg = update.effective_message
    if not await _dm_staff_ok(update.effective_user.id):
        await safe_reply_text(msg, UNAUTHORIZED_TEXT)
        return
    if update.effective_chat.type != "private" or not context.args:
        await safe_reply_text(msg, "Usage in the bot's PM: /dmhistory <user_id or @username>")
        return
    uid = await _dm_target(context.args[0])
    if uid is None:
        await safe_reply_text(msg, DM_UNKNOWN_TEXT)
        return
    text, markup = await _dm_history(uid, 0, update.effective_user.id)
    await msg.reply_text(text, parse_mode="HTML", reply_markup=markup)

async def dm_callback(update, context):
    q, uid = update.callback_query, update.callback_query.from_user.id
    parts = (q.data or "").split(":")
    act, a, b = parts[1] if len(parts) > 1 else "m", parts[2] if len(parts) > 2 else "", parts[3] if len(parts) > 3 else "0"
    # Owner: everything. Executives: the DM menu, History and replies; not 📤 Send / 🚫 Don't send (owner's choice) and not 🗑 Remove.
    if not is_owner(uid) and not (act in ("m", "x", "new", "hist", "r", "cx", "rm", "ri", "l", "h") and await _is_exec(uid)):
        await q.answer(UNAUTHORIZED_TEXT, show_alert=True)
        return
    if q.message is None or q.message.chat.type != "private":
        await q.answer("Open me in a private chat to use DM.", show_alert=True)
        return

    async def show(text, markup):
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup)
        except TelegramError:
            pass

    cancel = _bc_kb([_bc_btn("❌ Cancel", "dm:x")])
    await q.answer()
    if act in ("m", "x"):
        _dm_state.pop(uid, None)
        await show(*_dm_panel(is_owner(uid)))
    elif act in ("new", "hist"):
        _dm_state[uid] = {"step": "id" if act == "new" else "hist"}
        await show("<b>💬 DM</b>\n\nSend the user ID or @username of the person" + (" you want to message." if act == "new" else
                   " whose chat you want to see."), cancel)
    elif act == "all" and is_owner(uid):                # 📢 DM All, step 1: ask for the one message
        _dm_state[uid] = {"step": "all", "t": time.monotonic()}
        await show(DM_ALL_PROMPT, cancel)
    elif act == "ay" and is_owner(uid):                 # 📢 DM All, step 2: confirmed, send in the background
        st = _dm_state.get(uid)
        if not st or st.get("step") != "allc":
            await show("⌛ This DM All has expired. Open it again from 💬 DM.", _bc_kb([_bc_btn("🔙 Back", "dm:m")]))
        elif _dm_all_running:
            await show("⏳ A DM All is already being sent. Please wait for its report.", None)
        else:
            _dm_state.pop(uid, None)
            await show("⏳ Sending to all members... You will get a report here when it is done.", None)
            task = asyncio.create_task(_dm_all_run(context.bot, q.message.chat.id, st["chat"], st["mid"], uid))
            _dm_all_tasks.add(task)
            task.add_done_callback(_dm_all_tasks.discard)
    elif act == "r" and a.lstrip("-").isdigit():
        _dm_state[uid] = {"step": "msg", "to": int(a)}
        await context.bot.send_message(q.message.chat.id, f"✍️ Send your message for <b>{html_escape(await _dm_name(int(a)))}</b>. "
                                       "Text, photo, video or a file all work.", parse_mode="HTML", reply_markup=cancel)
    elif act == "cx":                                   # cancel a pending "send your reply" prompt
        _dm_state.pop(uid, None)
        try:
            await q.message.delete()
        except TelegramError:
            pass
    elif act == "rm" and a.lstrip("-").isdigit() and b.isdigit():   # ✍️ Reply under a member's message #n (n = 0: plain message)
        target, n = int(a), int(b)
        ref = await _dm_find_in(target, n) if n else None
        if n and ref is None:
            await context.bot.send_message(q.message.chat.id, "❌ That message is no longer saved (messages are kept for 5 days).")
            return
        _dm_state[uid] = {"step": "msg", "to": target, "ref": ref, "t": time.monotonic()}
        name = html_escape(await _dm_name(target))
        await context.bot.send_message(
            q.message.chat.id, (f"✍️ Send your reply to message #{n} from <b>{name}</b>." if n else f"✍️ Send your message for <b>{name}</b>.")
            + " Text, photo, video or a file all work.", parse_mode="HTML", reply_markup=_bc_kb([_bc_btn("❌ Cancel", "dm:cx")]))
    elif act == "ri" and a.lstrip("-").isdigit() and re.fullmatch(r"[isa]\d{1,9}", b):   # ✍️ Reply under an Idea / Issue / Appeal
        target = int(a)
        ctx = await _dm_item_ctx(target, b[0], int(b[1:]))
        if ctx is None:
            await context.bot.send_message(q.message.chat.id, "❌ I can't find that message anymore.")
            return
        _dm_state[uid] = {"step": "msg", "to": target, "ctx": ctx, "t": time.monotonic()}
        name = html_escape(await _dm_name(target))
        await context.bot.send_message(
            q.message.chat.id, f"✍️ Send your reply to <b>{name}</b> about <b>{html_escape(ctx['label'])}</b>. "
            "Text, photo, video or a file all work.", parse_mode="HTML", reply_markup=_bc_kb([_bc_btn("❌ Cancel", "dm:cx")]))
    elif act in ("sy", "sn") and a.lstrip("-").isdigit() and b.isdigit():   # owner: show this reply to the executives, or not
        target, mid = int(a), int(b)
        name = html_escape(await _dm_name(target))
        if act == "sn":
            _dm_shared.add((target, mid))
            await show(f"✅ Sent to <b>{name}</b>.\n🚫 Not shown to executives.", None)
        elif (target, mid) in _dm_shared:
            await show(f"✅ Sent to <b>{name}</b>.\n📤 Already shown to executives.", None)
        else:
            row = await _dm_find_sent(target, mid)
            if row is None:
                await show("❌ That message is no longer saved, so it can't be copied.", None)
                return
            _dm_shared.add((target, mid))
            await _dm_share(context, target, {"mid": row.get("mid"), "mid2": row.get("mid2")}, sorted(await _exec_ids()))
            await _dm_mark_visible(target, row)
            await show(f"✅ Sent to <b>{name}</b>.\n📤 Shown to executives.", None)
    elif act == "l":
        await show(*await _dm_list(int(a) if a.isdigit() else 0, uid))
    elif act == "h" and a.lstrip("-").isdigit() and b.isdigit():
        await show(*await _dm_history(int(a), int(b), uid))
    elif act == "d" and a.lstrip("-").isdigit():        # 🗑 Remove on a "Reply from" message: step 1, ask first
        await context.bot.send_message(
            q.message.chat.id, f"🗑 Remove chat with <b>{html_escape(await _dm_name(int(a)))}</b>?\n"
            "All saved messages with them will be deleted. This can't be undone.", parse_mode="HTML",
            reply_markup=_bc_kb([_bc_btn("✅ Yes, remove", f"dm:dy:{a}:{q.message.message_id}"), _bc_btn("❌ Cancel", "dm:dn")]))
    elif act == "dh" and a.lstrip("-").isdigit():       # 🗑 Remove on the chat history screen: step 1, ask first
        await show(f"🗑 Remove chat with <b>{html_escape(await _dm_name(int(a)))}</b>?\n\n"
                   "All saved messages with them will be deleted. This can't be undone.",
                   _bc_kb([_bc_btn("✅ Yes, remove", f"dm:dy:{a}:0"), _bc_btn("❌ Cancel", f"dm:h:{a}:0")]))
    elif act == "dn":                                   # cancelled: just drop the question
        try:
            await q.message.delete()
        except TelegramError:
            pass
    elif act == "dy" and a.lstrip("-").isdigit():       # step 2: confirmed
        target = int(a)
        name = html_escape(await _dm_name(target))
        try:
            res = await asyncio.to_thread(_mc(DM_COLL).delete_many, {"uid": target})
            deleted = res.deleted_count
        except Exception as e:
            print("DM remove error:", e)
            await show(f"❌ Couldn't remove the chat with <b>{name}</b> right now. Please try again.",
                       _bc_kb([_bc_btn("📜 History", "dm:l:0")]))
            return
        await show(f"✅ Chat with <b>{name}</b> removed ({deleted} saved message{'s' if deleted != 1 else ''} deleted).",
                   _bc_kb([_bc_btn("📜 History", "dm:l:0")]))
        if b.isdigit() and int(b):                      # drop the old buttons from the message the question came from
            try:
                await context.bot.edit_message_reply_markup(q.message.chat.id, int(b), reply_markup=None)
            except TelegramError:
                pass

async def dm_message(update, context):
    """The owner's next message in a DM step, or a user's message to the bot staff (forwarded to the owner)."""
    msg, user = update.effective_message, update.effective_user
    if not msg or not user:
        return
    text = (msg.text or msg.caption or "").strip()
    st = _dm_state.get(user.id)
    if st is not None and "t" in st and time.monotonic() - st["t"] > DM_STATE_TTL:     # a forgotten "send your reply" prompt expires
        _dm_state.pop(user.id, None)
        st = None
    rm = getattr(msg, "reply_to_message", None)
    owner = is_owner(user.id)
    if owner or ((st is not None or rm is not None) and await _is_exec(user.id)):
        if st is not None and st["step"] == "msg":          # the reply they were asked to type
            _dm_state.pop(user.id, None)
            await _dm_staff_send(msg, context, user, st["to"], src=msg, ctx=st.get("ctx"), ref=st.get("ref"))
            return
        if owner and st is not None and st["step"] == "all":       # 📢 DM All: the message to send to everyone
            await _dm_all_confirm(msg, user.id)
            return
        if owner and st is not None and st["step"] == "allc":
            await safe_reply_text(msg, "⏳ Press ✅ Send to all or ❌ Cancel on the question above first.")
            return
        if st is not None:
            if (target := await _dm_target(msg.text)) is None:
                await safe_reply_text(msg, DM_UNKNOWN_TEXT)
            elif st["step"] == "hist":
                _dm_state.pop(user.id, None)
                out, markup = await _dm_history(target, 0, user.id)
                await msg.reply_text(out, parse_mode="HTML", reply_markup=markup)
            else:
                st.update(step="msg", to=target)
                await safe_reply_text(msg, f"✍️ Send your message for <b>{html_escape(await _dm_name(st['to']))}</b>.",
                                      parse_mode="HTML", reply_markup=_bc_kb([_bc_btn("❌ Cancel", "dm:x")]))
            return
        if rm is not None and (note := await _dm_note_find(user.id, rm.message_id)) is not None:
            # swiped on a member's message / an Idea / Issue / Appeal in the staff chat: answer exactly that one
            ctx = ref = None
            if note.get("ctx"):
                ctx = await _dm_item_ctx(note["uid"], note["ctx"][0], int(note["ctx"][1:]))
            elif note.get("n") is not None:
                ref = await _dm_find_in(note["uid"], note["n"])
            await _dm_staff_send(msg, context, user, note["uid"], src=msg, ctx=ctx, ref=ref)
            return
        if owner:
            return
    if (waiting := _rp_wait.pop(user.id, None)) is not None and time.monotonic() - waiting["t"] < RP_WAIT:   # after /reply
        ok = await _dm_forward(context, msg, user, "💬 Reply from", ref=waiting["ref"], about=waiting["about"])
        await safe_reply_text(msg, "✅ Sent to the bot staff." if ok else "❌ Couldn't deliver your message right now. Please try again later.")
        return
    if ADMIN_IDS and rm is not None and (ref := await _dm_find_sent(user.id, rm.message_id)) is not None:
        # they swiped on one of the owner's DMs = a reply. Nothing else they type is forwarded.
        ok = await _dm_forward(context, msg, user, "💬 Reply from", ref=ref)
        await safe_reply_text(msg, "✅ Sent to the bot staff." if ok else "❌ Couldn't deliver your message right now. Please try again later.")

async def _dm_forward(context, msg, user, title, text=None, ref=None, about=None):
    """Send a user's message to the owner with ✍️ Reply / 📜 History / 🗑 Remove buttons. True when it was delivered.
    ref = the owner's numbered DM (log row) it answers; about = preview of a normal bot message they pointed at."""
    text = (text if text is not None else (msg.text or msg.caption or "")).strip()
    kind = "text" if text and not msg else _dm_kind(msg)
    reply_n, reply_prev, is_about = None, "", False
    if ref is not None:
        reply_n = ref.get("n")
        reply_prev = (ref.get("text") or "").strip() or _DM_LABELS.get(ref.get("kind"), "")
    elif about is not None:
        reply_prev, is_about = about, True
    vis = ref is None or bool(ref.get("vis")) or bool(ref.get("byn"))      # an answer to a hidden owner DM stays hidden from executives
    n = await _dm_log(user.id, False, kind, text, mid=getattr(msg, "message_id", None), reply_n=reply_n,
                      reply_prev=reply_prev, about=is_about, vis=vis)
    who = html_escape(await _dm_name(user.id))
    head = (f"{title} <b>{who}</b>\n🆔 <code>{user.id}</code> | "
            f"{'@' + html_escape(user.username) if user.username else 'no username'}"
            f"{f' | #{n}' if n is not None else ''}\n")
    if ref is not None or is_about:
        short = html_escape(reply_prev[:100] + ("…" if len(reply_prev) > 100 else ""))
        if ref is not None:
            head += f"↩️ Replying to your message{f' #{reply_n}' if reply_n is not None else ''}" + (f': "{short}"' if short else "") + "\n"
        else:
            head += "↩️ About a bot message" + (f': "{short}"' if short else "") + "\n"
    head += "\n"
    body = (head + (html_escape(text) if kind == "text" else _DM_LABELS[kind]))[:4000]
    recipients = [(ADMIN_IDS[0], True)]
    by = (ref or {}).get("by")                  # an executive wrote the message they answered: they get the answer too
    if by is not None and not is_owner(by):
        recipients.append((int(by), False))
    delivered = False
    for rid, is_main in recipients:
        kb = (_bc_kb([_bc_btn("✍️ Reply", f"dm:rm:{user.id}:{n or 0}"), _bc_btn("📜 History", f"dm:h:{user.id}:0")],
                     [_bc_btn("🗑 Remove", f"dm:d:{user.id}")])
              if is_main else _bc_kb([_bc_btn("✍️ Reply", f"dm:rm:{user.id}:{n or 0}")]))
        try:
            first = await context.bot.send_message(rid, body, parse_mode="HTML", reply_markup=kb)
            mids = [first.message_id]
            if kind != "text":
                mids.append((await context.bot.copy_message(rid, msg.chat_id, msg.message_id)).message_id)
            await _dm_note(rid, mids, user.id, n=n)
            delivered = delivered or is_main
        except TelegramError as e:
            print("DM forward error:", e)
    return delivered

RP_WAIT, RP_COOLDOWN = 300, 30           # /reply waits 5 minutes for the message; one use per user per 30 seconds
_rp_wait = {}                            # user id -> {"t": when they typed /reply, "ref": owner DM row or None, "about": preview or None}
_rp_last = {}                            # user id -> last /reply use

async def reply_command(update, context):
    """/reply [text] writes to the bot staff.  /reply 3 [text] (or #3) answers the staff's DM #3.
    /reply on a swiped message points at it (a staff DM = answer to it; any other bot message = "about" it)."""
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    if chat.type != "private":
        await safe_reply_text(msg, "Please use /reply in my private chat.")
        return
    if is_owner(user.id) or not ADMIN_IDS:
        await safe_reply_text(msg, "Use 💬 DM in /help → 📣 Broadcast to message people.")
        return
    if time.monotonic() - _rp_last.get(user.id, -999.0) < RP_COOLDOWN:
        await safe_reply_text(msg, "⏳ Please wait a few seconds before using /reply again.")
        return
    parts = (msg.text or "").split(None, 1)
    rest = parts[1].strip() if len(parts) > 1 else ""
    ref, about = None, None
    if (m := re.match(r"#?(\d{1,9})(?:\s+(.*))?$", rest, re.S)):
        num, rest = int(m.group(1)), (m.group(2) or "").strip()
        ref = await _dm_find_n(user.id, num)
        if ref is None:
            await safe_reply_text(msg, f"❌ I can't find message #{num}. Check the number, or use /reply on its own to send a normal message.")
            return
    elif (rm := msg.reply_to_message) is not None:
        ref = await _dm_find_sent(user.id, rm.message_id)
        if ref is None and not (rm.from_user and rm.from_user.id == user.id):
            about = _dm_preview(rm)                      # a normal bot message
    _rp_last[user.id] = time.monotonic()
    if rest:
        ok = await _dm_forward(context, None, user, "💬 Reply from", text=rest, ref=ref, about=about)
        await safe_reply_text(msg, "✅ Sent to the bot staff." if ok else "❌ Couldn't deliver your message right now. Please try again later.")
        return
    _rp_wait[user.id] = {"t": time.monotonic(), "ref": ref, "about": about}
    if ref is not None and ref.get("n") is not None:
        ask = f"✍️ Send your reply to message #{ref['n']}."
    elif about is not None:
        ask = "✍️ Send your message about that bot message."
    else:
        ask = "✍️ Send your message for the bot staff."
    await safe_reply_text(msg, ask + " Text, photo, video or a file all work.", reply_markup=_bc_kb([_bc_btn("❌ Cancel", "um:x")]))

async def reply_cancel_callback(update, context):
    query = update.callback_query
    _rp_wait.pop(query.from_user.id, None)
    await query.answer("Cancelled.")
    try:
        await query.message.delete()
    except TelegramError:
        pass

async def send_character_check_result(bot, chat_id, character, source_message=None):
    code, name, anime, rarity, worth, photo = character
    recruit_names = (await asyncio.to_thread(get_recruit_names, code))
    owners = (await asyncio.to_thread(mongo_db.get_character_owners, code))
    owner_names = (await asyncio.to_thread(mongo_db.get_users_by_ids, [uid for uid, _ in owners]))
    lines = [
        f"🎭 {name}",
        f"📺 Anime: {anime or '—'}",
        f"🏷 Rarity: {rarity_text(rarity) if rarity else '— Not set'}",
        f"💰 Worth: {worth}",
        f"🔢 Code: {code}",
    ]
    lines.append(f"🔎 Recruitment Name: {', '.join(recruit_names) if recruit_names else '— Not set'}")
    if (await asyncio.to_thread(is_character_discontinued, code)):
        lines.append("🚫 Discontinued — no longer spawns")
    adder_text = (await asyncio.to_thread(get_character_adder_text, code))
    lines += ["", f"➕ Added by: {adder_text}"]
    lines += ["", "👑 Owners:"]
    for uid, qty in owners:
        u = owner_names.get(int(uid))
        first, last, username = u if u else ("Unknown", "", "")
        display = " ".join(v for v in [first, last] if v).strip() or "Unknown"
        lines.append(f"• {display} ×{qty}")
    if not owners:
        lines.append("• No owners yet")

    text = add_display_name_header(source_message, "\n".join(lines)) if source_message else "\n".join(lines)
    if photo:
        await bot.send_photo(chat_id=chat_id, photo=photo, caption=text, parse_mode="HTML")
    else:
        await bot.send_message(chat_id=chat_id, text=text, parse_mode="HTML")

async def check(update, context):
    (await save_user_async(update.effective_user))
    query = " ".join(context.args).strip()
    if not query:
        await safe_reply_text(
            update.message,
            "Usage: /check <4-digit code, first name, last name, or full name>\n"
            "Anime list: /check (Naruto)",
        )
        return

    character = None
    anime_query = parse_anime_query(query)

    if anime_query:
        character = await reply_anime_character_list(update, "check", anime_query)
        if not character:
            return
    elif query.isdigit():
        character = (await asyncio.to_thread(get_character_by_code, query))
    else:
        matches = (await asyncio.to_thread(find_characters_by_name_parts, query))
        if len(matches) > 1:
            await safe_reply_text(
                update.message,
                "❓ Multiple characters found. Select one:",
                reply_markup=character_selection_keyboard(
                    update.effective_user.id, "check", matches
                ),
            )
            return
        if len(matches) == 1:
            character = matches[0]

    if not character:
        await safe_reply_text(update.message, "❌ Character not found.")
        return

    await send_character_check_result(context.bot, update.message.chat_id, character, update.message)

# ======================================================================================================
# MULTI-CHARACTER SELL  (💰 Sell button in the collection  +  /sell naruto 2 / sakura)
#   * Format: characters are separated by "/", a number after a character = copies (no number = 1).
#   * Payout per character = worth * copies // 2 (same rule as the single /sell).
#   * Nothing is removed until the user presses ✅ Confirm; the whole sale is ONE database transaction.
# ======================================================================================================
SELL_INPUT_TTL = 120          # seconds the bot waits for the list after 💰 Sell / bare /sell
SELL_CONFIRM_TTL = 300        # seconds the ✅ Confirm / ❌ Cancel screen stays valid
SELL_MAX_ENTRIES = 25         # characters per sale
PENDING_SELL_INPUT = {}       # (chat_id, user_id) -> {"guide_id": message_id, "expires": monotonic seconds}
PENDING_SELL_CONFIRM = {}     # token -> {"uid", "chat_id", "lines", "total", "expires"}
_BG_TASKS = set()             # keeps background tasks alive until they finish

SELL_GUIDE_TITLE = "💰 Sell Characters"
SELL_GUIDE_TEXT = (
    f"{SELL_GUIDE_TITLE}\n\n"
    "Send the characters you want to sell in ONE message:\n"
    "• Separate different characters with /\n"
    "• Add a number after a character for more copies (no number = 1 copy)\n"
    "• Use the 4-digit code or the name\n\n"
    "Examples:\n"
    "naruto 2 / sakura\n"
    "1344 2 / 6023 / 1329 3\n\n"
    "💸 You get half of each character's worth in Berrys.\n"
    "✅ You will see a summary and confirm before anything is sold.\n\n"
    "Send your list now, or reply to this message with it if nothing happens."
)


class _SellShort(Exception):
    """A character copy count changed (or the user row is missing) while the sale was being committed."""

    def __init__(self, name=None, have=0):
        super().__init__(name or "")
        self.name, self.have = name, have


def _spawn_bg(coro):
    task = asyncio.create_task(coro)
    _BG_TASKS.add(task)
    task.add_done_callback(_BG_TASKS.discard)
    return task


def parse_sell_list(text):
    """'naruto 2 / sakura' -> [('naruto', 2), ('sakura', 1)].  '/' (or a new line) separates characters; a number as the
    last word of a part is the copy count (default 1). Names with spaces are fine ('rem ram 2')."""
    entries = []
    for part in re.split(r"[/\n]+", text or ""):
        tokens = part.split()
        if not tokens:
            continue
        qty = 1
        if len(tokens) >= 2 and tokens[-1].isascii() and tokens[-1].isdigit():
            qty = int(tokens[-1])
            tokens = tokens[:-1]
        entries.append((" ".join(tokens), qty))
    return entries


def _sell_resolve_character(lookup):
    """(character_row, None) or (None, error text). Unlike get_character() it says WHY a name did not resolve."""
    lookup = (lookup or "").strip()
    shown = lookup if len(lookup) <= 30 else lookup[:30] + "…"
    if not lookup:
        return None, "❌ An entry is empty (check your / separators)."
    if lookup.isascii() and lookup.isdigit():
        row = get_character_by_code(lookup)
        return (row, None) if row else (None, f"❌ No character with code {shown}.")
    rows = find_characters_by_name_parts(lookup)
    if len(rows) == 1:
        return rows[0], None
    if len(rows) > 1:
        names = ", ".join(f"{r[1]} [{r[0]}]" for r in rows[:5]) + ("…" if len(rows) > 5 else "")
        return None, f"❌ \"{shown}\" matches several characters ({names}). Use the 4-digit code."
    recruit = find_character_by_recruit_name(lookup)
    if recruit:
        return recruit, None
    return None, f"❌ Character \"{shown}\" not found."


def _sell_build_plan(uid, entries):
    """Sync (run in a thread). Returns (lines, errors): lines = characters that can be sold, errors = skipped entries."""
    owned = {str(r[0]): int(r[5]) for r in mongo_db.get_collection_summary(uid)}
    favorite = get_favorite_code(uid)
    favorite = str(favorite) if favorite else None
    merged, order, errors = {}, [], []
    for lookup, qty in entries:
        if qty <= 0:
            errors.append(f"❌ \"{lookup[:30]}\" — the number of copies must be at least 1.")
            continue
        character, err = _sell_resolve_character(lookup)
        if err:
            errors.append(err)
            continue
        code, name, _anime, rarity, worth, _photo = character
        code = str(code)
        if code not in merged:
            merged[code] = {"code": code, "name": name, "rarity": rarity, "worth": int(worth or 0), "qty": 0}
            order.append(code)
        merged[code]["qty"] += qty          # the same character written twice is added together
    lines = []
    for code in order:
        ln = merged[code]
        have = owned.get(code, 0)
        if have <= 0:
            errors.append(f"❌ {ln['name']} [{code}] — you don't own this character.")
            continue
        if ln["qty"] > have:
            errors.append(f"❌ {ln['name']} [{code}] — you have only {have}, but asked for {ln['qty']}.")
            continue
        ln["have"] = have
        ln["payout"] = (ln["worth"] * ln["qty"]) // 2
        ln["fav"] = (code == favorite)
        ln["clears_fav"] = ln["fav"] and ln["qty"] >= have
        lines.append(ln)
    return lines, errors


def _sell_commit(uid, lines):
    """Sync (run in a thread). Removes the copies and pays the Berrys in ONE transaction; returns the Berrys paid.
    Raises _SellShort (nothing changed) if any copy count is no longer enough."""
    def _work(session):
        coll = _mc(mongo_db.COLLECTIONS)
        total = 0
        for ln in lines:
            ids = [d["_id"] for d in coll.find({"user_id": uid, "character_code": ln["code"]}, {"_id": 1},
                                               sort=[("_id", 1)], limit=ln["qty"], session=session)]
            if len(ids) < ln["qty"]:
                raise _SellShort(ln["name"], len(ids))
            coll.delete_many({"_id": {"$in": ids}}, session=session)
            total += ln["payout"]
        if total:
            res = _mc(mongo_db.USERS).update_one({"_id": uid}, {"$inc": {"coins": total}}, session=session)
            if res.matched_count != 1:
                raise _SellShort(None, 0)
        fav = _mc(mongo_db.FAVORITES).find_one({"_id": uid}, session=session)
        if fav and str(fav.get("character_code")) in {ln["code"] for ln in lines}:
            if coll.count_documents({"user_id": uid, "character_code": str(fav["character_code"])}, session=session) == 0:
                _mc(mongo_db.FAVORITES).delete_one({"_id": uid}, session=session)   # sold the last copy of the favourite
        return total
    return mongo_db.run_transaction(_work)


def sell_guide_keyboard(user_id):
    return InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data=f"sellg:{user_id}:x")]])


async def _sell_guide_expire(bot, chat_id, user_id, guide_id):
    await asyncio.sleep(SELL_INPUT_TTL + 2)
    pend = PENDING_SELL_INPUT.get((chat_id, user_id))
    if pend and pend.get("guide_id") == guide_id and time.monotonic() >= pend["expires"]:
        PENDING_SELL_INPUT.pop((chat_id, user_id), None)
        await safe_delete_message(bot, chat_id, guide_id)


async def _sell_send_guide(context, chat_id, user_id):
    """Send the how-to message and start waiting for this user's list in this chat."""
    old = PENDING_SELL_INPUT.pop((chat_id, user_id), None)
    if old:
        await safe_delete_message(context.bot, chat_id, old.get("guide_id"))
    sent = await context.bot.send_message(chat_id=chat_id, text=SELL_GUIDE_TEXT, reply_markup=sell_guide_keyboard(user_id))
    PENDING_SELL_INPUT[(chat_id, user_id)] = {"guide_id": sent.message_id, "expires": time.monotonic() + SELL_INPUT_TTL}
    _spawn_bg(_sell_guide_expire(context.bot, chat_id, user_id, sent.message_id))


async def _sell_begin(update, context, raw_text):
    """Parse the list, check ownership and show the ✅ Confirm / ❌ Cancel summary. Returns True if a summary was shown."""
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    entries = parse_sell_list(raw_text)
    if not entries:
        await safe_reply_text(msg, "❌ I could not find any character in your message.\nExample: naruto 2 / sakura")
        return False
    if len(entries) > SELL_MAX_ENTRIES:
        await safe_reply_text(msg, f"❌ You can sell at most {SELL_MAX_ENTRIES} different characters at once.")
        return False
    try:
        lines, errors = await asyncio.to_thread(_sell_build_plan, user.id, entries)
    except Exception as e:
        print("Sell plan error:", e)
        await safe_reply_text(msg, "❌ Could not check your collection. Please try again.")
        return False
    skipped = "\n".join(errors[:10]) + (f"\n…and {len(errors) - 10} more" if len(errors) > 10 else "")
    if not lines:
        await safe_reply_text(msg, "❌ Nothing can be sold:\n" + skipped + "\n\nSend a corrected list.")
        return False

    now = time.monotonic()
    for key in [k for k, v in PENDING_SELL_CONFIRM.items() if v["expires"] < now]:
        PENDING_SELL_CONFIRM.pop(key, None)
    total = sum(ln["payout"] for ln in lines)
    token = uuid.uuid4().hex[:12]
    PENDING_SELL_CONFIRM[token] = {"uid": user.id, "chat_id": chat.id, "lines": lines, "total": total,
                                   "expires": now + SELL_CONFIRM_TTL}
    body = "\n".join(
        f"{SYMBOL.get(ln['rarity'], '⭐')} {ln['name']} [{ln['code']}] x{ln['qty']} → 💰 {ln['payout']}"
        + (" ⭐" if ln["fav"] else "")
        for ln in lines)
    text = f"🧾 Sale Summary\n\n{body}\n\n💰 Total: {total} Berrys"
    if any(ln["clears_fav"] for ln in lines):
        text += "\n⭐ Your favourite will be cleared (you are selling all its copies)."
    if errors:
        text += "\n\n⚠️ Not included:\n" + skipped
    text += "\n\nNothing is sold until you press Confirm."
    keyboard = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Confirm", callback_data=f"sellc:{token}:y"),
        InlineKeyboardButton("❌ Cancel", callback_data=f"sellc:{token}:n"),
    ]])
    await safe_reply_text(msg, text, reply_markup=keyboard)
    pend = PENDING_SELL_INPUT.pop((chat.id, user.id), None)      # the list was received: stop waiting, tidy the guide
    guide_id = (pend or {}).get("guide_id")
    reply = getattr(msg, "reply_to_message", None)
    if reply is not None and SELL_GUIDE_TITLE in (reply.text or "")[:80] and getattr(reply.from_user, "id", None) == context.bot.id:
        guide_id = reply.message_id
    if guide_id:
        await safe_delete_message(context.bot, chat.id, guide_id)
    return True


async def sell_input_handler(update, context):
    """Plain text from a user who tapped 💰 Sell (or replied to the guide message) = their sell list."""
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    if msg is None or user is None or chat is None or not msg.text:
        return
    key = (chat.id, user.id)
    pend = PENDING_SELL_INPUT.get(key)
    if pend and time.monotonic() > pend["expires"]:
        PENDING_SELL_INPUT.pop(key, None)
        pend = None
    reply = msg.reply_to_message
    replied_to_guide = bool(reply is not None and getattr(reply.from_user, "id", None) == context.bot.id
                            and SELL_GUIDE_TITLE in (reply.text or "")[:80])
    if not pend and not replied_to_guide:
        return
    if chat.type in ("group", "supergroup") and not await asyncio.to_thread(is_bot_enabled, chat.id):
        return
    await save_user_async(user)
    await _sell_begin(update, context, msg.text)


async def sell_guide_callback(update, context):
    """❌ Cancel under the how-to message."""
    query = update.callback_query
    parts = (query.data or "").split(":")
    if len(parts) != 3 or parts[0] != "sellg":
        await query.answer()
        return
    try:
        owner_id = int(parts[1])
    except ValueError:
        await query.answer()
        return
    if query.from_user.id != owner_id:
        await query.answer("❌ This menu belongs to another user.", show_alert=True)
        return
    await query.answer("Cancelled.")
    PENDING_SELL_INPUT.pop((query.message.chat_id, owner_id), None)
    await safe_delete_message(context.bot, query.message.chat_id, query.message.message_id)


async def sell_confirm_callback(update, context):
    """✅ Confirm / ❌ Cancel on the sale summary."""
    query = update.callback_query
    parts = (query.data or "").split(":")
    if len(parts) != 3 or parts[0] != "sellc":
        await query.answer()
        return
    token, choice = parts[1], parts[2]

    async def _edit(text):
        try:
            await query.edit_message_text(add_display_name_header(query, text), reply_markup=None)
        except Exception as e:
            print("Sell edit error:", e)

    info = PENDING_SELL_CONFIRM.get(token)
    if info is None or time.monotonic() > info["expires"]:
        PENDING_SELL_CONFIRM.pop(token, None)
        await query.answer("⌛ This sale has expired. Start again with 💰 Sell or /sell.", show_alert=True)
        await _edit("⌛ This sale has expired. Nothing was sold.")
        return
    if query.from_user.id != info["uid"]:
        await query.answer("❌ This sale belongs to another user.", show_alert=True)
        return
    if choice != "y":
        PENDING_SELL_CONFIRM.pop(token, None)
        await query.answer("Cancelled.")
        await _edit("❌ Sale cancelled. Nothing was sold.")
        return

    info = PENDING_SELL_CONFIRM.pop(token, None)      # removed BEFORE the first await: a second tap can never pay twice
    if info is None:
        await query.answer()
        return
    await query.answer()
    uid, lines = info["uid"], info["lines"]
    try:
        total = await asyncio.to_thread(_sell_commit, uid, lines)
    except _SellShort as e:
        if e.name:
            await _edit(f"❌ Sale cancelled: you now have only {e.have} of {e.name}. Nothing was sold.")
        else:
            await _edit("❌ Sale cancelled: your account could not be updated. Nothing was sold.")
        return
    except Exception as e:
        print("Multi-sell transaction error:", e)
        await _edit("❌ Could not complete the sale. Nothing was sold. Please try again.")
        return

    for ln in lines:
        await fusion.record_sell(uid, ln["rarity"], ln["qty"])      # stone task progress (never raises)
    await rewards.task_hook(context.bot, uid, "sell", name=berry_display_name(query.from_user))     # invite friend task (never raises)
    done = "\n".join(f"• {ln['name']} [{ln['code']}] x{ln['qty']} → +{ln['payout']}" for ln in lines)
    await _edit(f"💸 Sold {sum(ln['qty'] for ln in lines)} character copies!\n\n{done}\n\n💰 +{total} Berrys")
    await fusion.stone_remind(uid, chat_id=info["chat_id"], name=berry_display_name(query.from_user))


# ======================================================================================================
# /rem  -  delete the bot's OWN messages (everyone can use it)
#   * reply to a bot message + /rem            -> deletes that one message (works for any message < 48 hours old)
#   * /rem 10  or  /rem10                      -> deletes the bot's last 10 messages in this chat
#   * /rem alone (no reply)                    -> deletes the bot's last message
#   * reply + number                           -> the replied message AND the newest others, N in total
# Telegram cannot list a bot's past messages, so the id of every message the bot sends is remembered per chat
# (last BOT_SENT_KEEP ids, kept in memory and saved to MongoDB every few seconds so a restart does not lose them).
# Messages that are already gone are skipped, so /rem 10 keeps going until 10 messages were really deleted.
# Telegram only allows deleting messages that are less than 48 hours old.
# ======================================================================================================
import collections as _collections

BOT_SENT_KEEP = 100
REM_MAX = 50
BOT_SENT_COLLECTION = "bot_sent_ids_v1"
BOT_SENT_FLUSH_DELAY = 10                  # seconds between saves of the remembered ids
_BOT_SENT_IDS = {}                         # chat_id -> deque of message ids sent by the bot (oldest ... newest)
_BOT_SENT_LOADED = set()                   # chats whose saved ids were already merged into memory
_BOT_SENT_DIRTY = set()                    # chats with changes not saved yet
_BOT_SENT_FLUSH = {"pending": False}
_REM_RE = r"(?i)^/rem(?:@(\w+))?\s*(\d{0,3})\s*$"      # /rem  /rem 10  /rem10  /rem@MyBot 10
_TRACKED_SEND_METHODS = ("send_message", "send_photo", "send_animation", "send_document", "send_video", "send_sticker",
                         "send_audio", "send_voice", "send_video_note", "send_dice", "send_poll")


def _sent_deque(chat_id):
    return _BOT_SENT_IDS.setdefault(chat_id, _collections.deque(maxlen=BOT_SENT_KEEP))


async def _sent_flush_once():
    await asyncio.sleep(BOT_SENT_FLUSH_DELAY)
    _BOT_SENT_FLUSH["pending"] = False
    chats = list(_BOT_SENT_DIRTY)
    _BOT_SENT_DIRTY.clear()
    for chat_id in chats:
        try:
            await _sent_ensure_loaded(chat_id)           # never overwrite saved ids that were not merged yet
            ids = list(_BOT_SENT_IDS.get(chat_id, ()))
            await asyncio.to_thread(_mc(BOT_SENT_COLLECTION).update_one, {"_id": chat_id}, {"$set": {"ids": ids}}, upsert=True)
        except Exception as e:
            print("Bot message ids save error:", e)


async def _sent_ensure_loaded(chat_id):
    """Merge the ids saved before the last restart (older) with the ones remembered since (newer)."""
    if chat_id in _BOT_SENT_LOADED:
        return
    _BOT_SENT_LOADED.add(chat_id)
    try:
        doc = await asyncio.to_thread(_mc(BOT_SENT_COLLECTION).find_one, {"_id": chat_id})
    except Exception as e:
        print("Bot message ids load error:", e)
        return
    saved = [int(i) for i in ((doc or {}).get("ids") or [])]
    dq = _sent_deque(chat_id)
    current = list(dq)
    known = set(current)
    merged = [i for i in saved if i not in known] + current
    dq.clear()
    dq.extend(merged[-BOT_SENT_KEEP:])


def _mark_sent_dirty(chat_id):
    _BOT_SENT_DIRTY.add(chat_id)
    if not _BOT_SENT_FLUSH["pending"]:
        _BOT_SENT_FLUSH["pending"] = True
        try:
            _spawn_bg(_sent_flush_once())
        except RuntimeError:                       # no running event loop
            _BOT_SENT_FLUSH["pending"] = False


def _track_bot_message(result):
    try:
        message_id = int(result.message_id)
        chat_id = int(result.chat_id if getattr(result, "chat_id", None) is not None else result.chat.id)
    except Exception:
        return
    if message_id >= 10 ** 9:                 # console-bridge test messages are not real Telegram ids
        return
    _sent_deque(chat_id).append(message_id)
    _mark_sent_dirty(chat_id)


def _forget_sent(chat_id, message_id):
    dq = _BOT_SENT_IDS.get(chat_id)
    if dq and message_id in dq:
        remaining = [i for i in dq if i != message_id]
        dq.clear()
        dq.extend(remaining)


def install_bot_message_tracker():
    """Remember the id of every message the bot sends (class-level wrapper, same technique as the console bridge)."""
    from telegram import Bot
    for name in _TRACKED_SEND_METHODS:
        original = getattr(Bot, name, None)
        if original is None or getattr(original, "_msg_tracker", False):
            continue

        def make(orig):
            async def wrapper(self, *args, **kwargs):
                result = await orig(self, *args, **kwargs)
                _track_bot_message(result)
                return result
            wrapper._msg_tracker = True
            return wrapper

        wrapper = make(original)
        wrapper.__name__ = name
        setattr(Bot, name, wrapper)


async def _delete_one(bot, chat_id, message_id):
    """(True, None) when deleted, (False, telegram error text) otherwise."""
    try:
        await asyncio.wait_for(bot.delete_message(chat_id=chat_id, message_id=message_id), timeout=15)
        return True, None
    except Exception as e:
        print(f"/rem delete error for {chat_id}/{message_id}: {e}")
        return False, str(e) or e.__class__.__name__


async def _delete_later(bot, chat_id, message_id, delay):
    await asyncio.sleep(delay)
    await safe_delete_message(bot, chat_id, message_id)


async def _rem_notice(context, chat_id, text, delay=6):
    """Short message that removes itself (and is not remembered as a bot message)."""
    try:
        sent = await context.bot.send_message(chat_id=chat_id, text=text)
        _forget_sent(chat_id, sent.message_id)
        _spawn_bg(_delete_later(context.bot, chat_id, sent.message_id, delay))
    except Exception as e:
        print("Rem notice error:", e)


async def rem_command(update, context):
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    if msg is None or user is None or chat is None or not msg.text:
        return
    m = re.match(_REM_RE, msg.text.strip())
    if not m:
        return
    target, digits = m.group(1), m.group(2)
    if target and context.bot.username and target.lower() != str(context.bot.username).lstrip("@").lower():
        return                                              # /rem@OtherBot: not for us
    if chat.type in ("group", "supergroup"):
        if not await is_group_approved(chat.id) or not await asyncio.to_thread(is_bot_enabled, chat.id):
            return                                          # unapproved / OFF group: stay silent like the other commands
    count = int(digits) if digits else None
    if count == 0:
        await _rem_notice(context, chat.id, "❌ The number must be at least 1. Example: /rem 10")
        return
    wanted = min(count, REM_MAX) if count else 1
    replied = msg.reply_to_message
    if replied is not None and (not replied.from_user or replied.from_user.id != context.bot.id):
        if count is None:
            await _rem_notice(context, chat.id, "❌ Reply to one of the bot's own messages. I can only delete my own messages.")
            return
        replied = None                                      # /rem 10 as a reply to someone else's message: just the last 10

    await _sent_ensure_loaded(chat.id)
    dq = _sent_deque(chat.id)
    deleted, attempted, last_error = 0, 0, None
    if replied is not None:                                 # the message that was replied to goes first
        _forget_sent(chat.id, replied.message_id)
        ok, err = await _delete_one(context.bot, chat.id, replied.message_id)
        attempted += 1
        if ok:
            deleted += 1
        else:
            last_error = err
    need = wanted - deleted if replied is not None else wanted
    if replied is not None and count is None:
        need = 0                                            # plain reply + /rem: only that one message
    while need > 0 and dq:                                  # newest first; messages that are already gone are skipped
        batch = [dq.pop() for _ in range(min(need, 10, len(dq)))]
        results = await asyncio.gather(*(_delete_one(context.bot, chat.id, mid) for mid in batch))
        attempted += len(batch)
        for ok, err in results:
            if ok:
                deleted += 1
                need -= 1
            else:
                last_error = err
    _mark_sent_dirty(chat.id)
    await safe_delete_message(context.bot, chat.id, msg.message_id)      # the /rem command itself (needs delete rights)

    if deleted:
        text = f"🧹 Deleted {deleted} bot message{'s' if deleted != 1 else ''}."
        if count and deleted < wanted:
            text += f"\nOnly {deleted} of {wanted} were still available (I remember my last {BOT_SENT_KEEP} messages, under 48 hours old)."
        await _rem_notice(context, chat.id, text)
    elif attempted == 0:
        await _rem_notice(context, chat.id,
                          "ℹ️ I have no saved messages of mine for this chat yet. I remember every message I send from now on.\n"
                          "To delete an older message, reply to it with /rem.")
    else:
        await _rem_notice(context, chat.id, f"❌ Could not delete: {last_error}", delay=10)


async def sell(update, context):
    (await save_user_async(update.effective_user))

    if not context.args:      # bare /sell: show the how-to guide and wait for the list
        await _sell_send_guide(context, update.effective_chat.id, update.effective_user.id)
        return

    joined_args = " ".join(context.args)
    if "/" in joined_args:      # several characters at once: /sell naruto 2 / sakura
        await _sell_begin(update, context, joined_args)
        return

    quantity = 1
    lookup_args = context.args
    if len(context.args) >= 2 and context.args[-1].isdigit():
        quantity = int(context.args[-1])
        lookup_args = context.args[:-1]
    if quantity <= 0:
        await safe_reply_text(update.message, "❌ Quantity must be at least 1.")
        return
    lookup = " ".join(lookup_args).strip()
    character = (await asyncio.to_thread(get_character, lookup))
    if not character:
        await safe_reply_text(update.message, "❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
        return

    code, name, anime, rarity, worth, photo = character
    total_value = (worth * quantity) // 2
    try:
        ok, available = (await asyncio.to_thread(mongo_db.sell_copies, update.effective_user.id, code, quantity, total_value))
    except Exception as e:
        print("Sell transaction error:", e)
        await safe_reply_text(update.message, "❌ Could not complete the sale. Please try again.")
        return
    if not ok:
        await safe_reply_text(update.message, f"❌ You only have {available} copy/copies of {name}.")
        return

    await fusion.record_sell(update.effective_user.id, rarity, quantity)  # stone task progress (never raises)
    await rewards.task_hook(context.bot, update.effective_user.id, "sell", name=berry_display_name(update.effective_user))     # invite friend task (never raises)

    try:
        await update.message.delete()
    except Exception as e:
        print(f"Sale message delete error: {e}")

    await safe_reply_text(update.message,
        f"💸 Sold {name} [{code}] x{quantity}!\n💰 +{total_value} Berrys"
    )
    await fusion.stone_remind(update.effective_user.id, chat_id=update.effective_chat.id,
                              name=berry_display_name(update.effective_user))  # "stone task complete - claim it" message (never raises)

PENDING_TRANSFERS = {}
PENDING_EXCHANGES = {}

async def exchange(update, context):
    (await save_user_async(update.effective_user))
    if not is_group_chat(update) or not update.message.reply_to_message:
        await safe_reply_text(update.effective_message, "❌ Reply to the other user's message in the group and use /exchange <your character code> <their character code>.")
        return
    if len(context.args) != 2 or not all(str(v).isdigit() for v in context.args):
        await safe_reply_text(update.effective_message, "Usage: /exchange <your character code> <their character code>")
        return
    sender = update.effective_user
    target = update.message.reply_to_message.from_user
    if not target or target.is_bot or target.id == sender.id:
        await safe_reply_text(update.effective_message, "❌ You can only exchange characters with another user.")
        return
    first = (await asyncio.to_thread(get_character_by_code, context.args[0]))
    second = (await asyncio.to_thread(get_character_by_code, context.args[1]))
    if not first or not second:
        await safe_reply_text(update.effective_message, "❌ Character not found.")
        return
    if first[3] != second[3]:
        await safe_reply_text(update.effective_message, "❌ Exchange is allowed only between characters of the same tier.")
        return
    own_id = (await asyncio.to_thread(mongo_db.find_copy_id, sender.id, first[0]))
    theirs_id = (await asyncio.to_thread(mongo_db.find_copy_id, target.id, second[0]))
    own = (own_id,) if own_id is not None else None
    theirs = (theirs_id,) if theirs_id is not None else None
    if not own:
        await safe_reply_text(update.effective_message, "❌ You don't own your selected character.")
        return
    if not theirs:
        await safe_reply_text(update.effective_message, "❌ The recipient doesn't own their selected character.")
        return
    exchange_id = f"{sender.id}:{target.id}:{update.message.message_id}:{time.time_ns()}"
    PENDING_EXCHANGES[exchange_id] = {
        "sender": sender.id, "target": target.id,
        "give_code": first[0], "receive_code": second[0],
        "give_id": own[0], "receive_id": theirs[0],
        "expires": datetime.now() + timedelta(hours=1),
        "sender_name": sender.first_name or "Unknown",
        "target_name": target.first_name or "Unknown",
    }
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Accept", callback_data=f"ex_accept:{exchange_id}"),
        InlineKeyboardButton("❌ Decline", callback_data=f"ex_decline:{exchange_id}"),
    ]])
    await safe_reply_text(
        update.effective_message,
        f"🔄 Character exchange request\n\n"
        f"👤 From: {sender.first_name or sender.id}\n"
        f"🎭 Gives: {first[1]} [{first[0]}]\n"
        f"🎭 Receives: {second[1]} [{second[0]}]\n"
        f"🏷 Tier: {rarity_text(first[3])}\n"
        "⏰ Valid for 1 hour.",
        reply_markup=kb,
    )

async def exchange_callback(update, context):
    q = update.callback_query
    data = q.data or ""
    if ":" not in data:
        await q.answer()
        return
    action, exchange_id = data.split(":", 1)
    item = PENDING_EXCHANGES.get(exchange_id)
    if not item:
        await q.answer("⚠️ This exchange has expired or the bot was restarted.", show_alert=True)
        return
    if q.from_user.id != item["target"]:
        await q.answer("❌ Only the recipient can accept or decline this exchange.", show_alert=True)
        return
    if datetime.now() >= item["expires"]:
        PENDING_EXCHANGES.pop(exchange_id, None)
        await q.answer("⏰ This exchange has expired.", show_alert=True)
        await q.edit_message_text("⏰ The exchange window expired. No characters were exchanged.")
        return
    if action == "ex_decline":
        PENDING_EXCHANGES.pop(exchange_id, None)
        await q.answer("Exchange declined.")
        await q.edit_message_text("❌ Exchange declined. Both characters remain with their owners.")
        return
    if action != "ex_accept":
        await q.answer("❌ Unknown exchange action.", show_alert=True)
        return
    try:
        swapped = (await asyncio.to_thread(mongo_db.swap_copies, item["give_id"], item["sender"], item["receive_id"], item["target"]))
    except Exception as e:
        print("Exchange transaction error:", e)
        await q.answer("❌ Exchange failed. Please try again.", show_alert=True)
        return
    if not swapped:
        PENDING_EXCHANGES.pop(exchange_id, None)
        await q.answer("❌ One of the characters is no longer available.", show_alert=True)
        await q.edit_message_text("❌ Exchange failed because one of the characters is no longer owned by the required user.")
        return
    PENDING_EXCHANGES.pop(exchange_id, None)
    await q.answer("✅ Exchange completed!")
    await q.edit_message_text("✅ Exchange completed successfully. Both characters have been exchanged.")

TRANSFER_TTL = 3600

def transfer_pair_key(user_id_1, user_id_2):
    a, b = sorted((int(user_id_1), int(user_id_2)))
    return a, b

def transfer_pair_blocked(user_id_1, user_id_2):
    a, b = transfer_pair_key(user_id_1, user_id_2)
    return _mc("transfer_blocks_v2").find_one({"user_id_1": a, "user_id_2": b}, {"_id": 1}) is not None

async def block_transfer_pair(update, context):
    user = update.effective_user
    if not (is_owner(user.id) or is_executive(user.id)):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    if len(context.args) != 2:
        await safe_reply_text(update.effective_message, "Usage: /btransfer <user_id_1> <user_id_2>")
        return
    try:
        u1, u2 = int(context.args[0]), int(context.args[1])
    except ValueError:
        await safe_reply_text(update.effective_message, "❌ Both user IDs must be numbers.")
        return
    if u1 == u2:
        await safe_reply_text(update.effective_message, "❌ You cannot block a user with themselves.")
        return
    a, b = transfer_pair_key(u1, u2)
    res = (await asyncio.to_thread(_mc("transfer_blocks_v2").update_one,
        {"user_id_1": a, "user_id_2": b},
        {"$setOnInsert": {"created_at": timestamp(), "blocked_by": user.id}},
        upsert=True,
    ))
    changed = res.upserted_id is not None
    if changed:
        await safe_reply_text(update.effective_message,
            f"🚫 Transfer blocked between:\n👤 {a}\n👤 {b}\n\n"
            "These two users cannot transfer characters to each other. Other transfers are unaffected."
        )
    else:
        await safe_reply_text(update.effective_message, "ℹ️ This user pair is already transfer-blocked.")

async def unblock_transfer_pair(update, context):
    user = update.effective_user
    if not (is_owner(user.id) or is_executive(user.id)):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    if len(context.args) != 2:
        await safe_reply_text(update.effective_message, "Usage: /unbtransfer <user_id_1> <user_id_2>")
        return
    try:
        u1, u2 = int(context.args[0]), int(context.args[1])
    except ValueError:
        await safe_reply_text(update.effective_message, "❌ Both user IDs must be numbers.")
        return
    if u1 == u2:
        await safe_reply_text(update.effective_message, "❌ Invalid user pair.")
        return
    a, b = transfer_pair_key(u1, u2)
    changed = (await asyncio.to_thread(_mc("transfer_blocks_v2").delete_many, {"user_id_1": a, "user_id_2": b})).deleted_count > 0
    if changed:
        await safe_reply_text(update.effective_message,
            f"✅ Transfer block removed between {a} and {b}."
        )
    else:
        await safe_reply_text(update.effective_message, "ℹ️ No transfer block exists for this pair.")

BERRY_TRANSFER_DAILY_SEND_LIMIT = 1000
BERRY_TRANSFER_DAILY_RECEIVE_LIMIT = 2000

def berry_transfer_day():
    return datetime.now(timezone.utc).astimezone(timezone(timedelta(hours=5, minutes=30))).date().isoformat()

def berry_transfer_stats(user_id, day=None):
    day = day or berry_transfer_day()

    def _total(field):
        res = list(_mc("berry_transfers_v2").aggregate([
            {"$match": {field: int(user_id), "transfer_day": day}},
            {"$group": {"_id": None, "total": {"$sum": "$amount"}}},
        ]))
        return int(res[0]["total"]) if res else 0

    return _total("sender_id"), _total("receiver_id")

async def berry(update, context):
    user = update.effective_user
    (await save_user_async(user))
    sent, received = (await asyncio.to_thread(berry_transfer_stats, user.id))
    send_left = max(0, BERRY_TRANSFER_DAILY_SEND_LIMIT - sent)
    receive_left = max(0, BERRY_TRANSFER_DAILY_RECEIVE_LIMIT - received)
    _coins = (await asyncio.to_thread(mongo_db.get_coins, user.id))
    row = (_coins,) if _coins is not None else None
    balance = int(row[0] or 0) if row else 0
    await safe_reply_text(update.effective_message,
        "🫐 Your Berry Transfer Status\n\n"
        f"💰 Balance: {balance} ⦵\n"
        f"📤 Transferred today: {sent} ⦵\n"
        f"📤 Transfer remaining: {send_left} ⦵ / {BERRY_TRANSFER_DAILY_SEND_LIMIT} ⦵\n"
        f"📥 Received today: {received} ⦵\n"
        f"📥 Receive remaining: {receive_left} ⦵ / {BERRY_TRANSFER_DAILY_RECEIVE_LIMIT} ⦵\n\n"
        "⏰ Limits reset at 12:00 AM IST.",
        parse_mode="HTML"
    )

async def berrytransfer(update, context):
    sender = update.effective_user
    (await save_user_async(sender))
    message = update.effective_message
    reply = message.reply_to_message if message else None
    if not is_group_chat(update) or not reply or not reply.from_user:
        await safe_reply_text(message, "❌ Reply to the recipient's message in the group and use /berrytransfer <amount>.")
        return
    target = reply.from_user
    if target.is_bot:
        await safe_reply_text(message, "❌ You cannot transfer Berrys to a bot.")
        return
    if target.id == sender.id:
        await safe_reply_text(message, "❌ You cannot transfer Berrys to yourself.")
        return
    if len(context.args) != 1:
        await safe_reply_text(message, "Usage: /berrytransfer <amount>\nExample: /berrytransfer 500")
        return
    try:
        amount = int(context.args[0])
    except (TypeError, ValueError):
        await safe_reply_text(message, "❌ Amount must be a whole number.")
        return
    if amount <= 0:
        await safe_reply_text(message, "❌ Amount must be greater than 0.")
        return
    if amount > BERRY_TRANSFER_DAILY_SEND_LIMIT:
        await safe_reply_text(message, f"❌ You can transfer a maximum of {BERRY_TRANSFER_DAILY_SEND_LIMIT} ⦵ per day.")
        return
    if (await asyncio.to_thread(transfer_pair_blocked, sender.id, target.id)):
        await safe_reply_text(message, "🚫 Transfers between these two users have been blocked by staff.")
        return

    day = berry_transfer_day()
    sender_debited = False
    receiver_credited = False
    try:
        (await asyncio.to_thread(mongo_db.ensure_user, sender.id, sender.username or "", sender.first_name or "", sender.last_name or ""))
        (await asyncio.to_thread(mongo_db.ensure_user, target.id, target.username or "", target.first_name or "", target.last_name or ""))

        sender_balance = int((await asyncio.to_thread(mongo_db.get_coins, sender.id)) or 0)
        sent_today, _ = (await asyncio.to_thread(berry_transfer_stats, sender.id, day))
        _, target_received_today = (await asyncio.to_thread(berry_transfer_stats, target.id, day))

        sender_remaining = BERRY_TRANSFER_DAILY_SEND_LIMIT - sent_today
        receiver_remaining = BERRY_TRANSFER_DAILY_RECEIVE_LIMIT - target_received_today
        if sender_remaining < amount:
            raise ValueError(f"SEND_LIMIT:{sent_today}:{sender_remaining}")
        if receiver_remaining < amount:
            raise ValueError(f"RECEIVE_LIMIT:{target_received_today}:{receiver_remaining}")
        if sender_balance < amount:
            raise ValueError(f"BALANCE:{sender_balance}")

        # atomic conditional deduct (re-checks the balance), then credit, then record
        if not (await asyncio.to_thread(mongo_db.spend_coins, sender.id, amount)):
            raise ValueError(f"BALANCE:{int((await asyncio.to_thread(mongo_db.get_coins, sender.id)) or 0)}")
        sender_debited = True
        if not (await asyncio.to_thread(mongo_db.add_coins, target.id, amount)):
            raise RuntimeError("receiver account missing")
        receiver_credited = True
        (await asyncio.to_thread(mongo_db.insert_with_id, "berry_transfers_v2", {
            "sender_id": sender.id, "receiver_id": target.id, "amount": amount,
            "transfer_day": day, "created_at": india_timestamp(),
        }))
    except ValueError as e:
        reason = str(e)
        if reason.startswith("SEND_LIMIT:"):
            _, sent, remaining = reason.split(":")
            await safe_reply_text(message, f"❌ Daily transfer limit reached.\n📤 Transferred today: {sent} ⦵\n📤 Remaining: {remaining} ⦵")
        elif reason.startswith("RECEIVE_LIMIT:"):
            _, received, remaining = reason.split(":")
            await safe_reply_text(message, f"❌ The recipient has reached or is close to their daily receive limit.\n📥 Received today: {received} ⦵\n📥 Receive remaining: {remaining} ⦵")
        else:
            _, balance = reason.split(":")
            await safe_reply_text(message, f"❌ You only have {balance} ⦵ available.")
        return
    except Exception as e:
        # undo any balance change that already happened
        if receiver_credited:
            try:
                (await asyncio.to_thread(mongo_db.add_coins, target.id, -amount))
            except Exception as undo_err:
                print("Berry transfer undo (receiver) error:", undo_err)
        if sender_debited:
            try:
                (await asyncio.to_thread(mongo_db.add_coins, sender.id, amount))
            except Exception as undo_err:
                print("Berry transfer undo (sender) error:", undo_err)
        print("Berry transfer error:", e)
        await safe_reply_text(message, "❌ Berry transfer failed. Please try again.")
        return

    sent_after = sent_today + amount
    received_after = target_received_today + amount
    sender_send_remaining = BERRY_TRANSFER_DAILY_SEND_LIMIT - sent_after
    target_receive_remaining = BERRY_TRANSFER_DAILY_RECEIVE_LIMIT - received_after

    transfers_today = (await asyncio.to_thread(_mc("berry_transfers_v2").count_documents, {"sender_id": sender.id, "transfer_day": day}))

    await safe_reply_text(message,
        f"🫐 You gave {amount} Berrys to {berry_display_name(target)}\n\n"
        f"📤 Total sent today: {sent_after} ⦵\n"
        f"📤 Send remaining today: {sender_send_remaining} ⦵\n"
        f"🔄 Total transfers today: {transfers_today}",
        parse_mode="HTML"
    )

    try:
        await context.bot.send_message(
            chat_id=target.id,
            text=(f"🫐 You received {amount} Berrys from {berry_display_name(sender)}\n\n"
                  f"📥 Total received today: {received_after} ⦵\n"
                  f"📥 Receive remaining today: {target_receive_remaining} ⦵"),
            parse_mode="HTML"
        )
    except Exception:
        pass

async def transfer(update, context):
    (await save_user_async(update.effective_user))
    if not is_group_chat(update) or not update.message.reply_to_message:
        await safe_reply_text(update.message, "❌ Reply to the recipient's message in the group and use /transfer <code/name>.")
        return
    if not context.args:
        await safe_reply_text(update.message, "Usage: /transfer <4-digit code or character name>")
        return
    character_query = " ".join(context.args).strip()
    character = (await asyncio.to_thread(get_character, character_query))
    if not character:
        await safe_reply_text(update.message, "❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
        return
    sender_id = update.effective_user.id
    target_id = update.message.reply_to_message.from_user.id
    if target_id == sender_id:
        await safe_reply_text(update.message, "❌ You cannot transfer to yourself.")
        return
    if (await asyncio.to_thread(transfer_pair_blocked, sender_id, target_id)):
        await safe_reply_text(update.message,
            "🚫 Character transfer between these two users is blocked by staff."
        )
        return
    owned = (await asyncio.to_thread(mongo_db.count_user_copies, sender_id, character[0]))
    if owned < 1:
        await safe_reply_text(update.message, "❌ You don't own this character.")
        return
    transfer_id=f"{sender_id}:{target_id}:{character[0]}:{update.message.message_id}"
    PENDING_TRANSFERS[transfer_id]={
        "sender":sender_id,
        "target":target_id,
        "code":character[0],
        "expires":datetime.now()+timedelta(seconds=TRANSFER_TTL),
        "sender_name": update.effective_user.first_name or "Unknown",
        "sender_username": update.effective_user.username or "",
        "target_name": update.message.reply_to_message.from_user.first_name or "Unknown",
        "target_username": update.message.reply_to_message.from_user.username or "",
    }
    kb=InlineKeyboardMarkup([[InlineKeyboardButton("✅ Accept", callback_data=f"tr_accept:{transfer_id}"), InlineKeyboardButton("❌ Decline", callback_data=f"tr_decline:{transfer_id}")]])
    await safe_reply_text(update.message,
        f"🎁 {character[1]} [{character[0]}] transfer request\n"
        f"👤 From: {update.effective_user.first_name or sender_id}\n"
        f"👤 To: {update.message.reply_to_message.from_user.first_name or target_id}\n"
        "⏰ Valid for 1 hour.", reply_markup=kb
    )

async def transfer_callback(update, context):
    q=update.callback_query
    data=q.data or ""
    action, transfer_id = data.split(":",1)
    item=PENDING_TRANSFERS.get(transfer_id)
    if not item:
        await q.answer("⚠️ This transfer has expired or the bot was restarted.", show_alert=True); return
    if q.from_user.id != item["target"]:
        await q.answer("❌ Only the recipient can accept or decline this request.", show_alert=True); return
    if datetime.now() >= item["expires"]:
        PENDING_TRANSFERS.pop(transfer_id,None)
        await q.answer("⏰ This transfer has expired.", show_alert=True)
        await q.edit_message_text("⏰ The acceptance window expired, so the character was not transferred.")
        return
    if action == "tr_decline":
        PENDING_TRANSFERS.pop(transfer_id,None)
        await q.answer("Transfer declined.")
        await q.edit_message_text("❌ Transfer declined. The character remains with the sender.")
        return
    try:
        (await asyncio.to_thread(mongo_db.ensure_user, item["target"], q.from_user.username or "", q.from_user.first_name or "", q.from_user.last_name or ""))
        moved = (await asyncio.to_thread(mongo_db.transfer_one_copy, item["sender"], item["target"], item["code"]))
    except Exception as e:
        print("Transfer transaction error:", e)
        await q.answer("❌ Transfer failed. Please try again.", show_alert=True)
        return
    if not moved:
        PENDING_TRANSFERS.pop(transfer_id, None)
        await q.answer("❌ The sender no longer owns this character.", show_alert=True); await q.edit_message_text("❌ Transfer failed: the sender no longer owns this character."); return
    PENDING_TRANSFERS.pop(transfer_id, None)
    await q.answer("✅ Character received!")
    await q.edit_message_text(f"✅ Transfer accepted! Character [{item['code']}] has been added to the recipient's collection.")

    try:
        transferred_character = (await asyncio.to_thread(get_character_by_code, item["code"]))
        sender_handle = f"@{item.get('sender_username')}" if item.get('sender_username') else "No username"
        target_handle = f"@{item.get('target_username')}" if item.get('target_username') else "No username"
        await notify_admins(
            context,
            f"🎁 CHARACTER TRANSFERRED\n"
            f"🎭 Character: {transferred_character[1] if transferred_character else item['code']} [{item['code']}]\n"
            f"👤 From: {item.get('sender_name', 'Unknown')} | ID: {item['sender']} | {sender_handle}\n"
            f"👤 To: {item.get('target_name', 'Unknown')} | ID: {item['target']} | {target_handle}"
        )
    except Exception as e:
        print("Transfer notification error:", e)

async def gift(update, context):
    owner_id = update.effective_user.id
    if not is_owner(owner_id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return

    target_id = None
    code = None
    reply = update.message.reply_to_message

    if is_group_chat(update) and reply and reply.from_user and context.args:
        target = reply.from_user
        if target.is_bot:
            await safe_reply_text(update.message, "❌ You cannot gift a character to a bot.")
            return
        target_id = target.id
        code = " ".join(context.args).strip()

    elif update.effective_chat.type == "private" and len(context.args) >= 2:
        target_text = context.args[-1].strip()
        if not target_text.isdigit():
            await safe_reply_text(update.message, "❌ User ID must contain numbers only.")
            return
        target_id = int(target_text)
        code = " ".join(context.args[:-1]).strip()

    else:
        await safe_reply_text(update.message,
            "🎁 Gift Usage\n\n"
            "Owner DM: /gift <code or character name> <user_id>\n"
            "Group reply: /gift <code or character name>"
        )
        return

    character = (await asyncio.to_thread(get_character, code))
    if not character:
        await safe_reply_text(update.message, "❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
        return
    code = character[0]

    if target_id == update.effective_user.id:
        await safe_reply_text(update.message, "❌ You cannot gift a character to yourself.")
        return

    try:
        (await asyncio.to_thread(mongo_db.ensure_user, target_id, "", ""))
        (await asyncio.to_thread(mongo_db.add_collection, target_id, character[0], timestamp()))
    except Exception as e:
        print("Gift transaction error:", e)
        await safe_reply_text(update.message, "❌ Gift failed due to a database error. Check the bot console.")
        return

    await safe_reply_text(update.message,
        f"🎁 Gift sent successfully!\n🎭 {character[1]} [{character[0]}]\n👤 User ID: {target_id}"
    )

    try:
        await context.bot.send_message(
            chat_id=target_id,
            text=f"🎁 You received a character gift!\n🎭 {character[1]} [{character[0]}]\n👑 From: Owner"
        )
    except Exception as e:
        print(f"Gift recipient notification error for {target_id}: {e}")

async def daily(update, context):
    (await save_user_async(update.effective_user))
    user_id = update.effective_user.id

    india_tz = timezone(timedelta(hours=5, minutes=30))
    now_dt = datetime.now(india_tz)

    rare_characters = (await asyncio.to_thread(get_characters_by_rarity, "Rare"))
    common_characters = (await asyncio.to_thread(get_characters_by_rarity, "Common"))
    if not rare_characters or len(common_characters) < 2:
        await safe_reply_text(update.message,
            "❌ Daily reward cannot be prepared because the required Rare/Common characters are missing."
        )
        return

    rare = random.choice(rare_characters)
    common_pool = random.sample(common_characters, 2)
    rewards = [rare, common_pool[0], common_pool[1]]

    reward_stamp = timestamp()

    def _claim_daily(session):
        exists, last_daily = mongo_db.get_last_daily(user_id, session=session)
        if not exists:
            raise RuntimeError("daily user row missing")
        if last_daily:
            try:
                last = datetime.fromisoformat(last_daily)
                if last.tzinfo is None:
                    last = last.replace(tzinfo=india_tz)
                reset = now_dt.replace(hour=DAILY_RESET_HOUR, minute=0, second=0, microsecond=0)
                if now_dt < reset:
                    reset -= timedelta(days=1)
                if last >= reset:
                    return "already"
            except (ValueError, TypeError):
                pass
        # compare-and-set on last_daily so two simultaneous /daily calls cannot both pay out
        if not mongo_db.claim_daily(user_id, last_daily, DAILY_COINS, reward_stamp, session=session):
            return "already"
        mongo_db.add_collections(user_id, [ch[0] for ch in rewards], reward_stamp, session=session)
        return "ok"

    try:
        daily_result = (await asyncio.to_thread(mongo_db.run_transaction, _claim_daily))
    except Exception as e:
        print("Daily transaction error:", e)
        await safe_reply_text(update.message, "❌ Daily reward could not be claimed. Please try again.")
        return
    if daily_result == "already":
        await safe_reply_text(update.message, "⏳ Daily already claimed.")
        return

    await safe_reply_text(update.message,
        "🎁 Daily Reward!\n\n"
        f"💰 +{DAILY_COINS} Berrys\n"
        "🎭 +1 Rare character\n"
        "⚪ +2 Common characters\n\n"
        f"🔵 {rare[1]} [{rare[0]}]\n"
        f"⚪ {common_pool[0][1]} [{common_pool[0][0]}]\n"
        f"⚪ {common_pool[1][1]} [{common_pool[1][0]}]"
    )

    for character in rewards:
        photo = character[5]
        if photo:
            try:
                await context.bot.send_photo(
                    chat_id=update.message.chat_id,
                    photo=photo,
                    caption=add_display_name_header(
                        update.message, f"{rarity_text(character[3])} {character[1]}"
                    ),
                    parse_mode="HTML",
                )
            except Exception as e:
                print("Daily photo error:", e)
    await rewards.record(context.bot, user_id, "daily", chat_id=update.message.chat_id,
                          name=berry_display_name(update.effective_user))     # festival quests (never raises)

ADD_NAME, ADD_RECRUIT, ADD_ANIME, ADD_RARITY, ADD_WORTH, ADD_CODE, ADD_PHOTO = range(7)

async def addcharacter_start(update, context):
    if update.effective_chat.type != "private":
        await safe_reply_text(update.message, "⚠️ /addcharacter can only be used in the bot's PM (private chat).")
        return ConversationHandler.END
    if not (await asyncio.to_thread(can_manage_characters, update.effective_user.id)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return ConversationHandler.END

    _rg_state.pop(update.effective_user.id, None)
    for key in ("name", "anime", "rarity", "worth", "code", "worth_default"):
        context.user_data.pop(key, None)

    await safe_reply_text(update.message, "1️⃣ Send character name:")
    return ADD_NAME

async def addcharacter_name(update, context):
    name = update.message.text.strip()
    if not name or is_skip_text(name):
        await safe_reply_text(update.message, "❌ Character name is required. Please send a valid name.")
        return ADD_NAME
    context.user_data["name"] = name
    await safe_reply_text(update.message,
        "2️⃣ Send recruitment names (comma separated), or tap ⏭ Skip:\n"
        "Example: Naruto, Uzumaki, Hero of the Village\n\n"
        "⚠️ These are only search/catch names. The real character name stays unchanged." ,
        reply_markup=skip_keyboard()
    )
    return ADD_RECRUIT

async def addcharacter_recruit(update, context):
    text = update.message.text.strip()
    if is_skip_text(text):
        names = []
    else:
        names = []
        seen = set()
        for part in text.split(","):
            alias = " ".join(part.split()).strip()
            key = alias.casefold()
            if alias and key not in seen:
                seen.add(key)
                names.append(alias)
    context.user_data["recruit_names"] = names
    await safe_reply_text(update.message, "3️⃣ Send anime name, or tap ⏭ Skip:", reply_markup=skip_keyboard())
    return ADD_ANIME

async def addcharacter_anime(update, context):
    text = update.message.text.strip()
    context.user_data["anime"] = "" if is_skip_text(text) else text
    await safe_reply_text(update.message,
        "3️⃣ Send rarity:\n"
        "Common / Rare / Epic / Legendary / Mythical / Celestial"
    )
    return ADD_RARITY

async def addcharacter_rarity(update, context):
    text = update.message.text.strip()
    if is_skip_text(text):
        context.user_data["rarity"] = ""
        context.user_data["worth_default"] = None
        await safe_reply_text(update.message, "4️⃣ Send worth in Berrys (required):")
        return ADD_WORTH
    rarity = text.title()

    if rarity not in SYMBOL or rarity in ("Heavenly", "Special"):
        await safe_reply_text(update.message, "❌ Invalid rarity.")
        return ADD_RARITY

    context.user_data["rarity"] = rarity
    default = await default_worth_async(rarity)
    context.user_data["worth_default"] = default
    if default is None:
        await safe_reply_text(update.message, "4️⃣ Send worth in Berrys:")
    else:
        await safe_reply_text(update.message,
            f"4️⃣ The default worth of a {rarity} character is {default}.\n"
            "To change it, send a number. To keep it, tap ⏭ Skip.",
            reply_markup=skip_keyboard())
    return ADD_WORTH

async def addcharacter_worth(update, context):
    text = update.message.text.strip()
    default = context.user_data.get("worth_default")
    if is_skip_text(text) and default is not None:
        worth = default                      # Skip = keep the default worth of this rarity
    else:
        try:
            worth = int(text)
            if worth < 0:
                raise ValueError
        except ValueError:
            await safe_reply_text(update.message, "❌ Worth must be a number.")
            return ADD_WORTH

    context.user_data["worth"] = worth
    markup = await rg_free_codes_markup(update.effective_user.id, context.user_data.get("anime"))
    await safe_reply_text(update.message, "5️⃣ Send unique 4-digit code:", reply_markup=markup or ReplyKeyboardRemove())
    return ADD_CODE

async def addcharacter_code(update, context):
    code = update.message.text.strip()

    if not (code.isdigit() and len(code) == 4 and 1 <= int(code) <= 9999):
        await safe_reply_text(update.message,
            "❌ Code must be exactly 4 digits (0001-9999)."
        )
        return ADD_CODE

    problem = await rg_code_problem(context.user_data.get("anime"), code)      # anime code range check
    if problem:
        await safe_reply_text(update.message, problem,
                              reply_markup=await rg_free_codes_markup(update.effective_user.id, context.user_data.get("anime")))
        return ADD_CODE

    if (await asyncio.to_thread(get_character, code)):
        await safe_reply_text(update.message, "❌ Code already exists.")
        return ADD_CODE

    context.user_data["code"] = code
    await safe_reply_text(update.message, "6️⃣ Send the character photo, or tap ⏭ Skip:", reply_markup=skip_keyboard())
    return ADD_PHOTO

async def addcharacter_photo(update, context):
    if is_skip_text(update.message.text):
        photo_id = None
    elif update.message.photo:
        photo_id = update.message.photo[-1].file_id
    else:
        await safe_reply_text(update.message, "❌ Send a photo or /skip.")
        return ADD_PHOTO

    d = dict(context.user_data)

    try:
        (await asyncio.to_thread(mongo_db.insert_character, d["code"], d["name"], d["anime"], d["rarity"], d["worth"], photo_id,
                                  d.get("recruit_names", [])))
        adder = update.effective_user
        (await asyncio.to_thread(log_character_action, d["code"], d["name"], adder, "add"))
    except mongo_db.DuplicateKeyError:
        context.user_data.clear()
        await safe_reply_text(update.message, "❌ Name or code already exists.")
        return ConversationHandler.END
    except Exception as e:
        print("Add character error:", e)
        context.user_data.clear()
        await safe_reply_text(update.message, "❌ Could not add character. Please try again.")
        return ConversationHandler.END

    context.user_data.clear()

    await safe_reply_text(update.message,
        f"✅ Character added successfully!\n"
        f"🎭 {d['name']}\n"
        f"🏷 {rarity_text(d['rarity'])}\n"
        f"💰 {d['worth']}\n"
        f"🔢 {d['code']}"
    )
    try:
        await notify_staff_action(
            context,
            f"🎭 NEW CHARACTER ADDED\n"
            f"🎭 {d['name']} [{d['code']}]\n"
            f"📺 Anime: {d.get('anime') or 'Not set'}\n"
            f"🏷 {rarity_text(d['rarity'])}\n"
            f"💰 Worth: {d['worth']}\n"
            f"📷 Photo: {'Added' if photo_id else 'Not added'}\n"
            f"👤 By: {display_user(update.effective_user)}",
            actor_id=update.effective_user.id,
        )
    except Exception as e:
        print("Character add notification error:", e)

    await release_conv_log(context, update.effective_user.id, "addcharacter")
    return ConversationHandler.END

async def addlist(update, context):
    today = india_today_key()
    stats = {}
    for d in await asyncio.to_thread(lambda: list(_mc("character_additions_v2").find({}))):
        s = stats.setdefault(d.get("added_by"), [None, None, None, 0, 0, 0, 0])
        for i, key in enumerate(("added_first_name", "added_last_name", "added_username")):
            v = d.get(key)
            if v is not None and (s[i] is None or v > s[i]):
                s[i] = v
        action = d.get("action")
        action = "add" if action is None else action
        is_today = str(d.get("added_at") or "")[:10] == today
        if action == "add":
            s[3] += 1
            s[4] += 1 if is_today else 0
        elif action == "edit":
            s[5] += 1
            s[6] += 1 if is_today else 0
    rows = sorted(((uid, *s) for uid, s in stats.items()), key=lambda r: (-r[4], -r[6], r[0] or 0))

    if not rows:
        await safe_reply_text(update.message, "📊 No character add/edit records yet.")
        return

    lines = ["🏆 NEW CHARACTER ADD/EDIT RANKING", "",
             "Ranking = Total Character Added", ""]
    for rank, (uid, first, last, username, total_added, today_added, total_edited, today_edited) in enumerate(rows, 1):
        name = " ".join(v for v in (first or "", last or "") if v).strip() or "Unknown"
        medal = {1: "🥇", 2: "🥈", 3: "🥉"}.get(rank, f"{rank}.")
        lines.append(f"{medal} {name}")
        if username:
            lines.append(f"@{username}")
        lines.append(f"🆔 {uid}")
        lines.append(f"🎭 Total Character Added: {total_added}")
        lines.append(f"📅 Today Character Added: {today_added}")
        lines.append(f"✏️ Total Characters Edited: {total_edited}")
        lines.append(f"📅 Today Character Edited: {today_edited}")
        lines.append("")

    await safe_reply_text(update.message, "\n".join(lines).rstrip())

async def addphoto(update, context):
    if not (await asyncio.to_thread(can_manage_characters, update.effective_user.id)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return

    if not context.args:
        await safe_reply_text(update.message,
            "Usage: /editphoto <name or code>"
        )
        return

    character = (await asyncio.to_thread(get_character, " ".join(context.args)))

    if not character:
        await safe_reply_text(update.message, "❌ Character not found.")
        return
    if await asyncio.to_thread(mongo_db.is_evolution_character, character[0]):
        await safe_reply_text(update.message, f"{mongo_db.evolution_mark(character[0])} This is an Evolution character. Change its photo with /editevo.")
        return

    context.user_data["photo_code"] = character[0]
    await safe_reply_text(update.message,
        f"📷 Send photo for {character[1]}."
    )

async def receive_photo(update, context):
    code = context.user_data.get("photo_code")

    if (
        not code
        or not (await asyncio.to_thread(can_manage_characters, update.effective_user.id))
        or not update.message.photo
    ):
        return

    if await asyncio.to_thread(mongo_db.is_evolution_character, code):    # still guarded at save time
        context.user_data.pop("photo_code", None)
        await safe_reply_text(update.message, f"{mongo_db.evolution_mark(code)} This is an Evolution character. Change its photo with /editevo.")
        return
    try:
        updated = (await asyncio.to_thread(mongo_db.update_character_photo, code, update.message.photo[-1].file_id))
    except Exception as e:
        print("Photo save error:", e)
        await safe_reply_text(update.message, "❌ Could not save the photo. Please try again.")
        return
    if not updated:
        await safe_reply_text(update.message, "❌ Character no longer exists.")
        return

    context.user_data.pop("photo_code", None)
    await asyncio.to_thread(clear_photo_restriction, code)       # photo exists now: the character may spawn again
    await safe_reply_text(update.message, "✅ Photo saved.", reply_markup=ReplyKeyboardRemove())
    character = (await asyncio.to_thread(get_character_by_code, code))
    await notify_staff_action(
        context,
        f"📷 CHARACTER PHOTO UPDATED\n🎭 {character[1] if character else 'Unknown'} [{code}]\n👤 By: {display_user(update.effective_user)}",
        actor_id=update.effective_user.id,
    )

EDIT_NAME, EDIT_RECRUIT, EDIT_ANIME, EDIT_RARITY, EDIT_WORTH, EDIT_CODE = range(10, 16)

async def editcharacter(update, context):
    if update.effective_chat.type != "private":
        await safe_reply_text(update.message, "⚠️ /editcharacter can only be used in the bot's PM (private chat).")
        return ConversationHandler.END
    if not (await asyncio.to_thread(can_manage_characters, update.effective_user.id)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return ConversationHandler.END
    if not context.args:
        await safe_reply_text(update.message, "Usage: /editcharacter <4-digit code or character name>")
        return ConversationHandler.END
    _rg_state.pop(update.effective_user.id, None)
    query = " ".join(context.args).strip()
    character = (await asyncio.to_thread(get_character, query))
    normal_matches = []
    if not character:
        matches = (await asyncio.to_thread(find_characters_by_name_parts, query))
        normal_matches = [m for m in matches if not mongo_db.is_evolution_character(m[0])]
        if matches and not normal_matches:
            await safe_reply_text(update.message, f"{mongo_db.evolution_mark(matches[0][0])} This is an Evolution character. Evolution characters are edited with /editevo.")
            return ConversationHandler.END
        if len(matches) > 1 and len(normal_matches) == 1:
            character = normal_matches[0]      # the other match is an Evolution character: edit the normal one
    if not character:
        if len(normal_matches) > 1:
            await safe_reply_text(
                update.message,
                "❓ Multiple characters found. Select one:",
                reply_markup=character_selection_keyboard(update.effective_user.id, "edit", normal_matches),
            )
            return ConversationHandler.END
        recruit_matches = [m for m in (await asyncio.to_thread(find_characters_by_recruit_name_partial, query))
                           if not mongo_db.is_evolution_character(m[0])]
        if len(recruit_matches) > 1:
            await safe_reply_text(
                update.message,
                "❓ Multiple characters found. Select one:",
                reply_markup=character_selection_keyboard(update.effective_user.id, "edit", recruit_matches),
            )
            return ConversationHandler.END
        await safe_reply_text(update.message, "❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
        return ConversationHandler.END
    code = character[0]
    if await asyncio.to_thread(mongo_db.is_evolution_character, code):    # /edit and /editcharacter: NORMAL characters only
        await safe_reply_text(update.message, f"{mongo_db.evolution_mark(code)} This is an Evolution character. Evolution characters are edited with /editevo.")
        return ConversationHandler.END
    context.user_data["edit_code_original"] = code
    context.user_data["edit_character"] = character
    await safe_reply_text(update.message,
        f"✏️ Editing {character[1]} [{character[0]}]\n\n"
        "1️⃣ Send new character name, or tap ⏭ Skip to keep current."
        f"\nCurrent: {character[1]}",
        reply_markup=skip_keyboard()
    )
    return EDIT_NAME

async def edit_name(update, context):
    if is_skip_text(update.message.text):
        context.user_data["edit_name"] = context.user_data["edit_character"][1]
    else:
        name = update.message.text.strip()
        if not name:
            await safe_reply_text(update.message, "❌ Character name cannot be empty. Send a valid name or /skip.")
            return EDIT_NAME
        context.user_data["edit_name"] = name
    await safe_reply_text(update.message,
        "2️⃣ Send recruitment names (comma separated), or tap ⏭ Skip to keep current.\n"
        "These are search/catch aliases only."
    , reply_markup=skip_keyboard())
    return EDIT_RECRUIT

async def edit_recruit(update, context):
    current = (await asyncio.to_thread(get_recruit_names, context.user_data["edit_code_original"]))
    if is_skip_text(update.message.text):
        names=current
    else:
        names=[]; seen=set()
        for part in update.message.text.split(","):
            alias=" ".join(part.split()).strip()
            key=alias.casefold()
            if alias and key not in seen:
                seen.add(key); names.append(alias)
    context.user_data["edit_recruit_names"] = names
    await safe_reply_text(update.message, "3️⃣ Send new anime name, or tap ⏭ Skip to keep current.", reply_markup=skip_keyboard())
    return EDIT_ANIME

async def edit_anime(update, context):
    if is_skip_text(update.message.text):
        context.user_data["edit_anime"] = context.user_data["edit_character"][2]
    else:
        context.user_data["edit_anime"] = update.message.text.strip()
    await safe_reply_text(update.message, "3️⃣ Send rarity (Common/Rare/Epic/Legendary/Mythical/Celestial), or tap ⏭ Skip.", reply_markup=skip_keyboard())
    return EDIT_RARITY

async def edit_rarity(update, context):
    text = update.message.text.strip()
    if is_skip_text(text):
        rarity = context.user_data["edit_character"][3]
    else:
        rarity = text.title()
        if rarity not in SYMBOL or rarity in ("Heavenly", "Special"):
            await safe_reply_text(update.message, "❌ Invalid rarity.")
            return EDIT_RARITY
    context.user_data["edit_rarity"] = rarity
    default = None
    if rarity != context.user_data["edit_character"][3]:
        default = await default_worth_async(rarity)      # rarity changed -> worth follows the new rarity's default
    context.user_data["edit_worth_default"] = default
    if default is not None:
        await safe_reply_text(update.message,
            f"4️⃣ Rarity changed to {rarity}. The default worth of a {rarity} character is {default}.\n"
            "To change it, send a number. To keep it, tap ⏭ Skip.",
            reply_markup=skip_keyboard())
    else:
        await safe_reply_text(update.message, "4️⃣ Send new worth, or tap ⏭ Skip to keep current worth.", reply_markup=skip_keyboard())
    return EDIT_WORTH

async def edit_worth(update, context):
    text = update.message.text.strip()
    if is_skip_text(text):
        default = context.user_data.get("edit_worth_default")
        worth = default if default is not None else context.user_data["edit_character"][4]
    else:
        try:
            worth = int(text)
            if worth < 0: raise ValueError
        except ValueError:
            await safe_reply_text(update.message, "❌ Worth must be a non-negative number.")
            return EDIT_WORTH
    context.user_data["edit_worth"] = worth
    await safe_reply_text(update.message, "5️⃣ Send new unique 4-digit code, or tap ⏭ Skip to keep current.", reply_markup=skip_keyboard())
    return EDIT_CODE

async def edit_code(update, context):
    text = update.message.text.strip()
    old_code = context.user_data["edit_code_original"]
    if is_skip_text(text):
        new_code = old_code
    else:
        if not (text.isdigit() and len(text) == 4 and 1 <= int(text) <= 9999):
            await safe_reply_text(update.message, "❌ Code must be exactly 4 digits (0001-9999).")
            return EDIT_CODE
        if text != old_code:
            problem = await rg_code_problem(context.user_data.get("edit_anime"), text, exclude_code=old_code)
            if problem:
                await safe_reply_text(update.message, problem)
                return EDIT_CODE
        existing = (await asyncio.to_thread(get_character_by_code, text))
        if existing and text != old_code:
            await safe_reply_text(update.message, "❌ That code already exists.")
            return EDIT_CODE
        new_code = text

    d = context.user_data
    active = context.application.bot_data.setdefault("active_spawns", {})
    if any(str(spawn.get("code")) == str(old_code) for spawn in active.values()):
        await safe_reply_text(update.message, "❌ This character is currently spawned in a group. Catch/expire that spawn before editing it.")
        context.user_data.clear()
        return ConversationHandler.END
    new_recruit_names = d.get("edit_recruit_names", (await asyncio.to_thread(get_recruit_names, old_code)))
    try:
        updated = (await asyncio.to_thread(mongo_db.update_character, old_code, new_code, d["edit_name"], d["edit_anime"],
                                           d["edit_rarity"], d["edit_worth"], new_recruit_names))
        if not updated:      # missing, or an Evolution character (those use /editevo)
            await safe_reply_text(update.message, "❌ Update failed: the character no longer exists, or it is an Evolution character (use /editevo).")
            context.user_data.clear()
            return ConversationHandler.END
    except mongo_db.DuplicateKeyError:
        await safe_reply_text(update.message, "❌ Update failed: name or code may already exist.")
        context.user_data.clear()
        return ConversationHandler.END
    except Exception as e:
        print("Edit character error:", e)
        await safe_reply_text(update.message, "❌ Update failed. Please try again.")
        context.user_data.clear()
        return ConversationHandler.END
    # shop + audit-log bookkeeping
    try:
        if new_code != old_code:
            (await asyncio.to_thread(_mc("shop_v3").update_many, {"character_code": old_code}, {"$set": {"character_code": new_code}}))
        (await asyncio.to_thread(log_character_action, new_code, d["edit_name"], update.effective_user, "edit"))
    except Exception as e:
        print("Edit character bookkeeping error:", e)

    await safe_reply_text(update.message,
        f"✅ Character edit successfully!\n\n🎭 {d['edit_name']}\n📺 {d['edit_anime']}\n"
        f"🏷 {rarity_text(d['edit_rarity'])}\n💰 {d['edit_worth']}\n🔢 {new_code}\n"
        f"🔎 Aliases: {', '.join(d.get('edit_recruit_names', [])) or 'None'}"
    )
    code_line = (
        f"🔁 Old code: {old_code}\n"
        if new_code != old_code
        else f"🔢 Code: {new_code}\n"
    )
    await notify_staff_action(
        context,
        f"✏️ CHARACTER UPDATED\n"
        f"🎭 {d['edit_name']} [{new_code}]\n"
        f"📺 Anime: {d['edit_anime'] or 'Not set'}\n"
        f"🏷 {rarity_text(d['edit_rarity'])}\n"
        f"💰 Worth: {d['edit_worth']}\n"
        f"{code_line}"
        f"👤 By: {display_user(update.effective_user)}",
        actor_id=update.effective_user.id,
    )
    context.user_data.clear()
    await release_conv_log(context, update.effective_user.id, "editcharacter")
    return ConversationHandler.END

async def discontinue_command(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    if not context.args:
        await safe_reply_text(update.message, "Usage: /discontinue <4-digit code or character name>")
        return
    query = " ".join(context.args).strip()
    character = (await asyncio.to_thread(get_character, query))
    if not character:
        await safe_reply_text(update.message, "❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
        return
    code = character[0]
    if (await asyncio.to_thread(is_character_discontinued, code)):
        await safe_reply_text(update.message, f"⚠️ {character[1]} [{code}] is already discontinued.")
        return
    (await asyncio.to_thread(discontinue_character, code, update.effective_user.id))
    await safe_reply_text(update.message,
        f"🚫 Character discontinued.\n\n🎭 {character[1]}\n🔢 Code: {code}\n\n"
        f"It will no longer spawn until the Owner uses /continue {code}."
    )
    await notify_staff_action(context, f"🚫 CHARACTER DISCONTINUED\n🎭 {character[1]} [{code}]\n👤 By: {display_user(update.effective_user)}", actor_id=update.effective_user.id)

async def continue_command(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    if not context.args:
        await safe_reply_text(update.message, "Usage: /continue <4-digit code or character name>")
        return
    query = " ".join(context.args).strip()
    character = (await asyncio.to_thread(get_character, query))
    if not character:
        await safe_reply_text(update.message, "❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
        return
    code = character[0]
    if not (await asyncio.to_thread(continue_character, code)):
        await safe_reply_text(update.message, f"⚠️ {character[1]} [{code}] is not discontinued.")
        return
    await safe_reply_text(update.message,
        f"✅ Character continued.\n\n🎭 {character[1]}\n🔢 Code: {code}\n\nIt can spawn again."
    )
    await notify_staff_action(context, f"✅ CHARACTER CONTINUED\n🎭 {character[1]} [{code}]\n👤 By: {display_user(update.effective_user)}", actor_id=update.effective_user.id)

async def delete(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return

    if not context.args:
        await safe_reply_text(update.message,
            "Usage: /delete <name or code>"
        )
        return

    character = (await asyncio.to_thread(get_character, " ".join(context.args)))

    if not character:
        await safe_reply_text(update.message, "❌ Character not found.")
        return

    code, name, anime, rarity, worth, photo = character

    lock = get_spawn_lock(context.application)
    async with lock:
        active = context.application.bot_data.setdefault("active_spawns", {})
        removed_active = {}
        for chat_id, spawn_data in list(active.items()):
            if str(spawn_data.get("code")) == str(code):
                removed_active[chat_id] = spawn_data
                del active[chat_id]

        try:
            (await asyncio.to_thread(mongo_db.delete_character, code))
        except Exception as e:
            active.update(removed_active)
            print("delete character error:", e)
            await safe_reply_text(update.message, "❌ Could not delete the character.")
            return

    for removed_chat_id, removed_spawn in removed_active.items():
        await safe_delete_message(context.bot, removed_chat_id, removed_spawn.get("message_id"))

    await safe_reply_text(update.message,
        f"🗑 Deleted {name} [{code}]."
        + (f"\n🧹 Removed {len(removed_active)} active spawn(s)." if removed_active else "")
    )
    await notify_staff_action(
        context,
        f"🗑 CHARACTER DELETED\n🎭 {name} [{code}]\n🏷 {rarity_text(rarity)}\n👤 By: {display_user(update.effective_user)}",
        actor_id=update.effective_user.id,
    )

def purge_user_data(user_id):
    """Remove a user completely: characters, coins/profile, favorites, shop rows, free-refresh credits."""
    uid = int(user_id)
    def _work(session):
        copies = _mc(mongo_db.COLLECTIONS).delete_many({"user_id": uid}, session=session).deleted_count
        _mc(mongo_db.FAVORITES).delete_one({"_id": uid}, session=session)
        _mc(mongo_db.NOTIFICATIONS).delete_one({"_id": uid}, session=session)
        _mc("shop_v3").delete_many({"user_id": uid}, session=session)
        _mc("shop_purchases_v2").delete_many({"user_id": uid}, session=session)
        _mc("shop_free_refresh_v1").delete_one({"_id": uid}, session=session)
        badge_banner.purge_user(uid, session)        # badge claims + equipped banner
        rewards.purge_user(uid, session)            # festival progress, claims, event-banner grants, wishes
        removed = _mc(mongo_db.USERS).delete_one({"_id": uid}, session=session).deleted_count
        return copies, removed
    return mongo_db.run_transaction(_work)

DELETED_SWEEP_HOURS = float(os.getenv("DELETED_ACCOUNT_SWEEP_HOURS", "6"))
DELETED_SWEEP_STRIKES = 2          # consecutive sweeps that must flag an account before the owner is asked about it
DELETED_KEEP_DAYS = float(os.getenv("DELETED_ACCOUNT_KEEP_DAYS", "30"))   # after "Keep Data", don't ask again for this long
DELETED_MAX_NOTIFY_PER_SWEEP = 10  # never flood the owner; the rest are picked up by later sweeps
DELETED_CONFIRM_SECONDS = 600      # how long the "Yes, delete permanently" screen stays valid after Delete Data

# Review state is stored on the existing users document (no new collection; mongo_db only ever $set/$inc's
# users documents, so these extra fields are never wiped and never break existing code):
#   deleted_review       = "pending"  -> owner was notified and has not answered yet (no repeat notifications)
#                          "kept"     -> owner chose Keep Data (suppressed for DELETED_KEEP_DAYS)
#                          "deleting" -> a confirmed deletion is running right now (blocks double taps)
#   deleted_review_token = random id of ONE notification; every button carries it, so buttons from an
#                          old/cancelled/answered notification can never act on a newer review
#   deleted_review_at    = unix time of the last state change
#   deleted_review_confirm_at = unix time the owner pressed Delete Data (opened the confirmation screen);
#                          the final "Yes" is only accepted for DELETED_CONFIRM_SECONDS after this
_DELETED_REVIEW_FIELDS = {"deleted_review": "", "deleted_review_at": "", "deleted_review_reason": "",
                          "deleted_review_token": "", "deleted_review_confirm_at": ""}
_DELETED_CB_RE = re.compile(r"^delacct:(ask|keep|yes|no):(-?\d+):([0-9a-f]{10})$")

def _deleted_review_protected(uid):
    """Owner IDs (and anything that is not a normal positive user id) never enter this workflow."""
    try:
        uid = int(uid)
    except (TypeError, ValueError):
        return True
    return uid <= 0 or is_owner(uid) or uid in ADMIN_IDS

async def _telegram_account_deleted(bot, uid):
    """
    Classify what Telegram says about a user. NOTHING here ever deletes data.
      "deleted"     = Telegram returned a profile named "Deleted Account" with no username and no last name
                      (strong signal, but still only a signal: the owner always decides)
      "unreachable" = Telegram said "chat not found"/"user not found" (WEAK signal: this also happens for users
                      who never started the bot, blocked it, or during a temporary API problem - never proof)
      False         = the account exists
      None          = could not tell (network error, timeout, rate limit, anything uncertain)
    """
    try:
        chat = await bot.get_chat(uid)
    except RetryAfter as e:
        await asyncio.sleep(float(e.retry_after) + 1)
        return None
    except BadRequest as e:
        reason = str(e).lower()
        return "unreachable" if ("chat not found" in reason or "user not found" in reason) else None
    except Exception:
        return None
    if (getattr(chat, "first_name", None) or "").strip().lower() != "deleted account":
        return False
    if getattr(chat, "username", None) or (getattr(chat, "last_name", None) or "").strip():
        return False                                   # a live account that merely uses that name
    return "deleted"

def _deleted_review_keyboard(uid, token):
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("🗑️ Delete Data", callback_data=f"delacct:ask:{uid}:{token}"),
        InlineKeyboardButton("❌ Keep Data", callback_data=f"delacct:keep:{uid}:{token}"),
    ]])

async def _notify_owner_possible_deleted(app, uid, signal, strikes, token):
    """Send the owner a review message. Returns True only if Telegram accepted it (really delivered)."""
    owner_id = ADMIN_IDS[0] if ADMIN_IDS else None
    if owner_id is None or _deleted_review_protected(uid):
        return False
    try:
        names = await asyncio.to_thread(mongo_db.get_user_names, uid)
        owned = await asyncio.to_thread(lambda: _mc(mongo_db.COLLECTIONS).count_documents({"user_id": uid}))
    except Exception as e:
        print(f"Possible-deleted-account lookup error for {uid}:", e)
        names, owned = None, "unknown"
    first, last, username = names if names else ("Unknown", "", "")
    display = " ".join(v for v in [first, last] if v).strip() or "Unknown"
    if signal == "deleted":
        why = "STRONG signal: Telegram shows this profile as \"Deleted Account\"."
    else:
        why = ("UNCERTAIN result: Telegram reports the chat/user as not found. This can also mean the user never "
               "started the bot, blocked it, or a temporary Telegram problem.")
    text = (
        "⚠️ POSSIBLE DELETED ACCOUNT\n\n"
        f"🆔 ID: {uid}\n"
        f"👤 Name: {display}\n"
        f"🔗 Username: {('@' + username) if username else 'none'}\n"
        f"🎴 Characters: {owned}\n"
        f"🔎 Why flagged: {why}\n"
        f"📊 Flagged in {strikes} checks.\n\n"
        "Nothing has been deleted. Choose what to do with this user's data:"
    )
    try:
        await app.bot.send_message(chat_id=owner_id, text=text, entities=copyable_ids(text),
                                   reply_markup=_deleted_review_keyboard(uid, token))
        return True
    except Exception as e:
        print(f"Possible-deleted-account notification error for {uid}:", e)
        return False

async def sweep_deleted_accounts(app):
    """
    Look for users whose Telegram account MAY be deleted and ask the bot owner what to do.
    This sweep NEVER deletes any data. Deletion only happens after the owner presses Delete Data
    and then explicitly confirms (see deleted_account_review_callback), or via /deleteuser.
    """
    users = _mc(mongo_db.USERS)
    rows = await asyncio.to_thread(lambda: list(users.find(
        {}, {"_id": 1, "missing_strikes": 1, "deleted_review": 1, "deleted_review_at": 1})))
    checked = 0
    found = []                                         # (uid, state, strikes_if_recorded)
    now = time.time()
    for row in rows:
        try:
            uid = int(row["_id"])
        except (KeyError, TypeError, ValueError):
            continue
        if _deleted_review_protected(uid):
            continue
        review = row.get("deleted_review")
        if review == "kept" and (now - float(row.get("deleted_review_at") or 0)) < max(0.0, DELETED_KEEP_DAYS) * 86400:
            continue                                   # owner said Keep Data recently
        state = await _telegram_account_deleted(app.bot, uid)
        checked += 1
        await asyncio.sleep(0.06)                      # stay far below Telegram's rate limits
        if state is None:
            continue                                   # uncertain: no strike, no notice, nothing
        if state is False:
            unset = {}
            if row.get("missing_strikes"):
                unset["missing_strikes"] = ""
            if review in ("pending", "kept"):
                unset.update(_DELETED_REVIEW_FIELDS)   # the account is alive again: drop any stale review state
            if unset:
                try:
                    await asyncio.to_thread(users.update_one, {"_id": uid}, {"$unset": unset})
                except Exception as e:
                    print(f"Deleted-account review reset error for {uid}:", e)
            continue
        if review in ("pending", "deleting"):
            continue                                   # owner already notified: never notify twice
        found.append((uid, state, int(row.get("missing_strikes") or 0) + 1))
    # Safety brake, applied BEFORE any strike is written: many weak "not found" results at once means a
    # Telegram/API problem or users who never started the bot, so those results are discarded entirely.
    weak_count = sum(1 for _u, s, _n in found if s != "deleted")
    if weak_count > max(10, int(checked * 0.2)):
        print(f"⚠️ Deleted-account sweep: {weak_count} of {checked} weak 'not found' results ignored (looks like an API problem).")
        found = [f for f in found if f[1] == "deleted"]
    candidates = []
    for uid, state, strikes in found:
        try:
            await asyncio.to_thread(users.update_one, {"_id": uid}, {"$set": {"missing_strikes": strikes}})
        except Exception as e:
            print(f"Deleted-account strike save error for {uid}:", e)
            continue
        if strikes >= DELETED_SWEEP_STRIKES:
            candidates.append((uid, state, strikes))
    candidates.sort(key=lambda c: c[1] != "deleted")   # strong signals first
    notified = 0
    for uid, state, strikes in candidates[:DELETED_MAX_NOTIFY_PER_SWEEP]:
        token = uuid.uuid4().hex[:10]
        if not await _notify_owner_possible_deleted(app, uid, state, strikes, token):
            continue                                   # not delivered: do NOT mark pending, retry next sweep
        try:
            res = await asyncio.to_thread(
                users.update_one, {"_id": uid, "deleted_review": {"$nin": ["pending", "deleting"]}},
                {"$set": {"deleted_review": "pending", "deleted_review_at": time.time(),
                          "deleted_review_reason": state, "deleted_review_token": token},
                 "$unset": {"deleted_review_confirm_at": ""}})
            if res.matched_count:
                notified += 1
        except Exception as e:
            # The notice was delivered but could not be recorded: its buttons will simply report "no longer active".
            print(f"Deleted-account pending-state save error for {uid}:", e)
        await asyncio.sleep(0.2)
    print(f"🔎 Deleted-account sweep done: checked {checked}, owner notified about {notified} (no data deleted).")
    return notified

DELETED_BACKUP_COLLECTION = "deleted_user_backups"   # durable backup of owner-confirmed deletions (survives Render redeploys)
DELETED_ARCHIVE_DIR = os.getenv("DELETED_ARCHIVE_DIR",
                                os.path.join(os.path.dirname(os.path.abspath(__file__)), "deleted_user_archives"))

def _archive_user_data(uid):
    """
    READ-ONLY. Collect exactly the data purge_user_data() would remove for this user and return
    (json_bytes, filename, counts, raw_data). Used only by the owner-confirmed Delete Data button, so a backup
    exists before anything is deleted. Nothing is written to the database here.
    """
    import json as _json
    spec = [(mongo_db.USERS, {"_id": uid}), (mongo_db.COLLECTIONS, {"user_id": uid}),
            (mongo_db.FAVORITES, {"_id": uid}), (mongo_db.NOTIFICATIONS, {"_id": uid}),
            ("shop_v3", {"user_id": uid}), ("shop_purchases_v2", {"user_id": uid}),
            ("shop_free_refresh_v1", {"_id": uid})]
    spec += [(name, {key: uid}) for name, key in badge_banner.USER_DATA_SPEC]      # badge claims + equipped banner
    spec += [(name, {key: uid}) for name, key in rewards.USER_DATA_SPEC]          # festival progress, claims, event-banner grants
    data = {name: list(_mc(name).find(flt)) for name, flt in spec}
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    doc = {"archived_at": stamp, "user_id": uid,
           "note": "Backup made right before an owner-confirmed deletion. Contains personal data: keep it private.",
           "data": data}
    try:
        from bson import json_util as _ju          # keeps ObjectId/dates exact, so the file can be restored
        payload = _ju.dumps(doc, ensure_ascii=False, indent=2).encode("utf-8")
    except Exception:
        payload = _json.dumps(doc, ensure_ascii=False, indent=2, default=str).encode("utf-8")
    return payload, f"deleted_user_{uid}_{stamp}.json", {k: len(v) for k, v in data.items()}, data

def _save_archive_locally(filename, payload):
    """Best-effort extra copy on the bot server (owner-only permissions). Returns the path or None."""
    try:
        os.makedirs(DELETED_ARCHIVE_DIR, exist_ok=True)
        path = os.path.join(DELETED_ARCHIVE_DIR, filename)
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, "wb") as f:
            f.write(payload)
        return path
    except Exception as e:
        print("Deleted-account local archive save error:", e)
        return None

async def deleted_account_review_callback(update, context):
    """Owner-only buttons for a possible-deleted-account notice. Data: delacct:<ask|keep|yes|no>:<user_id>:<token>"""
    q = update.callback_query
    if q is None or q.from_user is None:
        return
    if not is_owner(q.from_user.id):
        await deny_callback(q)
        return
    chat = q.message.chat if q.message else None
    if chat is None or chat.type != "private" or int(chat.id) != int(q.from_user.id):
        await _dacct_answer(q, "Use these buttons in your private chat with the bot.", True)
        return
    m = _DELETED_CB_RE.match(q.data or "")
    if not m:
        await _dacct_answer(q, "Invalid button.", True)
        return
    action, uid, token = m.group(1), int(m.group(2)), m.group(3)
    if _deleted_review_protected(uid):
        await _dacct_answer(q, "❌ An owner account can never be deleted here.", True)
        return
    users = _mc(mongo_db.USERS)
    review_filter = {"_id": uid, "deleted_review": "pending", "deleted_review_token": token}

    async def _edit(text, markup=None):
        try:
            await q.edit_message_text(text, reply_markup=markup)
        except Exception as e:
            print("Deleted-account review edit error:", e)

    try:
        row = await asyncio.to_thread(users.find_one, {"_id": uid}, {"deleted_review": 1, "deleted_review_token": 1, "deleted_review_confirm_at": 1,
                                                                 "deleted_review_reason": 1})
    except Exception as e:
        print(f"Deleted-account review lookup error for {uid}:", e)
        await _dacct_answer(q, "Database error. Nothing was changed or deleted.", True)
        return
    if row is None:
        await _dacct_answer(q, "No data found for that user (already removed?).", True)
        await _edit(f"ℹ️ No data found for user {uid}. Nothing to do.")
        return
    if row.get("deleted_review") != "pending" or row.get("deleted_review_token") != token:
        await _dacct_answer(q, "This request is no longer active.", True)
        await _edit(f"ℹ️ This request for user {uid} is no longer active. Nothing was deleted.\n"
                    f"You can still use /deleteuser {uid} manually.")
        return

    if action == "keep":
        try:
            res = await asyncio.to_thread(
                users.update_one, review_filter,
                {"$set": {"deleted_review": "kept", "deleted_review_at": time.time()},
                 "$unset": {"missing_strikes": "", "deleted_review_confirm_at": ""}})
        except Exception as e:
            print(f"Deleted-account keep save error for {uid}:", e)
            await _dacct_answer(q, "Database error: your decision was NOT saved. Nothing was deleted.", True)
            return
        if not res.matched_count:
            await _dacct_answer(q, "This request is no longer active.", True)
            return
        await _dacct_answer(q, "Data kept.")
        await _edit(f"❌ Kept. User {uid}'s data was NOT deleted.")
        return

    if action == "ask":
        try:                                           # the confirmation step is recorded server-side and expires
            res = await asyncio.to_thread(users.update_one, review_filter,
                                          {"$set": {"deleted_review_confirm_at": time.time()}})
        except Exception as e:
            print(f"Deleted-account confirm-step save error for {uid}:", e)
            await _dacct_answer(q, "Database error. Nothing was deleted.", True)
            return
        if not res.matched_count:
            await _dacct_answer(q, "This request is no longer active.", True)
            return
        await _dacct_answer(q)
        warn = ""
        if row.get("deleted_review_reason") != "deleted":
            warn = ("⚠️ UNCERTAIN RESULT: Telegram only said this user was \"not found\". The user may still be "
                    "ACTIVE (or may simply have never started / blocked the bot). Delete only if you are sure "
                    "the account is really gone.\n\n")
        await _edit(
            f"⚠️ CONFIRM DELETION\n\n{warn}This will permanently delete user {uid}: all characters, coins, profile, "
            "favorites and shop data. This cannot be undone.\n\nPress Confirm Delete only if you are sure.",
            InlineKeyboardMarkup([                     # safe option first, destructive option alone on its own row
                [InlineKeyboardButton("↩️ Cancel (keep data)", callback_data=f"delacct:no:{uid}:{token}")],
                [InlineKeyboardButton("✅ Confirm Delete — permanent", callback_data=f"delacct:yes:{uid}:{token}")],
            ]))
        return

    if action == "no":
        try:
            await asyncio.to_thread(users.update_one, review_filter, {"$unset": {"deleted_review_confirm_at": ""}})
        except Exception as e:                         # harmless: the confirmation expires on its own
            print(f"Deleted-account cancel save error for {uid}:", e)
        await _dacct_answer(q, "Cancelled. Nothing was deleted.")
        await _edit(f"⚠️ POSSIBLE DELETED ACCOUNT\n\n🆔 ID: {uid}\n\nNothing has been deleted. Choose what to do with this user's data:",
                    _deleted_review_keyboard(uid, token))
        return

    # action == "yes": explicit confirmation. Re-check authorization and target safety right before deleting.
    if not is_owner(q.from_user.id) or _deleted_review_protected(uid):
        await _dacct_answer(q, "❌ Not allowed.", True)
        return
    confirm_at = row.get("deleted_review_confirm_at")
    now = time.time()
    if not isinstance(confirm_at, (int, float)) or confirm_at > now + 60 or now - confirm_at > DELETED_CONFIRM_SECONDS:
        await _dacct_answer(q, "Confirmation missing or expired. Press Delete Data again.", True)
        await _edit(f"⚠️ POSSIBLE DELETED ACCOUNT\n\n🆔 ID: {uid}\n\nNothing has been deleted. Choose what to do with this user's data:",
                    _deleted_review_keyboard(uid, token))
        return
    state = await _telegram_account_deleted(context.bot, uid)
    if state is False:
        try:
            await asyncio.to_thread(users.update_one, review_filter, {"$unset": _DELETED_REVIEW_FIELDS})
        except Exception as e:
            print(f"Deleted-account review reset error for {uid}:", e)
        await _dacct_answer(q, "Telegram shows this account still exists.", True)
        await _edit(f"ℹ️ User {uid}'s Telegram account appears to exist, so nothing was deleted.\n"
                    f"If you still want to remove the data, use /deleteuser {uid}.")
        return
    try:                                               # atomic claim: only ONE tap can ever pass this point
        claimed = await asyncio.to_thread(
            users.update_one,
            dict(review_filter, deleted_review_confirm_at={"$gte": time.time() - DELETED_CONFIRM_SECONDS}),
            {"$set": {"deleted_review": "deleting", "deleted_review_at": time.time()},
             "$unset": {"deleted_review_confirm_at": ""}})
    except Exception as e:
        print(f"Deleted-account claim error for {uid}:", e)
        await _dacct_answer(q, "Database error. Nothing was deleted.", True)
        return
    if not claimed.matched_count:
        await _dacct_answer(q, "This request is no longer active.", True)
        return
    # Backup first. The durable backup is a document in the DELETED_BACKUP_COLLECTION collection (raw documents, so
    # the data can be restored later). If it cannot be written, NOTHING is deleted and the review goes back to
    # pending. A JSON file sent to the owner's chat and a copy on the server are extra, best-effort copies.
    backup_ok = False
    try:
        payload, fname, counts, raw = await asyncio.to_thread(_archive_user_data, uid)
        await asyncio.to_thread(
            lambda: _mc(DELETED_BACKUP_COLLECTION).insert_one(
                {"user_id": uid, "deleted_at": time.time(), "deleted_by": q.from_user.id,
                 "filename": fname, "counts": counts, "data": raw}))
        backup_ok = True
    except Exception as e:
        print(f"Deleted-account backup error for {uid}:", e)
    if not backup_ok:
        reverted = False
        try:
            back = await asyncio.to_thread(users.update_one, {"_id": uid, "deleted_review": "deleting"},
                                           {"$set": {"deleted_review": "pending"},
                                            "$unset": {"deleted_review_confirm_at": ""}})
            reverted = bool(back.matched_count)
        except Exception as e2:
            print(f"Deleted-account review revert error for {uid}:", e2)
        await _dacct_answer(q, "Backup failed. Nothing was deleted.", True)
        await _edit(f"❌ Could not save the backup for user {uid}, so NOTHING was deleted.",
                    _deleted_review_keyboard(uid, token) if reverted else None)
        return
    file_sent = False
    try:
        import io as _io
        bio = _io.BytesIO(payload)
        bio.name = fname
        await context.bot.send_document(chat_id=q.from_user.id, document=bio, filename=fname,
                                        caption=f"Backup of user {uid}, made before deletion. Keep this file private.")
        file_sent = True
    except Exception as e:
        print(f"Deleted-account backup file send error for {uid}:", e)
    local_path = await asyncio.to_thread(_save_archive_locally, fname, payload)
    try:
        copies, _removed = await asyncio.to_thread(purge_user_data, uid)
    except Exception as e:
        print(f"Deleted-account purge error for {uid}:", e)
        reverted = False
        try:
            back = await asyncio.to_thread(users.update_one, {"_id": uid, "deleted_review": "deleting"},
                                           {"$set": {"deleted_review": "pending"},
                                            "$unset": {"deleted_review_confirm_at": ""}})
            reverted = bool(back.matched_count)
        except Exception as e2:
            print(f"Deleted-account review revert error for {uid}:", e2)
        await _dacct_answer(q, "Deletion failed.", True)
        await _edit(f"❌ Deletion of user {uid} failed. Some of this user's data MAY ALREADY HAVE BEEN DELETED "
                    f"(this bot cannot tell, and nothing was restored). /deleteuser {uid} shows whether any "
                    f"data is still found for this ID.",
                    _deleted_review_keyboard(uid, token) if reverted else None)
        return
    await _dacct_answer(q, "Deleted.")
    await _edit(f"🗑 Deleted user {uid}.\n🧹 Removed {copies} character copy(ies).\n"
                f"📦 The data was removed from the main database and saved in the \"{DELETED_BACKUP_COLLECTION}\" backup collection.\n"
                + ("📁 A backup file was also sent to this chat." if file_sent else "⚠️ The backup file could not be sent to this chat (the database backup is safe).")
                + (" A copy was also saved on the bot server." if local_path else ""))
    print(f"🧹 Owner-confirmed deletion of {uid}: removed {copies} character copy(ies) and profile.")

async def _dacct_answer(q, text=None, alert=False):
    try:
        await q.answer(text, show_alert=alert)
    except Exception as e:
        print("Deleted-account review answer error:", e)

# ---- /restoreuser: owner-only restore of a user saved by the Delete Data button (see deleted_user_backups) ----
# Same collections (and the same ownership keys) that purge_user_data removes / _archive_user_data saves.
_RESTORE_SPEC = ((mongo_db.USERS, "_id"), (mongo_db.COLLECTIONS, "user_id"), (mongo_db.FAVORITES, "_id"),
                 (mongo_db.NOTIFICATIONS, "_id"), ("shop_v3", "user_id"), ("shop_purchases_v2", "user_id"),
                 ("shop_free_refresh_v1", "_id")) + badge_banner.USER_DATA_SPEC + rewards.USER_DATA_SPEC
# Review bookkeeping that must never come back with a restored profile (it would leave the user stuck in "deleting").
_RESTORE_STRIP_USER_FIELDS = ("deleted_review", "deleted_review_at", "deleted_review_reason",
                              "deleted_review_token", "deleted_review_confirm_at", "missing_strikes")

def _restore_plan(uid):
    """READ-ONLY. Returns (latest_backup_doc, None) or (None, reason_text)."""
    backups = list(_mc(DELETED_BACKUP_COLLECTION).find({"user_id": uid}))
    if not backups:
        return None, "❌ No backup found for that user ID."
    backup = max(backups, key=lambda b: float(b.get("deleted_at") or 0))
    prof = ((backup.get("data") or {}).get(mongo_db.USERS) or [{}])[0] if isinstance(backup.get("data"), dict) else {}
    moved_to = backup.get("moved_to") if backup.get("moved_to") is not None else prof.get("moved_to")
    if moved_to is not None:
        return None, (f"❌ This user's data was already transferred to account {moved_to}, so restoring it would "
                      f"create duplicates. Nothing was restored.")
    if _mc(mongo_db.USERS).find_one({"_id": uid}, {"_id": 1}) is not None \
            or _mc(mongo_db.COLLECTIONS).count_documents({"user_id": uid}) > 0:
        return None, (f"❌ User {uid} already has data in the main database, so restoring could overwrite or duplicate it. "
                      f"Nothing was restored. If you really want to replace it, remove that data first with /deleteuser {uid}.")
    return backup, None

def _restore_docs(backup, uid):
    """Validate a backup and return {collection: [documents]}. Raises ValueError if anything looks wrong."""
    data = backup.get("data")
    if not isinstance(data, dict):
        raise ValueError("the backup has no data section")
    out = {}
    for name, key in _RESTORE_SPEC:
        docs = data.get(name, [])
        if not isinstance(docs, list):
            raise ValueError(f"the {name} section is damaged")
        clean = []
        for d in docs:
            if not isinstance(d, dict) or d.get(key) != uid or "_id" not in d:
                raise ValueError(f"a record in {name} does not belong to user {uid}")
            d = dict(d)
            if name == mongo_db.USERS:
                for f in _RESTORE_STRIP_USER_FIELDS:
                    d.pop(f, None)
            clean.append(d)
        out[name] = clean
    if not out[mongo_db.USERS]:
        raise ValueError("the backup has no profile record")
    return out

def _restore_user_data(uid, docs_by_collection):
    """
    Put a validated backup back, all-or-nothing. With transactions the database rolls everything back on failure.
    Without them, only the records THIS attempt inserted are removed again (each id is remembered after its own
    successful insert, so a record that someone else created in the meantime is never touched).
    """
    def _work(session):
        inserted = []
        try:
            for name, docs in docs_by_collection.items():
                for d in docs:
                    _mc(name).insert_one(d, session=session)      # duplicate _id -> error, nothing is overwritten
                    inserted.append((name, d["_id"]))
        except Exception:
            if session is None:
                for name, _id in inserted:
                    _mc(name).delete_one({"_id": _id})
            raise
        return {name: len(docs) for name, docs in docs_by_collection.items()}
    return mongo_db.run_transaction(_work)

_DATA_CONFIRM_SECONDS = 600
_DATA_CONFIRM_RE = re.compile(r"^dconf:(go|no):([0-9a-f]{10})$")

def _data_confirm_keyboard(token, label):
    """Safe option first; the confirm button sits alone on its own row."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("↩️ Cancel", callback_data=f"dconf:no:{token}")],
        [InlineKeyboardButton(label, callback_data=f"dconf:go:{token}")],
    ])

def _data_pending(context):
    """In-memory, single-use confirmations (lost on restart = buttons simply expire, which is the safe side)."""
    store = context.application.bot_data.setdefault("pending_data_confirms", {})
    now = time.monotonic()
    for t in [t for t, r in store.items() if r["exp"] < now]:
        store.pop(t, None)
    while len(store) > 50:
        store.pop(next(iter(store)))
    return store

async def _run_restore(uid, expected_backup_id):
    """Re-validate everything and restore. Returns (ok, text). Used only by the owner's confirm button."""
    if _deleted_review_protected(uid):
        return False, "❌ That ID cannot be restored with this command."
    try:
        backup, problem = await asyncio.to_thread(_restore_plan, uid)
        docs = _restore_docs(backup, uid) if backup else None
    except ValueError as e:
        return False, f"❌ The backup cannot be used ({e}). Nothing was restored."
    except Exception as e:
        print("restore lookup error:", e)
        return False, "❌ Database error. Nothing was restored."
    if problem:
        return False, problem
    if backup["_id"] != expected_backup_id:
        return False, "❌ The backup changed since the preview. Nothing was restored. Run /restoreuser again."
    try:
        counts = await asyncio.to_thread(_restore_user_data, uid, docs)
    except Exception as e:
        print(f"restore error for {uid}:", e)
        return False, (f"❌ Restore failed. The bot only removes the records it had just added, and the backup itself is "
                       f"unchanged. Check with /deleteuser {uid} whether any data is present, then try again.")
    try:                                               # record keeping only; the backup is never deleted
        await asyncio.to_thread(_mc(DELETED_BACKUP_COLLECTION).update_one, {"_id": backup["_id"]},
                                {"$set": {"restored_at": time.time()}})
    except Exception as e:
        print(f"restore backup-mark error for {uid}:", e)
    return True, (f"✅ Restored user {uid}: {counts.get(mongo_db.COLLECTIONS, 0)} character copy(ies) and their profile. "
                  f"The backup was kept.")

def _live_data_problem(uid):
    """Text if this user already has data in the main database (restoring could overwrite/duplicate it), else None."""
    if _mc(mongo_db.USERS).find_one({"_id": uid}, {"_id": 1}) is not None \
            or _mc(mongo_db.COLLECTIONS).count_documents({"user_id": uid}) > 0:
        return (f"❌ User {uid} already has data in the main database, so restoring could overwrite or duplicate it. "
                f"Nothing was restored.")
    return None

def _restore_from_file_plan(raw):
    """READ-ONLY. Parse a backup file the bot sent to the owner. Returns (uid, docs, None) or (None, None, problem)."""
    try:
        from bson import json_util as _ju
        doc = _ju.loads(raw.decode("utf-8"))
    except Exception:
        return None, None, "❌ That file is not a valid backup file. Nothing was restored."
    if not isinstance(doc, dict) or not isinstance(doc.get("data"), dict):
        return None, None, "❌ That file is not a backup file made by this bot. Nothing was restored."
    uid = doc.get("user_id")
    if not isinstance(uid, int) or isinstance(uid, bool):
        return None, None, "❌ The backup file has no valid user ID. Nothing was restored."
    if _deleted_review_protected(uid):
        return None, None, "❌ That ID cannot be restored with this command."
    try:
        docs = _restore_docs({"data": doc["data"]}, uid)
    except ValueError as e:
        return None, None, f"❌ The backup file cannot be used ({e}). Nothing was restored."
    problem = _live_data_problem(uid)
    if problem:
        return None, None, problem
    return uid, docs, None

async def _run_restore_file(uid, docs):
    """Re-check and restore from a file-based backup. Returns (ok, text). Used only by the owner's confirm button."""
    if _deleted_review_protected(uid):
        return False, "❌ That ID cannot be restored with this command."
    try:
        problem = await asyncio.to_thread(_live_data_problem, uid)
    except Exception as e:
        print("restore-file lookup error:", e)
        return False, "❌ Database error. Nothing was restored."
    if problem:
        return False, problem
    try:
        counts = await asyncio.to_thread(_restore_user_data, uid, docs)
    except Exception as e:
        print(f"restore-file error for {uid}:", e)
        return False, (f"❌ Restore failed. The bot only removes the records it had just added. "
                       f"Check with /deleteuser {uid} whether any data is present, then try again.")
    return True, (f"✅ Restored user {uid}: {counts.get(mongo_db.COLLECTIONS, 0)} character copy(ies) and their profile "
                  f"from the backup file.")

async def _restore_from_file(update, context, document):
    if (document.file_size or 0) > 15 * 1024 * 1024:
        await safe_reply_text(update.message, "❌ That file is too large to be a backup file. Nothing was restored.")
        return
    try:
        tg_file = await document.get_file()
        raw = bytes(await tg_file.download_as_bytearray())
    except Exception as e:
        print("restore-file download error:", e)
        await safe_reply_text(update.message, "❌ I could not download that file. Nothing was restored.")
        return
    uid, docs, problem = await asyncio.to_thread(_restore_from_file_plan, raw)
    if problem:
        await safe_reply_text(update.message, problem)
        return
    chars = len(docs.get(mongo_db.COLLECTIONS, []))
    token = uuid.uuid4().hex[:10]
    _data_pending(context)[token] = {"kind": "restore_file", "owner": update.effective_user.id, "uid": uid,
                                     "docs": docs, "exp": time.monotonic() + _DATA_CONFIRM_SECONDS}
    await safe_reply_text(update.message,
        f"♻️ Backup file for user {uid}: {chars} character copy(ies) and their profile.\n\n"
        f"Press Confirm Restore to restore it (valid for 10 minutes). Nothing has been changed yet.",
        reply_markup=_data_confirm_keyboard(token, "✅ Confirm Restore"))

async def restoreuser(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    chat = update.effective_chat
    if chat is None or chat.type != "private":
        await safe_reply_text(update.message, "❌ Use /restoreuser in your private chat with the bot.")
        return
    args = context.args or []
    reply = update.message.reply_to_message if update.message else None
    if not args and reply is not None and reply.document is not None:
        await _restore_from_file(update, context, reply.document)
        return
    if not args or not re.fullmatch(r"[0-9]+", args[0]):
        await safe_reply_text(update.message,
            "Usage: /restoreuser <user_id>\nOr reply to a backup file the bot sent you with /restoreuser")
        return
    uid = int(args[0])
    if _deleted_review_protected(uid):
        await safe_reply_text(update.message, "❌ That ID cannot be restored with this command.")
        return
    try:
        backup, problem = await asyncio.to_thread(_restore_plan, uid)
        docs = _restore_docs(backup, uid) if backup else None
    except ValueError as e:
        await safe_reply_text(update.message, f"❌ The backup cannot be used ({e}). Nothing was restored.")
        return
    except Exception as e:
        print("restoreuser lookup error:", e)
        await safe_reply_text(update.message, "❌ Database error. Nothing was restored.")
        return
    if problem:
        await safe_reply_text(update.message, problem)
        return
    when = datetime.fromtimestamp(float(backup.get("deleted_at") or 0)).strftime("%Y-%m-%d %H:%M")
    chars = len(docs.get(mongo_db.COLLECTIONS, []))
    token = uuid.uuid4().hex[:10]
    _data_pending(context)[token] = {"kind": "restore", "owner": update.effective_user.id, "uid": uid,
                                     "ref": backup["_id"], "exp": time.monotonic() + _DATA_CONFIRM_SECONDS}
    await safe_reply_text(update.message,
        f"♻️ Backup found for user {uid} (deleted {when}): {chars} character copy(ies).\n\n"
        f"Press Confirm Restore to restore it (valid for 10 minutes). Nothing has been changed yet.",
        reply_markup=_data_confirm_keyboard(token, "✅ Confirm Restore"))

# ---- /moveuser: copy an old (deleted) account's game data onto the same person's NEW Telegram account ----
_MOVE_KEEP_NEW_PROFILE = ("_id", "username", "first_name", "last_name")   # identity always stays the new account's

def _move_plan(old, new):
    """
    READ-ONLY. Returns (plan, None) or (None, reason). The source is the old user's live data if it is still in
    the main database, otherwise the latest backup in DELETED_BACKUP_COLLECTION.
    """
    users = _mc(mongo_db.USERS)
    new_doc = users.find_one({"_id": new})
    if new_doc is None:
        return None, (f"❌ Account {new} is not in the bot's database yet. Ask the person to open the bot and press "
                      f"/start with the new account first.")
    if _mc(mongo_db.COLLECTIONS).count_documents({"user_id": new}) > 0:
        return None, (f"❌ Account {new} already owns characters. To avoid mixing data, nothing was moved.")
    old_doc = users.find_one({"_id": old})
    if old_doc is not None:
        if old_doc.get("moved_to") is not None:
            return None, f"❌ User {old}'s data was already transferred to account {old_doc.get('moved_to')}."
        _p, _f, _c, raw = _archive_user_data(old)
        kind, src_col, src_filter, when = "live data", mongo_db.USERS, {"_id": old}, None
        data = _restore_docs({"data": raw}, old)
    else:
        backups = list(_mc(DELETED_BACKUP_COLLECTION).find({"user_id": old}))
        if not backups:
            return None, f"❌ No data or backup found for user {old}."
        backup = max(backups, key=lambda b: float(b.get("deleted_at") or 0))
        prof = ((backup.get("data") or {}).get(mongo_db.USERS) or [{}])[0] if isinstance(backup.get("data"), dict) else {}
        moved_to = backup.get("moved_to") if backup.get("moved_to") is not None else prof.get("moved_to")
        if moved_to is not None:
            return None, f"❌ User {old}'s data was already transferred to account {moved_to}."
        kind, src_col, src_filter, when = "backup", DELETED_BACKUP_COLLECTION, {"_id": backup["_id"]}, backup.get("deleted_at")
        data = _restore_docs(backup, old)
    return {"kind": kind, "src_col": src_col, "src_filter": src_filter, "when": when, "data": data,
            "old_profile": data[mongo_db.USERS][0], "new_profile": new_doc}, None

def _move_user_data(plan, old, new):
    """
    Copy-only, all-or-nothing transfer. The source data is never deleted or changed except for a marker
    (moved_to) that blocks a second transfer. With transactions the database rolls everything back on failure;
    without them, only what THIS attempt created is removed again and the marker is cleared.
    """
    data = plan["data"]
    carry = {k: v for k, v in plan["old_profile"].items() if k not in _MOVE_KEEP_NEW_PROFILE}
    carry["transferred_from"] = old
    carry["transferred_at"] = time.time()

    def _work(session):
        src = _mc(plan["src_col"])
        claimed = src.update_one(dict(plan["src_filter"], moved_to={"$exists": False}),
                                 {"$set": {"moved_to": new, "moved_at": time.time()}}, session=session)
        if not claimed.matched_count:
            raise ValueError("already transferred or source changed")
        inserted = []
        try:
            for d in data[mongo_db.COLLECTIONS]:
                nd = {k: v for k, v in d.items() if k != "_id"}
                nd["user_id"] = new
                res = _mc(mongo_db.COLLECTIONS).insert_one(nd, session=session)
                inserted.append((mongo_db.COLLECTIONS, res.inserted_id))
            for name in (mongo_db.FAVORITES, mongo_db.NOTIFICATIONS):
                for d in data[name]:
                    if _mc(name).find_one({"_id": new}, {"_id": 1}, session=session) is None:   # never overwrite
                        nd = {k: v for k, v in d.items() if k != "_id"}
                        nd["_id"] = new
                        _mc(name).insert_one(nd, session=session)
                        inserted.append((name, new))
            badge_banner.move_user_data(data, new, session, inserted)      # badge claims + equipped banner (never overwrites)
            rewards.move_user_data(data, new, session, inserted)          # festival progress, claims, event-banner grants
            res = _mc(mongo_db.USERS).update_one({"_id": new}, {"$set": carry}, session=session)
            if not res.matched_count:
                raise ValueError("the new account disappeared")
        except Exception:
            if session is None:
                for name, _id in inserted:
                    _mc(name).delete_one({"_id": _id})
                src.update_one(plan["src_filter"], {"$unset": {"moved_to": "", "moved_at": ""}})
            raise
        return {"characters": len(data[mongo_db.COLLECTIONS])}
    return mongo_db.run_transaction(_work)

def _who(doc):
    name = " ".join(v for v in [doc.get("first_name"), doc.get("last_name")] if v).strip() or "no name"
    return f"{name} ({'@' + doc['username'] if doc.get('username') else 'no username'})"

async def _run_move(old, new, expected):
    """Re-validate everything and transfer. Returns (ok, text). Used only by the owner's confirm button."""
    if old == new or _deleted_review_protected(old) or _deleted_review_protected(new):
        return False, "❌ These IDs cannot be used with this command."
    try:
        plan, problem = await asyncio.to_thread(_move_plan, old, new)
    except ValueError as e:
        return False, f"❌ The source data cannot be used ({e}). Nothing was moved."
    except Exception as e:
        print("move lookup error:", e)
        return False, "❌ Database error. Nothing was moved."
    if problem:
        return False, problem
    if plan["kind"] != expected["kind"] or plan["src_filter"] != expected["src_filter"]:
        return False, "❌ The source data changed since the preview. Nothing was moved. Run /moveuser again."
    try:
        result = await asyncio.to_thread(_move_user_data, plan, old, new)
    except Exception as e:
        print(f"move error {old}->{new}:", e)
        return False, ("❌ Transfer failed. The bot only removes what it had just copied and the original data is "
                       "untouched. Nothing was lost; check the new account and try again.")
    tail = (f"The old account's data is still in the main database: once you have checked the new account, remove the "
            f"old data with /deleteuser {old}." if plan["kind"] == "live data" else "The backup was kept.")
    return True, f"✅ Transferred {result['characters']} character copy(ies) and the profile from {old} to {new}.\n{tail}"

async def moveuser(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    chat = update.effective_chat
    if chat is None or chat.type != "private":
        await safe_reply_text(update.message, "❌ Use /moveuser in your private chat with the bot.")
        return
    args = context.args or []
    if len(args) < 2 or not all(re.fullmatch(r"[0-9]+", a) for a in args[:2]):
        await safe_reply_text(update.message, "Usage: /moveuser <old_user_id> <new_user_id>")
        return
    old, new = int(args[0]), int(args[1])
    if old == new or _deleted_review_protected(old) or _deleted_review_protected(new):
        await safe_reply_text(update.message, "❌ These IDs cannot be used with this command.")
        return
    try:
        plan, problem = await asyncio.to_thread(_move_plan, old, new)
    except ValueError as e:
        await safe_reply_text(update.message, f"❌ The source data cannot be used ({e}). Nothing was moved.")
        return
    except Exception as e:
        print("moveuser lookup error:", e)
        await safe_reply_text(update.message, "❌ Database error. Nothing was moved.")
        return
    if problem:
        await safe_reply_text(update.message, problem)
        return
    d = plan["data"]
    chars = len(d[mongo_db.COLLECTIONS])
    src = plan["kind"] if plan["when"] is None else \
        f"backup from {datetime.fromtimestamp(float(plan['when'] or 0)).strftime('%Y-%m-%d %H:%M')}"
    summary = (f"OLD {old}: {_who(plan['old_profile'])}\nNEW {new}: {_who(plan['new_profile'])}\n"
               f"Source: {src}\nWill be copied: {chars} character copy(ies), "
               f"coins {plan['new_profile'].get('coins', 0)} → {plan['old_profile'].get('coins', 0)} (replaced), "
               f"favorite and notification settings (only if the new account has none).\n"
               f"Not moved: shop and purchase history, restrictions, event/redeem claims.")
    token = uuid.uuid4().hex[:10]
    _data_pending(context)[token] = {"kind": "move", "owner": update.effective_user.id, "old": old, "new": new,
                                     "ref": {"kind": plan["kind"], "src_filter": plan["src_filter"]},
                                     "exp": time.monotonic() + _DATA_CONFIRM_SECONDS}
    await safe_reply_text(update.message,
        f"🔁 Transfer preview\n\n{summary}\n\nCheck that both accounts are the same person, then press Confirm Transfer "
        f"(valid for 10 minutes). Nothing has been changed yet.",
        reply_markup=_data_confirm_keyboard(token, "✅ Confirm Transfer"))

async def data_confirm_callback(update, context):
    """Owner-only buttons of /restoreuser and /moveuser. Data: dconf:<go|no>:<token>. Each token works once."""
    q = update.callback_query
    if q is None or q.from_user is None:
        return
    if not is_owner(q.from_user.id):
        await deny_callback(q)
        return
    chat = q.message.chat if q.message else None
    if chat is None or chat.type != "private" or int(chat.id) != int(q.from_user.id):
        await _dacct_answer(q, "Use these buttons in your private chat with the bot.", True)
        return
    m = _DATA_CONFIRM_RE.match(q.data or "")
    if not m:
        await _dacct_answer(q, "Invalid button.", True)
        return
    action, token = m.group(1), m.group(2)

    async def _edit(text):
        try:
            await q.edit_message_text(text)
        except Exception as e:
            print("Data confirm edit error:", e)

    rec = _data_pending(context).pop(token, None)      # single use: a second tap or an old button finds nothing
    if rec is None or rec.get("owner") != q.from_user.id:
        await _dacct_answer(q, "This confirmation has expired. Run the command again.", True)
        await _edit("ℹ️ This confirmation has expired or was already used. Nothing was changed. "
                    "Run the command again if you still want it.")
        return
    if action == "no":
        await _dacct_answer(q, "Cancelled.")
        await _edit("↩️ Cancelled. Nothing was deleted." if rec["kind"] == "delete"
                    else "↩️ Cancelled. Nothing was changed.")
        return
    await _dacct_answer(q, "Working…")
    try:
        if rec["kind"] == "delete":
            _ok, text = await _run_delete(context, rec["uid"], q.from_user)
        elif rec["kind"] == "restore":
            _ok, text = await _run_restore(rec["uid"], rec["ref"])
        elif rec["kind"] == "restore_file":
            _ok, text = await _run_restore_file(rec["uid"], rec["docs"])
        else:
            _ok, text = await _run_move(rec["old"], rec["new"], rec["ref"])
    except Exception as e:                              # never leave the owner without an answer
        print("Data confirm error:", e)
        text = "❌ Something went wrong. Please check the data before trying again."
    await _edit(text)

async def deleted_account_sweep_loop(app):
    await asyncio.sleep(300)                           # let the bot finish starting first
    while True:
        try:
            await sweep_deleted_accounts(app)
            await asyncio.sleep(max(1.0, DELETED_SWEEP_HOURS) * 3600)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            print("Deleted-account sweep error; recovering:", e)
            await asyncio.sleep(600)

def _find_users(query, limit=100):
    """READ-ONLY. Users whose saved first name, last name or @username match every word of `query`."""
    q = (query or "").strip().lstrip("@").strip()
    if not q:
        return [], 0
    users = _mc(mongo_db.USERS)
    fields = ("first_name", "last_name", "username")
    ands = []
    for word in q.split():
        pat = {"$regex": re.escape(word), "$options": "i"}
        ands.append({"$or": [{f: pat} for f in fields]})
    flt = {"$and": ands}
    if q.isdigit():
        flt = {"$or": [flt, {"_id": int(q)}]}
    total = users.count_documents(flt)
    rows = list(users.find(flt, {"_id": 1, "first_name": 1, "last_name": 1, "username": 1}).limit(limit))
    out = []
    for r in rows:
        uid = r["_id"]
        owned = _mc(mongo_db.COLLECTIONS).count_documents({"user_id": uid})
        name = " ".join(v for v in [r.get("first_name"), r.get("last_name")] if v).strip() or "Unknown"
        out.append((uid, name, r.get("username") or "", owned))
    out.sort(key=lambda x: (x[1].lower(), x[0]))
    return out, total

async def finduser(update, context):
    """Owner only: find a user's ID from part of a saved name or @username."""
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    query = " ".join(context.args or []).strip()
    if not query:
        await safe_reply_text(update.message, "Usage: /finduser <name or @username>")
        return
    try:
        rows, total = await asyncio.to_thread(_find_users, query)
    except Exception as e:
        print("finduser error:", e)
        await safe_reply_text(update.message, "❌ Database error. Nothing was changed.")
        return
    shown_query = html_escape(query)
    if not rows:
        await safe_reply_text(update.message, f"❌ No user found for \"{shown_query}\".", parse_mode="HTML")
        return
    entries = []
    for i, (uid, name, username, owned) in enumerate(rows, 1):
        handle = f"@{html_escape(username)}" if username else "No username"
        entries.append(f"{i}. {html_escape(name)} ({handle})\n   🆔 ID: <code>{uid}</code>\n   🎴 Characters: {owned}")
    head = f'🔎 Matches for "{shown_query}" ({total}):'
    if total > len(rows):
        head = f'🔎 Showing {len(rows)} of {total} matches for "{shown_query}".\nType a longer name to narrow it down.'
    chunks = [entries[i:i + 15] for i in range(0, len(entries), 15)]
    for n, chunk in enumerate(chunks):
        text = (head + "\n\n" if n == 0 else "") + "\n\n".join(chunk)
        await safe_reply_text(update.message, text, parse_mode="HTML")

async def deleteuser(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    args = context.args or []
    if not args or not args[0].lstrip("-").isdigit():
        await safe_reply_text(update.message,
            "Usage: /deleteuser <user_id>")
        return
    uid = int(args[0])
    if is_owner(uid):
        await safe_reply_text(update.message, "❌ You can't delete an owner account.")
        return
    names = (await asyncio.to_thread(mongo_db.get_user_names, uid))
    owned = (await asyncio.to_thread(
        lambda: _mc(mongo_db.COLLECTIONS).count_documents({"user_id": uid})))
    if not names and not owned:
        await safe_reply_text(update.message, "❌ No data found for that user ID.")
        return
    first, last, username = names if names else ("Unknown", "", "")
    display = " ".join(v for v in [first, last] if v).strip() or "Unknown"
    chat = update.effective_chat
    if chat is None or chat.type != "private":
        await safe_reply_text(update.message, "Use /deleteuser in your private chat with the bot.")
        return
    token = uuid.uuid4().hex[:10]
    _data_pending(context)[token] = {"kind": "delete", "owner": update.effective_user.id, "uid": uid,
                                     "exp": time.monotonic() + _DATA_CONFIRM_SECONDS}
    await safe_reply_text(update.message,
        f"⚠️ This will permanently delete {display} [{uid}]: {owned} character(s), coins and profile.\n"
        f"📁 A backup file of all their data will be sent to your PM first (it is not stored on the bot).\n\n"
        f"Press Delete Data to delete it (valid for 10 minutes). Nothing has been deleted yet.",
        reply_markup=_data_confirm_keyboard(token, "🗑 Delete Data"))

async def _run_delete(context, uid, actor):
    """Owner's Delete Data button: re-check, send the backup file to the owner's PM, then delete. Returns (ok, text)."""
    if is_owner(uid):
        return False, "❌ You can't delete an owner account. Nothing was deleted."
    names = await asyncio.to_thread(mongo_db.get_user_names, uid)
    owned = await asyncio.to_thread(lambda: _mc(mongo_db.COLLECTIONS).count_documents({"user_id": uid}))
    if not names and not owned:
        return False, "❌ No data found for that user ID. Nothing was deleted."
    first, last, username = names if names else ("Unknown", "", "")
    display = " ".join(v for v in [first, last] if v).strip() or "Unknown"
    # Collect all of the user's data and send it to the owner's PM BEFORE deleting. Nothing is stored anywhere else.
    try:
        import io as _io
        payload, fname, _counts, _raw = await asyncio.to_thread(_archive_user_data, uid)
        bio = _io.BytesIO(payload)
        bio.name = fname
        await context.bot.send_document(chat_id=actor.id, document=bio, filename=fname,
                                        caption=f"Data of user {uid}, sent before deletion. Keep this file private.")
    except Exception as e:
        print("deleteuser backup-file error:", e)
        return False, ("❌ I could not send the backup file to your PM (open a private chat with me and press Start). "
                       "Nothing was deleted.")
    try:
        copies, removed = (await asyncio.to_thread(purge_user_data, uid))
    except Exception as e:
        print("deleteuser error:", e)
        return False, "❌ Could not delete that user. Nothing was deleted."
    await notify_staff_action(
        context,
        f"🗑 USER DELETED\n👤 {display} [{uid}]\n🧹 {copies} character copy(ies)\n👤 By: {display_user(actor)}",
        actor_id=actor.id,
    )
    return True, f"🗑 Deleted {display} [{uid}].\n🧹 Removed {copies} character copy(ies).\n📁 The backup file was sent to your PM."

DEFAULT_GSTATS_GROUP_ID = -1003379716050
DEFAULT_GSTATS_GROUP_TITLE = "Wonderland Anime gc"


def build_group_open_link(chat_id, username=None, invite_link=None):
    """
    A URL that really opens the group (tg://openmessage?chat_id=... does NOT work for groups).
      1. public group  -> https://t.me/<username>
      2. the group's own invite link, when the bot is an admin and Telegram returns it (works for non-members)
      3. supergroup    -> https://t.me/c/<id without -100>/1 (opens for members of the group)
      4. basic group without any link -> None (Telegram offers no way to link to it)
    """
    username = (username or "").lstrip("@").strip()
    if username:
        return f"https://t.me/{username}"
    if invite_link and str(invite_link).startswith(("https://t.me/", "http://t.me/", "https://telegram.me/")):
        return str(invite_link)
    cid = str(int(chat_id))
    if cid.startswith("-100") and len(cid) > 4:
        return f"https://t.me/c/{cid[4:]}/1"
    return None

async def _safe_edit_text(message, text, **kwargs):
    """edit_text that survives 'message is not modified' and texts over the 4096 limit (sends chunks instead)."""
    try:
        if len(text) > 4000:
            await safe_reply_text(message, text, **{k: v for k, v in kwargs.items() if k != "reply_markup"})
            return
        await message.edit_text(text, **kwargs)
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            raise


GSTATS_PAGE_SIZE = 10
GSTATS_CACHE_TTL = 45        # seconds: page / manage taps reuse the last Telegram refresh instead of re-checking every group


async def _gstats_collect(context, force=False):
    """Refresh the group registry from Telegram (hidden groups are skipped).
    Returns (groups, invite_links), or None when Telegram cannot be reached."""
    bd = context.application.bot_data
    cache = bd.get("gstats_cache")
    if not force and cache and time.monotonic() - cache["ts"] < GSTATS_CACHE_TTL:
        return cache["groups"], cache["links"]

    hidden_ids = (await asyncio.to_thread(load_gstats_hidden_groups))
    groups = (await asyncio.to_thread(load_bot_groups))
    known_ids = set(groups.keys())
    _approved_now = (await asyncio.to_thread(load_approved_groups))
    _auto_now = (await asyncio.to_thread(load_auto_spawn_groups))
    _states_now = (await asyncio.to_thread(load_bot_group_states))
    known_ids.update(str(int(x)) for x in _approved_now)
    known_ids.update(str(int(x)) for x in _auto_now)
    known_ids.update(str(k) for k in _states_now.keys() if str(k).lstrip("-").isdigit())

    known_ids.add(str(DEFAULT_GSTATS_GROUP_ID))

    known_ids = {group_id for group_id in known_ids if int(group_id) not in hidden_ids}

    try:
        me = await context.bot.get_me()
        bot_user_id = int(me.id)
    except Exception as e:
        print("/gstats get_me error:", e)
        return None

    refreshed = {}
    invite_links = {}                      # raw_id -> invite link returned by Telegram (not persisted)
    gate = asyncio.Semaphore(8)            # check several groups at the same time (one after another was slow)

    async def _check(raw_id):
        """-> (raw_id, group info or None, invite link or None)"""
        chat_id = int(raw_id)
        info = groups.get(raw_id, {})
        async with gate:
            try:
                member = await context.bot.get_chat_member(chat_id, bot_user_id)
                member_status = getattr(member, "status", "")
                member_is_present = getattr(member, "is_member", True)
                if member_status not in ("creator", "administrator", "member", "restricted") or (
                    member_status == "restricted" and not member_is_present
                ):
                    await cleanup_left_group(chat_id, context)
                    return raw_id, None, None

                chat = await context.bot.get_chat(chat_id)
                entry = {
                    "title": (
                        DEFAULT_GSTATS_GROUP_TITLE
                        if chat_id == DEFAULT_GSTATS_GROUP_ID
                        else getattr(chat, "title", None) or getattr(chat, "username", None) or info.get("title") or "Unknown"
                    ),
                    "type": getattr(chat, "type", info.get("type", "group")),
                    "username": getattr(chat, "username", info.get("username")),
                }
                return raw_id, entry, getattr(chat, "invite_link", None)
            except ChatMigrated as e:                         # the group became a supergroup: move its settings to the new id
                if getattr(e, "new_chat_id", None):
                    await migrate_group_data(context.application, chat_id, e.new_chat_id)
                return raw_id, None, None
            except (Forbidden, BadRequest) as e:
                reason = str(e).lower()
                if isinstance(e, Forbidden) or any(w in reason for w in (
                        "chat not found", "kicked", "not a member", "bot was kicked", "bot is not a member", "group chat was deleted")):
                    print(f"/gstats: bot is no longer in {chat_id} ({e}); removing it")
                    await cleanup_left_group(chat_id, context)
                    return raw_id, None, None
                print(f"/gstats refresh error for {chat_id} (kept):", e)   # unknown API refusal: keep the group, do not wipe it
                return raw_id, (dict(info) if info else None), None
            except Exception as e:                        # network / flood control / timeout: NEVER clean up
                print(f"/gstats membership refresh error for {chat_id} (kept):", e)
                return raw_id, (dict(info) if info else None), None

    for raw_id, entry, link in await asyncio.gather(*[_check(r) for r in sorted(known_ids, key=lambda v: int(v))]):
        if entry:
            refreshed[raw_id] = entry
        if link:
            invite_links[raw_id] = link

    # Hidden groups are not refreshed, but they must keep their registration and name (the registry is replaced as a whole).
    to_save = dict(refreshed)
    for cid in hidden_ids:
        key = str(int(cid))
        if key in groups and key not in to_save:
            to_save[key] = groups[key]
    (await asyncio.to_thread(save_bot_groups, to_save))
    bd["gstats_cache"] = {"ts": time.monotonic(), "groups": refreshed, "links": invite_links}
    return refreshed, invite_links


async def _gstats_deliver(update, text, markup=None, preview=False):
    """Edit the GStats message (button taps) or send it (the /gstats command)."""
    if update.callback_query:
        requester = update.callback_query.from_user
        first = (getattr(requester, "first_name", None) or "").strip()
        last = (getattr(requester, "last_name", None) or "").strip()
        display_name = " ".join(part for part in (first, last) if part) or "Unknown"
        await _safe_edit_text(update.callback_query.message, f"👤 {html_escape(display_name)}\n\n{text}",
                              parse_mode="HTML", reply_markup=markup, disable_web_page_preview=not preview)
    else:
        await safe_reply_text(update.effective_message, text, parse_mode="HTML",
                              disable_web_page_preview=not preview, reply_markup=markup)


def _gstats_name_rows(buttons):
    """Group-name buttons, two per row."""
    return [buttons[k:k + 2] for k in range(0, len(buttons), 2)]


def _gstats_nav_row(page, pages, prefix):
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("‹ Prev", callback_data=f"{prefix}:{page - 1}"))
    if page < pages - 1:
        nav.append(InlineKeyboardButton("Next ›", callback_data=f"{prefix}:{page + 1}"))
    return nav


async def gstats(update, context, page=0, force=True):
    """/gstats: text list of every group the bot is in + one name button per group (tap = manage that group)."""
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return

    got = await _gstats_collect(context, force)
    if got is None:
        await safe_reply_text(update.effective_message, "⚠️ Could not refresh group membership right now. Please try again.")
        return
    groups, invite_links = got
    hidden_count = len(await asyncio.to_thread(load_gstats_hidden_groups))
    total_line = f"Total Groups: {len(groups)}" + (f" ({hidden_count} hidden)" if hidden_count else "")
    hidden_row = [[InlineKeyboardButton(f"👁 Hidden ({hidden_count})", callback_data="gstats:h:0")]] if hidden_count else []

    if not groups:
        await _gstats_deliver(update, f"📊 Group Statistics\n\n{total_line}",
                              InlineKeyboardMarkup(hidden_row) if hidden_row else None)
        return

    sorted_groups = sorted(
        groups.items(),
        key=lambda item: (
            0 if int(item[0]) == DEFAULT_GSTATS_GROUP_ID else 1,
            (item[1].get("title") or "").casefold(),
        ),
    )
    pages = max(1, -(-len(sorted_groups) // GSTATS_PAGE_SIZE))
    page = max(0, min(int(page), pages - 1))
    offset = page * GSTATS_PAGE_SIZE

    lines = ["📊 Group Statistics", "", total_line, ""]
    buttons = []
    states = await asyncio.to_thread(load_bot_group_states)          # one read for the whole page
    for i, (chat_id, info) in enumerate(sorted_groups[offset:offset + GSTATS_PAGE_SIZE], offset + 1):
        title = info.get("title") or "Unknown"
        status = "🟢 ON" if states.get(str(int(chat_id)), True) else "🔴 OFF"
        approved = "✅ Approved" if await is_group_approved(int(chat_id)) else "❌ Not Approved"
        lines.append(f"{i}. 🏠 {html_escape(title)}")
        lines.append(f"🆔 Group ID: <code>{chat_id}</code>")      # tap to copy
        lines.append(f"🤖 Bot: {status}")
        lines.append(f"🔐 Approval: {approved}")
        lines.append("")
        buttons.append(InlineKeyboardButton(f"{i}. {title[:22]}", callback_data=f"gstats:g:{chat_id}:{page}"))

    if pages > 1:
        lines.append(f"Page {page + 1}/{pages}")
        lines.append("")
    default_info = groups.get(str(DEFAULT_GSTATS_GROUP_ID))
    if default_info:
        default_link = build_group_open_link(
            DEFAULT_GSTATS_GROUP_ID, default_info.get("username"), invite_links.get(str(DEFAULT_GSTATS_GROUP_ID)))
        if default_link:
            lines.append(f'<a href="{html_escape(default_link)}">Telegram Wonderland</a>')

    rows = _gstats_name_rows(buttons)
    nav = _gstats_nav_row(page, pages, "gstats:p")
    if nav:
        rows.append(nav)
    rows.extend(hidden_row)
    await _gstats_deliver(update, "\n".join(lines).rstrip(), InlineKeyboardMarkup(rows), preview=True)


async def set_group_bot_state(context, chat_id, enabled, actor):
    """Bot ON/OFF in one group, with the same effects as /boton and /botoff. Returns an error text, or None when done."""
    if not await is_group_approved(chat_id):
        return "⚠️ This group is not approved. Use /approve first."
    bd = context.application.bot_data
    await asyncio.to_thread(set_bot_enabled, chat_id, bool(enabled))
    bd.setdefault("bot_off_warning_sent", set()).discard(chat_id)
    if enabled:
        await asyncio.to_thread(register_auto_spawn_group, chat_id)
        bd.setdefault("active_chats", set()).add(chat_id)
    else:
        bd.setdefault("active_chats", set()).discard(chat_id)
        removed_spawn = bd.setdefault("active_spawns", {}).pop(chat_id, None)
        if removed_spawn:
            await cancel_spawn_expiry_task(removed_spawn)
            await safe_delete_message(context.bot, chat_id, removed_spawn.get("message_id"))
    await notify_staff_action(
        context,
        ("🟢 BOT TURNED ON" if enabled else "🔴 BOT TURNED OFF") + f"\n🆔 Group ID: {chat_id}\n👤 By: {display_user(actor)}",
        actor_id=actor.id,
    )
    return None


GSTATS_JOIN_LINK_TTL = 12 * 3600


async def _gstats_join_link(context, chat_id, info, links):
    """(url, joinable). joinable=True: the link lets a non-member join (public name, the group's invite link, or a link the
    bot creates when it is an admin with the 'Add users' right). Otherwise a members-only link (or None)."""
    username = (info.get("username") or "").lstrip("@").strip()
    if username:
        return f"https://t.me/{username}", True
    primary = links.get(str(chat_id))
    if primary and str(primary).startswith(("https://t.me/", "http://t.me/", "https://telegram.me/")):
        return str(primary), True
    cache = context.application.bot_data.setdefault("gstats_join_links", {})
    hit = cache.get(chat_id)
    if hit and time.monotonic() - hit[0] < GSTATS_JOIN_LINK_TTL:
        return hit[1], True
    try:
        created = await context.bot.create_chat_invite_link(chat_id, name="Owner access")   # extra link, nothing is revoked
        url = getattr(created, "invite_link", None)
        if url:
            cache[chat_id] = (time.monotonic(), url)
            return url, True
    except Exception as e:
        print(f"/gstats invite link error for {chat_id}:", e)
    return build_group_open_link(chat_id), False


async def _gstats_show_group(update, context, chat_id, page):
    """Manage page of one group: details + Open Link / Bot ON-OFF / Hide / Back."""
    got = await _gstats_collect(context, False)
    info = got[0].get(str(chat_id)) if got else None
    if info is None:                                   # no longer in the list (hidden, or the bot left)
        await gstats(update, context, page=page, force=False)
        return
    links = got[1]
    title = info.get("title") or "Unknown"
    enabled = await asyncio.to_thread(is_bot_enabled, chat_id)
    approved = await is_group_approved(chat_id)
    (members, (link, joinable)) = await asyncio.gather(
        group_member_count(context.bot, chat_id), _gstats_join_link(context, chat_id, info, links))
    text = (f"🏠 <b>{html_escape(title)}</b>\n"
            f"🆔 Group ID: <code>{chat_id}</code>\n"
            f"👥 Members: {members if members is not None else '?'}\n"
            f"🤖 Bot: {'🟢 ON' if enabled else '🔴 OFF'}\n"
            f"🔐 Approval: {'✅ Approved' if approved else '❌ Not Approved'}")
    if not joinable:
        text += ("\n\n⚠️ No join link. The link below opens only for members. "
                 "To get a join link, make the bot an admin with the “Add users” right.")
    rows = []
    if link:
        rows.append([InlineKeyboardButton("🔗 Open Link" if joinable else "🔗 Open (members only)", url=link)])
    rows.append([InlineKeyboardButton("🤖 Bot: Turn OFF" if enabled else "🤖 Bot: Turn ON",
                                      callback_data=f"gstats:t:{chat_id}:{page}")])
    rows.append([InlineKeyboardButton("🙈 Hide", callback_data=f"gstats:x:{chat_id}:{page}")])
    rows.append([InlineKeyboardButton("« Back", callback_data=f"gstats:p:{page}")])
    await _gstats_deliver(update, text, InlineKeyboardMarkup(rows))


async def _gstats_hidden_items(context):
    """[(chat_id, title)] of hidden groups. A name that is not stored is read from Telegram (and remembered)."""
    hidden_ids = await asyncio.to_thread(load_gstats_hidden_groups)
    registry = await asyncio.to_thread(load_bot_groups)
    names = context.application.bot_data.setdefault("gstats_title_cache", {})
    titles = {}
    missing = []
    for cid in hidden_ids:
        cid = int(cid)
        stored = (registry.get(str(cid), {}).get("title") or "").strip()
        if cid == DEFAULT_GSTATS_GROUP_ID:
            stored = DEFAULT_GSTATS_GROUP_TITLE
        stored = stored or names.get(cid, "")
        if stored:
            titles[cid] = stored
        else:
            missing.append(cid)

    async def _live_title(cid):
        try:
            chat = await asyncio.wait_for(context.bot.get_chat(cid), timeout=6)
            return cid, (getattr(chat, "title", None) or getattr(chat, "username", None) or "").strip()
        except Exception as e:
            print(f"Hidden group name lookup error for {cid}:", e)
            return cid, ""

    for cid, name in await asyncio.gather(*[_live_title(c) for c in missing]):
        if name:
            names[cid] = name
        titles[cid] = name or "Unknown"
    items = [(cid, titles[cid]) for cid in titles]
    items.sort(key=lambda it: it[1].casefold())
    return items


async def _gstats_hidden_list(update, context, page):
    items = await _gstats_hidden_items(context)
    back = [InlineKeyboardButton("« Back", callback_data="gstats:p:0")]
    if not items:
        await _gstats_deliver(update, "👁 <b>Hidden groups</b>\n\nNo group is hidden.", InlineKeyboardMarkup([back]))
        return
    pages = max(1, -(-len(items) // GSTATS_PAGE_SIZE))
    page = max(0, min(int(page), pages - 1))
    offset = page * GSTATS_PAGE_SIZE
    lines = [f"👁 <b>Hidden groups</b> ({len(items)})", "", "Tap a group to show it again.", ""]
    buttons = []
    for i, (cid, title) in enumerate(items[offset:offset + GSTATS_PAGE_SIZE], offset + 1):
        lines.append(f"{i}. 🏠 {html_escape(title)}")
        lines.append(f"🆔 Group ID: <code>{cid}</code>")
        lines.append("")
        buttons.append(InlineKeyboardButton(f"{i}. {title[:22]}", callback_data=f"gstats:hg:{cid}:{page}"))
    if pages > 1:
        lines.append(f"Page {page + 1}/{pages}")
    rows = _gstats_name_rows(buttons)
    nav = _gstats_nav_row(page, pages, "gstats:h")
    if nav:
        rows.append(nav)
    rows.append(back)
    await _gstats_deliver(update, "\n".join(lines).rstrip(), InlineKeyboardMarkup(rows))


async def _gstats_hidden_group(update, context, chat_id, page):
    """Page of one hidden group: details + Show / Back."""
    title = next((t for c, t in await _gstats_hidden_items(context) if c == chat_id), "Unknown")
    enabled = await asyncio.to_thread(is_bot_enabled, chat_id)
    approved = await is_group_approved(chat_id)
    text = (f"🙈 <b>{html_escape(title)}</b> (hidden)\n"
            f"🆔 Group ID: <code>{chat_id}</code>\n"
            f"🤖 Bot: {'🟢 ON' if enabled else '🔴 OFF'}\n"
            f"🔐 Approval: {'✅ Approved' if approved else '❌ Not Approved'}\n\n"
            "This group is hidden from the /gstats list. Nothing was removed.")
    rows = [[InlineKeyboardButton("👁 Show", callback_data=f"gstats:s:{chat_id}:{page}")],
            [InlineKeyboardButton("« Back", callback_data=f"gstats:h:{page}")]]
    await _gstats_deliver(update, text, InlineKeyboardMarkup(rows))


async def gstats_callback(update, context):
    """GStats buttons. Callback data: gstats:<p|g|t|x|h|hg|s>:<page or group id>[:<page>]  (gstats:delete:<id> = old Hide)."""
    query = update.callback_query
    if not is_owner(query.from_user.id):
        await deny_callback(query)
        return
    parts = (query.data or "").split(":")
    action = parts[1] if len(parts) > 1 else ""
    arg = parts[2] if len(parts) > 2 else ""
    page_arg = parts[3] if len(parts) > 3 else "0"
    page = int(page_arg) if page_arg.isdigit() else 0
    is_group_arg = arg.lstrip("-").isdigit()

    async def _answer(text=None, alert=False):
        try:
            await query.answer(text, show_alert=alert)       # answer first (Telegram expires it after ~15 s)
        except Exception:
            pass

    try:
        if action == "p" and arg.isdigit():
            await _answer()
            await gstats(update, context, page=int(arg), force=False)
        elif action == "g" and is_group_arg:
            await _answer()
            await _gstats_show_group(update, context, int(arg), page)
        elif action == "t" and is_group_arg:
            chat_id = int(arg)
            now_enabled = await asyncio.to_thread(is_bot_enabled, chat_id)
            error = await set_group_bot_state(context, chat_id, not now_enabled, query.from_user)
            if error:
                await _answer(error, alert=True)
                return
            await _answer("🔴 Bot is now OFF" if now_enabled else "🟢 Bot is now ON")
            await _gstats_show_group(update, context, chat_id, page)
        elif action in ("x", "delete") and is_group_arg:
            chat_id = int(arg)
            await _answer("🙈 Hiding group from GStats…")
            if not (await asyncio.to_thread(hide_gstats_group, chat_id)):
                await safe_reply_text(query.message, "❌ Could not hide this group.")
                return
            cache = context.application.bot_data.get("gstats_cache")
            if cache:
                cache["groups"].pop(str(chat_id), None)
            await gstats(update, context, page=page, force=False)
        elif action == "h" and arg.isdigit():
            await _answer()
            await _gstats_hidden_list(update, context, int(arg))
        elif action == "hg" and is_group_arg:
            await _answer()
            await _gstats_hidden_group(update, context, int(arg), page)
        elif action == "s" and is_group_arg:
            await _answer("👁 Showing group in GStats…")
            if not (await asyncio.to_thread(unhide_gstats_group, int(arg))):
                await safe_reply_text(query.message, "❌ Could not show this group.")
                return
            await gstats(update, context, page=0, force=True)
        else:
            await _answer("❌ Invalid GStats option.", alert=True)
    except Exception as e:
        print("GStats callback error:", repr(e))
        await _answer("⚠️ Something went wrong. Please try /gstats again.", alert=True)

def _staff_rows(ids):
    """[(user_id, display name, username|None)] sorted by id, from the users collection (one worker-thread call)."""
    rows = []
    for uid in sorted({int(i) for i in ids}):
        try:
            names = mongo_db.get_user_names(uid)
        except Exception as e:
            print(f"Staff list lookup error ({uid}):", e)
            names = None
        if names:
            first, last, username = names
            name = " ".join(v for v in (first, last) if v).strip() or "Unknown"
        else:
            name, username = "Unknown", None
        rows.append((uid, name, username))
    return rows


def format_staff_list(title, rows):
    lines = [f"<b>{html_escape(title)} (Total: {len(rows)}):</b>"]
    if not rows:
        lines.append("None assigned yet.")
    for i, (uid, name, username) in enumerate(rows, 1):
        handle = f" (<code>@{html_escape(username)}</code>)" if username else ""            # inside <code>: shown, but never pings
        if username:                                                                         # normal profile link: opens the profile, does not ping
            name_html = f'<a href="{html_escape("https://t.me/" + username, quote=True)}">{html_escape(name)}</a>'
        else:
            name_html = html_escape(name)                                                    # no tg://user link: that one would ping
        lines.append(f'{i}. {name_html}{handle} - ID: <code>{uid}</code>')
    return "\n".join(lines)


async def executives(update, context):
    """Public: every user can view the Executive list."""
    rows = await asyncio.to_thread(_staff_rows, list(EXECUTIVE_IDS))
    await safe_reply_text(update.effective_message, format_staff_list("Executives", rows), parse_mode="HTML")


async def addexec(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    if len(context.args) != 1 or not context.args[0].isdigit():
        await safe_reply_text(update.message, "Usage: /addexec <telegram_user_id>")
        return
    uid = int(context.args[0])
    if uid == update.effective_user.id or uid in EXECUTIVE_IDS or uid in SCOUT_IDS or is_owner(uid):
        await safe_reply_text(update.message, "❌ This user is already Owner/Executive/Scout.")
        return
    try:
        (await asyncio.to_thread(_mc("staff_roles_v2").update_one,
            {"_id": uid},
            {"$set": {"user_id": uid, "role": "executive"}, "$setOnInsert": {"added_at": timestamp()}},
            upsert=True,
        ))
    except Exception as e:
        print("addexec error:", e)
        await safe_reply_text(update.message, "❌ Could not add this Executive.")
        return
    if uid not in EXECUTIVE_IDS:
        EXECUTIVE_IDS.append(uid)
    await refresh_command_menu(context.bot, uid)
    await safe_reply_text(update.message, f"✅ {uid} added as Executive.")
    await notify_staff_action(context, f"⚡ EXECUTIVE ADDED\n🆔 User ID: {uid}\n👤 By: {display_user(update.effective_user)}", actor_id=update.effective_user.id)

async def removeexec(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    if len(context.args) != 1 or not context.args[0].isdigit():
        await safe_reply_text(update.message, "Usage: /removeexec <telegram_user_id>")
        return
    uid=int(context.args[0])
    if uid not in EXECUTIVE_IDS:
        await safe_reply_text(update.message, "❌ Executive not found.")
        return
    try:
        role_removed = (await asyncio.to_thread(_mc("staff_roles_v2").delete_one, {"_id": uid, "role": "executive"})).deleted_count > 0
        if not role_removed:
            await safe_reply_text(update.message, "❌ Executive not found in database.")
            return
        (await asyncio.to_thread(_mc("group_approval_permissions_v2").delete_one, {"_id": uid}))
    except Exception as e:
        print("removeexec error:", e)
        await safe_reply_text(update.message, "❌ Could not remove this Executive.")
        return
    EXECUTIVE_IDS.remove(uid)
    await refresh_command_menu(context.bot, uid)
    await safe_reply_text(update.message, f"✅ {uid} removed from Executive staff.")
    await notify_staff_action(context, f"⚠️ EXECUTIVE REMOVED\n🆔 User ID: {uid}\n👤 By: {display_user(update.effective_user)}", actor_id=update.effective_user.id)

async def addscout(update, context):
    if not (is_owner(update.effective_user.id) or is_executive(update.effective_user.id)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    if len(context.args) != 1 or not context.args[0].isdigit():
        await safe_reply_text(update.message, "Usage: /addscout <telegram_user_id>")
        return
    uid = int(context.args[0])
    if uid == update.effective_user.id or is_owner(uid) or is_executive(uid) or (await asyncio.to_thread(is_scout, uid)):
        await safe_reply_text(update.message, "❌ This user is already Owner/Executive/Scout.")
        return
    try:
        (await asyncio.to_thread(_mc("staff_roles_v2").update_one,
            {"_id": uid},
            {"$set": {"user_id": uid, "role": "scout"}, "$setOnInsert": {"added_at": timestamp()}},
            upsert=True,
        ))
    except Exception as e:
        print("addscout error:", e)
        await safe_reply_text(update.message, "❌ Could not add this Scout.")
        return
    if uid not in SCOUT_IDS:
        SCOUT_IDS.append(uid)
    await refresh_command_menu(context.bot, uid)
    await safe_reply_text(update.message, f"✅ {uid} added as Scout.\n\n🔭 Scout commands are now enabled for this user in Bot PM.")
    await notify_staff_action(context, f"🔭 SCOUT ADDED\n🆔 User ID: {uid}\n👤 By: {display_user(update.effective_user)}", actor_id=update.effective_user.id)

async def removescout(update, context):
    if not (is_owner(update.effective_user.id) or is_executive(update.effective_user.id)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    if len(context.args) != 1 or not context.args[0].isdigit():
        await safe_reply_text(update.message, "Usage: /removescout <telegram_user_id>")
        return
    uid = int(context.args[0])
    if uid not in SCOUT_IDS:
        await safe_reply_text(update.message, "❌ Scout not found.")
        return
    try:
        if (await asyncio.to_thread(_mc("staff_roles_v2").delete_one, {"_id": uid, "role": "scout"})).deleted_count == 0:
            await safe_reply_text(update.message, "❌ Scout not found in database.")
            return
    except Exception as e:
        print("removescout error:", e)
        await safe_reply_text(update.message, "❌ Could not remove this Scout.")
        return
    SCOUT_IDS.remove(uid)
    await refresh_command_menu(context.bot, uid)
    await safe_reply_text(update.message, f"✅ {uid} removed from Scout staff.")
    await notify_staff_action(context, f"⚠️ SCOUT REMOVED\n🆔 User ID: {uid}\n👤 By: {display_user(update.effective_user)}", actor_id=update.effective_user.id)

ISSUE_TEXT, ISSUE_ATTACHMENT = range(100, 102)
IDEA_TEXT, IDEA_ATTACHMENT = range(200, 202)
APPEAL_TEXT, APPEAL_ATTACHMENT = range(300, 302)

async def issue_start(update, context):
    (await save_user_async(update.effective_user))
    await safe_reply_text(update.message,
        "🛠 Please send your issue details.\n\n"
        "After that, you can optionally send a photo/screenshot.\n"
        "If you don't have a photo, send /skip."
    )
    return ISSUE_TEXT

async def issue_text(update, context):
    text = (update.message.text or "").strip()
    if not text:
        await safe_reply_text(update.message, "❌ Please send issue details.")
        return ISSUE_TEXT

    context.user_data["issue_text"] = text
    await safe_reply_text(update.message,
        "📷 Optional: send a photo/screenshot.\n"
        "Or send /skip."
    )
    return ISSUE_ATTACHMENT

async def issue_attachment(update, context):
    if update.message.photo:
        context.user_data["issue_photo"] = update.message.photo[-1].file_id
        return await finish_issue(update, context)

    if update.message.document and update.message.document.mime_type:
        if update.message.document.mime_type.startswith("image/"):
            context.user_data["issue_photo"] = update.message.document.file_id
            return await finish_issue(update, context)

    await safe_reply_text(update.message,
        "❌ Please send an image/screenshot or tap ⏭ Skip."
        , reply_markup=skip_keyboard()
    )
    return ISSUE_ATTACHMENT

async def issue_skip(update, context):
    return await finish_issue(update, context)

async def finish_issue(update, context):
    user = update.effective_user
    text = context.user_data.get("issue_text", "").strip()
    photo = context.user_data.get("issue_photo")

    try:
        issue_id = (await asyncio.to_thread(mongo_db.insert_with_id, "issues_v2", {
            "user_id": user.id, "username": user.username or "", "first_name": user.first_name or "",
            "issue_text": text, "photo_file_id": photo, "created_at": timestamp(), "status": "pending",
        }))
    except Exception as e:
        print("Issue submission database error:", e)
        await safe_reply_text(update.message, "❌ Issue could not be submitted. Please try again.", reply_markup=ReplyKeyboardRemove())
        return ConversationHandler.END

    username_str = f"@{user.username}" if user.username else "No username"
    full_name = " ".join(filter(None, [user.first_name, user.last_name])) or "Unknown"

    notification = (
        f"📥 NEW ISSUE #{issue_id}\n\n"
        f"👤 Name: {full_name}\n"
        f"🆔 User ID: {user.id}\n"
        f"🔗 Username: {username_str}\n\n"
        f"📝 Issue:\n{text}"
    )

    await notify_admins(context, notification, photo, reply_to=(user.id, "s", issue_id))

    context.user_data.pop("issue_text", None)
    context.user_data.pop("issue_photo", None)

    await safe_reply_text(update.message,
        f"✅ Issue submitted successfully.\n"
        f"🆔 Issue ID: #{issue_id}\n"
        "👨‍💼 It has been sent to the owner/admin for review.",
        reply_markup=ReplyKeyboardRemove(),
    )
    return ConversationHandler.END

async def idea_start(update, context):
    (await save_user_async(update.effective_user))
    await safe_reply_text(update.message,
        "💡 Please send your idea.\n\n"
        "After that, you can optionally send a photo/screenshot.\n"
        "If you don't have a photo, send /skip."
    )
    return IDEA_TEXT

async def idea_text(update, context):
    text = (update.message.text or "").strip()
    if not text:
        await safe_reply_text(update.message, "❌ Please send your idea.")
        return IDEA_TEXT

    context.user_data["idea_text"] = text
    await safe_reply_text(update.message,
        "📷 Optional: send a photo/screenshot.\n"
        "Or send /skip."
    )
    return IDEA_ATTACHMENT

async def idea_attachment(update, context):
    if update.message.photo:
        context.user_data["idea_photo"] = update.message.photo[-1].file_id
        return await finish_idea(update, context)

    if update.message.document and update.message.document.mime_type:
        if update.message.document.mime_type.startswith("image/"):
            context.user_data["idea_photo"] = update.message.document.file_id
            return await finish_idea(update, context)

    await safe_reply_text(update.message,
        "❌ Please send an image/screenshot or tap ⏭ Skip."
        , reply_markup=skip_keyboard()
    )
    return IDEA_ATTACHMENT

async def idea_skip(update, context):
    return await finish_idea(update, context)

async def finish_idea(update, context):
    user = update.effective_user
    text = context.user_data.get("idea_text", "").strip()
    photo = context.user_data.get("idea_photo")

    try:
        idea_id = (await asyncio.to_thread(mongo_db.insert_with_id, "ideas_v2", {
            "user_id": user.id, "username": user.username or "", "first_name": user.first_name or "",
            "idea_text": text, "photo_file_id": photo, "created_at": timestamp(), "status": "pending",
        }))
    except Exception as e:
        print("Idea submission database error:", e)
        await safe_reply_text(update.message, "❌ Idea could not be submitted. Please try again.", reply_markup=ReplyKeyboardRemove())
        return ConversationHandler.END

    username = f"@{user.username}" if user.username else "No username"
    full_name = " ".join(filter(None, [user.first_name, user.last_name])) or "Unknown"
    notification = (
        f"📥 NEW IDEA #{idea_id}\n\n"
        f"👤 Name: {full_name}\n"
        f"🆔 User ID: {user.id}\n"
        f"🔗 Username: {username}\n\n"
        f"📝 Idea:\n{text}"
    )

    await notify_admins(context, notification, photo, reply_to=(user.id, "i", idea_id))

    context.user_data.pop("idea_text", None)
    context.user_data.pop("idea_photo", None)

    await safe_reply_text(update.message,
        f"✅ Idea submitted successfully.\n"
        f"🆔 Idea ID: #{idea_id}\n"
        "👨‍💼 It has been sent to the owner/admin for review.",
        reply_markup=ReplyKeyboardRemove(),
    )
    return ConversationHandler.END

async def appeal_start(update, context):
    (await save_user_async(update.effective_user))
    await safe_reply_text(update.message,
        "⚖️ Please send your appeal details.\n\n"
        "Mention the punishment/restriction and why you think it should "
        "be reviewed.\n"
        "After that, you can optionally send a photo/screenshot.\n"
        "If you don't have a photo, send /skip."
    )
    return APPEAL_TEXT

async def appeal_text(update, context):
    text = (update.message.text or "").strip()
    if not text:
        await safe_reply_text(update.message, "❌ Please send appeal details.")
        return APPEAL_TEXT

    context.user_data["appeal_text"] = text
    await safe_reply_text(update.message,
        "📷 Optional: send a photo/screenshot.\n"
        "Or send /skip."
    )
    return APPEAL_ATTACHMENT

async def appeal_attachment(update, context):
    if update.message.photo:
        context.user_data["appeal_photo"] = update.message.photo[-1].file_id
        return await finish_appeal(update, context)

    if update.message.document and update.message.document.mime_type:
        if update.message.document.mime_type.startswith("image/"):
            context.user_data["appeal_photo"] = update.message.document.file_id
            return await finish_appeal(update, context)

    await safe_reply_text(update.message,
        "❌ Please send an image/screenshot or tap ⏭ Skip."
        , reply_markup=skip_keyboard()
    )
    return APPEAL_ATTACHMENT

async def appeal_skip(update, context):
    return await finish_appeal(update, context)

async def finish_appeal(update, context):
    user = update.effective_user
    text = context.user_data.get("appeal_text", "").strip()
    photo = context.user_data.get("appeal_photo")

    try:
        appeal_id = (await asyncio.to_thread(mongo_db.insert_with_id, "appeals_v2", {
            "user_id": user.id, "username": user.username or "", "first_name": user.first_name or "",
            "appeal_text": text, "photo_file_id": photo, "created_at": timestamp(), "status": "pending",
        }))
    except Exception as e:
        print("Appeal submission database error:", e)
        await safe_reply_text(update.message, "❌ Appeal could not be submitted. Please try again.", reply_markup=ReplyKeyboardRemove())
        return ConversationHandler.END

    username = f"@{user.username}" if user.username else "No username"
    full_name = " ".join(filter(None, [user.first_name, user.last_name])) or "Unknown"
    notification = (
        f"📥 NEW APPEAL #{appeal_id}\n\n"
        f"👤 Name: {full_name}\n"
        f"🆔 User ID: {user.id}\n"
        f"🔗 Username: {username}\n\n"
        f"📝 Appeal:\n{text}"
    )

    await notify_admins(context, notification, photo, reply_to=(user.id, "a", appeal_id))

    context.user_data.pop("appeal_text", None)
    context.user_data.pop("appeal_photo", None)

    await safe_reply_text(update.message,
        f"✅ Appeal submitted successfully.\n"
        f"🆔 Appeal ID: #{appeal_id}\n"
        "👨‍💼 It has been sent to the owner/admin for review.",
        reply_markup=ReplyKeyboardRemove(),
    )
    return ConversationHandler.END

def notification_history_cutoff():
    now = datetime.now(IST)
    day = now.date() if now.hour >= 4 else (now - timedelta(days=1)).date()
    return datetime.combine(day, dt_time(4, 0), tzinfo=IST).astimezone(timezone.utc)

def clear_old_notification_history():
    try:
        cutoff = notification_history_cutoff().isoformat()
        return _mc("notification_history_v2").delete_many({"created_at": {"$lt": cutoff}}).deleted_count
    except Exception as e:
        print("Notification history cleanup error:", e)
        return 0

def save_notification_history(user_id, notification_text):
    try:
        clear_old_notification_history()
        now = datetime.now(timezone.utc)
        mongo_db.insert_with_id("notification_history_v2", {
            "user_id": int(user_id), "notification_text": str(notification_text), "created_at": now.isoformat(),
        })
    except Exception as e:
        print(f"Notification history save error for {user_id}: {e}")

def load_notification_history(user_id, limit=None):
    try:
        clear_old_notification_history()
        rows = [(d.get("notification_text"), d.get("created_at"))
                for d in _mc("notification_history_v2").find({"user_id": int(user_id)}).sort([("created_at", 1), ("_id", 1)])]
        # Always chronological (oldest -> newest). With a limit, keep the LATEST N, still oldest -> newest,
        # so the newest entry is always the very last line of the message.
        if limit:
            return rows[-int(limit):]
        return rows
    except Exception as e:
        print(f"Notification history load error for {user_id}: {e}")
        return []

def format_notification_history_time(value):
    try:
        dt = datetime.fromisoformat(value)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone(timedelta(hours=5, minutes=30))).strftime("%d-%m-%Y %I:%M %p")
    except Exception:
        return str(value)

async def notification_history_command(update, context):
    uid = update.effective_user.id
    if not (is_owner(uid) or is_executive(uid) or (await asyncio.to_thread(is_scout, uid))):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(update.effective_message, "Use /notificationhistory in your Bot PM.")
        return
    rows = (await asyncio.to_thread(load_notification_history, uid))
    if not rows:
        await safe_reply_text(update.effective_message, "🔔 NOTIFICATION HISTORY\n\n📭 No notifications yet.")
        return
    lines = ["🔔 YOUR NOTIFICATION HISTORY", "", "📜 Oldest → newest (latest at bottom):", ""]
    for index, (text, created_at) in enumerate(rows, 1):
        lines.append(f"{index}. 🕒 {format_notification_history_time(created_at)}")
        lines.append(str(text).strip())
        lines.append("────────────────")
    await safe_reply_text(update.effective_message, "\n".join(lines))

async def notify_admins(context, text, photo_file_id=None, reply_to=None, include_scouts=True):
    owner_id = ADMIN_IDS[0] if ADMIN_IDS else None

    executive_ids = set()
    scout_ids = set(int(uid) for uid in SCOUT_IDS)
    try:
        for uid, role in (await asyncio.to_thread(_staff_role_rows)):
            uid = int(uid)
            if role == "executive":
                executive_ids.add(uid)
            elif role == "scout":
                scout_ids.add(uid)
        pass
    except Exception as e:
        print("Staff notification lookup error:", e)

    executive_ids.update(int(uid) for uid in EXECUTIVE_IDS)
    scout_ids = {uid for uid in scout_ids if uid not in executive_ids and uid != owner_id}
    if not include_scouts:
        scout_ids = set()

    recipients = []
    if owner_id is not None:
        recipients.append(owner_id)
    recipients.extend(uid for uid in sorted(executive_ids) if uid != owner_id)
    recipients.extend(uid for uid in sorted(scout_ids) if uid != owner_id and uid not in executive_ids)

    if not recipients:
        print("Staff notification skipped: no staff recipient configured")
        return

    delivered = 0
    skipped = 0
    for staff_id in recipients:
        (await asyncio.to_thread(save_notification_history, staff_id, text))
        if not (await asyncio.to_thread(notifications_enabled_for, staff_id)):
            skipped += 1
            print(f"Staff notification skipped for {staff_id}: personal setting OFF")
            continue
        markup = None                                # ✍️ Reply under an Idea / Issue / Appeal: owner + executives only
        if reply_to:
            r_uid, r_kind, r_id = reply_to
            if staff_id == owner_id:
                markup = _bc_kb([_bc_btn("✍️ Reply", f"dm:ri:{r_uid}:{r_kind}{r_id}"), _bc_btn("📜 History", f"dm:h:{r_uid}:0")])
            elif staff_id in executive_ids:
                markup = _bc_kb([_bc_btn("✍️ Reply", f"dm:ri:{r_uid}:{r_kind}{r_id}")])
        try:
            sent_ids = []
            if photo_file_id:
                if len(text) <= 1024:
                    m = await asyncio.wait_for(
                        context.bot.send_photo(chat_id=staff_id, photo=photo_file_id, caption=text,
                                               caption_entities=copyable_ids(text), reply_markup=markup),
                        timeout=15,
                    )
                    sent_ids.append(m.message_id)
                else:
                    await asyncio.wait_for(
                        context.bot.send_photo(
                            chat_id=staff_id,
                            photo=photo_file_id,
                            caption="📎 Attachment for the submission below.",
                        ),
                        timeout=15,
                    )
                    m = await asyncio.wait_for(
                        context.bot.send_message(chat_id=staff_id, text=text, entities=copyable_ids(text), reply_markup=markup), timeout=15
                    )
                    sent_ids.append(m.message_id)
            else:
                m = await asyncio.wait_for(
                    context.bot.send_message(chat_id=staff_id, text=text, entities=copyable_ids(text), reply_markup=markup), timeout=15
                )
                sent_ids.append(m.message_id)
            if markup is not None:
                await _dm_note(staff_id, sent_ids, reply_to[0], ctx=f"{reply_to[1]}{reply_to[2]}")
            delivered += 1
            print(f"Staff notification delivered to {staff_id}")
        except asyncio.TimeoutError:
            print(f"Staff notification timeout for {staff_id}")
        except Exception as e:
            print(f"Staff notification error for {staff_id}: {e}")

    print(f"Staff notification result: {delivered}/{len(recipients)} delivered, {skipped} personally OFF")

# Character / evolution add + update actions ALWAYS notify staff, even when the Owner does them.
_ALWAYS_NOTIFY_PREFIXES = (
    "🎭 NEW CHARACTER ADDED", "✏️ CHARACTER UPDATED", "📷 CHARACTER PHOTO UPDATED",
    "🎭 NEW EVOLUTION ADDED", "✏️ EVOLUTION UPDATED",
)

async def notify_staff_action(context, action_text, actor_id=None, owner_choice=False):
    try:
        if actor_id is not None and is_owner(actor_id):
            if not str(action_text).lstrip().startswith(_ALWAYS_NOTIFY_PREFIXES):
                return      # Other Owner actions: no notification, no Yes/No prompt (the 3 allowed ones use the log prompt)
            notification = f"🔔 BOT NOTIFICATION\n\n{action_text}"
            await notify_admins(context, notification)   # Owner + Executives + Scouts (each personal /notificationoff respected)
            return
        choice_id = int(actor_id) if actor_id is not None and is_owner(actor_id) else (int(ADMIN_IDS[0]) if owner_choice and ADMIN_IDS else None)
        if choice_id is not None:
            pending = context.application.bot_data.setdefault("pending_owner_notifications", {})
            pending[choice_id] = str(action_text)
            keyboard = InlineKeyboardMarkup([[
                InlineKeyboardButton("🔔 Send Notification", callback_data="owner_notify:yes"),
                InlineKeyboardButton("🔕 Don't Send", callback_data="owner_notify:no"),
            ]])
            try:
                await asyncio.wait_for(
                    context.bot.send_message(
                        chat_id=choice_id,
                        text="🔔 Notification sent karni hai?\n\n👇 Choose an option:",
                        reply_markup=keyboard,
                    ),
                    timeout=15,
                )
                print(f"Owner notification choice sent to {choice_id}")
            except Exception as e:
                print(f"Owner notification choice send error for {choice_id}: {e}")
            return
        notification = f"🔔 BOT NOTIFICATION\n\n{action_text}"
        await notify_admins(context, notification)

        if actor_id is not None and (is_owner(actor_id) or is_executive(actor_id) or (await asyncio.to_thread(is_scout, actor_id))):
            if not (await asyncio.to_thread(notifications_enabled_for, actor_id)):
                return
            owner_id = ADMIN_IDS[0] if ADMIN_IDS else None
            executive_ids = set(int(uid) for uid in EXECUTIVE_IDS)
            scout_ids = set(int(uid) for uid in SCOUT_IDS)
            try:
                for uid, role in (await asyncio.to_thread(_staff_role_rows)):
                    if role == "executive": executive_ids.add(int(uid))
                    elif role == "scout": scout_ids.add(int(uid))
            except Exception:
                pass
            known_recipients = {owner_id} | executive_ids | scout_ids
            if actor_id not in known_recipients:
                try:
                    await asyncio.wait_for(
                        context.bot.send_message(chat_id=actor_id, text=notification), timeout=15
                    )
                except Exception as e:
                    print(f"Actor notification error for {actor_id}: {e}")
    except Exception as e:
        print("Staff action notification error:", e)

async def owner_notification_callback(update, context):
    q = update.callback_query
    owner_id = q.from_user.id
    if not is_owner(owner_id):
        await deny_callback(q)
        return

    data = q.data or ""
    pending = context.application.bot_data.setdefault("pending_owner_notifications", {})
    action_text = pending.pop(owner_id, None)
    if not action_text:
        await q.answer("⚠️ No pending notification found.", show_alert=True)
        try:
            await q.edit_message_text("⚠️ No pending notification found.")
        except Exception:
            pass
        return

    if data == "owner_notify:yes":
        await notify_admins(context, f"🔔 BOT NOTIFICATION\n\n{action_text}")
        await q.answer("✅ Notification sent.")
        try:
            await q.edit_message_text("🔔 Notification sent.\n\n👤 Owner")
        except Exception:
            pass
    else:
        await q.answer("🔕 Notification not sent.")
        try:
            await q.edit_message_text("🔕 Notification not sent.\n\n👤 Owner")
        except Exception:
            pass

def record_spawn_history(chat_id, character, spawned_by="auto"):
    try:
        _group_cooldown_add(chat_id, character)
        return mongo_db.sh_insert(chat_id, character[0], character[3], spawned_by, india_timestamp())
    except Exception as e:
        print("Spawn history error:", e)
        return None

def mark_spawn_expiry_notified(history_id):
    if not history_id:
        return
    try:
        mongo_db.sh_mark_expiry_notified(history_id, india_timestamp())
    except Exception as e:
        print("Spawn expiry notification history error:", e)

def mark_spawn_caught(history_id, user_id):
    if not history_id:
        return
    try:
        mongo_db.sh_mark_caught(history_id, user_id, india_timestamp())
    except Exception as e:
        print("Spawn catch history error:", e)

async def history(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return

    limit = 20
    if context.args:
        try:
            limit = max(1, min(int(context.args[0]), 50))
        except ValueError:
            await safe_reply_text(update.message, "Usage: /history [1-50]")
            return

    rows = []
    try:
        _hist_rows = (await asyncio.to_thread(mongo_db.sh_latest, limit))
        _hist_names = (await asyncio.to_thread(mongo_db.get_character_names, [r[0] for r in _hist_rows]))
        rows = [tuple(r) + (_hist_names.get(str(r[0])),) for r in reversed(_hist_rows)]   # newest-first -> oldest-first
    except Exception as e:
        print("history error:", e)
        await safe_reply_text(update.message, "❌ Could not load spawn history.")
        return

    if not rows:
        await safe_reply_text(update.message, "📜 No spawn history yet.")
        return

    now = datetime.now(INDIA_TZ)
    lines = [f"📜 Spawn History — latest {len(rows)} (oldest → newest, latest at bottom)", ""]
    for i, row in enumerate(rows, 1):
        code, rarity, spawned_by, spawned_at, caught_by, caught_at, name = row
        char_name = name or "Unknown Character"
        try:
            spawned_dt = datetime.fromisoformat(str(spawned_at))
            if spawned_dt.tzinfo is None:
                spawned_dt = spawned_dt.replace(tzinfo=INDIA_TZ)
            spawned_dt = spawned_dt.astimezone(INDIA_TZ)
            spawned_text = spawned_dt.strftime("%d %b %Y, %I:%M %p")
            expired = (now - spawned_dt).total_seconds() >= SPAWN_LIFETIME
        except Exception:
            spawned_text = str(spawned_at)
            expired = False

        source_map = {
            "auto_spawn": "Auto",
            "manual_spawn": "Manual /spawn",
            "owner_callchar": "Owner /callcharacter",
            "auto": "Auto",
            "manual": "Manual",
        }
        source = source_map.get(spawned_by, spawned_by or "Unknown")

        if caught_by:
            caught_text = f"Caught by <code>{caught_by}</code>"
            if caught_at:
                try:
                    caught_text += f" at {datetime.fromisoformat(caught_at).strftime('%d %b %Y, %I:%M %p')}"
                except Exception:
                    caught_text += f" at {caught_at}"
        elif expired:
            caught_text = "⏰ Expired / uncaught"
        else:
            caught_text = "🟢 Still active / uncaught"

        lines.append(
            f"#{i} {char_name} [{rarity}]\n"
            f"Code: <code>{code}</code> • Spawned: {spawned_text}\n"
            f"By: {source}\n"
            f"{caught_text}"
        )

    await safe_reply_text(update.message, "\n\n".join(lines), parse_mode="HTML")

SPAWN_TRACKING_RESET_HOUR_IST = 0

def get_spawn_tracking_today_key():
    now = datetime.now(INDIA_TZ)
    if now.hour < SPAWN_TRACKING_RESET_HOUR_IST:
        now -= timedelta(days=1)
    return now.strftime("%Y-%m-%d")

def get_today_group_spawn_tracking():
    today_key = get_spawn_tracking_today_key()
    tracking = {}
    try:
        rows = mongo_db.sh_day_rows(today_key)
    except Exception as e:
        print("Group spawn tracking error:", e)
        return tracking

    for chat_id, rarity, spawned_at in rows:
        try:
            dt = datetime.fromisoformat(str(spawned_at))
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=INDIA_TZ)
            dt = dt.astimezone(INDIA_TZ)
            if dt.hour < SPAWN_TRACKING_RESET_HOUR_IST:
                dt -= timedelta(days=1)
            if dt.date().isoformat() != today_key:
                continue
            key = str(chat_id)
            bucket = tracking.setdefault(key, {
                "Common": 0, "Rare": 0, "Epic": 0,
                "Legendary": 0, "Mythical": 0, "Celestial": 0,
                "total": 0,
            })
            rarity = str(rarity)
            if rarity not in bucket:
                bucket[rarity] = 0
            bucket[rarity] += 1
            bucket["total"] += 1
        except Exception:
            continue
    return tracking

async def build_status_lines(app):
    active = app.bot_data.setdefault("active_spawns", {})
    users = (await asyncio.to_thread(mongo_db.count_users))
    characters = (await asyncio.to_thread(mongo_db.count_characters))
    catches = (await asyncio.to_thread(mongo_db.count_collections))

    lines = [
        "🟢 Bot Status (Owner Only)", "",
        f"👤 Registered users: {users}",
        f"🎭 Characters: {characters}",
        f"🎯 Total catches: {catches}",
        f"🔥 Active spawns: {len(active)}",
        "",
    ]

    # High-rank tracking is shown first and refreshed every time /status is opened.
    high_counts = (await asyncio.to_thread(_successful_global_quota_counts, None, get_high_rank_today_key()))
    high_gap, celestial_gap = (await asyncio.to_thread(_get_random_spawn_high_rarity_gaps, app))
    high_target, celestial_target = (await asyncio.to_thread(_get_high_rarity_spacing_targets))
    lines += [
        "💎 High-Rank Spawn Tracking:",
        f"💎 Legendary: {high_counts['Legendary']}/{LEGENDARY_DAILY_LIMIT} spawned today | Gap: {(high_gap or 0)}/{high_target}",
        f"🔮 Mythical: {high_counts['Mythical']}/{MYTHICAL_DAILY_LIMIT} spawned today | Gap: {(high_gap or 0)}/{high_target}",
        f"💠 Celestial: {high_counts['Celestial']}/{CELESTIAL_DAILY_LIMIT} spawned today | Gap: {(celestial_gap or 0)}/{celestial_target}",
        "",
    ]

    # Live ALL-GROUPS rarity totals for today's random/manual spawns.
    today_key = get_spawn_tracking_today_key()
    rarity_totals = {"Common": 0, "Rare": 0, "Epic": 0, "Legendary": 0, "Mythical": 0, "Celestial": 0}
    for rarity, count in (await asyncio.to_thread(mongo_db.sh_day_rarity_counts, today_key)).items():
        if rarity in rarity_totals:
            rarity_totals[rarity] = int(count)

    ist_now = datetime.now(INDIA_TZ)
    lines += [
        "📊 Today's Spawn Totals — All Groups:",
        f"⚪ Common: {rarity_totals['Common']}",
        f"🔵 Rare: {rarity_totals['Rare']}",
        f"🟣 Epic: {rarity_totals['Epic']}",
        f"💎 Legendary: {rarity_totals['Legendary']}/{LEGENDARY_DAILY_LIMIT}",
        f"🔮 Mythical: {rarity_totals['Mythical']}/{MYTHICAL_DAILY_LIMIT}",
        f"💠 Celestial: {rarity_totals['Celestial']}/{CELESTIAL_DAILY_LIMIT}",
        "",
        f"🕐 Current Time: {ist_now.strftime('%d %b %Y, %I:%M:%S %p')} IST",
        "",
    ]

    tracking = (await asyncio.to_thread(get_today_group_spawn_tracking))
    groups = (await asyncio.to_thread(load_bot_groups))
    group_ids = set(groups) | set(tracking)
    if group_ids:
        lines += ["", "📍 Today's Spawn Tracking — All Groups:"]
        order = sorted(group_ids, key=lambda value: int(value) if str(value).lstrip("-").isdigit() else str(value))
        for chat_id in order:
            info = groups.get(str(chat_id), {})
            title = info.get("title") or info.get("username") or f"Group {chat_id}"
            bucket = tracking.get(str(chat_id), {
                "Common": 0, "Rare": 0, "Epic": 0,
                "Legendary": 0, "Mythical": 0, "Celestial": 0, "total": 0,
            })
            lines.append(
                f"• {title} ({chat_id}) — Total: {bucket['total']}"
            )
            lines.append(
                f"  ⚪ {bucket['Common']} | 🔵 {bucket['Rare']} | 🟣 {bucket['Epic']} | "
                f"💎 {bucket['Legendary']} | 💠 {bucket['Mythical']} | 🧠 {bucket['Celestial']}"
            )
    else:
        lines += ["", "📍 Today's Spawn Tracking — No group spawn recorded yet."]

    if active:
        lines += ["", "🔥 Current active spawns:"]
        for chat_id, sp in list(active.items())[:10]:
            remaining = max(0, int((sp["expires_at"] - datetime.now()).total_seconds()))
            lines.append(f"• Chat {chat_id}: {sp['name']} [{sp['rarity']}] — {format_duration(remaining)} left")
    return lines

STATUS_REFRESH_MARKUP = InlineKeyboardMarkup([[InlineKeyboardButton("🔄 Refresh", callback_data="status:refresh")]])

def _chunk_status_lines(lines, limit=4000):
    chunks, current = [], ""
    for line in lines:
        while len(line) > limit:
            if current:
                chunks.append(current)
                current = ""
            chunks.append(line[:limit])
            line = line[limit:]
        candidate = f"{current}\n{line}" if current else line
        if len(candidate) > limit:
            chunks.append(current)
            current = line
        else:
            current = candidate
    if current:
        chunks.append(current)
    return chunks

async def status(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    lines = await build_status_lines(context.application)
    chunks = _chunk_status_lines(lines)
    if update.effective_chat.type != "private":
        try:
            for i, chunk in enumerate(chunks):
                await context.bot.send_message(chat_id=update.effective_user.id, text=chunk,
                                               reply_markup=STATUS_REFRESH_MARKUP if i == len(chunks) - 1 else None)
        except (Forbidden, BadRequest):
            await safe_reply_text(update.message, "📩 I couldn't message you privately. Open a private chat with me, press Start, then run /status again.")
            return
        await safe_reply_text(update.message, "📩 Opened in your private chat.")
        return
    for i, chunk in enumerate(chunks):
        await safe_reply_text(update.message, chunk, reply_markup=STATUS_REFRESH_MARKUP if i == len(chunks) - 1 else None)

async def status_refresh_callback(update, context):
    query = update.callback_query
    if not is_owner(query.from_user.id):
        await deny_callback(query)
        return
    lines = await build_status_lines(context.application)
    text = "\n".join(lines)
    if len(text) > 4000:
        text = _chunk_status_lines(lines)[0] + "\n… (use /status for the full list)"
    try:
        await query.edit_message_text(text, reply_markup=STATUS_REFRESH_MARKUP)
        await query.answer("🔄 Refreshed")
    except BadRequest as e:
        if "not modified" in str(e).lower():
            await query.answer("✅ Already up to date")
        else:
            print("Status refresh error:", e)
            await query.answer("⚠️ Could not refresh. Use /status.", show_alert=True)
    except Exception as e:
        print("Status refresh error:", e)

async def event(update, context):
    (await save_user_async(update.effective_user))
    row = (await asyncio.to_thread(get_active_event))
    if not row:
        await safe_reply_text(update.message, "🎉 No active event right now.")
        return

    event_id, name, description, reward_type, reward_value, end_at, _ = row
    _ev = (await asyncio.to_thread(_mc("events_v2").find_one, {"_id": event_id}))
    trigger_text = ((_ev or {}).get("trigger_text") or "") or name
    try:
        end_text = datetime.fromisoformat(end_at).strftime("%d %b %Y, %I:%M %p")
    except (TypeError, ValueError):
        end_text = end_at or "Not set"

    rw, limit = event_rewards(_ev), int((_ev or {}).get("max_per_user") or 1)
    _c = (await asyncio.to_thread(_mc("event_claims_v2").find_one, {"event_id": event_id, "user_id": update.effective_user.id}))
    n = int(_c.get("count") or 1) if _c else 0

    text = (
        f"🎉 EVENT: {name}\n\n"
        f"{description or 'Special event is live!'}\n\n"
        f"🎁 Reward: {(await asyncio.to_thread(format_event_rewards, rw))}\n"
        f"💬 Trigger: {trigger_text}\n"
        f"⏰ Ends: {end_text}"
    )
    if limit > 1:
        text += f"\n🔁 Claimed: {n}/{limit}"
    if n >= limit:
        text += "\n\n✅ You have already claimed this event reward."
    await safe_reply_text(update.message, text)

EVENT_NAME, EVENT_CODE, EVENT_BERRYS, EVENT_STONES, EVENT_TRIGGER, EVENT_END_DAY, EVENT_END_MONTH, EVENT_END_YEAR, EVENT_END_HOUR, EVENT_END_MINUTE = range(400,410)
EVENT_CHAR, EVENT_LIMIT = 410, 411

async def add_event_start(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT); return ConversationHandler.END
    await safe_reply_text(update.message, "1️⃣ Event name:"); return EVENT_NAME

async def add_event_name(update, context):
    text=update.message.text.strip()
    if not text or text.startswith("/"):
        await safe_reply_text(update.message, "❌ Event name required."); return EVENT_NAME
    context.user_data["event_name"]=text
    await safe_reply_text(update.message, "2️⃣ Event code (letters and digits, any length, e.g. spring2025):")
    return EVENT_CODE

async def add_event_code(update, context):
    key, text, code_error = parse_code(update.message.text)
    if code_error:
        await safe_reply_text(update.message, f"❌ {code_error} Send the event code again:")
        return EVENT_CODE
    active_events = (await asyncio.to_thread(lambda: list(_mc("events_v2").find({"active": 1}))))
    if any(parse_code(str(e.get("event_code") or ""))[0] == key for e in active_events):
        await safe_reply_text(update.message, "❌ This event code is already in use (capital and small letters count as the same). Send another code:")
        return EVENT_CODE
    context.user_data["event_code"]=text
    await safe_reply_text(update.message, "3️⃣ Berrys amount (send 0 to skip):")
    return EVENT_BERRYS

def _amount_or_skip(text):
    t = (text or "").strip().lower()
    return 0 if t in ("0", "none", "skip") else _positive_amount(t)

async def add_event_berrys(update, context):
    amount = _amount_or_skip(update.message.text)
    if amount is None:
        await safe_reply_text(update.message, "❌ Send a positive number, or 0 to skip."); return EVENT_BERRYS
    context.user_data["event_berrys"] = amount
    await safe_reply_text(update.message, "4️⃣ Special Stones amount (send 0 to skip):")
    return EVENT_STONES

async def add_event_stones(update, context):
    amount = _amount_or_skip(update.message.text)
    if amount is None:
        await safe_reply_text(update.message, "❌ Send a positive number, or 0 to skip."); return EVENT_STONES
    context.user_data["event_stones"] = amount
    await safe_reply_text(update.message, "5️⃣ Characters: send one or more (code or name), separated by commas. Send none to skip:")
    return EVENT_CHAR

async def add_event_char(update, context):
    text = update.message.text.strip()
    d = context.user_data
    d["event_card"] = None
    if text.lower() not in ("none", "skip", "0"):
        codes, err = (await asyncio.to_thread(parse_character_list, text))
        if err:
            await safe_reply_text(update.message, err + "\nOr send none to skip.")
            return EVENT_CHAR
        d["event_card"] = codes
    if not (d.get("event_berrys") or d.get("event_stones") or d.get("event_card")):
        await safe_reply_text(update.message, "❌ Give at least one reward. Send the Berrys amount again (0 to skip):")
        return EVENT_BERRYS
    await safe_reply_text(update.message, "6️⃣ Exact trigger phrase users must type:")
    return EVENT_TRIGGER

async def add_event_trigger(update, context):
    text=update.message.text.strip()
    if not text or text.startswith("/"):
        await safe_reply_text(update.message, "❌ Trigger phrase required and cannot start with /."); return EVENT_TRIGGER
    context.user_data["event_trigger"]=text
    await safe_reply_text(update.message, "7️⃣ How many times can each user claim the reward? (1-1000):")
    return EVENT_LIMIT

async def add_event_limit(update, context):
    n = _positive_amount(update.message.text, 1000)
    if n is None:
        await safe_reply_text(update.message, "❌ Send a number from 1 to 1000."); return EVENT_LIMIT
    context.user_data["event_limit"] = n
    await safe_reply_text(update.message, "8️⃣ Send end date — DD (day) only:")
    return EVENT_END_DAY

async def _event_end_error(update, message):
    await safe_reply_text(update.message, message)

async def add_event_end_day(update, context):
    text=update.message.text.strip()
    if not text.isdigit() or not 1<=int(text)<=31:
        await _event_end_error(update,"❌ Send a valid DD (01-31).") ; return EVENT_END_DAY
    context.user_data["event_end_day"]=int(text)
    await safe_reply_text(update.message, "7️⃣ Send end date — MM (month) only:")
    return EVENT_END_MONTH

async def add_event_end_month(update, context):
    text=update.message.text.strip()
    if not text.isdigit() or not 1<=int(text)<=12:
        await _event_end_error(update,"❌ Send a valid MM (01-12).") ; return EVENT_END_MONTH
    context.user_data["event_end_month"]=int(text)
    await safe_reply_text(update.message, "8️⃣ Send end date — YY (2-digit year) only:")
    return EVENT_END_YEAR

async def add_event_end_year(update, context):
    text=update.message.text.strip()
    if not text.isdigit() or len(text)!=2:
        await _event_end_error(update,"❌ Send a valid YY (2 digits).") ; return EVENT_END_YEAR
    context.user_data["event_end_year"]=int(text)
    await safe_reply_text(update.message, "9️⃣ Send end time — HH (hour, 00-23) only:")
    return EVENT_END_HOUR

async def add_event_end_hour(update, context):
    text=update.message.text.strip()
    if not text.isdigit() or not 0<=int(text)<=23:
        await _event_end_error(update,"❌ Send a valid HH (00-23).") ; return EVENT_END_HOUR
    context.user_data["event_end_hour"]=int(text)
    await safe_reply_text(update.message, "🔟 Send end time — MM (minute, 00-59) only:")
    return EVENT_END_MINUTE

async def add_event_end_minute(update, context):
    text=update.message.text.strip()
    if not text.isdigit() or not 0<=int(text)<=59:
        await _event_end_error(update,"❌ Send a valid MM (00-59).") ; return EVENT_END_MINUTE
    context.user_data["event_end_minute"]=int(text)
    d=dict(context.user_data)
    try:
        dt=datetime(2000+d["event_end_year"],d["event_end_month"],d["event_end_day"],d["event_end_hour"],d["event_end_minute"])
    except ValueError:
        await safe_reply_text(update.message,"❌ Invalid date. Please start /addevent again.")
        return ConversationHandler.END
    now=datetime.now()
    dt=dt.replace(year=(now.year//100)*100+d["event_end_year"])
    if dt<=now:
        await safe_reply_text(update.message,"❌ End time must be in the future.")
        return EVENT_END_MINUTE
    end_at=dt.isoformat(timespec="seconds")
    rw={k: d[f"event_{k}"] for k in ("berrys","stones","card") if d.get(f"event_{k}")}
    k0=next(iter(rw)); rewards_text=(await asyncio.to_thread(format_event_rewards, rw))
    def _create_event(session):
        _mc("events_v2").update_many({"active": 1}, {"$set": {"active": 0}}, session=session)
        mongo_db.insert_with_id("events_v2", {
            "name": d["event_name"], "event_code": d["event_code"], "description": "",
            "reward_type": {"berrys":"coins","stones":"stones","card":"character"}[k0], "reward_value": (rw[k0][0] if isinstance(rw[k0], list) else rw[k0]),
            "rewards": rw, "max_per_user": d["event_limit"],
            "end_at": end_at, "active": 1, "created_at": timestamp(), "trigger_text": d["event_trigger"],
        }, session=session)
    (await asyncio.to_thread(mongo_db.run_transaction, _create_event))
    _EVENT_CACHE["val"] = None
    context.user_data.clear()
    await safe_reply_text(update.message, f"✅ Event created!\n🎉 {d['event_name']} [{d['event_code']}]\n🎁 {rewards_text}\n💬 Trigger: {d['event_trigger']}\n🔁 Limit: {d['event_limit']} per user\n⏰ Ends: {dt.strftime('%d %m %y %I:%M %p')}", reply_markup=ReplyKeyboardRemove())
    await notify_staff_action(context, f"🎉 EVENT ADDED\n🎉 {d['event_name']} [{d['event_code']}]\n🎁 Reward: {rewards_text}\n💬 Trigger: {d['event_trigger']}\n🔁 Limit: {d['event_limit']} per user\n⏰ Ends: {dt.strftime('%d %m %y %I:%M %p')}\n👤 By: {display_user(update.effective_user)}", actor_id=update.effective_user.id)
    await release_conv_log(context, update.effective_user.id, "addevent")      # Yes/No prompt only after success
    return ConversationHandler.END

async def event_trigger_message(update, context):
    if not update.message or not update.message.text or update.message.text.startswith("/"): return
    row, trigger_text = await _active_event_cached()
    if not row: return
    event_id, name, description, reward_type, reward_value, end_at, active = row
    (await save_user_async(update.effective_user))
    trigger = (trigger_text or "") or name
    if update.message.text.strip().casefold() != trigger.strip().casefold(): return
    if end_at:
        try:
            if datetime.fromisoformat(end_at) <= datetime.now():
                (await asyncio.to_thread(_mc("events_v2").update_one, {"_id": event_id}, {"$set": {"active": 0}}))
                _EVENT_CACHE["val"] = None
                return
        except ValueError: pass
    uid = update.effective_user.id
    claims = _mc("event_claims_v2")
    ev = (await asyncio.to_thread(_mc("events_v2").find_one, {"_id": event_id}))
    rw, limit = event_rewards(ev), int((ev or {}).get("max_per_user") or 1)
    def _take_claim():      # one claim row per (event, user) with a counter; the unique index + the $lt filter keep it atomic
        r = claims.find_one_and_update({"event_id": event_id, "user_id": uid, "count": {"$lt": limit}}, {"$inc": {"count": 1}})
        if r:
            return r["_id"], r["count"] + 1
        return claims.insert_one({"event_id": event_id, "user_id": uid, "count": 1, "claimed_at": timestamp()}).inserted_id, 1
    try:
        claim_id, n = (await asyncio.to_thread(_take_claim))
    except mongo_db.DuplicateKeyError:      # limit reached: tell the user once, then stay silent until the event ends
        if await asyncio.to_thread(claims.find_one_and_update, {"event_id": event_id, "user_id": uid, "notified": {"$ne": True}}, {"$set": {"notified": True}}):
            await safe_reply_text(update.message, f"🚫 You have already claimed this event reward the maximum number of times ({limit}/{limit}).")
        return
    def _undo_claim():
        claims.update_one({"_id": claim_id}, {"$inc": {"count": -1}})
        claims.delete_one({"_id": claim_id, "count": {"$lte": 0}})

    undo = []
    try:
        if rw.get("berrys"):
            amt = int(rw["berrys"])
            if not (await asyncio.to_thread(mongo_db.add_coins, uid, amt)):
                raise RuntimeError("event reward user missing")
            undo.append(lambda amt=amt: mongo_db.add_coins(uid, -amt))
        if rw.get("stones"):
            amt = int(rw["stones"])
            if not (await asyncio.to_thread(mongo_db.add_special_stones, uid, amt)):
                raise RuntimeError("event reward user missing")
            undo.append(lambda amt=amt: mongo_db.add_special_stones(uid, -amt))
        for _c in _reward_cards(rw.get("card")):
            if not (await asyncio.to_thread(mongo_db.get_character_by_code, str(_c))):
                raise RuntimeError("event reward character missing")
            gid = (await asyncio.to_thread(mongo_db.add_collection, uid, _c, timestamp()))
            undo.append(lambda gid=gid: mongo_db.delete_collection_by_id(gid))
    except Exception as e:
        for fn in reversed(undo):
            try:
                (await asyncio.to_thread(fn))
            except Exception as undo_err:
                print("Event reward undo error:", undo_err)
        try:
            (await asyncio.to_thread(_undo_claim))
        except Exception as undo_err:
            print("Event reward undo error:", undo_err)
        print("Event reward error:", e)
        return
    await safe_reply_text(update.message, f"🎉 Event reward!\n🎁 {(await asyncio.to_thread(format_event_rewards, rw))}"
                          + (f"\n🔁 Claim {n}/{limit}" if limit > 1 else ""))

END_EVENT_CODE = 500

async def end_event_start(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return ConversationHandler.END
    row=(await asyncio.to_thread(get_active_event))
    if not row:
        await safe_reply_text(update.message, "ℹ️ No active event.")
        return ConversationHandler.END
    _ev = (await asyncio.to_thread(_mc("events_v2").find_one, {"_id": row[0]})); r = (_ev.get("event_code"),) if _ev else None
    if not r or not r[0]:
        await safe_reply_text(update.message, "❌ This event has no code and cannot be manually ended. Create a new event with a code.")
        return ConversationHandler.END
    await safe_reply_text(update.message, "🔚 Send the event code:")
    return END_EVENT_CODE

async def end_event_confirm(update, context):
    key, text, code_error = parse_code(update.message.text)
    if code_error:
        await safe_reply_text(update.message, f"❌ {code_error} Send the event code again:")
        return END_EVENT_CODE
    ev = (await asyncio.to_thread(_mc("events_v2").find_one, {"active": 1}, sort=[("_id", -1)]))
    if not ev:
        await safe_reply_text(update.message, "ℹ️ No active event.")
        return ConversationHandler.END
    event_id, name, code = ev["_id"], ev.get("name"), ev.get("event_code")
    if key != parse_code(str(code or ""))[0]:
        await safe_reply_text(update.message, "❌ Wrong event code. Send the correct code (capital and small letters do not matter):")
        return END_EVENT_CODE
    (await asyncio.to_thread(_mc("events_v2").update_one, {"_id": event_id}, {"$set": {"active": 0}}))
    _EVENT_CACHE["val"] = None
    await safe_reply_text(update.message, f"✅ Event ended successfully!\n🎉 {name} [{code}]")
    await notify_staff_action(context, f"🛑 EVENT ENDED MANUALLY\n🎉 {name} [{code}]\n👤 By: {display_user(update.effective_user)}", actor_id=update.effective_user.id)
    await release_conv_log(context, update.effective_user.id, "endevent")
    return ConversationHandler.END

async def event_claim_callback(update, context):
    query = update.callback_query
    await query.answer("🎯 Type the trigger phrase to claim the event reward.", show_alert=True)
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass

REDEEM_TYPE, REDEEM_REWARD, REDEEM_COUNT, REDEEM_EXPIRY, REDEEM_CODE = range(500,505)
REDEEM_MORE = 505

CODE_MAX_LENGTH = 1000      # safety ceiling only (a code is one Telegram command argument); there is no practical limit


def parse_code(text):
    """
    Redeem codes and event codes: letters of ANY language and digits, mixed freely (hello123), any length from 1 character.
    Returns (key, display, error). `key` is the case-insensitive form (Unicode NFKC + casefold) used for storage and lookup, so
    Hello123, hello123 and HELLO123 are ONE code; `display` is the code exactly as the Owner typed it.
    """
    raw = (text or "").strip()
    if not raw:
        return None, None, "Send the code."
    if len(raw) > CODE_MAX_LENGTH:
        return None, None, f"That code is {len(raw)} characters long; the safety limit is {CODE_MAX_LENGTH}."
    for n, ch in enumerate(raw):
        cat = unicodedata.category(ch)
        if not (cat[0] == "L" or cat == "Nd" or (cat[0] == "M" and n > 0)):     # letters, digits, and combining marks inside words
            return None, None, "Use letters and digits only (any language) - no spaces, symbols or emoji."
    return unicodedata.normalize("NFKC", raw).casefold(), raw, None


def _positive_amount(text, limit=1_000_000_000):
    t = (text or "").strip()
    return int(t) if t.isascii() and t.isdigit() and 0 < int(t) <= limit else None

async def add_redeem_start(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return ConversationHandler.END
    context.user_data.pop("redeem_type", None)
    context.user_data.pop("redeem_reward", None)
    context.user_data.pop("redeem_count", None)
    context.user_data.pop("redeem_expiry", None)
    context.user_data["redeem_rewards"] = {}
    await safe_reply_text(update.message, "1️⃣ Reward type: Character, Berrys or Stone\n(you can add several rewards to one code)")
    return REDEEM_TYPE

async def _redeem_pick_type(update, context, text):
    """Shared by the first reward and 'add another reward'. Returns the next state, or None if the text was not a valid type."""
    text = text.strip().lower()
    if text not in ("character", "berrys", "stone", "stones", "special stone", "special stones"):
        await safe_reply_text(update.message, "❌ Send Character, Berrys or Stone.")
        return None
    typ = "coins" if text == "berrys" else "character" if text == "character" else "stones"
    if typ in ("coins", "stones") and typ in context.user_data.get("redeem_rewards", {}):
        await safe_reply_text(update.message, "❌ That reward is already added. Send a different type (Character, Berrys or Stone), or done.")
        return None
    context.user_data["redeem_type"] = typ
    await safe_reply_text(update.message,
        {"character": "2️⃣ Characters: send one or more (code or name), separated by commas:",
         "coins": "2️⃣ Berrys amount:",
         "stones": "2️⃣ Special Stones amount:"}[typ]
    )
    return REDEEM_REWARD

async def add_redeem_type(update, context):
    return (await _redeem_pick_type(update, context, update.message.text)) or REDEEM_TYPE

async def add_redeem_reward(update, context):
    text = update.message.text.strip()
    typ = context.user_data["redeem_type"]
    rewards = context.user_data.setdefault("redeem_rewards", {})

    if typ == "character":
        codes, err = (await asyncio.to_thread(parse_character_list, text))
        if err:
            await safe_reply_text(update.message, err)
            return REDEEM_REWARD
        merged = list(_reward_cards(rewards.get("character")))
        for c in codes:
            if c not in merged:
                merged.append(c)
        if len(merged) > MAX_REWARD_CHARACTERS:
            await safe_reply_text(update.message, f"❌ A code can hold at most {MAX_REWARD_CHARACTERS} characters.")
            return REDEEM_REWARD
        rewards["character"] = merged
    else:
        amount = _positive_amount(text)
        if amount is None:
            await safe_reply_text(update.message, "❌ " + ("Special Stones" if typ == "stones" else "Berrys") +
                                  " amount must be a positive whole number.")
            return REDEEM_REWARD
        rewards[typ] = amount

    await safe_reply_text(update.message,
        f"✅ Added. Rewards so far:\n🎁 {(await asyncio.to_thread(format_redeem_rewards, rewards))}\n\n"
        "➕ Add another reward? Send Character, Berrys or Stone — or send done to continue.")
    return REDEEM_MORE

async def add_redeem_more(update, context):
    text = update.message.text.strip().lower()
    if text in ("done", "no", "n", "finish", "next", "skip"):
        await safe_reply_text(update.message, "3️⃣ How many users can redeem this code? Send a positive number, or 0 for unlimited users (each user can still redeem it only once):")
        return REDEEM_COUNT
    return (await _redeem_pick_type(update, context, text)) or REDEEM_MORE

async def add_redeem_count(update, context):
    text = update.message.text.strip()
    if not (text.isascii() and text.isdigit()):
        await safe_reply_text(update.message, "❌ Send a positive number, or 0 for unlimited users.")
        return REDEEM_COUNT

    context.user_data["redeem_count"] = int(text) or None      # 0 = unlimited
    await safe_reply_text(update.message,
        "4️⃣ When should this code expire? (India time)\n\n"
        "📅 Exact date and time: DD-MM-YY h:mm am/pm\n"
        "Example: 10-11-26 4:30am (10 Nov 2026, 4:30 AM)\n"
        "Example: 25-12-26 11:00pm\n\n"
        "⏱ Or a duration from now\n"
        "Examples: 24h, 7d, 2d 12h\n\n"
        "♾ Send 0 for no expiry."
    )
    return REDEEM_EXPIRY

def parse_redeem_expiry(value):
    raw = value.strip().lower()
    if raw in ("0", "never", "none", "no"):
        return None, None

    # Exact date and time (India time): DD-MM-YY h:mm am/pm  (also DD/MM/YYYY, 24-hour 16:30, "4:30 pm")
    m = re.fullmatch(r"(\d{1,2})[-/.](\d{1,2})[-/.](\d{4}|\d{2})[\s,]+(\d{1,2}):(\d{2})\s*([ap]\.?m\.?)?", raw)
    if m:
        day, month, year, hour, minute = (int(m.group(i)) for i in range(1, 6))
        ampm = (m.group(6) or "").replace(".", "")
        if year < 100:
            year += 2000
        if ampm:
            if not 1 <= hour <= 12:
                return None, "❌ Invalid time. With am/pm the hour must be 1-12, for example 10-11-26 4:30am"
            hour = hour % 12 + (12 if ampm == "pm" else 0)
        try:
            when = datetime(year, month, day, hour, minute)
        except ValueError:
            return None, "❌ Invalid date or time. Use DD-MM-YY h:mm am/pm, for example 10-11-26 4:30am"
        if when <= datetime.now() + timedelta(seconds=60):
            return None, "❌ That time has already passed (or is under 1 minute away). Send a future date and time."
        return when.isoformat(timespec="seconds"), None

    matches = re.findall(r"(\d+)\s*(d|h|m)", raw)
    if not matches:
        return None, "❌ Invalid expiry. Send a date and time like 10-11-26 4:30am, a duration like 24h, 7d or 2d 12h, or 0 for no expiry."

    normalized = re.sub(r"(\d+)\s*(d|h|m)", "", raw)
    if normalized.strip():
        return None, "❌ Invalid expiry. Send a date and time like 10-11-26 4:30am, a duration like 24h, 7d or 2d 12h, or 0 for no expiry."

    total_seconds = 0
    seen = set()
    multipliers = {"d": 86400, "h": 3600, "m": 60}
    for amount, unit in matches:
        if unit in seen:
            return None, "❌ Use each unit only once (for example: `2d 12h 30m`)."
        seen.add(unit)
        total_seconds += int(amount) * multipliers[unit]

    if total_seconds < 60:
        return None, "❌ Expiry must be at least 1 minute."

    expiry = datetime.now() + timedelta(seconds=total_seconds)
    return expiry.isoformat(timespec="seconds"), None

async def add_redeem_expiry(update, context):
    expiry, error = parse_redeem_expiry(update.message.text)
    if error:
        await safe_reply_text(update.message, error)
        return REDEEM_EXPIRY

    context.user_data["redeem_expiry"] = expiry
    await safe_reply_text(update.message,
        "5️⃣ Send a unique redeem code.\n"
        "Letters (any language) and digits, any length, mixed as you like - for example hello123. "
        "Capital and small letters count as the same code.")
    return REDEEM_CODE

async def add_redeem_code(update, context):
    code, shown, code_error = parse_code(update.message.text)
    if code_error:
        await safe_reply_text(update.message, f"❌ {code_error}")
        return REDEEM_CODE

    d = dict(context.user_data)
    _rw = d.get("redeem_rewards") or {}
    if not _rw:
        await safe_reply_text(update.message, "❌ No reward added. Start again with /addredeem.")
        context.user_data.clear()
        return ConversationHandler.END
    # first reward is also kept in the old single-reward fields
    if _rw.get("character"):
        _legacy_type, _legacy_value = "character", str(_reward_cards(_rw["character"])[0])
    elif _rw.get("coins"):
        _legacy_type, _legacy_value = "coins", str(_rw["coins"])
    else:
        _legacy_type, _legacy_value = "stones", str(_rw["stones"])
    try:
        (await asyncio.to_thread(_mc("redeem_codes_v2").insert_one, {
            "_id": code, "code": shown, "reward_type": _legacy_type, "reward_value": _legacy_value, "rewards": d["redeem_rewards"],
            "created_at": timestamp(), "active": 1, "max_claims": d["redeem_count"],
            "expires_at": d["redeem_expiry"],
        }))
    except mongo_db.DuplicateKeyError:
        await safe_reply_text(update.message, "❌ Redeem code already exists (capital and small letters count as the same code).")
        return REDEEM_CODE
    except Exception as e:
        print("Redeem creation error:", e)
        await safe_reply_text(update.message, "❌ Could not create redeem code. Please try again.")
        return REDEEM_CODE

    rw = _rw
    max_claims = d["redeem_count"]
    expiry = d["redeem_expiry"]

    if expiry:
        expiry_text = expiry.replace("T", " ") + " (local time)"
    else:
        expiry_text = "Never"

    context.user_data.clear()
    await safe_reply_text(update.message,
        f"✅ Redeem created!\n"
        f"🎟️ {shown}\n"
        f"🎁 {(await asyncio.to_thread(format_redeem_rewards, rw))}\n"
        f"👥 Limit: {(str(max_claims) + ' users') if max_claims is not None else 'Unlimited (1 per user)'}\n"
        f"⏳ Expiry: {expiry_text}"
    )
    await release_conv_log(context, update.effective_user.id, "addredeem")
    return ConversationHandler.END

async def redeem(update, context):
    (await save_user_async(update.effective_user))
    if len(context.args) != 1:
        await safe_reply_text(update.message, "Usage: /redeem CODE")
        return

    code, _shown, code_error = parse_code(context.args[0])      # case-insensitive key (Hello123 == hello123)
    if code_error:
        await safe_reply_text(update.message, "❌ Invalid redeem code. Codes contain only letters and digits.")
        return

    user_id = update.effective_user.id
    codes = _mc("redeem_codes_v2")
    claims = _mc("redeem_claims_v2")
    undo = []
    claim_id = None

    async def _rollback():
        """Take back everything already granted and release the claim, so a failure never leaves a half-redeemed code."""
        for fn in reversed(undo):
            try:
                (await asyncio.to_thread(fn))
            except Exception as undo_err:
                print("Redeem undo error:", undo_err)
        if claim_id is not None:
            try:
                (await asyncio.to_thread(claims.delete_one, {"_id": claim_id}))
            except Exception as undo_err:
                print("Redeem undo error:", undo_err)

    try:
        row = (await asyncio.to_thread(codes.find_one, {"_id": code}))
        if not row or not row.get("active"):
            await safe_reply_text(update.message, "❌ Invalid or inactive redeem code.")
            return

        rw = redeem_rewards_of(row)
        max_claims = row.get("max_claims")
        expires_at = row.get("expires_at")
        shown = row.get("code") or code             # the code as the Owner typed it (for messages)

        if expires_at:
            try:
                if datetime.now() >= datetime.fromisoformat(expires_at):
                    (await asyncio.to_thread(codes.update_one, {"_id": code}, {"$set": {"active": 0}}))
                    await safe_reply_text(update.message, "⏰ This redeem code has expired.")
                    await notify_staff_action(
                        context,
                        f"⏰ REDEEM CODE EXPIRED\n🎟️ Code: {shown}\n⏰ Expired: {expires_at.replace('T', ' ')}\n👤 Checked by: {display_user(update.effective_user)}",
                    )
                    return
            except ValueError:
                print("Invalid stored redeem expiry:", expires_at)

        if (await asyncio.to_thread(claims.find_one, {"code": code, "user_id": user_id})):
            await safe_reply_text(update.message, "⚠️ You have already redeemed this code.")
            return

        claim_count = (await asyncio.to_thread(claims.count_documents, {"code": code}))
        if max_claims is not None and claim_count >= int(max_claims):
            (await asyncio.to_thread(codes.update_one, {"_id": code}, {"$set": {"active": 0}}))
            await safe_reply_text(update.message, "🚫 This redeem code has reached its redemption limit.")
            return

        # Claim first: the unique (code, user_id) index makes a double redeem impossible.
        try:
            claim_id = (await asyncio.to_thread(claims.insert_one, {"code": code, "user_id": user_id, "claimed_at": timestamp()})).inserted_id
        except mongo_db.DuplicateKeyError:
            await safe_reply_text(update.message, "⚠️ You have already redeemed this code.")
            return

        cards = _reward_cards(rw.get("character"))
        for _c in cards:      # check every character exists before giving anything
            if not (await asyncio.to_thread(mongo_db.get_character_by_code, str(_c))):
                await _rollback()
                await safe_reply_text(update.message, "❌ This redeem reward is no longer available.")
                return

        if rw.get("coins"):
            amt = int(rw["coins"])
            if not (await asyncio.to_thread(mongo_db.add_coins, user_id, amt)):
                await _rollback()
                await safe_reply_text(update.message, "❌ User account could not be updated. Try /start first.")
                return
            undo.append(lambda amt=amt: mongo_db.add_coins(user_id, -amt))
        if rw.get("stones"):
            amt = int(rw["stones"])
            if not (await asyncio.to_thread(mongo_db.add_special_stones, user_id, amt)):
                await _rollback()
                await safe_reply_text(update.message, "❌ User account could not be updated. Try /start first.")
                return
            undo.append(lambda amt=amt: mongo_db.add_special_stones(user_id, -amt))
        for _c in cards:
            gid = (await asyncio.to_thread(mongo_db.add_collection, user_id, _c, timestamp()))
            undo.append(lambda gid=gid: mongo_db.delete_collection_by_id(gid))

        if max_claims is not None and claim_count + 1 >= int(max_claims):
            (await asyncio.to_thread(codes.update_one, {"_id": code}, {"$set": {"active": 0}}))
    except Exception as e:
        await _rollback()
        print("Redeem error:", e)
        await safe_reply_text(update.message, "❌ Redeem failed. Please try again.")
        return

    await safe_reply_text(update.message,
        f"🎉 Redeemed successfully!\n🎁 {(await asyncio.to_thread(format_redeem_rewards, rw))}"
    )
    redeem_notification = (
        f"🎟️ REDEEM CODE USED\n"
        f"🎟️ Code: {shown}\n"
        f"🎁 Reward: {(await asyncio.to_thread(format_redeem_rewards, rw))}\n"
        f"👤 Redeemed by: {display_user(update.effective_user)}"
    )
    if max_claims is not None and claim_count + 1 >= int(max_claims):
        redeem_notification += f"\n👥 Final usage: {claim_count + 1}/{max_claims}"
        redeem_notification = "🔴 REDEEM CODE LIMIT REACHED\n" + redeem_notification
    if not is_owner(user_id):
        await notify_admins(context, f"🔔 BOT NOTIFICATION\n\n{redeem_notification}", include_scouts=False)

async def delete_redeem(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    if len(context.args) != 1:
        await safe_reply_text(update.message, "Usage: /deleteredeem CODE")
        return
    code, _shown, code_error = parse_code(context.args[0])
    changed = 0 if code_error else (await asyncio.to_thread(_mc("redeem_codes_v2").update_one, {"_id": code}, {"$set": {"active": 0}})).matched_count
    code = context.args[0]
    await safe_reply_text(update.message, "✅ Redeem code disabled." if changed else "❌ Redeem code not found.")
    if changed:
        await notify_staff_action(context, f"🛑 REDEEM CODE DISABLED\n🎟️ Code: {code}\n👤 By: {display_user(update.effective_user)}", actor_id=update.effective_user.id)

async def list_redeems(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return

    codes = _mc("redeem_codes_v2")
    claims = _mc("redeem_claims_v2")
    _code_docs = await asyncio.to_thread(lambda: list(codes.find({"active": 1}).sort("created_at", -1)))
    rows = [(d.get("code") or d["_id"], redeem_rewards_of(d), d.get("max_claims"), d.get("expires_at"))
            for d in _code_docs]

    if not rows:
        pass
        await safe_reply_text(update.message, "🎟️ No active redeem codes.")
        return

    lines = ["🎟️ Active Redeem Codes:"]
    now = datetime.now()

    for code, rw, max_claims, expires_at in rows:
        if expires_at:
            try:
                if now >= datetime.fromisoformat(expires_at):
                    (await asyncio.to_thread(codes.update_one, {"_id": code}, {"$set": {"active": 0}}))
                    continue
            except ValueError:
                pass

        used = (await asyncio.to_thread(claims.count_documents, {"code": code}))

        limit_text = f"{used}/{max_claims}" if max_claims is not None else f"{used}/∞"
        expiry_text = expires_at.replace("T", " ") if expires_at else "Never"

        lines.append(
            f"• {code} → {(await asyncio.to_thread(format_redeem_rewards, rw))}\n"
            f"  👥 Redeemed: {limit_text} | ⏳ Expiry: {expiry_text}"
        )

    # (nothing to commit)

    if len(lines) == 1:
        await safe_reply_text(update.message, "🎟️ No active redeem codes.")
        return

    await safe_reply_text(update.message, "\n".join(lines))

def expire_active_spawn_locked(app, chat_id, now_dt=None):
    now_dt = now_dt or datetime.now()
    active = app.bot_data.setdefault("active_spawns", {})
    spawn = active.get(chat_id)
    if not spawn:
        return None
    expires_at = spawn.get("expires_at")
    if not isinstance(expires_at, datetime) or now_dt < expires_at:
        return None
    removed = active.pop(chat_id, None)
    if removed:
        if removed.get("spawned_by") in ("auto_spawn", "manual_spawn"):
            release_daily_character_spawn(chat_id, removed.get("code"))
        task = removed.get("expiry_task") if isinstance(removed, dict) else None
        if task is not None and not task.done() and task is not asyncio.current_task():
            task.cancel()
        app.bot_data.setdefault("next_auto_spawn_at", {})[chat_id] = (
            now_dt + timedelta(seconds=AUTO_SPAWN_INTERVAL)
        )
    return removed

def format_expiry_notice(spawn):
    return (
        "⏳ The character is gone...\n\n"
        "No one added them.\n\n"
        f"Name: {spawn.get('name', 'Unknown Character')}\n"
        f"Code: {spawn.get('code', '')}\n"
        f"Tier: {SYMBOL.get(spawn.get('rarity', ''), '⭐')} {spawn.get('rarity', '')}\n"
        f"Anime: {spawn.get('anime', '')}"
    )

async def migrate_group_data(app, old_id, new_id):
    """A group became a supergroup (new chat id): carry its approval, bot ON/OFF, auto-spawn and /gstats-hidden state to the
    new id and forget the old one. Safe to run more than once."""
    old_id, new_id = int(old_id), int(new_id)
    if old_id == new_id:
        return
    bd = app.bot_data
    approved = await asyncio.to_thread(load_approved_groups)
    states = await asyncio.to_thread(load_bot_group_states)
    auto = await asyncio.to_thread(load_auto_spawn_groups)
    hidden = await asyncio.to_thread(load_gstats_hidden_groups)
    was_approved = old_id in approved
    old_state = states.get(str(old_id))
    if was_approved:
        await asyncio.to_thread(_mongo_safe, mongo_db.set_group_approved, new_id, True)
    if old_state is not None and str(new_id) not in states:
        await asyncio.to_thread(set_bot_enabled, new_id, bool(old_state))
    if old_id in auto:
        await asyncio.to_thread(register_auto_spawn_group, new_id)
    if old_id in hidden:
        await asyncio.to_thread(hide_gstats_group, new_id)
    await asyncio.to_thread(_mongo_safe, mongo_db.cleanup_left_group, old_id)
    await asyncio.to_thread(_mongo_safe, mongo_db.sh_mark_chat_expiry_notified, old_id, india_timestamp())
    active = bd.setdefault("active_chats", set())
    active.discard(old_id)
    bd.setdefault("active_spawns", {}).pop(old_id, None)
    bd.setdefault("next_auto_spawn_at", {}).pop(old_id, None)
    if was_approved and old_state is not False:
        active.add(new_id)
    print(f"Group became a supergroup: {old_id} -> {new_id} (settings moved)")


async def group_migrated_handler(update, context):
    """Service message 'group migrated to supergroup' (seen in the old chat and in the new one)."""
    msg = update.effective_message
    chat = update.effective_chat
    if msg is None or chat is None:
        return
    old_id = getattr(msg, "migrate_from_chat_id", None)
    new_id = getattr(msg, "migrate_to_chat_id", None)
    if old_id:
        new_id = chat.id
    elif new_id:
        old_id = chat.id
    if old_id and new_id:
        await migrate_group_data(context.application, old_id, new_id)


async def send_expiry_notice(app, chat_id, spawn):
    """Tell the group that a spawned character is gone. Only temporary errors (network, flood limit) are retried; a permanent
    error (group migrated / deleted, bot removed) marks the notice as done, so it can never loop forever."""
    history_id = spawn.get("history_id")
    inflight = app.bot_data.setdefault("expiry_notice_inflight", set())
    if history_id:
        if history_id in inflight:
            return True                      # this notice is already being sent
        inflight.add(history_id)
    try:
        if history_id:
            try:
                if await asyncio.to_thread(mongo_db.sh_is_expiry_notified, history_id):
                    return True
            except Exception as e:
                print(f"Expiry notification status check error for {chat_id}: {e}")

        text = format_expiry_notice(spawn)
        for attempt in range(3):
            try:
                await asyncio.wait_for(
                    app.bot.send_message(chat_id=chat_id, text=text),
                    timeout=15,
                )
                (await asyncio.to_thread(mark_spawn_expiry_notified, history_id))
                return True
            except ChatMigrated as e:
                new_id = getattr(e, "new_chat_id", None)
                if new_id:
                    await migrate_group_data(app, chat_id, new_id)
                (await asyncio.to_thread(mark_spawn_expiry_notified, history_id))
                return True
            except (Forbidden, BadRequest) as e:
                print(f"Expiry notification dropped for {chat_id} (permanent error, not retried): {e}")
                (await asyncio.to_thread(mark_spawn_expiry_notified, history_id))
                return True
            except RetryAfter as e:
                print(f"Expiry notification flood wait for {chat_id} (attempt {attempt + 1}/3): {e}")
                if attempt < 2:
                    await asyncio.sleep(min(float(getattr(e, "retry_after", 1) or 1), 10))
            except Exception as e:
                print(f"Expiry notification error for {chat_id} (attempt {attempt + 1}/3): {e}")
                if attempt < 2:
                    await asyncio.sleep(1)
        return False
    finally:
        if history_id:
            inflight.discard(history_id)

async def restore_persisted_spawn_expiries(app):
    try:
        rows = (await asyncio.to_thread(mongo_db.sh_pending_expiry_rows))
    except Exception as e:
        print("Spawn expiry recovery query error:", e)
        return

    for history_id, chat_id, code, rarity, spawned_at, spawned_by in rows:
        try:
            if app.bot_data.setdefault("active_spawns", {}).get(chat_id):
                continue

            spawned_dt = datetime.fromisoformat(str(spawned_at))
            if spawned_dt.tzinfo is None:
                spawned_dt = spawned_dt.replace(tzinfo=INDIA_TZ)
            age = datetime.now(timezone.utc) - spawned_dt.astimezone(timezone.utc)
            remaining = SPAWN_LIFETIME - age.total_seconds()

            character = (await asyncio.to_thread(get_character_by_code, str(code)))
            if not character:
                expired = {
                    "code": code, "name": "Unknown Character",
                    "anime": "", "rarity": rarity, "worth": 0,
                    "photo": None, "history_id": history_id,
                }
            else:
                expired = {
                    "code": character[0], "name": character[1],
                    "anime": character[2], "rarity": character[3],
                    "worth": character[4], "photo": character[5],
                    "recruit_names": (await asyncio.to_thread(get_recruit_names, character[0])),
                    "history_id": history_id,
                }

            if remaining <= 0:
                await send_expiry_notice(app, chat_id, expired)
                app.bot_data.setdefault("next_auto_spawn_at", {})[chat_id] = (
                    datetime.now() + timedelta(seconds=AUTO_SPAWN_INTERVAL)
                )
                continue

            expired["expires_at"] = datetime.now() + timedelta(seconds=remaining)
            app.bot_data.setdefault("active_spawns", {})[chat_id] = expired
            expired["expiry_task"] = asyncio.create_task(
                expire_spawn_after_delay(app, chat_id, str(code)),
                name=f"spawn-expiry-recovered-{chat_id}-{code}",
            )
        except Exception as e:
            print(f"Spawn expiry recovery error for {chat_id}/{code}: {e}")

async def retry_pending_expiry_notices(app):
    try:
        rows = [r[:5] for r in (await asyncio.to_thread(mongo_db.sh_pending_expiry_rows))]
    except Exception as e:
        print("Pending expiry notification query error:", e)
        return

    now_utc = datetime.now(timezone.utc)

    # Clean-up: a notice for a spawn that ended long ago, or for a group that is not approved any more, is not worth sending.
    # Close those rows once (no message) so they are never retried.
    try:
        approved_now = await asyncio.to_thread(load_approved_groups)
        stale_ids, live_rows = [], []
        for row in rows:
            try:
                sd = datetime.fromisoformat(str(row[4]))
                if sd.tzinfo is None:
                    sd = sd.replace(tzinfo=INDIA_TZ)
                too_old = (now_utc - sd.astimezone(timezone.utc)).total_seconds() > SPAWN_LIFETIME + STALE_EXPIRY_NOTICE_SECONDS
            except Exception:
                too_old = False
            if too_old or int(row[1]) not in approved_now:
                stale_ids.append(row[0])
            else:
                live_rows.append(row)
        if stale_ids:
            await asyncio.to_thread(_mongo_safe, mongo_db.sh_mark_expiry_notified_many, stale_ids, india_timestamp())
            print(f"Closed {len(stale_ids)} old/unused expiry notice(s) without sending")
        rows = live_rows
    except Exception as e:
        print("Pending expiry clean-up error:", e)

    for history_id, chat_id, code, rarity, spawned_at in rows:
        try:
            spawned_dt = datetime.fromisoformat(str(spawned_at))
            if spawned_dt.tzinfo is None:
                spawned_dt = spawned_dt.replace(tzinfo=INDIA_TZ)
            age = now_utc - spawned_dt.astimezone(timezone.utc)
            if age < timedelta(seconds=SPAWN_LIFETIME):
                continue

            active = app.bot_data.setdefault("active_spawns", {}).get(chat_id)
            if active:
                active_code = str(active.get("code"))
                if active_code == str(code):
                    lock = get_spawn_lock(app)
                    async with lock:
                        removed = expire_active_spawn_locked(app, chat_id, datetime.now())
                    if removed:
                        await send_expiry_notice(app, chat_id, removed)
                    else:
                        continue
                else:
                    continue

            character = (await asyncio.to_thread(get_character_by_code, str(code)))
            if character:
                spawn = {
                    "code": character[0], "name": character[1],
                    "anime": character[2], "rarity": character[3],
                    "worth": character[4], "photo": character[5],
                    "history_id": history_id,
                }
            else:
                spawn = {
                    "code": code, "name": "Unknown Character",
                    "anime": "", "rarity": rarity, "worth": 0,
                    "photo": None, "history_id": history_id,
                }

            delivered = await send_expiry_notice(app, chat_id, spawn)
            if delivered:
                app.bot_data.setdefault("next_auto_spawn_at", {})[chat_id] = (
                    datetime.now() + timedelta(seconds=AUTO_SPAWN_INTERVAL)
                )
        except Exception as e:
            print(f"Pending expiry notification error for {chat_id}/{code}: {e}")

async def spawn_expiry_tick(app):
    now_dt = datetime.now()
    expired = []
    lock = get_spawn_lock(app)
    async with lock:
        active = app.bot_data.setdefault("active_spawns", {})
        for chat_id in list(active):
            try:
                removed = expire_active_spawn_locked(app, chat_id, now_dt)
                if removed:
                    expired.append((chat_id, removed))
            except Exception as e:
                print(f"Spawn expiry check error for {chat_id}: {e}")

    for chat_id, spawn in expired:
        await send_expiry_notice(app, chat_id, spawn)

    # Pending (missed) notices are a safety net: checking them every second cost hundreds of DB calls per minute.
    now_m = time.monotonic()
    if now_m - app.bot_data.get("pending_expiry_checked", -PENDING_EXPIRY_CHECK_SECONDS) >= PENDING_EXPIRY_CHECK_SECONDS:
        app.bot_data["pending_expiry_checked"] = now_m
        await retry_pending_expiry_notices(app)

async def spawn_expiry_loop(app):
    while True:
        try:
            await spawn_expiry_tick(app)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            print("Spawn expiry loop error; recovering:", e)
        await asyncio.sleep(1)

async def _auto_spawn_one_chat(app, chat_id):
    if not await is_group_approved(chat_id) or not (await asyncio.to_thread(is_bot_enabled, chat_id)):
        app.bot_data.setdefault("active_chats", set()).discard(chat_id)
        app.bot_data.setdefault("active_spawns", {}).pop(chat_id, None)
        app.bot_data.setdefault("next_auto_spawn_at", {}).pop(chat_id, None)
        (await asyncio.to_thread(unregister_auto_spawn_group, chat_id))
        return

    active_spawns = app.bot_data.setdefault("active_spawns", {})
    next_auto = app.bot_data.setdefault("next_auto_spawn_at", {})
    now_dt = datetime.now()

    spawn = active_spawns.get(chat_id)
    if spawn:
        lock = get_spawn_lock(app)
        async with lock:
            expired_spawn = expire_active_spawn_locked(app, chat_id, now_dt)
        if expired_spawn:
            await send_expiry_notice(app, chat_id, expired_spawn)
            return
        return

    if await asyncio.to_thread(group_spawn_flag, chat_id, "auto_off"):
        next_auto.pop(chat_id, None)          # automatic spawning is switched off here (/autooff)
        return

    if chat_id not in next_auto:
        next_auto[chat_id] = now_dt + timedelta(seconds=AUTO_SPAWN_INTERVAL)
        return

    if now_dt < next_auto[chat_id]:
        return

    last_activity = app.bot_data.setdefault("last_group_member_activity", {}).get(chat_id)
    if not last_activity or (now_dt - last_activity).total_seconds() > 300:
        return

    if not await bot_is_group_admin(app.bot, app, chat_id):   # no spawns until the bot is an admin
        next_auto[chat_id] = datetime.now() + timedelta(minutes=1)
        return

    # Use the normal rarity picker first so high-rank spawns still occur when allowed.
    # Emergency fallback is only used when the normal pool is exhausted.
    character = (await asyncio.to_thread(choose_character, chat_id, app=app, require_photo=True))
    if character is None:
        character = (await asyncio.to_thread(_choose_unlimited_fallback_character, chat_id=chat_id, require_photo=True))
    if character is None:
        character = (await asyncio.to_thread(_choose_unlimited_fallback_character, chat_id=chat_id, allow_recent=True, require_photo=True))

    try:
        success, reason = await asyncio.wait_for(
            spawn_reserved(chat_id, app, character, "auto_spawn"),
            timeout=45,
        )
        if not success:
            next_auto[chat_id] = datetime.now() + timedelta(minutes=1)
            if reason:
                print(f"Auto spawn retry for {chat_id}: {reason}")
            return
        next_auto.pop(chat_id, None)
    except asyncio.TimeoutError:
        next_auto[chat_id] = datetime.now() + timedelta(minutes=1)
        print(f"Auto spawn timeout for {chat_id}; retrying in 1 minute.")
    except Exception as e:
        next_auto[chat_id] = datetime.now() + timedelta(minutes=1)
        print(f"Auto spawn error for {chat_id}; retrying in 1 minute:", e)

async def event_redeem_expiry_loop(app):
    while True:
        try:
            now = datetime.now()
            notifications = []
            ev_col = _mc("events_v2")
            rc_col = _mc("redeem_codes_v2")

            expired_events = []
            for ev in await asyncio.to_thread(lambda: list(ev_col.find({"active": 1, "end_at": {"$nin": [None, ""]}}))):
                try:
                    if datetime.fromisoformat(ev["end_at"]) <= now:
                        expired_events.append((ev["_id"], ev.get("name"), ev["end_at"]))
                except (TypeError, ValueError):
                    continue
            for event_id, name, end_at in expired_events:
                if (await asyncio.to_thread(ev_col.update_one, {"_id": event_id, "active": 1}, {"$set": {"active": 0}})).modified_count:
                    notifications.append(
                        f"⏰ EVENT EXPIRED AUTOMATICALLY\n🎉 {name}\n⏰ Ended: {end_at.replace('T', ' ')}"
                    )

            expired_redeems = []
            for rc in await asyncio.to_thread(lambda: list(rc_col.find({"active": 1, "expires_at": {"$nin": [None, ""]}}))):
                try:
                    if datetime.fromisoformat(rc["expires_at"]) <= now:
                        expired_redeems.append((rc["_id"], redeem_rewards_of(rc), rc["expires_at"]))
                except (TypeError, ValueError):
                    continue
            for code, rw, expires_at in expired_redeems:
                if (await asyncio.to_thread(rc_col.update_one, {"_id": code, "active": 1}, {"$set": {"active": 0}})).modified_count:
                    notifications.append(
                        f"⏰ REDEEM CODE EXPIRED AUTOMATICALLY\n🎟️ Code: {code}\n"
                        f"🎁 Reward: {(await asyncio.to_thread(format_redeem_rewards, rw))}\n"
                        f"⏰ Expired: {expires_at.replace('T', ' ')}"
                    )
            for message in notifications:
                await notify_staff_action(app, message)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            print("Event/redeem expiry loop error:", e)
            try:
                pass
            except Exception:
                pass
        await asyncio.sleep(30)

async def auto_spawn_loop(app):
    while True:
        try:
            active_chats = app.bot_data.setdefault("active_chats", set())

            async def safe_one(chat_id):
                try:
                    await _auto_spawn_one_chat(app, chat_id)
                except asyncio.CancelledError:
                    raise
                except Exception as e:
                    print(f"Auto spawn group loop error for {chat_id}:", e)

            await asyncio.gather(
                *(safe_one(chat_id) for chat_id in list(active_chats)),
                return_exceptions=True,
            )

        except asyncio.CancelledError:
            raise
        except Exception as e:
            print("Auto spawn loop error; recovering:", e)

        try:
            await asyncio.sleep(5)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            print("Auto spawn sleep error; recovering:", e)

async def skip_conversation(update, context):
    await safe_reply_text(
        update.effective_message,
        "⚠️ This step cannot be skipped. Please send the required information "
        "or use /cancel to stop the active process."
    )
    return None

async def cancel_everything(update, context):
    """
    /cancel: stop EVERYTHING this user has in progress and return short labels of what was stopped:
    the active guided command (add/edit character, photo, issue/idea/appeal, events, redeem codes, call character,
    /addevo, /editevo ...), a pending Customize Bot input, an active Guess-the-Number game and transfer offers the user sent
    that nobody has answered yet. Finished actions (sales, evolutions, claims, accepted transfers) cannot be undone.
    """
    user = update.effective_user
    stopped = []
    if user is None:
        return stopped
    uid = user.id
    drop_conv_log(context, uid)                      # a cancelled command never gets a log prompt
    keys = set(context.user_data)
    if any(k.startswith(("evo_", "eevo_")) for k in keys):
        stopped.append("Evolution setup/edit")
    if any(not k.startswith(("evo_", "eevo_")) for k in keys):
        stopped.append("Active command (add/edit/photo/event/redeem/report)")
    context.user_data.clear()
    if _aa_waiting_min.pop(uid, None) is not None:
        stopped.append("Auto Approve minimum-members input")
    if _cw_waiting.pop(uid, None) is not None:
        stopped.append("Change Worth input")
    if _rg_state.pop(uid, None) is not None:
        stopped.append("Range Panel")
    if uid in _imp_state:
        _imp_cleanup(uid)
        stopped.append("Restore session")
    try:
        if theme.cancel_input(uid):
            stopped.append("Customize Bot input")
    except Exception as e:
        print("cancel: theme input error:", e)
    try:
        _attempts, _secret, active = (await asyncio.to_thread(get_guess_state, uid))
        if active:
            (await asyncio.to_thread(save_guess_state, uid, 0, None, False))
            stopped.append("Number-guess game (no reward)")
    except Exception as e:
        print("cancel: guess game error:", e)
    offers = [tid for tid, item in list(PENDING_TRANSFERS.items()) if item.get("sender") == uid]
    for tid in offers:
        PENDING_TRANSFERS.pop(tid, None)
    if offers:
        stopped.append(f"{len(offers)} pending transfer offer(s)")
    return stopped


async def cancel_conversation(update, context):
    stopped = await cancel_everything(update, context)
    if stopped:
        text = ("❌ Cancelled. Stopped:\n" + "\n".join(f"• {item}" for item in stopped) +
                "\n\nAnything already finished (sales, evolutions, claims, accepted transfers) cannot be undone.")
    else:
        text = "❌ Cancelled. The active process has been stopped and its temporary data cleared."
    await safe_reply_text(update.effective_message, text, reply_markup=ReplyKeyboardRemove())
    return ConversationHandler.END

# ==========================================================================
# LOG CHANNEL (Owner only) + BOT RULES
# ==========================================================================
# Log categories: name -> (title, description, commands). Commands not listed fall into "general".
LOG_CATEGORIES = {
    "character": ("Character events",
                  "Spawns, catches, adding/editing/deleting characters, gifts, collection changes",
                  {"spawn", "callcharacter", "add", "addcharacter", "addphoto", "editphoto",
                   "addevo", "editevo", "delevo", "edit", "editcharacter", "gift", "removechar", "delete", "discontinue", "continue", "clearspawn",
                   "setrange", "delrange", "editcode", "fillranges", "undocodes"}),
    "shop": ("Shop activities", "Opening and using the daily character shop", {"shop"}),
    "economy": ("Economy", "Daily rewards, Berry transfers, selling, exchanging and transferring characters, redeem codes",
                {"daily", "berrytransfer", "berry", "sell", "exchange", "transfer", "redeem"}),
    "games": ("Games", "Guess the Number", {"guess_num", "nguess"}),
    "events": ("Events & redeem codes", "Creating/ending events and managing redeem codes",
               {"event", "addevent", "endevent", "addredeem", "deleteredeem", "redeems"}),
    "moderation": ("Moderation", "Restrictions, transfer blocks, appeals, issues and ideas",
                   {"restrict", "unrestrict", "restrictions", "btransfer", "unbtransfer", "appeal", "issue", "idea"}),
    "staff": ("Staff management", "Executives, Scouts and group-approval permissions",
              {"addexec", "removeexec", "executives", "addscout", "removescout", "scout",
               "addgroupapprove", "removegroupapprove"}),
    "system": ("System logs", "Group approval, bot ON/OFF, leaving groups, status, history and broadcasts",
               {"approve", "removeapprove", "leavegroup", "autoapprove", "boton", "botoff", "spawnon", "spawnoff", "autoon", "autooff", "status",
                "history", "gstats", "setrules", "resetrules"}),
    "general": ("General", "Every other command (collection, stats, characters, view, check ...)", set()),
}
LOG_CATEGORY_OF = {cmd: cat for cat, (_t, _d, cmds) in LOG_CATEGORIES.items() for cmd in cmds}
# Owner "Category A": logged to the log channel automatically, no confirmation.
OWNER_AUTO_LOG_CATEGORIES = {"character"}
# Never logged in any way (no log entry, no security entry, no prompt) - /callcharacter is Owner-only and silent.
SILENT_LOG_COMMANDS = {"callcharacter", "cooldown", "cd", "rem"}
# When the OWNER runs one of these, the log is held and the Owner is asked Yes/No first (whatever the category).
OWNER_CONFIRM_LOG_COMMANDS = {"addredeem", "redeem"}
# Multi-step (ConversationHandler) commands: the Owner's Yes/No prompt is held back until the LAST step succeeds
# (the final step calls release_conv_log). Cancelling or failing a step never produces a prompt.
import importlib.util as _ilu
# Multi-step flows: the log entry is held until the LAST step succeeds. A flow that is cancelled, abandoned or
# times out never produces a log (pending entries are purged after CONV_LOG_TTL).
CONVERSATION_LOG_COMMANDS = {"addevent", "endevent", "addredeem", "addcharacter", "editcharacter"}
CONV_TIMEOUT = 900 if _ilu.find_spec("apscheduler") else None        # idle seconds before a flow is dropped
CONV_LOG_TTL = 1000.0
# The ONLY Owner actions that reach the log pipeline (Yes/No prompt). Everything else the Owner does is silent.
OWNER_LOG_ALLOWED = {"addcharacter", "editcharacter", "editcode", "spawn", "add"}
# Commands that are logged only when the handler explicitly calls mark_success(update).
EXPLICIT_SUCCESS_COMMANDS = {"spawn", "add", "editcode"}
LOG_MAX_CHANNELS = 10
# Extra routable "category": unauthorized-attempt (security) entries can go to their own channel.
ROUTABLE_EXTRA_CATEGORIES = {"security": "Unauthorized command / button attempts"}
# Never logged: the log/rules management commands themselves and trivial navigation commands.
# Commands that are never logged. Extend without editing code: LOG_IGNORED_EXTRA="skip,notifications"
LOG_IGNORED_COMMANDS = {
    "start", "help", "cancel", "rules",
    "setlog", "unsetlog", "log", "nolog", "logcategories", "logchannel", "addcategory", "removecategory",
    "logmap", "unlogmap", "logmappings", "logroute", "unlogroute", "logroutes", "logdefault",
    # Range commands: read-only ones are never logged; /setrange and /delrange are logged by log_range_change()
    # (Executive: Yes/No prompt after the whole action succeeded; Owner: never).
    "range", "ranges", "freecode", "freecodes", "nextcode", "setrange", "delrange", "fillranges", "undocodes",
} | {c.strip().lstrip("/").lower() for c in os.getenv("LOG_IGNORED_EXTRA", "").split(",") if c.strip()}
LOG_COMMANDS = {"setlog", "unsetlog", "log", "nolog", "logcategories", "logchannel", "addcategory", "removecategory",
                "logmap", "unlogmap", "logmappings", "logroute", "unlogroute", "logroutes", "logdefault"}
COMMAND_NAME_RE = re.compile(r"^[a-z0-9_]{1,32}$")   # Telegram command syntax
RULES_COMMANDS = {"rules", "setrules", "resetrules"}
# command -> text that replaces its arguments in the log (secrets are never copied into the channel)
LOG_MASKED_ARGS = {"redeem": "[MASKED_CODE]"}
LOG_QUEUE_MAX = 500                  # max entries buffered per log channel between flushes
LOG_BATCH_SECONDS = float(os.getenv("LOG_BATCH_SECONDS", "60"))   # 1-minute log batching window
LOG_SEND_GAP = 1.0                   # seconds between channel posts (RetryAfter from Telegram is handled below)
LOG_SEND_ATTEMPTS = 5
CATEGORY_NAME_RE = re.compile(r"^[a-z0-9_]{2,32}$")
CATEGORY_DESC_MAX = 200
_LOG_CFG = {"ts": 0.0, "val": None, "loaded": False, "gen": 0}
_LOG_CFG_TTL = 10.0
_ROLE_CACHE = {}


def _invalidate_log_cfg():
    """Drop the cached log settings NOW. The generation bump also stops a read that started before this
    write from re-populating the cache with stale data when it finishes."""
    _LOG_CFG["loaded"] = False
    _LOG_CFG["gen"] += 1


async def get_log_config():
    """
    Log settings (cached 10 s): {chat_id (None = no channel linked), title, username, set_at,
    custom_categories {name: description}, disabled_categories [names]}.
    """
    if _LOG_CFG["loaded"] and time.monotonic() - _LOG_CFG["ts"] < _LOG_CFG_TTL:
        return _LOG_CFG["val"]
    val = _LOG_CFG["val"]
    for _attempt in range(2):
        gen = _LOG_CFG["gen"]
        try:
            val = await asyncio.to_thread(mongo_db.get_log_config)
        except Exception as e:
            print("Log config load error:", e)
            return _LOG_CFG["val"]
        if gen == _LOG_CFG["gen"]:                       # nothing was written while we were reading
            _LOG_CFG.update(ts=time.monotonic(), val=val, loaded=True)
            return val
    return val                                           # still racing writes: return fresh data, cache nothing


_COMMAND_RE = re.compile(r"^/([A-Za-z0-9_]{1,32})(?:@([A-Za-z0-9_]{3,32}))?(?=\s|$)")


def _parse_command(text, bot_username=None):
    """
    ('cmd', 'args') from message text.
    (None, '') when the text is not a command OR the command is addressed to another bot
    ("/cmd@OtherBot"). "/cmd" and "/cmd@MyBotUsername" both belong to this bot.
    Pass bot_username (context.bot.username) - without it a "@target" cannot be checked and is accepted.
    """
    if not text or not text.startswith("/"):
        return None, ""
    m = _COMMAND_RE.match(text)
    if not m:
        return None, ""
    name, target = m.group(1), m.group(2)
    if target and bot_username and target.lower() != str(bot_username).lstrip("@").lower():
        return None, ""                                   # /command@OtherBot: not ours - stay completely silent
    args = text[m.end():].strip()
    return name.lower(), args


async def _role_label(user_id):
    if is_owner(user_id):
        return "Owner"
    if is_executive(user_id):
        return "Executive"
    if user_id in SCOUT_IDS:                         # in-memory, updated the moment a Scout is added/removed
        return "Scout"
    cached = _ROLE_CACHE.get(user_id)
    if cached and time.monotonic() - cached < 60:
        return "Member"                              # only "not a scout" lookups are cached
    if await asyncio.to_thread(is_scout, user_id):
        return "Scout"
    _ROLE_CACHE[user_id] = time.monotonic()
    return "Member"


def resolve_log_category(command, cfg):
    """
    Category for a command: the Owner's dynamic /logmap mapping first, then the built-in default
    (LOG_CATEGORY_OF), then "general". A mapping to a category that no longer exists is ignored.
    """
    mapped = ((cfg or {}).get("command_mappings") or {}).get(command)
    if mapped and (mapped in LOG_CATEGORIES or mapped in ((cfg or {}).get("custom_categories") or {})):
        return mapped
    return LOG_CATEGORY_OF.get(command, "general")


def resolve_log_targets(cfg, command=None, category=None):
    """
    Channel ids an entry is posted to (a list, empty when no channel is linked).
    Order of precedence: the Owner's route for the COMMAND  >  the route for its CATEGORY  >  the default channel.
    A route that points at a channel that is no longer linked is ignored.
    """
    cfg = cfg or {}
    channels = cfg.get("channels") or {}
    routes = cfg.get("routes") or {}
    for kind, key in (("commands", command), ("categories", category)):
        if not key:
            continue
        target = (routes.get(kind) or {}).get(key)
        if target is not None and str(target) in channels:
            return [int(target)]
    default = cfg.get("chat_id")
    return [int(default)] if default is not None else []


def enqueue_log_routed(app, cfg, text, command=None, category=None):
    """Queue `text` for every channel the routing rules select. Returns how many channels got it."""
    queued = 0
    for chat_id in resolve_log_targets(cfg, command, category):
        if enqueue_log(app, chat_id, text):
            queued += 1
    return queued


def build_log_text(category, role, user, chat, command, args):
    title = LOG_CATEGORIES[category][0] if category in LOG_CATEGORIES else category
    shown_args = ""
    if args:
        if command in LOG_MASKED_ARGS:
            shown_args = " " + LOG_MASKED_ARGS[command]
        else:
            shown_args = " " + args[:200] + ("…" if len(args) > 200 else "")
    where = "Private chat" if chat.type == "private" else f"{getattr(chat, 'title', None) or 'Group'} ({chat.id})"
    return (
        f"📝 {title} — {role}\n"
        f"👤 {display_user(user)}\n"
        f"💬 {where}\n"
        f"⌨️ /{command}{shown_args}\n"
        f"🕒 {log_time_text()}"
    )


def _next_batch_boundary():
    """Wall-clock time of the end of the current batching interval (next multiple of LOG_BATCH_SECONDS)."""
    step = max(1.0, LOG_BATCH_SECONDS)
    return (time.time() // step + 1) * step


def enqueue_log(app, chat_id, text):
    """
    Buffer a log entry for the log channel. Entries are NOT posted one by one: the first entry of a window
    starts a LOG_BATCH_SECONDS (default 60 s) timer, and when it expires everything collected for that chat is
    posted as one batch message, oldest first, newest at the VERY BOTTOM. Handlers never wait on Telegram.
    """
    try:
        chat_id = int(chat_id)
        buf = app.bot_data.setdefault("log_buffer", {})
        entries = buf.setdefault(chat_id, [])
        if len(entries) >= LOG_QUEUE_MAX:
            print("Log buffer full: dropped one log entry")
            return False
        entries.append((datetime.now(IST), str(text)))
        # Clock-aligned window: entries from 02:00:00 to 02:01:00 are sent together at 02:01:00.
        # Later entries join the open window; they never extend it.
        app.bot_data.setdefault("log_deadline", {}).setdefault(chat_id, _next_batch_boundary())
        return True
    except Exception as e:
        print("Log enqueue error:", e)
        return False


def _split_batch(entries):
    """
    entries: [(datetime, text)] oldest -> newest. Returns the message strings to post, in order.
    One entry is posted as-is; several become one batch message (split into numbered parts only when the
    batch would exceed Telegram's 4096-character limit). Order is never changed: newest is always last.
    """
    if not entries:
        return []
    if len(entries) == 1:
        return [entries[0][1][:4000]]
    total = len(entries)
    first, last = entries[0][0], entries[-1][0]
    span = f"{first.strftime('%I:%M:%S %p')} → {last.strftime('%I:%M:%S %p')} IST"
    sep = "\n──────────────\n"
    blocks = [f"[{i}/{total}]\n{t[:3000]}" for i, (_ts, t) in enumerate(entries, 1)]
    limit = 3700                                           # room for the header + part label
    parts, cur, cur_len = [], [], 0
    for blk in blocks:
        if cur and cur_len + len(sep) + len(blk) > limit:
            parts.append(cur)
            cur, cur_len = [], 0
        cur.append(blk)
        cur_len += len(blk) + (len(sep) if len(cur) > 1 else 0)
    if cur:
        parts.append(cur)
    messages = []
    for idx, part in enumerate(parts, 1):
        label = f" (part {idx}/{len(parts)})" if len(parts) > 1 else ""
        header = f"📦 LOG BATCH — {total} entries{label}\n🕒 {span}\n━━━━━━━━━━━━━━\n"
        messages.append(header + sep.join(part))
    return messages


async def _post_to_log_channel(app, chat_id, text):
    """Send one message to the log channel, honouring Telegram flood control. True when delivered."""
    for _attempt in range(LOG_SEND_ATTEMPTS):
        try:
            await app.bot.send_message(chat_id=chat_id, text=text[:4096], entities=copyable_ids(text[:4096]))
            return True
        except RetryAfter as e:
            delay = getattr(e, "retry_after", 5)
            delay = delay.total_seconds() if hasattr(delay, "total_seconds") else float(delay)
            print(f"Log channel rate limited: retrying in {delay + 0.5:.1f}s")
            await asyncio.sleep(delay + 0.5)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            print(f"Log channel send error ({chat_id}):", e)
            return False
    print(f"Log channel post dropped after {LOG_SEND_ATTEMPTS} rate-limited attempts ({chat_id})")
    return False


async def flush_log_buffer(app, chat_id):
    """Post everything buffered for one chat as a batch (oldest first, newest last)."""
    entries = app.bot_data.get("log_buffer", {}).pop(chat_id, [])
    app.bot_data.get("log_deadline", {}).pop(chat_id, None)
    if not entries:
        return
    cfg = await get_log_config()
    linked = {int(k) for k in ((cfg or {}).get("channels") or {})}
    if int(chat_id) not in linked:
        print(f"Log batch discarded: {chat_id} is no longer a linked log channel")
        return
    retries = app.bot_data.setdefault("log_retry", {})
    for index, message in enumerate(_split_batch(entries)):
        delivered = await _post_to_log_channel(app, chat_id, message)
        if not delivered and index == 0 and retries.get(chat_id, 0) < 3:
            retries[chat_id] = retries.get(chat_id, 0) + 1          # nothing went out: try the whole batch again
            app.bot_data.setdefault("log_buffer", {}).setdefault(chat_id, [])[0:0] = entries
            app.bot_data.setdefault("log_deadline", {})[chat_id] = time.time() + 30
            return
        if delivered:
            retries.pop(chat_id, None)
        await asyncio.sleep(LOG_SEND_GAP)


async def flush_all_log_buffers(app):
    """Flush every pending window now (used on shutdown so buffered entries are not lost)."""
    for chat_id in list(app.bot_data.get("log_buffer", {})):
        try:
            await flush_log_buffer(app, chat_id)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            print(f"Log batch flush error ({chat_id}):", e)


async def log_channel_worker(app):
    """Background timer: at the end of each 1-minute interval, post each log channel's batch."""
    app.bot_data.setdefault("log_buffer", {})
    app.bot_data.setdefault("log_deadline", {})
    while True:
        try:
            await asyncio.sleep(1.0)
            now = time.time()
            due = [cid for cid, dl in list(app.bot_data["log_deadline"].items()) if dl <= now]

            async def _flush_one(chat_id):
                try:
                    await flush_log_buffer(app, chat_id)
                except asyncio.CancelledError:
                    raise
                except Exception as e:
                    print(f"Log batch flush error ({chat_id}):", e)

            if due:                       # channels are independent: one slow channel must not delay the others
                await asyncio.gather(*(_flush_one(cid) for cid in due))
            _purge_pending_conv(app)
            _purge_cmd_state()
        except asyncio.CancelledError:
            raise
        except Exception as e:
            print("Log worker error:", e)


async def _prepare_log_entry(update, context):
    """
    Decide how a command message is logged. Returns None (nothing to log) or a dict:
      command, args, category, role, text, needs_confirmation, cfg
    Commands addressed to another bot ("/cmd@OtherBot") are never logged.
    """
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    if not msg or not user or not chat or chat.type == "channel":
        return None
    command, args = _parse_command(msg.text, getattr(context.bot, "username", None))
    if not command or command in LOG_IGNORED_COMMANDS or command in SILENT_LOG_COMMANDS:
        return None
    cfg = await get_log_config()
    if not cfg or cfg.get("chat_id") is None:
        return None
    if command not in COMMANDS and command not in (cfg.get("command_mappings") or {}):
        return None                                   # unknown commands are only logged once the Owner maps them
    category = resolve_log_category(command, cfg)
    if category in set(cfg.get("disabled_categories") or []):
        return None
    role = await _role_label(user.id)
    if role == "Owner" and command not in OWNER_LOG_ALLOWED:
        return None                                    # Owner is silent: no log, no notification, no prompt
    text = build_log_text(category, role, user, chat, command, args)
    needs_confirmation = role == "Owner"                # Owner (3 allowed actions): Yes/No. Everyone else: automatic
    return {"command": command, "args": args, "category": category, "role": role, "text": text,
            "needs_confirmation": needs_confirmation, "cfg": cfg, "chat_id": chat.id}


LOG_PROMPT_TTL = 600            # an unanswered "upload this log?" prompt expires after 10 minutes
_LOG_PROMPT_TASKS = set()


async def _expire_log_prompt(bot, token, user_id, message_id):
    """After 10 minutes: if the prompt is still unanswered, discard it and remove the message."""
    await asyncio.sleep(LOG_PROMPT_TTL)
    try:
        if await asyncio.to_thread(mongo_db.pop_log_prompt, token, user_id) is not None:
            await bot.delete_message(user_id, message_id)
    except Exception as e:
        print("Log prompt expiry error:", e)


async def _send_log_prompt(context, user_id, text, category, command, chat_id):
    """Send the Owner the Yes/No prompt (pending approval is stored in MongoDB, so it survives restarts)."""
    token = str(uuid.uuid4())
    await asyncio.to_thread(
        mongo_db.create_log_prompt, token, user_id,
        {"text": text, "category": category, "command": command, "chat_id": chat_id})
    sent = await context.bot.send_message(
        chat_id=user_id,
        text="📝 Do you want to upload this action log to the log channel?\n\n" + text,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("✅ Yes", callback_data=f"lg:y:{token}"),
            InlineKeyboardButton("❌ No", callback_data=f"lg:n:{token}"),
        ]]),
    )
    task = asyncio.create_task(_expire_log_prompt(context.bot, token, user_id, sent.message_id))
    _LOG_PROMPT_TASKS.add(task)
    task.add_done_callback(_LOG_PROMPT_TASKS.discard)


def _purge_pending_conv(app):
    pend = app.bot_data.get("pending_conv_logs")
    if not pend:
        return
    now = time.monotonic()
    for uid in [u for u, it in pend.items() if now - it.get("ts", 0) > CONV_LOG_TTL]:
        pend.pop(uid, None)
    if len(pend) > 500:
        for uid in sorted(pend, key=lambda u: pend[u].get("ts", 0))[:len(pend) - 250]:
            pend.pop(uid, None)


async def _deliver_log(context, user_id, item):
    """Owner (3 allowed actions) -> Yes/No prompt. Everyone else -> automatic post. Always routed by the rules."""
    if item.get("needs_confirmation"):
        await _send_log_prompt(context, user_id, item["text"], item["category"], item["command"], item["chat_id"])
        return
    cfg = await get_log_config()
    if cfg and cfg.get("chat_id") is not None:
        enqueue_log_routed(context.application, cfg, item["text"], item["command"], item["category"])


async def command_outcome_hook(update, context):
    """
    POST-command hook (group 60). It runs only after the command's own handler finished, and never when a gate
    (role / approval / ON-OFF / restriction) blocked the command. THE ONLY PLACE command logs are created:
      * failed / unauthorized / crashed commands (_CMD_FAILED)              -> nothing
      * spawn / add without mark_success(update)                            -> nothing
      * Owner commands other than add/edit character, /add, /spawn          -> nothing (silent)
      * multi-step commands (addcharacter, editcharacter, addevent, ...)    -> held until the LAST step succeeds
      * otherwise: Owner -> Yes/No prompt, everyone else -> automatic post.
    """
    try:
        msg, user = update.effective_message, update.effective_user
        if not msg or not user:
            return
        key = (msg.chat_id, msg.message_id)
        failed = _CMD_FAILED.pop(key, None) is not None
        ok = _CMD_OK.pop(key, None) is not None
        entry = await _prepare_log_entry(update, context)
        if not entry or failed:
            return
        if entry["command"] in EXPLICIT_SUCCESS_COMMANDS and not ok:
            return
        if entry["command"] in CONVERSATION_LOG_COMMANDS:
            _purge_pending_conv(context.application)
            context.application.bot_data.setdefault("pending_conv_logs", {})[user.id] = {
                "command": entry["command"], "text": entry["text"], "category": entry["category"],
                "chat_id": entry["chat_id"], "needs_confirmation": entry["needs_confirmation"],
                "ts": time.monotonic()}
            return
        await _deliver_log(context, user.id, entry)
    except Exception as e:
        print("Log outcome error:", e)


async def release_conv_log(context, user_id, command):
    """Called by the LAST step of a multi-step command after it succeeded."""
    try:
        item = context.application.bot_data.get("pending_conv_logs", {}).pop(user_id, None)
        if not item or item.get("command") != command or time.monotonic() - item.get("ts", 0) > CONV_LOG_TTL:
            return
        await _deliver_log(context, user_id, item)
    except Exception as e:
        print("Conversation log release error:", e)


def drop_conv_log(context, user_id):
    """Cancelled / abandoned multi-step command: forget its pending log."""
    try:
        context.application.bot_data.get("pending_conv_logs", {}).pop(user_id, None)
    except Exception:
        pass


PROMPT_EXPIRED = "⚠️ This prompt has expired or was already handled."


async def log_prompt_callback(update, context):
    query = update.callback_query
    if not (is_owner(query.from_user.id) or is_executive(query.from_user.id)):
        await deny_callback(query)
        return                                       # someone else tapping must not consume the prompt
    try:
        _, choice, token = query.data.split(":", 2)
    except ValueError:
        await query.answer(PROMPT_EXPIRED, show_alert=True)
        return
    # find_one_and_delete: only one tap can ever win, even with a double-tap or a second bot instance.
    try:
        doc = await asyncio.to_thread(mongo_db.pop_log_prompt, token, query.from_user.id)
    except Exception as e:
        print("Log prompt lookup error:", e)
        await query.answer("⚠️ Something went wrong. Please try again.", show_alert=True)
        return
    if doc is None:
        handled = None
        try:
            handled = await asyncio.to_thread(mongo_db.receipt_get, f"lg:{token}")
        except Exception as e:
            print("Log prompt receipt lookup error:", e)
        if handled is not None:                      # retried tap: the first one already succeeded
            await query.answer("✅ Already handled.")
        else:
            await query.answer(PROMPT_EXPIRED, show_alert=True)
        try:
            await query.message.delete()
        except Exception:
            pass
        return
    created = doc.get("created_at")
    if created is not None:                          # tapped after 10 minutes (e.g. the bot restarted meanwhile): expired
        created = created if created.tzinfo else created.replace(tzinfo=timezone.utc)
        if (datetime.now(timezone.utc) - created).total_seconds() > LOG_PROMPT_TTL:
            await query.answer(PROMPT_EXPIRED, show_alert=True)
            try:
                await query.message.delete()
            except Exception:
                pass
            return
    text = (doc.get("action_data") or {}).get("text", "")
    if choice == "n":
        # Discard entirely: nothing goes to the log channel, no notification, and no record is kept
        # (the pending prompt was already deleted by pop_log_prompt; no receipt is written either).
        try:
            await query.answer()
        except Exception:
            pass
        try:
            await query.message.delete()           # remove the PM prompt without a trace
        except Exception:
            pass
        return
    try:
        await asyncio.to_thread(mongo_db.receipt_put, f"lg:{token}", {"choice": choice})
    except Exception as e:
        print("Log prompt receipt save error:", e)
    cfg = await get_log_config()
    data = doc.get("action_data") or {}
    if not cfg or cfg.get("chat_id") is None:
        await query.answer("⚠️ No log channel is set.", show_alert=True)
        try:
            await query.edit_message_text("⚠️ No log channel is set, so nothing was logged.\n\n" + text)
        except Exception:
            pass
        return
    enqueue_log_routed(context.application, cfg, text, data.get("command"), data.get("category"))
    await query.answer("Logged.")
    try:
        await query.message.delete()                 # no confirmation message is left behind
    except Exception:
        pass


async def log_category_event(app, category, text):
    """
    Programmatic hook for custom categories: post `text` to the log channel if the category exists and is
    enabled. Example (future guild feature):  await log_category_event(app, "guild", "Guild X created")
    Returns True if the entry was queued.
    """
    cfg = await get_log_config()
    if not cfg or cfg.get("chat_id") is None:
        return False
    if category not in LOG_CATEGORIES and category not in (cfg.get("custom_categories") or {}):
        return False
    if category in set(cfg.get("disabled_categories") or []):
        return False
    return enqueue_log_routed(app, cfg, f"📝 {category}\n{text}", category=category) > 0


# ---- security logging: unauthorized command attempts and restricted button taps ------------------------
# Posted to the log channel (when linked) regardless of the Owner's /nolog category switches.
_SECURITY_APP = {"app": None}
_SECURITY_TASKS = set()


async def log_security_denial(app, user, chat, kind, detail=""):
    """Queue a security entry for the log channel. Never raises and never delays the handler."""
    try:
        app = app or _SECURITY_APP.get("app")
        if app is None or user is None:
            return
        cfg = await get_log_config()
        if not cfg or cfg.get("chat_id") is None:
            return
        role = await _role_label(user.id)
        if chat is None:
            where = "Unknown chat"
        elif chat.type == "private":
            where = "Private chat"
        else:
            where = f"{getattr(chat, 'title', None) or 'Group'} ({chat.id})"
        detail = (detail or "")[:200]
        text = (f"🚨 Security — Unauthorized {kind} — {role}\n"
                f"👤 {display_user(user)}\n"
                f"💬 {where}\n"
                f"⌨️ {detail}\n"
                f"🕒 {log_time_text()}")
        enqueue_log_routed(app, cfg, text, category="security")
    except Exception as e:
        print("Security log error:", e)


def _security_log_from_message(message):
    """Fire-and-forget security entry for a denied command (called from safe_reply_text)."""
    try:
        user, chat = getattr(message, "from_user", None), getattr(message, "chat", None)
        if user is None or getattr(user, "is_bot", False):
            return                                   # a bot's own message: callbacks log via deny_callback
        command, args = _parse_command(getattr(message, "text", None) or "")
        if command in SILENT_LOG_COMMANDS:
            return                                   # /callcharacter is never written to the log channel
        if command:
            args = LOG_MASKED_ARGS.get(command, args)
            detail = f"/{command}{(' ' + args) if args else ''}"
        else:
            detail = "command"
        task = asyncio.get_running_loop().create_task(log_security_denial(None, user, chat, "command", detail))
        _SECURITY_TASKS.add(task)
        task.add_done_callback(_SECURITY_TASKS.discard)
    except Exception as e:
        print("Security log schedule error:", e)


async def deny_callback(query):
    """Unified denial for a restricted button tap: alert the user and write the security log entry."""
    try:
        await query.answer(UNAUTHORIZED_TEXT, show_alert=True)
    except Exception as e:
        print("Deny answer error:", e)
    await log_security_denial(None, query.from_user, query.message.chat if query.message else None,
                              "button tap", f"button {query.data}")


# ---- log channel commands (Owner only) ------------------------------------
LOG_DENIED = UNAUTHORIZED_TEXT


async def _owner_only_log(update):
    user = update.effective_user
    if user is None or not is_owner(user.id):
        await safe_reply_text(update.effective_message, LOG_DENIED)
        return False
    return True


LOG_TARGET_TYPES = ("channel", "supergroup", "group")


def _forwarded_chat(msg):
    """
    The chat a message was forwarded from, or None.
    Modern API (PTB 21+): msg.forward_origin = MessageOriginChannel (.chat) or MessageOriginChat (.sender_chat,
    anonymous group admin). Legacy API (PTB 20.x): msg.forward_from_chat. Missing attributes never raise.
    """
    chat = None
    try:
        origin = getattr(msg, "forward_origin", None)
        if origin is not None:
            chat = getattr(origin, "chat", None) or getattr(origin, "sender_chat", None)
        if chat is None:
            chat = getattr(msg, "forward_from_chat", None)          # legacy API; may not exist on new PTB
    except Exception:
        chat = None
    return chat if chat is not None and getattr(chat, "type", None) in LOG_TARGET_TYPES else None


def _forwarded_channel(msg):
    """Backwards-compatible alias (channels and groups are both accepted as log targets)."""
    return _forwarded_chat(msg)


def _member_status(member):
    """Lower-case status string ('administrator', 'creator', ...) for str or enum values."""
    status = getattr(member, "status", "")
    return str(getattr(status, "value", status) or "").lower()


async def _log_target_from_args(context):
    """/setlog <chat_id> fallback (for channels whose messages cannot be forwarded). Returns chat or None."""
    if not context.args:
        return None
    raw = context.args[0].strip()
    if not re.fullmatch(r"-?\d{5,20}|@[A-Za-z][A-Za-z0-9_]{3,31}", raw):
        return None
    chat = await context.bot.get_chat(int(raw) if not raw.startswith("@") else raw)
    return chat if getattr(chat, "type", None) in LOG_TARGET_TYPES else None


async def setlog_command(update, context):
    """
    Link the log channel / supergroup. Ways to call it (Owner only, except step 1):
      1. /setlog inside the channel, then forward that message to the bot in private chat
      2. /setlog <chat_id>   (e.g. /setlog -1001234567890) or /setlog @publicusername
      3. /setlog inside a supergroup/group that should receive the logs (links that group)
    Linking succeeds when a real test post succeeds. get_chat_member is diagnostics only: Telegram hides
    can_post_messages for channel owners / full admins, so permission flags are never used to refuse.
    """
    msg = update.effective_message
    if msg is None:
        return
    # 1) /setlog posted inside the channel: it only explains the next step (the poster is anonymous).
    if msg.chat.type == "channel":
        try:
            await context.bot.send_message(
                chat_id=msg.chat.id,
                text="✅ Almost done. The Bot Owner must now FORWARD the /setlog message above to the bot "
                     "(in private chat) to link this channel as the log channel. "
                     "If forwarding is blocked, send /setlog " + str(msg.chat.id) + " to the bot instead.")
        except Exception as e:
            print("setlog channel reply error:", e)
        return
    if not await _owner_only_log(update):
        return
    # 2) Owner forwards that channel message to the bot, or passes a chat id / @username: bind it.
    channel = None
    try:
        channel = _forwarded_chat(msg) or await _log_target_from_args(context)
    except Exception as e:
        await safe_reply_text(msg, f"❌ I can't find that chat. Add me to it as an Administrator first.\n({e})")
        return
    # 3) /setlog (no forward, no id) sent inside a supergroup/group: that group becomes the log target.
    if channel is None and not context.args and msg.chat.type in ("supergroup", "group"):
        channel = msg.chat
    if channel is None:
        await safe_reply_text(
            msg,
            "📡 Set up the log channel:\n"
            "1. Add me to the log channel (or supergroup) as an Administrator with permission to post.\n"
            "2. Send /setlog inside that channel.\n"
            "3. Forward that /setlog message here.\n\n"
            "If forwarding is blocked, send: /setlog <chat_id>  (e.g. /setlog -1001234567890)\n"
            "For a supergroup you can also just send /setlog inside that group.\n\n"
            "You can link several log channels (max " + str(LOG_MAX_CHANNELS) + "): repeat the steps for each one. "
            "The first becomes the default; send other categories/commands to them with /logroute.")
        return
    # Diagnostics only. The only hard refusals from this lookup are "left" / "kicked": the bot is not in the chat.
    status, can_post = "unknown", None
    try:
        member = await context.bot.get_chat_member(channel.id, context.bot.id)
        status, can_post = _member_status(member), getattr(member, "can_post_messages", None)
    except Exception as e:
        print("setlog get_chat_member error:", repr(e))
    if status in ("left", "kicked"):
        await safe_reply_text(
            msg, f"❌ I'm not a member of that chat (my status: {status}). "
                 "Add me as an Administrator with permission to post, then try again.")
        return
    _invalidate_log_cfg()
    cfg_now = await get_log_config() or {}
    linked_now = cfg_now.get("channels") or {}
    if str(channel.id) not in linked_now and len(linked_now) >= LOG_MAX_CHANNELS:
        await safe_reply_text(msg, f"❌ You already have {len(linked_now)} log channels (maximum {LOG_MAX_CHANNELS}). "
                                   "Remove one with /unsetlog <chat_id> first.")
        return
    # The real test: actually post a confirmation message. Success = linked ("restricted" is judged by this too).
    try:
        await context.bot.send_message(
            chat_id=channel.id, text="✅ Log channel linked. Bot activity routed to this chat will be posted here "
                                     "(batched once every minute).")
    except Exception as e:
        await safe_reply_text(
            msg, "❌ I could not post in that chat.\n"
                 f"Telegram says: {e}\n"
                 f"My status there: {status}; can post messages: {can_post if can_post is not None else 'not reported'}.\n"
                 "Make sure I am an Administrator with the 'Post messages' permission.")
        return
    res = await asyncio.to_thread(
        mongo_db.add_log_channel, channel.id, getattr(channel, "title", "") or "",
        getattr(channel, "username", "") or "", update.effective_user.id, timestamp())
    _invalidate_log_cfg()
    name = getattr(channel, "title", None) or channel.id
    lines = [f"✅ Log channel {'updated' if res['already'] else 'added'}: {name} ({channel.id})"]
    if res["is_default"]:
        lines.append("⭐ It is the DEFAULT channel: everything without a route is posted here.")
    else:
        lines.append("ℹ️ The default channel is unchanged. Send logs here with /logroute <category|/command> "
                     f"{channel.id}, or make it the default with /logdefault {channel.id}.")
    lines.append(f"📡 Linked channels: {res['count']} (see /logchannel, /logroutes, /logcategories).")
    await safe_reply_text(msg, "\n".join(lines))


def _chan_label(cfg, chat_id):
    info = ((cfg or {}).get("channels") or {}).get(str(chat_id)) or {}
    return f"{info.get('title') or 'Unnamed'} ({chat_id})"


def _find_log_channel(cfg, raw):
    """Linked channel id from '-100123...' or '@username' (None when it is not a linked channel)."""
    raw = (raw or "").strip()
    channels = (cfg or {}).get("channels") or {}
    if re.fullmatch(r"-?\d{5,20}", raw):
        return int(raw) if str(int(raw)) in channels else None
    if raw.startswith("@"):
        for cid, info in channels.items():
            if str((info or {}).get("username") or "").lower() == raw[1:].lower():
                return int(cid)
    return None


async def unsetlog_command(update, context):
    """/unsetlog [chat_id|@username|all] - unlink one log channel (or all of them)."""
    if not await _owner_only_log(update):
        return
    msg = update.effective_message
    _invalidate_log_cfg()
    cfg = await get_log_config() or {}
    channels = cfg.get("channels") or {}
    if not channels:
        await safe_reply_text(msg, "ℹ️ No log channel is configured.")
        return
    arg = context.args[0].strip() if context.args else ""
    if arg.lower() == "all":
        res = await asyncio.to_thread(mongo_db.remove_log_channel, None)
        _invalidate_log_cfg()
        await safe_reply_text(msg, f"✅ Removed all {res['removed']} log channel(s) and their routes.")
        return
    if not arg:
        if len(channels) > 1:
            rows = "\n".join(f"• {_chan_label(cfg, cid)}{' ⭐' if int(cid) == cfg.get('chat_id') else ''}" for cid in channels)
            await safe_reply_text(msg, "Several log channels are linked. Choose one:\n" + rows +
                                       "\n\nUsage: /unsetlog <chat_id>   (or /unsetlog all)")
            return
        target = int(next(iter(channels)))
    else:
        target = _find_log_channel(cfg, arg)
        if target is None:
            await safe_reply_text(msg, "❌ That chat is not a linked log channel. See /logchannel.")
            return
    label = _chan_label(cfg, target)
    res = await asyncio.to_thread(mongo_db.remove_log_channel, target)
    _invalidate_log_cfg()
    if not res["removed"]:
        await safe_reply_text(msg, "❌ That chat is not a linked log channel. See /logchannel.")
        return
    lines = [f"✅ Log channel removed: {label}"]
    if res["routes_removed"]:
        lines.append(f"🧹 {res['routes_removed']} route(s) that pointed to it were removed (they use the default now).")
    if res["default"] is not None:
        fresh = await get_log_config() or {}
        lines.append(f"⭐ Default channel: {_chan_label(fresh, res['default'])}")
    else:
        lines.append("ℹ️ No log channel is linked any more.")
    await safe_reply_text(msg, "\n".join(lines))


async def logchannel_command(update, context):
    if not await _owner_only_log(update):
        return
    _invalidate_log_cfg()
    cfg = await get_log_config()
    channels = (cfg or {}).get("channels") or {}
    if not channels:
        await safe_reply_text(update.effective_message,
                              "ℹ️ No log channel is configured.\nUse /setlog (see /help → Owner Commands).")
        return
    off = list(cfg.get("disabled_categories") or [])
    routes = cfg.get("routes") or {}
    lines = [f"📡 Log Channels ({len(channels)})\n"]
    for cid, info in channels.items():
        info = info or {}
        handle = f"@{info['username']}" if info.get("username") else "private"
        n_cat = sum(1 for v in (routes.get("categories") or {}).values() if str(v) == str(cid))
        n_cmd = sum(1 for v in (routes.get("commands") or {}).values() if str(v) == str(cid))
        star = "⭐ DEFAULT — " if int(cid) == cfg.get("chat_id") else ""
        lines.append(f"{star}{info.get('title') or 'Unnamed'}\n    ID: {cid} · {handle}\n"
                     f"    Linked: {info.get('set_at', '?')}\n    Routes: {n_cat} categor{'y' if n_cat == 1 else 'ies'}, "
                     f"{n_cmd} command{'' if n_cmd == 1 else 's'}")
    lines.append(f"\nDisabled categories: {', '.join(off) if off else 'none'}")
    lines.append("Manage: /setlog (add) · /unsetlog <chat_id> · /logdefault <chat_id> · /logroute · /logroutes")
    await safe_reply_text(update.effective_message, "\n".join(lines))


async def logdefault_command(update, context):
    if not await _owner_only_log(update):
        return
    msg = update.effective_message
    _invalidate_log_cfg()
    cfg = await get_log_config() or {}
    target = _find_log_channel(cfg, context.args[0]) if len(context.args) == 1 else None
    if target is None:
        await safe_reply_text(msg, "Usage: /logdefault <chat_id>\nThe channel must already be linked (see /logchannel).")
        return
    if not await asyncio.to_thread(mongo_db.set_log_default, target):
        await safe_reply_text(msg, "❌ That chat is not a linked log channel.")
        return
    _invalidate_log_cfg()
    await safe_reply_text(msg, f"⭐ Default log channel is now {_chan_label(cfg, target)}.\n"
                               "Entries without a command/category route are posted there.")


def _route_key(raw, cfg):
    """('commands'|'categories', key, None) or (None, None, error text). '/craft' = a command, 'shop' = a category."""
    raw = (raw or "").strip()
    if raw.startswith("/"):
        key = _clean_command_arg(raw)
        if not COMMAND_NAME_RE.match(key):
            return None, None, "❌ Invalid command name. Use letters, digits and underscore only (e.g. /craft)."
        if key in LOG_IGNORED_COMMANDS:
            return None, None, f"❌ /{key} is on the never-log list and cannot be routed."
        return "commands", key, None
    key = raw.lower()
    valid = {n for n, _d, _c in _all_categories(cfg)} | set(ROUTABLE_EXTRA_CATEGORIES)
    if key in valid:
        return "categories", key, None
    hint = f" Did you mean the command? Use /logroute /{key} <chat_id>." if COMMAND_NAME_RE.match(key) else ""
    return None, None, (f"❌ '{raw}' is not a log category.{hint}\nCategories: {', '.join(sorted(valid))}")


async def logroute_command(update, context):
    """/logroute <category|/command> <chat_id|default>"""
    if not await _owner_only_log(update):
        return
    msg = update.effective_message
    if len(context.args) != 2:
        await safe_reply_text(msg, "Usage: /logroute <category|/command> <chat_id|default>\n"
                                   "Examples:\n/logroute economy -1001234567890   (a whole category)\n"
                                   "/logroute /daily -1001234567890   (one command; wins over its category)\n"
                                   "/logroute economy default   (back to the default channel)\n"
                                   "See /logroutes and /logchannel.")
        return
    _invalidate_log_cfg()
    cfg = await get_log_config() or {}
    if not (cfg.get("channels") or {}):
        await safe_reply_text(msg, "⚠️ No log channel is linked yet. Use /setlog first.")
        return
    kind, key, err = _route_key(context.args[0], cfg)
    if err:
        await safe_reply_text(msg, err)
        return
    shown = f"/{key}" if kind == "commands" else key
    if context.args[1].strip().lower() == "default":
        removed = await asyncio.to_thread(mongo_db.clear_log_route, kind, key)
        _invalidate_log_cfg()
        await safe_reply_text(msg, f"✅ {shown} now uses the default channel." if removed
                              else f"ℹ️ {shown} had no route (it already uses the default channel).")
        return
    target = _find_log_channel(cfg, context.args[1])
    if target is None:
        await safe_reply_text(msg, "❌ That chat is not a linked log channel. Link it with /setlog first (see /logchannel).")
        return
    try:
        previous = await asyncio.to_thread(mongo_db.set_log_route, kind, key, target)
    except ValueError:
        await safe_reply_text(msg, "❌ That chat is not a linked log channel.")
        return
    _invalidate_log_cfg()
    lines = []
    if previous is not None and str(previous) == str(target):
        lines.append(f"ℹ️ {shown} was already routed to {_chan_label(cfg, target)}.")
    elif previous is not None:
        lines.append(f"🔁 {shown}: {_chan_label(cfg, previous)} → {_chan_label(cfg, target)}")
    else:
        lines.append(f"✅ {shown} is now posted to {_chan_label(cfg, target)}.")
    if kind == "commands" and key not in known_commands(context.application) and key not in (cfg.get("command_mappings") or {}):
        lines.append(f"⚠️ /{key} is not a registered bot command; the route applies as soon as it exists (and is mapped with /logmap).")
    await safe_reply_text(msg, "\n".join(lines))


async def unlogroute_command(update, context):
    """/unlogroute <category|/command>"""
    if not await _owner_only_log(update):
        return
    msg = update.effective_message
    if len(context.args) != 1:
        await safe_reply_text(msg, "Usage: /unlogroute <category|/command>   (e.g. /unlogroute economy, /unlogroute /daily)")
        return
    _invalidate_log_cfg()
    cfg = await get_log_config() or {}
    kind, key, err = _route_key(context.args[0], cfg)
    if err:
        await safe_reply_text(msg, err)
        return
    removed = await asyncio.to_thread(mongo_db.clear_log_route, kind, key)
    _invalidate_log_cfg()
    shown = f"/{key}" if kind == "commands" else key
    await safe_reply_text(msg, f"✅ Route for {shown} removed. It uses the default channel again." if removed
                          else f"❌ No route exists for {shown}.")


async def logroutes_command(update, context):
    if not await _owner_only_log(update):
        return
    _invalidate_log_cfg()
    cfg = await get_log_config() or {}
    channels = cfg.get("channels") or {}
    if not channels:
        await safe_reply_text(update.effective_message, "ℹ️ No log channel is configured. Use /setlog.")
        return
    routes = cfg.get("routes") or {}
    lines = ["🧭 Log Routing\n", f"⭐ Default: {_chan_label(cfg, cfg.get('chat_id'))}"]
    cats = routes.get("categories") or {}
    cmds = routes.get("commands") or {}
    lines.append("\n📂 Category routes")
    lines.extend([f"• {c} → {_chan_label(cfg, t)}" for c, t in sorted(cats.items())] or ["• none"])
    lines.append("\n⌨️ Command routes (win over category routes)")
    lines.extend([f"• /{c} → {_chan_label(cfg, t)}" for c, t in sorted(cmds.items())] or ["• none"])
    lines.append("\nSet: /logroute <category|/command> <chat_id>   Remove: /unlogroute <category|/command>")
    await safe_reply_text(update.effective_message, "\n".join(lines))


def _all_categories(cfg):
    """[(name, description, is_custom)] — built-in categories first, then custom ones (alphabetical)."""
    rows = [(n, f"{t}: {d}", False) for n, (t, d, _c) in LOG_CATEGORIES.items()]
    for n, d in sorted((cfg.get("custom_categories") or {}).items()):
        rows.append((n, d, True))
    return rows


async def logcategories_command(update, context):
    if not await _owner_only_log(update):
        return
    _invalidate_log_cfg()
    cfg = await get_log_config() or {}
    off = set(cfg.get("disabled_categories") or [])
    lines = ["📂 Log Categories\n"]
    for name, desc, custom in _all_categories(cfg):
        lines.append(f"{'❌ Disabled' if name in off else '✅ Enabled'} — {name}{' (custom)' if custom else ''}\n    {desc}")
    lines.append("\nEnable: /log <category|all>   Disable: /nolog <category|all>\n"
                 "Add: /addcategory <name> <description>   Remove: /removecategory <name>")
    if cfg.get("chat_id") is None:
        lines.append("\n⚠️ No log channel is linked yet (see /setlog).")
    await safe_reply_text(update.effective_message, "\n".join(lines))


async def _set_category(update, context, enabled):
    if not await _owner_only_log(update):
        return
    cmd = "log" if enabled else "nolog"
    arg = (context.args[0].lower() if context.args else "")
    _invalidate_log_cfg()
    cfg = await get_log_config() or {}
    names = [n for n, _d, _c in _all_categories(cfg)]
    if arg != "all" and arg not in names:
        await safe_reply_text(update.effective_message,
                              f"Usage: /{cmd} <category|all>\nCategories: {', '.join(names)}")
        return
    if arg == "all":
        await asyncio.to_thread(mongo_db.set_all_log_categories, names, enabled)
    else:
        await asyncio.to_thread(mongo_db.set_log_category, arg, enabled)
    _invalidate_log_cfg()
    note = "" if cfg.get("chat_id") is not None else "\n⚠️ No log channel is linked yet (see /setlog)."
    await safe_reply_text(update.effective_message,
                          f"{'✅ Enabled' if enabled else '🔕 Disabled'} log category: {arg}{note}")


async def log_enable_command(update, context):
    await _set_category(update, context, True)


async def log_disable_command(update, context):
    await _set_category(update, context, False)


def registered_commands(app):
    """Every command that has a handler registered on the application (CommandHandler, incl. inside conversations)."""
    names = set()

    def walk(h):
        cmds = getattr(h, "commands", None)
        if cmds:
            names.update(str(c).lower() for c in cmds)
        for attr in ("entry_points", "fallbacks"):
            for x in getattr(h, attr, None) or []:
                walk(x)
        states = getattr(h, "states", None)
        if isinstance(states, dict):
            for group in states.values():
                for x in group:
                    walk(x)

    for handlers in (getattr(app, "handlers", None) or {}).values():
        for h in handlers:
            walk(h)
    return names


def known_commands(app):
    """COMMANDS (the documented list) plus anything actually registered as a handler."""
    return set(COMMANDS) | registered_commands(app)


def _op_id(msg):
    """Stable id of one Telegram message: a retried/redelivered update carries the same chat + message id."""
    try:
        return f"{msg.chat_id}:{msg.message_id}"
    except Exception:
        return None


def _clean_command_arg(raw):
    """'/Craft@mybot' -> 'craft' (leading slash and @botname stripped, lowercased)."""
    return (raw or "").strip().lstrip("/").split("@", 1)[0].lower()


async def logmap_command(update, context):
    if not await _owner_only_log(update):
        return
    msg = update.effective_message
    if len(context.args) != 2:
        await safe_reply_text(msg, "Usage: /logmap <command> <category>\n"
                                   "Example: /logmap /craft shop_v2   (the leading / is optional)\n"
                                   "See /logcategories for valid categories and /logmappings for current mappings.")
        return
    command, category = _clean_command_arg(context.args[0]), context.args[1].strip().lower()
    _invalidate_log_cfg()
    cfg = await get_log_config() or {}
    valid = {n for n, _d, _c in _all_categories(cfg)}
    # Validation 1: the category must exist (built-in or custom)
    if category not in valid:
        await safe_reply_text(msg, f"⚠️ Category '{category}' does not exist. Use /logcategories to view valid categories.")
        return
    # Validation 2: a real command name that is not on the never-log list
    if not COMMAND_NAME_RE.match(command):
        await safe_reply_text(msg, "❌ Invalid command name. Use letters, digits and underscore only (e.g. /craft).")
        return
    if command in LOG_IGNORED_COMMANDS:
        await safe_reply_text(msg, f"❌ /{command} is on the never-log list (LOG_IGNORED_COMMANDS) and cannot be mapped.")
        return
    previous, replayed = await asyncio.to_thread(
        mongo_db.set_command_mapping_op, command, category, _op_id(msg))
    if replayed:                                       # same message retried after a dropped connection: it DID succeed
        previous = None
    _invalidate_log_cfg()
    lines = []
    if previous == category:
        lines.append(f"ℹ️ /{command} was already mapped to '{category}'.")
    elif previous:
        lines.append(f"🔁 /{command} was mapped to '{previous}' — now overwritten with '{category}'.")
    else:
        lines.append(f"✅ /{command} is now logged under '{category}'.")
    if command not in known_commands(context.application):
        lines.append(f"⚠️ Warning: /{command} is not a registered bot command (no handler / not in COMMANDS). "
                     "The mapping is saved and applies as soon as the command exists.")
    await safe_reply_text(msg, "\n".join(lines))


async def unlogmap_command(update, context):
    if not await _owner_only_log(update):
        return
    msg = update.effective_message
    if len(context.args) != 1:
        await safe_reply_text(msg, "Usage: /unlogmap <command>   (e.g. /unlogmap /craft)")
        return
    command = _clean_command_arg(context.args[0])
    if not COMMAND_NAME_RE.match(command):
        await safe_reply_text(msg, "❌ Invalid command name.")
        return
    removed = await asyncio.to_thread(mongo_db.remove_command_mapping, command, _op_id(msg))
    _invalidate_log_cfg()
    if not removed:
        await safe_reply_text(msg, f"❌ No mapping exists for /{command}.")
        return
    default = LOG_CATEGORY_OF.get(command, "general")
    await safe_reply_text(msg, f"✅ Mapping for /{command} removed. It now falls back to '{default}'.")


async def logmappings_command(update, context):
    if not await _owner_only_log(update):
        return
    _invalidate_log_cfg()
    cfg = await get_log_config() or {}
    maps = cfg.get("command_mappings") or {}
    if not maps:
        await safe_reply_text(update.effective_message,
                              "🗺 No command mappings set.\nUse /logmap <command> <category> to add one.")
        return
    off = set(cfg.get("disabled_categories") or [])
    known = {n for n, _d, _c in _all_categories(cfg)}
    width = max(len(c) for c in maps) + 1
    lines = [f"🗺 Command Mappings ({len(maps)})\n"]
    for command, category in sorted(maps.items(), key=lambda kv: (kv[1], kv[0])):
        flag = " ⚠️ unknown category (ignored)" if category not in known else (" ❌ disabled" if category in off else "")
        lines.append(f"/{command.ljust(width)}→ {category}{flag}")
    lines.append("\nRemove: /unlogmap <command>")
    await safe_reply_text(update.effective_message, "\n".join(lines))


async def addcategory_command(update, context):
    if not await _owner_only_log(update):
        return
    msg = update.effective_message
    parts = (msg.text or "").split(None, 2)
    usage = ("Usage: /addcategory <name> <description>\n"
             "Name: lowercase letters, digits and underscore, 2-32 characters (e.g. guild, shop_v2).")
    if len(parts) < 3 or not parts[2].strip():
        await safe_reply_text(msg, usage)
        return
    name, desc = parts[1].lower(), " ".join(parts[2].split())
    if parts[1] != name or not CATEGORY_NAME_RE.match(name) or name == "all":
        await safe_reply_text(msg, "❌ Invalid category name. Use lowercase letters, digits and underscore only "
                                   "(2-32 characters, e.g. guild, shop_v2).")
        return
    if len(desc) > CATEGORY_DESC_MAX:
        await safe_reply_text(msg, f"❌ Description is too long ({len(desc)}). Maximum is {CATEGORY_DESC_MAX} characters.")
        return
    if name in LOG_CATEGORIES:
        await safe_reply_text(msg, f"❌ The category '{name}' already exists (built-in).")
        return
    created = await asyncio.to_thread(mongo_db.add_custom_category, name, desc, _op_id(msg))
    _invalidate_log_cfg()
    if not created:
        await safe_reply_text(msg, f"❌ The category '{name}' already exists.")
        return
    await safe_reply_text(msg, f"✅ Category '{name}' added and enabled.\n{desc}")


async def removecategory_command(update, context):
    if not await _owner_only_log(update):
        return
    msg = update.effective_message
    name = (context.args[0].lower() if context.args else "")
    if not name:
        await safe_reply_text(msg, "Usage: /removecategory <name>")
        return
    if name in LOG_CATEGORIES:
        await safe_reply_text(msg, f"❌ '{name}' is a built-in category and cannot be removed "
                                   f"(use /nolog {name} to disable it).")
        return
    if not CATEGORY_NAME_RE.match(name):
        await safe_reply_text(msg, "❌ Invalid category name.")
        return
    removed, n_maps = await asyncio.to_thread(mongo_db.remove_custom_category, name, _op_id(msg))   # cascades the mappings
    _invalidate_log_cfg()
    if not removed:
        await safe_reply_text(msg, f"❌ No custom category named '{name}'.")
        return
    extra = f"\nAlso removed {n_maps} command mapping(s) that pointed to it." if n_maps else ""
    await safe_reply_text(msg, f"✅ Category '{name}' removed.{extra}")


# ---- bot rules --------------------------------------------------------------
RULES_ROLE_DENIED = UNAUTHORIZED_TEXT
RULES_RESET_DENIED = UNAUTHORIZED_TEXT
RULES_PM_ONLY = "⚠️ This command can only be used in private messages."
RULES_MAX_CHARS = 8000


def _split_chunks(text, limit=3900):
    chunks, rest = [], text
    while len(rest) > limit:
        cut = rest.rfind("\n", 0, limit)
        if cut < limit // 2:
            cut = limit
        chunks.append(rest[:cut])
        rest = rest[cut:].lstrip("\n")
    chunks.append(rest)
    return chunks


async def _send_rules(msg, raw=False):
    """Send the bot rules to `msg`'s chat. False when no rules are set."""
    doc = await asyncio.to_thread(mongo_db.get_rules)
    if not doc:
        await safe_reply_text(msg, "📜 No bot rules have been set yet.")
        return False
    text = doc["text"]
    if raw:
        for chunk in _split_chunks(text):
            await safe_reply_text(msg, chunk)               # plain text: markdown stays visible and copyable
        return True
    chunks = _split_chunks("📜 Bot Rules\n\n" + text)
    for chunk in chunks:
        try:
            await safe_reply_text(msg, chunk, parse_mode="Markdown")
        except Exception:                                   # unbalanced markdown: fall back to plain text
            await safe_reply_text(msg, chunk)
    return True


async def rules_command(update, context):
    await _send_rules(update.effective_message, bool(context.args) and context.args[0].lower() == "noformat")


async def setrules_command(update, context):
    msg, user = update.effective_message, update.effective_user
    if user is None or not (is_owner(user.id) or is_executive(user.id)):
        await safe_reply_text(msg, RULES_ROLE_DENIED)
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(msg, RULES_PM_ONLY)
        return
    parts = (msg.text or "").split(None, 1)
    text = parts[1].strip() if len(parts) > 1 else ""
    if not text and msg.reply_to_message and msg.reply_to_message.text:
        text = msg.reply_to_message.text.strip()
    if not text:
        await safe_reply_text(msg, "Usage: /setrules <rules text>\nMarkdown is supported "
                                   "(*bold*, _italic_, `code`). Replying to a message with /setrules also works.")
        return
    if len(text) > RULES_MAX_CHARS:
        await safe_reply_text(msg, f"❌ Rules are too long ({len(text)} characters). Maximum is {RULES_MAX_CHARS}.")
        return
    await asyncio.to_thread(mongo_db.set_rules, text, user.id, timestamp())
    await safe_reply_text(msg, "✅ Bot rules updated. Everyone can view them with /rules.")


async def resetrules_command(update, context):
    msg, user = update.effective_message, update.effective_user
    if user is None or not (is_owner(user.id) or is_executive(user.id)):
        await safe_reply_text(msg, RULES_RESET_DENIED)
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(msg, RULES_PM_ONLY)
        return
    removed = await asyncio.to_thread(mongo_db.clear_rules)
    await safe_reply_text(msg, "✅ All bot rules have been cleared." if removed else "ℹ️ There were no rules set.")


# ==========================================================================
# STRICT ROLE GATE (runs before every handler group >= -89, so it covers every command handler)
#   Owner commands      -> Owner only
#   Executive commands  -> Owner, Executive
#   Scout commands      -> Owner, Executive, Scout
# The tables are derived from the same command sets that build the Telegram command menus and the help
# panels, so the menus, the help and the enforcement can never disagree.
# ==========================================================================
ROLE_OWNER, ROLE_EXEC, ROLE_SCOUT = 3, 2, 1
# /approve and /removeapprove keep their own check (Owner, or an Executive the Owner granted permission to).
ROLE_SELF_ENFORCED = {"approve", "removeapprove"}
_ROLE_TABLE = {}


def command_min_role_table():
    """{command: minimum role level}. Built lazily because the command sets are defined further down.
    Public commands (including the /executives and /scouts lists) are never in this table."""
    if not _ROLE_TABLE:
        public = set(PUBLIC_COMMANDS)
        scout = (set(SCOUT_COMMANDS) | {"notificationhistory"}) - public
        execs = set(EXECUTIVE_COMMANDS) - scout - public
        owner = set(OWNER_COMMANDS) - set(EXECUTIVE_COMMANDS) - scout - public
        table = {c: ROLE_OWNER for c in owner}
        table.update({c: ROLE_EXEC for c in execs})
        table.update({c: ROLE_SCOUT for c in scout})
        for c in ROLE_SELF_ENFORCED:
            table.pop(c, None)
        _ROLE_TABLE.update(table)
    return _ROLE_TABLE


async def role_gate(update, context):
    """Fail-closed: whatever goes wrong while replying or checking, an unauthorized command never reaches its handler."""
    msg, user = update.effective_message, update.effective_user
    if msg is None or user is None:
        return
    command, _args = _parse_command(msg.text, getattr(context.bot, "username", None))
    need = command_min_role_table().get(command) if command else None
    if not need:
        return
    uid = user.id
    allowed = is_owner(uid) or (need <= ROLE_EXEC and is_executive(uid))
    if not allowed and need <= ROLE_SCOUT:
        try:
            allowed = bool(await asyncio.to_thread(is_scout, uid))
        except Exception as e:
            print("Role gate scout lookup error:", e)
            allowed = False
    if allowed:
        return
    try:
        await safe_reply_text(msg, UNAUTHORIZED_TEXT)
    except Exception as e:
        print("Role gate reply error:", e)
    raise ApplicationHandlerStop


def register_log_and_rules_commands(app):
    for name, callback in (
        ("rules", rules_command), ("setrules", setrules_command), ("resetrules", resetrules_command),
        ("setlog", setlog_command), ("unsetlog", unsetlog_command), ("logchannel", logchannel_command),
        ("log", log_enable_command), ("nolog", log_disable_command), ("logcategories", logcategories_command),
        ("addcategory", addcategory_command), ("removecategory", removecategory_command),
        ("logmap", logmap_command), ("unlogmap", unlogmap_command), ("logmappings", logmappings_command),
        ("logroute", logroute_command), ("unlogroute", unlogroute_command), ("logroutes", logroutes_command),
        ("logdefault", logdefault_command),
    ):
        app.add_handler(CommandHandler(name, callback))
    # /setlog sent inside a channel arrives as a channel post
    app.add_handler(MessageHandler(
        filters.UpdateType.CHANNEL_POSTS & filters.Regex(r"^/setlog(@\w+)?(\s|$)"), setlog_command))
    app.add_handler(CallbackQueryHandler(log_prompt_callback, pattern=r"^lg:[yn]:"))
    # group -4: own group (only the first matching handler of a group runs); block=False never delays commands
    # group 60: runs only AFTER the command's own handler finished (gates that block a command skip it), so the
    # Owner's Yes/No log prompt is sent only for commands that completed successfully.
    app.add_handler(MessageHandler(filters.COMMAND, command_outcome_hook), group=60)


COMMANDS = {
    "start": "Start the bot",
    "help": "Show help",
    "spawn": "Spawn a character (group only)",
    "add": "Catch the spawned character (group only)",
    "mycollection": "View your collection",
    "see": "View another user's collection (/see <user_id or @username>)",
    "reply": "Send a message to the bot staff (private chat)",
    "removechar": "Remove a character from any user collection",
    "myfav": "Set favourite character",
    "mystats": "View your stats",
    "daily": "Claim daily reward",
    "dailytask": "View your daily missions",
    "characters": "List characters",
    "view": "View a character",
    "check": "Check character details and owners",
    "sell": "Sell characters (many at once: /sell naruto 2 / sakura)",
    "rem": "Delete the bot's own messages (reply to one, or /rem 10)",
    "transfer": "Transfer a character to the replied user",
    "berrytransfer": "Give Berrys by replying to a user",
    "berry": "View your daily Berry transfer status",
    "issue": "Report an issue",
    "idea": "Submit an idea",
    "appeal": "Appeal a restriction",
    "event": "View active event",
    "redeem": "Redeem a code",
    "shop": "Open the daily character shop",
    "exchange": "Exchange a character for another character of the same tier",
    "guess_num": "Start a Guess the Number game",
    "nguess": "Guess a number and win 150 Berrys",
    "cooldown": "View character cooldowns for a group (works in PM)",
    "scout": "View the Scout list",
    "scouts": "View the Scout list",
    "cancel": "Cancel current action",
    "rules": "View the bot usage rules (add 'noformat' for raw text)",

    "callcharacter": "Owner: spawn a specific character; PM asks character then Group ID (no cooldown)",
    "clearspawn": "Owner/Executive/Scout: remove a stuck active spawn (group only)",
    "gift": "Owner only: gift by reply + character code or name",
    "delete": "Owner: delete a character",
    "discontinue": "Owner: stop a character from spawning",
    "continue": "Owner: allow a discontinued character again",
    "editphoto": "Edit character photo",
    "addevo": "Owner/Executive: add an evolution",
    "editevo": "Owner/Executive: edit an evolution",
    "delevo": "Owner: delete an evolution recipe",
    "evolution": "View all evolution recipes",
    "evolve": "Evolve a character",
    "item": "View your items (inventory)",
    "about": "About this bot",
    "stone": "Stone leaderboard",
    "stonetask": "View your daily stone tasks",
    "claimstone": "Claim your completed task stones",
    "addcharacter": "Add a character",
    "editcharacter": "Edit a character",
    "addlist": "Character add/edit ranking",
    "executives": "View the Executive list",
    "addexec": "Owner: add executive",
    "removeexec": "Owner: remove executive",
    "addscout": "Owner/Executive: add Scout",
    "removescout": "Owner/Executive: remove Scout",
    "addevent": "Owner: create an event",
    "endevent": "Owner: end the event",
    "addredeem": "Owner: create a redeem code",
    "deleteredeem": "Owner: disable a redeem code",
    "redeems": "Owner: list redeem codes",
    "history": "Owner: spawn history",
    "approve": "Owner/trusted Executive: approve a group (PM: /approve <group_chat_id>)",
    "spawncooldown": "Owner: personal /spawn cooldown of members and Scouts in one group (/spawncooldown <minutes> [group_id], reset)",
    "removeapprove": "Owner/trusted Executive: remove group approval (PM: /removeapprove <group_chat_id>)",
    "addgroupapprove": "Owner: give an Executive group approval permission",
    "removegroupapprove": "Owner: remove an Executive's group approval permission",
    "leavegroup": "Owner: remove a group and make the bot leave it (PM: /leavegroup <group_chat_id>)",
    "autoapprove": "Owner: auto-approve new groups (/autoapprove on|off|min <number>, alone = status)",
    "dm": "Owner/Executive: open the DM menu, or /dm <user_id or @username> <message> (PM only)",
    "dmhistory": "Owner/Executive: read your chat with a user (/dmhistory <user_id or @username>, PM only)",
    "dmall": "Owner: send one message to every member's PM (PM only; or reply to a message with /dmall)",
    "boton": "Owner/Executive: turn bot ON (PM: /boton <group_chat_id>)",
    "botoff": "Owner/Executive: turn bot OFF (PM: /botoff <group_chat_id>)",
    "spawnoff": "Owner/Executive: turn /spawn OFF in a group (PM: /spawnoff <group_chat_id>)",
    "spawnon": "Owner/Executive: turn /spawn ON in a group (PM: /spawnon <group_chat_id>)",
    "autooff": "Owner/Executive: turn automatic spawning OFF in a group (PM: /autooff <group_chat_id>)",
    "autoon": "Owner/Executive: turn automatic spawning ON in a group (PM: /autoon <group_chat_id>)",
    "status": "Owner: bot status and active spawns",
    "gstats": "Owner: list groups where bot is added",
    "restrict": "Owner/Executive: restrict by reply or user ID + duration + optional reason",
    "unrestrict": "Owner/Executive: remove restriction by reply or user ID",
    "restrictions": "View your restriction (Owner/Executive: all active restrictions)",
    "notifications": "PM: Your personal staff notification ON/OFF",
    "notificationoff": "Owner/Executive/Scout: turn your own PM notifications OFF",
    "notificationon": "Owner/Executive/Scout: turn your own PM notifications ON",
    "notificationhistory": "Owner/Executive/Scout: view your personal notification history",
    "btransfer": "Owner/Executive: block transfer between two user IDs",
    "unbtransfer": "Owner/Executive: remove transfer block between two user IDs",
    "setrules": "Owner/Executive: set the bot usage rules (PM only)",
    "resetrules": "Owner/Executive: clear all bot usage rules (PM only)",
    "setlog": "Owner: link a log channel - repeat to add more (send in the channel, then forward it here)",
    "unsetlog": "Owner: unlink a log channel (/unsetlog <chat_id> or all)",
    "logchannel": "Owner: show all linked log channels",
    "logdefault": "Owner: choose the default log channel (/logdefault <chat_id>)",
    "logroute": "Owner: send a category or command to a channel (/logroute <category|/command> <chat_id>)",
    "unlogroute": "Owner: remove a log route (/unlogroute <category|/command>)",
    "logroutes": "Owner: show the default channel and all log routes",
    "log": "Owner: enable a log category",
    "nolog": "Owner: disable a log category",
    "logcategories": "Owner: list log categories (built-in + custom) and their status",
    "addcategory": "Owner: add a custom log category (/addcategory <name> <description>)",
    "removecategory": "Owner: remove a custom log category (/removecategory <name>)",
    "logmap": "Owner: log a command under a category (/logmap <command> <category>)",
    "unlogmap": "Owner: remove a command's log mapping (/unlogmap <command>)",
    "logmappings": "Owner: list command -> log category mappings",
    "setrange": "Owner/Executive: set or update an anime's code range (/setrange <anime> <start> <end>)",
    "delrange": "Owner/Executive: delete an anime's code range (/delrange <anime>)",
    "range": "Owner/Executive: show all code ranges, or one anime (/range <anime>)",
    "freecode": "Owner/Executive: show used and free codes (all anime, or /freecode <anime>)",
    "nextcode": "Owner/Executive: show the next free code (/nextcode [anime] [count])",
    "editcode": "Owner/Executive: change a character's code directly (/editcode <code/name> <new code>)",
    "fillranges": "Owner/Executive: move every character into its anime's code range (/fillranges [anime])",
    "undocodes": "Owner/Executive: undo the last /fillranges or range shift",
    "exportdb": "Owner: send the whole database as zip file(s) to your PM (/exportdb [collections])",
    "importdb": "Owner: restore the database from /exportdb zip files (/importdb [collections])",
}
COMMANDS.update(badge_banner.COMMAND_DESCRIPTIONS)
COMMANDS.update(rewards.COMMAND_DESCRIPTIONS)
COMMANDS.update(security.COMMAND_DESCRIPTIONS)

PUBLIC_COMMANDS = badge_banner.PUBLIC_COMMANDS | rewards.PUBLIC_COMMANDS | {
    "executives", "scouts", "scout",
    "start", "help", "spawn", "add", "mycollection", "see", "myfav", "mystats", "addlist",
    "daily", "characters", "view", "check", "sell", "rem", "transfer", "issue", "idea",
    "appeal", "restrictions", "cancel", "event", "redeem", "berrytransfer", "berry",
    "shop", "exchange", "guess_num", "nguess", "rules",
    "evolution", "evolve", "item", "stone", "stonetask", "claimstone", "about", "dailytask",
}

PRIVATE_ONLY_COMMANDS = {"reply"}      # shown in the command menu of private chats only, never in groups

MENU_HIDDEN_COMMANDS = {"spawnon", "spawnoff", "autoon", "autooff"}    # work and are logged, but are not listed in Telegram's "/" menu

def make_bot_commands(names):
    return badge_banner.fit_command_menu([BotCommand(name, COMMANDS[name]) for name in names if name in COMMANDS and name not in MENU_HIDDEN_COMMANDS])   # Telegram: max 100

async def refresh_group_command_menu(bot, chat_id, user_id):
    from telegram import BotCommandScopeChatMember
    (await asyncio.to_thread(is_scout, user_id))
    if is_owner(user_id):
        names=PUBLIC_COMMANDS | OWNER_COMMANDS | EXECUTIVE_COMMANDS | SCOUT_COMMANDS
    elif is_executive(user_id):
        names=PUBLIC_COMMANDS | EXECUTIVE_COMMANDS
        if (await asyncio.to_thread(has_group_approval_permission, user_id)):
            names |= {"approve", "removeapprove"}
    elif (await asyncio.to_thread(is_scout, user_id)):
        names=PUBLIC_COMMANDS | SCOUT_COMMANDS
    else:
        names=PUBLIC_COMMANDS
    try:
        await bot.set_my_commands(make_bot_commands(sorted(names)), scope=BotCommandScopeChatMember(chat_id=chat_id, user_id=user_id))
    except Exception as e:
        print(f"Group command menu refresh error for {user_id} in {chat_id}:", e)

async def refresh_command_menu(bot, user_id):
    from telegram import BotCommandScopeChat
    (await asyncio.to_thread(is_scout, user_id))
    if is_owner(user_id):
        names = PUBLIC_COMMANDS | OWNER_COMMANDS | EXECUTIVE_COMMANDS | SCOUT_COMMANDS
    elif is_executive(user_id):
        names = PUBLIC_COMMANDS | EXECUTIVE_COMMANDS | PRIVATE_ONLY_COMMANDS
        if (await asyncio.to_thread(has_group_approval_permission, user_id)):
            names |= {"approve", "removeapprove"}
    elif (await asyncio.to_thread(is_scout, user_id)):
        names = PUBLIC_COMMANDS | SCOUT_COMMANDS | PRIVATE_ONLY_COMMANDS
    else:
        names = PUBLIC_COMMANDS | PRIVATE_ONLY_COMMANDS
    try:
        await bot.set_my_commands(
            make_bot_commands(sorted(names)),
            scope=BotCommandScopeChat(chat_id=user_id),
        )
    except Exception as e:
        print(f"Command menu refresh error for {user_id}:", e)

# ---------------------------------------------------------------------------------------------------
# PERFORMANCE DIAGNOSTICS: tells you (in the Render logs) what makes the bot slow.
#   🐢 SLOW UPDATE  a command/button took longer than SLOW_UPDATE_MS (default 1500): name, time, DB share, delay before it started
#   🐢 SLOW DB      one MongoDB call took longer than SLOW_DB_MS (default 300)
#   🧊 EVENT LOOP   the bot froze for longer than LOOP_LAG_MS (default 300): something ran without waiting
#   📈 PERF         a summary line every PERF_REPORT_SECONDS (default 300)
# ---------------------------------------------------------------------------------------------------
SLOW_UPDATE_MS = int(os.getenv("SLOW_UPDATE_MS", "1500"))
LOOP_LAG_MS = int(os.getenv("LOOP_LAG_MS", "300"))
PERF_REPORT_SECONDS = max(30, int(os.getenv("PERF_REPORT_SECONDS", "300")))
_perf = {"durations": [], "behind_max": 0.0, "loop_max": 0.0}


def _perf_label(update):
    try:
        query = getattr(update, "callback_query", None)
        if query is not None:
            return "button " + ":".join((query.data or "").split(":")[:2])
        msg = update.effective_message
        text = (getattr(msg, "text", None) or getattr(msg, "caption", None) or "")
        if text.startswith("/"):
            return text.split()[0].split("@")[0][:40]
        return "message"
    except Exception:
        return "update"


def install_perf_monitor():
    """Times every update (class-level wrapper, same technique as install_bot_message_tracker)."""
    from telegram.ext import Application
    original = Application.process_update
    if getattr(original, "_perf_timed", False):
        return

    async def timed(self, update):
        stats = {"ms": 0.0, "n": 0}
        token = mongo_db.db_stats_var.set(stats)
        started = time.perf_counter()
        behind = None
        try:
            msg = getattr(update, "message", None)
            if msg is not None and getattr(msg, "date", None) is not None:
                behind = max(0.0, time.time() - msg.date.timestamp())      # Telegram -> bot -> start of handling
        except Exception:
            pass
        try:
            return await original(self, update)
        finally:
            elapsed = (time.perf_counter() - started) * 1000.0
            try:
                mongo_db.db_stats_var.reset(token)
                durations = _perf["durations"]
                if len(durations) < 5000:
                    durations.append(elapsed)
                if behind is not None:
                    _perf["behind_max"] = max(_perf["behind_max"], behind)
                if elapsed >= SLOW_UPDATE_MS:
                    chat = getattr(update, "effective_chat", None)
                    where = getattr(chat, "type", "?") if chat is not None else "?"
                    extra = f" | started {behind:.1f}s after it was sent" if behind is not None else ""
                    print(f"🐢 SLOW UPDATE {elapsed / 1000:.1f}s | {_perf_label(update)} | {where} | "
                          f"DB {stats['ms'] / 1000:.1f}s in {stats['n']} calls{extra}")
            except Exception:
                pass

    timed._perf_timed = True
    Application.process_update = timed


async def loop_lag_monitor():
    """Wakes up every 0.25 s; if it wakes up late, something blocked the bot's event loop."""
    interval = 0.25
    while True:
        before = time.perf_counter()
        await asyncio.sleep(interval)
        lag = (time.perf_counter() - before - interval) * 1000.0
        _perf["loop_max"] = max(_perf["loop_max"], lag)
        if lag >= LOOP_LAG_MS:
            print(f"🧊 EVENT LOOP BLOCKED for {lag:.0f} ms (the whole bot froze for that long)")


async def perf_report_loop():
    while True:
        await asyncio.sleep(PERF_REPORT_SECONDS)
        try:
            durations = sorted(_perf["durations"])
            db = mongo_db.pop_db_perf()
            if durations or db["calls"]:
                n = len(durations)
                avg = sum(durations) / n if n else 0.0
                p95 = durations[min(n - 1, int(n * 0.95))] if n else 0.0
                avg_db = db["ms"] / db["calls"] if db["calls"] else 0.0
                print(f"📈 PERF last {PERF_REPORT_SECONDS // 60} min | updates {n}: avg {avg:.0f} ms, p95 {p95:.0f} ms, "
                      f"max {(durations[-1] if n else 0):.0f} ms | DB calls {db['calls']}: avg {avg_db:.0f} ms, max {db['max']:.0f} ms | "
                      f"worst loop freeze {_perf['loop_max']:.0f} ms | worst delay before handling {_perf['behind_max']:.1f}s")
            _perf["durations"] = []
            _perf["behind_max"] = 0.0
            _perf["loop_max"] = 0.0
        except Exception as e:
            print("Perf report error:", e)


async def startup_init(app):
    _SECURITY_APP["app"] = app
    app.bot_data["perf_tasks"] = [
        asyncio.create_task(loop_lag_monitor(), name="loop-lag-monitor"),
        asyncio.create_task(perf_report_loop(), name="perf-report"),
    ]
    # asyncio's default pool is only min(32, cpu+4) threads (5 on a 1-vCPU host): size it for DB calls.
    asyncio.get_running_loop().set_default_executor(
        ThreadPoolExecutor(max_workers=DB_THREADS, thread_name_prefix="db"))
    app.bot_data.setdefault("bot_off_warning_sent", set())
    restored_active = app.bot_data.setdefault("active_chats", set())
    for restored_chat_id in (await asyncio.to_thread(load_auto_spawn_groups)):
        try:
            if await is_group_approved(restored_chat_id) and (await asyncio.to_thread(is_bot_enabled, restored_chat_id)):
                restored_active.add(restored_chat_id)
        except Exception as e:
            print(f"Auto-spawn group restore error for {restored_chat_id}: {e}")

    try:
        (await asyncio.to_thread(reconcile_group_character_spawn_counts))
    except Exception as e:
        print("Group character reservation recovery error:", e)

    await restore_persisted_spawn_expiries(app)

    if not app.bot_data.get("background_jobs_scheduled"):
        app.bot_data["background_jobs_scheduled"] = True

        app.bot_data["spawn_expiry_task"] = asyncio.create_task(
            spawn_expiry_loop(app),
            name="spawn-expiry-loop",
        )
        app.bot_data["auto_spawn_task"] = asyncio.create_task(
            auto_spawn_loop(app),
            name="auto-spawn-loop",
        )

        # Event/redeem expiry is a never-ending loop: run it as a plain asyncio task (like the
        # other loops) so it works with or without JobQueue and is cancelled cleanly on shutdown.
        app.bot_data["log_worker_task"] = asyncio.create_task(
            log_channel_worker(app), name="log-channel-worker")

        app.bot_data["event_redeem_task"] = asyncio.create_task(
            event_redeem_expiry_loop(app),
            name="event-redeem-expiry-loop",
        )

        app.bot_data["deleted_sweep_task"] = asyncio.create_task(
            deleted_account_sweep_loop(app),
            name="deleted-account-sweep-loop",
        )

        app.bot_data["dm_cleanup_task"] = asyncio.create_task(dm_cleanup(), name="dm-cleanup")   # DM messages: keep 5 days

        if app.job_queue is not None:
            app.job_queue.run_daily(
                daily_shop_reset_job,
                time=dt_time(4, 0, tzinfo=IST),
                name="daily-shop-reset",
            )
        else:
            print("⚠️ JobQueue is unavailable (install python-telegram-bot[job-queue]); using an asyncio fallback for the 04:00 IST shop reset.")
            app.bot_data["shop_reset_task"] = asyncio.create_task(
                _daily_shop_reset_fallback_loop(app),
                name="daily-shop-reset-fallback",
            )

    try:
        await app.bot.set_my_commands(
            make_bot_commands(sorted(PUBLIC_COMMANDS)),
            scope=BotCommandScopeDefault(),
        )
    except Exception as e:
        print("Default command menu setup error:", e)
    try:                                              # private chats also get the private-only commands (/reply)
        await app.bot.set_my_commands(make_bot_commands(sorted(PUBLIC_COMMANDS | PRIVATE_ONLY_COMMANDS)),
                                      scope=BotCommandScopeAllPrivateChats())
    except Exception as e:
        print("Private command menu setup error:", e)

    async def _refresh_staff_menus():
        try:
            staff_ids = set(int(uid) for uid in EXECUTIVE_IDS)
            staff_ids.update(int(uid) for uid in SCOUT_IDS)
            staff_ids.add(int(ADMIN_IDS[0])) if ADMIN_IDS else None

            try:
                for uid, role in (await asyncio.to_thread(_staff_role_rows)):
                    staff_ids.add(int(uid))
                    if role == "scout" and int(uid) not in SCOUT_IDS and int(uid) not in EXECUTIVE_IDS and not is_owner(int(uid)):
                        SCOUT_IDS.append(int(uid))
            except Exception as e:
                print("Staff menu lookup error:", e)

            for uid in sorted(staff_ids):
                await refresh_command_menu(app.bot, uid)

            groups = (await asyncio.to_thread(load_bot_groups))
            for chat_id_text in groups:
                try:
                    chat_id = int(chat_id_text)
                except (TypeError, ValueError):
                    continue
                for uid in sorted(staff_ids):
                    await refresh_group_command_menu(app.bot, chat_id, uid)
        except Exception as e:
            print("Staff command suggestion refresh error:", e)

    app.bot_data["staff_menu_task"] = asyncio.create_task(
        _refresh_staff_menus(),
        name="staff-menu-refresh",
    )

async def _daily_shop_reset_fallback_loop(app):
    """Only used when JobQueue is missing: run daily_shop_reset_job at 04:00 IST."""
    while True:
        try:
            now = datetime.now(IST)
            nxt = now.replace(hour=4, minute=0, second=0, microsecond=0)
            if nxt <= now:
                nxt += timedelta(days=1)
            await asyncio.sleep(max(1.0, (nxt - now).total_seconds()))
            await daily_shop_reset_job(None)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            print("Shop reset fallback loop error; recovering:", e)
            await asyncio.sleep(60)

async def post_shutdown(app):
    try:                                              # do not lose entries still waiting in the 1-minute window
        await asyncio.wait_for(flush_all_log_buffers(app), timeout=15)
    except Exception as e:
        print("Log buffer shutdown flush error:", e)
    for key, label in (
        ("spawn_expiry_task", "Spawn expiry"),
        ("auto_spawn_task", "Auto-spawn"),
        ("event_redeem_task", "Event/redeem expiry"),
        ("deleted_sweep_task", "Deleted-account sweep"),
        ("log_worker_task", "Log channel worker"),
        ("shop_reset_task", "Shop reset"),
        ("staff_menu_task", "Staff menu refresh"),
    ):
        task = app.bot_data.get(key)
        if task is not None and not task.done():
            task.cancel()
            try:
                await task
            except asyncio.CancelledError:
                pass
            except Exception as e:
                print(f"{label} shutdown error:", e)

UNAPPROVED_GROUP_WARNING_HEAD = (
    "🚫 Bot is OFF in this group.\n"
    "⚠️ Owner approval is mandatory before any bot function can work here.\n"
    "❌ Spawn, catch, sell, transfer, daily, callbacks and other bot actions are blocked.\n\n"
    "👑 Only the Owner can approve this group with /approve."
    "\n🔴 After approval, Owner can use /boton or /botoff to control the bot."
)

GATE_WARNING_COOLDOWN = float(os.getenv("GATE_WARNING_COOLDOWN", "60"))   # seconds between notices in one chat


def _known_command_names(app):
    """Every command name this bot really handles (documented lists + registered handlers). Cached."""
    cached = app.bot_data.get("_known_command_names")
    if cached is None:
        cached = {str(c).lower() for c in known_commands(app)}
        cached |= set(PUBLIC_COMMANDS) | PRIVATE_ONLY_COMMANDS | set(OWNER_COMMANDS) | set(EXECUTIVE_COMMANDS) | set(SCOUT_COMMANDS)
        app.bot_data["_known_command_names"] = cached
    return cached


def _warning_allowed(app, chat_id, interval=None, message_id=None):
    """
    May a "Bot is OFF" / "Not approved" notice be sent now?
      * at most ONE notice per triggering message (message_id is remembered, so a duplicated/redelivered update
        or a second gate cannot answer the same message twice);
      * at most one notice per chat every GATE_WARNING_COOLDOWN seconds (a burst of commands = one notice).
    """
    now = time.monotonic()
    if message_id is not None:
        seen = app.bot_data.setdefault("warning_msg_ids", {})
        key = (str(chat_id), int(message_id))
        if key in seen:
            return False
        if len(seen) > 200:
            for old in [k for k, t in seen.items() if now - t > 600]:
                seen.pop(old, None)
        if len(seen) > 2000:
            seen.clear()
        seen[key] = now
    sent = app.bot_data.setdefault("warning_last_sent", {})
    if len(sent) > 500:
        for old in [k for k, t in sent.items() if now - t > 3600]:
            sent.pop(old, None)
    previous = sent.get(str(chat_id), 0.0)
    limit = GATE_WARNING_COOLDOWN if interval is None else interval
    if previous and now - previous < limit:
        return False
    sent[str(chat_id)] = now
    return True


async def block_unapproved_group(update, context):
    """
    Group/approval/ON-OFF gate (runs before every other handler).
    It only reacts to commands that are meant for THIS bot ("/cmd" or "/cmd@MyBotUsername"):
      * plain text, media, and commands for other bots ("/cmd@OtherBot")  -> ignored, never answered, never blocked
      * a command in a not-approved / OFF group -> the command is blocked, and the notice is sent only when the
        command is one of ours, at most once per message and once per cooldown window.
    """
    msg = update.effective_message
    chat = update.effective_chat
    text = (msg.text or "") if msg else ""
    command_name, _args = _parse_command(text, getattr(context.bot, "username", None))

    if command_name in SILENT_OWNER_COMMANDS and not (update.effective_user and is_owner(update.effective_user.id)):
        raise ApplicationHandlerStop         # /cooldown and /cd: anyone but the Owner is ignored, no reply at all

    if not chat or chat.type not in ("group", "supergroup"):
        if command_name in RESTRICTED_COMMANDS:
            restricted = await get_restricted_message(update)
            if restricted:
                await safe_reply_text(msg, restricted)
                raise ApplicationHandlerStop
        return

    if not command_name:
        return                                   # not a command for us: stay silent

    user = update.effective_user
    approved, enabled = await group_gate(chat)
    known = _known_command_names(context.application)

    if not approved:
        if command_name == "approve" and user and (await asyncio.to_thread(has_group_approval_permission, user.id)):
            return
        if command_name in known and msg is not None and _warning_allowed(
                context.application, chat.id, message_id=msg.message_id):
            try:
                await safe_reply_text(msg, await build_unapproved_group_text(
                    context.bot, context.application, chat.id, UNAPPROVED_GROUP_WARNING_HEAD), parse_mode="HTML")
            except Exception as e:
                print("Unapproved warning error:", e)
        raise ApplicationHandlerStop

    if not enabled and command_name not in ("boton", "approve", "removeapprove"):
        if command_name not in known:
            return
        if msg is not None and _warning_allowed(context.application, chat.id, message_id=msg.message_id):
            try:
                await safe_reply_text(msg, "🔴 Bot is OFF in this group.\n👑 Owner/Executive can turn it ON with /boton.")
            except Exception as e:
                print("Bot OFF warning error:", e)
        raise ApplicationHandlerStop

    if command_name in RESTRICTED_COMMANDS:
        restricted = await get_restricted_message(update)
        if restricted:
            try:
                await safe_reply_text(msg, restricted)
            except Exception as e:
                print("Restriction warning error:", e)
            raise ApplicationHandlerStop


async def block_unapproved_callback(update, context):
    query = update.callback_query
    chat = query.message.chat if query and query.message else None
    if query is not None and (query.data or "").startswith(RESTRICTED_CALLBACK_PREFIXES):
        restricted = await get_restricted_message(update)      # restricted members cannot accept transfers / exchanges
        if restricted:
            try:
                await query.answer(restricted[:200], show_alert=True)
            except Exception:
                pass
            raise ApplicationHandlerStop
    if not chat or chat.type not in ("group", "supergroup"):
        return
    if not await is_group_approved(chat.id):
        try:
            await query.answer("This group is not approved by the Owner.", show_alert=True)
        except Exception:
            pass
        try:
            if _warning_allowed(context.application, chat.id):          # taps never spam the group
                await safe_reply_text(query.message, await build_unapproved_group_text(
                    context.bot, context.application, chat.id, UNAPPROVED_GROUP_WARNING_HEAD), parse_mode="HTML")
        except Exception:
            pass
        raise ApplicationHandlerStop
    if not (await asyncio.to_thread(is_bot_enabled, chat.id)):
        try:
            await query.answer("Bot is OFF in this group. Owner can use /boton.", show_alert=True)
        except Exception:
            pass
        raise ApplicationHandlerStop

# ---------------------------------------------------------------------------------------------------
# HUMAN-ONLY USAGE RULE: bot accounts and channels can never use this bot.
# One central gate (handler group -300, runs before every other handler); humans (private chats and
# groups, including anonymous group admins) pass through untouched.
# ---------------------------------------------------------------------------------------------------
HUMAN_ONLY_TEXT = "\u274c Bots and channels are not allowed to access this bot."


def _human_only_sender_kind(update):
    """'bot' / 'channel' when the actual requester is a bot account or a channel, else None (human)."""
    if update.channel_post is not None or update.edited_channel_post is not None:
        return "channel"
    msg = update.message or update.edited_message
    if msg is not None:
        sender_chat = getattr(msg, "sender_chat", None)
        if sender_chat is not None:
            chat = getattr(msg, "chat", None)
            if getattr(sender_chat, "type", None) in ("group", "supergroup") and chat is not None \
                    and sender_chat.id == chat.id:
                return None            # anonymous group admin: a human posting as the group itself
            return "channel"           # "send as channel" posts in groups
        if getattr(msg, "is_automatic_forward", None):
            return "channel"           # linked-channel post auto-forwarded into the discussion group
        user = getattr(msg, "from_user", None)
        return "bot" if user is not None and getattr(user, "is_bot", False) else None
    query = update.callback_query or update.inline_query
    user = getattr(query, "from_user", None) if query is not None else None
    return "bot" if user is not None and getattr(user, "is_bot", False) else None


async def human_only_gate(update, context):
    kind = _human_only_sender_kind(update)
    if kind is None:
        return
    # Existing logging system exemption: any log command (/setlog, /logroute, /logmap, ... = LOG_COMMANDS) is
    # passed on untouched to the existing handlers and their own Owner/permission checks (e.g. /setlog posted
    # inside a channel). The text is parsed WITHOUT the bot username on purpose: the existing channel
    # /setlog handler accepts "/setlog@AnyName", so this must too.
    _msg = update.effective_message
    if _msg is not None and update.callback_query is None and update.inline_query is None:
        _cmd, _args = _parse_command(_msg.text)
        if _cmd in LOG_COMMANDS:
            return
    # Notify only when it is really an attempt to USE the bot (a command for this bot, a button/inline
    # request, or any message in a private chat). Other bot/channel chatter is dropped silently so
    # groups are never spammed and two bots can never answer each other in a loop.
    try:
        if update.callback_query is not None:
            await update.callback_query.answer(HUMAN_ONLY_TEXT, show_alert=True)
        elif update.inline_query is not None:
            await update.inline_query.answer([], cache_time=0)
        else:
            msg = update.effective_message
            chat = update.effective_chat
            if msg is not None and chat is not None:
                command, _args = _parse_command(msg.text or msg.caption, getattr(context.bot, "username", None))
                if command or chat.type == "private":
                    await context.bot.send_message(chat_id=chat.id, text=HUMAN_ONLY_TEXT)
    except Exception as e:
        print("Human-only gate reply error:", e)
    raise ApplicationHandlerStop


async def restrict(update, context):
    uid = update.effective_user.id
    if not (is_owner(uid) or is_executive(uid)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return

    import re
    args = [str(a).strip() for a in context.args]
    target = update.message.reply_to_message.from_user if update.message.reply_to_message else None
    reason = ""

    if target:
        if not args:
            await safe_reply_text(update.message, "Usage: reply to a user with /restrict <duration> [reason]\nExamples: /restrict 1h spammer, /restrict 10h repeated spam")
            return
        duration_text = args[0].lower()
        reason = " ".join(args[1:]).strip()
    else:
        if len(args) < 2 or not args[0].isdigit():
            await safe_reply_text(update.message, "Usage: /restrict <user_id> <duration> [reason] or reply to a user with /restrict <duration> [reason]")
            return
        target_id = int(args[0])
        duration_text = args[1].lower()
        reason = " ".join(args[2:]).strip()
        target_name = str(target_id)
        target_username = ""
        try:
            row_lookup = (await asyncio.to_thread(mongo_db.get_user_names, target_id))
            if row_lookup:
                first, last, uname = row_lookup
                target_name = " ".join(v for v in [first, last] if v).strip() or target_name
                target_username = uname or ""
        except Exception:
            pass
        target = type("T", (), {"id": target_id, "first_name": target_name, "username": target_username, "is_bot": False})()

    m = re.fullmatch(r"([1-9]\d{0,3})([hd])", duration_text)
    if not m:
        await safe_reply_text(update.message, "❌ Invalid duration. Use 1h, 10h, 1d or 365d.")
        return
    amount, unit = int(m.group(1)), m.group(2)
    seconds = amount * (3600 if unit == "h" else 86400)
    if seconds > 365 * 86400:
        await safe_reply_text(update.message, "❌ Maximum restriction is 365 days.")
        return
    if target.id == uid:
        await safe_reply_text(update.message, "❌ You cannot restrict yourself.")
        return
    if is_owner(target.id):
        await safe_reply_text(update.message, "❌ The Owner cannot be restricted.")
        return
    if is_executive(target.id) and not is_owner(uid):
        await safe_reply_text(update.message, "❌ Only the Owner can restrict an Executive.")
        return

    now_ts = int(datetime.now().timestamp())
    new_label = f"{amount}{unit}"
    expiry = now_ts + seconds
    data = (await asyncio.to_thread(load_restrictions))
    old = data.get(str(target.id))
    old = old if isinstance(old, dict) and int(old.get("expiry", 0)) > now_ts else None     # an active restriction is being changed
    old_label = (old.get("duration") or "") if old else ""
    if old and not reason:
        reason = str(old.get("reason") or "").strip()          # no new reason typed: keep the old one
    entry = {
        "expiry": expiry,
        "duration": new_label,
        "reason": reason,
        "restricted_by": uid,
        "restricted_by_name": update.effective_user.first_name or "Unknown",
        "restricted_by_username": update.effective_user.username or "",
        "target_name": target.first_name or "Unknown",
        "target_username": getattr(target, "username", "") or "",
        "created_at": now_ts,
    }
    if old_label:
        entry["previous_duration"] = old_label
    data[str(target.id)] = entry
    (await asyncio.to_thread(save_restrictions, data))

    by_label = restricted_by_label(entry)
    reason_shown = reason or "Not provided"
    if old:
        old_secs = _duration_seconds(old_label)
        if old_secs is None:
            old_secs = max(0, int(old.get("expiry", 0)) - now_ts)
        if seconds < old_secs:
            head, verb = "✅ Your restriction was reduced.", "reduced"
        elif seconds > old_secs:
            head, verb = "⚠️ Your restriction was extended.", "extended"
        else:
            head, verb = "🔄 Your restriction was renewed.", "renewed"
        pm_text = (f"{head}\n{old_label or '?'} → {new_label}\n⏳ Time left: {new_label}\n"
                   f"📝 Reason: {reason_shown}\n👮 Restricted by: {by_label}")
        reply_text = (f"🔒 {target.first_name}'s restriction changed: {old_label or '?'} → {new_label}.\n"
                      f"📝 Reason: {reason_shown}")
    else:
        verb = "restricted"
        pm_text = ("🚫 You have been restricted.\n"
                   f"⏳ Duration: {new_label}\n📝 Reason: {reason_shown}\n👮 Restricted by: {by_label}\n"
                   "Think it's a mistake? Use /appeal")
        reply_text = f"🔒 {target.first_name} restricted for {new_label}.\n📝 Reason: {reason_shown}"
    sent = await notify_restricted_user(context, target.id, pm_text)
    await safe_reply_text(update.message, reply_text + ("" if sent else "\n⚠️ Couldn't notify the user."))
    target_handle = f"@{getattr(target, 'username', '')}" if getattr(target, 'username', '') else "No username"
    await notify_staff_action(
        context,
        f"{'🔄 USER RESTRICTION CHANGED (' + (old_label or '?') + ' → ' + new_label + ')' if old else '🔒 USER RESTRICTED'}\n"
        f"👤 User: {target.first_name} | ID: {target.id} | {target_handle}\n"
        f"⏳ Duration: {new_label}\n"
        f"📝 Reason: {reason or 'Not provided'}\n"
        f"👮 Restricted by: {display_user(update.effective_user)}",
        actor_id=update.effective_user.id,
    )

async def restrictions_list(update, context):
    uid = update.effective_user.id
    if not (is_owner(uid) or is_executive(uid)):
        # Normal members: only their own restriction details.
        expiry, info = await asyncio.to_thread(_restriction_lookup, uid)
        if not expiry:
            await safe_reply_text(update.effective_message, "✅ You are not restricted.")
            return
        info = info if isinstance(info, dict) else {}
        await safe_reply_text(update.effective_message,
            "🔒 Your Restriction\n"
            f"⏳ Duration: {info.get('duration') or 'Unknown'}{(' (was ' + info['previous_duration'] + ')') if info.get('previous_duration') else ''}"
            f" | Remaining: {format_remaining(expiry - int(datetime.now().timestamp()))}\n"
            f"📝 Reason: {str(info.get('reason') or '').strip() or 'Not provided'}\n"
            f"👮 Restricted by: {restricted_by_label(info)}\n"
            "Think it's a mistake? Use /appeal")
        return

    data = (await asyncio.to_thread(load_restrictions))
    active = []
    now = int(datetime.now().timestamp())
    changed = False
    for target_id, entry in list(data.items()):
        expiry = int(entry.get("expiry", 0)) if isinstance(entry, dict) else int(entry)
        if expiry <= now:
            data.pop(target_id, None)
            changed = True
            continue
        active.append((int(target_id), entry, expiry))
    if changed:
        (await asyncio.to_thread(save_restrictions, data))

    if not active:
        await safe_reply_text(update.message, "🔒 No users are currently restricted.")
        return

    active.sort(key=lambda item: item[2])
    lines = ["🔒 CURRENT RESTRICTIONS\n"]
    for target_id, entry, expiry in active:
        if isinstance(entry, dict):
            name = entry.get("target_name") or "Unknown"
            username = entry.get("target_username") or ""
            duration = (entry.get("duration") or "Unknown") + (f" (was {entry['previous_duration']})" if entry.get("previous_duration") else "")
            reason = entry.get("reason") or "Not provided"
            by_name = entry.get("restricted_by_name") or "Unknown"
            by_username = entry.get("restricted_by_username") or ""
            by_id = entry.get("restricted_by") or "Unknown"
        else:
            name, username, duration, reason = "Unknown", "", "Legacy", "Not recorded"
            by_name, by_username, by_id = "Unknown", "", "Unknown"
        handle = f"@{username}" if username else "No username"
        by_handle = f"@{by_username}" if by_username else "No username"
        lines.append(
            f"👤 {name} ({handle})\n"
            f"🆔 ID: {target_id}\n"
            f"⏳ Duration: {duration} | Remaining: {format_remaining(expiry - now)}\n"
            f"📝 Reason: {reason}\n"
            f"👮 Restricted by: {by_name} ({by_handle}) | ID: {by_id}\n"
        )
    await safe_reply_text(update.message, "\n".join(lines))

async def unrestrict(update, context):
    uid = update.effective_user.id
    if not (is_owner(uid) or is_executive(uid)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return

    args = [str(a).strip() for a in context.args]
    target = update.message.reply_to_message.from_user if update.message.reply_to_message else None

    if target:
        if args:
            await safe_reply_text(update.message, "Usage: reply to a user with /unrestrict")
            return
        target_id = target.id
        target_name = target.first_name
    else:
        if len(args) != 1 or not args[0].isdigit():
            await safe_reply_text(update.message, "Usage: /unrestrict <user_id> or reply to a user with /unrestrict")
            return
        target_id = int(args[0])
        target_name = str(target_id)

    data = (await asyncio.to_thread(load_restrictions))
    if str(target_id) not in data:
        (await asyncio.to_thread(get_restriction_expiry, target_id))
        data = (await asyncio.to_thread(load_restrictions))
        if str(target_id) not in data:
            await safe_reply_text(update.message, "ℹ️ This user is not currently restricted.")
            return

    if is_executive(target_id) and not is_owner(uid):
        await safe_reply_text(update.message, "❌ Only the Owner can lift an Executive's restriction.")
        return
    removed_entry = data.get(str(target_id), {})
    data.pop(str(target_id), None)
    (await asyncio.to_thread(save_restrictions, data))
    sent = await notify_restricted_user(context, target_id,
        "🔓 Your restriction has been lifted.\nYou can use the bot normally again.")
    await safe_reply_text(update.message,
        f"🔓 User {target_name} restriction removed successfully.\n"
        f"🆔 User ID: {target_id}" + ("" if sent else "\n⚠️ Couldn't notify the user.")
    )
    removed_name = target_name
    removed_username = ""
    removed_reason = "Not recorded"
    if isinstance(removed_entry, dict):
        removed_name = removed_entry.get("target_name") or removed_name
        removed_username = removed_entry.get("target_username") or ""
        removed_reason = removed_entry.get("reason") or "Not provided"
    removed_handle = f"@{removed_username}" if removed_username else "No username"
    await notify_staff_action(
        context,
        f"🔓 USER RESTRICTION REMOVED\n"
        f"👤 User: {removed_name} | ID: {target_id} | {removed_handle}\n"
        f"📝 Original reason: {removed_reason}\n"
        f"👮 Removed by: {display_user(update.effective_user)}",
        actor_id=update.effective_user.id,
    )

async def notifications_command(update, context):
    uid = update.effective_user.id
    if not (is_owner(uid) or is_executive(uid) or (await asyncio.to_thread(is_scout, uid))):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(update.effective_message, "Use this in your Bot PM: /notifications, /notifications on or /notifications off")
        return

    if len(context.args) != 1 or context.args[0].lower() not in ("on", "off"):
        state = "ON" if (await asyncio.to_thread(notifications_enabled_for, uid)) else "OFF"
        await safe_reply_text(
            update.effective_message,
            f"🔔 Your staff PM notifications are currently {state}.\n\n"
            "Use: /notifications on\n"
            "or: /notifications off",
        )
        return

    enabled = context.args[0].lower() == "on"
    (await asyncio.to_thread(set_notifications_enabled_for, uid, enabled))
    await safe_reply_text(
        update.effective_message,
        "🟢 Your staff PM notifications are now ON." if enabled
        else "🔴 Your staff PM notifications are now OFF.",
    )

async def notificationoff_command(update, context):
    uid = update.effective_user.id
    if not (is_owner(uid) or is_executive(uid) or (await asyncio.to_thread(is_scout, uid))):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(update.effective_message, "Use /notificationoff in your Bot PM.")
        return
    (await asyncio.to_thread(set_notifications_enabled_for, uid, False))
    await safe_reply_text(update.effective_message, "🔴 Your staff PM notifications are now OFF.")

async def notificationon_command(update, context):
    uid = update.effective_user.id
    if not (is_owner(uid) or is_executive(uid) or (await asyncio.to_thread(is_scout, uid))):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    if update.effective_chat.type != "private":
        await safe_reply_text(update.effective_message, "Use /notificationon in your Bot PM.")
        return
    (await asyncio.to_thread(set_notifications_enabled_for, uid, True))
    await safe_reply_text(update.effective_message, "🟢 Your staff PM notifications are now ON.")

async def scout_list_command(update, context):
    """Public: every user can view the Scout list (/scouts, alias /scout)."""
    rows = await asyncio.to_thread(_staff_rows, list(SCOUT_IDS))
    await safe_reply_text(update.effective_message, format_staff_list("Scouts", rows), parse_mode="HTML")

EXECUTIVE_COMMANDS = {
    "addcharacter", "addphoto", "editphoto", "editcharacter", "edit", "addevo", "editevo", "restrict", "unrestrict",
    "clearspawn", "boton", "botoff", "spawnon", "spawnoff", "autoon", "autooff", "addscout", "removescout", "notifications", "notificationoff", "notificationon", "notificationhistory",
    "btransfer", "unbtransfer", "setrules", "resetrules", "dm", "dmhistory",
    "setrange", "delrange", "range", "ranges", "freecode", "freecodes", "nextcode",      # anime code ranges (Owner + Executive)
    "editcode",                                                                          # change a character's code directly
    "fillranges", "undocodes",                                                           # move characters into their ranges / undo that
} | badge_banner.STAFF_COMMANDS
SCOUT_COMMANDS = {
    "addcharacter", "addphoto", "editphoto", "editcharacter", "edit", "clearspawn", "notifications", "notificationoff", "notificationon",
}
def register_executive_commands(app):
    app.add_handler(CommandHandler(["editphoto", "addphoto"], addphoto))   # /addphoto = hidden alias of /editphoto
    app.add_handler(CommandHandler(["scouts", "scout"], scout_list_command))
    app.add_handler(CommandHandler("restrict", restrict))
    app.add_handler(CommandHandler("unrestrict", unrestrict))
    app.add_handler(CommandHandler("setrange", setrange_command))
    app.add_handler(CommandHandler("delrange", delrange_command))
    app.add_handler(CommandHandler(["range", "ranges"], range_command))
    app.add_handler(CommandHandler(["freecode", "freecodes"], freecode_command))
    app.add_handler(CommandHandler("nextcode", nextcode_command))
    app.add_handler(CommandHandler("editcode", editcode_command))
    app.add_handler(CommandHandler("fillranges", fillranges_command))
    app.add_handler(CommandHandler("undocodes", undocodes_command))
    app.add_handler(CommandHandler("restrictions", restrictions_list))
    app.add_handler(CommandHandler("botoff", bot_off))
    app.add_handler(CommandHandler("spawnoff", spawn_off_command))
    app.add_handler(CommandHandler("spawnon", spawn_on_command))
    app.add_handler(CommandHandler("autooff", auto_off_command))
    app.add_handler(CommandHandler("autoon", auto_on_command))
    app.add_handler(CommandHandler("notifications", notifications_command))
    app.add_handler(CommandHandler("notificationoff", notificationoff_command))
    app.add_handler(CommandHandler("notificationon", notificationon_command))
    app.add_handler(CommandHandler("notificationhistory", notification_history_command))
    app.add_handler(CallbackQueryHandler(bc_callback, pattern=r"^bc:"))
    app.add_handler(CallbackQueryHandler(dm_callback, pattern=r"^dm:"))
    app.add_handler(CallbackQueryHandler(reply_cancel_callback, pattern=r"^um:x$"))
    app.add_handler(CommandHandler("dm", dm_command))
    app.add_handler(CommandHandler("dmhistory", dmhistory_command))
    app.add_handler(CommandHandler("dmall", dmall_command))
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & ~filters.COMMAND & ~filters.StatusUpdate.ALL, dm_message), group=103)
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & ~filters.COMMAND & ~filters.StatusUpdate.ALL, bc_message), group=102)
    app.add_handler(CommandHandler("btransfer", block_transfer_pair))
    app.add_handler(CommandHandler("unbtransfer", unblock_transfer_pair))
    app.add_handler(CommandHandler("clearspawn", clearspawn))

    edit_conv = ConversationHandler(
        entry_points=[
            CommandHandler(["editcharacter", "edit"], editcharacter),   # /edit = short alias
            CallbackQueryHandler(character_selection_callback, pattern=r"^charselect:edit:"),
        ],
        states={
            EDIT_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, edit_name), CommandHandler("skip", edit_name)],
            EDIT_RECRUIT: [MessageHandler(filters.TEXT & ~filters.COMMAND, edit_recruit), CommandHandler("skip", edit_recruit)],
            EDIT_ANIME: [MessageHandler(filters.TEXT & ~filters.COMMAND, edit_anime), CommandHandler("skip", edit_anime)],
            EDIT_RARITY: [MessageHandler(filters.TEXT & ~filters.COMMAND, edit_rarity), CommandHandler("skip", edit_rarity)],
            EDIT_WORTH: [MessageHandler(filters.TEXT & ~filters.COMMAND, edit_worth), CommandHandler("skip", edit_worth)],
            EDIT_CODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, edit_code), CommandHandler("skip", edit_code)],
        },
        fallbacks=[CommandHandler("cancel", cancel_conversation), CommandHandler("skip", skip_conversation)],
        allow_reentry=True,
        conversation_timeout=CONV_TIMEOUT,
    )
    app.add_handler(edit_conv)

    add_conv = ConversationHandler(
        entry_points=[CommandHandler("addcharacter", addcharacter_start)],
        states={
            ADD_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, addcharacter_name)],
            ADD_RECRUIT: [MessageHandler(filters.TEXT & ~filters.COMMAND, addcharacter_recruit), MessageHandler(filters.Regex(r"^⏭ Skip$"), addcharacter_recruit), CommandHandler("skip", addcharacter_recruit)],
            ADD_ANIME: [MessageHandler(filters.TEXT & ~filters.COMMAND, addcharacter_anime), MessageHandler(filters.Regex(r"^⏭ Skip$"), addcharacter_anime), CommandHandler("skip", addcharacter_anime)],
            ADD_RARITY: [MessageHandler(filters.TEXT & ~filters.COMMAND, addcharacter_rarity)],
            ADD_WORTH: [MessageHandler(filters.TEXT & ~filters.COMMAND, addcharacter_worth), CommandHandler("skip", addcharacter_worth)],
            ADD_CODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, addcharacter_code)],
            ADD_PHOTO: [MessageHandler(filters.PHOTO, addcharacter_photo), MessageHandler(filters.Regex(r"^⏭ Skip$"), addcharacter_photo), CommandHandler("skip", addcharacter_photo)],
        },
        fallbacks=[CommandHandler("cancel", cancel_conversation), CommandHandler("skip", skip_conversation)],
        allow_reentry=True,
        conversation_timeout=CONV_TIMEOUT,
    )
    app.add_handler(add_conv)

OWNER_COMMANDS = {
    "delevo", "callcharacter", "clearspawn", "gift", "delete", "discontinue", "continue",
    "addexec", "removeexec", "addscout", "removescout",
    "addevent", "endevent", "addredeem", "deleteredeem", "redeems", "history",
    "approve", "removeapprove", "addgroupapprove", "removegroupapprove", "leavegroup", "autoapprove", "removechar", "boton", "dm", "dmhistory", "dmall",
    "status", "gstats", "cooldown", "cd", "spawncooldown", "notifications", "notificationoff", "notificationon",
    "notificationhistory",
    "setrules", "resetrules", "setlog", "unsetlog", "logchannel", "log", "nolog", "logcategories",
    "addcategory", "removecategory", "logmap", "unlogmap", "logmappings",
    "logroute", "unlogroute", "logroutes", "logdefault", "exportdb", "importdb",
} | rewards.OWNER_COMMANDS | security.OWNER_COMMANDS       # security.py: /bangroup /unbangroup ...  # /addfestival /festivals /editfestival /delfestival /addquest /editquest /delquest
OWNER_COMMANDS = OWNER_COMMANDS | EXECUTIVE_COMMANDS | SCOUT_COMMANDS      # Owner section lists everything (gating unchanged)

def register_owner_commands(app):
    app.add_handler(CommandHandler("removechar", removechar))
    app.add_handler(CommandHandler("gift", gift))
    app.add_handler(CommandHandler("delete", delete))
    app.add_handler(CommandHandler("deleteuser", deleteuser))
    app.add_handler(CommandHandler("finduser", finduser))
    app.add_handler(CommandHandler("restoreuser", restoreuser))
    app.add_handler(CommandHandler("moveuser", moveuser))
    app.add_handler(CommandHandler("exportdb", exportdb_command))
    app.add_handler(CommandHandler("importdb", importdb_command))
    app.add_handler(CallbackQueryHandler(importdb_callback, pattern=r"^imp:"))
    app.add_handler(MessageHandler(filters.Document.ALL & filters.ChatType.PRIVATE, importdb_file), group=54)
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE, importdb_confirm_text), group=55)
    app.add_handler(CallbackQueryHandler(data_confirm_callback, pattern=r"^dconf:(go|no):[0-9a-f]{10}$"))
    app.add_handler(CommandHandler("discontinue", discontinue_command))
    app.add_handler(CommandHandler("continue", continue_command))
    app.add_handler(CommandHandler("executives", executives))
    app.add_handler(CommandHandler("addexec", addexec))
    app.add_handler(CommandHandler("removeexec", removeexec))
    app.add_handler(CommandHandler("addscout", addscout))
    app.add_handler(CommandHandler("removescout", removescout))
    app.add_handler(CommandHandler("history", history))
    app.add_handler(CommandHandler("status", status))
    app.add_handler(CallbackQueryHandler(callchar_confirm_callback, pattern=r"^cc:[0-9a-f]{8}:[yn]$"))
    app.add_handler(CallbackQueryHandler(status_refresh_callback, pattern=r"^status:refresh$"))
    app.add_handler(CallbackQueryHandler(cooldown_refresh_callback, pattern=r"^cd:r:(all|-?\d+)$"))
    app.add_handler(CommandHandler("gstats", gstats))
    app.add_handler(CommandHandler("approve", approve_group))
    app.add_handler(CommandHandler("spawncooldown", spawncooldown_command))
    app.add_handler(CallbackQueryHandler(approve_group_button, pattern=r"^apvg:-?\d+$"))
    app.add_handler(CommandHandler("removeapprove", remove_approval))
    app.add_handler(CommandHandler("addgroupapprove", add_group_approval_permission))
    app.add_handler(CommandHandler("removegroupapprove", remove_group_approval_permission))
    app.add_handler(CommandHandler("leavegroup", leave_group))
    app.add_handler(CommandHandler("autoapprove", autoapprove_command))
    app.add_handler(CallbackQueryHandler(auto_approve_callback, pattern=r"^aa:"))
    app.add_handler(CallbackQueryHandler(group_link_callback, pattern=r"^gl:-?\d+$"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE, auto_approve_min_input), group=51)
    app.add_handler(CommandHandler("boton", bot_on))

    call_conv = ConversationHandler(
        entry_points=[
            CommandHandler("callcharacter", callchar_start),
            CallbackQueryHandler(character_selection_callback, pattern=r"^charselect:callchar:"),
        ],
        states={
            CALLCHAR_CHARACTER: [MessageHandler(filters.TEXT & ~filters.COMMAND, callchar_character_step)],
            CALLCHAR_GROUP: [MessageHandler(filters.TEXT & ~filters.COMMAND, callchar_group_step)],
        },
        fallbacks=[CommandHandler("cancel", cancel_conversation), CommandHandler("skip", skip_conversation)],
        allow_reentry=True,
    )
    app.add_handler(call_conv)

    event_conv = ConversationHandler(
        entry_points=[CommandHandler("addevent", add_event_start)],
        states={
            EVENT_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_name)],
            EVENT_CODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_code)],
            EVENT_BERRYS: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_berrys)],
            EVENT_STONES: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_stones)],
            EVENT_CHAR: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_char)],
            EVENT_TRIGGER: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_trigger)],
            EVENT_LIMIT: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_limit)],
            EVENT_END_DAY: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_end_day)],
            EVENT_END_MONTH: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_end_month)],
            EVENT_END_YEAR: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_end_year)],
            EVENT_END_HOUR: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_end_hour)],
            EVENT_END_MINUTE: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_end_minute)],
        },
        fallbacks=[CommandHandler("cancel", cancel_conversation), CommandHandler("skip", skip_conversation)],
        allow_reentry=True,
        conversation_timeout=CONV_TIMEOUT,
    )
    app.add_handler(event_conv)

    redeem_conv = ConversationHandler(
        entry_points=[CommandHandler("addredeem", add_redeem_start)],
        states={
            REDEEM_TYPE: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_redeem_type)],
            REDEEM_REWARD: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_redeem_reward)],
            REDEEM_MORE: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_redeem_more)],
            REDEEM_COUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_redeem_count)],
            REDEEM_EXPIRY: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_redeem_expiry)],
            REDEEM_CODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_redeem_code)],
        },
        fallbacks=[CommandHandler("cancel", cancel_conversation), CommandHandler("skip", skip_conversation)],
        allow_reentry=True,
        conversation_timeout=CONV_TIMEOUT,
    )
    app.add_handler(redeem_conv)
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("endevent", end_event_start)],
        states={END_EVENT_CODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, end_event_confirm)]},
        fallbacks=[CommandHandler("cancel", cancel_conversation), CommandHandler("skip", skip_conversation)],
        allow_reentry=True,
        conversation_timeout=CONV_TIMEOUT,
    ))
    app.add_handler(CommandHandler("deleteredeem", delete_redeem))
    app.add_handler(CommandHandler("redeems", list_redeems))

def _keepalive_loop(url, interval):
    """
    Render's free web service sleeps after ~15 minutes without INBOUND HTTP traffic. This thread requests the
    service's own public URL every `interval` seconds (default 10 minutes), which Render counts as traffic.
    Uses only the standard library. Never raises; a failed ping is just logged and retried next round.
    """
    import urllib.request
    time.sleep(60)                                    # let the server and the bot finish starting first
    failures = 0
    while True:
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "keepalive-ping"})
            with urllib.request.urlopen(req, timeout=20) as resp:
                resp.read(64)
            if failures:
                logger.info("Keep-alive ping recovered (%s)", url)
            failures = 0
        except Exception as e:
            failures += 1
            if failures in (1, 5) or failures % 30 == 0:         # do not flood the log
                logger.warning("Keep-alive ping failed (%s): %s", url, e)
        time.sleep(interval)


def start_health_server():
    """
    Tiny HTTP server (standard library) so Render sees an open port, plus an optional keep-alive self-ping.
      PORT                 set by Render -> server starts; without it (local/Pydroid run) nothing starts.
      RENDER_EXTERNAL_URL  set automatically by Render -> used as the ping target.
      KEEPALIVE_URL        optional: ping this URL instead (e.g. your custom domain).
      KEEPALIVE_INTERVAL   optional seconds between pings (default 600, allowed 60-840).
                           Set KEEPALIVE_URL=off to disable the self-ping.
    """
    port = os.getenv("PORT")
    if not port:
        return
    import threading
    from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

    class HealthHandler(BaseHTTPRequestHandler):
        def do_GET(self):
            self.send_response(200)
            self.send_header("Content-Type", "text/plain")
            self.end_headers()
            self.wfile.write(b"Bot is running")

        def do_HEAD(self):
            self.send_response(200)
            self.end_headers()

        def log_message(self, *args):
            pass

    server = ThreadingHTTPServer(("0.0.0.0", int(port)), HealthHandler)
    server.daemon_threads = True
    threading.Thread(target=server.serve_forever, name="health-server", daemon=True).start()

    url = (os.getenv("KEEPALIVE_URL") or os.getenv("RENDER_EXTERNAL_URL") or "").strip()
    if not url or url.lower() in ("off", "false", "0", "no"):
        if not url:
            logger.info("Keep-alive ping not started: no RENDER_EXTERNAL_URL / KEEPALIVE_URL. "
                        "Use an external pinger (e.g. UptimeRobot) against this service's URL.")
        return
    if not url.startswith(("http://", "https://")):
        url = "https://" + url
    try:
        interval = min(840.0, max(60.0, float(os.getenv("KEEPALIVE_INTERVAL", "600"))))
    except ValueError:
        interval = 600.0
    threading.Thread(target=_keepalive_loop, args=(url, interval), name="keepalive", daemon=True).start()
    logger.info("Keep-alive ping every %d s -> %s", int(interval), url)

def main():
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )
    logging.getLogger("httpx").setLevel(logging.WARNING)  # one INFO line per Telegram request is noise
    if not BOT_TOKEN:
        logger.error("TELEGRAM_BOT_TOKEN is missing. Set it in your .env file or environment variables.")
        raise ValueError("TELEGRAM_BOT_TOKEN is missing. Set it in your .env file or environment variables.")
    _utc_offset = datetime.now().astimezone().utcoffset()
    if _utc_offset != timedelta(hours=5, minutes=30):
        logger.warning(
            "Process timezone is UTC%s, not IST (UTC+05:30). Daily resets and expiry times will be "
            "off. Remove any conflicting TZ environment variable (use TZ=Asia/Kolkata).", _utc_offset)
    # Bind the health-check port FIRST so Render sees the service as alive
    # while MongoDB connects (connect retries can take several seconds).
    start_health_server()
    try:
        mongo_db.init_mongo()
        mongo_db.ensure_indexes()
    except Exception as e:
        logger.error("MongoDB startup failed: %s", e)
        raise SystemExit(f"MongoDB startup failed: {e}")
    try:
        lat = mongo_db.measure_latency()
        verdict = ("good" if lat["avg"] < 40 else "a little slow" if lat["avg"] < 150
                   else "SLOW: MongoDB is far from this server (put them in the same region)")
        print(f"🗄 MongoDB round trip: avg {lat['avg']:.0f} ms (min {lat['min']:.0f}, max {lat['max']:.0f}) - {verdict}")
    except Exception as e:
        print("MongoDB latency check failed:", e)
    setup_database()
    install_bot_message_tracker()      # remembers the bot's own message ids for /rem
    install_perf_monitor()             # slow-update / slow-DB / frozen-loop logging (see PERFORMANCE DIAGNOSTICS)

    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .connect_timeout(30)
        .read_timeout(30)
        .write_timeout(30)
        .pool_timeout(30)
        .concurrent_updates(
            ChatOrderedUpdateProcessor(CONCURRENT_UPDATES)
            if ChatOrderedUpdateProcessor is not None and UPDATE_ORDERING == "chat"
            else CONCURRENT_UPDATES
        )
        .post_init(startup_init)
        .post_shutdown(post_shutdown)
        .build()
    )

    from telegram.ext import TypeHandler as _HumanOnlyTypeHandler
    app.add_handler(_HumanOnlyTypeHandler(Update, human_only_gate), group=-300)   # Human-only rule: runs before everything
    app.add_handler(MessageHandler(filters.StatusUpdate.MIGRATE, group_migrated_handler, block=False), group=-150)   # group -> supergroup
    app.add_handler(MessageHandler(filters.ChatType.GROUPS, track_group_chat, block=False), group=-101)

    app.add_handler(MessageHandler(filters.ALL, block_unapproved_group), group=-100)
    app.add_handler(CallbackQueryHandler(block_unapproved_callback), group=-100)
    # Start first: new members must open the bot's PM before the bot reacts to them in groups (after the approved-group check).
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & ~filters.StatusUpdate.ALL, start_first_gate), group=-96)
    app.add_handler(CallbackQueryHandler(start_first_callback_gate), group=-96)
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE, mark_started_private, block=False), group=-95)
    # Strict role check for restricted commands: after the approved-group check, before every real handler.
    app.add_handler(MessageHandler(filters.COMMAND & filters.UpdateType.MESSAGE, role_gate), group=-90)
    app.add_handler(CallbackQueryHandler(exchange_callback, pattern=r"^ex_(accept|decline):"))
    app.add_handler(CallbackQueryHandler(character_selection_callback, pattern=r"^charselect:(check|view):"))
    app.add_handler(CallbackQueryHandler(character_page_callback, pattern=r"^charpage:"))
    app.add_handler(ChatMemberHandler(track_bot_membership, ChatMemberHandler.MY_CHAT_MEMBER), group=-2)

    public_handlers = (
        ("start", start),
        ("help", help_command),
        ("spawn", spawn),
        ("add", add),
        ("mycollection", mycollection),
        ("see", see_command),
        ("reply", reply_command),
        ("myfav", myfav),
        ("mystats", mystats),
        ("addlist", addlist),
        ("daily", daily),
        ("characters", characters),
        ("view", view),
        ("check", check),
        ("sell", sell),
        ("transfer", transfer),
        ("berrytransfer", berrytransfer),
        ("berry", berry),
        ("event", event),
        ("redeem", redeem),
        ("shop", shop),
        ("exchange", exchange),
        ("guess_num", guess_num_start),
        ("nguess", guess_number),
        (["cooldown", "cd"], cooldown),
    )
    for command_name, callback in public_handlers:
        app.add_handler(CommandHandler(command_name, callback))
    app.add_handler(MessageHandler(filters.Regex(_REM_RE) & filters.UpdateType.MESSAGE, rem_command))   # /rem, /rem 10, /rem10
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, sell_input_handler), group=50)      # list after 💰 Sell
    app.add_handler(CallbackQueryHandler(sell_confirm_callback, pattern=r"^sellc:"))
    app.add_handler(CallbackQueryHandler(sell_guide_callback, pattern=r"^sellg:"))
    fusion.bind(is_owner=is_owner, is_executive=is_executive, symbols=SYMBOL, conv_timeout=CONV_TIMEOUT,
                notify=notify_staff_action, log_action=log_character_action, mark_success=mark_success,
                safe_reply=safe_reply_text, skip_keyboard=skip_keyboard, is_skip_text=is_skip_text,
                display_user=display_user, rarity_text=rarity_text, cancel_all=cancel_conversation)
    fusion.register(app)  # stone tasks, /stone, /item, Evolution: /addevo /evolution /evolve /delevo
    theme.bind(is_owner=is_owner, default_start_text=START_TEXT, build_help_text=build_help_text,
               add_header=add_display_name_header)
    theme.register(app)   # 🎨 Customize Bot callbacks, owner input handler, /about
    badge_banner.bind(is_owner=is_owner, is_executive=is_executive, conv_timeout=CONV_TIMEOUT, safe_reply=safe_reply_text,
                      cancel_all=cancel_conversation, mark_success=mark_success, items_per_page=ITEMS_PER_PAGE)
    badge_banner.register(app)   # /badges /claimbadge /banner /usebanner + staff /addbanner /editbanner /delbanner
    rewards.bind(is_owner=is_owner, conv_timeout=CONV_TIMEOUT, safe_reply=safe_reply_text, cancel_all=cancel_conversation,
                  mark_success=mark_success, save_user=save_user_async, timestamp=timestamp,
                  rarities=tuple(r for r in SYMBOL if r not in ("Heavenly", "Special")), symbols=SYMBOL,
                  items_per_page=ITEMS_PER_PAGE)
    security.bind(is_owner=is_owner, is_staff=lambda u: is_owner(u) or is_executive(u) or bool(is_scout(u)),
                  owner_id=ADMIN_IDS[0] if ADMIN_IDS else None, safe_reply=safe_reply_text,
                  unauthorized_text=UNAUTHORIZED_TEXT, mark_success=mark_success)
    security.register(app)      # gate (group -299) + /bangroup /unbangroup /bannedgroups /banuser /unbanuser /bannedusers /allowuser /removeallow /allowlist /checkuser
    rewards.register(app)       # /quests + owner /addfestival /festivals /editfestival /delfestival /addquest /editquest /delquest

    register_executive_commands(app)
    register_owner_commands(app)
    register_log_and_rules_commands(app)

    async def global_error_handler(update, context):
        # Never raise from here: log the full traceback and keep polling.
        try:
            _mark_command_failed(getattr(update, "effective_message", None))   # a crashed command is not "successful"
        except Exception:
            pass
        try:
            logger.error("Telegram handler error: %r", context.error, exc_info=context.error)
        except Exception:
            print(f"Telegram handler error: {context.error!r}")

    app.add_error_handler(global_error_handler)

    issue_conv = ConversationHandler(
        entry_points=[
            CommandHandler("issue", issue_start)
        ],
        states={
            ISSUE_TEXT: [
                MessageHandler(
                    filters.TEXT & ~filters.COMMAND,
                    issue_text,
                )
            ],
            ISSUE_ATTACHMENT: [
                MessageHandler(
                    filters.PHOTO | filters.Document.IMAGE,
                    issue_attachment,
                ),
                MessageHandler(filters.Regex(r"^⏭ Skip$"), issue_skip),
                CommandHandler("skip", issue_skip),
            ],
        },
        fallbacks=[
            CommandHandler("cancel", cancel_conversation),
            CommandHandler("skip", skip_conversation),
        ],
        allow_reentry=True,
    )
    app.add_handler(issue_conv)

    idea_conv = ConversationHandler(
        entry_points=[
            CommandHandler("idea", idea_start)
        ],
        states={
            IDEA_TEXT: [
                MessageHandler(
                    filters.TEXT & ~filters.COMMAND,
                    idea_text,
                )
            ],
            IDEA_ATTACHMENT: [
                MessageHandler(
                    filters.PHOTO | filters.Document.IMAGE,
                    idea_attachment,
                ),
                MessageHandler(filters.Regex(r"^⏭ Skip$"), idea_skip),
                CommandHandler("skip", idea_skip),
            ],
        },
        fallbacks=[
            CommandHandler("cancel", cancel_conversation),
            CommandHandler("skip", skip_conversation),
        ],
        allow_reentry=True,
    )
    app.add_handler(idea_conv)

    appeal_conv = ConversationHandler(
        entry_points=[
            CommandHandler("appeal", appeal_start)
        ],
        states={
            APPEAL_TEXT: [
                MessageHandler(
                    filters.TEXT & ~filters.COMMAND,
                    appeal_text,
                )
            ],
            APPEAL_ATTACHMENT: [
                MessageHandler(
                    filters.PHOTO | filters.Document.IMAGE,
                    appeal_attachment,
                ),
                MessageHandler(filters.Regex(r"^⏭ Skip$"), appeal_skip),
                CommandHandler("skip", appeal_skip),
            ],
        },
        fallbacks=[
            CommandHandler("cancel", cancel_conversation),
            CommandHandler("skip", skip_conversation),
        ],
        allow_reentry=True,
    )
    app.add_handler(appeal_conv)

    app.add_handler(
        MessageHandler(filters.PHOTO, receive_photo)
    )

    app.add_handler(CallbackQueryHandler(gstats_callback, pattern=r"^gstats:"))
    app.add_handler(CallbackQueryHandler(owner_notification_callback, pattern=r"^owner_notify:(yes|no)$"), group=-1)
    app.add_handler(CallbackQueryHandler(deleted_account_review_callback, pattern=r"^delacct:(ask|keep|yes|no):-?\d+:[0-9a-f]{10}$"))
    app.add_handler(CallbackQueryHandler(help_callback, pattern=r"^help:"))
    app.add_handler(CallbackQueryHandler(change_worth_callback, pattern=r"^cw:"))
    app.add_handler(CallbackQueryHandler(range_callback, pattern=r"^rg:"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE, range_panel_input), group=53)
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE, change_worth_input), group=52)
    app.add_handler(CallbackQueryHandler(event_claim_callback, pattern=r"^event:"))
    app.add_handler(CallbackQueryHandler(transfer_callback, pattern=r"^tr_(accept|decline):"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, event_trigger_message))

    app.add_handler(CommandHandler("cancel", cancel_conversation))
    app.add_handler(CommandHandler("skip", skip_conversation))

    app.add_handler(CallbackQueryHandler(collection_callback, pattern=r"^coll:"))
    app.add_handler(CallbackQueryHandler(collview_callback, pattern=r"^cv:"))
    app.add_handler(CallbackQueryHandler(shop_callback, pattern=r"^shop:"))

    print("✅ Anime Character Bot is running...")
    app.run_polling(
        poll_interval=0.0,  # 0.5 s here was a sleep after EVERY getUpdates batch (long-polling already waits)
        timeout=10,
        drop_pending_updates=True,
        bootstrap_retries=-1,
    )


# ======================================================================================================
# CONSOLE BRIDGE (added block - nothing above this line was changed)
#   1. Telegram event logging : every command a user sends in Telegram is printed with the exact reply
#        [Telegram] User: /start -> Response: Hello! Welcome.
#   2. Terminal command execution: type a command in the console; it runs through the REAL handlers and the
#      reply is printed here instead of being sent to Telegram
#        [Terminal Input]: /daily -> Response: Here is your daily reward!
#      Console syntax:  /daily | as <user_id> /daily | in <chat_id> /spawn | as <user_id> in <chat_id> /add naruto
#      (default user = the Owner, default chat = that user's private chat; text without "/" is sent as a plain
#       message, e.g. to answer the steps of /addcharacter).
#   Switches: CONSOLE_BRIDGE_TERMINAL=0 (no console input)  CONSOLE_BRIDGE_LOG=0 (no Telegram logging)
#             CONSOLE_MULTILINE=1 (replies on several lines instead of one line)
#   It only wraps outgoing Bot calls and adds one early handler; no existing command or function is touched.
#   On Render there is no console, so only the [Telegram] log lines appear (in the Render Logs).
# ======================================================================================================
import asyncio as _cb_asyncio, contextvars as _cb_contextvars, itertools as _cb_itertools
import os as _cb_os, re as _cb_re, threading as _cb_threading
from datetime import datetime as _cb_datetime, timezone as _cb_timezone
_CB_CTX = _cb_contextvars.ContextVar("console_bridge_ctx", default=None)
_CB_TERMINAL_IDS = set()
_CB_RUNS = {}
_cb_counter = _cb_itertools.count(1)
_cb_state = {"default_uid": None, "wrapped": False, "terminal": True, "log": True}


# ----------------------------------------------------------------------------- output
def _cb_flat(text):
    text = "" if text is None else str(text)
    if _cb_os.getenv("CONSOLE_MULTILINE") == "1":
        return text
    return _cb_re.sub(r"\s*\n\s*", " ⏎ ", text).strip()


def _cb_emit(ctx, label, text):
    ctx["n"] += 1
    response = _cb_flat(((label + " ") if label else "") + ("" if text is None else str(text)))
    tag = "[Terminal Input]:" if ctx["mode"] == "terminal" else "[Telegram] User:"
    print(f"{tag} {ctx['input']} -> Response: {response}", flush=True)


# ----------------------------------------------------------------------------- real-PTB object builders (replaceable in tests)
def _cb_make_update(uid, chat_id, text):
    from telegram import Chat, Message, MessageEntity, Update, User
    n = next(_cb_counter)
    chat = Chat(id=chat_id, type="private" if chat_id > 0 else "supergroup", title=None if chat_id > 0 else "Console group")
    user = User(id=uid, first_name="Console", is_bot=False)
    entities = None
    if text.startswith("/"):
        token = text.split()[0]
        entities = [MessageEntity(type="bot_command", offset=0, length=len(token))]
    msg = Message(message_id=10 ** 9 + n, date=_cb_datetime.now(_cb_timezone.utc), chat=chat, from_user=user, text=text, entities=entities)
    return Update(update_id=10 ** 9 + n, message=msg), msg


def _cb_bind_bot(msg, bot):
    msg.set_bot(bot)


def _cb_make_bot_message(bot, chat_id, chat_type, text):
    from telegram import Chat, Message, User
    n = next(_cb_counter)
    return Message(message_id=2 * 10 ** 9 + n, date=_cb_datetime.now(_cb_timezone.utc), chat=Chat(id=chat_id, type=chat_type),
                   from_user=User(id=bot.id, first_name="Bot", is_bot=True, username=bot.username), text=text or "")


# ----------------------------------------------------------------------------- outgoing-message wrapper
def _cb_pick(args, kwargs, name, idx):
    if name in kwargs:
        return kwargs[name]
    return args[idx] if idx is not None and len(args) > idx else None


# method: (label, chat getter, text getter, returns-a-message)
_CB_METHODS = {
    "send_message":       ("",           lambda a, k: _cb_pick(a, k, "chat_id", 0), lambda a, k: _cb_pick(a, k, "text", 1), True),
    "send_photo":         ("[photo]",    lambda a, k: _cb_pick(a, k, "chat_id", 0), lambda a, k: _cb_pick(a, k, "caption", 2), True),
    "send_document":      ("[document]", lambda a, k: _cb_pick(a, k, "chat_id", 0), lambda a, k: _cb_pick(a, k, "caption", None), True),
    "send_animation":     ("[animation]", lambda a, k: _cb_pick(a, k, "chat_id", 0), lambda a, k: _cb_pick(a, k, "caption", None), True),
    "send_video":         ("[video]",    lambda a, k: _cb_pick(a, k, "chat_id", 0), lambda a, k: _cb_pick(a, k, "caption", None), True),
    "edit_message_text":  ("[edited]",   lambda a, k: _cb_pick(a, k, "chat_id", 1), lambda a, k: _cb_pick(a, k, "text", 0), False),
    "edit_message_caption": ("[edited]", lambda a, k: _cb_pick(a, k, "chat_id", 0), lambda a, k: _cb_pick(a, k, "caption", None), False),
    "edit_message_media": ("[edited]",   lambda a, k: _cb_pick(a, k, "chat_id", 0),
                           lambda a, k: getattr(_cb_pick(a, k, "media", 1), "caption", None), False),
}


def _cb_is_log_prompt(kwargs):
    markup = kwargs.get("reply_markup")
    try:
        return any(str(getattr(b, "callback_data", "") or "").startswith("lg:")
                   for row in getattr(markup, "inline_keyboard", ()) for b in row)
    except Exception:
        return False


def _cb_wrap_method(bot_cls, name, label, chat_get, text_get, returns_message):
    original = getattr(bot_cls, name, None)
    if original is None or getattr(original, "_console_bridge", False):
        return

    async def wrapper(self, *args, **kwargs):
        ctx = _CB_CTX.get()
        chat_id = chat_get(args, kwargs)
        if (not ctx or chat_id is None or str(chat_id) != str(ctx["chat_id"])
                or (not _cb_state["log"] and ctx["mode"] != "terminal")):
            return await original(self, *args, **kwargs)
        text = text_get(args, kwargs)
        if ctx["mode"] == "terminal" and _cb_is_log_prompt(kwargs):
            # The Owner's Yes/No log prompt needs real tappable buttons: send it to Telegram, note it here.
            _cb_emit(ctx, "", "(Yes/No log prompt sent to your Telegram chat - tap a button there)")
            return await original(self, *args, **kwargs)
        if ctx["mode"] == "terminal":                       # terminal run: print, do NOT send to Telegram
            _cb_emit(ctx, label, text)
            if returns_message:
                msg = _cb_make_bot_message(self, int(chat_id), ctx["chat_type"], text)
                _cb_bind_bot(msg, self)
                return msg
            return True
        result = await original(self, *args, **kwargs)      # Telegram run: send for real, then log what was sent
        _cb_emit(ctx, label, text)
        return result

    wrapper._console_bridge = True
    wrapper.__name__ = name
    setattr(bot_cls, name, wrapper)


def _cb_wrap_bot_methods(bot_cls):
    for name, (label, chat_get, text_get, returns_message) in _CB_METHODS.items():
        _cb_wrap_method(bot_cls, name, label, chat_get, text_get, returns_message)
    _cb_state["wrapped"] = True


# ----------------------------------------------------------------------------- per-update context
async def _cb_context_hook(update, context):
    msg = update.effective_message
    text = getattr(msg, "text", None) if msg is not None else None
    chat = update.effective_chat
    if not text or chat is None:
        return
    terminal = update.update_id in _CB_TERMINAL_IDS
    if not terminal:
        if not text.startswith("/"):
            return                                           # only commands are logged
        _name, _, target = text.split()[0][1:].partition("@")
        if target and target.lower() != str(getattr(context.bot, "username", "") or "").lower():
            return                                           # a command for another bot
    ctx = {"mode": "terminal" if terminal else "telegram", "input": text, "chat_id": chat.id,
           "chat_type": chat.type, "n": 0}
    _CB_CTX.set(ctx)
    _CB_RUNS[update.update_id] = ctx


# ----------------------------------------------------------------------------- terminal side
_CB_LINE = _cb_re.compile(r"^(?:as\s+(-?\d+)\s+)?(?:in\s+(-?\d+)\s+)?(.+)$", _cb_re.S)


async def _cb_run_terminal(app, line, default_uid=None):
    m = _CB_LINE.match(line.strip())
    if not m:
        return
    uid = int(m.group(1)) if m.group(1) else (default_uid or _cb_state["default_uid"])
    chat_id = int(m.group(2)) if m.group(2) else uid
    text = m.group(3).strip()
    if uid is None:
        print("[Console] No default user known - use:  as <user_id> /command", flush=True)
        return
    update, msg = _cb_make_update(uid, chat_id, text)
    _cb_bind_bot(msg, app.bot)
    _CB_TERMINAL_IDS.add(update.update_id)
    try:
        await app.process_update(update)
    finally:
        ctx = _CB_RUNS.pop(update.update_id, None)
        _CB_TERMINAL_IDS.discard(update.update_id)
    if ctx is not None and ctx["n"] == 0:
        print(f"[Terminal Input]: {text} -> Response: (no response)", flush=True)


def _cb_reader(app, loop):
    print("[Console] Type a bot command (e.g. /start, /daily, /help) and press Enter. "
          "Prefix:  as <user_id>  and/or  in <chat_id>.", flush=True)
    while True:
        try:
            line = input()
        except (EOFError, OSError):
            return                                           # no console (e.g. Render): quietly stop
        if not line.strip():
            continue
        try:
            _cb_asyncio.run_coroutine_threadsafe(_cb_run_terminal(app, line, _cb_state["default_uid"]), loop).result(timeout=180)
        except Exception as e:
            print(f"[Console] Error: {type(e).__name__}: {e}", flush=True)


# ----------------------------------------------------------------------------- installation
def _cb_attach(app):
    from telegram import Update
    from telegram.ext import TypeHandler
    app.add_handler(TypeHandler(Update, _cb_context_hook), group=-200)       # runs before every other handler
    previous = getattr(app, "post_init", None)

    async def chained(application):
        if previous is not None:
            await previous(application)
        if _cb_state["terminal"]:
            _cb_threading.Thread(target=_cb_reader, args=(application, _cb_asyncio.get_running_loop()),
                             name="console-bridge", daemon=True).start()

    app.post_init = chained


def console_bridge_enable(default_user_id=None):
    """Call once BEFORE bot.main(). Wraps Application.run_polling so the hook is attached just before polling starts."""
    from telegram import Bot
    from telegram.ext import Application
    _cb_state["default_uid"] = default_user_id
    _cb_state["terminal"] = _cb_os.getenv("CONSOLE_BRIDGE_TERMINAL", "1") != "0"
    _cb_state["log"] = _cb_os.getenv("CONSOLE_BRIDGE_LOG", "1") != "0"
    _cb_wrap_bot_methods(Bot)
    original = Application.run_polling
    if getattr(original, "_console_bridge", False):
        return

    def run_polling(self, *args, **kwargs):
        _cb_attach(self)
        return original(self, *args, **kwargs)

    run_polling._console_bridge = True
    Application.run_polling = run_polling


if __name__ == "__main__":
    console_bridge_enable(default_user_id=ADMIN_IDS[0] if ADMIN_IDS else None)
    main()
