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
import uuid
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
    BotCommandScopeChat,
    BotCommandScopeDefault,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputMediaPhoto,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
)
from telegram.error import BadRequest, Forbidden, RetryAfter, TelegramError
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

def load_restrictions():
    return mongo_db.load_restrictions()

def save_restrictions(data):
    _RESTRICTION_CACHE.clear()
    return _mongo_safe(mongo_db.replace_restrictions, data)

def get_restriction_expiry(user_id):
    # Called on many updates, so keep a very short per-user cache (cleared on every write).
    now_mono = time.monotonic()
    cached = _RESTRICTION_CACHE.get(user_id)
    if cached and now_mono - cached[0] < _RESTRICTION_TTL:
        return cached[1]
    entry = mongo_db.get_restriction(user_id)
    expiry = None
    if entry:
        value = int(entry.get("expiry", 0))
        if value <= int(datetime.now().timestamp()):
            mongo_db.remove_restriction(user_id)
        else:
            expiry = value
    _RESTRICTION_CACHE[user_id] = (now_mono, expiry)
    return expiry

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

async def get_restricted_message(update):
    user = getattr(update, "effective_user", None)
    if not user or is_owner(user.id) or is_executive(user.id):
        return None
    cached = _RESTRICTION_CACHE.get(user.id)
    if cached and time.monotonic() - cached[0] < _RESTRICTION_TTL:
        expiry = cached[1]
    else:
        expiry = await asyncio.to_thread(get_restriction_expiry, user.id)
    if not expiry:
        return None
    remaining = format_remaining(expiry - int(datetime.now().timestamp()))
    return (
        "🚫 You are currently restricted.\n"
        f"⏳ Time remaining: {remaining}\n"
        "Your restriction will expire automatically after this time."
    )

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


async def approve_group(update, context):
    uid = update.effective_user.id
    if not (await asyncio.to_thread(has_group_approval_permission, uid)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    chat = update.effective_chat
    if chat.type in ("group", "supergroup"):
        if context.args:
            await safe_reply_text(update.message, "Usage: /approve")
            return
        chat_id = chat.id
    else:
        if len(context.args) != 1 or not context.args[0].lstrip("-").isdigit():
            await safe_reply_text(update.message, "Usage in Owner DM: /approve <group_chat_id>")
            return
        chat_id = int(context.args[0])

    groups = (await asyncio.to_thread(load_approved_groups))
    groups.add(chat_id)
    saved = (await asyncio.to_thread(save_approved_groups, groups))
    (await asyncio.to_thread(set_bot_enabled, chat_id, True))
    (await asyncio.to_thread(register_auto_spawn_group, chat_id))
    context.application.bot_data.setdefault("active_chats", set()).add(chat_id)
    context.application.bot_data.setdefault("unapproved_notified", set()).discard(chat_id)
    # Confirmation goes to the exact group that was just approved, only after the approval was saved.
    group_notified = (saved is not False) and (await send_group_approved_confirmation(context, chat_id))
    if chat.type in ("group", "supergroup"):
        if not group_notified:  # the confirmation above already answers in the group; fall back to the old reply
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
        if await is_group_approved(chat.id):
            (await asyncio.to_thread(register_auto_spawn_group, chat.id))
            context.application.bot_data.setdefault("active_chats", set()).add(chat.id)
            return

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
                    await context.bot.send_message(
                        chat_id=owner_id,
                        text=(
                            "🔔 New Group Approval Request\n"
                            f"🏷 Group: {html_escape(chat.title or 'Unknown')}\n"
                            f"🆔 Group ID: {group_id_html(chat.id)}\n"
                            f"👤 Requested by: {html_escape(added_by_text)}\n\n"
                            f"Approve with: /approve {html_escape(str(chat.id))}"
                        ),
                        parse_mode="HTML",
                    )
                except Exception as e:
                    print("Owner group-approval notification error:", e)
        (await asyncio.to_thread(unregister_auto_spawn_group, chat.id))
        context.application.bot_data.setdefault("active_chats", set()).discard(chat.id)
    elif status in ("left", "kicked"):
        (await asyncio.to_thread(unregister_bot_group, chat.id))
        (await asyncio.to_thread(unregister_auto_spawn_group, chat.id))
        context.application.bot_data.setdefault("active_chats", set()).discard(chat.id)

SPAWN_LIFETIME = 20 * 60  # 20 minutes
AUTO_SPAWN_INTERVAL = 30 * 60  # 30 minutes
PERSONAL_SPAWN_COOLDOWN = 3600  # 1 hour
GROUP_SPAWN_COOLDOWN = 70       # 70 seconds
SYMBOL = {
    "Common": "⚪",
    "Rare": "🔵",
    "Epic": "🟣",
    "Legendary": "💎",
    "Mythical": "🔮",
    "Celestial": "💠",
}

WORTH = {
    "Common": 50,
    "Rare": 100,
    "Epic": 200,
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
    return mongo_db.find_character_by_recruit_name(value)

def find_characters_by_recruit_name_partial(value):
    return mongo_db.find_characters_by_recruit_name_partial(value)

def find_characters_by_name_parts(query):
    return mongo_db.find_characters_by_name_parts(query)

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
    return mongo_db.get_all_characters()

def get_characters_by_rarity(rarity):
    return mongo_db.get_characters_by_rarity(rarity)

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
    return _number_commands(_build_help_text_raw())


def _build_help_text_raw():
    return (
        "🎮 Anime Character Catcher — Command List\n\n"
        "👤 Profile & Collection\n"
        "/start — Register / start the bot\n"
        "/help — Show this command list\n"
        "/mycollection — View your collection\n"
        "/myfav <code/name> — Set or change favourite character\n"
        "/mystats — View your stats and collection progress\n"
        "/characters — List all characters by rarity\n"
        "/view <code/name> — View a character's full details and image\n"
        "/check <code/name> — Check character details and owners\n"
        "/addlist — View character add/edit ranking\n\n"
        "🎯 Catching & Rewards\n"
        "/spawn — Spawn a character in the group\n"
        "/cooldown — View character cooldowns for this group\n"
        "/add — Catch the spawned character\n"
        "/daily — Claim your daily reward\n"
        "/sell <code/name> [quantity] — Sell a character\n"
        "/transfer <code/name> — Transfer a character by replying to a user\n"
        "/exchange <your_code> <their_code> — Exchange same-tier characters by replying to a user\n\n"
        "🎮 Games\n"
        "/guess_num — Start a Guess the Number game\n"
        "/nguess <number> — Guess a number from 1–100 (10 attempts, 150 Berrys reward)\n\n"
        "🫐 Berrys\n"
        "/berrytransfer <amount> — Give Berrys by replying to a user\n"
        "/berry — View your daily Berry transfer status\n\n"
        "🎪 Events & Redeem\n"
        "/event — View the active event\n"
        "/redeem <code> — Redeem a code\n\n"
        "🛒 Shop\n"
        "/shop — Open your personal character shop\n\n"
        "📜 Rules\n"
        "/rules — View the bot usage rules (/rules noformat for raw text)\n\n"
        "👥 Staff\n"
        "/executives — View the Executive list\n"
        "/scouts — View the Scout list\n\n"
        "📝 Support\n"
        "/issue — Report an issue\n"
        "/idea — Send a suggestion\n"
        "/appeal — Appeal a restriction\n"
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
        ("rules", "📜 Bot Rules", _help_page(
            "📜 Bot Rules",
            "The usage rules everyone can read. Only staff can change them.",
            [("/rules", "Show the rules (everyone, groups and PM)"),
             ("/rules noformat", "Raw markdown text for easy copying"),
             ("/setrules <text>", "Set the rules (Owner/Executive, private chat only; Markdown supported)"),
             ("/resetrules", "Clear all rules (Owner only, private chat only)")])),
        ("staff", "👔 Staff Roles", _help_page(
            "👔 Staff Roles (Owner only)",
            "Manage Executives and who may approve groups.",
            [("/addexec <user_id>", "Add an Executive"),
             ("/removeexec <user_id>", "Remove an Executive"),
             ("/addgroupapprove <executive_user_id>", "Let an Executive approve/remove groups"),
             ("/removegroupapprove <executive_user_id>", "Take that permission away")],
            "The Executive and Scout lists are public: /executives and /scouts. Scouts are added with /addscout.")),
        ("groups", "🏘 Groups", _help_page(
            "🏘 Groups",
            "Approve groups, remove them, and check the bot's state.",
            [("/approve", "In a group: approve it. In PM: /approve <group_chat_id> (Owner, or an Executive with permission)"),
             ("/removeapprove", "In PM: /removeapprove <group_chat_id>"),
             ("/leavegroup", "In PM: /leavegroup <group_chat_id> — remove the group and leave it"),
             ("/status", "Bot status and active spawns")])),
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
            [("/addevent", "Guided setup: name, code, reward, trigger text, end date and time"),
             ("/endevent", "End the active event"),
             ("/addredeem", "Guided setup: type, reward, claim limit, expiry, code"),
             ("/deleteredeem CODE", "Disable a code"),
             ("/redeems", "List active codes")])),
        ("history", "📊 History", _help_page(
            "📊 History (Owner only)",
            "Look back at what the bot has been doing.",
            [("/history [1-50]", "Recent spawn history")])),
    ],
    "executive": [
        ("restrict", "🚫 Restrictions", _help_page(
            "🚫 Restrictions (Owner & Executive)",
            "Temporarily block a user from the bot. Durations: 1h, 10h, 1d up to 365d; they expire automatically.",
            [("/restrict <duration> [reason]", "Reply to the user"),
             ("/restrict <user_id> <duration> [reason]", "By user ID"),
             ("/unrestrict", "Reply to the user to lift the restriction"),
             ("/unrestrict <user_id>", "Lift by user ID"),
             ("/restrictions", "View all active restrictions")])),
        ("transfers", "🔁 Transfer Blocks", _help_page(
            "🔁 Transfer Blocks (Owner & Executive)",
            "Stop character transfers between two specific users.",
            [("/btransfer <user_id_1> <user_id_2>", "Block transfers between the pair"),
             ("/unbtransfer <user_id_1> <user_id_2>", "Remove the block")])),
        ("groupctl", "🤖 Group Control", _help_page(
            "🤖 Group Control (Owner & Executive)",
            "Switch the bot on or off per group and view group statistics.",
            [("/boton [group_chat_id]", "Turn the bot ON in a group (PM supported)"),
             ("/botoff [group_chat_id]", "Turn the bot OFF in a group (PM supported)"),
             ("/gstats", "View bot group statistics")])),
        ("broadcast", "📣 Broadcast", _help_page(
            "📣 Broadcast (Owner & Executive)",
            "Send one announcement to every linked group.",
            [("/addmessage", "Broadcast a PM message to all linked groups (PM only)")])),
        ("scouts", "🔭 Scout Mgmt", _help_page(
            "🔭 Scout Management (Owner & Executive)",
            "Add or remove Scouts, the staff who manage characters.",
            [("/addscout <user_id>", "Add a Scout"),
             ("/removescout <user_id>", "Remove a Scout"),
             ("/scouts", "View the Scout list (public: every user can run it)")])),
        ("execrules", "📜 Exec Rules", _help_page(
            "📜 Exec Rules (Owner & Executive)",
            "Executives can set the bot rules; everyone can read them.",
            [("/setrules <text>", "Set the rules (private chat only; Markdown supported). "
                                  "Tip: reply to a message in PM with /setrules to use that message"),
             ("/rules", "View the rules"),
             ("/rules noformat", "Raw markdown text for copying")],
            "Clearing the rules is reserved for the Owner.")),
    ],
    "scout": [
        ("addedit", "🎴 Add & Edit", _help_page(
            "🎴 Add & Edit Characters (Owner, Executive & Scout)",
            "Add and maintain characters. The editor also changes recruitment/search names.",
            [("/addcharacter", "Add a character (guided)"),
             ("/addphoto <name/code>", "Add a character photo"),
             ("/editcharacter <code/name>", "Edit name, anime, rank/rarity, worth, 4-digit code, recruitment/search names")])),
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


NOT_YOURS_TEXT = "⚠️ This isn't yours. Please run /help to open your own menu."
# Executive and Scout modules stay in their own menus AND are copied (same text) into the Owner menu.
_owner_keys = {k for k, _l, _t in HELP_MODULES["owner"]}
for _role in ("executive", "scout"):
    for _module in HELP_MODULES[_role]:
        if _module[0] not in _owner_keys:
            HELP_MODULES["owner"].append(_module)
            _owner_keys.add(_module[0])
HELP_STALE_TEXT = "⚠️ This menu is outdated. Please run /help to open your own menu."
HELP_PM_START_TEXT = ("📩 I couldn't message you privately. Open a private chat with me, press Start, "
                      "then run /help again.")
# Callback data format (<= 64 bytes): help:<menu_owner_id>:<action>[:<module>]
#   action = open | back | owner | executive | scout        (menu_owner_id = the user who ran /help or /start)


def help_grid_keyboard(role, owner_id):
    """LAYER 2: module buttons in a strict 3-column grid + « Back to Layer 1 (main help)."""
    buttons = [_module_button(label, f"help:{owner_id}:{role}:{key}") for key, label, _text in HELP_MODULES[role]]
    rows = [buttons[i:i + 3] for i in range(0, len(buttons), 3)]
    rows.append([InlineKeyboardButton("« Back", callback_data=f"help:{owner_id}:back")])
    return InlineKeyboardMarkup(rows)


def help_grid_text(role):
    return f"{HELP_ROLE_TITLES[role]}\n\nChoose a module to see its overview and command syntax."


def help_detail(role, key, owner_id):
    """LAYER 3: (text, keyboard) for one module, or None for an unknown key. « Back returns to Layer 2."""
    for k, _label, text in HELP_MODULES[role]:
        if k == key:
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
    return InlineKeyboardMarkup(rows) if rows else None

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
    if reward_type == "character":
        character = get_character_by_code(str(reward_value))
        if character:
            return f"🎭 {character[1]} [{character[0]}]"
        return f"🎭 Character code {reward_value}"
    return str(reward_value)

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
        counts = mongo_db.sh_code_counts()
        # Least-used first prevents unnecessary repeats while keeping the choice random.
        least = min(counts.get(str(r[0]), 0) for r in rows)
        pool = [r for r in rows if counts.get(str(r[0]), 0) == least]
        return random.choice(pool)
    except Exception as e:
        pass
        print("Fallback character count lookup error:", e)
        return random.choice(rows)

def choose_character(chat_id, excluded_codes=None, app=None, respect_daily_limit=True, require_photo=False):
    excluded = {str(code) for code in (excluded_codes or set())}
    if respect_daily_limit:
        excluded.update(get_daily_random_spawn_limited_codes(chat_id, app))
    excluded.update(get_recent_global_spawn_codes(chat_id))

    def available_rows(rarity):
        return [row for row in get_characters_by_rarity(rarity) if str(row[0]) not in excluded and (not require_photo or spawn_photo_ok(row))]

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
                counts = mongo_db.sh_code_counts()

                rows.sort(key=lambda r: int(r[0]) if str(r[0]).isdigit() else 0)
                mid = max(1, len(rows) // 2)
                buckets = [rows[:mid], rows[mid:]] if len(rows) > 1 else [rows]
                totals = [sum(counts.get(str(r[0]), 0) for r in b) for b in buckets]
                bucket = buckets[0] if len(buckets) == 1 or totals[0] < totals[1] else buckets[1] if totals[1] < totals[0] else random.choice(buckets)
                least = min(counts.get(str(r[0]), 0) for r in bucket)
                return random.choice([r for r in bucket if counts.get(str(r[0]), 0) == least])

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
    lock = get_spawn_lock(app)

    random_spawn = spawned_by in ("auto_spawn", "manual_spawn")
    character_code = None
    forced_reuse = False
    history_id = None

    async with lock:
        active = app.bot_data.setdefault("active_spawns", {})
        if chat_id in active:
            return False, "❌ A character is already spawned in this chat."

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

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    (await save_user_async(update.effective_user))
    if update.effective_chat and update.effective_chat.type in ("group", "supergroup"):
        (await asyncio.to_thread(register_bot_group, update.effective_chat))
    user_id = update.effective_user.id

    if update.effective_chat.type == "private":
        await refresh_command_menu(context.bot, user_id)
    else:
        await refresh_group_command_menu(context.bot, update.effective_chat.id, user_id)

    await safe_reply_text(update.message,
        "🎮 Welcome to Anime Character Catcher!\n\n"
        "Catch characters, build your collection, earn Berrys, and enjoy the game.\n\n"
        "📖 Use /help to see all available commands.",
        reply_markup=start_help_keyboard(update.effective_user.id),
    )

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
    active = context.application.bot_data.setdefault("active_spawns", {})

    if chat_id in active:
        await safe_reply_text(
            update.message,
            "❌ A character is already spawned in this chat.\nUse /add to catch it first.",
        )
        return

    now_dt = datetime.now()
    last_calls = context.application.bot_data.setdefault("last_calls", {})
    personal_remaining = PERSONAL_SPAWN_COOLDOWN - (now_dt - last_calls[user_id]).total_seconds() if user_id in last_calls else 0
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

    last_calls = context.application.bot_data.setdefault("last_calls", {})
    last_calls[user_id] = datetime.now()
    context.application.bot_data.setdefault("active_chats", set()).add(chat_id)
    context.application.bot_data.setdefault("next_auto_spawn_at", {})[chat_id] = (
        datetime.now() + timedelta(seconds=AUTO_SPAWN_INTERVAL)
    )

async def cooldown(update, context):
    """Show this group's auto-spawn/life state and up to 10 character cooldowns."""
    if not await require_group_spawn(update):
        return
    chat_id = update.effective_chat.id
    now_dt = datetime.now()

    # Current character life for this exact group.
    active = context.application.bot_data.setdefault("active_spawns", {}).get(chat_id)
    life_text = "No character currently spawned"
    if active:
        expires = active.get("expires_at")
        try:
            sec = max(0, (expires - now_dt).total_seconds())
            life_text = f"{html_escape(str(active.get('name', active.get('code', 'Unknown'))))} — {format_duration(sec)} remaining"
        except Exception:
            life_text = "Character currently spawned"

    # Personal and group /spawn cooldowns.
    last_calls = context.application.bot_data.setdefault("last_calls", {})
    personal_remaining = (PERSONAL_SPAWN_COOLDOWN - (now_dt - last_calls[update.effective_user.id]).total_seconds()
                          if update.effective_user.id in last_calls else 0)
    personal_text = format_duration(personal_remaining) if personal_remaining > 0 else "Ready"

    group_until = context.application.bot_data.setdefault("chat_spawn_cooldowns", {}).get(chat_id)
    group_remaining = (group_until - now_dt).total_seconds() if group_until else 0
    group_text = format_duration(group_remaining) if group_remaining > 0 else "Ready"

    # Next auto-spawn for this exact group.
    next_auto = context.application.bot_data.setdefault("next_auto_spawn_at", {}).get(chat_id)
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

    text = (f"⏳ <b>Spawn Cooldown</b>\n\n"
            f"🤖 Auto Spawn: <b>{auto_text}</b>\n"
            f"❤️ Character Life: <b>{html_escape(life_text)}</b>\n"
            f"👤 Your /spawn: <b>{personal_text}</b>\n"
            f"🏠 Group /spawn: <b>{group_text}</b>\n\n"
            "🎴 <b>Character Cooldowns</b>\n")
    text += "\n".join(rows) if rows else "• No character is currently on cooldown. All characters are eligible."
    await safe_reply_text(update.message, text, parse_mode="HTML")

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
        for code, name, anime, rarity, worth, photo in rows
    ])

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
    if action == "edit":
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
        success, reason = await spawn_reserved(group_id, context, character, "owner_callchar")
        if not success:
            await safe_reply_text(update.effective_message, reason)
            return ConversationHandler.END
        context.application.bot_data.setdefault("active_chats", set()).add(group_id)
        await safe_reply_text(update.effective_message, f"✅ Character called successfully.\n🎭 {character[1]} [{character[0]}]\n🆔 Group ID: {group_id}")
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
        success, reason = await spawn_reserved(chat_id, context, character, "owner_callchar")
    except Exception as e:
        print("Callchar spawn error:", e)
        await tell("⚠️ Character could not be delivered. Please try again.")
        return

    if not success:
        await tell(reason or "⚠️ Character could not be delivered. Please try again.")
        return

    context.application.bot_data.setdefault("active_chats", set()).add(chat_id)
    return ConversationHandler.END

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
    await safe_reply_text(
        update.message,
        f"🌸 Recruiter: {berry_display_name(update.effective_user)}\n\n"
        "🎉 Congratulations! Character added to your collection!\n\n"
        f"Name: {caught_spawn['name']}\n"
        f"Code: {caught_spawn['code']}\n"
        f"Tier: {caught_rarity} {caught_symbol}\n"
        f"Worth: {caught_spawn['worth']} Berrys\n"
    )

async def get_collection_rows(user_id, sort_mode="tier"):
    rows = (await asyncio.to_thread(mongo_db.get_collection_summary, user_id))

    rarity_order = {
        "Celestial": 0,
        "Mythical": 1,
        "Legendary": 2,
        "Epic": 3,
        "Rare": 4,
        "Common": 5,
    }

    if sort_mode == "time":
        rows.sort(key=lambda r: r[6] or "", reverse=True)
    elif sort_mode == "name":
        rows.sort(key=lambda r: r[1].lower())
    elif sort_mode == "qty":
        rows.sort(key=lambda r: (-r[5], r[1].lower()))
    else:
        rows.sort(key=lambda r: (rarity_order.get(r[3], 99), r[1].lower()))

    return rows

def get_favorite_code(user_id):
    return mongo_db.get_favorite_code(user_id)

def set_favorite(user_id, character_code):
    mongo_db.set_favorite(user_id, character_code, timestamp())

def clear_favorite(user_id):
    mongo_db.clear_favorite(user_id)

def collection_keyboard(user_id, page, total_pages, sort_mode, favorite_code):
    buttons = []
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅️", callback_data=f"coll:{user_id}:{sort_mode}:{page-1}"))
    nav.append(InlineKeyboardButton(f"📖 {page+1}/{total_pages}", callback_data=f"coll:{user_id}:nochange:0"))
    if page < total_pages - 1:
        nav.append(InlineKeyboardButton("➡️", callback_data=f"coll:{user_id}:{sort_mode}:{page+1}"))
    buttons.append(nav)

    buttons.append([
        InlineKeyboardButton("🔹 Tier", callback_data=f"coll:{user_id}:tier:0"),
        InlineKeyboardButton("🔤 Name", callback_data=f"coll:{user_id}:name:0"),
    ])
    buttons.append([
        InlineKeyboardButton("🔢 Quantity", callback_data=f"coll:{user_id}:qty:0"),
        InlineKeyboardButton("🕒 Recent", callback_data=f"coll:{user_id}:time:0"),
    ])

    if favorite_code:
        buttons.append([
            InlineKeyboardButton("⭐ Favourite", callback_data=f"coll:{user_id}:nochange:0"),
            InlineKeyboardButton("❌ Clear Favourite", callback_data=f"coll:{user_id}:clearfav:0"),
        ])
    return InlineKeyboardMarkup(buttons)

def build_collection_text(rows, page, per_page, sort_mode, favorite_code, total_copies, owner_name="Player"):
    total_pages = max(1, (len(rows) + per_page - 1) // per_page)
    page = max(0, min(page, total_pages - 1))
    page_rows = rows[page * per_page:(page + 1) * per_page]

    text = (
        "━━━━━━━━━━━━━━━━━━\n"
        f"❀• {owner_name} •❀'s crew  ➜  Page {page + 1}/{total_pages}\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        f"📚 Collection: {total_copies} total | {len(rows)} unique\n"
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
    text += "\n" + labels.get(sort_mode, "🔹 Sorted by Tier")
    if favorite_code:
        fav = next((r for r in rows if r[0] == favorite_code), None)
        if fav:
            text += f"\n⭐ Favourite: {fav[1]} [{fav[0]}]"
    return text, total_pages, page

async def send_collection(update_or_query, context, user_id, page=0, sort_mode="tier", edit=False, owner_name=None):
    rows = await get_collection_rows(user_id, sort_mode)
    sender_message = getattr(update_or_query, "message", None)
    if sender_message is None and hasattr(update_or_query, "effective_message"):
        sender_message = update_or_query.effective_message
    if sender_message is None and hasattr(update_or_query, "message"):
        sender_message = update_or_query.message
    if not rows:
        message = add_display_name_header(sender_message, "📚 Your collection is empty. Catch a character with /spawn then use /add.")
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
        rows, page, per_page, sort_mode, favorite_code, total_copies, owner_name
    )
    text = add_display_name_header(sender_message, text)
    keyboard = collection_keyboard(user_id, page, total_pages, sort_mode, favorite_code)

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

    await query.answer()
    action = parts[2]
    if action == "nochange":
        return
    if action == "clearfav":
        (await asyncio.to_thread(clear_favorite, user_id))
        page = 0
        action = "tier"

    if action not in {"tier", "time", "name", "qty"}:
        action = "tier"

    await send_collection(
        query, context, user_id, page, action, edit=True,
        owner_name=query.from_user.first_name or "Player"
    )

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

    await safe_reply_text(update.message,
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
        f"🔄 Transfers today: {int(transfers_today or 0)}"
    , parse_mode="HTML")

SHOP_RARITIES = ("Common", "Rare", "Legendary", "Mythical")
SHOP_REFRESH_COST = 100
SHOP_PRICE_MULTIPLIER = 5
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
            r for r in mongo_db.get_characters_by_rarity(rarity)
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
    if not force and count == 4 and current_day == key:
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

def shop_keyboard(user_id, page, price, bought=False, total=4):
    prev_page = (page - 1) % total
    next_page = (page + 1) % total
    buy_label = "✅ BOUGHT" if bought else f"🛒 BUY FOR {price} ⦵"
    buy_action = "bought" if bought else "buy"
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("◀️ BACK", callback_data=f"shop:page:{user_id}:{prev_page}"),
            InlineKeyboardButton("▶️ NEXT", callback_data=f"shop:page:{user_id}:{next_page}"),
        ],
        [InlineKeyboardButton("🔄 REFRESH — 100 ⦵", callback_data=f"shop:refresh:{user_id}:0")],
        [InlineKeyboardButton(buy_label, callback_data=f"shop:{buy_action}:{user_id}:{page}")],
    ])

def build_shop_caption(row, page, total=4):
    _, code, name, anime, rarity, worth, photo, _rotation_key = row
    price = int(worth) * SHOP_PRICE_MULTIPLIER
    return (
        "🛒 CHARACTER SHOP\n\n"
        f"🎭 {name}\n"
        f"📺 Anime: {anime}\n"
        f"{rarity_text(rarity)}\n"
        f"💎 Worth: {worth} ⦵\n"
        f"🪙 Buy Price: {price} ⦵\n\n"
        f"📦 Shop: {page + 1}/{total}\n"
        "🕓 Daily reset: 4:00 AM IST\n"
        "🔄 Manual refresh: 100 ⦵"
    )

async def render_shop(target, context, user_id, page=0, edit=False):
    try:
        if not (await asyncio.to_thread(ensure_shop_rotation, user_id)):
            raise RuntimeError("shop rotation could not be created")
        rows = (await asyncio.to_thread(get_shop_rows, user_id))
        if len(rows) != 4:
            (await asyncio.to_thread(ensure_shop_rotation, user_id, force=True))
            rows = (await asyncio.to_thread(get_shop_rows, user_id))
        if len(rows) != 4:
            text = "❌ Shop is temporarily unavailable. Please try again later."
            if edit:
                try:
                    await target.edit_message_text(text=text)
                except Exception:
                    pass
            else:
                await safe_reply_text(target.message, text)
            return

        page = int(page) % 4
        row = rows[page]
        caption = add_display_name_header(target.message, build_shop_caption(row, page, 4))
        price = int(row[5]) * SHOP_PRICE_MULTIPLIER
        bought = (await asyncio.to_thread(_mc("shop_purchases_v2").find_one, {"user_id": int(user_id), "rotation_key": row[7], "slot": row[0]})) is not None
        keyboard = shop_keyboard(user_id, page, price, bought=bought)
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
        try:
            balance = (await asyncio.to_thread(mongo_db.get_coins, owner_id))
            if balance is None:
                await query.answer("❌ Your account could not be found.", show_alert=True)
                return
            if int(balance or 0) < SHOP_REFRESH_COST:
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
                    "❌ I couldn't find 4 unused characters for your new shop. Your 100 ⦵ were not deducted.",
                    show_alert=True,
                )
                return

            new_codes = {str(row[0]) for row in new_rows}
            if current_codes & new_codes:
                await query.answer(
                    "❌ New shop still contains an old character. Your 100 ⦵ were not deducted.",
                    show_alert=True,
                )
                return

            # atomic conditional deduct, then swap the 4 shop rows in one transaction
            if not (await asyncio.to_thread(mongo_db.spend_coins, owner_id, SHOP_REFRESH_COST)):
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
                    (await asyncio.to_thread(mongo_db.add_coins, owner_id, SHOP_REFRESH_COST))
                except Exception as undo_err:
                    print("Shop refresh refund error:", undo_err)
            print("Shop refresh error:", e)
            await query.answer("❌ Refresh failed. Your 100 ⦵ were not deducted.", show_alert=True)
            return

        await query.answer("✅ Shop refreshed! -100 ⦵")
        await render_shop(query, context, owner_id, 0, edit=True)
        return

    if action == "buy":
        rows = (await asyncio.to_thread(get_shop_rows, owner_id))
        if len(rows) != 4 or page < 0 or page >= len(rows):
            await query.answer("❌ Shop is unavailable. Try again.", show_alert=True)
            return
        row = rows[page]
        _, code, name, anime, rarity, worth, photo, rotation_key = row
        price = int(worth) * SHOP_PRICE_MULTIPLIER
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

        await query.answer(f"✅ {name} bought for {price} ⦵")
        keyboard = shop_keyboard(owner_id, page, price, bought=True)
        try:
            await query.message.edit_reply_markup(reply_markup=keyboard)
        except Exception as e:
            print("Shop bought-button update error:", e)
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

async def characters(update, context):
    rows = (await asyncio.to_thread(get_all_characters))

    if not rows:
        await safe_reply_text(update.message, "❌ No characters found.")
        return

    text = "🎭 Character List\n\n"
    text += "\n".join(
        f"{i}. {rarity_text(r)} {name} [{code}]"
        for i, (code, name, anime, r, worth, photo) in enumerate(rows, 1)
    )

    for i in range(0, len(text), 3800):
        await safe_reply_text(update.message, text[i:i + 3800])

async def view(update, context):
    (await save_user_async(update.effective_user))
    if not context.args:
        await safe_reply_text(update.message,
            "Usage: /view <4-digit code, first name, last name, or full name>\n"
            "Examples: /view 1001, /view Yuji, /view Itadori, /view Yuji Itadori"
        )
        return

    query = " ".join(context.args).strip()
    character = None

    if query.isdigit():
        character = (await asyncio.to_thread(get_character_by_code, query))
    else:
        name_rows = (await asyncio.to_thread(find_characters_by_name_parts, query))
        if len(name_rows) == 1:
            character = name_rows[0]
        elif len(name_rows) > 1:
            await safe_reply_text(update.message,
                "❓ Multiple characters found. Please use the 4-digit code."
            )
            return
        else:
            rows = (await asyncio.to_thread(mongo_db.find_characters_by_anime, query))
            if len(rows) == 1:
                character = rows[0]
            elif len(rows) > 1:
                await safe_reply_text(update.message,
                    "❓ Multiple characters found. Please use the 4-digit code."
                )
                return

    if not character:
        await safe_reply_text(update.message, "❌ Character not found.")
        return

    code, name, anime, rarity, worth, photo = character

    owned = (await asyncio.to_thread(mongo_db.user_owns, update.effective_user.id, str(code)))
    if not owned:
        await safe_reply_text(update.message, "❌ This character is not in your collection.")
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
        await context.bot.send_photo(
            chat_id=update.message.chat_id,
            photo=photo,
            caption=add_display_name_header(update.message, text),
            parse_mode="HTML",
        )
    else:
        await safe_reply_text(update.message, text + "\n📷 Photo: Not added")

async def add_message(update, context):
    user = update.effective_user
    chat = update.effective_chat
    if not (is_owner(user.id) or is_executive(user.id)):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return
    if not chat or chat.type != "private":
        await safe_reply_text(update.effective_message, "⚠️ /addmessage can only be used in the bot's PM.")
        return

    source = update.effective_message.reply_to_message
    text = " ".join(context.args).strip()
    if not source and not text:
        await safe_reply_text(update.effective_message,
            "Usage:\n"
            "1. Reply to any message in PM and send /addmessage\n"
            "2. Or send /addmessage <message>\n\n"
            "Replying to a message keeps its Telegram formatting/media exactly as a copied message."
        )
        return

    groups = (await asyncio.to_thread(load_bot_groups))
    if not groups:
        await safe_reply_text(update.effective_message, "❌ No linked groups are registered yet.")
        return

    success = 0
    failed = 0
    failed_groups = []

    for raw_chat_id, info in sorted(groups.items(), key=lambda item: str(item[0])):
        try:
            group_id = int(raw_chat_id)
            if source:
                await context.bot.copy_message(
                    chat_id=group_id,
                    from_chat_id=source.chat_id,
                    message_id=source.message_id,
                )
            else:
                await context.bot.send_message(chat_id=group_id, text=text)
            success += 1
        except Exception as e:
            failed += 1
            title = (info or {}).get("title") or str(raw_chat_id)
            failed_groups.append(f"• {title} ({raw_chat_id})")
            print(f"/addmessage broadcast failed for {raw_chat_id}:", e)

    result = (
        "📢 MESSAGE BROADCAST COMPLETE\n\n"
        f"✅ Sent: {success}\n"
        f"❌ Failed: {failed}\n"
        f"👥 Linked groups: {len(groups)}"
    )
    if failed_groups:
        result += "\n\nFailed groups:\n" + "\n".join(failed_groups[:20])
        if len(failed_groups) > 20:
            result += f"\n• ...and {len(failed_groups) - 20} more"
    await safe_reply_text(update.effective_message, result)

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
    lines += ["", "👑 Owners:"]
    for uid, qty in owners:
        u = owner_names.get(int(uid))
        first, last, username = u if u else ("Unknown", "", "")
        display = " ".join(v for v in [first, last] if v).strip() or "Unknown"
        handle = f"@{username}" if username else "No username"
        lines.append(f"• {display} ({handle}) ×{qty}")
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
            "Usage: /check <4-digit code, first name, last name, or full name>",
        )
        return

    character = None

    if query.isdigit():
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
        else:
            recruit_matches = (await asyncio.to_thread(find_characters_by_recruit_name_partial, query))
            if len(recruit_matches) > 1:
                await safe_reply_text(
                    update.message,
                    "❓ Multiple characters found. Select one:",
                    reply_markup=character_selection_keyboard(
                        update.effective_user.id, "check", recruit_matches
                    ),
                )
                return
            if len(recruit_matches) == 1:
                character = recruit_matches[0]

            if not character:
                rows = (await asyncio.to_thread(mongo_db.find_characters_by_anime, query))

                if len(rows) > 1:
                    await safe_reply_text(
                        update.message,
                        "❓ Multiple characters found. Select one:",
                        reply_markup=character_selection_keyboard(
                            update.effective_user.id, "check", rows
                        ),
                    )
                    return
                if len(rows) == 1:
                    character = rows[0]

    if not character:
        rows = (await asyncio.to_thread(mongo_db.find_characters_by_anime, query))

        if len(rows) == 1:
            character = rows[0]
        elif len(rows) > 1:
            await safe_reply_text(
                update.message,
                "❓ Multiple characters found. Select one:",
                reply_markup=character_selection_keyboard(
                    update.effective_user.id, "check", rows
                ),
            )
            return

    if not character:
        await safe_reply_text(update.message, "❌ Character not found.")
        return

    await send_character_check_result(context.bot, update.message.chat_id, character, update.message)

async def sell(update, context):
    (await save_user_async(update.effective_user))

    if not context.args:
        await safe_reply_text(update.message,
            "Usage: /sell <4-digit code, first name, last name, or full name> [quantity]\nExamples: /sell 1001 2, /sell Yuji 2, /sell Itadori"
        )
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

    try:
        await update.message.delete()
    except Exception as e:
        print(f"Sale message delete error: {e}")

    await safe_reply_text(update.message,
        f"💸 Sold {name} [{code}] x{quantity}!\n💰 +{total_value} Berrys"
    )

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

ADD_NAME, ADD_RECRUIT, ADD_ANIME, ADD_RARITY, ADD_WORTH, ADD_CODE, ADD_PHOTO = range(7)

async def addcharacter_start(update, context):
    if update.effective_chat.type != "private":
        await safe_reply_text(update.message, "⚠️ /addcharacter can only be used in the bot's PM (private chat).")
        return ConversationHandler.END
    if not (await asyncio.to_thread(can_manage_characters, update.effective_user.id)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return ConversationHandler.END

    for key in ("name", "anime", "rarity", "worth", "code"):
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
        await safe_reply_text(update.message, "4️⃣ Send worth in Berrys (required):")
        return ADD_WORTH
    rarity = text.title()

    if rarity not in SYMBOL:
        await safe_reply_text(update.message, "❌ Invalid rarity.")
        return ADD_RARITY

    context.user_data["rarity"] = rarity
    await safe_reply_text(update.message, "4️⃣ Send worth in Berrys:")
    return ADD_WORTH

async def addcharacter_worth(update, context):
    try:
        worth = int(update.message.text.strip())
        if worth < 0:
            raise ValueError
    except ValueError:
        await safe_reply_text(update.message, "❌ Worth must be a number.")
        return ADD_WORTH

    context.user_data["worth"] = worth
    await safe_reply_text(update.message, "5️⃣ Send unique 4-digit code:")
    return ADD_CODE

async def addcharacter_code(update, context):
    code = update.message.text.strip()

    if not (code.isdigit() and len(code) == 4 and 1 <= int(code) <= 9999):
        await safe_reply_text(update.message,
            "❌ Code must be exactly 4 digits (0001-9999)."
        )
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
            "Usage: /addphoto <name or code>"
        )
        return

    character = (await asyncio.to_thread(get_character, " ".join(context.args)))

    if not character:
        await safe_reply_text(update.message, "❌ Character not found.")
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
    query = " ".join(context.args).strip()
    character = (await asyncio.to_thread(get_character, query))
    if not character:
        matches = (await asyncio.to_thread(find_characters_by_name_parts, query))
        if len(matches) > 1:
            await safe_reply_text(
                update.message,
                "❓ Multiple characters found. Select one:",
                reply_markup=character_selection_keyboard(update.effective_user.id, "edit", matches),
            )
            return ConversationHandler.END
        recruit_matches = (await asyncio.to_thread(find_characters_by_recruit_name_partial, query))
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
        if rarity not in SYMBOL:
            await safe_reply_text(update.message, "❌ Invalid rarity.")
            return EDIT_RARITY
    context.user_data["edit_rarity"] = rarity
    await safe_reply_text(update.message, "4️⃣ Send new worth, or tap ⏭ Skip to keep current worth.", reply_markup=skip_keyboard())
    return EDIT_WORTH

async def edit_worth(update, context):
    text = update.message.text.strip()
    if is_skip_text(text):
        worth = context.user_data["edit_character"][4]
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
        (await asyncio.to_thread(mongo_db.update_character, old_code, new_code, d["edit_name"], d["edit_anime"],
                                  d["edit_rarity"], d["edit_worth"], new_recruit_names))
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


async def gstats(update, context):
    if not (is_owner(update.effective_user.id) or is_executive(update.effective_user.id)):
        await safe_reply_text(update.effective_message, UNAUTHORIZED_TEXT)
        return

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
        await safe_reply_text(update.effective_message, "⚠️ Could not refresh group membership right now. Please try again.")
        return

    refreshed = {}
    invite_links = {}                      # raw_id -> invite link returned by Telegram (not persisted)
    for raw_id in sorted(known_ids, key=lambda v: int(v)):
        chat_id = int(raw_id)
        info = groups.get(raw_id, {})
        try:
            member = await context.bot.get_chat_member(chat_id, bot_user_id)
            member_status = getattr(member, "status", "")
            member_is_present = getattr(member, "is_member", True)
            if member_status not in ("creator", "administrator", "member", "restricted") or (
                member_status == "restricted" and not member_is_present
            ):
                await cleanup_left_group(chat_id, context)
                continue

            chat = await context.bot.get_chat(chat_id)
            refreshed[raw_id] = {
                "title": (
                    DEFAULT_GSTATS_GROUP_TITLE
                    if chat_id == DEFAULT_GSTATS_GROUP_ID
                    else getattr(chat, "title", None) or getattr(chat, "username", None) or info.get("title") or "Unknown"
                ),
                "type": getattr(chat, "type", info.get("type", "group")),
                "username": getattr(chat, "username", info.get("username")),
            }
            invite_links[raw_id] = getattr(chat, "invite_link", None)
        except (Forbidden, BadRequest) as e:
            reason = str(e).lower()
            if isinstance(e, Forbidden) or any(w in reason for w in (
                    "chat not found", "kicked", "not a member", "bot was kicked", "bot is not a member", "group chat was deleted")):
                print(f"/gstats: bot is no longer in {chat_id} ({e}); removing it")
                await cleanup_left_group(chat_id, context)
            else:                                     # unknown API refusal: keep the group, do not wipe it
                print(f"/gstats refresh error for {chat_id} (kept):", e)
                if info:
                    refreshed[raw_id] = dict(info)
        except Exception as e:                        # network / flood control / timeout: NEVER clean up
            print(f"/gstats membership refresh error for {chat_id} (kept):", e)
            if info:
                refreshed[raw_id] = dict(info)

    groups = refreshed
    (await asyncio.to_thread(save_bot_groups, groups))

    if not groups:
        text = "📊 Group Statistics\n\nTotal Groups: 0"
        if update.callback_query:
            requester = update.callback_query.from_user
            first = (getattr(requester, "first_name", None) or "").strip()
            last = (getattr(requester, "last_name", None) or "").strip()
            display_name = " ".join(part for part in (first, last) if part) or "Unknown"
            await _safe_edit_text(update.callback_query.message, 
                f"👤 {html_escape(display_name)}\n\n{text}",
                parse_mode="HTML",
            )
        else:
            await safe_reply_text(update.effective_message, text)
        return

    lines = ["📊 Group Statistics", "", f"Total Groups: {len(groups)}", ""]
    keyboard = []
    sorted_groups = sorted(
        groups.items(),
        key=lambda item: (
            0 if int(item[0]) == DEFAULT_GSTATS_GROUP_ID else 1,
            (item[1].get("title") or "").casefold(),
        ),
    )
    for i, (chat_id, info) in enumerate(sorted_groups, 1):
        title = info.get("title") or "Unknown"
        status = "🟢 ON" if (await asyncio.to_thread(is_bot_enabled, int(chat_id))) else "🔴 OFF"
        approved = "✅ Approved" if await is_group_approved(int(chat_id)) else "❌ Not Approved"
        lines.append(f"{i}. 🏠 {html_escape(title)}")
        lines.append(f"🆔 Group ID: <code>{chat_id}</code>")      # tap to copy
        group_link = build_group_open_link(chat_id, info.get("username"), invite_links.get(chat_id))
        lines.append(f"🤖 Bot: {status}")
        lines.append(f"🔐 Approval: {approved}")
        lines.append("")
        row = []
        if group_link:
            row.append(InlineKeyboardButton("🔗 Open Link", url=group_link))
        row.append(InlineKeyboardButton(
            f"🗑 Remove: {title[:24]}",
            callback_data=f"gstats:delete:{chat_id}",
        ))
        keyboard.append(row)

    default_info = groups.get(str(DEFAULT_GSTATS_GROUP_ID))
    if default_info:
        default_link = build_group_open_link(
            DEFAULT_GSTATS_GROUP_ID, default_info.get("username"), invite_links.get(str(DEFAULT_GSTATS_GROUP_ID)))
        if default_link:
            lines.append(f'<a href="{html_escape(default_link)}">Telegram Wonderland</a>')

    markup = InlineKeyboardMarkup(keyboard)
    text = "\n".join(lines).rstrip()

    if update.callback_query:
        requester = update.callback_query.from_user
        first = (getattr(requester, "first_name", None) or "").strip()
        last = (getattr(requester, "last_name", None) or "").strip()
        display_name = " ".join(part for part in (first, last) if part) or "Unknown"
        text = f"👤 {html_escape(display_name)}\n\n{text}"
        await _safe_edit_text(update.callback_query.message, 
            text, parse_mode="HTML", reply_markup=markup, disable_web_page_preview=False
        )
    else:
        await safe_reply_text(
            update.effective_message,
            text,
            parse_mode="HTML",
            disable_web_page_preview=False,
            reply_markup=markup,
        )

async def gstats_callback(update, context):
    query = update.callback_query
    user_id = query.from_user.id
    if not (is_owner(user_id) or is_executive(user_id)):
        await deny_callback(query)
        return

    data = query.data or ""
    parts = data.split(":", 2)
    if len(parts) != 3 or parts[1] != "delete" or not parts[2].lstrip("-").isdigit():
        await query.answer("❌ Invalid GStats option.", show_alert=True)
        return

    chat_id = int(parts[2])
    try:
        await query.answer("🗑 Removing group from GStats…")        # answer first (Telegram expires it after ~15 s)
    except Exception:
        pass
    if not (await asyncio.to_thread(hide_gstats_group, chat_id)):
        await safe_reply_text(query.message, "❌ Could not remove this group from GStats.")
        return
    await gstats(update, context)

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
        handle = f" (@{html_escape(username)})" if username else ""
        lines.append(f"{i}. {html_escape(name)}{handle} - ID: {uid}")
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
        f"📥 OWNER PM — NEW ISSUE #{issue_id}\n\n"
        f"👤 Name: {full_name}\n"
        f"🆔 User ID: {user.id}\n"
        f"🔗 Username: {username_str}\n\n"
        f"📝 Issue:\n{text}"
    )

    await notify_admins(context, notification, photo)

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
        f"📥 OWNER PM — NEW IDEA #{idea_id}\n\n"
        f"👤 Name: {full_name}\n"
        f"🆔 User ID: {user.id}\n"
        f"🔗 Username: {username}\n\n"
        f"📝 Idea:\n{text}"
    )

    await notify_admins(context, notification, photo)

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
        f"📥 OWNER PM — NEW APPEAL #{appeal_id}\n\n"
        f"👤 Name: {full_name}\n"
        f"🆔 User ID: {user.id}\n"
        f"🔗 Username: {username}\n\n"
        f"📝 Appeal:\n{text}"
    )

    await notify_admins(context, notification, photo)

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

async def notify_admins(context, text, photo_file_id=None):
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
        try:
            if photo_file_id:
                if len(text) <= 1024:
                    await asyncio.wait_for(
                        context.bot.send_photo(chat_id=staff_id, photo=photo_file_id, caption=text),
                        timeout=15,
                    )
                else:
                    await asyncio.wait_for(
                        context.bot.send_photo(
                            chat_id=staff_id,
                            photo=photo_file_id,
                            caption="📎 Attachment for the submission below.",
                        ),
                        timeout=15,
                    )
                    await asyncio.wait_for(
                        context.bot.send_message(chat_id=staff_id, text=text), timeout=15
                    )
            else:
                await asyncio.wait_for(
                    context.bot.send_message(chat_id=staff_id, text=text), timeout=15
                )
            delivered += 1
            print(f"Staff notification delivered to {staff_id}")
        except asyncio.TimeoutError:
            print(f"Staff notification timeout for {staff_id}")
        except Exception as e:
            print(f"Staff notification error for {staff_id}: {e}")

    print(f"Staff notification result: {delivered}/{len(recipients)} delivered, {skipped} personally OFF")

async def notify_staff_action(context, action_text, actor_id=None, owner_choice=False):
    try:
        if actor_id is not None and is_owner(actor_id):
            return          # Owner actions: no notification, no Yes/No prompt (the 3 allowed ones use the log prompt)
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

async def status(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    active = context.application.bot_data.setdefault("active_spawns", {})
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
    high_gap, celestial_gap = (await asyncio.to_thread(_get_random_spawn_high_rarity_gaps, context.application))
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
    await safe_reply_text(update.message, "\n".join(lines))

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

    claimed = (await asyncio.to_thread(_mc("event_claims_v2").find_one, {"event_id": event_id, "user_id": update.effective_user.id})) is not None

    text = (
        f"🎉 EVENT: {name}\n\n"
        f"{description or 'Special event is live!'}\n\n"
        f"🎁 Reward: {(await asyncio.to_thread(format_reward, reward_type, reward_value))}\n"
        f"💬 Trigger: {trigger_text}\n"
        f"⏰ Ends: {end_text}"
    )
    if claimed:
        text += "\n\n✅ You have already claimed this event reward."
    await safe_reply_text(update.message, text)

EVENT_NAME, EVENT_CODE, EVENT_REWARD_TYPE, EVENT_REWARD_VALUE, EVENT_TRIGGER, EVENT_END_DAY, EVENT_END_MONTH, EVENT_END_YEAR, EVENT_END_HOUR, EVENT_END_MINUTE = range(400,410)

async def add_event_start(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT); return ConversationHandler.END
    await safe_reply_text(update.message, "1️⃣ Event name:"); return EVENT_NAME

async def add_event_name(update, context):
    text=update.message.text.strip()
    if not text or text.startswith("/"):
        await safe_reply_text(update.message, "❌ Event name required."); return EVENT_NAME
    context.user_data["event_name"]=text
    await safe_reply_text(update.message, "2️⃣ Event 2-digit code (00-99):")
    return EVENT_CODE

async def add_event_code(update, context):
    text=update.message.text.strip()
    if not text.isdigit() or len(text)!=2:
        await safe_reply_text(update.message, "❌ Event code must be exactly 2 digits (00-99). Send again:")
        return EVENT_CODE
    exists = (await asyncio.to_thread(_mc("events_v2").find_one, {"active": 1, "event_code": text}))
    if exists:
        await safe_reply_text(update.message, "❌ This event code is already in use. Send another 2-digit code:")
        return EVENT_CODE
    context.user_data["event_code"]=text
    await safe_reply_text(update.message, "3️⃣ Reward type: Berrys or Character")
    return EVENT_REWARD_TYPE

async def add_event_reward_type(update, context):
    text=update.message.text.strip().lower()
    if text not in ("coin", "coins", "berrys", "character"):
        await safe_reply_text(update.message, "❌ Send Berrys or Character."); return EVENT_REWARD_TYPE
    context.user_data["event_reward_type"]="coins" if text in ("coin", "coins", "berrys") else "character"
    await safe_reply_text(update.message, "4️⃣ Send Berrys amount:" if context.user_data["event_reward_type"]=="coins" else "4️⃣ Send character code or character name:")
    return EVENT_REWARD_VALUE

async def add_event_reward_value(update, context):
    text=update.message.text.strip()
    if context.user_data.get("event_reward_type") == "character":
        character = (await asyncio.to_thread(get_character, text))
        if not character:
            await safe_reply_text(update.message, "❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
            return EVENT_REWARD_VALUE
        context.user_data["event_reward_value"] = int(character[0])
    else:
        if not text.isdigit() or int(text)<1:
            await safe_reply_text(update.message, "❌ Send a valid positive number."); return EVENT_REWARD_VALUE
        context.user_data["event_reward_value"]=int(text)
    await safe_reply_text(update.message, "5️⃣ Exact trigger phrase users must type:")
    return EVENT_TRIGGER

async def add_event_trigger(update, context):
    text=update.message.text.strip()
    if not text or text.startswith("/"):
        await safe_reply_text(update.message, "❌ Trigger phrase required and cannot start with /."); return EVENT_TRIGGER
    context.user_data["event_trigger"]=text
    await safe_reply_text(update.message, "6️⃣ Send end date — DD (day) only:")
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
    def _create_event(session):
        _mc("events_v2").update_many({"active": 1}, {"$set": {"active": 0}}, session=session)
        mongo_db.insert_with_id("events_v2", {
            "name": d["event_name"], "event_code": d["event_code"], "description": "",
            "reward_type": d["event_reward_type"], "reward_value": d["event_reward_value"],
            "end_at": end_at, "active": 1, "created_at": timestamp(), "trigger_text": d["event_trigger"],
        }, session=session)
    (await asyncio.to_thread(mongo_db.run_transaction, _create_event))
    _EVENT_CACHE["val"] = None
    context.user_data.clear()
    await safe_reply_text(update.message, f"✅ Event created!\n🎉 {d['event_name']} [{d['event_code']}]\n🎁 {(await asyncio.to_thread(format_reward, d['event_reward_type'],d['event_reward_value']))}\n💬 Trigger: {d['event_trigger']}\n⏰ Ends: {dt.strftime('%d %m %y %I:%M %p')}", reply_markup=ReplyKeyboardRemove())
    await notify_staff_action(context, f"🎉 EVENT ADDED\n🎉 {d['event_name']} [{d['event_code']}]\n🎁 Reward: {(await asyncio.to_thread(format_reward, d['event_reward_type'],d['event_reward_value']))}\n💬 Trigger: {d['event_trigger']}\n⏰ Ends: {dt.strftime('%d %m %y %I:%M %p')}\n👤 By: {display_user(update.effective_user)}", actor_id=update.effective_user.id)
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
    # the unique (event_id, user_id) index makes a double claim impossible
    try:
        claim_id = (await asyncio.to_thread(claims.insert_one, {"event_id": event_id, "user_id": uid, "claimed_at": timestamp()})).inserted_id
    except mongo_db.DuplicateKeyError:
        return

    granted_id = None
    coins_given = False
    try:
        if reward_type == "coins":
            if not (await asyncio.to_thread(mongo_db.add_coins, uid, int(reward_value))):
                raise RuntimeError("event reward user missing")
            coins_given = True
            reward = f"🪙 {reward_value} Berrys"
        else:
            char_row = (await asyncio.to_thread(mongo_db.get_character_by_code, str(reward_value)))
            if not char_row:
                (await asyncio.to_thread(claims.delete_one, {"_id": claim_id}))
                return
            granted_id = (await asyncio.to_thread(mongo_db.add_collection, uid, reward_value, timestamp()))
            reward = f"🎭 {char_row[1]} [{reward_value}]"
    except Exception as e:
        try:
            (await asyncio.to_thread(claims.delete_one, {"_id": claim_id}))
        except Exception as undo_err:
            print("Event reward undo error:", undo_err)
        if coins_given:
            try:
                (await asyncio.to_thread(mongo_db.add_coins, uid, -int(reward_value)))
            except Exception as undo_err:
                print("Event reward undo error:", undo_err)
        if granted_id is not None:
            try:
                (await asyncio.to_thread(mongo_db.delete_collection_by_id, granted_id))
            except Exception as undo_err:
                print("Event reward undo error:", undo_err)
        print("Event reward error:", e)
        return
    await safe_reply_text(update.message, f"🎉 Event reward!\n🎁 {reward}")

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
        await safe_reply_text(update.message, "❌ This event has no 2-digit code and cannot be manually ended. Create a new event with a code.")
        return ConversationHandler.END
    await safe_reply_text(update.message, "🔚 Send the 2-digit event code (00-99):")
    return END_EVENT_CODE

async def end_event_confirm(update, context):
    text = update.message.text.strip()
    if not text.isdigit() or len(text) != 2:
        await safe_reply_text(update.message, "❌ Event code must be exactly 2 digits (00-99). Send again:")
        return END_EVENT_CODE
    ev = (await asyncio.to_thread(_mc("events_v2").find_one, {"active": 1}, sort=[("_id", -1)]))
    if not ev:
        await safe_reply_text(update.message, "ℹ️ No active event.")
        return ConversationHandler.END
    event_id, name, code = ev["_id"], ev.get("name"), ev.get("event_code")
    if text != (code or ""):
        await safe_reply_text(update.message, "❌ Wrong event code. Send the correct 2-digit code:")
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

async def add_redeem_start(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return ConversationHandler.END
    context.user_data.pop("redeem_type", None)
    context.user_data.pop("redeem_reward", None)
    context.user_data.pop("redeem_count", None)
    context.user_data.pop("redeem_expiry", None)
    await safe_reply_text(update.message, "1️⃣ Reward type: Character or Berrys")
    return REDEEM_TYPE

async def add_redeem_type(update, context):
    text = update.message.text.strip().lower()
    if text not in ("character", "berrys"):
        await safe_reply_text(update.message, "❌ Send Character or Berrys.")
        return REDEEM_TYPE

    context.user_data["redeem_type"] = "coins" if text == "berrys" else "character"
    await safe_reply_text(update.message,
        "2️⃣ Existing character code or name:" if context.user_data["redeem_type"] == "character"
        else "2️⃣ Berrys amount:"
    )
    return REDEEM_REWARD

async def add_redeem_reward(update, context):
    text = update.message.text.strip()
    typ = context.user_data["redeem_type"]

    if typ == "character":
        char = (await asyncio.to_thread(get_character, text))
        if not char:
            await safe_reply_text(update.message, "❌ Character not found. Use a 4-digit code, first name, last name, or full name.")
            return REDEEM_REWARD
        value = char[0]
    else:
        if not text.isdigit() or int(text) <= 0:
            await safe_reply_text(update.message, "❌ Berrys amount must be positive.")
            return REDEEM_REWARD
        value = text

    context.user_data["redeem_reward"] = value
    await safe_reply_text(update.message, "3️⃣ How many users can redeem this code? Send a positive number:")
    return REDEEM_COUNT

async def add_redeem_count(update, context):
    text = update.message.text.strip()
    if not text.isdigit() or int(text) <= 0:
        await safe_reply_text(update.message, "❌ Redeem count must be a positive number.")
        return REDEEM_COUNT

    context.user_data["redeem_count"] = int(text)
    await safe_reply_text(update.message,
        "4️⃣ Expiry duration:\n"
        "Examples: 24h, 7d, 2d 12h\n"
        "Send 0 for no expiry."
    )
    return REDEEM_EXPIRY

def parse_redeem_expiry(value):
    raw = value.strip().lower()
    if raw in ("0", "never", "none", "no"):
        return None, None

    matches = re.findall(r"(\d+)\s*(d|h|m)", raw)
    if not matches:
        return None, "❌ Invalid expiry. Use examples like `24h`, `7d`, or `2d 12h`, or send `0` for no expiry."

    normalized = re.sub(r"(\d+)\s*(d|h|m)", "", raw)
    if normalized.strip():
        return None, "❌ Invalid expiry. Use examples like `24h`, `7d`, or `2d 12h`, or send `0` for no expiry."

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
    await safe_reply_text(update.message, "5️⃣ Send a unique 6-digit redeem code:")
    return REDEEM_CODE

async def add_redeem_code(update, context):
    code = update.message.text.strip()
    if not (code.isdigit() and len(code) == 6):
        await safe_reply_text(update.message, "❌ Redeem code must be exactly 6 digits.")
        return REDEEM_CODE

    d = dict(context.user_data)
    try:
        (await asyncio.to_thread(_mc("redeem_codes_v2").insert_one, {
            "_id": code, "code": code, "reward_type": d["redeem_type"], "reward_value": d["redeem_reward"],
            "created_at": timestamp(), "active": 1, "max_claims": d["redeem_count"],
            "expires_at": d["redeem_expiry"],
        }))
    except mongo_db.DuplicateKeyError:
        await safe_reply_text(update.message, "❌ Redeem code already exists.")
        return REDEEM_CODE
    except Exception as e:
        print("Redeem creation error:", e)
        await safe_reply_text(update.message, "❌ Could not create redeem code. Please try again.")
        return REDEEM_CODE

    reward_type = d["redeem_type"]
    reward_value = d["redeem_reward"]
    max_claims = d["redeem_count"]
    expiry = d["redeem_expiry"]

    if expiry:
        expiry_text = expiry.replace("T", " ") + " (local time)"
    else:
        expiry_text = "Never"

    context.user_data.clear()
    await safe_reply_text(update.message,
        f"✅ Redeem created!\n"
        f"🎟️ {code}\n"
        f"🎁 {(await asyncio.to_thread(format_reward, reward_type, reward_value))}\n"
        f"👥 Limit: {max_claims} users\n"
        f"⏳ Expiry: {expiry_text}"
    )
    await release_conv_log(context, update.effective_user.id, "addredeem")
    return ConversationHandler.END

async def redeem(update, context):
    (await save_user_async(update.effective_user))
    if len(context.args) != 1:
        await safe_reply_text(update.message, "Usage: /redeem CODE")
        return

    code = context.args[0].strip()
    if not (code.isdigit() and len(code) == 6):
        await safe_reply_text(update.message, "❌ Redeem code must be exactly 6 digits.")
        return

    user_id = update.effective_user.id
    codes = _mc("redeem_codes_v2")
    claims = _mc("redeem_claims_v2")
    granted_id = None
    coins_given = False
    claim_id = None

    try:
        row = (await asyncio.to_thread(codes.find_one, {"_id": code}))
        if not row or not row.get("active"):
            await safe_reply_text(update.message, "❌ Invalid or inactive redeem code.")
            return

        reward_type = row.get("reward_type")
        reward_value = row.get("reward_value")
        max_claims = row.get("max_claims")
        expires_at = row.get("expires_at")

        if expires_at:
            try:
                if datetime.now() >= datetime.fromisoformat(expires_at):
                    (await asyncio.to_thread(codes.update_one, {"_id": code}, {"$set": {"active": 0}}))
                    await safe_reply_text(update.message, "⏰ This redeem code has expired.")
                    await notify_staff_action(
                        context,
                        f"⏰ REDEEM CODE EXPIRED\n🎟️ Code: {code}\n⏰ Expired: {expires_at.replace('T', ' ')}\n👤 Checked by: {display_user(update.effective_user)}",
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

        if reward_type == "coins":
            if not (await asyncio.to_thread(mongo_db.add_coins, user_id, int(reward_value))):
                (await asyncio.to_thread(claims.delete_one, {"_id": claim_id}))
                await safe_reply_text(update.message, "❌ User account could not be updated. Try /start first.")
                return
            coins_given = True
        else:
            if not (await asyncio.to_thread(mongo_db.get_character_by_code, str(reward_value))):
                (await asyncio.to_thread(claims.delete_one, {"_id": claim_id}))
                await safe_reply_text(update.message, "❌ This redeem reward is no longer available.")
                return
            granted_id = (await asyncio.to_thread(mongo_db.add_collection, user_id, reward_value, timestamp()))

        if max_claims is not None and claim_count + 1 >= int(max_claims):
            (await asyncio.to_thread(codes.update_one, {"_id": code}, {"$set": {"active": 0}}))
    except Exception as e:
        # take back anything already granted so a failure never leaves a half-redeemed code
        if claim_id is not None:
            try:
                (await asyncio.to_thread(claims.delete_one, {"_id": claim_id}))
            except Exception as undo_err:
                print("Redeem undo error:", undo_err)
        if coins_given:
            try:
                (await asyncio.to_thread(mongo_db.add_coins, user_id, -int(reward_value)))
            except Exception as undo_err:
                print("Redeem undo error:", undo_err)
        if granted_id is not None:
            try:
                (await asyncio.to_thread(mongo_db.delete_collection_by_id, granted_id))
            except Exception as undo_err:
                print("Redeem undo error:", undo_err)
        print("Redeem error:", e)
        await safe_reply_text(update.message, "❌ Redeem failed. Please try again.")
        return

    await safe_reply_text(update.message,
        f"🎉 Redeemed successfully!\n🎁 {(await asyncio.to_thread(format_reward, reward_type, reward_value))}"
    )
    redeem_notification = (
        f"🎟️ REDEEM CODE USED\n"
        f"🎟️ Code: {code}\n"
        f"🎁 Reward: {(await asyncio.to_thread(format_reward, reward_type, reward_value))}\n"
        f"👤 Redeemed by: {display_user(update.effective_user)}"
    )
    if max_claims is not None and claim_count + 1 >= int(max_claims):
        redeem_notification += f"\n👥 Final usage: {claim_count + 1}/{max_claims}"
        redeem_notification = "🔴 REDEEM CODE LIMIT REACHED\n" + redeem_notification
    await notify_staff_action(
        context,
        redeem_notification,
        actor_id=user_id,
        owner_choice=True,
    )

async def delete_redeem(update, context):
    if not is_owner(update.effective_user.id):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
        return
    if len(context.args) != 1:
        await safe_reply_text(update.message, "Usage: /deleteredeem CODE")
        return
    code = context.args[0].upper()
    changed = (await asyncio.to_thread(_mc("redeem_codes_v2").update_one, {"_id": code}, {"$set": {"active": 0}})).matched_count
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
    rows = [(d["_id"], d.get("reward_type"), d.get("reward_value"), d.get("max_claims"), d.get("expires_at"))
            for d in _code_docs]

    if not rows:
        pass
        await safe_reply_text(update.message, "🎟️ No active redeem codes.")
        return

    lines = ["🎟️ Active Redeem Codes:"]
    now = datetime.now()

    for code, reward_type, reward_value, max_claims, expires_at in rows:
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
            f"• {code} → {(await asyncio.to_thread(format_reward, reward_type, reward_value))}\n"
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

async def send_expiry_notice(app, chat_id, spawn):
    history_id = spawn.get("history_id")
    notice_lock = app.bot_data.setdefault("expiry_notice_lock", asyncio.Lock())

    async with notice_lock:
        if history_id:
            try:
                row = (True,) if (await asyncio.to_thread(mongo_db.sh_is_expiry_notified, history_id)) else None
                if row and row[0]:
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
            except Exception as e:
                print(f"Expiry notification error for {chat_id} (attempt {attempt + 1}/3): {e}")
                if attempt < 2:
                    await asyncio.sleep(1)
        return False

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

    if chat_id not in next_auto:
        next_auto[chat_id] = now_dt + timedelta(seconds=AUTO_SPAWN_INTERVAL)
        return

    if now_dt < next_auto[chat_id]:
        return

    last_activity = app.bot_data.setdefault("last_group_member_activity", {}).get(chat_id)
    if not last_activity or (now_dt - last_activity).total_seconds() > 300:
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
                        expired_redeems.append((rc["_id"], rc.get("reward_type"), rc.get("reward_value"), rc["expires_at"]))
                except (TypeError, ValueError):
                    continue
            for code, reward_type, reward_value, expires_at in expired_redeems:
                if (await asyncio.to_thread(rc_col.update_one, {"_id": code, "active": 1}, {"$set": {"active": 0}})).modified_count:
                    notifications.append(
                        f"⏰ REDEEM CODE EXPIRED AUTOMATICALLY\n🎟️ Code: {code}\n"
                        f"🎁 Reward: {(await asyncio.to_thread(format_reward, reward_type, reward_value))}\n"
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

async def cancel_conversation(update, context):
    if update.effective_user:
        drop_conv_log(context, update.effective_user.id)           # a cancelled command never gets a log prompt
    for key in (
        "name", "recruit_names", "anime", "rarity", "worth", "code",
        "photo_code",
        "edit_code_original", "edit_character", "edit_name",
        "edit_recruit_names", "edit_anime", "edit_rarity", "edit_worth",
        "callchar_character_query",
        "issue_text", "issue_photo",
        "idea_text", "idea_photo",
        "appeal_text", "appeal_photo",
        "event_name", "event_code", "event_reward_type",
        "event_reward_value", "event_trigger",
        "event_end", "event_end_day", "event_end_month",
        "event_end_year", "event_end_hour", "event_end_minute",
        "redeem_type", "redeem_reward", "redeem_count",
        "redeem_expiry",
    ):
        context.user_data.pop(key, None)

    await safe_reply_text(
        update.effective_message,
        "❌ Cancelled. The active process has been stopped and its temporary data cleared."
    )
    return ConversationHandler.END

# ==========================================================================
# LOG CHANNEL (Owner only) + BOT RULES
# ==========================================================================
# Log categories: name -> (title, description, commands). Commands not listed fall into "general".
LOG_CATEGORIES = {
    "character": ("Character events",
                  "Spawns, catches, adding/editing/deleting characters, gifts, collection changes",
                  {"spawn", "callcharacter", "add", "addcharacter", "addphoto",
                   "editcharacter", "gift", "removechar", "delete", "discontinue", "continue", "clearspawn"}),
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
               {"approve", "removeapprove", "leavegroup", "boton", "botoff", "status",
                "history", "gstats", "addmessage", "setrules", "resetrules"}),
    "general": ("General", "Every other command (collection, stats, characters, view, check ...)", set()),
}
LOG_CATEGORY_OF = {cmd: cat for cat, (_t, _d, cmds) in LOG_CATEGORIES.items() for cmd in cmds}
# Owner "Category A": logged to the log channel automatically, no confirmation.
OWNER_AUTO_LOG_CATEGORIES = {"character"}
# Never logged in any way (no log entry, no security entry, no prompt) - /callcharacter is Owner-only and silent.
SILENT_LOG_COMMANDS = {"callcharacter"}
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
OWNER_LOG_ALLOWED = {"addcharacter", "editcharacter", "spawn", "add"}
# Commands that are logged only when the handler explicitly calls mark_success(update).
EXPLICIT_SUCCESS_COMMANDS = {"spawn", "add"}
LOG_MAX_CHANNELS = 10
# Extra routable "category": unauthorized-attempt (security) entries can go to their own channel.
ROUTABLE_EXTRA_CATEGORIES = {"security": "Unauthorized command / button attempts"}
# Never logged: the log/rules management commands themselves and trivial navigation commands.
# Commands that are never logged. Extend without editing code: LOG_IGNORED_EXTRA="skip,notifications"
LOG_IGNORED_COMMANDS = {
    "start", "help", "cancel", "rules",
    "setlog", "unsetlog", "log", "nolog", "logcategories", "logchannel", "addcategory", "removecategory",
    "logmap", "unlogmap", "logmappings", "logroute", "unlogroute", "logroutes", "logdefault",
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
            await app.bot.send_message(chat_id=chat_id, text=text[:4096])
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


async def _send_log_prompt(context, user_id, text, category, command, chat_id):
    """Send the Owner the Yes/No prompt (pending approval is stored in MongoDB, so it survives restarts)."""
    token = str(uuid.uuid4())
    await asyncio.to_thread(
        mongo_db.create_log_prompt, token, user_id,
        {"text": text, "category": category, "command": command, "chat_id": chat_id})
    await context.bot.send_message(
        chat_id=user_id,
        text="📝 Do you want to upload this action log to the log channel?\n\n" + text,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("✅ Yes", callback_data=f"lg:y:{token}"),
            InlineKeyboardButton("❌ No", callback_data=f"lg:n:{token}"),
        ]]),
    )


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
    if not is_owner(query.from_user.id):
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
        await query.edit_message_text("✅ Confirmed — action log queued for the log channel.\n\n" + text)
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


async def rules_command(update, context):
    msg = update.effective_message
    doc = await asyncio.to_thread(mongo_db.get_rules)
    if not doc:
        await safe_reply_text(msg, "📜 No bot rules have been set yet.")
        return
    text = doc["text"]
    raw = bool(context.args) and context.args[0].lower() == "noformat"
    if raw:
        for chunk in _split_chunks(text):
            await safe_reply_text(msg, chunk)               # plain text: markdown stays visible and copyable
        return
    chunks = _split_chunks("📜 Bot Rules\n\n" + text)
    for chunk in chunks:
        try:
            await safe_reply_text(msg, chunk, parse_mode="Markdown")
        except Exception:                                   # unbalanced markdown: fall back to plain text
            await safe_reply_text(msg, chunk)


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
    if user is None or not is_owner(user.id):
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
    "removechar": "Remove a character from any user collection",
    "myfav": "Set favourite character",
    "mystats": "View your stats",
    "daily": "Claim daily reward",
    "characters": "List characters",
    "view": "View a character",
    "check": "Check character details and owners",
    "sell": "Sell a character",
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
    "cooldown": "View character cooldowns for this group",
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
    "addphoto": "Add character photo",
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
    "removeapprove": "Owner/trusted Executive: remove group approval (PM: /removeapprove <group_chat_id>)",
    "addgroupapprove": "Owner: give an Executive group approval permission",
    "removegroupapprove": "Owner: remove an Executive's group approval permission",
    "leavegroup": "Owner: remove a group and make the bot leave it (PM: /leavegroup <group_chat_id>)",
    "boton": "Owner/Executive: turn bot ON (PM: /boton <group_chat_id>)",
    "botoff": "Owner/Executive: turn bot OFF (PM: /botoff <group_chat_id>)",
    "status": "Owner: bot status and active spawns",
    "gstats": "Owner: list groups where bot is added",
    "restrict": "Owner/Executive: restrict by reply or user ID + duration + optional reason",
    "unrestrict": "Owner/Executive: remove restriction by reply or user ID",
    "restrictions": "Owner/Executive: view active restrictions",
    "notifications": "PM: Your personal staff notification ON/OFF",
    "notificationoff": "Owner/Executive/Scout: turn your own PM notifications OFF",
    "notificationon": "Owner/Executive/Scout: turn your own PM notifications ON",
    "notificationhistory": "Owner/Executive/Scout: view your personal notification history",
    "addmessage": "Owner/Executive: broadcast a message to linked groups (PM only)",
    "btransfer": "Owner/Executive: block transfer between two user IDs",
    "unbtransfer": "Owner/Executive: remove transfer block between two user IDs",
    "setrules": "Owner/Executive: set the bot usage rules (PM only)",
    "resetrules": "Owner: clear all bot usage rules (PM only)",
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
}

PUBLIC_COMMANDS = {
    "executives", "scouts", "scout",
    "start", "help", "spawn", "add", "mycollection", "myfav", "mystats", "addlist",
    "daily", "characters", "view", "check", "sell", "transfer", "issue", "idea",
    "appeal", "cancel", "event", "redeem", "berrytransfer", "berry",
    "shop", "exchange", "guess_num", "nguess", "cooldown", "rules"
}

def make_bot_commands(names):
    return [BotCommand(name, COMMANDS[name]) for name in names if name in COMMANDS]

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
        names = PUBLIC_COMMANDS | EXECUTIVE_COMMANDS
        if (await asyncio.to_thread(has_group_approval_permission, user_id)):
            names |= {"approve", "removeapprove"}
    elif (await asyncio.to_thread(is_scout, user_id)):
        names = PUBLIC_COMMANDS | SCOUT_COMMANDS
    else:
        names = PUBLIC_COMMANDS
    try:
        await bot.set_my_commands(
            make_bot_commands(sorted(names)),
            scope=BotCommandScopeChat(chat_id=user_id),
        )
    except Exception as e:
        print(f"Command menu refresh error for {user_id}:", e)

async def startup_init(app):
    _SECURITY_APP["app"] = app
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
        cached |= set(PUBLIC_COMMANDS) | set(OWNER_COMMANDS) | set(EXECUTIVE_COMMANDS) | set(SCOUT_COMMANDS)
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

    if not chat or chat.type not in ("group", "supergroup"):
        if command_name:
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
    msg = await get_restricted_message(update)
    if msg:
        try:
            await query.answer("You are currently restricted.", show_alert=True)
            if _warning_allowed(context.application, chat.id, interval=10):
                await safe_reply_text(query.message, msg)
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
    if target.id == uid or is_owner(target.id) or is_executive(target.id):
        await safe_reply_text(update.message, "❌ You cannot restrict the Owner or an Executive.")
        return

    expiry = int(datetime.now().timestamp()) + seconds
    data = (await asyncio.to_thread(load_restrictions))
    data[str(target.id)] = {
        "expiry": expiry,
        "duration": f"{amount}{unit}",
        "reason": reason,
        "restricted_by": uid,
        "restricted_by_name": update.effective_user.first_name or "Unknown",
        "restricted_by_username": update.effective_user.username or "",
        "target_name": target.first_name or "Unknown",
        "target_username": getattr(target, "username", "") or "",
        "created_at": int(datetime.now().timestamp()),
    }
    (await asyncio.to_thread(save_restrictions, data))
    reason_line = f"\n📝 Reason: {reason}" if reason else "\n📝 Reason: Not provided"
    await safe_reply_text(update.message,
        f"🔒 User {target.first_name} has been restricted successfully.\n"
        f"⏳ Duration: {amount}{unit}\n"
        f"⌛ Remaining: {format_remaining(seconds)}"
        f"{reason_line}\n"
        "The restriction will expire automatically."
    )
    target_handle = f"@{getattr(target, 'username', '')}" if getattr(target, 'username', '') else "No username"
    await notify_staff_action(
        context,
        f"🔒 USER RESTRICTED\n"
        f"👤 User: {target.first_name} | ID: {target.id} | {target_handle}\n"
        f"⏳ Duration: {amount}{unit}\n"
        f"📝 Reason: {reason or 'Not provided'}\n"
        f"👮 Restricted by: {display_user(update.effective_user)}",
        actor_id=update.effective_user.id,
    )

async def restrictions_list(update, context):
    uid = update.effective_user.id
    if not (is_owner(uid) or is_executive(uid)):
        await safe_reply_text(update.message, UNAUTHORIZED_TEXT)
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
            duration = entry.get("duration") or "Unknown"
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

    removed_entry = data.get(str(target_id), {})
    data.pop(str(target_id), None)
    (await asyncio.to_thread(save_restrictions, data))
    await safe_reply_text(update.message,
        f"🔓 User {target_name} restriction removed successfully.\n"
        f"🆔 User ID: {target_id}"
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
    "addcharacter", "addphoto", "editcharacter", "restrict", "unrestrict", "restrictions",
    "clearspawn", "boton", "botoff", "addscout", "removescout", "notifications", "notificationoff", "notificationon", "notificationhistory", "addmessage",
    "btransfer", "unbtransfer", "gstats", "setrules",
}
SCOUT_COMMANDS = {
    "addcharacter", "addphoto", "editcharacter", "clearspawn", "notifications", "notificationoff", "notificationon",
}
def register_executive_commands(app):
    app.add_handler(CommandHandler("addphoto", addphoto))
    app.add_handler(CommandHandler(["scouts", "scout"], scout_list_command))
    app.add_handler(CommandHandler("restrict", restrict))
    app.add_handler(CommandHandler("unrestrict", unrestrict))
    app.add_handler(CommandHandler("restrictions", restrictions_list))
    app.add_handler(CommandHandler("botoff", bot_off))
    app.add_handler(CommandHandler("notifications", notifications_command))
    app.add_handler(CommandHandler("notificationoff", notificationoff_command))
    app.add_handler(CommandHandler("notificationon", notificationon_command))
    app.add_handler(CommandHandler("notificationhistory", notification_history_command))
    app.add_handler(CommandHandler("addmessage", add_message))
    app.add_handler(CommandHandler("btransfer", block_transfer_pair))
    app.add_handler(CommandHandler("unbtransfer", unblock_transfer_pair))
    app.add_handler(CommandHandler("clearspawn", clearspawn))

    edit_conv = ConversationHandler(
        entry_points=[
            CommandHandler("editcharacter", editcharacter),
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
            ADD_WORTH: [MessageHandler(filters.TEXT & ~filters.COMMAND, addcharacter_worth)],
            ADD_CODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, addcharacter_code)],
            ADD_PHOTO: [MessageHandler(filters.PHOTO, addcharacter_photo), MessageHandler(filters.Regex(r"^⏭ Skip$"), addcharacter_photo), CommandHandler("skip", addcharacter_photo)],
        },
        fallbacks=[CommandHandler("cancel", cancel_conversation), CommandHandler("skip", skip_conversation)],
        allow_reentry=True,
        conversation_timeout=CONV_TIMEOUT,
    )
    app.add_handler(add_conv)

OWNER_COMMANDS = {
    "callcharacter", "clearspawn", "gift", "delete", "discontinue", "continue",
    "addexec", "removeexec", "addscout", "removescout",
    "addevent", "endevent", "addredeem", "deleteredeem", "redeems", "history",
    "approve", "removeapprove", "addgroupapprove", "removegroupapprove", "leavegroup", "removechar", "boton",
    "status", "gstats", "notifications", "notificationoff", "notificationon",
    "notificationhistory",
    "setrules", "resetrules", "setlog", "unsetlog", "logchannel", "log", "nolog", "logcategories",
    "addcategory", "removecategory", "logmap", "unlogmap", "logmappings",
    "logroute", "unlogroute", "logroutes", "logdefault",
}
OWNER_COMMANDS = OWNER_COMMANDS | EXECUTIVE_COMMANDS | SCOUT_COMMANDS      # Owner section lists everything (gating unchanged)

def register_owner_commands(app):
    app.add_handler(CommandHandler("removechar", removechar))
    app.add_handler(CommandHandler("gift", gift))
    app.add_handler(CommandHandler("delete", delete))
    app.add_handler(CommandHandler("discontinue", discontinue_command))
    app.add_handler(CommandHandler("continue", continue_command))
    app.add_handler(CommandHandler("executives", executives))
    app.add_handler(CommandHandler("addexec", addexec))
    app.add_handler(CommandHandler("removeexec", removeexec))
    app.add_handler(CommandHandler("addscout", addscout))
    app.add_handler(CommandHandler("removescout", removescout))
    app.add_handler(CommandHandler("history", history))
    app.add_handler(CommandHandler("status", status))
    app.add_handler(CommandHandler("gstats", gstats))
    app.add_handler(CommandHandler("approve", approve_group))
    app.add_handler(CommandHandler("removeapprove", remove_approval))
    app.add_handler(CommandHandler("addgroupapprove", add_group_approval_permission))
    app.add_handler(CommandHandler("removegroupapprove", remove_group_approval_permission))
    app.add_handler(CommandHandler("leavegroup", leave_group))
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
            EVENT_REWARD_TYPE: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_reward_type)],
            EVENT_REWARD_VALUE: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_reward_value)],
            EVENT_TRIGGER: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_event_trigger)],
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
    setup_database()

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
    app.add_handler(MessageHandler(filters.ChatType.GROUPS, track_group_chat, block=False), group=-101)

    app.add_handler(MessageHandler(filters.ALL, block_unapproved_group), group=-100)
    app.add_handler(CallbackQueryHandler(block_unapproved_callback), group=-100)
    # Strict role check for restricted commands: after the approved-group check, before every real handler.
    app.add_handler(MessageHandler(filters.COMMAND & filters.UpdateType.MESSAGE, role_gate), group=-90)
    app.add_handler(CallbackQueryHandler(exchange_callback, pattern=r"^ex_(accept|decline):"))
    app.add_handler(CallbackQueryHandler(character_selection_callback, pattern=r"^charselect:check:"))
    app.add_handler(ChatMemberHandler(track_bot_membership, ChatMemberHandler.MY_CHAT_MEMBER), group=-2)

    public_handlers = (
        ("start", start),
        ("help", help_command),
        ("spawn", spawn),
        ("add", add),
        ("mycollection", mycollection),
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
        ("cooldown", cooldown),
    )
    for command_name, callback in public_handlers:
        app.add_handler(CommandHandler(command_name, callback))

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

    app.add_handler(CallbackQueryHandler(gstats_callback, pattern=r"^gstats:delete:-?\d+$"))
    app.add_handler(CallbackQueryHandler(owner_notification_callback, pattern=r"^owner_notify:(yes|no)$"), group=-1)
    app.add_handler(CallbackQueryHandler(help_callback, pattern=r"^help:"))
    app.add_handler(CallbackQueryHandler(event_claim_callback, pattern=r"^event:"))
    app.add_handler(CallbackQueryHandler(transfer_callback, pattern=r"^tr_(accept|decline):"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, event_trigger_message))

    app.add_handler(CommandHandler("cancel", cancel_conversation))
    app.add_handler(CommandHandler("skip", skip_conversation))

    app.add_handler(CallbackQueryHandler(collection_callback, pattern=r"^coll:"))
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
