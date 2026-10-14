"""
Group moderation bot - a Rose-style Telegram group management bot.

Files:
    nova.py              this file: core bot logic, handlers and the entry point (python nova.py)
    extra.py             utilities, AI/search helpers, auto-ads + promotion blocker, logging, the Render keep-alive web server
    fun_systems.py       games and entertainment: roast battles, court
    migrate_to_mongo.py  the MongoDB data layer + the one-time SQLite -> MongoDB import

Setup:
    pip install -r requirements.txt
    Put these in .env next to this script (on Render: the Environment tab):
        BOT_TOKEN=your-token-from-BotFather
        MONGO_URI=mongodb+srv://user:password@cluster.mongodb.net/
        OWNER_IDS=your-telegram-user-id
        GEMINI_API_KEY=optional, for the AI commands
    python nova.py

Import an existing rose_clone.db once:  python migrate_to_mongo.py rose_clone.db
(or just leave rose_clone.db next to nova.py: it is imported automatically while MongoDB is empty).
Never commit .env to version control.

Add the bot to your group and make it admin (delete messages, ban users,
restrict members, pin messages).
"""

import os
import re
import sys

from dotenv import load_dotenv

_HERE = os.path.dirname(os.path.abspath(__file__))
load_dotenv()  # loads key=value pairs from a local .env file into the environment
_ENV_NAMES = ("env", "env.txt", "bot.env", "bot.env.txt", ".env")
for _dir in dict.fromkeys((_HERE, os.getcwd())):  # script folder first, then current folder
    for _name in _ENV_NAMES:  # first one found wins; "env" is phone-friendly
        load_dotenv(os.path.join(_dir, _name))

# =====================================================================
#  BOT TOKEN  -  read from the BOT_TOKEN environment variable / .env file
# =====================================================================
BOT_TOKEN = os.environ.get("BOT_TOKEN")
# =====================================================================
#  PRIMARY BOT OWNER  -  Telegram USER IDs (positive numbers, never a group/channel ID) that
#  may use Bot Edit (/bot) and manage Super Admins. Super Admins and group owners/admins can NOT
#  use Bot Edit. (send /id to the bot to see your own ID), e.g. OWNER_IDS = [123456789]
# =====================================================================
# Comma/space separated list in the OWNER_IDS environment variable; the default keeps the old owner.
# Only positive numbers count: Telegram user IDs are positive, group/channel IDs are negative.
OWNER_IDS = [int(x) for x in re.split(r"[,\s]+", os.environ.get("OWNER_IDS", "5675165124").strip())
             if x.isascii() and x.isdigit() and int(x) > 0]
# =====================================================================

import asyncio
import contextvars
import functools
import hashlib
import html
import logging
import random
import re
import time
from collections import defaultdict
from datetime import datetime, timedelta, timezone

from telegram import (
    BotCommand,
    BotCommandScopeAllChatAdministrators,
    BotCommandScopeAllGroupChats,
    BotCommandScopeAllPrivateChats,
    BotCommandScopeChat,
    BotCommandScopeChatAdministrators,
    BotCommandScopeChatMember,
    BotCommandScopeDefault,
    ChatPermissions,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Update,
)
from telegram.constants import ChatMemberStatus
from telegram.error import BadRequest, Forbidden, RetryAfter, TelegramError
from telegram.request import HTTPXRequest
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    ChatMemberHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

try:  # needed to change the bot's own profile photo (Bot API 9.4+, newer PTB)
    from telegram import InputProfilePhotoStatic
except ImportError:
    InputProfilePhotoStatic = None

import traceback

try:
    import extra  # utilities, AI/search/fun helpers, logging + Render keep-alive server
except ModuleNotFoundError:  # the file was saved as extras.py: accept it instead of crashing
    import extras as extra
    sys.modules["extra"] = extra
import fun_systems  # roast + court entertainment (wired up in main())
import msgcount  # message count / leaderboard / milestones (wired up in main())
import migrate_to_mongo as store  # the MongoDB data layer (the only file that talks to the database)
from extra import (  # pure helpers (no bot state): see extra.py
    fmt_duration,
    parse_duration,
    split_time_reason,
    word_match,
    split_keyword,
    norm_url,
    _retry_seconds,
    make_challenge,
    command_args_text,
    _on_off,
    _numbered,
    sa_label,
    _show_allow,
    _text_or_none,
    _entity_items,
)
from types import SimpleNamespace

extra.setup_logging()
BOT_NAME = "Group moderation bot"
ADMIN_STATUSES = (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER)
FLOOD_LIMIT, FLOOD_WINDOW = 6, 5  # messages per seconds
flood_log = defaultdict(list)
repeat_log = defaultdict(list)
REPEAT_WINDOW = 60  # seconds used to detect identical-message spam


# ---------------------------------------------------------------- database
# Everything is stored in MongoDB (migrate_to_mongo.py). Reads are cached in memory and every
# write goes straight to the database, so callers just use these functions.
get_setting = store.get_setting
set_setting = store.set_setting


# ----------------------------------------------------------------- helpers
# Telegram's stand-in sender for admins (including the group owner) who post
# anonymously. Telegram only ever sends this ID for an anonymous admin of that
# very chat, so it can't be faked by a normal member.
ANON_ADMIN_ID = 1087968824


ROLE_TTL = 30          # seconds a looked-up role is trusted (promote/demote clear it at once)
_role_cache = {}       # (chat_id, user_id) -> (status, time looked up)


async def get_role(chat, user_id):
    """The member's status ('creator', 'administrator', 'member', ...), or None
    when Telegram wouldn't tell us. Failures are logged so the cause is visible.
    Successful lookups are cached briefly: every admin check used to cost a Telegram
    round-trip (often 0.2-1s each, several per command)."""
    if is_bot_owner(user_id):
        return "creator"  # owner power ON: counts as the group owner everywhere (never cached)
    key = (chat.id, user_id)
    hit = _role_cache.get(key)
    if hit and time.time() - hit[1] < ROLE_TTL:
        return hit[0]
    try:
        status = (await chat.get_member(user_id)).status
        if len(_role_cache) > 5000:
            _role_cache.clear()
        _role_cache[key] = (status, time.time())
        return status
    except TelegramError as e:
        logging.warning("get_member failed chat=%s user=%s: %s: %s",
                        chat.id, user_id, type(e).__name__, e)
        return None


async def is_admin(chat, user_id):
    """Owner ('creator') and administrators both count as admins."""
    if user_id == ANON_ADMIN_ID:
        return True
    return await get_role(chat, user_id) in ADMIN_STATUSES


# ------------------------------------------------------------- owner power (global, owner's private chat only)
# /power on|off|<time>|show, used by a Primary Bot Owner in a private chat with the bot. While it is ON the owner
# can use every command and menu in every group without being an admin, and no automatic or manual action
# touches them. It is OFF by default and is stored globally (chat 0) as "owner_power_until":
# 0 = off, -1 = on until /power off, otherwise the unix time when it switches itself off.
POWER_KEY = "owner_power_until"
POWER_MAX_SECS = 365 * 24 * 3600


def power_state():
    """0 = off, -1 = on until switched off, otherwise the number of seconds left."""
    try:
        until = int(get_setting(0, POWER_KEY, 0) or 0)
    except (TypeError, ValueError):
        return 0
    if until == -1:
        return -1
    left = until - int(time.time())
    return left if until > 0 and left > 0 else 0


def owner_power_on() -> bool:
    return power_state() != 0


def is_bot_owner(user_id) -> bool:
    """True only for a Primary Bot Owner (OWNER_IDS) while /power is ON. Everything that gives the owner
    extra rights or immunity asks this, so with power OFF the owner is an ordinary member or admin."""
    return user_id in OWNER_IDS and owner_power_on()


def is_approved(chat_id, user_id) -> bool:
    """Approved users are exempt from locks, blocklists, antiflood and antispam.
    The bot owner counts as approved everywhere, so every guard that checks approval skips them."""
    return is_bot_owner(user_id) or store.is_approved(chat_id, user_id)


# ------------------------------------------------------------- pause / resume (per group)
# /pause [time] switches every automatic function off in ONE group until /resume (or until the time ends).
# Stored as the per-group setting "paused_until": 0 = running, -1 = paused until /resume, otherwise the
# unix time when it resumes by itself. Commands and menus keep working so an admin can always /resume.
PAUSE_KEY = "paused_until"


def pause_state(chat_id):
    """0 = running, -1 = paused until /resume, otherwise the number of seconds left."""
    try:
        until = int(get_setting(chat_id, PAUSE_KEY, 0) or 0)
    except (TypeError, ValueError):
        return 0
    if until == -1:
        return -1
    left = until - int(time.time())
    return left if until > 0 and left > 0 else 0


def is_paused(chat_id) -> bool:
    return chat_id < 0 and pause_state(chat_id) != 0


async def admin_only(update: Update) -> bool:
    """Requires group-admin status in a group; always passes in a private chat
    (there you're the only 'admin' of your own space with the bot)."""
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if chat.type == "private":
        return True
    # An owner/admin posting anonymously arrives as sender_chat == this chat.
    if user.id == ANON_ADMIN_ID or (msg.sender_chat and msg.sender_chat.id == chat.id):
        return True
    role = await get_role(chat, user.id)
    if role in ADMIN_STATUSES:  # 'creator' and 'administrator'
        return True
    if role is None:
        await msg.reply_text("⚠️ I couldn't check your admin status right now. "
                             "Make sure I'm still in this group, then try again.")
    else:
        await msg.reply_text("Admins only.")
    return False


async def group_only(update: Update) -> bool:
    """For commands that act on another chat member - Telegram has no such concept
    in a private chat, so these still require a real group."""
    if update.effective_chat.type == "private":
        await update.effective_message.reply_text(
            "This only works in a group - there's no one else to act on here."
        )
        return False
    return await admin_only(update)


_uname_seen = {}  # (chat_id, lowercase username) -> user id, filled by remember_username


async def remember_username(update, context):
    """group=-5, no command: remembers who owns which @username in each group so that
    /mute @name, /promote @name etc. can resolve it (Telegram bots can't look up most
    users by @username). Stored with the same settings helpers as name-change detection."""
    try:
        chat, msg = update.effective_chat, update.effective_message
        if not chat or not msg or chat.type == "private":
            return
        users = [msg.from_user]
        if msg.reply_to_message:
            users.append(msg.reply_to_message.from_user)
        for ent in msg.entities or []:
            if ent.type == "text_mention":
                users.append(ent.user)
        for u in users:
            if not u or not u.username or u.id == ANON_ADMIN_ID:
                continue
            key = (chat.id, u.username.lower())
            if _uname_seen.get(key) == u.id:
                continue
            _uname_seen[key] = u.id
            try:
                set_setting(chat.id, f"uname:{u.username.lower()}", str(u.id))
            except Exception:
                logging.exception("Couldn't store username %s in %s", u.username, chat.id)
    except Exception:
        logging.exception("remember_username failed")  # never block other handlers


async def resolve_user_arg(update, context):
    """Target given as a tapped mention or an @username. Returns (user_id, mention_html,
    text_after_target), or (None, None, "") when there isn't one / it can't be resolved."""
    msg, chat = update.effective_message, update.effective_chat
    after_cmd = (msg.text or "").partition(" ")[2].strip()
    for ent in msg.entities or []:
        if ent.type == "text_mention" and ent.user:
            shown = msg.parse_entity(ent)
            return ent.user.id, ent.user.mention_html(), after_cmd.partition(shown)[2].strip()
    if not context.args or not re.fullmatch(r"@[A-Za-z][A-Za-z0-9_]{3,31}", context.args[0]):
        return None, None, ""
    arg = context.args[0]
    uname = arg[1:].lower()
    uid = _uname_seen.get((chat.id, uname))
    if not uid:
        raw = str(get_setting(chat.id, f"uname:{uname}", "") or "")
        uid = int(raw) if raw.isdigit() else None
    if not uid:
        try:
            found = await context.bot.get_chat(arg)
            if found.type == "private":
                uid = found.id
        except TelegramError:
            pass
    if not uid:
        return None, None, ""
    return uid, f'<a href="tg://user?id={uid}">{html.escape(arg)}</a>', after_cmd.partition(" ")[2].strip()


ERR_USER_NOT_FOUND = (
    "I couldn't find that user. Reply to one of their messages, use their numeric user ID, "
    "or have them send a message in this group first so I can learn their @username."
)


async def get_target(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Target = replied-to user, or a numeric user ID as first argument."""
    msg = update.effective_message
    if msg.reply_to_message and msg.reply_to_message.from_user:
        u = msg.reply_to_message.from_user
        return u.id, u.mention_html()
    if context.args and context.args[0].isdigit():
        return int(context.args[0]), context.args[0]
    uid, mention, _ = await resolve_user_arg(update, context)
    if uid:
        return uid, mention
    if context.args and context.args[0].startswith("@"):
        await msg.reply_text(ERR_USER_NOT_FOUND)
        return None, None
    await msg.reply_text("Reply to a user (or give a numeric user ID).")
    return None, None


async def can_target(update, user_id) -> bool:
    if is_bot_owner(user_id):
        await update.effective_message.reply_text("I won't act on the bot owner.")
        return False
    if await is_admin(update.effective_chat, user_id):
        await update.effective_message.reply_text("I won't act on an admin.")
        return False
    return True


async def target_and_rest(update, context):
    """Like get_target, but also returns the text after the target (reason, duration...)."""
    msg = update.effective_message
    rest = msg.text.partition(" ")[2].strip()
    if msg.reply_to_message and msg.reply_to_message.from_user:
        u = msg.reply_to_message.from_user
        return u.id, u.mention_html(), rest
    if context.args and context.args[0].isdigit():
        return int(context.args[0]), context.args[0], rest.partition(" ")[2].strip()
    uid, mention, after = await resolve_user_arg(update, context)
    if uid:
        return uid, mention, after
    if context.args and context.args[0].startswith("@"):
        await msg.reply_text(ERR_USER_NOT_FOUND)
        return None, None, ""
    await msg.reply_text("Reply to a user (or give a numeric user ID).")
    return None, None, ""


# Actions ("modes") are stored as strings: nothing, delete, warn, mute, kick, ban, tmute:<seconds>
MODE_TEXT = {
    "nothing": "do nothing",
    "delete": "delete the message",
    "warn": "warn the user",
    "mute": "mute",
    "kick": "kick",
    "ban": "ban",
}
MUTED = ChatPermissions(can_send_messages=False)
DEFAULT_PERMS = ChatPermissions(
    can_send_messages=True,
    can_send_audios=True,
    can_send_documents=True,
    can_send_photos=True,
    can_send_videos=True,
    can_send_video_notes=True,
    can_send_voice_notes=True,
    can_send_polls=True,
    can_send_other_messages=True,
    can_add_web_page_previews=True,
    can_invite_users=True,
)


def parse_mode(args, allowed):
    """Command args -> stored mode string, or None when invalid."""
    if not args:
        return None
    kind = args[0].lower()
    if kind not in allowed:
        return None
    if kind == "tmute":
        secs = parse_duration(args[1]) if len(args) > 1 else None
        return f"tmute:{secs}" if secs else None
    return kind


def describe_mode(mode):
    kind, _, arg = mode.partition(":")
    if kind == "tmute":
        return f"mute for {fmt_duration(int(arg))}"
    return MODE_TEXT.get(kind, kind)


_recent_mutes = {}  # (chat_id, user_id) -> time the bot last muted them (lets announce() add an Unmute button)


async def do_action(chat, user_id, mode):
    """Run ban/kick/mute/tmute. Returns a past-tense word, or None if Telegram refused."""
    if is_bot_owner(user_id):
        return None  # never act on the bot owner, whatever triggered it
    kind, _, arg = mode.partition(":")
    try:
        if kind == "ban":
            await chat.ban_member(user_id)
            return "banned"
        if kind == "kick":
            await chat.ban_member(user_id)
            await chat.unban_member(user_id)
            return "kicked"
        if kind == "mute":
            await chat.restrict_member(user_id, MUTED)
            _recent_mutes[(chat.id, user_id)] = time.time()
            return "muted"
        if kind == "tmute":
            secs = int(arg)
            await chat.restrict_member(user_id, MUTED, until_date=int(time.time()) + secs)
            _recent_mutes[(chat.id, user_id)] = time.time()
            return f"muted for {fmt_duration(secs)}"
    except TelegramError as e:
        logging.warning("Action %s failed in chat %s: %s", mode, chat.id, e)
    return None


def active_warns(chat_id, user_id):
    """Unexpired warnings for a user, oldest first, as (id, reason, timestamp)."""
    expiry = int(get_setting(chat_id, "warn_time", 0))
    return store.warn_active(chat_id, user_id, expiry)


def warn_summary(chat_id, user_id):
    limit = int(get_setting(chat_id, "warn_limit", 3))
    return f"{len(active_warns(chat_id, user_id))}/{limit}"


async def add_warn(chat, user_id, mention, reason, by=None):
    """Record a warning; at the limit, apply the chat's warn mode. Returns the notice text to announce."""
    limit = int(get_setting(chat.id, "warn_limit", 3))
    store.warn_add(chat.id, user_id, reason, int(time.time()))
    count = len(active_warns(chat.id, user_id))
    mode = get_setting(chat.id, "warn_mode", "ban")
    why = reason or "No reason given"
    if count < limit:
        label = f"Warned ({count}/{limit})"
        punish = (f"Warning {count}/{limit}: no mute or ban yet. At {limit}/{limit} warnings the action is "
                  f"{describe_mode(mode)}")
        await extra.record_action(chat.id, user_id, mention, label, why, punish, by, "warn")
        return extra.action_notice(mention, label, why, punish, by)

    store.warn_clear(chat.id, user_id)
    done = await do_action(chat, user_id, mode)
    if done:
        kind, secs = extra.mode_kind(mode)
        label = f"{extra.ACTION_LABEL.get(kind, kind.title())} (warn limit reached)"
        punish = extra.punishment_text(kind, secs)
        why = f"Reached {limit}/{limit} warnings. Last warning: {why}"
        await extra.record_action(chat.id, user_id, mention, label, why, punish, by, "warn")
        return extra.action_notice(mention, label, why, punish, by)
    return (
        f"{mention} reached {limit}/{limit} warnings, but I couldn't "
        f"{describe_mode(mode)}. Check my admin permissions.\nReason: {html.escape(why)}"
    )


async def enforce(chat, user_id, mention, mode, reason, category=None):
    """Apply a feature's configured action. Returns text to announce, or None."""
    kind = mode.partition(":")[0]
    if kind in ("nothing", "delete"):
        return None
    if kind == "warn":
        text = await add_warn(chat, user_id, mention, reason)
    else:
        done = await do_action(chat, user_id, mode)
        text = None
        if done:
            kind, secs = extra.mode_kind(mode)
            label, punish = extra.ACTION_LABEL.get(kind, kind.title()), extra.punishment_text(kind, secs)
            text = extra.action_notice(mention, label, reason, punish)
            await extra.record_action(chat.id, user_id, mention, label, reason, punish, None, category or "mod")
    if text and category:
        await log_action(chat, category, text)
    return text


async def announce(chat, text, uid=None):
    if not text:
        return
    kb = None
    # when the bot itself just muted this user, attach the same Unmute button /mute uses
    if uid is not None and time.time() - _recent_mutes.pop((chat.id, uid), 0) < 15:
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Unmute", callback_data=f"unmute:{uid}")]])
    try:
        sent = await chat.send_message(text, parse_mode="HTML", reply_markup=kb)
    except TelegramError as e:
        logging.warning("Couldn't announce in chat %s: %s", chat.id, e)
        return None
    await extra.track_notice(sent)  # every action notice disappears 1 day later (schedule kept in MongoDB)
    return sent


async def try_delete(msg):
    try:
        await msg.delete()
    except TelegramError as e:
        logging.warning("Couldn't delete message: %s", e)


LOG_CATS = {
    "ban": "Bans, unbans and kicks",
    "mute": "Mutes and unmutes",
    "warn": "Warnings given, removed or reset",
    "admin": "Promotions and demotions",
    "blocklist": "Blocklist hits and list changes",
    "flood": "Antiflood actions",
    "spam": "Antispam actions",
    "lock": "Messages deleted by a lock",
    "note": "Notes saved or removed",
    "filter": "Filters added or removed",
    "purge": "Purges",
    "captcha": "CAPTCHA failures",
    "report": "User reports",
}
SETLOG_TIMEOUT = 600  # seconds to forward the /setlog message

DISABLEABLE_COMMANDS = [
    "info", "id", "rules", "donate", "runs", "markdownhelp",
    "warns", "report", "approval", "get", "limits",
]


def _disabled_set(chat_id):
    raw = get_setting(chat_id, "disabled_cmds", "")
    return {c for c in (raw or "").split(",") if c}


async def disable_cmd(update, context):
    if not await admin_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    if chat.type == "private":
        await msg.reply_text("Disabling only applies inside a group.")
        return
    if not context.args:
        await msg.reply_text("Usage: /disable <commandname>  (or /disable all)")
        return
    name = context.args[0].lower().lstrip("/")
    current = _disabled_set(chat.id)
    if name == "all":
        current |= set(DISABLEABLE_COMMANDS)
        set_setting(chat.id, "disabled_cmds", ",".join(sorted(current)))
        await msg.reply_text("Disabled every disableable command. See /disabled.")
        return
    if name not in DISABLEABLE_COMMANDS:
        await msg.reply_text(f"'{name}' isn't disableable. See /disableable for the list.")
        return
    current.add(name)
    set_setting(chat.id, "disabled_cmds", ",".join(sorted(current)))
    await msg.reply_text(f"Disabled /{name}.")


async def enable_cmd(update, context):
    if not await admin_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    if chat.type == "private":
        await msg.reply_text("Disabling only applies inside a group.")
        return
    if not context.args:
        await msg.reply_text("Usage: /enable <commandname>  (or /enable all)")
        return
    name = context.args[0].lower().lstrip("/")
    current = _disabled_set(chat.id)
    if name == "all":
        set_setting(chat.id, "disabled_cmds", "")
        await msg.reply_text("Re-enabled every command.")
        return
    current.discard(name)
    set_setting(chat.id, "disabled_cmds", ",".join(sorted(current)))
    await msg.reply_text(f"Enabled /{name}.")


async def disableable_cmd(update, context):
    names = "\n".join(f"- /{c}" for c in DISABLEABLE_COMMANDS)
    await update.effective_message.reply_text(f"Disableable commands:\n{names}")


async def disabled_cmd(update, context):
    chat = update.effective_chat
    current = _disabled_set(chat.id) if chat.type != "private" else set()
    names = "\n".join(f"- /{c}" for c in sorted(current)) or "Nothing is disabled here."
    await update.effective_message.reply_text(names)


async def disabledel_toggle(update, context):
    if not await admin_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    arg = context.args[0].lower() if context.args else ""
    if arg in ("yes", "on"):
        set_setting(chat.id, "disable_del", True)
        await msg.reply_text("Disabled commands will now be deleted when used.")
    elif arg in ("no", "off"):
        set_setting(chat.id, "disable_del", False)
        await msg.reply_text("Disabled commands will be ignored, not deleted.")
    else:
        current = get_setting(chat.id, "disable_del", "False") == "True"
        await msg.reply_text(
            f"Deleting disabled commands: {'on' if current else 'off'}.\n"
            "Usage: /disabledel yes|no|on|off"
        )


async def disableadmin_toggle(update, context):
    if not await admin_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    arg = context.args[0].lower() if context.args else ""
    if arg in ("yes", "on"):
        set_setting(chat.id, "disable_admin", True)
        await msg.reply_text("Disabled commands now also block admins.")
    elif arg in ("no", "off"):
        set_setting(chat.id, "disable_admin", False)
        await msg.reply_text("Disabled commands no longer block admins.")
    else:
        current = get_setting(chat.id, "disable_admin", "False") == "True"
        await msg.reply_text(
            f"Disabling applies to admins too: {'on' if current else 'off'}.\n"
            "Usage: /disableadmin yes|no|on|off"
        )


def guard_disableable(name, fn):
    """Wraps a disableable command so /disable actually takes effect for it."""
    async def wrapper(update, context):
        chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
        if chat.type != "private" and name in _disabled_set(chat.id):
            blocks_admin = get_setting(chat.id, "disable_admin", "False") == "True"
            if blocks_admin or not await is_admin(chat, user.id):
                if get_setting(chat.id, "disable_del", "False") == "True":
                    await try_delete(msg)
                return
        return await fn(update, context)
    return wrapper


async def approve_user(update, context):
    if not await group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    uid, name = await get_target(update, context)
    if not uid:
        return
    if await is_admin(chat, uid):
        await msg.reply_html(
            f"{name} is an admin, so locks, blocklists and antiflood already don't apply to them."
        )
        return
    store.approve(chat.id, uid)
    await msg.reply_html(
        f"Approved {name}. Locks, blocklists and antiflood/antispam won't apply to them."
    )


async def unapprove_user(update, context):
    if not await group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    uid, name = await get_target(update, context)
    if not uid:
        return
    store.unapprove(chat.id, uid)
    await msg.reply_html(f"Unapproved {name}. They're subject to locks and filters again.")


async def approved_list(update, context):
    if not await admin_only(update):
        return
    chat = update.effective_chat
    if chat.type == "private":
        await update.effective_message.reply_text("Approvals only apply inside a group.")
        return
    rows = [(u,) for u in store.approved_ids(chat.id)]
    if not rows:
        await update.effective_message.reply_text("No one is approved in this chat.")
        return
    lines = []
    for (uid,) in rows:
        try:
            member = await chat.get_member(uid)
            lines.append(f"- {member.user.mention_html()}")
        except TelegramError:
            lines.append(f"- <code>{uid}</code>")
    await update.effective_message.reply_html("Approved users:\n" + "\n".join(lines))


async def _can_unapprove_all(chat, user_id) -> bool:
    """Only the chat creator (or a bot owner with power ON) may wipe every approval."""
    if is_bot_owner(user_id):
        return True
    try:
        member = await chat.get_member(user_id)
    except TelegramError:
        return False
    return member.status == ChatMemberStatus.OWNER


async def unapprove_all(update, context):
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if chat.type == "private":
        await msg.reply_text("Approvals only apply inside a group.")
        return
    if not await _can_unapprove_all(chat, user.id):
        await msg.reply_text("Only the chat creator can unapprove everyone.")
        return
    count = store.approved_count(chat.id)
    if not count:
        await msg.reply_text("No one is approved in this chat.")
        return
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("Unapprove all", callback_data=f"unall:yes:{user.id}"),
        InlineKeyboardButton("Cancel", callback_data=f"unall:no:{user.id}"),
    ]])
    await msg.reply_text(
        f"Unapprove all {count} approved user(s) in this chat? This cannot be undone.",
        reply_markup=kb,
    )


async def unapprove_all_callback(update, context):
    q = update.callback_query
    _, choice, starter = q.data.split(":")
    chat, user = q.message.chat, q.from_user
    if user.id != int(starter) or not await _can_unapprove_all(chat, user.id):
        await q.answer("Only the chat creator who ran the command can use this.", show_alert=True)
        return
    if choice == "no":
        await q.edit_message_text("Cancelled. No approvals were removed.")
        await q.answer()
        return
    removed = store.unapprove_all(chat.id)
    await q.edit_message_text(f"Unapproved all {removed} previously-approved user(s).")
    await q.answer()


async def approval_status(update, context):
    chat, msg = update.effective_chat, update.effective_message
    if chat.type == "private":
        await msg.reply_text("Approvals only apply inside a group.")
        return
    if msg.reply_to_message or (context.args and (context.args[0].isdigit() or context.args[0].startswith("@"))):
        uid, name = await get_target(update, context)
        if not uid:
            return
    else:
        uid, name = update.effective_user.id, update.effective_user.mention_html()
    status = "is approved" if is_approved(chat.id, uid) else "is not approved"
    await msg.reply_html(f"{name} {status} in this chat.")


async def reports_toggle(update, context):
    if not await admin_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    if chat.type == "private":
        await msg.reply_text("Reports only apply inside a group.")
        return
    arg = context.args[0].lower() if context.args else ""
    if arg in ("yes", "on"):
        set_setting(chat.id, "reports_on", True)
        await msg.reply_text("User reports: on.")
    elif arg in ("no", "off"):
        set_setting(chat.id, "reports_on", False)
        await msg.reply_text("User reports: off.")
    else:
        current = get_setting(chat.id, "reports_on", "True") == "True"
        await msg.reply_text(
            f"User reports: {'on' if current else 'off'}.\nUsage: /reports yes|no|on|off"
        )


async def file_report(update, context):
    """Shared by /report and a reply containing '@admin'."""
    chat, msg, reporter = update.effective_chat, update.effective_message, update.effective_user
    if chat.type == "private" or get_setting(chat.id, "reports_on", "True") != "True":
        return
    target_msg = msg.reply_to_message
    if not target_msg or not target_msg.from_user:
        if msg.text and msg.text.startswith("/report"):
            await msg.reply_text("Reply to the message you want to report.")
        return
    reported = target_msg.from_user
    # Admins don't need to report, and can't be reported - they're assumed exempt.
    if await is_admin(chat, reporter.id) or await is_admin(chat, reported.id):
        return
    try:
        admins = await chat.get_administrators()
    except TelegramError:
        return
    mentions = " ".join(a.user.mention_html() for a in admins if not a.user.is_bot)
    if not mentions:
        return
    await target_msg.reply_html(
        f"{reporter.mention_html()} reported this message to: {mentions}"
    )
    await log_action(
        chat, "report", f"🚨 {reporter.mention_html()} reported {reported.mention_html()}."
    )


async def report_cmd(update, context):
    await file_report(update, context)


async def log_action(chat, category, text):
    """Send text to the chat's log channel, if one is set and this category is enabled."""
    log_id = get_setting(chat.id, "log_channel")
    if not log_id:
        return
    enabled = set(filter(None, get_setting(chat.id, "log_categories", "").split(",")))
    if category not in enabled:
        return
    try:
        bot = chat.get_bot()
        await bot.send_message(int(log_id), f"<b>{html.escape(chat.title or str(chat.id))}</b>\n{text}", parse_mode="HTML")
    except TelegramError as e:
        logging.warning("Couldn't send log message for chat %s: %s", chat.id, e)


async def _mode_cmd(update, context, cmd, key, default, allowed, label):
    """Shared handler for /warnmode, /floodmode, /blocklistmode, /spammode."""
    if not await admin_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    options = " | ".join("tmute <time>" if a == "tmute" else a for a in allowed)
    if not context.args:
        current = get_setting(chat.id, key, default)
        await msg.reply_text(f"{label}: {describe_mode(current)}\nChange with: /{cmd} {options}")
        return
    mode = parse_mode(context.args, allowed)
    if not mode:
        await msg.reply_text(f"Usage: /{cmd} {options}\nExample time: 30m, 2h, 1d, 1w")
        return
    set_setting(chat.id, key, mode)
    await msg.reply_text(f"{label}: {describe_mode(mode)}")


async def _number_setting(update, context, cmd, key, default, low, high, unit):
    """Shared handler for numeric settings where 0 turns the feature off."""
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    arg = context.args[0] if context.args else ""
    if arg.isdigit() and (int(arg) == 0 or low <= int(arg) <= high):
        set_setting(chat_id, key, int(arg))
        await msg.reply_text("Turned off." if int(arg) == 0 else f"Set to {arg} {unit}.")
    else:
        current = get_setting(chat_id, key, default)
        await msg.reply_text(
            f"Current: {current} {unit} (0 = off).\nUsage: /{cmd} <{low}-{high}, or 0 to turn off>"
        )


# ---------------------------------------------------------------- commands


HELP_SECTIONS = {
    "mod": (
        "Admin",
        "<b>Moderation</b> (reply to a user, or give a user ID)\n\n" + _numbered([
            "/ban: Ban a user from the group.",
            "/unban: Lift a user's ban.",
            "/kick: Remove a user; they can rejoin.",
            "/promote [title]: Give a user admin rights, with an optional title.",
            "/demote: Remove a user's admin rights.",
            "/mute [time] [reason]: Silence a user, forever or for a set time.",
            "/tmute time [reason]: Silence a user for a set time (time required).",
            "/dmute [time] [reason]: Like /mute, and also deletes their message.",
            "/unmute: Lift a user's mute.",
        ]),
    ),
    "warn": (
        "Warnings",
        "<b>Warnings</b>\n\n" + _numbered([
            "/warn [reason]: Give a user a warning.",
            "/dwarn [reason]: Like /warn, and also deletes their message.",
            "/warns: Show a user's warnings (or your own).",
            "/rmwarn: Remove a user's most recent warning.",
            "/resetwarns: Clear all of a user's warnings.",
            "/warnlimit N: Set how many warnings trigger the warn action.",
            "/warnmode ban|kick|mute|tmute: Set the action at the limit.",
            "/warntime 7d|off: Make warnings expire after a time, or never.",
        ]),
    ),
    "flood": (
        "Antiflood",
        "<b>Flood &amp; spam</b>\n\n" + _numbered([
            "/flood: Show the current antiflood settings.",
            "/setflood N [secs]|off: Set the message-flood threshold.",
            "/floodmode: Set the action taken on flooders.",
            "/antispam on|off: Toggle repeated-message and mass-mention detection.",
            "/spammode: Set the action taken on spammers.",
            "/repeatlimit N: How many identical messages count as spam.",
            "/mentionlimit N: How many @mentions in one message count as spam.",
        ]),
    ),
    "captcha": (
        "CAPTCHA",
        "<b>Join verification</b>\n\n" + _numbered([
            "/captcha on|off: Require new members to verify they're human.",
            "/captchamode button|math: Choose a tap-button or a math challenge.",
            "/captchatime 2m: How long a new member has to solve it.",
            "/captchaaction kick|mute|ban: What happens if they fail or time out.",
        ]),
    ),
    "greet": (
        "Greetings",
        "<b>Greetings</b>\n\n" + _numbered([
            "/setwelcome text: Set the message shown to new members.",
            "/welcome on|off: Toggle welcome messages.",
            "/cleanwelcome on|off: Delete the previous welcome when a new one is sent.",
            "/resetwelcome: Restore the default welcome message.",
            "/setgoodbye text: Set the message shown when someone leaves.",
            "/goodbye on|off: Toggle goodbye messages.",
            "/resetgoodbye: Restore the default goodbye message.",
        ]),
    ),
    "rules": (
        "Rules",
        "<b>Rules</b>\n\n" + _numbered([
            "/rules: Show the group's rules (/rules raw shows the unformatted text).",
            "/setrules text: Set the group's rules (markdown, buttons and placeholders work).",
            "/resetrules: Remove the group's rules.",
            "/privaterules yes|no: Show rules through a button that opens them in private.",
            "/setrulesbutton text: Rename the rules button (also used by {rules} in welcome text).",
            "/resetrulesbutton: Put the button name back to Rules.",
        ]),
    ),
    "notes": (
        "Filters",
        "<b>Notes &amp; filters</b>\n\n" + _numbered([
            "/save name text (or reply): Save a note, fetched later with #name.",
            "/get name: Fetch a saved note.",
            "/notes: List all saved notes.",
            "/clear name: Delete a saved note.",
            "/filter keyword reply: Auto-reply when a keyword is said (quote phrases).",
            "/stop keyword: Remove a filter.",
            "/filters: List all filters.",
        ]),
    ),
    "locks": (
        "Locks",
        "<b>Locks</b>\n\n" + _numbered([
            "/lock item [item ...]: Block those items for non-admins.",
            "/unlock item [item ...]: Allow them again.",
            "/locks: List the locks that are active.",
            "/locktypes: List every item that can be locked.",
            "/lockwarns yes|no: Warn people who send a locked item.",
            "/allowlist [items]: Exempt URLs, IDs, @names, commands, cashtags or sticker packs from locks; no items shows the list.",
            "/rmallowlist items: Remove items from the allowlist.",
            "/rmallowlistall: Clear the whole allowlist.",
        ]),
    ),
    "purge": (
        "Purges",
        "<b>Purges</b> (need the 'Delete messages' admin right)\n\n" + _numbered([
            "/purge (reply): Delete the replied-to message, everything after it, and your command.",
            "/purge &lt;X&gt; (reply): Delete the replied-to message and the X messages after it.",
            "/spurge (reply): Silent /purge, with no confirmation message.",
            "/del (reply): Delete the replied-to message and your command.",
            "/purgefrom (reply): Save the start of a range. Valid for 10 minutes.",
            "/purgeto (reply): Delete from the saved start point to the replied-to message.",
        ]),
    ),
    "log": (
        "Log Channels",
        "<b>Log channels</b>\n\n" + _numbered([
            "/setlog: Send in a channel (bot must be admin there) to start linking it.",
            "/logchannel: Show the current log channel and enabled categories.",
            "/unsetlog: Remove the log channel.",
            "/log category: Start logging that category (see /logcategories).",
            "/nolog category: Stop logging that category.",
            "/logcategories: List every loggable category and what it covers.",
            "/modlog: Show the last bot and admin actions in this group (action, reason, punishment). Kept for 15 days.",
        ]),
    ),
    "reports": (
        "Reports",
        "<b>Reports</b>\n\n" + _numbered([
            "/report (reply): Report a message to all admins.",
            "Reply with @admin: Same as /report.",
            "/reports yes|no|on|off: Turn user reports on or off (admin only).",
        ]),
    ),
    "disabling": (
        "Disabling",
        "<b>Disabling</b>\n\n" + _numbered([
            "/disable name: Stop non-admins using a command (or /disable all).",
            "/enable name: Allow it again (or /enable all).",
            "/disableable: List every command that can be disabled.",
            "/disabled: List commands disabled in this chat.",
            "/disabledel yes|no: Delete disabled commands when someone uses them.",
            "/disableadmin yes|no: Also block admins from disabled commands.",
        ]),
    ),
    "approval": (
        "Approval",
        "<b>Approval</b>\n\n" + _numbered([
            "/approval: Check a user's approval status (or your own).",
            "/approve: Exempt a user from locks, blocklists and antiflood/antispam.",
            "/unapprove: Remove that exemption.",
            "/approved: List everyone approved in this chat.",
            "/unapproveall: Remove every approval in this chat (chat creator only, asks to confirm).",
        ]),
    ),
    "groupedit": (
        "👥 Group Edit",
        "<b>Group Edit</b>\n\n" + _numbered([
            "/groupedit: Change the group's name, username, photo or bio "
            "(needs the 'Change Group Info' admin permission).",
            "/cancel: Cancel the current edit process.",
        ]),
    ),
    "botedit": (
        "🤖 Bot Edit",
        "<b>Bot Edit</b>\n\n" + _numbered([
            "/bot: Change the bot's name, username, photo or bio "
            "(Bot Owner only).",
            "/addadmin: Add a Super Admin - reply to a user, or give an ID or @username "
            "(Primary Bot Owner only).",
            "/removeadmin: Remove a Super Admin (Primary Bot Owner only).",
            "/adminlist: List all Super Admins (Primary Bot Owner only).",
        ]),
    ),
    "other": (
        "Misc",
        "<b>Misc</b>\n\n" + _numbered([
            "/pause [time]: Switch every automatic function off in this group until /resume, or for a set time (admins).",
            "/resume: Switch everything back on (admins).",
            "/pin (reply): Pin the replied-to message.",
            "/suggestions on|off: Show or hide the / command-suggestion menu here.",
        ]),
    ),
    "info": (
        "Info",
        "<b>Info</b>\n\n" + _numbered([
            "/id: Get the ID of a user, group or channel.",
            "/info: Get a user's info.",
            "/limits: Show this chat's moderation limits and settings.",
        ]),
    ),
    "ai": ("AI", "<b>AI</b>\n\n" + _numbered(extra.AI_HELP_LINES)),
    "extras": (
        "Extras",
        "<b>Extras</b>\n\n" + _numbered([
            "/runs: A random 'run away' reply, just for fun.",
            "/donate: Support the bot's creator.",
            "/markdownhelp: Formatting help (PM only).",
        ]),
    ),
    "roast": (
        "🔥 Roast",
        "<b>Roast</b> (playful fun: no hate, threats or low blows)\n\n" + _numbered([
            "/roast @user: Roast someone (or reply to their message).",
            "/roastme: Roast yourself.",
            "/cook @user: Get someone cooked in the kitchen.",
            "/burn @user: A fiery burn with a heat level.",
            "/finisher @user: Deliver the finishing blow.",
            "/comeback: Reply to a message for an instant comeback.",
            "/roastbattle @user: Challenge someone to a timed 2-player roast battle.",
            "/roastvote 1|2: Vote for a fighter while a battle is open for voting.",
            "/roastscore [@user]: Points, wins and streaks in this chat.",
            "/roaststats [@user]: Detailed roast stats and rank.",
            "/roastking: This chat's top 5 roasters.",
        ]) + "\n\n<b>Rules</b>\n"
        "• You can't target yourself (except /roastme), and bots can't be roasted.\n"
        "• Battle: the opponent has 60s to accept, then each fighter sends one roast "
        "(3+ words) within 60s. A fair scoring system judges it (70%) and the crowd votes (30%).\n"
        "• Win +10 points, loss +2, draw +5. All scores are tracked per chat.",
    ),
    "court": (
        "⚖️ Court",
        "<b>Court</b> (a comedy minigame: it never bans, mutes or kicks anyone)\n\n" + _numbered([
            "/court @user: Put someone on trial with absurd charges.",
            "/trial @user: Same as /court.",
            "/guilty [@user]: Vote guilty as a juror.",
            "/innocent [@user]: Vote innocent as a juror.",
            "/verdict [@user]: Close the trial early (admin or prosecutor), or see the last verdict.",
            "/crime @user: Generate a crime report.",
            "/evidence @user: Present absurd evidence.",
            "/alibi @user: Hear a questionable alibi.",
            "/sentence @user: A harmless, funny sentence.",
            "/bail @user: Post imaginary cookies as bail.",
            "/pardon @user: Pardon a case (admins only).",
            "/appeal: Appeal your own guilty verdict (once).",
            "/execute @user: A purely fictional comedy execution.",
            "/wanted @user: A funny wanted poster with a cookie reward.",
        ]) + "\n\n<b>Rules</b>\n"
        "• The defendant picks a plea with the buttons: 😇 innocent, 😭 guilty, 🤫 no comment.\n"
        "• Everyone else is the jury. The trial closes by itself after 5 minutes.\n"
        "• Verdicts: INNOCENT, GUILTY, NOT PROVEN or CHAOS VERDICT. Cases are tracked per chat.",
    ),
    # the 🎂 Birthday button opens the interactive Birthday System menu (see help_callback / fun_systems.py);
    # this text is only a fallback and has no numbered "/command" lines, so the "/" suggestion list is unchanged
    "birthday": (
        "🎂 Birthday",
        "<b>Birthday</b>\n\nSend /wish to open the Birthday System menu.",
    ),
}
HELP_ORDER = ["mod", "warn", "flood", "captcha", "greet", "rules", "notes", "locks", "purge", "log", "reports", "approval", "disabling", "groupedit", "botedit", "other", "info", "extras", "roast", "court", "birthday"]


def _build_bot_commands():
    """Auto-generate Telegram's '/' suggestion list from the numbered /help text,
    so the two never drift apart. Lines without a leading /command are skipped."""
    seen, out = set(), []
    line_re = re.compile(r"^\d+\.\s+/(\w+)[^:]*:\s*(.+)$")
    for _, body in HELP_SECTIONS.values():
        for line in body.split("\n"):
            m = line_re.match(line)
            if not m:
                continue
            cmd, desc = m.group(1), m.group(2).rstrip(".") + "."
            if cmd in seen:
                continue
            seen.add(cmd)
            out.append(BotCommand(cmd, desc[:256]))
    return out


# Telegram allows at most 100 commands per list. This bot has 137 unique commands, so the
# published "/" menu holds the 97 most useful ones; the rest are rarely-used aliases and
# fine-tuning settings (e.g. /setwarnlimit, /captchatime, /spurge). Those still work when
# typed and are listed in /help. Only commands that exist in this bot belong here.
ESSENTIAL_COMMANDS = [
    # general
    ("start", "Start the bot"),
    ("help", "Open the help menu"),
    ("id", "Get a user, group or channel ID"),
    ("info", "Get a user's info"),
    ("runs", "Get a random funny reply"),
    ("donate", "Support the bot"),
    ("limits", "Show this chat's limits"),
    # AI and fun utilities
    ("ai", "Open the AI commands menu"),
    ("ask", "Ask the AI a question"),
    ("search", "AI web search summary"),
    ("translate", "Translate to Hindi and English"),
    ("imagine", "Generate an AI image"),
    ("joke", "Get a random joke"),
    ("quote", "Get a motivational quote"),
    ("fact", "Get an interesting fact"),
    ("roll", "Roll a dice"),
    ("flip", "Flip a coin"),
    ("say", "Make the bot say something"),
    # roast game
    ("roast", "Roast someone"),
    ("roastme", "Roast yourself"),
    ("cook", "Cook someone with a roast"),
    ("burn", "Burn someone"),
    ("finisher", "Finish someone off"),
    ("comeback", "Get a comeback line"),
    ("roastbattle", "Challenge someone to a roast battle"),
    ("roastvote", "Vote in a roast battle"),
    ("roastscore", "Show roast scores"),
    ("roaststats", "Detailed roast stats and rank"),
    ("roastking", "This chat's top roasters"),
    # court game
    ("court", "Put someone on trial"),
    ("guilty", "Vote guilty as a juror"),
    ("innocent", "Vote innocent as a juror"),
    ("verdict", "Close the trial or see the last verdict"),
    ("crime", "Generate a crime report"),
    ("evidence", "Present absurd evidence"),
    ("alibi", "Hear a questionable alibi"),
    ("sentence", "Give a funny sentence"),
    ("bail", "Post imaginary bail"),
    ("pardon", "Pardon a case (admins)"),
    ("appeal", "Appeal your guilty verdict"),
    ("execute", "A purely fictional comedy execution"),
    ("wanted", "Make a funny wanted poster"),
    # moderation
    ("ban", "Ban a user"),
    ("unban", "Unban a user"),
    ("kick", "Kick a user"),
    ("mute", "Mute a user"),
    ("tmute", "Mute a user for a set time"),
    ("dmute", "Mute a user and delete their message"),
    ("unmute", "Unmute a user"),
    ("promote", "Promote a user to admin"),
    ("demote", "Demote an admin"),
    ("report", "Report a message to the admins"),
    ("reports", "Turn user reports on or off"),
    # warnings
    ("warn", "Warn a user"),
    ("warns", "Check a user's warnings"),
    ("rmwarn", "Remove a user's last warning"),
    ("resetwarns", "Reset a user's warnings"),
    ("warnlimit", "Set the warning limit"),
    # flood and spam
    ("flood", "Show the flood settings"),
    ("antispam", "Turn the anti-spam filter on or off"),
    # rules and welcome
    ("rules", "Show this group's rules"),
    ("setrules", "Set the group rules"),
    ("welcome", "Show or change the welcome message"),
    ("setwelcome", "Set the welcome message"),
    ("goodbye", "Show or change the goodbye message"),
    ("setgoodbye", "Set the goodbye message"),
    # captcha, logging
    ("captcha", "Turn the join captcha on or off"),
    ("log", "Enable a log category"),
    ("setlog", "Set the log channel"),
    # notes, filters, blocklist
    ("save", "Save a note"),
    ("get", "Get a saved note"),
    ("notes", "List saved notes"),
    ("clear", "Delete a saved note"),
    ("filter", "Add a chat filter"),
    ("filters", "List chat filters"),
    ("stop", "Remove a chat filter"),
    ("blocklist", "Show the blocklist"),
    ("addblocklist", "Add a word to the blocklist"),
    # locks, cleanup
    ("lock", "Lock a message type"),
    ("unlock", "Unlock a message type"),
    ("locks", "Show current locks"),
    ("pin", "Pin the replied message"),
    ("purge", "Delete messages in bulk"),
    ("purgeto", "Delete from the saved start to the replied message"),
    ("purgefrom", "Save the replied message as the purge start"),
    ("del", "Delete the replied message"),
    # approvals, admins, settings
    ("approve", "Approve a user"),
    ("unapprove", "Unapprove a user"),
    ("approved", "List approved users"),
    ("unapproveall", "Unapprove all users"),
    ("addadmin", "Add a bot admin"),
    ("removeadmin", "Remove a bot admin"),
    ("adminlist", "List the bot admins"),
    ("disable", "Disable a command in this chat"),
    ("enable", "Enable a command in this chat"),
    ("disabled", "List disabled commands"),
    ("groupedit", "Open group settings"),
    ("bot", "Open bot profile settings"),
    ("suggestions", "Show or hide the / menu here"),
    ("trial", "Start or open the Court Trial System"),
]
assert len({c for c, _ in ESSENTIAL_COMMANDS}) == len(ESSENTIAL_COMMANDS), "duplicate command"
assert len(ESSENTIAL_COMMANDS) <= 100, "Telegram allows at most 100 commands per list"
BOT_COMMANDS = [BotCommand(c, d) for c, d in ESSENTIAL_COMMANDS]
HELP_INTRO = (
    "Add me to a group as admin and I'll help you moderate it.\n"
    "Tap a category below to see its commands."
)


# IMPORTANT: HELP MENU BUTTON LAYOUT RULES
# - Normal Help Menu buttons must always be arranged 3 buttons per row.
# - Never intentionally create a normal row containing only 2 buttons.
# - If buttons are added or removed in the future, automatically recalculate
#   the layout so normal buttons continue to appear 3 per row.
# - The Suggestion Bar button is the ONLY exception to the 3-button rule.
# - Suggestion Bar must ALWAYS be the final button in the Help Menu.
# - Suggestion Bar must ALWAYS appear alone on its own final row.
# - Never place any button after the Suggestion Bar.
# - Never combine the Suggestion Bar with another button.
# - Preserve these rules whenever the Help Menu is modified in the future.
def help_main_keyboard(chat=None, user_id=None):
    """Category buttons in a strict 3-column grid, then the command-suggestions
    toggle as a single full-width button on the very last row."""
    buttons = [
        InlineKeyboardButton(HELP_SECTIONS[key][0], callback_data=f"help:{key}")
        for key in HELP_ORDER
    ]
    buttons.append(msgcount.menu_button())  # "📊 Message Count" (handled by msgcount.mc_callback)
    buttons.append(extra.ai_menu_button())  # "🤖 AI Commands" (handled by extra.ai_menu_callback)
    buttons.append(extra.blocking_menu_button())  # "🔒 Blocking" (handled by extra.blocking_callback)
    rows = [buttons[i : i + 3] for i in range(0, len(buttons), 3)]
    if len(rows) > 1 and len(rows[-1]) == 1:  # never leave a lone button: share the last two rows (2 + 2)
        rows[-1].insert(0, rows[-2].pop())
    
    # IMPORTANT:
    # The Suggestion Bar button must ALWAYS remain the final button
    # in the Help Menu button list.
    # It must ALWAYS remain alone on its own row.
    # Do not move it, combine it with another button, or place any
    # button after it.
    
    if user_id in OWNER_IDS:  # 👑 Owner: its own row, just above the Suggestion Bar, shown to the Bot Owner only
        rows.append([InlineKeyboardButton("👑 Owner", callback_data="own:m")])
    if chat is not None:  # always the last row, in groups and in private chat
        rows.append([suggestions_button(chat.id, "help")])
    return InlineKeyboardMarkup(rows)


def help_section_keyboard(key=None, chat=None):
    rows = []
    if key == "mod" and chat is not None and chat.type != "private":
        # Admin section: pause / resume every automatic function of this group (same state as /pause, /resume)
        rows.append([InlineKeyboardButton("⏸ Pause", callback_data="pz:p"),
                     InlineKeyboardButton("▶️ Resume", callback_data="pz:r")])
    rows.append([InlineKeyboardButton("« Back", callback_data="help:main")])
    return InlineKeyboardMarkup(rows)


def admin_section_text(chat=None):
    label, body = HELP_SECTIONS["mod"]
    text = f"<b>{label}</b>\n\n{body}"
    if chat is not None and chat.type != "private":
        text += "\n\n" + html.escape(pause_text(chat.id))
    return text


async def help_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    sent = await update.effective_message.reply_html(
        f"<b>{html.escape(extra.bot_name())}</b>\n\n{HELP_INTRO}",
        reply_markup=help_main_keyboard(update.effective_chat, update.effective_user.id if update.effective_user else None),
        disable_web_page_preview=True,
    )
    extra.remember_menu_owner(sent, update.effective_user.id if update.effective_user else None)


async def action_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the Unban / Unmute / Remove warning buttons on moderation replies."""
    q = update.callback_query
    chat = update.effective_chat
    if not (await is_admin(chat, q.from_user.id)
            or is_bot_owner(q.from_user.id) or store.is_super_admin(q.from_user.id)):
        await q.answer("Admins only.", show_alert=True)
        return
    action, _, uid = q.data.partition(":")
    uid = int(uid)
    if action == "unban":
        await chat.unban_member(uid, only_if_banned=True)
        await q.answer("Unbanned.")
        await q.edit_message_reply_markup(None)
        await q.edit_message_text(q.message.text_html + "\n<i>Unbanned.</i>", parse_mode="HTML")
    elif action == "unmute":
        perms = (await context.bot.get_chat(chat.id)).permissions or DEFAULT_PERMS
        await chat.restrict_member(uid, perms)
        await q.answer("Unmuted.")
        await q.edit_message_text(q.message.text_html + "\n<i>Unmuted.</i>", parse_mode="HTML")
    elif action == "rmwarn":
        rows = active_warns(chat.id, uid)
        if rows:
            store.warn_delete(rows[-1][0])
            await q.answer("Warning removed.")
            await q.edit_message_text(q.message.text_html + "\n<i>Warning removed.</i>", parse_mode="HTML")
        else:
            await q.answer("No warnings left.")
            await q.edit_message_reply_markup(None)


async def help_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if await extra.menu_not_owner(q):
        return
    key = q.data.partition(":")[2]
    if key in EDIT_HELP_KEYS:
        await open_edit_menu(update, context, EDIT_HELP_KEYS[key])
        return
    if key == "birthday":  # 🎂 Birthday: the same interactive menu that /wish opens
        await fun_systems.birthday_menu_from_help(update, context)
        return
    await q.answer()
    if key == "main" or key not in HELP_SECTIONS:
        text = f"<b>{html.escape(extra.bot_name())}</b>\n\n{HELP_INTRO}"
        markup = help_main_keyboard(update.effective_chat, update.effective_user.id if update.effective_user else None)
    else:
        label, body = HELP_SECTIONS[key]
        text = admin_section_text(update.effective_chat) if key == "mod" else f"<b>{label}</b>\n\n{body}"
        markup = help_section_keyboard(key, update.effective_chat)
    try:
        await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup)
    except TelegramError:
        pass  # message unchanged (double tap) or too old to edit; safe to ignore


# ------------------------------------------------- 👑 Owner: default settings for NEW groups
# kind "split": one key for the action + one key for the mute seconds (Ads, Protection)
# kind "mode":  one key holding "ban" / "kick" / "tmute:<seconds>" ... (Flood, Spam, Blocklist, Warnings, Captcha)
OWNER_DEFAULTS = {
    "ads":   {"label": "📢 Ads & Promotion", "kind": "split", "keys": ("block_punish", "block_punish_secs"),
              "options": ("mute", "kick", "ban", "delete")},
    "prot":  {"label": "🔞 Protection", "kind": "split", "keys": ("nsfw_action", "nsfw_secs"),
              "options": ("delete", "mute", "kick", "ban")},
    "flood": {"label": "🌊 Flood", "kind": "mode", "keys": ("flood_mode",),
              "options": ("warn", "mute", "tmute", "kick", "ban")},
    "spam":  {"label": "📨 Spam", "kind": "mode", "keys": ("spam_mode",),
              "options": ("delete", "warn", "mute", "tmute", "kick", "ban")},
    "block": {"label": "🚫 Blocklist", "kind": "mode", "keys": ("blocklist_mode",),
              "options": ("nothing", "delete", "warn", "mute", "tmute", "kick", "ban")},
    "warn":  {"label": "⚠️ Warnings (at the limit)", "kind": "mode", "keys": ("warn_mode",),
              "options": ("ban", "kick", "mute", "tmute")},
    "cap":   {"label": "🤖 Captcha (if failed)", "kind": "mode", "keys": ("captcha_action",),
              "options": ("kick", "mute", "ban")},
}
OWNER_CAT_ORDER = ("ads", "prot", "flood", "spam", "block", "warn", "cap")
OWNER_TIMES = (300, 1800, 3600, 86400, 604800)  # 5 minutes, 30 minutes, 1 hour, 1 day, 7 days
OWNER_OPT_LABEL = {"mute": "🔇 Mute (permanent)", "tmute": "⏱ Timed mute", "kick": "👢 Kick", "ban": "🚫 Ban",
                   "delete": "🗑 Delete only", "warn": "⚠️ Warn", "nothing": "Do nothing"}
OWNER_ACTION_WORDS = {"mute": "mute (permanent)", "kick": "kick (can rejoin)", "ban": "ban (permanent)",
                      "delete": "delete the message only", "warn": "warn the user", "nothing": "do nothing"}


def _owner_values(cat, defaults):
    """(action, mute seconds or None) for one category, read from a defaults dict."""
    spec = OWNER_DEFAULTS[cat]
    if spec["kind"] == "split":
        action_key, secs_key = spec["keys"]
        try:
            secs = int(defaults.get(secs_key))
        except (TypeError, ValueError):
            secs = NEW_GROUP_DEFAULTS[secs_key]
        return str(defaults.get(action_key)), secs
    kind, _, arg = str(defaults.get(spec["keys"][0])).partition(":")
    return kind, (int(arg) if arg.isdigit() else None)


def _owner_timed(cat, action):
    """True when this action carries a mute length."""
    return action == ("mute" if OWNER_DEFAULTS[cat]["kind"] == "split" else "tmute")


def _owner_describe(cat, defaults):
    action, secs = _owner_values(cat, defaults)
    if _owner_timed(cat, action):
        return f"mute for {fmt_duration(secs or 300)} (temporary)"
    return OWNER_ACTION_WORDS.get(action, action)


def _owner_option_label(cat, option):
    if OWNER_DEFAULTS[cat]["kind"] == "split" and option == "mute":
        return "⏱ Timed mute"
    return OWNER_OPT_LABEL.get(option, option)


def owner_main_text():
    return ("<b>👑 Owner: default settings</b>\n\n"
            "These are the settings every <b>new</b> group starts with when the bot is added. Groups that already "
            "exist are not changed, and each group's admins can still change their own group.\n\n"
            "Tap a category to see or change its default.")


def owner_main_keyboard():
    buttons = [InlineKeyboardButton(OWNER_DEFAULTS[c]["label"], callback_data=f"own:c:{c}") for c in OWNER_CAT_ORDER]
    rows = [buttons[i:i + 2] for i in range(0, len(buttons), 2)]
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="help:main")])
    return InlineKeyboardMarkup(rows)


def owner_cat_text(cat):
    now = _owner_describe(cat, new_group_defaults())
    orig = _owner_describe(cat, NEW_GROUP_DEFAULTS)
    return (f"<b>{html.escape(OWNER_DEFAULTS[cat]['label'])}: default for new groups</b>\n\n"
            f"Now: <b>{html.escape(now)}</b>\nOriginal: {html.escape(orig)}\n\n"
            "Pick the action. If it is a timed mute, pick how long. The change applies to groups added from now on.")


def owner_cat_keyboard(cat):
    spec = OWNER_DEFAULTS[cat]
    action, secs = _owner_values(cat, new_group_defaults())
    opts = [InlineKeyboardButton(("✅ " if o == action else "") + _owner_option_label(cat, o),
                                 callback_data=f"own:a:{cat}:{i}") for i, o in enumerate(spec["options"])]
    rows = [opts[i:i + 2] for i in range(0, len(opts), 2)]
    if _owner_timed(cat, action):
        times = [InlineKeyboardButton(("✅ " if t == secs else "") + fmt_duration(t), callback_data=f"own:t:{cat}:{t}")
                 for t in OWNER_TIMES]
        rows += [times[i:i + 3] for i in range(0, len(times), 3)]
    rows.append([InlineKeyboardButton("♻️ Reset to original", callback_data=f"own:r:{cat}")])
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="own:m")])
    return InlineKeyboardMarkup(rows)


def _owner_save(cat, action=None, secs=None):
    """Save the owner's choice for one category (global, stored in MongoDB)."""
    spec = OWNER_DEFAULTS[cat]
    cur_action, cur_secs = _owner_values(cat, new_group_defaults())
    action = action or cur_action
    if spec["kind"] == "split":
        action_key, secs_key = spec["keys"]
        store.set_owner_default(action_key, action)
        store.set_owner_default(secs_key, int(secs or cur_secs or NEW_GROUP_DEFAULTS[secs_key]))
    else:
        value = f"tmute:{int(secs or cur_secs or 300)}" if action == "tmute" else action
        store.set_owner_default(spec["keys"][0], value)


async def owner_callback(update, context):
    """👑 Owner panel buttons. Strictly the Bot Owner (OWNER_IDS): the button is hidden from others, and every
    tap re-checks the person."""
    q = update.callback_query
    if q.from_user.id not in OWNER_IDS:
        await q.answer("This is for the bot owner only.", show_alert=True)
        return
    if await extra.menu_not_owner(q):
        return
    parts = (q.data or "").split(":")
    action = parts[1] if len(parts) > 1 else "m"
    cat = parts[2] if len(parts) > 2 else None
    note = None
    try:
        if action in ("c", "a", "t", "r") and cat not in OWNER_DEFAULTS:
            await q.answer("This button is no longer valid.", show_alert=True)
            return
        if action == "a":
            options = OWNER_DEFAULTS[cat]["options"]
            if len(parts) != 4 or not parts[3].isdigit() or int(parts[3]) >= len(options):
                await q.answer("This button is no longer valid.", show_alert=True)
                return
            await asyncio.to_thread(_owner_save, cat, options[int(parts[3])])
            note = "Saved."
        elif action == "t":
            if len(parts) != 4 or not parts[3].isdigit() or int(parts[3]) not in OWNER_TIMES:
                await q.answer("This button is no longer valid.", show_alert=True)
                return
            await asyncio.to_thread(_owner_save, cat, None, int(parts[3]))
            note = "Saved."
        elif action == "r":
            for key in OWNER_DEFAULTS[cat]["keys"]:
                await asyncio.to_thread(store.del_owner_default, key)
            note = "Back to the original."
    except store.DBError:
        logging.exception("owner defaults: save failed")
        await q.answer("The database had a problem. Nothing was changed.", show_alert=True)
        return
    await q.answer(note)
    if action in ("c", "a", "t", "r"):
        text, markup = owner_cat_text(cat), owner_cat_keyboard(cat)
    else:
        text, markup = owner_main_text(), owner_main_keyboard()
    try:
        await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup)
    except TelegramError:
        pass  # unchanged (double tap) or too old to edit


async def ban(update, context):
    if not await group_only(update):
        return
    uid, name, reason = await target_and_rest(update, context)
    if uid and await can_target(update, uid):
        await update.effective_chat.ban_member(uid)
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Unban", callback_data=f"unban:{uid}")]])
        by, why, punish = update.effective_user.mention_html(), reason[:200] or "Banned by an admin (no reason given)", extra.punishment_text("ban")
        sent = await update.effective_message.reply_html(extra.action_notice(name, "Banned", why, punish, by), reply_markup=kb)
        await extra.track_notice(sent)
        await extra.record_action(update.effective_chat.id, uid, name, "Banned", why, punish, by, "ban")
        await log_action(update.effective_chat, "ban", f"🚫 {by} banned {name}.")


async def unban(update, context):
    if not await group_only(update):
        return
    uid, name = await get_target(update, context)
    if uid:
        await update.effective_chat.unban_member(uid, only_if_banned=True)
        await update.effective_message.reply_html(f"Unbanned {name}.")
        await log_action(update.effective_chat, "ban", f"✅ {update.effective_user.mention_html()} unbanned {name}.")


async def kick(update, context):
    if not await group_only(update):
        return
    uid, name, reason = await target_and_rest(update, context)
    if uid and await can_target(update, uid):
        await update.effective_chat.ban_member(uid)
        await update.effective_chat.unban_member(uid)
        by, why, punish = update.effective_user.mention_html(), reason[:200] or "Kicked by an admin (no reason given)", extra.punishment_text("kick")
        sent = await update.effective_message.reply_html(extra.action_notice(name, "Kicked", why, punish, by))
        await extra.track_notice(sent)
        await extra.record_action(update.effective_chat.id, uid, name, "Kicked", why, punish, by, "ban")
        await log_action(update.effective_chat, "ban", f"👢 {by} kicked {name}.")


PROMOTE_PERMS = dict(
    can_manage_chat=True,
    can_delete_messages=True,
    can_restrict_members=True,
    can_pin_messages=True,
    can_invite_users=True,
    can_manage_video_chats=True,
    can_change_info=False,
    can_promote_members=False,
)
DEMOTE_PERMS = {k: False for k in PROMOTE_PERMS}


# ---- "Add New Admin" permission + tracking of admins this bot promoted (per group) ----
# Telegram's "Add New Admins" admin right (can_promote_members) is group-specific, and the group
# owner always has it. /promote needs it on the PROMOTER and on the BOT (never on the target).
ERR_NO_ADD_ADMIN = "❌ You don't have permission to add new admins."
ERR_BOT_NO_ADD_ADMIN = "❌ I don't have permission to add new admins. Please give me the required permission."
_PROMOTED_KEY = "bot_promoted_admins"  # per-group setting: comma-separated user IDs


async def has_add_admin_right(chat, user_id):
    """Does this user hold the 'Add New Admin' right in THIS chat? True/False, or None when
    Telegram wouldn't tell us. Always a fresh lookup (not the cached role)."""
    if is_bot_owner(user_id):
        return True  # owner power ON
    try:
        member = await chat.get_member(user_id)
    except TelegramError as e:
        logging.warning("get_member failed chat=%s user=%s: %s", chat.id, user_id, e)
        return None
    if member.status == ChatMemberStatus.OWNER:
        return True
    if member.status == ChatMemberStatus.ADMINISTRATOR:
        return bool(getattr(member, "can_promote_members", False))
    return False


def _bot_promoted_ids(chat_id) -> set:
    raw = str(get_setting(chat_id, _PROMOTED_KEY, "") or "")
    return {int(x) for x in raw.split(",") if x.strip().lstrip("-").isdigit()}


def was_promoted_by_bot(chat_id, user_id) -> bool:
    return user_id in _bot_promoted_ids(chat_id)


def track_bot_promotion(chat_id, user_id, promoted: bool):
    """Record (or forget) that this bot promoted user_id in this group only."""
    ids = _bot_promoted_ids(chat_id)
    if promoted:
        ids.add(user_id)
    else:
        ids.discard(user_id)
    set_setting(chat_id, _PROMOTED_KEY, ",".join(str(i) for i in sorted(ids)))


async def promote(update, context):
    """/promote [title]  - reply to or name the user to promote."""
    if not await group_only(update):
        return
    msg, chat, sender = update.effective_message, update.effective_chat, update.effective_user
    uid, name, title = await target_and_rest(update, context)
    if not uid:
        return
    # 1) The person using /promote must have "Add New Admin" in this group.
    if sender.id == ANON_ADMIN_ID or (msg.sender_chat and msg.sender_chat.id == chat.id):
        await msg.reply_text(
            "❌ I can't verify your \"Add New Admin\" permission while you post anonymously. "
            "Please send the command as yourself."
        )
        return
    sender_ok = await has_add_admin_right(chat, sender.id)
    if sender_ok is None:
        await msg.reply_text("⚠️ I couldn't check your permissions right now. Please try again.")
        return
    if not sender_ok:
        await msg.reply_text(ERR_NO_ADD_ADMIN)
        return
    # 2) The bot itself must have "Add New Admins" too.
    bot_ok = await has_add_admin_right(chat, context.bot.id)
    if bot_ok is None:
        await msg.reply_text("⚠️ I couldn't check my own permissions right now. Please try again.")
        return
    if not bot_ok:
        await msg.reply_text(ERR_BOT_NO_ADD_ADMIN)
        return
    # 3) The target is the member being promoted: its own rights are never checked, only "already admin".
    if await is_admin(chat, uid):
        await msg.reply_text("⚠️ This user is already an admin.")
        return
    try:
        await chat.promote_member(uid, **PROMOTE_PERMS)
    except TelegramError as e:
        logging.warning("Promote failed in chat %s: %s", chat.id, e)
        await msg.reply_text("I couldn't promote that user. Check my own admin rights.")
        return
    try:
        track_bot_promotion(chat.id, uid, True)  # this bot promoted them, in this group
    except Exception:
        logging.exception("Couldn't record promotion of %s in chat %s", uid, chat.id)
    _role_cache.pop((chat.id, uid), None)
    if title:
        try:
            await chat.set_administrator_custom_title(uid, title[:16])
        except TelegramError:
            pass  # title is optional; the promotion itself already succeeded
    await msg.reply_html(
        f"Promoted {name}" + (f" as <i>{html.escape(title[:16])}</i>." if title else ".")
    )
    await log_action(chat, "admin", f"⬆️ {update.effective_user.mention_html()} promoted {name}.")


async def _require_add_admin_for_demote(update, context) -> bool:
    """/demote gate: the person using it and the bot must both hold "Add New Admins" in
    THIS group (same rule as /promote). Replies with a clear reason and returns False if not."""
    msg, chat, sender = update.effective_message, update.effective_chat, update.effective_user
    if sender.id == ANON_ADMIN_ID or (msg.sender_chat and msg.sender_chat.id == chat.id):
        await msg.reply_text(
            "❌ I can't verify your \"Add New Admin\" permission while you post anonymously. "
            "Please send the command as yourself."
        )
        return False
    sender_ok = await has_add_admin_right(chat, sender.id)
    if sender_ok is None:
        await msg.reply_text("⚠️ I couldn't check your permissions right now. Please try again.")
        return False
    if not sender_ok:
        await msg.reply_text(ERR_NO_ADD_ADMIN)
        return False
    bot_ok = await has_add_admin_right(chat, context.bot.id)
    if bot_ok is None:
        await msg.reply_text("⚠️ I couldn't check my own permissions right now. Please try again.")
        return False
    if not bot_ok:
        await msg.reply_text(ERR_BOT_NO_ADD_ADMIN)
        return False
    return True


async def demote(update, context):
    """/demote  - reply to or name the admin to demote (only admins this bot promoted)."""
    if not await group_only(update):
        return
    msg, chat = update.effective_message, update.effective_chat
    if not await _require_add_admin_for_demote(update, context):
        return
    uid, name, _ = await target_and_rest(update, context)
    if not uid:
        return
    if not await is_admin(chat, uid):
        if was_promoted_by_bot(chat.id, uid):  # no longer an admin: drop the stale record
            track_bot_promotion(chat.id, uid, False)
        await msg.reply_html(f"{name} isn't an admin.")
        return
    not_mine = (
        f"❌ I can only demote admins that I promoted myself in this group. "
        f"{name} was not promoted by me."
    )
    if not was_promoted_by_bot(chat.id, uid):
        await msg.reply_html(not_mine)
        return
    # Telegram says whether this bot may still edit that admin; if not, our record is stale
    # (e.g. they were demoted and re-promoted by someone else).
    try:
        member = await chat.get_member(uid)
        if getattr(member, "can_be_edited", True) is False:
            track_bot_promotion(chat.id, uid, False)
            await msg.reply_html(not_mine)
            return
    except TelegramError as e:
        logging.warning("get_member failed in demote chat=%s: %s", chat.id, e)
    try:
        await chat.promote_member(uid, **DEMOTE_PERMS)
    except TelegramError as e:
        logging.warning("Demote failed in chat %s: %s", chat.id, e)
        await msg.reply_text(
            "I couldn't demote that user. Telegram only lets me demote admins that "
            "I promoted myself, and I need my own admin rights."
        )
        return
    track_bot_promotion(chat.id, uid, False)
    _role_cache.pop((chat.id, uid), None)
    await msg.reply_html(f"Demoted {name}.")
    await log_action(chat, "admin", f"⬇️ {update.effective_user.mention_html()} demoted {name}.")


async def _mute_cmd(update, context, timed_required=False, delete_replied=False):
    if not await group_only(update):
        return
    msg, chat = update.effective_message, update.effective_chat
    uid, name, rest = await target_and_rest(update, context)
    if not uid or not await can_target(update, uid):
        return
    secs, reason = split_time_reason(rest)
    if timed_required and not secs:
        await msg.reply_text("Usage: /tmute <time> [reason]  (time like 30m, 2h, 1d, 1w)")
        return
    if delete_replied and msg.reply_to_message:
        await try_delete(msg.reply_to_message)
    done = await do_action(chat, uid, f"tmute:{secs}" if secs else "mute")
    if not done:
        await msg.reply_text("I couldn't mute that user. Check my admin permissions.")
        return
    why = reason[:200] or "Muted by an admin (no reason given)"
    by, punish = update.effective_user.mention_html(), extra.punishment_text("mute", secs)
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Unmute", callback_data=f"unmute:{uid}")]])
    sent = await msg.reply_html(extra.action_notice(name, "Muted", why, punish, by), reply_markup=kb)
    await extra.track_notice(sent)
    await extra.record_action(chat.id, uid, name, "Muted", why, punish, by, "mute")
    await log_action(chat, "mute", f"🔇 {by} {done} {name}.\nReason: {html.escape(why)}")


async def mute(update, context):
    """/mute [time] [reason]  - no time means indefinitely."""
    await _mute_cmd(update, context)


async def tmute(update, context):
    """/tmute <time> [reason]"""
    await _mute_cmd(update, context, timed_required=True)


async def dmute(update, context):
    """/dmute [time] [reason]  - also deletes the replied-to message."""
    await _mute_cmd(update, context, delete_replied=True)


async def unmute(update, context):
    if not await group_only(update):
        return
    msg, chat = update.effective_message, update.effective_chat
    uid, name, _ = await target_and_rest(update, context)
    if not uid:
        return
    try:
        # Restore the group's default permissions (not a hard-coded set).
        perms = (await context.bot.get_chat(chat.id)).permissions or DEFAULT_PERMS
        await chat.restrict_member(uid, perms)
    except TelegramError as e:
        logging.warning("Unmute failed in chat %s: %s", chat.id, e)
        await msg.reply_text("I couldn't unmute that user. Check my admin permissions.")
        return
    await msg.reply_html(f"Unmuted {name}.")
    await log_action(chat, "mute", f"🔊 {update.effective_user.mention_html()} unmuted {name}.")


async def _warn_cmd(update, context, delete_replied=False):
    if not await admin_only(update):
        return
    msg, chat = update.effective_message, update.effective_chat
    uid, name, reason = await target_and_rest(update, context)
    if not uid or not await can_target(update, uid):
        return
    if delete_replied and msg.reply_to_message:
        await try_delete(msg.reply_to_message)
    text = await add_warn(chat, uid, name, reason[:200], update.effective_user.mention_html())
    kb = None
    if warn_summary(chat.id, uid).split("/")[0] != "0":
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🗑 Remove warning", callback_data=f"rmwarn:{uid}")]])
    await extra.track_notice(await msg.reply_html(text, reply_markup=kb))
    await log_action(chat, "warn", f"⚠️ {update.effective_user.mention_html()} warned {name}. {text}")


async def warn(update, context):
    """/warn [reason]"""
    await _warn_cmd(update, context)


async def dwarn(update, context):
    """/dwarn [reason]  - also deletes the replied-to message."""
    await _warn_cmd(update, context, delete_replied=True)


async def warns_cmd(update, context):
    """/warns  - your own warnings; admins can reply to or name someone else."""
    msg, chat, me = update.effective_message, update.effective_chat, update.effective_user
    if chat.type == "private":
        await msg.reply_text("This command only works in groups.")
        return
    if msg.reply_to_message or (context.args and (context.args[0].isdigit() or context.args[0].startswith("@"))):
        if not await admin_only(update):
            return
        uid, name, _ = await target_and_rest(update, context)
        if not uid:
            return
    else:
        uid, name = me.id, me.mention_html()
    rows = active_warns(chat.id, uid)
    limit = int(get_setting(chat.id, "warn_limit", 3))
    if not rows:
        await msg.reply_html(f"{name} has no warnings.")
        return
    lines = [f"{name} has {len(rows)}/{limit} warnings:"]
    for i, (_, reason, ts) in enumerate(rows, 1):
        date = time.strftime("%Y-%m-%d", time.gmtime(ts))
        lines.append(f"{i}. {html.escape(reason) if reason else 'no reason given'} ({date})")
    await msg.reply_html("\n".join(lines))


async def rmwarn(update, context):
    """/rmwarn  - remove a user's most recent warning."""
    if not await admin_only(update):
        return
    msg, chat = update.effective_message, update.effective_chat
    uid, name, _ = await target_and_rest(update, context)
    if not uid:
        return
    rows = active_warns(chat.id, uid)
    if not rows:
        await msg.reply_html(f"{name} has no warnings.")
        return
    store.warn_delete(rows[-1][0])
    limit = int(get_setting(chat.id, "warn_limit", 3))
    await msg.reply_html(f"Removed the latest warning from {name} ({len(rows) - 1}/{limit}).")
    await log_action(chat, "warn", f"🗑 {update.effective_user.mention_html()} removed a warning from {name}.")


async def modlog_cmd(update, context):
    """/modlog - the last actions taken in THIS group (admins only). History is kept for 15 days."""
    if not await group_only(update) or not await admin_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    try:
        rows = await asyncio.to_thread(store.modlog_recent, chat.id, 15)
    except store.DBError:
        logging.exception("modlog read failed in chat %s", chat.id)
        await msg.reply_text("I couldn't read the action history right now. Please try again.")
        return
    if not rows:
        await msg.reply_text("No actions recorded in the last 15 days.")
        return
    ist = timezone(timedelta(hours=5, minutes=30))
    lines = [f"Last {len(rows)} actions in this group (kept for {store.HISTORY_KEEP_DAYS} days, times in IST):", ""]
    for r in rows:
        when = datetime.fromtimestamp(r["ts"], ist).strftime("%d %b %I:%M %p")
        lines.append(f"{when}: {r['text']}")
    out = "\n".join(lines)
    await msg.reply_text(out[:4000])


async def resetwarns(update, context):
    if not await admin_only(update):
        return
    uid, name, _ = await target_and_rest(update, context)
    if uid:
        store.warn_clear(update.effective_chat.id, uid)
        await update.effective_message.reply_html(f"Warnings reset for {name}.")
        await log_action(update.effective_chat, "warn", f"🗑 {update.effective_user.mention_html()} reset warnings for {name}.")


async def warnlimit(update, context):
    """/warnlimit N  (also /setwarnlimit)"""
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    arg = context.args[0] if context.args else ""
    if arg.isdigit() and 1 <= int(arg) <= 100:
        set_setting(chat_id, "warn_limit", int(arg))
        await msg.reply_text(f"Warn limit set to {arg}.")
    else:
        current = get_setting(chat_id, "warn_limit", 3)
        await msg.reply_text(f"Warn limit is {current}.\nUsage: /warnlimit <1-100>")


async def warnmode(update, context):
    await _mode_cmd(
        update, context, "warnmode", "warn_mode", "ban",
        ("ban", "kick", "mute", "tmute"), "Action at the warn limit",
    )


async def warntime(update, context):
    """/warntime 7d  - make warnings expire (or /warntime off)."""
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    arg = context.args[0].lower() if context.args else ""
    if arg in ("off", "0", "no"):
        set_setting(chat_id, "warn_time", 0)
        await msg.reply_text("Warnings no longer expire.")
        return
    secs = parse_duration(arg)
    if secs:
        set_setting(chat_id, "warn_time", secs)
        await msg.reply_text(f"Warnings now expire after {fmt_duration(secs)}.")
        return
    expiry = int(get_setting(chat_id, "warn_time", 0))
    current = f"expire after {fmt_duration(expiry)}" if expiry else "never expire"
    await msg.reply_text(f"Warnings {current}.\nUsage: /warntime <30m|2h|7d|1w> or /warntime off")


# --------------------------------------------------------- welcome & rules
DEFAULT_WELCOME = "Welcome {mention} to {chat}!"
DEFAULT_GOODBYE = "Goodbye {first}, we'll miss you!"
PLACEHOLDERS = "{first} {last} {fullname} {username} {mention} {id} {chat} {count}"


def markdown_to_html(text):
    """Small Markdown subset on already-escaped text: *bold* _italic_ `code` ```pre``` [t](url)."""
    stash = []

    def keep(piece):
        stash.append(piece)
        return f"\x00{len(stash) - 1}\x00"

    text = re.sub(
        r"```(.+?)```", lambda m: keep(f"<pre>{m.group(1).strip()}</pre>"), text, flags=re.S
    )
    text = re.sub(r"`([^`\n]+)`", lambda m: keep(f"<code>{m.group(1)}</code>"), text)
    text = re.sub(
        r"\[([^\]\n]+)\]\(((?:https?://|tg://)[^\s)\"]+)\)",
        lambda m: keep(f'<a href="{m.group(2)}">{m.group(1)}</a>'),
        text,
    )
    text = re.sub(r"(?<!\w)\*(?=\S)(.+?)(?<=\S)\*(?!\w)", r"<b>\1</b>", text)
    text = re.sub(r"(?<!\w)_(?=\S)(.+?)(?<=\S)_(?!\w)", r"<i>\1</i>", text)
    return re.sub(r"\x00(\d+)\x00", lambda m: stash[int(m.group(1))], text)


def render(template, user, chat, count):
    """Fill placeholders. Template text is HTML-escaped; send with parse_mode=HTML."""
    text = markdown_to_html(html.escape(template, quote=False))
    values = {
        "{first}": html.escape(user.first_name or ""),
        "{last}": html.escape(user.last_name or ""),
        "{fullname}": html.escape(user.full_name or ""),
        "{username}": f"@{user.username}" if user.username else html.escape(user.first_name or ""),
        "{mention}": user.mention_html(),
        "{id}": str(user.id),
        "{chat}": html.escape(chat.title or ""),
        "{count}": str(count),
    }
    for key, val in values.items():
        text = text.replace(key, val)
    return text


async def safe_html(send, text):
    """Send as HTML; if Telegram rejects the markup, fall back to plain text."""
    try:
        return await send(text, parse_mode="HTML")
    except BadRequest:
        plain = html.unescape(re.sub(r"<[^>]+>", "", text))
        return await send(plain)


async def reply_rendered(update, template):
    """Reply with a template (placeholders + markdown) rendered for the sender."""
    chat, user, msg = update.effective_chat, update.effective_user, update.effective_message
    count = await chat.get_member_count() if "{count}" in template else ""
    return await safe_html(msg.reply_text, render(template, user, chat, count))


async def _set_greeting(update, key, label):
    if not await admin_only(update):
        return
    msg = update.effective_message
    text = msg.text.partition(" ")[2].strip()
    if not text and msg.reply_to_message:
        text = msg.reply_to_message.text or ""
    if not text:
        await msg.reply_text(f"Usage: /set{label} <text>\nPlaceholders: {PLACEHOLDERS}")
        return
    set_setting(update.effective_chat.id, key, text)
    await msg.reply_text(f"{label.capitalize()} message saved.")


async def _reset_greeting(update, key, label):
    if not await admin_only(update):
        return
    store.del_setting(update.effective_chat.id, key)
    await update.effective_message.reply_text(f"{label.capitalize()} message reset to default.")


async def setwelcome(update, context):
    await _set_greeting(update, "welcome", "welcome")


async def setgoodbye(update, context):
    await _set_greeting(update, "goodbye", "goodbye")


async def resetwelcome(update, context):
    await _reset_greeting(update, "welcome", "welcome")


async def resetgoodbye(update, context):
    await _reset_greeting(update, "goodbye", "goodbye")


async def welcome_cmd(update, context):
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    flag = _on_off(context)
    if flag is not None:
        set_setting(chat_id, "welcome_on", flag)
        await msg.reply_text(f"Welcome messages: {'on' if flag else 'off'}.")
        return
    on = get_setting(chat_id, "welcome_on", "True") == "True"
    clean = get_setting(chat_id, "clean_welcome", "False") == "True"
    template = get_setting(chat_id, "welcome", DEFAULT_WELCOME)
    await msg.reply_text(
        f"Welcome messages: {'on' if on else 'off'}\n"
        f"Clean welcome: {'on' if clean else 'off'}\n"
        f"Current message:\n{template}\n\n"
        f"Placeholders: {PLACEHOLDERS}"
    )


async def goodbye_cmd(update, context):
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    flag = _on_off(context)
    if flag is not None:
        set_setting(chat_id, "goodbye_on", flag)
        await msg.reply_text(f"Goodbye messages: {'on' if flag else 'off'}.")
        return
    on = get_setting(chat_id, "goodbye_on", "False") == "True"
    template = get_setting(chat_id, "goodbye", DEFAULT_GOODBYE)
    await msg.reply_text(
        f"Goodbye messages: {'on' if on else 'off'}\n"
        f"Current message:\n{template}\n\n"
        f"Placeholders: {PLACEHOLDERS}"
    )


async def cleanwelcome(update, context):
    """When on, the previous welcome message is deleted as a new one is sent."""
    if not await admin_only(update):
        return
    flag = _on_off(context)
    if flag is None:
        await update.effective_message.reply_text("Usage: /cleanwelcome on|off")
        return
    set_setting(update.effective_chat.id, "clean_welcome", flag)
    await update.effective_message.reply_text(f"Clean welcome: {'on' if flag else 'off'}.")


async def send_welcome(context, chat, user, reply_to=None):
    """Send the chat's welcome message for one user (honours /welcome and /cleanwelcome)."""
    if get_setting(chat.id, "welcome_on", "True") != "True":
        return
    template = get_setting(chat.id, "welcome", DEFAULT_WELCOME)
    count = await chat.get_member_count()

    if get_setting(chat.id, "clean_welcome", "False") == "True":
        old = get_setting(chat.id, "last_welcome_id")
        if old:
            try:
                await context.bot.delete_message(chat.id, int(old))
            except TelegramError:
                pass

    template, markup = await template_markup(template, context, chat.id)
    send = reply_to.reply_text if reply_to else chat.send_message
    if markup:
        send = functools.partial(send, reply_markup=markup)
    sent = await safe_html(send, render(template, user, chat, count))
    set_setting(chat.id, "last_welcome_id", sent.message_id)


async def on_new_members(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat, msg = update.effective_chat, update.effective_message
    adder = msg.from_user
    adder_is_admin = bool(adder and await is_admin(chat, adder.id))
    verify = get_setting(chat.id, "captcha", "False") == "True"

    for user in msg.new_chat_members:
        if user.is_bot:
            continue
        added_by_admin = adder_is_admin and adder.id != user.id
        if verify and not added_by_admin and not is_bot_owner(user.id) and not await is_admin(chat, user.id):
            await start_captcha(context, chat, user)
        else:
            await send_welcome(context, chat, user, reply_to=msg)


async def on_left_member(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat, msg = update.effective_chat, update.effective_message
    user = msg.left_chat_member
    if not user or user.is_bot:
        return
    await captcha_cleanup(context, chat.id, user.id)
    if get_setting(chat.id, "goodbye_on", "False") != "True":
        return
    template = get_setting(chat.id, "goodbye", DEFAULT_GOODBYE)
    count = await chat.get_member_count()
    template, markup = await template_markup(template, context, chat.id)
    send = functools.partial(chat.send_message, reply_markup=markup) if markup else chat.send_message
    await safe_html(send, render(template, user, chat, count))


# ------------------------------------------------------------ rules module
DEFAULT_RULES_BUTTON = "Rules"
NO_RULES_TEXT = "The group admins haven't set any rules for this chat yet."
RULES_MAX = 4000  # Telegram's message limit is 4096 characters
BUTTON_RE = re.compile(r"\[([^\]\n]+)\]\(buttonurl://([^\s)]+?)(:same)?\)")
YES_WORDS = {"yes", "on", "true", "enable", "enabled", "1"}
NO_WORDS = {"no", "off", "false", "disable", "disabled", "0"}


def parse_yes_no(args):
    """True / False for yes|on / no|off, None if missing or unclear."""
    if args:
        word = args[0].lower()
        if word in YES_WORDS:
            return True
        if word in NO_WORDS:
            return False
    return None


async def bot_username(context):
    return context.bot.username or (await context.bot.get_me()).username


def rules_button_text(chat_id):
    return get_setting(chat_id, "rules_button") or DEFAULT_RULES_BUTTON


async def rules_button(context, chat_id):
    link = f"https://t.me/{await bot_username(context)}?start=rules_{chat_id}"
    return InlineKeyboardButton(rules_button_text(chat_id), url=link)


def extract_buttons(template):
    """Pull [Label](buttonurl://https://example.com) out of a template.
    Add ':same' after the URL to put a button on the previous row.
    Returns (text without the buttons, rows of InlineKeyboardButton)."""
    rows = []

    def grab(m):
        label, url, same = m.group(1).strip(), m.group(2), bool(m.group(3))
        if not re.match(r"(?i)(https?://|tg://)", url):
            return m.group(0)  # not a safe link: leave it as plain text
        button = InlineKeyboardButton(label, url=url)
        if same and rows:
            rows[-1].append(button)
        else:
            rows.append([button])
        return ""

    return BUTTON_RE.sub(grab, template).strip(), rows


async def template_markup(template, context, chat_id):
    """Buttons for welcome/goodbye text: [..](buttonurl://..) links, and {rules}
    becomes the rules button. Returns (clean text, markup or None)."""
    body, rows = extract_buttons(template)
    if "{rules}" in body:
        body = body.replace("{rules}", "").strip()
        rows.append([await rules_button(context, chat_id)])
    if rows and not body:
        body = "👋"
    return body, (InlineKeyboardMarkup(rows) if rows else None)


async def send_rules(send, chat, user, text):
    """Render rules text (markdown, placeholders, buttons) and send it."""
    body, rows = extract_buttons(text)
    count = await chat.get_member_count() if "{count}" in body else ""
    if rows:
        send = functools.partial(send, reply_markup=InlineKeyboardMarkup(rows))
    return await safe_html(send, render(body or "📜", user, chat, count))


async def deliver_rules_pm(update, context, chat_id):
    """/start rules_<chat id>: send a group's rules to someone in private."""
    msg, user = update.effective_message, update.effective_user
    try:
        chat = await context.bot.get_chat(chat_id)
    except TelegramError as e:
        logging.warning("Rules deep link: can't open chat %s: %s", chat_id, e)
        await msg.reply_text("I couldn't find that group. Ask an admin to add me back to it.")
        return
    if await get_role(chat, user.id) in (None, ChatMemberStatus.LEFT, ChatMemberStatus.BANNED):
        await msg.reply_text("You need to be a member of that group to read its rules.")
        return
    text = get_setting(chat_id, "rules")
    if not text:
        await msg.reply_text(NO_RULES_TEXT)
        return
    await send_rules(msg.reply_text, chat, user, text)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    arg = context.args[0] if context.args else ""
    if chat.type == "private" and arg.startswith("rules_"):
        try:
            await deliver_rules_pm(update, context, int(arg[len("rules_"):]))
        except ValueError:
            await update.effective_message.reply_text("That rules link isn't valid.")
        return
    await update.effective_message.reply_text(
        f"Hi! I'm {extra.bot_name()}. Add me to your group as an admin and use /help."
    )


async def setrules(update, context):
    if not await group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    text = command_args_text(msg)
    if not text and msg.reply_to_message:
        text = (msg.reply_to_message.text or msg.reply_to_message.caption or "").strip()
    if not text:
        await msg.reply_text(
            "Usage: /setrules <text>  (or reply to a message with /setrules)\n"
            "Formatting: *bold* _italic_ `code` [link](https://example.com)\n"
            "Button: [Label](buttonurl://https://example.com)\n"
            f"Placeholders: {PLACEHOLDERS}"
        )
        return
    if len(text) > RULES_MAX:
        await msg.reply_text(f"❌ Those rules are too long ({len(text)} characters, max {RULES_MAX}).")
        return
    set_setting(chat.id, "rules", text)
    await msg.reply_text("✅ Rules saved. Use /rules to preview them.")


async def resetrules(update, context):
    if not await group_only(update):
        return
    store.del_setting(update.effective_chat.id, "rules")
    await update.effective_message.reply_text("✅ Rules reset. This chat has no rules now.")


async def rules(update, context):
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if chat.type == "private":
        await msg.reply_text("Use /rules inside a group to read that group's rules.")
        return
    text = get_setting(chat.id, "rules")
    if not text:
        await msg.reply_text(NO_RULES_TEXT)
        return
    if context.args and context.args[0].lower() in ("noformat", "raw"):
        await msg.reply_text(text)  # no parse_mode: exactly what's stored, easy to copy and edit
        return
    if get_setting(chat.id, "rules_private", "False") == "True":
        kb = InlineKeyboardMarkup([[await rules_button(context, chat.id)]])
        await msg.reply_text("Tap the button below to read this group's rules in private.", reply_markup=kb)
        return
    await send_rules(msg.reply_text, chat, user, text)


async def privaterules(update, context):
    if not await group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    flag = parse_yes_no(context.args)
    if flag is None:
        on = get_setting(chat.id, "rules_private", "False") == "True"
        await msg.reply_text(f"Private rules are {'on' if on else 'off'}.\nUse /privaterules yes or /privaterules no.")
        return
    set_setting(chat.id, "rules_private", "True" if flag else "False")
    await msg.reply_text(
        "✅ /rules will now show a button that opens the rules in private." if flag
        else "✅ /rules will now show the rules in the group."
    )


async def setrulesbutton(update, context):
    if not await group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    text = " ".join(command_args_text(msg).split())
    if not text:
        await msg.reply_text(f"Usage: /setrulesbutton <text>\nCurrent button: {rules_button_text(chat.id)}")
        return
    if len(text) > 64:
        await msg.reply_text("❌ Button text can be at most 64 characters.")
        return
    set_setting(chat.id, "rules_button", text)
    await msg.reply_text(f"✅ Rules button is now: {text}")


async def resetrulesbutton(update, context):
    if not await group_only(update):
        return
    store.del_setting(update.effective_chat.id, "rules_button")
    await update.effective_message.reply_text(f"✅ Rules button is back to \"{DEFAULT_RULES_BUTTON}\".")


# ------------------------------------------------- join verification (captcha)
CAPTCHA_ATTEMPTS = 3


def captcha_text(chat_id):
    if get_setting(chat_id, "captcha", "False") != "True":
        return "off"
    mode = get_setting(chat_id, "captcha_mode", "button")
    secs = int(get_setting(chat_id, "captcha_time", 120))
    action = describe_mode(get_setting(chat_id, "captcha_action", "kick"))
    return f"{mode} check, {fmt_duration(secs)} to answer, then {action}"


async def restore_permissions(context, chat, user_id):
    """Give a user back the group's default permissions."""
    try:
        perms = (await context.bot.get_chat(chat.id)).permissions or DEFAULT_PERMS
        await chat.restrict_member(user_id, perms)
        return True
    except TelegramError as e:
        logging.warning("Couldn't restore permissions in chat %s: %s", chat.id, e)
        return False


async def start_captcha(context, chat, user):
    """Mute a new member and post a challenge; falls back to a plain welcome on failure."""
    pending = store.captcha_get(chat.id, user.id)
    if pending:
        try:  # they rejoined mid-challenge: replace the old one
            await context.bot.delete_message(chat.id, pending[0])
        except TelegramError:
            pass
    else:
        try:
            member = await chat.get_member(user.id)
            if member.status == "restricted" and not getattr(member, "can_send_messages", True):
                return  # already muted by an admin; don't override that
        except TelegramError:
            pass

    try:
        await chat.restrict_member(user.id, MUTED)
    except TelegramError as e:
        logging.warning("Captcha: can't restrict in chat %s (%s); sending plain welcome", chat.id, e)
        await send_welcome(context, chat, user)
        return

    mode = get_setting(chat.id, "captcha_mode", "button")
    secs = int(get_setting(chat.id, "captcha_time", 120))
    question, answer, options = make_challenge(mode)
    keyboard = InlineKeyboardMarkup(
        [[InlineKeyboardButton(label, callback_data=f"cap:{user.id}:{value}") for label, value in options]]
    )
    mention = user.mention_html()
    try:
        sent = await chat.send_message(
            f"Welcome {mention}! Please verify within {fmt_duration(secs)} to start chatting.\n{question}",
            parse_mode="HTML",
            reply_markup=keyboard,
        )
    except TelegramError as e:
        logging.warning("Captcha: couldn't post challenge in chat %s: %s", chat.id, e)
        await restore_permissions(context, chat, user.id)
        return
    store.captcha_put(chat.id, user.id, sent.message_id, answer, 0, int(time.time()) + secs, mention)


async def captcha_fail(bot, chat_id, user_id, msg_id, mention, why):
    """Remove the challenge and apply the chat's captcha action."""
    try:
        await bot.delete_message(chat_id, msg_id)
    except TelegramError:
        pass
    try:
        chat = await bot.get_chat(chat_id)
    except TelegramError as e:
        logging.warning("Captcha: can't reach chat %s: %s", chat_id, e)
        return
    mode = get_setting(chat_id, "captcha_action", "kick")
    done = await do_action(chat, user_id, mode)
    if done:
        kind, secs = extra.mode_kind(mode)
        label, punish = extra.ACTION_LABEL.get(kind, kind.title()), extra.punishment_text(kind, secs)
        reason = f"Failed the CAPTCHA: {why}"
        text = extra.action_notice(mention, label, reason, punish)
        await announce(chat, text, user_id)
        await extra.record_action(chat_id, user_id, mention, label, reason, punish, None, "captcha")
        await log_action(chat, "captcha", f"🤖 {text}")


async def captcha_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    _, uid_text, choice = q.data.split(":", 2)
    uid = int(uid_text)
    chat = q.message.chat
    if q.from_user.id != uid:
        await q.answer("This verification isn't for you.", show_alert=True)
        return
    row = store.captcha_get(chat.id, uid)
    if not row:
        await q.answer("This verification has expired.")
        return
    msg_id, answer, attempts, mention = row

    if choice == answer:
        store.captcha_delete(chat.id, uid)
        await restore_permissions(context, chat, uid)
        await q.answer("Verified, welcome!")
        await try_delete(q.message)
        await send_welcome(context, chat, q.from_user)
        return

    attempts += 1
    if attempts >= CAPTCHA_ATTEMPTS:
        store.captcha_delete(chat.id, uid)
        await q.answer("Wrong answer.", show_alert=True)
        await captcha_fail(context.bot, chat.id, uid, msg_id, mention, "failed verification")
    else:
        store.captcha_set_attempts(chat.id, uid, attempts)
        left = CAPTCHA_ATTEMPTS - attempts
        await q.answer(f"Wrong answer. {left} {'try' if left == 1 else 'tries'} left.", show_alert=True)


async def captcha_cleanup(context, chat_id, user_id):
    """A member left mid-challenge: drop the challenge message and record."""
    msg_id = store.captcha_pop(chat_id, user_id)
    if msg_id:
        try:
            await context.bot.delete_message(chat_id, msg_id)
        except TelegramError:
            pass


async def captcha_release_all(context, chat):
    """Captcha turned off: let everyone still waiting in."""
    rows = store.captcha_pop_chat(chat.id)
    for user_id, msg_id in rows:
        try:
            await context.bot.delete_message(chat.id, msg_id)
        except TelegramError:
            pass
        await restore_permissions(context, chat, user_id)


def _take_expired_captchas(now):
    return store.captcha_take_expired(now)


async def captcha_sweeper(app):
    """Background loop: fail challenges that timed out (survives restarts via the DB)."""
    while True:
        await asyncio.sleep(15)
        try:
            rows = await asyncio.to_thread(_take_expired_captchas, int(time.time()))
            for chat_id, user_id, msg_id, mention in rows:
                await captcha_fail(app.bot, chat_id, user_id, msg_id, mention, "didn't verify in time")
        except Exception:
            logging.exception("Captcha sweeper error")


async def captcha_cmd(update, context):
    """/captcha on|off"""
    if not await admin_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    flag = _on_off(context)
    if flag is not None:
        set_setting(chat.id, "captcha", flag)
        if not flag:
            await captcha_release_all(context, chat)
    await msg.reply_text(
        f"Captcha: {captcha_text(chat.id)}\n"
        "Settings: /captchamode button|math, /captchatime <1m-60m>, "
        "/captchaaction kick|mute|ban.\n"
        "I need permission to restrict members for this to work."
    )


async def captchamode(update, context):
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    arg = context.args[0].lower() if context.args else ""
    if arg in ("button", "math"):
        set_setting(chat_id, "captcha_mode", arg)
        await msg.reply_text(f"Captcha mode: {arg}")
    else:
        current = get_setting(chat_id, "captcha_mode", "button")
        await msg.reply_text(f"Captcha mode: {current}\nUsage: /captchamode button|math")


async def captchatime(update, context):
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    secs = parse_duration(context.args[0].lower()) if context.args else None
    if secs and 60 <= secs <= 3600:
        set_setting(chat_id, "captcha_time", secs)
        await msg.reply_text(f"New members have {fmt_duration(secs)} to verify.")
    else:
        current = int(get_setting(chat_id, "captcha_time", 120))
        await msg.reply_text(
            f"New members have {fmt_duration(current)} to verify.\nUsage: /captchatime <1m-60m>"
        )


async def captchaaction(update, context):
    await _mode_cmd(
        update, context, "captchaaction", "captcha_action", "kick",
        ("kick", "mute", "ban"), "Action when verification fails",
    )


# ------------------------------------------------------------ notes/filters
async def save_note(update, context):
    if not await admin_only(update):
        return
    msg = update.effective_message
    if not context.args:
        await msg.reply_text("Usage: /save name text (or reply to a message)")
        return
    name = context.args[0].lower()
    content = msg.text.partition(name)[2].strip() if len(context.args) > 1 else ""
    if not content and msg.reply_to_message:
        content = msg.reply_to_message.text or ""
    if not content:
        await msg.reply_text("Give me some text or reply to a message.")
        return
    store.note_set(update.effective_chat.id, name, content)
    await msg.reply_text(f"Saved note '{name}'. Get it with #{name}")
    await log_action(update.effective_chat, "note", f"📝 {update.effective_user.mention_html()} saved note '{name}'.")


async def get_note(update, context):
    if not context.args:
        return
    content = store.note_get(update.effective_chat.id, context.args[0].lower())
    if content is not None:
        await reply_rendered(update, content)
    else:
        await update.effective_message.reply_text("Note not found.")


async def list_notes(update, context):
    text = "\n".join(f"- #{n}" for n in store.note_names(update.effective_chat.id)) or "No notes saved."
    await update.effective_message.reply_text(text)


async def clear_note(update, context):
    if not await admin_only(update) or not context.args:
        return
    store.note_del(update.effective_chat.id, context.args[0].lower())
    await update.effective_message.reply_text("Note removed.")
    await log_action(update.effective_chat, "note", f"🗑 {update.effective_user.mention_html()} removed note '{context.args[0].lower()}'.")


async def add_filter(update, context):
    if not await admin_only(update):
        return
    msg = update.effective_message
    keyword, reply = split_keyword(msg.text.partition(" ")[2])
    if not reply and msg.reply_to_message:
        reply = msg.reply_to_message.text or msg.reply_to_message.caption or ""
    if not keyword or not reply:
        await msg.reply_text(
            'Usage: /filter keyword reply text\n'
            'Phrases: /filter "good morning" Hello {first}!\n'
            "Or reply to a message with /filter keyword.\n"
            f"Placeholders: {PLACEHOLDERS}"
        )
        return
    store.filter_add(update.effective_chat.id, keyword, reply)
    await msg.reply_text(f"Filter '{keyword}' added.")
    await log_action(update.effective_chat, "filter", f"➕ {update.effective_user.mention_html()} added filter '{keyword}'.")


async def stop_filter(update, context):
    if not await admin_only(update):
        return
    keyword, _ = split_keyword(update.effective_message.text.partition(" ")[2])
    if not keyword:
        await update.effective_message.reply_text("Usage: /stop keyword")
        return
    removed = store.filter_remove(update.effective_chat.id, keyword)
    await update.effective_message.reply_text(
        "Filter removed." if removed else "No such filter."
    )
    if removed:
        await log_action(update.effective_chat, "filter", f"➖ {update.effective_user.mention_html()} removed filter '{keyword}'.")


async def list_filters(update, context):
    rows = store.filter_rows(update.effective_chat.id)
    text = "\n".join(f"- {r[0]}" for r in rows) or "No filters set."
    await update.effective_message.reply_text(text)


async def addblocklist(update, context):
    if not await admin_only(update):
        return
    word, _ = split_keyword(update.effective_message.text.partition(" ")[2])
    if not word:
        await update.effective_message.reply_text(
            'Usage: /addblocklist word  (quotes for phrases, * as wildcard: spam*)'
        )
        return
    store.block_add(update.effective_chat.id, word)
    await update.effective_message.reply_text(
        f"'{word}' added to the blocklist "
        f"(action: {describe_mode(get_setting(update.effective_chat.id, 'blocklist_mode', 'delete'))})."
    )
    await log_action(update.effective_chat, "blocklist", f"➕ {update.effective_user.mention_html()} blocklisted '{word}'.")


async def unblocklist(update, context):
    if not await admin_only(update):
        return
    word, _ = split_keyword(update.effective_message.text.partition(" ")[2])
    if not word:
        await update.effective_message.reply_text("Usage: /unblocklist word")
        return
    removed = store.block_remove(update.effective_chat.id, word)
    await update.effective_message.reply_text(
        "Removed from the blocklist." if removed else "That word isn't blocklisted."
    )
    if removed:
        await log_action(update.effective_chat, "blocklist", f"➖ {update.effective_user.mention_html()} removed '{word}' from the blocklist.")


async def blocklist_cmd(update, context):
    if not await admin_only(update):
        return
    chat_id = update.effective_chat.id
    mode = get_setting(chat_id, "blocklist_mode", "delete")
    words = "\n".join(f"- {w}" for w in store.block_words(chat_id)) or "The blocklist is empty."
    await update.effective_message.reply_text(
        f"Blocklist action: {describe_mode(mode)}\n\n{words}"
    )


async def blocklistmode(update, context):
    await _mode_cmd(
        update, context, "blocklistmode", "blocklist_mode", "delete",
        ("nothing", "delete", "warn", "mute", "tmute", "kick", "ban"), "Blocklist action",
    )


# ------------------------------------------------------------- log channels
async def setlog(update, context):
    """Send in the channel itself; the bot must be admin there."""
    chat, msg = update.effective_chat, update.effective_message
    if chat.type != "channel":
        await msg.reply_text("Send /setlog inside the channel you want to log to, not here.")
        return
    sent = await chat.send_message(
        "Forward this message to the group you want logged, within 10 minutes."
    )
    store.setlog_put(chat.id, sent.message_id, int(time.time()))


async def unsetlog(update, context):
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    if not get_setting(chat_id, "log_channel"):
        await msg.reply_text("No log channel is set.")
        return
    set_setting(chat_id, "log_channel", "")
    await msg.reply_text("Log channel unset.")


async def logchannel(update, context):
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    log_id = get_setting(chat_id, "log_channel")
    if not log_id:
        await msg.reply_text("No log channel is set. Use /setlog to set one.")
        return
    try:
        title = (await context.bot.get_chat(int(log_id))).title
    except TelegramError:
        title = f"chat {log_id}"
    enabled = get_setting(chat_id, "log_categories", "") or "none"
    await msg.reply_text(f"Log channel: {title}\nCategories logged: {enabled}")


async def _log_toggle(update, context, enable):
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    if not context.args:
        cats = ", ".join(LOG_CATS)
        await msg.reply_text(f"Usage: /{'log' if enable else 'nolog'} <category>\nCategories: {cats}")
        return
    cat = context.args[0].lower()
    if cat not in LOG_CATS:
        await msg.reply_text(f"Unknown category '{cat}'. See /logcategories.")
        return
    current = set(filter(None, get_setting(chat_id, "log_categories", "").split(",")))
    current.add(cat) if enable else current.discard(cat)
    set_setting(chat_id, "log_categories", ",".join(sorted(current)))
    await msg.reply_text(f"'{cat}' logging {'enabled' if enable else 'disabled'}.")


async def log_enable(update, context):
    await _log_toggle(update, context, True)


async def log_disable(update, context):
    await _log_toggle(update, context, False)


async def logcategories(update, context):
    lines = [f"{i}. <b>{k}</b>: {v}" for i, (k, v) in enumerate(LOG_CATS.items(), 1)]
    await update.effective_message.reply_html(
        "<b>Log categories</b>\nEnable with /log &lt;category&gt;, disable with /nolog.\n\n"
        + "\n".join(lines)
    )


async def check_setlog_forward(update, context):
    """If this group message is the forward that completes a /setlog handshake, wire it up."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    origin = getattr(msg, "forward_origin", None)
    origin_chat = getattr(origin, "chat", None)
    origin_msg_id = getattr(origin, "message_id", None)
    if not origin_chat or origin_msg_id is None:
        return False
    row = store.setlog_get(origin_chat.id)
    if not row or row[0] != origin_msg_id or time.time() - row[1] > SETLOG_TIMEOUT:
        return False
    if not await is_admin(chat, user.id):
        await msg.reply_text("Only a group admin can finish setting up the log channel.")
        return True
    # The channel must belong to whoever links it: otherwise one group's logs could be pointed at (and mixed
    # into) a channel another group uses. The Bot Owner and Super Admins are exempt.
    if user.id not in OWNER_IDS and not is_super_admin(user.id):
        try:
            channel_admin = (await context.bot.get_chat_member(origin_chat.id, user.id)).status in ADMIN_STATUSES
        except TelegramError:
            channel_admin = False
        if not channel_admin:
            await msg.reply_text("Only an admin of that channel can set it as this group's log channel.")
            return True
    set_setting(chat.id, "log_channel", origin_chat.id)
    store.setlog_del(origin_chat.id)
    await msg.reply_text(f"Log channel set to {origin_chat.title}. Enable categories with /log.")
    return True


_sug_synced = set()   # groups whose command list was already published this run
_sug_locks = {}       # one toggle at a time per chat
_BOT_ID = None        # set in post_init: settings that mirror Telegram state are keyed per bot

SUG_DENIED = "Only Group Admins, Bot Owner, or Moderators can toggle this setting."
HELP_ONLY = [BotCommand("help", "Open the help menu")]


_toggle_locks = {}


def _toggle_lock(chat_id):
    return _toggle_locks.setdefault(chat_id, asyncio.Lock())


def _bkey(name):
    """Telegram stores command lists PER BOT. If the main bot and the test bot share one
    database file, a plain key would make one bot believe the other one's state is its own
    (e.g. the test bot skipping its first command publish because prod already did it)."""
    return f"{name}:{_BOT_ID}" if _BOT_ID else name


def suggestions_on(chat_id) -> bool:
    val = get_setting(chat_id, _bkey("suggestions_on"))
    if val is None:  # older versions stored one shared key; use it only as the starting value
        val = get_setting(chat_id, "suggestions_on", "True")
    return val == "True"


COMMON_LANGS = ("en", "hi", "ur", "ar", "bn", "es", "ru", "pt", "id", "tr", "fa")


async def _try_delete(bot, scope, code=None):
    try:
        await bot.delete_my_commands(scope=scope, language_code=code)
    except TelegramError:
        pass  # nothing stored there, which is what we want


async def _gather_limited(coros, limit=6):
    """Run Telegram calls concurrently (a few at a time) instead of one after another."""
    sem = asyncio.Semaphore(limit)

    async def run(c):
        async with sem:
            return await c

    await asyncio.gather(*(run(c) for c in coros))


async def can_toggle_suggestions(chat, user_id, msg=None) -> bool:
    """Bot Owner, Bot Moderators (Super Admins) and group admins/owner only."""
    if is_bot_owner(user_id) or is_super_admin(user_id):
        return True
    if msg is not None and msg.sender_chat is not None and msg.sender_chat.id == chat.id:
        return True  # anonymous group admin
    return await is_admin(chat, user_id)


async def clear_stale_scopes(bot, chat_id, langs=()):
    """Telegram always shows the MOST specific list: member > chat-admins > chat > ...
    Older versions (or BotFather) may have left lists at more specific scopes or in other
    languages, which would silently override the on/off switch. Every toggle clears the
    clicker's language; the full sweep (all common languages + every admin's member-scope)
    runs once per chat per bot."""
    codes = [c for c in dict.fromkeys(list(langs) + ["en"]) if c]
    full = get_setting(chat_id, _bkey("sug_clean")) != "1"
    if full:
        codes = list(dict.fromkeys(codes + list(COMMON_LANGS)))
    jobs = [_try_delete(bot, BotCommandScopeChatAdministrators(chat_id), None)]
    for code in codes:
        jobs.append(_try_delete(bot, BotCommandScopeChatAdministrators(chat_id), code))
        jobs.append(_try_delete(bot, BotCommandScopeChat(chat_id), code))  # language variants of the chat list
    swept = True
    if full:
        try:
            admins = await bot.get_chat_administrators(chat_id)
        except TelegramError:
            admins, swept = [], False
        for a in admins[:30]:
            if not a.user.is_bot:
                for code in [None] + codes:
                    jobs.append(_try_delete(bot, BotCommandScopeChatMember(chat_id, a.user.id), code))
    await _gather_limited(jobs)
    if full and swept:
        set_setting(chat_id, _bkey("sug_clean"), "1")


async def _publish_chat_commands(bot, chat_id, on):
    """The one place that writes the chat's command list: explicit BotCommandScopeChat,
    full list when ON, only /help when OFF (Telegram doesn't accept an empty list)."""
    cmds = BOT_COMMANDS if on else HELP_ONLY
    for attempt in range(2):
        try:
            await bot.set_my_commands(cmds, scope=BotCommandScopeChat(chat_id))
            return
        except RetryAfter as e:
            if attempt:
                raise
            await asyncio.sleep(_retry_seconds(e))


async def apply_suggestions(bot, chat_id, on, langs=()) -> bool:
    """Show or hide the "/" command menu for the WHOLE chat. Commands keep working either way."""
    lock = _sug_locks.setdefault(chat_id, asyncio.Lock())
    async with lock:
        try:
            await clear_stale_scopes(bot, chat_id, langs)
            await _publish_chat_commands(bot, chat_id, on)
        except TelegramError as e:
            logging.warning("Couldn't update command suggestions in chat %s: %s: %s",
                            chat_id, type(e).__name__, e)
            return False
        set_setting(chat_id, _bkey("suggestions_on"), on)
        _sug_synced.add(chat_id)
        return True


async def sync_suggestions(update, context):
    """First time we see a group this run (or after the bot was re-added), re-publish the
    stored state - ON or OFF - to Telegram so the database flag and the real list agree."""
    chat = update.effective_chat
    if not chat or chat.type == "private" or chat.id in _sug_synced:
        return
    _sug_synced.add(chat.id)
    try:
        await _publish_chat_commands(context.bot, chat.id, suggestions_on(chat.id))
    except TelegramError as e:
        _sug_synced.discard(chat.id)
        logging.warning("Couldn't publish commands for %s: %s", chat.id, e)


# --------------------------------------------------- automatic name-change detection
# No command: runs on every ordinary group message (see group=-4 in main()). The last seen
# first/last name is kept per (group, Telegram user ID) in the same database as the other
# settings, so it survives restarts. Reads hit an in-memory cache first and the database is
# written only the first time a user is seen or when their name actually changes.
_name_seen = {}  # (chat_id, user_id) -> (first_name, last_name) as last recorded


def _full_name(first, last):
    return " ".join(p for p in (first, last) if p).strip() or "Unknown"


async def name_change_watch(update, context):
    chat, user, msg = update.effective_chat, update.effective_user, update.effective_message
    try:
        if not chat or not user or not msg or chat.type == "private":
            return
        # skip bots, anonymous-admin / channel senders (their "name" is the group or channel)
        if user.is_bot or user.id == ANON_ADMIN_ID or msg.sender_chat:
            return
        key = (chat.id, user.id)
        current = (user.first_name or "", user.last_name or "")
        old = _name_seen.get(key)
        if old is None:  # not cached this run: look in the database (itself cached)
            raw = get_setting(chat.id, f"lastname:{user.id}", "")
            if raw:
                first, _, last = str(raw).partition("\n")
                old = (first, last)
        if old == current:
            _name_seen[key] = current
            return
        # first time we ever see this user here, or the name really changed: store the new name
        _name_seen[key] = current  # cache first: even if the DB write fails, no repeat spam
        try:
            set_setting(chat.id, f"lastname:{user.id}", f"{current[0]}\n{current[1]}")
        except Exception:
            logging.exception("Couldn't store last name for %s in %s", user.id, chat.id)
        if old is None:
            return  # first sighting: just record it, nothing to announce
        text = (
            "🔄 <b>Name Change Detected</b>\n"
            f"{html.escape(_full_name(*old))} changed their name to "
            f"{html.escape(_full_name(*current))}.\n"
            f'👤 User ID: "<code>{user.id}</code>"'
        )
        if user.username:
            text += f'\n🔗 Username: "@{html.escape(user.username)}"'
        await chat.send_message(text, parse_mode="HTML")
    except TelegramError as e:
        logging.warning("Name-change notice failed in %s: %s", chat.id if chat else "?", e)
    except Exception:
        logging.exception("name_change_watch failed")  # never let this block other handlers


def suggestions_button(chat_id, origin):
    on = suggestions_on(chat_id) if chat_id < 0 else True  # private chats: always on
    label = "⌨️ Command suggestions: ON ✅" if on else "⌨️ Command suggestions: OFF ❌"
    return InlineKeyboardButton(label, callback_data=f"sug:toggle:{origin}")


def suggestions_text(chat_id):
    state = "on" if suggestions_on(chat_id) else "off"
    return (
        f"Command suggestions are <b>{state}</b>.\n"
        "When off, the / menu shows only /help here, but every command still works when typed."
    )


async def suggestions_toggle(update, context):
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if chat.type == "private":
        await msg.reply_text(
            "Suggestions can be switched on or off inside a group. "
            "Here in private chat the / menu is always shown."
        )
        return
    if not await can_toggle_suggestions(chat, user.id, msg):
        await msg.reply_text(SUG_DENIED)
        return
    arg = context.args[0].lower() if context.args else ""
    if arg in ("on", "yes", "off", "no"):
        if not await apply_suggestions(
                context.bot, chat.id, arg in ("on", "yes"), langs=(user.language_code,)):
            await msg.reply_text("Couldn't update that here - check my permissions.")
            return
    sent = await msg.reply_html(
        suggestions_text(chat.id),
        reply_markup=InlineKeyboardMarkup([[suggestions_button(chat.id, "cmd")]]),
    )
    extra.remember_menu_owner(sent, user.id)


async def suggestions_callback(update, context):
    q = update.callback_query
    chat = update.effective_chat
    if q is None or chat is None:
        return
    origin = q.data.split(":")[2] if q.data.count(":") >= 2 else "cmd"
    if chat.type == "private":
        await q.answer("Command suggestions are always on in private chat. "
                       "Use this button inside a group to switch them.", show_alert=True)
        return
    if await extra.menu_not_owner(q):
        return
    # Permission gate FIRST: regular members get the alert and nothing changes.
    if not await can_toggle_suggestions(chat, q.from_user.id):
        await q.answer(SUG_DENIED, show_alert=True)
        return
    async with _toggle_lock(chat.id):  # two admins tapping together can't flip it twice
        want = not suggestions_on(chat.id)
        ok = await apply_suggestions(context.bot, chat.id, want, langs=(q.from_user.language_code,))
    try:
        if not ok:
            await q.answer("Couldn't update that - check my permissions.", show_alert=True)
            return
        await q.answer("Command suggestions: " + ("ON" if want else "OFF"))
    except BadRequest:
        pass  # the callback query expired while Telegram was busy; the change itself succeeded
    if not ok:
        return
    try:
        if origin == "help":
            await q.edit_message_text(
                f"<b>{html.escape(extra.bot_name())}</b>\n\n{HELP_INTRO}",
                parse_mode="HTML", reply_markup=help_main_keyboard(chat, q.from_user.id),
            )
        else:
            await q.edit_message_text(
                suggestions_text(chat.id), parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup([[suggestions_button(chat.id, "cmd")]]),
            )
    except TelegramError:
        pass


PAUSE_MAX_SECS = 30 * 24 * 3600  # a timed pause can last at most 30 days
PAUSE_USAGE = ("Usage:\n"
               "1. /pause: Switch every automatic function off here until /resume.\n"
               "2. /pause 30m: Pause for a set time, then resume by itself (m, h, d, w; up to 30 days).\n"
               "3. /pause status: Show whether this group is paused.\n"
               "4. /resume: Switch everything back on.")


def pause_text(chat_id):
    state = pause_state(chat_id)
    if state == 0:
        return "▶️ Everything is running normally in this group."
    if state == -1:
        return "⏸ This group is paused until an admin sends /resume."
    return f"⏸ This group is paused. It resumes by itself in {fmt_duration(state)}, or send /resume now."


async def _pause_allowed(update) -> bool:
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if chat is None or msg is None or user is None:
        return False
    if chat.type == "private":
        await msg.reply_text("Use this command in a group.")
        return False
    if not await can_toggle_suggestions(chat, user.id, msg):  # Bot Owner, Super Admins, group admins
        await msg.reply_text("Only group admins, the Bot Owner or Moderators can use this command.")
        return False
    return True


async def pause_cmd(update, context):
    """/pause [time|status]: every automatic function off in this group (locks, flood, spam, blocklist,
    ads/promotion, NSFW protection, captcha, welcome/goodbye, filters, notes, message counting...).
    Commands and menu buttons keep working."""
    if not await _pause_allowed(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    arg = context.args[0].lower() if context.args else ""
    if arg == "status":
        await msg.reply_text(pause_text(chat.id))
        return
    secs = None
    if arg:
        secs = parse_duration(arg)
        if not secs or secs > PAUSE_MAX_SECS:
            await msg.reply_text("❌ That time isn't valid.\n\n" + PAUSE_USAGE)
            return
    try:
        set_setting(chat.id, PAUSE_KEY, int(time.time()) + secs if secs else -1)
    except Exception:
        logging.exception("Couldn't save the pause state for chat %s", chat.id)
        await msg.reply_text("⚠️ I couldn't save that right now, so nothing was changed. Please try again.")
        return
    await msg.reply_text(
        "⏸ Paused. Locks, flood and spam control, blocklist, ads/promotion and NSFW protection, captcha, "
        "welcome messages, filters and message counting are all off in this group.\n"
        + (f"I'll resume by myself in {fmt_duration(secs)}. " if secs else "")
        + "Commands still work. Send /resume to switch everything back on."
    )
    await log_action(chat, "admin", f"⏸ {update.effective_user.mention_html()} paused the bot"
                     + (f" for {fmt_duration(secs)}." if secs else "."))


async def resume_cmd(update, context):
    """/resume: switch every function back on."""
    if not await _pause_allowed(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    if not is_paused(chat.id):
        set_setting(chat.id, PAUSE_KEY, 0)  # also clears an expired timer
        await msg.reply_text("▶️ Everything is already running in this group.")
        return
    try:
        set_setting(chat.id, PAUSE_KEY, 0)
    except Exception:
        logging.exception("Couldn't clear the pause state for chat %s", chat.id)
        await msg.reply_text("⚠️ I couldn't save that right now, so nothing was changed. Please try again.")
        return
    await msg.reply_text("▶️ Resumed. Every function is back on in this group.")
    await log_action(chat, "admin", f"▶️ {update.effective_user.mention_html()} resumed the bot.")


async def pause_callback(update, context):
    """Pause / Resume buttons of the Admin menu. Permissions are re-checked on every click."""
    q = update.callback_query
    chat = getattr(q.message, "chat", None)
    if chat is None or chat.type == "private":
        await q.answer("Use this in a group.", show_alert=True)
        return
    if await extra.menu_not_owner(q):
        return
    if q.data not in ("pz:p", "pz:r"):
        await q.answer("This button is no longer valid.", show_alert=True)
        return
    if not await can_toggle_suggestions(chat, q.from_user.id):
        await q.answer("Only group admins, the Bot Owner or Moderators can do this.", show_alert=True)
        return
    pausing = q.data == "pz:p"
    if pausing == is_paused(chat.id):
        await q.answer("Already paused." if pausing else "Already running.")
        return
    try:
        set_setting(chat.id, PAUSE_KEY, -1 if pausing else 0)
    except Exception:
        logging.exception("Couldn't save the pause state for chat %s", chat.id)
        await q.answer("I couldn't save that right now, so nothing was changed.", show_alert=True)
        return
    await q.answer("Paused. Press Resume to switch everything back on." if pausing else "Resumed.", show_alert=pausing)
    try:
        await q.edit_message_text(admin_section_text(chat), parse_mode="HTML",
                                  reply_markup=help_section_keyboard("mod", chat))
    except TelegramError:
        pass
    await log_action(chat, "admin", f"{'⏸' if pausing else '▶️'} {q.from_user.mention_html()} "
                     f"{'paused' if pausing else 'resumed'} the bot.")


def power_text():
    state = power_state()
    if state == 0:
        return "🔒 Owner Power: OFF"
    if state == -1:
        return "🔓 Owner Power: ON (until you send /power off)"
    return f"🔓 Owner Power: ON ({fmt_duration(state)} left, then it switches itself off)"


POWER_USAGE = ("Usage:\n"
               "/power on: Switch Owner Power on until you switch it off.\n"
               "/power 30m: Switch it on for a set time (m, h, d, w; up to 1 year), then it turns off by itself.\n"
               "/power off: Switch it off.\n"
               "/power show: Show the current status.")


async def power_cmd(update, context):
    """/power on | off | <time> | show. Primary Bot Owner only, in a private chat only. Anyone else gets no
    reply at all (the handler isn't even matched for them; the checks below are a second lock)."""
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if not chat or not msg or not user or chat.type != "private" or user.id not in OWNER_IDS:
        return
    arg = (context.args[0].lower() if context.args else "")
    if update.effective_message.text and update.effective_message.text.lstrip("/").lower().startswith("showpower"):
        arg = "show"
    if arg in ("", "show", "status"):
        await msg.reply_text(power_text() + ("" if arg else "\n\n" + POWER_USAGE))
        return
    if arg == "on":
        value = -1
    elif arg == "off":
        value = 0
    else:
        secs = parse_duration(arg)
        if not secs or secs > POWER_MAX_SECS:
            await msg.reply_text("❌ That time isn't valid.\n\n" + POWER_USAGE)
            return
        value = int(time.time()) + secs
    try:
        set_setting(0, POWER_KEY, value)
    except Exception:
        logging.exception("Couldn't save the owner power state")
        await msg.reply_text("⚠️ I couldn't save that right now, so nothing was changed. Please try again.")
        return
    await msg.reply_text(power_text())


async def pause_gate(update, context):
    """group=-100, before every other handler: while a group is paused, ordinary messages and join/leave
    events are not processed at all. Commands still go through (so /resume works); the guards that also
    look at commands (locks, ads, NSFW) check is_paused themselves."""
    chat = update.effective_chat
    if chat is not None and is_paused(chat.id):
        raise ApplicationHandlerStop


def flood_text(chat_id):
    limit = int(get_setting(chat_id, "flood_limit", FLOOD_LIMIT))
    if not limit:
        return "off"
    secs = int(get_setting(chat_id, "flood_secs", FLOOD_WINDOW))
    mode = get_setting(chat_id, "flood_mode", "tmute:300")
    return f"{limit} messages within {secs} seconds, then {describe_mode(mode)}"


def spam_text(chat_id):
    if get_setting(chat_id, "antispam", "False") != "True":
        return "off"
    repeat = int(get_setting(chat_id, "repeat_limit", 4))
    mentions = int(get_setting(chat_id, "mention_limit", 5))
    rules_on = []
    if repeat:
        rules_on.append(f"{repeat} identical messages within {REPEAT_WINDOW}s")
    if mentions:
        rules_on.append(f"more than {mentions} mentions in one message")
    mode = get_setting(chat_id, "spam_mode", "warn")
    return f"{' or '.join(rules_on) or 'no rules enabled'}; action: {describe_mode(mode)}"


def limits_lines(chat_id):
    """Chat-specific lines for /limits."""
    limit = int(get_setting(chat_id, "warn_limit", 3))
    expiry = int(get_setting(chat_id, "warn_time", 0))
    warn_mode = describe_mode(get_setting(chat_id, "warn_mode", "ban"))
    expires = f", warnings expire after {fmt_duration(expiry)}" if expiry else ""
    return [
        f"Warnings: {limit} warns, then {warn_mode}{expires}",
        f"Antiflood: {flood_text(chat_id)}",
        f"Antispam: {spam_text(chat_id)}",
        "Blocklist action: " + describe_mode(get_setting(chat_id, "blocklist_mode", "delete")),
        f"Captcha: {captcha_text(chat_id)}",
    ]


async def flood(update, context):
    if not await admin_only(update):
        return
    await update.effective_message.reply_text(
        f"Antiflood: {flood_text(update.effective_chat.id)}\n"
        "Change with /setflood <messages> [seconds] or /setflood off. "
        "Set the action with /floodmode."
    )


async def setflood(update, context):
    """/setflood 6 5  = 6 messages within 5 seconds.  /setflood off"""
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    args = [a.lower() for a in context.args]
    if args and args[0] in ("off", "0", "no"):
        set_setting(chat_id, "flood_limit", 0)
        await msg.reply_text("Antiflood is off.")
        return
    if args and args[0].isdigit() and 2 <= int(args[0]) <= 100:
        set_setting(chat_id, "flood_limit", int(args[0]))
        if len(args) > 1 and args[1].isdigit() and 1 <= int(args[1]) <= 60:
            set_setting(chat_id, "flood_secs", int(args[1]))
        await msg.reply_text(f"Antiflood: {flood_text(chat_id)}")
        return
    await msg.reply_text("Usage: /setflood <messages 2-100> [seconds 1-60]  or  /setflood off")


async def floodmode(update, context):
    await _mode_cmd(
        update, context, "floodmode", "flood_mode", "tmute:300",
        ("warn", "mute", "tmute", "kick", "ban"), "Flood action",
    )


async def antispam(update, context):
    """/antispam on|off  - repeated messages and mass mentions."""
    if not await admin_only(update):
        return
    chat_id, msg = update.effective_chat.id, update.effective_message
    flag = _on_off(context)
    if flag is not None:
        set_setting(chat_id, "antispam", flag)
    await msg.reply_text(
        f"Antispam: {spam_text(chat_id)}\n"
        "Tune with /repeatlimit, /mentionlimit and /spammode. Toggle with /antispam on|off."
    )


async def spammode(update, context):
    await _mode_cmd(
        update, context, "spammode", "spam_mode", "warn",
        ("delete", "warn", "mute", "tmute", "kick", "ban"), "Spam action",
    )


async def repeatlimit(update, context):
    await _number_setting(
        update, context, "repeatlimit", "repeat_limit", 4, 2, 20, "identical messages"
    )


async def mentionlimit(update, context):
    await _number_setting(update, context, "mentionlimit", "mention_limit", 5, 1, 50, "mentions")


def spam_reason(msg, chat_id, user_id, text):
    """Returns (reason, message_ids_to_delete); (None, []) when the message looks fine."""
    mention_limit = int(get_setting(chat_id, "mention_limit", 5))
    if mention_limit:
        entities = list(msg.entities or []) + list(msg.caption_entities or [])
        count = sum(1 for e in entities if e.type in ("mention", "text_mention"))
        if count > mention_limit:
            return f"too many mentions ({count})", [msg.message_id]

    repeat_limit = int(get_setting(chat_id, "repeat_limit", 4))
    body = text.strip()
    if repeat_limit and len(body) >= 3:
        now = time.time()
        key = (chat_id, user_id)
        log = [e for e in repeat_log[key] if now - e[0] < REPEAT_WINDOW]
        log.append((now, body, msg.message_id))
        repeat_log[key] = log
        same = [e for e in log if e[1] == body]
        if len(same) >= repeat_limit:
            repeat_log[key] = []
            return "repeated messages", [e[2] for e in same]
    return None, []


# ---------------------------------------------------------- locks & allowlist
# Lock state lives in the settings table as lock_<name> = "1"/"0" (same as the old
# module, so existing locks keep working); the allowlist has its own table.
LOCK_DESCRIPTIONS = {
    "stickers": "stickers",
    "stickerpack": "links to sticker/emoji packs",
    "photos": "photos",
    "video": "videos",
    "videonotes": "round video messages",
    "audio": "audio files",
    "voice": "voice messages",
    "documents": "files and documents",
    "gifs": "GIFs",
    "media": "photos, videos, audio, voice, documents and GIFs",
    "polls": "polls",
    "contacts": "shared contacts",
    "locations": "shared locations and venues",
    "links": "links and URLs",
    "invitelinks": "Telegram invite links",
    "forwards": "forwarded messages",
    "commands": "bot commands (/something)",
    "inline": "messages sent through inline bots",
    "anonchannel": "messages sent as a channel",
    "cashtag": "cashtags like $BTC",
}
LOCK_TYPES = tuple(LOCK_DESCRIPTIONS)
LOCK_ALIASES = {
    "url": "links", "urls": "links", "link": "links", "sticker": "stickers",
    "stickerpacks": "stickerpack", "photo": "photos", "pictures": "photos",
    "videos": "video", "videonote": "videonotes", "document": "documents",
    "doc": "documents", "docs": "documents", "gif": "gifs", "poll": "polls",
    "contact": "contacts", "location": "locations", "forward": "forwards",
    "invite": "invitelinks", "invites": "invitelinks", "invitelink": "invitelinks",
    "command": "commands", "cashtags": "cashtag",
}
ALLOW_AWARE = {"links", "forwards", "invitelinks", "inline", "commands",
               "anonchannel", "cashtag", "stickers", "stickerpack"}
ALLOWLIST_MAX = 200
INVITE_RE = re.compile(r"(?:https?://)?(?:www\.)?(?:t|telegram)\.me/(?:\+|joinchat/)([\w-]+)"
                       r"|tg://join\?invite=([\w-]+)", re.I)
STICKER_RE = re.compile(r"(?:https?://)?(?:www\.)?(?:t|telegram)\.me/(?:addstickers|addemoji)/(\w+)", re.I)
TME_USER_RE = re.compile(r"^(?:t|telegram)\.me/(\w{4,})(?:/\d+)?$")
TME_RESERVED = {"addstickers", "addemoji", "joinchat", "share", "proxy", "socks", "setlanguage", "c"}
_lock_notice = {}  # chat_id -> time of the last "I can't delete" notice


def locked_set(chat_id):
    rows = store.settings_with_prefix(chat_id, "lock").items()
    return {k[5:] for k, v in rows if k.startswith("lock_") and v == "1"}


def load_allow(chat_id):
    return store.allow_load(chat_id)


def parse_allow_item(token):
    """Turn what an admin typed into (kind, value), or None if it isn't recognisable."""
    tok = token.strip().strip(",;")
    if not tok:
        return None
    if tok.startswith("/"):
        cmd = tok[1:].split("@")[0].lower()
        return ("command", cmd) if re.fullmatch(r"\w{1,32}", cmd) else None
    if tok.startswith("$"):
        tag = tok[1:].lower()
        return ("cashtag", tag) if re.fullmatch(r"\w{1,20}", tag) else None
    if tok.startswith("@"):
        name = tok[1:].lower()
        return ("user", name) if re.fullmatch(r"\w{3,32}", name) else None
    if re.fullmatch(r"-?\d{5,}", tok):
        return ("id", str(int(tok)))
    m = STICKER_RE.search(tok)
    if m:
        return ("stickerpack", m.group(1).lower())
    m = INVITE_RE.search(tok)
    if m:
        return ("invite", m.group(1) or m.group(2))
    n = norm_url(tok)
    m = TME_USER_RE.match(n)
    if m and m.group(1).lower() not in TME_RESERVED:
        return ("user", m.group(1).lower())
    if re.fullmatch(r"[a-z0-9.-]+\.[a-z]{2,}(?::\d+)?(?:/\S*)?", n):
        return ("url", n)
    return None


def url_allowed(url, allow):
    m = STICKER_RE.search(url)
    if m:
        return m.group(1).lower() in allow["stickerpack"]
    m = INVITE_RE.search(url)
    if m:
        return (m.group(1) or m.group(2)) in allow["invite"]
    n = norm_url(url)
    host = n.split("/", 1)[0].split(":")[0]
    m = TME_USER_RE.match(n)
    if m and m.group(1).lower() in allow["user"]:
        return True
    return any(n == e or n.startswith(e + "/") or host == e or host.endswith("." + e)
               for e in allow["url"])


def _source_allowed(obj, allow):
    """Is this chat/user/bot allowlisted by numeric ID or @username?"""
    if obj is None:
        return False
    username = (getattr(obj, "username", None) or "").lower()
    return str(obj.id) in allow["id"] or (bool(username) and username in allow["user"])


def find_violation(msg, locked, allow):
    """Name of the first active lock this message breaks, or None."""
    on = locked.__contains__
    if on("photos") and msg.photo:
        return "photos"
    if on("video") and msg.video:
        return "video"
    if on("videonotes") and msg.video_note:
        return "videonotes"
    if on("audio") and msg.audio:
        return "audio"
    if on("voice") and msg.voice:
        return "voice"
    if on("documents") and msg.document and not msg.animation:
        return "documents"
    if on("gifs") and msg.animation:
        return "gifs"
    if on("media") and (msg.photo or msg.video or msg.video_note or msg.audio
                        or msg.voice or msg.document or msg.animation):
        return "media"
    if on("polls") and msg.poll:
        return "polls"
    if on("contacts") and msg.contact:
        return "contacts"
    if on("locations") and (msg.location or msg.venue):
        return "locations"
    if on("stickers") and msg.sticker:
        if (msg.sticker.set_name or "").lower() not in allow["stickerpack"]:
            return "stickers"
    if on("forwards") and msg.forward_origin:
        o = msg.forward_origin
        if not any(_source_allowed(getattr(o, a, None), allow) for a in ("chat", "sender_chat", "sender_user")):
            return "forwards"
    if on("inline") and msg.via_bot and not _source_allowed(msg.via_bot, allow):
        return "inline"
    sender = msg.sender_chat
    if (on("anonchannel") and sender is not None and sender.id != msg.chat.id
            and not msg.is_automatic_forward and not _source_allowed(sender, allow)):
        return "anonchannel"

    if locked & {"links", "invitelinks", "stickerpack"}:
        urls = [e.url if e.type == "text_link" else t
                for e, t in _entity_items(msg, ["url", "text_link"]).items()
                if (e.url if e.type == "text_link" else t)]
        haystack = " ".join([msg.text or msg.caption or ""] + urls)
        if on("invitelinks"):
            for m in INVITE_RE.finditer(haystack):
                if (m.group(1) or m.group(2)) not in allow["invite"]:
                    return "invitelinks"
        if on("stickerpack"):
            for m in STICKER_RE.finditer(haystack):
                if m.group(1).lower() not in allow["stickerpack"]:
                    return "stickerpack"
        if on("links") and any(not url_allowed(u, allow) for u in urls):
            return "links"
    if on("commands"):
        for _, text in _entity_items(msg, ["bot_command"]).items():
            if text.lstrip("/").split("@")[0].lower() not in allow["command"]:
                return "commands"
    if on("cashtag"):
        for _, text in _entity_items(msg, ["cashtag"]).items():
            if text.lstrip("$").lower() not in allow["cashtag"]:
                return "cashtag"
    return None


async def lock_exempt(chat, msg, user, bot_id):
    """Admins, the owner, genuine anonymous admins, approved users and Telegram's own
    forwards are never touched by locks."""
    if msg.is_automatic_forward or user.id in (777000, bot_id) or is_bot_owner(user.id):
        return True
    if msg.sender_chat is not None:
        # sender_chat == this chat is a real anonymous admin; any other channel is not exempt
        return msg.sender_chat.id == chat.id
    if await is_admin(chat, user.id):  # 'creator' and 'administrator'
        return True
    return is_approved(chat.id, user.id)


# Telegram service messages (someone changes a member tag, the group name/photo/settings, ...) carry no text and no
# media. The library may not know the newest kinds, so they can't be told apart by type: a message with no content at
# all is a service message. It must never count as flooding, spam or a locked item.
_CONTENT_ATTRS = ("text", "caption", "photo", "video", "audio", "voice", "document", "sticker", "animation",
                  "video_note", "contact", "location", "venue", "poll", "dice", "game", "story", "invoice",
                  "paid_media", "checklist")


def is_service_message(msg):
    return not any(getattr(msg, attr, None) for attr in _CONTENT_ATTRS)


async def lock_guard(update, context):
    """Runs before every other handler (group -2): deletes a locked item sent by a
    non-admin, optionally warns, and stops the update so nothing else acts on it."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user or chat.type == "private":
        return
    if is_service_message(msg):
        return  # group-setting / member-tag changes are not messages to police
    if is_paused(chat.id):
        return  # /pause: every function is off in this group
    locked = locked_set(chat.id)
    if not locked:
        return  # fast path: no locks, no Telegram calls
    allow = load_allow(chat.id) if locked & ALLOW_AWARE else defaultdict(set)
    lock_name = find_violation(msg, locked, allow)
    if not lock_name or await lock_exempt(chat, msg, user, context.bot.id):
        return
    try:
        await msg.delete()
    except TelegramError as e:
        logging.warning("Lock '%s': couldn't delete in chat %s: %s: %s", lock_name, chat.id, type(e).__name__, e)
        if time.time() - _lock_notice.get(chat.id, 0) > 600:
            _lock_notice[chat.id] = time.time()
            bot_rights.pop(chat.id, None)
            try:
                await chat.send_message("⚠️ A locked item was sent but I couldn't delete it. "
                                        "Please give me the 'Delete messages' admin right.")
            except TelegramError:
                pass
        return
    mention = user.mention_html()
    await log_action(chat, "lock", f"🔒 Deleted a locked ({lock_name}) message from {mention}.")
    if get_setting(chat.id, "lockwarns", "False") == "True" and msg.sender_chat is None:
        await announce(chat, await add_warn(chat, user.id, mention, f"sent a locked item ({lock_name})"), user.id)
    raise ApplicationHandlerStop


def _lock_names(args):
    """Split typed names into (valid, unknown), resolving aliases, keeping order."""
    good, bad = [], []
    for arg in args:
        name = LOCK_ALIASES.get(arg.lower(), arg.lower())
        target = good if name in LOCK_TYPES else bad
        if name not in target and (target is good or arg not in bad):
            target.append(name if target is good else arg)
    return good, bad


async def _lock_change(update, context, value):
    if not await group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    verb = "lock" if value else "unlock"
    good, bad = _lock_names(context.args)
    if not good:
        extra = f"\nUnknown: {', '.join(bad)}" if bad else ""
        await msg.reply_text(f"Usage: /{verb} <item> [item ...]\nSee /locktypes for every item.{extra}")
        return
    for name in good:
        set_setting(chat.id, f"lock_{name}", "1" if value else "0")
    lines = [f"{'🔒 Locked' if value else '🔓 Unlocked'}: {', '.join(good)}"]
    if bad:
        lines.append(f"Unknown (see /locktypes): {', '.join(bad)}")
    if value:
        rights = await get_bot_rights(chat, context.bot)
        if not (rights and rights["can_delete"]):
            lines.append("⚠️ I need the 'Delete messages' admin right to enforce locks.")
    await msg.reply_text("\n".join(lines))


async def lock(update, context):
    await _lock_change(update, context, True)


async def unlock(update, context):
    await _lock_change(update, context, False)


async def locks_cmd(update, context):
    if not await group_only(update):
        return
    chat = update.effective_chat
    active = [t for t in LOCK_TYPES if t in locked_set(chat.id)]
    warns = "on" if get_setting(chat.id, "lockwarns", "False") == "True" else "off"
    head = f"🔒 Locked: {', '.join(active)}" if active else "No locks are active in this chat."
    await update.effective_message.reply_text(f"{head}\nLock warnings: {warns}")


async def lockwarns(update, context):
    if not await group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    flag = parse_yes_no(context.args)
    if flag is None:
        on = get_setting(chat.id, "lockwarns", "False") == "True"
        await msg.reply_text(f"Lock warnings are {'on' if on else 'off'}.\nUse /lockwarns yes or /lockwarns no.")
        return
    set_setting(chat.id, "lockwarns", "True" if flag else "False")
    await msg.reply_text("✅ Sending a locked item now gives a warning." if flag
                         else "✅ Locked items are deleted without a warning.")


async def locktypes(update, context):
    if not await admin_only(update):
        return
    lines = [f"<code>{name}</code>: {desc}" for name, desc in LOCK_DESCRIPTIONS.items()]
    await update.effective_message.reply_html(
        "<b>Lockable items</b>\n" + "\n".join(lines) + "\n\nUse /lock item1 item2 ... to lock them."
    )


ALLOW_LABELS = (("url", "Links"), ("id", "IDs"), ("user", "Users, channels and bots"),
                ("command", "Commands"), ("cashtag", "Cashtags"),
                ("stickerpack", "Sticker packs"), ("invite", "Invite links"))


async def allowlist_cmd(update, context):
    if not await group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    tokens = [t for a in context.args for t in a.split(",") if t.strip()]
    if not tokens:
        allow = load_allow(chat.id)
        if not any(allow.values()):
            await msg.reply_text("The allowlist is empty. Add items with /allowlist <url|id|command|@name|$cashtag>.")
            return
        lines = [f"<b>{label}</b>: " + ", ".join(f"<code>{html.escape(_show_allow(k, v))}</code>"
                                                   for v in sorted(allow[k]))
                 for k, label in ALLOW_LABELS if allow[k]]
        await msg.reply_html("<b>Allowlisted items</b>\n" + "\n".join(lines))
        return
    total = store.allow_count(chat.id)
    added, bad, full = [], [], False
    for tok in tokens:
        item = parse_allow_item(tok)
        if not item:
            bad.append(tok)
            continue
        if total >= ALLOWLIST_MAX:
            full = True
            break
        if store.allow_add(chat.id, *item):
            total += 1
        added.append(_show_allow(*item))
    lines = []
    if added:
        lines.append("✅ Allowlisted: " + ", ".join(added))
    if bad:
        lines.append("❌ Couldn't understand: " + ", ".join(bad))
    if full:
        lines.append(f"❌ The allowlist is full ({ALLOWLIST_MAX} items).")
    await msg.reply_text("\n".join(lines))


async def rmallowlist(update, context):
    if not await group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    tokens = [t for a in context.args for t in a.split(",") if t.strip()]
    if not tokens:
        await msg.reply_text("Usage: /rmallowlist <url|id|command|@name|$cashtag> [more ...]")
        return
    removed, missing = [], []
    for tok in tokens:
        item = parse_allow_item(tok)
        if item and store.allow_remove(chat.id, *item):
            removed.append(_show_allow(*item))
        else:
            missing.append(tok)
    lines = []
    if removed:
        lines.append("✅ Removed: " + ", ".join(removed))
    if missing:
        lines.append("❌ Not on the allowlist: " + ", ".join(missing))
    await msg.reply_text("\n".join(lines))


async def rmallowlistall(update, context):
    if not await group_only(update):
        return
    chat = update.effective_chat
    n = store.allow_clear(chat.id)
    await update.effective_message.reply_text(f"✅ Allowlist cleared ({n} items removed).")


# ---------------------------------------------------- general message watcher
async def watcher(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user or chat.type == "private":
        return
    if is_service_message(msg):
        return  # group-setting / member-tag changes must never count as flooding or spam
    if msg.forward_origin and await check_setlog_forward(update, context):
        return
    text = (msg.text or msg.caption or "").lower()
    mention = user.mention_html()

    # (locks are enforced earlier, in lock_guard)

    # "@admin" in a reply reports it, same as /report
    if msg.reply_to_message and re.search(r"(?<!\w)@admin\b", text):
        await file_report(update, context)
        return

    # antiflood (per-chat limit/window/action; a limit of 0 means off)
    limit = int(get_setting(chat.id, "flood_limit", FLOOD_LIMIT))
    if limit:
        window = int(get_setting(chat.id, "flood_secs", FLOOD_WINDOW))
        now = time.time()
        key = (chat.id, user.id)
        flood_log[key] = [t for t in flood_log[key] if now - t < window] + [now]
        if len(flood_log[key]) >= limit:
            flood_log[key].clear()
            if not await is_admin(chat, user.id) and not is_approved(chat.id, user.id):
                await try_delete(msg)
                mode = get_setting(chat.id, "flood_mode", "tmute:300")
                await announce(chat, await enforce(chat, user.id, mention, mode, "flooding", "flood"), user.id)
                return

    # antispam: repeated messages, mass mentions
    if get_setting(chat.id, "antispam", "False") == "True":
        reason, ids = spam_reason(msg, chat.id, user.id, text)
        if reason and not await is_admin(chat, user.id) and not is_approved(chat.id, user.id):
            try:
                await chat.delete_messages(ids)
            except TelegramError as e:
                logging.warning("Couldn't delete spam: %s", e)
            mode = get_setting(chat.id, "spam_mode", "warn")
            await announce(chat, await enforce(chat, user.id, mention, mode, reason, "spam"), user.id)
            return

    if not text:
        return

    # blocklist (admins are exempt)
    words = store.block_words(chat.id)
    hit = next((w for w in words if word_match(w, text)), None)
    if hit and not await is_admin(chat, user.id) and not is_approved(chat.id, user.id):
        mode = get_setting(chat.id, "blocklist_mode", "delete")
        if mode != "nothing":
            await try_delete(msg)
            await announce(
                chat,
                await enforce(chat, user.id, mention, mode, f"blocklisted word '{hit}'", "blocklist"),
                user.id,
            )
        return

    # #note shortcut
    if text.startswith("#"):
        name = text[1:].split()[0]
        content = store.note_get(chat.id, name)
        if content is not None:
            await reply_rendered(update, content)
            return

    # keyword filters
    for keyword, reply in store.filter_rows(chat.id):
        if word_match(keyword, text):
            await reply_rendered(update, reply)
            break


# ------------------------------------------------------------------- misc
async def pin(update, context):
    if not await admin_only(update):
        return
    reply = update.effective_message.reply_to_message
    if reply:
        await reply.pin()
    else:
        await update.effective_message.reply_text("Reply to the message you want pinned.")


# ------------------------------------------------------------ purge module
# One implementation of /purge, /purge X, /spurge, /del, /purgefrom, /purgeto.
PURGE_BATCH = 100         # Telegram's deleteMessages limit per call
PURGE_BATCH_DELAY = 0.4   # seconds between batches (gentle throttling)
PURGE_NOTICE_TTL = 5      # seconds temporary notices stay visible
PURGE_START_TTL = 600     # /purgefrom start point lives 10 minutes
PURGE_RETRY_LIMIT = 5     # flood-wait retries per batch

PURGE_ERR = {
    "no_reply": "❌ Please reply to a message to use this command.",
    "no_start": "❌ No purge start point found. Use /purgefrom first.",
    "expired": "❌ The purge start point has expired. Use /purgefrom again.",
    "user_perm": "❌ You need administrator permission to delete messages.",
    "bot_perm": "❌ I don't have permission to delete messages in this chat.",
    "bad_number": "❌ Invalid number. Use a positive whole number, for example: /purge 10",
    "group_only": "❌ Purge commands only work inside a group.",
}

# {(chat_id, user_id): {"message_id": int, "created_at": float}}; per chat AND per admin.
purge_state = {}
_purge_locks = {}         # one running purge per chat
_purge_tasks = set()      # keeps temp-notice tasks alive until they finish


def purge_clear_legacy_state():
    """Drop the old module's saved 'purgefrom' rows from the settings table."""
    try:
        store.del_setting_everywhere("purgefrom")
    except store.DBError as e:
        logging.warning("Couldn't clear legacy purge state: %s", e)


def _purge_sweep():
    """Forget start points older than the timeout."""
    now = time.time()
    for key in [k for k, v in purge_state.items() if now - v["created_at"] > PURGE_START_TTL]:
        purge_state.pop(key, None)


async def _purge_temp_notice(chat, text):
    """Send a notice and delete it after PURGE_NOTICE_TTL seconds without blocking."""
    try:
        note = await chat.send_message(text)
    except TelegramError as e:
        logging.warning("Purge notice failed in chat %s: %s", chat.id, e)
        return

    async def _later():
        await asyncio.sleep(PURGE_NOTICE_TTL)
        try:
            await note.delete()
        except TelegramError:
            pass  # already gone

    task = asyncio.create_task(_later())
    _purge_tasks.add(task)
    task.add_done_callback(_purge_tasks.discard)


def _real_reply(msg):
    """The message being replied to, or None. Checked on its own, never on message age.
    In forum groups Telegram attaches the topic's first message to every plain message in
    the topic; that is not a reply the user chose, so it doesn't count."""
    r = msg.reply_to_message
    if r is None:
        return None
    thread = getattr(msg, "message_thread_id", None)
    if getattr(msg, "is_topic_message", False) and thread is not None and r.message_id == thread:
        return None
    return r


def _purge_failure_text(deleted, failed, reasons):
    """Professional notice for messages Telegram refused to delete. The reasons are the real
    API error descriptions Telegram returned - nothing is assumed about time limits."""
    detail = "; ".join(sorted(reasons)[:3])[:300] if reasons else "no details were returned"
    head = (f"⚠️ {failed} message{'s' if failed != 1 else ''} could not be deleted."
            if deleted == 0 else
            f"⚠️ Purge completed with exceptions: {deleted} processed, {failed} could not be deleted.")
    return (
        f"{head}\n"
        "Some messages could not be deleted because of Telegram's deletion restrictions or a "
        "specific Telegram API limitation. All other eligible messages were processed normally.\n"
        f"Telegram API response: {detail}"
    )


async def _purge_checks(update, context, need_reply=True):
    """Shared gate for every purge command. Returns True if the command may run."""
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if chat.type == "private":
        await msg.reply_text(PURGE_ERR["group_only"])
        return False
    anonymous_admin = msg.sender_chat is not None and msg.sender_chat.id == chat.id
    # Bot Owner and Bot Moderators (Super Admins) may purge in any group.
    privileged = is_bot_owner(user.id) or is_super_admin(user.id)
    if not anonymous_admin and not privileged:
        try:
            member = await chat.get_member(user.id)
        except TelegramError:
            member = None
        allowed = member is not None and (
            member.status == ChatMemberStatus.OWNER
            or (member.status == ChatMemberStatus.ADMINISTRATOR
                and getattr(member, "can_delete_messages", False))
        )
        if not allowed:
            await msg.reply_text(PURGE_ERR["user_perm"])
            return False
    rights = await get_bot_rights(chat, context.bot)
    if not (rights and rights["can_delete"]):
        await msg.reply_text(PURGE_ERR["bot_perm"])
        return False
    if need_reply:
        if _real_reply(msg) is None:
            await msg.reply_text(PURGE_ERR["no_reply"])
            return False
    return True


async def _delete_one(bot, chat_id, mid, stats):
    """Delete a single message; update stats. Returns False if we must stop."""
    reasons = stats.setdefault("reasons", set())
    for _ in range(PURGE_RETRY_LIMIT):
        try:
            await bot.delete_message(chat_id, mid)
            stats["deleted"] += 1
            return True
        except RetryAfter as e:
            await asyncio.sleep(_retry_seconds(e))
        except Forbidden:
            stats["no_perm"] = True
            return False
        except BadRequest as e:
            text = str(e).lower()
            if "not enough rights" in text or "need to be admin" in text:
                stats["no_perm"] = True
                return False
            if "not found" in text or "message_id_invalid" in text:
                return True  # already gone: nothing to delete, not a failure
            stats["failed"] += 1
            reasons.add(str(e)[:120])  # Telegram's own explanation
            return True
        except TelegramError as e:
            logging.warning("Purge: delete of %s failed: %s", mid, e)
            stats["failed"] += 1
            reasons.add(f"{type(e).__name__}: {str(e)[:100]}")
            return True
    stats["failed"] += 1
    reasons.add("Telegram rate limit (flood wait) kept being returned")
    return True


async def _purge_delete(chat, bot, first_id, last_id, extra_ids=()):
    """Delete message IDs first_id..last_id (plus extra_ids) in batches of 100, generated
    on the fly so a huge range never builds one giant list. A failing batch is retried
    message by message; flood waits are honoured; processing continues after any failure.
    Returns stats: deleted / failed / reasons (Telegram's error texts) / no_perm."""
    stats = {"deleted": 0, "failed": 0, "reasons": set(), "no_perm": False}
    lock = _purge_locks.setdefault(chat.id, asyncio.Lock())

    def batches():
        for i in range(first_id, last_id + 1, PURGE_BATCH):
            yield list(range(i, min(i + PURGE_BATCH, last_id + 1)))
        extra = [m for m in extra_ids if not first_id <= m <= last_id]
        if extra:
            yield extra

    async with lock:
        for batch in batches():
            done = False
            for _ in range(PURGE_RETRY_LIMIT):
                try:
                    await bot.delete_messages(chat.id, batch)
                    stats["deleted"] += len(batch)
                    done = True
                    break
                except RetryAfter as e:
                    await asyncio.sleep(_retry_seconds(e))
                except Forbidden:
                    stats["no_perm"] = True
                    return stats
                except BadRequest as e:
                    text = str(e).lower()
                    if "not enough rights" in text or "need to be admin" in text:
                        stats["no_perm"] = True
                        return stats
                    # The batch call was rejected as a whole; go one by one so we
                    # can count exactly what worked and what didn't.
                    for mid in batch:
                        if not await _delete_one(bot, chat.id, mid, stats):
                            return stats
                    done = True
                    break
                except TelegramError as e:  # network / API trouble: skip this batch, keep going
                    logging.warning("Purge batch failed in chat %s: %s", chat.id, e)
                    stats["reasons"].add(f"{type(e).__name__}: {str(e)[:100]}")
                    break
            if not done:
                stats["failed"] += len(batch)
                logging.warning("Purge gave up on a batch in chat %s", chat.id)
            await asyncio.sleep(PURGE_BATCH_DELAY)
    return stats


async def _purge_range(update, context, first_id, last_id, cmd, silent=False):
    """Delete first_id..last_id plus the command message, then report."""
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    first_id, last_id = min(first_id, last_id), max(first_id, last_id)
    # The command message always goes too (it is the newest message the bot can know about).
    stats = await _purge_delete(chat, context.bot, first_id, last_id, (msg.message_id,))
    d, f = stats["deleted"], stats["failed"]
    logging.info("purge chat=%s actor=%s cmd=%s range=%s-%s deleted=%s failed=%s reasons=%s ts=%s",
                 chat.id, user.id, cmd, first_id, last_id, d, f, sorted(stats["reasons"]), int(time.time()))
    await log_action(chat, "purge", f"🧹 {user.mention_html()} used /{cmd}: deleted {d} messages; {f} failed.")
    if stats["no_perm"]:
        await chat.send_message(PURGE_ERR["bot_perm"])
        return
    if f:  # failures are always reported, even for the silent /spurge
        try:
            await chat.send_message(_purge_failure_text(d, f, stats["reasons"]))
        except TelegramError as e:
            logging.warning("Purge failure notice failed in chat %s: %s", chat.id, e)
        return
    if silent:
        return
    else:
        await _purge_temp_notice(chat, f"✅ Purged {d} messages.")


async def purge(update, context, silent=False):
    """/purge and /purge X: reply target (+ next X messages) and the command."""
    if not await _purge_checks(update, context):
        return
    msg = update.effective_message
    cmd = "spurge" if silent else "purge"
    start_id = _real_reply(msg).message_id
    end_id = msg.message_id
    if context.args:
        if len(context.args) != 1 or not re.fullmatch(r"[0-9]+", context.args[0]) or int(context.args[0]) < 1:
            await msg.reply_text(PURGE_ERR["bad_number"])
            return
        end_id = min(start_id + int(context.args[0]), msg.message_id)
    await _purge_range(update, context, start_id, end_id, cmd, silent)


async def spurge(update, context):
    await purge(update, context, silent=True)


async def del_cmd(update, context):
    """/del: delete the replied-to message and the command."""
    if not await _purge_checks(update, context):
        return
    msg, chat = update.effective_message, update.effective_chat
    stats = {"deleted": 0, "failed": 0, "reasons": set(), "no_perm": False}
    await _delete_one(context.bot, chat.id, _real_reply(msg).message_id, stats)
    await _delete_one(context.bot, chat.id, msg.message_id,
                      {"deleted": 0, "failed": 0, "reasons": set(), "no_perm": False})
    if stats["no_perm"]:
        await chat.send_message(PURGE_ERR["bot_perm"])
    elif stats["failed"]:
        await chat.send_message(_purge_failure_text(0, stats["failed"], stats["reasons"]))


async def purgefrom(update, context):
    """/purgefrom: remember the replied-to message as the range start."""
    if not await _purge_checks(update, context):
        return
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    _purge_sweep()
    purge_state[(chat.id, user.id)] = {
        "message_id": _real_reply(msg).message_id,
        "created_at": time.time(),
    }
    await _purge_temp_notice(chat, "✅ Purge start point saved.")


async def purgeto(update, context):
    """/purgeto: delete from the saved start point to the replied-to message."""
    if not await _purge_checks(update, context):
        return
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    key = (chat.id, user.id)
    state = purge_state.get(key)
    if state is None:
        await msg.reply_text(PURGE_ERR["no_start"])
        return
    if time.time() - state["created_at"] > PURGE_START_TTL:
        purge_state.pop(key, None)
        await msg.reply_text(PURGE_ERR["expired"])
        return
    purge_state.pop(key, None)  # clear right away so nothing stale is left behind
    await _purge_range(update, context, state["message_id"], _real_reply(msg).message_id, "purgeto")


# ------------------------------------------------- super admin management
ERR_SA_DENIED = "⚠️ Access Denied: Only the Primary Bot Owner can manage Super Admins."
ERR_SA_INVALID = (
    "⚠️ Invalid user. Please give a numeric User ID or an @username, "
    "or reply to the user's message with the command."
)
ERR_SA_NOT_FOUND = (
    "⚠️ I couldn't find that username. Please use their numeric User ID, "
    "or reply to one of their messages."
)


def super_admin_rows():
    return store.sa_rows()


def is_super_admin(user_id) -> bool:
    return store.is_super_admin(user_id)


def owner_setup_hint(user_id):
    return (
        "⚠️ No Primary Bot Owner is set up yet. Set the OWNER_IDS environment variable "
        f"to your Telegram ID (your ID is {user_id}), then restart the bot."
    )


async def owner_only(update) -> bool:
    user = update.effective_user
    if user and user.id in OWNER_IDS:
        return True
    await update.effective_message.reply_text(
        ERR_SA_DENIED if OWNER_IDS else owner_setup_hint(user.id)
    )
    return False


async def resolve_admin_target(update, context):
    """Returns (user_id, username, error) from a reply, a text mention, a numeric ID
    or an @username."""
    msg = update.effective_message
    reply = msg.reply_to_message
    if reply and reply.from_user:
        u = reply.from_user
        if u.is_bot:
            return None, None, "⚠️ Bots can't be Super Admins."
        return u.id, u.username, None
    for ent in msg.entities or []:
        if ent.type == "text_mention" and ent.user:
            return ent.user.id, ent.user.username, None
    if not context.args:
        return None, None, ERR_SA_INVALID
    arg = context.args[0].strip()
    if arg.isdigit() and int(arg) > 0:
        uid, username = int(arg), None
        try:  # best effort: only works if the user has talked to the bot before
            username = (await context.bot.get_chat(uid)).username
        except TelegramError:
            pass
        return uid, username, None
    if re.fullmatch(r"@[A-Za-z][A-Za-z0-9_]{4,31}", arg):
        try:
            found = await context.bot.get_chat(arg)
        except TelegramError:
            return None, None, ERR_SA_NOT_FOUND
        if found.type != "private":
            return None, None, ERR_SA_INVALID
        return found.id, found.username, None
    return None, None, ERR_SA_INVALID


async def addadmin_cmd(update, context):
    msg = update.effective_message
    if not await owner_only(update):
        return
    uid, username, err = await resolve_admin_target(update, context)
    if err:
        await msg.reply_text(err)
        return
    if uid in OWNER_IDS:
        await msg.reply_text("ℹ️ That user is the Primary Bot Owner and already has full access.")
        return
    if is_super_admin(uid):
        await msg.reply_text("⚠️ User is already a Super Admin.")
        return
    store.sa_add(uid, username, update.effective_user.id, int(time.time()))
    await msg.reply_html(f"✅ User {sa_label(uid, username)} has been added as a Super Admin.")


async def removeadmin_cmd(update, context):
    msg = update.effective_message
    if not await owner_only(update):
        return
    uid, username, err = await resolve_admin_target(update, context)
    if err:
        await msg.reply_text(err)
        return
    if uid in OWNER_IDS:
        await msg.reply_text("⚠️ The Primary Bot Owner can't be removed.")
        return
    if not is_super_admin(uid):
        await msg.reply_text("⚠️ User is not a Super Admin.")
        return
    stored = store.sa_remove(uid)
    await msg.reply_html(
        f"✅ User {sa_label(uid, username or stored)} "
        "has been removed from Super Admins."
    )


async def adminlist_cmd(update, context):
    msg = update.effective_message
    if not await owner_only(update):
        return
    rows = super_admin_rows()
    if not rows:
        await msg.reply_text("ℹ️ No Super Admins have been added yet.")
        return
    lines = []
    for i, (uid, username) in enumerate(rows, 1):
        if not username:  # refresh a missing username if Telegram can tell us
            try:
                username = (await context.bot.get_chat(uid)).username
            except TelegramError:
                username = None
            if username:
                store.sa_set_username(uid, username)
        who = f"@{html.escape(username)}" if username else "no username"
        lines.append(f"{i}. <code>{uid}</code> - {who}")
    await msg.reply_html(f"<b>🛡 Super Admins ({len(rows)})</b>\n\n" + "\n".join(lines))


# ------------------------------------------- help-menu editors (group / bot)
SESSION_TIMEOUT = 180  # seconds of inactivity before an edit session is cleared
MAX_FILE_BYTES = 10 * 1024 * 1024  # largest image accepted for a profile photo

AWAITING_GROUP_NAME = "AWAITING_GROUP_NAME"
AWAITING_GROUP_USERNAME = "AWAITING_GROUP_USERNAME"
AWAITING_GROUP_PHOTO = "AWAITING_GROUP_PHOTO"
AWAITING_GROUP_BIO = "AWAITING_GROUP_BIO"
AWAITING_BOT_NAME = "AWAITING_BOT_NAME"
AWAITING_BOT_USERNAME = "AWAITING_BOT_USERNAME"
AWAITING_BOT_PHOTO = "AWAITING_BOT_PHOTO"
AWAITING_BOT_BIO = "AWAITING_BOT_BIO"

# (chat_id, user_id) -> {"state", "kind", "ts", "task"}
edit_sessions = {}

EDIT_PREFIX = {"group": "gedit", "bot": "bedit"}
EDIT_KIND = {"gedit": "group", "bedit": "bot"}
EDIT_HELP_KEYS = {"groupedit": "group", "botedit": "bot"}

EDIT_ACTIONS = {
    # (kind, action): (state, prompt)
    ("group", "name"): (
        AWAITING_GROUP_NAME,
        "Please send the new display name you wish to apply to the group.",
    ),
    ("group", "username"): (
        AWAITING_GROUP_USERNAME,
        "Please send the new username you would like to set for the group. "
        "(Note: You do not need to include @; it will be added automatically).",
    ),
    ("group", "photo"): (
        AWAITING_GROUP_PHOTO,
        "Please upload the new profile photo you would like to set for the group.",
    ),
    ("group", "bio"): (
        AWAITING_GROUP_BIO,
        "Please send the new bio or description you would like to set for the group.",
    ),
    ("bot", "name"): (
        AWAITING_BOT_NAME,
        "Please send the new display name you wish to apply to the bot.",
    ),
    ("bot", "username"): (
        AWAITING_BOT_USERNAME,
        "Please send the new username you would like to set for the bot. "
        "(Note: You do not need to include @; it will be added automatically).",
    ),
    ("bot", "photo"): (
        AWAITING_BOT_PHOTO,
        "Please upload the new profile photo you would like to set for the bot.",
    ),
    ("bot", "bio"): (
        AWAITING_BOT_BIO,
        "Please send the new bio or description you would like to set for the bot.",
    ),
}

ERR_GROUP_DENIED = (
    "⚠️ Access Denied: You need the 'Change Group Info' admin permission to use this command."
)
ERR_BOT_DENIED = "⚠️ Access Denied: Only the Bot Owner can manage or edit bot settings."
ERR_USERNAME_CHARS = (
    "⚠️ Invalid Username: Spaces and special characters are not allowed. "
    "Only letters, numbers, and underscores (_) can be used."
)
ERR_USERNAME_SHORT = "⚠️ Invalid Username: Username must be at least 5 characters long."
ERR_USERNAME_LONG = "⚠️ Invalid Username: Username cannot exceed 32 characters."
ERR_USERNAME_BOT = (
    "⚠️ Invalid Bot Username: Telegram bot usernames must end with 'bot' (e.g., my_custom_bot)."
)
ERR_USERNAME_TAKEN = "This username is already taken. Please try something else."
MSG_TIMEOUT = "Session timed out. Please try again."
MSG_CANCELLED = "Process cancelled."


def edit_menu_keyboard(kind):
    p, label = EDIT_PREFIX[kind], kind.capitalize()
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(f"✏️ Change {label} Name", callback_data=f"{p}:name")],
        [InlineKeyboardButton(
            f"🏷️ Change {label} Username" + (" / Handle" if kind == "bot" else ""),
            callback_data=f"{p}:username")],
        [InlineKeyboardButton(
            f"🖼️ Change {label} " + ("Profile Photo" if kind == "bot" else "Photo"),
            callback_data=f"{p}:photo")],
        [InlineKeyboardButton(f"📝 Change {label} Bio / Description", callback_data=f"{p}:bio")],
        [InlineKeyboardButton("🔙 Back", callback_data="help:main")],
    ])


def edit_menu_text(kind):
    if kind == "group":
        return "<b>👥 Group Edit</b>\n\nWhat would you like to change about this group?"
    return "<b>🤖 Bot Edit</b>\n\nWhat would you like to change about the bot's profile?"


def cancel_keyboard(kind):
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("✖ Cancel", callback_data=f"{EDIT_PREFIX[kind]}:cancel")
    ]])


async def edit_perm_error(kind, chat, user_id):
    """Returns an error message if this user may not use the editor, else None."""
    if kind == "bot":
        # Bot settings: ONLY the configured Bot Owner (never group roles or Super Admins).
        if user_id in OWNER_IDS:
            return None
        return ERR_BOT_DENIED if OWNER_IDS else owner_setup_hint(user_id)
    if chat.type == "private":
        return "⚠️ Group editing only works inside a group. Use /groupedit or /help there."
    if is_bot_owner(user_id):
        return None  # owner power ON
    try:
        member = await chat.get_member(user_id)
    except TelegramError:
        return ERR_GROUP_DENIED
    if member.status == ChatMemberStatus.OWNER:
        return None
    if member.status == ChatMemberStatus.ADMINISTRATOR and getattr(member, "can_change_info", False):
        return None
    return ERR_GROUP_DENIED


# ---- sessions (state + inactivity timeout)
def end_session(key):
    s = edit_sessions.pop(key, None)
    if s and s.get("task"):
        s["task"].cancel()


async def _session_watchdog(bot, key, session):
    try:
        while edit_sessions.get(key) is session:
            remaining = session["ts"] + SESSION_TIMEOUT - time.time()
            if remaining > 0:
                await asyncio.sleep(remaining)
                continue
            edit_sessions.pop(key, None)
            try:
                await bot.send_message(key[0], MSG_TIMEOUT)
            except TelegramError:
                pass
            return
    except asyncio.CancelledError:
        pass


def start_session(bot, key, kind, state):
    end_session(key)
    session = {"state": state, "kind": kind, "ts": time.time(), "task": None}
    edit_sessions[key] = session
    session["task"] = asyncio.create_task(_session_watchdog(bot, key, session))


# ---- menus
async def open_edit_menu(update, context, kind):
    q = update.callback_query
    err = await edit_perm_error(kind, update.effective_chat, q.from_user.id)
    if err:
        await q.answer(err, show_alert=True)
        return
    await q.answer()
    try:
        await q.edit_message_text(
            edit_menu_text(kind), parse_mode="HTML", reply_markup=edit_menu_keyboard(kind)
        )
    except TelegramError:
        pass


async def _edit_command(update, kind):
    chat, user, msg = update.effective_chat, update.effective_user, update.effective_message
    err = await edit_perm_error(kind, chat, user.id)
    if err:
        await msg.reply_text(err)
        return
    sent = await msg.reply_html(edit_menu_text(kind), reply_markup=edit_menu_keyboard(kind))
    extra.remember_menu_owner(sent, user.id)


async def groupedit_cmd(update, context):
    await _edit_command(update, "group")


async def bot_cmd(update, context):
    await _edit_command(update, "bot")


async def edit_callback(update, context):
    q = update.callback_query
    prefix, _, action = q.data.partition(":")
    kind = EDIT_KIND.get(prefix)
    chat, user = update.effective_chat, q.from_user
    if not kind:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    err = await edit_perm_error(kind, chat, user.id)
    if err:
        await q.answer(err, show_alert=True)
        return
    await q.answer()
    key = (chat.id, user.id)

    if action == "cancel":
        end_session(key)
        await q.edit_message_text(MSG_CANCELLED)
        return
    if action == "menu":
        end_session(key)
        await q.edit_message_text(
            edit_menu_text(kind), parse_mode="HTML", reply_markup=edit_menu_keyboard(kind)
        )
        return
    if (kind, action) not in EDIT_ACTIONS:
        return
    state, prompt = EDIT_ACTIONS[(kind, action)]
    start_session(context.bot, key, kind, state)
    await q.edit_message_text(prompt, reply_markup=cancel_keyboard(kind))


async def cancel_cmd(update, context):
    chat, user = update.effective_chat, update.effective_user
    if chat and user:
        end_session((chat.id, user.id))
    await update.effective_message.reply_text(MSG_CANCELLED)


# ---- validation helpers
def check_username(raw, is_bot):
    """Returns (name_without_at, error). '@' is added automatically if missing."""
    name = (raw or "").strip()
    if name.startswith("@"):
        name = name[1:]
    if not name or not re.fullmatch(r"[A-Za-z0-9_]+", name):
        return None, ERR_USERNAME_CHARS
    if len(name) < 5:
        return None, ERR_USERNAME_SHORT
    if len(name) > 32:
        return None, ERR_USERNAME_LONG
    if is_bot and not name.lower().endswith("bot"):
        return None, ERR_USERNAME_BOT
    if not name[0].isalpha():
        return None, "⚠️ Invalid Username: It must begin with a letter."
    return name, None


async def username_taken(bot, name, own_chat_id=None):
    try:
        found = await bot.get_chat(f"@{name}")
    except TelegramError:
        return False  # Telegram reports no public chat/bot/user with this name
    return found.id != own_chat_id


async def read_image(context, msg, jpeg_only=False):
    """Returns (bytes, error) for a photo message or an image sent as a file."""
    if msg.photo:
        item = msg.photo[-1]
    elif msg.document and (msg.document.mime_type or "").startswith("image/"):
        mime = msg.document.mime_type
        allowed = ("image/jpeg",) if jpeg_only else ("image/jpeg", "image/png")
        if mime not in allowed:
            return None, ("⚠️ Unsupported format. Please send a JPG image." if jpeg_only
                          else "⚠️ Unsupported format. Please send a JPG or PNG image.")
        item = msg.document
    else:
        return None, "⚠️ Please upload an image (as a photo, or as a JPG/PNG file)."
    if item.file_size and item.file_size > MAX_FILE_BYTES:
        return None, "⚠️ That image is too large. Please send one under 10 MB."
    try:
        tg_file = await context.bot.get_file(item.file_id)
        return bytes(await tg_file.download_as_bytearray()), None
    except TelegramError as e:
        logging.warning("Image download failed: %s", e)
        return None, "⚠️ I couldn't download that image. Please try again."


def _api_error_text(e) -> str:
    """Short description of a Telegram API error (plain text; shown without HTML parsing)."""
    return (getattr(e, "message", None) or str(e) or type(e).__name__)[:200]


def card(title, detail=""):
    return f"✅ <b>{title}</b>" + (f"\n\n{detail}" if detail else "")


# ---- state handlers: each returns True when finished, False to stay in the state
async def h_group_name(update, context, s):
    msg, chat = update.effective_message, update.effective_chat
    value = _text_or_none(msg)
    if not value or len(value) > 128:
        await msg.reply_text("⚠️ Invalid Name: Please send text between 1 and 128 characters.")
        return False
    try:
        await context.bot.set_chat_title(chat.id, value)
    except TelegramError as e:
        logging.warning("Set title failed in %s: %s", chat.id, e)
        await msg.reply_text("⚠️ I couldn't change the group name. Please make sure I'm an admin "
                             "with the 'Change Group Info' permission.")
        return True
    await msg.reply_html(card("Group name updated", f"New name: <b>{html.escape(value)}</b>"))
    return True


async def h_group_bio(update, context, s):
    msg, chat = update.effective_message, update.effective_chat
    value = _text_or_none(msg)
    if not value or len(value) > 255:
        await msg.reply_text("⚠️ Invalid Description: Please send text between 1 and 255 characters.")
        return False
    try:
        await context.bot.set_chat_description(chat.id, value)
    except TelegramError as e:
        logging.warning("Set description failed in %s: %s", chat.id, e)
        await msg.reply_text("⚠️ I couldn't change the description. Please make sure I'm an admin "
                             "with the 'Change Group Info' permission.")
        return True
    await msg.reply_html(card("Group description updated", html.escape(value)))
    return True


async def h_group_photo(update, context, s):
    msg, chat = update.effective_message, update.effective_chat
    data, err = await read_image(context, msg)
    if err:
        await msg.reply_text(err)
        return False
    try:
        await context.bot.set_chat_photo(chat.id, photo=data)
    except TelegramError as e:
        logging.warning("Set photo failed in %s: %s", chat.id, e)
        await msg.reply_text("⚠️ I couldn't set that photo. Please make sure I'm an admin "
                             "with the 'Change Group Info' permission.")
        return True
    await msg.reply_html(card("Group photo updated"))
    return True


async def h_group_username(update, context, s):
    msg, chat = update.effective_message, update.effective_chat
    name, err = check_username(msg.text, is_bot=False) if msg.text else (None, ERR_USERNAME_CHARS)
    if err:
        await msg.reply_text(err)
        return False
    if await username_taken(context.bot, name, own_chat_id=chat.id):
        await msg.reply_text(ERR_USERNAME_TAKEN)
        return False
    await msg.reply_html(
        card(f"@{name} is available",
             "Telegram does not allow bots to change a group's username, so the group owner "
             "needs to finish this step in the Telegram app:\n"
             f"Group info → Edit → Group Type → Public → set the link to <code>t.me/{name}</code>")
    )
    return True


async def h_bot_name(update, context, s):
    msg = update.effective_message
    value = _text_or_none(msg)
    if not value or len(value) > 64:
        await msg.reply_text("⚠️ Invalid Name: Please send text between 1 and 64 characters.")
        return False
    try:
        await context.bot.set_my_name(value)
    except RetryAfter as e:
        logging.warning("Set bot name rate-limited: %s", e)
        await msg.reply_text(f"⚠️ Telegram is rate-limiting bot name changes. "
                             f"Please try again in about {int(e.retry_after)} seconds.")
        return True
    except TelegramError as e:
        logging.warning("Set bot name failed: %s", e)
        await msg.reply_text(f"⚠️ Telegram rejected the name change: {_api_error_text(e)}\n"
                             "(Telegram also limits how often a bot's name can be changed.)")
        return True
    # Saved per bot (test bot and main bot may share one database) so a restart can re-apply it.
    set_setting(0, _bkey("bot_name"), value)
    extra.set_bot_name(value)
    await extra.refresh_identity(context.bot, force=True)
    await msg.reply_html(card("Bot name updated", f"New name: <b>{html.escape(value)}</b>"))
    return True


async def h_bot_bio(update, context, s):
    msg = update.effective_message
    value = _text_or_none(msg)
    if not value or len(value) > 512:
        await msg.reply_text("⚠️ Invalid Description: Please send text between 1 and 512 characters.")
        return False
    try:
        await context.bot.set_my_description(value)
        set_setting(0, "bot_description", value)
        if len(value) <= 120:  # also fits the short "About" line on the bot's profile
            await context.bot.set_my_short_description(value)
            set_setting(0, "bot_short_description", value)
    except TelegramError as e:
        logging.warning("Set bot description failed: %s", e)
        await msg.reply_text("⚠️ Telegram rejected that description. Please try again.")
        return True
    await msg.reply_html(card("Bot bio / description updated", html.escape(value)))
    return True


async def h_bot_photo(update, context, s):
    msg = update.effective_message
    data, err = await read_image(context, msg, jpeg_only=True)  # Telegram accepts only JPG here
    if err:
        await msg.reply_text(err)
        return False
    if InputProfilePhotoStatic is None or not hasattr(context.bot, "set_my_profile_photo"):
        await msg.reply_text("⚠️ This version of python-telegram-bot can't change a bot's photo. "
                             "Please upgrade it: pip install -U python-telegram-bot")
        return True
    if not data.startswith(b"\xff\xd8\xff"):  # real JPEG signature; the API only takes .JPG
        await msg.reply_text("⚠️ That file isn't a valid JPG image. Please send a JPG photo.")
        return False
    try:
        ok = await context.bot.set_my_profile_photo(InputProfilePhotoStatic(photo=data))
    except RetryAfter as e:
        logging.warning("Set bot photo rate-limited: %s", e)
        await msg.reply_text(f"⚠️ Telegram is rate-limiting profile photo changes. "
                             f"Please try again in about {int(e.retry_after)} seconds.")
        return True
    except TelegramError as e:
        logging.warning("Set bot photo failed: %s", e)
        await msg.reply_text(f"⚠️ Telegram rejected the profile photo: {_api_error_text(e)}\n"
                             "Please try a different square JPG photo.")
        return True
    if ok is not True:  # the API returns True on success; never report success otherwise
        logging.warning("Set bot photo returned %r", ok)
        await msg.reply_text("⚠️ Telegram did not confirm the profile photo change. Please try again.")
        return True
    await msg.reply_html(card("Bot profile photo updated"))
    return True


async def h_bot_username(update, context, s):
    msg = update.effective_message
    name, err = check_username(msg.text, is_bot=True) if msg.text else (None, ERR_USERNAME_CHARS)
    if err:
        await msg.reply_text(err)
        return False
    if await username_taken(context.bot, name):
        await msg.reply_text(ERR_USERNAME_TAKEN)
        return False
    await msg.reply_html(
        card(f"@{name} is available",
             "Telegram does not allow a bot to change its own username through the Bot API. "
             "To finish, open @BotFather, send <code>/setusername</code>, choose this bot, then "
             f"send <code>@{name}</code>. Your bot token stays the same.")
    )
    return True


EDIT_HANDLERS = {
    AWAITING_GROUP_NAME: h_group_name,
    AWAITING_GROUP_USERNAME: h_group_username,
    AWAITING_GROUP_PHOTO: h_group_photo,
    AWAITING_GROUP_BIO: h_group_bio,
    AWAITING_BOT_NAME: h_bot_name,
    AWAITING_BOT_USERNAME: h_bot_username,
    AWAITING_BOT_PHOTO: h_bot_photo,
    AWAITING_BOT_BIO: h_bot_bio,
}


async def edit_input(update, context):
    """Runs before every other message handler; consumes a message only when the
    sender has an active edit session."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not chat or not user:
        return
    key = (chat.id, user.id)
    s = edit_sessions.get(key)
    if not s:
        return
    if time.time() - s["ts"] > SESSION_TIMEOUT:
        end_session(key)
        await msg.reply_text(MSG_TIMEOUT)
        raise ApplicationHandlerStop
    err = await edit_perm_error(s["kind"], chat, user.id)
    if err:
        end_session(key)
        await msg.reply_text(err)
        raise ApplicationHandlerStop
    s["ts"] = time.time()
    if await EDIT_HANDLERS[s["state"]](update, context, s):
        end_session(key)
    raise ApplicationHandlerStop


# ------------------------------------------- bot rights, migration, errors
BOT_RIGHTS_TTL = 120  # seconds a looked-up value is trusted; my_chat_member updates it instantly
bot_rights = {}       # chat_id -> {"status", "can_delete", "ts"}
_err_notice = {}      # chat_id -> time of the last "missing rights" notice


def _rights_from(member):
    return {
        "status": member.status,
        "can_delete": member.status == ChatMemberStatus.ADMINISTRATOR
        and bool(getattr(member, "can_delete_messages", False)),
        "ts": time.time(),
    }


async def get_bot_rights(chat, bot, fresh=False):
    """The bot's own status in a chat. Cached briefly and refreshed by
    my_chat_member events, so a promotion/demotion takes effect right away."""
    hit = bot_rights.get(chat.id)
    if hit and not fresh and time.time() - hit["ts"] < BOT_RIGHTS_TTL:
        return hit
    try:
        bot_rights[chat.id] = _rights_from(await chat.get_member(bot.id))
    except TelegramError as e:
        logging.warning("Couldn't read my own rights in chat %s: %s: %s", chat.id, type(e).__name__, e)
        bot_rights.pop(chat.id, None)
        return None
    return bot_rights[chat.id]


async def on_my_chat_member(update, context):
    """The bot was added, removed, promoted, demoted or restricted somewhere."""
    ev = update.my_chat_member
    chat, old, new = ev.chat, ev.old_chat_member, ev.new_chat_member
    if chat.type == "private":  # a user blocked/unblocked the bot
        return
    logging.info("Bot status in chat %s (%s): %s -> %s (by %s)", chat.id, chat.title,
                 old.status, new.status, ev.from_user.id if ev.from_user else "?")
    _sug_synced.discard(chat.id)  # republish the command list on the next message
    if new.status in (ChatMemberStatus.LEFT, ChatMemberStatus.BANNED):
        bot_rights.pop(chat.id, None)
        return
    bot_rights[chat.id] = _rights_from(new)
    if new.status == ChatMemberStatus.ADMINISTRATOR and not bot_rights[chat.id]["can_delete"]:
        logging.warning("I'm admin in chat %s but without the 'delete messages' right", chat.id)


async def on_migrate(update, context):
    """A basic group became a supergroup: it gets a NEW chat id, which is why the
    bot looked dead until it was re-added. Move every saved setting across."""
    msg = update.effective_message
    old_id, new_id = msg.chat.id, msg.migrate_to_chat_id
    if not new_id:
        return
    store.migrate_chat(old_id, new_id)
    bot_rights.pop(old_id, None)
    _sug_synced.discard(new_id)
    logging.info("Chat %s migrated to supergroup %s; settings moved", old_id, new_id)


async def on_error(update, context):
    """Log every handler failure with its chat, command and source line."""
    err = context.error
    where, cmd = "no chat", ""
    if isinstance(update, Update):
        if update.effective_chat:
            where = f"chat={update.effective_chat.id} ({update.effective_chat.type})"
        m = update.effective_message
        cmd = ((m.text or m.caption or "")[:60]) if m else ""
    frame = traceback.extract_tb(err.__traceback__)[-1] if err and err.__traceback__ else None
    src = f"{os.path.basename(frame.filename)}:{frame.lineno} in {frame.name}()" if frame else "unknown"
    logging.error("Handler failed | %s | text=%r | %s: %s | at %s",
                  where, cmd, type(err).__name__, err, src, exc_info=err)
    if not isinstance(update, Update) or not update.effective_chat or not update.effective_message:
        return
    chat = update.effective_chat
    low = str(err).lower()
    rights_problem = isinstance(err, (Forbidden, BadRequest)) and any(
        k in low for k in ("not enough rights", "need to be admin", "have no rights",
                           "rights to", "can't be deleted", "chat_admin_required"))
    if rights_problem and chat.type != "private" and time.time() - _err_notice.get(chat.id, 0) > 60:
        _err_notice[chat.id] = time.time()
        bot_rights.pop(chat.id, None)  # force a fresh look at my rights next time
        try:
            await chat.send_message("⚠️ That command failed because I'm missing an admin right it "
                                    "needs. Please check my admin permissions in this group.")
        except TelegramError:
            pass


async def _startup_sync(app):
    """Slow one-off Telegram housekeeping (profile text, command lists). Runs in the BACKGROUND
    so the bot answers messages immediately instead of after dozens of sequential API calls."""
    try:
        # Only an owner edit (Bot Edit) may change the Telegram name. The old code pushed the generic
        # BOT_NAME default on every start, undoing a rename done in BotFather.
        target_name = get_setting(0, _bkey("bot_name"))
        if target_name:
            try:
                current = await app.bot.get_my_name()
                if current.name != target_name:  # name changes are rate-limited, so only when needed
                    await app.bot.set_my_name(target_name)
            except TelegramError as e:
                logging.warning("Couldn't re-apply the saved bot name: %s", e)
        await extra.refresh_identity(app.bot, force=True)
        await app.bot.set_my_short_description(
            get_setting(0, "bot_short_description")
            or "Group moderation: warnings, mutes, filters, welcomes and join verification."
        )
        await app.bot.set_my_description(
            get_setting(0, "bot_description")
            or "I help admins keep groups tidy: warnings, mutes, blocklists, antiflood and "
            "antispam, welcome messages, filters, notes and join verification. "
            "Add me to your group as an admin and send /help."
        )
    except TelegramError as e:
        logging.warning("Couldn't update the bot profile: %s", e)

    # Commands are published ONCE, globally (default scope), and only when the list changed.
    # No loop over groups: per-chat lists are touched only when an admin uses /suggestions.
    cmd_sig = hashlib.md5("|".join(f"{c.command}:{c.description}" for c in BOT_COMMANDS).encode()).hexdigest()
    if get_setting(0, _bkey("cmd_sig")) == cmd_sig and not os.environ.get("FORCE_COMMAND_SYNC"):
        logging.info("Command list unchanged since the last start - nothing to publish.")
        return
    try:
        await app.bot.set_my_commands(BOT_COMMANDS, scope=BotCommandScopeDefault())
    except TelegramError as e:
        logging.warning("Couldn't set the command list: %s", e)
        return
    # Remove older, more specific global lists that would hide the new one (a handful of calls,
    # run together; chats are NOT visited one by one).
    jobs = []
    for scope in (BotCommandScopeAllPrivateChats(), BotCommandScopeAllGroupChats(),
                  BotCommandScopeAllChatAdministrators()):
        jobs.append(_try_delete(app.bot, scope))
        for code in COMMON_LANGS:
            jobs.append(_try_delete(app.bot, scope, code))
    for code in COMMON_LANGS:
        jobs.append(_try_delete(app.bot, BotCommandScopeDefault(), code))
    await _gather_limited(jobs, limit=8)
    set_setting(0, _bkey("cmd_sig"), cmd_sig)  # remembered only after a complete sync, per bot


async def _startup_sync_safe(app):
    t0 = time.perf_counter()
    try:
        await _startup_sync(app)
    except Exception:
        logging.exception("Background startup sync failed")
    logging.info("⏱ background startup sync finished in %.1fs", time.perf_counter() - t0)


async def post_init(app):
    """Must stay instant: polling doesn't begin until this returns."""
    if not OWNER_IDS:
        logging.warning("OWNER_IDS is empty - Bot Edit and Super Admin commands are locked "
                        "until you set the OWNER_IDS environment variable to your Telegram ID.")
    global _BOT_ID
    _BOT_ID = app.bot.id  # main bot and test bot keep separate command-sync state
    await extra.refresh_identity(app.bot, force=True)  # current Telegram name/username (bot.get_me())
    logging.info("Bot identity: name=%r username=@%s id=%s", extra.bot_name(), extra.bot_username(), _BOT_ID)
    app.bot_data["captcha_task"] = asyncio.create_task(captcha_sweeper(app))
    app.bot_data["msgcount_task"] = asyncio.create_task(msgcount.outbox_sweeper(app))  # pending milestone messages
    app.bot_data["notice_task"] = asyncio.create_task(extra.notice_sweeper(app))  # deletes action notices after 1 day
    app.bot_data["startup_task"] = asyncio.create_task(_startup_sync_safe(app))


# ------------------------------------------------- performance logging / profiling
# Every command and button press logs how long it took ("⏱ /ban took 0.412s"). Anything slower
# than SLOW_HANDLER_SECS is a WARNING, and so is any single Telegram API call slower than
# SLOW_API_SECS - together they show exactly WHICH call causes a delay, e.g.
#   🐢 Telegram API sendMessage took 3.20s (during /warn)
# When the sender's message reached the bot late, the log says so: that means the delay is
# on Telegram's side / the network / a backlog, not inside the handlers.
SLOW_HANDLER_SECS = float(os.environ.get("SLOW_HANDLER_SECS", "1.0"))
SLOW_API_SECS = float(os.environ.get("SLOW_API_SECS", "1.5"))
_current_handler = contextvars.ContextVar("current_handler", default="-")


class TimedRequest(HTTPXRequest):
    """Same HTTP client as the default, plus a warning for every slow Telegram API call."""

    async def do_request(self, url, method, *args, **kwargs):
        t0 = time.perf_counter()
        try:
            return await super().do_request(url, method, *args, **kwargs)
        finally:
            dt = time.perf_counter() - t0
            api = str(url).rsplit("/", 1)[-1]
            if api != "getUpdates" and dt >= SLOW_API_SECS:  # getUpdates is a long poll: slow by design
                logging.warning("🐢 Telegram API %s took %.2fs (during %s)", api, dt, _current_handler.get())


def timed(label, fn, always=True):
    """Wrap a handler callback with execution-time logging."""
    @functools.wraps(fn)
    async def wrapper(update, context):
        token = _current_handler.set(label)
        t0 = time.perf_counter()
        late = ""
        sent = getattr(getattr(update, "message", None), "date", None)
        if sent is not None and time.time() - sent.timestamp() > 3:
            late = f" | message reached the bot {time.time() - sent.timestamp():.1f}s after it was sent"
        try:
            return await fn(update, context)
        finally:
            dt = time.perf_counter() - t0
            if dt >= SLOW_HANDLER_SECS:
                logging.warning("🐌 %s took %.2fs%s", label, dt, late)
            elif always or late:
                logging.info("⏱ %s took %.3fs%s", label, dt, late)
            _current_handler.reset(token)
    wrapper._timed = True
    return wrapper


def instrument_handlers(app):
    """Add timing to every registered handler (including the ones extra.py registers)."""
    for group_handlers in app.handlers.values():
        for h in group_handlers:
            cb = getattr(h, "callback", None)
            if cb is None or getattr(cb, "_timed", False):
                continue
            cmds = getattr(h, "commands", None)
            if cmds:
                label, loud = "/" + "|".join(sorted(cmds)), True
            elif isinstance(h, CallbackQueryHandler):
                label, loud = f"button:{getattr(cb, '__name__', 'callback')}", True
            else:  # passive handlers see every message: only log them when slow
                label, loud = f"handler:{getattr(cb, '__name__', type(h).__name__)}", False
            h.callback = timed(label, cb, always=loud)


# ------------------------------------------------------------------ /stats (Bot Owner only)
# Lists every group the bot is in, with an Open Group and a Remove (leave) button for each.
# The list is kept in the settings store under chat_id 0 (the same place the bot keeps its other
# bot-wide values) and is updated automatically: when the bot is added/removed (my_chat_member),
# when a group is migrated to a supergroup, and the first time a message is seen in a group.
# Every /stats view re-checks each stored group with Telegram and drops the ones the bot has left.
import json as _stats_json

_STATS_KEY = "stats_groups"   # settings(0, "stats_groups") = JSON {"<chat id>": "<title>"}
STATS_PAGE_SIZE = 8
_stats_cache = {}             # chat id (int) -> last stored title, so repeated messages cost nothing


def _stats_load():
    try:
        data = _stats_json.loads(get_setting(0, _STATS_KEY, "{}") or "{}")
        return data if isinstance(data, dict) else {}
    except Exception:
        logging.exception("stats: couldn't read the group list")
        return {}


def _stats_save(data):
    set_setting(0, _STATS_KEY, _stats_json.dumps(data, ensure_ascii=False))


def _stats_remember(chat_id, title):
    title = (title or "").strip() or str(chat_id)
    if _stats_cache.get(chat_id) == title:
        return
    try:
        data = _stats_load()
        if data.get(str(chat_id)) != title:
            data[str(chat_id)] = title
            _stats_save(data)
        _stats_cache[chat_id] = title
    except Exception:
        logging.exception("stats: couldn't record chat %s", chat_id)


def _stats_forget(chat_id):
    _stats_cache.pop(chat_id, None)
    try:
        data = _stats_load()
        if data.pop(str(chat_id), None) is not None:
            _stats_save(data)
    except Exception:
        logging.exception("stats: couldn't remove chat %s", chat_id)


async def stats_record(update, context):
    """group=-30, never blocks: remembers each group the bot sees a message in."""
    chat = update.effective_chat
    if chat is not None and chat.type in ("group", "supergroup"):
        _stats_remember(chat.id, chat.title)


# Defaults a NEW group starts with when the bot is added to it. These are the ORIGINAL values; the 👑 Owner panel can
# change any of them (saved in MongoDB). Existing groups keep what they have: a value is only written when the group
# has no value of its own yet.
NEW_GROUP_DEFAULTS = {
    "block_punish": "mute", "block_punish_secs": 30 * 60,  # Ads + Promotion: mute 30 minutes (/adpunish overrides per group)
    "nsfw_action": "delete", "nsfw_secs": 5 * 60,           # Protection: delete; a mute lasts 5 minutes
    "flood_mode": "tmute:300",                              # Antiflood: mute 5 minutes
    "spam_mode": "warn",
    "blocklist_mode": "delete",
    "warn_mode": "ban",                                     # action when the warn limit is reached
    "captcha_action": "kick",
}


def new_group_defaults():
    """What a new group gets: the original values, replaced by whatever the owner changed in the 👑 Owner panel."""
    out = dict(NEW_GROUP_DEFAULTS)
    try:
        out.update(store.owner_defaults())
    except Exception:
        logging.exception("Couldn't read the owner's default settings; using the original defaults")
    return out


def apply_new_group_defaults(chat_id):
    """Save the new-group defaults for a group the bot was just added to (never overwrites a saved value)."""
    for key, value in new_group_defaults().items():
        if get_setting(chat_id, key) is None:
            set_setting(chat_id, key, value)


async def stats_member_update(update, context):
    """group=40: the bot was added to / removed from a group."""
    ev = update.my_chat_member
    chat = ev.chat
    if chat.type not in ("group", "supergroup"):
        return
    if ev.new_chat_member.status in (ChatMemberStatus.LEFT, ChatMemberStatus.BANNED):
        _stats_forget(chat.id)
    else:
        _stats_remember(chat.id, chat.title)
        was_out = ev.old_chat_member.status in (ChatMemberStatus.LEFT, ChatMemberStatus.BANNED)
        if was_out:  # the bot has just been ADDED (a promotion inside a group it was already in does not count)
            try:
                await asyncio.to_thread(apply_new_group_defaults, chat.id)
            except Exception:
                logging.exception("Couldn't save the new-group defaults for chat %s", chat.id)


async def stats_migrate(update, context):
    """group=41: a basic group became a supergroup (new chat id): move the entry across."""
    msg = update.effective_message
    new_id = msg.migrate_to_chat_id if msg else None
    if not new_id:
        return
    _stats_forget(msg.chat.id)
    _stats_remember(new_id, msg.chat.title)


def _stats_link(info, chat_id):
    if getattr(info, "username", None):
        return f"https://t.me/{info.username}"
    if getattr(info, "invite_link", None):
        return info.invite_link
    s = str(chat_id)
    if s.startswith("-100"):
        return f"https://t.me/c/{s[4:]}/1"  # opens the group for members (the owner)
    return None


async def _stats_refresh(bot):
    """Re-check every stored group with Telegram. Returns [(chat_id, title, link)] and drops groups
    the bot is no longer in. A temporary Telegram/network error keeps the stored entry."""
    data = _stats_load()
    sem = asyncio.Semaphore(5)

    async def check(cid_text):
        cid, title = int(cid_text), data[cid_text]
        async with sem:
            try:
                me = await bot.get_chat_member(cid, bot.id)
                if me.status in (ChatMemberStatus.LEFT, ChatMemberStatus.BANNED):
                    return cid, None, None
                info = await bot.get_chat(cid)
            except Forbidden:
                return cid, None, None
            except BadRequest as e:
                if "chat not found" in str(e).lower():
                    return cid, None, None
                return cid, title, None
            except TelegramError as e:
                logging.warning("stats: couldn't check chat %s: %s", cid, e)
                return cid, title, None
        return cid, (info.title or title), _stats_link(info, cid)

    results = await asyncio.gather(*(check(k) for k in data))
    gone = [cid for cid, title, _ in results if title is None]
    changed = False
    for cid in gone:
        _stats_cache.pop(cid, None)
        data.pop(str(cid), None)
        changed = True
    for cid, title, _ in results:
        if title is not None and data.get(str(cid)) != title:
            data[str(cid)] = title
            _stats_cache[cid] = title
            changed = True
    if changed:
        try:
            _stats_save(data)
        except Exception:
            logging.exception("stats: couldn't save the refreshed group list")
    return [(cid, title, link) for cid, title, link in results if title is not None]


async def _stats_render(bot, page):
    groups = await _stats_refresh(bot)
    total = len(groups)
    pages = max(1, -(-total // STATS_PAGE_SIZE))
    page = min(max(page, 0), pages - 1)
    chunk = groups[page * STATS_PAGE_SIZE:(page + 1) * STATS_PAGE_SIZE]
    lines = ["📊 <b>Group Statistics</b>", "", f"Total Groups: {total}"]
    rows = []
    for i, (cid, title, link) in enumerate(chunk, page * STATS_PAGE_SIZE + 1):
        lines += ["", f"{i}. 🏠 {html.escape(title)}", f"🆔 Group ID: <code>{cid}</code>"]
        open_btn = (InlineKeyboardButton("🔗 Open Group", url=link) if link
                    else InlineKeyboardButton("🔗 Open Group", callback_data="stats:nolink"))
        short = title if len(title) <= 20 else title[:19] + "…"
        rows.append([open_btn,
                     InlineKeyboardButton(f"🗑 Remove: {short}", callback_data=f"stats:rm:{cid}:{page}")])
    if not total:
        lines += ["", "No groups yet. A group appears here when I'm added to it or when a message is seen in it."]
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("◀ Prev", callback_data=f"stats:p:{page - 1}"))
    nav.append(InlineKeyboardButton("🔄 Refresh", callback_data=f"stats:p:{page}"))
    if page < pages - 1:
        nav.append(InlineKeyboardButton("Next ▶", callback_data=f"stats:p:{page + 1}"))
    rows.append(nav)
    if pages > 1:
        lines += ["", f"Page {page + 1}/{pages}"]
    return "\n".join(lines), InlineKeyboardMarkup(rows)


async def stats_cmd(update, context):
    """/stats: Bot Owner only."""
    msg, user = update.effective_message, update.effective_user
    if not user or user.id not in OWNER_IDS:
        await msg.reply_text("⚠️ Access Denied: Only the Bot Owner can use /stats.")
        return
    if update.effective_chat.type != "private":  # the all-groups list is never shown in a group
        await msg.reply_text("🔒 Global information is private. Send /stats to me in a private chat.")
        return
    text, markup = await _stats_render(context.bot, 0)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


async def stats_callback(update, context):
    """Buttons: stats:p:<page>, stats:rm:<chat id>:<page>, stats:nolink."""
    q = update.callback_query
    if q.from_user.id not in OWNER_IDS:
        await q.answer("Only the Bot Owner can use this.", show_alert=True)
        return
    if q.message is None or q.message.chat.type != "private":
        await q.answer("Global information is only available in a private chat.", show_alert=True)
        return
    parts = (q.data or "").split(":")
    action = parts[1] if len(parts) > 1 else ""
    page, toast, alert = 0, None, False
    try:
        if action == "nolink":
            await q.answer("This group has no public link, so I can't open it from here.", show_alert=True)
            return
        if action == "p" and len(parts) == 3:
            page = int(parts[2])
        elif action == "rm" and len(parts) == 4:
            cid, page = int(parts[2]), int(parts[3])
            if str(cid) in _stats_load():
                try:
                    await context.bot.leave_chat(cid)
                    _stats_forget(cid)
                    toast = "Left the group."
                except TelegramError as e:
                    logging.warning("stats: couldn't leave chat %s: %s", cid, e)
                    toast, alert = f"Couldn't leave that group: {str(e)[:150]}", True
            else:
                toast = "That group is no longer in the list."
    except ValueError:
        pass
    try:
        await q.answer(toast, show_alert=alert)
    except TelegramError:
        pass
    text, markup = await _stats_render(context.bot, page)
    try:
        await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup, disable_web_page_preview=True)
    except TelegramError:
        pass  # unchanged message (e.g. Refresh with no change)


def main():
    extra.start_web_server()  # Render: open the port first (health check / keep-alive)
    missing = [n for n in ("BOT_TOKEN", "MONGO_URI") if not (os.getenv(n) or "").strip()]
    if missing:
        logging.critical("Missing required environment variable(s): %s. Add them in the Render "
                         "dashboard (Environment tab) or in your local .env file.", ", ".join(missing))
        # Say exactly where the bot looked, so a .env in the wrong folder is obvious.
        for _dir in dict.fromkeys((_HERE, os.getcwd())):
            try:
                names = sorted(os.listdir(_dir))
            except OSError:
                names = []
            found = [n for n in _ENV_NAMES if n in names]
            logging.critical("Looked in: %s | env file found there: %s", _dir, found or "NONE")
        logging.critical("Put the .env file in the SAME folder as nova.py (the first path above).")
        sys.exit(1)
    try:
        store.connect()    # MongoDB Atlas; exits with a readable reason if it can't be reached
        store.auto_seed()  # first run only: imports an old rose_clone.db if one is next to this file
    except store.StoreError as e:
        logging.critical("%s", e)
        sys.exit(1)
    extra.start_self_ping()
    purge_clear_legacy_state()
    # concurrent_updates: one slow job (a big purge, a flood-wait) no longer freezes every chat.
    # Own HTTP clients: a big connection pool and generous pool/connect timeouts, so a burst of
    # replies never queues behind a tiny pool ("Pool timeout"), plus slow-API-call logging.
    app = (Application.builder().token(BOT_TOKEN.strip()).post_init(post_init)
           .concurrent_updates(True)
           .request(TimedRequest(connection_pool_size=128, connect_timeout=10, read_timeout=20,
                                 write_timeout=20, pool_timeout=15))
           .get_updates_request(TimedRequest(connection_pool_size=2, connect_timeout=10,
                                             read_timeout=20, write_timeout=10, pool_timeout=15))
           .build())
    app.add_error_handler(on_error)
    app.add_handler(ChatMemberHandler(on_my_chat_member, ChatMemberHandler.MY_CHAT_MEMBER))
    app.add_handler(MessageHandler(filters.StatusUpdate.MIGRATE, on_migrate))

    commands = {
        "start": start, "help": help_cmd,
        "ban": ban, "unban": unban, "kick": kick, "promote": promote, "demote": demote,
        "mute": mute, "tmute": tmute, "dmute": dmute, "unmute": unmute,
        "warn": warn, "dwarn": dwarn, "warns": warns_cmd, "rmwarn": rmwarn,
        "modlog": modlog_cmd, "resetwarns": resetwarns, "warnlimit": warnlimit, "setwarnlimit": warnlimit,
        "warnmode": warnmode, "warntime": warntime,
        "flood": flood, "setflood": setflood, "floodmode": floodmode,
        "antispam": antispam, "spammode": spammode,
        "repeatlimit": repeatlimit, "mentionlimit": mentionlimit,
        "blocklistmode": blocklistmode, "report": report_cmd, "reports": reports_toggle,
        "groupedit": groupedit_cmd, "bot": bot_cmd, "cancel": cancel_cmd,
        "addadmin": addadmin_cmd, "removeadmin": removeadmin_cmd, "adminlist": adminlist_cmd,
        "disable": disable_cmd, "enable": enable_cmd, "disableable": disableable_cmd,
        "disabled": disabled_cmd, "disabledel": disabledel_toggle, "disableadmin": disableadmin_toggle,
        "approve": approve_user, "unapprove": unapprove_user, "approved": approved_list,
        "unapproveall": unapprove_all, "approval": approval_status, "suggestions": suggestions_toggle,
        "setlog": setlog, "unsetlog": unsetlog, "logchannel": logchannel,
        "log": log_enable, "nolog": log_disable, "logcategories": logcategories,
        "captcha": captcha_cmd, "captchamode": captchamode,
        "captchatime": captchatime, "captchaaction": captchaaction,
        "setwelcome": setwelcome, "welcome": welcome_cmd, "resetwelcome": resetwelcome,
        "cleanwelcome": cleanwelcome, "setgoodbye": setgoodbye, "goodbye": goodbye_cmd,
        "resetgoodbye": resetgoodbye,
        "setrules": setrules, "rules": rules, "resetrules": resetrules, "privaterules": privaterules,
        "setrulesbutton": setrulesbutton, "resetrulesbutton": resetrulesbutton,
        "locks": locks_cmd, "lockwarns": lockwarns, "locktypes": locktypes,
        "allowlist": allowlist_cmd, "rmallowlist": rmallowlist, "rmallowlistall": rmallowlistall,
        "save": save_note, "get": get_note, "notes": list_notes, "clear": clear_note,
        "filter": add_filter, "stop": stop_filter, "filters": list_filters,
        "pause": pause_cmd, "resume": resume_cmd,
        "lock": lock, "unlock": unlock, "pin": pin, "purge": purge, "spurge": spurge, "del": del_cmd,
        "purgefrom": purgefrom, "purgeto": purgeto,
        "addblocklist": addblocklist, "unblocklist": unblocklist, "blocklist": blocklist_cmd,
    }
    for name, fn in commands.items():
        if name in DISABLEABLE_COMMANDS:
            fn = guard_disableable(name, fn)
        app.add_handler(CommandHandler(name, fn))
    app.add_handler(MessageHandler(filters.ChatType.CHANNEL & filters.Regex(r"^/setlog(@\w+)?\s*$"), setlog))

    extra.register(app, warn_summary, limits_lines)
    extra.register_ai(app)  # /ask /imagine /search /translate /joke /quote /fact /roll /flip /say
    # roast and court systems: the bot's own helpers are handed in (no re-import of this file)
    fun_systems.register(app, SimpleNamespace(
        is_admin=is_admin, admin_only=admin_only, lock_exempt=lock_exempt,
        load_allow=load_allow, url_allowed=url_allowed, log_action=log_action, MUTED=MUTED))
    # auto-ads / promotion blocker + the 🔒 Blocking menu (lives in extra.py; per-group settings in the settings store)
    extra.register_blocking(app, SimpleNamespace(
        is_admin=is_admin, lock_exempt=lock_exempt, load_allow=load_allow, url_allowed=url_allowed,
        log_action=log_action, MUTED=MUTED, is_super_admin=is_super_admin, owner_ids=OWNER_IDS,
        is_paused=is_paused, is_bot_owner=is_bot_owner, get_setting=store.get_setting, set_setting=store.set_setting,
        block_words=store.block_words))  # the Blocklist is the shared word source for NSFW Word
    msgcount.register(app)  # /rank /top /today /week /overall /me /radmin /resetrank + counter + 📊 menu
    app.add_handler(CallbackQueryHandler(captcha_callback, pattern=r"^cap:"))
    app.add_handler(CallbackQueryHandler(help_callback, pattern=r"^help:"))
    app.add_handler(CallbackQueryHandler(owner_callback, pattern=r"^own:"))  # 👑 Owner: defaults for new groups
    app.add_handler(CallbackQueryHandler(pause_callback, pattern=r"^pz:"))
    # /power: matched ONLY for a Primary Bot Owner in a private chat, so everyone else gets complete silence
    app.add_handler(CommandHandler(["power", "showpower"], power_cmd,
                                   filters=filters.ChatType.PRIVATE & filters.User(user_id=OWNER_IDS)))
    app.add_handler(CallbackQueryHandler(edit_callback, pattern=r"^(gedit|bedit):"))
    app.add_handler(CallbackQueryHandler(suggestions_callback, pattern=r"^sug:"))
    app.add_handler(CallbackQueryHandler(unapprove_all_callback, pattern=r"^unall:"))
    app.add_handler(CallbackQueryHandler(action_callback, pattern=r"^(unban|unmute|rmwarn):"))
    # default list is published once at startup; each group's own list (ON/OFF) is synced from the
    # database on the first message seen there (group=-3 runs before everything else, never blocks)
    app.add_handler(MessageHandler(filters.ChatType.GROUPS, sync_suggestions), group=-3)
    # group=-100: /pause gate. Runs before everything else; a paused group's ordinary messages and join/leave
    # events stop here. Commands and the group->supergroup migration notice are never stopped.
    app.add_handler(MessageHandler(
        filters.ChatType.GROUPS & ~filters.COMMAND & ~filters.StatusUpdate.MIGRATE, pause_gate), group=-100)
    # group=-4: automatic name-change detection (no command; a group of its own so it never
    # competes with, or blocks, the other handlers)
    app.add_handler(MessageHandler(
        filters.ChatType.GROUPS & filters.UpdateType.MESSAGE & ~filters.StatusUpdate.ALL,
        name_change_watch,
    ), group=-4)
    # group=-5: remembers @usernames per group so /mute @name etc. can resolve them (never blocks)
    app.add_handler(MessageHandler(
        filters.ChatType.GROUPS & filters.UpdateType.MESSAGE & ~filters.StatusUpdate.ALL,
        remember_username,
    ), group=-5)
    # group=-2: locks see every group message (commands too) before anything else acts on it
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & ~filters.StatusUpdate.ALL, lock_guard), group=-2)
    # group=-1 runs before all other handlers so an active edit session gets first look
    app.add_handler(MessageHandler(
        ~filters.COMMAND & (filters.TEXT | filters.PHOTO | filters.Document.IMAGE)
        & (filters.ChatType.PRIVATE | filters.ChatType.GROUPS),
        edit_input,
    ), group=-1)
    app.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS, on_new_members))
    app.add_handler(MessageHandler(filters.StatusUpdate.LEFT_CHAT_MEMBER, on_left_member))
    app.add_handler(MessageHandler(~filters.COMMAND & ~filters.StatusUpdate.ALL, watcher))
    # /stats (Bot Owner only): group list with Open / Remove buttons. Own handler groups (-30, 40, 41)
    # so none of the existing handlers is replaced or shadowed; none of these ever stops an update.
    app.add_handler(CommandHandler("stats", stats_cmd))
    app.add_handler(CallbackQueryHandler(stats_callback, pattern=r"^stats:"))
    app.add_handler(MessageHandler(filters.ChatType.GROUPS, stats_record), group=-30)
    app.add_handler(ChatMemberHandler(stats_member_update, ChatMemberHandler.MY_CHAT_MEMBER), group=40)
    app.add_handler(MessageHandler(filters.StatusUpdate.MIGRATE, stats_migrate), group=41)
    instrument_handlers(app)
    # Set DROP_PENDING_UPDATES=1 to skip the backlog that piled up while the bot was offline
    # (otherwise a restart first replays every old message, which feels like lag).
    app.run_polling(allowed_updates=Update.ALL_TYPES,
                    drop_pending_updates=bool(os.environ.get("DROP_PENDING_UPDATES")))


if __name__ == "__main__":
    main()

