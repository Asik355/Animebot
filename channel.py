"""
channel.py - everything about Telegram CHANNELS lives in this one file.

  1. LOG CHANNEL system (Owner only): /setlog /unsetlog /logchannel /logdefault /logroute /unlogroute /logroutes
     /logcategories /log /nolog /addcategory /removecategory /logmap /unlogmap /logmappings, the 1-minute batching
     worker, the Owner's Yes/No "upload this log?" prompts, security logging and the post-command log hook.
     This code was MOVED here from bot.py without any change in behaviour (the section starting at
     "LOG CHANNEL (Owner only)" below is the old bot.py text; only the three new command names were added to
     LOG_IGNORED_COMMANDS / LOG_COMMANDS).

  2. CHARACTER CHANNEL (Owner only): a separate channel that gets a post for every character, evolution and weapon
     that is added, edited or given a new photo.  /setcharchannel /charchannel /delcharchannel.
     It is independent of the log channels above.  Nothing is posted until a channel is set.

How the main files hook up (nothing else is needed):
  bot.py     import channel
             channel.bind(**{name: globals()[name] for name in channel.NEEDS})     # once, in main()
             channel.register(app)                                                 # from register_log_and_rules_commands(app)
             COMMANDS.update(channel.COMMAND_DESCRIPTIONS), OWNER_COMMANDS |= channel.OWNER_COMMANDS,
             the /help "📡 Log Channel" page appends channel.HELP_ROWS
             await channel.post(context, "char_new" | "char_edit" | "photo", ...)  next to the staff notifications
  fusion.py  import channel
             await channel.post(context, "evo_new" | "evo_edit" | "weapon_new" | "weapon_edit", ...)

bot.py is never imported from here (that would load the 800 KB file twice); the few bot.py helpers this module
needs are injected by bind() exactly like fusion.bind() / rewards.bind() do.
"""
import asyncio
import html
import os
import re
import time
import uuid
from datetime import datetime, timezone
from types import SimpleNamespace

from telegram import InlineKeyboardButton
from telegram.error import RetryAfter
from telegram.ext import CallbackQueryHandler, CommandHandler, MessageHandler, filters

import mongo_db

# ---------------------------------------------------------------------------------------------------------
# Dependencies that live in bot.py (injected by bind(); the names are used exactly as they were in bot.py).
#   ADMIN_IDS, SYMBOL, COMMANDS ........ bot.py data (Owner id, rarity -> emoji, documented command list)
#   IST, SCOUT_IDS ..................... time zone and the in-memory Scout list
#   InlineKeyboardMarkup ............... bot.py's subclass (max 3 buttons per row)
#   is_owner / is_executive / is_scout . role checks
#   safe_reply_text, display_user, copyable_ids, log_time_text, timestamp ... message / text helpers
#   _CMD_FAILED, _CMD_OK, _purge_cmd_state ... the command outcome book-keeping used by the log pipeline
# ---------------------------------------------------------------------------------------------------------
NEEDS = (
    "ADMIN_IDS", "COMMANDS", "IST", "InlineKeyboardMarkup", "SCOUT_IDS", "SYMBOL", "UNAUTHORIZED_TEXT",
    "_CMD_FAILED", "_CMD_OK", "_purge_cmd_state", "copyable_ids", "display_user", "is_executive", "is_owner",
    "is_scout", "log_time_text", "safe_reply_text", "timestamp",
)

# Same text as bot.py's UNAUTHORIZED_TEXT. It is needed while this file is imported (LOG_DENIED below is computed at
# import time); bind() then replaces it with the real bot.py object.
UNAUTHORIZED_TEXT = "⚠️ Access Denied: You do not have permission to perform this action."


def bind(**kwargs):
    """Inject the bot.py helpers listed in NEEDS."""
    unknown = sorted(set(kwargs) - set(NEEDS))
    if unknown:
        raise TypeError("channel.bind() got unexpected names: " + ", ".join(unknown))
    globals().update(kwargs)


def _check_bound():
    missing = [name for name in NEEDS if name not in globals()]
    if missing:
        raise RuntimeError("channel.bind() was not called with: " + ", ".join(missing))


# ==========================================================================
# LOG CHANNEL (Owner only)   (moved here from bot.py - the bot rules stay in bot.py)
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
# Multi-step flows: the log entry is held until the LAST step succeeds. A flow that is cancelled, abandoned or
# times out never produces a log (pending entries are purged after CONV_LOG_TTL).
CONVERSATION_LOG_COMMANDS = {"addevent", "endevent", "addredeem", "addcharacter", "editcharacter"}
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
    "setcharchannel", "charchannel", "delcharchannel",
    "logmap", "unlogmap", "logmappings", "logroute", "unlogroute", "logroutes", "logdefault",
    # Range commands: read-only ones are never logged; /setrange and /delrange are logged by log_range_change()
    # (Executive: Yes/No prompt after the whole action succeeded; Owner: never).
    "range", "ranges", "freecode", "freecodes", "nextcode", "setrange", "delrange", "fillranges", "undocodes",
} | {c.strip().lstrip("/").lower() for c in os.getenv("LOG_IGNORED_EXTRA", "").split(",") if c.strip()}
LOG_COMMANDS = {"setlog", "unsetlog", "log", "nolog", "logcategories", "logchannel", "addcategory", "removecategory",
                "logmap", "unlogmap", "logmappings", "logroute", "unlogroute", "logroutes", "logdefault",
                "setcharchannel", "charchannel", "delcharchannel"}
COMMAND_NAME_RE = re.compile(r"^[a-z0-9_]{1,32}$")   # Telegram command syntax
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


# ==========================================================================
# CHARACTER CHANNEL (Owner only)
#   A separate channel that gets one post for every character / evolution / weapon that is added, edited or given
#   a new photo.  Independent of the log channels.  Nothing is posted until a channel is set (/setcharchannel).
#   Posts: photo above the text (a photo caption), bold labels, names and user IDs as plain text (never @username,
#   so nobody is tagged).  Posting never delays or breaks the action that triggered it: it runs in its own task,
#   and when it fails the Owner gets ONE short DM (the item itself is always saved first).
# ==========================================================================
CHAR_CHANNEL_COL = "char_channel_v1"       # one document {_id: 1, chat_id, title, username, enabled, set_by, set_at}
CHAR_CHANNEL_DOC_ID = 1
CHAR_CHANNEL_TTL = 30.0                    # seconds the saved setting is cached
CHAR_CLAIM_TTL = 600.0                     # a "/setcharchannel sent in a channel" request waits 10 minutes for the Owner
CHAR_CLAIM_MAX = 20
CHAR_SEND_ATTEMPTS = 3
CAPTION_LIMIT = 1024                       # Telegram's limit for a photo caption
MESSAGE_LIMIT = 4096
CHAR_POST_FAILED_TEXT = "I could not post to the character channel. Check that I am an admin there."

_CC = {"ts": 0.0, "val": None, "loaded": False, "gen": 0}
_CC_TASKS = set()

COMMAND_DESCRIPTIONS = {
    # --- log channel system (moved from bot.py's COMMANDS table, same texts)
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
    # --- character channel
    "setcharchannel": "Owner: set the character channel (send it in the channel, or /setcharchannel <id or @username>)",
    "charchannel": "Owner: show the character channel and ON/OFF (/charchannel on or off to pause or resume)",
    "delcharchannel": "Owner: remove the character channel",
}
OWNER_COMMANDS = set(COMMAND_DESCRIPTIONS)

# Rows appended to the "📡 Log Channel" page of /help -> Owner Commands.
HELP_ROWS = [
    ("/setcharchannel", "Set the character channel: send it in the channel, then confirm in private chat "
                        "(or /setcharchannel <id or @username> here)"),
    ("/charchannel [on|off]", "Show the character channel and ON/OFF, or pause / resume its posts"),
    ("/delcharchannel", "Remove the character channel"),
]


# ---- saved setting (MongoDB) -------------------------------------------------------------------------------
def _cc_col():
    return mongo_db.col(CHAR_CHANNEL_COL)


def _cc_read():
    return _cc_col().find_one({"_id": CHAR_CHANNEL_DOC_ID})


def _cc_write(chat_id, title, username, user_id):
    _cc_col().update_one(
        {"_id": CHAR_CHANNEL_DOC_ID},
        {"$set": {"chat_id": int(chat_id), "title": title or "", "username": username or "", "enabled": True,
                  "set_by": int(user_id), "set_at": timestamp()}},
        upsert=True)


def _cc_set_enabled(flag):
    return _cc_col().update_one({"_id": CHAR_CHANNEL_DOC_ID}, {"$set": {"enabled": bool(flag)}}).matched_count


def _cc_delete():
    return _cc_col().delete_one({"_id": CHAR_CHANNEL_DOC_ID}).deleted_count


def _cc_invalidate():
    """Drop the cached setting now; the generation bump stops an older read from re-filling the cache."""
    _CC["loaded"] = False
    _CC["gen"] += 1


async def get_char_channel():
    """The saved character channel {chat_id, title, username, enabled, set_by, set_at} or None (cached 30 s)."""
    if _CC["loaded"] and time.monotonic() - _CC["ts"] < CHAR_CHANNEL_TTL:
        return _CC["val"]
    val = _CC["val"]
    for _attempt in range(2):
        gen = _CC["gen"]
        try:
            val = await asyncio.to_thread(_cc_read)
        except Exception as e:
            print("Character channel config load error:", e)
            return _CC["val"]
        if gen == _CC["gen"]:
            _CC.update(ts=time.monotonic(), val=val, loaded=True)
            return val
    return val


# ---- post text ----------------------------------------------------------------------------------------------
def _plain(value, limit=None):
    """Single-line plain text. A zero-width character after every '@' (same as bot.py's _no_tag) so no name can become a mention."""
    text = " ".join(str(value if value is not None else "").split()).replace("@", "@\u200b")
    if limit and len(text) > limit:
        text = text[:limit - 1].rstrip() + "…"
    return text


def _esc(value, limit=None):
    return html.escape(_plain(value, limit), quote=False)


def _tier(rarity):
    """'Mythical 🔮' (the rarity name, then its emoji)."""
    name = str(rarity or "").strip()
    if not name:
        return "Not set"
    symbol = (SYMBOL or {}).get(name)
    return f"{name} {symbol}" if symbol else name


def _num(value):
    try:
        return f"{int(str(value).replace(',', '').strip()):,}"
    except (TypeError, ValueError):
        return str(value if value is not None else "").strip()


_NUMERIC_KEYS = {"worth", "price", "stones", "berries"}
_LABELS = {"name": "Name", "code": "Code", "tier": "Tier", "series": "Series", "worth": "Worth",
           "recruits": "Recruiting Names", "type": "Type", "price": "Shop price", "recipe": "Recipe",
           "stones": "Evolution Stones", "berries": "Berries", "photo": "Photo"}
_DIFF_KEYS = {
    "char": ("name", "code", "tier", "series", "worth", "recruits", "photo"),
    "evo": ("name", "code", "tier", "series", "worth", "recipe", "stones", "berries", "photo"),
    "weapon": ("name", "code", "type", "series", "tier", "price", "photo"),
}
_ROWS = {                        # the lines of a post, in order: (label key, field limit)
    "char": (("name", 80), ("code", 10), ("tier", 40), ("series", 80), ("worth", 20), ("recruits", 200)),
    "evo": (("name", 80), ("code", 10), ("tier", 40), ("series", 80), ("worth", 20), ("recipe", 260),
            ("stones", 20), ("berries", 20)),
    "weapon": (("name", 80), ("code", 10), ("type", 60), ("series", 80), ("tier", 40), ("price", 20)),
}
_TITLES = {
    "char_new": "🆕 <b>New Character Added</b>", "char_edit": "✏️ <b>Character Updated</b>",
    "evo_new": "🧬 <b>New Evolution Added</b>", "evo_edit": "✏️ <b>Evolution Updated</b>",
    "weapon_new": "⚔️ <b>New Weapon Added</b>", "weapon_edit": "✏️ <b>Weapon Updated</b>",
    "photo": "📷 <b>Photo Updated</b>",
}
_BASE_OF = {"char_new": "char", "char_edit": "char", "evo_new": "evo", "evo_edit": "evo",
            "weapon_new": "weapon", "weapon_edit": "weapon"}


def _norm(key, value):
    """The comparable text of one field."""
    if key == "recruits" and not isinstance(value, str):             # a list of names (a string is already joined)
        return ", ".join(str(x).strip() for x in (value or []) if str(x).strip())
    return "" if value is None else str(value).strip()


def _fmt(key, value):
    """The shown text of one field (plain, not yet escaped)."""
    text = _norm(key, value)
    if key == "tier":
        return _tier(text)
    if key == "recruits":
        return text or "None"
    if key == "price":
        return _num(text) if text not in ("", "0") else "Not in shop"
    if key in _NUMERIC_KEYS and text:
        return _num(text)
    return text or "Not set"


def _view(base, obj):
    """One item as {name, code, tier, series, worth, ...}. A weapon may be given as its raw database document."""
    obj = dict(obj or {})
    if base == "weapon":
        return {"name": obj.get("name"), "code": obj.get("_id") or obj.get("code"), "type": obj.get("type"),
                "series": obj.get("anime"), "tier": obj.get("rarity"), "price": obj.get("shop_price"),
                "photo": obj.get("photo")}
    if obj.get("code") is not None:
        obj["code"] = str(obj["code"])
    return obj


def _diff(old, new, keys):
    """[(key, old text, new text)] for the fields that BOTH sides report and that differ."""
    out = []
    for key in keys:
        if key not in old or key not in new:
            continue
        before, after = _norm(key, old[key]), _norm(key, new[key])
        if before != after:
            out.append((key, before, after))
    return out


def _actor_text(user):
    """'Name (user id)' as plain text - never @username."""
    if user is None:
        return "Unknown"
    first, last = (getattr(user, "first_name", None) or "").strip(), (getattr(user, "last_name", None) or "").strip()
    name = " ".join(part for part in (first, last) if part) or "Unknown"
    uid = getattr(user, "id", None)
    return f"<i>{_esc(name, 60)}</i>" + (f" ({int(uid)})" if uid is not None else "")


def _changed_text(changes):
    parts = []
    for key, before, after in changes:
        if key == "photo":
            parts.append("Photo updated")
            continue
        parts.append(f"{_LABELS[key]} {_fmt(key, before) if before else '—'} → {_fmt(key, after) if after else '—'}")
    return html.escape(_plain(", ".join(parts), 450), quote=False)


def _compose(kind, base, item, photo, changes, actor):
    """{text (HTML), plain, photo} for one post."""
    lines = [_TITLES[kind], ""]
    if kind == "photo":
        lines.append(f"<b>Name:</b> {_esc(item.get('name'), 80) or 'Unknown'}")
        lines.append(f"<b>Code:</b> {_esc(item.get('code'), 10)}")
    else:
        for key, limit in _ROWS[base]:
            if key == "recipe":
                value = _plain(f"{item.get('recipe') or '?'} ➡️ {item.get('name') or '?'}", limit)
            else:
                value = _plain(_fmt(key, item.get(key)), limit)
            lines.append(f"<b>{_LABELS[key]}:</b> {html.escape(value, quote=False)}")
    lines.append("")
    if changes:
        lines.append(f"<b>Changed:</b> {_changed_text(changes)}")
    lines.append(f"<b>{'Added' if kind.endswith('_new') else 'Updated'} by:</b> {_actor_text(actor)}")
    text = "\n".join(lines)
    plain = html.unescape(re.sub(r"<[^>]+>", "", text))
    return {"text": text, "plain": plain, "photo": photo or None}


def build_post(kind, **data):
    """
    The post for one event, or None when there is nothing to post.
      char_new / evo_new / weapon_new      new=<item>, actor=<telegram user>, photo=<file id, optional>
      char_edit / evo_edit / weapon_edit   old=<item>, new=<item>, actor=..., photo=...   (only the changed fields are
                                           listed; a change of the photo alone becomes a "Photo Updated" post;
                                           no change at all = no post)
      photo                                name=, code=, photo=, actor=
    char/evo items are dicts with name, code, tier (rarity name), series, worth, recruits (list, characters) or
    recipe (ingredients text), stones, berries (evolutions); a weapon is its database document.
    """
    actor = data.get("actor")
    if kind == "photo":
        item = {"name": data.get("name"), "code": data.get("code")}
        return _compose("photo", None, item, data.get("photo"), [], actor)
    base = _BASE_OF.get(kind)
    if base is None:
        return None
    new = _view(base, data.get("new"))
    photo = new.get("photo") or data.get("photo")
    if kind.endswith("_new"):
        return _compose(kind, base, new, photo, [], actor)
    changes = _diff(_view(base, data.get("old")), new, _DIFF_KEYS[base])
    if not changes:
        return None
    if [c[0] for c in changes] == ["photo"]:
        return _compose("photo", None, new, photo, [], actor)
    return _compose(kind, base, new, photo, changes, actor)


# ---- sending ------------------------------------------------------------------------------------------------
def _retry_delay(error):
    delay = getattr(error, "retry_after", 5)
    return (delay.total_seconds() if hasattr(delay, "total_seconds") else float(delay)) + 0.5


async def _send_item(bot, chat_id, item):
    """Photo + caption (or text only). True when delivered."""
    text, plain, photo = item["text"], item["plain"], item.get("photo")
    mode = {"parse_mode": "HTML"}
    if len(plain) > CAPTION_LIMIT:
        text, mode = plain[:CAPTION_LIMIT - 1].rstrip() + "…", {}           # too long for a caption: plain, shortened
    for _attempt in range(CHAR_SEND_ATTEMPTS):
        try:
            if photo:
                try:
                    await bot.send_photo(chat_id=chat_id, photo=photo, caption=text, **mode)
                    return True
                except (RetryAfter, asyncio.CancelledError):
                    raise
                except Exception as e:                                       # e.g. an expired file id: post the text
                    print("Character channel photo failed, posting text only:", repr(e))
            if len(item["text"]) <= MESSAGE_LIMIT:
                await bot.send_message(chat_id=chat_id, text=item["text"], parse_mode="HTML")
            else:                                                            # (practically never) too long: plain, shortened
                await bot.send_message(chat_id=chat_id, text=plain[:MESSAGE_LIMIT - 1].rstrip() + "…")
            return True
        except RetryAfter as e:
            delay = _retry_delay(e)
            print(f"Character channel rate limited: retrying in {delay:.1f}s")
            await asyncio.sleep(delay)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            print(f"Character channel send error ({chat_id}):", repr(e))
            return False
    print(f"Character channel post dropped after {CHAR_SEND_ATTEMPTS} rate-limited attempts ({chat_id})")
    return False


async def _notify_post_failed(bot):
    """The one short DM to the Owner."""
    try:
        owner = ADMIN_IDS[0] if ADMIN_IDS else None
        if owner is not None:
            await bot.send_message(chat_id=int(owner), text=CHAR_POST_FAILED_TEXT)
    except Exception as e:
        print("Character channel failure DM error:", repr(e))


async def _deliver(bot, chat_id, item):
    delivered = False
    try:
        delivered = await _send_item(bot, chat_id, item)
    except asyncio.CancelledError:
        raise
    except Exception as e:
        print("Character channel post error:", repr(e))
    if not delivered:
        await _notify_post_failed(bot)


async def post(context, kind, **data):
    """
    Queue one character-channel post (see build_post for the kinds and fields). NEVER raises and never waits for
    Telegram: call it AFTER the item is saved. Returns True when a post was queued; False when no channel is set,
    posting is OFF, or there was nothing to post.
    """
    try:
        cfg = await get_char_channel()
        if not cfg or not cfg.get("enabled") or cfg.get("chat_id") is None:
            return False
        item = build_post(kind, **data)
        if item is None:
            return False
        bot = getattr(context, "bot", context)
        task = asyncio.get_running_loop().create_task(_deliver(bot, int(cfg["chat_id"]), item))
        _CC_TASKS.add(task)
        task.add_done_callback(_CC_TASKS.discard)
        return True
    except Exception as e:
        print("Character channel post error:", repr(e))
        return False


# ---- Owner commands -----------------------------------------------------------------------------------------
def _cc_label(cfg):
    return f"{cfg.get('title') or 'Unnamed'} ({cfg.get('chat_id')})"


def _cc_purge_claims(pending):
    now = time.monotonic()
    for token in [t for t, c in pending.items() if now - c.get("ts", 0) > CHAR_CLAIM_TTL]:
        pending.pop(token, None)
    if len(pending) > CHAR_CLAIM_MAX:
        for token in sorted(pending, key=lambda t: pending[t].get("ts", 0))[:len(pending) - CHAR_CLAIM_MAX]:
            pending.pop(token, None)


async def _cc_link(bot, chat, user_id):
    """Test-post in the chat and save it as the character channel. Returns (ok, text for the Owner)."""
    status, can_post = "unknown", None
    try:
        member = await bot.get_chat_member(chat.id, bot.id)
        status, can_post = _member_status(member), getattr(member, "can_post_messages", None)
    except Exception as e:
        print("setcharchannel get_chat_member error:", repr(e))
    if status in ("left", "kicked"):
        return False, (f"❌ I'm not a member of that chat (my status: {status}). "
                       "Add me as an Administrator with permission to post, then try again.")
    try:
        await bot.send_message(chat_id=chat.id, text="✅ Character channel linked. New characters, evolutions and "
                                                     "weapons will be posted here.")
    except Exception as e:
        return False, ("❌ I could not post in that chat.\n"
                       f"Telegram says: {e}\n"
                       f"My status there: {status}; can post messages: {can_post if can_post is not None else 'not reported'}.\n"
                       "Make sure I am an Administrator with the 'Post messages' permission.")
    title, username = getattr(chat, "title", None) or "", getattr(chat, "username", None) or ""
    await asyncio.to_thread(_cc_write, chat.id, title, username, user_id)
    _cc_invalidate()
    return True, f"✅ Character channel set: {title or chat.id} ({chat.id})\n📡 Posting is ON (see /charchannel)."


async def _cc_claim_from_channel(update, context):
    """
    /setcharchannel posted INSIDE the channel. The poster of a channel post is anonymous, so the Owner cannot be
    verified here: the Owner confirms with one tap in private chat (otherwise anybody who adds the bot to a channel
    could redirect the posts).
    """
    msg = update.effective_message
    owner = ADMIN_IDS[0] if ADMIN_IDS else None
    if msg is None or owner is None:
        return
    chat = msg.chat
    pending = context.application.bot_data.setdefault("char_channel_claims", {})
    _cc_purge_claims(pending)
    now = time.monotonic()
    if any(c["chat_id"] == chat.id and now - c["ts"] < 60 for c in pending.values()):
        return                                                    # the same request is already waiting
    token = uuid.uuid4().hex[:16]
    pending[token] = {"chat_id": chat.id, "title": getattr(chat, "title", None) or "",
                      "username": getattr(chat, "username", None) or "", "ts": now}
    try:
        await context.bot.send_message(
            chat_id=chat.id, text="⏳ Waiting for the Bot Owner to confirm this channel in private chat.")
    except Exception as e:
        print("setcharchannel channel reply error:", repr(e))
    try:
        await context.bot.send_message(
            chat_id=owner,
            text=f"📣 /setcharchannel was sent in this channel:\n\n{pending[token]['title'] or 'Unnamed'} ({chat.id})\n\n"
                 "Use it as the character channel?",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("✅ Confirm", callback_data=f"cc:y:{token}"),
                                                InlineKeyboardButton("❌ Cancel", callback_data=f"cc:n:{token}")]]))
    except Exception as e:
        pending.pop(token, None)
        print("setcharchannel owner prompt error:", repr(e))


async def charchannel_claim_callback(update, context):
    query = update.callback_query
    if not is_owner(query.from_user.id):
        await deny_callback(query)
        return
    try:
        _, choice, token = query.data.split(":", 2)
    except ValueError:
        await query.answer(PROMPT_EXPIRED, show_alert=True)
        return
    pending = context.application.bot_data.setdefault("char_channel_claims", {})
    _cc_purge_claims(pending)
    claim = pending.pop(token, None)
    if claim is None:
        await query.answer(PROMPT_EXPIRED, show_alert=True)
        try:
            await query.message.delete()
        except Exception:
            pass
        return
    if choice == "n":
        await query.answer("Cancelled.")
        try:
            await query.edit_message_text("❌ Cancelled. The character channel was not changed.")
        except Exception:
            pass
        return
    chat = SimpleNamespace(id=claim["chat_id"], title=claim["title"], username=claim["username"])
    ok, text = await _cc_link(context.bot, chat, query.from_user.id)
    await query.answer("Done." if ok else "Not set.", show_alert=not ok)
    try:
        await query.edit_message_text(text)
    except Exception:
        pass


async def setcharchannel_command(update, context):
    """
    /setcharchannel   - Owner: set the character channel.
      * sent inside the channel (the bot is an admin with 'Post messages'): the Owner then confirms in private chat
      * /setcharchannel <channel id or @username> in the Owner's private chat
    Linking succeeds when a real test post succeeds.
    """
    msg = update.effective_message
    if msg is None:
        return
    if msg.chat.type == "channel":
        await _cc_claim_from_channel(update, context)
        return
    if not await _owner_only_log(update):
        return
    chat = None
    if context.args:
        try:
            chat = await _log_target_from_args(context)
        except Exception as e:
            await safe_reply_text(msg, f"❌ I can't find that chat. Add me to it as an Administrator first.\n({e})")
            return
    if chat is None:
        await safe_reply_text(
            msg,
            "📡 Set the character channel:\n"
            "1. Add me to the channel as an Administrator with permission to post messages.\n"
            "2. Send /setcharchannel inside that channel, then tap ✅ Confirm in the message I send you here.\n\n"
            "Or send: /setcharchannel <channel id or @username>  (e.g. /setcharchannel -1001234567890)")
        return
    ok, text = await _cc_link(context.bot, chat, update.effective_user.id)
    await safe_reply_text(msg, text)


async def charchannel_command(update, context):
    """/charchannel - show the character channel and ON/OFF.  /charchannel on | off - resume / pause the posts."""
    if not await _owner_only_log(update):
        return
    msg = update.effective_message
    arg = context.args[0].strip().lower() if context.args else ""
    if arg not in ("", "on", "off") or len(context.args or []) > 1:
        await safe_reply_text(msg, "Usage: /charchannel   or   /charchannel on   or   /charchannel off")
        return
    _cc_invalidate()
    cfg = await get_char_channel()
    if not cfg or cfg.get("chat_id") is None:
        await safe_reply_text(msg, "ℹ️ No character channel is set.\nUse /setcharchannel (see /help → Owner Commands).")
        return
    if arg:
        await asyncio.to_thread(_cc_set_enabled, arg == "on")
        _cc_invalidate()
        await safe_reply_text(msg, f"✅ Character channel posting is now {'ON' if arg == 'on' else 'OFF'}: {_cc_label(cfg)}")
        return
    handle = f"@{cfg['username']}" if cfg.get("username") else "private"
    await safe_reply_text(
        msg,
        f"📡 Character Channel\n\n{cfg.get('title') or 'Unnamed'}\n    ID: {cfg.get('chat_id')} · {handle}\n"
        f"    Linked: {cfg.get('set_at', '?')}\n"
        f"    Status: {'✅ ON' if cfg.get('enabled') else '⏸ OFF (paused)'}\n\n"
        "Manage: /setcharchannel · /charchannel on|off · /delcharchannel")


async def delcharchannel_command(update, context):
    """/delcharchannel - remove the character channel (nothing is posted until a new one is set)."""
    if not await _owner_only_log(update):
        return
    msg = update.effective_message
    _cc_invalidate()
    cfg = await get_char_channel()
    if not cfg or cfg.get("chat_id") is None:
        await safe_reply_text(msg, "ℹ️ No character channel is set.")
        return
    label = _cc_label(cfg)
    await asyncio.to_thread(_cc_delete)
    _cc_invalidate()
    await safe_reply_text(msg, f"✅ Character channel removed: {label}\nNothing is posted until you set one again.")


# ==========================================================================
# REGISTRATION (called once from bot.py: register_log_and_rules_commands -> channel.register(app))
# ==========================================================================
def register(app):
    _check_bound()
    for name, callback in (
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
    # character channel
    for name, callback in (("setcharchannel", setcharchannel_command), ("charchannel", charchannel_command),
                           ("delcharchannel", delcharchannel_command)):
        app.add_handler(CommandHandler(name, callback))
    app.add_handler(MessageHandler(
        filters.UpdateType.CHANNEL_POSTS & filters.Regex(r"^/setcharchannel(@\w+)?(\s|$)"), setcharchannel_command))
    app.add_handler(CallbackQueryHandler(charchannel_claim_callback, pattern=r"^cc:[yn]:"))
