"""
fusion.py - Special Stone Daily Task System
===========================================

Self-contained module. bot.py only needs:
    import fusion
    fusion.register(app)                              # in main(), after public_handlers
    await fusion.record_catch(user_id, rarity, code)  # in add(), after a successful catch
    await fusion.record_sell(user_id, rarity, qty)    # in sell(), after sell_copies returned ok

Storage (same MongoDB database as the rest of the bot, through the existing mongo_db helpers):
    users.special_stones      existing `users` document, atomic $inc ($inc creates the field)
    stone_tasks               one doc per user per IST day, _id = "<user_id>:<YYYY-MM-DD>"
    stone_daily               one doc per IST day, _id = "<YYYY-MM-DD>", holds the /add target codes
    (collection names + creation live in the Fusion section of mongo_db.py)

Daily reset (02:00 AM IST):
    The "day key" is derived from UTC + 5:30 with a 02:00 cutoff, never from the server's local
    timezone. Every read/write is addressed by the current day key, so after the cutoff the
    previous day's documents are never read or claimed again: progress restarts at 0, unclaimed
    rewards simply expire (there is no pending balance), and a new target is generated lazily on
    first use. Expired documents are purged once per process per day to keep the DB small.

Evolution system (same file, second half): /addevo (Owner+Executive), /evolution (everyone), /evolve (everyone),
/delevo (Owner only). Evolution characters live in the normal `characters` collection with char_type = EVOLUTION; recipes live in
`evolution_recipes` (one recipe per base character, _id = evolution character code). Evolution Stones = the same
`users.special_stones` field the stone tasks pay into. See the "EVOLUTION SYSTEM" section below.

Weapons (last section): weapon items, /weaponshop, group weapon drops and the weapon slot of an evolution recipe (/evoweapon);
bot.py only merges fusion.WEAPON_*_COMMANDS / WEAPON_COMMAND_DESCRIPTIONS into its command lists.

Stone task reminders (stone_remind) + Daily Missions (/dailytask) are the last sections of this file: separate system, independent of /daily and of the stone tasks.
    Hooks: dt_record_catch(...) in add(), dt_record_purchase(...) in the shop. See the DAILY MISSIONS section.

Claiming:
    claim_all() is the ONLY claim logic; the button and /claimstone both call it. For each
    completed task it runs one conditional update ("completed AND not yet claimed" -> claimed).
    Only tasks whose update really flipped the flag are paid, and the stone $inc happens in the
    same transaction (mongo_db.run_transaction). Concurrent / repeated claims therefore cannot
    pay the same task twice.
"""

import asyncio
import logging
import random
from collections import namedtuple
from datetime import datetime, timedelta, timezone

import mongo_db
import rewards  # Mystery Box lines for /item (rewards.item_lines)

logger = logging.getLogger(__name__)

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------
IST = timezone(timedelta(hours=5, minutes=30))   # fixed UTC+5:30, independent of server TZ
RESET_HOUR_IST = 2                               # daily reset at 02:00 AM IST

# Collection names are defined in mongo_db.py (Fusion section); collections + index are created at startup
# by mongo_db.ensure_fusion_collections(), called from mongo_db.ensure_indexes().
TASKS_COL = mongo_db.FUSION_STONE_TASKS
DAILY_COL = mongo_db.FUSION_STONE_DAILY
USERS_COL = "users"

# Rarities the daily /add target may be picked from. Celestial/Ethereal/Mythical/Legendary are excluded
# on purpose: they have daily spawn limits, so a target could be impossible to catch.
ADD_TASK_RARITIES = ("Common", "Rare", "Epic")

# (key, emoji, title, needed, reward) - simple "catch N" tasks, counted from successful /add catches
CATCH_TASKS = (
    ("catch", "🎯", "Catch 20 Characters", 20, 1),
    ("epic", "🟣", "Catch 10 Epic Characters", 10, 1),
    ("legendary", "🟡", "Catch 1 Legendary Character", 1, 3),
    ("mythical", "🔴", "Catch 1 Mythical Character", 1, 5),
    ("celestial", "🌟", "Catch 1 Celestial Character", 1, 10),
)
SELL_REWARD = 1
SELL_COMMON_NEEDED = 15
SELL_RARE_NEEDED = 5
ADD_REWARD = 10

# Order shown in /stonetask and used when claiming
TASK_ORDER = ("catch", "epic", "legendary", "mythical", "celestial", "sell", "add")
REWARDS = {t[0]: t[4] for t in CATCH_TASKS}
REWARDS["sell"] = SELL_REWARD
REWARDS["add"] = ADD_REWARD
# Collection Add resets DAILY (02:00 AM IST); every other task resets WEEKLY (Monday 02:00 AM IST).
DAILY_KEYS = ("add",)
WEEKLY_KEYS = tuple(k for k in TASK_ORDER if k not in DAILY_KEYS)
TITLES = {t[0]: f"{t[1]} {t[2]}" for t in CATCH_TASKS}
TITLES["sell"] = "⚪🔵 Sell 15 Common + 5 Rare Characters"
TITLES["add"] = "📚 Collection Add Task"
NEEDED = {t[0]: t[3] for t in CATCH_TASKS}
NEEDED["add"] = 1

# rarity (lower-case) -> progress key for the rarity-specific catch tasks
_RARITY_KEYS = {"epic": "epic", "legendary": "legendary", "mythical": "mythical", "celestial": "celestial"}

RARITY_SYMBOLS = {"Common": "⚪", "Rare": "🔵", "Epic": "🟣", "Legendary": "🟡", "Mythical": "🔴", "Ethereal": "🌠", "Celestial": "🌟"}


# --------------------------------------------------------------------------
# Time helpers (IST day with a 02:00 cutoff)
# --------------------------------------------------------------------------
def _now():
    return datetime.now(timezone.utc)


def current_day_key(now=None):
    """IST 'task day' as YYYY-MM-DD. Before 02:00 IST we are still in the previous task day."""
    ist = (now or _now()).astimezone(IST)
    day = ist.date() if ist.hour >= RESET_HOUR_IST else (ist - timedelta(days=1)).date()
    return day.isoformat()


def current_week_key(now=None):
    """Monday (YYYY-MM-DD) of the current IST task week; the week rolls over Monday 02:00 AM IST."""
    day = datetime.fromisoformat(current_day_key(now)).date()
    return (day - timedelta(days=day.weekday())).isoformat()


def next_weekly_reset(now=None):
    """The next Monday 02:00 AM IST moment (timezone-aware)."""
    ist = (now or _now()).astimezone(IST)
    monday = datetime.fromisoformat(current_week_key(now)).date() + timedelta(days=7)
    return datetime(monday.year, monday.month, monday.day, RESET_HOUR_IST, tzinfo=IST)


def _fmt_secs(secs):
    secs = max(0, int(secs))
    days, rem = divmod(secs, 86400)
    hours, minutes = rem // 3600, (rem % 3600) // 60
    if days == 0 and hours == 0 and minutes == 0:
        return "less than 1m"
    return (f"{days}d " if days else "") + f"{hours}h {minutes}m"


def format_weekly_countdown(now=None):
    now = now or _now()
    return _fmt_secs((next_weekly_reset(now) - now.astimezone(IST)).total_seconds())


def next_reset(now=None):
    """The next 02:00 AM IST moment (timezone-aware)."""
    ist = (now or _now()).astimezone(IST)
    reset = ist.replace(hour=RESET_HOUR_IST, minute=0, second=0, microsecond=0)
    if ist >= reset:
        reset += timedelta(days=1)
    return reset


def format_countdown(now=None):
    """'7h 25m' until the next reset."""
    now = now or _now()
    secs = max(0, int((next_reset(now) - now.astimezone(IST)).total_seconds()))
    hours, minutes = secs // 3600, (secs % 3600) // 60
    if hours == 0 and minutes == 0:
        return "less than 1m"
    return f"{hours}h {minutes}m"


# --------------------------------------------------------------------------
# Database helpers (blocking - always call through asyncio.to_thread from handlers)
# --------------------------------------------------------------------------
_state = {"day": None, "codes": None}


def _tasks():
    return mongo_db.col(TASKS_COL)


def _task_id(user_id, day):
    return f"{int(user_id)}:{day}"


def _week_id(user_id, week):
    return f"{int(user_id)}:W{week}"


def _purge_expired(day):
    """Permanently drop previous days' tasks/targets (they can never be claimed again anyway)."""
    try:
        _tasks().delete_many({"day": {"$lt": day}})
        _tasks().delete_many({"week": {"$lt": current_week_key()}})
        mongo_db.col(DAILY_COL).delete_many({"_id": {"$lt": day}})
    except Exception as e:
        logger.warning("stone task purge failed: %s", e)


def _pick_targets():
    """1 or 2 random non-discontinued characters for today's Collection Add Task."""
    pool = []
    for rarity in ADD_TASK_RARITIES:
        pool.extend(mongo_db.get_characters_by_rarity(rarity))
    if not pool:
        return []
    count = min(random.choice((1, 2)), len(pool))
    return [row[0] for row in random.sample(pool, count)]


def get_targets(day=None):
    """Today's /add target codes. Created once per day (atomic $setOnInsert), cached per process."""
    day = day or current_day_key()
    if _state["day"] == day and _state["codes"] is not None:
        return list(_state["codes"])
    daily = mongo_db.col(DAILY_COL)
    doc = daily.find_one({"_id": day})
    if doc is None:
        _purge_expired(day)
        try:
            daily.update_one({"_id": day}, {"$setOnInsert": {"codes": _pick_targets()}}, upsert=True)
        except Exception as e:  # duplicate key from a concurrent first insert: someone else won, read theirs
            logger.info("stone_daily insert race: %s", e)
        doc = daily.find_one({"_id": day})
    codes = [str(c) for c in (doc or {}).get("codes", [])]
    _state["day"], _state["codes"] = day, codes
    return list(codes)


def _bump(user_id, daily_incs=None, weekly_incs=None):
    """Atomic progress increments: daily doc (Collection Add) and weekly doc (all other tasks)."""
    if daily_incs:
        day = current_day_key()
        _tasks().update_one(
            {"_id": _task_id(user_id, day)},
            {"$setOnInsert": {"user_id": int(user_id), "day": day}, "$inc": daily_incs},
            upsert=True,
        )
    if weekly_incs:
        week = current_week_key()
        _tasks().update_one(
            {"_id": _week_id(user_id, week)},
            {"$setOnInsert": {"user_id": int(user_id), "week": week}, "$inc": weekly_incs},
            upsert=True,
        )


def record_catch_sync(user_id, rarity, code):
    """Called after a successful /add catch. Duplicates count; only real rarity is used."""
    incs = {"progress.catch": 1}
    key = _RARITY_KEYS.get(str(rarity or "").strip().lower())
    if key:
        incs[f"progress.{key}"] = 1
    daily = {"progress.add": 1} if str(code) in get_targets() else None   # caught one of today's targets via /add
    _bump(user_id, daily, incs)


def record_sell_sync(user_id, rarity, quantity):
    """Called after a successful /sell. Only Common and Rare sales matter."""
    quantity = int(quantity)
    rarity = str(rarity or "").strip().lower()
    if quantity <= 0 or rarity not in ("common", "rare"):
        return
    _bump(user_id, None, {f"progress.sell_{rarity}": quantity})


async def record_catch(user_id, rarity, code):
    """Never raises: a stone-task problem must not break /add."""
    try:
        await asyncio.to_thread(record_catch_sync, user_id, rarity, code)
    except Exception as e:
        logger.error("stone task catch tracking failed: %s", e)


async def record_sell(user_id, rarity, quantity):
    """Never raises: a stone-task problem must not break /sell."""
    try:
        await asyncio.to_thread(record_sell_sync, user_id, rarity, quantity)
    except Exception as e:
        logger.error("stone task sell tracking failed: %s", e)


# --------------------------------------------------------------------------
# Completion rules (single source of truth, used by the UI and by the claim filters)
# --------------------------------------------------------------------------
def _claim_filter(user_id, day, key, week=None):
    """Mongo filter that matches ONLY if the task is completed AND not yet claimed."""
    doc_id = _task_id(user_id, day) if key in DAILY_KEYS else _week_id(user_id, week or current_week_key())
    flt = {"_id": doc_id, f"claimed.{key}": {"$ne": True}}
    if key == "sell":
        flt["progress.sell_common"] = {"$gte": SELL_COMMON_NEEDED}
        flt["progress.sell_rare"] = {"$gte": SELL_RARE_NEEDED}
    else:
        flt[f"progress.{key}"] = {"$gte": NEEDED[key]}
    return flt


def claim_all_sync(user_id):
    """
    Shared claim logic for the button AND /claimstone.
    Returns {"status": "ok"|"nothing"|"nouser", "keys": [...], "stones": int, "balance": int}.
    """
    user_id = int(user_id)
    day = current_day_key()
    week = current_week_key()
    if mongo_db.col(USERS_COL).find_one({"_id": user_id}, {"_id": 1}) is None:
        return {"status": "nouser", "keys": [], "stones": 0, "balance": 0}

    def _work(session):
        keys, total = [], 0
        for key in TASK_ORDER:
            res = _tasks().update_one(
                _claim_filter(user_id, day, key, week), {"$set": {f"claimed.{key}": True}}, session=session
            )
            if res.modified_count == 1:          # we (and only we) flipped it -> we pay it
                keys.append(key)
                total += REWARDS[key]
        if total:
            paid = mongo_db.col(USERS_COL).update_one(
                {"_id": user_id}, {"$inc": {"special_stones": total}}, session=session
            )
            if paid.matched_count != 1:
                raise RuntimeError("stone payout failed: user missing")   # aborts the transaction
        return keys, total

    keys, total = mongo_db.run_transaction(_work)
    balance = get_balance_sync(user_id)
    return {"status": "ok" if keys else "nothing", "keys": keys, "stones": total, "balance": balance}


def get_balance_sync(user_id):
    doc = mongo_db.col(USERS_COL).find_one({"_id": int(user_id)}, {"special_stones": 1})
    return int((doc or {}).get("special_stones") or 0)


# --------------------------------------------------------------------------
# Text rendering
# --------------------------------------------------------------------------
def _target_text(codes):
    parts = []
    for code in codes:
        row = mongo_db.get_character_by_code(code)
        if row:
            parts.append(f"{row[1]} [{code}] {RARITY_SYMBOLS.get(row[3], '')}".strip())
        else:
            parts.append(f"[{code}]")
    return " / ".join(parts)


def build_view_sync(user_id, now=None):
    """The one-message /stonetask text for this user (only their own progress)."""
    now = now or _now()
    day = current_day_key(now)
    ddoc = _tasks().find_one({"_id": _task_id(user_id, day)}) or {}
    wdoc = _tasks().find_one({"_id": _week_id(user_id, current_week_key(now))}) or {}
    prog = dict(wdoc.get("progress", {}) or {})
    prog.update(ddoc.get("progress", {}) or {})
    claimed = dict(wdoc.get("claimed", {}) or {})
    claimed.update(ddoc.get("claimed", {}) or {})
    targets = get_targets(day)

    def status(key, done):
        if claimed.get(key):
            return "🎁 Claimed"
        return "✅ Complete" if done else "🔒 In Progress"

    lines = ["💎 STONE TASKS", "📚 Collection Add resets daily • all other tasks reset weekly", ""]
    for key in TASK_ORDER:
        reward = REWARDS[key]
        stone_word = "Stone" if reward == 1 else "Stones"
        if key == "sell":
            c = min(int(prog.get("sell_common", 0)), SELL_COMMON_NEEDED)
            r = min(int(prog.get("sell_rare", 0)), SELL_RARE_NEEDED)
            done = c >= SELL_COMMON_NEEDED and r >= SELL_RARE_NEEDED
            progress = f"⚪ Common {c}/{SELL_COMMON_NEEDED} • 🔵 Rare {r}/{SELL_RARE_NEEDED}"
        elif key == "add":
            n = min(int(prog.get("add", 0)), 1)
            done = n >= 1
            progress = f"{n}/1"
        else:
            n = min(int(prog.get(key, 0)), NEEDED[key])
            done = n >= NEEDED[key]
            progress = f"{n}/{NEEDED[key]}"
        lines.append(TITLES[key] + (" (Daily)" if key in DAILY_KEYS else " (Weekly)"))
        if key == "add":
            lines.append(f"Target: {_target_text(targets) if targets else 'No target available today'}")
            lines.append("Catch any ONE of them with /add")
        lines.append(f"Progress: {progress}")
        lines.append(f"Reward: 💎 {reward} {stone_word}")
        lines.append(status(key, done and (key != "add" or bool(targets))))
        lines.append("")
    lines.append(f"💎 Your Special Stones: {get_balance_sync(user_id)}")
    lines.append(f"🔄 Collection Add resets in: {format_countdown(now)}")
    lines.append(f"🔄 Weekly tasks reset in: {format_weekly_countdown(now)}")
    return "\n".join(lines)


def claim_text(result):
    if result["status"] == "nouser":
        return "❌ Please use /start first."
    if result["status"] == "nothing":
        return ("❌ No completed tasks to claim right now.\n"
                "Finish a task first - rewards must be claimed before the 2:00 AM IST reset (weekly tasks: Monday).")
    lines = ["💎 STONES CLAIMED!", ""]
    for key in result["keys"]:
        lines.append(f"{TITLES[key]}: +{REWARDS[key]}")
    lines += ["", f"Total: +{result['stones']} 💎", f"Your Special Stones: {result['balance']}"]
    return "\n".join(lines)


# --------------------------------------------------------------------------
# Telegram handlers (telegram imports are lazy so the core logic is importable anywhere)
# --------------------------------------------------------------------------
def _keyboard(user_id):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    return InlineKeyboardMarkup([[InlineKeyboardButton("💎 CLAIM STONE", callback_data=f"stone:claim:{int(user_id)}")]])


async def stonetask_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None or user.is_bot:
        return
    try:
        text = await asyncio.to_thread(build_view_sync, user.id)
    except Exception as e:
        logger.error("/stonetask failed: %s", e)
        await msg.reply_text("❌ Could not load your stone tasks. Please try again.")
        return
    await msg.reply_text(text, reply_markup=_keyboard(user.id))


async def claimstone_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None or user.is_bot:
        return
    try:
        result = await asyncio.to_thread(claim_all_sync, user.id)   # same function as the button
    except Exception as e:
        logger.error("/claimstone failed: %s", e)
        await msg.reply_text("❌ Could not claim right now. Please try again.")
        return
    await msg.reply_text(claim_text(result))


async def stone_claim_callback(update, context):
    q = update.callback_query
    if q is None or q.from_user is None:
        return
    try:
        owner_id = int(q.data.split(":")[2])
    except (IndexError, ValueError):
        await q.answer()
        return
    if q.from_user.id != owner_id:
        await q.answer("❌ This is not your task list. Use /stonetask.", show_alert=True)
        return
    try:
        result = await asyncio.to_thread(claim_all_sync, owner_id)  # same function as /claimstone
    except Exception as e:
        logger.error("stone claim button failed: %s", e)
        await q.answer("❌ Could not claim right now. Please try again.", show_alert=True)
        return
    if result["status"] == "ok":
        await q.answer(f"💎 +{result['stones']} Stones claimed!")
        try:
            await q.message.reply_text(claim_text(result))
            text = await asyncio.to_thread(build_view_sync, owner_id)
            await q.edit_message_text(text, reply_markup=_keyboard(owner_id))
        except Exception as e:   # e.g. "message is not modified" - the claim itself already succeeded
            logger.info("stone view refresh skipped: %s", e)
    else:
        await q.answer(claim_text(result), show_alert=True)


def _register_stone(app):
    """Attach /stonetask, /claimstone and the single claim button to the application."""
    from telegram.ext import CallbackQueryHandler, CommandHandler
    _stone_deps["bot"] = app.bot     # used by stone_remind() to announce completed tasks
    app.add_handler(CommandHandler("stonetask", stonetask_command))
    app.add_handler(CommandHandler("claimstone", claimstone_command))
    app.add_handler(CallbackQueryHandler(stone_claim_callback, pattern=r"^stone:claim:\d+$"))


def register(app):
    """Attach every Fusion handler (stone tasks + Evolution + Weapons). Call fusion.bind(...) first."""
    _register_stone(app)
    _register_evolution(app)
    _register_dailytask(app)
    _register_weapons(app)


# ==========================================================================
# EVOLUTION SYSTEM
# ==========================================================================
# Dependencies that live in bot.py are injected with bind() (avoids a circular import).
_deps = {
    "is_owner": lambda uid: False,
    "is_executive": lambda uid: False,
    "symbols": RARITY_SYMBOLS,        # bot.SYMBOL (rarity -> emoji); also the list of valid rarities
    "conv_timeout": None,
    "notify": None,                   # async notify_staff_action(context, text, actor_id=...)
    "log_action": None,               # log_character_action(code, name, user, "add")
    "mark_success": None,             # mark_success(update) for the log pipeline
    "safe_reply": None,               # async safe_reply_text(message, text, **kw)
    "display_user": None,             # bot.display_user(user) -> "Name | ID: 123 | @username" (same as every staff notification)
    "rarity_text": None,              # bot.rarity_text(rarity) -> "🔵 Rare"
    "cancel_all": None,               # bot.cancel_conversation: the universal /cancel (clears EVERYTHING, replies, returns END)
    "skip_keyboard": None,            # bot.skip_keyboard() - the "⏭ Skip" reply keyboard
    "is_skip_text": lambda t: (t or "").strip().lower() in ("/skip", "⏭ skip"),
}


def bind(**kwargs):
    """Inject bot.py helpers: is_owner, is_executive, symbols, conv_timeout, notify, log_action, mark_success, safe_reply,
    skip_keyboard, is_skip_text."""
    _deps.update({k: v for k, v in kwargs.items() if v is not None})


EVO_MIN_STONES = 10          # hard minimum for the Evolution Stones requirement
EVO_MAX_BASE_QTY = 100
EVO_MAX_STONES = 100000
EVO_MAX_BERRIES = 1000000000
EVO_MAX_WORTH = 1000000000
NOT_ALLOWED_TEXT = "⚠️ Access Denied: You do not have permission to perform this action."
RECIPES_COL = mongo_db.FUSION_EVOLUTION_RECIPES


def _recipes():
    return mongo_db.col(RECIPES_COL)


def _stamp():
    """Naive IST timestamp - the same format the bot already stores for collection copies."""
    return datetime.now(IST).replace(tzinfo=None).isoformat(timespec="seconds")


async def _reply(msg, text, **kw):
    fn = _deps.get("safe_reply")
    if fn:
        return await fn(msg, text, **kw)
    return await msg.reply_text(text, **kw)


def _sym(rarity):
    return _deps["symbols"].get(rarity, "⭐")


def _by(user):
    """'Name | ID: 123 | @username' - identical to the 'By:' line of the normal character notifications."""
    fn = _deps.get("display_user")
    if fn:
        return fn(user)
    return f"{getattr(user, 'first_name', None) or 'Unknown'} | ID: {user.id} | " + (f"@{user.username}" if getattr(user, "username", None) else "No username")


def _rarity_line(rarity):
    fn = _deps.get("rarity_text")
    return fn(rarity) if fn else f"{_sym(rarity)} {rarity}"


def _is_staff_evo(uid):
    return bool(_deps["is_owner"](uid) or _deps["is_executive"](uid))


def _row(code):
    return mongo_db.get_character_by_code(code)


def _char_label(row):
    """'🔵 Rare Naruto (1234)' - row[1] already carries the 🌟/💫 mark for Evolution characters."""
    return f"{_sym(row[3])} {row[3]} {row[1]} ({row[0]})"


def _parse_int(text):
    t = str(text or "").strip().replace(",", "")
    if not t.isdigit():
        return None
    return int(t)


def _valid_code(code):
    return code.isdigit() and len(code) == 4 and 1 <= int(code) <= 9999


# ---- range values for drop stock / drop price ("3-10", "5", "0" = not set), same rules as the Invite Manager (rewards._parse_range)
def _wd_parse(text, cap):
    """'100-1000' / '300' / '0' -> (lo, hi), or None when invalid. (0, 0) means not set. A range starts at 1 or more."""
    rng = rewards._parse_range(str(text or "").replace(",", ""), cap)
    if rng is None or (rng[1] > 0 and rng[0] < 1):
        return None
    return rng


def _wd_bounds(w, kind):
    """(min, max) of a weapon's drop 'stock' or 'price'. drop_<kind> holds the maximum; a weapon saved before ranges counts as min = max."""
    hi = int(w.get(f"drop_{kind}") or 0)
    if hi <= 0:
        return 0, 0
    lo = int(w.get(f"drop_{kind}_min") or 0)
    return (lo if 1 <= lo <= hi else hi), hi


def _wd_text(w, kind, commas=False):
    """'3-10', '5' or None (not set)."""
    lo, hi = _wd_bounds(w, kind)
    if hi <= 0:
        return None
    f = (lambda n: f"{n:,}") if commas else str
    return f(hi) if lo == hi else f"{f(lo)}-{f(hi)}"


def _wd_fields(kind, rng):
    return {f"drop_{kind}": rng[1], f"drop_{kind}_min": rng[0]}


# ---------------------------------------------------------------- recipe queries
def get_recipe_sync(evo_code):
    return _recipes().find_one({"_id": str(evo_code)})


def get_recipe_by_base_sync(base_code):
    """The SAME-card recipe whose base is this card (one per card). Different Card recipes are found by their pair."""
    return _recipes().find_one({"base_code": str(base_code), "kind": {"$ne": "pair"}})


def is_pair_recipe(recipe):
    return (recipe or {}).get("kind") == "pair"


def recipe_ingredients(recipe):
    """[(code, qty), ...]: one entry for a Same Card recipe, two for a Different Card recipe."""
    items = [(str(recipe["base_code"]), int(recipe["base_qty"]))]
    if is_pair_recipe(recipe):
        items.append((str(recipe["second_code"]), int(recipe["second_qty"])))
    return items


def pair_key(a, b=None):
    return "+".join(sorted([str(a), str(b)])) if b is not None else str(a)


def get_pair_recipe_sync(a, b):
    return _recipes().find_one({"pair_key": pair_key(a, b)})


def recipes_using_sync(code):
    """Every recipe that uses this card as an ingredient (either side), sorted by result code."""
    code = str(code)
    return sorted(_recipes().find({"$or": [{"base_code": code}, {"second_code": code}]}), key=lambda r: str(r["_id"]))


def _is_ancestor(target, codes):
    """True if `target` is (transitively) an ingredient of any card in `codes` through the recipes."""
    stack, seen = [str(c) for c in codes], set()
    while stack:
        cur = stack.pop()
        if cur == str(target):
            return True
        if cur in seen:
            continue
        seen.add(cur)
        recipe = get_recipe_sync(cur)
        if recipe:
            stack.extend(c for c, _q in recipe_ingredients(recipe))
    return False


FUSION_SYMBOL_SAME = "🌟"   # same character fused (two or more copies of one card)
FUSION_SYMBOL_DIFF = "💫"   # two different characters fused


def fusion_symbol(recipe_or_kind):
    """Fusion type symbol from a recipe (or its kind string): 💫 for pair (different cards), 🌟 for same."""
    kind = recipe_or_kind if isinstance(recipe_or_kind, str) else (recipe_or_kind or {}).get("kind")
    return FUSION_SYMBOL_DIFF if kind == "pair" else FUSION_SYMBOL_SAME


def _ingredient_text(recipe):
    """'2× Naruto [1234]' or '1× Naruto [1234] + 1× Sasuke [1005]'."""
    parts = []
    for code, qty in recipe_ingredients(recipe):
        row = _row(code)
        parts.append(f"{qty}× {row[1] if row else '?'} [{code}]")
    return " + ".join(parts)


def _name_taken(name):
    folded = mongo_db.strip_evo_mark(name).casefold()
    return any(str(r[1]).casefold() == folded or mongo_db.strip_evo_mark(r[1]).casefold() == folded
               for r in mongo_db.get_all_characters())


HEAVENLY_RARITY = "Heavenly"                          # fusion-only top tier (symbol 🧿 lives in bot.SYMBOL)
HEAVENLY_INGREDIENT_RARITIES = ("Celestial", "Ethereal", "Mythical")


def heavenly_error(rarity, codes):
    """A Heavenly evolution may only be made from Celestial, Ethereal or Mythical characters. Returns an error text or None."""
    if str(rarity or "").title() != HEAVENLY_RARITY:
        return None
    for code in codes:
        row = _row(str(code))
        if row is None or str(row[3]) not in HEAVENLY_INGREDIENT_RARITIES:
            return "❌ Heavenly evolutions can only use Celestial, Ethereal or Mythical characters."
    return None


def validate_recipe(base_code, base_qty, evo_code, stones, berries, second_code=None, second_qty=None):
    """Returns an error text, or None when the recipe may be created. second_code makes it a Different Card recipe."""
    base_code, evo_code = str(base_code), str(evo_code)
    pair = second_code is not None
    if not _valid_code(base_code) or _row(base_code) is None:
        return "❌ Card A does not exist." if pair else "❌ The base character code does not exist."
    if not isinstance(base_qty, int) or not (1 <= base_qty <= EVO_MAX_BASE_QTY):
        return f"❌ Base quantity must be a whole number from 1 to {EVO_MAX_BASE_QTY}."
    if pair:
        second_code = str(second_code)
        if not _valid_code(second_code) or _row(second_code) is None:
            return "❌ Card B does not exist."
        if second_code == base_code:
            return "❌ Card A and card B must be two different cards."
        if not isinstance(second_qty, int) or not (1 <= second_qty <= EVO_MAX_BASE_QTY):
            return f"❌ Card B quantity must be a whole number from 1 to {EVO_MAX_BASE_QTY}."
    if not isinstance(stones, int) or stones < EVO_MIN_STONES:
        return f"❌ Evolution Stones must be at least {EVO_MIN_STONES}."
    if stones > EVO_MAX_STONES:
        return f"❌ Evolution Stones cannot be more than {EVO_MAX_STONES}."
    if not isinstance(berries, int) or berries < 0 or berries > EVO_MAX_BERRIES:
        return "❌ Berries cost must be a whole number (0 or more)."
    if not _valid_code(evo_code):
        return "❌ The evolution code must be exactly 4 digits (0001-9999)."
    if evo_code == base_code or (pair and evo_code == second_code):
        return "❌ A character cannot evolve into itself (the evolution code equals an ingredient code)."
    if _row(evo_code) is not None:
        return "❌ That code already belongs to a character."
    if get_recipe_sync(evo_code) is not None:
        return "❌ An evolution recipe with that code already exists."
    if pair:
        if get_pair_recipe_sync(base_code, second_code) is not None:
            return "❌ That pair of cards already has an evolution recipe (conflict)."
    elif get_recipe_by_base_sync(base_code) is not None:
        return "❌ That base character already has an evolution recipe (conflict). Use /delevo first."
    return None


def create_evolution_sync(base_code, base_qty, name, anime, rarity, worth, stones, berries, evo_code, photo, created_by,
                          second_code=None, second_qty=None):
    """Creates the EVOLUTION character and its recipe in ONE transaction (both or neither)."""
    err = (validate_recipe(base_code, base_qty, evo_code, stones, berries, second_code, second_qty)
           or heavenly_error(rarity, [base_code] + ([second_code] if second_code is not None else [])))
    if err:
        return {"ok": False, "error": err}
    if _name_taken(name):
        return {"ok": False, "error": "❌ A character with that name already exists."}
    pair = second_code is not None
    recipe = {
        "_id": str(evo_code), "evo_code": str(evo_code), "base_code": str(base_code), "base_qty": int(base_qty),
        "kind": "pair" if pair else "same", "pair_key": pair_key(base_code, second_code if pair else None),
        "stones": int(stones), "berries": int(berries), "created_by": int(created_by), "created_at": _stamp(),
    }
    if pair:
        recipe.update({"second_code": str(second_code), "second_qty": int(second_qty)})

    def _work(session):
        mongo_db.insert_evolution_character(evo_code, name, anime, rarity, worth, photo, session=session)
        _recipes().insert_one(recipe, session=session)

    try:
        mongo_db.run_transaction(_work)
    except mongo_db.DuplicateKeyError:
        return {"ok": False, "error": "❌ The name, code or card pair already has a record. Nothing was created."}
    finally:
        mongo_db.invalidate_character_cache()
    return {"ok": True}


def set_recipe_weapon_sync(evo_code, weapon_code, stones=None):
    """Attach (weapon_code) or remove (None) the weapon an evolution needs. With a weapon the recipe may need 0 stones;
    without one it needs at least EVO_MIN_STONES again. Returns {"ok": True, "stones": n} or {"ok": False, "error": text}."""
    evo_code = str(evo_code)
    recipe = get_recipe_sync(evo_code) if _valid_code(evo_code) else None
    if recipe is None:
        return {"ok": False, "error": "❌ No evolution recipe found for that code."}
    if weapon_code is not None and get_weapon(weapon_code) is None:
        return {"ok": False, "error": "❌ That weapon code does not exist."}
    if stones is not None and not (isinstance(stones, int) and 0 <= stones <= EVO_MAX_STONES):
        return {"ok": False, "error": f"❌ Stones must be a whole number from 0 to {EVO_MAX_STONES}."}
    new_stones = int(recipe["stones"]) if stones is None else int(stones)
    if weapon_code is None:
        new_stones = max(new_stones, EVO_MIN_STONES)
        _recipes().update_one({"_id": evo_code}, {"$set": {"stones": new_stones}, "$unset": {"weapon_code": ""}})
    else:
        _recipes().update_one({"_id": evo_code}, {"$set": {"stones": new_stones, "weapon_code": str(weapon_code)}})
    return {"ok": True, "stones": new_stones}


def delete_recipe_sync(evo_code):
    """Deletes ONLY the recipe. Evolution characters (and the copies users own) are untouched."""
    return _recipes().delete_one({"_id": str(evo_code)}).deleted_count == 1


# ---------------------------------------------------------------- evolve (atomic)
class _EvoAbort(Exception):
    def __init__(self, status, **info):
        super().__init__(status)
        self.status, self.info = status, info


def evolve_sync(user_id, evo_code, receipt_key=None):
    """
    Deterministic evolution of a Same Card OR Different Card recipe. Everything happens in ONE transaction:
      receipt (one-click-per-card guard) -> verify recipe/characters/materials -> conditional stone+berry deduct
      -> remove exactly the required copies of EACH ingredient card -> add exactly 1 Evolution character.
    Any shortage aborts the transaction, so nothing is consumed and nothing is half done.
    Returns {"status": "ok"|"norecipe"|"nochar"|"nobase_char"|"nouser"|"nocopies"|"nostones"|"noberries"|"dup"|"changed", ...}
    """
    user_id, evo_code = int(user_id), str(evo_code)
    # `state` records what was applied so it can be undone by hand ONLY when the server has no transactions
    # (mongo_db.run_transaction then calls fn(None)). With a real transaction MongoDB rolls everything back itself.
    state = {"no_txn": False, "receipt": None, "deducted": None, "deleted": [], "weapon": None}

    def _work(session):
        state.update(no_txn=session is None, receipt=None, deducted=None, deleted=[], weapon=None)   # _work may be retried
        users = mongo_db.col(USERS_COL)
        recipe = _recipes().find_one({"_id": evo_code}, session=session)
        if not recipe:
            raise _EvoAbort("norecipe")
        chars = mongo_db.col(mongo_db.CHARACTERS)
        evo_char = chars.find_one({"code": evo_code}, session=session)
        if not evo_char or evo_char.get("char_type") != mongo_db.CHAR_TYPE_EVOLUTION:
            raise _EvoAbort("nochar")
        ingredients = recipe_ingredients(recipe)
        stones, berries = int(recipe["stones"]), int(recipe["berries"])
        for code, _qty in ingredients:
            if not chars.find_one({"code": code}, session=session):
                raise _EvoAbort("nobase_char", code=code)
        user = users.find_one({"_id": user_id}, session=session)
        if user is None:
            raise _EvoAbort("nouser")

        if receipt_key:      # one evolution per confirmation card, however many times the button is pressed
            try:
                mongo_db.col(mongo_db.OP_RECEIPTS).insert_one(
                    {"_id": str(receipt_key), "result": {"evolve": evo_code}, "created_at": datetime.now(timezone.utc)},
                    session=session)
                state["receipt"] = str(receipt_key)
            except mongo_db.DuplicateKeyError:
                raise _EvoAbort("dup")

        for code, need in ingredients:
            have = mongo_db.count_user_copies(user_id, code, session=session)
            if have < need:
                raise _EvoAbort("nocopies", have=have, need=need, code=code)
        weapon_code = recipe.get("weapon_code")          # optional weapon slot: the player must own 1 of this weapon
        if weapon_code:
            if get_weapon(weapon_code) is None:
                raise _EvoAbort("noweapon_def", code=weapon_code)
            if count_user_weapon(user_id, weapon_code, session=session) < 1:
                raise _EvoAbort("noweapon", code=weapon_code)
        have_stones, have_coins = int(user.get("special_stones") or 0), int(user.get("coins") or 0)
        if have_stones < stones:
            raise _EvoAbort("nostones", have=have_stones, need=stones)
        if have_coins < berries:
            raise _EvoAbort("noberries", have=have_coins, need=berries)

        paid = users.update_one(
            {"_id": user_id, "special_stones": {"$gte": stones}, "coins": {"$gte": berries}},
            {"$inc": {"special_stones": -stones, "coins": -berries}}, session=session)
        if paid.modified_count != 1:
            raise _EvoAbort("changed")
        state["deducted"] = (stones, berries)

        if weapon_code:                                  # the weapon is used up together with the cards
            if not take_user_weapon(user_id, weapon_code, 1, session=session):
                raise _EvoAbort("changed")
            state["weapon"] = weapon_code

        copies = mongo_db.col(mongo_db.COLLECTIONS)
        for code, need in ingredients:
            for _ in range(need):                  # exactly `need` copies of each card; extra copies stay untouched
                doc = copies.find_one_and_delete({"user_id": user_id, "character_code": code}, session=session)
                if doc is None:
                    raise _EvoAbort("changed")
                state["deleted"].append(doc)
            if mongo_db.count_user_copies(user_id, code, session=session) == 0:
                mongo_db.col(mongo_db.FAVORITES).delete_one({"_id": user_id, "character_code": code}, session=session)

        mongo_db.add_collection(user_id, evo_code, _stamp(), session=session)   # exactly 1 result
        return {"status": "ok", "base_code": ingredients[0][0], "base_qty": ingredients[0][1], "ingredients": ingredients,
                "stones": stones, "berries": berries, "evo_code": evo_code, "weapon": weapon_code}

    try:
        result = mongo_db.run_transaction(_work)
    except _EvoAbort as abort:
        if state["no_txn"]:
            _undo_manually(user_id, state)
        return {"status": abort.status, **abort.info}
    except Exception:
        if state["no_txn"]:
            _undo_manually(user_id, state)
        raise
    result["stones_left"], result["berries_left"] = _balances(user_id)
    return result


def _balances(user_id):
    doc = mongo_db.col(USERS_COL).find_one({"_id": int(user_id)}) or {}
    return int(doc.get("special_stones") or 0), int(doc.get("coins") or 0)


def _undo_manually(user_id, state):
    """No-transaction fallback only: put back deleted base copies and the weapon, refund stones/berries, free the card receipt."""
    try:
        for doc in state["deleted"]:
            mongo_db.col(mongo_db.COLLECTIONS).insert_one(doc)
        if state["deducted"]:
            stones, berries = state["deducted"]
            mongo_db.col(USERS_COL).update_one({"_id": int(user_id)}, {"$inc": {"special_stones": stones, "coins": berries}})
        if state.get("weapon"):
            add_user_weapon(user_id, state["weapon"], 1)
        if state["receipt"]:
            mongo_db.col(mongo_db.OP_RECEIPTS).delete_one({"_id": state["receipt"]})
    except Exception as e:   # never hide the original problem
        logger.error("evolve manual undo failed: %s", e)


def evolve_error_text(res):
    s = res.get("status")
    if s == "norecipe":
        return "❌ This evolution recipe no longer exists."
    if s == "nochar":
        return "❌ The evolution result character no longer exists."
    if s == "nobase_char":
        return "❌ The base character no longer exists."
    if s == "nouser":
        return "❌ Please use /start first."
    if s == "noweapon_def":
        return "❌ The weapon this evolution needs no longer exists. Nothing was used."
    if s == "noweapon":
        w = get_weapon(res.get("code"))
        return f"❌ You need the weapon {w['name'] if w else res.get('code')} to do this evolution. Nothing was used."
    if s == "nocopies":
        row = _row(res["code"]) if res.get("code") else None
        return f"❌ You need {res['need']}× {row[1] if row else 'the base character'} but only have {res['have']}. Nothing was used."
    if s == "nostones":
        return f"❌ Not enough Evolution Stones: need {res['need']}, you have {res['have']}. Nothing was used."
    if s == "noberries":
        return f"❌ Not enough Berries: need {res['need']:,}, you have {res['have']:,}. Nothing was used."
    if s == "dup":
        return "⚠️ This evolution was already processed."
    return "⚠️ Your materials changed while evolving. Nothing was used. Please try again."


# ---------------------------------------------------------------- texts
def evolution_list_pages_sync():
    """Pages (<= ~3800 chars) of the public /evolution list. Recipes are numbered 1, 2, 3... and the numbers continue across pages."""
    head = "Evolution List\n\n"
    blocks, n = [], 0
    for r in sorted(_recipes().find({}), key=lambda x: str(x["_id"])):
        ingredients = recipe_ingredients(r)
        rows = [_row(code) for code, _q in ingredients]
        evo = _row(r["_id"])
        if evo is None or any(x is None for x in rows):
            continue   # recipe whose character was deleted: not shown (and cannot be used)
        n += 1
        lines = [f"{n}. {fusion_symbol(r)} {ingredients[0][1]}× {_char_label(rows[0])}"]
        if len(ingredients) > 1:
            lines.append(f"   + {ingredients[1][1]}× {_char_label(rows[1])}")
        lines.append(f"   ➡️ {_char_label(evo)}")
        if r.get("weapon_code"):
            wpn = get_weapon(r["weapon_code"])
            lines.append(f"   ⚔️ Weapon: {wpn['name'] if wpn else '?'} [{r['weapon_code']}] ×1")
        lines.append(f"   💎 {r['stones']} Stones • 🪙 {r['berries']:,} Berries")
        blocks.append("\n".join(lines))
    if not blocks:
        return [head + "No evolution recipes have been set up yet."]
    pages, cur = [], head
    for b in blocks:
        if len(cur) + len(b) + 2 > 3800 and cur != head:
            pages.append(cur.rstrip())
            cur = head
        cur += b + "\n\n"
    pages.append(cur.rstrip())
    return pages


def _resolve_recipe_sync(query):
    """Recipes a user means by a character code or name. Typing an INGREDIENT card returns every recipe that uses it;
    typing a RESULT card returns the recipe that makes it. Returns (list_of_recipes, error_text|None)."""
    q = mongo_db.strip_evo_mark(query)
    if _valid_code(q):
        row = _row(q)
    else:
        matches = mongo_db.find_characters_by_name_parts(q)
        if len(matches) > 1:
            return [], "❓ Several characters match that name. Please use the 4-digit code."
        row = matches[0] if matches else None
    if row is None:
        return [], "❌ Character not found."
    recipes = recipes_using_sync(row[0])
    if not recipes:
        producing = get_recipe_sync(row[0])
        recipes = [producing] if producing else []
    if not recipes:
        return [], "❌ There is no evolution recipe for that character. See /evolution."
    return recipes, None


def build_card_sync(user_id, recipe):
    ingredients = recipe_ingredients(recipe)
    rows = [_row(code) for code, _q in ingredients]
    evo = _row(recipe["_id"])
    if evo is None or any(x is None for x in rows):
        return None
    stones, coins = _balances(user_id)
    have = " • ".join(f"{r[1]} ×{mongo_db.count_user_copies(user_id, r[0])}" for r in rows)
    if len(ingredients) == 1:
        who = f"{fusion_symbol(recipe)} Base Character: {rows[0][1]} ×{ingredients[0][1]}\n"
    else:
        sym = fusion_symbol(recipe)
        who = f"{sym} Card A: {rows[0][1]} ×{ingredients[0][1]}\n{sym} Card B: {rows[1][1]} ×{ingredients[1][1]}\n"
    weapon_line, weapon_have = "", ""
    if recipe.get("weapon_code"):
        wpn = get_weapon(recipe["weapon_code"])
        owned = count_user_weapon(user_id, recipe["weapon_code"])
        weapon_line = f"⚔️ Weapon: {wpn['name'] if wpn else '?'} [{recipe['weapon_code']}] ×1\n"
        weapon_have = f" • ⚔️ {owned}"
    return (
        "EVOLUTION\n\n"
        f"{who}"
        f"{weapon_line}"
        f"💎 Evolution Stone: ×{recipe['stones']}\n"
        f"🪙 Berries: {recipe['berries']:,}\n\n"
        "⬇️\n\n"
        f"✨ Result: {evo[1]} ×1\n\n"
        f"You have: {have}{weapon_have} • 💎 {stones} • 🪙 {coins:,}"
    )


def success_text(res):
    used = " + ".join(f"{(_row(c)[1] if _row(c) else c)} ×{q}" for c, q in res.get("ingredients") or [(res["base_code"], res["base_qty"])])
    evo = _row(res["evo_code"])
    wpn = get_weapon(res.get("weapon")) if res.get("weapon") else None
    weapon_used = f"⚔️ Weapon used: {wpn['name']} [{res['weapon']}] ×1\n" if res.get("weapon") else ""
    return (
        "✅ EVOLUTION COMPLETE!\n\n"
        f"{FUSION_SYMBOL_DIFF if len(res.get('ingredients') or []) > 1 else FUSION_SYMBOL_SAME} Used: {used}\n"
        f"{weapon_used}"
        f"💎 Stones used: {res['stones']}\n"
        f"🪙 Berries used: {res['berries']:,}\n\n"
        f"✨ Received: {evo[1] if evo else res['evo_code']} ×1\n\n"
        f"💎 Stones left: {res['stones_left']} • 🪙 Berries left: {res['berries_left']:,}"
    )


def _evolve_keyboard(user_id, evo_code):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    return InlineKeyboardMarkup([[InlineKeyboardButton("EVOLVE", callback_data=f"evo:go:{int(user_id)}:{evo_code}")]])


def _recipe_buttons_sync(user_id, recipes):
    """One button per recipe (max 10): 'Naruto ×2 ➡️ Sage Naruto' or 'Naruto + Sasuke ➡️ Final Fight'."""
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    rows = []
    for r in recipes[:10]:
        ingredients = recipe_ingredients(r)
        cards, evo = [_row(c) for c, _q in ingredients], _row(r["_id"])
        if evo and all(cards):
            names = " + ".join(c[1] for c in cards) if len(cards) > 1 else f"{cards[0][1]} ×{ingredients[0][1]}"
            rows.append([InlineKeyboardButton(f"{fusion_symbol(r)} {names} ➡️ {evo[1]}"[:60], callback_data=f"evo:pick:{int(user_id)}:{r['_id']}")])
    return InlineKeyboardMarkup(rows) if rows else None


def _pick_keyboard_sync(user_id):
    """Buttons for every recipe in which the user owns at least one of the ingredient cards."""
    usable = [r for r in sorted(_recipes().find({}), key=lambda x: str(x["_id"]))
              if any(mongo_db.count_user_copies(user_id, c) > 0 for c, _q in recipe_ingredients(r))]
    return _recipe_buttons_sync(user_id, usable)


# ---------------------------------------------------------------- /evolution /evolve /delevo handlers
async def evolution_command(update, context):
    msg = update.effective_message
    if msg is None:
        return
    pages = await asyncio.to_thread(evolution_list_pages_sync)
    for page in pages:
        await _reply(msg, page)


async def evolve_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None or user.is_bot:
        return
    query = " ".join(getattr(context, "args", None) or []).strip()
    if not query:
        kb = await asyncio.to_thread(_pick_keyboard_sync, user.id)
        if kb is None:
            await _reply(msg, "You don't own a character that can evolve right now.\nSee /evolution for every recipe, "
                              "or use /evolve <code or name>.")
        else:
            await _reply(msg, "Choose what to evolve:", reply_markup=kb)
        return
    recipes, err = await asyncio.to_thread(_resolve_recipe_sync, query)
    if err:
        await _reply(msg, err)
        return
    if len(recipes) > 1:
        kb = await asyncio.to_thread(_recipe_buttons_sync, user.id, recipes)
        await _reply(msg, "Several evolutions use this card. Choose one:", reply_markup=kb)
        return
    recipe = recipes[0]
    card = await asyncio.to_thread(build_card_sync, user.id, recipe)
    if card is None:
        await _reply(msg, "❌ This evolution is unavailable (a character was removed).")
        return
    await _reply(msg, card, reply_markup=_evolve_keyboard(user.id, recipe["_id"]))


async def evolve_callback(update, context):
    q = update.callback_query
    if q is None or q.from_user is None:
        return
    try:
        _evo, action, owner, code = (q.data or "").split(":")
        owner = int(owner)
    except ValueError:
        await q.answer()
        return
    if q.from_user.id != owner:
        await q.answer("❌ This is not your evolution card. Use /evolve.", show_alert=True)
        return

    if action == "pick":
        recipe = await asyncio.to_thread(get_recipe_sync, code)
        card = await asyncio.to_thread(build_card_sync, owner, recipe) if recipe else None
        if card is None:
            await q.answer("❌ This evolution is unavailable.", show_alert=True)
            return
        await q.answer()
        try:
            await q.edit_message_text(card, reply_markup=_evolve_keyboard(owner, code))
        except Exception as e:
            logger.info("evolve pick edit skipped: %s", e)
        return

    # action == "go": the confirmation button
    msg = q.message
    key = f"evo:{getattr(getattr(msg, 'chat', None), 'id', 0)}:{getattr(msg, 'message_id', 0)}" if msg is not None else None
    try:
        res = await asyncio.to_thread(evolve_sync, owner, code, key)
    except Exception as e:
        logger.error("evolve failed: %s", e)
        await q.answer("❌ Evolution failed. Nothing was used. Please try again.", show_alert=True)
        return
    if res["status"] != "ok":
        await q.answer(evolve_error_text(res), show_alert=True)
        return
    await q.answer("Evolution complete!")
    text = success_text(res)
    try:
        await q.edit_message_text(text)       # card (and its button) replaced by the result
    except Exception as e:
        logger.info("evolve result edit skipped: %s", e)
    evo = _row(res["evo_code"])
    if evo and evo[5] and msg is not None:
        try:
            await msg.reply_photo(photo=evo[5], caption=f"✨ {_char_label(evo)}")
        except Exception as e:
            logger.info("evolve photo skipped: %s", e)


async def delevo_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return
    if not _deps["is_owner"](user.id):          # Owner ONLY - Executives are denied here as well as in the role gate
        await _reply(msg, NOT_ALLOWED_TEXT)
        return
    args = getattr(context, "args", None) or []
    code = str(args[0]).strip() if args else ""
    if not _valid_code(code):
        await _reply(msg, "Usage: /delevo <evolution character code>")
        return
    recipe = await asyncio.to_thread(get_recipe_sync, code)
    if recipe is None:
        await _reply(msg, "❌ No evolution recipe found for that code.")
        return
    await asyncio.to_thread(delete_recipe_sync, code)
    evo = await asyncio.to_thread(_row, code)
    label = evo[1] if evo else code
    recipe_text = await asyncio.to_thread(_ingredient_text, recipe)
    await _reply(msg, f"🗑 Evolution recipe for {label} [{code}] deleted.\n"
                      "Evolution characters users already own are not affected.")
    try:
        if _deps["notify"]:
            await _deps["notify"](
                context,
                f"🗑 EVOLUTION RECIPE DELETED\n"
                f"🎭 {label} [{code}]\n"
                + (f"🏷 {_rarity_line(evo[3])}\n" if evo else "")
                + f"🧬 Recipe: {fusion_symbol(recipe)} {recipe_text} ➡️ {label} [{code}]\n"
                f"💎 Evolution Stones: {recipe['stones']}\n"
                f"🪙 Berries: {recipe['berries']:,}\n"
                f"ℹ️ Evolution characters users already own were kept.\n"
                f"👤 By: {_by(user)}", actor_id=user.id)
    except Exception as e:
        logger.info("delevo notification skipped: %s", e)
    if _deps["mark_success"]:
        _deps["mark_success"](update)


# ---------------------------------------------------------------- /addevo conversation (the exact 10 steps)
(E_BASE, E_QTY, E_NAME, E_ANIME, E_RARITY, E_WORTH, E_STONES, E_BERRIES, E_CODE, E_PHOTO) = range(200, 210)
_EVO_KEYS = ("evo_base", "evo_base_name", "evo_qty", "evo_name", "evo_anime", "evo_rarity", "evo_worth",
             "evo_stones", "evo_berries", "evo_code")


def _clear_evo(context):
    for k in _EVO_KEYS:
        context.user_data.pop(k, None)


async def addevo_start(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return -1
    if update.effective_chat.type != "private":
        await _reply(msg, "⚠️ /addevo can only be used in the bot's PM (private chat).")
        return -1
    if not _is_staff_evo(user.id):              # Owner + Executive only (normal users and Scouts are refused)
        await _reply(msg, NOT_ALLOWED_TEXT)
        return -1
    _clear_evo(context)
    context.user_data["evo_phase"] = "type"
    await _reply(msg, "New Evolution\nChoose the evolution type:", reply_markup=_type_keyboard(user.id))
    return E_TYPE


async def addevo_base(update, context):
    msg = update.effective_message
    code = (msg.text or "").strip()
    row = _row(code) if _valid_code(code) else None
    if row is None:
        await _reply(msg, "❌ That character code does not exist. Evolution setup stopped.")
        _clear_evo(context)
        return -1
    if await asyncio.to_thread(get_recipe_by_base_sync, code):
        await _reply(msg, "❌ That character already has an evolution recipe. Evolution setup stopped.")
        _clear_evo(context)
        return -1
    context.user_data["evo_base"], context.user_data["evo_base_name"] = code, row[1]
    await _reply(msg, f"2️⃣ Base Character Quantity\nHow many copies of {row[1]} are required? (1-{EVO_MAX_BASE_QTY})")
    return E_QTY


async def addevo_qty(update, context):
    msg = update.effective_message
    n = _parse_int(msg.text)
    if n is None or not (1 <= n <= EVO_MAX_BASE_QTY):
        await _reply(msg, f"❌ Send a whole number from 1 to {EVO_MAX_BASE_QTY}.")
        return E_QTY
    context.user_data["evo_qty"] = n
    await _reply(msg, "3️⃣ Evolution Character Name:")
    return E_NAME


async def addevo_name(update, context):
    msg = update.effective_message
    name = mongo_db.strip_evo_mark(msg.text)        # the lightning mark is display-only: never stored, never doubled
    if not name:
        await _reply(msg, "❌ The name cannot be empty.")
        return E_NAME
    if await asyncio.to_thread(_name_taken, name):
        await _reply(msg, "❌ A character with that name already exists. Send a different name.")
        return E_NAME
    context.user_data["evo_name"] = name
    await _reply(msg, f"{_stepno(context, 4)} Anime Name:")
    return E_ANIME


async def addevo_anime(update, context):
    msg = update.effective_message
    anime = (msg.text or "").strip()
    if not anime:
        await _reply(msg, "❌ The anime name cannot be empty.")
        return E_ANIME
    context.user_data["evo_anime"] = anime
    await _reply(msg, f"{_stepno(context, 5)} Rarity:\nCommon / Rare / Epic / Legendary / Mythical / Ethereal / Celestial / Heavenly")
    return E_RARITY


async def addevo_rarity(update, context):
    msg = update.effective_message
    rarity = (msg.text or "").strip().title()
    if rarity not in _deps["symbols"]:
        await _reply(msg, "❌ Invalid rarity.")
        return E_RARITY
    context.user_data["evo_rarity"] = rarity
    await _reply(msg, f"{_stepno(context, 6)} Worth in Berries:")
    return E_WORTH


async def addevo_worth(update, context):
    msg = update.effective_message
    n = _parse_int(msg.text)
    if n is None or n > EVO_MAX_WORTH:
        await _reply(msg, "❌ Worth must be a whole number (0 or more).")
        return E_WORTH
    context.user_data["evo_worth"] = n
    await _reply(msg, f"{_stepno(context, 7)} Evolution Stones required (minimum {EVO_MIN_STONES}):")
    return E_STONES


async def addevo_stones(update, context):
    msg = update.effective_message
    n = _parse_int(msg.text)
    if n is None or n < EVO_MIN_STONES:
        await _reply(msg, f"❌ Evolution Stones must be a number of at least {EVO_MIN_STONES}.")
        return E_STONES
    if n > EVO_MAX_STONES:
        await _reply(msg, f"❌ Evolution Stones cannot be more than {EVO_MAX_STONES}.")
        return E_STONES
    context.user_data["evo_stones"] = n
    await _reply(msg, f"{_stepno(context, 8)} Berries Cost:")
    return E_BERRIES


async def addevo_berries(update, context):
    msg = update.effective_message
    n = _parse_int(msg.text)
    if n is None or n > EVO_MAX_BERRIES:
        await _reply(msg, "❌ Berries cost must be a whole number (0 or more).")
        return E_BERRIES
    context.user_data["evo_berries"] = n
    await _reply(msg, f"{_stepno(context, 9)} Evolution Character Code (unique 4-digit code):")
    return E_CODE


async def addevo_code(update, context):
    msg = update.effective_message
    code = (msg.text or "").strip()
    if not _valid_code(code):
        await _reply(msg, "❌ Code must be exactly 4 digits (0001-9999).")
        return E_CODE
    if code in (context.user_data.get("evo_base"), context.user_data.get("evo_second")):
        await _reply(msg, "❌ The evolution code cannot be the same as an ingredient character (no self-evolution).")
        return E_CODE
    if _row(code) is not None or await asyncio.to_thread(get_recipe_sync, code):
        await _reply(msg, "❌ Code already exists.")
        return E_CODE
    context.user_data["evo_code"] = code
    await _reply(msg, f"{_stepno(context, 10)} Evolution Character Photo - send the photo:")
    return E_PHOTO


async def addevo_photo(update, context):
    msg = update.effective_message
    if not getattr(msg, "photo", None):
        await _reply(msg, "❌ Please send a photo (the photo is required).")
        return E_PHOTO
    d = dict(context.user_data)
    pair = d.get("evo_kind") == "pair"
    required = [k for k in _EVO_KEYS if k not in ("evo_base_name", "evo_second", "evo_second_name", "evo_qty2", "evo_kind", "evo_phase")]
    if pair:
        required += ["evo_second", "evo_qty2"]
    if not all(k in d for k in required):
        _clear_evo(context)
        await _reply(msg, "❌ The setup expired. Start again with /addevo.")
        return -1
    photo_id = msg.photo[-1].file_id
    user = update.effective_user
    if not _is_staff_evo(user.id):              # re-check: the role could have been removed mid-flow
        _clear_evo(context)
        await _reply(msg, NOT_ALLOWED_TEXT)
        return -1
    try:
        res = await asyncio.to_thread(
            create_evolution_sync, d["evo_base"], d["evo_qty"], d["evo_name"], d["evo_anime"], d["evo_rarity"],
            d["evo_worth"], d["evo_stones"], d["evo_berries"], d["evo_code"], photo_id, user.id,
            d.get("evo_second") if pair else None, d.get("evo_qty2") if pair else None)
    except Exception as e:
        logger.error("addevo failed: %s", e)
        _clear_evo(context)
        await _reply(msg, "❌ Could not create the evolution. Please try again.")
        return -1
    _clear_evo(context)
    if not res["ok"]:
        await _reply(msg, res["error"])
        return -1
    recipe = {"base_code": d["evo_base"], "base_qty": d["evo_qty"], "kind": "pair" if pair else "same",
              "second_code": d.get("evo_second"), "second_qty": d.get("evo_qty2")}
    base, evo = _row(d["evo_base"]), _row(d["evo_code"])
    second = _row(d["evo_second"]) if pair else None
    lines = f"{d['evo_qty']}× {_char_label(base)}\n" + (f"+ {d['evo_qty2']}× {_char_label(second)}\n" if pair else "")
    await _reply(msg, "✅ Evolution created!\n\n" + f"{fusion_symbol(recipe)} " + lines + f"➡️ {_char_label(evo)}\n"
                      f"💎 {d['evo_stones']} Stones • 🪙 {d['evo_berries']:,} Berries")
    try:
        if _deps["log_action"]:
            await asyncio.to_thread(_deps["log_action"], d["evo_code"], d["evo_name"], user, "add")
        if _deps["notify"]:
            await _deps["notify"](
                context,
                f"🎭 NEW EVOLUTION ADDED\n"
                f"🎭 {evo[1]} [{evo[0]}]\n"
                f"📺 Anime: {d['evo_anime'] or 'Not set'}\n"
                f"🏷 {_rarity_line(d['evo_rarity'])}\n"
                f"💰 Worth: {d['evo_worth']}\n"
                f"📷 Photo: Added\n"
                f"🧬 Recipe: {fusion_symbol(recipe)} {_ingredient_text(recipe)} ➡️ {evo[1]} [{evo[0]}]\n"
                f"💎 Evolution Stones: {d['evo_stones']}\n"
                f"🪙 Berries: {d['evo_berries']:,}\n"
                f"👤 By: {_by(user)}", actor_id=user.id)
        if _deps["mark_success"]:
            _deps["mark_success"](update)
    except Exception as e:
        logger.info("addevo notification skipped: %s", e)
    return -1


async def addevo_cancel(update, context):
    _clear_evo(context)
    if _deps.get("cancel_all"):             # the bot's universal /cancel: stops EVERYTHING in progress, replies, returns END
        await _deps["cancel_all"](update, context)
        return -1
    if update.effective_message is not None:
        await _reply(update.effective_message, "❌ Evolution setup cancelled.")
    return -1


# ==========================================================================
# /editevo - edit an EVOLUTION character and its recipe in one place (normal characters use /edit)
# ==========================================================================
(X_NAME, X_ANIME, X_RARITY, X_WORTH, X_PHOTO, X_CODE, X_BASE, X_QTY, X_STONES, X_BERRIES) = range(210, 220)
_XKEYS = ("eevo_code0", "eevo_row", "eevo_recipe", "eevo_name", "eevo_anime", "eevo_rarity", "eevo_worth",
          "eevo_photo", "eevo_code", "eevo_base", "eevo_qty", "eevo_stones", "eevo_berries")


def _clear_x(context):
    for k in _XKEYS:
        context.user_data.pop(k, None)


def _skip_markup():
    fn = _deps.get("skip_keyboard")
    return fn() if fn else None


def _is_skip(text):
    return bool(_deps["is_skip_text"](text))


def _creates_cycle(ingredient_codes, evo_code):
    """True if `evo_code` is already an ancestor of one of the ingredient cards through other recipes (loops like A->B, B->A)."""
    if isinstance(ingredient_codes, str):
        ingredient_codes = [ingredient_codes]
    return _is_ancestor(evo_code, ingredient_codes)


def validate_recipe_edit(evo_code0, new_code, base_code, base_qty, stones, berries, second_code=None, second_qty=None,
                         weapon_code=None):
    """Checks for /editevo (the evolution character already exists, so codes are compared against OTHER characters).
    A recipe that needs a weapon may have 0 or more Evolution Stones; every other recipe needs at least EVO_MIN_STONES."""
    base_code, new_code = str(base_code), str(new_code)
    pair = second_code is not None
    if not _valid_code(new_code):
        return "❌ The evolution code must be exactly 4 digits (0001-9999)."
    if new_code != str(evo_code0) and (_row(new_code) is not None or get_recipe_sync(new_code) is not None):
        return "❌ That code already exists."
    if not _valid_code(base_code) or _row(base_code) is None:
        return "❌ Card A does not exist." if pair else "❌ The base character code does not exist."
    if base_code == new_code:
        return "❌ A character cannot evolve into itself (the base code equals the evolution code)."
    if not isinstance(base_qty, int) or not (1 <= base_qty <= EVO_MAX_BASE_QTY):
        return f"❌ Base quantity must be a whole number from 1 to {EVO_MAX_BASE_QTY}."
    if pair:
        second_code = str(second_code)
        if not _valid_code(second_code) or _row(second_code) is None:
            return "❌ Card B does not exist."
        if second_code == base_code:
            return "❌ Card A and card B must be two different cards."
        if second_code == new_code:
            return "❌ A character cannot evolve into itself (card B equals the evolution code)."
        if not isinstance(second_qty, int) or not (1 <= second_qty <= EVO_MAX_BASE_QTY):
            return f"❌ Card B quantity must be a whole number from 1 to {EVO_MAX_BASE_QTY}."
    min_stones = 0 if weapon_code else EVO_MIN_STONES
    if not isinstance(stones, int) or stones < min_stones:
        return f"❌ Evolution Stones must be at least {min_stones}."
    if stones > EVO_MAX_STONES:
        return f"❌ Evolution Stones cannot be more than {EVO_MAX_STONES}."
    if not isinstance(berries, int) or berries < 0 or berries > EVO_MAX_BERRIES:
        return "❌ Berries cost must be a whole number (0 or more)."
    other = get_pair_recipe_sync(base_code, second_code) if pair else get_recipe_by_base_sync(base_code)
    if other is not None and str(other["_id"]) != str(evo_code0):
        return "❌ That " + ("pair of cards" if pair else "base character") + " already has another evolution recipe (conflict)."
    if _creates_cycle([base_code] + ([second_code] if pair else []), evo_code0):
        return "❌ That would create an evolution loop (an ingredient already comes from this evolution)."
    return None


def edit_evolution_sync(code0, v, edited_by):
    """
    Saves the character edit AND the recipe edit in ONE transaction (both or neither).
    v = {name, anime, rarity, worth, photo (or None to keep), code, base, qty, stones, berries[, second, qty2]}
    """
    pair = v.get("second") is not None
    weapon_code = (get_recipe_sync(code0) or {}).get("weapon_code")       # the weapon slot is kept as it is by /editevo
    err = validate_recipe_edit(code0, v["code"], v["base"], v["qty"], v["stones"], v["berries"],
                               v.get("second") if pair else None, v.get("qty2") if pair else None, weapon_code) \
        or heavenly_error(v["rarity"], [v["base"]] + ([v["second"]] if pair else []))
    if err:
        return {"ok": False, "error": err}
    if _name_taken_by_other(v["name"], code0):
        return {"ok": False, "error": "❌ A character with that name already exists."}

    def _work(session):
        done = mongo_db.update_character_tx(session, code0, v["code"], v["name"], v["anime"], v["rarity"], v["worth"],
                                            None, evolution=True)
        if not done:
            raise _EvoAbort("notevo")
        if v.get("photo"):
            mongo_db.col(mongo_db.CHARACTERS).update_one({"code": v["code"]}, {"$set": {"photo_file_id": v["photo"]}},
                                                         session=session)
        fields = {"evo_code": v["code"], "base_code": str(v["base"]), "base_qty": int(v["qty"]),
                  "stones": int(v["stones"]), "berries": int(v["berries"]), "kind": "pair" if pair else "same",
                  "pair_key": pair_key(v["base"], v["second"] if pair else None)}
        if pair:
            fields.update({"second_code": str(v["second"]), "second_qty": int(v["qty2"])})
        res = _recipes().update_one({"_id": v["code"]}, {"$set": fields}, session=session)
        if res.matched_count != 1:      # recipe had been deleted with /delevo: this edit recreates it
            _recipes().insert_one({"_id": v["code"], **fields, "created_by": int(edited_by), "created_at": _stamp()},
                                  session=session)

    try:
        mongo_db.run_transaction(_work)
    except _EvoAbort:
        return {"ok": False, "error": "❌ This is not an Evolution character (or it no longer exists)."}
    except mongo_db.DuplicateKeyError:
        return {"ok": False, "error": "❌ The name, code or card pair already has a record. Nothing was changed."}
    finally:
        mongo_db.invalidate_character_cache()
    return {"ok": True}


def _name_taken_by_other(name, code):
    folded = mongo_db.strip_evo_mark(name).casefold()
    return any(r[0] != str(code) and mongo_db.strip_evo_mark(r[1]).casefold() == folded for r in mongo_db.get_all_characters())


def _current(value):
    return "None (required)" if value in (None, "") else value


async def editevo_start(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return -1
    if update.effective_chat.type != "private":
        await _reply(msg, "⚠️ /editevo can only be used in the bot's PM (private chat).")
        return -1
    if not _is_staff_evo(user.id):              # Owner + Executive only
        await _reply(msg, NOT_ALLOWED_TEXT)
        return -1
    query = " ".join(getattr(context, "args", None) or []).strip()
    if not query:
        await _reply(msg, "Usage: /editevo <4-digit code or name of an Evolution character>")
        return -1
    q = mongo_db.strip_evo_mark(query)
    if _valid_code(q):
        row = await asyncio.to_thread(_row, q)
        rows = [row] if row else []
    else:
        rows = await asyncio.to_thread(mongo_db.find_characters_by_name_parts, q)
    if not rows:
        await _reply(msg, "❌ Character not found. Use the 4-digit code or the name.")
        return -1
    evo_rows = [r for r in rows if mongo_db.is_evolution_character(r[0])]
    if not evo_rows:
        await _reply(msg, "❌ That is a normal character. Normal characters are edited with /edit.")
        return -1
    if len(evo_rows) > 1:
        listing = "\n".join(f"• {r[1]} [{r[0]}]" for r in evo_rows[:10])
        await _reply(msg, f"❓ Several Evolution characters match. Send /editevo with the 4-digit code:\n{listing}")
        return -1
    row = evo_rows[0]
    _clear_x(context)
    d = context.user_data
    d["eevo_code0"], d["eevo_row"] = row[0], row
    d["eevo_recipe"] = await asyncio.to_thread(get_recipe_sync, row[0])
    d["eevo_kind"] = ("pair" if is_pair_recipe(d["eevo_recipe"]) else "same") if d["eevo_recipe"] else None
    await _reply(msg, f"✏️ Editing {row[1]} [{row[0]}] (Evolution)\n\n1️⃣ Send the new name, or tap ⏭ Skip to keep it."
                      f"\nCurrent: {mongo_db.strip_evo_mark(row[1])}", reply_markup=_skip_markup())
    return X_NAME


async def _x_gate(update, context):
    """Re-check the role on every step (it could be revoked mid-flow) and that the flow is still alive."""
    if not _is_staff_evo(update.effective_user.id):
        _clear_x(context)
        await _reply(update.effective_message, NOT_ALLOWED_TEXT)
        return False
    if "eevo_code0" not in context.user_data:
        await _reply(update.effective_message, "❌ The edit expired. Start again with /editevo.")
        return False
    return True


async def editevo_name(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    if _is_skip(msg.text):
        d["eevo_name"] = mongo_db.strip_evo_mark(d["eevo_row"][1])
    else:
        name = mongo_db.strip_evo_mark(msg.text)
        if not name:
            await _reply(msg, "❌ The name cannot be empty.")
            return X_NAME
        if await asyncio.to_thread(_name_taken_by_other, name, d["eevo_code0"]):
            await _reply(msg, "❌ A character with that name already exists. Send a different name.")
            return X_NAME
        d["eevo_name"] = name
    await _reply(msg, f"2️⃣ Anime name, or ⏭ Skip.\nCurrent: {d['eevo_row'][2]}", reply_markup=_skip_markup())
    return X_ANIME


async def editevo_anime(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    if _is_skip(msg.text):
        d["eevo_anime"] = d["eevo_row"][2]
    else:
        anime = (msg.text or "").strip()
        if not anime:
            await _reply(msg, "❌ The anime name cannot be empty.")
            return X_ANIME
        d["eevo_anime"] = anime
    await _reply(msg, f"3️⃣ Rarity (Common / Rare / Epic / Legendary / Mythical / Ethereal / Celestial / Heavenly), or ⏭ Skip.\n"
                      f"Current: {d['eevo_row'][3]}", reply_markup=_skip_markup())
    return X_RARITY


async def editevo_rarity(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    if _is_skip(msg.text):
        d["eevo_rarity"] = d["eevo_row"][3]
    else:
        rarity = (msg.text or "").strip().title()
        if rarity not in _deps["symbols"]:
            await _reply(msg, "❌ Invalid rarity.")
            return X_RARITY
        d["eevo_rarity"] = rarity
    await _reply(msg, f"4️⃣ Worth in Berries, or ⏭ Skip.\nCurrent: {d['eevo_row'][4]}", reply_markup=_skip_markup())
    return X_WORTH


async def editevo_worth(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    if _is_skip(msg.text):
        d["eevo_worth"] = int(d["eevo_row"][4] or 0)
    else:
        n = _parse_int(msg.text)
        if n is None or n > EVO_MAX_WORTH:
            await _reply(msg, "❌ Worth must be a whole number (0 or more).")
            return X_WORTH
        d["eevo_worth"] = n
    await _reply(msg, "5️⃣ Send the new photo, or ⏭ Skip to keep the current one.", reply_markup=_skip_markup())
    return X_PHOTO


async def editevo_photo(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    if getattr(msg, "photo", None):
        d["eevo_photo"] = msg.photo[-1].file_id
    elif _is_skip(msg.text):
        d["eevo_photo"] = None
    else:
        await _reply(msg, "❌ Send a photo, or tap ⏭ Skip.")
        return X_PHOTO
    await _reply(msg, f"6️⃣ Evolution character code (4 digits), or ⏭ Skip.\nCurrent: {d['eevo_code0']}",
                 reply_markup=_skip_markup())
    return X_CODE


def _remove_keyboard():
    try:
        from telegram import ReplyKeyboardRemove
        return ReplyKeyboardRemove()
    except Exception:
        return None


async def editevo_cancel(update, context):
    _clear_x(context)
    if _deps.get("cancel_all"):
        await _deps["cancel_all"](update, context)
        return -1
    if update.effective_message is not None:
        await _reply(update.effective_message, "❌ Evolution edit cancelled.", reply_markup=_remove_keyboard())
    return -1


# ==========================================================================
# /item (personal inventory) and /stone (stone leaderboard)
# ==========================================================================
# To add a future item: add ONE line here. Its count is read from the given field of the user's document
# (dotted paths allowed, e.g. "items.ticket"). Evolution Stone reuses the existing `special_stones` field.
ITEM_REGISTRY = (
    # (key, emoji, display name, field in the users document)
    ("evolution_stone", "💎", "Evolution Stone", "special_stones"),
)
LEADERBOARD_SIZE = 10
_MEDALS = {1: "🥇", 2: "🥈", 3: "🥉"}


def _dotted_get(doc, path):
    cur = doc
    for part in path.split("."):
        if not isinstance(cur, dict) or part not in cur:
            return 0
        cur = cur[part]
    try:
        return int(cur or 0)
    except (TypeError, ValueError):
        return 0


def item_text_sync(user_id):
    doc = mongo_db.col(USERS_COL).find_one({"_id": int(user_id)}) or {}
    lines = ["🎒 YOUR ITEMS", ""]
    for _key, emoji, name, field in ITEM_REGISTRY:
        lines.append(f"{emoji} {name}: {_dotted_get(doc, field)}")
    lines += rewards.item_lines(doc)         # Mystery Boxes the user owns (only listed here, opened from /invite)
    return "\n".join(lines)


def _user_label(doc):
    full = " ".join(v for v in (doc.get("first_name") or "", doc.get("last_name") or "") if v).strip()
    if full:
        return full
    if doc.get("username"):
        return "@" + str(doc["username"])
    return f"User {doc['_id']}"


def stone_leaderboard_sync(user_id, limit=LEADERBOARD_SIZE):
    users = mongo_db.col(USERS_COL)
    top = list(users.find({"special_stones": {"$gt": 0}}).sort([("special_stones", -1), ("_id", 1)]).limit(int(limit)))
    mine = int((users.find_one({"_id": int(user_id)}) or {}).get("special_stones") or 0)
    rank = users.count_documents({"special_stones": {"$gt": mine}}) + 1 if mine > 0 else None
    if not top:
        return "🏆 STONE LEADERBOARD\n\nNo one has any stones yet. Complete /stonetask to earn some!"
    lines = ["🏆 STONE LEADERBOARD", ""]
    for place, doc in enumerate(top, 1):
        lines.append(f"{_MEDALS.get(place, f'{place}.')} {_user_label(doc)} — 💎 {int(doc['special_stones'])}")
    lines.append("")
    lines.append(f"Your rank: #{rank} — 💎 {mine}" if rank else "You have no stones yet. Complete /stonetask to earn some!")
    return "\n".join(lines)


async def item_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None or user.is_bot:
        return
    await _reply(msg, await asyncio.to_thread(item_text_sync, user.id))


async def stone_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None or user.is_bot:
        return
    await _reply(msg, await asyncio.to_thread(stone_leaderboard_sync, user.id))


# ---------------------------------------------------------------- Different Card evolution: type chooser + extra steps
E_TYPE, E_ACODE, E_AQTY, E_BCODE, E_BQTY = range(220, 225)
X_BASE2, X_QTY2, X_KIND = range(225, 228)
_EVO_KEYS = _EVO_KEYS + ("evo_kind", "evo_second", "evo_second_name", "evo_qty2", "evo_phase")
_XKEYS = _XKEYS + ("eevo_kind", "eevo_second", "eevo_qty2")
_EMOJI = ["", "1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣", "6️⃣", "7️⃣", "8️⃣", "9️⃣", "🔟"]


def _stepno(context, n):
    """Step label. Same Card keeps the original 1️⃣..🔟; Different Card has two extra steps and uses 'Step N/12:'."""
    if context.user_data.get("evo_kind") == "pair":
        return f"Step {n + 2}/12:"
    return _EMOJI[n]


def _parse_kind(text):
    t = (text or "").strip().lower()
    if t in ("1", "s", "same", "same card"):
        return "same"
    if t in ("2", "d", "diff", "different", "two", "different card"):
        return "pair"
    return None


def _type_keyboard(uid):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    return InlineKeyboardMarkup([[InlineKeyboardButton("🌟 Same Card", callback_data=f"evoadd:{int(uid)}:same"),
                                  InlineKeyboardButton("💫 Different Card", callback_data=f"evoadd:{int(uid)}:diff")]])


def _begin_kind(context, kind):
    """Records the chosen type and returns (first question, next state)."""
    context.user_data["evo_kind"], context.user_data["evo_phase"] = kind, None
    if kind == "pair":
        return "Step 1/12: Enter the code of card A (for example Naruto):", E_ACODE
    return "Enter the code of the character you want to create an evolution for:", E_BASE


async def addevo_type_text(update, context):
    msg = update.effective_message
    if not _is_staff_evo(update.effective_user.id):
        _clear_evo(context)
        await _reply(msg, NOT_ALLOWED_TEXT)
        return -1
    kind = _parse_kind(msg.text)
    if kind is None:
        await _reply(msg, "❌ Choose Same Card or Different Card (or send 1 or 2).", reply_markup=_type_keyboard(update.effective_user.id))
        return E_TYPE
    text, state = _begin_kind(context, kind)
    await _reply(msg, text)
    return state


async def addevo_type_callback(update, context):
    """The two type buttons. Only the staff member who started /addevo can use them, and only while the setup is open."""
    q = update.callback_query
    if q is None or q.from_user is None:
        return None
    try:
        _tag, owner, choice = (q.data or "").split(":")
        owner = int(owner)
    except ValueError:
        await q.answer()
        return None
    if q.from_user.id != owner:
        await q.answer("❌ This is not your setup. Use /addevo.", show_alert=True)
        return None
    if not _is_staff_evo(q.from_user.id):
        await q.answer(NOT_ALLOWED_TEXT, show_alert=True)
        return None
    if context.user_data.get("evo_phase") != "type":
        await q.answer("⚠️ This setup is no longer active. Use /addevo.", show_alert=True)
        return None
    kind = "pair" if choice == "diff" else "same"
    text, state = _begin_kind(context, kind)
    await q.answer()
    title = "💫 Different Card" if kind == "pair" else "🌟 Same Card"
    try:
        await q.edit_message_text(f"{title}\n\n{text}")           # the buttons disappear, so a choice cannot be tapped twice
    except Exception:
        await _reply(q.message, text)
    return state


async def addevo_acode(update, context):
    msg = update.effective_message
    code = (msg.text or "").strip()
    row = _row(code) if _valid_code(code) else None
    if row is None:
        await _reply(msg, "❌ That card code does not exist. Evolution setup stopped.")
        _clear_evo(context)
        return -1
    context.user_data["evo_base"], context.user_data["evo_base_name"] = code, row[1]
    await _reply(msg, f"Step 2/12: How many copies of {row[1]} are required? (usually 1; 1-{EVO_MAX_BASE_QTY})")
    return E_AQTY


async def addevo_aqty(update, context):
    msg = update.effective_message
    n = _parse_int(msg.text)
    if n is None or not (1 <= n <= EVO_MAX_BASE_QTY):
        await _reply(msg, f"❌ Send a whole number from 1 to {EVO_MAX_BASE_QTY}.")
        return E_AQTY
    context.user_data["evo_qty"] = n
    await _reply(msg, "Step 3/12: Enter the code of card B (for example Sasuke):")
    return E_BCODE


async def addevo_bcode(update, context):
    msg, d = update.effective_message, context.user_data
    code = (msg.text or "").strip()
    row = _row(code) if _valid_code(code) else None
    if row is None:
        await _reply(msg, "❌ That card code does not exist. Evolution setup stopped.")
        _clear_evo(context)
        return -1
    if code == d.get("evo_base"):
        await _reply(msg, "❌ Card B must be a different card than card A. Send another code:")
        return E_BCODE
    if await asyncio.to_thread(get_pair_recipe_sync, d.get("evo_base"), code):
        await _reply(msg, "❌ This pair of cards already has an evolution recipe. Evolution setup stopped.")
        _clear_evo(context)
        return -1
    d["evo_second"], d["evo_second_name"] = code, row[1]
    await _reply(msg, f"Step 4/12: How many copies of {row[1]} are required? (usually 1; 1-{EVO_MAX_BASE_QTY})")
    return E_BQTY


async def addevo_bqty(update, context):
    msg = update.effective_message
    n = _parse_int(msg.text)
    if n is None or not (1 <= n <= EVO_MAX_BASE_QTY):
        await _reply(msg, f"❌ Send a whole number from 1 to {EVO_MAX_BASE_QTY}.")
        return E_BQTY
    context.user_data["evo_qty2"] = n
    await _reply(msg, f"{_stepno(context, 3)} Evolution Character Name:")
    return E_NAME


# ---------------------------------------------------------------- /editevo: the recipe steps for both types
def _xl(d, same_n, pair_n):
    return f"Step {pair_n}/12:" if d.get("eevo_kind") == "pair" else _EMOJI[same_n]


def _skip_hint(d):
    return ", or ⏭ Skip" if d["eevo_recipe"] else ""


async def _x_base_prompt(msg, d):
    recipe = d["eevo_recipe"]
    cur = recipe["base_code"] if recipe else None
    if d.get("eevo_kind") == "pair":
        text = f"{_xl(d, 7, 7)} Card A code{_skip_hint(d)}.\nCurrent: {_current(cur)}"
    else:
        text = (f"{_xl(d, 7, 7)} Base character code (the character that evolves into this one){_skip_hint(d)}.\n"
                f"Current: {_current(cur)}")
    await _reply(msg, text, reply_markup=_skip_markup() if recipe else None)


async def editevo_code(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    if _is_skip(msg.text):
        d["eevo_code"] = d["eevo_code0"]
    else:
        code = (msg.text or "").strip()
        if not _valid_code(code):
            await _reply(msg, "❌ Code must be exactly 4 digits (0001-9999).")
            return X_CODE
        if code != d["eevo_code0"] and (_row(code) is not None or await asyncio.to_thread(get_recipe_sync, code)):
            await _reply(msg, "❌ That code already exists.")
            return X_CODE
        d["eevo_code"] = code
    if d.get("eevo_kind") is None:           # the recipe was deleted with /delevo: say which kind to recreate
        await _reply(msg, "This evolution has no recipe now. Which kind should it be? Send Same (copies of one card) "
                          "or Different (two different cards).")
        return X_KIND
    await _x_base_prompt(msg, d)
    return X_BASE


async def editevo_kind(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    kind = _parse_kind(msg.text)
    if kind is None:
        await _reply(msg, "❌ Send Same or Different (or 1 or 2).")
        return X_KIND
    d["eevo_kind"] = kind
    await _x_base_prompt(msg, d)
    return X_BASE


async def editevo_base(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    recipe = d["eevo_recipe"]
    if recipe and _is_skip(msg.text):
        d["eevo_base"] = str(recipe["base_code"])
    else:
        code = (msg.text or "").strip()
        if not _valid_code(code) or await asyncio.to_thread(_row, code) is None:
            await _reply(msg, "❌ That " + ("card" if d.get("eevo_kind") == "pair" else "base character") + " code does not exist.")
            return X_BASE
        if code == d["eevo_code"]:
            await _reply(msg, "❌ A character cannot evolve into itself. Send a different base code.")
            return X_BASE
        d["eevo_base"] = code
    cur = recipe["base_qty"] if recipe else None
    await _reply(msg, f"{_xl(d, 8, 8)} {'Card A' if d.get('eevo_kind') == 'pair' else 'Base character'} quantity required "
                      f"(1-{EVO_MAX_BASE_QTY}){_skip_hint(d)}.\nCurrent: {_current(cur)}",
                 reply_markup=_skip_markup() if recipe else None)
    return X_QTY


async def editevo_qty(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    recipe = d["eevo_recipe"]
    if recipe and _is_skip(msg.text):
        d["eevo_qty"] = int(recipe["base_qty"])
    else:
        n = _parse_int(msg.text)
        if n is None or not (1 <= n <= EVO_MAX_BASE_QTY):
            await _reply(msg, f"❌ Send a whole number from 1 to {EVO_MAX_BASE_QTY}.")
            return X_QTY
        d["eevo_qty"] = n
    if d.get("eevo_kind") == "pair":
        cur = recipe.get("second_code") if recipe else None
        await _reply(msg, f"{_xl(d, 8, 9)} Card B code{_skip_hint(d)}.\nCurrent: {_current(cur)}",
                     reply_markup=_skip_markup() if recipe else None)
        return X_BASE2
    await _x_stones_prompt(msg, d)
    return X_STONES


async def editevo_base2(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    recipe = d["eevo_recipe"]
    if recipe and recipe.get("second_code") and _is_skip(msg.text):
        d["eevo_second"] = str(recipe["second_code"])
    else:
        code = (msg.text or "").strip()
        if not _valid_code(code) or await asyncio.to_thread(_row, code) is None:
            await _reply(msg, "❌ That card code does not exist.")
            return X_BASE2
        if code == d["eevo_base"]:
            await _reply(msg, "❌ Card B must be a different card than card A.")
            return X_BASE2
        if code == d["eevo_code"]:
            await _reply(msg, "❌ A character cannot evolve into itself. Send a different card code.")
            return X_BASE2
        d["eevo_second"] = code
    cur = recipe.get("second_qty") if recipe else None
    await _reply(msg, f"{_xl(d, 8, 10)} Card B quantity required (1-{EVO_MAX_BASE_QTY}){_skip_hint(d)}.\nCurrent: {_current(cur)}",
                 reply_markup=_skip_markup() if recipe else None)
    return X_QTY2


async def editevo_qty2(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    recipe = d["eevo_recipe"]
    if recipe and recipe.get("second_qty") and _is_skip(msg.text):
        d["eevo_qty2"] = int(recipe["second_qty"])
    else:
        n = _parse_int(msg.text)
        if n is None or not (1 <= n <= EVO_MAX_BASE_QTY):
            await _reply(msg, f"❌ Send a whole number from 1 to {EVO_MAX_BASE_QTY}.")
            return X_QTY2
        d["eevo_qty2"] = n
    await _x_stones_prompt(msg, d)
    return X_STONES


async def _x_stones_prompt(msg, d):
    recipe = d["eevo_recipe"]
    cur = recipe["stones"] if recipe else None
    min_s = 0 if (recipe or {}).get("weapon_code") else EVO_MIN_STONES
    await _reply(msg, f"{_xl(d, 9, 11)} Evolution Stones required (minimum {min_s}){_skip_hint(d)}.\nCurrent: {_current(cur)}",
                 reply_markup=_skip_markup() if recipe else None)


async def editevo_stones(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    recipe = d["eevo_recipe"]
    if recipe and _is_skip(msg.text):
        d["eevo_stones"] = int(recipe["stones"])
    else:
        n = _parse_int(msg.text)
        min_s = 0 if (recipe or {}).get("weapon_code") else EVO_MIN_STONES
        if n is None or n < min_s:
            await _reply(msg, f"❌ Evolution Stones must be a number of at least {min_s}.")
            return X_STONES
        if n > EVO_MAX_STONES:
            await _reply(msg, f"❌ Evolution Stones cannot be more than {EVO_MAX_STONES}.")
            return X_STONES
        d["eevo_stones"] = n
    cur = recipe["berries"] if recipe else None
    await _reply(msg, f"{_xl(d, 10, 12)} Berries cost{_skip_hint(d)}.\nCurrent: {_current(cur)}",
                 reply_markup=_skip_markup() if recipe else None)
    return X_BERRIES


async def editevo_berries(update, context):
    if not await _x_gate(update, context):
        return -1
    msg, d = update.effective_message, context.user_data
    recipe = d["eevo_recipe"]
    if recipe and _is_skip(msg.text):
        d["eevo_berries"] = int(recipe["berries"])
    else:
        n = _parse_int(msg.text)
        if n is None or n > EVO_MAX_BERRIES:
            await _reply(msg, "❌ Berries cost must be a whole number (0 or more).")
            return X_BERRIES
        d["eevo_berries"] = n
    pair = d.get("eevo_kind") == "pair"
    user, code0 = update.effective_user, d["eevo_code0"]
    values = {"name": d["eevo_name"], "anime": d["eevo_anime"], "rarity": d["eevo_rarity"], "worth": d["eevo_worth"],
              "photo": d["eevo_photo"], "code": d["eevo_code"], "base": d["eevo_base"], "qty": d["eevo_qty"],
              "stones": d["eevo_stones"], "berries": d["eevo_berries"]}
    if pair:
        values.update({"second": d["eevo_second"], "qty2": d["eevo_qty2"]})
    try:
        res = await asyncio.to_thread(edit_evolution_sync, code0, values, user.id)
    except Exception as e:
        logger.error("editevo failed: %s", e)
        _clear_x(context)
        await _reply(msg, "❌ Update failed. Nothing was changed. Please try again.")
        return -1
    _clear_x(context)
    if not res["ok"]:
        await _reply(msg, res["error"])
        return -1
    base, evo = _row(values["base"]), _row(values["code"])
    second = _row(values["second"]) if pair else None
    recipe_now = {"base_code": values["base"], "base_qty": values["qty"], "kind": "pair" if pair else "same",
                  "second_code": values.get("second"), "second_qty": values.get("qty2")}
    lines = f"{values['qty']}× {_char_label(base)}\n" + (f"+ {values['qty2']}× {_char_label(second)}\n" if pair else "")
    await _reply(
        msg,
        "✅ Evolution edited successfully!\n\n" + f"{fusion_symbol(recipe_now)} " + lines + f"➡️ {_char_label(evo)}\n"
        f"💰 Worth: {values['worth']}\n💎 {values['stones']} Stones • 🪙 {values['berries']:,} Berries",
        reply_markup=_remove_keyboard())
    try:
        if _deps["log_action"]:
            await asyncio.to_thread(_deps["log_action"], values["code"], values["name"], user, "edit")
        if _deps["notify"]:
            code_line = f"🔁 Old code: {code0}\n" if code0 != values["code"] else f"🔢 Code: {values['code']}\n"
            await _deps["notify"](
                context,
                f"✏️ EVOLUTION UPDATED\n"
                f"🎭 {evo[1]} [{evo[0]}]\n"
                f"📺 Anime: {values['anime'] or 'Not set'}\n"
                f"🏷 {_rarity_line(values['rarity'])}\n"
                f"💰 Worth: {values['worth']}\n"
                f"📷 Photo: {'Updated' if values['photo'] else 'Unchanged'}\n"
                f"🧬 Recipe: {fusion_symbol(recipe_now)} {_ingredient_text(recipe_now)} ➡️ {evo[1]} [{evo[0]}]\n"
                f"💎 Evolution Stones: {values['stones']}\n"
                f"🪙 Berries: {values['berries']:,}\n"
                f"{code_line}"
                f"👤 By: {_by(user)}", actor_id=user.id)
        if _deps["mark_success"]:
            _deps["mark_success"](update)
    except Exception as e:
        logger.info("editevo notification skipped: %s", e)
    return -1


def _register_evolution(app):
    from telegram.ext import (CallbackQueryHandler, CommandHandler, ConversationHandler, MessageHandler, filters)
    text = filters.TEXT & ~filters.COMMAND
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("addevo", addevo_start),
                      CallbackQueryHandler(addevo_type_callback, pattern=r"^evoadd:\d+:(same|diff)$")],
        states={
            E_TYPE: [MessageHandler(text, addevo_type_text)],
            E_ACODE: [MessageHandler(text, addevo_acode)],
            E_AQTY: [MessageHandler(text, addevo_aqty)],
            E_BCODE: [MessageHandler(text, addevo_bcode)],
            E_BQTY: [MessageHandler(text, addevo_bqty)],
            E_BASE: [MessageHandler(text, addevo_base)],
            E_QTY: [MessageHandler(text, addevo_qty)],
            E_NAME: [MessageHandler(text, addevo_name)],
            E_ANIME: [MessageHandler(text, addevo_anime)],
            E_RARITY: [MessageHandler(text, addevo_rarity)],
            E_WORTH: [MessageHandler(text, addevo_worth)],
            E_STONES: [MessageHandler(text, addevo_stones)],
            E_BERRIES: [MessageHandler(text, addevo_berries)],
            E_CODE: [MessageHandler(text, addevo_code)],
            E_PHOTO: [MessageHandler(filters.PHOTO, addevo_photo), MessageHandler(text, addevo_photo)],
        },
        fallbacks=[CommandHandler("cancel", addevo_cancel)],
        allow_reentry=True,
        conversation_timeout=_deps["conv_timeout"],
    ))
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("editevo", editevo_start)],
        states={
            X_NAME: [MessageHandler(text, editevo_name)],
            X_ANIME: [MessageHandler(text, editevo_anime)],
            X_RARITY: [MessageHandler(text, editevo_rarity)],
            X_WORTH: [MessageHandler(text, editevo_worth)],
            X_PHOTO: [MessageHandler(filters.PHOTO, editevo_photo), MessageHandler(text, editevo_photo)],
            X_CODE: [MessageHandler(text, editevo_code)],
            X_KIND: [MessageHandler(text, editevo_kind)],
            X_BASE: [MessageHandler(text, editevo_base)],
            X_QTY: [MessageHandler(text, editevo_qty)],
            X_BASE2: [MessageHandler(text, editevo_base2)],
            X_QTY2: [MessageHandler(text, editevo_qty2)],
            X_STONES: [MessageHandler(text, editevo_stones)],
            X_BERRIES: [MessageHandler(text, editevo_berries)],
        },
        fallbacks=[CommandHandler("cancel", editevo_cancel)],
        allow_reentry=True,
        conversation_timeout=_deps["conv_timeout"],
    ))
    app.add_handler(CommandHandler("evolution", evolution_command))
    app.add_handler(CommandHandler("evolve", evolve_command))
    app.add_handler(CommandHandler("delevo", delevo_command))
    app.add_handler(CommandHandler("item", item_command))
    app.add_handler(CommandHandler("stone", stone_command))
    app.add_handler(CallbackQueryHandler(evolve_callback, pattern=r"^evo:(go|pick):\d+:\d{4}$"))


# ==========================================================================
# STONE TASK COMPLETION REMINDERS
# ==========================================================================
# When a stone task becomes claimable, the player gets ONE message per task with the existing 💎 CLAIM STONE button
# (the same button/handler as /stonetask, so claiming works exactly the same). Each task is announced once per period
# through a "notified.<task>" flag on the task document. Nothing about progress, rewards or claiming changes.
# bot.py hook (after the catch / sell reply):  await fusion.stone_remind(user_id, chat_id=..., name=...)
_stone_deps = {"bot": None}      # set by _register_stone(app)


async def _notify_user(bot, user_id, text, reply_markup=None, chat_id=None, name=None):
    """Stateless sender: the player's private chat first; if that is impossible, the chat where it happened."""
    if bot is None:
        return False
    try:
        await bot.send_message(chat_id=int(user_id), text=text, reply_markup=reply_markup)
        return True
    except Exception as e:      # e.g. the player never opened a private chat with the bot
        logger.info("notification DM skipped: %s", e)
    if chat_id and int(chat_id) != int(user_id):
        try:
            await bot.send_message(chat_id=int(chat_id), text=(f"👤 {name}\n\n" if name else "") + text,
                                   reply_markup=reply_markup)
            return True
        except Exception as e:
            logger.info("notification chat fallback skipped: %s", e)
    return False


def stone_ready_sync(user_id):
    """Stone tasks that are completed, not yet claimed and not yet announced. Marks them announced (once per period)."""
    user_id = int(user_id)
    day, week = current_day_key(), current_week_key()
    keys = []
    for key in TASK_ORDER:
        flt = _claim_filter(user_id, day, key, week)        # completed AND not claimed (same rule the claim uses)
        flt[f"notified.{key}"] = {"$ne": True}
        if _tasks().update_one(flt, {"$set": {f"notified.{key}": True}}).modified_count == 1:
            keys.append(key)
    return keys


def stone_reminder_text(key, now=None):
    now = now or _now()
    reward = REWARDS[key]
    reset = (f"Daily reset in {format_countdown(now)}" if key in DAILY_KEYS
             else f"Weekly reset in {format_weekly_countdown(now)}")
    return ("💎 STONE TASK COMPLETE!\n\n"
            f"{TITLES[key]}\n"
            f"Reward: 💎 {reward} {'Stone' if reward == 1 else 'Stones'}\n\n"
            "👇 Tap CLAIM STONE to collect it before the reset.\n"
            f"⏳ {reset}")


async def stone_remind(user_id, chat_id=None, name=None):
    """Never raises: a reminder problem must not break /add or /sell."""
    try:
        keys = await asyncio.to_thread(stone_ready_sync, user_id)
        for key in keys:
            await _notify_user(_stone_deps["bot"], user_id, stone_reminder_text(key), _keyboard(user_id), chat_id, name)
    except Exception as e:
        logger.error("stone task reminder failed: %s", e)


# ==========================================================================
# DAILY MISSIONS (/dailytask)
# ==========================================================================
# Separate from the stone tasks above and from the existing /daily command (login streak), which is NOT touched.
# Works like the stone tasks: finish a mission -> you get ONE message with a 💰 CLAIM BERRYS button -> claiming pays
# the Berrys (also available from the button under /dailytask). Unclaimed rewards expire at the daily reset.
# bot.py hooks (all functions here are prefixed dt_ / _dt_ so nothing above is overridden):
#     await fusion.dt_record_catch(user_id, rarity, code, event_id=..., chat_id=..., name=...)      # end of add(), after the catch reply
#     await fusion.dt_record_purchase(user_id, rarity, qty, event_id=..., chat_id=..., name=...)    # shop buy handler, ONLY after a successful purchase
#     (chat_id/name are optional: used only if the player cannot be messaged privately)
#     fusion.bind_dailytask(back_callback="<your menu's Back callback_data>")   # optional
# /dailytask + its buttons are registered by fusion.register(app) (through _register_dailytask).
# 10 missions, max 2,450 Berrys per daily cycle. Reset 02:00 AM IST on its own clock (_dt_day_key), independent of the stone tasks.
# Storage: collection "daily_missions" (one doc per user per task day) + users.coins (Berrys).
#     progress.*  counters   claimed.<mission>  paid flag   notified.<mission>  announced flag   events  duplicate-event guard
# Each mission is paid once through a conditional "not yet claimed" flip inside one transaction.

MISSIONS_COL = "daily_missions"
CURRENCY_FIELD = "coins"          # Berrys (existing users field)

Mission = namedtuple("Mission", "key emoji name task needed reward counter")

MISSIONS = (
    # --- catching ---
    Mission("beginner", "🥉", "Beginner Catcher", "Catch 4 characters", 4, 150, "catch"),
    Mission("unique", "🆕", "Unique Hunter", "Catch 1 previously unowned character", 1, 200, "new"),
    Mission("pro", "⚔️", "Pro Catcher", "Catch 10 characters", 10, 500, "catch"),
    Mission("explorer", "🌍", "Anime Explorer", "Catch characters from 5 different anime series", 5, 200, "series"),
    Mission("rare", "🔵", "Rare Hunter", "Catch 7 Rare characters", 7, 300, "rare"),
    Mission("common", "⚪", "Common Hunter", "Catch 10 Common characters", 10, 300, "common"),
    Mission("epic", "🟣", "Epic Hunter", "Catch 5 Epic characters", 5, 200, "epic"),
    # --- shop ---
    Mission("buy_legendary", "💎", "Legendary Buyer", "Purchase 1 Legendary character from the shop", 1, 200, "shop_legendary"),
    Mission("buy_mythical", "🔮", "Mythical Buyer", "Purchase 1 Mythical character from the shop", 1, 200, "shop_mythical"),
    Mission("shopper", "🛍️", "Shopping Expert", "Purchase 3 shop items", 3, 200, "shop_any"),
)
TOTAL_REWARD = sum(m.reward for m in MISSIONS)      # 2,450
assert TOTAL_REWARD == 2450 and len(MISSIONS) == 10

_CATCH_RARITY_COUNTERS = ("common", "rare", "epic")   # only these rarities have a catching mission
_SHOP_RARITY_COUNTERS = ("legendary", "mythical")

# Daily missions have their OWN reset clock (02:00 AM IST). It does not use the stone tasks' current_day_key /
# format_countdown / RESET_HOUR_IST, so changing or breaking one system can never move or break the other.
_DT_IST = timezone(timedelta(hours=5, minutes=30))
_DT_RESET_HOUR_IST = 2


def _dt_day_key(now=None):
    """Daily-mission 'task day' (YYYY-MM-DD, IST, 02:00 AM cutoff)."""
    ist = (now or datetime.now(timezone.utc)).astimezone(_DT_IST)
    day = ist.date() if ist.hour >= _DT_RESET_HOUR_IST else (ist - timedelta(days=1)).date()
    return day.isoformat()


def _dt_countdown(now=None):
    """'7h 25m' until the next daily-mission reset."""
    now = now or datetime.now(timezone.utc)
    ist = now.astimezone(_DT_IST)
    reset = ist.replace(hour=_DT_RESET_HOUR_IST, minute=0, second=0, microsecond=0)
    if ist >= reset:
        reset += timedelta(days=1)
    secs = max(0, int((reset - ist).total_seconds()))
    hours, minutes = secs // 3600, (secs % 3600) // 60
    return "less than 1m" if hours == 0 and minutes == 0 else f"{hours}h {minutes}m"


_dt_deps = {
    "bot": None,             # set by _register_dailytask(app); used to send the completion messages
    "back_callback": None,   # optional: callback_data of the existing menu's "⬅️ Back" button
}
_dt_state = {"purged_day": None}


def bind_dailytask(**kwargs):
    """Optional: fusion.bind_dailytask(back_callback="your_menu_callback") makes ⬅️ Back open your existing menu.
    Without it, ⬅️ Back simply closes the /dailytask message."""
    _dt_deps.update({k: v for k, v in kwargs.items() if v is not None})


# --------------------------------------------------------------------------
# Database helpers (blocking - always call through asyncio.to_thread from handlers)
# --------------------------------------------------------------------------
def _dt_col():
    return mongo_db.col(MISSIONS_COL)


def _dt_doc_id(user_id, day):
    return f"{int(user_id)}:{day}"


def _dt_purge_expired(day):
    """Drop previous days' mission documents once per process per day (they can never be claimed again)."""
    if _dt_state["purged_day"] == day:
        return
    try:
        _dt_col().delete_many({"day": {"$lt": day}})
        _dt_state["purged_day"] = day
    except Exception as e:
        logger.warning("daily mission purge failed: %s", e)


def _dt_value(progress, mission):
    """Current progress number for a mission (Anime Explorer counts DISTINCT anime series)."""
    if mission.counter == "series":
        return len(progress.get("series") or [])
    return int(progress.get(mission.counter, 0) or 0)


def _dt_bump(user_id, incs, series=None, event_id=None):
    """
    Atomic progress update. With an event_id the same event can never count twice: the filter requires that
    the id is not stored yet, and a replay then fails with a duplicate-key error on the upsert (-> ignored).
    Returns False when the event was a duplicate.
    """
    day = _dt_day_key()
    _dt_purge_expired(day)
    doc_id = _dt_doc_id(user_id, day)
    flt = {"_id": doc_id}
    update = {"$setOnInsert": {"user_id": int(user_id), "day": day}}
    if incs:
        update["$inc"] = incs
    add = {}
    if series:
        add["progress.series"] = series
    if event_id:
        flt["events"] = {"$ne": str(event_id)}
        add["events"] = str(event_id)
    if add:
        update["$addToSet"] = add
    try:
        _dt_col().update_one(flt, update, upsert=True)
    except mongo_db.DuplicateKeyError:
        return False
    return True


def dt_notices_sync(user_id):
    """
    Missions that are completed, not yet claimed and not yet announced. Each one is marked announced with a conditional
    update, so a mission is announced exactly once per daily cycle even if several catches/purchases race.
    """
    user_id = int(user_id)
    doc_id = _dt_doc_id(user_id, _dt_day_key())
    doc = _dt_col().find_one({"_id": doc_id})
    if not doc:
        return []
    progress, claimed, notified = doc.get("progress") or {}, doc.get("claimed") or {}, doc.get("notified") or {}
    out = []
    for m in MISSIONS:
        if claimed.get(m.key) or notified.get(m.key) or _dt_value(progress, m) < m.needed:
            continue
        res = _dt_col().update_one({"_id": doc_id, f"notified.{m.key}": {"$ne": True}},
                                   {"$set": {f"notified.{m.key}": True}})
        if res.modified_count == 1:
            out.append(m)
    return out


def dt_balance_sync(user_id):
    doc = mongo_db.col(USERS_COL).find_one({"_id": int(user_id)}, {CURRENCY_FIELD: 1})
    return int((doc or {}).get(CURRENCY_FIELD) or 0)


def dt_claim_all_sync(user_id):
    """
    Shared claim logic for the CLAIM BERRYS button. Pays every completed-but-unclaimed mission of today exactly once.
    Returns {"status": "ok"|"nothing"|"nouser", "missions": [Mission...], "berrys": int, "balance": int}.
    """
    user_id = int(user_id)
    if mongo_db.col(USERS_COL).find_one({"_id": user_id}, {"_id": 1}) is None:
        return {"status": "nouser", "missions": [], "berrys": 0, "balance": 0}
    doc_id = _dt_doc_id(user_id, _dt_day_key())
    doc = _dt_col().find_one({"_id": doc_id}) or {}
    progress, claimed = doc.get("progress") or {}, doc.get("claimed") or {}
    due = [m for m in MISSIONS if not claimed.get(m.key) and _dt_value(progress, m) >= m.needed]
    if not due:
        return {"status": "nothing", "missions": [], "berrys": 0, "balance": dt_balance_sync(user_id)}

    def _work(session):
        paid, total = [], 0
        for m in due:
            res = _dt_col().update_one(
                {"_id": doc_id, f"claimed.{m.key}": {"$ne": True}},
                {"$set": {f"claimed.{m.key}": True}}, session=session)
            if res.modified_count == 1:          # we (and only we) flipped it -> we pay it
                paid.append(m)
                total += m.reward
        if total:
            res = mongo_db.col(USERS_COL).update_one(
                {"_id": user_id}, {"$inc": {CURRENCY_FIELD: total}}, session=session)
            if res.matched_count != 1:
                raise RuntimeError("berry payout failed: user missing")   # aborts the transaction
        return paid, total

    paid, total = mongo_db.run_transaction(_work)
    return {"status": "ok" if paid else "nothing", "missions": paid, "berrys": total,
            "balance": dt_balance_sync(user_id)}


def dt_record_catch_sync(user_id, rarity, code, event_id=None, is_new=None):
    """
    Called after a SUCCESSFUL /add catch (the copy must already be saved; failed catches never reach this).
    Returns the missions that just became claimable (to announce).
    is_new: pass True/False if bot.py already knows the character was unowned; otherwise it is derived from the
    number of copies the player owns after the catch (exactly 1 -> it was genuinely new).
    """
    row = mongo_db.get_character_by_code(code)       # (code, name, anime, rarity, worth, photo, ...)
    if row is None:
        return []
    incs = {"progress.catch": 1}
    key = str(rarity or row[3] or "").strip().lower()
    if key in _CATCH_RARITY_COUNTERS:
        incs[f"progress.{key}"] = 1
    if is_new is None:
        is_new = mongo_db.count_user_copies(user_id, code) <= 1
    if is_new:
        incs["progress.new"] = 1
    anime = str(row[2] or "").strip().casefold()
    if not _dt_bump(user_id, incs, series=anime or None, event_id=event_id):
        return []                                    # duplicate event: no progress, nothing to announce
    return dt_notices_sync(user_id)


def dt_record_purchase_sync(user_id, rarity, quantity=1, event_id=None):
    """Called ONLY after a successful shop purchase of a character (cancelled/failed purchases never reach this)."""
    quantity = int(quantity)
    if quantity <= 0:
        return []
    incs = {"progress.shop_any": quantity}
    key = str(rarity or "").strip().lower()
    if key in _SHOP_RARITY_COUNTERS:
        incs[f"progress.shop_{key}"] = quantity
    if not _dt_bump(user_id, incs, event_id=event_id):
        return []
    return dt_notices_sync(user_id)


# --------------------------------------------------------------------------
# Texts, buttons, notifications
# --------------------------------------------------------------------------
def dt_notice_text(mission, now=None):
    return ("🎉 Mission Complete!\n\n"
            f"{mission.emoji} {mission.name}\n"
            f"✔️ {mission.task}\n\n"
            f"💰 Reward: {mission.reward:,} Berrys\n\n"
            "👇 Tap CLAIM BERRYS to collect it.\n"
            f"⌛ Unclaimed rewards expire in {_dt_countdown(now)} (daily reset).")


def dt_claim_text(result):
    if result["status"] == "nouser":
        return "❌ Please use /start first."
    if result["status"] == "nothing":
        return ("❌ No completed missions to claim right now.\n"
                "Finish a mission first - rewards must be claimed before the 2:00 AM IST reset.")
    lines = ["💰 BERRYS CLAIMED!", ""]
    for m in result["missions"]:
        lines.append(f"{m.emoji} {m.name}: +{m.reward:,} Berrys added to your balance!")
    lines += ["", f"Total: +{result['berrys']:,} Berrys", f"Your Berrys: {result['balance']:,}"]
    return "\n".join(lines)


def _dt_keyboard(user_id, back=True):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    rows = [[InlineKeyboardButton("💰 CLAIM BERRYS", callback_data=f"dtask:claim:{int(user_id)}:{_dt_day_key()}")]]
    if back:
        cb = _dt_deps.get("back_callback") or f"dailytask:back:{int(user_id)}"
        rows.append([InlineKeyboardButton("⬅️ Back", callback_data=cb)])
    return InlineKeyboardMarkup(rows)


async def _dt_notify(user_id, missions, bot=None, chat_id=None, name=None):
    """One message (with the CLAIM BERRYS button) per mission that just became claimable."""
    if not missions:
        return
    bot = bot or _dt_deps.get("bot")
    for m in missions:
        await _notify_user(bot, user_id, dt_notice_text(m), _dt_keyboard(user_id, back=False), chat_id, name)


async def dt_record_catch(user_id, rarity, code, event_id=None, is_new=None, chat_id=None, name=None):
    """Never raises: a mission problem must not break /add."""
    try:
        missions = await asyncio.to_thread(dt_record_catch_sync, user_id, rarity, code, event_id, is_new)
        await _dt_notify(user_id, missions, chat_id=chat_id, name=name)
    except Exception as e:
        logger.error("daily mission catch tracking failed: %s", e)


async def dt_record_purchase(user_id, rarity, quantity=1, event_id=None, chat_id=None, name=None):
    """Never raises: a mission problem must not break the shop."""
    try:
        missions = await asyncio.to_thread(dt_record_purchase_sync, user_id, rarity, quantity, event_id)
        await _dt_notify(user_id, missions, chat_id=chat_id, name=name)
    except Exception as e:
        logger.error("daily mission purchase tracking failed: %s", e)


def dt_build_view_sync(user_id, now=None):
    """The /dailytask text for this user (plain numeric progress, no progress bars)."""
    day = _dt_day_key(now)
    doc = _dt_col().find_one({"_id": _dt_doc_id(user_id, day)}) or {}
    progress, claimed = doc.get("progress") or {}, doc.get("claimed") or {}
    lines = ["🎯 DAILY TASKS", ""]
    earned = ready = done_count = 0
    for m in MISSIONS:
        value = _dt_value(progress, m)
        n = min(value, m.needed)
        lines += [f"{m.emoji} {m.name}", f"Task: {m.task}", f"Progress: {n}/{m.needed}", f"Reward: {m.reward:,} Berrys"]
        if claimed.get(m.key):
            earned += m.reward
            done_count += 1
            lines.append("🎁 Claimed")
        elif value >= m.needed:
            ready += m.reward
            done_count += 1
            lines.append("✅ Completed - tap CLAIM BERRYS!")
        lines.append("")
    lines += ["━━━━━━━━━━━━━━", "",
              f"💰 Rewards Earned: {earned:,} / {TOTAL_REWARD:,} Berrys"]
    if ready:
        lines.append(f"🎁 Ready to Claim: {ready:,} Berrys")
        lines.append("⌛ Unclaimed rewards expire at the daily reset!")
    lines += [f"🏆 Missions Completed: {done_count} / {len(MISSIONS)}",
              f"⏳ Reset in: {_dt_countdown(now)}"]
    return "\n".join(lines)


# --------------------------------------------------------------------------
# Telegram handlers (telegram imports are lazy, like the stone handlers)
# --------------------------------------------------------------------------
async def dailytask_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None or user.is_bot:
        return
    try:
        await asyncio.to_thread(dt_notices_sync, user.id)    # the list itself shows what is ready: mark as seen
        text = await asyncio.to_thread(dt_build_view_sync, user.id)
    except Exception as e:
        logger.error("/dailytask failed: %s", e)
        await msg.reply_text("❌ Could not load your daily missions. Please try again.")
        return
    await msg.reply_text(text, reply_markup=_dt_keyboard(user.id))


async def dailytask_claim_callback(update, context):
    q = update.callback_query
    if q is None or q.from_user is None:
        return
    try:
        owner_id = int(q.data.split(":")[2])
    except (IndexError, ValueError):
        await q.answer()
        return
    if q.from_user.id != owner_id:
        await q.answer("❌ This is not your mission list. Use /dailytask.", show_alert=True)
        return
    parts = (q.data or "").split(":")
    if len(parts) > 3 and parts[3] != _dt_day_key():          # button from a previous daily cycle
        await q.answer("⌛ This reward expired at the daily reset. Unclaimed rewards cannot be claimed.\n"
                       "Use /dailytask for today's missions.", show_alert=True)
        try:
            await q.edit_message_reply_markup(reply_markup=None)     # remove the dead button
        except Exception as e:
            logger.info("expired claim button cleanup skipped: %s", e)
        return
    try:
        result = await asyncio.to_thread(dt_claim_all_sync, owner_id)
    except Exception as e:
        logger.error("daily mission claim failed: %s", e)
        await q.answer("❌ Could not claim right now. Please try again.", show_alert=True)
        return
    if result["status"] == "ok":
        await q.answer(f"💰 +{result['berrys']:,} Berrys claimed!")
        try:
            await q.message.reply_text(dt_claim_text(result))
            text = await asyncio.to_thread(dt_build_view_sync, owner_id)
            await q.edit_message_text(text, reply_markup=_dt_keyboard(owner_id))
        except Exception as e:   # e.g. "message is not modified" - the claim itself already succeeded
            logger.info("daily mission view refresh skipped: %s", e)
    else:
        await q.answer(dt_claim_text(result), show_alert=True)


async def dailytask_back_callback(update, context):
    """Default ⬅️ Back: closes the missions message (only for its owner). Replaced by bind_dailytask(back_callback=...)."""
    q = update.callback_query
    if q is None or q.from_user is None:
        return
    try:
        owner_id = int(q.data.split(":")[2])
    except (IndexError, ValueError):
        await q.answer()
        return
    if q.from_user.id != owner_id:
        await q.answer("❌ This is not your mission list. Use /dailytask.", show_alert=True)
        return
    await q.answer()
    try:
        await q.message.delete()
    except Exception as e:
        logger.info("dailytask back skipped: %s", e)


def _register_dailytask(app):
    """Attach /dailytask, its CLAIM BERRYS button and its Back button. Does not register, replace or touch /daily."""
    from telegram.ext import CallbackQueryHandler, CommandHandler
    _dt_deps["bot"] = app.bot
    app.add_handler(CommandHandler("dailytask", dailytask_command))
    app.add_handler(CallbackQueryHandler(dailytask_claim_callback, pattern=r"^dtask:claim:\d+(:\d{4}-\d{2}-\d{2})?$"))
    app.add_handler(CallbackQueryHandler(dailytask_back_callback, pattern=r"^dailytask:back:\d+$"))


# ==========================================================================
# WEAPONS: weapon items, weapon shop, group drops, and the weapon slot of an evolution recipe
# ==========================================================================
# Storage: weapons (catalog, _id = the 4-digit weapon code), user_weapons (_id = "<user_id>:<code>", qty), weapon_settings (_id = "drops"),
# weapon_drops (one doc per drop). Berries = users.coins. A recipe may carry weapon_code: /evolve then also uses up 1 weapon.
# Commands: public /weapons /weaponshop | Owner+Executive /addweapon /editweapon /weaponlist /evoweapon |
#           Owner /delweapon /giveweapon /weapondrops /dropgroups /dropconfig /dropnow
import re
import secrets

WEAPONS_COL = "weapons"
USER_WEAPONS_COL = "user_weapons"
SETTINGS_COL = "weapon_settings"
DROPS_COL = "weapon_drops"

BERRY = "⦵"
MAX_PRICE = 1_000_000_000
MAX_QTY = 99
MAX_STOCK = 1000
TICK_SECONDS = 15

WEAPON_PUBLIC_COMMANDS = {"weapons", "weaponshop", "weaponlist"}
WEAPON_STAFF_COMMANDS = {"addweapon", "editweapon", "evoweapon"}        # Owner + Executive
WEAPON_OWNER_COMMANDS = {"delweapon", "giveweapon", "weapondrops", "dropgroups", "dropconfig", "dropnow"}
WEAPON_COMMAND_DESCRIPTIONS = {
    "weapons": "View your weapons",
    "weaponshop": "Open the weapon shop",
    "addweapon": "Owner/Executive: add a weapon (PM)",
    "editweapon": "Owner/Executive: edit a weapon",
    "weaponlist": "See every weapon",
    "evoweapon": "Owner/Executive: set the weapon an evolution needs",
    "delweapon": "Owner: delete a weapon",
    "giveweapon": "Owner: give a weapon to a user",
    "weapondrops": "Owner: manage weapon drops",
    "dropgroups": "Owner: choose the groups that get weapon drops",
    "dropconfig": "Owner: drop timing, stock and prices",
    "dropnow": "Owner: start a weapon drop now",
}


# ---------------------------------------------------------------- small helpers
def _col(name):
    return mongo_db.col(name)


def _utcnow():
    return datetime.now(timezone.utc)


def _aware(dt):
    if dt is not None and dt.tzinfo is None:
        return dt.replace(tzinfo=timezone.utc)
    return dt


def _is_owner(uid):
    return bool(_deps["is_owner"](uid))


def _is_staff(uid):
    return bool(_deps["is_owner"](uid) or _deps["is_executive"](uid))


def _rarity_text(rarity):
    fn = _deps.get("rarity_text")
    if fn:
        return fn(rarity)
    return f"{_deps['symbols'].get(rarity, '⭐')} {rarity}"


def _rarities():
    return [r for r in _deps["symbols"] if r != "Special"]


def norm_code(text):
    """A weapon code is a unique 4-digit code like characters and evolutions (0001-9999); None when it is not one."""
    t = str(text or "").strip()
    return t if _valid_code(t) else None


async def _notify(context, text, user):
    try:
        if _deps.get("notify"):
            await _deps["notify"](context, text, actor_id=user.id)
    except Exception as e:
        logger.info("weapon notification skipped: %s", e)


def _success(update):
    try:
        if _deps.get("mark_success"):
            _deps["mark_success"](update)
    except Exception:
        pass


def _weapon_label(w):
    return f"{w['name']} [{w['_id']}]"


# ---------------------------------------------------------------- weapon catalog + inventory (sync)
def get_weapon(code):
    return _col(WEAPONS_COL).find_one({"_id": code}) if code else None


def all_weapons():
    return sorted(_col(WEAPONS_COL).find({}), key=lambda w: w["_id"])


def find_weapon(query):
    """A weapon by code or by name (exact, then a unique partial match). Returns (weapon|None, error|None)."""
    code = norm_code(query)
    if code:
        w = get_weapon(code)
        return (w, None) if w else (None, "❌ That weapon code does not exist.")
    q = str(query or "").strip().casefold()
    if not q:
        return None, "❌ Send a weapon code or name."
    items = all_weapons()
    exact = [w for w in items if w["name"].casefold() == q]
    part = exact or [w for w in items if q in w["name"].casefold()]
    if len(part) == 1:
        return part[0], None
    if not part:
        return None, "❌ Weapon not found."
    return None, "❓ Several weapons match that name. Please use the weapon code."


def _inv_id(user_id, code):
    return f"{int(user_id)}:{code}"


def count_user_weapon(user_id, code, session=None):
    doc = _col(USER_WEAPONS_COL).find_one({"_id": _inv_id(user_id, code)}, session=session)
    return int((doc or {}).get("qty") or 0)


def add_user_weapon(user_id, code, qty=1, session=None):
    _col(USER_WEAPONS_COL).update_one(
        {"_id": _inv_id(user_id, code)},
        {"$inc": {"qty": int(qty)}, "$setOnInsert": {"user_id": int(user_id), "weapon_code": code}},
        upsert=True, session=session)


def take_user_weapon(user_id, code, qty=1, session=None):
    """Removes `qty` weapons only if the user really has them. True when taken."""
    col = _col(USER_WEAPONS_COL)
    res = col.update_one({"_id": _inv_id(user_id, code), "qty": {"$gte": int(qty)}}, {"$inc": {"qty": -int(qty)}},
                         session=session)
    if res.modified_count != 1:
        return False
    col.delete_one({"_id": _inv_id(user_id, code), "qty": {"$lte": 0}}, session=session)
    return True


def user_weapons_sync(user_id):
    """[(weapon, qty), ...] sorted by code, only weapons that still exist."""
    rows = list(_col(USER_WEAPONS_COL).find({"user_id": int(user_id), "qty": {"$gt": 0}}))
    out = []
    for r in sorted(rows, key=lambda x: str(x.get("weapon_code"))):
        w = get_weapon(r.get("weapon_code"))
        if w:
            out.append((w, int(r["qty"])))
    return out


def _user_exists(user_id):
    return _col(USERS_COL).find_one({"_id": int(user_id)}, {"_id": 1}) is not None


def _balance(user_id):
    doc = _col(USERS_COL).find_one({"_id": int(user_id)}, {"coins": 1}) or {}
    return int(doc.get("coins") or 0)


def _charge(user_id, amount):
    """Takes Berries only if the user has enough (one conditional update). True when charged."""
    amount = int(amount)
    if amount <= 0:
        return True
    res = _col(USERS_COL).update_one({"_id": int(user_id), "coins": {"$gte": amount}}, {"$inc": {"coins": -amount}})
    return res.modified_count == 1


def _refund(user_id, amount):
    if int(amount) > 0:
        _col(USERS_COL).update_one({"_id": int(user_id)}, {"$inc": {"coins": int(amount)}})


def _receipt_take(key):
    """One-click guard: False when this confirmation was already processed."""
    if not key:
        return True
    try:
        _col(mongo_db.OP_RECEIPTS).insert_one({"_id": str(key), "result": {"weapon_shop": True}, "created_at": _utcnow()})
        return True
    except mongo_db.DuplicateKeyError:
        return False


def _receipt_free(key):
    if key:
        try:
            _col(mongo_db.OP_RECEIPTS).delete_one({"_id": str(key)})
        except Exception:
            pass


# ---------------------------------------------------------------- shop (sync)
def shop_items_sync():
    return [w for w in all_weapons() if w.get("shop_enabled") and int(w.get("shop_price") or 0) > 0]


def shop_buy_sync(user_id, code, receipt_key=None):
    w = get_weapon(code)
    if not w or not w.get("shop_enabled") or int(w.get("shop_price") or 0) <= 0:
        return {"status": "notforsale"}
    price = int(w["shop_price"])
    if not _user_exists(user_id):
        return {"status": "nouser"}
    if not _receipt_take(receipt_key):
        return {"status": "dup"}
    if not _charge(user_id, price):
        _receipt_free(receipt_key)
        return {"status": "noberries", "need": price, "have": _balance(user_id)}
    try:
        add_user_weapon(user_id, code, 1)
    except Exception:
        _refund(user_id, price)
        _receipt_free(receipt_key)
        raise
    return {"status": "ok", "weapon": w, "price": price, "owned": count_user_weapon(user_id, code),
            "balance": _balance(user_id)}


# ---------------------------------------------------------------- shop (UI)
def _shop_caption(w, idx, total, owned):
    return (
        "⚔️ WEAPON SHOP\n\n"
        f"⚔️ {w['name']} [{w['_id']}]\n"
        f"📺 Anime: {w.get('anime') or '-'}\n"
        f"{_rarity_text(w.get('rarity'))}\n"
        f"🪙 Price: {int(w['shop_price']):,} {BERRY}\n"
        f"🎒 You own: {owned}\n\n"
        f"📦 Weapon {idx + 1}/{total}\n"
        "ℹ️ Weapons are used in /evolve."
    )


def _shop_keyboard(uid, idx, total, w):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    rows = []
    if total > 1:
        rows.append([InlineKeyboardButton("◀️ BACK", callback_data=f"wshop:page:{uid}:{(idx - 1) % total}"),
                     InlineKeyboardButton("▶️ NEXT", callback_data=f"wshop:page:{uid}:{(idx + 1) % total}")])
    rows.append([InlineKeyboardButton(f"🛒 BUY FOR {int(w['shop_price']):,} {BERRY}",
                                      callback_data=f"wshop:buy:{uid}:{w['_id']}")])
    return InlineKeyboardMarkup(rows)


def _shop_page_sync(uid, idx):
    items = shop_items_sync()
    if not items:
        return None
    idx = int(idx) % len(items)
    w = items[idx]
    owned = count_user_weapon(uid, w["_id"])
    return {"w": w, "idx": idx, "total": len(items), "caption": _shop_caption(w, idx, len(items), owned)}


async def _show_shop_page(q, context, uid, idx):
    """Edit the shop message (callback) to page `idx`."""
    page = await asyncio.to_thread(_shop_page_sync, uid, idx)
    message = q.message
    if page is None:
        try:
            await q.edit_message_caption(caption="⚔️ The weapon shop is empty right now.")
        except Exception:
            pass
        return
    kb = _shop_keyboard(uid, page["idx"], page["total"], page["w"])
    photo = page["w"].get("photo")
    from telegram import InputMediaPhoto
    try:
        if photo and message.photo:
            await message.edit_media(media=InputMediaPhoto(media=photo, caption=page["caption"]), reply_markup=kb)
        else:
            await message.edit_text(text=page["caption"], reply_markup=kb)
    except Exception as e:
        if "not modified" in str(e).lower():
            return
        logger.info("weapon shop edit fallback: %s", e)
        try:
            await message.delete()
        except Exception:
            pass
        await _send_shop_message(context.bot, message.chat_id, page, kb)


async def _send_shop_message(bot, chat_id, page, kb):
    photo = page["w"].get("photo")
    if photo:
        await bot.send_photo(chat_id=chat_id, photo=photo, caption=page["caption"], reply_markup=kb)
    else:
        await bot.send_message(chat_id=chat_id, text=page["caption"], reply_markup=kb)


async def weaponshop_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None or user.is_bot:
        return
    page = await asyncio.to_thread(_shop_page_sync, user.id, 0)
    if page is None:
        await _reply(msg, "⚔️ The weapon shop is empty right now. Check back later, weapons also drop in groups!")
        return
    await _send_shop_message(context.bot, msg.chat_id, page, _shop_keyboard(user.id, page["idx"], page["total"], page["w"]))


async def wshop_callback(update, context):
    q = update.callback_query
    if q is None or q.from_user is None or q.message is None:
        return
    parts = (q.data or "").split(":")
    if len(parts) < 4 or parts[0] != "wshop":
        await q.answer()
        return
    action, owner, arg = parts[1], parts[2], parts[3]
    try:
        owner = int(owner)
    except ValueError:
        await q.answer()
        return
    if q.from_user.id != owner:
        await q.answer("❌ This is not your weapon shop. Use /weaponshop.", show_alert=True)
        return

    if action == "open":                                  # button under /shop
        page = await asyncio.to_thread(_shop_page_sync, owner, 0)
        if page is None:
            await q.answer("⚔️ The weapon shop is empty right now.", show_alert=True)
            return
        await q.answer()
        await _send_shop_message(context.bot, q.message.chat_id, page,
                                 _shop_keyboard(owner, page["idx"], page["total"], page["w"]))
        return

    if action == "page":
        await q.answer()
        await _show_shop_page(q, context, owner, arg)
        return

    if action == "show":
        items = await asyncio.to_thread(shop_items_sync)
        idx = next((i for i, w in enumerate(items) if w["_id"] == arg), 0)
        await q.answer()
        await _show_shop_page(q, context, owner, idx)
        return

    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    if action == "buy":                                   # confirmation card
        w = await asyncio.to_thread(get_weapon, arg)
        if not w or not w.get("shop_enabled") or int(w.get("shop_price") or 0) <= 0:
            await q.answer("❌ This weapon is not for sale.", show_alert=True)
            return
        await q.answer()
        text = (f"🛒 Buy {w['name']} [{w['_id']}] for {int(w['shop_price']):,} {BERRY}?\n"
                f"💰 Your Berries: {await asyncio.to_thread(_balance, owner):,}")
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ CONFIRM", callback_data=f"wshop:ok:{owner}:{w['_id']}"),
                                    InlineKeyboardButton("✖️ CANCEL", callback_data=f"wshop:show:{owner}:{w['_id']}")]])
        try:
            if q.message.photo:
                await q.message.edit_caption(caption=text, reply_markup=kb)
            else:
                await q.message.edit_text(text=text, reply_markup=kb)
        except Exception as e:
            logger.info("weapon shop confirm edit skipped: %s", e)
        return

    if action == "ok":                                    # confirmed purchase
        key = f"wshop:{q.message.chat_id}:{q.message.message_id}:{arg}"
        try:
            res = await asyncio.to_thread(shop_buy_sync, owner, arg, key)
        except Exception as e:
            logger.error("weapon shop buy failed: %s", e)
            await q.answer("❌ Purchase failed. Nothing was charged. Please try again.", show_alert=True)
            return
        s = res["status"]
        if s == "noberries":
            await q.answer(f"❌ Not enough Berries: need {res['need']:,}, you have {res['have']:,}.", show_alert=True)
            return
        if s == "nouser":
            await q.answer("❌ Please use /start first.", show_alert=True)
            return
        if s == "notforsale":
            await q.answer("❌ This weapon is not for sale.", show_alert=True)
            return
        if s == "dup":
            await q.answer("⚠️ This purchase was already processed.", show_alert=True)
            return
        w = res["weapon"]
        await q.answer("Purchase complete!")
        text = (f"✅ Purchased {w['name']} [{w['_id']}]\n"
                f"🪙 Paid: {res['price']:,} {BERRY}\n"
                f"🎒 You now own: {res['owned']}\n"
                f"💰 Berries left: {res['balance']:,}\n\n"
                "Use it with /evolve.")
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("◀️ BACK TO SHOP", callback_data=f"wshop:show:{owner}:{w['_id']}")]])
        try:
            if q.message.photo:
                await q.message.edit_caption(caption=text, reply_markup=kb)
            else:
                await q.message.edit_text(text=text, reply_markup=kb)
        except Exception as e:
            logger.info("weapon shop result edit skipped: %s", e)
        return
    await q.answer()


# ---------------------------------------------------------------- /weapons /weaponlist
def _chunk_lines(head, lines, limit=3800):
    pages, cur = [], head
    for ln in lines:
        if len(cur) + len(ln) + 1 > limit and cur != head:
            pages.append(cur.rstrip())
            cur = head
        cur += ln + "\n"
    pages.append(cur.rstrip())
    return pages


async def weapons_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None or user.is_bot:
        return
    rows = await asyncio.to_thread(user_weapons_sync, user.id)
    if not rows:
        await _reply(msg, "⚔️ You don't own any weapons yet.\nBuy them in /weaponshop or catch them when they drop in groups.")
        return
    lines = [f"{_deps['symbols'].get(w.get('rarity'), '⭐')} {w['name']} [{w['_id']}] ×{qty}" for w, qty in rows]
    pages = _chunk_lines("⚔️ Your Weapons\n\n", lines)
    pages[-1] += "\n\nWeapons are used in /evolve."
    for p in pages:
        await _reply(msg, p)


def _weaponlist_lines(staff=False):
    """Everyone sees name, code, anime, rarity and the shop price; Owner/Executive also see the drop settings."""
    lines = []
    for w in all_weapons():
        in_shop = w.get("shop_enabled") and int(w.get("shop_price") or 0) > 0
        shop = f"🛒 {int(w['shop_price']):,} {BERRY}" if in_shop else "🛒 Not in the shop"
        line = (f"{_deps['symbols'].get(w.get('rarity'), '⭐')} {w['name']} [{w['_id']}] • {w.get('anime') or '-'}\n"
                f"   {shop}")
        if staff:
            line += (f" • 🎁 {'on' if w.get('drop_enabled') else 'off'} (stock {_wd_text(w, 'stock') or 0}, "
                     f"{_wd_text(w, 'price', True) or 0})")
        lines.append(line)
    return lines


async def weaponlist_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None or user.is_bot:
        return
    staff = _is_staff(user.id)
    lines = await asyncio.to_thread(_weaponlist_lines, staff)
    if not lines:
        await _reply(msg, "No weapons yet. Add one with /addweapon." if staff else "⚔️ No weapons yet. Check back later!")
        return
    for p in _chunk_lines("⚔️ All Weapons\n\n", lines):
        await _reply(msg, p)


# ---------------------------------------------------------------- /addweapon (PM, Owner + Executive)
# Same flow as /addcharacter and /addevo: numbered steps, photo last, a success card and a staff-log notification.
(W_NAME, W_ANIME, W_RARITY, W_PRICE, W_CODE, W_PHOTO) = range(230, 236)
_WKEYS = ("wpn_name", "wpn_anime", "wpn_rarity", "wpn_price", "wpn_code")


def _clear_w(context):
    for k in _WKEYS:
        context.user_data.pop(k, None)


async def addweapon_start(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return -1
    if update.effective_chat.type != "private":
        await _reply(msg, "⚠️ /addweapon can only be used in the bot's PM (private chat).")
        return -1
    if not _is_staff(user.id):                  # Owner + Executive only
        await _reply(msg, NOT_ALLOWED_TEXT)
        return -1
    _clear_w(context)
    await _reply(msg, f"{_EMOJI[1]} Send weapon name:")
    return W_NAME


async def addweapon_name(update, context):
    msg = update.effective_message
    name = (msg.text or "").strip()
    if not name:
        await _reply(msg, "❌ Weapon name is required. Please send a valid name.")
        return W_NAME
    if len(name) > 60:
        await _reply(msg, "❌ The name is too long (60 characters at most).")
        return W_NAME
    if any(w["name"].casefold() == name.casefold() for w in await asyncio.to_thread(all_weapons)):
        await _reply(msg, "❌ A weapon with that name already exists. Send a different name.")
        return W_NAME
    context.user_data["wpn_name"] = name
    await _reply(msg, f"{_EMOJI[2]} Anime Name:")
    return W_ANIME


async def addweapon_anime(update, context):
    msg = update.effective_message
    anime = (msg.text or "").strip()
    if not anime:
        await _reply(msg, "❌ The anime name cannot be empty.")
        return W_ANIME
    context.user_data["wpn_anime"] = anime
    await _reply(msg, f"{_EMOJI[3]} Rarity:\nCommon / Rare / Epic / Legendary / Mythical / Ethereal / Celestial / Heavenly")
    return W_RARITY


async def addweapon_rarity(update, context):
    msg = update.effective_message
    rarity = (msg.text or "").strip().title()
    if rarity not in _rarities():
        await _reply(msg, "❌ Invalid rarity.")
        return W_RARITY
    context.user_data["wpn_rarity"] = rarity
    await _reply(msg, f"{_EMOJI[4]} Shop Price in Berries (send 0 to keep it out of the shop):")
    return W_PRICE


async def addweapon_price(update, context):
    msg = update.effective_message
    n = _parse_int(msg.text)
    if n is None or n > MAX_PRICE:
        await _reply(msg, "❌ Price must be a whole number (0 or more).")
        return W_PRICE
    context.user_data["wpn_price"] = n
    await _reply(msg, f"{_EMOJI[5]} Weapon Code (unique 4-digit code):")
    return W_CODE


async def addweapon_code(update, context):
    msg = update.effective_message
    code = (msg.text or "").strip()
    if not _valid_code(code):
        await _reply(msg, "❌ Code must be exactly 4 digits (0001-9999).")
        return W_CODE
    if await asyncio.to_thread(get_weapon, code):
        await _reply(msg, "❌ Code already exists.")
        return W_CODE
    context.user_data["wpn_code"] = code
    await _reply(msg, f"{_EMOJI[6]} Weapon Photo - send the photo:")
    return W_PHOTO


async def addweapon_photo(update, context):
    msg, user = update.effective_message, update.effective_user
    if not getattr(msg, "photo", None):
        await _reply(msg, "❌ Please send a photo (the photo is required).")
        return W_PHOTO
    d = dict(context.user_data)
    if not all(k in d for k in _WKEYS):
        _clear_w(context)
        await _reply(msg, "❌ The setup expired. Start again with /addweapon.")
        return -1
    if not _is_staff(user.id):                  # re-check: the role could have been removed mid-flow
        _clear_w(context)
        await _reply(msg, NOT_ALLOWED_TEXT)
        return -1
    price = int(d["wpn_price"])
    doc = {"_id": d["wpn_code"], "code": d["wpn_code"], "name": d["wpn_name"], "anime": d["wpn_anime"],
           "rarity": d["wpn_rarity"], "photo": msg.photo[-1].file_id,
           "shop_enabled": price > 0, "shop_price": price,
           "drop_enabled": False, "drop_stock": 3, "drop_price": price,
           "created_by": int(user.id), "created_at": _stamp()}
    _clear_w(context)
    try:
        await asyncio.to_thread(_col(WEAPONS_COL).insert_one, doc)
    except mongo_db.DuplicateKeyError:
        await _reply(msg, "❌ Code already exists.")
        return -1
    except Exception as e:
        logger.error("addweapon failed: %s", e)
        await _reply(msg, "❌ Could not add the weapon. Please try again.")
        return -1
    await _reply(msg, "✅ Weapon added successfully!\n"
                      f"⚔️ {doc['name']}\n"
                      f"🏷 {_rarity_text(doc['rarity'])}\n"
                      f"💰 {price}\n"
                      f"🔢 {doc['code']}")
    await _notify(context, f"⚔️ NEW WEAPON ADDED\n"
                           f"⚔️ {doc['name']} [{doc['code']}]\n"
                           f"📺 Anime: {doc['anime'] or 'Not set'}\n"
                           f"🏷 {_rarity_text(doc['rarity'])}\n"
                           f"💰 Shop Price: {price}\n"
                           f"📷 Photo: Added\n"
                           f"👤 By: {_by(user)}", user)
    _success(update)
    return -1


async def addweapon_cancel(update, context):
    _clear_w(context)
    if _deps.get("cancel_all"):                 # the bot's universal /cancel: stops EVERYTHING in progress
        await _deps["cancel_all"](update, context)
        return -1
    if update.effective_message is not None:
        await _reply(update.effective_message, "❌ Weapon setup cancelled.")
    return -1


# ---------------------------------------------------------------- /editweapon /delweapon /giveweapon
EDIT_USAGE = ("Usage:\n/editweapon <code> name <new name>\n/editweapon <code> anime <anime>\n"
              "/editweapon <code> rarity <rarity>\n/editweapon <code> price <berries>  (0 = remove from shop)\n"
              "/editweapon <code> photo  (reply to a photo)")


async def editweapon_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return
    if not _is_staff(user.id):
        await _reply(msg, NOT_ALLOWED_TEXT)
        return
    args = list(getattr(context, "args", None) or [])
    code = norm_code(args[0]) if args else None
    if not code or len(args) < 2:
        await _reply(msg, EDIT_USAGE)
        return
    w = await asyncio.to_thread(get_weapon, code)
    if not w:
        await _reply(msg, "❌ That weapon code does not exist.")
        return
    field, value = args[1].lower(), " ".join(args[2:]).strip()
    upd = {}
    if field == "name":
        if not value or len(value) > 60:
            await _reply(msg, "❌ Send a name (1-60 characters).")
            return
        if any(x["name"].casefold() == value.casefold() and x["_id"] != code for x in await asyncio.to_thread(all_weapons)):
            await _reply(msg, "❌ A weapon with that name already exists.")
            return
        upd["name"] = value
    elif field == "anime":
        if not value:
            await _reply(msg, "❌ The anime name cannot be empty.")
            return
        upd["anime"] = value
    elif field == "rarity":
        r = value.title()
        if r not in _rarities():
            await _reply(msg, "❌ Invalid rarity: " + " / ".join(_rarities()))
            return
        upd["rarity"] = r
    elif field == "price":
        n = _parse_int(value)
        if n is None or n > MAX_PRICE:
            await _reply(msg, "❌ Price must be a whole number (0 or more).")
            return
        upd.update({"shop_price": n, "shop_enabled": n > 0})
    elif field == "photo":
        reply = msg.reply_to_message
        if not reply or not getattr(reply, "photo", None):
            await _reply(msg, "❌ Reply to a photo with /editweapon <code> photo.")
            return
        upd["photo"] = reply.photo[-1].file_id
    else:
        await _reply(msg, EDIT_USAGE)
        return
    await asyncio.to_thread(_col(WEAPONS_COL).update_one, {"_id": code}, {"$set": upd})
    w = await asyncio.to_thread(get_weapon, code)
    await _reply(msg, f"✅ Weapon updated: {_weapon_label(w)} ({field})")
    await _notify(context, f"✏️ WEAPON UPDATED\n⚔️ {_weapon_label(w)}\n🔧 Changed: {field}\n👤 By: {_by(user)}", user)
    _success(update)


def _recipes_using_weapon(code):
    try:
        return list(_col(mongo_db.FUSION_EVOLUTION_RECIPES).find({"weapon_code": code}))
    except Exception:
        return []


async def delweapon_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return
    if not _is_owner(user.id):
        await _reply(msg, NOT_ALLOWED_TEXT)
        return
    args = list(getattr(context, "args", None) or [])
    code = norm_code(args[0]) if args else None
    if not code:
        await _reply(msg, "Usage: /delweapon <code> [confirm]")
        return
    w = await asyncio.to_thread(get_weapon, code)
    if not w:
        await _reply(msg, "❌ That weapon code does not exist.")
        return
    used = await asyncio.to_thread(_recipes_using_weapon, code)
    if used:
        await _reply(msg, f"❌ {_weapon_label(w)} is needed by {len(used)} evolution recipe(s). "
                          f"Remove it first with /evoweapon <evolution code> off.")
        return
    owners = await asyncio.to_thread(_col(USER_WEAPONS_COL).count_documents, {"weapon_code": code, "qty": {"$gt": 0}})
    if (len(args) < 2 or args[1].lower() != "confirm"):
        await _reply(msg, f"⚠️ This deletes {_weapon_label(w)} and removes it from {owners} player(s).\n"
                          f"Send /delweapon {code} confirm to continue.")
        return
    await asyncio.to_thread(_col(USER_WEAPONS_COL).delete_many, {"weapon_code": code})
    await asyncio.to_thread(_col(WEAPONS_COL).delete_one, {"_id": code})
    await _reply(msg, f"🗑 Weapon {_weapon_label(w)} deleted.")
    await _notify(context, f"🗑 WEAPON DELETED\n⚔️ {_weapon_label(w)}\n👥 Removed from {owners} player(s)\n👤 By: {_by(user)}", user)
    _success(update)


async def giveweapon_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return
    if not _is_owner(user.id):
        await _reply(msg, NOT_ALLOWED_TEXT)
        return
    args = list(getattr(context, "args", None) or [])
    target_id = None
    if msg.reply_to_message and msg.reply_to_message.from_user:
        target_id = msg.reply_to_message.from_user.id
    elif args and args[0].isdigit():
        target_id = int(args.pop(0))
    code = norm_code(args[0]) if args else None
    qty = _parse_int(args[1]) if len(args) > 1 else 1
    if target_id is None or not code or qty is None or not (1 <= qty <= MAX_QTY):
        await _reply(msg, f"Usage: reply to a user with /giveweapon <code> [qty]\nor /giveweapon <user_id> <code> [qty] (qty 1-{MAX_QTY})")
        return
    w = await asyncio.to_thread(get_weapon, code)
    if not w:
        await _reply(msg, "❌ That weapon code does not exist.")
        return
    if not await asyncio.to_thread(_user_exists, target_id):
        await _reply(msg, "❌ That user has not started the bot yet.")
        return
    await asyncio.to_thread(add_user_weapon, target_id, code, qty)
    await _reply(msg, f"✅ Gave {qty}× {_weapon_label(w)} to user {target_id}.")
    try:
        await context.bot.send_message(chat_id=target_id, text=f"🎁 You received {qty}× {w['name']} [{code}]! Use it in /evolve.")
    except Exception:
        pass
    await _notify(context, f"🎁 WEAPON GIVEN\n⚔️ {qty}× {_weapon_label(w)}\n🎯 To: {target_id}\n👤 By: {_by(user)}", user)
    _success(update)


# ---------------------------------------------------------------- /evoweapon (the evolution weapon slot)
async def evoweapon_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return
    if not _is_staff(user.id):
        await _reply(msg, NOT_ALLOWED_TEXT)
        return
    args = list(getattr(context, "args", None) or [])
    usage = ("Usage:\n/evoweapon <evolution code> <weapon code> [stones]\n   the evolution then needs 1 of that weapon "
             "(stones can be 0 or more; if you leave it out the current stones stay)\n"
             "/evoweapon <evolution code> off [stones]\n   removes the weapon requirement (stones go back to at least 10)")
    if len(args) < 2:
        await _reply(msg, usage)
        return
    evo_code = args[0].strip()
    stones = _parse_int(args[2]) if len(args) > 2 else None
    if len(args) > 2 and stones is None:
        await _reply(msg, "❌ Stones must be a whole number (0 or more).")
        return
    if args[1].lower() == "off":
        weapon = None
    else:
        weapon = norm_code(args[1])
        if not weapon:
            await _reply(msg, usage)
            return
    res = await asyncio.to_thread(set_recipe_weapon_sync, evo_code, weapon, stones)
    if not res["ok"]:
        await _reply(msg, res["error"])
        return
    evo = await asyncio.to_thread(_row, evo_code)
    label = evo[1] if evo else evo_code
    if weapon:
        w = await asyncio.to_thread(get_weapon, weapon)
        await _reply(msg, f"✅ {label} [{evo_code}] now needs 1× {_weapon_label(w)}.\n💎 Stones: {res['stones']}")
        what = f"⚔️ Weapon: {_weapon_label(w)}"
    else:
        await _reply(msg, f"✅ {label} [{evo_code}] no longer needs a weapon.\n💎 Stones: {res['stones']}")
        what = "⚔️ Weapon: removed"
    await _notify(context, f"⚔️ EVOLUTION WEAPON CHANGED\n🎭 {label} [{evo_code}]\n{what}\n💎 Stones: {res['stones']}\n"
                           f"👤 By: {_by(user)}", user)
    _success(update)


# ==========================================================================
# GROUP DROPS: a weapon appears in the groups the Owner enabled; first come, first served, limited stock + time
# ==========================================================================
DEFAULT_SETTINGS = {"enabled": False, "mode": "random", "min_hours": 3, "max_hours": 8, "min_minutes": None, "max_minutes": None, "fixed_times": [],
                    "duration_min": 10, "groups": [], "next_at": None, "last_fixed": None, "active_drop": None}


def _ensure_settings():
    _col(SETTINGS_COL).update_one({"_id": "drops"}, {"$setOnInsert": dict(DEFAULT_SETTINGS)}, upsert=True)


def get_settings():
    _ensure_settings()
    doc = _col(SETTINGS_COL).find_one({"_id": "drops"}) or {}
    return {**DEFAULT_SETTINGS, **doc}


def set_settings(**fields):
    _ensure_settings()
    _col(SETTINGS_COL).update_one({"_id": "drops"}, {"$set": fields})


def _approved_groups():
    try:
        return {int(c) for c in mongo_db.load_approved_groups()}
    except Exception as e:
        logger.warning("approved groups unavailable: %s", e)
        return set()


def _drop_target_groups(settings):
    """Enabled groups that are still approved and have the bot switched on."""
    approved = _approved_groups()
    out = []
    for cid in settings.get("groups") or []:
        try:
            cid = int(cid)
            if cid in approved and mongo_db.is_bot_enabled(cid):
                out.append(cid)
        except Exception:
            continue
    return out


def _pool_sync():
    return [w for w in all_weapons() if w.get("drop_enabled") and int(w.get("drop_stock") or 0) > 0
            and int(w.get("drop_price") or 0) > 0]


def _drops():
    return _col(DROPS_COL)


def _fmt_ist(dt):
    return _aware(dt).astimezone(IST).strftime("%I:%M %p").lstrip("0") + " IST"


def _drop_caption(drop, w, state="active"):
    head = {"active": "⚔️ WEAPON DROP!", "soldout": "⚔️ WEAPON DROP: SOLD OUT", "expired": "⚔️ WEAPON DROP: ENDED"}[state]
    lines = [head, "",
             f"⚔️ {w['name']} [{w['_id']}]",
             f"📺 Anime: {w.get('anime') or '-'}",
             _rarity_text(w.get("rarity")),
             f"🪙 Price: {int(drop['price']):,} {BERRY}",
             f"📦 Stock: {max(int(drop['stock_left']), 0)}/{int(drop['stock_total'])}"]
    if state == "active":
        lines += [f"⏳ Ends at {_fmt_ist(drop['ends_at'])}", "", "One per player. First come, first served!"]
    elif state == "soldout":
        lines += ["", "Every weapon was bought. Watch for the next drop!"]
    else:
        lines += ["", "This drop is over. Watch for the next one!"]
    return "\n".join(lines)


def _drop_keyboard(drop):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    return InlineKeyboardMarkup([[InlineKeyboardButton(f"🛒 BUY FOR {int(drop['price']):,} {BERRY}",
                                                       callback_data=f"wdrop:buy:{drop['_id']}")]])


def _create_drop_sync(w, duration_min):
    """Inserts the drop and claims the single 'active drop' slot. Returns the drop doc or None when one is running."""
    _ensure_settings()
    now = _utcnow()
    s_lo, s_hi = _wd_bounds(w, "stock")                    # a range is rolled once per drop (a single number always gives itself)
    p_lo, p_hi = _wd_bounds(w, "price")
    stock, price = random.randint(s_lo, s_hi), random.randint(p_lo, p_hi)
    drop = {"_id": secrets.token_hex(4), "weapon_code": w["_id"], "price": price,
            "stock_total": stock, "stock_left": stock, "buyers": [],
            "created_at": now, "ends_at": now + timedelta(minutes=int(duration_min)),
            "status": "active", "dirty": False, "messages": []}
    _drops().insert_one(drop)
    claimed = _col(SETTINGS_COL).find_one_and_update({"_id": "drops", "active_drop": None},
                                                     {"$set": {"active_drop": drop["_id"]}})
    if claimed is None:
        _drops().delete_one({"_id": drop["_id"]})
        return None
    return drop


async def start_drop(bot, w, source="auto"):
    """Starts a drop of weapon `w` in every enabled group. Returns (ok, text)."""
    settings = await asyncio.to_thread(get_settings)
    groups = await asyncio.to_thread(_drop_target_groups, settings)
    if not groups:
        return False, "❌ No group is enabled for weapon drops. Use /dropgroups."
    if int(w.get("drop_price") or 0) <= 0 or int(w.get("drop_stock") or 0) <= 0:
        return False, "❌ That weapon needs a drop price and stock first (/dropconfig price|stock)."
    drop = await asyncio.to_thread(_create_drop_sync, w, settings["duration_min"])
    if drop is None:
        return False, "❌ A weapon drop is already running."
    sent = 0
    for cid in groups:
        try:
            caption, kb = _drop_caption(drop, w), _drop_keyboard(drop)
            if w.get("photo"):
                m = await bot.send_photo(chat_id=cid, photo=w["photo"], caption=caption, reply_markup=kb)
            else:
                m = await bot.send_message(chat_id=cid, text=caption, reply_markup=kb)
            await asyncio.to_thread(_drops().update_one, {"_id": drop["_id"]},
                                    {"$push": {"messages": {"chat_id": cid, "message_id": m.message_id}}})
            sent += 1
        except Exception as e:
            logger.info("drop message to %s failed: %s", cid, e)
        await asyncio.sleep(0.05)
    if sent == 0:                                   # nobody could receive it: do not keep a dead drop alive
        await asyncio.to_thread(_finish_drop_sync, drop["_id"], "ended")
        return False, "❌ The drop could not be sent to any group (is the bot still in them?)."
    return True, f"✅ Weapon drop started: {w['name']} in {sent} group(s)."


def _finish_drop_sync(drop_id, status):
    """Marks an active drop finished exactly once. Returns the final drop doc, or None if someone else finished it."""
    doc = _drops().find_one_and_update({"_id": drop_id, "status": "active"}, {"$set": {"status": status}},
                                       return_document=True)
    _col(SETTINGS_COL).update_one({"_id": "drops", "active_drop": drop_id}, {"$set": {"active_drop": None}})
    return doc


async def _edit_drop_messages(bot, drop, w, state):
    text = _drop_caption(drop, w, state)
    kb = _drop_keyboard(drop) if state == "active" else None
    for m in drop.get("messages") or []:
        try:
            if w.get("photo"):
                await bot.edit_message_caption(chat_id=m["chat_id"], message_id=m["message_id"], caption=text, reply_markup=kb)
            else:
                await bot.edit_message_text(chat_id=m["chat_id"], message_id=m["message_id"], text=text, reply_markup=kb)
        except Exception as e:
            if "not modified" not in str(e).lower():
                logger.info("drop message edit skipped: %s", e)
        await asyncio.sleep(0.1)


def _drop_buy_sync(user_id, drop_id):
    """One purchase. The stock slot is claimed with ONE conditional update, so the last weapon can never be sold twice."""
    now = _utcnow()
    drop = _drops().find_one_and_update(
        {"_id": drop_id, "status": "active", "ends_at": {"$gt": now}, "stock_left": {"$gt": 0},
         "buyers": {"$ne": int(user_id)}},
        {"$inc": {"stock_left": -1}, "$push": {"buyers": int(user_id)}, "$set": {"dirty": True}},
        return_document=True)
    if drop is None:
        cur = _drops().find_one({"_id": drop_id})
        if cur is None or cur.get("status") != "active" or _aware(cur["ends_at"]) <= now:
            return {"status": "over"}
        if int(user_id) in (cur.get("buyers") or []):
            return {"status": "already"}
        return {"status": "soldout"}

    def _release():
        _drops().update_one({"_id": drop_id}, {"$inc": {"stock_left": 1}, "$pull": {"buyers": int(user_id)}, "$set": {"dirty": True}})

    w = get_weapon(drop["weapon_code"])
    if w is None:
        _release()
        return {"status": "over"}
    if not _user_exists(user_id):
        _release()
        return {"status": "nouser"}
    price = int(drop["price"])
    if not _charge(user_id, price):
        _release()
        return {"status": "noberries", "need": price, "have": _balance(user_id)}
    try:
        add_user_weapon(user_id, w["_id"], 1)
    except Exception:
        _refund(user_id, price)
        _release()
        raise
    return {"status": "ok", "drop": drop, "weapon": w, "price": price, "owned": count_user_weapon(user_id, w["_id"]),
            "balance": _balance(user_id)}


async def wdrop_callback(update, context):
    q = update.callback_query
    if q is None or q.from_user is None:
        return
    parts = (q.data or "").split(":")
    if len(parts) != 3 or parts[0] != "wdrop" or parts[1] != "buy":
        await q.answer()
        return
    try:
        res = await asyncio.to_thread(_drop_buy_sync, q.from_user.id, parts[2])
    except Exception as e:
        logger.error("weapon drop buy failed: %s", e)
        await q.answer("❌ Purchase failed. Nothing was charged. Please try again.", show_alert=True)
        return
    s = res["status"]
    if s == "over":
        await q.answer("⌛ This drop is over.", show_alert=True)
    elif s == "soldout":
        await q.answer("❌ Sold out!", show_alert=True)
    elif s == "already":
        await q.answer("⚠️ You already bought this weapon from this drop.", show_alert=True)
    elif s == "nouser":
        await q.answer("❌ Please use /start in the bot's PM first.", show_alert=True)
    elif s == "noberries":
        await q.answer(f"❌ Not enough Berries: need {res['need']:,}, you have {res['have']:,}.", show_alert=True)
    elif s == "ok":
        w, drop = res["weapon"], res["drop"]
        await q.answer(f"✅ You bought {w['name']}! It is in /weapons.", show_alert=True)
        try:
            await context.bot.send_message(
                chat_id=q.message.chat_id,
                text=(f"🎉 {q.from_user.mention_html()} bought {w['name']}! "
                      f"({max(int(drop['stock_left']), 0)}/{int(drop['stock_total'])} left)"),
                parse_mode="HTML")
        except Exception:
            pass
        if int(drop["stock_left"]) <= 0:
            final = await asyncio.to_thread(_finish_drop_sync, drop["_id"], "soldout")
            if final:
                final["stock_left"] = 0
                await _edit_drop_messages(context.bot, final, w, "soldout")
        else:
            try:
                await q.edit_message_caption(caption=_drop_caption(drop, w), reply_markup=_drop_keyboard(drop)) \
                    if q.message.photo else await q.edit_message_text(text=_drop_caption(drop, w), reply_markup=_drop_keyboard(drop))
            except Exception as e:
                if "not modified" not in str(e).lower():
                    logger.info("drop caption refresh skipped: %s", e)


# ---------------------------------------------------------------- background tick (JobQueue or asyncio fallback)
def _next_random_at(settings):
    lo, hi = _rand_range(settings)                 # minutes (older settings only hold hours)
    return _utcnow() + timedelta(minutes=random.randint(lo, max(lo, hi)))


def _due_fixed_key(settings):
    """'YYYY-MM-DD HH:MM' of a fixed time that became due in the last 5 minutes and was not used yet, else None."""
    now_ist = datetime.now(IST)
    for hhmm in settings.get("fixed_times") or []:
        try:
            h, m = (int(x) for x in hhmm.split(":"))
        except ValueError:
            continue
        slot = now_ist.replace(hour=h, minute=m, second=0, microsecond=0)
        if timedelta(0) <= now_ist - slot < timedelta(minutes=5):
            key = slot.strftime("%Y-%m-%d %H:%M")
            if key != settings.get("last_fixed"):
                return key
    return None


async def tick(bot):
    """Runs every few seconds: finishes expired drops, refreshes stock text, starts scheduled drops."""
    try:
        settings = await asyncio.to_thread(get_settings)
        active_id = settings.get("active_drop")
        if active_id:
            drop = await asyncio.to_thread(_drops().find_one, {"_id": active_id})
            if drop is None or drop.get("status") != "active":
                await asyncio.to_thread(_col(SETTINGS_COL).update_one, {"_id": "drops", "active_drop": active_id},
                                        {"$set": {"active_drop": None}})
            else:
                w = await asyncio.to_thread(get_weapon, drop["weapon_code"])
                if w is None or _aware(drop["ends_at"]) <= _utcnow() or int(drop["stock_left"]) <= 0:
                    state = "soldout" if int(drop["stock_left"]) <= 0 else "expired"
                    final = await asyncio.to_thread(_finish_drop_sync, active_id, "soldout" if state == "soldout" else "ended")
                    if final and w:
                        await _edit_drop_messages(bot, final, w, state)
                elif drop.get("dirty"):
                    claimed = await asyncio.to_thread(_drops().find_one_and_update, {"_id": active_id, "dirty": True},
                                                      {"$set": {"dirty": False}}, return_document=True)
                    if claimed:
                        await _edit_drop_messages(bot, claimed, w, "active")
            return
        if not settings.get("enabled"):
            return
        pool = await asyncio.to_thread(_pool_sync)
        if not pool:
            return
        if settings.get("mode") == "fixed":
            key = await asyncio.to_thread(_due_fixed_key, settings)
            if not key:
                return
            await asyncio.to_thread(set_settings, last_fixed=key)
        else:
            nxt = _aware(settings.get("next_at"))
            if nxt is None:
                await asyncio.to_thread(set_settings, next_at=_next_random_at(settings))
                return
            if _utcnow() < nxt:
                return
            await asyncio.to_thread(set_settings, next_at=_next_random_at(settings))
        ok, text = await start_drop(bot, random.choice(pool))
        logger.info("scheduled weapon drop: %s", text)
    except Exception as e:
        logger.error("weapon drop tick failed: %s", e)


async def _tick_job(context):
    await tick(context.bot)


async def _fallback_loop(app):
    while True:
        await asyncio.sleep(TICK_SECONDS)
        await tick(app.bot)





# ---------------------------------------------------------------- /dropgroups
GROUPS_PER_PAGE = 8


async def _group_title(bot, cid):
    try:
        chat = await bot.get_chat(cid)
        return (chat.title or str(cid))[:28]
    except Exception:
        return f"Group {cid}"


async def _dropgroups_view(bot, page):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    settings = await asyncio.to_thread(get_settings)
    approved = sorted(await asyncio.to_thread(_approved_groups))
    enabled = {int(c) for c in settings.get("groups") or []}
    pages = max(1, (len(approved) + GROUPS_PER_PAGE - 1) // GROUPS_PER_PAGE)
    page = max(0, min(int(page), pages - 1))
    chunk = approved[page * GROUPS_PER_PAGE:(page + 1) * GROUPS_PER_PAGE]
    rows = []
    for cid in chunk:
        title = await _group_title(bot, cid)
        rows.append([InlineKeyboardButton(("✅ " if cid in enabled else "⬜ ") + title, callback_data=f"wdg:t:{cid}:{page}")])
    if pages > 1:
        rows.append([InlineKeyboardButton("◀️", callback_data=f"wdg:p:0:{(page - 1) % pages}"),
                     InlineKeyboardButton(f"{page + 1}/{pages}", callback_data=f"wdg:p:0:{page}"),
                     InlineKeyboardButton("▶️", callback_data=f"wdg:p:0:{(page + 1) % pages}")])
    rows.append([InlineKeyboardButton("✅ Enable all", callback_data=f"wdg:all:1:{page}"),
                 InlineKeyboardButton("⬜ Disable all", callback_data=f"wdg:all:0:{page}")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="wdp:main:0:0")])
    text = (f"⚔️ Drop Groups\n\nWeapon drops appear only in ✅ groups.\n"
            f"Enabled: {len(enabled & set(approved))} of {len(approved)} approved group(s).")
    return text, InlineKeyboardMarkup(rows)


async def dropgroups_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return
    if not _is_owner(user.id):
        await _reply(msg, NOT_ALLOWED_TEXT)
        return
    text, kb = await _dropgroups_view(context.bot, 0)
    await _reply(msg, text, reply_markup=kb)


async def dropgroups_callback(update, context):
    q = update.callback_query
    if q is None or q.from_user is None:
        return
    if not _is_owner(q.from_user.id):
        await q.answer(NOT_ALLOWED_TEXT, show_alert=True)
        return
    try:
        _w, action, arg, page = q.data.split(":")
        arg, page = int(arg), int(page)
    except ValueError:
        await q.answer()
        return
    if action == "t":
        await asyncio.to_thread(_ensure_settings)
        cur = {int(c) for c in (await asyncio.to_thread(get_settings)).get("groups") or []}
        op = "$pull" if arg in cur else "$addToSet"
        await asyncio.to_thread(_col(SETTINGS_COL).update_one, {"_id": "drops"}, {op: {"groups": arg}})
    elif action == "all":
        groups = sorted(await asyncio.to_thread(_approved_groups)) if arg == 1 else []
        await asyncio.to_thread(set_settings, groups=groups)
    await q.answer()
    text, kb = await _dropgroups_view(context.bot, page)
    try:
        await q.edit_message_text(text=text, reply_markup=kb)
    except Exception as e:
        if "not modified" not in str(e).lower():
            logger.info("dropgroups edit skipped: %s", e)


# ---------------------------------------------------------------- /weapondrops panel (buttons), /dropconfig, /dropnow
POOL_PER_PAGE = 8
MAX_FIXED_TIMES = 6
DUR_MIN, DUR_MAX = 1, 1440                    # drop length, minutes
RAND_MIN, RAND_MAX = 5, 168 * 60              # random gap, minutes
DUR_PRESETS = ((15, "15 min"), (30, "30 min"), (60, "1 hour"), (120, "2 hours"))
RAND_PRESETS = ((60, 180, "1-3 h"), (180, 480, "3-8 h"), (360, 720, "6-12 h"))

# ---- time input: minutes and hours ("70m", "2h", "1h 10", "1h10m", plain number = default unit)
_DUR_RE = re.compile(r"^(\d+)\s*(hours|hour|hrs|hr|h|minutes|minute|mins|min|m)?"
                     r"(?:\s*(\d+)\s*(minutes|minute|mins|min|m)?)?$")


def parse_duration(text, default_unit="m"):
    """Minutes from '70m', '45 min', '2h', '1h 10', '1h10m' or a plain number (default_unit 'm' or 'h'). None if invalid."""
    t = str(text or "").strip().lower().replace(",", "")
    m = _DUR_RE.match(t)
    if not m:
        return None
    a, u1, b, _u2 = m.groups()
    a = int(a)
    if b is not None:                          # "1h 10" / "1h 10m": the first part must be hours
        if not u1 or u1[0] != "h":
            return None
        b = int(b)
        return a * 60 + b if b <= 59 else None
    unit = u1 or default_unit
    return a * 60 if unit[0] == "h" else a


def parse_range(text, default_unit="h"):
    """(min_minutes, max_minutes) from '30m-2h', '1h to 3h', '30m 2h' or '1 3'. None if invalid."""
    t = str(text or "").strip().lower()
    parts = re.split(r"\s*(?:-|–|—|,|\bto\b)\s*", t)
    if len(parts) == 1:
        parts = t.split()
    if len(parts) != 2:
        return None
    lo, hi = parse_duration(parts[0], default_unit), parse_duration(parts[1], default_unit)
    if lo is None or hi is None:
        return None
    return lo, hi


def fmt_minutes(total):
    """70 -> '1h 10m', 120 -> '2h', 45 -> '45m'."""
    h, m = divmod(int(total), 60)
    if h and m:
        return f"{h}h {m}m"
    return f"{h}h" if h else f"{m}m"


def _parse_hhmm(text):
    m = re.fullmatch(r"(\d{1,2}):(\d{2})", str(text or "").strip())
    if not m or int(m.group(1)) > 23 or int(m.group(2)) > 59:
        return None
    return f"{int(m.group(1)):02d}:{m.group(2)}"


def _rand_range(s):
    """(min, max) random gap in minutes; older settings only have min_hours/max_hours."""
    lo, hi = s.get("min_minutes"), s.get("max_minutes")
    if lo is None or hi is None:
        lo, hi = int(s["min_hours"]) * 60, int(s["max_hours"]) * 60
    return int(lo), int(hi)


def _timing_text(s):
    if s["mode"] == "fixed":
        times = ", ".join(s.get("fixed_times") or []) or "no times set"
        return f"Fixed times (IST): {times}"
    lo, hi = _rand_range(s)
    return f"Random: every {fmt_minutes(lo)}-{fmt_minutes(hi)}"


# ---- guides (📜 Commands, 🔘 Buttons)
_CMD_GUIDE = (
    "📜 WEAPON COMMANDS (1/3): EVERYONE\n\n"
    "/weapons\nShows the weapons you own and how many of each. A weapon is used up in /evolve when an evolution needs it.\n\n"
    "/weaponshop\nOpens the weapon shop. Use ◀️ BACK and ▶️ NEXT to look through the weapons and 🛒 BUY to buy one. "
    "The price is taken from your Berries.\n\n"
    "/weaponlist\nLists every weapon with its code, anime, rarity and shop price. Owner and Executive also see "
    "if the weapon is in the drop pool, its drop stock and its drop price.",

    "📜 WEAPON COMMANDS (2/3): OWNER + EXECUTIVE\n\n"
    "/addweapon\nPM only. Guided steps: name, anime, rarity, shop price, 4-digit code, photo. Send /cancel to stop.\n\n"
    "/editweapon <code> <field> <value>\nChanges one thing of a weapon:\n"
    "• name <new name>\n• anime <anime>\n• rarity <rarity>\n"
    "• price <berries> (shop price, 0 removes it from the shop)\n• photo (reply to a photo with /editweapon <code> photo)\n\n"
    "/evoweapon <evolution code> <weapon code> [stones]\nMakes an evolution need 1 of that weapon. "
    "Stones is optional (0 or more); leave it out to keep the current stones.\n\n"
    "/evoweapon <evolution code> off [stones]\nRemoves the weapon requirement. The stones go back to at least 10.",

    "📜 WEAPON COMMANDS (3/3): OWNER ONLY\n\n"
    "/weapondrops\nThis panel: ON/OFF, drop now, timing, duration, groups, weapons and the guides.\n\n"
    "/dropnow [weapon]\nStarts a drop right now in every enabled group. Send a weapon code or name, or nothing for a random "
    "weapon from the pool. Only one drop can run at a time.\n\n"
    "/dropgroups\nChoose which groups get weapon drops.\n\n"
    "/dropconfig\nShortcuts for the panel:\n"
    "• random <min> <max> (e.g. 30m-2h; plain numbers are hours)\n"
    "• fixed 18:00 22:00 (IST, up to 6 times)\n"
    "• duration <time> (e.g. 45m, 2h, 1h 10; a plain number is minutes)\n"
    "• stock <code> <number or range> (1-1000, like 3-10; 0 = none)\n"
    "• price <code> <berries or range> (like 5000-20000; 0 = none)\n\n"
    "/giveweapon <user_id> <code> [qty]\nGives a weapon (qty 1-99), or reply to a user with /giveweapon <code> [qty]. "
    "The user must have started the bot.\n\n"
    "/delweapon <code> [confirm]\nDeletes a weapon and removes it from every player. The first send shows a warning; "
    "send it again with confirm. Blocked while an evolution still needs the weapon.\n\n"
    "/cancel\nStops any typing step (✏️ buttons, /addweapon).",
)

_BTN_GUIDE = (
    "🔘 BUTTONS (1/3): MAIN PANEL\n\n"
    "🟢 Turn ON / 🔴 Turn OFF\nStarts or stops the automatic drops. 🎁 Drop now and /dropnow still work while OFF.\n\n"
    "🎁 Drop now\nStarts a drop right away with a random weapon from the pool, in every enabled group.\n\n"
    "⏱ Timing\nWhen drops start: random gaps or fixed IST times.\n\n"
    "⌛ Duration\nHow long each drop stays open.\n\n"
    "👥 Groups\nWhich groups get drops.\n\n"
    "⚔️ Weapons\nStock, drop price and pool of each weapon.\n\n"
    "📜 Commands / 🔘 Buttons\nThese two guides.\n\n"
    "⬅️ Back\nGoes back to the screen before.\n◀️ ▶️\nTurn pages.\n✅\nMarks the current choice.",

    "🔘 BUTTONS (2/3): TIMING AND DURATION\n\n"
    "🎲 Random\nA drop starts after a random wait between a minimum and a maximum.\n"
    "1-3 h, 3-8 h, 6-12 h: quick ranges.\n"
    "✏️ Custom: type your own, like 30m-2h or 1h-3h (5 minutes to 168 hours).\n\n"
    "🕒 Fixed times\nDrops start at the same IST times every day, up to 6.\n"
    "18:00 ❌: removes that time.\n"
    "➕ Add time: type a time like 18:30 (IST, 24-hour).\n\n"
    "15 min, 30 min, 1 hour, 2 hours\nQuick drop lengths.\n"
    "✏️ Custom: type 70m, 2h or 1h 10 (1 minute to 24 hours).\n\n"
    "Time format: 70m = 70 minutes, 2h = 2 hours, 1h 10 = 1 hour 10 minutes.",

    "🔘 BUTTONS (3/3): WEAPONS, GROUPS, DROP MESSAGE\n\n"
    "⚔️ Weapons list\nTap a weapon to open it. ✅ = in the drop pool, ⬜ = not in the pool. Each line shows stock and drop price.\n\n"
    "Weapon page\n"
    "➖ ➕: change the stock by 1 (both ends of a range, 1-1000).\n"
    "✏️ Stock: type the stock: a range like 3-10 (a random amount each drop), one number, or 0 for none.\n"
    "✏️ Price: type the drop price in Berries the same way, like 5000-20000.\n"
    "✅ In pool / ⬜ Not in pool: a weapon drops only when it is in the pool, has stock and has a drop price.\n\n"
    "👥 Groups\nTap a group to turn it ✅ or ⬜. ✅ Enable all and ⬜ Disable all change every group. "
    "Drops appear only in enabled, approved groups where the bot is ON.\n\n"
    "In the group\n🛒 BUY FOR <price>: first come, first served, one per player, until the stock is gone or the time is over.\n\n"
    "Typing steps\nAfter a ✏️ button the bot waits for your next message. Send /cancel to stop.",
)


def _kb(rows):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    return InlineKeyboardMarkup([[InlineKeyboardButton(t, callback_data=d) for t, d in row] for row in rows])


BACK_ROW = [("⬅️ Back", "wdp:main:0:0")]


def _view_main():
    s = get_settings()
    nxt = ""
    if s["enabled"] and s["mode"] == "random" and s.get("next_at"):
        nxt = f"\n⏭ Next drop: about {_fmt_ist(s['next_at'])}"
    active = "\n🔥 A drop is running now." if s.get("active_drop") else ""
    text = "\n".join(["⚔️ WEAPON DROPS", "",
                      f"Status: {'🟢 ON' if s['enabled'] else '🔴 OFF'}",
                      f"⏱ {_timing_text(s)}",
                      f"⌛ Each drop lasts {fmt_minutes(s['duration_min'])}",
                      f"👥 Groups enabled: {len(s.get('groups') or [])}"]) + nxt + active
    rows = [[("🔴 Turn OFF" if s["enabled"] else "🟢 Turn ON", "wdp:master:0:0"), ("🎁 Drop now", "wdp:now:0:0")],
            [("⏱ Timing", "wdp:tim:0:0"), ("⌛ Duration", "wdp:dur:0:0")],
            [("👥 Groups", "wdp:grp:0:0"), ("⚔️ Weapons", "wdp:wlist:0:0")],
            [("📜 Commands", "wdp:cmds:0:0"), ("🔘 Buttons", "wdp:btns:0:0")]]
    return text, _kb(rows)


def _view_timing():
    s = get_settings()
    fixed = s["mode"] == "fixed"
    hint = ("Drops start at these IST times every day (up to 6)." if fixed
            else "A drop starts after a random wait between the minimum and the maximum.")
    text = f"⏱ DROP TIMING\n\n{_timing_text(s)}\n{hint}"
    rows = [[("🎲 Random" + ("" if fixed else " ✅"), "wdp:tmode:r:0"),
             ("🕒 Fixed times" + (" ✅" if fixed else ""), "wdp:tmode:f:0")]]
    if fixed:
        times = sorted(set(s.get("fixed_times") or []))
        for i in range(0, len(times), 3):
            rows.append([(f"{t} ❌", f"wdp:tdel:{t.replace(':', '')}:0") for t in times[i:i + 3]])
        if len(times) < MAX_FIXED_TIMES:
            rows.append([("➕ Add time", "wdi:time:0:0")])
    else:
        cur = _rand_range(s)
        rows.append([(("✅ " if cur == (lo, hi) else "") + label, f"wdp:trand:{lo}-{hi}:0") for lo, hi, label in RAND_PRESETS])
        rows.append([("✏️ Custom", "wdi:rand:0:0")])
    rows.append(BACK_ROW)
    return text, _kb(rows)


def _view_duration():
    s = get_settings()
    cur = int(s["duration_min"])
    text = f"⌛ DROP DURATION\n\nNow: {fmt_minutes(cur)}\nHow long each drop stays open."
    rows = [[(("✅ " if cur == m else "") + label, f"wdp:dset:{m}:0") for m, label in DUR_PRESETS],
            [("✏️ Custom", "wdi:dur:0:0")], BACK_ROW]
    return text, _kb(rows)


def _view_wlist(page):
    weapons = all_weapons()
    pages = max(1, (len(weapons) + POOL_PER_PAGE - 1) // POOL_PER_PAGE)
    page = max(0, min(int(page), pages - 1))
    lines = ["⚔️ DROP WEAPONS", "", "Tap a weapon to set its stock, drop price and pool.", "✅ in the pool   ⬜ not in the pool"]
    rows = []
    if not weapons:
        lines += ["", "No weapons yet. Add one with /addweapon."]
    for w in weapons[page * POOL_PER_PAGE:(page + 1) * POOL_PER_PAGE]:
        info = f"{_wd_text(w, 'stock') or 0} • " + (_wd_text(w, 'price', True) or "no price")
        rows.append([(f"{'✅' if w.get('drop_enabled') else '⬜'} {w['name'][:18]} • {info}", f"wdp:wpage:{w['_id']}:{page}")])
    if pages > 1:
        rows.append([("◀️", f"wdp:wlist:0:{(page - 1) % pages}"), (f"{page + 1}/{pages}", f"wdp:wlist:0:{page}"),
                     ("▶️", f"wdp:wlist:0:{(page + 1) % pages}")])
    rows.append(BACK_ROW)
    return "\n".join(lines), _kb(rows)


def _view_wpage(code, page):
    w = get_weapon(code)
    if not w:
        return _view_wlist(page)
    stock, price, on = int(w.get("drop_stock") or 0), int(w.get("drop_price") or 0), bool(w.get("drop_enabled"))
    lines = [f"⚔️ {_weapon_label(w)}", "",
             "📦 Stock: " + (_wd_text(w, "stock") or "not set") + (" (random each drop)" if _wd_bounds(w, "stock")[0] != stock else ""),
             "🪙 Drop price: " + (f"{_wd_text(w, 'price', True)} {BERRY}" if price else "not set")
             + (" (random each drop)" if _wd_bounds(w, "price")[0] != price else ""),
             f"🎁 Pool: {'✅ In pool' if on else '⬜ Not in pool'}"]
    if on and (stock <= 0 or price <= 0):
        lines += ["", "⚠️ It will not drop until it has stock and a drop price."]
    rows = [[("➖", f"wdp:wminus:{code}:{page}"), ("➕", f"wdp:wplus:{code}:{page}")],
            [("✏️ Stock", f"wdi:stock:{code}:{page}"), ("✏️ Price", f"wdi:price:{code}:{page}")],
            [("✅ In pool" if on else "⬜ Not in pool", f"wdp:wpool:{code}:{page}")],
            [("⬅️ Weapons", f"wdp:wlist:0:{page}")]]
    return "\n".join(lines), _kb(rows)


def _view_guide(action, page, from_help=False, uid=0):
    """Guide pages. Opened from /weapondrops (arg 0) ⬅️ Back returns to the drop panel; opened from /help (arg h) it returns to the Weapons help page."""
    pages = _CMD_GUIDE if action == "cmds" else _BTN_GUIDE
    page = max(0, min(int(page), len(pages) - 1))
    flag = "h" if from_help and uid else "0"
    back = [("⬅️ Back", f"help:{uid}:owner:weapons")] if flag == "h" else BACK_ROW
    rows = [[("◀️", f"wdp:{action}:{flag}:{(page - 1) % len(pages)}"), (f"{page + 1}/{len(pages)}", f"wdp:{action}:{flag}:{page}"),
             ("▶️", f"wdp:{action}:{flag}:{(page + 1) % len(pages)}")], back]
    return pages[page], _kb(rows)


def _view_sync(view, arg="0", page=0, uid=0):
    """(text, markup) of one /weapondrops screen."""
    if view == "tim":
        return _view_timing()
    if view == "dur":
        return _view_duration()
    if view == "wlist":
        return _view_wlist(page)
    if view == "wpage":
        return _view_wpage(arg, page)
    if view in ("cmds", "btns"):
        return _view_guide(view, page, arg == "h", uid)
    return _view_main()


def _adjust_stock_sync(code, delta):
    """+1 / -1 drop stock (both ends of a range), kept within 1-MAX_STOCK. Returns the new maximum, or None when nothing changed."""
    w = get_weapon(code)
    if not w:
        return None
    lo, hi = _wd_bounds(w, "stock")                       # a range moves as a whole (both ends)
    if delta > 0:
        if hi >= MAX_STOCK:
            return None
        lo, hi = (1, 1) if hi == 0 else (lo + 1, hi + 1)
    else:
        if lo <= 1:
            return None
        lo, hi = lo - 1, hi - 1
    _col(WEAPONS_COL).update_one({"_id": code}, {"$set": _wd_fields("stock", (lo, hi))})
    return hi


def _add_fixed_time_sync(hhmm):
    times = sorted(set(get_settings().get("fixed_times") or []))
    if hhmm in times:
        return "dup"
    if len(times) >= MAX_FIXED_TIMES:
        return "full"
    set_settings(fixed_times=sorted(times + [hhmm]), last_fixed=None)
    return "ok"


async def _show(q, text, kb):
    try:
        await q.edit_message_text(text=text, reply_markup=kb)
    except Exception as e:
        if "not modified" not in str(e).lower():
            logger.info("weapondrops edit skipped: %s", e)


async def weapondrops_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return
    if not _is_owner(user.id):
        await _reply(msg, NOT_ALLOWED_TEXT)
        return
    text, kb = await asyncio.to_thread(_view_sync, "main")
    await _reply(msg, text, reply_markup=kb)


async def wdp_callback(update, context):
    """Every button of the /weapondrops panel: wdp:<action>:<arg>:<page>."""
    q = update.callback_query
    if q is None or q.from_user is None:
        return
    if not _is_owner(q.from_user.id):
        await q.answer(NOT_ALLOWED_TEXT, show_alert=True)
        return
    parts = (q.data or "").split(":")
    if len(parts) != 4:
        await q.answer()
        return
    _w, action, arg, page = parts
    try:
        page = int(page)
    except ValueError:
        page = 0
    context.user_data.pop("wdi", None)             # pressing any panel button drops a pending ✏️ input
    note, view = None, action
    if action == "main":
        view = "main"
    elif action == "master":
        s = await asyncio.to_thread(get_settings)
        await asyncio.to_thread(set_settings, enabled=not s["enabled"], next_at=None)
        view = "main"
    elif action == "now":
        pool = await asyncio.to_thread(_pool_sync)
        if not pool:
            await q.answer("❌ No weapon in the pool has stock and a drop price.", show_alert=True)
            return
        _ok, text = await start_drop(context.bot, random.choice(pool), "owner")
        await q.answer(text[:190], show_alert=True)
        return
    elif action == "grp":
        await q.answer()
        text, kb = await _dropgroups_view(context.bot, 0)
        await _show(q, text, kb)
        return
    elif action == "tmode":
        if arg == "f":
            s = await asyncio.to_thread(get_settings)
            await asyncio.to_thread(set_settings, mode="fixed", last_fixed=None)
            if not s.get("fixed_times"):
                note = "Fixed mode is on. Tap ➕ Add time to add a time."
        else:
            await asyncio.to_thread(set_settings, mode="random", next_at=None)
        view = "tim"
    elif action == "trand":
        try:
            lo, hi = (int(x) for x in arg.split("-"))
        except ValueError:
            await q.answer()
            return
        await asyncio.to_thread(set_settings, mode="random", min_minutes=lo, max_minutes=hi, next_at=None)
        view = "tim"
    elif action == "tdel":
        hhmm = _parse_hhmm(f"{arg[:2]}:{arg[2:]}")
        if hhmm:
            await asyncio.to_thread(_col(SETTINGS_COL).update_one, {"_id": "drops"}, {"$pull": {"fixed_times": hhmm}})
        view = "tim"
    elif action == "dset":
        minutes = _parse_int(arg)
        if minutes is not None and DUR_MIN <= minutes <= DUR_MAX:
            await asyncio.to_thread(set_settings, duration_min=minutes)
        view = "dur"
    elif action in ("wplus", "wminus"):
        new = await asyncio.to_thread(_adjust_stock_sync, arg, 1 if action == "wplus" else -1)
        if new is None:
            note = f"Stock must stay between 1 and {MAX_STOCK}."
        view = "wpage"
    elif action == "wpool":
        w = await asyncio.to_thread(get_weapon, arg)
        if w:
            await asyncio.to_thread(_col(WEAPONS_COL).update_one, {"_id": arg}, {"$set": {"drop_enabled": not w.get("drop_enabled")}})
            if not w.get("drop_enabled") and (int(w.get("drop_price") or 0) <= 0 or int(w.get("drop_stock") or 0) <= 0):
                note = "⚠️ It needs stock and a drop price before it can drop."
        view = "wpage"
    elif action not in ("tim", "dur", "wlist", "wpage", "cmds", "btns"):
        await q.answer()
        return
    await q.answer(note[:190] if note else None, show_alert=bool(note and note.startswith("⚠️")))
    text, kb = await asyncio.to_thread(_view_sync, view, arg, page, q.from_user.id)
    await _show(q, text, kb)


# ---- typed input after a ✏️ button: wdi:<kind>:<arg>:<page>
(WD_INPUT,) = range(240, 241)
_WDI_PROMPTS = {
    "dur": "⌛ Send the duration, for example 45m, 2h or 1h 10 (1m-24h). A plain number is minutes.",
    "rand": "🎲 Send the minimum and maximum wait, for example 30m-2h or 1h-3h (5m-168h). Plain numbers are hours.",
    "time": "🕒 Send the time in IST, 24-hour, for example 18:30:",
}


async def wdi_start(update, context):
    q = update.callback_query
    if q is None or q.from_user is None or q.message is None:
        return -1
    if not _is_owner(q.from_user.id):
        await q.answer(NOT_ALLOWED_TEXT, show_alert=True)
        return -1
    parts = (q.data or "").split(":")
    if len(parts) != 4:
        await q.answer()
        return -1
    _w, kind, arg, page = parts
    try:
        page = int(page)
    except ValueError:
        page = 0
    if kind in ("stock", "price"):
        w = await asyncio.to_thread(get_weapon, arg)
        if not w:
            await q.answer("❌ That weapon no longer exists.", show_alert=True)
            return -1
        prompt = (f"📦 Stock for {w['name']}. Send a range from 1 to {MAX_STOCK}, like 3-10 (a random amount each drop), "
                  "one number like 5, or 0 for none." if kind == "stock"
                  else f"🪙 Drop price in Berries for {w['name']}. Send a range from 1 to {MAX_PRICE:,}, like 5000-20000 "
                       "(a random price each drop), one number like 5000, or 0 for none.")
    elif kind in _WDI_PROMPTS:
        prompt = _WDI_PROMPTS[kind]
    else:
        await q.answer()
        return -1
    context.user_data["wdi"] = {"kind": kind, "arg": arg, "page": page,
                                "chat_id": q.message.chat_id, "message_id": q.message.message_id}
    await q.answer()
    await _reply(q.message, prompt + "\nSend /cancel to stop.")
    return WD_INPUT


async def _wdi_refresh(bot, pend):
    """Redraw the panel message the ✏️ button was pressed on."""
    kind = pend["kind"]
    view = {"dur": "dur", "rand": "tim", "time": "tim"}.get(kind, "wpage")
    try:
        text, kb = await asyncio.to_thread(_view_sync, view, pend["arg"], pend["page"])
        await bot.edit_message_text(chat_id=pend["chat_id"], message_id=pend["message_id"], text=text, reply_markup=kb)
    except Exception as e:
        if "not modified" not in str(e).lower():
            logger.info("weapondrops refresh skipped: %s", e)


async def wdi_text(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return -1
    if not _is_owner(user.id):
        return -1
    pend = context.user_data.get("wdi")
    if not pend:
        await _reply(msg, "⌛ That input expired. Open /weapondrops again.")
        return -1
    kind, text = pend["kind"], (msg.text or "").strip()
    if kind == "dur":
        minutes = parse_duration(text, "m")
        if minutes is None or not (DUR_MIN <= minutes <= DUR_MAX):
            await _reply(msg, "❌ Send a duration from 1m to 24h, like 45m, 2h or 1h 10.")
            return WD_INPUT
        await asyncio.to_thread(set_settings, duration_min=minutes)
        done = f"✅ Each drop now lasts {fmt_minutes(minutes)}."
    elif kind == "rand":
        rng = parse_range(text, "h")
        if rng is None or not (RAND_MIN <= rng[0] <= rng[1] <= RAND_MAX):
            await _reply(msg, "❌ Send the minimum and maximum like 30m-2h or 1h-3h (5m to 168h, minimum not above maximum).")
            return WD_INPUT
        await asyncio.to_thread(set_settings, mode="random", min_minutes=rng[0], max_minutes=rng[1], next_at=None)
        done = f"✅ Random drops: every {fmt_minutes(rng[0])}-{fmt_minutes(rng[1])}."
    elif kind == "time":
        hhmm = _parse_hhmm(text)
        if hhmm is None:
            await _reply(msg, "❌ Send the time like 18:30 (IST, 24-hour).")
            return WD_INPUT
        res = await asyncio.to_thread(_add_fixed_time_sync, hhmm)
        if res == "dup":
            await _reply(msg, f"❌ {hhmm} is already in the list. Send another time or /cancel.")
            return WD_INPUT
        if res == "full":
            await _reply(msg, f"❌ You can set up to {MAX_FIXED_TIMES} times. Remove one first.")
            context.user_data.pop("wdi", None)
            return -1
        done = f"✅ Added {hhmm} IST."
    else:                                          # stock / price of one weapon
        code = pend["arg"]
        limit = MAX_STOCK if kind == "stock" else MAX_PRICE
        w = await asyncio.to_thread(get_weapon, code)
        if w is None:
            await _reply(msg, "❌ That weapon no longer exists.")
            context.user_data.pop("wdi", None)
            return -1
        rng = _wd_parse(text, limit)
        if rng is None:
            await _reply(msg, (f"❌ Stock goes from 1 to {limit:,}. Send a range like 3-10, one number like 5, or 0 for none."
                               if kind == "stock" else
                               f"❌ Drop price goes from 1 to {limit:,}. Send a range like 5000-20000, one number like 5000, or 0 for none.")
                         + "\nTry again, or send /cancel.")
            return WD_INPUT
        await asyncio.to_thread(_col(WEAPONS_COL).update_one, {"_id": code}, {"$set": _wd_fields(kind, rng)})
        w.update(_wd_fields(kind, rng))
        done = f"✅ {w['name']}: drop {kind} = {_wd_text(w, kind, kind == 'price') or 'not set'}"
    context.user_data.pop("wdi", None)
    await _reply(msg, done)
    await _wdi_refresh(context.bot, pend)
    _success(update)
    return -1


async def wdi_cancel(update, context):
    context.user_data.pop("wdi", None)
    if _deps.get("cancel_all"):                  # the bot's universal /cancel: stops EVERYTHING in progress
        await _deps["cancel_all"](update, context)
        return -1
    if update.effective_message is not None:
        await _reply(update.effective_message, "❌ Cancelled.")
    return -1


CONFIG_USAGE = ("Usage:\n/dropconfig random <min> <max>  (e.g. 30m-2h or 1h-3h; plain numbers are hours)\n"
                "/dropconfig fixed 18:00 22:00 (IST, up to 6 times)\n"
                "/dropconfig duration <time>  (e.g. 45m, 2h, 1h 10; a plain number is minutes)\n"
                "/dropconfig stock <weapon code> <number or range like 3-10, 0 = none>\n"
                "/dropconfig price <weapon code> <berries or range like 5000-20000, 0 = none>\n\nTip: /weapondrops has buttons for all of this.")


async def dropconfig_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return
    if not _is_owner(user.id):
        await _reply(msg, NOT_ALLOWED_TEXT)
        return
    args = [a.strip() for a in (getattr(context, "args", None) or [])]
    if not args:
        await _reply(msg, CONFIG_USAGE)
        return
    cmd = args[0].lower()
    if cmd == "random" and len(args) >= 2:
        rng = parse_range(" ".join(args[1:]), "h")
        if rng is None or not (RAND_MIN <= rng[0] <= rng[1] <= RAND_MAX):
            await _reply(msg, "❌ Send the minimum and maximum like 30m-2h or 1h-3h (5m to 168h, minimum not above maximum).")
            return
        await asyncio.to_thread(set_settings, mode="random", min_minutes=rng[0], max_minutes=rng[1], next_at=None)
        await _reply(msg, f"✅ Random drops: every {fmt_minutes(rng[0])}-{fmt_minutes(rng[1])}.")
    elif cmd == "fixed" and 2 <= len(args) <= MAX_FIXED_TIMES + 1:
        times = []
        for t in args[1:]:
            hhmm = _parse_hhmm(t)
            if hhmm is None:
                await _reply(msg, f"❌ '{t}' is not a valid time. Use HH:MM (24-hour, IST).")
                return
            times.append(hhmm)
        await asyncio.to_thread(set_settings, mode="fixed", fixed_times=sorted(set(times)), last_fixed=None)
        await _reply(msg, "✅ Fixed drops at " + ", ".join(sorted(set(times))) + " IST.")
    elif cmd == "duration" and len(args) >= 2:
        minutes = parse_duration(" ".join(args[1:]), "m")
        if minutes is None or not (DUR_MIN <= minutes <= DUR_MAX):
            await _reply(msg, "❌ Send a duration from 1m to 24h, like 45m, 2h or 1h 10.")
            return
        await asyncio.to_thread(set_settings, duration_min=minutes)
        await _reply(msg, f"✅ Each drop lasts {fmt_minutes(minutes)}.")
    elif cmd in ("stock", "price") and len(args) >= 3:
        code = norm_code(args[1])
        w = await asyncio.to_thread(get_weapon, code) if code else None
        limit = MAX_STOCK if cmd == "stock" else MAX_PRICE
        if not w:
            await _reply(msg, "❌ Check the weapon code.")
            return
        rng = _wd_parse("".join(args[2:]), limit)
        if rng is None:
            await _reply(msg, (f"❌ Stock goes from 1 to {limit:,}. Send a range like 3-10, one number like 5, or 0 for none."
                               if cmd == "stock" else
                               f"❌ Drop price goes from 1 to {limit:,}. Send a range like 5000-20000, one number like 5000, or 0 for none."))
            return
        await asyncio.to_thread(_col(WEAPONS_COL).update_one, {"_id": code}, {"$set": _wd_fields(cmd, rng)})
        w.update(_wd_fields(cmd, rng))
        await _reply(msg, f"✅ {_weapon_label(w)}: drop {cmd} = {_wd_text(w, cmd, cmd == 'price') or 'not set'}")
    else:
        await _reply(msg, CONFIG_USAGE)
        return
    _success(update)


async def dropnow_command(update, context):
    user, msg = update.effective_user, update.effective_message
    if user is None or msg is None:
        return
    if not _is_owner(user.id):
        await _reply(msg, NOT_ALLOWED_TEXT)
        return
    args = list(getattr(context, "args", None) or [])
    if args:
        w, err = await asyncio.to_thread(find_weapon, " ".join(args))
        if err:
            await _reply(msg, err)
            return
    else:
        pool = await asyncio.to_thread(_pool_sync)
        if not pool:
            await _reply(msg, "❌ No weapon in the drop pool has stock and a drop price. Use /weapondrops.")
            return
        w = random.choice(pool)
    ok, text = await start_drop(context.bot, w, "owner")
    await _reply(msg, text)
    if ok:
        _success(update)


# ---------------------------------------------------------------- registration
def weapon_help_module():
    """(key, button label, page text) for the Owner /help menu, next to Invites and Security (see bot.py HELP_MODULES)."""
    entries = [
        ("/addweapon", "Add a weapon (guided, PM only)"),
        ("/editweapon <code> <name|anime|rarity|price|photo>", "Edit a weapon"),
        ("/weaponlist", "List all weapons"),
        ("/evoweapon <evolution code> <weapon code|off> [stones]", "Set the weapon an evolution needs"),
        ("/giveweapon <user_id> <code> [qty]", "Give a weapon (or reply to a user)"),
        ("/delweapon <code> [confirm]", "Delete a weapon"),
        ("/weapondrops", "Drop panel: ON/OFF, drop now, timing, duration, groups, weapons, command and button guides"),
        ("/dropgroups", "Choose the groups that get drops"),
        ("/dropconfig <random|fixed|duration|stock|price> ...", "Shortcuts for the panel (times like 30m, 2h, 1h 10)"),
        ("/dropnow [weapon]", "Start a drop now"),
    ]
    lines = ["⚔️ Weapons (Owner only)", "", "📌 Overview",
             "Weapons are used in /evolve. Players buy them in /weaponshop or catch them in group drops.",
             "", "⌨️ Commands & usage"]
    lines += [f"{i}. {syntax} - {desc}" for i, (syntax, desc) in enumerate(entries, 1)]
    lines += ["", "Players use /weapons (their weapons) and /weaponshop.",
              "Open /weapondrops and tap 📜 Commands or 🔘 Buttons for the full guide."]
    return ("weapons", "⚔️ Weapons", "\n".join(lines))


def ensure_weapon_collections():
    """Idempotent, best effort: create the weapon collections (visible in Atlas right after start-up) and their indexes."""
    try:
        db = mongo_db.get_db()
        existing = set(db.list_collection_names())
        for name in (WEAPONS_COL, USER_WEAPONS_COL, SETTINGS_COL, DROPS_COL):
            if name not in existing:
                try:
                    db.create_collection(name)
                except Exception:                  # created by a concurrent start-up: fine
                    pass
        _col(USER_WEAPONS_COL).create_index([("user_id", 1)], name="user_id")
        _col(USER_WEAPONS_COL).create_index([("weapon_code", 1)], name="weapon_code")
        _col(DROPS_COL).create_index([("status", 1)], name="status")
    except Exception as e:
        logger.warning("weapon collections could not be prepared: %s", e)


def _register_weapons(app):
    """Attach every weapon handler (called by register(app) below the stone and evolution handlers)."""
    ensure_weapon_collections()
    from telegram.ext import (CallbackQueryHandler, CommandHandler, ConversationHandler, MessageHandler, filters)
    text = filters.TEXT & ~filters.COMMAND
    app.add_handler(ConversationHandler(
        entry_points=[CommandHandler("addweapon", addweapon_start)],
        states={
            W_NAME: [MessageHandler(text, addweapon_name)],
            W_ANIME: [MessageHandler(text, addweapon_anime)],
            W_RARITY: [MessageHandler(text, addweapon_rarity)],
            W_PRICE: [MessageHandler(text, addweapon_price)],
            W_CODE: [MessageHandler(text, addweapon_code)],
            W_PHOTO: [MessageHandler(filters.PHOTO, addweapon_photo), MessageHandler(text, addweapon_photo)],
        },
        fallbacks=[CommandHandler("cancel", addweapon_cancel)],
        allow_reentry=True,
        conversation_timeout=_deps["conv_timeout"],
    ))
    app.add_handler(ConversationHandler(            # ✏️ buttons of the /weapondrops panel (typed value, /cancel stops)
        entry_points=[CallbackQueryHandler(wdi_start, pattern=r"^wdi:")],
        states={WD_INPUT: [MessageHandler(text, wdi_text)]},
        fallbacks=[CommandHandler("cancel", wdi_cancel)],
        allow_reentry=True,
        conversation_timeout=_deps["conv_timeout"],
    ))
    for name, fn in (("weapons", weapons_command), ("weaponshop", weaponshop_command),
                     ("weaponlist", weaponlist_command), ("editweapon", editweapon_command),
                     ("delweapon", delweapon_command), ("giveweapon", giveweapon_command),
                     ("evoweapon", evoweapon_command), ("dropgroups", dropgroups_command),
                     ("weapondrops", weapondrops_command), ("dropconfig", dropconfig_command),
                     ("dropnow", dropnow_command)):
        app.add_handler(CommandHandler(name, fn))
    app.add_handler(CallbackQueryHandler(wshop_callback, pattern=r"^wshop:"))
    app.add_handler(CallbackQueryHandler(wdrop_callback, pattern=r"^wdrop:buy:[0-9a-f]{8}$"))
    app.add_handler(CallbackQueryHandler(dropgroups_callback, pattern=r"^wdg:"))
    app.add_handler(CallbackQueryHandler(wdp_callback, pattern=r"^wdp:"))
    if app.job_queue is not None:
        app.job_queue.run_repeating(_tick_job, interval=TICK_SECONDS, first=20, name="weapon-drop-tick")
    else:                                         # no JobQueue: start the ticker with the bot's own startup hook
        previous = getattr(app, "post_init", None)

        async def _start_ticker(application):
            if previous:
                await previous(application)
            application.bot_data["weapon_tick_task"] = asyncio.create_task(_fallback_loop(application), name="weapon-drop-tick")
        app.post_init = _start_ticker
