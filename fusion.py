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
from datetime import datetime, timedelta, timezone

import mongo_db

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

# Rarities the daily /add target may be picked from. Celestial/Mythical/Legendary are excluded
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
TITLES = {t[0]: f"{t[1]} {t[2]}" for t in CATCH_TASKS}
TITLES["sell"] = "⚪🔵 Sell 15 Common + 5 Rare Characters"
TITLES["add"] = "📚 Collection Add Task"
NEEDED = {t[0]: t[3] for t in CATCH_TASKS}
NEEDED["add"] = 1

# rarity (lower-case) -> progress key for the rarity-specific catch tasks
_RARITY_KEYS = {"epic": "epic", "legendary": "legendary", "mythical": "mythical", "celestial": "celestial"}

RARITY_SYMBOLS = {"Common": "⚪", "Rare": "🔵", "Epic": "🟣", "Legendary": "🟡", "Mythical": "🔴", "Celestial": "🌟"}


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


def _purge_expired(day):
    """Permanently drop previous days' tasks/targets (they can never be claimed again anyway)."""
    try:
        _tasks().delete_many({"day": {"$lt": day}})
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


def _bump(user_id, incs):
    """Atomic progress increment on today's document (created on first use)."""
    day = current_day_key()
    _tasks().update_one(
        {"_id": _task_id(user_id, day)},
        {"$setOnInsert": {"user_id": int(user_id), "day": day}, "$inc": incs},
        upsert=True,
    )


def record_catch_sync(user_id, rarity, code):
    """Called after a successful /add catch. Duplicates count; only real rarity is used."""
    incs = {"progress.catch": 1}
    key = _RARITY_KEYS.get(str(rarity or "").strip().lower())
    if key:
        incs[f"progress.{key}"] = 1
    if str(code) in get_targets():
        incs["progress.add"] = 1   # caught one of today's targets via /add
    _bump(user_id, incs)


def record_sell_sync(user_id, rarity, quantity):
    """Called after a successful /sell. Only Common and Rare sales matter."""
    quantity = int(quantity)
    rarity = str(rarity or "").strip().lower()
    if quantity <= 0 or rarity not in ("common", "rare"):
        return
    _bump(user_id, {f"progress.sell_{rarity}": quantity})


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
def _claim_filter(user_id, day, key):
    """Mongo filter that matches ONLY if the task is completed AND not yet claimed."""
    flt = {"_id": _task_id(user_id, day), f"claimed.{key}": {"$ne": True}}
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
    if mongo_db.col(USERS_COL).find_one({"_id": user_id}, {"_id": 1}) is None:
        return {"status": "nouser", "keys": [], "stones": 0, "balance": 0}

    def _work(session):
        keys, total = [], 0
        for key in TASK_ORDER:
            res = _tasks().update_one(
                _claim_filter(user_id, day, key), {"$set": {f"claimed.{key}": True}}, session=session
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
    doc = _tasks().find_one({"_id": _task_id(user_id, day)}) or {}
    prog = doc.get("progress", {}) or {}
    claimed = doc.get("claimed", {}) or {}
    targets = get_targets(day)

    def status(key, done):
        if claimed.get(key):
            return "🎁 Claimed"
        return "✅ Complete" if done else "🔒 In Progress"

    lines = ["💎 TODAY'S STONE TASKS", ""]
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
        lines.append(TITLES[key])
        if key == "add":
            lines.append(f"Target: {_target_text(targets) if targets else 'No target available today'}")
            lines.append("Catch any ONE of them with /add")
        lines.append(f"Progress: {progress}")
        lines.append(f"Reward: 💎 {reward} {stone_word}")
        lines.append(status(key, done and (key != "add" or bool(targets))))
        lines.append("")
    lines.append(f"💎 Your Special Stones: {get_balance_sync(user_id)}")
    lines.append(f"🔄 Reset in: {format_countdown(now)}")
    return "\n".join(lines)


def claim_text(result):
    if result["status"] == "nouser":
        return "❌ Please use /start first."
    if result["status"] == "nothing":
        return ("❌ No completed tasks to claim right now.\n"
                "Finish a task first - rewards must be claimed before the 2:00 AM IST reset.")
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
    app.add_handler(CommandHandler("stonetask", stonetask_command))
    app.add_handler(CommandHandler("claimstone", claimstone_command))
    app.add_handler(CallbackQueryHandler(stone_claim_callback, pattern=r"^stone:claim:\d+$"))


def register(app):
    """Attach every Fusion handler (stone tasks + Evolution). Call fusion.bind(...) first."""
    _register_stone(app)
    _register_evolution(app)


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
    """'🔵 Rare Naruto (1234)' - row[1] already carries the ⚡ for Evolution characters."""
    return f"{_sym(row[3])} {row[3]} {row[1]} ({row[0]})"


def _parse_int(text):
    t = str(text or "").strip().replace(",", "")
    if not t.isdigit():
        return None
    return int(t)


def _valid_code(code):
    return code.isdigit() and len(code) == 4 and 1 <= int(code) <= 9999


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
    err = validate_recipe(base_code, base_qty, evo_code, stones, berries, second_code, second_qty)
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
    state = {"no_txn": False, "receipt": None, "deducted": None, "deleted": []}

    def _work(session):
        state.update(no_txn=session is None, receipt=None, deducted=None, deleted=[])   # _work may be retried
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
                "stones": stones, "berries": berries, "evo_code": evo_code}

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
    """No-transaction fallback only: put back deleted base copies, refund stones/berries, free the card receipt."""
    try:
        for doc in state["deleted"]:
            mongo_db.col(mongo_db.COLLECTIONS).insert_one(doc)
        if state["deducted"]:
            stones, berries = state["deducted"]
            mongo_db.col(USERS_COL).update_one({"_id": int(user_id)}, {"$inc": {"special_stones": stones, "coins": berries}})
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
    head = "⚡ Evolution List\n\n"
    blocks, n = [], 0
    for r in sorted(_recipes().find({}), key=lambda x: str(x["_id"])):
        ingredients = recipe_ingredients(r)
        rows = [_row(code) for code, _q in ingredients]
        evo = _row(r["_id"])
        if evo is None or any(x is None for x in rows):
            continue   # recipe whose character was deleted: not shown (and cannot be used)
        n += 1
        lines = [f"{n}. {ingredients[0][1]}× {_char_label(rows[0])}"]
        if len(ingredients) > 1:
            lines.append(f"   + {ingredients[1][1]}× {_char_label(rows[1])}")
        lines.append(f"   ➡️ {_char_label(evo)}")
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
        who = f"🧍 Base Character: {rows[0][1]} ×{ingredients[0][1]}\n"
    else:
        who = f"🧍 Card A: {rows[0][1]} ×{ingredients[0][1]}\n🧍 Card B: {rows[1][1]} ×{ingredients[1][1]}\n"
    return (
        "⚡ EVOLUTION\n\n"
        f"{who}"
        f"💎 Evolution Stone: ×{recipe['stones']}\n"
        f"🪙 Berries: {recipe['berries']:,}\n\n"
        "⬇️\n\n"
        f"✨ Result: {evo[1]} ×1\n\n"
        f"You have: {have} • 💎 {stones} • 🪙 {coins:,}"
    )


def success_text(res):
    used = " + ".join(f"{(_row(c)[1] if _row(c) else c)} ×{q}" for c, q in res.get("ingredients") or [(res["base_code"], res["base_qty"])])
    evo = _row(res["evo_code"])
    return (
        "✅ EVOLUTION COMPLETE!\n\n"
        f"🧍 Used: {used}\n"
        f"💎 Stones used: {res['stones']}\n"
        f"🪙 Berries used: {res['berries']:,}\n\n"
        f"✨ Received: {evo[1] if evo else res['evo_code']} ×1\n\n"
        f"💎 Stones left: {res['stones_left']} • 🪙 Berries left: {res['berries_left']:,}"
    )


def _evolve_keyboard(user_id, evo_code):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    return InlineKeyboardMarkup([[InlineKeyboardButton("⚡ EVOLVE", callback_data=f"evo:go:{int(user_id)}:{evo_code}")]])


def _recipe_buttons_sync(user_id, recipes):
    """One button per recipe (max 10): 'Naruto ×2 ➡️ Sage Naruto' or 'Naruto + Sasuke ➡️ Final Fight'."""
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    rows = []
    for r in recipes[:10]:
        ingredients = recipe_ingredients(r)
        cards, evo = [_row(c) for c, _q in ingredients], _row(r["_id"])
        if evo and all(cards):
            names = " + ".join(c[1] for c in cards) if len(cards) > 1 else f"{cards[0][1]} ×{ingredients[0][1]}"
            rows.append([InlineKeyboardButton(f"{names} ➡️ {evo[1]}"[:60], callback_data=f"evo:pick:{int(user_id)}:{r['_id']}")])
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
            await _reply(msg, "⚡ You don't own a character that can evolve right now.\nSee /evolution for every recipe, "
                              "or use /evolve <code or name>.")
        else:
            await _reply(msg, "⚡ Choose what to evolve:", reply_markup=kb)
        return
    recipes, err = await asyncio.to_thread(_resolve_recipe_sync, query)
    if err:
        await _reply(msg, err)
        return
    if len(recipes) > 1:
        kb = await asyncio.to_thread(_recipe_buttons_sync, user.id, recipes)
        await _reply(msg, "⚡ Several evolutions use this card. Choose one:", reply_markup=kb)
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
    await q.answer("⚡ Evolution complete!")
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
                + f"🧬 Recipe: {recipe_text} ➡️ {label} [{code}]\n"
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
    await _reply(msg, "⚡ New Evolution\nChoose the evolution type:", reply_markup=_type_keyboard(user.id))
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
    await _reply(msg, f"{_stepno(context, 5)} Rarity:\nCommon / Rare / Epic / Legendary / Mythical / Celestial")
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
    await _reply(msg, "✅ Evolution created!\n\n" + lines + f"➡️ {_char_label(evo)}\n"
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
                f"🧬 Recipe: {_ingredient_text(recipe)} ➡️ {evo[1]} [{evo[0]}]\n"
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


def validate_recipe_edit(evo_code0, new_code, base_code, base_qty, stones, berries, second_code=None, second_qty=None):
    """Checks for /editevo (the evolution character already exists, so codes are compared against OTHER characters)."""
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
    if not isinstance(stones, int) or stones < EVO_MIN_STONES:
        return f"❌ Evolution Stones must be at least {EVO_MIN_STONES}."
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
    err = validate_recipe_edit(code0, v["code"], v["base"], v["qty"], v["stones"], v["berries"],
                               v.get("second") if pair else None, v.get("qty2") if pair else None)
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
    await _reply(msg, f"3️⃣ Rarity (Common / Rare / Epic / Legendary / Mythical / Celestial), or ⏭ Skip.\n"
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
    return InlineKeyboardMarkup([[InlineKeyboardButton("🧍 Same Card", callback_data=f"evoadd:{int(uid)}:same"),
                                  InlineKeyboardButton("👥 Different Card", callback_data=f"evoadd:{int(uid)}:diff")]])


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
    title = "👥 Different Card" if kind == "pair" else "🧍 Same Card"
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
    await _reply(msg, f"{_xl(d, 9, 11)} Evolution Stones required (minimum {EVO_MIN_STONES}){_skip_hint(d)}.\nCurrent: {_current(cur)}",
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
        if n is None or n < EVO_MIN_STONES:
            await _reply(msg, f"❌ Evolution Stones must be a number of at least {EVO_MIN_STONES}.")
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
        "✅ Evolution edited successfully!\n\n" + lines + f"➡️ {_char_label(evo)}\n"
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
                f"🧬 Recipe: {_ingredient_text(recipe_now)} ➡️ {evo[1]} [{evo[0]}]\n"
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
