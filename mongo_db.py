"""
mongo_db.py - MongoDB Atlas data layer for the anime character bot.

Phase 1/2 scope (core data):
    users, coins, characters (+ recruit names, discontinued flag),
    collections, favorites, and the group / notification / restriction
    registries that used to live in JSON files.

Everything is configured from environment variables (never hardcoded):
    MONGO_URI            required   mongodb+srv://... connection string
    MONGO_DB_NAME        optional   default "anime_bot"
    MONGO_MAX_POOL       optional   default 20
    MONGO_MIN_POOL       optional   default 1
    MONGO_CONNECT_RETRIES optional  default 5
    MONGO_CHAR_CACHE_TTL optional   seconds, default 30
    MONGO_GROUP_CACHE_TTL optional  seconds, default 10

Design notes
------------
* The bot's handlers are synchronous-style code calling a blocking DB (same as
  the old sqlite3 usage), so this module uses the synchronous PyMongo driver.
* Character functions return the same tuples the old SQL code returned:
      (code, name, anime, rarity, worth, photo_file_id)
  so the rest of bot.py keeps working unchanged.
* Retry policy: reads retry on any transient network error. Writes retry ONLY
  when server selection failed (nothing was sent, so it is always safe); the
  driver's own retryWrites=True covers the "sent but no reply" case exactly-once.
  This avoids double-applying a $inc coin update.
* Multi-document changes (daily reward, sell, exchange, delete character...) use
  run_transaction(). Atlas (including the free M0 tier) is a replica set, so
  transactions are supported. If a standalone server is used, it falls back to
  running without a transaction.
"""

import contextvars
import functools
import logging
import os
import re
import threading
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path

from dotenv import load_dotenv
from pymongo import ASCENDING, DESCENDING, MongoClient, ReturnDocument, UpdateOne, monitoring
from pymongo.errors import (
    AutoReconnect,
    ConfigurationError,
    ConnectionFailure,
    DuplicateKeyError,
    NetworkTimeout,
    OperationFailure,
    PyMongoError,
    ServerSelectionTimeoutError,
)

try:  # certifi ships with python-telegram-bot's dependencies (httpx)
    import certifi
except Exception:  # pragma: no cover
    certifi = None

load_dotenv(Path(__file__).with_name(".env"))
logger = logging.getLogger(__name__)

__all__ = [
    "DuplicateKeyError", "PyMongoError", "get_client", "get_db", "col", "close",
    "ping", "init_mongo", "ensure_indexes", "run_transaction", "next_sequence",
]

# --------------------------------------------------------------------------
# Collection names
# --------------------------------------------------------------------------
USERS = "users"
CHARACTERS = "characters"
COLLECTIONS = "collections"
FAVORITES = "favorites"
GROUPS = "groups"
NOTIFICATIONS = "notification_settings"
RESTRICTIONS = "restrictions"
COUNTERS = "counters"

# --------------------------------------------------------------------------
# Connection management
# --------------------------------------------------------------------------
_client = None
_client_lock = threading.Lock()


def _env_int(name, default):
    try:
        return int(os.getenv(name, default))
    except (TypeError, ValueError):
        return int(default)


def _db_name():
    return os.getenv("MONGO_DB_NAME", "anime_bot")


# ---- Performance diagnostics: times every MongoDB command (the round trip, network included) ----
# db_stats_var is set by bot.py for each Telegram update, so the log can say how much of an update's time was spent in the DB.
db_stats_var = contextvars.ContextVar("db_stats", default=None)
_DB_PERF = {"calls": 0, "ms": 0.0, "max": 0.0}
_DB_PERF_LOCK = threading.Lock()
SLOW_DB_MS = _env_int("SLOW_DB_MS", 300)
_QUIET_COMMANDS = {"hello", "isMaster", "ismaster", "saslStart", "saslContinue", "endSessions", "buildInfo", "getnonce"}


class _DbTimer(monitoring.CommandListener):
    def __init__(self):
        self._names = {}

    def started(self, event):
        if event.command_name in _QUIET_COMMANDS:
            return
        try:
            self._names[event.request_id] = str(event.command.get(event.command_name))[:40]
        except Exception:
            pass

    def succeeded(self, event):
        self._done(event)

    def failed(self, event):
        self._done(event)

    def _done(self, event):
        if event.command_name in _QUIET_COMMANDS:
            return
        ms = event.duration_micros / 1000.0
        name = self._names.pop(event.request_id, "?")
        with _DB_PERF_LOCK:
            _DB_PERF["calls"] += 1
            _DB_PERF["ms"] += ms
            _DB_PERF["max"] = max(_DB_PERF["max"], ms)
        stats = db_stats_var.get()
        if stats is not None:
            stats["ms"] += ms
            stats["n"] += 1
        if ms >= SLOW_DB_MS:
            print(f"🐢 SLOW DB {event.command_name} on '{name}': {ms:.0f} ms")


def pop_db_perf():
    """{calls, ms, max} since the last call (used by the periodic performance line in bot.py)."""
    with _DB_PERF_LOCK:
        out = dict(_DB_PERF)
        _DB_PERF.update({"calls": 0, "ms": 0.0, "max": 0.0})
    return out


def measure_latency(samples=4):
    """MongoDB ping round-trip in ms: {avg, min, max}. The first ping (it opens the connection) is left out."""
    client = get_client()
    times = []
    for _ in range(max(2, samples)):
        started = time.perf_counter()
        client.admin.command("ping")
        times.append((time.perf_counter() - started) * 1000.0)
    times = times[1:]
    return {"avg": sum(times) / len(times), "min": min(times), "max": max(times)}


def _build_client():
    uri = os.getenv("MONGO_URI")
    if not uri:
        raise RuntimeError(
            "MONGO_URI is not set. Add it to your .env file or Render environment variables."
        )
    kwargs = dict(
        maxPoolSize=_env_int("MONGO_MAX_POOL", 20),
        minPoolSize=_env_int("MONGO_MIN_POOL", 1),
        maxIdleTimeMS=60_000,
        serverSelectionTimeoutMS=8_000,
        connectTimeoutMS=8_000,
        socketTimeoutMS=20_000,
        waitQueueTimeoutMS=10_000,
        retryWrites=True,
        retryReads=True,
        appName="anime-bot",
        tz_aware=False,
        event_listeners=[_DbTimer()],
    )
    if certifi is not None:
        kwargs["tlsCAFile"] = certifi.where()
    return MongoClient(uri, **kwargs)


def init_mongo(max_attempts=None, base_delay=1.0):
    """Create the shared client and verify it with a ping, with exponential backoff."""
    global _client
    attempts = max_attempts or _env_int("MONGO_CONNECT_RETRIES", 5)
    with _client_lock:
        if _client is not None:
            return _client
        last_exc = None
        for attempt in range(1, attempts + 1):
            client = None
            try:
                client = _build_client()
                client.admin.command("ping")
                _client = client
                logger.info("MongoDB connected (db=%s)", _db_name())
                return _client
            except (RuntimeError, ConfigurationError):
                raise  # missing/invalid URI: retrying cannot help
            except PyMongoError as exc:
                last_exc = exc
                if client is not None:
                    client.close()
                delay = min(base_delay * (2 ** (attempt - 1)), 30)
                logger.warning("MongoDB connect attempt %d/%d failed: %s (retry in %.1fs)",
                               attempt, attempts, exc.__class__.__name__, delay)
                if attempt < attempts:
                    time.sleep(delay)
        raise ConnectionFailure(f"Could not connect to MongoDB after {attempts} attempts: {last_exc}")


def get_client():
    return _client if _client is not None else init_mongo()


def get_db():
    return get_client()[_db_name()]


def col(name):
    return get_db()[name]


def ping():
    try:
        get_client().admin.command("ping")
        return True
    except Exception:
        return False


def close():
    global _client
    with _client_lock:
        if _client is not None:
            _client.close()
            _client = None


# --------------------------------------------------------------------------
# Retry helpers
# --------------------------------------------------------------------------
_READ_RETRY = (AutoReconnect, NetworkTimeout, ServerSelectionTimeoutError, ConnectionFailure)
_WRITE_RETRY = (ServerSelectionTimeoutError,)


def _retrying(exc_types, attempts=3, base_delay=0.4):
    def deco(fn):
        @functools.wraps(fn)
        def wrapper(*args, **kwargs):
            for attempt in range(1, attempts + 1):
                try:
                    return fn(*args, **kwargs)
                except exc_types as exc:
                    if attempt == attempts:
                        logger.error("%s failed after %d attempts: %s", fn.__name__, attempts, exc)
                        raise
                    time.sleep(base_delay * (2 ** (attempt - 1)))
        return wrapper
    return deco


retry_read = _retrying(_READ_RETRY)
retry_write = _retrying(_WRITE_RETRY)


def run_transaction(fn, *, retries=2):
    """
    Run fn(session) inside a multi-document transaction.
    fn may be re-executed on transient errors, so it must only touch MongoDB
    (no Telegram calls / side effects) and must pass `session=` to every call.
    Falls back to fn(None) if the server does not support transactions.
    """
    client = get_client()
    for attempt in range(retries + 1):
        try:
            with client.start_session() as session:
                return session.with_transaction(lambda s: fn(s))
        except OperationFailure as exc:
            msg = str(exc)
            if exc.code == 20 or "replica set" in msg or "Transaction numbers" in msg:
                logger.warning("Transactions unsupported by this server; running without one.")
                return fn(None)
            raise
        except _READ_RETRY:
            if attempt == retries:
                raise
            time.sleep(0.5 * (2 ** attempt))


def next_sequence(name):
    """
    Atomic integer counter (replacement for SQLite AUTOINCREMENT). `name` is the collection name.
    If the counter does not exist yet it is seeded from the highest integer _id already stored,
    so ids can never collide with migrated rows.
    """
    counters = col(COUNTERS)
    if counters.find_one({"_id": name}, {"_id": 1}) is None:
        top = col(name).find_one({"_id": {"$type": "number"}}, {"_id": 1}, sort=[("_id", DESCENDING)])
        try:
            counters.update_one({"_id": name}, {"$setOnInsert": {"seq": int(top["_id"]) if top else 0}}, upsert=True)
        except DuplicateKeyError:
            pass
    doc = counters.find_one_and_update(
        {"_id": name}, {"$inc": {"seq": 1}}, upsert=True, return_document=ReturnDocument.AFTER
    )
    return int(doc["seq"])


@retry_write
def insert_with_id(name, doc, session=None):
    """Insert `doc` into collection `name` with an auto-incrementing integer _id (also stored as `id`)."""
    new_id = next_sequence(name)
    col(name).insert_one(dict(doc, _id=new_id, id=new_id), session=session)
    return new_id


# --------------------------------------------------------------------------
# Indexes
# --------------------------------------------------------------------------
def ensure_indexes():
    """Idempotent. Safe to call on every startup."""
    col(CHARACTERS).create_index([("code", ASCENDING)], unique=True, name="uniq_code")
    col(CHARACTERS).create_index(
        [("name_ci", ASCENDING)], unique=True, name="uniq_name_ci",
        partialFilterExpression={"name_ci": {"$type": "string"}},
    )
    col(CHARACTERS).create_index([("code_int", ASCENDING)], name="code_int")
    col(CHARACTERS).create_index([("rarity", ASCENDING)], name="rarity")
    col("anime_ranges").create_index([("anime_key", ASCENDING)], unique=True, name="uniq_anime_key")
    col(COLLECTIONS).create_index([("user_id", ASCENDING), ("character_code", ASCENDING)], name="user_char")
    col(COLLECTIONS).create_index([("character_code", ASCENDING)], name="char")
    col(GROUPS).create_index([("approved", ASCENDING)], name="approved")
    # ---- step 3 collections
    col("group_character_spawn_v1").create_index(
        [("chat_id", ASCENDING), ("character_code", ASCENDING), ("day_key", ASCENDING)],
        unique=True, name="pk_chat_id_character_code_day_key")
    col("event_claims_v2").create_index(
        [("event_id", ASCENDING), ("user_id", ASCENDING)], unique=True, name="pk_event_id_user_id")
    col("redeem_claims_v2").create_index(
        [("code", ASCENDING), ("user_id", ASCENDING)], unique=True, name="pk_code_user_id")
    col("shop_v3").create_index(
        [("user_id", ASCENDING), ("slot", ASCENDING)], unique=True, name="pk_user_id_slot")
    col("shop_v3").create_index([("shop_day", ASCENDING)], name="shop_day")
    col("transfer_blocks_v2").create_index(
        [("user_id_1", ASCENDING), ("user_id_2", ASCENDING)], unique=True, name="pk_user_id_1_user_id_2")
    col("spawn_history_v2").create_index([("spawned_at", ASCENDING)], name="spawned_at")
    col("spawn_history_v2").create_index([("caught_by", ASCENDING), ("expiry_notified_at", ASCENDING)], name="pending_expiry")
    # Owner log-approval prompts that were never answered are purged by MongoDB after 7 days.
    col(PENDING_LOG_PROMPTS).create_index([("created_at", ASCENDING)], expireAfterSeconds=7 * 86400, name="ttl_created_at")
    col(PENDING_LOG_PROMPTS).create_index([("owner_id", ASCENDING)], name="owner_id")
    # Idempotency receipts for retried requests are purged after 2 days.
    col(OP_RECEIPTS).create_index([("created_at", ASCENDING)], expireAfterSeconds=2 * 86400, name="ttl_created_at")
    col("notification_history_v2").create_index([("user_id", ASCENDING), ("id", ASCENDING)], name="user_id_id")
    col("berry_transfers_v2").create_index([("sender_id", ASCENDING), ("transfer_day", ASCENDING)], name="sender_day")
    col("berry_transfers_v2").create_index([("receiver_id", ASCENDING), ("transfer_day", ASCENDING)], name="receiver_day")
    col("events_v2").create_index([("active", ASCENDING)], name="active")
    ensure_fusion_collections()


def ensure_fusion_collections():
    """Idempotent. Creates the Fusion collections (visible in Atlas right after startup) and their index."""
    existing = set(get_db().list_collection_names())
    for name in (FUSION_STONE_TASKS, FUSION_STONE_DAILY, FUSION_EVOLUTION_RECIPES):
        if name not in existing:
            try:
                get_db().create_collection(name)
            except Exception:   # already created by a concurrent start-up: fine
                pass
    col(FUSION_STONE_TASKS).create_index([("day", ASCENDING)], name="day")
    recipes = col(FUSION_EVOLUTION_RECIPES)
    try:
        recipes.drop_index("uniq_base_code")      # old rule (one recipe per base card): replaced by uniq_pair_key below
    except Exception:
        pass                                      # not there (new database or already migrated)
    for old in list(recipes.find({"pair_key": {"$exists": False}})):    # recipes made before Different Card existed
        recipes.update_one({"_id": old["_id"]}, {"$set": {"pair_key": _recipe_pair_key(old)}})
    recipes.create_index([("pair_key", ASCENDING)], unique=True, name="uniq_pair_key",
                         partialFilterExpression={"pair_key": {"$exists": True}})


# --------------------------------------------------------------------------
# Users & coins
# --------------------------------------------------------------------------
def _user_defaults():
    return {
        "coins": 0, "last_daily": None, "guess_attempts": 0,
        "guess_secret": None, "guess_active": 0, "guess_reward_total": 0,
        # join stamp: only members created after the "View Rules" update have it (old members never get the rules button)
        "joined": datetime.now(timezone(timedelta(hours=5, minutes=30))).replace(tzinfo=None).isoformat(timespec="seconds"),
    }


@retry_write
def save_user(user_id, username="", first_name="", last_name=""):
    """Upsert profile fields; create the user with defaults if new (never resets coins)."""
    col(USERS).update_one(
        {"_id": int(user_id)},
        {"$set": {"username": username or "", "first_name": first_name or "", "last_name": last_name or ""},
         "$setOnInsert": _user_defaults()},
        upsert=True,
    )


@retry_write
def ensure_user(user_id, username="", first_name="", last_name="", session=None):
    """INSERT OR IGNORE equivalent: creates the user only if missing."""
    doc = {"username": username or "", "first_name": first_name or "", "last_name": last_name or ""}
    doc.update(_user_defaults())
    col(USERS).update_one({"_id": int(user_id)}, {"$setOnInsert": doc}, upsert=True, session=session)


@retry_read
def get_user(user_id):
    return col(USERS).find_one({"_id": int(user_id)})


@retry_read
def get_coins(user_id, session=None):
    """Returns int coins, or None if the user does not exist."""
    doc = col(USERS).find_one({"_id": int(user_id)}, {"coins": 1}, session=session)
    if doc is None:
        return None
    return int(doc.get("coins") or 0)


@retry_write
def add_coins(user_id, amount, session=None):
    """Atomic $inc. Returns True if the user exists. Negative amounts allowed."""
    res = col(USERS).update_one({"_id": int(user_id)}, {"$inc": {"coins": int(amount)}}, session=session)
    return res.matched_count == 1


@retry_write
def add_special_stones(user_id, amount, session=None):
    """Atomic $inc of the Special/Evolution Stones (users.special_stones). True if the user exists. Negative amounts allowed."""
    res = col(USERS).update_one({"_id": int(user_id)}, {"$inc": {"special_stones": int(amount)}}, session=session)
    return res.matched_count == 1


@retry_write
def spend_coins(user_id, amount, session=None):
    """Atomic conditional deduct: only succeeds if balance >= amount."""
    amount = int(amount)
    res = col(USERS).update_one(
        {"_id": int(user_id), "coins": {"$gte": amount}}, {"$inc": {"coins": -amount}}, session=session
    )
    return res.modified_count == 1


@retry_read
def get_users_by_ids(user_ids):
    """{user_id: (first_name, last_name, username)} for ids that exist."""
    ids = [int(u) for u in set(user_ids)]
    if not ids:
        return {}
    out = {}
    for d in col(USERS).find({"_id": {"$in": ids}}, {"first_name": 1, "last_name": 1, "username": 1}):
        out[d["_id"]] = (d.get("first_name"), d.get("last_name"), d.get("username"))
    return out


def get_user_names(user_id):
    """(first, last, username) or None - drop-in for the old SELECT first_name,last_name,username."""
    return get_users_by_ids([user_id]).get(int(user_id))


@retry_read
def count_users():
    return col(USERS).count_documents({})


@retry_read
def get_all_user_ids():
    """Every saved user id (used by the owner's DM All)."""
    return [d["_id"] for d in col(USERS).find({}, {"_id": 1})]


@retry_read
def needs_rules_prompt(user_id):
    """True for a NEW member (created after the rules-button update) who has not opened the rules yet, while rules are set."""
    doc = col(USERS).find_one({"_id": int(user_id)}, {"joined": 1, "rules_seen": 1})
    if not doc or not doc.get("joined") or doc.get("rules_seen"):
        return False
    return get_rules() is not None


@retry_read
def has_started(user_id):
    """May this user use the bot in groups? False only for NEW members (never seen, or created after the start-first update)
    who have not opened the bot's PM yet. Members created before the update have no 'joined' stamp and are always allowed."""
    doc = col(USERS).find_one({"_id": int(user_id)}, {"joined": 1, "started": 1})
    if doc is None:
        return False
    return bool(doc.get("started")) or not doc.get("joined")


@retry_write
def mark_started(user_id):
    """The user opened the bot's PM (the only way the bot can message them)."""
    col(USERS).update_one({"_id": int(user_id)}, {"$set": {"started": True}, "$setOnInsert": _user_defaults()}, upsert=True)


@retry_write
def mark_rules_seen(user_id):
    col(USERS).update_one({"_id": int(user_id)}, {"$set": {"rules_seen": True}})


@retry_read
def get_last_daily(user_id, session=None):
    """Returns (user_exists, last_daily_value)."""
    doc = col(USERS).find_one({"_id": int(user_id)}, {"last_daily": 1}, session=session)
    return (doc is not None, None if doc is None else doc.get("last_daily"))


@retry_write
def claim_daily(user_id, expected_last_daily, coins, stamp, session=None):
    """Compare-and-set so two simultaneous /daily calls cannot both pay out."""
    res = col(USERS).update_one(
        {"_id": int(user_id), "last_daily": expected_last_daily},
        {"$inc": {"coins": int(coins)}, "$set": {"last_daily": stamp}},
        session=session,
    )
    return res.modified_count == 1


@retry_read
def get_guess_state(user_id):
    d = col(USERS).find_one({"_id": int(user_id)}, {"guess_attempts": 1, "guess_secret": 1, "guess_active": 1})
    if not d:
        return (0, None, False)
    return (int(d.get("guess_attempts") or 0), d.get("guess_secret"), bool(d.get("guess_active")))


@retry_write
def save_guess_state(user_id, attempts, secret=None, active=False):
    col(USERS).update_one(
        {"_id": int(user_id)},
        {"$set": {"guess_attempts": int(attempts), "guess_secret": secret, "guess_active": int(bool(active))}},
    )


@retry_write
def finish_guess_win(user_id, attempt, per_win, cap):
    """Award min(per_win, cap - total_so_far) coins and close the game. Returns reward."""
    day = (datetime.now(timezone(timedelta(hours=5, minutes=30))) - timedelta(hours=4)).date().isoformat()
    d = col(USERS).find_one({"_id": int(user_id)}, {"guess_reward_total": 1, "guess_reward_day": 1})
    total = int((d or {}).get("guess_reward_total") or 0)
    if (d or {}).get("guess_reward_day") != day:
        total = 0
    reward = min(int(per_win), max(0, int(cap) - total))
    col(USERS).update_one(
        {"_id": int(user_id)},
        {"$inc": {"coins": reward},
         "$set": {"guess_reward_total": total + reward, "guess_reward_day": day,
                  "guess_attempts": int(attempt), "guess_secret": None, "guess_active": 0}},
    )
    return reward


# --------------------------------------------------------------------------
# Characters (returned as tuples: code, name, anime, rarity, worth, photo_file_id)
# --------------------------------------------------------------------------
CHAR_CACHE_TTL = _env_int("MONGO_CHAR_CACHE_TTL", 30)
_char_cache = {"docs": None, "ts": 0.0}
_char_lock = threading.Lock()


def invalidate_character_cache():
    with _char_lock:
        _char_cache["docs"] = None
        _evo_kind_cache["map"] = None


# ---- Character type (NORMAL / EVOLUTION) --------------------------------------------------------------
# Existing characters have no `char_type` field and are NORMAL. Evolution characters are created by /addevo with
# char_type = "EVOLUTION". The 🌟/💫 mark (formerly ⚡) is DISPLAY ONLY: it is added in _row()/display_name() and is never
# stored in the character's name (every write path strips it).
CHAR_TYPE_NORMAL = "NORMAL"
CHAR_TYPE_EVOLUTION = "EVOLUTION"
EVO_MARK = "\u26a1"   # legacy lightning mark: still stripped from names, no longer displayed
EVO_MARK_SAME = "\U0001F31F"   # 🌟 Evolution made from a Same Card recipe
EVO_MARK_DIFF = "\U0001F4AB"   # 💫 Evolution made from a Different Card recipe
_EVO_TAIL_MARKS = (EVO_MARK_SAME, EVO_MARK_DIFF)

# {evolution code: recipe kind}, refreshed with the character cache. Only used to pick the display symbol.
_evo_kind_cache = {"map": None, "ts": 0.0}


def _evo_kinds():
    now = time.monotonic()
    with _char_lock:
        cached = _evo_kind_cache["map"]
        if cached is not None and now - _evo_kind_cache["ts"] < CHAR_CACHE_TTL:
            return cached
    try:
        fresh = {str(d["_id"]): d.get("kind") for d in col("evolution_recipes").find({}, {"kind": 1})}
    except PyMongoError:
        return cached if cached is not None else {}
    with _char_lock:
        _evo_kind_cache["map"] = fresh
        _evo_kind_cache["ts"] = time.monotonic()
    return fresh


def strip_evo_mark(name):
    """Remove every mark (the legacy lightning, also its emoji-variant form, and a trailing 🌟/💫) so a mark is never
    saved, and never doubled. A name without a mark is returned exactly as given."""
    text = str(name or "")
    changed = False
    if EVO_MARK in text:
        text = text.replace(EVO_MARK + "\ufe0f", " ").replace(EVO_MARK, " ")
        changed = True
    while True:
        t = text.rstrip()
        hit = next((m for m in _EVO_TAIL_MARKS if t.endswith(m) or t.endswith(m + "\ufe0f")), None)
        if hit is None:
            break
        text = t[: t.rindex(hit)]
        changed = True
    return " ".join(text.split()) if changed else text


def display_name(name, char_type=None, code=None):
    """Reusable display rule: EVOLUTION -> 'Name 💫' (different-card recipe) or 'Name 🌟' (same-card recipe), exactly one
    mark; NORMAL -> 'Name'."""
    if char_type == CHAR_TYPE_EVOLUTION:
        base = strip_evo_mark(name)
        mark = EVO_MARK_DIFF if _evo_kinds().get(str(code)) == "pair" else EVO_MARK_SAME
        return f"{base} {mark}" if base else name
    return name


def evolution_mark(code):
    """The fusion symbol of an Evolution character by code: 💫 (Different Card recipe) or 🌟 (Same Card recipe)."""
    return EVO_MARK_DIFF if _evo_kinds().get(str(code)) == "pair" else EVO_MARK_SAME


def _row(d):
    return (d["code"], display_name(d.get("name"), d.get("char_type"), d.get("code")), d.get("anime"), d.get("rarity"),
            d.get("worth"), d.get("photo_file_id"))


def _chars():
    now = time.monotonic()
    with _char_lock:
        docs = _char_cache["docs"]
        if docs is not None and now - _char_cache["ts"] < CHAR_CACHE_TTL:
            return docs
    try:
        fresh = _fetch_all_characters()
    except PyMongoError:
        if docs is not None:
            logger.warning("Character refresh failed; serving stale cache.")
            return docs
        raise
    with _char_lock:
        _char_cache["docs"] = fresh
        _char_cache["ts"] = time.monotonic()
    return fresh


@retry_read
def _fetch_all_characters():
    return list(col(CHARACTERS).find({}).sort([("code_int", ASCENDING), ("code", ASCENDING)]))


def get_character_by_code(code):
    code = str(code)
    for d in _chars():
        if d["code"] == code:
            return _row(d)
    return None


def get_all_characters():
    return [_row(d) for d in _chars()]


def get_characters_by_rarity(rarity):
    """Random-spawn / shop / recruit pool. Evolution characters are NEVER in it (checked by char_type)."""
    return [_row(d) for d in _chars()
            if d.get("rarity") == rarity and not d.get("discontinued")
            and d.get("char_type") != CHAR_TYPE_EVOLUTION]


def get_character_type(code):
    """'EVOLUTION' / 'NORMAL', or None if the character does not exist."""
    code = str(code)
    for d in _chars():
        if d["code"] == code:
            return d.get("char_type") or CHAR_TYPE_NORMAL
    return None


def is_evolution_character(code):
    return get_character_type(code) == CHAR_TYPE_EVOLUTION


def get_character_names(codes):
    wanted = {str(c) for c in codes}
    return {d["code"]: display_name(d.get("name"), d.get("char_type"), d.get("code")) for d in _chars() if d["code"] in wanted}


def find_characters_by_name_parts(query):
    parts = [p.strip() for p in str(query).split() if p.strip()]
    if not parts:
        return []
    wanted = [p.casefold() for p in parts]
    wanted_compact = "".join(wanted)
    result = []
    for d in _chars():
        name_parts = [p.casefold() for p in (d.get("name") or "").split() if p.strip()]
        if not name_parts:
            continue
        first, last = name_parts[0], name_parts[-1]
        compact = "".join(name_parts)
        if (len(wanted) == 1 and wanted[0] in {first, last}) or compact == wanted_compact \
                or sorted(wanted) == sorted(name_parts):
            result.append(_row(d))
    return result


def find_character_by_recruit_name(value):
    value = str(value).strip().casefold()
    if not value:
        return None
    for d in _chars():
        if any(str(n).casefold() == value for n in d.get("recruit_names", [])):
            return _row(d)
    return None


def find_characters_by_recruit_name_partial(value):
    value = str(value).strip().casefold()
    if not value:
        return []
    return [_row(d) for d in _chars() if any(value in str(n).casefold() for n in d.get("recruit_names", []))]


def find_characters_by_anime(query):
    """Replacement for: anime=? COLLATE NOCASE OR anime LIKE %?% (substring, case-insensitive)."""
    q = str(query).strip().casefold()
    if not q:
        return []
    return [_row(d) for d in _chars() if q in str(d.get("anime") or "").casefold()]


def get_recruit_names(code):
    code = str(code)
    for d in _chars():
        if d["code"] == code:
            return list(d.get("recruit_names", []))
    return []


def _clean_names(names):
    cleaned, seen = [], set()
    for name in names or []:
        value = str(name).strip()
        key = value.casefold()
        if value and key not in seen:
            seen.add(key)
            cleaned.append(value)
    return cleaned


@retry_write
def set_recruit_names(code, names, session=None):
    cleaned = _clean_names(names)
    col(CHARACTERS).update_one({"code": str(code)}, {"$set": {"recruit_names": cleaned}}, session=session)
    invalidate_character_cache()
    return cleaned


def is_character_discontinued(code):
    code = str(code)
    for d in _chars():
        if d["code"] == code:
            return bool(d.get("discontinued"))
    return False


@retry_write
def discontinue_character(code, user_id, stamp):
    col(CHARACTERS).update_one(
        {"code": str(code)},
        {"$set": {"discontinued": True, "discontinued_at": stamp, "discontinued_by": int(user_id)}},
    )
    invalidate_character_cache()


@retry_write
def continue_character(code):
    res = col(CHARACTERS).update_one(
        {"code": str(code), "discontinued": True},
        {"$unset": {"discontinued": "", "discontinued_at": "", "discontinued_by": ""}},
    )
    invalidate_character_cache()
    return res.modified_count > 0


def _char_doc(code, name, anime, rarity, worth, photo, recruit_names=None, char_type=None):
    code = str(code)
    name = strip_evo_mark(name) if name else name      # the lightning mark is never stored
    doc = {
        "code": code,
        "code_int": int(code) if code.isdigit() else 0,
        "name": name,
        "name_ci": str(name).casefold() if name else None,
        "anime": anime,
        "rarity": rarity,
        "worth": int(worth),
        "photo_file_id": photo,
        "recruit_names": _clean_names(recruit_names),
    }
    if char_type == CHAR_TYPE_EVOLUTION:                # NORMAL characters keep no field (missing == NORMAL)
        doc["char_type"] = CHAR_TYPE_EVOLUTION
    return doc


@retry_write
def insert_character(code, name, anime, rarity, worth, photo=None, recruit_names=None):
    """Raises DuplicateKeyError if the code or (case-insensitive) name already exists."""
    col(CHARACTERS).insert_one(_char_doc(code, name, anime, rarity, worth, photo, recruit_names))
    invalidate_character_cache()


def _recipe_pair_key(doc):
    """Uniqueness key of an Evolution recipe: the base code for a Same Card recipe, 'A+B' (sorted) for a Different Card recipe."""
    if doc.get("kind") == "pair" and doc.get("second_code"):
        return "+".join(sorted([str(doc["base_code"]), str(doc["second_code"])]))
    return str(doc.get("base_code"))


def insert_evolution_character(code, name, anime, rarity, worth, photo, session=None):
    """Create an EVOLUTION character in the normal characters collection. Raises DuplicateKeyError on code/name clash.
    Caller must call invalidate_character_cache() after the surrounding transaction commits."""
    col(CHARACTERS).insert_one(
        _char_doc(code, name, anime, rarity, worth, photo, None, char_type=CHAR_TYPE_EVOLUTION), session=session)


@retry_write
def update_character_photo(code, photo):
    res = col(CHARACTERS).update_one({"code": str(code)}, {"$set": {"photo_file_id": photo}})
    invalidate_character_cache()
    return res.matched_count == 1


def update_character_tx(session, old_code, new_code, name, anime, rarity, worth, recruit_names=None, evolution=False):
    """
    The character-edit writes, to be run INSIDE a transaction (session may be None). Returns False (nothing written) when the
    character does not exist OR is the wrong kind: evolution=False edits NORMAL characters only, evolution=True edits
    EVOLUTION characters only. If the code changes, collections, favorites and Evolution recipes are re-pointed too.
    Raises DuplicateKeyError on code/name clash.
    """
    old_code, new_code = str(old_code), str(new_code)
    name = strip_evo_mark(name) if name else name       # never store the lightning mark (char_type is untouched)
    kind = {"char_type": CHAR_TYPE_EVOLUTION} if evolution else {"char_type": {"$ne": CHAR_TYPE_EVOLUTION}}
    fields = {
        "code": new_code, "code_int": int(new_code) if new_code.isdigit() else 0,
        "name": name, "name_ci": str(name).casefold() if name else None,
        "anime": anime, "rarity": rarity, "worth": int(worth),
    }
    if recruit_names is not None:
        fields["recruit_names"] = _clean_names(recruit_names)
    res = col(CHARACTERS).update_one({"code": old_code, **kind}, {"$set": fields}, session=session)
    if res.matched_count != 1:
        return False
    if new_code != old_code:
        col(COLLECTIONS).update_many({"character_code": old_code}, {"$set": {"character_code": new_code}}, session=session)
        col(FAVORITES).update_many({"character_code": old_code}, {"$set": {"character_code": new_code}}, session=session)
        # Evolution recipes keep pointing at the renumbered character (base side and result side)
        col(FUSION_EVOLUTION_RECIPES).update_many({"base_code": old_code}, {"$set": {"base_code": new_code}}, session=session)
        col(FUSION_EVOLUTION_RECIPES).update_many({"second_code": old_code}, {"$set": {"second_code": new_code}}, session=session)
        for changed in list(col(FUSION_EVOLUTION_RECIPES).find({"$or": [{"base_code": new_code}, {"second_code": new_code}]},
                                                               session=session)):
            col(FUSION_EVOLUTION_RECIPES).update_one({"_id": changed["_id"]}, {"$set": {"pair_key": _recipe_pair_key(changed)}},
                                                     session=session)
        recipe = col(FUSION_EVOLUTION_RECIPES).find_one({"_id": old_code}, session=session)
        if recipe:
            col(FUSION_EVOLUTION_RECIPES).delete_one({"_id": old_code}, session=session)
            recipe.update({"_id": new_code, "evo_code": new_code})
            col(FUSION_EVOLUTION_RECIPES).insert_one(recipe, session=session)
    return True


def update_character(old_code, new_code, name, anime, rarity, worth, recruit_names=None, evolution=False):
    """Edit a character (normal ones by default; Evolution characters are edited with /editevo -> evolution=True)."""
    try:
        return run_transaction(lambda session: update_character_tx(
            session, old_code, new_code, name, anime, rarity, worth, recruit_names, evolution))
    finally:
        invalidate_character_cache()


def delete_character(code):
    """Delete a character plus every collection copy and favorite pointing at it."""
    code = str(code)

    def _work(session):
        col(COLLECTIONS).delete_many({"character_code": code}, session=session)
        col(FAVORITES).delete_many({"character_code": code}, session=session)
        # a recipe whose base or result character is gone can never work: remove it
        col(FUSION_EVOLUTION_RECIPES).delete_many({"$or": [{"_id": code}, {"base_code": code}, {"second_code": code}]},
                                                  session=session)
        return col(CHARACTERS).delete_one({"code": code}, session=session).deleted_count == 1

    try:
        return run_transaction(_work)
    finally:
        invalidate_character_cache()


def seed_characters(characters, worth_map, rarity_overrides=None, first_code=1001):
    """
    Insert built-in characters that are missing (never overwrites existing rows or photos).
    Mirrors the old INSERT OR IGNORE + 'Mythic'->'Mythical' + popular-override logic.
    """
    ops = []
    for code, (name, anime, rarity) in enumerate(characters, first_code):
        doc = _char_doc(code, name, anime, rarity, worth_map[rarity], None)
        ops.append(UpdateOne({"code": doc["code"]}, {"$setOnInsert": doc}, upsert=True))
    try:
        if ops:
            col(CHARACTERS).bulk_write(ops, ordered=False)
    except DuplicateKeyError:
        logger.warning("Seed skipped a built-in character whose name already exists under another code.")
    except Exception as exc:  # BulkWriteError for name clashes is non-fatal
        logger.warning("Character seeding warning: %s", exc)
    if "Mythical" in worth_map:
        col(CHARACTERS).update_many({"rarity": "Mythic"}, {"$set": {"rarity": "Mythical", "worth": worth_map["Mythical"]}})
    for name, rarity in (rarity_overrides or {}).items():
        col(CHARACTERS).update_one(
            {"name_ci": str(name).casefold()}, {"$set": {"rarity": rarity, "worth": worth_map[rarity]}}
        )
    invalidate_character_cache()


@retry_read
def count_characters():
    return col(CHARACTERS).count_documents({})


# --------------------------------------------------------------------------
# Collections (one document per owned copy)
# --------------------------------------------------------------------------
@retry_write
def add_collection(user_id, code, caught_at, session=None):
    res = col(COLLECTIONS).insert_one(
        {"user_id": int(user_id), "character_code": str(code), "caught_at": caught_at}, session=session
    )
    return res.inserted_id


@retry_write
def add_collections(user_id, codes, caught_at, session=None):
    docs = [{"user_id": int(user_id), "character_code": str(c), "caught_at": caught_at} for c in codes]
    if docs:
        col(COLLECTIONS).insert_many(docs, session=session)


@retry_write
def delete_collection_by_id(copy_id, session=None):
    return col(COLLECTIONS).delete_one({"_id": copy_id}, session=session).deleted_count == 1


@retry_read
def count_user_collection(user_id):
    return col(COLLECTIONS).count_documents({"user_id": int(user_id)})


@retry_read
def count_user_copies(user_id, code, session=None):
    return col(COLLECTIONS).count_documents({"user_id": int(user_id), "character_code": str(code)}, session=session)


@retry_read
def user_owns(user_id, code, session=None):
    return col(COLLECTIONS).find_one(
        {"user_id": int(user_id), "character_code": str(code)}, {"_id": 1}, session=session
    ) is not None


@retry_read
def find_copy_id(user_id, code, session=None):
    d = col(COLLECTIONS).find_one({"user_id": int(user_id), "character_code": str(code)}, {"_id": 1}, session=session)
    return d["_id"] if d else None


@retry_read
def count_collections():
    return col(COLLECTIONS).count_documents({})


@retry_read
def get_collection_summary(user_id):
    """[(code, name, anime, rarity, photo, qty, last_caught)] - same shape as the old JOIN."""
    pipeline = [
        {"$match": {"user_id": int(user_id)}},
        {"$group": {"_id": "$character_code", "qty": {"$sum": 1}, "last": {"$max": "$caught_at"}}},
    ]
    stats = {d["_id"]: d for d in col(COLLECTIONS).aggregate(pipeline)}
    rows = []
    for d in _chars():
        s = stats.get(d["code"])
        if s:
            rows.append((d["code"], display_name(d.get("name"), d.get("char_type"), d.get("code")), d.get("anime"), d.get("rarity"),
                         d.get("photo_file_id"), int(s["qty"]), s.get("last")))
    return rows


@retry_read
def get_character_owners(code):
    """[(user_id, qty)] sorted by qty desc."""
    pipeline = [
        {"$match": {"character_code": str(code)}},
        {"$group": {"_id": "$user_id", "qty": {"$sum": 1}}},
        {"$sort": {"qty": -1, "_id": -1}},  # ties: user_id DESC, exactly what SQLite's ORDER BY COUNT(*) DESC produced
    ]
    return [(d["_id"], int(d["qty"])) for d in col(COLLECTIONS).aggregate(pipeline)]


@retry_read
def find_copy_ids(user_id, code, limit, session=None):
    cur = col(COLLECTIONS).find(
        {"user_id": int(user_id), "character_code": str(code)}, {"_id": 1}, session=session
    ).limit(int(limit))
    return [d["_id"] for d in cur]


@retry_write
def delete_collection_ids(ids, session=None):
    if ids:
        col(COLLECTIONS).delete_many({"_id": {"$in": list(ids)}}, session=session)


def remove_copies(user_id, code, quantity):
    """
    Atomically remove `quantity` copies (all or nothing).
    Returns (ok, available). If the user owns the character no more, any favorite on it is cleared.
    """
    quantity = int(quantity)

    def _work(session):
        ids = find_copy_ids(user_id, code, quantity, session=session)
        if len(ids) < quantity:
            return (False, len(ids))
        delete_collection_ids(ids, session=session)
        if count_user_copies(user_id, code, session=session) == 0:
            col(FAVORITES).delete_one({"_id": int(user_id), "character_code": str(code)}, session=session)
        return (True, len(ids))

    return run_transaction(_work)


def sell_copies(user_id, code, quantity, total_value):
    """Delete copies and credit coins in one transaction. Returns (ok, available)."""
    quantity = int(quantity)

    def _work(session):
        ids = find_copy_ids(user_id, code, quantity, session=session)
        if len(ids) < quantity:
            return (False, len(ids))
        delete_collection_ids(ids, session=session)
        if not add_coins(user_id, total_value, session=session):
            raise RuntimeError("seller account missing")
        return (True, len(ids))  # (like the original, /sell never touches favorites)

    return run_transaction(_work)


@retry_write
def transfer_one_copy(sender_id, target_id, code):
    """Atomically move one copy sender -> target. Returns True if the sender owned one. Favorites untouched."""
    d = col(COLLECTIONS).find_one_and_update(
        {"user_id": int(sender_id), "character_code": str(code)},
        {"$set": {"user_id": int(target_id)}},
        projection={"_id": 1},
    )
    return d is not None  # (like the original, /transfer never touches favorites)


def swap_copies(copy_a, owner_a, copy_b, owner_b):
    """Exchange two specific copies between their owners. True on success."""
    def _work(session):
        a = col(COLLECTIONS).update_one({"_id": copy_a, "user_id": int(owner_a)}, {"$set": {"user_id": int(owner_b)}}, session=session)
        b = col(COLLECTIONS).update_one({"_id": copy_b, "user_id": int(owner_b)}, {"$set": {"user_id": int(owner_a)}}, session=session)
        if a.modified_count != 1 or b.modified_count != 1:
            raise _AbortTransaction()
        return True

    try:
        return run_transaction(_work)
    except _AbortTransaction:
        return False


class _AbortTransaction(Exception):
    pass


# --------------------------------------------------------------------------
# Favorites
# --------------------------------------------------------------------------
@retry_read
def get_favorite_code(user_id):
    d = col(FAVORITES).find_one({"_id": int(user_id)})
    return d["character_code"] if d else None


@retry_write
def set_favorite(user_id, code, stamp):
    col(FAVORITES).update_one(
        {"_id": int(user_id)}, {"$set": {"character_code": str(code), "set_at": stamp}}, upsert=True
    )


@retry_write
def clear_favorite(user_id):
    col(FAVORITES).delete_one({"_id": int(user_id)})


# --------------------------------------------------------------------------
# Group registry (replaces approved_groups / auto_spawn_groups / bot_groups /
# bot_group_state / gstats_hidden_groups JSON files). One doc per chat.
#   _id: chat_id (int)
#   approved, auto_spawn, registered, gstats_hidden : bool
#   bot_enabled : bool (absent => default True)
#   title, type, username : set while registered
# --------------------------------------------------------------------------
GROUP_CACHE_TTL = _env_int("MONGO_GROUP_CACHE_TTL", 10)
_group_cache = {"docs": None, "ts": 0.0}
_group_lock = threading.Lock()


def _invalidate_groups():
    with _group_lock:
        _group_cache["docs"] = None


def _group_docs():
    now = time.monotonic()
    with _group_lock:
        docs = _group_cache["docs"]
        if docs is not None and now - _group_cache["ts"] < GROUP_CACHE_TTL:
            return docs
    try:
        fresh = _fetch_groups()
    except PyMongoError:
        if docs is not None:
            logger.warning("Group registry refresh failed; serving stale cache.")
            return docs
        raise
    with _group_lock:
        _group_cache["docs"] = fresh
        _group_cache["ts"] = time.monotonic()
    return fresh


@retry_read
def _fetch_groups():
    return {int(d["_id"]): d for d in col(GROUPS).find({})}


@retry_write
def _set_group_fields(chat_id, set_fields=None, unset_fields=None):
    update = {}
    if set_fields:
        update["$set"] = set_fields
    if unset_fields:
        update["$unset"] = {k: "" for k in unset_fields}
    col(GROUPS).update_one({"_id": int(chat_id)}, update, upsert=True)
    _invalidate_groups()
    return True


def _flag_set(flag):
    return {cid for cid, d in _group_docs().items() if d.get(flag)}


def _replace_flag_set(flag, ids):
    """Make `flag` True for exactly `ids` (used only by legacy whole-set save_* wrappers)."""
    ids = {int(x) for x in ids}
    ops = [UpdateOne({"_id": i}, {"$set": {flag: True}}, upsert=True) for i in ids]
    if ops:
        col(GROUPS).bulk_write(ops, ordered=False)
    col(GROUPS).update_many({"_id": {"$nin": list(ids)}, flag: True}, {"$set": {flag: False}})
    _invalidate_groups()
    return True


# approved
def load_approved_groups():
    return _flag_set("approved")


def set_group_approved(chat_id, approved=True):
    return _set_group_fields(chat_id, {"approved": bool(approved)})


def replace_approved_groups(ids):
    return _replace_flag_set("approved", ids)


# auto-spawn
def load_auto_spawn_groups():
    return _flag_set("auto_spawn")


def set_auto_spawn_group(chat_id, enabled=True):
    return _set_group_fields(chat_id, {"auto_spawn": bool(enabled)})


# gstats hidden
def load_gstats_hidden_groups():
    return _flag_set("gstats_hidden")


def hide_gstats_group(chat_id):
    return _set_group_fields(chat_id, {"gstats_hidden": True})


def unhide_gstats_group(chat_id):
    """Show a group in /gstats again (the Hide button in the group's manage page only sets this flag)."""
    return _set_group_fields(chat_id, {"gstats_hidden": False})


# registered bot groups (title info)
def load_bot_groups():
    out = {}
    for cid, d in _group_docs().items():
        if d.get("registered"):
            out[str(cid)] = {"title": d.get("title"), "type": d.get("type"), "username": d.get("username")}
    return out


def replace_bot_groups(groups):
    """
    Make the registered-group list exactly `groups` ({chat_id: {title, type, username}}),
    like the old bot_groups.json overwrite: anything not listed is un-registered.
    """
    ids = []
    for key, info in groups.items():
        cid = int(key)
        ids.append(cid)
        col(GROUPS).update_one(
            {"_id": cid},
            {"$set": {"registered": True, "title": info.get("title"), "type": info.get("type"),
                      "username": info.get("username")}},
            upsert=True,
        )
    col(GROUPS).update_many(
        {"registered": True, "_id": {"$nin": ids}},
        {"$set": {"registered": False}, "$unset": {"title": "", "type": "", "username": ""}},
    )
    _invalidate_groups()
    return True


def register_bot_group_info(chat_id, title, chat_type, username):
    return _set_group_fields(
        chat_id, {"registered": True, "title": title, "type": chat_type, "username": username}
    )


def unregister_bot_group(chat_id):
    return _set_group_fields(chat_id, {"registered": False}, ["title", "type", "username"])


# enable/disable state (default: enabled)
def load_bot_group_states():
    return {str(cid): bool(d["bot_enabled"]) for cid, d in _group_docs().items() if "bot_enabled" in d}


def is_bot_enabled(chat_id):
    d = _group_docs().get(int(chat_id))
    return bool(d["bot_enabled"]) if d and "bot_enabled" in d else True


def set_bot_enabled(chat_id, enabled):
    _set_group_fields(chat_id, {"bot_enabled": bool(enabled)})
    return bool(enabled)


def replace_bot_group_states(states):
    states = {int(k): bool(v) for k, v in states.items()}
    ops = [UpdateOne({"_id": k}, {"$set": {"bot_enabled": v}}, upsert=True) for k, v in states.items()]
    if ops:
        col(GROUPS).bulk_write(ops, ordered=False)
    col(GROUPS).update_many({"_id": {"$nin": list(states)}, "bot_enabled": {"$exists": True}}, {"$unset": {"bot_enabled": ""}})
    _invalidate_groups()
    return True


def cleanup_left_group(chat_id):
    """Bot left / was removed: forget approval, auto-spawn, registration and enable-state."""
    return _set_group_fields(
        chat_id,
        {"approved": False, "auto_spawn": False, "registered": False},
        ["bot_enabled", "title", "type", "username", "gstats_hidden"],
    )


# ---- Auto Approve (Owner setting). Stored in bot_settings (_id "auto_approve"); BOT_SETTINGS is defined further down,
# which is fine because these functions only read it when they run.
_AUTO_APPROVE_TTL = 5.0
_auto_approve_cache = {"v": None, "ts": 0.0}


@retry_read
def _fetch_auto_approve():
    d = col(BOT_SETTINGS).find_one({"_id": "auto_approve"}) or {}
    try:
        minimum = max(0, int(d.get("min_members") or 0))
    except (TypeError, ValueError):
        minimum = 0
    return {"enabled": bool(d.get("enabled")), "min_members": minimum,
            "set_by": d.get("set_by"), "set_at": d.get("set_at")}


def get_auto_approve(fresh=False):
    """{enabled, set_by, set_at}. Cached for a few seconds (it is read whenever the bot is added to a group)."""
    now = time.monotonic()
    cached = _auto_approve_cache["v"]
    if not fresh and cached is not None and now - _auto_approve_cache["ts"] < _AUTO_APPROVE_TTL:
        return dict(cached)
    value = _fetch_auto_approve()
    _auto_approve_cache["v"] = value
    _auto_approve_cache["ts"] = time.monotonic()
    return dict(value)


@retry_write
def set_auto_approve(enabled, set_by=None, set_at=None):
    col(BOT_SETTINGS).update_one(
        {"_id": "auto_approve"},
        {"$set": {"enabled": bool(enabled), "set_by": set_by, "set_at": set_at}},
        upsert=True,
    )
    _auto_approve_cache["v"] = None
    return bool(enabled)


@retry_write
def set_auto_approve_min_members(min_members, set_by=None, set_at=None):
    """Smallest member count a new group needs to be auto-approved (0 = no limit). Leaves the ON/OFF switch alone."""
    value = max(0, int(min_members))
    col(BOT_SETTINGS).update_one(
        {"_id": "auto_approve"},
        {"$set": {"min_members": value, "set_by": set_by, "set_at": set_at}},
        upsert=True,
    )
    _auto_approve_cache["v"] = None
    return value


def load_pending_groups():
    """[(chat_id, title)] of groups the bot is in (registered) that are not approved yet. Always a fresh read."""
    _invalidate_groups()
    out = []
    for cid, d in _fetch_groups().items():
        if d.get("registered") and not d.get("approved"):
            out.append((int(cid), d.get("title")))
    return out


# --------------------------------------------------------------------------
# Per-user notification toggle (default: DISABLED - a user must explicitly turn it ON)
# --------------------------------------------------------------------------
@retry_read
def notifications_enabled_for(user_id):
    d = col(NOTIFICATIONS).find_one({"_id": int(user_id)})
    return bool(d.get("enabled", False)) if d else False


@retry_write
def set_notifications_enabled_for(user_id, enabled):
    col(NOTIFICATIONS).update_one({"_id": int(user_id)}, {"$set": {"enabled": bool(enabled)}}, upsert=True)


# --------------------------------------------------------------------------
# Restrictions (_id = user_id, plus the old JSON entry fields)
# --------------------------------------------------------------------------
def _restriction_entry(d):
    entry = {k: v for k, v in d.items() if k != "_id"}
    return entry


@retry_read
def load_restrictions():
    return {str(d["_id"]): _restriction_entry(d) for d in col(RESTRICTIONS).find({})}


@retry_read
def get_restriction(user_id):
    d = col(RESTRICTIONS).find_one({"_id": int(user_id)})
    return _restriction_entry(d) if d else None


@retry_write
def set_restriction(user_id, entry):
    entry = {k: v for k, v in dict(entry).items() if k != "_id"}
    col(RESTRICTIONS).replace_one({"_id": int(user_id)}, entry, upsert=True)


@retry_write
def remove_restriction(user_id):
    return col(RESTRICTIONS).delete_one({"_id": int(user_id)}).deleted_count == 1


def replace_restrictions(data):
    ids = []
    for k, v in data.items():
        entry = dict(v) if isinstance(v, dict) else {"expiry": int(v)}
        set_restriction(int(k), entry)
        ids.append(int(k))
    col(RESTRICTIONS).delete_many({"_id": {"$nin": ids}})


# --------------------------------------------------------------------------
# Bot settings (collection `bot_settings`, one document per setting)
#   _id "log_channel":    LEGACY single channel {chat_id, title, username, set_by, set_at} (read only until the first
#                         multi-channel write, then migrated into "log_channels")
#   _id "log_channels":   {channels: {"<chat_id>": {title, username, set_by, set_at}}, default: chat_id|None,
#                          routes: {commands: {command: chat_id}, categories: {category: chat_id}}}
#   _id "log_categories": {custom: {name: description}, disabled: [category names]}
#   _id "command_mappings": {map: {command: category}}   (Owner /logmap: command -> log category)
#   _id "rules":          {text, updated_by, updated_at}
#   _id "auto_approve":   {enabled, min_members, set_by, set_at}   (Owner /autoapprove: approve new groups automatically;
#                          min_members = smallest group size that is auto-approved, 0 = no limit)
# Category switches live in their own document so unlinking/re-linking the log channel keeps them.
# --------------------------------------------------------------------------
BOT_SETTINGS = "bot_settings"
PENDING_LOG_PROMPTS = "pending_log_prompts"
OP_RECEIPTS = "op_receipts"

# ---- Fusion system collections (Special Stone daily tasks, Evolution) - used by fusion.py
FUSION_STONE_TASKS = "stone_tasks"            # one doc per user per IST day: task progress + claimed flags
FUSION_STONE_DAILY = "stone_daily"            # one doc per IST day: the daily /add target character codes
FUSION_EVOLUTION_RECIPES = "evolution_recipes"  # one doc per Evolution character code (used by the Evolution system)


@retry_read
def get_log_config():
    """
    Everything the logger needs in one read (flat dict, never None):
      chat_id            DEFAULT log channel id (None when no log channel is linked), title, username, set_by, set_at
      channels           {"<chat_id>": {title, username, set_by, set_at}}  every linked log channel
      routes             {"commands": {command: chat_id}, "categories": {category: chat_id}}
      custom_categories {name: description}, disabled_categories [names], command_mappings {command: category}
    """
    docs = {d["_id"]: d for d in col(BOT_SETTINGS).find(
        {"_id": {"$in": ["log_channel", "log_channels", "log_categories", "command_mappings"]}})}
    legacy = docs.get("log_channel") if isinstance(docs.get("log_channel"), dict) else {}
    multi = docs.get("log_channels") if isinstance(docs.get("log_channels"), dict) else None
    cats = docs.get("log_categories") if isinstance(docs.get("log_categories"), dict) else {}
    maps = docs.get("command_mappings") if isinstance(docs.get("command_mappings"), dict) else {}
    disabled = _as_list(cats.get("disabled"))
    for old in _as_list(legacy.get("disabled_categories")):      # older versions stored switches on the channel doc
        if old not in disabled:
            disabled.append(old)

    channels = {}
    if multi is not None:
        for k, v in _as_dict(multi.get("channels")).items():
            channels[str(k)] = v if isinstance(v, dict) else {}
        default = multi.get("default")
        routes = _as_dict(multi.get("routes"))
    else:                                                          # nothing migrated yet: the legacy channel is the only one
        default = legacy.get("chat_id")
        routes = {}
        if default is not None:
            channels[str(int(default))] = {k: legacy.get(k) for k in ("title", "username", "set_by", "set_at")}
    if default is None or str(default) not in channels:
        default = int(next(iter(channels))) if channels else None
    info = channels.get(str(default), {}) if default is not None else {}
    return {
        "chat_id": default, "title": info.get("title", "") or "", "username": info.get("username", "") or "",
        "set_by": info.get("set_by"), "set_at": info.get("set_at"),
        "channels": channels,
        "routes": {"commands": _as_dict(routes.get("commands")), "categories": _as_dict(routes.get("categories"))},
        "custom_categories": _as_dict(cats.get("custom")),
        "disabled_categories": disabled,
        "command_mappings": _as_dict(maps.get("map")),
    }


def _ensure_log_channels_doc():
    """Return the `log_channels` document, creating it (and migrating the legacy single channel) on first use."""
    d = col(BOT_SETTINGS).find_one({"_id": "log_channels"})
    if isinstance(d, dict):
        return d
    legacy = col(BOT_SETTINGS).find_one({"_id": "log_channel"}) or {}
    channels, default = {}, None
    if legacy.get("chat_id") is not None:
        default = int(legacy["chat_id"])
        channels[str(default)] = {k: legacy.get(k) for k in ("title", "username", "set_by", "set_at")}
    try:
        col(BOT_SETTINGS).update_one(
            {"_id": "log_channels"},
            {"$setOnInsert": {"channels": channels, "default": default,
                              "routes": {"commands": {}, "categories": {}}}},
            upsert=True)
    except DuplicateKeyError:
        pass                                  # a concurrent writer created it first: just read theirs
    return col(BOT_SETTINGS).find_one({"_id": "log_channels"}) or {}


@retry_write
def add_log_channel(chat_id, title, username, set_by, set_at):
    """
    Link one more log channel (or refresh an already linked one). The first channel becomes the default.
    Returns {"is_default": bool, "already": bool, "count": total channels after the call}.
    """
    cid = int(chat_id)
    doc = _ensure_log_channels_doc()
    already = str(cid) in _as_dict(doc.get("channels"))
    col(BOT_SETTINGS).update_one({"_id": "log_channels"}, {"$set": {
        f"channels.{cid}": {"title": title or "", "username": username or "",
                            "set_by": int(set_by), "set_at": set_at}}})
    # Atomic default election: only succeeds while no default exists, so concurrent /setlog calls cannot disagree.
    col(BOT_SETTINGS).update_one({"_id": "log_channels", "default": None}, {"$set": {"default": cid}})
    fresh = col(BOT_SETTINGS).find_one({"_id": "log_channels"}) or {}
    channels = _as_dict(fresh.get("channels"))
    default = fresh.get("default")
    if default is None or str(default) not in channels:       # stale default (should not happen): repair it
        default = cid
        col(BOT_SETTINGS).update_one({"_id": "log_channels"}, {"$set": {"default": cid}})
    return {"is_default": int(default) == cid, "already": already, "count": len(channels)}


def set_log_channel(chat_id, title, username, set_by, set_at):
    """Backwards-compatible alias: links the channel (multi-channel aware)."""
    return add_log_channel(chat_id, title, username, set_by, set_at)


@retry_write
def remove_log_channel(chat_id=None):
    """
    Unlink one log channel (chat_id) or all of them (None). Routes that pointed at it are dropped and, when it
    was the default, another linked channel takes over. Returns {"removed": count, "default": new default|None,
    "routes_removed": count}. Category switches and custom categories are kept.
    """
    doc = _ensure_log_channels_doc()
    channels = _as_dict(doc.get("channels"))
    routes = _as_dict(doc.get("routes"))
    if chat_id is None:
        n_routes = sum(len(_as_dict(routes.get(k))) for k in ("commands", "categories"))
        col(BOT_SETTINGS).update_one(
            {"_id": "log_channels"},
            {"$set": {"channels": {}, "default": None, "routes": {"commands": {}, "categories": {}}}})
        col(BOT_SETTINGS).delete_one({"_id": "log_channel"})
        return {"removed": len(channels), "default": None, "routes_removed": n_routes}
    cid = int(chat_id)
    if str(cid) not in channels:
        return {"removed": 0, "default": doc.get("default"), "routes_removed": 0}
    unset, n_routes = {f"channels.{cid}": ""}, 0
    for kind in ("commands", "categories"):
        for key, target in _as_dict(routes.get(kind)).items():
            if str(target) == str(cid):
                unset[f"routes.{kind}.{key}"] = ""
                n_routes += 1
    new_default = doc.get("default")
    if new_default is None or str(new_default) == str(cid) or str(new_default) not in channels:
        remaining = [int(c) for c in channels if c != str(cid)]
        new_default = remaining[0] if remaining else None
    col(BOT_SETTINGS).update_one({"_id": "log_channels"}, {"$unset": unset, "$set": {"default": new_default}})
    legacy = col(BOT_SETTINGS).find_one({"_id": "log_channel"}) or {}
    if legacy.get("chat_id") is not None and int(legacy["chat_id"]) == cid:
        col(BOT_SETTINGS).delete_one({"_id": "log_channel"})
    return {"removed": 1, "default": new_default, "routes_removed": n_routes}


def clear_log_channel():
    """Backwards-compatible alias: unlink every log channel. True if at least one was linked."""
    return remove_log_channel(None)["removed"] > 0


@retry_write
def set_log_default(chat_id):
    """Make an already linked channel the default one. False if it is not linked."""
    doc = _ensure_log_channels_doc()
    if str(int(chat_id)) not in _as_dict(doc.get("channels")):
        return False
    col(BOT_SETTINGS).update_one({"_id": "log_channels"}, {"$set": {"default": int(chat_id)}})
    return True


@retry_write
def set_log_route(kind, key, chat_id):
    """
    Route a category (kind="categories") or a command (kind="commands") to a linked channel.
    `key` must already be validated (lowercase letters/digits/underscore). Returns the previous channel id or None;
    raises ValueError when the channel is not linked.
    """
    if kind not in ("commands", "categories"):
        raise ValueError("kind must be 'commands' or 'categories'")
    doc = _ensure_log_channels_doc()
    if str(int(chat_id)) not in _as_dict(doc.get("channels")):
        raise ValueError("channel is not linked")
    before = col(BOT_SETTINGS).find_one_and_update(
        {"_id": "log_channels"}, {"$set": {f"routes.{kind}.{key}": int(chat_id)}},
        return_document=ReturnDocument.BEFORE) or {}
    return _as_dict(_as_dict(before.get("routes")).get(kind)).get(key)


@retry_write
def clear_log_route(kind, key):
    """Remove one route (the entry falls back to the next rule / the default channel). True if it existed."""
    if kind not in ("commands", "categories"):
        return False
    res = col(BOT_SETTINGS).update_one(
        {"_id": "log_channels", f"routes.{kind}.{key}": {"$exists": True}},
        {"$unset": {f"routes.{kind}.{key}": ""}})
    return res.modified_count == 1


@retry_write
def set_log_category(category, enabled):
    """Enable/disable one log category (built-in or custom)."""
    if enabled:
        col(BOT_SETTINGS).update_one({"_id": "log_categories"}, {"$pull": {"disabled": category}})
        col(BOT_SETTINGS).update_one({"_id": "log_channel"}, {"$pull": {"disabled_categories": category}})
    else:
        col(BOT_SETTINGS).update_one({"_id": "log_categories"}, {"$addToSet": {"disabled": category}}, upsert=True)
    return True


@retry_write
def set_all_log_categories(categories, enabled):
    """Enable or disable every category in `categories` at once."""
    col(BOT_SETTINGS).update_one(
        {"_id": "log_categories"}, {"$set": {"disabled": [] if enabled else list(categories)}}, upsert=True)
    col(BOT_SETTINGS).update_one({"_id": "log_channel"}, {"$set": {"disabled_categories": []}})
    return True


@retry_write
def add_custom_category(name, description, op_id=None):
    """
    Create a custom log category, enabled by default. Atomic: returns False if the name already exists.
    `name` must already be validated (lowercase letters/digits/underscore: it becomes a field name).
    `op_id` (the Telegram message id) makes a retried request idempotent: if THIS request already created
    the category, the retry returns True instead of a misleading "already exists".
    """
    to_set = {f"custom.{name}": description}
    if op_id:
        to_set[f"add_ops.{name}"] = str(op_id)
    try:
        res = col(BOT_SETTINGS).update_one(
            {"_id": "log_categories", f"custom.{name}": {"$exists": False}},
            {"$set": to_set, "$unset": {f"remove_ops.{name}": ""}, "$pull": {"disabled": name}},
            upsert=True,
        )
        if res.modified_count or res.upserted_id:
            return True
    except DuplicateKeyError:           # filter did not match an existing document that already has the key
        pass
    if op_id:
        d = col(BOT_SETTINGS).find_one({"_id": "log_categories"}) or {}
        return _as_dict(d.get("add_ops")).get(name) == str(op_id)
    return False


@retry_write
def remove_custom_category(name, op_id=None):
    """
    Delete a custom category and its description, and cascade-delete every command mapping that pointed at it.
    Returns (removed, deleted_mappings): removed is False (and the count 0) when no such category existed.
    A retried request (same `op_id`) that finds the category already removed by itself returns (True, 0).
    """
    update = {"$unset": {f"custom.{name}": "", f"add_ops.{name}": ""}, "$pull": {"disabled": name}}
    if op_id:
        update["$set"] = {f"remove_ops.{name}": str(op_id)}
    res = col(BOT_SETTINGS).update_one({"_id": "log_categories", f"custom.{name}": {"$exists": True}}, update)
    if res.modified_count == 1:
        return True, remove_mappings_for_category(name)
    if op_id:
        d = col(BOT_SETTINGS).find_one({"_id": "log_categories"}) or {}
        if _as_dict(d.get("remove_ops")).get(name) == str(op_id):
            return True, 0
    return False, 0


# ---- dynamic command -> category mappings (Owner /logmap) ----
def _as_dict(value):
    """Dict or {} (a missing / null / wrong-typed field must never raise)."""
    return dict(value) if isinstance(value, dict) else {}


def _as_list(value):
    return list(value) if isinstance(value, (list, tuple)) else []


@retry_read
def get_command_mappings():
    """
    {command: category}; always a dict. Returns {} when the `command_mappings` document does not exist
    (or is malformed). Commands are stored lowercase without the leading slash.
    """
    d = col(BOT_SETTINGS).find_one({"_id": "command_mappings"})
    return _as_dict(d.get("map")) if isinstance(d, dict) else {}


@retry_write
def set_command_mapping_op(command, category, op_id=None):
    """
    Map `command` to `category` (overwrites). Returns (previous_category_or_None, replayed).
    replayed is True when the SAME request (`op_id`) already wrote this mapping (a retry after a lost response).
    `command` must already be validated (lowercase letters/digits/underscore: it becomes a field name).
    """
    to_set = {f"map.{command}": category}
    if op_id:
        to_set[f"map_ops.{command}"] = str(op_id)
    before = col(BOT_SETTINGS).find_one_and_update(
        {"_id": "command_mappings"}, {"$set": to_set, "$unset": {f"unmap_ops.{command}": ""}},
        upsert=True, return_document=ReturnDocument.BEFORE)
    before = before or {}
    previous = _as_dict(before.get("map")).get(command)
    replayed = bool(op_id) and previous == category and _as_dict(before.get("map_ops")).get(command) == str(op_id)
    return previous, replayed


def set_command_mapping(command, category):
    """Map `command` to `category` (overwrites an existing mapping). Returns the PREVIOUS category or None."""
    return set_command_mapping_op(command, category)[0]


@retry_write
def remove_command_mapping(command, op_id=None):
    """Delete the mapping for one command. True if it existed (or if this same request already removed it)."""
    update = {"$unset": {f"map.{command}": "", f"map_ops.{command}": ""}}
    if op_id:
        update["$set"] = {f"unmap_ops.{command}": str(op_id)}
    res = col(BOT_SETTINGS).update_one({"_id": "command_mappings", f"map.{command}": {"$exists": True}}, update)
    if res.modified_count == 1:
        return True
    if op_id:
        d = col(BOT_SETTINGS).find_one({"_id": "command_mappings"}) or {}
        return _as_dict(d.get("unmap_ops")).get(command) == str(op_id)
    return False


@retry_write
def remove_mappings_for_category(category):
    """Drop every mapping that points at `category` (used when a custom category is deleted). Returns the count."""
    stale = [c for c, v in get_command_mappings().items() if v == category]
    if stale:
        col(BOT_SETTINGS).update_one({"_id": "command_mappings"}, {"$unset": {f"map.{c}": "" for c in stale}})
    return len(stale)


@retry_read
def get_all_categories():
    """{'custom': {name: description}, 'disabled': [names]}; built-in categories are defined in bot.py."""
    cfg = get_log_config()
    return {"custom": cfg["custom_categories"], "disabled": cfg["disabled_categories"]}


# ---- persistent Owner approval prompts (collection `pending_log_prompts`) ----
@retry_write
def create_log_prompt(prompt_id, owner_id, action_data):
    """Store a pending approval prompt. Idempotent: a retried insert (lost response) is not an error."""
    try:
        col(PENDING_LOG_PROMPTS).insert_one({
            "_id": str(prompt_id), "owner_id": int(owner_id), "action_data": action_data,
            "created_at": datetime.now(timezone.utc),
        })
    except DuplicateKeyError:
        pass
    return str(prompt_id)


@retry_write
def pop_log_prompt(prompt_id, owner_id=None):
    """Atomically fetch AND delete a prompt (find_one_and_delete). None if missing / already handled."""
    flt = {"_id": str(prompt_id)}
    if owner_id is not None:
        flt["owner_id"] = int(owner_id)
    return col(PENDING_LOG_PROMPTS).find_one_and_delete(flt)


# ---- idempotency receipts (collection `op_receipts`, purged by a TTL index) ----
@retry_write
def receipt_put(key, result=None):
    """Remember that the operation `key` completed (first write wins; a duplicate is not an error)."""
    try:
        col(OP_RECEIPTS).insert_one({"_id": str(key), "result": result or {}, "created_at": datetime.now(timezone.utc)})
    except DuplicateKeyError:
        pass


@retry_read
def receipt_get(key):
    """The stored result dict for `key`, or None when no such operation completed."""
    d = col(OP_RECEIPTS).find_one({"_id": str(key)})
    return None if d is None else (d.get("result") or {})


@retry_read
def get_rules():
    """The bot usage rules document, or None when no rules are set."""
    d = col(BOT_SETTINGS).find_one({"_id": "rules"})
    return d if d and (d.get("text") or "").strip() else None


@retry_write
def set_rules(text, updated_by, updated_at):
    col(BOT_SETTINGS).update_one(
        {"_id": "rules"},
        {"$set": {"text": text, "updated_by": int(updated_by), "updated_at": updated_at}},
        upsert=True,
    )


@retry_write
def clear_rules():
    """Remove all rules. True if any were set."""
    return col(BOT_SETTINGS).delete_one({"_id": "rules"}).deleted_count == 1


# --------------------------------------------------------------------------
# Character spawn cooldowns (collection `character_spawn_cooldowns`;
# migrated from character_spawn_cooldowns.json)
#   _id: character code (str)
#   character_code: same as _id
#   last_spawned_at: ISO-8601 string, stored exactly as given
# `_id` is already uniquely indexed, so no extra index is needed.
# --------------------------------------------------------------------------
CHARACTER_SPAWN_COOLDOWNS = "character_spawn_cooldowns"


def _parse_stamp(value):
    """ISO string -> datetime, or None if it cannot be parsed."""
    try:
        return datetime.fromisoformat(str(value))
    except (TypeError, ValueError):
        return None


@retry_read
def get_character_spawn_cooldown(code):
    """last_spawned_at ISO string for one character, or None if it has no entry."""
    d = col(CHARACTER_SPAWN_COOLDOWNS).find_one({"_id": str(code)})
    return d.get("last_spawned_at") if d else None


@retry_read
def load_character_spawn_cooldowns():
    """{character_code: last_spawned_at ISO string} for every stored entry."""
    return {str(d["_id"]): d.get("last_spawned_at")
            for d in col(CHARACTER_SPAWN_COOLDOWNS).find({})}


@retry_write
def set_character_spawn_cooldown(code, stamp=None):
    """Create or overwrite the cooldown start for a character. stamp defaults to now (local tz-aware ISO)."""
    code = str(code)
    stamp = str(stamp) if stamp else datetime.now().astimezone().isoformat(timespec="seconds")
    col(CHARACTER_SPAWN_COOLDOWNS).update_one(
        {"_id": code}, {"$set": {"character_code": code, "last_spawned_at": stamp}}, upsert=True)
    return stamp


@retry_write
def clear_character_spawn_cooldown(code):
    """Remove one character's cooldown. True if an entry existed."""
    return col(CHARACTER_SPAWN_COOLDOWNS).delete_one({"_id": str(code)}).deleted_count == 1


@retry_write
def clear_all_character_spawn_cooldowns():
    """Remove every cooldown entry. Returns how many were deleted."""
    return col(CHARACTER_SPAWN_COOLDOWNS).delete_many({}).deleted_count


def get_active_character_cooldowns(duration_seconds, now=None):
    """
    {character_code: seconds_remaining} for entries whose cooldown (last_spawned_at + duration_seconds)
    has not yet ended. Entries with an unparseable timestamp are skipped. Naive timestamps are
    read as local time.
    """
    now = now or datetime.now().astimezone()
    if now.tzinfo is None:
        now = now.astimezone()
    out = {}
    for code, stamp in load_character_spawn_cooldowns().items():
        dt = _parse_stamp(stamp)
        if dt is None:
            continue
        if dt.tzinfo is None:
            dt = dt.astimezone()
        remaining = (dt + timedelta(seconds=float(duration_seconds)) - now).total_seconds()
        if remaining > 0:
            out[code] = remaining
    return out


# --------------------------------------------------------------------------
# Step 3: spawn history (collection `spawn_history_v2`, integer _id == old id)
# --------------------------------------------------------------------------
SH = "spawn_history_v2"
RANDOM_SPAWN = ["auto_spawn", "manual_spawn"]
_RANDOM = {"$in": RANDOM_SPAWN}
# Spawns that count toward daily totals / high-rank gaps: random spawns plus Owner /callcharacter.
COUNTED_SPAWN = RANDOM_SPAWN + ["owner_callchar"]
_COUNTED = {"$in": COUNTED_SPAWN}


@retry_write
def sh_insert(chat_id, code, rarity, spawned_by, stamp):
    return insert_with_id(SH, {
        "chat_id": int(chat_id), "character_code": str(code), "rarity": rarity,
        "spawned_by": spawned_by, "spawned_at": stamp, "caught_by": None,
        "caught_at": None, "expiry_notified_at": None,
    })


@retry_write
def sh_mark_expiry_notified(history_id, stamp):
    return col(SH).update_one({"_id": int(history_id), "expiry_notified_at": None},
                              {"$set": {"expiry_notified_at": stamp}}).modified_count == 1


@retry_write
def sh_mark_expiry_notified_many(history_ids, stamp):
    """Mark several 'character expired' notices as done without sending them (old rows / groups that are gone)."""
    ids = [int(h) for h in history_ids]
    if not ids:
        return 0
    return col(SH).update_many({"_id": {"$in": ids}, "expiry_notified_at": None},
                               {"$set": {"expiry_notified_at": stamp}}).modified_count


@retry_write
def sh_mark_chat_expiry_notified(chat_id, stamp):
    """All unannounced expiry notices of one (dead / migrated) chat are done."""
    return col(SH).update_many({"chat_id": int(chat_id), "caught_by": None, "expiry_notified_at": None},
                               {"$set": {"expiry_notified_at": stamp}}).modified_count


@retry_read
def sh_is_expiry_notified(history_id):
    d = col(SH).find_one({"_id": int(history_id)}, {"expiry_notified_at": 1})
    return bool(d and d.get("expiry_notified_at"))


@retry_write
def sh_mark_caught(history_id, user_id, stamp):
    col(SH).update_one({"_id": int(history_id)}, {"$set": {"caught_by": int(user_id), "caught_at": stamp}})


@retry_write
def sh_claim_catch(history_id, user_id, stamp):
    """Atomic: succeeds only if nobody caught this spawn yet."""
    return col(SH).update_one({"_id": int(history_id), "caught_by": None},
                              {"$set": {"caught_by": int(user_id), "caught_at": stamp}}).modified_count == 1


@retry_write
def sh_release_catch(history_id):
    col(SH).update_one({"_id": int(history_id)}, {"$set": {"caught_by": None, "caught_at": None}})


@retry_write
def sh_delete_uncaught(history_id):
    return col(SH).delete_one({"_id": int(history_id), "caught_by": None}).deleted_count == 1


@retry_read
def sh_pending_expiry_rows():
    """[(id, chat_id, code, rarity, spawned_at, spawned_by)] uncaught and not yet announced as expired."""
    cur = col(SH).find({"caught_by": None, "expiry_notified_at": None}).sort("_id", ASCENDING)
    return [(d["_id"], d["chat_id"], d["character_code"], d.get("rarity"), d.get("spawned_at"), d.get("spawned_by"))
            for d in cur]


@retry_read
def sh_recent_codes(cutoff):
    return {str(d) for d in col(SH).distinct("character_code", {"spawned_by": _COUNTED, "spawned_at": {"$gte": cutoff}})}


@retry_read
def sh_code_counts():
    return {str(d["_id"]): int(d["n"]) for d in col(SH).aggregate([
        {"$match": {"spawned_by": _RANDOM}}, {"$group": {"_id": "$character_code", "n": {"$sum": 1}}}])}


@retry_read
def sh_caught_random_rows(date_floor):
    """[(character_code, caught_at, chat_id)] caught random spawns with caught_at >= date_floor (YYYY-MM-DD)."""
    cur = col(SH).find({"spawned_by": _RANDOM, "caught_by": {"$ne": None}, "caught_at": {"$gte": date_floor}},
                       {"character_code": 1, "caught_at": 1, "chat_id": 1})
    return [(d["character_code"], d["caught_at"], d["chat_id"]) for d in cur]


@retry_read
def sh_rarity_rows(date_floor, rarities):
    cur = col(SH).find({"spawned_by": _COUNTED, "rarity": {"$in": list(rarities)}, "spawned_at": {"$gte": date_floor}},
                       {"rarity": 1, "spawned_at": 1})
    return [(d["rarity"], d["spawned_at"]) for d in cur]


@retry_read
def sh_last_spawn(rarities, since):
    """Most recent random spawn (by spawned_at, then id) of the given rarities since `since`."""
    d = col(SH).find_one({"spawned_by": _COUNTED, "rarity": {"$in": list(rarities)}, "spawned_at": {"$gte": since}},
                         {"spawned_at": 1}, sort=[("spawned_at", DESCENDING), ("_id", DESCENDING)])
    return (d["_id"], d["spawned_at"]) if d else None


@retry_read
def sh_count_random_since(since):
    # Gap counting: only spawns that were successfully caught (added to a collection) count.
    return col(SH).count_documents({"spawned_by": _COUNTED, "caught_by": {"$ne": None}, "spawned_at": {"$gte": since}})


@retry_read
def sh_count_random_after(since, after_at, exclude_id):
    # Gap counting: only caught spawns made after the last high-rank spawn count (the high-rank spawn itself
    # resets the gap whether or not it was caught).
    return col(SH).count_documents({"spawned_by": _COUNTED, "caught_by": {"$ne": None},
                                    "spawned_at": {"$gte": since, "$gt": after_at},
                                    "_id": {"$ne": int(exclude_id)}})


@retry_read
def sh_chat_recent(chat_id, limit=10):
    """[(character_code, rarity, last_spawned_at)] newest first, one row per character (cooldown view)."""
    best = {}
    for d in col(SH).find({"chat_id": int(chat_id), "spawned_by": _COUNTED}, {"character_code": 1, "rarity": 1, "spawned_at": 1}):
        code = d["character_code"]
        if code not in best or (d.get("spawned_at") or "") >= (best[code][2] or ""):
            best[code] = (code, d.get("rarity"), d.get("spawned_at"))
    return sorted(best.values(), key=lambda r: r[2] or "", reverse=True)[:int(limit)]


@retry_read
def sh_latest(limit):
    cur = col(SH).find({}).sort("_id", DESCENDING).limit(int(limit))
    return [(d["character_code"], d.get("rarity"), d.get("spawned_by"), d.get("spawned_at"),
             d.get("caught_by"), d.get("caught_at")) for d in cur]


@retry_read
def sh_day_rows(day_key):
    """[(chat_id, rarity, spawned_at)] for every spawn whose spawned_at date == day_key, oldest first."""
    cur = col(SH).find({"spawned_at": {"$regex": "^" + re.escape(day_key)}}, {"chat_id": 1, "rarity": 1, "spawned_at": 1}).sort("_id", ASCENDING)
    return [(d["chat_id"], d.get("rarity"), d["spawned_at"]) for d in cur]


@retry_read
def sh_day_rarity_counts(day_key):
    return {d["_id"]: int(d["n"]) for d in col(SH).aggregate([
        {"$match": {"spawned_by": _COUNTED, "spawned_at": {"$regex": "^" + re.escape(day_key)}}},
        {"$group": {"_id": "$rarity", "n": {"$sum": 1}}}])}


@retry_read
def sh_uncaught_random_counts(cutoff):
    """[(chat_id, code, n)] random spawns not caught yet and spawned at/after cutoff."""
    return [(d["_id"]["c"], d["_id"]["k"], int(d["n"])) for d in col(SH).aggregate([
        {"$match": {"spawned_by": _RANDOM, "caught_by": None, "caught_at": None, "spawned_at": {"$gte": cutoff}}},
        {"$group": {"_id": {"c": "$chat_id", "k": "$character_code"}, "n": {"$sum": 1}}}])]


@retry_read
def sh_spawn_row(history_id):
    """(spawned_at, caught_by) for one spawn, or None."""
    d = col(SH).find_one({"_id": int(history_id)}, {"spawned_at": 1, "caught_by": 1})
    return (d.get("spawned_at"), d.get("caught_by")) if d else None


# ==========================================================================
# ANIME CODE RANGES (collection `anime_ranges`)
# Every anime owns a reserved block of 4-digit character codes (like a serial): Naruto 0001-0200, Bleach 0201-0400.
# Document: {anime_name, start_code, end_code, anime_key (case-folded name, unique), updated_at (IST), updated_by}.
# Typed commands (/range, /freecode, /nextcode, /setrange, /delrange) and the Range Panel buttons in bot.py call
# THESE functions, so both always show identical results. A code counts as "used" when ANY character owns it.
# ==========================================================================
import bisect
import difflib
import hashlib

ANIME_RANGES = "anime_ranges"
CODE_MIN = 1
CODE_MAX = 9999
_IST = timezone(timedelta(hours=5, minutes=30))          # Asia/Kolkata


def fmt_code(n):
    """4-digit code with leading zeros: 7 -> '0007'."""
    return f"{int(n):04d}"


def parse_code(value):
    """'0001' / '1' / ' 0200 ' -> int 1..9999, or None when it is not a valid code."""
    text = str(value or "").strip()
    if not text.isdigit() or len(text) > 4:
        return None
    n = int(text)
    return n if CODE_MIN <= n <= CODE_MAX else None


def anime_key(name):
    """Matching key: case-insensitive, extra spaces ignored."""
    return " ".join(str(name or "").split()).casefold()


def anime_hash(name):
    """Short stable id of an anime name for button callback data (names are too long for it)."""
    return hashlib.sha1(anime_key(name).encode("utf-8")).hexdigest()[:10]


def compress_codes(codes):
    """Sorted ints -> [(first, last), ...] runs: [71, 72, 73, 75] -> [(71, 73), (75, 75)]."""
    runs = []
    for c in sorted(set(int(x) for x in codes)):
        if runs and c == runs[-1][1] + 1:
            runs[-1][1] = c
        else:
            runs.append([c, c])
    return [(a, b) for a, b in runs]


def format_runs(runs):
    """[(71, 74), (76, 200)] -> '0071-0074, 0076-0200' (a single code is shown alone)."""
    return ", ".join(fmt_code(a) if a == b else f"{fmt_code(a)}-{fmt_code(b)}" for a, b in runs)


def _range_row(d):
    return {"anime_name": d.get("anime_name"), "start_code": int(d.get("start_code")), "end_code": int(d.get("end_code")),
            "anime_key": d.get("anime_key") or anime_key(d.get("anime_name"))}


@retry_read
def get_ranges():
    """Every range, ordered by start code: [{anime_name, start_code, end_code, anime_key}]."""
    rows = [_range_row(d) for d in col(ANIME_RANGES).find({})]
    rows.sort(key=lambda r: (r["start_code"], r["anime_key"]))
    return rows


@retry_read
def get_range(anime):
    """The range of one anime (exact name, case-insensitive), or None."""
    d = col(ANIME_RANGES).find_one({"anime_key": anime_key(anime)})
    return _range_row(d) if d else None


def _numeric_code(d):
    """Integer value of a character's code, or None when the code is not numeric."""
    code = str(d.get("code") or "")
    if code.isdigit():
        return int(code)
    try:
        n = int(d.get("code_int") or 0)
    except (TypeError, ValueError):
        n = 0
    return n or None


def _used_codes():
    """Sorted list of every numeric code currently owned by a character (normal or evolution)."""
    out = []
    for d in _chars():
        n = _numeric_code(d)
        if n is not None:
            out.append(n)
    return sorted(set(out))


def canonical_anime_name(name):
    """The spelling already used by characters for this anime (so 'naruto' becomes 'Naruto'); else the cleaned input."""
    key = anime_key(name)
    for d in _chars():
        a = d.get("anime")
        if a and anime_key(a) == key:
            return " ".join(str(a).split())
    return " ".join(str(name or "").split())


def all_anime_names():
    """Every known anime (from ranges AND characters), spelling of its range first, sorted A-Z."""
    names = {}
    for d in _chars():
        a = " ".join(str(d.get("anime") or "").split())
        if a:
            names.setdefault(anime_key(a), a)
    for r in get_ranges():
        names[r["anime_key"]] = r["anime_name"]
    return sorted(names.values(), key=lambda n: n.casefold())


def anime_by_hash(h):
    """Anime name for a callback hash (see anime_hash), or None."""
    for name in all_anime_names():
        if anime_hash(name) == h:
            return name
    return None


def resolve_anime(query):
    """
    Shared name matching for every range command and button (case-insensitive, extra spaces ignored, multi-word ok).
      {"status": "exact"|"one", "name": ...}   exact match, or exactly one partial match
      {"status": "multi", "names": [...]}      several partial matches (shown as buttons)
      {"status": "none", "closest": [...]}     nothing found: the 3 closest names
    """
    key = anime_key(query)
    names = all_anime_names()
    if not key or not names:
        return {"status": "none", "closest": names[:3]}
    by_key = {anime_key(n): n for n in names}
    if key in by_key:
        return {"status": "exact", "name": by_key[key]}
    partial = [n for n in names if key in anime_key(n)]
    if len(partial) == 1:
        return {"status": "one", "name": partial[0]}
    if len(partial) > 1:
        return {"status": "multi", "names": partial}
    close_keys = difflib.get_close_matches(key, list(by_key), n=3, cutoff=0.0)
    return {"status": "none", "closest": [by_key[k] for k in close_keys]}


def find_overlap(anime, start, end):
    """The OTHER anime whose range overlaps start-end: {anime_name, start_code, end_code}, or None."""
    key = anime_key(anime)
    for r in get_ranges():
        if r["anime_key"] != key and not (end < r["start_code"] or start > r["end_code"]):
            return r
    return None


@retry_write
def set_range(anime, start, end, user_id=None):
    """
    Create or update an anime's range. Returns
      {"ok": True, "created": bool, "range": {...}, "previous": {...}|None}
      {"ok": False, "error": "invalid"|"overlap", "message": text, "overlap": {...}|None}
    """
    name = canonical_anime_name(anime)
    if not name:
        return {"ok": False, "error": "invalid", "message": "Anime name is required.", "overlap": None}
    s, e = parse_code(start), parse_code(end)
    if s is None or e is None:
        return {"ok": False, "error": "invalid", "message": f"Codes must be numbers from {fmt_code(CODE_MIN)} to {fmt_code(CODE_MAX)}.", "overlap": None}
    if s > e:
        return {"ok": False, "error": "invalid", "message": "The starting code must not be bigger than the ending code.", "overlap": None}
    other = find_overlap(name, s, e)
    if other:
        return {"ok": False, "error": "overlap", "overlap": other,
                "message": f"{name} ({fmt_code(s)}-{fmt_code(e)}) overlaps with {other['anime_name']} "
                           f"({fmt_code(other['start_code'])}-{fmt_code(other['end_code'])})."}
    key = anime_key(name)
    previous = get_range(name)
    stamp = datetime.now(_IST).replace(tzinfo=None).isoformat(timespec="seconds")
    col(ANIME_RANGES).update_one(
        {"anime_key": key},
        {"$set": {"anime_name": name, "anime_key": key, "start_code": s, "end_code": e,
                  "updated_at": stamp, "updated_by": int(user_id) if user_id is not None else None},
         "$setOnInsert": {"created_at": stamp}},
        upsert=True)
    return {"ok": True, "created": previous is None, "previous": previous,
            "range": {"anime_name": name, "start_code": s, "end_code": e, "anime_key": key}}


@retry_write
def delete_range(anime):
    """Delete an anime's range (characters are not touched). True when a range was deleted."""
    return col(ANIME_RANGES).delete_one({"anime_key": anime_key(anime)}).deleted_count > 0


def _status_from(r, used_sorted):
    s, e = r["start_code"], r["end_code"]
    lo, hi = bisect.bisect_left(used_sorted, s), bisect.bisect_right(used_sorted, e)
    used = used_sorted[lo:hi]
    total = e - s + 1
    used_set = set(used)
    free_runs, cur = [], None
    for c in range(s, e + 1):
        if c in used_set:
            if cur:
                free_runs.append((cur, c - 1))
                cur = None
        elif cur is None:
            cur = c
    if cur:
        free_runs.append((cur, e))
    return {"name": r["anime_name"], "start": s, "end": e, "total": total,
            "used": used, "used_count": len(used), "free_count": total - len(used),
            "used_runs": compress_codes(used), "free_runs": free_runs}


def range_status(anime):
    """Used/free numbers of one anime's range, or None when it has no range. Keys: name, start, end, total, used,
    used_count, free_count, used_runs, free_runs (runs are [(first, last)])."""
    r = get_range(anime)
    return _status_from(r, _used_codes()) if r else None


def all_range_status():
    """range_status() of every anime that has a range, ordered by start code (one character scan for all)."""
    used = _used_codes()
    return [_status_from(r, used) for r in get_ranges()]


def next_free_codes(anime, count=1):
    """
    {"name", "start", "end", "codes": [next free codes], "free_count", "full": bool}, or None without a range.
    """
    st = range_status(anime)
    if st is None:
        return None
    codes = []
    for a, b in st["free_runs"]:
        for c in range(a, b + 1):
            codes.append(c)
            if len(codes) >= max(1, int(count)):
                break
        if len(codes) >= max(1, int(count)):
            break
    return {"name": st["name"], "start": st["start"], "end": st["end"], "codes": codes,
            "free_count": st["free_count"], "full": not codes}


def code_owner_name(code):
    """Name of the character that uses this code, or None."""
    row = get_character_by_code(str(code))
    return row[1] if row else None


def check_code_for_anime(anime, code, exclude_code=None):
    """
    Add/edit validation of a 4-digit code against the anime's range.
      {"status": "no_range"}                                  anime has no range (nothing is enforced)
      {"status": "ok", ...}                                   inside the range and free
      {"status": "outside", "name", "start", "end"}           outside the range
      {"status": "taken", "name", "start", "end", "owner", "suggestions": [next 5 free codes]}
    `exclude_code`: a character's own current code (editing) never counts as taken.
    """
    r = get_range(anime) if anime_key(anime) else None
    if r is None:
        return {"status": "no_range"}
    n = parse_code(code)
    base = {"name": r["anime_name"], "start": r["start_code"], "end": r["end_code"]}
    if n is None or not (r["start_code"] <= n <= r["end_code"]):
        return {"status": "outside", **base}
    if exclude_code is not None and str(exclude_code) == fmt_code(n):
        return {"status": "ok", **base}
    owner = code_owner_name(fmt_code(n))
    if owner is not None:
        nxt = next_free_codes(r["anime_name"], 5)
        return {"status": "taken", **base, "owner": owner, "suggestions": nxt["codes"] if nxt else []}
    return {"status": "ok", **base}


def code_range_report():
    """
    REPORT ONLY (changes nothing): characters whose code is outside their anime's range.
    {"total": int, "with_range": int,
     "outside": [{code, name, anime, start, end}],            anime has a range but the code is outside it
     "no_range": {anime: {"count", "min", "max"}},             characters of anime that have no range yet
     "no_anime": [{code, name}],                               characters with no anime set
     "bad_code": [{code, name, anime}]}                        non-numeric / out-of-format codes
    """
    ranges = {r["anime_key"]: r for r in get_ranges()}
    out = {"total": 0, "with_range": 0, "outside": [], "no_range": {}, "no_anime": [], "bad_code": []}
    for d in _chars():
        out["total"] += 1
        code, name, anime = str(d.get("code") or ""), d.get("name"), " ".join(str(d.get("anime") or "").split())
        n = _numeric_code(d)
        if n is None:
            out["bad_code"].append({"code": code, "name": name, "anime": anime})
            continue
        if not anime:
            out["no_anime"].append({"code": code, "name": name})
            continue
        r = ranges.get(anime_key(anime))
        if r is None:
            info = out["no_range"].setdefault(anime, {"count": 0, "min": n, "max": n})
            info["count"] += 1
            info["min"], info["max"] = min(info["min"], n), max(info["max"], n)
            continue
        out["with_range"] += 1
        if not (r["start_code"] <= n <= r["end_code"]):
            out["outside"].append({"code": code, "name": name, "anime": r["anime_name"],
                                   "start": r["start_code"], "end": r["end_code"]})
    return out


def outside_count(anime):
    """How many existing characters of this anime have a code outside the anime's range (0 without a range)."""
    r = get_range(anime)
    if r is None:
        return 0
    key = anime_key(anime)
    total = 0
    for d in _chars():
        if anime_key(d.get("anime")) != key:
            continue
        n = _numeric_code(d)
        if n is None or not (r["start_code"] <= n <= r["end_code"]):
            total += 1
    return total


# --------------------------------------------------------------------------
# Changing character codes: one character (/editcode) or a whole anime when its range moves (Change codes button)
# --------------------------------------------------------------------------
def change_character_code_tx(session, old_code, new_code):
    """Change ONE normal character's code inside a transaction. Everything that points at the code follows
    (collections, favorites, Evolution recipes - see update_character_tx - and the shop). False when it does not exist
    or is an Evolution character (those are edited with /editevo)."""
    old_code, new_code = str(old_code), str(new_code)
    doc = col(CHARACTERS).find_one({"code": old_code, "char_type": {"$ne": CHAR_TYPE_EVOLUTION}}, session=session)
    if not doc:
        return False
    if not update_character_tx(session, old_code, new_code, doc.get("name"), doc.get("anime"), doc.get("rarity"),
                               doc.get("worth") or 0):
        return False
    if new_code != old_code:
        col("shop_v3").update_many({"character_code": old_code}, {"$set": {"character_code": new_code}}, session=session)
    return True


def change_character_code(old_code, new_code):
    """/editcode: change one normal character's code (all or nothing). True when changed."""
    try:
        return run_transaction(lambda session: change_character_code_tx(session, old_code, new_code))
    finally:
        invalidate_character_cache()


def plan_code_move(anime, old_start, old_end, new_start, new_end):
    """
    Plan for moving an anime's characters when its range changes from old_start-old_end to new_start-new_end: every
    normal character whose code is inside the OLD range keeps its position (0001 -> 5000, 0002 -> 5001 ...). Nothing is written.
      {"moves": [(old, new, name)] in a safe order, "shift": int, "evolution_left": int, "kept_outside": int, "error": text|None}
    `error` is set (and nothing may be moved) when a new code would leave the new range or is used by another character.
    """
    key = anime_key(anime)
    shift = int(new_start) - int(old_start)
    plan = {"moves": [], "shift": shift, "evolution_left": 0, "kept_outside": 0, "error": None}
    if shift == 0:
        return plan
    moving, others = {}, {}
    for d in _chars():
        n = _numeric_code(d)
        if n is None:
            continue
        mine = anime_key(d.get("anime")) == key
        is_evo = d.get("char_type") == CHAR_TYPE_EVOLUTION
        if mine and old_start <= n <= old_end:
            if is_evo:
                plan["evolution_left"] += 1
                others[n] = d.get("name")
            else:
                moving[n] = d.get("name")
        else:
            others[n] = d.get("name")
            if mine and not is_evo:
                plan["kept_outside"] += 1
    if not moving:
        return plan
    too_big = [c for c in moving if not (new_start <= c + shift <= new_end)]
    if too_big:
        need = max(c + shift for c in moving)
        plan["error"] = (f"The new range {fmt_code(new_start)}-{fmt_code(new_end)} is too small: "
                         f"{len(too_big)} character(s) would need codes up to {fmt_code(need)}.")
    else:
        clash = [(c, c + shift, others[c + shift]) for c in sorted(moving) if c + shift in others]
        if clash:
            shown = ", ".join(f"{fmt_code(n)} is used by {nm}" for _o, n, nm in clash[:3])
            plan["error"] = f"{len(clash)} new code(s) are already used by other characters ({shown})."
    order = sorted(moving, reverse=shift > 0)      # moving up: highest first; moving down: lowest first (no clashes while moving)
    plan["moves"] = [(c, c + shift, moving[c]) for c in order]
    return plan


def apply_code_move(moves):
    """Run the moves of plan_code_move in ONE transaction (all or nothing). Returns how many characters moved."""
    def _work(session):
        moved = 0
        for old, new, _name in moves:
            if not change_character_code_tx(session, fmt_code(old), fmt_code(new)):
                raise RuntimeError(f"Character {fmt_code(old)} could not be moved")
            moved += 1
        return moved
    try:
        return run_transaction(_work)
    finally:
        invalidate_character_cache()


# ==========================================================================
# FILLING RANGES AND SHIFTING RANGES (renumbering many characters safely)
#   plan_fill_ranges()  -> every normal character moves INTO its anime's range (characters already inside keep their code)
#   plan_range_extend() -> a range grows; the ranges it runs into (and their characters) shift up by the amount needed
# Both only PLAN (nothing is written). The plan is saved as a "move job" and executed in small transactions:
# every step is valid on its own and idempotent, so a stop halfway never breaks anything - the job just continues.
# ==========================================================================
import uuid

CODE_JOBS = "code_move_jobs"


def _order_moves(items, used_codes):
    """
    items: [{"id", "old", "new", "name"}] (old/new are ints, one character each, unique new codes).
    Returns the steps in an order where every step's target code is free at that moment. A cycle (A->B, B->A) is broken
    with one temporary pivot code that nobody uses. Raises ValueError when no pivot is available.
    """
    pending = {it["old"]: dict(it) for it in items if it["old"] != it["new"]}
    occupied = set(used_codes)
    steps = []
    while pending:
        progressed = False
        for old in sorted(pending):
            it = pending.get(old)
            if it is None:
                continue
            if it["new"] not in occupied:
                steps.append(dict(it))
                occupied.discard(old)
                occupied.add(it["new"])
                del pending[old]
                progressed = True
        if progressed:
            continue
        targets = {it["new"] for it in pending.values()}
        pivot = next((c for c in range(CODE_MAX, CODE_MIN - 1, -1) if c not in occupied and c not in targets), None)
        if pivot is None:
            raise ValueError("No free code is available to resolve the renumbering.")
        old = min(pending)
        it = pending.pop(old)
        steps.append({**it, "new": pivot})
        occupied.discard(old)
        occupied.add(pivot)
        pending[pivot] = {**it, "old": pivot}
    return steps


def _rows_for_planning():
    rows = []
    for d in _chars():
        rows.append({"id": d["_id"], "code": _numeric_code(d), "name": d.get("name"),
                     "akey": anime_key(d.get("anime")), "evo": d.get("char_type") == CHAR_TYPE_EVOLUTION})
    return rows


def plan_fill_ranges(spawned=None, only_anime=None):
    """
    Plan that moves every NORMAL character into the range of its anime. Characters already inside keep their code; the
    ones outside take the lowest free codes of the range, in the order of their current codes. Evolution characters,
    characters of anime without a range, and characters spawned right now (`spawned` = codes) stay where they are.
    An anime whose characters do not all fit is skipped (extend its range first). `only_anime` limits the moves to one anime.
    Returns {"per_anime": [{name,start,end,total_slots,inside,moving,need,slots,status}], "steps": [...], "moving": int,
             "inside": int, "skipped": [names], "deferred": int, "evolution": int, "unranged": {anime: count}, "samples": [...]}.
    """
    spawned = {int(c) for c in (spawned or []) if str(c).isdigit()}
    ranges = get_ranges()
    rmap = {r["anime_key"]: r for r in ranges}
    only_key = anime_key(only_anime) if only_anime else None
    rows = _rows_for_planning()
    numeric = [r for r in rows if r["code"] is not None]
    skipped = set()
    while True:
        out_by, in_by = {}, {}
        for r in numeric:
            rg = rmap.get(r["akey"])
            if rg is None or r["evo"] or r["akey"] in skipped or (only_key and r["akey"] != only_key):
                continue
            if rg["start_code"] <= r["code"] <= rg["end_code"]:
                in_by.setdefault(r["akey"], []).append(r)
            elif r["code"] not in spawned:
                out_by.setdefault(r["akey"], []).append(r)
        moving_ids = {id(r) for lst in out_by.values() for r in lst}
        stay_codes = {r["code"] for r in numeric if id(r) not in moving_ids}
        slots_by, newly = {}, False
        for rg in ranges:
            k = rg["anime_key"]
            outs = out_by.get(k, [])
            if not outs:
                continue
            slots = [c for c in range(rg["start_code"], rg["end_code"] + 1) if c not in stay_codes]
            slots_by[k] = slots
            if len(outs) > len(slots):
                skipped.add(k)
                newly = True
        if not newly:
            break
    items, per_anime = [], []
    unranged = {}
    for r in rows:
        if r["akey"] and r["akey"] not in rmap and not r["evo"] and r["code"] is not None:
            unranged[r["akey"]] = unranged.get(r["akey"], 0) + 1
    names = {}
    for d in _chars():
        a = " ".join(str(d.get("anime") or "").split())
        if a:
            names.setdefault(anime_key(a), a)
    for rg in ranges:
        k = rg["anime_key"]
        if only_key and k != only_key:
            continue
        outs = sorted(out_by.get(k, []), key=lambda r: (r["code"], str(r["name"])))
        slots = slots_by.get(k, [])
        inside = len(in_by.get(k, []))
        total_chars = sum(1 for r in numeric if r["akey"] == k and not r["evo"])
        entry = {"name": rg["anime_name"], "start": rg["start_code"], "end": rg["end_code"], "inside": inside,
                 "moving": 0, "need": 0, "slots": 0, "status": "ok"}
        if k in skipped:
            outside_all = [r for r in numeric if r["akey"] == k and not r["evo"]
                           and not (rg["start_code"] <= r["code"] <= rg["end_code"]) and r["code"] not in spawned]
            stay2 = {r["code"] for r in numeric if r["akey"] != k or r["evo"] or r["code"] in spawned
                     or (rg["start_code"] <= r["code"] <= rg["end_code"])}
            free2 = [c for c in range(rg["start_code"], rg["end_code"] + 1) if c not in stay2]
            entry.update(status="too_small", need=len(outside_all), slots=len(free2))
        else:
            for r, c in zip(outs, slots):
                items.append({"id": r["id"], "old": r["code"], "new": c, "name": r["name"]})
            entry.update(moving=len(outs), slots=len(slots), need=len(outs))
            if outs:
                entry["status"] = "moves"
        entry["total"] = total_chars
        per_anime.append(entry)
    used = {r["code"] for r in numeric}
    steps = _order_moves(items, used) if items else []
    deferred = sum(1 for r in numeric if r["code"] in spawned and rmap.get(r["akey"]) is not None and not r["evo"]
                   and not (rmap[r["akey"]]["start_code"] <= r["code"] <= rmap[r["akey"]]["end_code"])
                   and (not only_key or r["akey"] == only_key))
    return {"per_anime": per_anime, "steps": steps, "moving": len(items), "inside": sum(len(v) for v in in_by.values()),
            "skipped": [e["name"] for e in per_anime if e["status"] == "too_small"], "deferred": deferred,
            "evolution": sum(1 for r in numeric if r["evo"]),
            "unranged": {names.get(k, k): n for k, n in sorted(unranged.items())},
            "samples": [(it["old"], it["new"], it["name"]) for it in sorted(items, key=lambda i: i["old"])[:5]]}


def plan_range_extend(anime, new_start, new_end, spawned=None):
    """
    Plan for growing an EXISTING range to new_start-new_end when it runs into the next ranges: every range that would
    overlap shifts up only as far as needed (gaps absorb part of it) and its characters move with it, keeping their
    position (Bleach 0301 -> 0401). All or nothing: any problem sets "error" and nothing may be moved.
    Returns {"ok": bool, "error": text|None, "shifts": [{name, old:(s,e), new:(s,e), shift, chars}], "steps": [...],
             "ranges_after": [{anime_key, anime_name, start, end}], "moving": int}.
    """
    ns, ne = parse_code(new_start), parse_code(new_end)
    key = anime_key(anime)
    cur = get_range(anime)
    plan = {"ok": False, "error": None, "shifts": [], "steps": [], "ranges_after": [], "moving": 0}
    if cur is None or ns is None or ne is None or ns > ne:
        plan["error"] = "Only an existing range can be extended."
        return plan
    spawned = {int(c) for c in (spawned or []) if str(c).isdigit()}
    others = sorted((r for r in get_ranges() if r["anime_key"] != key), key=lambda r: r["start_code"])
    limit, shifts = ne, []
    for r in others:
        if r["end_code"] < ns:
            continue
        if r["start_code"] > limit:
            break
        if r["start_code"] < ns:
            plan["error"] = (f"{r['anime_name']} ({fmt_code(r['start_code'])}-{fmt_code(r['end_code'])}) starts before the new "
                             "range, so it cannot be shifted. Extend the end of the range instead.")
            return plan
        shift = limit + 1 - r["start_code"]
        new_r = (r["start_code"] + shift, r["end_code"] + shift)
        if new_r[1] > CODE_MAX:
            plan["error"] = (f"There is no room: {r['anime_name']} would have to end at {new_r[1]}, "
                             f"but codes stop at {CODE_MAX}.")
            return plan
        shifts.append({"key": r["anime_key"], "name": r["anime_name"], "old": (r["start_code"], r["end_code"]),
                       "new": new_r, "shift": shift, "chars": 0})
        limit = new_r[1]
    rows = _rows_for_planning()
    numeric = [r for r in rows if r["code"] is not None]
    items, moving_codes = [], set()
    for sh in shifts:
        for r in numeric:
            if r["akey"] == sh["key"] and not r["evo"] and sh["old"][0] <= r["code"] <= sh["old"][1]:
                items.append({"id": r["id"], "old": r["code"], "new": r["code"] + sh["shift"], "name": r["name"]})
                moving_codes.add(r["code"])
                sh["chars"] += 1
    busy = sorted(it["old"] for it in items if it["old"] in spawned)
    if busy:
        plan["error"] = ("These characters are spawned in a group right now: " + ", ".join(fmt_code(c) for c in busy[:10]) +
                         ". Try again in a minute.")
        return plan
    occupant = {r["code"]: r["name"] for r in numeric if r["code"] not in moving_codes}
    clash = [(it["new"], occupant[it["new"]]) for it in items if it["new"] in occupant]
    if clash:
        shown = ", ".join(f"{fmt_code(c)} is used by {nm}" for c, nm in clash[:3])
        plan["error"] = (f"{len(clash)} new code(s) are used by characters that cannot move here ({shown}). "
                         "Run /fillranges first, or move them with /editcode.")
        return plan
    try:
        plan["steps"] = _order_moves(items, {r["code"] for r in numeric})
    except ValueError as exc:
        plan["error"] = str(exc)
        return plan
    plan["ranges_after"] = [{"anime_key": key, "anime_name": cur["anime_name"], "start": ns, "end": ne}] + [
        {"anime_key": sh["key"], "anime_name": sh["name"], "start": sh["new"][0], "end": sh["new"][1]} for sh in shifts]
    plan["shifts"], plan["moving"], plan["ok"] = shifts, len(items), True
    return plan


@retry_write
def create_move_job(kind, steps, ranges_after, user_id):
    """Save a plan as a job (returns its id). Run it with run_move_job() until it reports finished."""
    stamp = datetime.now(_IST).replace(tzinfo=None).isoformat(timespec="seconds")
    job_id = uuid.uuid4().hex[:16]
    before = [{"anime_key": r["anime_key"], "anime_name": r["anime_name"], "start": r["start_code"], "end": r["end_code"]}
              for r in get_ranges()]
    col(CODE_JOBS).insert_one({
        "_id": job_id, "kind": kind, "status": "pending", "created_at": stamp, "created_ns": time.time_ns(),
        "created_by": int(user_id) if user_id is not None else None, "done": 0, "total": len(steps),
        "steps": [{"id": s["id"], "old": int(s["old"]), "new": int(s["new"]), "name": s.get("name")} for s in steps],
        "ranges_after": list(ranges_after or []), "ranges_before": before})
    return job_id


def get_move_job(job_id):
    job = col(CODE_JOBS).find_one({"_id": job_id})
    return None if job is None else {"id": job["_id"], "kind": job.get("kind"), "status": job.get("status"),
                                     "done": job.get("done", 0), "total": len(job.get("steps") or [])}


def run_move_job(job_id, batch=40):
    """
    Run the next `batch` steps of a job in ONE transaction. Each step is idempotent (a character already at its new code is
    skipped) and checked (a character that is not where the plan expects it stops the job with an error). When the last step is
    done the planned range changes are saved. Returns {"done", "total", "finished"}.
    """
    job = col(CODE_JOBS).find_one({"_id": job_id})
    if job is None:
        raise KeyError("Job not found")
    steps = job.get("steps") or []
    start = int(job.get("done", 0))
    chunk = steps[start:start + max(1, int(batch))]

    def _work(session):
        for st in chunk:
            doc = col(CHARACTERS).find_one({"_id": st["id"]}, session=session)
            if not doc:
                raise RuntimeError(f"{st.get('name') or st['id']} no longer exists")
            cur, new = str(doc.get("code")), fmt_code(st["new"])
            if cur == new:
                continue
            if cur != fmt_code(st["old"]):
                raise RuntimeError(f"{doc.get('name')} is at {cur}, not at {fmt_code(st['old'])} as planned")
            if not update_character_tx(session, cur, new, doc.get("name"), doc.get("anime"), doc.get("rarity"),
                                       doc.get("worth") or 0):
                raise RuntimeError(f"{doc.get('name')} could not be changed")
            col("shop_v3").update_many({"character_code": cur}, {"$set": {"character_code": new}}, session=session)

    try:
        if chunk:
            run_transaction(_work)
    except Exception:
        col(CODE_JOBS).update_one({"_id": job_id}, {"$set": {"status": "failed"}})
        raise
    finally:
        invalidate_character_cache()
    done = start + len(chunk)
    finished = done >= len(steps)
    col(CODE_JOBS).update_one({"_id": job_id}, {"$set": {"done": done, "status": "running"}})
    if finished:
        stamp = datetime.now(_IST).replace(tzinfo=None).isoformat(timespec="seconds")
        for r in job.get("ranges_after") or []:
            col(ANIME_RANGES).update_one(
                {"anime_key": r["anime_key"]},
                {"$set": {"anime_name": r["anime_name"], "anime_key": r["anime_key"], "start_code": int(r["start"]),
                          "end_code": int(r["end"]), "updated_at": stamp}}, upsert=True)
        col(CODE_JOBS).update_one({"_id": job_id}, {"$set": {"status": "done", "finished_at": stamp}})
    return {"done": done, "total": len(steps), "finished": finished}


# --------------------------------------------------------------------------
# Undo of the last code move
# --------------------------------------------------------------------------
def get_last_move_job():
    """
    The most recent code-move job and whether it can be undone:
    {"id", "kind", "status", "done", "total", "created_at", "can_undo", "reason"} or None when no job exists.
    Only the LATEST job can be undone (an older one may overlap with what came after), only fill/extend jobs, only once.
    """
    jobs = list(col(CODE_JOBS).find({}, {"kind": 1, "status": 1, "done": 1, "total": 1, "created_at": 1, "created_ns": 1, "undone": 1}))
    if not jobs:
        return None
    j = max(jobs, key=lambda d: (int(d.get("created_ns") or 0), str(d.get("created_at") or "")))
    info = {"id": j["_id"], "kind": j.get("kind"), "status": j.get("status"), "done": int(j.get("done", 0)),
            "total": int(j.get("total", 0)), "created_at": j.get("created_at"), "can_undo": True, "reason": None}
    if j.get("kind") == "undo":
        info.update(can_undo=False, reason="The last code move was already an undo.")
    elif j.get("undone"):
        info.update(can_undo=False, reason="The last code move was already undone.")
    elif info["done"] == 0 and j.get("status") != "done":
        info.update(can_undo=False, reason="The last code move did not change any character.")
    return info


@retry_write
def create_undo_job(job_id, user_id):
    """
    Save a job that reverses the executed steps of `job_id` (newest first) and puts the ranges back as they were.
    Run it with run_move_job() like any other job. Returns the new job id.
    """
    job = col(CODE_JOBS).find_one({"_id": job_id})
    if job is None:
        raise KeyError("Job not found")
    done = int(job.get("done", 0))
    reverse = [{"id": st["id"], "old": st["new"], "new": st["old"], "name": st.get("name")}
               for st in reversed((job.get("steps") or [])[:done])]
    undo_id = create_move_job("undo", reverse, job.get("ranges_before") or [], user_id)
    col(CODE_JOBS).update_one({"_id": job_id}, {"$set": {"undone": True}})
    return undo_id


# --------------------------------------------------------------------------
# Full database export (the /exportdb command)
# --------------------------------------------------------------------------
def export_database(dest_dir, only=None, chunk_bytes=4 * 1024 * 1024, part_bytes=10 * 1024 * 1024):
    """
    Stream every collection of the database (or only the names in `only`) into zip files inside dest_dir. Documents are
    written as Extended JSON, one per line (<collection>.0001.jsonl, ...), so the files keep every type (dates, ids). A
    part is closed after about `part_bytes` so each file fits Telegram's upload limit; manifest.json (collections, counts,
    date) goes into the last part. Parts stay well under 15 MB because a bot can only DOWNLOAD files up to 20 MB, and
    /importdb has to read them back. Returns {"parts": [paths], "collections": {name: count}, "docs": int}.
    """
    import json
    import os
    import zipfile
    from bson import json_util

    db = get_db()
    names = sorted(n for n in db.list_collection_names() if not n.startswith("system."))
    if only:
        wanted = {str(n).casefold() for n in only}
        names = [n for n in names if n.casefold() in wanted]
    parts, counts = [], {}
    state = {"zf": None, "path": None}

    def _open_part():
        path = os.path.join(dest_dir, f"part{len(parts) + 1:03d}.zip")
        state["zf"], state["path"] = zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED), path
        parts.append(path)

    def _write(name, data):
        if state["zf"] is None:
            _open_part()
        state["zf"].writestr(name, data)
        state["zf"].fp.flush()
        if os.path.getsize(state["path"]) >= part_bytes:
            state["zf"].close()
            state["zf"] = None

    for name in names:
        chunk, size, n_chunk, total = [], 0, 0, 0
        for doc in col(name).find({}, batch_size=500):
            line = json_util.dumps(doc, json_options=json_util.CANONICAL_JSON_OPTIONS)
            chunk.append(line)
            size += len(line) + 1
            total += 1
            if size >= chunk_bytes:
                n_chunk += 1
                _write(f"{name}.{n_chunk:04d}.jsonl", "\n".join(chunk) + "\n")
                chunk, size = [], 0
        if chunk or n_chunk == 0:
            n_chunk += 1
            _write(f"{name}.{n_chunk:04d}.jsonl", ("\n".join(chunk) + "\n") if chunk else "")
        counts[name] = total
    manifest = {"database": _db_name(), "exported_at_ist": datetime.now(_IST).replace(tzinfo=None).isoformat(timespec="seconds"),
                "format": "Extended JSON v2 (canonical), one document per line", "collections": counts}
    if state["zf"] is None:
        _open_part()
    state["zf"].writestr("manifest.json", json.dumps(manifest, indent=2))
    state["zf"].close()
    return {"parts": parts, "collections": counts, "docs": sum(counts.values())}


# --------------------------------------------------------------------------
# Restore from /exportdb files (the /importdb command)
# --------------------------------------------------------------------------
_CHUNK_RE = None


def inspect_backup(zip_paths, only=None):
    """
    Read the zip parts of an export WITHOUT changing anything. Returns
      {"collections": {name: documents found}, "members": {name: [(zip, member, chunk no)]}, "manifest": dict|None,
       "problems": [text]}
    A problem is reported for: a part that is not a valid export, a missing manifest (the last part is missing), a missing
    chunk, or a collection whose document count differs from the manifest.
    """
    import json
    import re
    import zipfile
    global _CHUNK_RE
    if _CHUNK_RE is None:
        _CHUNK_RE = re.compile(r"^(.+)\.(\d{4})\.jsonl$")
    wanted = {str(n).casefold() for n in only} if only else None
    members, manifest, problems, seen = {}, None, [], set()
    for path in zip_paths:
        try:
            with zipfile.ZipFile(path) as z:
                for info in z.infolist():
                    n = info.filename
                    if "/" in n or "\\" in n or n.startswith(".."):
                        problems.append(f"Unexpected file name in a part: {n}")
                        continue
                    if n == "manifest.json":
                        manifest = json.loads(z.read(n).decode("utf-8"))
                        continue
                    m = _CHUNK_RE.match(n)
                    if not m:
                        problems.append(f"Unknown file in a part: {n}")
                        continue
                    name, no = m.group(1), int(m.group(2))
                    if name.startswith("system."):
                        continue
                    if (name, no) in seen:
                        continue                                  # the same part was sent twice
                    seen.add((name, no))
                    members.setdefault(name, []).append((path, n, no))
        except Exception as e:
            problems.append(f"A file is not a valid export part ({type(e).__name__}).")
    counts = {}
    for name, items in list(members.items()):
        if wanted is not None and name.casefold() not in wanted:
            del members[name]
            continue
        items.sort(key=lambda t: t[2])
        if [t[2] for t in items] != list(range(1, len(items) + 1)):
            problems.append(f"{name}: a chunk is missing - send all parts of the backup.")
        total = 0
        for path, member, _no in items:
            with zipfile.ZipFile(path) as z, z.open(member) as fh:
                total += sum(1 for line in fh if line.strip())
        counts[name] = total
    if manifest is None:
        problems.append("manifest.json was not found: the LAST part of the backup is missing.")
    else:
        for name, expected in (manifest.get("collections") or {}).items():
            if wanted is not None and name.casefold() not in wanted:
                continue
            if counts.get(name, 0) != expected:
                problems.append(f"{name}: the backup should hold {expected} documents, the files hold {counts.get(name, 0)}.")
    return {"collections": counts, "members": members, "manifest": manifest, "problems": problems}


def import_collection(name, members, mode):
    """
    Put ONE collection of a backup back. mode "merge" adds only the documents that are missing (existing ones are left
    untouched, so it is safe to run twice); mode "replace" first empties the collection, then fills it from the backup.
    Returns {"inserted": int, "skipped": int}. Run inspect_backup() first.
    """
    import zipfile
    from bson import json_util
    from pymongo.errors import BulkWriteError
    c = col(name)
    if mode == "replace":
        c.delete_many({})
    out = {"inserted": 0, "skipped": 0}
    batch = []

    def _flush():
        if not batch:
            return
        try:
            res = c.insert_many(batch, ordered=False)
            out["inserted"] += len(res.inserted_ids)
        except BulkWriteError as e:
            details = getattr(e, "details", None) or {}
            if any(w.get("code") != 11000 for w in (details.get("writeErrors") or [])):
                raise
            done = int(details.get("nInserted", 0))
            out["inserted"] += done
            out["skipped"] += len(batch) - done
        batch.clear()

    for path, member, _no in sorted(members, key=lambda t: t[2]):
        with zipfile.ZipFile(path) as z, z.open(member) as fh:
            for raw in fh:
                line = raw.decode("utf-8").strip()
                if not line:
                    continue
                batch.append(json_util.loads(line))
                if len(batch) >= 500:
                    _flush()
    _flush()
    invalidate_character_cache()
    return out
