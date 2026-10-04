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

import functools
import logging
import os
import re
import threading
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path

from dotenv import load_dotenv
from pymongo import ASCENDING, DESCENDING, MongoClient, ReturnDocument, UpdateOne
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


# --------------------------------------------------------------------------
# Users & coins
# --------------------------------------------------------------------------
def _user_defaults():
    return {
        "coins": 0, "last_daily": None, "guess_attempts": 0,
        "guess_secret": None, "guess_active": 0, "guess_reward_total": 0,
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
    d = col(USERS).find_one({"_id": int(user_id)}, {"guess_reward_total": 1})
    total = int((d or {}).get("guess_reward_total") or 0)
    reward = min(int(per_win), max(0, int(cap) - total))
    col(USERS).update_one(
        {"_id": int(user_id)},
        {"$inc": {"coins": reward, "guess_reward_total": reward},
         "$set": {"guess_attempts": int(attempt), "guess_secret": None, "guess_active": 0}},
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


def _row(d):
    return (d["code"], d.get("name"), d.get("anime"), d.get("rarity"), d.get("worth"), d.get("photo_file_id"))


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
    return [_row(d) for d in _chars() if d.get("rarity") == rarity and not d.get("discontinued")]


def get_character_names(codes):
    wanted = {str(c) for c in codes}
    return {d["code"]: d.get("name") for d in _chars() if d["code"] in wanted}


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


def _char_doc(code, name, anime, rarity, worth, photo, recruit_names=None):
    code = str(code)
    return {
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


@retry_write
def insert_character(code, name, anime, rarity, worth, photo=None, recruit_names=None):
    """Raises DuplicateKeyError if the code or (case-insensitive) name already exists."""
    col(CHARACTERS).insert_one(_char_doc(code, name, anime, rarity, worth, photo, recruit_names))
    invalidate_character_cache()


@retry_write
def update_character_photo(code, photo):
    res = col(CHARACTERS).update_one({"code": str(code)}, {"$set": {"photo_file_id": photo}})
    invalidate_character_cache()
    return res.matched_count == 1


def update_character(old_code, new_code, name, anime, rarity, worth, recruit_names=None):
    """
    Edit a character. If the code changes, collections and favorites are re-pointed in the
    same transaction. Raises DuplicateKeyError on code/name clash.
    """
    old_code, new_code = str(old_code), str(new_code)

    def _work(session):
        if new_code != old_code:
            col(COLLECTIONS).update_many({"character_code": old_code}, {"$set": {"character_code": new_code}}, session=session)
            col(FAVORITES).update_many({"character_code": old_code}, {"$set": {"character_code": new_code}}, session=session)
        fields = {
            "code": new_code, "code_int": int(new_code) if new_code.isdigit() else 0,
            "name": name, "name_ci": str(name).casefold() if name else None,
            "anime": anime, "rarity": rarity, "worth": int(worth),
        }
        if recruit_names is not None:
            fields["recruit_names"] = _clean_names(recruit_names)
        res = col(CHARACTERS).update_one({"code": old_code}, {"$set": fields}, session=session)
        return res.matched_count == 1

    try:
        return run_transaction(_work)
    finally:
        invalidate_character_cache()


def delete_character(code):
    """Delete a character plus every collection copy and favorite pointing at it."""
    code = str(code)

    def _work(session):
        col(COLLECTIONS).delete_many({"character_code": code}, session=session)
        col(FAVORITES).delete_many({"character_code": code}, session=session)
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
            rows.append((d["code"], d.get("name"), d.get("anime"), d.get("rarity"),
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
        ["bot_enabled", "title", "type", "username"],
    )


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
#   _id "log_channel":    {chat_id, title, username, set_by, set_at}
#   _id "log_categories": {custom: {name: description}, disabled: [category names]}
#   _id "command_mappings": {map: {command: category}}   (Owner /logmap: command -> log category)
#   _id "rules":          {text, updated_by, updated_at}
# Category switches live in their own document so unlinking/re-linking the log channel keeps them.
# --------------------------------------------------------------------------
BOT_SETTINGS = "bot_settings"
PENDING_LOG_PROMPTS = "pending_log_prompts"
OP_RECEIPTS = "op_receipts"


@retry_read
def get_log_config():
    """
    Everything the logger needs in one read (flat dict, never None):
      chat_id (None when no log channel is linked), title, username, set_by, set_at,
      custom_categories {name: description}, disabled_categories [names], command_mappings {command: category}
    """
    docs = {d["_id"]: d for d in col(BOT_SETTINGS).find(
        {"_id": {"$in": ["log_channel", "log_categories", "command_mappings"]}})}
    ch = docs.get("log_channel") if isinstance(docs.get("log_channel"), dict) else {}
    cats = docs.get("log_categories") if isinstance(docs.get("log_categories"), dict) else {}
    maps = docs.get("command_mappings") if isinstance(docs.get("command_mappings"), dict) else {}
    disabled = _as_list(cats.get("disabled"))
    for legacy in _as_list(ch.get("disabled_categories")):      # older versions stored switches on the channel doc
        if legacy not in disabled:
            disabled.append(legacy)
    return {
        "chat_id": ch.get("chat_id"), "title": ch.get("title", ""), "username": ch.get("username", ""),
        "set_by": ch.get("set_by"), "set_at": ch.get("set_at"),
        "custom_categories": _as_dict(cats.get("custom")),
        "disabled_categories": disabled,
        "command_mappings": _as_dict(maps.get("map")),
    }


@retry_write
def set_log_channel(chat_id, title, username, set_by, set_at):
    """Link (or re-link) the log channel. Category settings are stored separately and are kept."""
    col(BOT_SETTINGS).update_one(
        {"_id": "log_channel"},
        {"$set": {"chat_id": int(chat_id), "title": title or "", "username": username or "",
                  "set_by": int(set_by), "set_at": set_at}},
        upsert=True,
    )


@retry_write
def clear_log_channel():
    """Unlink the log channel (custom categories and switches are kept). True if one was linked."""
    return col(BOT_SETTINGS).delete_one({"_id": "log_channel"}).deleted_count == 1


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
    return {str(d) for d in col(SH).distinct("character_code", {"spawned_by": _RANDOM, "spawned_at": {"$gte": cutoff}})}


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
    cur = col(SH).find({"spawned_by": _RANDOM, "rarity": {"$in": list(rarities)}, "spawned_at": {"$gte": date_floor}},
                       {"rarity": 1, "spawned_at": 1})
    return [(d["rarity"], d["spawned_at"]) for d in cur]


@retry_read
def sh_last_spawn(rarities, since):
    """Most recent random spawn (by spawned_at, then id) of the given rarities since `since`."""
    d = col(SH).find_one({"spawned_by": _RANDOM, "rarity": {"$in": list(rarities)}, "spawned_at": {"$gte": since}},
                         {"spawned_at": 1}, sort=[("spawned_at", DESCENDING), ("_id", DESCENDING)])
    return (d["_id"], d["spawned_at"]) if d else None


@retry_read
def sh_count_random_since(since):
    return col(SH).count_documents({"spawned_by": _RANDOM, "spawned_at": {"$gte": since}})


@retry_read
def sh_count_random_after(since, after_at, exclude_id):
    return col(SH).count_documents({"spawned_by": _RANDOM, "spawned_at": {"$gte": since, "$gt": after_at},
                                    "_id": {"$ne": int(exclude_id)}})


@retry_read
def sh_chat_recent(chat_id, limit=10):
    """[(character_code, rarity, last_spawned_at)] newest first, one row per character (cooldown view)."""
    best = {}
    for d in col(SH).find({"chat_id": int(chat_id), "spawned_by": _RANDOM}, {"character_code": 1, "rarity": 1, "spawned_at": 1}):
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
        {"$match": {"spawned_by": _RANDOM, "spawned_at": {"$regex": "^" + re.escape(day_key)}}},
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
