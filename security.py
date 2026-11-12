"""
security.py - Owner security tools: ban a whole group's members from the bot, ban single users, and give special
access to people who must stay allowed.

How a group's members are found (the bot does not need to be in the group any more):
    spawn_history_v2 keeps {chat_id, caught_by} for every character that was caught, so everybody who ever caught a
    character in a banned group is blocked. People who only chatted there and never caught anything are not stored
    anywhere - ban those by hand with /banuser.

Collections (all new, nothing existing is touched):
    security_banned_groups  {_id: chat_id, title, banned_at, banned_by}
    security_banned_users   {_id: user_id, source: "manual" | "group:<chat_id>", at, by, reason}
    security_allowed_users  {_id: user_id, at, by}                 (special access - never blocked)

Owner commands: /bangroup /unbangroup /bannedgroups /banuser /unbanuser /bannedusers /allowuser /removeallow
                /allowlist /checkuser
The gate (handler group -299) refuses blocked users everywhere (groups, PM, buttons) and silently ignores banned
groups. Owner, Executives, Scouts and allowed users are never blocked.
"""
import asyncio
import logging
import re
from html import escape as _h
import time
from datetime import datetime, timezone

from telegram import InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (ApplicationHandlerStop, CallbackQueryHandler, CommandHandler, ConversationHandler, MessageHandler,
                          TypeHandler, filters)
from telegram import Update

import mongo_db

logger = logging.getLogger(__name__)

BANNED_GROUPS = "security_banned_groups"
BANNED_USERS = "security_banned_users"
ALLOWED_USERS = "security_allowed_users"
SPAWN_HISTORY = "spawn_history_v2"

OWNER_COMMANDS = {"bangroup", "unbangroup", "bannedgroups", "banuser", "unbanuser", "bannedusers",
                  "allowuser", "removeallow", "allowlist", "checkuser", "blockedmembers"}

COMMAND_DESCRIPTIONS = {
    "bangroup": "Owner: ban a group - its players are blocked everywhere (/bangroup [group id])",
    "unbangroup": "Owner: lift a group ban (/unbangroup <group id>)",
    "bannedgroups": "Owner: list banned groups",
    "banuser": "Owner: ban one user (/banuser <user id> [reason])",
    "unbanuser": "Owner: lift a user ban (/unbanuser <user id>)",
    "bannedusers": "Owner: list banned users",
    "allowuser": "Owner: special access for a user from a banned group (/allowuser <user id>)",
    "removeallow": "Owner: remove special access (/removeallow <user id>)",
    "allowlist": "Owner: list users with special access",
    "checkuser": "Owner: see if a user is blocked and why (/checkuser <user id>)",
    "blockedmembers": "Owner: who is blocked - browse or search by name, @username or id (/blockedmembers [text])",
}

BLOCKED_TEXT = "🚫 You can't use this bot."
CACHE_TTL = 60.0
REPLY_GAP = 20.0               # seconds between refusal messages to the same user
NOTIFY_GAP = 3600.0            # seconds between owner notifications about the same user

_deps = {}
_state = {"ts": 0.0, "groups": {}, "members": set(), "manual": set(), "allow": set()}
_last_reply, _last_notify = {}, {}
_lock = asyncio.Lock()


def bind(**kwargs):
    """is_owner, is_staff (sync: Owner/Executive/Scout), owner_id, safe_reply, unauthorized_text, mark_success."""
    _deps.update({k: v for k, v in kwargs.items() if v is not None})


def _col(name):
    return mongo_db.col(name)


def _now():
    return datetime.now(timezone.utc).strftime("%d-%m-%Y %H:%M UTC")


def invalidate():
    _state["ts"] = 0.0


# ---------------- data (synchronous; call through asyncio.to_thread) ----------------
def _members_of(chat_ids):
    """Players who caught a character in any of these chats (the member list the database still has)."""
    if not chat_ids:
        return set()
    return {int(u) for u in _col(SPAWN_HISTORY).distinct(
        "caught_by", {"chat_id": {"$in": [int(c) for c in chat_ids]}, "caught_by": {"$ne": None}}) if u is not None}


def _load():
    groups = {int(d["_id"]): d for d in _col(BANNED_GROUPS).find({})}
    manual = {int(d["_id"]) for d in _col(BANNED_USERS).find({}, {"_id": 1})}
    allow = {int(d["_id"]) for d in _col(ALLOWED_USERS).find({}, {"_id": 1})}
    members = _members_of(groups.keys())
    return groups, members, manual, allow


async def _get_state():
    if time.monotonic() - _state["ts"] > CACHE_TTL:
        async with _lock:
            if time.monotonic() - _state["ts"] > CACHE_TTL:
                try:
                    groups, members, manual, allow = await asyncio.to_thread(_load)
                    _state.update(groups=groups, members=members, manual=manual, allow=allow, ts=time.monotonic())
                except Exception as e:
                    logger.warning("security state load failed: %s", e)
                    _state["ts"] = time.monotonic() - CACHE_TTL + 10        # retry in 10 s, keep the last good state
    return _state


def _is_staff(uid):
    try:
        return bool(_deps["is_staff"](uid))
    except Exception:
        return False


def _group_title(chat_id):
    doc = _col(mongo_db.GROUPS).find_one({"_id": int(chat_id)}) or {}
    return doc.get("title") or ""


def _group_choices(limit=12):
    """Chats the database knows from spawn history: [(chat_id, players, last_caught_at, title, bot_inside)]."""
    banned = {int(d["_id"]) for d in _col(BANNED_GROUPS).find({}, {"_id": 1})}
    rows = list(_col(SPAWN_HISTORY).aggregate([
        {"$match": {"caught_by": {"$ne": None}}},
        {"$group": {"_id": "$chat_id", "players": {"$addToSet": "$caught_by"}, "last": {"$max": "$caught_at"}}},
        {"$project": {"n": {"$size": "$players"}, "last": 1}},
    ], allowDiskUse=True))
    out = []
    for r in rows:
        cid = int(r["_id"])
        if cid in banned or cid > 0:                    # private chats (positive ids) are not groups
            continue
        gdoc = _col(mongo_db.GROUPS).find_one({"_id": cid}) or {}
        out.append((cid, int(r["n"]), str(r.get("last") or ""), gdoc.get("title") or "", bool(gdoc.get("registered"))))
    out.sort(key=lambda x: x[2], reverse=True)
    return out[:limit]


def _ban_group(chat_id, by):
    chat_id = int(chat_id)
    title = _group_title(chat_id)
    _col(BANNED_GROUPS).update_one({"_id": chat_id}, {"$set": {"title": title, "banned_at": _now(), "banned_by": int(by)}},
                                   upsert=True)
    invalidate()
    return title, len(_members_of([chat_id]))


def _unban_group(chat_id):
    deleted = _col(BANNED_GROUPS).delete_one({"_id": int(chat_id)}).deleted_count > 0
    _col(BANNED_USERS).delete_many({"source": f"group:{int(chat_id)}"})
    invalidate()
    return deleted


def _ban_user(uid, by, source="manual", reason=""):
    uid = int(uid)
    _col(BANNED_USERS).update_one({"_id": uid}, {"$set": {"source": source, "at": _now(), "by": int(by), "reason": reason[:100]}},
                                  upsert=True)
    _col(ALLOWED_USERS).delete_one({"_id": uid})          # an explicit ban cancels special access
    invalidate()


def _unban_user(uid):
    deleted = _col(BANNED_USERS).delete_one({"_id": int(uid)}).deleted_count > 0
    invalidate()
    return deleted


def _allow_user(uid, by):
    uid = int(uid)
    _col(ALLOWED_USERS).update_one({"_id": uid}, {"$set": {"at": _now(), "by": int(by)}}, upsert=True)
    _col(BANNED_USERS).delete_one({"_id": uid})
    invalidate()


def _remove_allow(uid):
    deleted = _col(ALLOWED_USERS).delete_one({"_id": int(uid)}).deleted_count > 0
    invalidate()
    return deleted


def _user_label(uid):
    d = _col(mongo_db.USERS).find_one({"_id": int(uid)}, {"username": 1, "first_name": 1, "last_name": 1}) or {}
    name = " ".join(x for x in (d.get("first_name"), d.get("last_name")) if x).strip()
    if d.get("username"):
        name = (name + " " if name else "") + "@" + d["username"]
    return f"{_h(name)} (<code>{int(uid)}</code>)" if name else f"<code>{int(uid)}</code>"   # HTML: tap the id to copy


def _user_groups(uid, group_ids):
    if not group_ids:
        return []
    return sorted(int(c) for c in _col(SPAWN_HISTORY).distinct(
        "chat_id", {"caught_by": int(uid), "chat_id": {"$in": [int(g) for g in group_ids]}}))


# ---------------- the gate ----------------
async def _refuse(update, context, uid, reason_text):
    now = time.monotonic()
    query, msg, chat = update.callback_query, update.effective_message, update.effective_chat
    try:
        if query is not None:
            await query.answer(BLOCKED_TEXT, show_alert=True)
        elif update.inline_query is not None:
            await update.inline_query.answer([], cache_time=0)
        elif msg is not None and chat is not None:
            text = msg.text or msg.caption or ""
            if (text.startswith("/") or chat.type == "private") and now - _last_reply.get(uid, -1e9) >= REPLY_GAP:
                if len(_last_reply) > 5000:
                    _last_reply.clear()
                _last_reply[uid] = now
                await context.bot.send_message(chat_id=chat.id, text=BLOCKED_TEXT)
    except Exception as e:
        logger.info("security refusal reply failed: %s", e)
    owner = _deps.get("owner_id")
    if owner and now - _last_notify.get(uid, -1e9) >= NOTIFY_GAP:
        if len(_last_notify) > 5000:
            _last_notify.clear()
        _last_notify[uid] = now
        try:
            where = update.effective_chat.title if update.effective_chat and update.effective_chat.title else (
                "private chat" if update.effective_chat and update.effective_chat.type == "private" else "a chat")
            await context.bot.send_message(
                chat_id=int(owner), parse_mode="HTML",
                text=f"🛡 SECURITY\n🚫 A blocked user tried to use the bot.\n👤 {await asyncio.to_thread(_user_label, uid)}\n"
                     f"📍 {_h(str(where))}\n📌 {_h(reason_text)}\n\nAllow them with /allowuser <code>{uid}</code>")
        except Exception as e:
            logger.info("security owner notice failed: %s", e)


async def security_gate(update, context):
    user, chat = update.effective_user, update.effective_chat
    if user is None or user.is_bot:
        return
    st = await _get_state()
    if not (st["groups"] or st["manual"] or st["members"]):
        return
    uid = user.id
    if chat is not None and chat.type in ("group", "supergroup") and chat.id in st["groups"]:
        # Banned group: the bot ignores it completely. Whoever speaks there is added to the blocked members.
        if uid not in st["manual"] and uid not in st["members"] and uid not in st["allow"] and not await asyncio.to_thread(_is_staff, uid):
            try:
                await asyncio.to_thread(_ban_user, uid, 0, f"group:{chat.id}", "spoke in a banned group")
            except Exception as e:
                logger.info("security auto-ban failed: %s", e)
        raise ApplicationHandlerStop
    manual = uid in st["manual"]
    member = uid in st["members"]
    if not (manual or member):
        return
    if not manual and uid in st["allow"]:
        return                                              # special access
    if await asyncio.to_thread(_is_staff, uid):
        return
    await _refuse(update, context, uid, "Banned by hand" if manual else "Member of a banned group")
    raise ApplicationHandlerStop


# ---------------- commands ----------------
async def _owner_only(update):
    uid = update.effective_user.id if update.effective_user else None
    if uid is not None and _deps["is_owner"](uid):
        return True
    try:
        await _deps["safe_reply"](update.effective_message, _deps.get("unauthorized_text") or "⚠️ Access Denied.")
    except Exception:
        pass
    return False


def _ok(update):
    try:
        _deps["mark_success"](update)
    except Exception:
        pass


async def _say(update, text, **kw):
    kw.setdefault("parse_mode", "HTML")          # every id is <code>..</code> so a tap copies it
    return await _deps["safe_reply"](update.effective_message, text, **kw)


def _target_user_id(update, context):
    msg = update.effective_message
    if msg is not None and msg.reply_to_message is not None and msg.reply_to_message.from_user is not None:
        return msg.reply_to_message.from_user.id
    if context.args and re.fullmatch(r"\d{4,15}", context.args[0].strip()):
        return int(context.args[0].strip())
    return None


def _parse_group_id(text):
    t = str(text or "").strip()
    return int(t) if re.fullmatch(r"-\d{5,20}", t) else None


def _confirm_kb(uid, chat_id):
    return InlineKeyboardMarkup([[InlineKeyboardButton("🚫 Ban group", callback_data=f"sec:by:{uid}:{chat_id}"),
                                  InlineKeyboardButton("↩️ Cancel", callback_data=f"sec:bn:{uid}")]])


async def _confirm_text(chat_id):
    title = await asyncio.to_thread(_group_title, chat_id)
    n = len(await asyncio.to_thread(_members_of, [chat_id]))
    return (f"🚫 Ban this group?\n\n🏷 {_h(title) or 'Title not stored'}\n🆔 <code>{chat_id}</code>\n"
            f"👥 {n} player(s) caught characters there. They will be blocked everywhere (groups, PM and buttons) unless "
            "they are staff or allowed with /allowuser.\nThe bot will also ignore the group itself and leave it if it is still inside.")


async def bangroup_command(update, context):
    if not await _owner_only(update):
        return
    uid = update.effective_user.id
    if context.args:
        chat_id = _parse_group_id(context.args[0])
        if chat_id is None:
            await _say(update, "❌ A group id looks like <code>-1001234567890</code>.\nUse /bangroup alone to pick from the groups in the database.")
            return
        await _say(update, await _confirm_text(chat_id), reply_markup=_confirm_kb(uid, chat_id))
        return
    choices = await asyncio.to_thread(_group_choices)
    if not choices:
        await _say(update, "ℹ️ The database has no group with caught characters to pick from.\nUse /bangroup &lt;group id&gt;.")
        return
    lines, rows = ["🚫 Ban a group - tap one", ""], []
    for i, (cid, n, last, title, inside) in enumerate(choices, 1):
        lines.append(f"{i}. {_h(title) or 'Title not stored'} · <code>{cid}</code>\n    👥 {n} players · {'🤖 bot inside' if inside else '🚪 bot left'}"
                     + (f" · last catch {last[:10]}" if last else ""))
        rows.append([InlineKeyboardButton(f"{i}. {(title or str(cid))[:30]} ({n})", callback_data=f"sec:bg:{uid}:{cid}")])
    lines += ["", "Newest activity first. A group that is not here: /bangroup &lt;group id&gt;."]
    await _say(update, "\n".join(lines), reply_markup=InlineKeyboardMarkup(rows))


async def security_callback(update, context):
    q = update.callback_query
    parts = (q.data or "").split(":")               # sec:<bg|by|bn>:<uid>[:<chat id>]
    if len(parts) < 3 or not parts[2].isdigit() or q.from_user.id != int(parts[2]):
        await q.answer("⚠️ This isn't yours.", show_alert=True)
        return
    if not _deps["is_owner"](q.from_user.id):
        await q.answer("⚠️ Access Denied.", show_alert=True)
        return
    action = parts[1]
    try:
        if action == "bn":
            await q.answer("Cancelled.")
            await q.edit_message_text("↩️ Cancelled. Nothing was banned.")
            return
        chat_id = int(parts[3])
        if action == "bg":
            await q.answer()
            await q.edit_message_text(await _confirm_text(chat_id), parse_mode="HTML", reply_markup=_confirm_kb(q.from_user.id, chat_id))
        elif action == "by":
            title, n = await asyncio.to_thread(_ban_group, chat_id, q.from_user.id)
            left = ""
            try:
                await context.bot.leave_chat(chat_id)
                left = "\n🚪 The bot left that group."
            except Exception:
                pass
            await q.answer("Banned.")
            await q.edit_message_text(f"✅ Group banned.\n🏷 {_h(title) or 'Title not stored'}\n🆔 <code>{chat_id}</code>\n"
                                      f"👥 {n} player(s) are now blocked.{left}\n\n"
                                      "Give someone special access: /allowuser &lt;user id&gt;\nUndo: /unbangroup <code>" + str(chat_id) + "</code>",
                                      parse_mode="HTML")
    except Exception as e:
        logger.error("security callback failed: %s", e)
        try:
            await q.answer("❌ Something went wrong.", show_alert=True)
        except Exception:
            pass


async def unbangroup_command(update, context):
    if not await _owner_only(update):
        return
    chat_id = _parse_group_id(context.args[0]) if context.args else None
    if chat_id is None:
        await _say(update, "Usage: /unbangroup &lt;group id&gt;\nSee /bannedgroups")
        return
    done = await asyncio.to_thread(_unban_group, chat_id)
    await _say(update, f"✅ Group <code>{chat_id}</code> is not banned any more. Its players can use the bot again." if done
               else f"ℹ️ Group <code>{chat_id}</code> was not banned.")
    if done:
        _ok(update)


async def bannedgroups_command(update, context):
    if not await _owner_only(update):
        return
    docs = await asyncio.to_thread(lambda: list(_col(BANNED_GROUPS).find({})))
    if not docs:
        await _say(update, "🛡 Banned Groups\n\nNo banned groups.")
        return
    lines = ["🛡 Banned Groups", ""]
    for i, d in enumerate(docs, 1):
        n = len(await asyncio.to_thread(_members_of, [d["_id"]]))
        lines.append(f"{i}. {_h(d.get('title') or '') or 'Title not stored'} · <code>{d['_id']}</code>\n    👥 {n} players · banned {_h(str(d.get('banned_at', '')))}")
    lines += ["", "Lift a ban: /unbangroup &lt;group id&gt;"]
    await _say(update, "\n".join(lines))


async def banuser_command(update, context):
    if not await _owner_only(update):
        return
    target = _target_user_id(update, context)
    if target is None:
        await _say(update, "Usage: /banuser &lt;user id&gt; [reason]  (or reply to the user with /banuser)")
        return
    if _deps["is_owner"](target) or await asyncio.to_thread(_is_staff, target):
        await _say(update, "❌ The Owner and staff cannot be banned. Remove their role first.")
        return
    reason = " ".join(context.args[1:]) if context.args and not (update.effective_message.reply_to_message) else " ".join(context.args)
    await asyncio.to_thread(_ban_user, target, update.effective_user.id, "manual", reason)
    await _say(update, f"✅ {await asyncio.to_thread(_user_label, target)} is banned from the bot.\nUndo: /unbanuser <code>{target}</code>")
    _ok(update)


async def unbanuser_command(update, context):
    if not await _owner_only(update):
        return
    target = _target_user_id(update, context)
    if target is None:
        await _say(update, "Usage: /unbanuser &lt;user id&gt;  (or reply to the user)")
        return
    done = await asyncio.to_thread(_unban_user, target)
    await _say(update, f"✅ <code>{target}</code> is not banned by hand any more." + (
        "\nℹ️ They may still be blocked as a member of a banned group - use /allowuser to give them access." if done else "")
        if done else f"ℹ️ <code>{target}</code> was not in the banned list.")
    if done:
        _ok(update)


async def bannedusers_command(update, context):
    if not await _owner_only(update):
        return
    docs = await asyncio.to_thread(lambda: list(_col(BANNED_USERS).find({}).sort("at", -1)))
    st = await _get_state()
    lines = ["🛡 Banned Users", "", f"👥 Blocked as members of banned groups: {len(st['members'])}", f"🚫 Banned by hand / seen in a banned group: {len(docs)}", ""]
    for i, d in enumerate(docs[:40], 1):
        src = "by hand" if d.get("source") == "manual" else str(d.get("source", "")).replace("group:", "group ")
        lines.append(f"{i}. <code>{d['_id']}</code> · {_h(src)}" + (f" · {_h(str(d['reason']))}" if d.get("reason") else ""))
    if len(docs) > 40:
        lines.append(f"… and {len(docs) - 40} more")
    await _say(update, "\n".join(lines))


async def allowuser_command(update, context):
    if not await _owner_only(update):
        return
    target = _target_user_id(update, context)
    if target is None:
        await _say(update, "Usage: /allowuser &lt;user id&gt;  (or reply to the user)\nGives special access to someone from a banned group.")
        return
    await asyncio.to_thread(_allow_user, target, update.effective_user.id)
    await _say(update, f"✅ {await asyncio.to_thread(_user_label, target)} has special access now.\nUndo: /removeallow <code>{target}</code>")
    _ok(update)


async def removeallow_command(update, context):
    if not await _owner_only(update):
        return
    target = _target_user_id(update, context)
    if target is None:
        await _say(update, "Usage: /removeallow &lt;user id&gt;")
        return
    done = await asyncio.to_thread(_remove_allow, target)
    await _say(update, f"✅ Special access removed for <code>{target}</code>." if done else f"ℹ️ <code>{target}</code> had no special access.")
    if done:
        _ok(update)


async def allowlist_command(update, context):
    if not await _owner_only(update):
        return
    docs = await asyncio.to_thread(lambda: list(_col(ALLOWED_USERS).find({}).sort("at", -1)))
    if not docs:
        await _say(update, "🛡 Special Access\n\nNobody has special access.")
        return
    lines = ["🛡 Special Access", ""]
    for i, d in enumerate(docs[:60], 1):
        lines.append(f"{i}. {await asyncio.to_thread(_user_label, d['_id'])} · since {_h(str(d.get('at', '')))}")
    await _say(update, "\n".join(lines))


async def checkuser_command(update, context):
    if not await _owner_only(update):
        return
    target = _target_user_id(update, context)
    if target is None:
        await _say(update, "Usage: /checkuser &lt;user id&gt;  (or reply to the user)")
        return
    st = await _get_state()
    groups = await asyncio.to_thread(_user_groups, target, list(st["groups"].keys()))
    manual, allowed = target in st["manual"], target in st["allow"]
    staff = _deps["is_owner"](target) or await asyncio.to_thread(_is_staff, target)
    blocked = (manual or bool(groups)) and not staff and not (allowed and not manual)
    lines = [f"🔎 {await asyncio.to_thread(_user_label, target)}", "",
             "Status: " + ("🚫 BLOCKED" if blocked else "✅ can use the bot"),
             f"👔 Staff: {'yes' if staff else 'no'}", f"🚫 Banned by hand: {'yes' if manual else 'no'}",
             f"🔑 Special access: {'yes' if allowed else 'no'}"]
    if groups:
        lines.append("🏠 Caught characters in banned group(s): " + ", ".join(f"<code>{g}</code>" for g in groups))
    await _say(update, "\n".join(lines))



# ---------------- /blockedmembers: browse or search everybody who is blocked ----------------
BM_PAGE = 12
BM_SEARCH_MAX = 20
SQ_INPUT = 1
_SQ = "sec_search_scope"


def _blocked_rows(gid=None):
    """[(uid, name, username, catches, tag)] - players of the banned groups (gid = one group) plus users banned by hand."""
    groups = [int(gid)] if gid else [int(d["_id"]) for d in _col(BANNED_GROUPS).find({}, {"_id": 1})]
    counts = {}
    if groups:
        for r in _col(SPAWN_HISTORY).aggregate([
                {"$match": {"chat_id": {"$in": groups}, "caught_by": {"$ne": None}}},
                {"$group": {"_id": "$caught_by", "n": {"$sum": 1}}}]):
            counts[int(r["_id"])] = int(r["n"])
    manual = {} if gid else {int(d["_id"]): d for d in _col(BANNED_USERS).find({})}
    ids = set(counts) | set(manual)
    users = {int(d["_id"]): d for d in _col(mongo_db.USERS).find({"_id": {"$in": list(ids)}},
                                                                {"username": 1, "first_name": 1, "last_name": 1})} if ids else {}
    rows = []
    for uid in ids:
        d = users.get(uid) or {}
        name = " ".join(x for x in (d.get("first_name"), d.get("last_name")) if x).strip()
        tag = ""
        if uid in manual:
            tag = "🚫 banned by hand" if manual[uid].get("source") == "manual" else "🚫 spoke in a banned group"
        rows.append((uid, name, d.get("username") or "", counts.get(uid, 0), tag))
    rows.sort(key=lambda r: (-r[3], r[0]))
    return rows


def _bm_filter(rows, text):
    q = (text or "").strip().lstrip("@").casefold()
    if not q:
        return rows
    return [r for r in rows if q in r[1].casefold() or q in r[2].casefold() or q in str(r[0])]


def _bm_lines(rows, start, allow):
    lines = []
    for i, (uid, name, username, n, tag) in enumerate(rows, start + 1):
        who = _h(name) if name else "Unknown"
        if username:
            who += f" @{_h(username)}"
        bits = [f"🆔 <code>{uid}</code>"]
        if n:
            bits.append(f"🎯 {n} catch{'es' if n != 1 else ''}")
        if tag:
            bits.append(tag)
        if uid in allow:
            bits.append("🔑 special access (not blocked)")
        elif _is_staff(uid):
            bits.append("👔 staff (not blocked)")
        lines.append(f"{i}. {who}\n    " + " · ".join(bits))
    return lines


def _bm_page(gid, page):
    rows = _blocked_rows(gid)
    pages = max(1, -(-len(rows) // BM_PAGE))
    page = min(max(page, 0), pages - 1)
    allow = {int(d["_id"]) for d in _col(ALLOWED_USERS).find({}, {"_id": 1})}
    chunk = rows[page * BM_PAGE:(page + 1) * BM_PAGE]
    head = f"🛡 Blocked Members (page {page + 1}/{pages}) · {len(rows)} total"
    if gid:
        head += f"\n🏠 Group <code>{int(gid)}</code>"
    body = _bm_lines(chunk, page * BM_PAGE, allow) if chunk else ["Nobody is blocked."]
    return page, pages, "\n".join([head, ""] + body)


def _bm_search(gid, text):
    rows = _bm_filter(_blocked_rows(gid), text)
    allow = {int(d["_id"]) for d in _col(ALLOWED_USERS).find({}, {"_id": 1})}
    shown = rows[:BM_SEARCH_MAX]
    head = f"🔍 Search: {_h(text)}\n{len(rows)} match(es)" + (f" - showing the first {BM_SEARCH_MAX}, type more letters to narrow it" if len(rows) > BM_SEARCH_MAX else "")
    body = _bm_lines(shown, 0, allow) if shown else ["No blocked user matches that name, @username or id.\nA user who is not blocked will not show here - use /checkuser <id>.".replace("<id>", "&lt;id&gt;")]
    return "\n".join([head, ""] + body)


def _bm_kb(uid, gid, page, pages):
    g = int(gid) if gid else 0
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("‹ Prev", callback_data=f"sec:bm:{uid}:{page - 1}:{g}"))
    if page < pages - 1:
        nav.append(InlineKeyboardButton("Next ›", callback_data=f"sec:bm:{uid}:{page + 1}:{g}"))
    rows = [[InlineKeyboardButton("🔍 Search by name, @username or id", callback_data=f"sec:sq:{uid}:{g}")]]
    if nav:
        rows.append(nav)
    return InlineKeyboardMarkup(rows)


async def blockedmembers_command(update, context):
    if not await _owner_only(update):
        return
    uid = update.effective_user.id
    args = list(context.args or [])
    gid = None
    if args and _parse_group_id(args[0]) is not None:
        gid = _parse_group_id(args.pop(0))
    if args:                                                    # /blockedmembers <text>  ->  search straight away
        await _say(update, await asyncio.to_thread(_bm_search, gid, " ".join(args)))
        return
    page, pages, text = await asyncio.to_thread(_bm_page, gid, 0)
    await _say(update, text, reply_markup=_bm_kb(uid, gid, page, pages))


async def blockedmembers_callback(update, context):
    q = update.callback_query
    parts = (q.data or "").split(":")                          # sec:bm:<uid>:<page>:<group id or 0>
    if len(parts) != 5 or not parts[2].isdigit() or q.from_user.id != int(parts[2]):
        await q.answer("⚠️ This isn't yours.", show_alert=True)
        return
    if not _deps["is_owner"](q.from_user.id):
        await q.answer("⚠️ Access Denied.", show_alert=True)
        return
    gid = int(parts[4]) or None
    try:
        page, pages, text = await asyncio.to_thread(_bm_page, gid, int(parts[3]))
        await q.answer()
        await q.edit_message_text(text, parse_mode="HTML", reply_markup=_bm_kb(q.from_user.id, gid, page, pages))
    except Exception as e:
        logger.info("blockedmembers page failed: %s", e)
        try:
            await q.answer()
        except Exception:
            pass


async def search_start(update, context):
    q = update.callback_query
    parts = (q.data or "").split(":")                          # sec:sq:<uid>:<group id or 0>
    if len(parts) != 4 or not parts[2].isdigit() or q.from_user.id != int(parts[2]):
        await q.answer("⚠️ This isn't yours.", show_alert=True)
        return ConversationHandler.END
    if not _deps["is_owner"](q.from_user.id):
        await q.answer("⚠️ Access Denied.", show_alert=True)
        return ConversationHandler.END
    context.user_data[_SQ] = int(parts[3]) or None
    await q.answer()
    await q.message.reply_text("🔍 Send a name, @username or id (part of it is enough).\nSend /cancel to stop.")
    return SQ_INPUT


async def search_input(update, context):
    if not update.effective_user or not _deps["is_owner"](update.effective_user.id):
        return ConversationHandler.END
    text = (update.effective_message.text or "").strip()
    if not text:
        return SQ_INPUT
    result = await asyncio.to_thread(_bm_search, context.user_data.get(_SQ), text)
    await _say(update, result + "\n\n🔍 Send another name to search again, or /cancel.")
    return SQ_INPUT                                            # stays open so you can keep searching


async def search_cancel(update, context):
    context.user_data.pop(_SQ, None)
    await _say(update, "↩️ Search closed.")
    return ConversationHandler.END


# ---------------- help page ----------------
HELP_TEXT = (
    "🛡 Security (Owner)\n\n"
    "📌 Overview\n"
    "Block a whole group's members from the bot, ban single users, and give special access to people who must stay allowed. "
    "Members of a banned group are the players who caught characters there - the database keeps that list even after the bot "
    "left the group. Staff (Owner, Executives, Scouts) are never blocked.\n\n"
    "⌨️ Commands & usage\n"
    "Groups\n"
    "1. /bangroup - Pick a group from the database and ban it (or /bangroup <group id>)\n"
    "2. /unbangroup <group id> - Lift a group ban\n"
    "3. /bannedgroups - List banned groups with player counts\n\n"
    "Users\n"
    "4. /banuser <user id> [reason] - Ban one user (or reply to them)\n"
    "5. /unbanuser <user id> - Lift a user ban\n"
    "6. /bannedusers - List banned users\n\n"
    "Special access\n"
    "7. /allowuser <user id> - Let someone use the bot even if they are from a banned group (or reply to them)\n"
    "8. /removeallow <user id> - Take the special access away\n"
    "9. /allowlist - List everyone with special access\n\n"
    "Check\n"
    "10. /checkuser <user id> - See if a user is blocked and why\n"
    "11. /blockedmembers - Browse everybody who is blocked, with a 🔍 Search button (name, @username or id)\n"
    "    /blockedmembers <text> - Search straight away (add a group id first to see one group)"
)


def help_module():
    return ("security", "🛡 Security", HELP_TEXT)


def register(app):
    app.add_handler(TypeHandler(Update, security_gate), group=-299)         # right after the human-only gate (-300)
    for name, callback in (("bangroup", bangroup_command), ("unbangroup", unbangroup_command),
                           ("bannedgroups", bannedgroups_command), ("banuser", banuser_command),
                           ("unbanuser", unbanuser_command), ("bannedusers", bannedusers_command),
                           ("allowuser", allowuser_command), ("removeallow", removeallow_command),
                           ("allowlist", allowlist_command), ("checkuser", checkuser_command)):
        app.add_handler(CommandHandler(name, callback))
    app.add_handler(CommandHandler("blockedmembers", blockedmembers_command))
    app.add_handler(ConversationHandler(
        entry_points=[CallbackQueryHandler(search_start, pattern=r"^sec:sq:\d+:-?\d+$")],
        states={SQ_INPUT: [MessageHandler(filters.TEXT & ~filters.COMMAND, search_input)]},
        fallbacks=[CommandHandler("cancel", search_cancel)],
        allow_reentry=True, conversation_timeout=180))
    app.add_handler(CallbackQueryHandler(blockedmembers_callback, pattern=r"^sec:bm:\d+:\d+:-?\d+$"))
    app.add_handler(CallbackQueryHandler(security_callback, pattern=r"^sec:(bg|by|bn):\d+(:-?\d+)?$"))
