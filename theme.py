"""
theme.py - Bot Theme Customization (Owner only)
===============================================

Self-contained module. bot.py only needs:
    import theme
    theme.bind(is_owner=..., default_start_text=..., add_header=..., build_help_text=...)   # in main(), before register
    theme.register(app)                                                                    # in main(); also re-applies the saved
                                                                                           # bot description after every restart
    await theme.send_start(update, context)   # in start(): returns False when nothing is customized -> original code runs
    theme.decorate_help_text(text)            # in build_help_text()

Entry point: Owner Commands (/help) -> [🎨 Customize Bot] -> hub with seven sections:
    📝 Welcome   🖼️ Banner   🔘 Start Menu   📖 About Bot   🔗 Links   🎭 Theme   📄 Description
Every section has its own Edit/Preview/Reset/Save controls and a full-width Back.

Persistence (existing MongoDB, collection `bot_settings`, one document):
    _id "theme_customization": {welcome:{text}, banner:{file_id,unique_id}, buttons:{items:[...]}, about:{text},
                                links:{channel|group|website:[{label,url},...]}, theme:{start,help}, description:{text}, updated_at}
    A section key that is missing means "built-in default". Save $sets only that section's key; Reset $unsets only it.
    The saved values are mirrored in memory (loaded at startup), so reads are free and saved settings survive restarts.

Safety model:
  * every tap re-checks the REAL owner (bot.is_owner) - never an id taken from the button - and that the chat is private;
  * one pending draft per owner and section (memory); Back/Cancel never saves; Save persists only its own section;
  * confirmations (reset / remove / delete) are single-use, expire, and are bound to the owner;
  * user text is validated (length, Telegram-HTML tags, URLs, image type/size) before it becomes a draft;
  * a database failure is reported and leaves both the database and the in-memory copy unchanged;
  * start-menu buttons the owner adds are URL buttons only (no callback/command execution can be configured).
"""

import asyncio
import copy
import html
import logging
import re
import secrets
import time
from datetime import datetime, timezone
from html.parser import HTMLParser
from urllib.parse import urlparse

import mongo_db

logger = logging.getLogger(__name__)

# --------------------------------------------------------------------------------------------- configuration
SETTINGS_ID = "theme_customization"
SECTIONS = ("welcome", "banner", "buttons", "about", "links", "theme", "description")
START_SECTIONS = ("welcome", "banner", "buttons", "links", "theme")      # sections that change /start

MAX_TEXT = 3500            # welcome / about (Telegram allows 4096; room for the name header and theme frame)
MAX_LABEL = 30
MAX_DESC = 120             # ONE description text. Telegram's profile line ("short description") holds at most 120
                           # characters, so that is the limit; the same text is also used as the empty-chat description.
MIN_DESC = 10              # shortest text accepted for the description
MAX_URL = 256
MAX_BUTTONS = 12
MAX_PER_ROW = 4                      # buttons in one row (Telegram allows 8, but names get cut off on phones)
MAX_PHOTO_BYTES = 10 * 1024 * 1024
CAPTION_LIMIT = 1000       # photo captions are limited to 1024 characters
AWAIT_TTL = 600            # seconds an Edit/Upload prompt stays active
CONFIRM_TTL = 300          # seconds a Yes/No confirmation stays valid

DEFAULT_HELP_LABEL = "📖 Help"      # the existing /start button (callback help:<uid>:open - fixed)
LINK_SLOTS = ("channel", "group", "website")
LINK_LABELS = {"channel": "📢 Channel", "group": "👥 Group", "website": "🌐 Website"}
LINK_WORDS = {"channel": "Channel", "group": "Group", "website": "Website/Social"}
LINK_PLURAL = {"channel": "Channels", "group": "Groups", "website": "Websites / Social"}
MAX_LINKS_PER_SLOT = 8
# Ready-made Group / Channel lists, used until the Owner saves their own Links (the Links panel shows them; press
# Save once to keep them, or change them first). Saving an empty list removes them.
DEFAULT_LINKS = {
    "group": [{"label": "👥 Wonderland Anime gc", "url": "https://t.me/WONDERLAND_anime_gc"},
              {"label": "👥 The Ravagers", "url": "https://t.me/The_Ravagers"}],
    "channel": [{"label": "📢 Anime Grabber Updates", "url": "https://t.me/grab_anime_update"}],
}               # e.g. Channel One ... Channel Eight

# Telegram cannot colour inline buttons, so themes are fixed presets: a decorative frame + the emoji of the default
# labels. "classic" is the built-in look and changes nothing.
PRESETS = {
    "classic": {"name": "Classic (default)", "emoji": "", "line": ""},
    "sakura": {"name": "🌸 Sakura", "emoji": "🌸", "line": "🌸━━━━━━━━━━━━🌸"},
    "midnight": {"name": "🌙 Midnight", "emoji": "🌙", "line": "🌙━━━━━━━━━━━━🌙"},
    "neon": {"name": "⚡ Neon", "emoji": "⚡", "line": "⚡━━━━━━━━━━━━⚡"},
}

DENIED_TEXT = "⚠️ Access Denied: Only the Bot Owner can use these controls."
NOT_YOURS_TEXT = "❌ This menu belongs to another user."
STALE_TEXT = "⚠️ This confirmation is outdated. Please open the menu again."

# --------------------------------------------------------------------------------------------- injected helpers
_deps = {
    "is_owner": lambda uid: False,
    "default_start_text": "",            # the existing /start message, word for word
    "default_start_keyboard": None,      # bot.start_help_keyboard(user_id)
    "build_help_text": None,             # bot.build_help_text()
    "add_header": None,                  # bot.add_display_name_header(message, text)
}


def bind(**kwargs):
    _deps.update({k: v for k, v in kwargs.items() if v is not None})


def _is_owner(uid):
    try:
        return bool(_deps["is_owner"](int(uid)))
    except Exception:
        return False


# --------------------------------------------------------------------------------------------- state
_saved = {}        # section -> saved value (mirror of the database)
_drafts = {}       # (owner_id, section) -> pending value
_awaiting = {}     # owner_id -> {"section", "field", "extra", "ts"}
_confirms = {}     # nonce -> {"owner", "section", "op", "arg", "ts"}


def _now():
    return time.monotonic()


def _awaiting_state(uid):
    st = _awaiting.get(uid)
    if st and _now() - st["ts"] > AWAIT_TTL:
        _awaiting.pop(uid, None)
        return None
    return st


def _is_awaiting(uid):
    return _awaiting_state(uid) is not None


def cancel_input(uid):
    """/cancel: drop a pending Edit/Upload prompt. True if one was waiting. Unsaved drafts are kept (they are never saved
    without 💾 Save, and the hub flags them)."""
    return _awaiting_state(uid) is not None and _awaiting.pop(uid, None) is not None


def _set_await(uid, section, field, extra=None):
    _awaiting[uid] = {"section": section, "field": field, "extra": dict(extra or {}), "ts": _now()}


def _make_confirm(owner, section, op, arg=None):
    for k in [k for k, v in _confirms.items() if _now() - v["ts"] > CONFIRM_TTL]:
        _confirms.pop(k, None)
    nonce = secrets.token_hex(4)
    _confirms[nonce] = {"owner": owner, "section": section, "op": op, "arg": arg, "ts": _now()}
    return nonce


def _pop_confirm(nonce, owner, section, op):
    """Single-use: a replayed or foreign confirmation returns None."""
    c = _confirms.pop(nonce, None)
    if not c or c["owner"] != owner or c["section"] != section or c["op"] != op or _now() - c["ts"] > CONFIRM_TTL:
        return None
    return c


def _draft(uid, section):
    return _drafts.get((uid, section))


def _set_draft(uid, section, value):
    _drafts[(uid, section)] = value


def _clear_draft(uid, section):
    _drafts.pop((uid, section), None)


# --------------------------------------------------------------------------------------------- persistence
def _col():
    return mongo_db.col(mongo_db.BOT_SETTINGS)


def load_settings():
    """Load the saved customization into memory (called once at startup). Never raises."""
    try:
        doc = _col().find_one({"_id": SETTINGS_ID}) or {}
    except Exception as e:
        logger.error("theme settings could not be loaded: %s", e)
        return False
    _saved.clear()
    for section in SECTIONS:
        if isinstance(doc.get(section), dict):
            _saved[section] = doc[section]
    return True


def _persist_sync(section, value):
    if value is None:
        _col().update_one({"_id": SETTINGS_ID}, {"$unset": {section: ""}}, upsert=True)
    else:
        _col().update_one({"_id": SETTINGS_ID},
                          {"$set": {section: value, "updated_at": datetime.now(timezone.utc).isoformat(timespec="seconds")}},
                          upsert=True)


async def _persist(section, value):
    """Write ONE section (None = remove it = back to the default). True only if the database confirmed it."""
    try:
        await asyncio.to_thread(_persist_sync, section, value)
    except Exception as e:
        logger.error("theme save failed (%s): %s", section, e)
        return False
    if value is None:
        _saved.pop(section, None)
    else:
        _saved[section] = copy.deepcopy(value)
    return True


# --------------------------------------------------------------------------------------------- validation
_ALLOWED_TAGS = {"b", "strong", "i", "em", "u", "ins", "s", "strike", "del", "a", "code", "pre", "tg-spoiler", "blockquote"}
_BAD_AMP = re.compile(r"&(?!(?:lt|gt|amp|quot|#\d+|#x[0-9a-fA-F]+);)")


class _HtmlChecker(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.stack, self.error_text = [], None

    def _fail(self, text):
        if self.error_text is None:
            self.error_text = text

    def handle_starttag(self, tag, attrs):
        if tag not in _ALLOWED_TAGS:
            return self._fail(f"The tag <{tag}> is not supported by Telegram.")
        if tag == "a":
            href = dict(attrs).get("href") or ""
            if urlparse(href).scheme.lower() not in ("http", "https", "tg"):
                return self._fail('Links must look like <a href="https://example.com">text</a>.')
        self.stack.append(tag)

    def handle_endtag(self, tag):
        if tag not in _ALLOWED_TAGS:
            return self._fail(f"The tag </{tag}> is not supported by Telegram.")
        if not self.stack or self.stack[-1] != tag:
            return self._fail(f"The closing tag </{tag}> does not match an open tag.")
        self.stack.pop()

    def handle_data(self, data):
        if "<" in data or ">" in data:
            self._fail("Write a literal < or > as &lt; or &gt;.")
        if _BAD_AMP.search(data):
            self._fail("Write a literal & as &amp;.")

    def handle_entityref(self, name):
        pass

    def handle_charref(self, name):
        pass


_TAGLIKE = re.compile(r"</?(?:b|strong|i|em|u|ins|s|strike|del|a|code|pre|tg-spoiler|blockquote)\b", re.I)


def validate_text(text):
    """
    -> (clean_html, None) or (None, error). The Owner can simply paste the message: formatting applied in Telegram is kept
    (the input handler passes text_html), plain text is shown exactly as typed (< > & are escaped for them), and hand-written
    Telegram HTML (<b>, <i>, <a href>, ...) is checked. Only HTML that is clearly broken is refused.
    """
    text = re.sub(r"</?tg-emoji[^>]*>", "", (text or "")).strip()     # custom emoji are not available to bots: keep the plain emoji
    if not text:
        return None, "The message cannot be empty."
    checker = _HtmlChecker()
    try:
        checker.feed(text)
        checker.close()
    except Exception:
        checker.error_text = "The formatting could not be read. Check your HTML tags."
    if checker.error_text is None and checker.stack:
        checker.error_text = f"The tag <{checker.stack[-1]}> is never closed."
    if checker.error_text:
        if _TAGLIKE.search(text):
            return None, checker.error_text            # the Owner clearly wrote HTML tags and made a mistake
        text = html.escape(text, quote=False)           # plain text: show every character literally
    if len(text) > MAX_TEXT:
        return None, f"That is {len(text)} characters; the limit is {MAX_TEXT}."
    return text, None


def render_user_text(text, user):
    """
    Fills the user placeholders with the Telegram user's details (HTML-escaped): {first} first name, {last} last name,
    {name} full name, {username} @username (or the name), {id}, {mention} clickable first name. Unknown {words} stay as written.
    """
    if not text or "{" not in text or user is None:
        return text
    first = getattr(user, "first_name", None) or ""
    last = getattr(user, "last_name", None) or ""
    full = " ".join(p for p in (first, last) if p) or "User"
    uname = getattr(user, "username", None)
    values = {
        "first": first or full, "firstname": first or full, "first_name": first or full, "last": last, "lastname": last,
        "last_name": last, "name": full, "fullname": full, "full_name": full, "user": full, "display": full,
        "username": f"@{uname}" if uname else full, "id": str(getattr(user, "id", "")),
    }

    def repl(m):
        key = m.group(1).lower()
        if key == "mention":
            return f'<a href="tg://user?id={user.id}">{html.escape(first or full, quote=False)}</a>'
        value = values.get(key)
        return m.group(0) if value is None else html.escape(value, quote=False)

    return re.sub(r"\{(\w+)\}", repl, text)


def _nopreview():
    """Keyword argument that switches off the big link-preview card (a URL inside a message would otherwise expand)."""
    try:
        from telegram import LinkPreviewOptions
        return {"link_preview_options": LinkPreviewOptions(is_disabled=True)}
    except Exception:
        return {"disable_web_page_preview": True}


_URL_IN_TEXT = re.compile(r"https?://[^\s<]+")


def _panel_html(text):
    """
    Panel text as Telegram HTML with every link shown as plain code text. Telegram never turns text inside <code> into a
    link, so no big preview card (like the channel invite card) can appear in the customization panels, whatever the
    bot library version does with the "no preview" option.
    """
    return _URL_IN_TEXT.sub(lambda m: f"<code>{m.group(0)}</code>", html.escape(text or "", quote=False))


def _grid(buttons):
    """Two buttons per row; an odd last button takes the full width (like the Add me / Commands / Website / About layout)."""
    rows = [buttons[i:i + 2] for i in range(0, len(buttons), 2)]
    return rows


_TG_NAME = re.compile(r"^[A-Za-z][A-Za-z0-9_]{3,31}$")


async def _link_title(bot, url):
    """
    Auto button name for a PUBLIC Telegram link (https://t.me/username): the real channel/group name, with an emoji for its
    type. Private invite links (t.me/+...) do not reveal a name, so they return None and the Owner is asked to type one.
    """
    try:
        p = urlparse(url)
        if (p.hostname or "").lower() not in ("t.me", "telegram.me", "www.t.me"):
            return None
        name = p.path.strip("/").split("/")[0]
        if not _TG_NAME.match(name):
            return None
        chat = await bot.get_chat("@" + name)
        title = (getattr(chat, "title", None) or getattr(chat, "first_name", None) or "").strip()
        if not title:
            return None
        kind = getattr(chat, "type", "")
        emoji = "📢" if kind == "channel" else "👥" if kind in ("group", "supergroup") else ""
        label = f"{emoji} {title}".strip()
        return label if len(label) <= MAX_LABEL else label[:MAX_LABEL - 1].rstrip() + "…"
    except Exception as e:
        logger.info("link title lookup failed: %s", e)
        return None


def validate_label(text):
    label = (text or "").strip()
    if not label or "\n" in label:
        return None, "Send a single line of text for the label."
    if len(label) > MAX_LABEL:
        return None, f"The label is {len(label)} characters; the limit is {MAX_LABEL}."
    return label, None


_HOST = re.compile(r"^[a-z0-9]([a-z0-9-]*[a-z0-9])?(\.[a-z0-9]([a-z0-9-]*[a-z0-9])?)+$")


def _normalize_tg(text):
    """
    Accepts every usual way of writing a Telegram link and returns the full https://t.me/... URL:
    https://t.me/name, t.me/name, @name, /name and plain name. Anything else (other websites) is returned as typed.
    """
    raw = (text or "").strip()
    m = re.fullmatch(r"(?:https?://)?(?:www\.)?(?:t|telegram)\.me/(.+)", raw, re.I)
    if m:
        return "https://t.me/" + m.group(1)
    m = re.fullmatch(r"[@/]?([A-Za-z][A-Za-z0-9_]{3,31})", raw)
    if m:
        return "https://t.me/" + m.group(1)
    return raw


def validate_url(text):
    """Only https links to a real-looking host (t.me included). -> (url, None) or (None, error)."""
    url = _normalize_tg(text)
    if not url or any(c.isspace() for c in url):
        return None, "Send the link as a single https:// URL (or just @username / t.me/username for Telegram)."
    if len(url) > MAX_URL:
        return None, f"The link is too long (limit {MAX_URL} characters)."
    try:
        parsed = urlparse(url)
        host = (parsed.hostname or "").lower()
    except ValueError:
        return None, "That link is not valid."
    if parsed.scheme.lower() != "https":
        return None, "The link must start with https:// (for Telegram: https://t.me/...)."
    if "@" in parsed.netloc or not _HOST.match(host):
        return None, "That link is not a valid web address."
    return url, None


# --------------------------------------------------------------------------------------------- defaults and composition
def _preset(theme_value, which):
    key = (theme_value or {}).get(which, "classic")
    return PRESETS.get(key, PRESETS["classic"])


def _frame(text, preset):
    line = preset["line"]
    return text if not line else f"{line}\n\n{text}\n\n{line}"


def _unframe(text, preset):
    line = preset["line"]
    if line and text.startswith(line + "\n\n") and text.endswith("\n\n" + line):
        return text[len(line) + 2:-(len(line) + 2)]
    return text


ADDGROUP_LABEL = "➕ Add me to group"
DETAILS_LABEL = "💜 Details"
# The /start layout shipped by default: Add me to group (full width) / Help + Details / Group + Channel.
DEFAULT_LAYOUT = [["addgroup"], ["help", "details"], ["link_group", "link_channel"]]


def default_buttons():
    return [{"id": "help", "kind": "help", "label": DEFAULT_HELP_LABEL}]


def _builtin_extras():
    return [{"id": "addgroup", "kind": "addgroup", "label": ADDGROUP_LABEL},
            {"id": "details", "kind": "details", "label": DETAILS_LABEL}]


def _button_items(value):
    """The configurable start buttons (saved or default). The built-in Help button is always present."""
    items = copy.deepcopy((value or {}).get("items") or default_buttons())
    if not any(i.get("kind") == "help" for i in items):
        items.insert(0, default_buttons()[0])
    if "layout" not in (value or {}):               # not arranged yet: offer the ready-made buttons too
        for extra in _builtin_extras():
            if not any(i.get("kind") == extra["kind"] for i in items):
                items.append(extra)
    return items


def _resolve_layout(items, links_value, layout):
    """
    The /start rows as lists of element ids: the saved layout (or the default one) limited to buttons that exist now.
    A button that is not in the layout yet (e.g. a newly added one) is put at the bottom, two per row.
    Element ids: the item ids (help, addgroup, details, b1, b2, ...) and link_channel / link_group / link_website.
    """
    available = [i["id"] for i in items] + [f"link_{slot}" for slot in LINK_SLOTS if _slot_links(links_value, slot)]
    base = layout if isinstance(layout, list) else DEFAULT_LAYOUT
    rows, used = [], set()
    for row in base:
        r = [e for e in row if e in available and e not in used]
        used.update(r)
        if r:
            rows.append(r)
    rest = [e for e in available if e not in used]
    rows.extend(rest[n:n + 2] for n in range(0, len(rest), 2))
    return rows


def _themed_label(label, default_label, word, preset):
    if preset["emoji"] and label == default_label:
        return f"{preset['emoji']} {word}"
    return label


_HAS_PLACEHOLDER = re.compile(r"\{(?:first|firstname|first_name|last|lastname|last_name|name|fullname|full_name|user|display|"
                              r"username|id|mention)\}", re.I)


def _with_greeting(text, user):
    """
    The Owner only pastes the message (e.g. "Welcome to Anime Bot ..."); the greeting with the reader's Telegram display
    name is added automatically. Skipped when the Owner already wrote a {placeholder} or their own greeting.
    """
    if user is None or _HAS_PLACEHOLDER.search(text):
        return text
    first = (getattr(user, "first_name", None) or "").strip()
    last = (getattr(user, "last_name", None) or "").strip()
    name = " ".join(p for p in (first, last) if p) or "there"
    return f"🌸 HEY {html.escape(name, quote=False)}! 🎉\n\n{text}"


_NAME_LINE = re.compile(r"\A\s*👤[^\n]*\{(?:first|firstname|first_name|last|lastname|last_name|name|fullname|full_name|user|display|username|mention)\}[^\n]*\n+",
                        re.I)


def start_text_for(welcome_value, theme_value, user=None):
    """
    -> (text, is_custom_html). Without a saved welcome this is the existing /start text, word for word.
    With `user`, a custom welcome is returned fully personalised (automatic greeting + any {placeholders} filled in).
    """
    custom = bool(welcome_value and welcome_value.get("text"))
    base = welcome_value["text"] if custom else _deps["default_start_text"]
    if custom:
        base = _NAME_LINE.sub("", base, count=1)       # the name is shown once, in the greeting - drop a leading "👤 ... {first} ..." line
    if custom and user is not None:
        base = render_user_text(_with_greeting(base, user), user)
    return _frame(base, _preset(theme_value, "start")), custom


def _slot_links(links_value, slot):
    """All links of one slot as [{"label", "url"}]. Understands the old single-link format {"url": ...} too."""
    v = (links_value or {}).get(slot)
    if isinstance(v, dict):
        v = [v]
    out = []
    for e in (v if isinstance(v, list) else []):
        if isinstance(e, dict) and e.get("url"):
            out.append({"label": (e.get("label") or "").strip() or LINK_LABELS[slot], "url": e["url"]})
    return out


def start_keyboard_for(uid, buttons_value, links_value, theme_value, preview=False, bot_username=None):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    preset = _preset(theme_value, "start")
    items = _button_items(buttons_value)
    elements = {}
    for item in items:
        kind = item["kind"]
        if kind == "help":
            label = _themed_label(item["label"], DEFAULT_HELP_LABEL, "Help", preset)
            data = f"theme:{uid}:noop:x" if preview else f"help:{uid}:open"     # the original action, untouched
            elements[item["id"]] = InlineKeyboardButton(label, callback_data=data)
        elif kind == "addgroup":
            if bot_username:
                elements[item["id"]] = InlineKeyboardButton(item["label"], url=f"https://t.me/{bot_username}?startgroup=true")
        elif kind == "details":
            data = f"theme:{uid}:noop:x" if preview else "tdetails"
            elements[item["id"]] = InlineKeyboardButton(item["label"], callback_data=data)
        elif item.get("url"):
            elements[item["id"]] = InlineKeyboardButton(item["label"], url=item["url"])
    for slot in LINK_SLOTS:
        if _slot_links(links_value, slot):          # ONE button per type; tapping it lists everything added under it
            data = f"theme:{uid}:noop:x" if preview else f"tlinks:{slot}"
            elements[f"link_{slot}"] = InlineKeyboardButton(
                _themed_label(LINK_LABELS[slot], LINK_LABELS[slot], LINK_WORDS[slot].split("/")[0], preset), callback_data=data)
    rows = _resolve_layout(items, links_value, (buttons_value or {}).get("layout"))
    keyboard = [[elements[e] for e in row if e in elements] for row in rows]
    return InlineKeyboardMarkup([r for r in keyboard if r])


def decorate_help_text(text):
    """/help message frame for the saved Help theme (classic = unchanged). Never raises."""
    try:
        return _frame(text, _preset(_saved.get("theme"), "help"))
    except Exception:
        return text


async def send_start(update, context):
    """
    Called by /start. Returns False when nothing is customized (the original code then runs unchanged) or when the
    customized message could not be sent at all; True once the customized /start has been delivered.
    """
    if not any(s in _saved for s in START_SECTIONS):
        return False
    msg, user = update.effective_message, update.effective_user
    if msg is None or user is None:
        return False
    photo_sent = False
    try:
        text, custom = start_text_for(_saved.get("welcome"), _saved.get("theme"), user)   # greeting + {first}, {name}, ... filled in
        header = _deps.get("add_header")
        if header and not custom:       # a custom welcome already greets the user by name: no second "👤 Name" line
            text = header(msg, text)
        keyboard = start_keyboard_for(user.id, _saved.get("buttons"), _links_saved(), _saved.get("theme"),
                                      bot_username=getattr(msg.get_bot(), "username", None))
        parse = "HTML" if custom else None
        bot, chat_id = msg.get_bot(), msg.chat_id
        banner = _saved.get("banner")
        if banner and banner.get("file_id"):
            try:
                if len(text) <= CAPTION_LIMIT:
                    await bot.send_photo(chat_id=chat_id, photo=banner["file_id"], caption=text, parse_mode=parse,
                                         reply_markup=keyboard)
                    return True
                await bot.send_photo(chat_id=chat_id, photo=banner["file_id"])
                photo_sent = True
            except Exception as e:      # missing/invalid file id: fall back to the normal text-only /start
                logger.warning("custom banner could not be sent: %s", e)
        await bot.send_message(chat_id=chat_id, text=text, parse_mode=parse, reply_markup=keyboard, **_nopreview())
        return True
    except Exception as e:
        logger.error("customized /start failed: %s", e)
        return photo_sent


async def links_callback(update, context):
    """Public (any user): the Channel / Group / Website button on /start -> a list of every link saved under it."""
    q = update.callback_query
    if q is None or q.message is None:
        return
    parts = (q.data or "").split(":")
    action = parts[1] if len(parts) > 1 else ""
    try:
        if action == "close":
            await q.answer()
            await q.message.delete()
            return
        if action not in LINK_SLOTS:
            await q.answer()
            return
        entries = _slot_links(_links_saved(), action)
        if not entries:
            await q.answer(f"No {LINK_PLURAL[action].lower()} have been added yet.", show_alert=True)
            return
        from telegram import InlineKeyboardButton, InlineKeyboardMarkup
        rows = [[InlineKeyboardButton(e["label"], url=e["url"])] for e in entries]
        rows.append([InlineKeyboardButton("✖️ Close", callback_data="tlinks:close")])
        await q.answer()
        await q.message.reply_text(f"{LINK_LABELS[action]}\n\nChoose one:", reply_markup=InlineKeyboardMarkup(rows), **_nopreview())
    except Exception as e:
        logger.info("links list failed: %s", e)
        try:
            await q.answer()
        except Exception:
            pass


async def details_callback(update, context):
    """Public (any user): the Details button on /start shows the About text the Owner saved."""
    q = update.callback_query
    if q is None or q.message is None:
        return
    value = _saved.get("about")
    try:
        if not (value and value.get("text")):
            await q.answer("No details have been added yet.", show_alert=True)
            return
        await q.answer()
        text = render_user_text(value["text"], q.from_user)
        try:
            await q.message.reply_text(text, parse_mode="HTML", **_nopreview())
        except Exception as e:
            logger.warning("Details text could not be sent as HTML: %s", e)
            await q.message.reply_text(html.unescape(re.sub(r"<[^>]+>", "", text)))
    except Exception as e:
        logger.info("details failed: %s", e)


async def about_command(update, context):
    msg = update.effective_message
    if msg is None:
        return
    value = _saved.get("about")
    if not (value and value.get("text")):
        await msg.reply_text("ℹ️ The About section has not been set up yet.")
        return
    text = render_user_text(value["text"], update.effective_user)
    header = _deps.get("add_header")
    try:
        await msg.reply_text(header(msg, text) if header else text, parse_mode="HTML", **_nopreview())
    except Exception as e:
        logger.warning("About text could not be sent as HTML: %s", e)
        await msg.reply_text(html.unescape(re.sub(r"<[^>]+>", "", text)))


# --------------------------------------------------------------------------------------------- keyboards / panels
def _cb(uid, section, action, arg=""):
    return f"theme:{uid}:{section}:{action}" + (f":{arg}" if arg else "")


def _markup(uid, rows):
    """rows: [[(label, section, action[, arg]), ...], ...] -> InlineKeyboardMarkup. A back row has exactly one button."""
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    out = []
    for row in rows:
        out.append([InlineKeyboardButton(b[0], callback_data=_cb(uid, *b[1:])) for b in row])
    return InlineKeyboardMarkup(out)


def _back(section="hub"):
    return [("↩️ Back", section, "open")]


def _owner_menu_back(uid):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    return InlineKeyboardButton("↩️ Back", callback_data=f"help:{uid}:owner")     # returns to the Owner Commands grid


def hub_view(uid):
    from telegram import InlineKeyboardMarkup
    base = _markup(uid, [
        [("📝 Welcome", "welcome", "open"), ("🖼️ Banner", "banner", "open")],
        [("🔘 Start Menu", "buttons", "open"), ("📖 About Bot", "about", "open")],
        [("🔗 Links", "links", "open"), ("🎭 Theme", "theme", "open")],
        [("📄 Description", "description", "open")],
    ])
    rows = list(base.inline_keyboard) + [[_owner_menu_back(uid)]]
    unsaved = sorted(s for s in SECTIONS if (uid, s) in _drafts)
    note = f"\n\n✏️ Unsaved changes in: {', '.join(unsaved)}" if unsaved else ""
    return ("🎨 Customize Bot\n\nChoose what to customize. Every section has its own Save and Reset; "
            "nothing changes for users until you press 💾 Save." + note), InlineKeyboardMarkup(rows)


def _status(uid, section):
    saved = "customized" if section in _saved else "default"
    pending = "✏️ unsaved changes" if (uid, section) in _drafts else "none"
    return f"Saved: {saved}\nPending: {pending}"


def panel_view(uid, section, notice=""):
    pre = (notice + "\n\n") if notice else ""
    if section == "welcome":
        text = (f"{pre}📝 Welcome Message\n\nThe text of your /start message (Telegram HTML is supported).\n\n{_status(uid, section)}")
        rows = [[("✏️ Edit", section, "edit"), ("👁️ Preview", section, "preview")],
                [("♻️ Reset", section, "reset"), ("💾 Save", section, "save")], _back()]
    elif section == "about":
        text = (f"{pre}📖 About Bot\n\nThe text shown by /about (Telegram HTML is supported).\n\n{_status(uid, section)}")
        rows = [[("✏️ Edit About", section, "edit"), ("👁️ Preview", section, "preview")],
                [("♻️ Reset", section, "reset"), ("💾 Save", section, "save")], _back()]
    elif section == "banner":
        d = _draft(uid, "banner")
        state = ("removal pending" if d and d.get("removed") else "new image pending" if d else "none")
        has = "custom banner" if _saved.get("banner") else "none (text-only /start)"
        text = (f"{pre}🖼️ Bot Banner\n\nAn image shown with your /start message.\n\nSaved banner: {has}\nPending: {state}")
        rows = [[("📤 Upload Banner", section, "upload"), ("👁️ Preview", section, "preview")],
                [("🗑️ Remove Banner", section, "remove"), ("♻️ Reset", section, "reset")],
                [("💾 Save", section, "save")], _back()]
    elif section == "buttons":
        items = _button_items(_draft(uid, "buttons") or _saved.get("buttons"))
        notes = {"help": " (opens the Help menu)", "addgroup": " (add-to-group link, automatic)", "details": " (shows your About text)"}
        listing = "\n".join(f"{n}. {i['label']}" + (notes[i["kind"]] if i["kind"] in notes else f" → {i['url']}")
                            for n, i in enumerate(items, 1))
        text = (f"{pre}🔘 Start Menu Buttons\n\nButtons on your /start message:\n{listing}\n\n"
                f"👉 Use 🧩 Layout to choose how many buttons are in each row and which row is on top.\n\n{_status(uid, section)}")
        rows = [[("🧩 Layout (rows and order)", section, "layout")],
                [("➕ Add Button", section, "add"), ("✏️ Edit Button", section, "edit")],
                [("🗑️ Delete Button", section, "delete"), ("↕️ Reorder Buttons", section, "reorder")],
                [("👁️ Preview", section, "preview"), ("♻️ Reset", section, "reset")],
                [("💾 Save", section, "save")], _back()]
    elif section == "links":
        links = _effective_links(uid)
        parts = []
        for s_ in LINK_SLOTS:
            entries = _slot_links(links, s_)
            parts.append(f"{LINK_LABELS[s_]}: " + (", ".join(e["label"] for e in entries) if entries else "none"))
        listing = "\n".join(parts)
        text = (f"{pre}🔗 Bot Links\n\nAdd several channels, groups or websites (up to {MAX_LINKS_PER_SLOT} each). /start shows ONE "
                f"Channel button and ONE Group button; tapping it opens the list of everything you add here.\n\n{listing}\n\n{_status(uid, section)}")
        rows = [[("➕ Add Channel", section, "setchannel"), ("➕ Add Group", section, "setgroup")],
                [("➕ Add Website/Social", section, "setwebsite"), ("🗑️ Remove Link", section, "remove")],
                [("👁️ Preview Links", section, "preview"), ("♻️ Reset", section, "reset")],
                [("💾 Save", section, "save")], _back()]
    elif section == "description":
        text = (f"{pre}📄 Bot Description\n\nThe text shown in the \"Description\" row of your bot's profile page "
                f"(plain text, {MIN_DESC}-{MAX_DESC} characters). The same text is also shown on the empty chat screen "
                f"before someone presses Start.\n\n{_description_summary(uid)}\n\n{_status(uid, section)}")
        rows = [[("✏️ Edit", section, "edit"), ("👁️ Preview", section, "preview")],
                [("♻️ Reset", section, "reset"), ("💾 Save", section, "save")], _back()]
    else:  # theme
        t = _draft(uid, "theme") or _saved.get("theme") or {}
        text = (f"{pre}🎭 Bot Theme\n\nOnly /start and /help are themed. Telegram does not allow custom button colours, "
                f"so themes are ready-made presets.\n\n🌸 Start menu: {_preset(t, 'start')['name']}\n"
                f"📚 Help menu: {_preset(t, 'help')['name']}\n\n{_status(uid, section)}")
        rows = [[("🌸 Start Menu Theme", section, "pickstart"), ("📚 Help Menu Theme", section, "pickhelp")],
                [("👁️ Preview", section, "preview"), ("♻️ Reset", section, "reset")],
                [("💾 Save", section, "save")], _back()]
    return text, _markup(uid, rows)


def _links_saved():
    """The links users see: the saved ones, or the ready-made defaults until the Owner saves their own."""
    value = _saved.get("links")
    return copy.deepcopy(DEFAULT_LINKS) if value is None else value


def _effective_links(uid):
    d = _draft(uid, "links")
    return d if d is not None else _links_saved()


def _confirm_view(uid, section, op, question, arg=None):
    nonce = _make_confirm(uid, section, op, arg)
    rows = [[("✅ Yes", section, f"{op}ok", nonce), ("❌ Cancel", section, "open")]]
    return question, _markup(uid, rows)


def _prompt_view(uid, section, text):
    return text, _markup(uid, [[("❌ Cancel", section, "cancel")]])


# --------------------------------------------------------------------------------------------- telegram helpers
async def _answer(q, text=None, alert=False):
    try:
        await q.answer(text, show_alert=alert)
    except Exception:
        pass


async def _show(q, text, markup):
    """Edit the panel message; if Telegram refuses (e.g. nothing changed) fall back quietly."""
    try:
        await q.edit_message_text(_panel_html(text), parse_mode="HTML", reply_markup=markup, **_nopreview())
    except Exception as e:
        if "not modified" not in str(e).lower():
            logger.info("panel edit failed, sending a new message: %s", e)
            try:
                await q.message.reply_text(_panel_html(text), parse_mode="HTML", reply_markup=markup, **_nopreview())
            except Exception as e2:
                logger.warning("panel send failed: %s", e2)


async def _send_panel(message, uid, section, notice=""):
    text, markup = hub_view(uid) if section == "hub" else panel_view(uid, section, notice)
    await message.reply_text(_panel_html(text), parse_mode="HTML", reply_markup=markup, **_nopreview())


async def _send_html(message, text, markup=None, prefix=""):
    """Preview/send Telegram-HTML text; a parse error is reported instead of crashing."""
    try:
        await message.reply_text(prefix + text, parse_mode="HTML", reply_markup=markup, **_nopreview())
        return True
    except Exception as e:
        logger.info("html preview failed: %s", e)
        await message.reply_text("⚠️ Telegram could not display this text. Edit it and check the formatting.")
        return False


# --------------------------------------------------------------------------------------------- callbacks
async def theme_callback(update, context):
    q = update.callback_query
    if q is None or q.from_user is None:
        return
    try:
        parts = (q.data or "").split(":", 4)
        if len(parts) < 4 or parts[0] != "theme" or not parts[1].isdigit():
            await _answer(q)
            return
        owner, section, action = int(parts[1]), parts[2], parts[3]
        arg = parts[4] if len(parts) > 4 else ""
        if q.from_user.id != owner:                         # a menu opened by someone else
            await _answer(q, NOT_YOURS_TEXT, True)
            return
        if not _is_owner(q.from_user.id):                   # the real owner check (never the id in the button)
            _awaiting.pop(q.from_user.id, None)
            await _answer(q, DENIED_TEXT, True)
            return
        chat = getattr(q.message, "chat", None)
        if chat is not None and getattr(chat, "type", "private") != "private":
            await _answer(q, "Open the customization menu in the bot's private chat.", True)
            return
        await _dispatch(q, context, owner, section, action, arg)
    except Exception as e:
        logger.error("theme callback failed: %s", e)
        await _answer(q, "⚠️ Something went wrong. Please reopen the menu.", True)


async def _dispatch(q, context, uid, section, action, arg):
    if section == "noop":
        await _answer(q, "👁 Preview only - this button is not active here.")
        return
    if section == "hub":
        _awaiting.pop(uid, None)
        await _answer(q)
        text, markup = hub_view(uid)
        await _show(q, text, markup)
        return
    if section not in SECTIONS:
        await _answer(q, STALE_TEXT, True)
        return

    if action == "open":
        _awaiting.pop(uid, None)
        await _answer(q)
        await _show(q, *panel_view(uid, section))
        return
    if action == "cancel":                       # leaves the saved settings AND the pending draft untouched
        _awaiting.pop(uid, None)
        await _answer(q, "Cancelled.")
        await _show(q, *panel_view(uid, section))
        return

    handler = _SECTION_HANDLERS[section]
    await handler(q, context, uid, action, arg)


# ---- shared: reset / save ----------------------------------------------------------------------------
async def _ask_reset(q, uid, section, what):
    await _answer(q)
    await _show(q, *_confirm_view(uid, section, "reset", f"♻️ Reset {what} to the default?\n\nThis removes your saved customization "
                                                        "for this section only."))


async def _do_reset(q, uid, section, arg, what):
    if _pop_confirm(arg, uid, section, "reset") is None:
        await _answer(q, STALE_TEXT, True)
        return
    if await _persist(section, None):
        _clear_draft(uid, section)
        await _answer(q, "♻️ Reset.")
        await _show(q, *panel_view(uid, section, f"✅ {what} was reset to the default."))
    else:
        await _answer(q, "❌ Could not reset (database problem). Nothing was changed.", True)


async def _do_save(q, uid, section, value_fn=None):
    draft = _draft(uid, section)
    if draft is None:
        await _answer(q, "Nothing to save - there are no pending changes.", True)
        return
    value = value_fn(draft) if value_fn else draft
    if await _persist(section, value):
        _clear_draft(uid, section)
        await _answer(q, "💾 Saved.")
        await _show(q, *panel_view(uid, section, "✅ Saved."))
    else:
        await _answer(q, "❌ Could not save (database problem). Your pending changes were kept - try again.", True)


# ---- welcome / about (text sections) -----------------------------------------------------------------------
_TEXT_COPY = {
    "welcome": ("welcome message", "Send the new WELCOME MESSAGE for /start.", "Welcome message"),
    "about": ("About text", "Send the new ABOUT text (shown by /about).", "About text"),
}


async def _text_section(q, context, uid, action, arg):
    section = q.data.split(":")[2]
    what, prompt, title = _TEXT_COPY[section]
    if action == "edit":
        _set_await(uid, section, "text")
        await _answer(q)
        await _show(q, *_prompt_view(uid, section, f"✏️ {prompt}\n\nJust paste your message - the formatting you apply in Telegram "
                                                  f"(bold, italic, links) is kept, and plain text is shown exactly as you wrote it.\n\n"
                                                  "✅ The greeting with each user's Telegram name (HEY <name>!) is added automatically - do NOT type it. "
                                                  "Paste only the rest of the message.\n\n"
                                                  "Optional: to place a name yourself, write {first} • {name} • {username} • {mention} • {id} "
                                                  "(then the automatic greeting is skipped).\n\n"
                                                  f"Up to {MAX_TEXT} characters. Tap Cancel to keep things as they are."))
    elif action == "preview":
        await _answer(q)
        draft = _draft(uid, section) or _saved.get(section)
        if section == "welcome":
            text, custom = start_text_for(draft, (_draft(uid, "theme") or _saved.get("theme")), q.from_user)
            text = text if custom else html.escape(text)
            await _send_html(q.message, text, prefix="👁 Preview (not saved)\n\n")
        elif draft and draft.get("text"):
            await _send_html(q.message, render_user_text(draft["text"], q.from_user), prefix="👁 Preview (not saved)\n\n")
        else:
            await q.message.reply_text("👁 Preview: the About section has not been set up yet (default).")
    elif action == "reset":
        await _ask_reset(q, uid, section, what)
    elif action == "resetok":
        await _do_reset(q, uid, section, arg, title)
    elif action == "save":
        await _do_save(q, uid, section)
    else:
        await _answer(q, STALE_TEXT, True)


async def _input_text(message, uid, section, st):
    text, error = validate_text(getattr(message, "text_html", None) or message.text)
    if error:
        await message.reply_text(f"❌ {error}\n\nYour saved version is unchanged. Send the text again, or tap Cancel on the "
                                 "message above.")
        return
    _set_draft(uid, section, {"text": text})
    _awaiting.pop(uid, None)
    await _send_panel(message, uid, section, "✏️ Pending change recorded (not saved yet). Use 👁️ Preview, then 💾 Save.")


# ---- banner ----------------------------------------------------------------------------------------------
async def _banner_section(q, context, uid, action, arg):
    section = "banner"
    if action == "upload":
        _set_await(uid, section, "photo")
        await _answer(q)
        await _show(q, *_prompt_view(uid, section, "📤 Send the banner image as a PHOTO (not as a file). Telegram photos only; "
                                                  "max 10 MB.\n\nTap Cancel to keep the current banner."))
    elif action == "preview":
        await _answer(q)
        d = _draft(uid, section)
        if d and d.get("removed"):
            await q.message.reply_text("👁 Preview: the banner will be removed (text-only /start) once you Save.")
            return
        banner = d or _saved.get(section)
        if not banner or not banner.get("file_id"):
            await q.message.reply_text("👁 Preview: no custom banner is set (text-only /start, the default).")
            return
        try:
            await q.message.reply_photo(photo=banner["file_id"], caption="👁 Banner preview" + ("" if d else " (saved)") +
                                                                       (" - not saved yet" if d else ""))
        except Exception as e:
            logger.info("banner preview failed: %s", e)
            await q.message.reply_text("⚠️ This image is no longer available. Please upload it again.")
    elif action == "remove":
        if not (_draft(uid, section) or _saved.get(section)) or (_draft(uid, section) or {}).get("removed"):
            await _answer(q, "There is no custom banner to remove.", True)
            return
        await _answer(q)
        await _show(q, *_confirm_view(uid, section, "remove", "🗑️ Remove the custom banner?\n\nIt is only removed after you "
                                                              "press 💾 Save."))
    elif action == "removeok":
        if _pop_confirm(arg, uid, section, "remove") is None:
            await _answer(q, STALE_TEXT, True)
            return
        _set_draft(uid, section, {"removed": True})
        await _answer(q, "Removal staged.")
        await _show(q, *panel_view(uid, section, "✏️ Banner removal is pending - press 💾 Save to apply it."))
    elif action == "reset":
        await _ask_reset(q, uid, section, "the banner")
    elif action == "resetok":
        await _do_reset(q, uid, section, arg, "The banner")
    elif action == "save":
        d = _draft(uid, section)
        if d is None:
            await _answer(q, "Nothing to save - there are no pending changes.", True)
            return
        await _do_save(q, uid, section, lambda draft: None if draft.get("removed") else
                       {"file_id": draft["file_id"], "unique_id": draft.get("unique_id", "")})
    else:
        await _answer(q, STALE_TEXT, True)


async def _input_banner(message, uid, section, st):
    if getattr(message, "photo", None):
        photo = message.photo[-1]
        size = getattr(photo, "file_size", None)
        if size and size > MAX_PHOTO_BYTES:
            await message.reply_text(f"❌ That image is {size // (1024 * 1024)} MB; the limit is 10 MB. Send a smaller photo.")
            return
        _set_draft(uid, section, {"file_id": photo.file_id, "unique_id": getattr(photo, "file_unique_id", "")})
        _awaiting.pop(uid, None)
        await _send_panel(message, uid, section, "✏️ New banner recorded (not saved yet). Use 👁️ Preview, then 💾 Save.")
        return
    if getattr(message, "document", None):
        await message.reply_text("❌ Please send the image as a PHOTO (compressed), not as a file or document. "
                                 "Files of other types are not accepted.")
        return
    await message.reply_text("❌ That is not an image. Send a photo, or tap Cancel on the message above.")


# ---- start menu buttons -----------------------------------------------------------------------------------
def _working_buttons(uid):
    d = _draft(uid, "buttons")
    return d["items"] if d is not None else _button_items(_saved.get("buttons"))


def _working_layout(uid):
    value = _draft(uid, "buttons") or _saved.get("buttons") or {}
    return _resolve_layout(_working_buttons(uid), _effective_links(uid), value.get("layout"))


def _working_value(uid):
    """The buttons value as it is right now (pending changes included), for previews."""
    return {"items": _working_buttons(uid), "layout": _working_layout(uid)}


def _commit_buttons(uid, items):
    _set_draft(uid, "buttons", {"items": items, "layout": _working_layout(uid)})


def _commit_layout(uid, layout):
    _set_draft(uid, "buttons", {"items": _working_buttons(uid), "layout": layout})


def _next_button_id(items):
    nums = [int(i["id"][1:]) for i in items if re.fullmatch(r"b\d+", str(i.get("id", "")))]
    return f"b{(max(nums) if nums else 0) + 1}"


def _pick_view(uid, section, action_prefix, title, items, note=""):
    rows = [[(f"{n}. {i['label']}"[:60], section, action_prefix, i["id"])] for n, i in enumerate(items, 1)]
    rows.append(_back(section))
    return (f"{title}{note}", _markup(uid, rows))


_layout_sel = {}          # owner id -> the button currently selected in the Layout screen

LAYOUT_GUIDE = (
    "📘 How to arrange your /start buttons\n\n"
    "Each line of buttons is a ROW. A row with one button is full width; with two or more they share the width.\n\n"
    "1️⃣ Tap a button name to select it (it gets a 👉).\n"
    "2️⃣ Use ⬆️ Row up / ⬇️ Row down to move its whole row higher or lower.\n"
    "3️⃣ Use ◀️ Left / ▶️ Right to change its place inside the row.\n"
    "4️⃣ Tap ⬛ Own row to make it full width on a new row.\n"
    "5️⃣ Tap 🔗 Join row above to put it side by side with the row above (up to " + str(MAX_PER_ROW) + " per row).\n\n"
    "⚡ Shortcut: 1 / 2 / 3 per row re-arranges everything at once, then fine-tune it with the steps above.\n"
    "♻️ Default layout goes back to: Add me to group, then Help + Details, then Group + Channel.\n\n"
    "Finish: tap 👁️ Preview to see exactly what users get, then 💾 Save. Nothing changes for users until you Save."
)


def _element_labels(uid):
    labels = {i["id"]: i["label"] for i in _working_buttons(uid)}
    for slot in LINK_SLOTS:
        labels[f"link_{slot}"] = LINK_LABELS[slot]
    return labels


def _layout_view(uid, notice=""):
    layout = _working_layout(uid)
    labels = _element_labels(uid)
    sel = _layout_sel.get(uid)
    if not any(sel in row for row in layout):
        sel = _layout_sel.pop(uid, None) and None
    lines = "\n".join(f"Row {n}: " + "  |  ".join(labels.get(e, e) for e in row) for n, row in enumerate(layout, 1))
    if sel:
        step = f"Selected: {labels.get(sel, sel)}\nStep 2: move it with the arrows below, or tap it again to unselect."
    else:
        step = "Step 1: tap a button below to select it. Not sure how? Tap 📘 How to use."
    text = ((notice + "\n\n") if notice else "") + f"🧩 Button Layout\n\nThis is how /start looks now:\n{lines}\n\n{step}\n\n{_status(uid, 'buttons')}"
    rows = [[((("👉 " if e == sel else "") + labels.get(e, e))[:30], "buttons", "lsel", e) for e in row] for row in layout]
    if sel:
        rows += [[("⬆️ Row up", "buttons", "lup"), ("⬇️ Row down", "buttons", "ldn")],
                 [("◀️ Left", "buttons", "lleft"), ("▶️ Right", "buttons", "lright")],
                 [("⬛ Own row", "buttons", "lalone"), ("🔗 Join row above", "buttons", "ljoin")]]
    rows += [[("1 per row", "buttons", "lp1"), ("2 per row", "buttons", "lp2"), ("3 per row", "buttons", "lp3")],
             [("📘 How to use", "buttons", "lguide"), ("♻️ Default layout", "buttons", "lreset")],
             [("👁️ Preview", "buttons", "preview"), ("💾 Save", "buttons", "save")],
             [("↩️ Back", "buttons", "open")]]
    return text, _markup(uid, rows)


async def _layout_action(q, uid, action, arg):
    if action == "layout":
        await _answer(q)
        await _show(q, *_layout_view(uid))
        return
    if action == "lguide":
        await _answer(q)
        await _show(q, LAYOUT_GUIDE, _markup(uid, [[("↩️ Back to Layout", "buttons", "layout")]]))
        return
    layout = [list(r) for r in _working_layout(uid)]
    sel = _layout_sel.get(uid)
    hint = " Move more, or tap 👁️ Preview, then 💾 Save."
    if action == "lsel":
        if arg == sel:
            _layout_sel.pop(uid, None)
        else:
            _layout_sel[uid] = arg
        await _answer(q)
        await _show(q, *_layout_view(uid))
        return
    if action in ("lp1", "lp2", "lp3"):
        n = int(action[2])
        flat = [e for row in layout for e in row]
        layout = [flat[k:k + n] for k in range(0, len(flat), n)]
        notice = f"✅ Now {n} per row." + hint
    elif action == "lreset":
        layout = _resolve_layout(_working_buttons(uid), _effective_links(uid), None)
        _layout_sel.pop(uid, None)
        notice = "✅ Default layout restored." + hint
    else:
        pos = next(((r, row.index(sel)) for r, row in enumerate(layout) if sel in row), None) if sel else None
        if pos is None:
            await _answer(q, "Step 1: tap a button name first, then use the arrows.", True)
            return
        r, c = pos
        row = layout[r]
        if action in ("lup", "ldn"):
            j = r - 1 if action == "lup" else r + 1
            if not 0 <= j < len(layout):
                await _answer(q, "That row is already at the " + ("top." if action == "lup" else "bottom."), True)
                return
            layout[r], layout[j] = layout[j], layout[r]
            notice = "✅ Row moved." + hint
        elif action in ("lleft", "lright"):
            j = c - 1 if action == "lleft" else c + 1
            if not 0 <= j < len(row):
                await _answer(q, "It is already the " + ("first" if action == "lleft" else "last") + " button in its row.", True)
                return
            row[c], row[j] = row[j], row[c]
            notice = "✅ Button moved." + hint
        elif action == "lalone":
            if len(row) == 1:
                await _answer(q, "It is already alone on its row (full width).", True)
                return
            row.remove(sel)
            layout.insert(r + 1, [sel])
            notice = "✅ Now on its own row (full width)." + hint
        elif action == "ljoin":
            if r == 0:
                await _answer(q, "There is no row above. Move it down first, or use ⬆️ Row up on another row.", True)
                return
            if len(layout[r - 1]) >= MAX_PER_ROW:
                await _answer(q, f"The row above is full ({MAX_PER_ROW} buttons). Move one of them to another row first.", True)
                return
            row.remove(sel)
            layout[r - 1].append(sel)
            layout = [x for x in layout if x]
            notice = "✅ Joined the row above." + hint
        else:
            await _answer(q, STALE_TEXT, True)
            return
    _commit_layout(uid, layout)
    await _answer(q)
    await _show(q, *_layout_view(uid, notice))


def _reorder_view(uid):
    items = _working_buttons(uid)
    rows = []
    for n, i in enumerate(items, 1):
        rows.append([(f"{n}. {i['label']}"[:40], "buttons", "noopx"), ("⬆️", "buttons", "up", i["id"]),
                     ("⬇️", "buttons", "down", i["id"])])
    rows.append(_back("buttons"))
    return "↕️ Reorder Buttons\n\nUse ⬆️ / ⬇️ to move a button. Changes are pending until you press 💾 Save.", _markup(uid, rows)


async def _buttons_section(q, context, uid, action, arg):
    section = "buttons"
    if action in ("layout", "lguide", "lsel", "lup", "ldn", "lleft", "lright", "lalone", "ljoin", "lp1", "lp2", "lp3", "lreset"):
        await _layout_action(q, uid, action, arg)
        return
    items = _working_buttons(uid)
    if action == "add":
        if len(items) >= MAX_BUTTONS:
            await _answer(q, f"You can have at most {MAX_BUTTONS} buttons.", True)
            return
        _set_await(uid, section, "add_auto")
        await _answer(q)
        await _show(q, *_prompt_view(uid, section, "➕ Send the https:// link for the new button (for Telegram: https://t.me/...).\n\n"
                                                  "For a public channel or group the button is named automatically with its real "
                                                  "name. For other links I will ask you for a name.\n\n"
                                                  "The button opens a link; it cannot run bot commands."))
    elif action == "edit":
        await _answer(q)
        await _show(q, *_pick_view(uid, section, "editsel", "✏️ Edit Button\n\nChoose the button to edit.", items))
    elif action == "editsel":
        item = next((i for i in items if i["id"] == arg), None)
        if not item:
            await _answer(q, STALE_TEXT, True)
            return
        _set_await(uid, section, "edit_label", {"id": arg})
        await _answer(q)
        from telegram import InlineKeyboardButton, InlineKeyboardMarkup
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("⏭ Keep current", callback_data=_cb(uid, section, "skip"))],
                                   [InlineKeyboardButton("❌ Cancel", callback_data=_cb(uid, section, "cancel"))]])
        await _show(q, f"✏️ Send the new label (current: {item['label']}).", kb)
    elif action == "skip":
        st = _awaiting_state(uid)
        if not st or st["section"] != section or st["field"] not in ("edit_label", "edit_url"):
            await _answer(q, STALE_TEXT, True)
            return
        await _answer(q)
        await _advance_edit(q.message, uid, st, label=None, url=None, via_query=q)
    elif action == "delete":
        custom = [i for i in items if i["kind"] != "help"]
        if not custom:
            await _answer(q, "There are no custom buttons to delete (📖 Help is built in).", True)
            return
        await _answer(q)
        await _show(q, *_pick_view(uid, section, "delsel", "🗑️ Delete Button\n\nChoose the button to delete.", custom))
    elif action == "delsel":
        item = next((i for i in items if i["id"] == arg and i["kind"] != "help"), None)
        if not item:
            await _answer(q, STALE_TEXT, True)
            return
        await _answer(q)
        await _show(q, *_confirm_view(uid, section, "delete", f"🗑️ Delete the button “{item['label']}”?", arg))
    elif action == "deleteok":
        c = _pop_confirm(arg, uid, section, "delete")
        if c is None:
            await _answer(q, STALE_TEXT, True)
            return
        _commit_buttons(uid, [i for i in items if not (i["id"] == c["arg"] and i["kind"] != "help")])
        await _answer(q, "Deleted (pending).")
        await _show(q, *panel_view(uid, section, "✏️ Button deleted - press 💾 Save to apply."))
    elif action == "reorder":
        if len(items) < 2:
            await _answer(q, "You need at least two buttons to reorder.", True)
            return
        await _answer(q)
        await _show(q, *_reorder_view(uid))
    elif action in ("up", "down"):
        idx = next((n for n, i in enumerate(items) if i["id"] == arg), None)
        if idx is None:
            await _answer(q, STALE_TEXT, True)
            return
        j = idx - 1 if action == "up" else idx + 1
        if not (0 <= j < len(items)):
            await _answer(q, "Already at the edge.")
            return
        items[idx], items[j] = items[j], items[idx]
        _commit_buttons(uid, items)
        await _answer(q)
        await _show(q, *_reorder_view(uid))
    elif action == "noopx":
        await _answer(q)
    elif action == "preview":
        await _answer(q)
        theme_value = _draft(uid, "theme") or _saved.get("theme")
        text, custom = start_text_for(_draft(uid, "welcome") or _saved.get("welcome"), theme_value, q.from_user)
        kb = start_keyboard_for(uid, _working_value(uid), _effective_links(uid), theme_value, preview=True,
                                bot_username=getattr(q.message.get_bot(), "username", None))
        try:
            await q.message.reply_text("👁 Preview (not saved)\n\n" + (text if custom else html.escape(text)),
                                       parse_mode="HTML", reply_markup=kb, **_nopreview())
        except Exception as e:
            logger.info("start preview failed: %s", e)
            await q.message.reply_text("⚠️ Telegram could not display the preview. Check the welcome text formatting.")
    elif action == "reset":
        await _ask_reset(q, uid, section, "the start menu buttons")
    elif action == "resetok":
        await _do_reset(q, uid, section, arg, "The start menu buttons")
    elif action == "save":
        await _do_save(q, uid, section, lambda d: {"items": d["items"], "layout": d.get("layout") if d.get("layout") is not None
                                                  else _resolve_layout(d["items"], _links_saved(), None)})
    else:
        await _answer(q, STALE_TEXT, True)


async def _advance_edit(message, uid, st, label, url, via_query=None):
    """Edit-button flow: label step -> (url step for link buttons) -> apply to the draft."""
    extra = st["extra"]
    if label is not None:
        extra["label"] = label
    item = next((i for i in _working_buttons(uid) if i["id"] == extra.get("id")), None)
    if item is None:
        _awaiting.pop(uid, None)
        await message.reply_text("⚠️ That button no longer exists.")
        return
    if st["field"] == "edit_label" and item["kind"] == "url":
        st["field"] = "edit_url"
        st["ts"] = _now()
        from telegram import InlineKeyboardButton, InlineKeyboardMarkup
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("⏭ Keep current", callback_data=_cb(uid, "buttons", "skip"))],
                                   [InlineKeyboardButton("❌ Cancel", callback_data=_cb(uid, "buttons", "cancel"))]])
        text = f"🔗 Send the new https:// link (current: {item['url']})."
        if via_query is not None:
            await _show(via_query, text, kb)
        else:
            await message.reply_text(_panel_html(text), parse_mode="HTML", reply_markup=kb, **_nopreview())
        return
    items = _working_buttons(uid)
    for i in items:
        if i["id"] == item["id"]:
            if extra.get("label"):
                i["label"] = extra["label"]
            if url and i["kind"] == "url":
                i["url"] = url
    _commit_buttons(uid, items)
    _awaiting.pop(uid, None)
    notice = "✏️ Button updated (not saved yet) - press 💾 Save to apply."
    if via_query is not None:
        await _show(via_query, *panel_view(uid, "buttons", notice))
    else:
        await _send_panel(message, uid, "buttons", notice)


async def _input_buttons(message, uid, section, st):
    field = st["field"]
    if field == "add_auto":
        url, error = validate_url(message.text)
        if error:
            await message.reply_text(f"❌ {error}\n\nSend a valid link, or tap Cancel above.")
            return
        items = _working_buttons(uid)
        if len(items) >= MAX_BUTTONS:
            _awaiting.pop(uid, None)
            await message.reply_text(f"❌ You can have at most {MAX_BUTTONS} buttons.")
            return
        title = await _link_title(message.get_bot(), url)
        if title:
            items.append({"id": _next_button_id(items), "kind": "url", "label": title, "url": url})
            _commit_buttons(uid, items)
            _awaiting.pop(uid, None)
            await _send_panel(message, uid, section, f"✏️ Button “{title}” added (not saved yet) - press 💾 Save to apply.")
            return
        st["extra"]["url"], st["field"], st["ts"] = url, "add_name", _now()
        await message.reply_text("✍️ I could not read a name from that link. Send the NAME for this button "
                                 f"(up to {MAX_LABEL} characters, emoji allowed).",
                                 reply_markup=_markup(uid, [[("❌ Cancel", section, "cancel")]]))
        return
    if field == "add_name":
        label, error = validate_label(message.text)
        if error:
            await message.reply_text(f"❌ {error}")
            return
        items = _working_buttons(uid)
        items.append({"id": _next_button_id(items), "kind": "url", "label": label, "url": st["extra"]["url"]})
        _commit_buttons(uid, items)
        _awaiting.pop(uid, None)
        await _send_panel(message, uid, section, "✏️ Button added (not saved yet) - press 💾 Save to apply.")
        return
    if field in ("add_label", "edit_label"):
        label, error = validate_label(message.text)
        if error:
            await message.reply_text(f"❌ {error}")
            return
        if field == "add_label":
            st["extra"]["label"], st["field"], st["ts"] = label, "add_url", _now()
            await message.reply_text("🔗 Now send the https:// link this button should open (for Telegram: https://t.me/...).",
                                     reply_markup=_markup(uid, [[("❌ Cancel", section, "cancel")]]))
            return
        await _advance_edit(message, uid, st, label=label, url=None)
        return
    url, error = validate_url(message.text)
    if error:
        await message.reply_text(f"❌ {error}\n\nYour saved buttons are unchanged. Send a valid link, or tap Cancel above.")
        return
    if field == "add_url":
        items = _working_buttons(uid)
        if len(items) >= MAX_BUTTONS:
            _awaiting.pop(uid, None)
            await message.reply_text(f"❌ You can have at most {MAX_BUTTONS} buttons.")
            return
        items.append({"id": _next_button_id(items), "kind": "url", "label": st["extra"]["label"], "url": url})
        _commit_buttons(uid, items)
        _awaiting.pop(uid, None)
        await _send_panel(message, uid, section, "✏️ Button added (not saved yet) - press 💾 Save to apply.")
        return
    await _advance_edit(message, uid, st, label=None, url=url)       # edit_url


# ---- links ---------------------------------------------------------------------------------------------
def _links_working(uid):
    """Draft-or-saved links normalised to {slot: [{"label","url"}]}."""
    links = _effective_links(uid)
    return {slot: _slot_links(links, slot) for slot in LINK_SLOTS}


async def _links_section(q, context, uid, action, arg):
    section = "links"
    if action in ("setchannel", "setgroup", "setwebsite"):
        slot = action[3:]
        if len(_links_working(uid)[slot]) >= MAX_LINKS_PER_SLOT:
            await _answer(q, f"You can have at most {MAX_LINKS_PER_SLOT} {LINK_WORDS[slot]} links.", True)
            return
        _set_await(uid, section, "url", {"slot": slot})
        await _answer(q)
        await _show(q, *_prompt_view(uid, section, f"➕ Add {LINK_WORDS[slot]}\n\nSend the https:// link (for Telegram: https://t.me/...).\n\n"
                                                  "For a public channel or group the button is named automatically with its real name. "
                                                  "For other links I will ask you for a name.\n\nYou can repeat this to add more."))
    elif action == "remove":
        work = _links_working(uid)
        rows = [[(f"🗑️ {LINK_WORDS[slot].split('/')[0]}: {e['label']}"[:60], section, "delsel", f"{slot}-{n}")]
                for slot in LINK_SLOTS for n, e in enumerate(work[slot])]
        if not rows:
            await _answer(q, "There are no links to remove.", True)
            return
        rows.append(_back(section))
        await _answer(q)
        await _show(q, "🗑️ Remove Link\n\nTap the link to remove it (pending until you press 💾 Save).", _markup(uid, rows))
    elif action == "delsel":
        slot, _, idx = (arg or "").partition("-")
        work = _links_working(uid)
        if slot not in work or not idx.isdigit() or int(idx) >= len(work[slot]):
            await _answer(q, STALE_TEXT, True)
            return
        work[slot].pop(int(idx))
        _set_draft(uid, section, work)
        await _answer(q, "Removed (pending).")
        await _show(q, *panel_view(uid, section, "✏️ Link removed (not saved yet) - press 💾 Save to apply."))
    elif action == "preview":
        await _answer(q)
        work = _links_working(uid)
        lines = ["👁 Links preview" + (" (not saved)" if (uid, section) in _drafts else "")]
        buttons = []
        from telegram import InlineKeyboardButton, InlineKeyboardMarkup
        for slot in LINK_SLOTS:
            if not work[slot]:
                lines.append(f"{LINK_LABELS[slot]}: none")
            for e in work[slot]:
                lines.append(f"{e['label']} → {e['url']}")
                buttons.append(InlineKeyboardButton(e["label"], url=e["url"]))
        await q.message.reply_text(_panel_html("\n".join(lines)), parse_mode="HTML",
                                   reply_markup=InlineKeyboardMarkup(_grid(buttons)) if buttons else None, **_nopreview())
    elif action == "reset":
        await _ask_reset(q, uid, section, "the links")
    elif action == "resetok":
        await _do_reset(q, uid, section, arg, "The links")
    elif action == "save":
        await _do_save(q, uid, section, lambda d: {k: [e for e in _slot_links(d, k)] for k in LINK_SLOTS if _slot_links(d, k)})
    else:
        await _answer(q, STALE_TEXT, True)


async def _input_link(message, uid, section, st):
    slot, field = st["extra"]["slot"], st["field"]
    raw = (message.text or "").strip()
    if field == "name":
        label, error = validate_label(raw)
        if error:
            await message.reply_text(f"❌ {error}\n\nSend the button name again, or tap Cancel above.")
            return
        url = st["extra"]["url"]
    else:
        url, error = validate_url(raw)
        if error:
            await message.reply_text(f"❌ {error}\n\nNothing was added. Send a valid link, or tap Cancel above.")
            return
        label = await _link_title(message.get_bot(), url)
        if label is None:
            st["extra"]["url"], st["field"], st["ts"] = url, "name", _now()
            await message.reply_text("✍️ I could not read a name from that link. Send the NAME for this button "
                                     f"(up to {MAX_LABEL} characters), e.g. {LINK_WORDS[slot].split('/')[0]} One.",
                                     reply_markup=_markup(uid, [[("❌ Cancel", section, "cancel")]]))
            return
    work = _links_working(uid)
    if len(work[slot]) >= MAX_LINKS_PER_SLOT:
        _awaiting.pop(uid, None)
        await message.reply_text(f"❌ You can have at most {MAX_LINKS_PER_SLOT} {LINK_WORDS[slot]} links.")
        return
    work[slot].append({"label": label, "url": url})
    _set_draft(uid, section, work)
    _awaiting.pop(uid, None)
    await _send_panel(message, uid, section, f"✏️ “{label}” added (not saved yet). Add more, or use 👁️ Preview Links, then 💾 Save.")


# ---- description (ONE text -> the bot's profile line AND its empty-chat description) -------------------------
def _tg_len(text):
    """Length the way Telegram counts it (UTF-16 units: an emoji can count as 2), so the counter never lies."""
    return len((text or "").encode("utf-16-le")) // 2


def validate_description(text, limit=MAX_DESC, what="description"):
    """Plain text only (Telegram does not render HTML here). -> (clean, None) or (None, error)."""
    t = (text or "").replace("\r\n", "\n").strip()
    if not t:
        return None, "Send the text as a normal message (plain text, not empty)."
    n = _tg_len(t)
    if n < MIN_DESC:
        return None, f"That is only {n} characters; the {what} must be at least {MIN_DESC}."
    if n > limit:
        return None, (f"That is {n} characters; the limit for the {what} is {limit} "
                      f"(Telegram counts an emoji as 2). Please shorten it by {n - limit}.")
    return t, None


def _description_value(uid):
    """The text being worked on: the pending draft if there is one, else the saved text."""
    d = _draft(uid, "description")
    if d is not None:
        return d.get("text") or ""
    return (_saved.get("description") or {}).get("text") or ""


def _description_summary(uid):
    t = _description_value(uid)
    return "Description: " + (f"{_tg_len(t)}/{MAX_DESC} characters" if t else "not set")


def _norm(s):
    return " ".join((s or "").split())


async def _read_description(bot):
    """What Telegram currently shows: (profile line, empty-chat description). Raises on failure."""
    short = await bot.get_my_short_description()
    long_ = await bot.get_my_description()
    return (getattr(short, "short_description", "") or ""), (getattr(long_, "description", "") or "")


async def _tg_apply(bot, text):
    """Set (or, with an empty value, clear) BOTH places on Telegram from one text. Raises on failure."""
    await bot.set_my_short_description(short_description=text or "")
    await bot.set_my_description(description=text or "")


async def _sync_description(bot, new_text, old_text):
    """
    Make Telegram show `new_text` (None/"" = cleared) and CHECK it by reading it back. On any failure Telegram is put
    back to what it showed before and the error text is returned (None = applied and verified).
    """
    try:
        before = await _read_description(bot)
    except Exception as e:
        logger.warning("could not read the current description: %s", e)
        before = None
    try:
        await _tg_apply(bot, new_text)
        short, long_ = await _read_description(bot)
        want = _norm(new_text)
        if _norm(short) != want or _norm(long_) != want:
            raise RuntimeError("Telegram did not keep the text (it shows something different after saving)")
        return None
    except Exception as e:
        logger.error("set description failed: %s", e)
        try:
            if before is not None:
                await bot.set_my_short_description(short_description=before[0])
                await bot.set_my_description(description=before[1])
            else:
                await _tg_apply(bot, old_text)
        except Exception as e2:
            logger.error("could not restore the previous description: %s", e2)
        return str(e) or e.__class__.__name__


async def apply_saved_description(bot):
    """Called at startup: push the saved description to Telegram again when it differs. Never raises."""
    want = (_saved.get("description") or {}).get("text")
    if not want:
        return
    try:
        short, long_ = await _read_description(bot)
        if _norm(short) != _norm(want):
            await bot.set_my_short_description(short_description=want)
        if _norm(long_) != _norm(want):
            await bot.set_my_description(description=want)
        logger.info("bot description checked against the database")
    except Exception as e:
        logger.warning("could not apply the saved bot description: %s", e)


async def _description_section(q, context, uid, action, arg):
    section = "description"
    bot = context.bot
    if action == "edit":
        _set_await(uid, section, "text")
        await _answer(q)
        await _show(q, *_prompt_view(uid, section, f"✏️ Send the new description.\n\nPlain text only (no HTML) - {MIN_DESC} to {MAX_DESC} "
                                                  "characters (an emoji counts as 2). It is shown in the Description row of the bot's profile. "
                                                  "Nothing is saved until you press 💾 Save.\n\nTap Cancel to keep things as they are."))
    elif action == "preview":
        await _answer(q)
        t = _description_value(uid)
        if not t:
            await q.message.reply_text("👁 Preview: no description is set.")
            return
        pending = " (not saved)" if (uid, section) in _drafts else ""
        await q.message.reply_text(
            f"👁 Preview{pending} - exactly as Telegram shows it ({_tg_len(t)}/{MAX_DESC})\n\n"
            f"On the bot's profile (Description row):\n{t}\n\n"
            f"On the empty chat screen:\n{t}", **_nopreview())
    elif action == "save":
        draft = _draft(uid, section)
        if not draft or not draft.get("text"):
            await _answer(q, "Nothing to save - there are no pending changes.", True)
            return
        old = dict(_saved.get(section) or {})
        new = {"text": draft["text"]}
        err = await _sync_description(bot, new["text"], old.get("text"))   # Telegram first, then verified by reading it back
        if err:
            await _answer(q, f"❌ Telegram refused it: {err[:120]}. Nothing was changed.", True)
            return
        if not await _persist(section, new):                               # database failed: put Telegram back as it was
            await _sync_description(bot, old.get("text"), new["text"])
            await _answer(q, "❌ Could not save (database problem). Nothing was changed - your pending text was kept.", True)
            return
        _clear_draft(uid, section)
        await _answer(q, "💾 Saved.")
        await _show(q, *panel_view(uid, section, "✅ Saved, applied on Telegram and checked. If you still see the old text, "
                                                 "close and reopen Telegram (it caches bot profiles)."))
    elif action == "reset":
        await _ask_reset(q, uid, section, "the description")
    elif action == "resetok":
        if _pop_confirm(arg, uid, section, "reset") is None:
            await _answer(q, STALE_TEXT, True)
            return
        old = dict(_saved.get(section) or {})
        err = await _sync_description(bot, "", old.get("text"))
        if err:
            await _answer(q, f"❌ Telegram refused it: {err[:120]}. Nothing was changed.", True)
            return
        if not await _persist(section, None):
            await _sync_description(bot, old.get("text"), "")
            await _answer(q, "❌ Could not reset (database problem). Nothing was changed.", True)
            return
        _clear_draft(uid, section)
        await _answer(q, "♻️ Reset.")
        await _show(q, *panel_view(uid, section, "✅ The description was cleared and removed from Telegram."))
    else:
        await _answer(q, STALE_TEXT, True)


async def _input_description(message, uid, section, st):
    if st["field"] != "text":
        _awaiting.pop(uid, None)
        return
    text, error = validate_description(message.text)
    if error:
        await message.reply_text(f"❌ {error}\n\nYour saved version is unchanged. Send the text again, or tap Cancel on the message above.")
        return
    _set_draft(uid, section, {"text": text})
    _awaiting.pop(uid, None)
    await _send_panel(message, uid, section, "✏️ Pending change recorded (not saved yet). Use 👁️ Preview, then 💾 Save.")


# ---- theme ----------------------------------------------------------------------------------------------
async def _theme_section(q, context, uid, action, arg):
    section = "theme"
    current = _draft(uid, section) or _saved.get(section) or {}
    if action in ("pickstart", "pickhelp"):
        which = action[4:]
        rows = [[(("✅ " if current.get(which, "classic") == key else "") + p["name"], section, "set", f"{which}-{key}")]
                for key, p in PRESETS.items()]
        rows.append(_back(section))
        title = "🌸 Start Menu Theme" if which == "start" else "📚 Help Menu Theme"
        extra = ("frame around the /start message and the emoji of the default buttons"
                 if which == "start" else "frame around the /help message")
        _drafts_last[uid] = which
        await _answer(q)
        await _show(q, f"{title}\n\nChoose a preset. It changes the {extra} only - never what a button or command does.",
                    _markup(uid, rows))
    elif action == "set":
        which, _, key = arg.partition("-")
        if which not in ("start", "help") or key not in PRESETS:
            await _answer(q, STALE_TEXT, True)
            return
        new = dict(current)
        new[which] = key
        _set_draft(uid, section, new)
        _drafts_last[uid] = which
        await _answer(q, f"{PRESETS[key]['name']} selected (pending).")
        await _show(q, *panel_view(uid, section, "✏️ Theme choice recorded (not saved yet). Use 👁️ Preview, then 💾 Save."))
    elif action == "preview":
        await _answer(q)
        which = _drafts_last.get(uid, "start")
        theme_value = _draft(uid, section) or _saved.get(section)
        if which == "start":
            text, custom = start_text_for(_draft(uid, "welcome") or _saved.get("welcome"), theme_value, q.from_user)
            kb = start_keyboard_for(uid, _working_value(uid), _effective_links(uid), theme_value, preview=True,
                                    bot_username=getattr(q.message.get_bot(), "username", None))
            try:
                await q.message.reply_text("👁 Start menu preview (not saved)\n\n" + (text if custom else html.escape(text)),
                                           parse_mode="HTML", reply_markup=kb, **_nopreview())
            except Exception as e:
                logger.info("theme start preview failed: %s", e)
                await q.message.reply_text("⚠️ Telegram could not display the preview.")
        else:
            build = _deps.get("build_help_text")
            base = _unframe(build(), _preset(_saved.get("theme"), "help")) if build else "(help text)"
            preview = "👁 Help menu preview (not saved)\n\n" + _frame(base, _preset(theme_value, "help"))
            await q.message.reply_text(preview[:3900])
    elif action == "reset":
        await _ask_reset(q, uid, section, "the theme")
    elif action == "resetok":
        await _do_reset(q, uid, section, arg, "The theme")
    elif action == "save":
        await _do_save(q, uid, section, lambda d: {k: v for k, v in d.items() if k in ("start", "help") and v in PRESETS})
    else:
        await _answer(q, STALE_TEXT, True)


_drafts_last = {}       # owner -> "start"/"help": which menu Preview shows

_SECTION_HANDLERS = {
    "welcome": _text_section, "about": _text_section, "banner": _banner_section,
    "buttons": _buttons_section, "links": _links_section, "theme": _theme_section, "description": _description_section,
}


# --------------------------------------------------------------------------------------------- owner text/photo input
async def theme_input(update, context):
    """Receives the owner's reply to an Edit/Upload prompt. Only reachable while an input is pending (see the filter)."""
    msg, user = update.effective_message, update.effective_user
    if msg is None or user is None:
        return
    st = _awaiting_state(user.id)
    if st is None:
        return
    if not _is_owner(user.id):                       # role revoked mid-flow
        _awaiting.pop(user.id, None)
        await msg.reply_text(DENIED_TEXT)
        return
    try:
        section, field = st["section"], st["field"]
        if section in ("welcome", "about"):
            await _input_text(msg, user.id, section, st)
        elif section == "banner":
            await _input_banner(msg, user.id, section, st)
        elif section == "buttons":
            await _input_buttons(msg, user.id, section, st)
        elif section == "links":
            await _input_link(msg, user.id, section, st)
        elif section == "description":
            await _input_description(msg, user.id, section, st)
    except Exception as e:
        logger.error("theme input failed: %s", e)
        await msg.reply_text("⚠️ Something went wrong. Nothing was saved. Please reopen the menu.")


def register(app):
    """Attach the customization callbacks, the owner input handler and /about. Loads the saved settings."""
    from telegram.ext import CallbackQueryHandler, CommandHandler, MessageHandler, filters
    from telegram.ext.filters import MessageFilter

    class _AwaitingInput(MessageFilter):
        name = "theme_awaiting_input"

        def filter(self, message):
            sender = message.from_user
            return bool(sender and message.chat and message.chat.type == "private" and _is_awaiting(sender.id))

    app.add_handler(CallbackQueryHandler(theme_callback, pattern=r"^theme:"))
    app.add_handler(CallbackQueryHandler(links_callback, pattern=r"^tlinks:"))
    app.add_handler(CallbackQueryHandler(details_callback, pattern=r"^tdetails$"))
    app.add_handler(MessageHandler(_AwaitingInput() & (filters.TEXT | filters.PHOTO | filters.Document.ALL) & ~filters.COMMAND,
                                   theme_input))
    app.add_handler(CommandHandler("about", about_command))
    load_settings()

    # Restart fix: after every start, push the saved description to Telegram again (only when it differs).
    previous = getattr(app, "post_init", None)

    async def _post_init(application):
        if previous is not None:
            await previous(application)
        await apply_saved_description(application.bot)

    app.post_init = _post_init
