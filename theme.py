"""
theme.py - Bot Theme Customization (Owner only)
===============================================

Self-contained module. bot.py only needs:
    import theme
    theme.bind(is_owner=..., default_start_text=..., add_header=..., build_help_text=...)   # in main(), before register
    theme.register(app)                                                                    # in main()
    await theme.send_start(update, context)   # in start(): returns False when nothing is customized -> original code runs
    theme.decorate_help_text(text)            # in build_help_text()

Entry point: Owner Commands (/help) -> [🎨 Customize Bot] -> hub with six sections:
    📝 Welcome   🖼️ Banner   🔘 Start Menu   📖 About Bot   🔗 Links   🎭 Theme
Every section has its own Edit/Preview/Reset/Save controls and a full-width Back.

Persistence (existing MongoDB, collection `bot_settings`, one document):
    _id "theme_customization": {welcome:{text}, banner:{file_id,unique_id}, buttons:{items:[...]}, about:{text},
                                links:{channel|group|website:[{label,url},...]}, theme:{start,help}, updated_at}
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
SECTIONS = ("welcome", "banner", "buttons", "about", "links", "theme")
START_SECTIONS = ("welcome", "banner", "buttons", "links", "theme")      # sections that change /start

MAX_TEXT = 3500            # welcome / about (Telegram allows 4096; room for the name header and theme frame)
MAX_LABEL = 30
MAX_URL = 256
MAX_BUTTONS = 8
MAX_PHOTO_BYTES = 10 * 1024 * 1024
CAPTION_LIMIT = 1000       # photo captions are limited to 1024 characters
AWAIT_TTL = 600            # seconds an Edit/Upload prompt stays active
CONFIRM_TTL = 300          # seconds a Yes/No confirmation stays valid

DEFAULT_HELP_LABEL = "📖 Help"      # the existing /start button (callback help:<uid>:open - fixed)
LINK_SLOTS = ("channel", "group", "website")
LINK_LABELS = {"channel": "📢 Channel", "group": "👥 Group", "website": "🌐 Website"}
LINK_WORDS = {"channel": "Channel", "group": "Group", "website": "Website/Social"}
MAX_LINKS_PER_SLOT = 8               # e.g. Channel One ... Channel Eight

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


def default_buttons():
    return [{"id": "help", "kind": "help", "label": DEFAULT_HELP_LABEL}]


def _button_items(value):
    """The configurable start buttons (saved or default). The built-in Help button is always present."""
    items = copy.deepcopy((value or {}).get("items") or default_buttons())
    if not any(i.get("kind") == "help" for i in items):
        items.insert(0, default_buttons()[0])
    return items


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


def start_text_for(welcome_value, theme_value, user=None):
    """
    -> (text, is_custom_html). Without a saved welcome this is the existing /start text, word for word.
    With `user`, a custom welcome is returned fully personalised (automatic greeting + any {placeholders} filled in).
    """
    custom = bool(welcome_value and welcome_value.get("text"))
    base = welcome_value["text"] if custom else _deps["default_start_text"]
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


def start_keyboard_for(uid, buttons_value, links_value, theme_value, preview=False):
    from telegram import InlineKeyboardButton, InlineKeyboardMarkup
    preset = _preset(theme_value, "start")
    buttons = []
    for item in _button_items(buttons_value):
        if item["kind"] == "help":
            label = _themed_label(item["label"], DEFAULT_HELP_LABEL, "Help", preset)
            data = f"theme:{uid}:noop:x" if preview else f"help:{uid}:open"     # the original action, untouched
            buttons.append(InlineKeyboardButton(label, callback_data=data))
        else:
            buttons.append(InlineKeyboardButton(item["label"], url=item["url"]))
    for slot in LINK_SLOTS:
        for link in _slot_links(links_value, slot):
            buttons.append(InlineKeyboardButton(_themed_label(link["label"], LINK_LABELS[slot], LINK_WORDS[slot].split("/")[0], preset),
                                                url=link["url"]))
    return InlineKeyboardMarkup(_grid(buttons))


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
        if header:
            text = header(msg, text)
        keyboard = start_keyboard_for(user.id, _saved.get("buttons"), _saved.get("links"), _saved.get("theme"))
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
        listing = "\n".join(f"{n}. {i['label']}" + (" (built-in Help)" if i["kind"] == "help" else f" → {i['url']}")
                            for n, i in enumerate(items, 1))
        text = (f"{pre}🔘 Start Menu Buttons\n\nButtons on your /start message:\n{listing}\n\n{_status(uid, section)}")
        rows = [[("➕ Add Button", section, "add"), ("✏️ Edit Button", section, "edit")],
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
        text = (f"{pre}🔗 Bot Links\n\nYou can add several channels, groups or websites - each one becomes its own "
                f"button on /start (up to {MAX_LINKS_PER_SLOT} per type).\n\n{listing}\n\n{_status(uid, section)}")
        rows = [[("➕ Add Channel", section, "setchannel"), ("➕ Add Group", section, "setgroup")],
                [("➕ Add Website/Social", section, "setwebsite"), ("🗑️ Remove Link", section, "remove")],
                [("👁️ Preview Links", section, "preview"), ("♻️ Reset", section, "reset")],
                [("💾 Save", section, "save")], _back()]
    else:  # theme
        t = _draft(uid, "theme") or _saved.get("theme") or {}
        text = (f"{pre}🎭 Bot Theme\n\nOnly /start and /help are themed. Telegram does not allow custom button colours, "
                f"so themes are ready-made presets.\n\n🌸 Start menu: {_preset(t, 'start')['name']}\n"
                f"📚 Help menu: {_preset(t, 'help')['name']}\n\n{_status(uid, section)}")
        rows = [[("🌸 Start Menu Theme", section, "pickstart"), ("📚 Help Menu Theme", section, "pickhelp")],
                [("👁️ Preview", section, "preview"), ("♻️ Reset", section, "reset")],
                [("💾 Save", section, "save")], _back()]
    return text, _markup(uid, rows)


def _effective_links(uid):
    d = _draft(uid, "links")
    return d if d is not None else (_saved.get("links") or {})


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


def _commit_buttons(uid, items):
    _set_draft(uid, "buttons", {"items": items})


def _next_button_id(items):
    nums = [int(i["id"][1:]) for i in items if re.fullmatch(r"b\d+", str(i.get("id", "")))]
    return f"b{(max(nums) if nums else 0) + 1}"


def _pick_view(uid, section, action_prefix, title, items, note=""):
    rows = [[(f"{n}. {i['label']}"[:60], section, action_prefix, i["id"])] for n, i in enumerate(items, 1)]
    rows.append(_back(section))
    return (f"{title}{note}", _markup(uid, rows))


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
        kb = start_keyboard_for(uid, {"items": items}, _effective_links(uid), theme_value, preview=True)
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
        await _do_save(q, uid, section, lambda d: {"items": d["items"]})
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
            kb = start_keyboard_for(uid, {"items": _working_buttons(uid)}, _effective_links(uid), theme_value, preview=True)
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
    "buttons": _buttons_section, "links": _links_section, "theme": _theme_section,
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
    app.add_handler(MessageHandler(_AwaitingInput() & (filters.TEXT | filters.PHOTO | filters.Document.ALL) & ~filters.COMMAND,
                                   theme_input))
    app.add_handler(CommandHandler("about", about_command))
    load_settings()
