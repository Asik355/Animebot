# Put your NEW BotFather token here.
# The old token that was previously exposed should NOT be reused.
BOT_TOKEN = ""

# First ID is treated as the bot owner for /callchar.
ADMIN_IDS = [5675165124]

# Add Telegram user IDs here for Executive staff.
# Executives can manage characters but cannot /callchar, /delete, or /gift.
EXECUTIVE_IDS = []

DB_NAME = "bot_database.db"

AUTO_SPAWN_COOLDOWN = 15 * 60
MANUAL_SPAWN_COOLDOWN = 1 * 60 + 10
CHARACTER_SPAWN_COOLDOWN = 60 * 60

RARITY_COINS = {
    "Common": 50,
    "Rare": 100,
    "Epic": 200,
    "Legendary": 500,
    "Mythic": 750,
    "Celestial": 1500,
}

RARITIES = [
    "Common",
    "Rare",
    "Epic",
    "Legendary",
    "Mythic",
    "Celestial",
]

DAILY_COINS = 100
DAILY_RARE_CHARACTER = True
DAILY_RESET_HOUR = 4

# Character IDs are unique numeric 4-digit codes (1000-9999).
CHARACTER_CODE_DIGITS = 4
CHARACTER_CODE_MIN = 1000
CHARACTER_CODE_MAX = 9999

# /myadd collection page size.
ITEMS_PER_PAGE = 5
