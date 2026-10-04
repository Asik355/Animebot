import re, sqlite3
from datetime import datetime
from telegram import InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import ConversationHandler, CommandHandler, CallbackQueryHandler, MessageHandler, filters

REDEEM_TYPE, REDEEM_REWARD, REDEEM_USES, REDEEM_DATE, REDEEM_TIME, REDEEM_CODE, REDEEM_CONFIRM = range(500,507)

def setup_redeem_database(connect):
    c=connect(); x=c.cursor()
    x.execute('''CREATE TABLE IF NOT EXISTS redeem_codes_v2 (code TEXT PRIMARY KEY COLLATE NOCASE,reward_type TEXT NOT NULL,reward_value TEXT NOT NULL,created_at TEXT NOT NULL,active INTEGER DEFAULT 1,max_uses INTEGER DEFAULT NULL,expires_at TEXT DEFAULT NULL)''')
    x.execute('''CREATE TABLE IF NOT EXISTS redeem_claims_v2 (id INTEGER PRIMARY KEY AUTOINCREMENT,code TEXT NOT NULL COLLATE NOCASE,user_id INTEGER NOT NULL,claimed_at TEXT NOT NULL,UNIQUE(code,user_id))''')
    for col,definition in [('max_uses','INTEGER DEFAULT NULL'),('expires_at','TEXT DEFAULT NULL')]:
        try:x.execute(f'ALTER TABLE redeem_codes_v2 ADD COLUMN {col} {definition}')
        except sqlite3.OperationalError:pass
    c.commit(); c.close()

def _reward(t,v,fmt):
    return fmt(t,v) if fmt else (f'Character [{v}]' if t=='character' else f'{v} coins')
def _expired(v):
    if not v:return False
    try:return datetime.fromisoformat(v)<=datetime.now()
    except:return True

def register_redeem_handlers(app, *, connect, save_user, is_owner, is_executive, get_character_by_code, format_reward=None, timestamp=None):
    setup_redeem_database(connect)
    deps=dict(connect=connect,save_user=save_user,is_owner=is_owner,is_executive=is_executive,get_character_by_code=get_character_by_code,format_reward=format_reward,timestamp=timestamp or (lambda:datetime.now().isoformat(timespec='seconds')))
    app.bot_data['redeem_deps']=deps
    app.add_handler(ConversationHandler(entry_points=[CommandHandler('addredeem',add_redeem_start)],states={
        REDEEM_TYPE:[CallbackQueryHandler(add_redeem_type_callback,pattern=r'^redeem_type:(character|coins)$|^redeem_cancel$')],
        REDEEM_REWARD:[MessageHandler(filters.TEXT&~filters.COMMAND,add_redeem_reward)],
        REDEEM_USES:[MessageHandler(filters.TEXT&~filters.COMMAND,add_redeem_uses)],
        REDEEM_DATE:[CallbackQueryHandler(add_redeem_expiry_callback,pattern=r'^redeem_expiry:none$|^redeem_cancel$'),MessageHandler(filters.TEXT&~filters.COMMAND,add_redeem_date)],
        REDEEM_TIME:[MessageHandler(filters.TEXT&~filters.COMMAND,add_redeem_time)],
        REDEEM_CODE:[MessageHandler(filters.TEXT&~filters.COMMAND,add_redeem_code)],
        REDEEM_CONFIRM:[CallbackQueryHandler(add_redeem_confirm_callback,pattern=r'^redeem_confirm:(yes|no)$')]},fallbacks=[],allow_reentry=True,per_message=False))
    app.add_handler(CommandHandler('redeem',redeem)); app.add_handler(CommandHandler('endredeem',end_redeem)); app.add_handler(CommandHandler('deleteredeem',delete_redeem)); app.add_handler(CommandHandler('redeems',list_redeems))

def _deps(context):return context.bot_data['redeem_deps']

async def add_redeem_start(update,context):
    d=_deps(context)
    if not d['is_owner'](update.effective_user.id): await update.message.reply_text('⚠️ Only the Owner can create redeem codes.'); return ConversationHandler.END
    context.user_data.clear()
    kb=[[InlineKeyboardButton('🎭 Character',callback_data='redeem_type:character'),InlineKeyboardButton('🪙 Coins',callback_data='redeem_type:coins')]]
    await update.message.reply_text('🎟️ *Add Redeem*\n\n1️⃣ Choose reward type:',reply_markup=InlineKeyboardMarkup(kb),parse_mode='Markdown'); return REDEEM_TYPE

async def add_redeem_type_callback(update,context):
    q=update.callback_query; await q.answer()
    if q.data=='redeem_cancel': context.user_data.clear(); await q.edit_message_text('❌ Redeem code cancelled.'); return ConversationHandler.END
    t=q.data.split(':',1)[1]; context.user_data['redeem_type']=t
    await q.edit_message_text('2️⃣ Send the *4-digit character code*.\nExample: `0023`' if t=='character' else '2️⃣ Send the *coin amount* in digits.\nExample: `5000`',parse_mode='Markdown'); return REDEEM_REWARD

async def add_redeem_reward(update,context):
    d=_deps(context); s=update.message.text.strip(); t=context.user_data.get('redeem_type')
    if t=='character':
        if not re.fullmatch(r'\d{4}',s): await update.message.reply_text('❌ Character code must be exactly 4 digits.'); return REDEEM_REWARD
        ch=d['get_character_by_code'](s)
        if not ch: await update.message.reply_text('❌ Character code not found. Send another 4-digit code.'); return REDEEM_REWARD
        v=ch[0]
    else:
        if not re.fullmatch(r'\d+',s) or int(s)<=0: await update.message.reply_text('❌ Coin amount must be a positive number.'); return REDEEM_REWARD
        v=s
    context.user_data['redeem_reward']=v
    await update.message.reply_text('3️⃣ Enter the *redeem count* in digits.\nExample: `10`\n⚠️ `0` means nobody can redeem this code.',parse_mode='Markdown'); return REDEEM_USES

async def add_redeem_uses(update,context):
    s=update.message.text.strip()
    if not s.isdigit(): await update.message.reply_text('❌ Redeem count must contain digits only.'); return REDEEM_USES
    context.user_data['redeem_max_uses']=int(s)
    kb=[[InlineKeyboardButton('♾️ No Expiry',callback_data='redeem_expiry:none'),InlineKeyboardButton('❌ Cancel',callback_data='redeem_cancel')]]
    await update.message.reply_text('4️⃣ Enter expiry *date* as `DD-MM`.\nExample: `25-12`\n\nOr choose *No Expiry*.',reply_markup=InlineKeyboardMarkup(kb),parse_mode='Markdown'); return REDEEM_DATE

async def add_redeem_date(update,context):
    s=update.message.text.strip()
    if not re.fullmatch(r'\d{2}-\d{2}',s): await update.message.reply_text('❌ Invalid date format. Use DD-MM.'); return REDEEM_DATE
    day,month=map(int,s.split('-')); valid=False
    for y in (datetime.now().year,datetime.now().year+1):
        try:datetime(y,month,day); valid=True; break
        except ValueError:pass
    if not valid: await update.message.reply_text('❌ Invalid calendar date.'); return REDEEM_DATE
    context.user_data['redeem_date']=s
    await update.message.reply_text('5️⃣ Enter expiry *time* as `HH:MM`.\nExample: `23:59`',parse_mode='Markdown'); return REDEEM_TIME

async def add_redeem_expiry_callback(update,context):
    q=update.callback_query; await q.answer()
    if q.data=='redeem_cancel': context.user_data.clear(); await q.edit_message_text('❌ Redeem code cancelled.'); return ConversationHandler.END
    context.user_data['redeem_expires_at']=None
    await q.edit_message_text('6️⃣ Enter a unique *6-digit redeem code*.\nExample: `123456`',parse_mode='Markdown'); return REDEEM_CODE

async def add_redeem_time(update,context):
    s=update.message.text.strip()
    if not re.fullmatch(r'\d{2}:\d{2}',s): await update.message.reply_text('❌ Invalid time format. Use HH:MM.'); return REDEEM_TIME
    h,m=map(int,s.split(':'))
    if h>23 or m>59: await update.message.reply_text('❌ Invalid time. Use 00:00–23:59.'); return REDEEM_TIME
    day,month=map(int,context.user_data['redeem_date'].split('-')); now=datetime.now(); dt=None
    for y in (now.year,now.year+1):
        try:
            candidate=datetime(y,month,day,h,m)
            if candidate>now: dt=candidate; break
        except ValueError:pass
    if dt is None: await update.message.reply_text('❌ Expiry must be a valid future date/time.'); return REDEEM_TIME
    context.user_data['redeem_expires_at']=dt.isoformat(timespec='minutes')
    await update.message.reply_text('6️⃣ Enter a unique *6-digit redeem code*.\nExample: `123456`',parse_mode='Markdown'); return REDEEM_CODE

async def add_redeem_code(update,context):
    d=_deps(context); code=update.message.text.strip()
    if not re.fullmatch(r'\d{6}',code): await update.message.reply_text('❌ Redeem code must be exactly 6 digits.'); return REDEEM_CODE
    c=d['connect'](); x=c.cursor(); x.execute('SELECT 1 FROM redeem_codes_v2 WHERE code=? COLLATE NOCASE',(code,)); exists=x.fetchone(); c.close()
    if exists: await update.message.reply_text('❌ This redeem code already exists. Send another unique 6-digit code.'); return REDEEM_CODE
    context.user_data['redeem_code']=code; u=context.user_data; ex=u.get('redeem_expires_at'); ex=ex.replace('T',' ') if ex else 'Never'
    kb=[[InlineKeyboardButton('✅ Yes',callback_data='redeem_confirm:yes'),InlineKeyboardButton('❌ No',callback_data='redeem_confirm:no')]]
    text=f"🎟️ *Redeem Code Preview*\n\n🎁 Reward: {_reward(u['redeem_type'],u['redeem_reward'],d['format_reward'])}\n🔢 Redeem count: {u['redeem_max_uses']}\n⏰ Expiry: {ex}\n🔐 Code: `{code}`\n\nCreate this redeem code?"
    await update.message.reply_text(text,reply_markup=InlineKeyboardMarkup(kb),parse_mode='Markdown'); return REDEEM_CONFIRM

async def add_redeem_confirm_callback(update,context):
    d=_deps(context); q=update.callback_query; await q.answer(); choice=q.data.split(':',1)[1]
    if choice=='no': context.user_data.clear(); await q.edit_message_text('❌ Redeem code cancelled.'); return ConversationHandler.END
    u=context.user_data; c=d['connect'](); x=c.cursor()
    try:
        x.execute('INSERT INTO redeem_codes_v2(code,reward_type,reward_value,created_at,active,max_uses,expires_at) VALUES(?,?,?,?,1,?,?)',(u['redeem_code'],u['redeem_type'],u['redeem_reward'],d['timestamp'](),u['redeem_max_uses'],u.get('redeem_expires_at'))); c.commit()
    except sqlite3.IntegrityError:
        c.rollback(); c.close(); context.user_data.clear(); await q.edit_message_text('❌ Redeem code already exists. Start /addredeem again.'); return ConversationHandler.END
    except Exception as e:
        c.rollback(); c.close(); print('Redeem creation error:',e); context.user_data.clear(); await q.edit_message_text('❌ Could not create redeem code.'); return ConversationHandler.END
    c.close(); code=u['redeem_code']; reward=_reward(u['redeem_type'],u['redeem_reward'],d['format_reward']); ex=u.get('redeem_expires_at'); ex=ex.replace('T',' ') if ex else 'Never'; uses=u['redeem_max_uses']; context.user_data.clear()
    await q.edit_message_text(f'✅ *Redeem code created successfully!*\n\n🔐 Code: `{code}`\n🎁 Reward: {reward}\n🔢 Redeem count: {uses}\n⏰ Expiry: {ex}',parse_mode='Markdown'); return ConversationHandler.END

async def redeem(update,context):
    d=_deps(context); d['save_user'](update.effective_user)
    if len(context.args)!=1: await update.message.reply_text('Usage: /redeem CODE'); return
    code=context.args[0].strip()
    if not re.fullmatch(r'\d{6}',code): await update.message.reply_text('❌ Redeem code must be exactly 6 digits.'); return
    uid=update.effective_user.id; c=d['connect'](); x=c.cursor()
    try:
        c.execute('BEGIN IMMEDIATE'); x.execute('SELECT reward_type,reward_value,active,max_uses,expires_at FROM redeem_codes_v2 WHERE code=? COLLATE NOCASE',(code,)); row=x.fetchone()
        if not row or not row[2]: c.rollback(); await update.message.reply_text('❌ Invalid or inactive redeem code.'); return
        t,v,_,max_uses,expires=row
        if _expired(expires): x.execute('UPDATE redeem_codes_v2 SET active=0 WHERE code=? COLLATE NOCASE',(code,)); c.commit(); await update.message.reply_text('⏰ This redeem code has expired.'); return
        x.execute('SELECT 1 FROM redeem_claims_v2 WHERE code=? COLLATE NOCASE AND user_id=?',(code,uid))
        if x.fetchone(): c.rollback(); await update.message.reply_text('⚠️ You have already redeemed this code.'); return
        x.execute('SELECT COUNT(*) FROM redeem_claims_v2 WHERE code=? COLLATE NOCASE',(code,)); used=x.fetchone()[0]
        if max_uses is not None and used>=int(max_uses): x.execute('UPDATE redeem_codes_v2 SET active=0 WHERE code=? COLLATE NOCASE',(code,)); c.commit(); await update.message.reply_text('❌ This redeem code has reached its usage limit.'); return
        if t=='coins':
            x.execute('UPDATE users_v2 SET coins=coins+? WHERE user_id=?',(int(v),uid))
            if x.rowcount==0: c.rollback(); await update.message.reply_text('❌ User account could not be updated. Try /start first.'); return
        elif t=='character':
            x.execute('SELECT name FROM characters_v2 WHERE code=? LIMIT 1',(str(v),))
            if not x.fetchone(): c.rollback(); await update.message.reply_text('❌ This redeem reward is no longer available.'); return
            x.execute('INSERT INTO collections_v2(user_id,character_code,caught_at) VALUES(?,?,?)',(uid,v,d['timestamp']()))
        else: c.rollback(); await update.message.reply_text('❌ Invalid redeem reward.'); return
        x.execute('INSERT INTO redeem_claims_v2(code,user_id,claimed_at) VALUES(?,?,?)',(code,uid,d['timestamp']())); new_used=used+1
        if max_uses is not None and new_used>=int(max_uses): x.execute('UPDATE redeem_codes_v2 SET active=0 WHERE code=? COLLATE NOCASE',(code,))
        c.commit()
    except Exception as e:
        c.rollback(); print('Redeem error:',e); await update.message.reply_text('❌ Redeem failed. Please try again.'); return
    finally:c.close()
    await update.message.reply_text(f"🎉 Redeemed successfully!\n🎁 {_reward(t,v,d['format_reward'])}")

async def end_redeem(update,context):
    d=_deps(context); uid=update.effective_user.id
    if not(d['is_owner'](uid) or d['is_executive'](uid)): await update.message.reply_text('⚠️ Only Owner or Executive can end a redeem code.'); return
    if len(context.args)!=1: await update.message.reply_text('Usage: /endredeem CODE'); return
    c=d['connect'](); x=c.cursor(); x.execute('UPDATE redeem_codes_v2 SET active=0 WHERE code=? COLLATE NOCASE AND active=1',(context.args[0].strip(),)); changed=x.rowcount; c.commit(); c.close(); await update.message.reply_text('✅ Redeem code ended.' if changed else '❌ Active redeem code not found.')

async def delete_redeem(update,context):
    d=_deps(context)
    if not d['is_owner'](update.effective_user.id): await update.message.reply_text('⚠️ Only the Owner can disable redeem codes.'); return
    if len(context.args)!=1: await update.message.reply_text('Usage: /deleteredeem CODE'); return
    c=d['connect'](); x=c.cursor(); x.execute('UPDATE redeem_codes_v2 SET active=0 WHERE code=? COLLATE NOCASE AND active=1',(context.args[0].strip(),)); changed=x.rowcount; c.commit(); c.close(); await update.message.reply_text('✅ Redeem code disabled.' if changed else '❌ Active redeem code not found.')

async def list_redeems(update,context):
    d=_deps(context)
    if not d['is_owner'](update.effective_user.id): await update.message.reply_text('⚠️ Only the Owner can view redeem codes.'); return
    c=d['connect'](); x=c.cursor(); x.execute('SELECT code,reward_type,reward_value,max_uses,expires_at FROM redeem_codes_v2 WHERE active=1 ORDER BY created_at DESC'); rows=x.fetchall(); visible=[]
    for code,t,v,m,e in rows:
        x.execute('SELECT COUNT(*) FROM redeem_claims_v2 WHERE code=? COLLATE NOCASE',(code,)); used=x.fetchone()[0]
        if (m is not None and used>=int(m)) or _expired(e): x.execute('UPDATE redeem_codes_v2 SET active=0 WHERE code=? COLLATE NOCASE',(code,)); continue
        visible.append((code,t,v,m,e,used))
    c.commit(); c.close()
    if not visible: await update.message.reply_text('🎟️ No active usable redeem codes.'); return
    lines=['🎟️ Active Redeem Codes:']
    for code,t,v,m,e,u in visible: lines.append(f'• {code} → {_reward(t,v,d["format_reward"])}\n  🔢 Uses: {u}/{m if m is not None else "∞"} | ⏰ {e.replace("T"," ") if e else "Never"}')
    await update.message.reply_text('\n'.join(lines))
