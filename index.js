import 'dotenv/config';
import http from 'node:http';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { writeFile, readFile, mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';

const run = promisify(execFile);

// Library dan dependency dimuat dengan await import() (ESM).
const lib = await import('@xbibzlibrary/whatsbibz');
const { default: pino } = await import('pino');
await import('qrcode'); // terpasang sesuai permintaan, QR tidak dipakai (login pakai pairing code)

const makeWASocket = lib.makeWASocket ?? lib.default;
const {
  useMultiFileAuthState,
  DisconnectReason,
  downloadVideoForSoundSticker,
  convertVideoToSoundSticker,
  prepareWAMessageMedia,
  generateWAMessageFromContent,
  downloadMediaMessage,
  proto,
} = lib;
const normalize = lib.normalizeMessageContent ?? ((m) => m);

const PACK_NAME = 'Hanzala Saputra';
const AUTHOR = 'Hanzala Saputra';
const AUDIO_WINDOW_MS = 10 * 60 * 1000;
const MAX_SECONDS = Number(process.env.MAX_SECONDS || 30); // durasi maksimal sticker bersuara
const AI_URL = process.env.AI_BASE_URL || 'https://text.pollinations.ai/openai';
const AI_MODEL = process.env.AI_MODEL || 'openai';
const AI_KEY = process.env.AI_API_KEY || '';
const AI_SYSTEM = 'Kamu asisten WhatsApp yang ramah. Jawab singkat dan jelas dalam bahasa pengguna.';
const aiHistory = new Map(); // chat JID -> riwayat percakapan
const MENU = `*MENU BOT STIKER*
.menu - tampilkan menu ini
!ping - cek bot (dibalas pong)
!sticker - kirim video dengan caption !sticker, atau reply video dengan !sticker (sticker bersuara, maks ${MAX_SECONDS} detik)
!stickerFT - kirim audio dulu, lalu kirim foto dengan caption !stickerFT (atau reply foto dengan !stickerFT). Audio diambil dari audio terakhir di chat ini (maks 10 menit), durasi maks ${MAX_SECONDS} detik
.ai <pesan> - ngobrol dengan AI
.aireset - hapus riwayat obrolan AI

Hak cipta: ${AUTHOR}`;

const PAIRING_NUMBER = (process.env.BOT_NUMBER || '').replace(/\D/g, ''); // format 62..., tanpa + dan 0
const PORT = Number(process.env.PORT || process.env.SERVER_PORT || 3000);
const AUTH_DIR = 'auth';

// Halaman status kecil di port panel (untuk cek app hidup).
http.createServer((req, res) => {
  res.writeHead(200, { 'content-type': 'text/plain; charset=utf-8' });
  res.end('Bot WA berjalan\n');
}).listen(PORT, '0.0.0.0', () => console.log(`Status HTTP di port ${PORT}`));

const seen = new Set();
const recentAudio = new Map(); // chat JID -> { msg, at } audio terakhir

function ownNumber(jid) {
  return jid ? jid.split('@')[0].split(':')[0] : '';
}

// Self-chat: chat ke nomor sendiri (PN atau LID).
function isSelfChat(msg, sock) {
  const chat = msg.key.remoteJid;
  const pn = ownNumber(sock.user?.id);
  const lid = ownNumber(sock.user?.lid);
  return chat === `${pn}@s.whatsapp.net` || (!!lid && chat === `${lid}@lid`);
}

function getText(m) {
  return m.conversation ?? m.extendedTextMessage?.text ?? m.videoMessage?.caption ?? m.imageMessage?.caption ?? '';
}

// Video langsung (caption) atau video hasil reply.
function hasVideo(m) {
  if (m.videoMessage) return true;
  const quoted = normalize(m.extendedTextMessage?.contextInfo?.quotedMessage);
  return !!quoted?.videoMessage;
}

// Pastikan WebP punya header VP8X (format extended). Kalau belum, header ditambahkan.
function ensureVp8x(webp) {
  const type = webp.toString('ascii', 12, 16);
  if (type === 'VP8X') return webp;
  const data = webp.subarray(20);
  let w;
  let h;
  if (type === 'VP8 ') {
    w = data.readUInt16LE(6) & 0x3fff;
    h = data.readUInt16LE(8) & 0x3fff;
  } else if (type === 'VP8L') {
    const bits = data.readUInt32LE(1);
    w = (bits & 0x3fff) + 1;
    h = ((bits >>> 14) & 0x3fff) + 1;
  } else {
    throw new Error(`Format WebP tidak dikenali: ${type}`);
  }
  const vp8x = Buffer.alloc(18);
  vp8x.write('VP8X', 0, 'ascii');
  vp8x.writeUInt32LE(10, 4);
  vp8x.writeUIntLE(w - 1, 12, 3);
  vp8x.writeUIntLE(h - 1, 15, 3);
  return Buffer.concat([webp.subarray(0, 12), vp8x, webp.subarray(12)]);
}

// Tambah metadata EXIF (nama pack dan author) ke WebP animasi.
function addExif(webpIn, pack, author) {
  const webp = ensureVp8x(webpIn);
  const json = Buffer.from(JSON.stringify({
    'sticker-pack-id': `hanzala-${Date.now()}`,
    'sticker-pack-name': pack,
    'sticker-pack-publisher': author,
    emojis: ['\ud83e\udd16'],
  }), 'utf8');
  const tiff = Buffer.concat([
    Buffer.from([0x49, 0x49, 0x2a, 0x00, 0x08, 0x00, 0x00, 0x00, 0x01, 0x00, 0x41, 0x57, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x16, 0x00, 0x00, 0x00]),
    json,
  ]);
  tiff.writeUInt32LE(json.length, 14);
  const chunkHead = Buffer.alloc(8);
  chunkHead.write('EXIF', 0, 'ascii');
  chunkHead.writeUInt32LE(tiff.length, 4);
  const parts = [webp, chunkHead, tiff];
  if (tiff.length % 2) parts.push(Buffer.alloc(1));
  const out = Buffer.concat(parts);
  out.writeUInt32LE(out.length - 8, 4);
  out[20] |= 0x08; // flag EXIF di VP8X
  return out;
}

// Kirim sticker bersuara (webp animasi + audio ogg) dengan nama pack dan author.
async function sendSoundSticker(sock, jid, parts, quotedMsg) {
  const sticker = addExif(parts.sticker, PACK_NAME, AUTHOR);
  const { stickerMessage } = await prepareWAMessageMedia({
    sticker, mimetype: 'image/webp', width: 512, height: 512, isAnimated: true,
  }, { upload: sock.waUploadToServer });
  const { audioMessage } = await prepareWAMessageMedia({
    audio: parts.audio, mimetype: 'audio/ogg; codecs=opus', seconds: parts.seconds, ptt: false,
  }, { upload: sock.waUploadToServer });
  if (!stickerMessage?.directPath || !audioMessage?.directPath) throw new Error('Upload sticker atau audio gagal.');
  stickerMessage.audioMessage = audioMessage;
  const quoted = proto.WebMessageInfo.decode(proto.WebMessageInfo.encode(proto.WebMessageInfo.fromObject(quotedMsg)).finish());
  const full = generateWAMessageFromContent(jid, { audioStickerMessage: { message: { stickerMessage } } }, {
    userJid: sock.user.id, quoted,
  });
  await sock.relayMessage(jid, full.message, { messageId: full.key.id });
}

async function ffmpeg(args) {
  await run('ffmpeg', ['-nostdin', '-hide_banner', '-loglevel', 'error', '-y', ...args], { timeout: 180_000 });
}

async function probeDuration(file) {
  const { stdout } = await run('ffprobe', ['-v', 'error', '-show_entries', 'format=duration', '-of', 'csv=p=0', file], { timeout: 30_000 });
  return Number(stdout.trim()) || 0;
}

// Video jadi sticker bersuara dengan durasi sampai MAX_SECONDS.
async function videoToSoundSticker(buf) {
  return withTemp(async (dir) => {
    const input = path.join(dir, 'in.mp4');
    const out = path.join(dir, 'out.webp');
    const oggPath = path.join(dir, 'out.ogg');
    await writeFile(input, buf);
    const dur = await probeDuration(input);
    if (!dur) throw new Error('Video tidak valid.');
    const secs = Math.min(MAX_SECONDS, dur);
    await ffmpeg(['-i', input, '-t', String(secs), '-map', '0:a:0', '-vn', '-c:a', 'libopus', '-b:a', '32k', '-ac', '1', '-ar', '48000', '-f', 'ogg', oggPath])
      .catch(() => { throw new Error('Video tidak punya suara.'); });
    const audio = await readFile(oggPath);
    if (!audio.length || audio.length > 1024 * 1024) throw new Error('Audio tidak valid atau terlalu besar.');
    const tiers = [[512, 15, 60], [512, 12, 40], [384, 10, 40], [320, 8, 30], [256, 6, 25], [192, 5, 20]];
    for (const [size, fps, q] of tiers) {
      await ffmpeg(['-i', input, '-t', String(secs), '-map', '0:v:0', '-an',
        '-vf', `fps=${fps},scale=${size}:${size}:force_original_aspect_ratio=decrease:flags=lanczos,format=rgba,pad=${size}:${size}:(ow-iw)/2:(oh-ih)/2:color=0x00000000,scale=512:512:flags=neighbor`,
        '-c:v', 'libwebp_anim', '-q:v', String(q), '-loop', '0', '-compression_level', '5', out]);
      const data = await readFile(out);
      if (data.length <= 500 * 1024) return { sticker: data, audio, seconds: Math.max(1, Math.ceil(secs)) };
    }
    throw new Error('Video terlalu berat untuk dijadikan sticker, coba video yang lebih pendek.');
  });
}

async function askAI(jid, prompt) {
  const hist = aiHistory.get(jid) ?? [];
  hist.push({ role: 'user', content: prompt });
  while (hist.length > 20) hist.shift();
  const res = await fetch(AI_URL, {
    method: 'POST',
    headers: { 'content-type': 'application/json', ...(AI_KEY ? { authorization: `Bearer ${AI_KEY}` } : {}) },
    body: JSON.stringify({ model: AI_MODEL, messages: [{ role: 'system', content: AI_SYSTEM }, ...hist] }),
    signal: AbortSignal.timeout(60_000),
  });
  if (!res.ok) throw new Error(`AI error ${res.status}`);
  const data = await res.json();
  const answer = data?.choices?.[0]?.message?.content?.trim();
  if (!answer) throw new Error('AI tidak memberi jawaban.');
  hist.push({ role: 'assistant', content: answer });
  aiHistory.set(jid, hist);
  return answer;
}

async function withTemp(fn) {
  const dir = await mkdtemp(path.join(tmpdir(), 'stk-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

// Foto jadi WebP animasi 512x512 sepanjang `secs` detik. Kualitas diturunkan kalau lebih dari 500 KiB.
async function photoToWebp(buf, mimetype, secs = 5) {
  const ext = mimetype === 'image/png' ? 'png' : mimetype === 'image/webp' ? 'webp' : 'jpg';
  return withTemp(async (dir) => {
    const input = path.join(dir, `in.${ext}`);
    const output = path.join(dir, 'out.webp');
    await writeFile(input, buf);
    for (const q of [70, 50, 30]) {
      await ffmpeg(['-loop', '1', '-t', String(secs), '-i', input,
        '-vf', 'fps=2,scale=512:512:force_original_aspect_ratio=decrease:flags=lanczos,format=rgba,pad=512:512:(ow-iw)/2:(oh-ih)/2:color=0x00000000',
        '-c:v', 'libwebp_anim', '-q:v', String(q), '-loop', '0', '-an', output]);
      const data = await readFile(output);
      if (data.length <= 500 * 1024) return data;
    }
    throw new Error('Foto terlalu besar untuk sticker (maks 500 KB).');
  });
}

// Audio apa pun jadi Ogg Opus mono 48 kHz, maksimal MAX_SECONDS detik.
async function audioToOgg(buf) {
  return withTemp(async (dir) => {
    const input = path.join(dir, 'in');
    const output = path.join(dir, 'out.ogg');
    await writeFile(input, buf);
    await ffmpeg(['-i', input, '-t', String(MAX_SECONDS), '-vn', '-c:a', 'libopus', '-b:a', '32k', '-ac', '1', '-ar', '48000', '-f', 'ogg', output]);
    const data = await readFile(output);
    if (!data.length || data.length > 1024 * 1024) throw new Error('Audio tidak valid atau terlalu besar.');
    const seconds = Math.max(1, Math.ceil((await probeDuration(output)) - 0.02));
    return { data, seconds };
  });
}

async function handleStickerFT(sock, msg, m, quotedM) {
  const jid = msg.key.remoteJid;
  const photoSrc = m.imageMessage ? msg : (quotedM?.imageMessage ? { key: msg.key, message: quotedM } : null);
  if (!photoSrc) {
    await sock.sendMessage(jid, { text: 'Kirim foto dengan caption !stickerFT, atau reply foto dengan !stickerFT.' }, { quoted: msg });
    return;
  }
  let audioSrc = null;
  if (quotedM?.audioMessage) {
    audioSrc = { key: msg.key, message: quotedM };
  } else {
    const last = recentAudio.get(jid);
    if (last && Date.now() - last.at <= AUDIO_WINDOW_MS) audioSrc = last.msg;
  }
  if (!audioSrc) {
    await sock.sendMessage(jid, { text: 'Kirim audio dulu di chat ini (maks 10 menit sebelum foto), lalu kirim foto dengan caption !stickerFT.' }, { quoted: msg });
    return;
  }
  await sock.sendMessage(jid, { text: 'Sedang membuat sticker...' }, { quoted: msg });
  try {
    const img = await downloadMediaMessage(photoSrc, 'buffer', {});
    const aud = await downloadMediaMessage(audioSrc, 'buffer', {});
    const audio = await audioToOgg(aud);
    const sticker = await photoToWebp(img, normalize(photoSrc.message)?.imageMessage?.mimetype, audio.seconds);
    await sendSoundSticker(sock, jid, { sticker, audio: audio.data, seconds: audio.seconds }, msg);
  } catch (err) {
    console.error('StickerFT gagal:', err?.message);
    await sock.sendMessage(jid, { text: `Gagal membuat sticker: ${err?.message || 'error tidak diketahui'}` }, { quoted: msg });
  }
}

async function handleMessage(sock, msg) {
  if (!msg.message || !msg.key?.remoteJid) return;
  if (msg.key.remoteJid === 'status@broadcast') return;
  // Pesan dari diri sendiri hanya diproses di self-chat.
  if (msg.key.fromMe && !isSelfChat(msg, sock)) return;

  const id = msg.key.id;
  if (id) {
    if (seen.has(id)) return;
    seen.add(id);
    if (seen.size > 500) seen.delete(seen.values().next().value);
  }

  const jid = msg.key.remoteJid;
  const m = normalize(msg.message) ?? msg.message;
  const quotedM = normalize(m.extendedTextMessage?.contextInfo?.quotedMessage);
  const text = getText(m).trim();

  if (m.audioMessage) recentAudio.set(jid, { msg, at: Date.now() });

  if (text.toLowerCase() === '.menu') {
    await sock.sendMessage(jid, { text: MENU }, { quoted: msg });
    return;
  }

  if (text === '!ping') {
    await sock.sendMessage(jid, { text: 'pong' }, { quoted: msg });
    return;
  }

  if (/^\.aireset$/i.test(text)) {
    aiHistory.delete(jid);
    await sock.sendMessage(jid, { text: 'Riwayat obrolan AI dihapus.' }, { quoted: msg });
    return;
  }

  const aiMatch = text.match(/^\.ai\s+([\s\S]+)/i);
  if (aiMatch) {
    try {
      await sock.sendPresenceUpdate('composing', jid).catch(() => {});
      const answer = await askAI(jid, aiMatch[1].trim());
      await sock.sendMessage(jid, { text: answer }, { quoted: msg });
    } catch (err) {
      console.error('AI gagal:', err?.message);
      await sock.sendMessage(jid, { text: `AI gagal: ${err?.message}` }, { quoted: msg });
    }
    return;
  }

  if (/^!stickerft$/i.test(text)) {
    await handleStickerFT(sock, msg, m, quotedM);
    return;
  }

  if (/^!sticker\b/i.test(text)) {
    if (!hasVideo(m)) {
      await sock.sendMessage(jid, { text: 'Kirim video dengan caption !sticker, atau reply video dengan !sticker.' }, { quoted: msg });
      return;
    }
    await sock.sendMessage(jid, { text: 'Sedang membuat sticker...' }, { quoted: msg });
    try {
      const video = await downloadVideoForSoundSticker(msg, { mediaHost: sock.getMediaHost?.() });
      const converted = await videoToSoundSticker(video);
      await sendSoundSticker(sock, jid, converted, msg);
    } catch (err) {
      console.error('Sticker gagal:', err?.code, err?.message);
      await sock.sendMessage(jid, { text: `Gagal membuat sticker: ${err?.message || 'error tidak diketahui'}` }, { quoted: msg });
    }
  }
}

async function startBot() {
  const { state, saveCreds } = await useMultiFileAuthState(AUTH_DIR);

  const sock = makeWASocket({
    auth: state,
    logger: pino({ level: 'silent' }),
    browser: ['Ubuntu', 'Chrome', '20.0.04'],
    autoFollowChannel: false,
    printQRInTerminal: false,
  });

  sock.ev.on('creds.update', saveCreds);

  sock.ev.on('connection.update', async (update) => {
    const { connection, lastDisconnect } = update;
    if (connection === 'open') {
      console.log('Bot tersambung. Nomor:', ownNumber(sock.user?.id));
    }
    if (connection === 'close') {
      const code = lastDisconnect?.error?.output?.statusCode;
      if (code === DisconnectReason.loggedOut) {
        console.error('Perangkat dikeluarkan dari WhatsApp (loggedOut). Hapus folder auth lalu pairing ulang.');
        return;
      }
      if (code === DisconnectReason.connectionReplaced) {
        console.error('Sesi dipakai di tempat lain (connectionReplaced). Bot berhenti.');
        return;
      }
      console.log('Koneksi putus, mencoba lagi. Kode:', code);
      setTimeout(() => startBot().catch((e) => console.error('Start ulang gagal:', e)), 3000);
    }
  });

  sock.ev.on('messages.upsert', async ({ messages, type }) => {
    if (type !== 'notify') return;
    for (const msg of messages) {
      try {
        await handleMessage(sock, msg);
      } catch (err) {
        console.error('Error pesan:', err?.message);
      }
    }
  });

  if (!state.creds.registered) {
    if (!PAIRING_NUMBER) {
      console.log('Belum login. Isi BOT_NUMBER (format 62..., tanpa + dan 0) lalu restart.');
    } else {
      setTimeout(async () => {
        try {
          const code = await sock.requestPairingCode(PAIRING_NUMBER);
          console.log('KODE PAIRING:', code, '-> WhatsApp > Perangkat tertaut > Tautkan dengan nomor telepon');
        } catch (err) {
          console.error('Gagal minta kode pairing:', err?.message);
        }
      }, 3000);
    }
  }
}

startBot().catch((err) => console.error('Bot gagal start:', err));
