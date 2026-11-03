// TAK — Atari 2600 Text Adventure Kit
// Parser / rebuilder for the Dark Mage (Greg Troutman, 1997) 8K F8 text-adventure engine,
// plus a small 6502 + RIOT emulator for play-testing the real ROM code.
(function (root) {
  'use strict';

  // ---------- Character sets ----------
  // CLASSIC: Troutman's font in page $F5 (text byte = glyph offset). Q and - are this kit's
  // additions in the spare tail of that page.
  const CHAR = {
    A: 0x60, B: 0x2F, C: 0x3A, D: 0x34, E: 0x40, F: 0x48, G: 0x4E, H: 0x5C, I: 0x93, J: 0x0A,
    K: 0x66, L: 0x45, M: 0x70, N: 0x75, O: 0x54, P: 0x7B, Q: 0xF2, R: 0x2A, S: 0x81, T: 0x12,
    U: 0x59, V: 0x6C, W: 0x87, X: 0x8D, Y: 0x95, Z: 0x9B,
    ' ': 0x1E, '.': 0x1C, ',': 0x1B, "'": 0x18, '"': 0x18, '!': 0x10, '?': 0x05, ':': 0x24, '-': 0xF8,
  };
  const DECODE = {};
  for (const [k, v] of Object.entries(CHAR)) if (k !== '"') DECODE[v] = k;
  const EXTRA_GLYPHS = [0x76, 0xCC, 0xD6, 0xC6, 0xC6, 0x7C, /* Q (bottom row first) */
                        0x00, 0x00, 0x00, 0x7C, 0x00, 0x00  /* - */];
  // EXTENDED: this kit's own 7x6 font (A-Z, 0-9, punctuation), packed into one page.
  // Used automatically when the text needs a character the classic font lacks.
  const XCHAR = {"1":0,"7":5,"Z":10,"4":14,"9":20,"U":25,"H":28,"N":33,"R":38,"G":44,"O":49,"5":54,"L":59,"F":62,"E":67,"2":72,"0":77,"3":82,"/":88,"I":94,"Y":96,"P":102,"B":104,"D":110,"K":113,"(":119,")":123,";":129,":":132,"!":136,"T":138,"?":144,"C":149,"J":154,"V":160,"M":164,"W":169,"A":173,"X":176,"-":182,"+":186,"=":191,"'":196,",":199,".":200," ":202,"\"":205,"Q":211,"S":216,"8":221,"6":226};
  const XFONT = [120,48,48,48,112,48,48,24,12,6,254,96,48,24,12,254,204,108,60,28,120,12,126,198,198,124,198,198,198,198,198,254,198,198,206,222,246,230,198,204,252,198,198,252,126,198,198,206,192,124,198,198,198,198,124,198,6,252,192,254,192,192,192,192,192,248,192,254,192,192,248,192,254,96,56,12,198,124,230,246,222,206,124,198,6,56,12,252,192,96,48,24,12,6,120,48,48,48,48,120,204,204,192,192,252,198,198,252,198,252,248,204,198,198,204,248,240,216,204,24,48,96,96,48,24,12,12,24,48,96,48,0,48,48,0,48,48,0,48,48,48,48,48,252,24,0,24,12,198,124,198,192,192,198,124,198,198,6,6,14,16,56,108,198,198,198,214,254,238,198,238,254,214,198,198,254,198,108,56,56,108,198,0,0,0,124,0,0,48,252,48,0,0,252,0,252,0,0,0,96,48,48,0,0,0,0,0,0,72,108,108,118,204,214,198,198,124,198,6,124,192,124,198,198,124,198,124,198,198,252,96,60];
  const XDECODE = {};
  for (const [k, v] of Object.entries(XCHAR)) XDECODE[v] = k;
  const LINE_W = 12, MAX_LINES = 10;
  // Workshop engine text: bytes 0..NGLYPH-1 are glyph numbers (GMAP turns them into font offsets),
  // NGLYPH..$FD are dictionary words of the bank, $FF ends a line, $FE ends a message.
  const GLYPHS = Object.keys(XCHAR), NGLYPH = GLYPHS.length;
  const GIDX = {}; GLYPHS.forEach((c, i) => GIDX[c] = i);
  const GMAP = GLYPHS.map(c => XCHAR[c]);
  const MAXTOK = 0xFE - NGLYPH, DICT_MAX = 256, TOK_MAXLEN = 12;
  // cycles the line reader may spend on one line (the gap timer allows a little more; see test18)
  const PARSE_BASE = 175, PARSE_PLAIN = 21, PARSE_TOK = 52, PARSE_TOKCH = 18, PARSE_MAX = 590;
  const lineCost = (line, tokLen) => { let c = PARSE_BASE; for (let i = 0; i < line.length; i++) { const v = line.charCodeAt(i); c += v < NGLYPH ? PARSE_PLAIN : PARSE_TOK + PARSE_TOKCH * tokLen[v - NGLYPH]; } return c; };
  // Build one bank's dictionary from its messages (arrays of encoded bytes) and return the compressed
  // messages. Greedy: repeatedly take the substring that saves the most bytes.
  const dictCache = new Map();
  function takCompress(pages) {
    const ckey = pages.map(p => p.join(',')).join('|');
    if (dictCache.has(ckey)) return dictCache.get(ckey);
    // lines as strings of symbol codes, weighted by how many messages contain them
    const lineW = new Map();
    const split = pages.map(p => {
      const parts = []; let cur = '';
      for (const b of p) { if (b >= 0xFE) { parts.push([cur, b]); cur = ''; } else cur += String.fromCharCode(b); }
      return parts;
    });
    for (const parts of split) for (const [l] of parts) if (l.length > 1) lineW.set(l, (lineW.get(l) || 0) + 1);
    let lines = [...lineW.entries()].map(([l, w]) => ({ orig: l, cur: l, w }));
    const toks = []; let dictBytes = 0; const banned = new Set();
    while (toks.length < MAXTOK) {
      const cnt = new Map(), seenAt = new Map();
      lines.forEach((L, li) => {
        const t = L.cur;
        for (let i = 0; i < t.length - 1; i++) {
          if (t.charCodeAt(i) >= NGLYPH) continue;
          for (let n = 2; n <= TOK_MAXLEN && i + n <= t.length; n++) {
            if (t.charCodeAt(i + n - 1) >= NGLYPH) break;
            const sub = t.substr(i, n), last = seenAt.get(sub);
            if (last && last[0] === li && last[1] > i) continue; // overlaps the previous match in this line
            seenAt.set(sub, [li, i + n]);
            cnt.set(sub, (cnt.get(sub) || 0) + L.w);
          }
        }
      });
      let best = null, bs = 0;
      for (const [sub, c] of cnt) {
        if (banned.has(sub)) continue;
        const sc = c * (sub.length - 1) - (sub.length + 2);
        if (sc > bs || (sc === bs && best && sub < best)) { bs = sc; best = sub; }
      }
      if (!best) break;
      if (dictBytes + best.length + 1 > DICT_MAX) { banned.add(best); continue; }
      const tc = String.fromCharCode(NGLYPH + toks.length);
      toks.push(best); dictBytes += best.length + 1;
      for (const L of lines) if (L.cur.includes(best)) L.cur = L.cur.split(best).join(tc);
    }
    // keep every line inside the reader's cycle budget: re-apply tokens in order while they fit
    let tokLen = toks.map(t => t.length);
    const tokAt = new Map(toks.map((t, k) => [t, k]));
    // shortest encoding of a line with the finished dictionary (ties: fewer cycles)
    const best = (l) => {
      const dp = [{ n: 0, c: 0, s: '' }];
      for (let i = 1; i <= l.length; i++) {
        let b = { n: dp[i - 1].n + 1, c: dp[i - 1].c + PARSE_PLAIN, s: dp[i - 1].s + l[i - 1] };
        for (let n = 2; n <= Math.min(TOK_MAXLEN, i); n++) {
          const k = tokAt.get(l.substr(i - n, n)); if (k === undefined) continue;
          const p = dp[i - n], c = p.c + PARSE_TOK + PARSE_TOKCH * n;
          if (p.n + 1 < b.n || (p.n + 1 === b.n && c < b.c)) b = { n: p.n + 1, c, s: p.s + String.fromCharCode(NGLYPH + k) };
        }
        dp[i] = b;
      }
      return dp[l.length].s;
    };
    const enc = new Map();
    for (const L of lines) {
      let t = best(L.orig);
      if (lineCost(t, tokLen) > PARSE_MAX) {
        // keep every line inside the reader's cycle budget: apply tokens in order while they fit
        t = L.orig;
        toks.forEach((tk, k) => { const u = t.split(tk).join(String.fromCharCode(NGLYPH + k)); if (u !== t && lineCost(u, tokLen) <= PARSE_MAX) t = u; });
      }
      enc.set(L.orig, t);
    }
    // drop words that ended up unused and renumber
    const used = new Set();
    for (const t of enc.values()) for (const ch of t) { const v = ch.charCodeAt(0); if (v >= NGLYPH) used.add(v - NGLYPH); }
    const keep = toks.map((_, k) => k).filter(k => used.has(k)), renum = new Map(keep.map((k, i) => [k, i]));
    for (const [o, t] of enc) enc.set(o, [...t].map(ch => { const v = ch.charCodeAt(0); return v >= NGLYPH ? String.fromCharCode(NGLYPH + renum.get(v - NGLYPH)) : ch; }).join(''));
    const toks2 = keep.map(k => toks[k]);
    dictBytes = toks2.reduce((t, w) => t + w.length + 1, 0);
    const out = split.map(parts => parts.flatMap(([l, end]) => [...(enc.get(l) || l)].map(c => c.charCodeAt(0)).concat([end])));
    const res = { toks: toks2.map(t => [...t].map(c => c.charCodeAt(0))), pages: out, dictBytes };
    if (dictCache.size > 64) dictCache.clear();
    dictCache.set(ckey, res);
    return res;
  }
  // read Workshop-engine text from a bank (expanding dictionary words) -> lines of font offsets
  function takLines(bk, a, menuWord) {
    const rdw = o => bk[o - BASE] | (bk[o + 1 - BASE] << 8);
    const toklo = rdw(0xFFD8), tpage = bk[0xFFDA - BASE], gmap = rdw(0xFFDB), ng = bk[0xFFDD - BASE];
    const lines = []; let line = [], i = a - BASE, n = 0;
    while (i >= 0 && i < 4096 && n++ < 400) {
      const v = bk[i++];
      if (v === 0xFE) break;
      if (v === 0xFF) { lines.push(line); line = []; if (menuWord) return lines; continue; }
      if (v < ng) line.push(bk[gmap + v - BASE]);
      else { let j = (tpage << 8 | bk[toklo + v - ng - BASE]) - BASE, m = 0; while (j >= 0 && j < 4096 && bk[j] < 0x80 && m++ < 16) line.push(bk[gmap + bk[j++] - BASE]); }
    }
    if (line.length) lines.push(line);
    return lines;
  }
  const SUBST = { '`': "'", '&': '+', '*': '+', '[': '(', ']': ')', '{': '(', '}': ')', '_': '-', '#': '+', '<': '(', '>': ')', '|': '!', '%': '/', '~': '-', '@': 'A', '$': 'S', '\\': '/' };
  let ENC = CHAR; // active encoding while building

  function normText(s) {
    return String(s || '').toUpperCase().replace(/\r/g, '');
  }
  function badChars(s) {
    const bad = new Set();
    for (const ch of normText(s)) if (ch !== '\n' && !(ch in XCHAR)) bad.add(ch);
    return [...bad];
  }
  // which font a project needs: 'classic' unless some text uses a character only the extended font has
  function allTexts(P) {
    const t = [...P.intro, ...P.items, ...Object.values(P.system)];
    for (const m of P.maps) for (const c of m.cells) {
      if (c.type === 'wall') t.push(c.text); else t.push(c.desc, c.look, c.take.text, c.use.text, c.give.text, c.talk.ok, c.talk.no, c.door.text);
    }
    return t;
  }
  function fontMode(P) {
    for (const t of allTexts(P)) for (const ch of normText(t)) if (ch !== '\n' && !(ch in CHAR) && ((ch in XCHAR) || SUBST[ch])) return 'extended';
    return 'classic';
  }
  // encode a page of text (lines joined with \n) -> bytes (each line + $FF, then $FE)
  function encodePage(s, menuWord) {
    const lines = normText(s).split('\n');
    const out = [];
    for (const line of lines) {
      for (const ch of line.slice(0, LINE_W)) out.push(ENC[ch] !== undefined ? ENC[ch] : (ENC[SUBST[ch]] !== undefined ? ENC[SUBST[ch]] : ENC[' ']));
      out.push(0xFF);
      if (menuWord) break;
    }
    if (!menuWord) out.push(0xFE);
    return out;
  }
  function checkPage(s, label, errs, warns, opts = {}) {
    const lines = normText(s).split('\n');
    const maxL = opts.menuWord ? 1 : MAX_LINES;
    if (opts.menuWord && lines.length > 1) errs.push(`${label}: menu words must be a single line`);
    else if (lines.length > maxL) errs.push(`${label}: ${lines.length} lines (max ${maxL})`);
    lines.forEach((l, i) => { if (l.length > LINE_W) errs.push(`${label}: line ${i + 1} is ${l.length} characters (max ${LINE_W})`); });
    const bad = badChars(s);
    if (bad.length) warns.push(`${label}: no glyph for ${bad.map(c => JSON.stringify(c)).join(' ')} (${bad.map(c => SUBST[c] ? c + '→' + SUBST[c] : c + '→space').join(', ')})`);
  }

  // ---------- Engine knowledge ----------
  const BASE = 0xF000;
  // code sites holding "LDA #lo / STA zp / LDA #hi / STA zp+1"  (lo at +1, hi at +5)
  const SITE = {
    bootText: 0xF039, startText: 0xF074, firstMenuWord: 0xF07C, nothingSpecial: 0xF29F,
    nothingToTake: 0xF2F5, talkDefault: 0xF328, selectGive: 0xF33D, cantGive: 0xF37D,
    selectUse: 0xF392, cantUse: 0xF3C0, carrying: 0xF3D5, itemTable: 0xF3FB, roomTable: 0xF5A1,
    introMenuWord: 0xF5D5,
  };
  const IMM = { introPages: 0xF046 - 1, startRoom: 0xF06D, startInv: 0xF071, portalB: 0xF259, portalA: 0xF261, widthN: 0xF212, widthS: 0xF21C };
  // IMM.introPages: LDA #$04 at F044 -> operand F045
  IMM.introPages = 0xF045;
  const TBL = { introMenu: 0xF4C6, introHandlers: 0xF4CA, introPages: 0xF4CE, moveMenu: 0xF4D8, actMenu: 0xF4EC };
  // hook sites: original engine bytes, restored whenever a fix is not used
  const HOOK = {
    gate: { at: 0xF04D, orig: [0x20, 0xAB, 0xF0] },                       // JSR $F0AB (read controls)
    portal: { at: 0xF223, orig: [0x20, 0x58, 0xF2] },                     // JSR $F258 (two hard-wired bank switches)
    reboot: { at: 0xF05D, orig: [0xAD, 0xF9, 0xFF] },                     // LDA $FFF9 (restart in the start bank)
    blocked: { at: 0xF241, orig: [0xA5, 0xA5, 0x85, 0xA2] },               // LDA $A5 / STA $A2 (turned away: restore the room)
    door: { at: 0xF237, orig: [0xA0, 0x07, 0xB1, 0xA3, 0x25, 0xAC, 0xD0, 0x0F] }, // LDY #7 / LDA (rec),Y / AND events / BNE open
    startInv: { at: 0xF070, orig: [0xA9, 0x01, 0x85, 0xA7] },             // LDA #inv / STA $A7
    lookHandler: { at: 0xF4E2, orig: [0x68, 0xF2] },                      // move-menu handler 0 (LOOK)
    actHandlers: { at: 0xF4F8, orig: [0xAA, 0xF2, 0xC8, 0xF2, 0x33, 0xF3, 0x88, 0xF3, 0x00, 0xF3, 0xCB, 0xF3] }, // GO TAKE GIVE USE TALK INVENTORY
    empty: { at: 0xF42C, orig: [0xA5, 0x81, 0x85, 0xBF] },                // LDA $81 / STA $BF (item-menu count)
    use: { at: 0xF3B4, orig: [0x05, 0xA9, 0x85, 0xA9, 0xA0, 0x0E] },     // ORA $A9 / STA $A9 / LDY #$0E (USE success)
    fontPage: { at: 0xF031, orig: [0xA9, 0xF5] },                         // LDA #$F5 (glyph pointer page)
    space: { at: 0xF171, orig: [0xA9, 0x1E] },                            // LDA #$1E (blank character)
  };
  const COLOR = { text: 0xF159, bg: 0xF15F, menuBg: 0xF1B7, menuText: 0xF1BB };
  const DEFAULT_COLORS = { bg: 0x42, text: 0x1A, menuBg: 0x56, menuText: 0x1D };
  const FONT_SUM = 0xdf9e4388; // fingerprint of Troutman's font, $F504-$F5A0
  const DATA_START = 0xF5F2, LIMIT = 0xFFF8;
  // cartridge formats: hotspot base (bank k is selected by reading base + k), and the bank
  // the game starts in (Map A lives there). Data must stay below the first hotspot.
  const CARTS = {
    '8K': { banks: 2, base: 0xFFF8, start: 1, scheme: 'F8' },
    '16K': { banks: 4, base: 0xFFF6, start: 0, scheme: 'F6' },
    '32K': { banks: 8, base: 0xFFF4, start: 0, scheme: 'F4' },
    '64K': { banks: 16, base: 0xFFE0, start: 0, scheme: 'EF', takOnly: true }, // hotspots $FFE0-$FFEF; "EFEF" at $FFF8 marks it
  };
  const LETTERS = 'ABCDEFGHIJKLMNOP';
  // which bank holds each map: Map A in the start bank, the others in the remaining banks in order
  function bankOrder(cart) { const c = CARTS[cart]; const o = [c.start]; for (let b = 0; b < c.banks; b++) if (b !== c.start) o.push(b); return o; }
  function mapOfBank(cart, bank) { return bankOrder(cart).indexOf(bank); } // never place data on bank-switch hotspots
  const MOVE_WORDS = ['look', 'north', 'east', 'south', 'west'];
  const ACT_WORDS = ['go', 'take', 'give', 'use', 'talk', 'inventory'];
  const SYS_MSGS = ['nothingSpecial', 'nothingToTake', 'talkDefault', 'selectGive', 'cantGive', 'selectUse', 'cantUse', 'carrying'];

  function rd(bk, a) { return bk[a - BASE]; }
  function rw(bk, a) { return bk[a - BASE] | (bk[a - BASE + 1] << 8); }
  function sitePtr(bk, site) { return bk[site + 1 - BASE] | (bk[site + 5 - BASE] << 8); }
  function setSite(bk, site, v) { bk[site + 1 - BASE] = v & 0xFF; bk[site + 5 - BASE] = v >> 8; }

  function isEngine(rom) {
    if (!rom || rom.length !== 8192) return 'ROM must be an 8K (8192-byte) F8 image';
    for (let b = 0; b < 2; b++) {
      const bk = rom.subarray(b * 4096, b * 4096 + 4096);
      // text kernel / room lookup / bank-switch compare signatures
      const want = [[0xF43B, [0xA2, 0x04, 0x85, 0x02]], [0xF5A9, [0xA4, 0xA2, 0xC8, 0xB1, 0xA3]], [0xF258, [0xC9]], [0xF25C, [0xAE, 0xF8, 0xFF]], [0xF264, [0xAE, 0xF9, 0xFF]], [0xF17F, [0xB1, 0x9C, 0xC8, 0xC9, 0xFF]]];
      for (const [a, bytes] of want) for (let i = 0; i < bytes.length; i++) if (rd(bk, a + i) !== bytes[i]) return 'This ROM does not contain the Dark Mage text engine (signature mismatch in bank ' + b + ')';
      let sum = 0; for (let a = 0xF504; a < 0xF5A1; a++) sum = (Math.imul(sum, 31) + rd(bk, a)) >>> 0;
      const modified = sum !== FONT_SUM || Object.values(HOOK).some(h => h.orig.some((v, i) => rd(bk, h.at + i) !== v));
      if (modified) return 'This is a modified copy of Dark Mage (perhaps a cartridge built here). Load the original Dark Mage ROM as the engine';
    }
    return null;
  }

  function readText(bk, a, menuWord, dec = DECODE) {
    let s = '', i = a - BASE, n = 0;
    while (i >= 0 && i < 4096 && n++ < 400) {
      const v = bk[i++];
      if (v === 0xFE) break;
      if (v === 0xFF) { if (menuWord) break; s += '\n'; continue; }
      s += dec[v] !== undefined ? dec[v] : ' ';
    }
    return s.replace(/\n$/, '');
  }
  function maskToIdx(m) { if (!m) return null; for (let i = 0; i < 8; i++) if (m & (1 << i)) return i; return null; }

  // ---------- Parse a ROM into an editable project ----------
  function parseRom(rom) {
    const err = isEngine(rom); if (err) throw new Error(err);
    const banks = [rom.subarray(0, 4096), rom.subarray(4096, 8192)];
    const A = banks[1], B = banks[0]; // Map A = bank 1 (power-on / start), Map B = bank 0
    const width = rd(A, IMM.widthN) >> 1;
    const sys = {};
    MOVE_WORDS.forEach((k, i) => sys[k] = readText(A, rw(A, TBL.moveMenu + 2 * i), true));
    ACT_WORDS.forEach((k, i) => sys[k] = readText(A, rw(A, TBL.actMenu + 2 * i), true));
    sys.more = readText(A, rw(A, TBL.introMenu), true);
    sys.start = readText(A, rw(A, TBL.introMenu + 2), true);
    for (const k of SYS_MSGS) sys[k] = readText(A, sitePtr(A, SITE[k]));
    sys.bootB = readText(B, sitePtr(B, SITE.bootText)).split('\n').slice(0, MAX_LINES).join('\n');
    if (!sys.bootB.trim()) sys.bootB = '';
    const itemTbl = sitePtr(A, SITE.itemTable);
    const items = [];
    for (let i = 0; i < 8; i++) items.push(readText(A, rw(A, itemTbl + 2 * i), true));
    // intro pages: first page from boot pointer; then table[n-1] .. table[0]
    const nPages = rd(A, IMM.introPages);
    const intro = [readText(A, sitePtr(A, SITE.bootText))];
    for (let k = nPages - 1; k >= 0; k--) intro.push(readText(A, rw(A, TBL.introPages + 2 * k)));
    const portalA = rd(A, IMM.portalB) >> 1; // index in Map A that leads into Map B (CMP #$2C -> bank0)
    const portalB = rd(A, IMM.portalA) >> 1; // index in Map B that leads into Map A (CMP #$2A -> bank1)
    const maps = [];
    for (const [bk, name, portal] of [[A, 'Map A', portalA], [B, 'Map B', portalB]]) {
      const tbl = sitePtr(bk, SITE.roomTable);
      // table length: entries until we hit something that isn't a plausible record pointer
      let n = 0;
      while (n < 128) {
        const p = rw(bk, tbl + 2 * n);
        if (p < DATA_START || p >= LIMIT) break;
        const f = rd(bk, p);
        if (f === 0) { const m = rw(bk, p + 1); if (m < DATA_START || m >= LIMIT) break; }
        n++;
      }
      n = Math.floor(n / width) * width;
      const cells = [];
      for (let i = 0; i < n; i++) {
        const p = rw(bk, tbl + 2 * i);
        const b = [...bk.subarray(p - BASE, p - BASE + 8)];
        const ptr = k => rw(bk, p + 8 + 2 * k);
        if (b[0] === 0) { cells.push({ type: 'wall', text: readText(bk, rw(bk, p + 1)) }); continue; }
        const f = b[0];
        const c = {
          type: 'room', name: '',
          desc: readText(bk, ptr(0)), look: readText(bk, ptr(1)),
          lookReveals: !(f & 0x80) && !!b[1],
          item: maskToIdx(b[2] || b[1]),
          take: { on: !!(f & 0x40), text: (f & 0x40) ? readText(bk, ptr(2)) : '' },
          use: { on: !!(f & 0x10), item: maskToIdx(b[3]), text: (f & 0x10) ? readText(bk, ptr(3)) : '' },
          give: { on: !!(f & 0x20), item: maskToIdx(b[4]), text: (f & 0x20) ? readText(bk, ptr(4)) : '' },
          talk: { on: !!(f & 0x08), needUsed: maskToIdx(b[5]), ok: (f & 0x08) && b[5] ? readText(bk, ptr(5)) : '', no: (f & 0x08) ? readText(bk, ptr(7)) : '' },
          sets: maskToIdx(b[6]),
          door: { on: !!(f & 0x02), needEvent: maskToIdx(b[7]), text: (f & 0x02) ? readText(bk, ptr(6)) : '' },
          ending: false,
        };
        c.use.setsEvent = false;
        c.name = c.desc.replace(/\n/g, ' ').replace(/^YOU ARE (IN|ON|AT|STANDING ON)( A| THE)?\s*/i, '').replace(/\s+/g, ' ').trim().slice(0, 28) || 'Room ' + i;
        cells.push(c);
      }
      const colors = { bg: rd(bk, COLOR.bg), text: rd(bk, COLOR.text), menuBg: rd(bk, COLOR.menuBg), menuText: rd(bk, COLOR.menuText) };
      maps.push({ name, width, rows: n / width, cells, colors });
    }
    return {
      kit: 'tak', version: 1, title: 'Untitled adventure', engine: 'darkmage',
      cart: '8K',
      settings: { endEvent: null },
      portals: [{ map: 0, idx: portalA, toMap: 1, toIdx: portalA }, { map: 1, idx: portalB, toMap: 0, toIdx: portalB }],
      start: { room: rd(A, IMM.startRoom) >> 1, inventory: [0, 1, 2, 3, 4, 5, 6, 7].filter(i => rd(A, IMM.startInv) & (1 << i)) },
      items, events: ['Event 1', 'Event 2', 'Event 3', 'Event 4', 'Event 5', 'Event 6', 'Event 7', 'Event 8'],
      system: Object.assign(sys, { theEnd: 'THE END', nothing: 'NOTHING' }), intro, maps,
    };
  }

  // fill in fields that older project files lack
  function normalize(P) {
    if (!P.cart) P.cart = '8K';
    if (!P.engine) P.engine = 'darkmage'; // files saved before the Workshop engine existed
    if (!P.portals) {
      const a = P.settings.portalA, b = P.settings.portalB;
      P.portals = [{ map: 0, idx: a, toMap: 1, toIdx: a }, { map: 1, idx: b, toMap: 0, toIdx: b }];
    }
    if (P.settings.width != null) { for (const m of P.maps) if (m.width == null) m.width = P.settings.width; }
    delete P.settings.width; delete P.settings.portalA; delete P.settings.portalB;
    P.maps.forEach((m, i) => { if (m.width == null) m.width = 6; m.name = 'Map ' + LETTERS[i]; });
    P.settings.endEvent = P.settings.endEvent === undefined ? null : P.settings.endEvent;
    if (P.system.theEnd == null) P.system.theEnd = 'THE END';
    if (P.system.nothing == null) P.system.nothing = 'NOTHING';
    if (!P.events) P.events = [];
    while (P.events.length < 16) P.events.push('Event ' + (P.events.length + 1));
    while (P.items.length < 16) P.items.push('');
    for (const m of P.maps) {
      if (!m.colors) m.colors = Object.assign({}, DEFAULT_COLORS);
      for (const c of m.cells) if (c.type === 'room') { if (c.ending == null) c.ending = false; if (c.use.setsEvent == null) c.use.setsEvent = false; }
    }
    return P;
  }
  // the original engine's portal code: 8K, exactly one gateway each way, landing on the same grid index
  function isLegacyPortals(P) {
    if (P.engine === 'tak' || P.cart !== '8K' || P.portals.length !== 2) return false;
    const a = P.portals.find(p => p.map === 0), b = P.portals.find(p => p.map === 1);
    return !!(a && b && a.toMap === 1 && a.toIdx === a.idx && b.toMap === 0 && b.toIdx === b.idx && a.idx !== b.idx);
  }
  // does the game reference item or event 9-16? Then it needs the wide (16-bit) game logic.
  function wideNeeded(P) {
    const hi = v => v != null && v >= 8;
    if (P.start.inventory.some(hi) || hi(P.settings.endEvent)) return true;
    return P.maps.some(m => m.cells.some(c => c.type === 'room' &&
      (hi(c.item) || (c.use.on && hi(c.use.item)) || (c.give.on && hi(c.give.item)) || (c.talk.on && hi(c.talk.needUsed)) || hi(c.sets) || (c.door.on && hi(c.door.needEvent)))));
  }
  function portalAt(P, m, idx) { return P.portals.find(p => p.map === m && p.idx === idx) || null; }
  // which engine fixes a project needs
  function fixesNeeded(P) {
    const given = new Set();
    let endingRooms = false, useEvents = false;
    P.maps.forEach((m, mi) => m.cells.forEach((c, i) => {
      if (c.type !== 'room') return;
      if (c.give.on && c.give.item != null) given.add(c.give.item);
      if (c.ending) endingRooms = true;
      if (c.use.on && c.use.setsEvent && c.sets != null) useEvents = true;
    }));
    const wide = wideNeeded(P);
    return {
      wide,                                                 // 16 items / 16 events: replaces the game-logic handlers
      empty: !wide && !P.start.inventory.some(i => !given.has(i)),  // inventory could become empty (wide mode handles it)
      gate: endingRooms || P.settings.endEvent != null,     // the game can end
      use: !wide && useEvents,                              // USE can set events (wide mode handles it)
      portal: !isLegacyPortals(P),                          // general portal table instead of the two CMPs
      font: fontMode(P),
    };
  }

  // ---------- Exits / validation helpers ----------
  function neighbors(project, mapIdx, idx) {
    const W = project.maps[mapIdx].width, a = idx * 2;
    const res = {};
    const own = project.maps[mapIdx].cells;
    for (const [dir, d] of [['N', -2 * W], ['E', 2], ['S', 2 * W], ['W', -2]]) {
      const t = (a + d) & 0xFF, ti = t >> 1;
      const pt = portalAt(project, mapIdx, ti);
      const map = pt ? pt.toMap : mapIdx, di = pt ? pt.toIdx : ti;
      const cells = project.maps[map] ? project.maps[map].cells : [];
      const wrap = (dir === 'E' && (idx % W) === W - 1) || (dir === 'W' && (idx % W) === 0);
      res[dir] = { map, idx: di, valid: ti < own.length && di < cells.length, wrap, portal: !!pt, cell: cells[di] };
    }
    return res;
  }

  function validate(project) {
    const errs = [], warns = [];
    const P = normalize(project);
    const cart = CARTS[P.cart];
    if (!cart) errs.push('Unknown cartridge size');
    else if (P.maps.length !== cart.banks) errs.push(`A ${P.cart} cartridge needs ${cart.banks} maps`);
    if (cart && cart.takOnly && P.engine !== 'tak') errs.push(`${P.cart} cartridges need the Workshop engine (Story & items › Engine)`);
    P.maps.forEach(m => {
      if (!(m.width >= 2 && m.width <= 16)) errs.push(`${m.name}: width must be 2 to 16 columns`);
      if (m.cells.length !== m.rows * m.width) errs.push(`${m.name}: cell count mismatch`);
      if (m.cells.length > 128) errs.push(`${m.name}: too many cells (max 128)`);
    });
    const at = (m, i) => `${P.maps[m] ? P.maps[m].name : 'Map ?'} r${Math.floor(i / (P.maps[m] || { width: 1 }).width) + 1}c${(i % (P.maps[m] || { width: 1 }).width) + 1}`;
    const seen = new Set();
    for (const p of P.portals) {
      const k = p.map + ':' + p.idx;
      if (seen.has(k)) errs.push(`${at(p.map, p.idx)}: two portals on the same cell`); seen.add(k);
      if (!P.maps[p.map] || p.idx >= P.maps[p.map].cells.length) { errs.push('A portal sits outside its map'); continue; }
      if (!P.maps[p.toMap] || p.toIdx >= P.maps[p.toMap].cells.length) { errs.push(`${at(p.map, p.idx)}: portal leads outside ${P.maps[p.toMap] ? P.maps[p.toMap].name : 'any map'}`); continue; }
      const dest = P.maps[p.toMap].cells[p.toIdx];
      if (portalAt(P, p.toMap, p.toIdx)) errs.push(`${at(p.map, p.idx)}: portal leads onto another portal cell`);
      else if (dest.type !== 'room') errs.push(`${at(p.map, p.idx)}: portal leads into a wall at ${at(p.toMap, p.toIdx)}`);
      else if (dest.door.on && isLegacyPortals(P)) warns.push(`${at(p.map, p.idx)}: portal leads into a locked room. With the original two gateways, a player turned away there is stranded on the wrong map (Dark Mage's quirk). Add any other portal, or use 16K/32K, to get the fixed portal code.`);
    }
    const sr = P.start.room;
    if (!P.maps[0].cells[sr] || P.maps[0].cells[sr].type !== 'room') errs.push('Start room must be a room in Map A');
    if (portalAt(P, 0, sr)) errs.push('Start room cannot be a portal cell');
    if (P.intro.length < 2 || P.intro.length > 6) errs.push('Intro must have 2 to 6 pages');
    P.intro.forEach((t, i) => checkPage(t, `Intro page ${i + 1}`, errs, warns));
    P.items.forEach((t, i) => { if (i < 8 || normText(t).trim()) checkPage(t, `Item ${i + 1} name`, errs, warns, { menuWord: true }); });
    for (const k of [...MOVE_WORDS, ...ACT_WORDS, 'more', 'start']) checkPage(P.system[k], `Menu word "${k}"`, errs, warns, { menuWord: true });
    for (const k of SYS_MSGS) checkPage(P.system[k], `System message "${k}"`, errs, warns);
    checkPage(P.system.theEnd, 'Menu word "the end"', errs, warns, { menuWord: true });
    checkPage(P.system.nothing, 'Menu word "nothing"', errs, warns, { menuWord: true });
    if (P.settings.endEvent != null && !P.maps.some(m => m.cells.some(c => c.type === 'room' && c.sets === P.settings.endEvent && (c.give.on || c.talk.on || (c.use.on && c.use.setsEvent)))))
      warns.push('No room ever sets the event that ends the game');
    if (P.maps.some(m => m.cells.some(c => c.type === 'room' && c.use.on && c.use.setsEvent && c.sets == null)))
      warns.push('A room\'s USE is set to trigger an event, but that room has no event chosen');
    checkPage(P.system.bootB, 'Power-on screen for other banks', errs, warns);
    P.maps.forEach((m, mi) => m.cells.forEach((c, i) => {
      if (portalAt(P, mi, i)) return; // never read by the engine
      const lbl = at(mi, i);
      if (c.type === 'wall') { checkPage(c.text, lbl + ' wall text', errs, warns); return; }
      const L = lbl + ` (${c.name || 'room'})`;
      checkPage(c.desc, L + ' description', errs, warns);
      checkPage(c.look, L + ' LOOK text', errs, warns);
      if (c.take.on) { checkPage(c.take.text, L + ' TAKE text', errs, warns); if (c.item == null) errs.push(L + ': TAKE is on but no item is set'); }
      if (c.use.on) { checkPage(c.use.text, L + ' USE text', errs, warns); if (c.use.item == null) errs.push(L + ': USE is on but no item chosen'); }
      if (c.give.on) { checkPage(c.give.text, L + ' GIVE text', errs, warns); if (c.give.item == null) errs.push(L + ': GIVE is on but no item chosen'); }
      if (c.talk.on) { checkPage(c.talk.ok, L + ' TALK (success) text', errs, warns); checkPage(c.talk.no, L + ' TALK (default) text', errs, warns); }
      if (c.door.on) { checkPage(c.door.text, L + ' blocked text', errs, warns); if (c.door.needEvent == null) errs.push(L + ': locked room needs an event'); }
      const nb = neighbors(P, mi, i);
      for (const [d, n] of Object.entries(nb)) {
        if (!n.valid) errs.push(`${L}: going ${d} leaves the map (put a wall cell there)`);
        else if (n.wrap && n.cell && n.cell.type === 'room') warns.push(`${L}: going ${d} wraps around to the other edge of the map`);
      }
    }));
    return { errs, warns };
  }

  // ---------- Build ----------
  // Writer: a main growing region plus optional small holes that strings can fill (first fit).
  class Writer {
    constructor(bk, start, limit, holes) {
      this.bk = bk; this.pc = start; this.cache = new Map(); this.limit = limit || LIMIT;
      this.holes = (holes || []).map(([a, b]) => ({ pc: a, end: b, start: a }));
      this.searchFrom = start;
    }
    put(bytes) { const a = this.pc; if (a + bytes.length > this.limit) throw new Error('OUT_OF_SPACE'); for (const b of bytes) this.bk[this.pc++ - BASE] = b; return a; }
    find(bytes, from, to) {
      outer: for (let i = from - BASE; i + bytes.length <= to - BASE; i++) {
        for (let j = 0; j < bytes.length; j++) if (this.bk[i + j] !== bytes[j]) continue outer;
        return i + BASE;
      }
      return -1;
    }
    // place a string, reusing any identical byte run already written
    str(bytes) {
      const key = bytes.join(',');
      if (this.cache.has(key)) return this.cache.get(key);
      let a = this.find(bytes, this.searchFrom, this.pc);
      for (const h of this.holes) if (a < 0) a = this.find(bytes, h.start, h.pc);
      if (a < 0) {
        const h = this.holes.find(h => h.pc + bytes.length <= h.end);
        if (h) { a = h.pc; for (const b of bytes) this.bk[h.pc++ - BASE] = b; }
        else a = this.put(bytes);
      }
      this.cache.set(key, a); return a;
    }
  }

  function bit(i) { return i == null ? 0 : (1 << i); }
  const lo = a => a & 0xFF, hi = a => (a >> 8) & 0xFF;

  // 6502 routines added by the kit (assembled by hand; see the engine notes)
  function asmGate(at, endMask, endWord) {
    // LDA $AC / AND #mask / BNE end / JSR $F5A1 / LDY #0 / LDA ($A3),Y / LSR / BCS end / JMP $F0AB
    // end: LDA #<word / STA $9E / LDA #>word / STA $9F / RTS
    return [0xA5, 0xAC, 0x29, endMask, 0xD0, 0x0D, 0x20, 0xA1, 0xF5, 0xA0, 0x00, 0xB1, 0xA3, 0x4A, 0xB0, 0x03, 0x4C, 0xAB, 0xF0,
      0xA9, lo(endWord), 0x85, 0x9E, 0xA9, hi(endWord), 0x85, 0x9F, 0x60];
  }
  function asmEmpty(nothingWord) {
    // LDA $81 / BNE ok / point item slot 0 at "NOTHING", item bit 0, count 1 / ok: STA $BF / RTS
    return [0xA5, 0x81, 0xD0, 0x0E, 0xA9, lo(nothingWord), 0x85, 0xAF, 0xA9, hi(nothingWord), 0x85, 0xB0, 0xA9, 0x00, 0x85, 0xC4, 0xA9, 0x01, 0x85, 0xBF, 0x60];
  }
  function asmUse() {
    // ORA $A9 / STA $A9 / if flags & 4: events |= byte6 / LDY #$0E / RTS
    return [0x05, 0xA9, 0x85, 0xA9, 0xA0, 0x00, 0xB1, 0xA3, 0x29, 0x04, 0xF0, 0x08, 0xA0, 0x06, 0xB1, 0xA3, 0x05, 0xAC, 0x85, 0xAC, 0xA0, 0x0E, 0x60];
  }
  // Portal table per bank: [own hotspot] then entries [from*2, hotspot, dest*2, msg lo, msg hi], $FF ends.
  // On a match the routine remembers where the player came from ($AA = that bank's hotspot) and the
  // copy of the destination's "locked" message kept in this bank ($AB/$A1), then switches banks.
  // The RTS runs in the new bank: every bank has this routine at the same address.
  function portalSource() {
    return [
      'LDX #0',
      'pLoop: LDY PT+1,X', 'CPY #$FF', 'BEQ pNone', 'CMP PT+1,X', 'BEQ pHit',
      'INX', 'INX', 'INX', 'INX', 'INX', 'BNE pLoop',
      'pHit: LDY PT', 'STY $AA', 'LDY PT+4,X', 'STY $AB', 'LDY PT+5,X', 'STY $A1',
      'LDA PT+3,X', 'LDY PT+2,X', 'LDX $FF00,Y', 'RTS',
      'pNone: LDX #0', 'STX $AA', 'RTS',
      // turned away by a lock: if a portal brought us here, show the copied message, return to the
      // bank we came from and finish the move there (the player stays where they were)
      'pBack: LDA $A5', 'STA $A2', 'LDY $AA', 'BEQ pB1', 'LDA #0', 'STA $AA', 'PLA', 'PLA',
      'LDA $AB', 'STA $9C', 'LDA $A1', 'STA $9D', 'LDA $FF00,Y', 'JMP $F253',
      'pB1: RTS',
    ];
  }
  function asmPortal(at, tbl) { return assemble(portalSource(), at, { PT: tbl }); }
  const portalLen = () => asmPortal(0xF000, 0xF000).bytes.length;
  const GATE_LEN = 28, EMPTY_LEN = 21, USE_LEN = 23;

  // Wide game logic: 16 items and 16 events. State bytes get a second byte $1E above the first
  // (taken $A6/$C4, inventory $A7/$C5, revealed $A8/$C6, used $A9/$C7, events $AC/$CA), and room
  // records hold item/event numbers ($FF = none) instead of bit masks:
  //   0 flags, 1 item here, 2 USE item, 3 GIVE item, 4 TALK needs used, 5 event set, 6 lock event
  // The item menu lists item numbers at $AF-$BE and name pointers at $CE-$ED.
  function wideSource() {
    return [
      // shared helpers. X = item/event number, Y = address of the state byte (its high byte is $1E above)
      'bTst: LDA $0000,Y', 'AND ML,X', 'BNE bT1', 'LDA $001E,Y', 'AND MH,X', 'bT1: RTS',                      // Z clear if set
      'bSet: LDA $0000,Y', 'ORA ML,X', 'STA $0000,Y', 'LDA $001E,Y', 'ORA MH,X', 'STA $001E,Y', 'RTS',
      'bClr: LDA ML,X', 'EOR #$FF', 'AND $0000,Y', 'STA $0000,Y', 'LDA MH,X', 'EOR #$FF', 'AND $001E,Y', 'STA $001E,Y', 'RTS',
      'rec0: JSR $F5A1', 'LDY #0', 'LDA ($A3),Y', 'RTS',                                                     // room flags
      'getF: LDA ($A3),Y', 'TAX', 'CMP #$FF', 'RTS',                                                          // field Y -> X (Z set if none)
      'say: JSR $F5E8', 'JMP $F2AF',                                                                          // show record text Y, back to walking
      // LOOK: show the LOOK text; reveal the item here unless it was already taken
      'wLook: JSR $F5A1', 'LDY #$0A', 'JSR $F5E8', 'LDY #0', 'LDA ($A3),Y', 'BEQ wLM', 'BMI wLM',
      'LDY #1', 'JSR getF', 'BEQ wLM', 'LDY #TK', 'JSR bTst', 'BNE wLN', 'LDY #SEEN', 'JSR bSet',
      'wLM: JMP $F288', 'wLN: JMP $F29F',
      // TAKE: the item here, if revealed, not taken before and not carried
      'wTake: JSR rec0', 'AND #$40', 'BEQ wTN', 'LDY #1', 'JSR getF', 'BEQ wTN',
      'LDY #TK', 'JSR bTst', 'BNE wTN', 'LDY #INV', 'JSR bTst', 'BNE wTN', 'LDY #SEEN', 'JSR bTst', 'BEQ wTN',
      'LDY #INV', 'JSR bSet', 'LDY #TK', 'JSR bSet', 'LDY #$0C', 'JMP say', 'wTN: JMP $F2F5',
      // GIVE / USE / INVENTORY open the item menu; MODE says what picking an item does
      'wGive: LDX #1', 'LDA #<SELGIVE', 'LDY #>SELGIVE', 'BNE wOpen',
      'wUse: LDX #2', 'LDA #<SELUSE', 'LDY #>SELUSE', 'BNE wOpen',
      'wInv: LDX #0', 'LDA #<CARRY', 'LDY #>CARRY',
      'wOpen: STX MODE', 'STA $9C', 'STY $9D',
      // build the menu from carried items (or one "nothing" entry): numbers at $AF, name pointers at $CE
      'LDA #0', 'STA $82', 'TAX',
      'wB1: LDY #INV', 'JSR bTst', 'BEQ wB2', 'LDY $82', 'TXA', 'STA $00AF,Y', 'INC $82', 'wB2: INX', 'CPX #16', 'BNE wB1',
      'LDA $82', 'BNE wB3', 'LDA #$FF', 'STA $AF', 'LDA #<NOTHING', 'STA $CE', 'LDA #>NOTHING', 'STA $CF', 'INC $82', 'BNE wB5',
      'wB3: LDX #0', 'wB4: TXA', 'LSR A', 'TAY', 'LDA $00AF,Y', 'ASL A', 'TAY', 'LDA ITEMS,Y', 'STA $CE,X', 'LDA ITEMS+1,Y', 'STA $CF,X',
      'INX', 'INX', 'TXA', 'LSR A', 'CMP $82', 'BNE wB4',
      'wB5: LDA $82', 'STA $BF', 'LDA #$CE', 'STA $C0', 'LDA #0', 'STA $C1', 'STA $A0', 'LDA #<PICKS', 'STA $C2', 'LDA #>PICKS', 'STA $C3', 'RTS',
      // an item was picked from the menu
      'wPick: LDX $A0', 'LDA $AF,X', 'STA SEL', 'LDA MODE', 'BEQ wBack', 'LSR A', 'BCS wGiveDo',
      // USE: the item counts as used; flag bit 2 makes it set the room's event as well
      'wUseDo: JSR rec0', 'AND #$10', 'BEQ wUN', 'LDY #2', 'LDA ($A3),Y', 'CMP SEL', 'BNE wUN', 'TAX', 'LDY #USED', 'JSR bSet',
      'JSR rec0', 'AND #$04', 'BEQ wU2', 'LDY #5', 'JSR getF', 'BEQ wU2', 'LDY #EV', 'JSR bSet', 'wU2: LDY #$0E', 'JMP say', 'wUN: JMP $F3C0',
      'wBack: JMP $F2AA',
      // GIVE: the item leaves the inventory; the room's event is set and its item revealed
      'wGiveDo: JSR rec0', 'AND #$20', 'BEQ wGN', 'LDY #3', 'LDA ($A3),Y', 'CMP SEL', 'BNE wGN', 'TAX', 'LDY #INV', 'JSR bClr',
      'LDY #5', 'JSR getF', 'BEQ wG2', 'LDY #EV', 'JSR bSet', 'wG2: LDY #1', 'JSR getF', 'BEQ wG3', 'LDY #SEEN', 'JSR bSet',
      'wG3: LDY #$10', 'JMP say', 'wGN: JMP $F37D',
      // TALK: the success reply needs an item to have been used here
      'wTalk: JSR rec0', 'AND #$08', 'BEQ wHello', 'LDY #4', 'JSR getF', 'BEQ wTK', 'LDY #USED', 'JSR bTst', 'BEQ wTK',
      'LDY #5', 'JSR getF', 'BEQ wT2', 'LDY #EV', 'JSR bSet', 'wT2: LDY #$12', 'JMP say', 'wTK: LDY #$16', 'JMP say', 'wHello: JMP $F328',
      // locked rooms: Z clear when the needed event has happened; X must come back as 8 (arrival text)
      'wDoor: LDY #6', 'LDA ($A3),Y', 'TAX', 'LDY #EV', 'JSR bTst', 'PHP', 'LDX #8', 'PLP', 'RTS',
      // start-of-game inventory
      'wStart: LDA #<STARTINV', 'STA INV', 'LDA #>STARTINV', 'STA INV+$1E', 'RTS',
      'ML: .byte 1,2,4,8,16,32,64,128,0,0,0,0,0,0,0,0', 'MH: .byte 0,0,0,0,0,0,0,0,1,2,4,8,16,32,64,128',
      'PICKS: .byte ' + Array.from({ length: 16 }, () => '<wPick,>wPick').join(','),
    ];
  }
  const WIDE_SYMS = { TK: 0xA6, INV: 0xA7, SEEN: 0xA8, USED: 0xA9, EV: 0xAC, SEL: 0xC8, MODE: 0xC9 };
  function asmWide(org, syms) { return assemble(wideSource(), org, Object.assign({}, WIDE_SYMS, syms)); }
  // the ending check, assembled: wide mode tests a 16-bit event number
  function asmGateWide(org, endEvent, endWord) {
    const L = [];
    if (endEvent != null) L.push(`LDX #${endEvent}`, 'LDA $AC', 'AND ML,X', 'BNE end', 'LDA $CA', 'AND MH,X', 'BNE end');
    L.push('JSR $F5A1', 'LDY #0', 'LDA ($A3),Y', 'LSR A', 'BCS end', 'JMP $F0AB', 'end: LDA #<WORD', 'STA $9E', 'LDA #>WORD', 'STA $9F', 'RTS');
    return L;
  }

  // opts.measure: only measure space (no engine needed, ignores validation errors)
  function buildRom(project, engine, opts = {}) {
    const measure = !!opts.measure;
    if (!measure) { const e = isEngine(engine); if (e) throw new Error(e); }
    const P = normalize(project);
    const { errs, warns } = measure ? { errs: [], warns: [] } : validate(P);
    if (errs.length) return { ok: false, errs, warns };
    const fx = fixesNeeded(P);
    ENC = fx.font === 'extended' ? XCHAR : CHAR;
    try { return build(); } finally { ENC = CHAR; }

    function build() {
      const cart = CARTS[P.cart], NB = cart.banks, LIM = cart.base;
      const lim = measure ? 0x30000 : LIM;
      const SZ = measure ? 0x20000 : 4096;
      const rom = new Uint8Array(SZ * NB).fill(0xFF);
      const banks = Array.from({ length: NB }, (_, b) => rom.subarray(b * SZ, (b + 1) * SZ));
      const order = bankOrder(P.cart);                 // order[m] = bank holding map m
      const startBank = cart.start;
      // every bank starts as a copy of the engine: code + font ($F000-$F5F1) and the vectors
      if (!measure) for (const bk of banks) { bk.set(engine.subarray(4096, 4096 + 0x5F2), 0); bk.set(engine.subarray(4096 + 0xFFA, 8192), 0xFFA); }

      // ---- common block: identical bytes at identical addresses in every bank ----
      const cb = banks[startBank];
      let cstart = DATA_START, holes = [];
      if (fx.font === 'extended') {
        for (let i = 0; i < XFONT.length; i++) cb[0xF600 + i - BASE] = XFONT[i];
        cstart = 0xF600 + XFONT.length;
        holes = [[0xF504, 0xF5A1], [0xF5F2, 0xF600]];
      } else if (/[Q-]/.test(allTexts(P).map(normText).join(''))) {
        for (let i = 0; i < EXTRA_GLYPHS.length; i++) cb[0xF5F2 + i - BASE] = EXTRA_GLYPHS[i];
        cstart = 0xF5FE;
      }
      const cw = new Writer(cb, cstart, lim);
      const caddr = {};
      const maxPortals = Math.max(0, ...P.maps.map((_, m) => P.portals.filter(p => p.map === m).length));
      try {
        // wide game logic: size it with placeholder addresses now, assemble for real once strings are placed
        const wideSyms0 = { SELGIVE: 0xF000, SELUSE: 0xF000, CARRY: 0xF000, NOTHING: 0xF000, ITEMS: 0xF000, STARTINV: 0 };
        if (fx.wide) caddr.wide = cw.put(new Array(asmWide(0xF000, wideSyms0).bytes.length).fill(0xEA));
        const gateLen = fx.wide ? assemble(asmGateWide(0xF000, P.settings.endEvent, 0xF000), 0xF000, { ML: 0xF000, MH: 0xF000, WORD: 0xF000 }).bytes.length : GATE_LEN;
        if (fx.gate) caddr.gate = cw.put(new Array(gateLen).fill(0xEA));
        if (fx.empty) caddr.empty = cw.put(new Array(EMPTY_LEN).fill(0xEA));
        if (fx.use) caddr.use = cw.put(asmUse());
        if (fx.portal) {
          caddr.portal = cw.put(new Array(portalLen()).fill(0xEA));
          caddr.portalTable = cw.put(new Array(maxPortals * 5 + 2).fill(0xFF)); // filled per bank below
          const pa = asmPortal(caddr.portal, caddr.portalTable);
          cb.set(pa.bytes, caddr.portal - BASE); caddr.portalBack = pa.labels.pBack;
        }
        cw.searchFrom = cw.pc;
        const pending = [];
        for (const k of [...MOVE_WORDS, ...ACT_WORDS, 'more', 'start']) pending.push(['w:' + k, encodePage(P.system[k], true)]);
        if (fx.gate) pending.push(['w:theEnd', encodePage(P.system.theEnd, true)]);
        if (fx.empty || fx.wide) pending.push(['w:nothing', encodePage(P.system.nothing, true)]);
        for (const k of SYS_MSGS) pending.push(['m:' + k, encodePage(P.system[k])]);
        const nItems = fx.wide ? 16 : 8;
        P.items.slice(0, nItems).forEach((t, i) => pending.push(['i:' + i, encodePage(t, true)]));
        pending.sort((a, b) => b[1].length - a[1].length);
        for (const [k, bytes] of pending) caddr[k] = cw.str(bytes);
        caddr.itemTable = cw.put(P.items.slice(0, nItems).flatMap((_, i) => [lo(caddr['i:' + i]), hi(caddr['i:' + i])]));
        if (fx.wide) {
          const startInv = P.start.inventory.reduce((acc, i) => acc | bit(i), 0);
          const wa = asmWide(caddr.wide, { SELGIVE: caddr['m:selectGive'], SELUSE: caddr['m:selectUse'], CARRY: caddr['m:carrying'], NOTHING: caddr['w:nothing'], ITEMS: caddr.itemTable, STARTINV: startInv });
          cb.set(wa.bytes, caddr.wide - BASE); caddr.wl = wa.labels;
          if (fx.gate) cb.set(assemble(asmGateWide(caddr.gate, P.settings.endEvent, caddr['w:theEnd']), caddr.gate, { ML: wa.labels.ML, MH: wa.labels.MH, WORD: caddr['w:theEnd'] }).bytes, caddr.gate - BASE);
        } else if (fx.gate) cb.set(asmGate(caddr.gate, bit(P.settings.endEvent), caddr['w:theEnd']), caddr.gate - BASE);
        if (fx.empty) cb.set(asmEmpty(caddr['w:nothing']), caddr.empty - BASE);
      } catch (x) { if (x.message === 'OUT_OF_SPACE') return { ok: false, errs: ['Out of space in the shared text block'], warns }; throw x; }
      const commonEnd = cw.pc;
      for (const bk of banks) if (bk !== cb) bk.set(cb.subarray(0xF5F2 - BASE, commonEnd - BASE), 0xF5F2 - BASE);

      // ---- code patches (per bank) ----
      for (let b = 0; b < NB; b++) {
        const bk = banks[b], m = mapOfBank(P.cart, b), map = P.maps[m];
        const put = (at, bytes) => bytes.forEach((v, i) => bk[at + i - BASE] = v);
        setSite(bk, SITE.firstMenuWord, caddr['w:look']);
        setSite(bk, SITE.introMenuWord, caddr['w:more']);
        for (const k of SYS_MSGS) setSite(bk, SITE[k], caddr['m:' + k]);
        setSite(bk, SITE.itemTable, caddr.itemTable);
        MOVE_WORDS.forEach((k, i) => put(TBL.moveMenu + 2 * i, [lo(caddr['w:' + k]), hi(caddr['w:' + k])]));
        ACT_WORDS.forEach((k, i) => put(TBL.actMenu + 2 * i, [lo(caddr['w:' + k]), hi(caddr['w:' + k])]));
        put(TBL.introMenu, [lo(caddr['w:more']), hi(caddr['w:more']), lo(caddr['w:start']), hi(caddr['w:start'])]);
        // the intro menu: MORE/START in the start bank; anywhere else both reboot into the start bank
        put(TBL.introHandlers, b === startBank ? [0xE8, 0xF1, 0x6C, 0xF0] : [0x5D, 0xF0, 0x5D, 0xF0]);
        put(HOOK.reboot.at, [0xAD, lo(cart.base + startBank), hi(cart.base + startBank)]);
        bk[IMM.widthN - BASE] = 2 * map.width; bk[IMM.widthS - BASE] = 2 * map.width;
        bk[IMM.startRoom - BASE] = P.start.room * 2;
        const startInvMask = P.start.inventory.reduce((acc, i) => acc | bit(i), 0);
        bk[IMM.introPages - BASE] = P.intro.length - 1;
        if (fx.portal) {
          put(HOOK.portal.at, [0x20, lo(caddr.portal), hi(caddr.portal)]);
          put(HOOK.blocked.at, [0x20, lo(caddr.portalBack), hi(caddr.portalBack), 0xEA]); // table is filled with the world data
        } else {
          put(HOOK.blocked.at, HOOK.blocked.orig);
          // the original two hard-wired gateways (8K only)
          const a = P.portals.find(p => p.map === 0), bb = P.portals.find(p => p.map === 1);
          put(HOOK.portal.at, HOOK.portal.orig);
          bk[IMM.portalB - BASE] = (a.idx * 2) & 0xFF;  // CMP #.. -> switch to bank 0 (Map B)
          bk[IMM.portalA - BASE] = (bb.idx * 2) & 0xFF; // CMP #.. -> switch to bank 1 (Map A)
        }
        put(HOOK.gate.at, fx.gate ? [0x20, lo(caddr.gate), hi(caddr.gate)] : HOOK.gate.orig);
        if (fx.wide) {
          const wl = caddr.wl, w2 = a => [lo(a), hi(a)];
          put(HOOK.lookHandler.at, w2(wl.wLook));
          put(HOOK.actHandlers.at, [0xAA, 0xF2, ...w2(wl.wTake), ...w2(wl.wGive), ...w2(wl.wUse), ...w2(wl.wTalk), ...w2(wl.wInv)]);
          // lock check: JSR wDoor / BNE open (to $F24E) / NOP x3
          put(HOOK.door.at, [0x20, ...w2(wl.wDoor), 0xD0, 0x12, 0xEA, 0xEA, 0xEA]);
          put(HOOK.startInv.at, [0x20, ...w2(wl.wStart), 0xEA]);
        } else {
          for (const k of ['lookHandler', 'actHandlers', 'door', 'startInv']) put(HOOK[k].at, HOOK[k].orig);
          bk[IMM.startInv - BASE] = startInvMask & 0xFF;
        }
        put(HOOK.empty.at, fx.empty ? [0x20, lo(caddr.empty), hi(caddr.empty), 0xEA] : HOOK.empty.orig);
        put(HOOK.use.at, fx.use ? [0x20, lo(caddr.use), hi(caddr.use), 0xEA, 0xEA, 0xEA] : HOOK.use.orig);
        put(HOOK.fontPage.at, [0xA9, fx.font === 'extended' ? 0xF6 : 0xF5]);
        put(HOOK.space.at, [0xA9, ENC[' ']]);
        const col = map.colors || DEFAULT_COLORS;
        for (const k of Object.keys(COLOR)) bk[COLOR[k] - BASE] = col[k] & 0xFE;
      }

      // ---- per-bank world data ----
      const usage = [];
      for (let m = 0; m < NB; m++) {
        const b = order[m], bk = banks[b], map = P.maps[m];
        const w = new Writer(bk, commonEnd, lim, holes);
        w.cache = new Map(cw.cache); // shared strings exist in every bank
        try {
          const table = w.put(new Array(map.cells.length * 2).fill(0));
          setSite(bk, SITE.roomTable, table);
          w.searchFrom = w.pc;
          const S = [];
          const want = (t) => { const bytes = encodePage(t); S.push(bytes); return bytes.join(','); };
          const recs = map.cells.map((c, i) => {
            if (portalAt(P, m, i)) return null; // never read: entering it switches maps first
            if (c.type === 'wall') return { wall: want(c.text) };
            const r = { c, k: [want(c.desc), want(c.look)] };
            r.k[2] = c.take.on ? want(c.take.text) : null;
            r.k[3] = c.use.on ? want(c.use.text) : null;
            r.k[4] = c.give.on ? want(c.give.text) : null;
            r.k[5] = c.talk.on && c.talk.needUsed != null ? want(c.talk.ok) : null;
            r.k[6] = c.door.on ? want(c.door.text) : null;
            r.k[7] = c.talk.on ? want(c.talk.no) : null;
            return r;
          });
          // a portal into a locked room shows that room's message from here, so keep a copy in this bank
          const myPortals = P.portals.filter(p => p.map === m);
          const lockKeys = myPortals.map(p => { const d = P.maps[p.toMap].cells[p.toIdx]; return d && d.type === 'room' && d.door.on ? want(d.door.text) : null; });
          let introKeys = [];
          if (m === 0) introKeys = P.intro.map(want);
          else want(P.system.bootB);
          S.sort((x, y) => y.length - x.length);
          const addr = {};
          for (const bytes of S) addr[bytes.join(',')] = w.str(bytes);
          const recCache = new Map();
          const recAddr = recs.map(r => {
            if (!r) return null;
            let bytes;
            if (r.wall) { const a = addr[r.wall]; bytes = [0, lo(a), hi(a)]; }
            else {
              const c = r.c;
              let f = 0;
              if (c.ending) f |= 0x01;
              if (c.door.on) f |= 0x02;
              if (c.use.on && c.use.setsEvent && (fx.use || fx.wide)) f |= 0x04;
              if (c.talk.on) f |= 0x08;
              if (c.use.on) f |= 0x10;
              if (c.give.on) f |= 0x20;
              if (c.take.on) f |= 0x40;
              const reveal = c.lookReveals && c.item != null;
              if (!reveal) f |= 0x80;
              const num = v => v == null ? 0xFF : v;
              bytes = fx.wide
                ? [f, num(c.item), c.use.on ? num(c.use.item) : 0xFF, c.give.on ? num(c.give.item) : 0xFF,
                  c.talk.on ? num(c.talk.needUsed) : 0xFF, num(c.sets), c.door.on ? num(c.door.needEvent) : 0xFF, 0]
                : [f, reveal ? bit(c.item) : 0, bit(c.item), c.use.on ? bit(c.use.item) : 0, c.give.on ? bit(c.give.item) : 0,
                  c.talk.on ? bit(c.talk.needUsed) : 0, bit(c.sets), c.door.on ? bit(c.door.needEvent) : 0];
              let last = 1; r.k.forEach((k, i) => { if (k) last = i; });
              for (let i = 0; i <= last; i++) { const a = r.k[i] ? addr[r.k[i]] : 0xFFFF; bytes.push(lo(a), hi(a)); }
            }
            const key = bytes.join(',');
            if (!recCache.has(key)) recCache.set(key, w.put(bytes));
            return recCache.get(key);
          });
          if (fx.portal) {
            const ents = myPortals.flatMap((p, k) => { const a = lockKeys[k] ? addr[lockKeys[k]] : 0; return [(p.idx * 2) & 0xFF, lo(cart.base + order[p.toMap]), (p.toIdx * 2) & 0xFF, lo(a), hi(a)]; });
            bk.set([lo(cart.base + b), ...ents, 0xFF], caddr.portalTable - BASE);
          }
          let any = recAddr.find(a => a != null);
          if (any == null) any = w.put([0, 0xFF, 0xFF]); // a map with no readable cells
          recAddr.forEach((a, i) => { const v = a == null ? any : a; bk[table + 2 * i - BASE] = lo(v); bk[table + 2 * i + 1 - BASE] = hi(v); });
          if (m === 0) {
            const ptrs = introKeys.map(k => addr[k]);
            setSite(bk, SITE.bootText, ptrs[0]);
            const n = ptrs.length - 1;
            for (let k = 0; k < 5; k++) { const v = k < n ? ptrs[n - k] : ptrs[ptrs.length - 1]; bk[TBL.introPages + 2 * k - BASE] = lo(v); bk[TBL.introPages + 2 * k + 1 - BASE] = hi(v); }
            setSite(bk, SITE.startText, addr[encodePage(P.maps[0].cells[P.start.room].desc).join(',')]);
          } else {
            const a = addr[encodePage(P.system.bootB).join(',')];
            setSite(bk, SITE.bootText, a); setSite(bk, SITE.startText, a);
            for (let k = 0; k < 5; k++) { bk[TBL.introPages + 2 * k - BASE] = lo(a); bk[TBL.introPages + 2 * k + 1 - BASE] = hi(a); }
          }
        } catch (x) {
          if (x.message === 'OUT_OF_SPACE') return { ok: false, errs: [`${map.name} does not fit in its 4K bank — shorten some text or reuse identical messages`], warns };
          throw x;
        }
        const holeFree = w.holes.reduce((t, h) => t + (h.end - h.pc), 0), holeSize = w.holes.reduce((t, h) => t + (h.end - h.start), 0);
        const total = LIM - DATA_START + holeSize, free = LIM - w.pc + holeFree;
        usage[m] = { used: total - free, total, free };
      }
      return { ok: true, rom: measure ? null : rom, warns, usage: { maps: usage, mapA: usage[0], mapB: usage[1] }, fixes: fx };
    }
  }

  // ---------- Space estimate without building (fast) ----------


  // ---------- New blank project ----------
  function room(name, desc, look) {
    return { type: 'room', name, desc, look, lookReveals: false, item: null, take: { on: false, text: '' }, use: { on: false, item: null, text: '', setsEvent: false },
      give: { on: false, item: null, text: '' }, talk: { on: false, needUsed: null, ok: '', no: '' }, sets: null, door: { on: false, needEvent: null, text: '' }, ending: false };
  }
  function wall(text) { return { type: 'wall', text }; }
  function blankMap(i, W, rows) {
    return { name: 'Map ' + LETTERS[i], width: W, rows, cells: Array.from({ length: rows * W }, () => wall("YOU CAN'T GO\nTHAT WAY.")), colors: Object.assign({}, DEFAULT_COLORS) };
  }
  function setCart(P, cart) {
    const n = CARTS[cart].banks;
    while (P.maps.length < n) P.maps.push(blankMap(P.maps.length, 6, 5));
    if (P.maps.length > n) { P.maps.length = n; P.portals = P.portals.filter(p => p.map < n && p.toMap < n); }
    P.cart = cart;
    return P;
  }
  function newProject(opts = {}) {
    const W = opts.width || 6, rA = opts.rowsA || 5, rB = opts.rowsB || 5;
    const mA = blankMap(0, W, rA), mB = blankMap(1, W, rB);
    const A = mA.cells, B = mB.cells;
    const pA = (opts.portalRow != null ? opts.portalRow : 2) * W + Math.floor(W / 2);   // cell in Map A that leads into Map B
    const pB = pA - 1;                                                                   // cell in Map B that leads into Map A
    A[W + 1] = room('Start', 'YOU ARE IN A\nSMALL ROOM.', 'IT IS VERY\nQUIET HERE.');
    A[pB] = room('Portal path (Map A side)', 'A NARROW\nPASSAGE\nLEADS EAST.', 'YOU FEEL A\nCOLD DRAFT.');
    B[pA] = room('Portal path (Map B side)', 'YOU HAVE\nCROSSED INTO\nA NEW LAND.', 'THE PASSAGE\nWEST LEADS\nBACK HOME.');
    return {
      kit: 'tak', version: 1, title: opts.title || 'My adventure', engine: 'tak',
      cart: '8K',
      settings: { endEvent: null },
      portals: [{ map: 0, idx: pA, toMap: 1, toIdx: pA }, { map: 1, idx: pB, toMap: 0, toIdx: pB }],
      start: { room: W + 1, inventory: [0] },
      items: ['A LAMP', 'A KEY', 'A COIN', 'A ROPE', 'A SCROLL', 'A SWORD', 'AN APPLE', 'A GEM'],
      events: ['Event 1', 'Event 2', 'Event 3', 'Event 4', 'Event 5', 'Event 6', 'Event 7', 'Event 8'],
      system: { look: 'LOOK', north: 'NORTH', east: 'EAST', south: 'SOUTH', west: 'WEST', go: 'GO', take: 'TAKE', give: 'GIVE', use: 'USE', talk: 'TALK', inventory: 'INVENTORY',
        more: 'MORE...', start: 'START', nothingSpecial: 'YOU SEE\nNOTHING\nSPECIAL', nothingToTake: 'YOU SEE\nNOTHING\nWORTH\nTAKING', talkDefault: 'NO ONE\nANSWERS.',
        selectGive: 'SELECT ITEM\nTO GIVE:', cantGive: "CAN'T GIVE\nTHAT", selectUse: 'SELECT ITEM\nTO USE:', cantUse: "CAN'T USE\nTHAT", carrying: 'YOU ARE\nCARRYING:', bootB: '', theEnd: 'THE END', nothing: 'NOTHING' },
      intro: ['\n\n  MY GAME\n\n\n    BY\n   ME', 'YOUR QUEST\nBEGINS NOW.'],
      maps: [mA, mB],
    };
  }

  // ---------- 6502 + F8 + RIOT emulator (enough for this engine) ----------
  class Emu {
    constructor(rom) {
      this.rom = rom; this.ram = new Uint8Array(128); this.nbanks = rom.length >> 12; this.hot = { 2: 0x1FF8, 4: 0x1FF6, 8: 0x1FF4, 16: 0x1FE0 }[this.nbanks]; this.bank = this.nbanks === 2 ? 1 : 0;
      this.a = 0; this.x = 0; this.y = 0; this.sp = 0xFD; this.p = 0x24; this.cyc = 0;
      this.swcha = 0xFF; this.inpt4 = 0x80; this.swchb = 0x0B;
      this.tStart = 0; this.tVal = 0; this.tShift = 1024; this.vsync = 0; this.frames = 0;
      this.pc = this.r16(0xFFFC);
    }
    access(a) { a &= 0x1FFF; const k = a - this.hot; if (k >= 0 && k < this.nbanks) this.bank = k; return a; }
    read(addr) {
      const a = this.access(addr);
      if (a & 0x1000) return this.rom[this.bank * 4096 + (a & 0xFFF)];
      if ((a & 0x80) && !(a & 0x200)) return this.ram[a & 0x7F];
      if (a & 0x80) { // RIOT
        const r = a & 0x2FF;
        if ((r & 0x7) === 0 && !(r & 0x4)) return this.swcha;          // 280
        if ((r & 0x7) === 2) return this.swchb;                         // 282
        if ((r & 0x5) === 4) return this.intim();                       // 284
        return 0;
      }
      const t = a & 0x0F; // TIA read
      if (t === 0x0C) return this.inpt4;
      if (t === 0x0D) return 0x80;
      return 0;
    }
    intim() {
      const el = this.cyc - this.tStart, ticks = Math.floor(el / this.tShift);
      if (ticks <= this.tVal) return this.tVal - ticks;
      return (0xFF - (el - (this.tVal + 1) * this.tShift)) & 0xFF;
    }
    write(addr, v) {
      const a = this.access(addr);
      if (a & 0x1000) return;
      if ((a & 0x80) && !(a & 0x200)) { this.ram[a & 0x7F] = v; return; }
      if (a & 0x80) { // RIOT
        if (a & 0x10) { const s = [1, 8, 64, 1024][a & 3]; this.tShift = s; this.tVal = v; this.tStart = this.cyc; }
        return;
      }
      const t = a & 0x3F;
      if (t === 0x02) { this.cyc += (76 - (this.cyc % 76)) % 76; } // WSYNC
      else if (t === 0x00) { const on = v & 2; if (on && !this.vsync) this.frames++; this.vsync = on; }
    }
    r16(a) { return this.read(a) | (this.read(a + 1) << 8); }
    push(v) { this.write(0x100 | this.sp, v); this.sp = (this.sp - 1) & 0xFF; }
    pull() { this.sp = (this.sp + 1) & 0xFF; return this.read(0x100 | this.sp); }
    nz(v) { this.p = (this.p & 0x7D) | (v & 0x80) | (v ? 0 : 2); return v; }
    step() {
      const op = this.read(this.pc); this.pc = (this.pc + 1) & 0xFFFF;
      const I = OPS[op];
      if (!I) throw new Error('Illegal opcode $' + op.toString(16) + ' at $' + ((this.pc - 1) & 0xFFFF).toString(16));
      I(this); this.cyc += CYC[op];
    }
    runFrame(maxCyc = 200000) {
      const f = this.frames, lim = this.cyc + maxCyc;
      while (this.frames === f && this.cyc < lim) this.step();
    }
    // engine state helpers
    textPtr() { return this.ram[0x1C] | (this.ram[0x1D] << 8); }
    menuPtr() { return this.ram[0x1E] | (this.ram[0x1F] << 8); }
    bankBytes() { return this.rom.subarray(this.bank * 4096, this.bank * 4096 + 4096); }
    fontPage() { return this.rom[this.bank * 4096 + (this.layout === 'tak' ? 0xFD7 : 0x032)]; }
    decoder() { return this.layout === 'tak' || this.fontPage() === 0xF6 ? XDECODE : DECODE; }
    takBank(a) { const n = (a >> 12) & 0xF; return n === 0xF ? this.bankBytes() : this.rom.subarray(n * 4096, n * 4096 + 4096); }
    takText(a, menuWord) { return takLines(this.takBank(a), a | 0xF000, menuWord).map(l => l.map(v => XDECODE[v] !== undefined ? XDECODE[v] : ' ').join('')).join('\n').replace(/\n$/, ''); }
    screenText() { return this.layout === 'tak' ? this.takText(this.textPtr(), false) : readText(this.bankBytes(), this.textPtr(), false, this.decoder()); }
    menuText() { return this.layout === 'tak' ? this.takText(this.menuPtr(), true) : readText(this.bankBytes(), this.menuPtr(), true, this.decoder()); }
    // raw text bytes as the kernel would draw them: up to 10 lines + the menu line
    screenBytes() {
      if (this.layout === 'tak') {
        const tp = this.textPtr(), t = takLines(this.takBank(tp), tp | 0xF000, false).slice(0, 10).map(l => l.slice(0, 12));
        while (t.length < 10) t.push([]);
        return { lines: t, menu: (takLines(this.bankBytes(), this.menuPtr(), true)[0] || []).slice(0, 12) };
      }
      const bk = this.bankBytes(), lines = [];
      let i = this.textPtr() - BASE, done = false;
      for (let l = 0; l < 10; l++) {
        const line = [];
        while (!done && i >= 0 && i < 4096) { const v = bk[i++]; if (v === 0xFF) break; if (v === 0xFE) { done = true; break; } if (line.length < 12) line.push(v); }
        lines.push(line);
      }
      const menu = []; let j = this.menuPtr() - BASE;
      while (j >= 0 && j < 4096 && menu.length < 12) { const v = bk[j++]; if (v === 0xFF) break; menu.push(v); }
      return { lines, menu };
    }
    glyph(code, row) { return this.rom[this.bank * 4096 + (this.fontPage() - 0xF0) * 256 + code + row]; }
    colors() { const b = this.bank * 4096; if (this.layout === 'tak') return { bg: this.rom[b + 0xFD0], text: this.rom[b + 0xFD1], menuBg: this.rom[b + 0xFD2], menuText: this.rom[b + 0xFD3] };
      return { bg: this.rom[b + 0x15F], text: this.rom[b + 0x159], menuBg: this.rom[b + 0x1B7], menuText: this.rom[b + 0x1BB] }; }
    // set .wide = true for cartridges built with 16 items / 16 events
    state() { const r = this.ram, h = a => this.wide ? r[a] << 8 : 0; return { room: r[0x22] >> 1, bank: this.bank, inv: r[0x27] | h(0x45), taken: r[0x26] | h(0x44), seen: r[0x28] | h(0x46), used: r[0x29] | h(0x47), events: r[0x2C] | h(0x4A) }; }
  }
  // addressing helpers
  const imm = c => { const v = c.pc; c.pc = (c.pc + 1) & 0xFFFF; return v; };
  const zp = c => c.read(imm(c));
  const zpx = c => (c.read(imm(c)) + c.x) & 0xFF;
  const zpy = c => (c.read(imm(c)) + c.y) & 0xFF;
  const abs = c => { const v = c.r16(c.pc); c.pc = (c.pc + 2) & 0xFFFF; return v; };
  const abx = c => { const b = abs(c), v = (b + c.x) & 0xFFFF; if ((b & 0xFF00) !== (v & 0xFF00)) c.cyc++; return v; };
  const aby = c => { const b = abs(c), v = (b + c.y) & 0xFFFF; if ((b & 0xFF00) !== (v & 0xFF00)) c.cyc++; return v; };
  const izx = c => { const z = (c.read(imm(c)) + c.x) & 0xFF; return c.read(z) | (c.read((z + 1) & 0xFF) << 8); };
  const izy = c => { const z = c.read(imm(c)); const b = c.read(z) | (c.read((z + 1) & 0xFF) << 8); const v = (b + c.y) & 0xFFFF; if ((b & 0xFF00) !== (v & 0xFF00)) c.cyc++; return v; };
  const OPS = new Array(256), CYC = new Array(256).fill(2);
  const AM = { imm: c => imm(c), zp: c => c.read(imm(c)), zpx, zpy, abs, abx, aby, izx, izy };
  function def(list, fn) { for (const [op, m, cy] of list) { const am = AM[m]; OPS[op] = c => fn(c, am ? am(c) : null); CYC[op] = cy; } }
  const adc = (c, v) => { const C = c.p & 1, r = c.a + v + C; c.p = (c.p & ~0x41) | (r > 0xFF ? 1 : 0) | ((~(c.a ^ v) & (c.a ^ r) & 0x80) ? 0x40 : 0); c.a = c.nz(r & 0xFF); };
  const cmp = (c, r, v) => { const t = (r - v) & 0xFF; c.p = (c.p & ~1) | (r >= v ? 1 : 0); c.nz(t); };
  def([[0x69, 'imm', 2], [0x65, 'zp', 3], [0x75, 'zpx', 4], [0x6D, 'abs', 4], [0x7D, 'abx', 4], [0x79, 'aby', 4], [0x61, 'izx', 6], [0x71, 'izy', 5]], (c, a) => adc(c, c.read(a)));
  def([[0xE9, 'imm', 2], [0xE5, 'zp', 3], [0xF5, 'zpx', 4], [0xED, 'abs', 4], [0xFD, 'abx', 4], [0xF9, 'aby', 4], [0xE1, 'izx', 6], [0xF1, 'izy', 5]], (c, a) => adc(c, c.read(a) ^ 0xFF));
  def([[0x29, 'imm', 2], [0x25, 'zp', 3], [0x35, 'zpx', 4], [0x2D, 'abs', 4], [0x3D, 'abx', 4], [0x39, 'aby', 4], [0x21, 'izx', 6], [0x31, 'izy', 5]], (c, a) => { c.a = c.nz(c.a & c.read(a)); });
  def([[0x09, 'imm', 2], [0x05, 'zp', 3], [0x15, 'zpx', 4], [0x0D, 'abs', 4], [0x1D, 'abx', 4], [0x19, 'aby', 4], [0x01, 'izx', 6], [0x11, 'izy', 5]], (c, a) => { c.a = c.nz(c.a | c.read(a)); });
  def([[0x49, 'imm', 2], [0x45, 'zp', 3], [0x55, 'zpx', 4], [0x4D, 'abs', 4], [0x5D, 'abx', 4], [0x59, 'aby', 4], [0x41, 'izx', 6], [0x51, 'izy', 5]], (c, a) => { c.a = c.nz(c.a ^ c.read(a)); });
  def([[0xC9, 'imm', 2], [0xC5, 'zp', 3], [0xD5, 'zpx', 4], [0xCD, 'abs', 4], [0xDD, 'abx', 4], [0xD9, 'aby', 4], [0xC1, 'izx', 6], [0xD1, 'izy', 5]], (c, a) => cmp(c, c.a, c.read(a)));
  def([[0xE0, 'imm', 2], [0xE4, 'zp', 3], [0xEC, 'abs', 4]], (c, a) => cmp(c, c.x, c.read(a)));
  def([[0xC0, 'imm', 2], [0xC4, 'zp', 3], [0xCC, 'abs', 4]], (c, a) => cmp(c, c.y, c.read(a)));
  def([[0xA9, 'imm', 2], [0xA5, 'zp', 3], [0xB5, 'zpx', 4], [0xAD, 'abs', 4], [0xBD, 'abx', 4], [0xB9, 'aby', 4], [0xA1, 'izx', 6], [0xB1, 'izy', 5]], (c, a) => { c.a = c.nz(c.read(a)); });
  def([[0xA2, 'imm', 2], [0xA6, 'zp', 3], [0xB6, 'zpy', 4], [0xAE, 'abs', 4], [0xBE, 'aby', 4]], (c, a) => { c.x = c.nz(c.read(a)); });
  def([[0xA0, 'imm', 2], [0xA4, 'zp', 3], [0xB4, 'zpx', 4], [0xAC, 'abs', 4], [0xBC, 'abx', 4]], (c, a) => { c.y = c.nz(c.read(a)); });
  def([[0x85, 'zp', 3], [0x95, 'zpx', 4], [0x8D, 'abs', 4], [0x9D, 'abx', 5], [0x99, 'aby', 5], [0x81, 'izx', 6], [0x91, 'izy', 6]], (c, a) => c.write(a, c.a));
  def([[0x86, 'zp', 3], [0x96, 'zpy', 4], [0x8E, 'abs', 4]], (c, a) => c.write(a, c.x));
  def([[0x84, 'zp', 3], [0x94, 'zpx', 4], [0x8C, 'abs', 4]], (c, a) => c.write(a, c.y));
  def([[0x24, 'zp', 3], [0x2C, 'abs', 4]], (c, a) => { const v = c.read(a); c.p = (c.p & 0x3D) | (v & 0xC0) | ((c.a & v) ? 0 : 2); });
  const rmw = (list, f) => def(list, (c, a) => { if (a === null) { c.a = f(c, c.a); } else { c.write(a, f(c, c.read(a))); } });
  rmw([[0x0A, null, 2], [0x06, 'zp', 5], [0x16, 'zpx', 6], [0x0E, 'abs', 6], [0x1E, 'abx', 7]], (c, v) => { c.p = (c.p & ~1) | (v >> 7); return c.nz((v << 1) & 0xFF); });
  rmw([[0x4A, null, 2], [0x46, 'zp', 5], [0x56, 'zpx', 6], [0x4E, 'abs', 6], [0x5E, 'abx', 7]], (c, v) => { c.p = (c.p & ~1) | (v & 1); return c.nz(v >> 1); });
  rmw([[0x2A, null, 2], [0x26, 'zp', 5], [0x36, 'zpx', 6], [0x2E, 'abs', 6], [0x3E, 'abx', 7]], (c, v) => { const C = c.p & 1; c.p = (c.p & ~1) | (v >> 7); return c.nz(((v << 1) | C) & 0xFF); });
  rmw([[0x6A, null, 2], [0x66, 'zp', 5], [0x76, 'zpx', 6], [0x6E, 'abs', 6], [0x7E, 'abx', 7]], (c, v) => { const C = c.p & 1; c.p = (c.p & ~1) | (v & 1); return c.nz((v >> 1) | (C << 7)); });
  rmw([[0xE6, 'zp', 5], [0xF6, 'zpx', 6], [0xEE, 'abs', 6], [0xFE, 'abx', 7]], (c, v) => c.nz((v + 1) & 0xFF));
  rmw([[0xC6, 'zp', 5], [0xD6, 'zpx', 6], [0xCE, 'abs', 6], [0xDE, 'abx', 7]], (c, v) => c.nz((v - 1) & 0xFF));
  const br = (op, test) => { OPS[op] = c => { const o = c.read(imm(c)); if (test(c)) { const t = (c.pc + (o < 128 ? o : o - 256)) & 0xFFFF; c.cyc += ((t & 0xFF00) !== (c.pc & 0xFF00)) ? 2 : 1; c.pc = t; } }; CYC[op] = 2; };
  br(0x10, c => !(c.p & 0x80)); br(0x30, c => c.p & 0x80); br(0x50, c => !(c.p & 0x40)); br(0x70, c => c.p & 0x40);
  br(0x90, c => !(c.p & 1)); br(0xB0, c => c.p & 1); br(0xD0, c => !(c.p & 2)); br(0xF0, c => c.p & 2);
  const imp = (op, cy, f) => { OPS[op] = f; CYC[op] = cy; };
  imp(0xEA, 2, () => { }); imp(0x18, 2, c => c.p &= ~1); imp(0x38, 2, c => c.p |= 1); imp(0x58, 2, c => c.p &= ~4); imp(0x78, 2, c => c.p |= 4);
  imp(0xB8, 2, c => c.p &= ~0x40); imp(0xD8, 2, c => c.p &= ~8); imp(0xF8, 2, c => c.p |= 8);
  imp(0xAA, 2, c => c.x = c.nz(c.a)); imp(0x8A, 2, c => c.a = c.nz(c.x)); imp(0xA8, 2, c => c.y = c.nz(c.a)); imp(0x98, 2, c => c.a = c.nz(c.y));
  imp(0xBA, 2, c => c.x = c.nz(c.sp)); imp(0x9A, 2, c => c.sp = c.x);
  imp(0xE8, 2, c => c.x = c.nz((c.x + 1) & 0xFF)); imp(0xCA, 2, c => c.x = c.nz((c.x - 1) & 0xFF));
  imp(0xC8, 2, c => c.y = c.nz((c.y + 1) & 0xFF)); imp(0x88, 2, c => c.y = c.nz((c.y - 1) & 0xFF));
  imp(0x48, 3, c => c.push(c.a)); imp(0x68, 4, c => c.a = c.nz(c.pull())); imp(0x08, 3, c => c.push(c.p | 0x30)); imp(0x28, 4, c => c.p = c.pull() | 0x20);
  imp(0x4C, 3, c => { c.pc = abs(c); });
  imp(0x6C, 5, c => { const a = abs(c); c.pc = c.read(a) | (c.read((a & 0xFF00) | ((a + 1) & 0xFF)) << 8); });
  imp(0x20, 6, c => { const t = abs(c), r = (c.pc - 1) & 0xFFFF; c.push(r >> 8); c.push(r & 0xFF); c.pc = t; });
  imp(0x60, 6, c => { const l = c.pull(), h = c.pull(); c.pc = (((h << 8) | l) + 1) & 0xFFFF; });
  imp(0x40, 6, c => { c.p = c.pull() | 0x20; const l = c.pull(), h = c.pull(); c.pc = (h << 8) | l; });
  imp(0x00, 7, c => { throw new Error('BRK at $' + ((c.pc - 1) & 0xFFFF).toString(16)); });

  // High-level input driver. The engine samples the stick once every 8 frames and acts on
  // the fire button's press edge, so: 'left'/'right' step the action menu by one;
  // 'N','E','S','W' hold that direction and press fire; 'fire' presses fire alone.
  const JOY = { N: 0xEF, S: 0xDF, W: 0xBF, E: 0x7F, left: 0xBF, right: 0x7F };
  // Input as frame segments [stick, fireDown, frames]; act() and the editor's replay both use them.
  function actSegs(what) {
    if (what === 'left' || what === 'right') return [[JOY[what], 0, 8], [0xFF, 0, 1]];
    const segs = [];
    if (JOY[what]) segs.push([JOY[what], 0, 9]);
    segs.push([JOY[what] || 0xFF, 1, 3], [0xFF, 0, 9]);
    return segs;
  }
  function runSegs(emu, segs) {
    for (const [stick, fire, n] of segs) { emu.swcha = stick; emu.inpt4 = fire ? 0x00 : 0x80; for (let i = 0; i < n; i++) emu.runFrame(); }
    emu.swcha = 0xFF; emu.inpt4 = 0x80;
  }
  function act(emu, what) {
    if (what === 'reset') { const idle = n => { for (let i = 0; i < n; i++) emu.runFrame(); }; emu.swchb = 0x0A; idle(4); emu.swchb = 0x0B; idle(12); return; }
    runSegs(emu, actSegs(what));
  }

  // ---------- A small two-pass 6502 assembler (for the kit's own routines) ----------
  // Syntax: "label:", "LDA #$1E", "STA $A7", "LDA ($A3),Y", "AND ML,X", "STA $00AF,Y" (4 hex
  // digits force absolute), "JMP ($1234)", "BNE label". Operands may use symbols, + - * and <x / >x.
  const OPC = (() => {
    const t = {};
    const src = '00 BRK imp|01 ORA izx|05 ORA zp|06 ASL zp|08 PHP imp|09 ORA imm|0A ASL acc|0D ORA abs|0E ASL abs|10 BPL rel|11 ORA izy|15 ORA zpx|16 ASL zpx|18 CLC imp|19 ORA aby|1D ORA abx|1E ASL abx|20 JSR abs|21 AND izx|24 BIT zp|25 AND zp|26 ROL zp|28 PLP imp|29 AND imm|2A ROL acc|2C BIT abs|2D AND abs|2E ROL abs|30 BMI rel|31 AND izy|35 AND zpx|36 ROL zpx|38 SEC imp|39 AND aby|3D AND abx|3E ROL abx|40 RTI imp|41 EOR izx|45 EOR zp|46 LSR zp|48 PHA imp|49 EOR imm|4A LSR acc|4C JMP abs|4D EOR abs|4E LSR abs|50 BVC rel|51 EOR izy|55 EOR zpx|56 LSR zpx|58 CLI imp|59 EOR aby|5D EOR abx|5E LSR abx|60 RTS imp|61 ADC izx|65 ADC zp|66 ROR zp|68 PLA imp|69 ADC imm|6A ROR acc|6C JMP ind|6D ADC abs|6E ROR abs|70 BVS rel|71 ADC izy|75 ADC zpx|76 ROR zpx|78 SEI imp|79 ADC aby|7D ADC abx|7E ROR abx|81 STA izx|84 STY zp|85 STA zp|86 STX zp|88 DEY imp|8A TXA imp|8C STY abs|8D STA abs|8E STX abs|90 BCC rel|91 STA izy|94 STY zpx|95 STA zpx|96 STX zpy|98 TYA imp|99 STA aby|9A TXS imp|9D STA abx|A0 LDY imm|A1 LDA izx|A2 LDX imm|A4 LDY zp|A5 LDA zp|A6 LDX zp|A8 TAY imp|A9 LDA imm|AA TAX imp|AC LDY abs|AD LDA abs|AE LDX abs|B0 BCS rel|B1 LDA izy|B4 LDY zpx|B5 LDA zpx|B6 LDX zpy|B8 CLV imp|B9 LDA aby|BA TSX imp|BC LDY abx|BD LDA abx|BE LDX aby|C0 CPY imm|C1 CMP izx|C4 CPY zp|C5 CMP zp|C6 DEC zp|C8 INY imp|C9 CMP imm|CA DEX imp|CC CPY abs|CD CMP abs|CE DEC abs|D0 BNE rel|D1 CMP izy|D5 CMP zpx|D6 DEC zpx|D8 CLD imp|D9 CMP aby|DD CMP abx|DE DEC abx|E0 CPX imm|E1 SBC izx|E4 CPX zp|E5 SBC zp|E6 INC zp|E8 INX imp|E9 SBC imm|EA NOP imp|EC CPX abs|ED SBC abs|EE INC abs|F0 BEQ rel|F1 SBC izy|F5 SBC zpx|F6 INC zpx|F8 SED imp|F9 SBC aby|FD SBC abx|FE INC abx';
    for (const e of src.split('|')) { const [o, m, md] = e.split(' '); t[m + ' ' + md] = parseInt(o, 16); }
    return t;
  })();
  const ASM_LEN = { imp: 1, acc: 1, imm: 2, zp: 2, zpx: 2, zpy: 2, izx: 2, izy: 2, rel: 2, abs: 3, abx: 3, aby: 3, ind: 3 };
  function assemble(lines, org, syms0 = {}) {
    const run = (syms, final) => {
      const out = [], labels = {}; let pc = org;
      const val = (expr) => {
        const e = expr.trim();
        if (e.startsWith('<')) return val(e.slice(1)) & 0xFF;
        if (e.startsWith('>')) return (val(e.slice(1)) >> 8) & 0xFF;
        let unknown = false;
        const js = e.replace(/\$([0-9A-Fa-f]+)/g, (_, h) => String(parseInt(h, 16)))
          .replace(/[A-Za-z_][A-Za-z0-9_]*/g, n => { if (n in syms) return String(syms[n]); unknown = true; return '0'; });
        if (unknown && final) throw new Error('Unknown symbol in "' + e + '"');
        if (!/^[0-9+\-*() ]+$/.test(js)) throw new Error('Bad expression "' + e + '"');
        return unknown ? null : Function('return (' + js + ')')();
      };
      for (let raw of lines) {
        const line = raw.replace(/;.*$/, '').trim(); if (!line) continue;
        const lm = /^([A-Za-z_][A-Za-z0-9_]*):\s*(.*)$/.exec(line);
        let body = line;
        if (lm) { labels[lm[1]] = pc; syms[lm[1]] = pc; body = lm[2].trim(); if (!body) continue; }
        if (/^\.byte /i.test(body)) { for (const b of body.slice(6).split(',')) { out.push((val(b) ?? 0) & 0xFF); pc++; } continue; }
        const [mn, ...rest] = body.split(/\s+/); const op = rest.join(' ').trim(); const M = mn.toUpperCase();
        let mode, v = null;
        if (!op || op === 'A') mode = OPC[M + ' imp'] !== undefined ? 'imp' : 'acc';
        else if (op[0] === '#') { mode = 'imm'; v = val(op.slice(1)); }
        else if (/^\(.*\),Y$/i.test(op)) { mode = 'izy'; v = val(op.slice(1, -3)); }
        else if (/^\(.*,X\)$/i.test(op)) { mode = 'izx'; v = val(op.slice(1, -3)); }
        else if (/^\(.*\)$/.test(op)) { mode = 'ind'; v = val(op.slice(1, -1)); }
        else if (OPC[M + ' rel'] !== undefined) { mode = 'rel'; v = val(op); }
        else {
          const idx = /,([XY])$/i.exec(op); const base = idx ? op.slice(0, -2) : op;
          v = val(base);
          const forceAbs = /^\$[0-9A-Fa-f]{4}$/.test(base.trim());
          const zp = !forceAbs && v !== null && v < 0x100;
          const r = idx ? idx[1].toUpperCase() : '';
          const zm = r ? 'zp' + r.toLowerCase() : 'zp', am = r ? 'ab' + r.toLowerCase() : 'abs';
          mode = zp && OPC[M + ' ' + zm] !== undefined ? zm : am;
        }
        const code = OPC[M + ' ' + mode];
        if (code === undefined) throw new Error(`Bad instruction "${body}" (${mode})`);
        out.push(code);
        const n = ASM_LEN[mode];
        if (mode === 'rel') {
          let off = 0;
          if (v !== null) { off = v - (pc + 2); if (final && (off < -128 || off > 127)) throw new Error('Branch out of range: ' + body); }
          out.push(off & 0xFF);
        } else if (n === 2) out.push((v ?? 0) & 0xFF);
        else if (n === 3) out.push((v ?? 0) & 0xFF, ((v ?? 0) >> 8) & 0xFF);
        pc += n;
      }
      return { bytes: out, labels };
    };
    const syms = Object.assign({}, syms0);
    run(syms, false);              // pass 1: collect labels
    return run(syms, true);        // pass 2: resolve everything
  }

  // =====================================================================================
  // The Workshop engine: an original 2600 text-adventure engine (no Dark Mage code).
  // Same player-facing behaviour and data model as the editor, 16 items / 16 events,
  // portals with locks, endings, per-map colours, F8/F6/F4 bank switching.
  //
  // Display: 10 lines x 12 characters plus a menu line. Both players use three medium
  // copies (NUSIZ 6: copies 32 px apart), player 1 sits 16 px right of player 0, giving six
  // 8-px character slots 16 px apart. Even frames draw characters 0,2,..10, odd frames are
  // shifted 8 px right and draw 1,3,..11. Player 0 is vertically delayed, so one write to
  // GRP1 both changes player 1 and latches player 0's next image: three writes per scanline
  // change the four images that follow the first two.
  //
  // Zero page: $80 frame, $81/$82 temp, $83-$8E six glyph pointers, $8F v6 temp, $90 lines
  // left, $91/$92 text read pointer, $93 frame parity, $9C/$9D message, $9E/$9F menu word,
  // $A0 menu index, $A1 portal message hi, $A2 room*2, $A3/$A4 room record, $A5 previous room,
  // $A6/$A7/$A8/$A9/$AC taken/inventory/revealed/used/events (high bytes $1E above),
  // $AA portal return hotspot, $AB portal message lo, $AD menu mode, $AE fire latch,
  // $AF-$BE item menu numbers, $BF menu count, $C0/$C1 menu words, $C2/$C3 menu handlers,
  // $C8 picked item, $C9 item-menu purpose, $CB intro page, $CC playing, $CE-$ED item names.
  // Per-bank header at $FFD0 (clear of every bank-switching scheme's hotspots): bg, text, menu bg, menu text, 2 x width, room table lo/hi, font page.
  // =====================================================================================
  const TAK_ZP = {
    FRAMEC: 0x80, T1: 0x81, T2: 0x82, P1: 0x83, P2: 0x85, P3: 0x87, P4: 0x89, P5: 0x8B, P6: 0x8D, TMPV: 0x8F,
    LINE: 0x90, TP: 0x91, PAR: 0x93, TXT: 0x9C, MENUW: 0x9E, SELI: 0xA0, PMSGHI: 0xA1, ROOM: 0xA2, REC: 0xA3,
    PREV: 0xA5, TK: 0xA6, INV: 0xA7, SEEN: 0xA8, USED: 0xA9, PHOT: 0xAA, PMSGLO: 0xAB, EV: 0xAC, MMODE: 0xAD,
    DEB: 0xAE, LIST: 0xAF, MCOUNT: 0xBF, MWORDS: 0xC0, MHAND: 0xC2, SEL: 0xC8, MODE: 0xC9, PAGE: 0xCB, STATE: 0xCC,
    NAMES: 0xCE, HDR: 0xFFD0, TOKP: 0x94, TT: 0x96, SY: 0x98, MHOT: 0x99, CBG: 0x9A, CMB: 0x9B, CMT: 0xCD,
    VSYNC: 0x00, VBLANK: 0x01, WSYNC: 0x02, NUSIZ0: 0x04, NUSIZ1: 0x05, COLUP0: 0x06, COLUP1: 0x07, COLUBK: 0x09,
    RESP0: 0x10, GRP0: 0x1B, GRP1: 0x1C, HMP0: 0x20, VDELP0: 0x25, VDELP1: 0x26, HMOVE: 0x2A, HMCLR: 0x2B,
    INPT4: 0x0C, SWCHA: 0x0280, SWCHB: 0x0282, INTIM: 0x0284, TIM8T: 0x0295, TIM64T: 0x0296,
  };
  // screen geometry (scanlines) and sprite positions; see the calibration notes in the builder
  const TAK_GEO = { TOPLINES: 11, PADLINES: 5, GAPT: 80, MENUPAD: 2, RESTLINES: 5, VBT: 43, OST: 35, XE: 29 };

  function takEngineSource(o) {
    const L = [];
    const add = (...x) => L.push(...x);
    // ---------- reset: make sure we run in the start bank, clear RAM and the TIA ----------
    add('RESET: SEI', 'CLD', 'LDA STARTHOT', 'LDX #0', 'TXA', 'RCLR: DEX', 'TXS', 'PHA', 'BNE RCLR',
      'LDA INTRO', 'STA TXT', 'LDA INTRO+1', 'STA TXT+1');
    add(o.npages > 1 ? 'JSR SETMOREM' : 'JSR SETSTARTM');
    // ---------- frame ----------
    add('FRAME: LDA #2', 'STA VBLANK', 'STA WSYNC', 'STA VSYNC', 'STA WSYNC', 'STA WSYNC', 'STA WSYNC', 'LDA #0', 'STA VSYNC',
      'LDA #VBT', 'STA TIM64T', 'INC FRAMEC', 'LDA FRAMEC', 'AND #1', 'STA PAR',
      'LDA SWCHB', 'LSR A', 'BCS NORES', 'JMP RESET',
      'NORES: JSR INPUT',
      // text can live in any bank: the high nibble of the message address names it ($F = this map's bank)
      'LDA PTBL', 'STA MHOT', 'LDA HDR', 'STA CBG', 'LDA HDR+2', 'STA CMB', 'LDA HDR+3', 'STA CMT',
      'LDA HDR+1', 'STA COLUP0', 'STA COLUP1',
      'LDA TXT+1', 'CMP #$F0', 'BCS NOSW', 'LSR A', 'LSR A', 'LSR A', 'LSR A', 'TAY', 'LDA HOTS,Y', 'NOSW: JSR PREP',
      'VBW: LDA INTIM', 'BNE VBW', 'STA WSYNC', 'LDA #0', 'STA VBLANK');
    // ---------- visible picture: 192 scanlines ----------
    add('LDX #TOPLINES', 'D1: STA WSYNC', 'DEX', 'BNE D1',
      'LDA CBG', 'STA COLUBK', 'LDX #PADLINES', 'D2: STA WSYNC', 'DEX', 'BNE D2',
      'LDA #10', 'STA LINE',
      'TL: LDY #5', 'LDA (P5),Y', 'TAX', 'LDA PAR', 'BNE TLO', 'STA WSYNC', 'JMP KE', 'TLO: STA WSYNC', 'JMP KO');
    // the two kernels differ only by a 3-cycle delay: odd frames' sprites sit 8 px further right
    for (const [K, odd] of [['KE', false], ['KO', true]]) {
      add(`${K}: LDA (P1),Y`, 'STA GRP0', 'LDA (P2),Y', 'STA GRP1', 'LDA (P3),Y', 'STA GRP0',
        'LDA (P6),Y', 'STA TMPV');
      if (odd) add('BIT $80');
      add('LDA (P4),Y', 'STA GRP1', 'STX GRP0', 'LDA TMPV', 'STA $001C', 'DEY', 'BMI KX',
        'LDA (P5),Y', 'TAX', 'STA WSYNC', `JMP ${K}`);
    }
    // after six rows: blank the players, then a gap during which the next line is read
    add('KX: LDA #0', 'NOP', 'STA GRP0', 'STA GRP1', 'STA GRP0',
      'LDA LINE', 'BEQ AFTERMENU',
      'STA WSYNC', 'LDA #GAPT', 'STA TIM8T', 'DEC LINE', 'BEQ TOMENU', 'JSR PARSE',
      'G1: LDA INTIM', 'BNE G1', 'LDY #5', 'LDA (P5),Y', 'TAX', 'LDA PAR', 'BNE G1O', 'STA WSYNC', 'JMP KE', 'G1O: STA WSYNC', 'JMP KO',
      'TOMENU: LDA MENUW', 'STA TP', 'LDA MENUW+1', 'STA TP+1', 'JSR PARSE',
      'G2: LDA INTIM', 'BNE G2', 'STA WSYNC', 'LDA CMB', 'STA COLUBK', 'LDA CMT', 'STA COLUP0', 'STA COLUP1',
      'LDX #MENUPAD', 'D3: STA WSYNC', 'DEX', 'BNE D3', 'JMP TL',
      'AFTERMENU: STA WSYNC', 'LDA #0', 'STA COLUBK', 'LDX #RESTLINES', 'D4: STA WSYNC', 'DEX', 'BNE D4',
      // overscan
      'LDA #2', 'STA VBLANK', 'LDA #OST', 'STA TIM64T', 'LDY MHOT', 'LDA $FF00,Y', 'OSW: LDA INTIM', 'BNE OSW', 'JMP FRAME');
    // ---------- read one text line from TP into the six glyph pointers (this frame's half) ----------
    // Every character is stored at P1+X with X = its column (odd frames start at -1), so this frame's
    // half land on the pointers' low bytes; the others land on high bytes, which are reset afterwards.
    // Dictionary words are copied from the bank's word page. Finally glyph numbers become font offsets.
    add('PARSE: LDA #SPACEI', 'STA P1', 'STA P2', 'STA P3', 'STA P4', 'STA P5', 'STA P6',
      'LDX #0', 'LDA PAR', 'BEQ PA0', 'DEX', 'PA0: LDY #0',
      'PL: LDA (TP),Y', 'INY', 'CMP #NGLYPH', 'BCS PSPEC', 'STA P1,X', 'INX', 'JMP PL',
      'PSPEC: CMP #$FE', 'BCS PEND', 'STY SY', 'SBC #NGLYPH-1', 'TAY', 'LDA (TOKP),Y', 'STA TT', 'LDY #0',
      'PT: LDA (TT),Y', 'BMI PTE', 'STA P1,X', 'INX', 'INY', 'BNE PT',
      'PTE: LDY SY', 'JMP PL',
      // $FF ends the line: step past it. $FE ends the message: stay on it so later lines are blank.
      'PEND: BEQ PMAP', 'TYA', 'CLC', 'ADC TP', 'STA TP', 'BCC PMAP', 'INC TP+1',
      'PMAP: LDA #>FONT', 'STA P1+1', 'STA P2+1', 'STA P3+1', 'STA P4+1', 'STA P5+1', 'STA P6+1',
      'LDY P1', 'LDA GMAP,Y', 'STA P1', 'LDY P2', 'LDA GMAP,Y', 'STA P2', 'LDY P3', 'LDA GMAP,Y', 'STA P3',
      'LDY P4', 'LDA GMAP,Y', 'STA P4', 'LDY P5', 'LDA GMAP,Y', 'STA P5', 'LDY P6', 'LDA GMAP,Y', 'STA P6', 'RTS');
    // ---------- per-frame set-up during vertical blank ----------
    add('PREP: LDA #6', 'STA NUSIZ0', 'STA NUSIZ1', 'LDA #1', 'STA VDELP0',
      'LDA #0', 'STA VDELP1', 'STA COLUBK', 'STA GRP0', 'STA GRP1', 'STA GRP0',
      'LDX #0', 'LDA PAR', 'BEQ PPE', 'LDA #XE+8', 'BNE PPP', 'PPE: LDA #XE', 'PPP: STA T1', 'JSR POS',
      'LDA T1', 'CLC', 'ADC #16', 'LDX #1', 'JSR POS', 'STA WSYNC', 'STA HMOVE',
      'LDA HDR+8', 'STA TOKP', 'LDA HDR+9', 'STA TOKP+1', 'LDA HDR+10', 'STA TT+1',
      'LDA TXT', 'STA TP', 'LDA TXT+1', 'ORA #$F0', 'STA TP+1', 'JMP PARSE',
      // horizontal positioning: coarse with RESPx after a divide-by-15 delay, fine with HMPx
      'POS: STA WSYNC', 'SEC', 'PD: SBC #15', 'BCS PD', 'EOR #7', 'ASL A', 'ASL A', 'ASL A', 'ASL A', 'STA HMP0,X', 'STA RESP0,X', 'RTS');
    // ---------- controls ----------
    add('INPUT: LDA STATE', 'BEQ IN1');
    if (o.endEvent != null) add(`LDX #${o.endEvent}`, 'LDY #EV', 'JSR BTST', 'BNE ENDED');
    add('JSR GETREC', 'LDY #0', 'LDA (REC),Y', 'LSR A', 'BCC IN1',
      'ENDED: LDA #<W_END', 'STA MENUW', 'LDA #>W_END', 'STA MENUW+1', 'RTS',
      'IN1: LDA INPT4', 'BMI NOTPR', 'LDA DEB', 'BNE IRTS', 'INC DEB', 'LDA ROOM', 'STA PREV',
      'LDA MMODE', 'CMP #2', 'BNE IN2', 'JMP HPICK', 'IN2: LDA SELI', 'ASL A', 'TAY', 'LDA (MHAND),Y', 'STA T1', 'INY', 'LDA (MHAND),Y', 'STA T2', 'JMP (T1)',
      'NOTPR: LDA #0', 'STA DEB', 'LDA FRAMEC', 'AND #7', 'BNE IRTS', 'LDA MMODE', 'BNE CYC',
      // walking: the stick picks NORTH/EAST/SOUTH/WEST, centred means LOOK
      'LDA SWCHA', 'LDX #2', 'ASL A', 'BCC SETI', 'LDX #4', 'ASL A', 'BCC SETI', 'LDX #3', 'ASL A', 'BCC SETI',
      'LDX #1', 'ASL A', 'BCC SETI', 'LDX #0', 'SETI: STX SELI', 'JMP SELWORD',
      // other menus: right / left step through the entries
      'CYC: LDA SWCHA', 'ASL A', 'BCC CRT', 'ASL A', 'BCC CLT', 'IRTS: RTS',
      'CRT: INC SELI', 'LDA SELI', 'CMP MCOUNT', 'BCC CSW', 'LDA #0', 'STA SELI', 'CSW: JMP SELWORD',
      'CLT: DEC SELI', 'BPL CSW', 'LDX MCOUNT', 'DEX', 'STX SELI', 'JMP SELWORD');
    // ---------- menus ----------
    add('SELWORD: LDA SELI', 'ASL A', 'TAY', 'LDA (MWORDS),Y', 'STA MENUW', 'INY', 'LDA (MWORDS),Y', 'STA MENUW+1', 'RTS',
      // each entry skips the next one's LDX with a BIT absolute ($2C)
      'SETMOVE: LDX #0', '.byte $2C', 'SETACT: LDX #6', '.byte $2C', 'SETMOREM: LDX #12', '.byte $2C', 'SETSTARTM: LDX #18',
      'LDA MT,X', 'STA MWORDS', 'LDA MT+1,X', 'STA MWORDS+1', 'LDA MT+2,X', 'STA MHAND', 'LDA MT+3,X', 'STA MHAND+1',
      'LDA MT+4,X', 'STA MCOUNT', 'LDA MT+5,X', 'STA MMODE', 'LDA #0', 'STA SELI', 'JMP SELWORD');
    // ---------- intro ----------
    add('HMORE: INC PAGE', 'LDA PAGE', 'ASL A', 'TAY', 'LDA INTRO,Y', 'STA TXT', 'LDA INTRO+1,Y', 'STA TXT+1',
      'LDA PAGE', 'CMP #NPAGES-1', 'BCC HM1', 'JMP SETSTARTM', 'HM1: RTS',
      'HSTART: LDA #1', 'STA STATE', 'LDA #START2', 'STA ROOM', 'LDA #<STARTINV', 'STA INV', 'LDA #>STARTINV', 'STA INV+$1E',
      'JSR GETREC', 'LDX #6', 'JMP SAY');
    // ---------- rooms ----------
    add('GETREC: LDA HDR+5', 'STA T1', 'LDA HDR+6', 'STA T2', 'LDY ROOM', 'LDA (T1),Y', 'STA REC', 'INY', 'LDA (T1),Y', 'STA REC+1', 'RTS',
      'REC0: JSR GETREC', 'LDY #0', 'LDA (REC),Y', 'RTS',
      // A room record is [flags, field mask lo, hi] and then only the fields it has, in order:
      // six one-byte fields (0-5) and eight message pointers (6-13). FLD: X = field -> Y = its offset, C = present.
      'FLD: STX SY', 'LDY #1', 'LDA (REC),Y', 'STA T1', 'INY', 'LDA (REC),Y', 'STA T2', 'INY', 'LDX #0',
      'FL1: CPX SY', 'BEQ FL3', 'LSR T2', 'ROR T1', 'BCC FL2', 'INY', 'CPX #6', 'BCC FL2', 'INY', 'FL2: INX', 'BNE FL1',
      'FL3: LSR T2', 'ROR T1', 'RTS',
      'GETF: JSR FLD', 'LDA #$FF', 'BCC GF1', 'LDA (REC),Y', 'GF1: TAX', 'CMP #$FF', 'RTS',
      'SETTXT: JSR FLD', 'SETTY: LDA (REC),Y', 'STA TXT', 'INY', 'LDA (REC),Y', 'STA TXT+1', 'RTS',
      'SAY: JSR SETTXT', 'JMP SETMOVE',
      'SAYW: STA TXT', 'STY TXT+1', 'JMP SETMOVE');
    // ---------- walking ----------
    add('HN: LDA ROOM', 'SEC', 'SBC HDR+4', 'JMP MOVE', 'HS: LDA ROOM', 'CLC', 'ADC HDR+4', 'JMP MOVE',
      'HE: LDA ROOM', 'CLC', 'ADC #2', 'JMP MOVE', 'HW: LDA ROOM', 'SEC', 'SBC #2',
      'MOVE: JSR PORTAL', 'STA ROOM', 'JSR GETREC', 'LDY #0', 'LDA (REC),Y', 'BEQ MWALL', 'AND #2', 'BEQ MOK',
      'LDX #5', 'JSR GETF', 'LDY #EV', 'JSR BTST', 'BNE MOK',
      // locked: stay put. Through a portal, show the copy of the message kept in the bank we came from.
      'LDA PREV', 'STA ROOM', 'LDY PHOT', 'BEQ MLK1', 'LDA #0', 'STA PHOT', 'LDA PMSGLO', 'STA TXT', 'LDA PMSGHI', 'STA TXT+1',
      'LDA $FF00,Y', 'JMP SETMOVE', 'MLK1: LDX #12', 'JMP SAY',
      'MWALL: LDA PREV', 'STA ROOM', 'LDY #1', 'JSR SETTY', 'JMP SETMOVE',
      'MOK: LDA #0', 'STA PHOT', 'LDX #6', 'JMP SAY',
      // portal table (same address in every bank, this bank's own contents):
      // [own hotspot] then [from*2, hotspot, dest*2, locked message lo, hi], $FF ends
      'PORTAL: LDX #0', 'PO1: LDY PTBL+1,X', 'CPY #$FF', 'BEQ PON', 'CMP PTBL+1,X', 'BEQ POH', 'INX', 'INX', 'INX', 'INX', 'INX', 'BNE PO1',
      'POH: LDY PTBL', 'STY PHOT', 'LDY PTBL+4,X', 'STY PMSGLO', 'LDY PTBL+5,X', 'STY PMSGHI', 'LDA PTBL+3,X', 'LDY PTBL+2,X', 'LDX $FF00,Y', 'RTS',
      'PON: LDX #0', 'STX PHOT', 'RTS');
    // ---------- 16-bit item / event bits: X = number, Y = address of the low byte ----------
    add('BTST: LDA $0000,Y', 'AND ML,X', 'BNE BT1', 'LDA $001E,Y', 'AND MH,X', 'BT1: RTS',
      'BSET: LDA $0000,Y', 'ORA ML,X', 'STA $0000,Y', 'LDA $001E,Y', 'ORA MH,X', 'STA $001E,Y', 'RTS',
      'BCLR: LDA ML,X', 'EOR #$FF', 'AND $0000,Y', 'STA $0000,Y', 'LDA MH,X', 'EOR #$FF', 'AND $001E,Y', 'STA $001E,Y', 'RTS');
    // ---------- verbs ----------
    add('HLOOK: JSR GETREC', 'LDX #7', 'JSR SETTXT', 'LDY #0', 'LDA (REC),Y', 'BEQ LK9', 'BMI LK9',
      'LDX #0', 'JSR GETF', 'BEQ LK9', 'LDY #TK', 'JSR BTST', 'BNE LKN', 'LDY #SEEN', 'JSR BSET', 'LK9: JMP SETACT',
      'LKN: LDA #<M_NSPEC', 'STA TXT', 'LDA #>M_NSPEC', 'STA TXT+1', 'JMP SETACT',
      'HGO: JSR GETREC', 'LDX #6', 'JMP SAY',
      'HTAKE: JSR REC0', 'AND #$40', 'BEQ TKN', 'LDX #0', 'JSR GETF', 'BEQ TKN', 'LDY #TK', 'JSR BTST', 'BNE TKN',
      'LDY #INV', 'JSR BTST', 'BNE TKN', 'LDY #SEEN', 'JSR BTST', 'BEQ TKN', 'LDY #INV', 'JSR BSET', 'LDY #TK', 'JSR BSET',
      'LDX #8', 'JMP SAY', 'TKN: LDA #<M_NTAKE', 'LDY #>M_NTAKE', 'JMP SAYW',
      'HTALK: JSR REC0', 'AND #$08', 'BEQ THELLO', 'LDX #3', 'JSR GETF', 'BEQ TDEF', 'LDY #USED', 'JSR BTST', 'BEQ TDEF',
      'LDX #4', 'JSR GETF', 'BEQ TOK', 'LDY #EV', 'JSR BSET', 'TOK: LDX #11', 'JMP SAY', 'TDEF: LDX #13', 'JMP SAY',
      'THELLO: LDA #<M_HELLO', 'LDY #>M_HELLO', 'JMP SAYW',
      // GIVE / USE / INVENTORY: list the carried items (or one "nothing" entry)
      'HGIVE: LDX #1', 'LDA #<M_SELG', 'LDY #>M_SELG', 'BNE OPEN', 'HUSE: LDX #2', 'LDA #<M_SELU', 'LDY #>M_SELU', 'BNE OPEN',
      'HINV: LDX #0', 'LDA #<M_CARRY', 'LDY #>M_CARRY',
      'OPEN: STX MODE', 'STA TXT', 'STY TXT+1', 'LDA #0', 'STA T2', 'TAX',
      'OB1: LDY #INV', 'JSR BTST', 'BEQ OB2', 'LDY T2', 'TXA', 'STA $00AF,Y', 'INC T2', 'OB2: INX', 'CPX #16', 'BNE OB1',
      'LDA T2', 'BNE OB3', 'LDA #$FF', 'STA LIST', 'LDA #<W_NOTHING', 'STA NAMES', 'LDA #>W_NOTHING', 'STA NAMES+1', 'INC T2', 'BNE OB5',
      'OB3: LDX #0', 'OB4: TXA', 'LSR A', 'TAY', 'LDA $00AF,Y', 'ASL A', 'TAY', 'LDA ITEMS,Y', 'STA NAMES,X', 'LDA ITEMS+1,Y', 'STA NAMES+1,X',
      'INX', 'INX', 'TXA', 'LSR A', 'CMP T2', 'BNE OB4',
      'OB5: LDA #NAMES', 'STA MWORDS', 'LDA #0', 'STA MWORDS+1', 'STA SELI', 'LDA T2', 'STA MCOUNT', 'LDA #2', 'STA MMODE', 'JMP SELWORD',
      'HPICK: LDX SELI', 'LDA LIST,X', 'STA SEL', 'LDA MODE', 'BNE PK1', 'JMP HGO', 'PK1: LSR A', 'BCS GIVEDO',
      'USEDO: JSR REC0', 'AND #$10', 'BEQ UNO', 'LDX #1', 'JSR GETF', 'CMP SEL', 'BNE UNO', 'LDY #USED', 'JSR BSET',
      'JSR REC0', 'AND #$04', 'BEQ UOK', 'LDX #4', 'JSR GETF', 'BEQ UOK', 'LDY #EV', 'JSR BSET', 'UOK: LDX #9', 'JMP SAY',
      'UNO: LDA #<M_CUSE', 'LDY #>M_CUSE', 'JMP SAYW',
      'GIVEDO: JSR REC0', 'AND #$20', 'BEQ GNO', 'LDX #2', 'JSR GETF', 'CMP SEL', 'BNE GNO', 'LDY #INV', 'JSR BCLR',
      'LDX #4', 'JSR GETF', 'BEQ GV2', 'LDY #EV', 'JSR BSET', 'GV2: LDX #0', 'JSR GETF', 'BEQ GV3', 'LDY #SEEN', 'JSR BSET',
      'GV3: LDX #10', 'JMP SAY', 'GNO: LDA #<M_CGIVE', 'LDY #>M_CGIVE', 'JMP SAYW');
    // ---------- tables ----------
    const tbl = (label, names) => { add(`${label}: .byte ` + names.map(n => `<${n},>${n}`).join(',')); };
    add('ML: .byte 1,2,4,8,16,32,64,128,0,0,0,0,0,0,0,0', 'MH: .byte 0,0,0,0,0,0,0,0,1,2,4,8,16,32,64,128');
    tbl('MOVEW', ['W_LOOK', 'W_NORTH', 'W_EAST', 'W_SOUTH', 'W_WEST']);
    tbl('MOVEH', ['HLOOK', 'HN', 'HE', 'HS', 'HW']);
    tbl('ACTW', ['W_GO', 'W_TAKE', 'W_GIVE', 'W_USE', 'W_TALK', 'W_INV']);
    tbl('ACTH', ['HGO', 'HTAKE', 'HGIVE', 'HUSE', 'HTALK', 'HINV']);
    tbl('MOREW', ['W_MORE']); tbl('MOREH', ['HMORE']); tbl('STARTW', ['W_START']); tbl('STARTH', ['HSTART']);
    add('MT: .byte <MOVEW,>MOVEW,<MOVEH,>MOVEH,5,0, <ACTW,>ACTW,<ACTH,>ACTH,6,1, <MOREW,>MOREW,<MOREH,>MOREH,1,1, <STARTW,>STARTW,<STARTH,>STARTH,1,1');
    return L;
  }

  // ---------- Build a cartridge on the Workshop engine (no Dark Mage ROM needed) ----------
  const TAK_HDR = 0xFFD0;
  function takSyms(extra) { return Object.assign({}, TAK_ZP, TAK_GEO, extra); }
  const TAK_DUMMY = {
    STARTHOT: 0xFFF9, NPAGES: 2, START2: 2, STARTINV: 0, PTBL: 0xF000, INTRO: 0xF000, ITEMS: 0xF000, FONT: 0xF100, HOTS: 0xFFF8, SPACEI: 0, GMAP: 0xF000, NGLYPH: 51,
    W_LOOK: 0xF000, W_NORTH: 0xF000, W_EAST: 0xF000, W_SOUTH: 0xF000, W_WEST: 0xF000, W_GO: 0xF000, W_TAKE: 0xF000, W_GIVE: 0xF000,
    W_USE: 0xF000, W_TALK: 0xF000, W_INV: 0xF000, W_MORE: 0xF000, W_START: 0xF000, W_END: 0xF000, W_NOTHING: 0xF000,
    M_NSPEC: 0xF000, M_NTAKE: 0xF000, M_HELLO: 0xF000, M_SELG: 0xF000, M_CGIVE: 0xF000, M_SELU: 0xF000, M_CUSE: 0xF000, M_CARRY: 0xF000,
  };
  function buildTak(project, opts = {}) {
    const measure = !!opts.measure;
    const P = normalize(project);
    const { errs, warns } = measure ? { errs: [], warns: [] } : validate(P);
    if (errs.length) return { ok: false, errs, warns };
    ENC = GIDX;
    try { return go(); } finally { ENC = CHAR; }
    function go() {
      const cart = CARTS[P.cart], NB = cart.banks;
      const order = bankOrder(P.cart), startBank = cart.start;
      const LIM = Math.min(cart.base, TAK_HDR);
      const rom = new Uint8Array(4096 * NB).fill(0xFF);
      const banks = Array.from({ length: NB }, (_, b) => rom.subarray(b * 4096, (b + 1) * 4096));
      const srcOpts = { npages: P.intro.length, endEvent: P.settings.endEvent };
      const dummy = assemble(takEngineSource(srcOpts), BASE, takSyms(TAK_DUMMY));
      const codeLen = dummy.bytes.length, logicAt = dummy.labels.INPUT;
      const codeEnd = BASE + codeLen;
      const FONT = (codeEnd + 0xFF) & ~0xFF;
      // ---- common block: identical in every bank ----
      const cb = banks[startBank];
      cb.set(XFONT, FONT - BASE);
      const cw = new Writer(cb, FONT + XFONT.length, LIM, [[codeEnd, FONT]]);
      const sym = {};
      const words = { W_LOOK: 'look', W_NORTH: 'north', W_EAST: 'east', W_SOUTH: 'south', W_WEST: 'west', W_GO: 'go', W_TAKE: 'take', W_GIVE: 'give',
        W_USE: 'use', W_TALK: 'talk', W_INV: 'inventory', W_MORE: 'more', W_START: 'start', W_END: 'theEnd', W_NOTHING: 'nothing' };
      const msgs = { M_NSPEC: 'nothingSpecial', M_NTAKE: 'nothingToTake', M_HELLO: 'talkDefault', M_SELG: 'selectGive', M_CGIVE: 'cantGive',
        M_SELU: 'selectUse', M_CUSE: 'cantUse', M_CARRY: 'carrying' };
      const maxPortals = Math.max(0, ...P.maps.map((_, m) => P.portals.filter(p => p.map === m).length));
      try {
        const pend = [];
        for (const [s, k] of Object.entries(words)) pend.push([s, encodePage(P.system[k], true)]);
        for (const [s, k] of Object.entries(msgs)) pend.push([s, encodePage(P.system[k])]);
        P.items.slice(0, 16).forEach((t, i) => pend.push(['I' + i, encodePage(t, true)]));
        pend.sort((a, b) => b[1].length - a[1].length);
        for (const [s, bytes] of pend) sym[s] = cw.str(bytes);
        sym.GMAP = cw.put(GMAP);
        sym.ITEMS = cw.put(Array.from({ length: 16 }, (_, i) => [lo(sym['I' + i]), hi(sym['I' + i])]).flat());
        sym.PTBL = cw.put(new Array(maxPortals * 5 + 2).fill(0xFF));
        sym.INTRO = cw.put(new Array(P.intro.length * 2).fill(0));
      } catch (x) { if (x.message === 'OUT_OF_SPACE') return { ok: false, errs: ['Out of space in the shared text block'], warns }; throw x; }
      const commonEnd = cw.pc, commonHoles = cw.holes.map(h => [h.pc, h.end]);
      for (const bk of banks) if (bk !== cb) bk.set(cb.subarray(codeEnd - BASE, commonEnd - BASE), codeEnd - BASE);

      // ---- what each map needs: its grid, its room records and the messages they point to ----
      const T = new Map(); // text key -> { bytes, refs: Set of maps }
      const want = (m, t) => { const bytes = encodePage(t), k = bytes.join(','); if (!T.has(k)) T.set(k, { bytes, refs: new Set() }); T.get(k).refs.add(m); return k; };
      const maps = P.maps.map((map, m) => {
        const hasRoom = map.cells.some((c, i) => c.type === 'room' && !portalAt(P, m, i));
        const used = m === 0 || hasRoom || P.portals.some(p => p.toMap === m);
        const info = { m, b: order[m], map, used, recs: [], lockKeys: [], introKeys: [], fixed: 0 };
        if (!used) return info;
        const wallSeen = new Set();
        info.recs = map.cells.map((c, i) => {
          if (portalAt(P, m, i)) return null;
          if (c.type === 'wall') { const k = want(m, c.text); if (!wallSeen.has(k)) { wallSeen.add(k); info.fixed += 3; } return { wall: k }; }
          const r = { c, k: [want(m, c.desc), want(m, c.look)] };
          r.k[2] = c.take.on ? want(m, c.take.text) : null;
          r.k[3] = c.use.on ? want(m, c.use.text) : null;
          r.k[4] = c.give.on ? want(m, c.give.text) : null;
          r.k[5] = c.talk.on && c.talk.needUsed != null ? want(m, c.talk.ok) : null;
          r.k[6] = c.door.on ? want(m, c.door.text) : null;
          r.k[7] = c.talk.on ? want(m, c.talk.no) : null;
          const one = [c.item, c.use.on ? c.use.item : null, c.give.on ? c.give.item : null, c.talk.on ? c.talk.needUsed : null, c.sets, c.door.on ? c.door.needEvent : null];
          info.fixed += 3 + one.filter(v => v != null).length + 2 * r.k.filter(Boolean).length;
          return r;
        });
        if (!info.recs.some(Boolean)) info.fixed += 3;
        info.fixed += map.cells.length * 2;
        info.lockKeys = P.portals.filter(p => p.map === m).map(p => { const d = P.maps[p.toMap].cells[p.toIdx]; return d && d.type === 'room' && d.door.on ? want(m, d.door.text) : null; });
        if (m === 0) info.introKeys = P.intro.map(t => want(m, t));
        return info;
      });
      const byBank = []; maps.forEach(x => byBank[x.b] = x);
      // room for text in each bank: everything after the shared block, plus the logic code area in a bank no map uses
      const holeFree0 = commonHoles.reduce((t, [a, e]) => t + (e - a), 0);
      const cap = byBank.map(x => LIM - commonEnd + holeFree0 + (x.used ? 0 : codeEnd - logicAt) - x.fixed - 12);
      // ---- place every message in a bank: first its own map's, then wherever there is room ----
      const place = new Map();
      for (const [k, t] of T) place.set(k, Math.min(...[...t.refs].map(m => order[m])));
      const sizeOf = keys => {
        if (!keys.length) return { size: 0, plain: 0, packed: 0, words: 0 };
        const pages = keys.map(k => T.get(k).bytes);
        const cz = opts.compress === false ? { toks: [], pages, dictBytes: 0 } : takCompress(pages);
        const packed = cz.pages.reduce((t, p) => t + p.length, 0) + cz.dictBytes + cz.toks.length;
        return { size: packed, plain: pages.reduce((t, p) => t + p.length, 0), packed, words: cz.toks.length };
      };
      const keysIn = b => [...place.keys()].filter(k => place.get(k) === b);
      let est = byBank.map((_, b) => sizeOf(keysIn(b)));
      for (let round = 0; round < 24; round++) {
        const over = byBank.map((_, b) => est[b].size - cap[b]);
        const worst = over.indexOf(Math.max(...over));
        if (over[worst] <= 0) break;
        // move messages out of the fullest bank, largest first, to banks with room (a bank's own messages stay put when possible)
        const room = byBank.map((_, b) => cap[b] - est[b].size);
        const ks = keysIn(worst).sort((a, c) => {
          const own = k => T.get(k).refs.has(byBank[worst].m) ? 1 : 0;
          return own(a) - own(c) || T.get(c).bytes.length - T.get(a).bytes.length;
        });
        let need = over[worst] + 8, moved = false;
        const touched = new Set([worst]);
        for (const k of ks) {
          if (need <= 0) break;
          const len = T.get(k).bytes.length, guess = Math.ceil(len * 0.85);
          let tgt = -1;
          for (let b = 0; b < NB; b++) if (b !== worst && b < 15 && room[b] - guess > 8 && (tgt < 0 || room[b] > room[tgt])) tgt = b;
          if (tgt < 0) break;
          place.set(k, tgt); room[tgt] -= guess; need -= guess; moved = true; touched.add(tgt);
        }
        if (!moved) break;
        for (const b of touched) est[b] = sizeOf(keysIn(b));
      }
      const overBy = byBank.map((_, b) => est[b].size - cap[b]);
      const usageOf = () => maps.map(x => {
        const b = x.b, total = LIM - commonEnd + holeFree0 + (x.used ? 0 : codeEnd - logicAt), used = x.fixed + est[b].size + 12;
        const own = [...T.entries()].filter(([k, t]) => t.refs.has(x.m));
        const away = own.filter(([k]) => place.get(k) !== b).reduce((t, [, v]) => t + v.bytes.length, 0);
        const guests = keysIn(b).filter(k => !T.get(k).refs.has(x.m)).reduce((t, k) => t + T.get(k).bytes.length, 0);
        return { used, total, free: total - used, text: est[b].plain, packed: est[b].packed, words: est[b].words, away, guests, textOnly: !x.used };
      });
      if (overBy.some(v => v > 0)) {
        const short = overBy.reduce((t, v) => t + Math.max(0, v), 0), roomLeft = overBy.reduce((t, v) => t + Math.max(0, -v), 0);
        const u = usageOf();
        return { ok: false, errs: [`Out of room: the text needs about ${Math.max(10, short - roomLeft).toLocaleString()} more bytes than this cartridge has. Shorten some text, reuse identical messages, or choose a bigger cartridge.`], warns, usage: { maps: u, mapA: u[0], mapB: u[1] } };
      }
      // ---- write each bank: dictionary and messages first, then the records that point at them ----
      const addr = new Map(), W = [], meta = [];
      try {
        for (let b = 0; b < NB; b++) {
          const x = byBank[b], bk = banks[b];
          const holes = commonHoles.concat(x.used ? [] : [[logicAt, codeEnd]]);
          const w = new Writer(bk, commonEnd, LIM, holes);
          w.cache = new Map(cw.cache);
          W[b] = w;
          const table = x.used ? w.put(new Array(x.map.cells.length * 2).fill(0)) : 0;
          w.searchFrom = w.pc;
          const keys = keysIn(b);
          const cz = !keys.length || opts.compress === false ? { toks: [], pages: keys.map(k => T.get(k).bytes) } : takCompress(keys.map(k => T.get(k).bytes));
          const toklo = w.put(new Array(Math.max(1, cz.toks.length)).fill(0));
          const dict = [], at = [];
          [...cz.toks.keys()].sort((a, c) => cz.toks[c].length - cz.toks[a].length).forEach(k => {
            const t = cz.toks[k].concat([0xFF]);
            let o = -1;
            for (let i = 0; i + t.length <= dict.length && o < 0; i++) if (t.every((v, j) => dict[i + j] === v)) o = i;
            if (o < 0) { o = dict.length; dict.push(...t); }
            at[k] = o;
          });
          let dictAt = w.pc;
          if (dict.length && (dictAt & 0xFF) + dict.length > 0x100) { const nx = (dictAt + 0xFF) & ~0xFF; w.holes.push({ pc: dictAt, end: nx, start: dictAt }); w.pc = nx; dictAt = nx; }
          if (dict.length) w.put(dict);
          at.forEach((o, k) => { bk[toklo + k - BASE] = lo(dictAt + o); });
          const z = new Map(keys.map((k, i) => [k, cz.pages[i]]));
          keys.slice().sort((p, q) => z.get(q).length - z.get(p).length).forEach(k => addr.set(k, { a: w.str(z.get(k)), b }));
          meta[b] = { table, toklo, dictAt };
        }
        // a pointer from map m to message k: the high nibble names the bank unless it is m's own
        const ptr = (m, k) => { const { a, b } = addr.get(k); return b === order[m] ? a : (a & 0x0FFF) | (b << 12); };
        for (let b = 0; b < NB; b++) {
          const x = byBank[b], bk = banks[b], w = W[b], { table, toklo, dictAt } = meta[b];
          const col = x.map.colors || DEFAULT_COLORS;
          let ents = [];
          if (x.used) {
            const m = x.m, recCache = new Map();
            const recAddr = x.recs.map(r => {
              if (!r) return null;
              let bytes;
              if (r.wall) { const a = ptr(m, r.wall); bytes = [0, lo(a), hi(a)]; }
              else {
                const c = r.c;
                let f = 0;
                if (c.ending) f |= 0x01;
                if (c.door.on) f |= 0x02;
                if (c.use.on && c.use.setsEvent) f |= 0x04;
                if (c.talk.on) f |= 0x08;
                if (c.use.on) f |= 0x10;
                if (c.give.on) f |= 0x20;
                if (c.take.on) f |= 0x40;
                if (!(c.lookReveals && c.item != null)) f |= 0x80;
                // [flags, mask lo, mask hi] + present one-byte fields + present message pointers
                const one = [c.item, c.use.on ? c.use.item : null, c.give.on ? c.give.item : null, c.talk.on ? c.talk.needUsed : null, c.sets, c.door.on ? c.door.needEvent : null];
                let mask = 0; const body = [];
                one.forEach((v, i) => { if (v != null) { mask |= 1 << i; body.push(v); } });
                r.k.forEach((k, i) => { if (k) { mask |= 1 << (6 + i); const a = ptr(m, k); body.push(lo(a), hi(a)); } });
                bytes = [f, mask & 0xFF, mask >> 8, ...body];
              }
              const key = bytes.join(',');
              if (!recCache.has(key)) recCache.set(key, w.put(bytes));
              return recCache.get(key);
            });
            let any = recAddr.find(a => a != null);
            if (any == null) any = w.put([0, 0xFF, 0xFF]);
            recAddr.forEach((a, i) => { const v = a == null ? any : a; bk[table + 2 * i - BASE] = lo(v); bk[table + 2 * i + 1 - BASE] = hi(v); });
            ents = P.portals.filter(p => p.map === m).flatMap((p, k) => { const a = x.lockKeys[k] ? ptr(m, x.lockKeys[k]) : 0; return [(p.idx * 2) & 0xFF, lo(cart.base + order[p.toMap]), (p.toIdx * 2) & 0xFF, lo(a), hi(a)]; });
          }
          bk.set([lo(cart.base + b), ...ents, 0xFF], sym.PTBL - BASE);
          bk.set([col.bg & 0xFE, col.text & 0xFE, col.menuBg & 0xFE, col.menuText & 0xFE, (x.map.width * 2) & 0xFF, lo(table), hi(table), FONT >> 8,
            lo(toklo), hi(toklo), hi(dictAt), lo(sym.GMAP), hi(sym.GMAP), NGLYPH], TAK_HDR - BASE);
        }
        // intro page table (shared; read in the start bank)
        const it = maps[0].introKeys.flatMap(k => { const a = ptr(0, k); return [lo(a), hi(a)]; });
        for (const bk of banks) bk.set(it, sym.INTRO - BASE);
      } catch (x) {
        if (x.message === 'OUT_OF_SPACE') {
          const u = usageOf();
          return { ok: false, errs: ['Out of room: the text only just fails to fit. Shorten a message or two, or choose a bigger cartridge.'], warns, usage: { maps: u, mapA: u[0], mapB: u[1] } };
        }
        throw x;
      }
      // real usage, measured from what was written
      const est0 = usageOf();
      const usage = maps.map((x, m) => {
        const w = W[x.b];
        const holeFree = w.holes.reduce((t, h) => t + (h.end - h.pc), 0), holeSize = w.holes.reduce((t, h) => t + (h.end - h.start), 0);
        const total = LIM - commonEnd + holeSize, free = LIM - w.pc + holeFree;
        return Object.assign({}, est0[m], { used: total - free, total, free });
      });
      // ---- the code, assembled with the real addresses, in every bank ----
      Object.assign(sym, {
        FONT, SPACEI: GIDX[' '], NGLYPH, STARTHOT: cart.base + startBank, HOTS: 0xFF00 | lo(cart.base), NPAGES: P.intro.length, START2: (P.start.room * 2) & 0xFF,
        STARTINV: P.start.inventory.reduce((acc, i) => acc | bit(i), 0),
      });
      const code = assemble(takEngineSource(srcOpts), BASE, takSyms(sym));
      if (code.bytes.length !== codeLen || code.labels.INPUT !== logicAt) throw new Error('engine size changed between passes');
      byBank.forEach((x, b) => {
        // a bank no map uses only needs the display code: its game-logic area holds text
        banks[b].set(x.used ? code.bytes : code.bytes.slice(0, logicAt - BASE), 0);
        banks[b].set([0x00, 0xF0, 0x00, 0xF0], 0xFFC); // reset and IRQ vectors -> $F000
        if (cart.scheme === 'EF') banks[b].set([0x45, 0x46, 0x45, 0x46], 0xFF8); // "EFEF": how emulators and flash carts recognise EF
      });
      return { ok: true, rom: measure ? null : rom, warns, usage: { maps: usage, mapA: usage[0], mapB: usage[1] }, fixes: { engine: 'tak', wide: true }, codeLen, font: FONT, labels: code.labels };
    }
  }

  // ---------- Playthrough analysis ----------
  // A model of the engine's rules, searched breadth-first over every reachable game state:
  // map, room, inventory, taken, revealed, used and event bytes.
  const DIRS = ['N', 'E', 'S', 'W'];
  const K = { MOVE: 0, LOOK: 4, TAKE: 5, GIVE: 6, USE: 7, TALK: 8 };
  function analyze(project, opts = {}) {
    const P = normalize(project);
    const cap = opts.maxStates || 250000;
    const endMask = bit(P.settings.endEvent);
    const legacy = isLegacyPortals(P); // only the original gateway code strands players
    const t0 = Date.now();
    // per-state storage
    const SM = new Uint8Array(cap), SR = new Uint8Array(cap), SI = new Uint16Array(cap), ST = new Uint16Array(cap),
      SS = new Uint16Array(cap), SU = new Uint16Array(cap), SE = new Uint16Array(cap), WIN = new Uint8Array(cap);
    const parent = new Int32Array(cap).fill(-1), pact = new Int32Array(cap), depth = new Int32Array(cap);
    const ids = new Map();
    let n = 0, truncated = false;
    const eFrom = [], eTo = [], eAct = [];
    const stranded = [];
    const key = (m, r, inv, tk, sn, us, ev) => ((m * 128 + r) * 65536 + inv) * 65536 + tk + ':' + ((sn * 65536 + us) * 65536 + ev);
    function add(m, r, inv, tk, sn, us, ev, win, from, a) {
      const k = key(m, r, inv, tk, sn, us, ev) + (win ? 'w' : '');
      let id = ids.get(k);
      if (id === undefined) {
        if (n >= cap) { truncated = true; return -1; }
        id = n++; ids.set(k, id);
        SM[id] = m; SR[id] = r; SI[id] = inv; ST[id] = tk; SS[id] = sn; SU[id] = us; SE[id] = ev; WIN[id] = win ? 1 : 0;
        parent[id] = from; pact[id] = a; depth[id] = from < 0 ? 0 : depth[from] + 1;
      }
      if (from >= 0) { eFrom.push(from); eTo.push(id); eAct.push(a); }
      return id;
    }
    const startInv = P.start.inventory.reduce((acc, i) => acc | bit(i), 0);
    add(0, P.start.room, startInv, 0, 0, 0, 0, !!(P.maps[0].cells[P.start.room] || {}).ending, -1, -1);
    for (let id = 0; id < n; id++) {
      if (WIN[id]) continue;
      const m = SM[id], r = SR[id], inv = SI[id], tk = ST[id], sn = SS[id], us = SU[id], ev = SE[id];
      const map = P.maps[m], c = map.cells[r];
      const won = e2 => !!(e2 & endMask);
      // moves
      const W = map.width;
      for (let d = 0; d < 4; d++) {
        const t = (r * 2 + [-2 * W, 2, 2 * W, -2][d]) & 0xFF, ti = t >> 1;
        const pt = portalAt(P, m, ti);
        let dm = m, di = ti;
        if (pt) { dm = pt.toMap; di = pt.toIdx; }
        else if (ti >= map.cells.length) continue; // off the map: validation reports it
        const dc = P.maps[dm].cells[di];
        if (!dc || dc.type !== 'room' || portalAt(P, dm, di) || (dc.door.on && !(ev & bit(dc.door.needEvent)))) {
          // turned away: the engine restores the room number, but in whichever bank is now active
          if (dm !== m && legacy) {
            const sc = P.maps[dm].cells[r];
            if (!sc || sc.type !== 'room' || portalAt(P, dm, r)) { stranded.push({ from: id, act: d, map: dm, idx: r }); continue; }
            add(dm, r, inv, tk, sn, us, ev, !!sc.ending, id, K.MOVE + d);
          }
          continue; // a wall or lock on the same map: nothing changes
        }
        add(dm, di, inv, tk, sn, us, ev, !!dc.ending, id, K.MOVE + d);
      }
      // LOOK (every verb is reached through LOOK, so its reveal happens first)
      let sn2 = sn;
      if (c.lookReveals && c.item != null && !(tk & bit(c.item))) sn2 |= bit(c.item);
      add(m, r, inv, tk, sn2, us, ev, false, id, K.LOOK);
      if (c.take.on && c.item != null) {
        const b = bit(c.item);
        if (!(tk & b) && (sn2 & b) && !(inv & b)) add(m, r, inv | b, tk | b, sn2, us, ev, false, id, K.TAKE);
      }
      if (c.give.on && c.give.item != null && (inv & bit(c.give.item))) {
        const e2 = ev | bit(c.sets);
        add(m, r, inv & ~bit(c.give.item) & 0xFFFF, tk, sn2 | bit(c.item), us, e2, won(e2), id, K.GIVE * 16 + c.give.item);
      }
      if (c.use.on && c.use.item != null && (inv & bit(c.use.item))) {
        const e2 = c.use.setsEvent ? ev | bit(c.sets) : ev;
        add(m, r, inv, tk, sn2, us | bit(c.use.item), e2, won(e2), id, K.USE * 16 + c.use.item);
      }
      if (c.talk.on && c.talk.needUsed != null && (us & bit(c.talk.needUsed))) {
        const e2 = ev | bit(c.sets);
        add(m, r, inv, tk, sn2, us, e2, won(e2), id, K.TALK);
      }
    }
    // which states can still reach a win (reverse search over the explored graph)
    const canWin = new Uint8Array(n);
    const rev = Array.from({ length: n }, () => []);
    for (let i = 0; i < eFrom.length; i++) rev[eTo[i]].push(eFrom[i]);
    const q = [];
    for (let i = 0; i < n; i++) if (WIN[i]) { canWin[i] = 1; q.push(i); }
    while (q.length) { const v = q.pop(); for (const u of rev[v]) if (!canWin[u]) { canWin[u] = 1; q.push(u); } }

    const stepOf = (from, a) => {
      const kind = a < 16 ? a : a >> 4;
      const st = { map: SM[from], idx: SR[from] };
      if (a < 4) st.action = DIRS[a];
      else if (a === K.LOOK) st.action = 'LOOK';
      else if (a === K.TAKE) st.action = 'TAKE';
      else if (a === K.TALK) st.action = 'TALK';
      else { st.action = (a >> 4) === K.GIVE ? 'GIVE' : 'USE'; st.item = a & 15; }
      return st;
    };
    const pathTo = id => { const out = []; while (parent[id] >= 0) { out.push(stepOf(parent[id], pact[id])); id = parent[id]; } return out.reverse(); };
    let best = -1;
    for (let i = 0; i < n; i++) if (WIN[i] && (best < 0 || depth[i] < depth[best])) best = i;
    // reachability summaries
    const seenRooms = P.maps.map(m => new Uint8Array(m.cells.length));
    let itemsHeld = 0, eventsSet = 0;
    for (let i = 0; i < n; i++) { seenRooms[SM[i]][SR[i]] = 1; itemsHeld |= SI[i]; eventsSet |= SE[i]; }
    const unreachable = [];
    P.maps.forEach((m, mi) => m.cells.forEach((c, i) => { if (c.type === 'room' && !portalAt(P, mi, i) && !seenRooms[mi][i]) unreachable.push({ map: mi, idx: i }); }));
    const usedItems = new Set(), usedEvents = new Set();
    P.maps.forEach(m => m.cells.forEach(c => {
      if (c.type !== 'room') return;
      if (c.take.on && c.item != null) usedItems.add(c.item);
      if (c.sets != null && (c.give.on || (c.talk.on && c.talk.needUsed != null) || (c.use.on && c.use.setsEvent))) usedEvents.add(c.sets);
    }));
    P.start.inventory.forEach(i => usedItems.add(i));
    const neverItems = [...usedItems].filter(i => !(itemsHeld & bit(i))).sort();
    const neverEvents = [...usedEvents].filter(e => !(eventsSet & bit(e))).sort();
    // points of no return: a move from a winnable state into one that can no longer win
    const noReturn = [];
    if (best >= 0) {
      const seenKey = new Map();
      for (let i = 0; i < eFrom.length; i++) {
        const u = eFrom[i], v = eTo[i];
        if (!canWin[u] || canWin[v]) continue;
        const st = stepOf(u, eAct[i]);
        const k2 = `${st.map}:${st.idx}:${st.action}:${st.item}`;
        const prev = seenKey.get(k2);
        if (!prev || depth[u] < prev.d) seenKey.set(k2, { d: depth[u], u, st });
      }
      for (const { u, st } of [...seenKey.values()].sort((a, b) => a.d - b.d).slice(0, 8)) noReturn.push(Object.assign(st, { path: pathTo(u) }));
    }
    return {
      endingDefined: endMask !== 0 || P.maps.some(m => m.cells.some(c => c.type === 'room' && c.ending)),
      winnable: best >= 0, solution: best >= 0 ? pathTo(best) : null,
      states: n, truncated, ms: Date.now() - t0,
      unreachable, neverItems, neverEvents, noReturn,
      stranded: stranded.slice(0, 5).map(x => ({ map: SM[x.from], idx: SR[x.from], action: DIRS[x.act], landsOn: { map: x.map, idx: x.idx }, path: pathTo(x.from) })),
    };
  }

  // Turn a walkthrough into controller input: intro pages, then each step as the engine wants it.
  function stepSegs(P, inv, st) {
    const out = [];
    const verb = (k, item) => {
      out.push(...actSegs('fire'));                      // LOOK opens the action menu
      for (let i = 0; i < k; i++) out.push(...actSegs('right'));
      out.push(...actSegs('fire'));
      if (item != null) {                                // pick the item from the carried list
        let pos = 0; for (let b = 0; b < item; b++) if (inv & bit(b)) pos++;
        for (let i = 0; i < pos; i++) out.push(...actSegs('right'));
        out.push(...actSegs('fire'));
      }
    };
    if (DIRS.includes(st.action)) out.push(...actSegs(st.action));
    else if (st.action === 'LOOK') { out.push(...actSegs('fire'), ...actSegs('fire')); } // LOOK, then GO back
    else if (st.action === 'TAKE') verb(1);
    else if (st.action === 'GIVE') verb(2, st.item);
    else if (st.action === 'USE') verb(3, st.item);
    else if (st.action === 'TALK') verb(4);
    return out;
  }
  function introSegs(P) { const out = []; for (let i = 0; i < P.intro.length; i++) out.push(...actSegs('fire')); return out; }
  // Replay a walkthrough on the built ROM and check it reaches THE END.
  function verifySolution(rom, project, steps) {
    const P = normalize(project);
    const e = new Emu(rom);
    // which engine built it: Dark Mage's text kernel sits at $F43B in every bank
    const dm = [0xA2, 0x04, 0x85, 0x02].every((v, i) => rom[0x43B + i] === v);
    if (!dm) { e.layout = 'tak'; e.wide = true; } else e.wide = fixesNeeded(P).wide;
    for (let i = 0; i < 3; i++) e.runFrame();
    runSegs(e, introSegs(P));
    for (let i = 0; i < steps.length; i++) {
      runSegs(e, stepSegs(P, e.state().inv, steps[i]));
    }
    for (let i = 0; i < 4; i++) e.runFrame();
    const ended = e.menuPtr() !== 0 && e.menuText() === normText(P.system.theEnd).split('\n')[0];
    return { ok: ended, finalText: e.screenText(), menu: e.menuText() };
  }

  function build(P, engineRom, opts = {}) {
    normalize(P);
    return P.engine === 'tak' ? buildTak(P, opts) : buildRom(P, engineRom, opts);
  }
  root.TAK = { build, wideNeeded, CARTS, LETTERS, bankOrder, mapOfBank, setCart, portalAt, isLegacyPortals, normalize, fixesNeeded, fontMode, XCHAR, XFONT, XDECODE, DEFAULT_COLORS, newProject, room, wall, CHAR, DECODE, LINE_W, MAX_LINES, SUBST, EXTRA_GLYPHS, normText, badChars, encodePage, parseRom, buildRom, validate, neighbors, isEngine, readText, Emu, act, actSegs, runSegs, stepSegs, introSegs, analyze, verifySolution, assemble, buildTak, takEngineSource, TAK_GEO, BASE, takCompress, takLines, NGLYPH, PARSE_MAX };
})(typeof window !== 'undefined' ? window : globalThis);
if (typeof module !== 'undefined') module.exports = globalThis.TAK;
