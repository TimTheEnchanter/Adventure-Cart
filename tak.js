// TAK — Atari 2600 Text Adventure Kit
// Parser / rebuilder for the Dark Mage (Greg Troutman, 1997) 8K F8 text-adventure engine,
// plus a small 6502 + RIOT emulator for play-testing the real ROM code.
(function (root) {
  'use strict';

  // ---------- Character set (glyph offsets into page $F5) ----------
  const CHAR = {
    A: 0x60, B: 0x2F, C: 0x3A, D: 0x34, E: 0x40, F: 0x48, G: 0x4E, H: 0x5C, I: 0x93, J: 0x0A,
    K: 0x66, L: 0x45, M: 0x70, N: 0x75, O: 0x54, P: 0x7B, Q: 0xF2, R: 0x2A, S: 0x81, T: 0x12,
    U: 0x59, V: 0x6C, W: 0x87, X: 0x8D, Y: 0x95, Z: 0x9B,
    ' ': 0x1E, '.': 0x1C, ',': 0x1B, "'": 0x18, '"': 0x18, '!': 0x10, '?': 0x05, ':': 0x24, '-': 0xF8,
  };
  const DECODE = {};
  for (const [k, v] of Object.entries(CHAR)) if (k !== '"') DECODE[v] = k;
  // extra glyphs this kit adds in the unused tail of the font page ($F5F2-$F5FD)
  const EXTRA_GLYPHS = [0x76, 0xCC, 0xD6, 0xC6, 0xC6, 0x7C, /* Q (bottom row first) */
                        0x00, 0x00, 0x00, 0x7C, 0x00, 0x00  /* - */];
  const LINE_W = 12, MAX_LINES = 10;
  const SUBST = { '0': 'O', '1': 'I', '5': 'S', '8': 'B', '(': '-', ')': '-', ';': ',', '`': "'" };

  function normText(s) {
    return String(s || '').toUpperCase().replace(/\r/g, '');
  }
  function badChars(s) {
    const bad = new Set();
    for (const ch of normText(s)) if (ch !== '\n' && !(ch in CHAR)) bad.add(ch);
    return [...bad];
  }
  // encode a page of text (lines joined with \n) -> bytes (each line + $FF, then $FE)
  function encodePage(s, menuWord) {
    const lines = normText(s).split('\n');
    const out = [];
    for (const line of lines) {
      for (const ch of line.slice(0, LINE_W)) out.push(CHAR[ch] !== undefined ? CHAR[ch] : (CHAR[SUBST[ch]] !== undefined ? CHAR[SUBST[ch]] : CHAR[' ']));
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
  const DATA_START = 0xF5F2, LIMIT = 0xFFF8; // never place data on bank-switch hotspots
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
    }
    return null;
  }

  function readText(bk, a, menuWord) {
    let s = '', i = a - BASE, n = 0;
    while (i >= 0 && i < 4096 && n++ < 400) {
      const v = bk[i++];
      if (v === 0xFE) break;
      if (v === 0xFF) { if (menuWord) break; s += '\n'; continue; }
      s += DECODE[v] !== undefined ? DECODE[v] : ' ';
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
          talk: { on: !!(f & 0x08), needUsed: maskToIdx(b[5]), ok: (f & 0x08) ? readText(bk, ptr(5)) : '', no: (f & 0x08) ? readText(bk, ptr(7)) : '' },
          sets: maskToIdx(b[6]),
          door: { on: !!(f & 0x02), needEvent: maskToIdx(b[7]), text: (f & 0x02) ? readText(bk, ptr(6)) : '' },
        };
        c.name = c.desc.replace(/\n/g, ' ').replace(/^YOU ARE (IN|ON|AT|STANDING ON)( A| THE)?\s*/i, '').replace(/\s+/g, ' ').trim().slice(0, 28) || 'Room ' + i;
        cells.push(c);
      }
      maps.push({ name, rows: n / width, cells });
    }
    return {
      kit: 'tak', version: 1, title: 'Untitled adventure',
      settings: { width, portalA, portalB },
      start: { room: rd(A, IMM.startRoom) >> 1, inventory: [0, 1, 2, 3, 4, 5, 6, 7].filter(i => rd(A, IMM.startInv) & (1 << i)) },
      items, events: ['Event 1', 'Event 2', 'Event 3', 'Event 4', 'Event 5', 'Event 6', 'Event 7', 'Event 8'],
      system: sys, intro, maps,
    };
  }

  // ---------- Exits / validation helpers ----------
  function neighbors(project, mapIdx, idx) {
    const W = project.settings.width, a = idx * 2;
    const res = {};
    for (const [dir, d] of [['N', -2 * W], ['E', 2], ['S', 2 * W], ['W', -2]]) {
      const t = (a + d) & 0xFF;
      let map = mapIdx;
      if ((t >> 1) === project.settings.portalA && (t & 1) === 0) map = 1;          // entering portalA index => Map B
      else if ((t >> 1) === project.settings.portalB && (t & 1) === 0) map = 0;     // entering portalB index => Map A
      // engine checks portalA (CMP #$2C) first, then portalB
      const ti = t >> 1;
      const cells = project.maps[map].cells;
      const wrap = (dir === 'E' && (idx % W) === W - 1) || (dir === 'W' && (idx % W) === 0);
      res[dir] = { map, idx: ti, valid: ti < cells.length && (t & 1) === 0, wrap, cell: cells[ti] };
    }
    return res;
  }

  function validate(project) {
    const errs = [], warns = [];
    const P = project, W = P.settings.width;
    if (!(W >= 2 && W <= 21)) errs.push('Map width must be between 2 and 21');
    P.maps.forEach((m, mi) => {
      if (m.cells.length !== m.rows * W) errs.push(`${m.name}: cell count mismatch`);
      if (m.cells.length * 2 > 256) errs.push(`${m.name}: too many cells (max 128)`);
    });
    const pA = P.settings.portalA, pB = P.settings.portalB;
    if (pA === pB) errs.push('The two portal cells must be different grid positions');
    if (pA >= P.maps[1].cells.length) errs.push('Portal into Map B points outside Map B');
    if (pB >= P.maps[0].cells.length) errs.push('Portal into Map A points outside Map A');
    if (P.maps[1].cells[pA] && P.maps[1].cells[pA].type !== 'room') warns.push('The Map B cell that the portal leads to is a wall');
    if (P.maps[0].cells[pB] && P.maps[0].cells[pB].type !== 'room') warns.push('The Map A cell that the portal leads to is a wall');
    const sr = P.start.room;
    if (!P.maps[0].cells[sr] || P.maps[0].cells[sr].type !== 'room') errs.push('Start room must be a room in Map A');
    if (sr === pA || sr === pB) errs.push('Start room cannot be a portal cell');
    if (P.intro.length < 2 || P.intro.length > 6) errs.push('Intro must have 2 to 6 pages');
    // The engine crashes if GIVE / USE / INVENTORY is opened with nothing carried (Dark Mage's
    // hammer exists for exactly this reason), so one starting item must never be given away.
    const given = new Set();
    P.maps.forEach(m => m.cells.forEach(c => { if (c.type === 'room' && c.give.on && c.give.item != null) given.add(c.give.item); }));
    if (!P.start.inventory.some(i => !given.has(i)))
      errs.push('The player must always carry something: start with at least one item that no GIVE puzzle takes (like Dark Mage\'s hammer). An empty inventory crashes the engine.');
    P.intro.forEach((t, i) => checkPage(t, `Intro page ${i + 1}`, errs, warns));
    P.items.forEach((t, i) => checkPage(t, `Item ${i + 1} name`, errs, warns, { menuWord: true }));
    for (const k of [...MOVE_WORDS, ...ACT_WORDS, 'more', 'start']) checkPage(P.system[k], `Menu word "${k}"`, errs, warns, { menuWord: true });
    for (const k of SYS_MSGS) checkPage(P.system[k], `System message "${k}"`, errs, warns);
    checkPage(P.system.bootB, 'Bank-0 power-on text', errs, warns);
    P.maps.forEach((m, mi) => m.cells.forEach((c, i) => {
      const portalHere = (mi === 0 && i === pA) || (mi === 1 && i === pB);
      if (portalHere) return; // never read by the engine
      const lbl = `${m.name} r${Math.floor(i / W) + 1}c${(i % W) + 1}`;
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
  class Writer {
    constructor(bk, start, limit) { this.bk = bk; this.pc = start; this.strStart = start; this.cache = new Map(); this.limit = limit || LIMIT; }
    put(bytes) { const a = this.pc; if (a + bytes.length > this.limit) throw new Error('OUT_OF_SPACE'); for (const b of bytes) this.bk[this.pc++ - BASE] = b; return a; }
    // place a string, reusing any identical byte run already in the string area
    str(bytes, searchFrom) {
      const key = bytes.join(',');
      if (this.cache.has(key)) return this.cache.get(key);
      const from = searchFrom - BASE, to = this.pc - BASE;
      outer: for (let i = from; i + bytes.length <= to; i++) {
        for (let j = 0; j < bytes.length; j++) if (this.bk[i + j] !== bytes[j]) continue outer;
        this.cache.set(key, i + BASE); return i + BASE;
      }
      const a = this.put(bytes); this.cache.set(key, a); return a;
    }
  }

  function bit(i) { return i == null ? 0 : (1 << i); }

  // opts.measure: only measure space (no engine needed, ignores validation errors)
  function buildRom(project, engine, opts = {}) {
    const measure = !!opts.measure;
    if (!measure) { const e = isEngine(engine); if (e) throw new Error(e); }
    const P = project, W = P.settings.width;
    const { errs, warns } = measure ? { errs: [], warns: [] } : validate(P);
    if (errs.length) return { ok: false, errs, warns };
    const lim = measure ? 0x30000 : LIMIT;
    const rom = measure ? new Uint8Array(0x40000) : new Uint8Array(engine);
    const banks = measure ? [rom.subarray(0, 0x20000), rom.subarray(0x20000, 0x40000)] : [rom.subarray(0, 4096), rom.subarray(4096, 8192)];
    // wipe data area of both banks
    for (const bk of banks) for (let a = DATA_START; a < LIMIT; a++) bk[a - BASE] = 0xFF;

    // ---- common block (identical in both banks, same addresses) ----
    const cb = banks[1];
    // the extra Q / - glyphs take 12 bytes of the font page; only reserve them if used
    const allText = JSON.stringify([P.intro, P.items, P.system, P.maps]).toUpperCase();
    const usesExtra = /[Q\-()]/.test(allText);
    let cstart = DATA_START;
    if (usesExtra) { for (let i = 0; i < EXTRA_GLYPHS.length; i++) cb[0xF5F2 + i - BASE] = EXTRA_GLYPHS[i]; cstart = 0xF5FE; }
    const cw = new Writer(cb, cstart, lim);
    const commonStr = [];
    const words = {};
    // longest strings first so shorter ones can reuse their tails
    const pending = [];
    for (const k of [...MOVE_WORDS, ...ACT_WORDS, 'more', 'start']) pending.push(['w:' + k, encodePage(P.system[k], true)]);
    for (const k of SYS_MSGS) pending.push(['m:' + k, encodePage(P.system[k])]);
    P.items.forEach((t, i) => pending.push(['i:' + i, encodePage(t, true)]));
    pending.sort((a, b) => b[1].length - a[1].length);
    const caddr = {};
    try {
      for (const [k, bytes] of pending) caddr[k] = cw.str(bytes, cstart);
      // item pointer table
      caddr.itemTable = cw.put(P.items.flatMap((_, i) => [caddr['i:' + i] & 0xFF, caddr['i:' + i] >> 8]));
    } catch (x) { if (x.message === 'OUT_OF_SPACE') return { ok: false, errs: ['Out of space in the shared text block'], warns }; throw x; }
    const commonEnd = cw.pc;
    for (let a = 0xF5F2; a < commonEnd; a++) banks[0][a - BASE] = cb[a - BASE];

    // ---- code patches common to both banks ----
    for (const bk of banks) {
      setSite(bk, SITE.firstMenuWord, caddr['w:look']);
      setSite(bk, SITE.introMenuWord, caddr['w:more']);
      for (const k of SYS_MSGS) setSite(bk, SITE[k], caddr['m:' + k]);
      setSite(bk, SITE.itemTable, caddr.itemTable);
      MOVE_WORDS.forEach((k, i) => { bk[TBL.moveMenu + 2 * i - BASE] = caddr['w:' + k] & 0xFF; bk[TBL.moveMenu + 2 * i + 1 - BASE] = caddr['w:' + k] >> 8; });
      ACT_WORDS.forEach((k, i) => { bk[TBL.actMenu + 2 * i - BASE] = caddr['w:' + k] & 0xFF; bk[TBL.actMenu + 2 * i + 1 - BASE] = caddr['w:' + k] >> 8; });
      bk[TBL.introMenu - BASE] = caddr['w:more'] & 0xFF; bk[TBL.introMenu + 1 - BASE] = caddr['w:more'] >> 8;
      bk[TBL.introMenu + 2 - BASE] = caddr['w:start'] & 0xFF; bk[TBL.introMenu + 3 - BASE] = caddr['w:start'] >> 8;
      bk[IMM.portalB - BASE] = (P.settings.portalA * 2) & 0xFF; // CMP #pA -> switch to bank 0 (Map B)
      bk[IMM.portalA - BASE] = (P.settings.portalB * 2) & 0xFF; // CMP #pB -> switch to bank 1 (Map A)
      bk[IMM.widthN - BASE] = 2 * W; bk[IMM.widthS - BASE] = 2 * W;
      bk[IMM.startRoom - BASE] = P.start.room * 2;
      bk[IMM.startInv - BASE] = P.start.inventory.reduce((m, i) => m | bit(i), 0);
      bk[IMM.introPages - BASE] = P.intro.length - 1;
    }
    // bank 0: both intro-menu entries reboot into bank 1 (original quirk fix)
    for (const off of [0, 2]) { banks[0][TBL.introHandlers + off - BASE] = 0x5D; banks[0][TBL.introHandlers + off + 1 - BASE] = 0xF0; }

    // ---- per-bank world data ----
    const usage = [];
    const mapForBank = [P.maps[1], P.maps[0]]; // bank0 = Map B, bank1 = Map A
    for (let b = 0; b < 2; b++) {
      const bk = banks[b], map = mapForBank[b];
      const w = new Writer(bk, commonEnd, lim);
      w.cache = new Map(cw.cache); // shared strings are present in both banks
      try {
        const table = w.put(new Array(map.cells.length * 2).fill(0));
        setSite(bk, SITE.roomTable, table);
        const strFrom = cstart;
        // gather all strings for this bank, place longest first
        const S = [];
        const want = (t) => { const bytes = encodePage(t); S.push(bytes); return bytes.join(','); };
        const deadIdx = b === 0 ? P.settings.portalB : P.settings.portalA;
        const recs = map.cells.map((c, i) => {
          if (i === deadIdx) return null;
          if (c.type === 'wall') return { wall: want(c.text) };
          const r = { c, k: [want(c.desc), want(c.look)] };
          r.k[2] = c.take.on ? want(c.take.text) : null;
          r.k[3] = c.use.on ? want(c.use.text) : null;
          r.k[4] = c.give.on ? want(c.give.text) : null;
          r.k[5] = c.talk.on ? want(c.talk.ok) : null;
          r.k[6] = c.door.on ? want(c.door.text) : null;
          r.k[7] = c.talk.on ? want(c.talk.no) : null;
          return r;
        });
        let introKeys = [];
        if (b === 1) introKeys = P.intro.map(want);
        else want(P.system.bootB);
        S.sort((x, y) => y.length - x.length);
        const addr = {};
        for (const bytes of S) addr[bytes.join(',')] = w.str(bytes, strFrom);
        // records
        const recCache = new Map();
        const recAddr = recs.map(r => {
          if (!r) return null;
          let bytes;
          if (r.wall) { const a = addr[r.wall]; bytes = [0, a & 0xFF, a >> 8]; }
          else {
            const c = r.c;
            let f = 0;
            if (c.door.on) f |= 0x02;
            if (c.talk.on) f |= 0x08;
            if (c.use.on) f |= 0x10;
            if (c.give.on) f |= 0x20;
            if (c.take.on) f |= 0x40;
            const reveal = c.lookReveals && c.item != null;
            if (!reveal) f |= 0x80;
            bytes = [f, reveal ? bit(c.item) : 0, bit(c.item), c.use.on ? bit(c.use.item) : 0, c.give.on ? bit(c.give.item) : 0,
              c.talk.on ? bit(c.talk.needUsed) : 0, bit(c.sets), c.door.on ? bit(c.door.needEvent) : 0];
            let last = 1; r.k.forEach((k, i) => { if (k) last = i; });
            for (let i = 0; i <= last; i++) { const a = r.k[i] ? addr[r.k[i]] : 0xFFFF; bytes.push(a & 0xFF, a >> 8); }
          }
          const key = bytes.join(',');
          if (!recCache.has(key)) recCache.set(key, w.put(bytes));
          return recCache.get(key);
        });
        // dead (portal) slot: point at any wall/record so the table is well-formed
        const any = recAddr.find(a => a != null);
        recAddr.forEach((a, i) => { const v = a == null ? any : a; bk[table + 2 * i - BASE] = v & 0xFF; bk[table + 2 * i + 1 - BASE] = v >> 8; });
        if (b === 1) {
          const ptrs = introKeys.map(k => addr[k]);
          setSite(bk, SITE.bootText, ptrs[0]);
          // pages 2..n come from table[n-2] down to table[0]
          const n = ptrs.length - 1;
          for (let k = 0; k < 5; k++) {
            const v = k < n ? ptrs[n - k] : ptrs[ptrs.length - 1];
            bk[TBL.introPages + 2 * k - BASE] = v & 0xFF; bk[TBL.introPages + 2 * k + 1 - BASE] = v >> 8;
          }
          const sc = P.maps[0].cells[P.start.room];
          setSite(bk, SITE.startText, addr[encodePage(sc.desc).join(',')]);
        } else {
          const a = addr[encodePage(P.system.bootB).join(',')];
          setSite(bk, SITE.bootText, a); setSite(bk, SITE.startText, a);
          for (let k = 0; k < 5; k++) { bk[TBL.introPages + 2 * k - BASE] = a & 0xFF; bk[TBL.introPages + 2 * k + 1 - BASE] = a >> 8; }
        }
      } catch (x) {
        if (x.message === 'OUT_OF_SPACE') return { ok: false, errs: [`${map.name} does not fit in its 4K bank — shorten some text or reuse identical messages`], warns };
        throw x;
      }
      usage[b] = { used: w.pc - DATA_START, total: LIMIT - DATA_START, free: LIMIT - w.pc };
    }
    return { ok: true, rom: measure ? null : rom, warns, usage: { mapA: usage[1], mapB: usage[0] }, extraGlyphs: usesExtra };
  }

  // ---------- Space estimate without building (fast) ----------


  // ---------- New blank project ----------
  function room(name, desc, look) {
    return { type: 'room', name, desc, look, lookReveals: false, item: null, take: { on: false, text: '' }, use: { on: false, item: null, text: '' },
      give: { on: false, item: null, text: '' }, talk: { on: false, needUsed: null, ok: '', no: '' }, sets: null, door: { on: false, needEvent: null, text: '' } };
  }
  function wall(text) { return { type: 'wall', text }; }
  function newProject(opts = {}) {
    const W = opts.width || 6, rA = opts.rowsA || 5, rB = opts.rowsB || 5;
    const mk = (rows) => Array.from({ length: rows * W }, () => wall('YOU CAN\'T GO\nTHAT WAY.'));
    const A = mk(rA), B = mk(rB);
    const pA = (opts.portalRow != null ? opts.portalRow : 2) * W + Math.floor(W / 2);   // cell in Map A that leads into Map B
    const pB = pA - 1;                                                                   // cell in Map B that leads into Map A
    A[W + 1] = room('Start', 'YOU ARE IN A\nSMALL ROOM.', 'IT IS VERY\nQUIET HERE.');
    A[pB] = room('Portal path (Map A side)', 'A NARROW\nPASSAGE\nLEADS EAST.', 'YOU FEEL A\nCOLD DRAFT.');
    B[pA] = room('Portal path (Map B side)', 'YOU HAVE\nCROSSED INTO\nA NEW LAND.', 'THE PASSAGE\nWEST LEADS\nBACK HOME.');
    return {
      kit: 'tak', version: 1, title: opts.title || 'My adventure',
      settings: { width: W, portalA: pA, portalB: pB },
      start: { room: W + 1, inventory: [0] },
      items: ['A LAMP', 'A KEY', 'A COIN', 'A ROPE', 'A SCROLL', 'A SWORD', 'AN APPLE', 'A GEM'],
      events: ['Event 1', 'Event 2', 'Event 3', 'Event 4', 'Event 5', 'Event 6', 'Event 7', 'Event 8'],
      system: { look: 'LOOK', north: 'NORTH', east: 'EAST', south: 'SOUTH', west: 'WEST', go: 'GO', take: 'TAKE', give: 'GIVE', use: 'USE', talk: 'TALK', inventory: 'INVENTORY',
        more: 'MORE...', start: 'START', nothingSpecial: 'YOU SEE\nNOTHING\nSPECIAL', nothingToTake: 'YOU SEE\nNOTHING\nWORTH\nTAKING', talkDefault: 'NO ONE\nANSWERS.',
        selectGive: 'SELECT ITEM\nTO GIVE:', cantGive: "CAN'T GIVE\nTHAT", selectUse: 'SELECT ITEM\nTO USE:', cantUse: "CAN'T USE\nTHAT", carrying: 'YOU ARE\nCARRYING:', bootB: '' },
      intro: ['\n\n  MY GAME\n\n\n    BY\n   ME', 'YOUR QUEST\nBEGINS NOW.'],
      maps: [{ name: 'Map A', rows: rA, cells: A }, { name: 'Map B', rows: rB, cells: B }],
    };
  }

  // ---------- 6502 + F8 + RIOT emulator (enough for this engine) ----------
  class Emu {
    constructor(rom) {
      this.rom = rom; this.ram = new Uint8Array(128); this.bank = 1;
      this.a = 0; this.x = 0; this.y = 0; this.sp = 0xFD; this.p = 0x24; this.cyc = 0;
      this.swcha = 0xFF; this.inpt4 = 0x80; this.swchb = 0x0B;
      this.tStart = 0; this.tVal = 0; this.tShift = 1024; this.vsync = 0; this.frames = 0;
      this.pc = this.r16(0xFFFC);
    }
    access(a) { a &= 0x1FFF; if (a === 0x1FF8) this.bank = 0; else if (a === 0x1FF9) this.bank = 1; return a; }
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
    screenText() { return readText(this.bankBytes(), this.textPtr()); }
    menuText() { return readText(this.bankBytes(), this.menuPtr(), true); }
    state() { const r = this.ram; return { room: r[0x22] >> 1, bank: this.bank, inv: r[0x27], taken: r[0x26], seen: r[0x28], used: r[0x29], events: r[0x2C] }; }
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
  function act(emu, what) {
    const idle = n => { for (let i = 0; i < n; i++) emu.runFrame(); };
    if (what === 'reset') { emu.swchb = 0x0A; idle(4); emu.swchb = 0x0B; idle(12); return; }
    if (what === 'left' || what === 'right') { emu.swcha = JOY[what]; idle(8); emu.swcha = 0xFF; idle(1); return; }
    if (JOY[what]) { emu.swcha = JOY[what]; idle(9); }
    emu.inpt4 = 0x00; idle(3); emu.inpt4 = 0x80; emu.swcha = 0xFF; idle(9);
  }
  root.TAK = { newProject, room, wall, CHAR, DECODE, LINE_W, MAX_LINES, SUBST, EXTRA_GLYPHS, normText, badChars, encodePage, parseRom, buildRom, validate, neighbors, isEngine, readText, Emu, act, BASE };
})(typeof window !== 'undefined' ? window : globalThis);
if (typeof module !== 'undefined') module.exports = globalThis.TAK;
