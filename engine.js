/* The Happy Hills Homicide 2: Out For Blood - HTML5 runtime
   Runs the original game (GameMaker Studio 1.4, bytecode 15) from game.js + tex/ + snd/ in the browser. */
(function () {
'use strict';
const G = window.GAME, D2R = Math.PI / 180;
const canvas = document.getElementById('c'), ctx = canvas.getContext('2d');
canvas.width = G.w; canvas.height = G.h; ctx.imageSmoothingEnabled = false;
let saveDepth = 0;                                           // balanced save/restore so an error can never leave a clip behind
{ const _s = ctx.save.bind(ctx), _r = ctx.restore.bind(ctx);
  ctx.save = () => { saveDepth++; _s(); }; ctx.restore = () => { if (saveDepth > 0) { saveDepth--; _r(); } }; }
const noop = () => {};

/* ================================================================== assets */
const tex = [];
function loadTextures(cb) {
  let left = G.ntex;
  for (let k = 0; k < G.ntex; k++) {
    const im = new Image();
    im.onload = im.onerror = () => { if (--left === 0) cb(); };
    im.src = 'tex/tex' + k + '.png'; tex[k] = im;
  }
}
const snds = G.snd.map(s => { const a = new Audio(); a.preload = s[3] && s[3] < 400000 ? 'auto' : 'metadata'; a.src = s[1]; return a; });
const clones = G.snd.map(() => []);
const live = a => !a.paused && !a.ended;
function playSnd(i, loop) {
  const base = snds[i]; if (!base) return;
  const vol = Math.max(0, Math.min(1, G.snd[i][2] == null ? 1 : G.snd[i][2]));
  try {
    if (loop) { base.loop = true; base.volume = vol; if (!live(base)) base.play().catch(noop); return; }
    let a = base;
    if (live(base)) { a = base.cloneNode(); clones[i].push(a); a.onended = () => { clones[i] = clones[i].filter(z => z !== a); }; }
    a.loop = false; a.volume = vol;
    try { a.currentTime = 0; } catch (e) { }
    a.play().catch(noop);
  } catch (e) { }
}
const sndPlaying = i => !!snds[i] && (live(snds[i]) || clones[i].some(live));
function stopSnd(i) {
  const b = snds[i]; if (!b) return;
  try { b.pause(); b.currentTime = 0; } catch (e) { }
  for (const a of clones[i]) { try { a.pause(); } catch (e) { } }
  clones[i] = [];
}
const stopAllSnd = () => snds.forEach((_, i) => stopSnd(i));

/* FIX: looping music / ambience / machine sounds are kept alive by a controller object ("if not playing, play").
   Nothing ever stopped them when that object vanished without a Destroy event (room change, loading a save), so they kept
   playing over the next music. Work out the controllers from the game data and stop any such sound whose controllers are all gone. */
const loopOwners = new Map();
{ const other = new Set();
  G.objs.forEach((o, oi) => { for (const t in o[8]) for (const sb in o[8][t]) for (const ci of o[8][t][sb]) { const c = G.code[ci]; if (!c) continue;
    const guard = new Set();
    c.forEach((op, pc) => { if (op[0] === 'c' && op[1] === 'action_if_sound' && c[pc - 2] && c[pc - 2][0] === 'k') guard.add(c[pc - 2][1]); });
    c.forEach((op, pc) => { if (op[0] === 'c' && op[1] === 'action_sound' && c[pc - 2] && c[pc - 2][0] === 'k') { const sn = c[pc - 2][1];
      if (+t === 3 && guard.has(sn)) { if (!loopOwners.has(sn)) loopOwners.set(sn, new Set()); loopOwners.get(sn).add(oi); } else other.add(sn); } }); } });
  for (const sn of other) loopOwners.delete(sn); }
function sweepSounds() {
  for (const [sn, owners] of loopOwners) { if (!sndPlaying(sn)) continue;
    let alive = false; for (const o of owners) if (countOf(o)) { alive = true; break; }
    if (!alive) stopSnd(sn); }
}

/* FIX: pre-load the sounds heard at the very start (tape going in, title sting, main menu) so they play on time */
const EARLY_SOUNDS = ['snd_vhs', 'snd_tape', 'snd_static', 'msc_copperbolt', 'snd_item_ui', 'snd_staticlow', 'msc_menu', 'snd_dialogue']
  .map(n => G.snd.findIndex(s => s[0] === n)).filter(i => i >= 0);
EARLY_SOUNDS.forEach(i => { try { snds[i].preload = 'auto'; snds[i].load(); } catch (e) { } });
function earlySoundsReady(cb) {
  let done = false; const fin = () => { if (!done) { done = true; cb(); } };
  const t0 = Date.now(), tick = () => { if (EARLY_SOUNDS.every(i => snds[i].readyState >= 3) || Date.now() - t0 > 3000) fin(); else setTimeout(tick, 40); };
  tick();
}

/* ================================================================== state */
let insts = [], room = null, roomIdx = -1, nextRoom = -1, nextId = 1000000;
let rel = 0, dcol = 16777215, dfont = 0, dalign = 0;          // 'relative' flag + drawing state
let gameOver = false, frame = 0, errCount = 0;
const keys = {}, pressed = {}, released = {};
const V = { view_visible: [], view_xview: [], view_yview: [], view_wview: [], view_hview: [], view_object: [], view_hspeed: [], view_vspeed: [], view_angle: [] };
const GL = { room_width: 0, room_height: 0, room_speed: 30, score: 0, lives: -1, health: 100 };
const GLV = {};                                               // 'global.' variables
const bgScroll = [], roomStore = {}, memSaves = {};
let pendingSave = null, pendingLoad = null, emitterId = 100;
let curView = { x: 0, y: 0, w: G.w, h: G.h };

const snap = v => (Math.abs(v) < 1e-9 ? 0 : v);                // kills floating point noise (sin(pi) etc.)
class Inst {
  constructor(obj, x, y, id) {
    const o = G.objs[obj];
    this.obj = obj; this.id = id; this.x = x; this.y = y; this.xstart = x; this.ystart = y; this.xprevious = x; this.yprevious = y;
    this.sprite_index = o[1]; this.image_index = 0; this.image_speed = 1; this.image_alpha = 1; this.image_blend = 16777215;
    this.image_xscale = 1; this.image_yscale = 1; this.image_angle = 0; this.image_single = -1;
    this.depth = o[4]; this.visible = !!o[2]; this.solid = !!o[3]; this.persistent = !!o[5]; this.mask_index = o[7];
    this.alarm = new Array(12).fill(-1);
    this._hs = 0; this._vs = 0; this._dir = 0; this.gravity = 0; this.gravity_direction = 270; this.friction = 0; this.dead = false;
  }
  get sprite_width() { const q = G.spr[this.sprite_index]; return q ? q[1] * this.image_xscale : 0; }
  get sprite_height() { const q = G.spr[this.sprite_index]; return q ? q[2] * this.image_yscale : 0; }
  get hspeed() { return this._hs; }
  get vspeed() { return this._vs; }
  set hspeed(v) { this._hs = v; if (this._hs || this._vs) this._dir = this._angle(); }
  set vspeed(v) { this._vs = v; if (this._hs || this._vs) this._dir = this._angle(); }
  _angle() { const a = Math.atan2(-this._vs, this._hs) / D2R; return ((Math.round(a * 1e6) / 1e6) % 360 + 360) % 360; }
  get speed() { return snap(Math.hypot(this._hs, this._vs)); }
  set speed(s) { const d = this._dir * D2R; this._hs = snap(s * Math.cos(d)); this._vs = snap(-s * Math.sin(d)); }
  get direction() { return this._dir; }
  set direction(d) { d = ((d % 360) + 360) % 360; const s = Math.hypot(this._hs, this._vs); this._dir = d; this._hs = snap(s * Math.cos(d * D2R)); this._vs = snap(-s * Math.sin(d * D2R)); }
}

/* ================================================================== objects, events, parents */
const anc = G.objs.map((_, o) => { const s = new Set(); let c = o; for (let n = 0; c >= 0 && n < 60; n++) { s.add(c); c = G.objs[c][6]; } return s; });
const isA = (i, o) => anc[i.obj].has(o);
const evCache = new Map();
function evMap(obj, type) {                                    // events including the ones inherited from parent objects
  const key = obj * 16 + type; let m = evCache.get(key);
  if (!m) { m = new Map(); let c = obj; for (let n = 0; c >= 0 && n < 60; n++) { const e = G.objs[c][8][type]; if (e) for (const sub in e) if (!m.has(+sub)) m.set(+sub, e[sub]); c = G.objs[c][6]; } evCache.set(key, m); }
  return m;
}
const getEv = (obj, type, sub) => evMap(obj, type).get(sub);
function fire(i, type, sub, other) { const ids = getEv(i.obj, type, sub); if (ids) for (const id of ids) run(id, i, other || null); }
function instOf(o) { const r = []; for (const i of insts) if (!i.dead && anc[i.obj].has(o)) r.push(i); return r; }
function countOf(o) { let n = 0; for (const i of insts) if (!i.dead && anc[i.obj].has(o)) n++; return n; }
function byId(id) { for (const i of insts) if (i.id === id && !i.dead) return i; return null; }
function resolve(it, self, other) {
  if (it === -1) return self; if (it === -2) return other;
  if (it >= 100000) return byId(it);
  if (it >= 0) { for (const i of insts) if (!i.dead && anc[i.obj].has(it)) return i; }
  return null;
}
function create(obj, x, y) { const i = new Inst(obj, x, y, nextId++); insts.push(i); fire(i, 0, 0); return i; }
function destroy(i) { if (i.dead) return; i.dead = true; fire(i, 1, 0); }

/* ================================================================== collisions (bounding boxes, rotated like GameMaker) */
function bbox(i, x, y) {
  const s = G.spr[i.mask_index >= 0 ? i.mask_index : i.sprite_index]; if (!s) return null;
  const xs = i.image_xscale, ys = i.image_yscale;
  let a = (s[5] - s[3]) * xs, b = (s[6] + 1 - s[3]) * xs, c = (s[7] - s[4]) * ys, d = (s[8] + 1 - s[4]) * ys;
  if (i.image_angle) {
    const t = i.image_angle * D2R, co = Math.cos(t), si = Math.sin(t);
    const px = [a * co + c * si, b * co + c * si, a * co + d * si, b * co + d * si], py = [-a * si + c * co, -b * si + c * co, -a * si + d * co, -b * si + d * co];
    a = Math.min(...px); b = Math.max(...px); c = Math.min(...py); d = Math.max(...py);
  }
  return [x + Math.min(a, b), y + Math.min(c, d), x + Math.max(a, b), y + Math.max(c, d)];
}
function hit(i, x, y, j) { const a = bbox(i, x, y), b = bbox(j, j.x, j.y); return !!a && !!b && a[0] < b[2] && a[2] > b[0] && a[1] < b[3] && a[3] > b[1]; }
function meeting(i, x, y, o) { for (const j of insts) if (j !== i && !j.dead && anc[j.obj].has(o) && hit(i, x, y, j)) return true; return false; }
function placeFree(i, x, y) { for (const j of insts) if (j !== i && !j.dead && j.solid && hit(i, x, y, j)) return false; return true; }
function placeEmpty(i, x, y) { for (const j of insts) if (j !== i && !j.dead && hit(i, x, y, j)) return false; return true; }

/* ================================================================== variables */
const GLOBAL_NAMES = new Set(['room_width', 'room_height', 'room_speed', 'score', 'lives', 'health']);
function getv(name, it, idx, self, other, loc) {
  if (idx !== null) { if (name in V) { const v = V[name][idx]; return v === undefined ? 0 : v; } const t = it === -1 ? self : it === -2 ? other : resolve(it, self, other); const a = t && t['_a_' + name]; return a && a[idx] !== undefined ? a[idx] : 0; }
  if (GLOBAL_NAMES.has(name)) return GL[name];
  if (it === -7) { const v = loc[name]; return v === undefined ? 0 : v; }
  if (it === -5) { const v = GLV[name]; return v === undefined ? 0 : v; }
  const t = it === -1 ? self : it === -2 ? other : resolve(it, self, other);
  if (!t) return 0;
  const v = t[name]; return v === undefined ? 0 : v;
}
function setv(name, it, idx, v, self, other, loc) {
  if (idx !== null) { if (name in V) { V[name][idx] = v; return; } const t = it === -1 ? self : it === -2 ? other : resolve(it, self, other); if (t) (t['_a_' + name] = t['_a_' + name] || {})[idx] = v; return; }
  if (GLOBAL_NAMES.has(name)) { GL[name] = v; return; }
  if (it === -7) { loc[name] = v; return; }
  if (it === -5) { GLV[name] = v; return; }
  const t = it === -1 ? self : it === -2 ? other : resolve(it, self, other);
  if (t) t[name] = v;
}
function withList(v, self, other) {
  if (v === -1) return [self]; if (v === -2) return other ? [other] : []; if (v === -3) return insts.filter(i => !i.dead); if (v === -4) return [];
  if (v >= 100000) { const i = byId(v); return i ? [i] : []; }
  if (v >= 0) return instOf(v);
  return [];
}

/* ================================================================== the bytecode interpreter */
/* FIX: comparison sites that were really ">" (see the compare ops below) */
const FLIP_CMP = new Set(["30:2", "62:16", "220:56", "1346:13", "1349:13", "1352:13", "1359:13", "1361:13", "1363:13", "1422:2", "1510:13", "1517:131", "1547:11", "1632:74", "1643:28", "1704:13", "1704:38", "1706:13", "1706:38", "1708:13", "1708:38", "1710:13", "1710:38", "1852:13", "1977:13", "2199:2", "2201:4", "2215:4", "3135:2", "3139:2", "3263:6", "3266:14", "3269:23", "3269:39", "3274:23", "3274:39", "3296:6", "3310:146", "3466:6", "3653:36", "3653:102", "3653:286", "3662:188", "3678:115", "3680:104"]);
/* FIX: "turn around" markers (collision code that only reverses direction) flipped an instance back and forth every step when it
   started a pixel inside them (Act 10 cameraman 'walked' on the spot). Don't reverse if it is already heading away from the marker. */
const BOUNCE_ONLY = new Set();
G.code.forEach((c, ci) => { if (c.length && c.some(o => o[0] === 'c' && o[1] === 'action_reverse_xdir') && c.every(o => (o[0] === 'c' && o[1] === 'action_reverse_xdir') || o[0] === 'pz')) BOUNCE_ONLY.add(ci); });
function movingAway(i, j) {
  const a = bbox(i, i.x, i.y), b = bbox(j, j.x, j.y); if (!a || !b) return false;
  const ca = (a[0] + a[2]) / 2, cb = (b[0] + b[2]) / 2;
  return (i.hspeed > 0 && cb < ca) || (i.hspeed < 0 && cb > ca);
}
function run(ci, self, other) {
  const prev = rel; rel = 0;                                   // 'relative' is per script, always off at the start
  try { exec(ci, self, other); } catch (e) { if (errCount++ < 25) console.error('script', ci, e); } finally { rel = prev; }
}
function exec(ci, self, other) {
  const c = G.code[ci]; if (!c) return;
  const st = [], loc = {}, envs = []; let pc = 0, guard = 0;
  while (pc < c.length) {
    if (++guard > 300000) { console.warn('script loop guard', ci); return; }
    const i = c[pc];
    switch (i[0]) {
      case 'k': st.push(i[1]); pc++; break;
      case 'v': { let idx = null; if (i[3]) { idx = st.pop(); st.pop(); } st.push(getv(i[1], i[2], idx, self, other, loc)); pc++; break; }
      case 's': { let idx = null; if (i[3]) { idx = st.pop(); st.pop(); } setv(i[1], i[2], idx, st.pop(), self, other, loc); pc++; break; }
      case 'c': { const args = []; for (let n = 0; n < i[2]; n++) args.push(st.pop()); const f = FN[i[1]]; let r = 0;
        if (f) { try { r = f(args, self, other); } catch (e) { if (errCount++ < 25) console.error('fn', i[1], e); } } else console.warn('missing fn', i[1]);
        st.push(r === undefined ? 0 : r); pc++; break; }
      case 'b': pc = i[1]; break;
      case 'bt': pc = st.pop() > 0.5 ? i[1] : pc + 1; break;
      case 'bf': pc = st.pop() > 0.5 ? pc + 1 : i[1]; break;
      case 'cv': { if (i[2] === 4) { st.push(st.pop() > 0.5 ? 1 : 0); } else if (i[2] === 2 && typeof st[st.length - 1] === 'number') st.push(Math.trunc(st.pop())); pc++; break; }
      case 'add': { const b = st.pop(), a = st.pop(); st.push(a + b); pc++; break; }
      case 'sub': { const b = st.pop(), a = st.pop(); st.push(a - b); pc++; break; }
      case 'mul': { const b = st.pop(), a = st.pop(); st.push(a * b); pc++; break; }
      case 'div': { const b = st.pop(), a = st.pop(); st.push(a / b); pc++; break; }
      case 'rem': case 'mod': { const b = st.pop(), a = st.pop(); st.push(a % b); pc++; break; }
      case 'and': { const b = st.pop(), a = st.pop(); st.push(a & b); pc++; break; }
      case 'or': { const b = st.pop(), a = st.pop(); st.push(a | b); pc++; break; }
      case 'xor': { const b = st.pop(), a = st.pop(); st.push(a ^ b); pc++; break; }
      case 'shl': { const b = st.pop(), a = st.pop(); st.push(a << b); pc++; break; }
      case 'shr': { const b = st.pop(), a = st.pop(); st.push(a >> b); pc++; break; }
      case 'neg': st.push(-st.pop()); pc++; break;
      case 'not': st.push(st.pop() > 0.5 ? 0 : 1); pc++; break;
      /* FIX: the game's converter turned every source ">" into "<" as well. The sites listed in FLIP_CMP are the ones whose surrounding
         logic shows they were really ">" (NPCs facing away, arcade enemies walking away, guards spotting you from behind...). */
      case 'slt': { const b = st.pop(), a = st.pop(); st.push((FLIP_CMP.has(ci + ':' + pc) ? b < a : a < b) ? 1 : 0); pc++; break; }
      case 'sle': { const b = st.pop(), a = st.pop(); st.push(a <= b ? 1 : 0); pc++; break; }
      case 'seq': { const b = st.pop(), a = st.pop(); st.push(a == b ? 1 : 0); pc++; break; }
      case 'sne': { const b = st.pop(), a = st.pop(); st.push(a != b ? 1 : 0); pc++; break; }
      case 'sge': { const b = st.pop(), a = st.pop(); st.push(a >= b ? 1 : 0); pc++; break; }
      case 'sgt': { const b = st.pop(), a = st.pop(); st.push(a > b ? 1 : 0); pc++; break; }
      case 'dup': { st.push(st[st.length - 1]); pc++; break; }
      case 'pz': st.pop(); pc++; break;
      case 'pe': { const l = withList(st.pop(), self, other);       // with (...) { ... }
        if (!l.length) pc = i[1] + 1; else { envs.push({ l, n: 0, self, other }); other = self; self = l[0]; pc++; } break; }
      case 'po': { const e = envs[envs.length - 1]; if (!e) { pc++; break; }
        if (i[2]) { envs.pop(); self = e.self; other = e.other; pc++; break; }
        if (++e.n < e.l.length) { self = e.l[e.n]; other = e.self; pc = i[1]; } else { envs.pop(); self = e.self; other = e.other; pc++; } break; }
      case 'ex': return;
      default: throw new Error('bad op ' + i[0]);
    }
  }
}

/* ================================================================== drawing */
const blendCache = {}, fontCache = {}, patCache = {};
function blended(si, fi, t, col) {
  const key = si + '_' + fi + '_' + col; if (blendCache[key]) return blendCache[key];
  const c = document.createElement('canvas'); c.width = t[2]; c.height = t[3];
  const x = c.getContext('2d'), img = tex[t[8]];
  x.drawImage(img, t[0], t[1], t[2], t[3], 0, 0, t[2], t[3]);
  x.globalCompositeOperation = 'multiply'; x.fillStyle = 'rgb(' + (col & 255) + ',' + ((col >> 8) & 255) + ',' + ((col >> 16) & 255) + ')'; x.fillRect(0, 0, t[2], t[3]);
  x.globalCompositeOperation = 'destination-in'; x.drawImage(img, t[0], t[1], t[2], t[3], 0, 0, t[2], t[3]);
  return (blendCache[key] = c);
}
function drawSpr(si, fi, x, y, xs, ys, ang, alpha, blend) {
  const s = G.spr[si]; if (!s) return;
  const n = s[9].length; if (!n) return;
  fi = Math.floor(fi) % n; if (fi < 0) fi += n;
  const t = G.tp[s[9][fi]]; if (!t) return;
  let img = tex[t[8]], sx = t[0], sy = t[1];
  if (blend !== undefined && blend !== 16777215 && blend !== -1 && Number.isFinite(blend)) { img = blended(si, fi, t, blend); sx = 0; sy = 0; }
  ctx.globalAlpha = Number.isFinite(alpha) ? Math.max(0, Math.min(1, alpha)) : 1;
  if (ang || xs !== 1 || ys !== 1) {
    ctx.save(); ctx.translate(x, y); if (ang) ctx.rotate(-ang * D2R); ctx.scale(xs, ys);
    ctx.drawImage(img, sx, sy, t[2], t[3], -s[3] + t[4], -s[4] + t[5], t[2], t[3]); ctx.restore();
  } else ctx.drawImage(img, sx, sy, t[2], t[3], Math.round(x - s[3] + t[4]), Math.round(y - s[4] + t[5]), t[2], t[3]);
  ctx.globalAlpha = 1;
}
function tinted(fi, col) {
  const key = fi + '_' + col; if (fontCache[key]) return fontCache[key];
  const f = G.fonts[fi], t = G.tp[f.tp];
  const c = document.createElement('canvas'); c.width = t[2]; c.height = t[3];
  const x = c.getContext('2d'); x.drawImage(tex[t[8]], t[0], t[1], t[2], t[3], 0, 0, t[2], t[3]);
  x.globalCompositeOperation = 'source-in'; x.fillStyle = 'rgb(' + (col & 255) + ',' + ((col >> 8) & 255) + ',' + ((col >> 16) & 255) + ')'; x.fillRect(0, 0, t[2], t[3]);
  return (fontCache[key] = c);
}
function fmt(v) {                                              // GameMaker's string(): whole numbers plain, otherwise up to 2 decimals
  if (typeof v === 'number') return Number.isInteger(v) ? String(v) : v.toFixed(2).replace(/\.?0+$/, '');
  return String(v);
}
const textWidth = (f, s) => { let w = 0; for (const ch of s) { const g = f.glyphs[ch.charCodeAt(0)]; if (g) w += g[4]; } return w; };
function drawText(str, x, y) {
  const f = G.fonts[dfont]; if (!f) return;
  const atlas = tinted(dfont, dcol), lh = f.lh || (f.lh = Math.max(1, ...Object.values(f.glyphs).map(g => g[3])));
  fmt(str).split(/#|\r?\n/).forEach((ln, li) => {
    let cx = x; const w = textWidth(f, ln);
    if (dalign === 1) cx -= w / 2; else if (dalign === 2) cx -= w;
    for (const ch of ln) { const g = f.glyphs[ch.charCodeAt(0)]; if (!g) continue;
      if (g[2] > 0 && g[3] > 0) ctx.drawImage(atlas, g[0], g[1], g[2], g[3], Math.round(cx + g[5]), Math.round(y + li * lh), g[2], g[3]);
      cx += g[4]; }
  });
}
function bgPattern(bgi) {                                      // tiled backgrounds are one pattern fill, not thousands of draws
  if (patCache[bgi] !== undefined) return patCache[bgi];
  const b = G.bg[bgi], t = b && G.tp[b[1]]; let pat = null;
  if (t) { const w = t[6] || t[2], h = t[7] || t[3], c = document.createElement('canvas'); c.width = w; c.height = h;
    c.getContext('2d').drawImage(tex[t[8]], t[0], t[1], t[2], t[3], t[4], t[5], t[2], t[3]);
    try { pat = ctx.createPattern(c, 'repeat'); } catch (e) { pat = null; } }
  return (patCache[bgi] = pat);
}
function fillPattern(pat, ox, oy, x0, y0, x1, y1) {
  if (x1 <= x0 || y1 <= y0) return; ox = Math.round(ox); oy = Math.round(oy);
  ctx.save(); ctx.translate(ox, oy); ctx.fillStyle = pat; ctx.fillRect(x0 - ox, y0 - oy, x1 - x0, y1 - y0); ctx.restore();
}
function drawBg(bgi, x, y, tiled) {
  const b = G.bg[bgi]; if (!b) return; const t = G.tp[b[1]]; if (!t) return;
  if (!tiled) { ctx.drawImage(tex[t[8]], t[0], t[1], t[2], t[3], Math.round(x + t[4]), Math.round(y + t[5]), t[2], t[3]); return; }
  const pat = bgPattern(bgi); if (!pat) return;
  fillPattern(pat, x, y, Math.max(0, curView.x), Math.max(0, curView.y), Math.min(room.w, curView.x + curView.w), Math.min(room.h, curView.y + curView.h));
}
function drawRoomBgs(fg) {
  room.bgs.forEach((b, n) => {
    if ((b.fg ? 1 : 0) !== fg || b.bg < 0) return;
    const sc = bgScroll[n] || [0, 0], x = b.x + sc[0], y = b.y + sc[1];
    const g = G.bg[b.bg], t = g && G.tp[g[1]]; if (!t) return;
    const w = t[6] || t[2], h = t[7] || t[3];
    if (!b.tx && !b.ty) { ctx.drawImage(tex[t[8]], t[0], t[1], t[2], t[3], Math.round(x + t[4]), Math.round(y + t[5]), t[2], t[3]); return; }
    const pat = bgPattern(b.bg); if (!pat) return;
    fillPattern(pat, x, y, b.tx ? curView.x : x, b.ty ? curView.y : y, b.tx ? curView.x + curView.w : x + w, b.ty ? curView.y + curView.h : y + h);
  });
}
function drawTile(t) {                                         // tiles are clipped to the picture's real (trimmed) area
  const b = G.bg[t[2]], tp = b && G.tp[b[1]]; if (!tp) return;
  const ix0 = Math.max(t[3], tp[4]), iy0 = Math.max(t[4], tp[5]), ix1 = Math.min(t[3] + t[5], tp[4] + tp[2]), iy1 = Math.min(t[4] + t[6], tp[5] + tp[3]);
  if (ix1 <= ix0 || iy1 <= iy0) return;
  const dx = t[0] + (ix0 - t[3]) * t[8], dy = t[1] + (iy0 - t[4]) * t[9], dw = (ix1 - ix0) * t[8], dh = (iy1 - iy0) * t[9];
  if (dx > curView.x + curView.w || dx + dw < curView.x || dy > curView.y + curView.h || dy + dh < curView.y) return;
  ctx.drawImage(tex[tp[8]], tp[0] + (ix0 - tp[4]), tp[1] + (iy0 - tp[5]), ix1 - ix0, iy1 - iy0, dx, dy, dw, dh);
}
function drawInst(i) {
  try {
    if (getEv(i.obj, 8, 0)) { fire(i, 8, 0); return; }
    const q = G.spr[i.sprite_index]; if (!q) return;
    const ext = Math.max(q[1], q[2]) * Math.max(Math.abs(i.image_xscale), Math.abs(i.image_yscale)) * 1.5 + 4;
    if (i.x + ext < curView.x || i.x - ext > curView.x + curView.w || i.y + ext < curView.y || i.y - ext > curView.y + curView.h) return;
    drawSpr(i.sprite_index, i.image_index, i.x, i.y, i.image_xscale, i.image_yscale, i.image_angle, i.image_alpha, i.image_blend);
  } catch (e) { ctx.globalAlpha = 1; if (errCount++ < 25) console.error('draw', e); }
}
function drawWorld() {
  if (room.drawbg) { const c = room.bgc; ctx.fillStyle = 'rgb(' + (c & 255) + ',' + ((c >> 8) & 255) + ',' + ((c >> 16) & 255) + ')'; ctx.fillRect(curView.x, curView.y, curView.w, curView.h); }
  drawRoomBgs(0);
  if (!room._tiles) room._tiles = room.tiles.slice().sort((a, b) => b[7] - a[7]);
  const T = room._tiles, list = [];
  for (const i of insts) if (!i.dead && i.visible) list.push(i);
  list.sort((a, b) => b.depth - a.depth);
  let ti = 0;
  for (const i of list) { while (ti < T.length && T[ti][7] >= i.depth) drawTile(T[ti++]); drawInst(i); }
  while (ti < T.length) drawTile(T[ti++]);
  drawRoomBgs(1);
}
function portOf(v) {                                           // keep the picture undistorted (default ports are sometimes the wrong shape)
  let pw = v.pw, ph = v.ph;
  if (v.w > 0 && v.h > 0 && Math.abs(pw / ph - v.w / v.h) > 0.01) ph = Math.round(pw * v.h / v.w);
  return [v.px, v.py, pw, ph];
}
function fit() {
  if (!canvas.style) return;
  const k = Math.min(innerWidth / canvas.width, innerHeight / canvas.height);
  canvas.style.width = Math.floor(canvas.width * k) + 'px'; canvas.style.height = Math.floor(canvas.height * k) + 'px';
}
function draw() {
  // the screen is the bounding box of the visible view ports (this is what makes zoomed views fill the window)
  let sw = 0, sh = 0; const vis = [];
  for (let n = 0; n < 8; n++) { const v = room.views[n]; if (!V.view_visible[n] || !v) continue; const p = portOf(v); vis.push([n, v, p]); sw = Math.max(sw, p[0] + p[2]); sh = Math.max(sh, p[1] + p[3]); }
  if (!vis.length) { sw = room.w; sh = room.h; }              // no camera: the room itself is the screen
  if (canvas.width !== sw || canvas.height !== sh) { canvas.width = sw; canvas.height = sh; saveDepth = 0; ctx.imageSmoothingEnabled = false; fit(); }
  while (saveDepth > 0) ctx.restore();
  ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over'; ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.fillStyle = '#000'; ctx.fillRect(0, 0, canvas.width, canvas.height);
  for (const [n, v, p] of vis) {
    ctx.save(); ctx.beginPath(); ctx.rect(p[0], p[1], p[2], p[3]); ctx.clip();
    ctx.translate(p[0], p[1]); ctx.scale(p[2] / v.w, p[3] / v.h);
    const vx = Number.isFinite(V.view_xview[n]) ? V.view_xview[n] : 0, vy = Number.isFinite(V.view_yview[n]) ? V.view_yview[n] : 0;
    ctx.translate(-Math.round(vx), -Math.round(vy));
    curView = { x: Math.round(vx), y: Math.round(vy), w: v.w, h: v.h };
    try { drawWorld(); } finally { ctx.globalAlpha = 1; ctx.restore(); }
  }
  if (!vis.length) { curView = { x: 0, y: 0, w: room.w, h: room.h }; drawWorld(); }
}

/* ================================================================== game actions (GameMaker's drag-and-drop library) */
const cmp = (a, b, op) => op === 1 ? a < b : op === 2 ? a > b : a == b;
const pt = (a0, a1, s) => rel ? [s.x + a0, s.y + a1] : [a0, a1];
const FN = {
  abs: a => Math.abs(a[0]), sign: a => Math.sign(a[0]), random: a => Math.random() * a[0],
  point_direction: a => ((Math.atan2(a[1] - a[3], a[2] - a[0]) / D2R) + 360) % 360,
  distance_to_object: (a, s) => { let best = 100000; const bs = bbox(s, s.x, s.y); if (!bs) return best;
    for (const j of instOf(a[0])) { if (j === s) continue; const bj = bbox(j, j.x, j.y); if (!bj) continue;
      best = Math.min(best, Math.hypot(Math.max(0, bj[0] - bs[2], bs[0] - bj[2]), Math.max(0, bj[1] - bs[3], bs[1] - bj[3]))); } return best; },
  draw_self: (a, s) => drawSpr(s.sprite_index, s.image_index, s.x, s.y, s.image_xscale, s.image_yscale, s.image_angle, s.image_alpha, s.image_blend),
  draw_sprite_ext: (a, s) => drawSpr(a[0], a[1] < 0 ? s.image_index : a[1], a[2], a[3], a[4], a[5], a[6], a[8], a[7]),
  action_set_relative: a => { rel = a[0]; },
  action_if: a => a[0],
  action_if_number: a => cmp(countOf(a[0]), a[1], a[2]) ? 1 : 0,
  action_if_variable: a => cmp(a[0], a[1], a[2]) ? 1 : 0,
  action_if_dice: a => Math.random() * a[0] < 1 ? 1 : 0,
  action_if_sound: a => sndPlaying(a[0]) ? 1 : 0,
  action_if_empty: (a, s) => { const [x, y] = pt(a[0], a[1], s); return (a[2] === 0 ? placeFree(s, x, y) : placeEmpty(s, x, y)) ? 1 : 0; },
  action_if_object: (a, s) => { const [x, y] = pt(a[1], a[2], s); return meeting(s, x, y, a[0]) ? 1 : 0; },
  action_if_score: a => cmp(GL.score, a[0], a[1]) ? 1 : 0,
  action_if_life: a => cmp(GL.lives, a[0], a[1]) ? 1 : 0,
  action_kill_object: (a, s) => { destroy(s); },
  action_create_object: (a, s) => { const [x, y] = pt(a[1], a[2], s); create(a[0], x, y); },
  action_create_object_motion: (a, s) => { const [x, y] = pt(a[1], a[2], s); const i = create(a[0], x, y); i.direction = a[4]; i.speed = a[3]; /* FIX: direction first, so a negative speed keeps its sign */ },
  action_change_object: (a, s) => { if (a[1]) fire(s, 1, 0); s.obj = a[0]; const o = G.objs[a[0]]; if (o[1] >= 0) s.sprite_index = o[1]; s.depth = o[4]; s.solid = !!o[3]; s.visible = !!o[2]; if (a[1]) fire(s, 0, 0); },
  action_set_alarm: (a, s) => { const k = a[1]; s.alarm[k] = rel && s.alarm[k] > 0 ? s.alarm[k] + a[0] : a[0]; },
  action_set_hspeed: (a, s) => { s.hspeed = rel ? s.hspeed + a[0] : a[0]; },
  action_set_vspeed: (a, s) => { s.vspeed = rel ? s.vspeed + a[0] : a[0]; },
  action_set_motion: (a, s) => { if (rel) { const h = s.hspeed + a[1] * Math.cos(a[0] * D2R), v = s.vspeed - a[1] * Math.sin(a[0] * D2R); s._hs = snap(h); s._vs = snap(v); s._dir = s._angle(); } else { s.direction = a[0]; s.speed = a[1]; } },
  action_set_gravity: (a, s) => { s.gravity_direction = a[0]; s.gravity = rel ? s.gravity + a[1] : a[1]; },
  action_set_friction: (a, s) => { s.friction = rel ? s.friction + a[0] : a[0]; },
  action_move_start: (a, s) => { s.x = s.xstart; s.y = s.ystart; },
  action_move_to: (a, s) => { const [x, y] = pt(a[0], a[1], s); s.x = x; s.y = y; },
  action_move_point: (a, s) => { const [x, y] = pt(a[0], a[1], s); s.direction = FN.point_direction([s.x, s.y, x, y]); s.speed = a[2]; },
  action_move: (a, s) => { const str = String(a[0]), map = [225, 270, 315, 180, -1, 0, 135, 90, 45], ch = [];
    for (let n = 0; n < 9; n++) if (str[n] === '1') ch.push(map[n]);
    if (!ch.length) return; const d = ch[Math.floor(Math.random() * ch.length)];
    if (d < 0) s.speed = 0; else { s.direction = d; s.speed = rel ? s.speed + a[1] : a[1]; } },
  action_move_contact: (a, s) => { const d = a[0] * D2R, max = a[1] > 0 ? a[1] : 1000, dx = Math.cos(d), dy = -Math.sin(d), solidOnly = a[2] === 0;
    for (let n = 0; n < max; n++) { const nx = s.x + dx, ny = s.y + dy; if (solidOnly ? !placeFree(s, nx, ny) : !placeEmpty(s, nx, ny)) break; s.x = nx; s.y = ny; } },
  action_bounce: (a, s) => { const free = (x, y) => a[1] === 1 ? placeEmpty(s, x, y) : placeFree(s, x, y);
    const hs = s.hspeed, vs = s.vspeed, hF = free(s.x + hs, s.y), vF = free(s.x, s.y + vs);
    if (!hF && vF) s.hspeed = -hs; else if (hF && !vF) s.vspeed = -vs;
    else if (!hF && !vF) { s.hspeed = -hs; s.vspeed = -vs; }
    else if (!free(s.x + hs, s.y + vs)) { s.hspeed = -hs; s.vspeed = -vs; } },
  action_reverse_xdir: (a, s) => { s.hspeed = -s.hspeed; },
  action_wrap: (a, s) => { if (a[0] !== 1) { if (s.x < 0) s.x += room.w; else if (s.x > room.w) s.x -= room.w; } if (a[0] !== 0) { if (s.y < 0) s.y += room.h; else if (s.y > room.h) s.y -= room.h; } },
  action_sprite_set: (a, s) => { if (a[0] >= 0) s.sprite_index = a[0]; if (a[1] >= 0) s.image_index = a[1]; if (a[2] >= 0) s.image_speed = a[2]; },
  action_sprite_transform: (a, s) => { let xs = a[0], ys = a[1]; const m = a[3]; s.image_angle = a[2]; if (m === 1 || m === 3) xs = -xs; if (m === 2 || m === 3) ys = -ys; s.image_xscale = xs; s.image_yscale = ys; },
  action_sprite_color: (a, s) => { s.image_blend = a[0]; s.image_alpha = a[1]; },
  action_sound: a => playSnd(a[0], a[1] > 0.5),
  action_end_sound: a => stopSnd(a[0]),
  audio_stop_sound: a => stopSnd(a[0]),
  action_color: a => { dcol = a[0]; },
  action_font: a => { dfont = a[0]; dalign = a[1]; },
  action_draw_text: (a, s) => { const [x, y] = pt(a[1], a[2], s); drawText(a[0], x, y); },
  action_draw_variable: (a, s) => { const [x, y] = pt(a[1], a[2], s); drawText(a[0], x, y); },
  action_draw_sprite: (a, s) => { const [x, y] = pt(a[1], a[2], s); drawSpr(a[0], a[3] < 0 ? s.image_index : a[3], x, y, 1, 1, 0, 1); },
  action_draw_background: a => drawBg(a[0], a[1], a[2], a[3]),
  action_draw_score: (a, s) => { const [x, y] = pt(a[0], a[1], s); drawText(String(a[2]) + fmt(GL.score), x, y); },
  action_draw_life_images: (a, s) => { const q = G.spr[a[2]]; if (!q) return; const [x, y] = pt(a[0], a[1], s); for (let n = 0; n < GL.lives; n++) drawSpr(a[2], 0, x + n * q[1], y, 1, 1, 0, 1); },
  action_set_score: a => { GL.score = rel ? GL.score + a[0] : a[0]; },
  action_set_life: a => { GL.lives = rel ? GL.lives + a[0] : a[0]; },
  action_set_cursor: a => { if (canvas.style) canvas.style.cursor = a[1] ? 'default' : 'none'; },
  action_next_room: () => { const p = G.order.indexOf(roomIdx); if (p >= 0 && p < G.order.length - 1) nextRoom = G.order[p + 1]; },
  action_previous_room: () => { const p = G.order.indexOf(roomIdx); if (p > 0) nextRoom = G.order[p - 1]; },
  action_current_room: () => { nextRoom = roomIdx; },
  action_another_room: a => { nextRoom = a[0]; },
  action_restart_game: () => { pendingRestart = true; },
  action_end_game: () => { gameOver = true; stopAllSnd(); },
  action_save_game: a => { pendingSave = String(a[0]); },
  action_load_game: a => { pendingLoad = String(a[0]); },
  audio_emitter_create: () => ++emitterId, audio_emitter_position: noop, audio_emitter_falloff: noop, audio_emitter_free: noop,
  audio_falloff_set_model: noop, audio_listener_position: noop, audio_listener_orientation: noop,
};
let pendingRestart = false;

/* ================================================================== saving and loading (GameMaker's game_save / game_load) */
function ser(i) {                                              // only what differs from a freshly created instance
  const base = new Inst(i.obj, i.x, i.y, i.id), o = { obj: i.obj, id: i.id, x: i.x, y: i.y };
  for (const k of Object.keys(i)) { if (k === 'obj' || k === 'id' || k === 'x' || k === 'y') continue;
    const v = i[k], b = base[k];
    if (Array.isArray(v)) { if (JSON.stringify(v) !== JSON.stringify(b)) o[k] = v.slice(); } else if (typeof v === 'object' && v !== null) o[k] = JSON.parse(JSON.stringify(v)); else if (v !== b) o[k] = v; }
  return o;
}
function unser(o) { const i = new Inst(o.obj, o.x, o.y, o.id); Object.assign(i, o); i.alarm = (o.alarm || i.alarm).slice(); i.dead = false; return i; }
function snapshot(withRooms) {
  const store = {}; if (withRooms) for (const k in roomStore) store[k] = roomStore[k].filter(i => !i.dead).map(ser);
  const V2 = {}; for (const k in V) V2[k] = V[k].slice();
  return JSON.stringify({ room: roomIdx, insts: insts.filter(i => !i.dead).map(ser), store, nextId, V: V2, GL: Object.assign({}, GL), GLV: Object.assign({}, GLV) });
}
function restore(str) {
  const d = JSON.parse(str);
  insts = d.insts.map(unser);
  for (const k in roomStore) delete roomStore[k];
  for (const k in d.store) roomStore[k] = d.store[k].map(unser);
  roomIdx = d.room; room = G.rooms[roomIdx]; nextRoom = -1; nextId = d.nextId;
  for (const k in d.V) V[k] = d.V[k].slice();
  Object.assign(GL, d.GL); for (const k in GLV) delete GLV[k]; Object.assign(GLV, d.GLV || {});
  room.bgs.forEach((b, n) => { bgScroll[n] = [0, 0]; });
}
/* FIX: the "select tape" menu reads stage1..20 from a persistent object that only gets its values back after a game_load.
   Keep the unlocked tapes in their own tiny key that is never evicted, and fold them back in whenever a room starts or a save loads. */
const CS_OBJ = G.objs.findIndex(o => o[0] === 'obj_chapter_select'), PROG_KEY = 'hh2_progress';
let progress = null;
function foldSave(str) {
  try { if (!str) return; const m = str.match(new RegExp('\\{"obj":' + CS_OBJ + ',[^{}]*\\}')); if (!m) return;
    const o = JSON.parse(m[0]); for (let n = 1; n <= 20; n++) { const k = 'stage' + n; if ((+o[k] || 0) > (progress[k] || 0)) progress[k] = +o[k]; } } catch (e) { }
}
function loadProgress() {
  if (progress) return progress; progress = {};
  try { const p = JSON.parse(localStorage.getItem(PROG_KEY) || '{}'); for (const k in p) progress[k] = +p[k] || 0; } catch (e) { }
  try { for (let k = 0; k < localStorage.length; k++) { const key = localStorage.key(k); if (key && key.startsWith('hh2_') && key !== PROG_KEY) foldSave(localStorage.getItem(key)); } } catch (e) { }
  for (const nm in memSaves) foldSave(memSaves[nm]);
  try { localStorage.setItem(PROG_KEY, JSON.stringify(progress)); } catch (e) { }
  return progress;
}
function syncProgress() {
  if (CS_OBJ < 0) return;
  try { const p = loadProgress(); let changed = false;
    for (const i of insts) { if (i.dead || i.obj !== CS_OBJ) continue;
      for (let n = 1; n <= 20; n++) { const k = 'stage' + n, cur = +i[k] || 0, pv = p[k] || 0; if (cur > pv) { p[k] = cur; changed = true; } else if (pv > cur) i[k] = pv; } }
    if (changed) try { localStorage.setItem(PROG_KEY, JSON.stringify(p)); } catch (e) { } } catch (e) { }
}
function persist(name, str) {
  try { localStorage.setItem('hh2_' + name, str); return true; } catch (e) { }
  try {                                                         // out of space: drop the biggest other checkpoints and retry
    const ks = []; for (let k = 0; k < localStorage.length; k++) { const key = localStorage.key(k); if (key && key.startsWith('hh2_') && key !== 'hh2_' + name && key !== PROG_KEY && key !== 'hh2_savegame') ks.push([key, localStorage.getItem(key).length]); }
    ks.sort((x, y) => y[1] - x[1]);
    for (const [key] of ks) { localStorage.removeItem(key); try { localStorage.setItem('hh2_' + name, str); return true; } catch (e) { } }
  } catch (e) { }
  return false;
}
function doSave(name) {
  let str = snapshot(true); if (str.length > 1500000) str = snapshot(false);
  memSaves[name] = str;                                         // always kept for this session even if the browser refuses
  if (!persist(name, str)) { str = snapshot(false); memSaves[name] = str; if (!persist(name, str)) console.warn('could not persist save'); }
  syncProgress();
}
function doLoad(name) { try { const d = memSaves[name] || localStorage.getItem('hh2_' + name); if (d) restore(d); } catch (e) { console.error('load failed', e); } syncProgress(); sweepSounds(); }

/* ================================================================== rooms */
function initViews() {
  for (let n = 0; n < 8; n++) { const v = room.views[n];
    V.view_visible[n] = v ? v.en : 0; V.view_xview[n] = v ? v.x : 0; V.view_yview[n] = v ? v.y : 0; V.view_wview[n] = v ? v.w : 0; V.view_hview[n] = v ? v.h : 0;
    V.view_object[n] = v ? v.obj : -1; V.view_hspeed[n] = v ? v.hs : -1; V.view_vspeed[n] = v ? v.vs : -1; V.view_angle[n] = 0; }
}
function enterRoom(ri) {
  for (const i of insts) if (!i.dead) fire(i, 7, 5);                                  // Room End
  const prev = roomIdx, hadRoom = !!room;
  const keep = insts.filter(i => i.persistent && !i.dead);
  if (hadRoom && room.pers) roomStore[prev] = insts.filter(i => !i.persistent && !i.dead);
  insts = keep; roomIdx = ri; room = G.rooms[ri]; nextRoom = -1;
  GL.room_width = room.w; GL.room_height = room.h; GL.room_speed = room.speed;
  initViews(); room.bgs.forEach((b, n) => { bgScroll[n] = [0, 0]; });
  if (ri === prev) delete roomStore[ri];                                              // restarting a room resets it
  if (room.pers && roomStore[ri]) { insts = keep.concat(roomStore[ri]); delete roomStore[ri]; }   // persistent room: restore what it was
  else {
    const fresh = [];
    for (const o of room.objs) {
      if (keep.some(k => k.id === o[3])) continue;
      const i = new Inst(o[2], o[0], o[1], o[3]); i.image_xscale = o[5]; i.image_yscale = o[6]; i.image_angle = o[7];
      insts.push(i); fresh.push([i, o[4]]);
    }
    for (const [i, cc] of fresh) { fire(i, 0, 0); if (cc >= 0) run(cc, i, null); }
    if (room.code >= 0) run(room.code, null, null);
  }
  for (const i of insts.slice()) if (!i.dead) fire(i, 7, 4);                          // Room Start
  followViews();
  syncProgress(); sweepSounds();
}
function restartGame() {
  for (const i of insts) i.dead = true;
  insts = []; room = null; roomIdx = -1; for (const k in roomStore) delete roomStore[k];
  GL.score = 0; GL.lives = -1; GL.health = 100; for (const k in GLV) delete GLV[k];
  stopAllSnd(); nextRoom = -1; gameOver = false; enterRoom(G.order[0]);
}
function followViews() {
  for (let n = 0; n < 8; n++) { const v = room.views[n]; if (!V.view_visible[n] || V.view_object[n] < 0 || !v) continue;
    const t = instOf(V.view_object[n])[0]; if (!t || !Number.isFinite(t.x) || !Number.isFinite(t.y)) continue;
    let vx = V.view_xview[n], vy = V.view_yview[n]; if (!Number.isFinite(vx)) vx = 0; if (!Number.isFinite(vy)) vy = 0;
    const bx = Math.min(v.bx, v.w / 2), by = Math.min(v.by, v.h / 2);                 // a huge border means "keep centered"
    let dx = vx, dy = vy;
    if (t.x < vx + bx) dx = t.x - bx; else if (t.x > vx + v.w - bx) dx = t.x - v.w + bx;
    if (t.y < vy + by) dy = t.y - by; else if (t.y > vy + v.h - by) dy = t.y - v.h + by;
    dx = Math.max(0, Math.min(room.w - v.w, dx)); dy = Math.max(0, Math.min(room.h - v.h, dy));
    const hs = V.view_hspeed[n], vsp = V.view_vspeed[n];                               // -1 = jump, otherwise max pixels per step
    if (hs >= 0) dx = vx + Math.max(-hs, Math.min(hs, dx - vx));
    if (vsp >= 0) dy = vy + Math.max(-vsp, Math.min(vsp, dy - vy));
    V.view_xview[n] = dx; V.view_yview[n] = dy; }
}

/* ================================================================== one game step */
function step() {
  try { stepInner(); } catch (e) { if (errCount++ < 25) console.error('step', e); }
  if (pendingRestart) { pendingRestart = false; pendingSave = pendingLoad = null; try { restartGame(); } catch (e) { console.error('restart', e); } return; }
  if (nextRoom >= 0) { try { enterRoom(nextRoom); } catch (e) { console.error('room', e); nextRoom = -1; } }
  if (pendingSave) { const n = pendingSave; pendingSave = null; doSave(n); }
  if (pendingLoad) { const n = pendingLoad; pendingLoad = null; doLoad(n); }
}
function stepInner() {
  frame++;
  if (frame % 5 === 0) sweepSounds();
  if (frame % 30 === 0) syncProgress();
  const list = insts.slice(), pk = Object.keys(pressed), rk = Object.keys(released);
  for (const i of list) if (!i.dead) fire(i, 3, 1);                                    // begin step
  for (const i of list) { if (i.dead) continue;                                        // alarms
    for (let k = 0; k < 12; k++) { if (i.alarm[k] > 0) { i.alarm[k]--; if (i.alarm[k] === 0) { i.alarm[k] = -1; fire(i, 2, k); } } } }
  for (const i of list) { if (i.dead) continue;                                        // keyboard
    for (const k of pk) fire(i, 9, +k);
    if (pk.length) fire(i, 9, 1);
    for (const k in keys) if (keys[k]) fire(i, 5, +k);
    for (const k of rk) fire(i, 10, +k); }
  for (const i of list) if (!i.dead) fire(i, 3, 0);                                    // step
  for (const i of list) { if (i.dead) continue;                                        // movement
    i.xprevious = i.x; i.yprevious = i.y;
    if (i.gravity) { const g = i.gravity_direction * D2R; i._hs = snap(i._hs + i.gravity * Math.cos(g)); i._vs = snap(i._vs - i.gravity * Math.sin(g)); i._dir = i._angle(); }
    if (i.friction && (i._hs || i._vs)) { const s = Math.hypot(i._hs, i._vs), k = Math.max(0, s - i.friction) / s; i._hs = snap(i._hs * k); i._vs = snap(i._vs * k); }
    if (i._hs || i._vs) { i.x += i._hs; i.y += i._vs; }
    if (!Number.isFinite(i.x)) i.x = i.xprevious; if (!Number.isFinite(i.y)) i.y = i.yprevious; }
  for (const i of list) {                                                              // collisions
    if (i.dead) continue; const cm = evMap(i.obj, 4); if (!cm.size) continue;
    for (const [sub, ids] of cm) {
      for (const j of insts.slice()) { if (i.dead) break; if (j === i || j.dead || !anc[j.obj].has(sub) || !hit(i, i.x, i.y, j)) continue;
        if (j.solid) { i.x = i.xprevious; i.y = i.yprevious; }                        // bumping into a solid puts you back
        for (const id of ids) { if (BOUNCE_ONLY.has(id) && movingAway(i, j)) continue; run(id, i, j); } } } }
  for (const i of list) if (!i.dead) fire(i, 3, 2);                                    // end step
  for (const i of list) { if (i.dead) continue;                                        // animation + outside events
    if (i.image_single >= 0) i.image_index = i.image_single;
    else if (i.image_speed) { const s = G.spr[i.sprite_index]; i.image_index += i.image_speed;
      if (s) { const n = s[9].length; if (n && (i.image_index >= n || i.image_index < 0)) { i.image_index = ((i.image_index % n) + n) % n; fire(i, 7, 7); } } }
    const om = evMap(i.obj, 7); if (!om.size) continue;
    const b = bbox(i, i.x, i.y); if (!b) continue;
    if (om.has(0) && (b[2] < 0 || b[0] > room.w || b[3] < 0 || b[1] > room.h)) fire(i, 7, 0);
    for (let n = 0; n < 8; n++) { if (!om.has(40 + n) || !V.view_visible[n] || !room.views[n]) continue;
      const vv = room.views[n], vx = V.view_xview[n], vy = V.view_yview[n];
      if (b[2] < vx || b[0] > vx + vv.w || b[3] < vy || b[1] > vy + vv.h) fire(i, 7, 40 + n); } }
  insts = insts.filter(i => !i.dead);
  followViews();
  room.bgs.forEach((b, n) => { if (b.sx || b.sy) { bgScroll[n][0] += b.sx; bgScroll[n][1] += b.sy; } });
  for (const k in pressed) delete pressed[k]; for (const k in released) delete released[k];
}

/* FIX: start loading the pictures as soon as the page loads (not only after the click) */
let texDone = false; const texWaiters = [];
loadTextures(() => { texDone = true; texWaiters.splice(0).forEach(f => f()); });
function whenTexturesReady(cb) { if (texDone) cb(); else texWaiters.push(cb); }

/* FIX: the EXAMINE / READ zone of the hand-placed message sprites is moved to where their picture really is (measured from the pixels) */
function fitInteractZones() {
  for (const nm of ['spr_date', 'spr_message']) {
    const si = G.spr.findIndex(s => s[0] === nm); if (si < 0) continue; const s = G.spr[si], t = G.tp[s[9][0]]; if (!t || !tex[t[8]]) continue;
    const c = document.createElement('canvas'); c.width = t[2]; c.height = t[3]; const x = c.getContext('2d');
    x.drawImage(tex[t[8]], t[0], t[1], t[2], t[3], 0, 0, t[2], t[3]);
    const d = x.getImageData(0, 0, t[2], t[3]).data; let sum = 0, w = 0;
    for (let yy = 0; yy < t[3]; yy++) for (let xx = 0; xx < t[2]; xx++) { const a = d[(yy * t[2] + xx) * 4 + 3]; if (a > 40) { sum += xx * a; w += a; } }
    if (!w) continue; const cx = Math.round(t[4] + sum / w), half = Math.floor((s[6] - s[5]) / 2), mid = Math.round((s[5] + s[6]) / 2);
    if (Math.abs(cx - mid) > 8) { s[5] = cx - half; s[6] = cx + half; }
  }
}

/* ================================================================== main loop and input */
let acc = 0, last = 0, started = false;
function loop(t) {
  requestAnimationFrame(loop);
  if (!last) last = t; acc += t - last; last = t; if (acc > 500) acc = 500;
  const dt = 1000 / (GL.room_speed || 30); let ran = false;
  while (acc >= dt && !gameOver) { step(); acc -= dt; ran = true; }
  if (ran || frame < 2) { try { draw(); } catch (e) { if (errCount++ < 25) console.error('draw', e); } }
  if (gameOver) { ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.fillStyle = '#000'; ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.fillStyle = '#fff'; ctx.font = '12px monospace'; ctx.textAlign = 'center'; ctx.fillText('Thanks for playing! Click or press Enter to start again', canvas.width / 2, canvas.height / 2); }
}
const KEYMAP = { ArrowLeft: 37, ArrowUp: 38, ArrowRight: 39, ArrowDown: 40, Enter: 13, Escape: 27, ' ': 32, Backspace: 8, Tab: 9, Shift: 16, Control: 17, Alt: 18 };
const keyCode = e => (e.keyCode && e.keyCode !== 229) ? e.keyCode : (KEYMAP[e.key] || (e.key && e.key.length === 1 ? e.key.toUpperCase().charCodeAt(0) : 0));
const GAME_KEYS = new Set([13, 27, 32, 37, 38, 39, 40]);
function keyDown(k) { if (!keys[k]) pressed[k] = 1; keys[k] = 1; }
function keyUp(k) { if (keys[k]) released[k] = 1; keys[k] = 0; }
window.addEventListener('keydown', e => { const k = keyCode(e); if (!k) return; if (GAME_KEYS.has(k)) e.preventDefault(); if (e.repeat) return;
  if (gameOver && (k === 13 || k === 32)) { restartGame(); return; } keyDown(k); });
window.addEventListener('keyup', e => { const k = keyCode(e); if (k) keyUp(k); });
window.addEventListener('blur', () => { for (const k in keys) keys[k] = 0; });
window.addEventListener('resize', fit);
canvas.addEventListener('click', () => { if (gameOver) restartGame(); });

window.HH = {
  fit, key(k, down) { down ? keyDown(k) : keyUp(k); },
  start() { if (started) return; started = true;
    whenTexturesReady(() => { try { fitInteractZones(); } catch (e) { } earlySoundsReady(() => { enterRoom(G.order[0]); requestAnimationFrame(loop); }); }); },
  _: { press: keyDown, release: keyUp, step, draw, enterRoom, create, run, FN, V, GL, roomStore, memSaves, doSave, doLoad, snapshot, restore, stopAllSnd,
       get insts() { return insts; }, get room() { return room; }, get roomIdx() { return roomIdx; }, get gameOver() { return gameOver; }, set nextRoom(v) { nextRoom = v; } },
};
})();
