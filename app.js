/* tessellation-mobile-workspace-v5.4-classroom-cr3 / app.js  (CR3: 40 points, Translation first, Sketch in Polygon with one Undo timeline, process recording, classroom polish; see CR3_REPORT.md)
 * v5.3-classroom-export / app.js  (CR2: Save image (PNG + hybrid SVG), sketch visibility, Tessellate outline width; see CR2_REPORT.md)
 * v5.2-classroom / app.js  (v5.1 + CR1: automatic save, recovery, Save project / Open project; see CR1_REPORT.md)
 * v5.1-polygon-p2 / app.js  (v5.0 + Polygon P2: the square's corners move wherever the construction allows; see V51_REPORT.md)
 * INTERACTION + PRESENTATION LAYER.  POLYGON (square grid → up to 10 straight sides) → SHAPE → ILLUSTRATE → TESSELLATE (compose by group).
 * GEOMETRY:  engine.js (unchanged since v1) and tiling-check.js (unchanged since v2). Nothing in this file changes the mathematics.
 * Three kinds of state, kept apart on purpose:
 *   GEOMETRY      – the boundary wire + edge pairing + canonical tile field          (engine.js; edited by Polygon nodes and Shape › Pull)
 *   ARTWORK       – sketch / fills / lines / art rasters in CELL coordinates         (history; repeated through each tile's matrix)
 *   COMPOSITION   – Tessellate-only DISPLAY choices per tile group (colour, opacity, hide, scale). NEVER touches geometry or artwork.
 *   (REFERENCE    – a practice image shown in Shape; not artwork, not in history, not in the tessellation)
 *   ONE FINGER CHANGES THE WORK. TWO FINGERS CHANGE THE VIEW.
 */
(() => {
'use strict';
const E = TessEngine, { N, TAU, PI, P, CONS, GROUP_COLORS, mapp, minv, mmul, det, IDM } = E;
const $ = id => document.getElementById(id);
const canvas = $('work'); let ctx = canvas.getContext('2d');      // CR2: `ctx` is swapped for an off-screen canvas while an image is exported
let EXP = null;                                                     // CR2: export settings while an image is being drawn ({ scale, transparent, sketch }), else null
const scratch = document.createElement('canvas').getContext('2d');
const PERF = window.__perf || null;                   // measurement probe (perf.js); null unless the page was opened with ?perf=1 / ?agent=1

/* ---------------- tunables (kept in one place so they are easy to adjust) ---------------- */
const INFLUENCE = { narrow: 0.12, wide: 0.30 };       // v4's two presets (fraction of edge length); now exact points on the continuous control below
// INFLUENCE WIDTH — one continuous control, Point ●──── Wide. It sets ONLY how much of the edge one pull bends (the engine's falloff radius, as a
// fraction of the edge length) — never the pull distance or elasticity. v4's Narrow and Wide are exact knots (0.35 and 1), so those settings give
// exactly v4's geometry. The Point end bends a single boundary sample: each edge is 96 segments, so that is the finest shape the engine can hold.
const INFL_KNOTS = [[0, 1.1 / N], [0.12, 2 / N], [0.24, 4.5 / N], [0.35, INFLUENCE.narrow], [0.65, 0.20], [1, INFLUENCE.wide]];
const INFL_DEFAULT = 0.35;                              // = v4's Narrow
const SNAP_BELOW = 5;                                   // radius in boundary samples below which the grab moves onto the nearest sample (see grabArc)
const ILLUSTRATE_GHOST = 0.26;                          // neighbours are quieter while illustrating
const SHAPE_GHOST = 0.42, SHAPE_DRAG_FADE = 0.35;       // Shape: neighbour loudness (v4.3: 0.42, quieter than v4.2's 0.55 but still clearly read), and the sketch fade while pulling
const MARK_ALPHA = { shape: 0.42, tessellate: 0.6 };     // the orientation 'F' in every tile: quieter while shaping (v4.2: 0.6 everywhere)
const LOCK_SVG = '<svg class="lk" viewBox="0 0 16 16" aria-hidden="true"><path d="M4.5 7V5a3.5 3.5 0 0 1 7 0v2" fill="none" stroke="currentColor" stroke-width="1.6"/><rect x="3" y="7" width="10" height="7.5" rx="1.6" fill="currentColor"/></svg>';
const HIT_PX = 28;                                      // edge grab radius in CSS px
const WORK_COMMIT_MS = 300;                             // a second finger within this window cancels the first finger's action
const TAP_PX = 10, TAP_MS = 600;                        // a short, still touch is a TAP (fill / select a tile group)
const INK_BIG = 2048, INK_SMALL = 512, INK_HALF = 1.25; // sketch/art raster domain: INK_HALF × cell size either side of the cell centre
const FLOOD = 1024;                                     // fills + lines rasters and the flood grid
const MAX_ZOOM_PX_PER_UNIT = 1100;                      // × (1/cell size): beyond this the raster would visibly blur
const COLORS = { bg: '#0f1624', fill: '#f7f1e3', fillMirror: '#cfe0f5', line: '#1d1b18', start: '#d9791a', edgeA: '#f4ca72', edgeB: '#5fd4c4' };
const SKETCH_COLOR = '#454a57';
const PALETTE = ['#1d1b18', '#ffffff', '#d94b3d', '#f08a24', '#f2c230', '#6aa84f', '#2f8f83', '#3b6fb6', '#7a4fa3', '#e58bb0', '#8b5a2b', '#9aa0a6'];
const GRID = { square: [1, 1], triangle: [0.5, 0.8660254], rhombus: [0.8, 0.5] };   // row/column pitch of tile centres, in cell sizes
const SIZE_RANGE = { sketch: [0.004, 0.10], pen: [0.004, 0.10], eraser: [0.008, 0.16], dot: [0.012, 0.14], texture: [0.02, 0.16] };
const MIN_ALPHA = 0.05;
const OUTLINE_MAX = 0.06, OUTLINE_DEFAULT = 0.428;                // CR2: Tessellate outline width = OUTLINE_MAX × v² cell sizes; the default (≈ 0.011) looks as before at the default zoom
const outlineWorld = () => OUTLINE_MAX * S.outline * S.outline * S.unit;
// POLYGON (v5.0)
const POLY_FAMILY = { translate: ['translation'], rotate: ['rotation-sq-ac', 'rotation-sq-bd'], glide: ['glide', 'glide-both'] };
const POLY_FAMILY_OF = { translation: 'translate', 'rotation-sq-ac': 'rotate', 'rotation-sq-bd': 'rotate', glide: 'glide', 'glide-both': 'glide' };
const POLY_MAX_SIDES = 10;                              // (v5.1's limit: 4 fixed corners + 2 per node → 3 nodes; no longer used)
const POLY_MAX_POINTS = 40, POLY_CUE_FROM = 30;          // CR3: up to 40 independent points per tile; a quiet count appears from 30
const NODE_PX = 24, CORNER_PX = 16, PSIDE_PX = 22;      // touch radii (CSS px): node handles, fixed corners, sides
const POLY_MIN_SEG = 0.02, POLY_CLEAR = 0.015;   // CR3: shortest side 2% of the cell (was 4%) so 40 points fit;          // × cell size: shortest side; closest a corner/node may come to a side it is not on

/* ---------------- state ---------------- */
const S = {
  mode: 'shape', shapeTool: 'pull', sketchTool: 'pen', tool: 'pen', pattern: 'hatch', color: '#1d1b18',
  sizes: { sketch: 0.3, pen: 0.3, eraser: 0.45, dot: 0.35, texture: 0.4 },     // each tool remembers its own size
  opac: { pen: 1, fill: 1, dot: 1, texture: 1 },                                // …and its own opacity
  angle: 45,                                                                    // texture angle, degrees (counter-clockwise)
  treat: 'same', comp: { same: {}, alt: {}, row: {}, col: {} }, sel: null,      // COMPOSITION (display only): per grouping, per group key
  influenceV: INFL_DEFAULT, inflPreview: 0, ghost: 'ghost', showStart: false, showSketch: false, outline: 0.428,   // CR2: Show sketch (Illustrate only); Tessellate outline (slider 0..1)
  consId: null, cellKind: 'square', field: null, fieldCull: 0, origVerts: null, path: null, cent: P(0, 0), centW: [], orientCue: false,
  cam: { x: 0, y: 0, s: 100 }, vw: 0, vh: 0, dpr: 1, cx: 0, cy: 0, fitS: 100, camByMode: {},
  ink: null, layers: null, flood: null, flood2: null, tint: new Map(), history: [], hp: 0, initialSnap: null, artVer: 0,
  opt: { refCache: true, coalesce: true, fastSampling: true, timerFallback: false },   // switches for benchmarking; timerFallback = the v4 scheduling (A/B only)
  layerVer: 0, compCache: new Map(), compPool: { big: [], small: [] }, pendingMove: null, fast: false, frameNo: 0, maskPool: null,   // render caches: layerVer bumps whenever ANY layer pixel changes
  ref: { img: null, x: 0, y: 0, sc: 1, sc0: 1, rot: 0, alpha: 0.45, visible: true, adjust: false, locked: false, cache: null, cacheLong: 0, cacheSrc: null },   // REFERENCE (practice aid only). adjust = 'Move reference' mode; locked = tracing paper
  hl: null, shape: null, stroke: null,
  seenHint: { polygon: false, shape: false, illustrate: false, tessellate: false, refLock: false },
  // POLYGON (v5.0). poly = { family, nodes, hist, hp, sel } for a square-grid start, null for the triangle / rhombus (they start in Shape).
  // shapeBaseKey = the polygon that the Shape state and history are built on; refined = the Shape boundary, put aside while Polygon is open;
  // recovery = a complete earlier version (kept whenever Polygon edits restart the Shape refinements; restoring it swaps the two).
  poly: null, pendingPoly: null, shapeBaseKey: null, refined: null, recovery: null, restartOK: false,
  // v5.1: cageNow = moved corners (null = the original square); engineId = the engine construction in use; unit = the original cell size
  // (drawing area, pen widths and limits refer to it, not to the moving cage); gridBasis = the lattice used for Tessellate's groups
  cageNow: null, engineId: null, unit: 1, gridBasis: null, lockFlash: null,
  guardShape: true, guardLog: []
};
const store = {                    // remembered settings (this browser only); the app works the same if storage is unavailable
  get(k, d) { try { const v = localStorage.getItem(k); return v == null ? d : JSON.parse(v); } catch (_) { return d; } },
  set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (_) {} }
};
S.influenceV = (v => Number.isFinite(v) ? Math.min(1, Math.max(0, v)) : INFL_DEFAULT)(store.get('tessellation.influenceWidth', INFL_DEFAULT));
function influenceRadius(v) {      // slider position (0 = Point … 1 = Wide) → falloff radius; smooth (log-linear) between knots, exact at each knot
  v = Math.min(1, Math.max(0, v)); let k = 1; while (k < INFL_KNOTS.length - 1 && v > INFL_KNOTS[k][0]) k++;
  const [v0, r0] = INFL_KNOTS[k - 1], [v1, r1] = INFL_KNOTS[k], t = (v - v0) / (v1 - v0);
  return t <= 0 ? r0 : t >= 1 ? r1 : Math.exp(Math.log(r0) + (Math.log(r1) - Math.log(r0)) * t);
}
// Where along the edge a pull is centred. With a tiny radius the boundary is only as fine as its samples, so a grab that lands BETWEEN two samples
// would move them only partly (about half at Point) — the boundary under the finger would lag it. Below SNAP_BELOW samples the centre moves onto
// the nearest sample (fully at ≤ 1 sample, blending out by SNAP_BELOW), so the point under the finger follows it. Narrow/Wide: unchanged.
function grabArc(L, sRaw) {
  const Rs = E.getRadius() * N, k = Math.min(1, Math.max(0, (SNAP_BELOW - Rs) / (SNAP_BELOW - 1))); if (k <= 0) return sRaw;
  let i = 1; for (let j = 2; j < N; j++) if (Math.abs(L[j] - sRaw) < Math.abs(L[i] - sRaw)) i = j;   // nearest movable sample (never a corner)
  return sRaw + (L[i] - sRaw) * k;
}
function pointAtArc(pts, L, s) { let i = 1; while (i < N && L[i] < s) i++; const t = (s - L[i - 1]) / ((L[i] - L[i - 1]) || 1); return P(pts[i - 1].x + (pts[i].x - pts[i - 1].x) * t, pts[i - 1].y + (pts[i].y - pts[i - 1].y) * t); }
const ptrs = new Map();            // active pointers (client coords)
let nav = null, refNav = null, work = null, lock = false;

/* ---------------- canvas / camera ---------------- */
function resize() {
  const r = canvas.getBoundingClientRect(); S.dpr = Math.min(window.devicePixelRatio || 1, 2);
  S.vw = r.width; S.vh = r.height;
  canvas.width = Math.max(1, Math.round(r.width * S.dpr)); canvas.height = Math.max(1, Math.round(r.height * S.dpr));
  const dock = $('dock').getBoundingClientRect(), top = $('top').getBoundingClientRect(), ref = $('frame-ref').getBoundingClientRect();
  document.documentElement.style.setProperty('--dock-h', Math.round(dock.height) + 'px');
  // v4.4: the view centre comes from the top bar and the Shape bar's FIXED geometry (#frame-ref), never from whichever bottom strip is showing,
  // so switching Shape ↔ Illustrate ↔ Tessellate cannot move the canvas (v4.3 moved it 3 pt and 21 pt: the strips differ in height). In Shape
  // the reference IS the bar's top edge, so the Shape view is exactly v4.3's.
  S.cx = r.width / 2; S.cy = (top.bottom + ref.top) / 2;
}
function fieldRadius() { return S.field ? S.fieldCull * S.field.size : 1; }
function zoomLimits() {
  const size = S.field.size, hd = 0.5 * Math.hypot(S.vw, S.vh);
  const minS = Math.max(hd / (fieldRadius() * 0.97), 8), maxS = Math.max(MAX_ZOOM_PX_PER_UNIT / size, minS * 1.2);
  return { minS, maxS };
}
function clampCam() {
  const { minS, maxS } = zoomLimits(), c = S.cam; c.s = Math.min(maxS, Math.max(minS, c.s));
  const hd = 0.5 * Math.hypot(S.vw, S.vh) / c.s, room = Math.max(0, fieldRadius() * 0.97 - hd), c0 = S.field.c0;
  const dx = c.x - c0.x, dy = c.y - c0.y, d = Math.hypot(dx, dy);
  if (d > room) { c.x = c0.x + dx / d * room; c.y = c0.y + dy / d * room; }
}
function fitCamera() {
  const availH = Math.max(120, 2 * Math.min(S.cy, S.vh - S.cy)), c0 = S.field.c0;
  S.fitS = 0.5 * Math.min(S.vw, availH) / S.field.size;
  S.cam = { x: c0.x, y: c0.y, s: S.fitS }; clampCam(); invalidate();
}
const w2s = p => P(S.cx + (p.x - S.cam.x) * S.cam.s, S.cy - (p.y - S.cam.y) * S.cam.s);
const s2w = (x, y) => P(S.cam.x + (x - S.cx) / S.cam.s, S.cam.y - (y - S.cy) / S.cam.s);
const worldToScreenMatrix = () => { const k = S.cam.s * S.dpr; return [k, 0, 0, -k, (S.cx - S.cam.x * S.cam.s) * S.dpr, (S.cy + S.cam.y * S.cam.s) * S.dpr]; };

/* ---------------- scheduling: requestAnimationFrame ONLY (while the page is visible).
 * v4 also rendered from a 60 ms timer. A timer-driven render happens outside Safari's rendering update, so Safari cannot hold it back when the
 * phone's drawing falls behind: drawing work piles up in Safari's GPU process and the canvas trails the finger by seconds, then "catches up"
 * (measured in iOS Safari: 2.4–3.6 s of queued drawing after 2 s). rAF frames are paced by Safari, so latency stays at a frame or two.
 * The timer is kept only for a HIDDEN document (a background tab / hidden preview pane, where rAF is paused). ---------------- */
let pending = false;
function invalidate() {
  if (pending) return; pending = true; const run = via => () => { if (!pending) return; pending = false; render(via); };
  requestAnimationFrame(run('raf')); if (document.hidden || S.opt.timerFallback) setTimeout(run('timer'), 60);
}

/* ---------------- shape / tile caches ---------------- */
const edgesNow = () => E.state.edges;
function polyCentroid(poly) { let a = 0, cx = 0, cy = 0;
  poly.forEach((p, i) => { const q = poly[(i + 1) % poly.length], w = p.x * q.y - q.x * p.y; a += w; cx += (p.x + q.x) * w; cy += (p.y + q.y) * w; });
  return P(cx / (3 * a), cy / (3 * a)); }
function rebuildPath() {
  const poly = E.polygon(edgesNow()), path = new Path2D();
  poly.forEach((p, i) => i ? path.lineTo(p.x, p.y) : path.moveTo(p.x, p.y)); path.closePath(); S.path = path;
}
function rebuildCentroids() {
  S.cent = polyCentroid(E.polygon(edgesNow()));
  S.centW = S.field.list.map(m => mapp(m, S.cent));
}
const snapshot = () => edgesNow().map(e => e.pts.map(p => ({ x: p.x, y: p.y })));
function restoreSnapshot(snap) { E.setEdges(snap.map(pts => ({ pts: pts.map(p => ({ x: p.x, y: p.y })) }))); rebuildPath(); rebuildCentroids(); }


/* ---------------- layers (ARTWORK): all rasters live in CELL coordinates and are repeated through each tile's matrix
 *   sketch  2048²  graphite sketch                          (Shape › Sketch)
 *   fills   1024²  flat colour regions, BENEATH everything  (Illustrate › Fill; re-fill REPLACES the region's colour)
 *   lines   1024²  invisible mask of pen lines only         (what Fill treats as a boundary; dots/textures are NOT boundaries)
 *   art     2048²  pen, eraser, dots, textures              (drawn on top of fills)
 * ---------------- */
const mkCanvas = n => { const c = document.createElement('canvas'); c.width = c.height = n; return c; };
function makeLayer(size, view) {
  // TRUTH (big): willReadFrequently pins the layer to ONE (software) rasteriser so a stroke replayed after Undo is pixel-identical to the original.
  // VIEW: a GPU-backed copy used ONLY for display. iOS Safari copies a whole willReadFrequently canvas (16 MB at 2048²) every time it is drawn into
  // another canvas — v4 did that on every pointer event while drawing. So the screen never reads the truth layers: composites are built from the
  // views, and a view is refreshed from its truth by rectangle (getImageData → putImageData moves only that rectangle).
  const big = mkCanvas(size), L = { size, big, bctx: big.getContext('2d', { willReadFrequently: true }), view: null, vctx: null };
  if (view) { L.view = mkCanvas(size); L.vctx = L.view.getContext('2d'); } L.k = size / S.ink.side; return L;
}
function makeInk() {
  const c0 = S.field.c0, side = 2 * INK_HALF * S.field.size; S.ink = { x0: c0.x - side / 2, y1: c0.y + side / 2, side };
  S.layers = { sketch: makeLayer(INK_BIG, true), art: makeLayer(INK_BIG, true), fills: makeLayer(FLOOD, true), lines: makeLayer(FLOOD, false) }; S.tint = new Map(); S.compCache = new Map(); S.compPool = { big: [], small: [] }; S.layerVer++;
}
const clearLayer = L => { L.bctx.clearRect(0, 0, L.size, L.size); if (L.view) L.vctx.clearRect(0, 0, L.size, L.size); };
const touchLayers = () => { S.layerVer++; };
// DIRTY RECTANGLES are kept in ink-domain units (0..1 across the raster domain, v downwards like pixel rows) so every raster maps them by its own size
const ALL = { u0: 0, v0: 0, u1: 1, v1: 1 };
const rEmpty = () => ({ u0: Infinity, v0: Infinity, u1: -Infinity, v1: -Infinity });
function rAddPt(r, p, pad) { const i = S.ink, u = (p.x - i.x0) / i.side, v = (i.y1 - p.y) / i.side, d = pad / i.side;
  if (u - d < r.u0) r.u0 = u - d; if (v - d < r.v0) r.v0 = v - d; if (u + d > r.u1) r.u1 = u + d; if (v + d > r.v1) r.v1 = v + d; return r; }
const rAdd = (r, q) => { r.u0 = Math.min(r.u0, q.u0); r.v0 = Math.min(r.v0, q.v0); r.u1 = Math.max(r.u1, q.u1); r.v1 = Math.max(r.v1, q.v1); return r; };
function rPx(r, n, m) {           // → whole-pixel rectangle on an n×n raster, grown by m px and clamped (null if empty)
  const x0 = Math.max(0, Math.floor(r.u0 * n) - m), y0 = Math.max(0, Math.floor(r.v0 * n) - m), x1 = Math.min(n, Math.ceil(r.u1 * n) + m), y1 = Math.min(n, Math.ceil(r.v1 * n) + m);
  return x1 > x0 && y1 > y0 ? { x: x0, y: y0, w: x1 - x0, h: y1 - y0 } : null;
}
function syncView(L, r) {        // VIEW := TRUTH inside r
  if (!L.view) return; const q = rPx(r, L.size, 2); if (!q) return; if (PERF) PERF.n('sync', q.w * q.h);
  L.vctx.putImageData(L.bctx.getImageData(q.x, q.y, q.w, q.h), q.x, q.y);
}
function syncAllViews() { [S.layers.sketch, S.layers.art, S.layers.fills].forEach(L => syncView(L, ALL)); S.compCache.forEach(e => paintComposite(e, null)); }
const toPx = (p, L) => P((p.x - S.ink.x0) * L.k, (S.ink.y1 - p.y) * L.k);

/* ---- painting. Pen/Eraser: smooth quadratic curves through stroke midpoints, one path per stroke (so opacity never darkens joins).
 *      Dots/Textures: marks stamped along the path at a fixed spacing. Everything is deterministic (seeded) so history REPLAYS exactly. ---- */
function rngFrom(seed) { let a = seed >>> 0; return () => { a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const isPenLike = st => st.tool === 'pen' || st.tool === 'eraser';
const layersFor = st => st.layer === 'sketch' ? [S.layers.sketch] : (isPenLike(st) ? [S.layers.art, S.layers.lines] : [S.layers.art]);
const mid = (a, b) => ({ x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 });
function penPrep(c, L, st, opaque) {
  c.save(); c.globalCompositeOperation = st.tool === 'eraser' ? 'destination-out' : 'source-over'; c.strokeStyle = c.fillStyle = st.color;
  c.globalAlpha = (st.tool === 'eraser' || opaque) ? 1 : st.alpha; c.lineCap = 'round'; c.lineJoin = 'round'; c.lineWidth = st.w * L.k;
}
function paintPenFull(L, st, opaque) {             // CANONICAL rendering of a pen/eraser stroke (used for the final stroke and for every replay)
  const c = L.bctx, q = st.pts.map(p => toPx(p, L)); penPrep(c, L, st, opaque);
  if (q.length === 1) { c.beginPath(); c.arc(q[0].x, q[0].y, c.lineWidth / 2, 0, TAU); c.fill(); }
  else { c.beginPath(); c.moveTo(q[0].x, q[0].y);
    if (q.length === 2) c.lineTo(q[1].x, q[1].y);
    else { for (let i = 1; i < q.length - 1; i++) { const m = mid(q[i], q[i + 1]); c.quadraticCurveTo(q[i].x, q[i].y, m.x, m.y); } c.lineTo(q[q.length - 1].x, q[q.length - 1].y); }
    c.stroke(); }
  c.restore();
}
function paintPenPiece(c, L, st, j, opaque) {       // LIVE preview of the piece of a pen/eraser stroke that ends at point j (into a VIEW, never the truth)
  const q = st.pts.slice(Math.max(0, j - 2), j + 1).map(p => toPx(p, L)); penPrep(c, L, st, opaque); c.beginPath();
  if (j === 0) { c.arc(q[0].x, q[0].y, c.lineWidth / 2, 0, TAU); c.fill(); }
  else if (j === 1) { c.moveTo(q[0].x, q[0].y); c.lineTo(q[1].x, q[1].y); c.stroke(); }
  else { const m1 = mid(q[0], q[1]), m2 = mid(q[1], q[2]); c.moveTo(m1.x, m1.y); c.quadraticCurveTo(q[1].x, q[1].y, m2.x, m2.y); c.lineTo(q[2].x, q[2].y); c.stroke(); }
  c.restore();
}
const SPACING = { hatch: 0.3, cross: 0.45, stipple: 0.5, scales: 0.85, waves: 0.8 };
const spacingPx = (st, D) => st.tool === 'dot' ? Math.max(D * 1.15, 2) : Math.max(D * SPACING[st.pattern], 2);
function stamp(c, st, x, y, D, idx) {                // patterns are defined horizontally, then turned by the texture angle (counter-clockwise)
  c.save(); c.globalAlpha = st.alpha; c.strokeStyle = c.fillStyle = st.color; c.translate(x, y);
  if (st.tool === 'dot') { c.beginPath(); c.arc(0, 0, D / 2, 0, TAU); c.fill(); c.restore(); return; }
  c.rotate(-(st.angle || 0) * PI / 180); c.lineWidth = Math.max(1.3, D * 0.07); c.lineCap = 'round';
  switch (st.pattern) {
    case 'hatch': c.beginPath(); c.moveTo(-D * .45, 0); c.lineTo(D * .45, 0); c.stroke(); break;
    case 'cross': c.beginPath(); c.moveTo(-D * .45, 0); c.lineTo(D * .45, 0); c.moveTo(0, -D * .45); c.lineTo(0, D * .45); c.stroke(); break;
    case 'stipple': { const r = rngFrom(st.seed + idx * 7919); for (let j = 0; j < 4; j++) { const a = r() * TAU, d = Math.sqrt(r()) * D * .5; c.beginPath(); c.arc(Math.cos(a) * d, Math.sin(a) * d, Math.max(.9, D * .045), 0, TAU); c.fill(); } break; }
    case 'scales': c.beginPath(); c.arc(0, 0, D * .38, 0, PI); c.stroke(); break;
    case 'waves': c.beginPath(); c.moveTo(-D * .5, 0); c.bezierCurveTo(-D * .25, -D * .35, D * .25, D * .35, D * .5, 0); c.stroke(); break;
  }
  c.restore();
}
const newWalker = () => ({ carry: 0, idx: 0 });
function stampStart(L, st, p, wk, c) { const q = toPx(p, L), D = st.w * L.k; stamp(c || L.bctx, st, q.x, q.y, D, wk.idx++); wk.carry = spacingPx(st, D); }
function stampSeg(L, st, a, b, wk, c) {
  const p = toPx(a, L), q = toPx(b, L), D = st.w * L.k, d = Math.hypot(q.x - p.x, q.y - p.y), sp = spacingPx(st, D);
  if (d < wk.carry) { wk.carry -= d; return; }
  let t = wk.carry; while (t <= d) { stamp(c || L.bctx, st, p.x + (q.x - p.x) * t / d, p.y + (q.y - p.y) * t / d, D, wk.idx++); t += sp; } wk.carry = t - d;
}
function paintStrokeCanonical(st) {
  if (st.layer === 'sketch') { paintPenFull(S.layers.sketch, st, true); return; }
  if (isPenLike(st)) { paintPenFull(S.layers.art, st, false); paintPenFull(S.layers.lines, st, true); return; }
  const L = S.layers.art, wk = newWalker(); stampStart(L, st, st.pts[0], wk); for (let i = 1; i < st.pts.length; i++) stampSeg(L, st, st.pts[i - 1], st.pts[i], wk);
}

const sizeKey = () => shaping() ? 'sketch' : (S.tool === 'fill' ? 'pen' : S.tool);   // which remembered size the slider edits
const widthFor = key => { const [a, b] = SIZE_RANGE[key], v = S.sizes[key]; return (a + b * v * v) * S.unit; };
function newStroke() {
  if (shaping()) return Object.assign({ kind: 'stroke', layer: 'sketch', tool: S.sketchTool, color: SKETCH_COLOR, alpha: 1, w: widthFor('sketch') * (S.sketchTool === 'eraser' ? 1.6 : 1), pts: [] }, S.mode === 'polygon' ? { stage: 'polygon' } : {});   // (CR3: Polygon too)
  return { kind: 'stroke', layer: 'art', tool: S.tool, pattern: S.pattern, angle: S.angle, seed: (Math.random() * 4294967295) >>> 0, color: S.color,
    alpha: S.tool === 'eraser' ? 1 : Math.max(MIN_ALPHA, S.opac[S.tool] == null ? 1 : S.opac[S.tool]), w: widthFor(S.tool), pts: [] };
}

/* ---- Fill: flood fill on a 1024² grid. Boundaries = outside the CURRENT tile, PEN lines, and (optionally) sketch lines.
 *      The region's old colour is CLEARED first and the new colour (with its opacity) painted into the FILLS layer, which sits
 *      beneath every line — so a region can always be recoloured, and no halo shows beside a line. ---- */
function maskPathFor(snap, L) {
  const path = new Path2D(); let first = true;
  snap.forEach(pts => { for (let k = 0; k < N; k++) { const q = toPx(pts[k], L); first ? path.moveTo(q.x, q.y) : path.lineTo(q.x, q.y); first = false; } });
  path.closePath(); return path;
}
function doFill(a, snap) {
  const F = S.layers.fills, G = F.size; S.flood = S.flood || mkCanvas(G); S.flood2 = S.flood2 || mkCanvas(G);
  const tc = S.flood.getContext('2d', { willReadFrequently: true }), mask = maskPathFor(snap, F);
  const alphaOf = draw => { tc.setTransform(1, 0, 0, 1, 0, 0); tc.clearRect(0, 0, G, G); draw(); const d = tc.getImageData(0, 0, G, G).data, out = new Uint8Array(G * G); for (let i = 0; i < out.length; i++) out[i] = d[i * 4 + 3]; return out; };
  const inside = alphaOf(() => { tc.fillStyle = '#fff'; tc.fill(mask); });
  const lines = alphaOf(() => tc.drawImage(S.layers.lines.big, 0, 0));
  const sk = a.respectSketch ? alphaOf(() => tc.drawImage(S.layers.sketch.big, 0, 0, G, G)) : null;
  const barrier = i => inside[i] < 128 || lines[i] > 24 || (sk && sk[i] > 24);
  const sp = toPx(a.seed, F); let sx = Math.round(sp.x), sy = Math.round(sp.y), seed = -1;
  for (let r = 0; r <= 4 && seed < 0; r++) for (let dy = -r; dy <= r && seed < 0; dy++) for (let dx = -r; dx <= r; dx++) {
    const x = sx + dx, y = sy + dy; if (x < 0 || y < 0 || x >= G || y >= G) continue; if (!barrier(y * G + x)) { seed = y * G + x; break; } }
  if (seed < 0) return false;
  const region = new Uint8Array(G * G), stack = [seed]; region[seed] = 1; let count = 0;
  while (stack.length) { const i = stack.pop(); count++; const x = i % G, y = (i - x) / G;
    if (x > 0 && !region[i - 1] && !barrier(i - 1)) { region[i - 1] = 1; stack.push(i - 1); }
    if (x < G - 1 && !region[i + 1] && !barrier(i + 1)) { region[i + 1] = 1; stack.push(i + 1); }
    if (y > 0 && !region[i - G] && !barrier(i - G)) { region[i - G] = 1; stack.push(i - G); }
    if (y < G - 1 && !region[i + G] && !barrier(i + G)) { region[i + G] = 1; stack.push(i + G); } }
  const grown = region.slice();
  for (let i = 0; i < region.length; i++) if (region[i]) { const x = i % G;
    if (x > 0) grown[i - 1] = 1; if (x < G - 1) grown[i + 1] = 1; if (i >= G) grown[i - G] = 1; if (i < G * G - G) grown[i + G] = 1; }
  if (a.edge) {                     // CR2: a new fill also reaches 3 grid pixels PAST the tile edge (outside the tile only), so where tiles meet the colour runs
    let front = [];                 // under the neighbour's edge instead of fading out before it: no light hairline with the Tessellate outline at 0.
    for (let i = 0; i < grown.length; i++) if (grown[i] && inside[i] >= 128) { const x = i % G;   // (fills made before CR2 have no `edge` and stay exactly as they were)
      for (const j of [x > 0 ? i - 1 : -1, x < G - 1 ? i + 1 : -1, i - G, i + G]) if (j >= 0 && j < grown.length && !grown[j] && inside[j] < 128) { grown[j] = 1; front.push(j); } }
    for (let pass = 1; pass < 3; pass++) { const next = []; for (const i of front) { const x = i % G;
      for (const j of [x > 0 ? i - 1 : -1, x < G - 1 ? i + 1 : -1, i - G, i + G]) if (j >= 0 && j < grown.length && !grown[j] && inside[j] < 128) { grown[j] = 1; next.push(j); } } front = next; }
  }
  const n = parseInt(a.color.slice(1), 16), R = n >> 16, Gc = (n >> 8) & 255, B = n & 255, fc = S.flood2.getContext('2d'), al = Math.round(255 * Math.max(MIN_ALPHA, a.alpha == null ? 1 : a.alpha));
  const img = (fn) => { const id = fc.createImageData(G, G); for (let i = 0; i < grown.length; i++) if (grown[i]) fn(id.data, i * 4); fc.putImageData(id, 0, 0); };
  const c = F.bctx; c.save(); c.setTransform(1, 0, 0, 1, 0, 0); if (!a.edge) c.clip(mask); c.imageSmoothingEnabled = false;
  img((d, o) => { d[o] = d[o + 1] = d[o + 2] = 0; d[o + 3] = 255; }); c.globalCompositeOperation = 'destination-out'; c.drawImage(S.flood2, 0, 0);           // clear the old colour
  img((d, o) => { d[o] = R; d[o + 1] = Gc; d[o + 2] = B; d[o + 3] = al; }); c.globalCompositeOperation = 'source-over'; c.drawImage(S.flood2, 0, 0);       // paint the new one
  c.restore(); touchLayers(); return count > 0;
}

/* ---------------- history: ONE chronological list (sketch strokes, art strokes/erases/dots/textures, fills, shape pulls, shape resets).
 *                  Composition (Tessellate display choices) and the Reference image are deliberately NOT in this history. ---------------- */
function pushAction(a) { S.history.length = S.hp; S.history.push(a); S.hp = S.history.length; syncUndo(); }
function syncUndo() {
  const u = S.hp === 0, r = S.hp >= S.history.length; $('undo').disabled = u; $('redo').disabled = r;
  $('sb-undo').disabled = u; $('sb-redo').disabled = r; $('sb-redo').classList.toggle('gone', r);   // Shape bar: Redo shows only after an Undo (its place is kept, so nothing shifts)
}
function rebuildLayers() {                      // replay, tracking the boundary as it was at each step (fills depend on it)
  Object.values(S.layers).forEach(clearLayer); let snap = S.initialSnap;
  for (let i = 0; i < S.hp; i++) { const a = S.history[i];
    if (a.kind === 'shape') snap = a.after; else if (a.kind === 'stroke') paintStrokeCanonical(a); else if (a.kind === 'fill') doFill(a, a.snap || snap); }
  syncAllViews(); S.artVer++; touchLayers();
}
function applyHistory(delta) {
  if (work) cancelWork();
  if (delta < 0 && S.hp > 0) { const a = S.history[--S.hp]; if (a.kind === 'shape') restoreSnapshot(a.before); else rebuildLayers(); }
  else if (delta > 0 && S.hp < S.history.length) { const a = S.history[S.hp++]; if (a.kind === 'shape') restoreSnapshot(a.after); else rebuildLayers(); }
  syncUndo(); invalidate();
}
const hasArt = () => S.history.slice(0, S.hp).some(a => a.kind === 'fill' || (a.kind === 'stroke' && a.layer === 'art' && a.tool !== 'eraser'));

/* ---------------- COMPOSITION support (Tessellate display only) ---------------- */
function getTint(color) {                        // a flat-colour silhouette of the FILLS layer (figure recolouring); cached per artwork version
  const h = S.tint.get(color); if (h && h.ver === S.layerVer) return h.canvas;
  const F = S.layers.fills, c = h ? h.canvas : mkCanvas(F.size), x = c.getContext('2d'); x.globalCompositeOperation = 'source-over'; x.clearRect(0, 0, F.size, F.size); x.drawImage(F.view, 0, 0);
  x.globalCompositeOperation = 'source-in'; x.fillStyle = color; x.fillRect(0, 0, F.size, F.size); x.globalCompositeOperation = 'source-over'; S.tint.set(color, { canvas: c, ver: S.layerVer }); return c;
}
const GROUPING_NAME = { same: 'All tiles', alt: 'Alternate', row: 'Row', col: 'Column' };
function gridIndex(i) {
  if (!S.poly) { const [cw, ch] = GRID[S.cellKind], c = S.centW[i], c0 = S.field.c0; return { col: Math.round((c.x - c0.x) / cw), row: Math.round((c.y - c0.y) / ch) }; }
  // v5.1: a moved cage is a parallelogram or a rectangle, so a square row/column pitch no longer fits. Use the tiling's own repeat: the
  // offsets from the cell centre to its neighbours across the two edge pairs. Every tile's image of the cell centre is an exact integer
  // combination of them (for the square this is exactly the old 1 × 1 grid).
  const B = S.gridBasis || (S.gridBasis = latticeBasis()), c0 = S.field.c0, q = mapp(S.field.list[i], c0), dx = q.x - c0.x, dy = q.y - c0.y;
  return { col: Math.round((dx * B.b2.y - dy * B.b2.x) / B.det), row: Math.round((B.b1.x * dy - B.b1.y * dx) / B.det) };
}
function latticeBasis() {
  const c0 = S.field.c0, d = polyRels().map(r => { const q = mapp(r.m, c0); return P(q.x - c0.x, q.y - c0.y); }), h = v => Math.abs(v.x) / Math.hypot(v.x, v.y);
  let [b1, b2] = h(d[0]) >= h(d[1]) ? [d[0], d[1]] : [d[1], d[0]];          // b1 = the more horizontal repeat (columns), b2 = the other (rows)
  if (b1.x < 0) b1 = P(-b1.x, -b1.y); if (b2.y < 0) b2 = P(-b2.x, -b2.y);
  return { b1, b2, det: b1.x * b2.y - b1.y * b2.x };
}
function groupOf(i, mode) {                      // which group does tile i belong to under the given grouping?
  mode = mode || S.treat; const g = gridIndex(i), mod = (v, n) => ((v % n) + n) % n;
  if (mode === 'same') return { key: 'all', label: 'All tiles' };
  if (mode === 'alt') { const p = mod(g.col + g.row, 2); return { key: 'p' + p, label: 'Alternate · group ' + (p ? 'B' : 'A') }; }
  if (mode === 'row') return { key: 'r' + g.row, label: 'Row ' + g.row };
  return { key: 'c' + g.col, label: 'Column ' + g.col };
}
const compOf = i => { const g = groupOf(i); return S.comp[S.treat][g.key] || null; };
const scaleAbout = (c, s) => [s, 0, 0, s, c.x * (1 - s), c.y * (1 - s)];
const compModified = () => Object.values(S.comp).some(m => Object.values(m).some(p => p.hidden || (p.scale != null && Math.abs(p.scale - 1) > 1e-6)));

/* ---------------- entering a construction ---------------- */
function makeField() {
  for (const f of [8, 6.5, 5, 4]) { const t = E.makeTiling(f); if (t.list.length < 650 || f === 4) return { t, f }; }
}
function start(id, opts) {
  S.consId = id; E.build(id);
  const { t, f } = makeField(); S.field = t; S.fieldCull = f;
  S.cellKind = id === 'rotation-tri' ? 'triangle' : id === 'reflection' ? 'rhombus' : 'square';
  S.origVerts = E.state.cons.verts.map(p => P(p.x, p.y));        // original cage, stored independently of the live boundary
  S.orientCue = orientCueNow();   // some neighbours turned/mirrored (not pure translation)
  makeInk(); S.history = []; S.hp = 0; S.hl = null; S.shape = null; S.stroke = null; S.artVer = 0; S.camByMode = {}; work = null; nav = refNav = null;
  S.comp = { same: {}, alt: {}, row: {}, col: {} }; S.sel = null; S.ref.img = null; S.ref.adjust = false; S.ref.locked = false; syncUndo();
  S.outline = OUTLINE_DEFAULT; S.showSketch = false; syncCR2UI();                                  // CR2
  // v5.0: a square-grid start opens in POLYGON (no transformation chosen yet: the plain square grid); triangle / rhombus open in Shape as before
  S.poly = opts && opts.polygon ? { family: null, nodes: {}, hist: [{ consId: id, family: null, nodes: {} }], hp: 0, sel: null } : null;
  S.shapeBaseKey = null; S.refined = null; S.recovery = null; S.restartOK = false; S.pendingPoly = null;
  S.cageNow = null; S.engineId = id; S.unit = S.field.size; S.gridBasis = null; S.lockFlash = null;
  rebuildPath(); rebuildCentroids(); E.setRadius(influenceRadius(S.influenceV)); S.initialSnap = snapshot();
  const mode = S.poly ? 'polygon' : 'shape';
  $('entry').hidden = true; S.mode = mode; resize(); fitCamera(); setMode(mode, true); syncRefUI(); syncPolyUI(); syncRestoreUI(); updateTitle();
  if (!(opts && opts.quiet)) toast(S.poly ? 'Polygon · choose how the tiles repeat' : cardInfo(id).short, 2000);   // the construction name: briefly on entry, and as the menu's heading (CR1: not when a saved project is rebuilt)
}
const startPolygon = () => {                  // CR3: the square Polygon starts with Translation chosen (Free polygon, later, will start with none)
  start('translation', { polygon: true, quiet: true });
  const st = { consId: 'translation', family: 'translate', cage: null, nodes: {} }; S.poly.hist[0] = st; applyPolyState(st);
  if (!S.seenHint.polygon) { S.seenHint.polygon = true; toast(HINTS.polygon, 3600); } else toast('Square · Translate', 1600);
};
function updateTitle() { $('menu-title').textContent = (S.poly && !S.poly.family ? 'Polygon' : cardInfo(S.consId).short) + (compModified() ? ' · composed' : ''); }

/* ---------------- rendering ---------------- */
const shaping = () => S.mode === 'shape' || S.mode === 'polygon';     // Polygon draws the tiles exactly as Shape does
function ghostAlpha() { return S.ghost === 'off' ? 0 : S.ghost === 'clear' ? 1 : (shaping() ? SHAPE_GHOST : ILLUSTRATE_GHOST); }
function layerAlphas() {          // how loud each layer is in each mode
  // CR2 sketch rule: shown in Polygon and Shape; hidden in Illustrate (unless Show sketch, for tracing) and in Tessellate. Exports: only Polygon
  // and Shape may include it (the sheet's Sketch switch); a finished-artwork export (Illustrate, Tessellate) never does.
  const sk = EXP ? !!EXP.sketch : true;
  if (S.mode === 'shape') { const dragging = !EXP && work && work.type === 'shape'; return { sketch: sk ? (dragging ? SHAPE_DRAG_FADE : 1) : 0, art: dragging ? 0.2 : 0.5 }; }
  if (S.mode === 'polygon') return { sketch: sk ? (S.polyTool === 'sketch' ? 1 : 0.45) : 0, art: 0.35 };   // (CR3: full strength while sketching)
  if (S.mode === 'illustrate') return { sketch: !EXP && S.showSketch ? 0.4 : 0, art: 1 };
  return { sketch: 0, art: 1 };
}
// RENDER CACHE. Everything that is the same in every tile (fills + sketch + art + the orientation 'F') is composited ONCE into a single raster in
// cell coordinates and re-used by every tile, so a tile costs one drawImage instead of three. Composites read ONLY the GPU views. One is BUILT when a
// layer's loudness (mode / drag fade) or a group's figure tint first needs it; when artwork changes, every cached composite is PATCHED inside the
// changed rectangle only (paintComposite with r) — the same draw calls, clipped, so a patch equals a rebuild. Boundary deformation never touches it.
function paintComposite(e, r) {
  const c = e.c, n = c.width, x = c.getContext('2d'), i = S.ink, k = n / i.side, L = S.layers, q = r ? rPx(r, n, 2) : { x: 0, y: 0, w: n, h: n }; if (!q) return;
  if (PERF) PERF.n(r ? 'patch' : 'comp');
  x.save(); x.setTransform(1, 0, 0, 1, 0, 0); x.globalAlpha = 1; x.globalCompositeOperation = 'source-over';
  if (r) { x.beginPath(); x.rect(q.x, q.y, q.w, q.h); x.clip(); }
  x.clearRect(q.x, q.y, q.w, q.h); x.imageSmoothingEnabled = true; x.imageSmoothingQuality = 'high';
  if (e.mark) { const c0 = S.field.c0, z = S.unit, segs = [[-0.08, -0.15, -0.08, 0.15], [-0.08, 0.15, 0.12, 0.15], [-0.08, 0.02, 0.07, 0.02]];
    x.save(); x.setTransform(k, 0, 0, -k, -i.x0 * k, i.y1 * k); x.globalAlpha = e.mark; x.strokeStyle = COLORS.line; x.lineWidth = 0.012 * z; x.lineCap = 'round'; x.beginPath();
    segs.forEach(s => { x.moveTo(c0.x + s[0] * z, c0.y + s[1] * z); x.lineTo(c0.x + s[2] * z, c0.y + s[3] * z); }); x.stroke(); x.restore(); }
  const layer = (img, alpha) => {           // whole image, or (patch) an aligned source window with a margin so edge resampling equals a full draw
    if (alpha <= 0) return; x.globalAlpha = alpha; if (!r) { x.drawImage(img, 0, 0, n, n); return; }
    const sc = img.width / n, al = sc < 1 ? Math.round(1 / sc) : 1, M = 8;
    const d0x = Math.floor(Math.max(0, q.x - M) / al) * al, d0y = Math.floor(Math.max(0, q.y - M) / al) * al, d1x = Math.min(n, Math.ceil((q.x + q.w + M) / al) * al), d1y = Math.min(n, Math.ceil((q.y + q.h + M) / al) * al);
    x.drawImage(img, d0x * sc, d0y * sc, (d1x - d0x) * sc, (d1y - d0y) * sc, d0x, d0y, d1x - d0x, d1y - d0y);
  };
  layer(e.tint ? getTint(e.tint) : L.fills.view, e.A.art); layer(L.sketch.view, e.A.sketch); layer(L.art.view, e.A.art);
  x.restore();
}
function patchComposites(r) {          // patch the composites in use (this or the previous frame); recycle the rest — they are rebuilt if needed again
  S.compCache.forEach((e, key) => { if (S.frameNo - e.used <= 1) { paintComposite(e, r); return; }
    S.compCache.delete(key); const pool = S.compPool[e.c.width === INK_BIG ? 'big' : 'small']; if (pool.length < 3) pool.push(e.c); });
}
function getComposite(big, A, tint, mark) {
  const key = [A.sketch, A.art, tint || '', mark || 0, big ? 1 : 0, mark ? S.field.c0.x + ',' + S.field.c0.y : ''].join('|'); let e = S.compCache.get(key);   // v5.1: the F sits at the cage centre
  if (e) { S.compCache.delete(key); S.compCache.set(key, e); e.used = S.frameNo; return e.c; }                  // most recently used goes last
  while (S.compCache.size > 4) { const old = S.compCache.keys().next().value, oc = S.compCache.get(old).c; S.compCache.delete(old); const pool = S.compPool[oc.width === INK_BIG ? 'big' : 'small']; if (pool.length < 3) pool.push(oc); }   // recycle, never churn allocations
  const n = big ? INK_BIG : INK_SMALL; e = { c: S.compPool[big ? 'big' : 'small'].pop() || mkCanvas(n), A: { sketch: A.sketch, art: A.art }, tint: tint || null, mark: mark || 0, used: S.frameNo };
  paintComposite(e, null); S.compCache.set(key, e); return e.c;
}
function drawComposite(sizePx, A, tint, mark) {
  const big = sizePx * S.dpr > 512, c = getComposite(big, A, tint, mark), i = S.ink, sc = (big ? INK_BIG : INK_SMALL) / i.side;
  ctx.save(); ctx.translate(i.x0, i.y1); ctx.scale(1 / sc, -1 / sc); ctx.imageSmoothingEnabled = true; ctx.imageSmoothingQuality = S.fast && S.opt.fastSampling ? 'low' : 'high'; ctx.drawImage(c, 0, 0); ctx.restore();
}
// A small asymmetric 'F' in the cell frame (now baked into the composite above); carried by every tile's transform so it turns / flips with the tile.
// COMPOSITION is applied here, at DRAW time only: a tile's group may recolour its background / figure fills, change opacity, hide, or scale it about
// the tile centroid. The scale matrix is composed in the CELL frame BEFORE the tile's own matrix, so turning/mirroring is preserved. Geometry is never touched.
function drawTile(m, alpha, active, i, A, artEmpty, part) {
  // CR2: `part` lets Tessellate draw in passes when the outline is (almost) 0: every tile's base, then every tile's artwork, then the outlines,
  // each tile reaching ¾ of a device pixel past its edge, so no light or dark hairline can appear where tiles meet. Otherwise ('all') as in v5.2.
  part = part || 'all'; const all = part === 'all';
  const tess = S.mode === 'tessellate', cp = tess ? compOf(i) : null, size = S.field.size * S.cam.s;
  if (cp && cp.hidden) {                                                 // hidden: draw only a faint outline so the tile can be tapped and shown again
    if (EXP || !(all || part === 'line')) return;                        // (CR2: that outline is a control, not part of an exported picture)
    ctx.save(); ctx.setTransform(...mmul(worldToScreenMatrix(), m)); ctx.globalAlpha = 0.18; ctx.setLineDash([4 / S.cam.s, 5 / S.cam.s]); ctx.strokeStyle = '#fff'; ctx.lineWidth = 1 / S.cam.s; ctx.stroke(S.path); ctx.restore(); drawSelection(m, i); return;
  }
  const mm = cp && cp.scale != null && Math.abs(cp.scale - 1) > 1e-6 ? mmul(m, scaleAbout(S.cent, cp.scale)) : m;
  ctx.save(); ctx.globalAlpha = alpha * (cp && cp.alpha != null ? cp.alpha : 1); ctx.setTransform(...mmul(worldToScreenMatrix(), mm));
  const tp = all ? S.path : bleedPath();
  if (all || part === 'bg') { ctx.fillStyle = tess ? ((cp && cp.bg) || COLORS.fill) : (S.orientCue && shaping() && det(m) < 0 ? COLORS.fillMirror : COLORS.fill); ctx.fill(tp); }
  if (all || part === 'art') {
    ctx.save(); ctx.clip(tp);
    const poly = S.mode === 'polygon';         // v5.1: in Polygon the cage (and so the F's place) can change every frame: draw the F as lines, not in the cached composite
    drawComposite(size, A, cp && cp.fig ? cp.fig : null, poly ? 0 : S.orientCue ? (shaping() ? MARK_ALPHA.shape : tess && artEmpty ? MARK_ALPHA.tessellate : 0) : 0);
    if (poly && S.orientCue) drawMarkLines(MARK_ALPHA.shape);
    ctx.restore();
  }
  if (all || part === 'line') {
    const lw = tess ? outlineWorld() : (active ? (shaping() ? 2.4 : 1.6) : 1.1) / S.cam.s;        // CR2: Tessellate's outline is part of the artwork (adjustable, 0 = none)
    if (lw > 0) { ctx.lineJoin = 'round'; ctx.strokeStyle = COLORS.line; ctx.lineWidth = lw; ctx.stroke(S.path); }
  }
  ctx.restore(); if (tess && !EXP && (all || part === 'line')) drawSelection(mm, i);
}
const thinOutline = () => S.mode === 'tessellate' && outlineWorld() * S.cam.s * S.dpr < 1.5;   // CR2: below 1.5 device pixels the outline no longer hides the tile edges
function drawMarkLines(alpha) {          // the orientation F in the cell frame (the current transform), exactly as the composite draws it
  const c0 = S.field.c0, z = S.unit, segs = [[-0.08, -0.15, -0.08, 0.15], [-0.08, 0.15, 0.12, 0.15], [-0.08, 0.02, 0.07, 0.02]];
  ctx.save(); ctx.globalAlpha = alpha; ctx.strokeStyle = COLORS.line; ctx.lineWidth = 0.012 * z; ctx.lineCap = 'round'; ctx.beginPath();
  segs.forEach(g => { ctx.moveTo(c0.x + g[0] * z, c0.y + g[1] * z); ctx.lineTo(c0.x + g[2] * z, c0.y + g[3] * z); }); ctx.stroke(); ctx.restore();
}
function drawSelection(m, i) {
  if (!S.sel || S.sel.mode !== S.treat || groupOf(i).key !== S.sel.key) return;
  ctx.save(); ctx.setTransform(...mmul(worldToScreenMatrix(), m)); ctx.lineJoin = 'round'; ctx.strokeStyle = COLORS.edgeA; ctx.lineWidth = 3 / S.cam.s; ctx.globalAlpha = 0.95; ctx.stroke(S.path); ctx.restore();
}
function refSource() {                  // a copy of the reference at (about) its on-screen resolution, in power-of-two steps, so it is rarely rebuilt
  const R = S.ref, long = Math.max(R.img.width, R.img.height), onScreen = R.sc * S.cam.s * S.dpr * long; let t = 256; while (t < onScreen && t < long) t *= 2; t = Math.min(t, long);
  if (R.cache && R.cacheLong === t && R.cacheSrc === R.img) return R.cache;
  if (t >= long) R.cache = R.img; else { const k = t / long, c = document.createElement('canvas'); c.width = Math.max(1, Math.round(R.img.width * k)); c.height = Math.max(1, Math.round(R.img.height * k)); const x = c.getContext('2d'); x.imageSmoothingQuality = 'high'; x.drawImage(R.img, 0, 0, c.width, c.height); R.cache = c; }
  R.cacheLong = t; R.cacheSrc = R.img; return R.cache;
}
function drawReference() {
  const R = S.ref; if (!R.img || !R.visible || S.mode !== 'shape') return;
  const src = S.opt.refCache ? refSource() : R.img, f = R.img.width / src.width;
  ctx.save(); ctx.setTransform(...worldToScreenMatrix()); ctx.globalAlpha = R.alpha; ctx.translate(R.x, R.y); ctx.rotate(R.rot); ctx.scale(R.sc * f, -R.sc * f);
  ctx.imageSmoothingEnabled = true; ctx.imageSmoothingQuality = S.opt.refCache ? (S.fast && S.opt.fastSampling ? 'low' : 'medium') : 'high'; ctx.drawImage(src, -src.width / 2, -src.height / 2);
  if (R.adjust && !R.locked) { ctx.globalAlpha = 0.9; ctx.strokeStyle = COLORS.edgeB; ctx.lineWidth = 2 / (R.sc * S.cam.s * f); ctx.setLineDash([8 / (R.sc * S.cam.s * f), 6 / (R.sc * S.cam.s * f)]); ctx.strokeRect(-src.width / 2, -src.height / 2, src.width, src.height); }
  ctx.restore();
}
// LIVE STROKES. While the finger is down a stroke only collects points; once per frame the new piece is painted into the GPU VIEW(s) and every
// composite is patched in that small rectangle. The TRUTH layers are painted once, canonically, when the finger lifts (exactly as v4 did), and the
// views then copy the truth in the stroke's rectangle — so what stays on screen is the canonical, replayable result.
const viewsFor = st => st.layer === 'sketch' ? [S.layers.sketch] : [S.layers.art];
const isTranslucentPen = st => st.tool === 'pen' && st.alpha < 1 && st.layer === 'art';
const strokePad = st => st.w * (isPenLike(st) ? 0.6 : 1.4) + 3 * S.ink.side / INK_BIG;
function takeMask() { const c = S.maskPool || mkCanvas(INK_BIG); S.maskPool = null; c.getContext('2d').clearRect(0, 0, INK_BIG, INK_BIG); return c; }
function flushStroke() {
  const s = S.stroke; if (!s) return; const st = s.st, n = st.pts.length; if (s.painted >= n) return;
  const r = rEmpty(), pad = strokePad(st);
  for (let j = Math.max(0, s.painted - 2); j < n; j++) rAddPt(r, st.pts[j], pad);
  s.views.forEach(L => {
    if (!isPenLike(st)) { for (let j = s.painted; j < n; j++) j === 0 ? stampStart(L, st, st.pts[0], s.wk, L.vctx) : stampSeg(L, st, st.pts[j - 1], st.pts[j], s.wk, L.vctx); return; }
    if (!s.mask) { for (let j = s.painted; j < n; j++) paintPenPiece(L.vctx, L, st, j, false); return; }
    // translucent pen: the stroke is drawn OPAQUE into a mask, then (inside r) the view = truth-before-stroke + mask × opacity — joins never darken
    const mc = s.mask.getContext('2d'); for (let j = s.painted; j < n; j++) paintPenPiece(mc, L, st, j, true);
    const q = rPx(r, L.size, 2); if (!q) return; L.vctx.putImageData(L.bctx.getImageData(q.x, q.y, q.w, q.h), q.x, q.y);
    L.vctx.save(); L.vctx.beginPath(); L.vctx.rect(q.x, q.y, q.w, q.h); L.vctx.clip(); L.vctx.globalAlpha = st.alpha; L.vctx.drawImage(s.mask, q.x, q.y, q.w, q.h, q.x, q.y, q.w, q.h); L.vctx.restore();
  });
  s.painted = n; rAdd(s.dirty, r); patchComposites(r);
}
function finishStroke(commit) {         // the finger lifted (commit) or the stroke was cancelled
  const s = S.stroke; S.stroke = null; if (!s) return; const pad = strokePad(s.st); s.st.pts.forEach(p => rAddPt(s.dirty, p, pad));
  if (commit) paintStrokeCanonical(s.st);                 // the TRUTH, painted once — identical to v4 and to any replay
  s.views.forEach(L => syncView(L, s.dirty)); patchComposites(s.dirty); if (s.mask) S.maskPool = s.mask; touchLayers();
}
function flushShapeMove() {                // boundary moves are applied ONCE per frame (the deformation is absolute from the gesture start, so the result is identical)
  const p = S.pendingMove; S.pendingMove = null; if (!p || !work || work.type !== 'shape') return;
  const w = s2w(p.x, p.y), g = S.shape.g; shapeMoveTo(P((w.x - g.start.x) * E.GAIN, (w.y - g.start.y) * E.GAIN)); rebuildPath();
}
/* ---- SELF-CROSSING GUARD (v5.0). The tiling proof checks that paired edges match — still true when an edge loops over itself — so it
 * cannot see a tile whose outline crosses itself (copies then overlap). A pull is applied as before; if the outline would cross, the pull
 * stops at the closest shape that does not (found by halving the step from the last good shape), so the edge stays with the finger up to
 * the point of contact. Only the stretch the pull can move is tested against the rest of the outline. ---- */
function segX(ax, ay, bx, by, cx, cy, dx, dy) {           // proper crossing of segments ab and cd
  const o1 = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax), o2 = (bx - ax) * (dy - ay) - (by - ay) * (dx - ax);
  if ((o1 > 1e-13 && o2 > 1e-13) || (o1 < -1e-13 && o2 < -1e-13)) return false;
  const o3 = (dx - cx) * (ay - cy) - (dy - cy) * (ax - cx), o4 = (dx - cx) * (by - cy) - (dy - cy) * (bx - cx);
  return ((o1 > 1e-13 && o2 < -1e-13) || (o1 < -1e-13 && o2 > 1e-13)) && ((o3 > 1e-13 && o4 < -1e-13) || (o3 < -1e-13 && o4 > 1e-13));
}
function movedRanges(g, whole) {          // the boundary segments a pull on edge g.e can move, as [edge, first, last] (segment k joins samples k and k+1)
  const st = E.state, n = st.edges.length, R = E.getRadius() * g.total, out = [];
  const general = whole || st.rels.some(r => r.self !== undefined || r.role === 'constraint');   // triangle / rhombus: test the whole linked edges
  let i0 = N, i1 = 0; for (let i = 1; i < N; i++) if (Math.abs(g.L[i] - g.s) < R) { if (i < i0) i0 = i; if (i > i1) i1 = i; }
  const lo = general ? 0 : Math.max(0, i0 - 1), hi = general ? N - 1 : Math.min(N - 1, i1);
  if (i0 > i1 && !general) return out;
  const seen = new Set([g.e]), q = [[g.e, false]]; out.push([g.e, lo, hi]);
  while (q.length) { const [e, flip] = q.shift(); st.rels.forEach(r => { if (r.self !== undefined) return; let d = -1;
    if (r.from === e) d = r.to; else if (r.to === e) d = r.from; if (d < 0 || seen.has(d)) return; seen.add(d); const f = flip !== !!r.rev;
    out.push(f ? [d, N - 1 - hi, N - 1 - lo] : [d, lo, hi]); q.push([d, f]); }); }
  void n; return out;
}
let gX = null, gY = null;
function outlineSimple(ranges) {          // does no moved segment properly cross any other segment of the tile outline?
  const poly = E.polygon(E.state.edges), n = poly.length; if (!gX || gX.length !== n) { gX = new Float64Array(n); gY = new Float64Array(n); }
  for (let i = 0; i < n; i++) { gX[i] = poly[i].x; gY[i] = poly[i].y; }
  for (const [e, lo, hi] of ranges) for (let k = lo; k <= hi; k++) {
    const i = e * N + k, i1 = (i + 1) % n, ax = gX[i], ay = gY[i], bx = gX[i1], by = gY[i1];
    const minx = ax < bx ? ax : bx, maxx = ax < bx ? bx : ax, miny = ay < by ? ay : by, maxy = ay < by ? by : ay;
    for (let j = 0; j < n; j++) {
      if (j === i || j === i1 || (j + 1) % n === i) continue;
      const j1 = (j + 1) % n, cx = gX[j], dx = gX[j1]; if ((cx < minx && dx < minx) || (cx > maxx && dx > maxx)) continue;
      const cy = gY[j], dy = gY[j1]; if ((cy < miny && dy < miny) || (cy > maxy && dy > maxy)) continue;
      if (segX(ax, ay, bx, by, cx, cy, dx, dy)) return false;
    }
  }
  return true;
}
const allRanges = () => E.state.edges.map((e, i) => [i, 0, N - 1]);
function shapeMoveTo(req) {               // apply a pull request (absolute from the gesture start), keeping the outline simple when the guard is on
  const sh = S.shape, g = sh.g; let use = req; E.updateGesture(g, req);
  if (sh.guard) {
    const t0 = performance.now(); sh.gs.frames++;
    if (!outlineSimple(sh.ranges)) {
      const a = sh.lastReq; let lo = 0, hi = 1;
      for (let k = 0; k < 7; k++) { const m = (lo + hi) / 2; E.updateGesture(g, P(a.x + (req.x - a.x) * m, a.y + (req.y - a.y) * m)); outlineSimple(sh.ranges) ? lo = m : hi = m; }
      use = P(a.x + (req.x - a.x) * lo, a.y + (req.y - a.y) * lo); E.updateGesture(g, use); sh.blocked = true; sh.gs.blocked++;
    } else sh.blocked = false;
    sh.lastReq = use; sh.gs.ms.push(performance.now() - t0);
  }
  sh.hitWorld = P(sh.c.x + use.x, sh.c.y + use.y);
}
function render(via) {
  if (!S.field || !S.path) return; const T0 = PERF ? performance.now() : 0; S.frameNo++;
  flushShapeMove(); flushPolyMove(); flushStroke(); S.fast = !!(work && (work.type === 'shape' || work.type === 'pnode' || work.type === 'pcorner' || work.type === 'pan' || work.type === 'refmove')) || !!nav || !!refNav;
  drawScene(canvas.width, canvas.height);
  placeRemoveChip();
  if (PERF) PERF.frame(T0, ctx, { work: work && work.type, nav: !!nav, mode: S.mode, via });
}
function drawScene(W, H) {             // CR2: the picture itself, drawn into `ctx` (the screen, or an export canvas with EXP set: then no reference photo, guides or handles)
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  if (EXP && EXP.transparent) ctx.clearRect(0, 0, W, H); else { ctx.fillStyle = COLORS.bg; ctx.fillRect(0, 0, W, H); }
  const list = S.field.list, tess = S.mode === 'tessellate', ga = tess ? 1 : ghostAlpha(), margin = 1.1 * S.field.size * S.cam.s, A = layerAlphas(), artEmpty = tess ? !hasArt() : false;
  const shown = [];
  if (ga > 0) for (let i = 1; i < list.length; i++) {
    const c = w2s(S.centW[i]); if (c.x < -margin || c.x > S.vw + margin || c.y < -margin || c.y > S.vh + margin) continue;
    shown.push(i); if (PERF && !EXP) PERF.n('tiles');
  }
  const pass = part => { shown.forEach(i => drawTile(list[i], ga, false, i, A, artEmpty, part)); drawTile(IDM, 1, true, 0, A, artEmpty, part); };
  if (thinOutline()) { pass('bg'); pass('art'); pass('line'); } else pass('all');
  if (EXP) return;
  drawReference();
  ctx.setTransform(S.dpr, 0, 0, S.dpr, 0, 0);
  if (S.showStart) drawStartShape();
  if (S.mode === 'shape') { drawHighlights(); drawInfluencePreview(); }
  if (S.mode === 'polygon') drawPolygonOverlay();
}
function drawStartShape() {
  ctx.save(); ctx.setLineDash([3, 6]); ctx.lineCap = 'round'; ctx.lineWidth = 1.6; ctx.strokeStyle = COLORS.start; ctx.globalAlpha = .85;
  ctx.beginPath(); S.origVerts.forEach((p, i) => { const q = w2s(p); i ? ctx.lineTo(q.x, q.y) : ctx.moveTo(q.x, q.y); }); ctx.closePath(); ctx.stroke(); ctx.restore();
}
function linkedEdges(e) {
  const out = new Set(); E.state.rels.forEach(r => { if (r.self !== undefined) { if (r.self === e) out.add(e); } else if (r.from === e) out.add(r.to); else if (r.to === e) out.add(r.from); }); return [...out];
}
function strokeEdge(ei, color, width, alpha) {
  const pts = edgesNow()[ei].pts; ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round'; ctx.strokeStyle = color; ctx.lineWidth = width; ctx.globalAlpha = alpha;
  ctx.beginPath(); pts.forEach((p, i) => { const q = w2s(p); i ? ctx.lineTo(q.x, q.y) : ctx.moveTo(q.x, q.y); }); ctx.stroke(); ctx.restore();
}
function drawHighlights() {
  const h = S.hl; if (!h) return;
  let a = 1; if (!h.active) { a = 1 - (performance.now() - h.t1) / 900; if (a <= 0) { S.hl = null; return; } invalidate(); }
  h.linked.forEach(ei => { if (ei !== h.edge) strokeEdge(ei, COLORS.edgeB, 6, a * 0.95); });
  strokeEdge(h.edge, COLORS.edgeA, 6, a);
  if (h.active && S.shape) {
    const p = S.shape.hitWorld; E.state.rels.forEach(r => {
      let q = null; if (r.self !== undefined) { if (r.self === h.edge) q = mapp(r.m, p); } else if (r.from === h.edge) q = mapp(r.m, p); else if (r.to === h.edge) q = mapp(r.inv, p);
      if (!q) return; const A = w2s(p), B = w2s(q); ctx.save(); ctx.setLineDash([4, 5]); ctx.strokeStyle = 'rgba(255,255,255,.75)'; ctx.lineWidth = 1.2; ctx.beginPath(); ctx.moveTo(A.x, A.y); ctx.lineTo(B.x, B.y); ctx.stroke();
      ctx.setLineDash([]); ctx.fillStyle = '#fff'; ctx.strokeStyle = '#1d1b18'; ctx.lineWidth = 1.5; [A, B].forEach(c => { ctx.beginPath(); ctx.arc(c.x, c.y, 5, 0, TAU); ctx.fill(); ctx.stroke(); }); ctx.restore(); });
  }
}

function drawInfluencePreview() {   // only while the Point ●── Wide slider moves (and briefly after): the stretch of each edge one pull would bend
  if (!S.inflPreview) return; const age = performance.now() - S.inflPreview, a = age < 700 ? 1 : 1 - (age - 700) / 500;
  if (a <= 0) { S.inflPreview = 0; return; } invalidate();
  const r = E.getRadius(); ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round'; ctx.strokeStyle = '#fff';
  edgesNow().forEach(e => { const L = E.cumLen(e.pts), m = L[N] / 2, lo = m - r * L[N], hi = m + r * L[N], pts = [pointAtArc(e.pts, L, lo)];
    for (let i = 1; i < N; i++) if (L[i] > lo && L[i] < hi) pts.push(e.pts[i]); pts.push(pointAtArc(e.pts, L, hi));
    ctx.beginPath(); pts.forEach((p, k) => { const q = w2s(p); k ? ctx.lineTo(q.x, q.y) : ctx.moveTo(q.x, q.y); });
    ctx.globalAlpha = 0.3 * a; ctx.lineWidth = 12; ctx.stroke(); ctx.globalAlpha = 0.95 * a; ctx.lineWidth = 3.5; ctx.stroke(); });
  ctx.restore();
}

/* ---------------- picking ---------------- */
function hitEdge(sx, sy) {
  let best = null;
  edgesNow().forEach((e, ei) => { for (let i = 0; i < N; i++) {
    const a = w2s(e.pts[i]), b = w2s(e.pts[i + 1]), abx = b.x - a.x, aby = b.y - a.y, l2 = abx * abx + aby * aby || 1e-9;
    const t = Math.max(0, Math.min(1, ((sx - a.x) * abx + (sy - a.y) * aby) / l2)), px = a.x + abx * t, py = a.y + aby * t, d = Math.hypot(sx - px, sy - py);
    if (d > HIT_PX || (best && d >= best.d)) continue;
    if ((i === 0 && t < 1e-6) || (i === N - 1 && t > 1 - 1e-6)) continue;
    best = { ei, i, t, d, w: s2w(px, py) }; } });
  return best;
}
// Which drawn tile contains this world point? Uses the CURRENT deformed tile (never the original polygon). `all` ignores the Neighbours: Off setting.
function tileAt(wp, all) {
  const order = S.field.list.map((m, i) => ({ i, d: Math.hypot(S.centW[i].x - wp.x, S.centW[i].y - wp.y) })).sort((a, b) => a.d - b.d).slice(0, 8);
  for (const { i } of order) {
    if (i > 0 && S.ghost === 'off' && !all) continue;
    const inv = minv(S.field.list[i]), lp = mapp(inv, wp);
    if (scratch.isPointInPath(S.path, lp.x, lp.y)) return { m: S.field.list[i], inv, i };
  }
  return null;
}

/* ---------------- one-finger work ---------------- */
function startWork(e, x, y) {
  if (S.mode === 'polygon' && S.polyTool !== 'sketch') { polyStart(e, x, y); return; }      // CR3: with Sketch on, Polygon draws like Shape › Sketch
  if (S.mode === 'tessellate') { work = { type: 'pan', tap: true, id: e.pointerId, t0: performance.now(), x0: x, y0: y, lx: x, ly: y }; return; }
  if (refActive()) { work = { type: 'refmove', id: e.pointerId, t0: performance.now(), lx: x, ly: y }; return; }
  if (S.mode === 'shape' && S.shapeTool === 'pull') {
    const h = hitEdge(x, y); if (!h) return;
    E.setRadius(influenceRadius(S.influenceV));
    const pts = edgesNow()[h.ei].pts, L = E.cumLen(pts), seg = L[h.i + 1] - L[h.i], s0 = grabArc(L, L[h.i] + seg * h.t), g = E.startGesture(h.ei, s0);
    g.start = h.w;                                   // the pull follows the finger from where it touched (unchanged)
    const c = pointAtArc(pts, L, s0);                // the boundary point the pull is centred on (= h.w unless snapped)
    S.shape = { g, before: snapshot(), hitWorld: c, c, ranges: movedRanges(g), lastReq: P(0, 0), blocked: false, gs: { frames: 0, blocked: 0, ms: [] } };
    S.shape.guard = S.guardShape && outlineSimple(allRanges());   // (a boundary that already crosses itself — impossible with the guard on — is left unguarded)
    S.hl = { edge: h.ei, linked: linkedEdges(h.ei), active: true, t1: 0 };
    work = { type: 'shape', id: e.pointerId, t0: performance.now() };
  } else if (S.mode === 'illustrate' && S.tool === 'fill') {
    work = { type: 'fill', id: e.pointerId, t0: performance.now(), x0: x, y0: y, lx: x, ly: y };
  } else {                                           // freehand: sketch (Shape › Sketch) or illustration (Illustrate)
    const t = tileAt(s2w(x, y)); if (!t) return;
    const st = newStroke(); st.pts = [mapp(t.inv, s2w(x, y))];
    S.stroke = { st, inv: t.inv, views: viewsFor(st), wk: newWalker(), painted: 0, dirty: rEmpty(), mask: isTranslucentPen(st) ? takeMask() : null };   // painted at the next frame
    work = { type: 'draw', id: e.pointerId, t0: performance.now() };
  }
  if (PERF && work) PERF.mark('start ' + work.type);
  invalidate();
}
function moveWork(x, y, coalesced) {
  if (work.type === 'draw') {                         // collect points only; they are painted once per frame (flushStroke)
    const { st, inv } = S.stroke, pts = coalesced && coalesced.length ? coalesced : [{ x, y }];
    pts.forEach(q => { const cp = mapp(inv, s2w(q.x, q.y)), last = st.pts[st.pts.length - 1];
      if (Math.hypot(cp.x - last.x, cp.y - last.y) < st.w * 0.12) return; st.pts.push(cp); });
  } else if (work.type === 'shape') {
    const w = s2w(x, y), g = S.shape.g;
    shapeMoveTo(P((w.x - g.start.x) * E.GAIN, (w.y - g.start.y) * E.GAIN));
    rebuildPath();
  } else if (work.type === 'pan') {
    S.cam.x -= (x - work.lx) / S.cam.s; S.cam.y += (y - work.ly) / S.cam.s; work.lx = x; work.ly = y; clampCam();
  } else if (work.type === 'refmove') {
    S.ref.x += (x - work.lx) / S.cam.s; S.ref.y -= (y - work.ly) / S.cam.s; work.lx = x; work.ly = y;
  } else if (work.type === 'fill') { work.lx = x; work.ly = y; }
  invalidate();
}
function applyFillAt(x, y) {
  const t = tileAt(s2w(x, y)); if (!t) return;
  // v5.0: the fill remembers the boundary it was made with (identical replay to v4.4, which tracked it through the history), so a later
  // Polygon change — which restarts the Shape history — can never change the artwork
  const act = { kind: 'fill', color: S.color, alpha: S.opac.fill, seed: mapp(t.inv, s2w(x, y)), respectSketch: false, edge: 1, snap: snapshot() };   // CR2: sketches never stop Fill; the colour reaches under the tile edge (earlier fills keep their own rules)
  if (doFill(act, act.snap)) { syncView(S.layers.fills, ALL); patchComposites(ALL); pushAction(act); S.artVer++; }
}
function selectGroupAt(x, y) {                       // Tessellate: tap a tile → its GROUP under the active grouping (Same / Alternate / Row / Column)
  const t = tileAt(s2w(x, y), true);
  if (!t) { S.sel = null; closePops(); invalidate(); return; }
  const g = groupOf(t.i); S.sel = { mode: S.treat, key: g.key, label: g.label }; openGroupPop(); invalidate();
}
function endWork() {
  if (!work) return; const w = work; if (PERF) PERF.mark('end ' + w.type);
  if (w.type === 'draw') {
    const st = S.stroke.st; work = null; finishStroke(true);   // the final pixels are the CANONICAL ones, identical to any replay
    pushAction(st); if (st.layer === 'art') S.artVer++;
  } else if (w.type === 'shape') {
    flushShapeMove(); E.endGesture(S.shape.g);
    const sh = S.shape;
    if (sh.guard) {                         // the release evens out the spacing of the moved edges; in the rare case that makes them touch, keep the shape before the pull
      const t0 = performance.now(), ok = outlineSimple(movedRanges(sh.g, true)); sh.gs.ms.push(performance.now() - t0);
      if (!ok) { restoreSnapshot(sh.before); sh.gs.reverted = true; toast('That pull would make the edges cross', 1800); }
      logGuard(sh.gs);
    }
    rebuildPath(); rebuildCentroids();
    if (!sh.gs.reverted) pushAction({ kind: 'shape', before: sh.before, after: snapshot() });
    if (S.hl) { S.hl.active = false; S.hl.t1 = performance.now(); } S.shape = null; work = null;
  } else if (w.type === 'pnode' || w.type === 'pcorner') { polyEndDrag(); }
  else if (w.type === 'fill') { work = null; if (Math.hypot(w.lx - w.x0, w.ly - w.y0) <= TAP_PX && performance.now() - w.t0 <= TAP_MS) applyFillAt(w.x0, w.y0); }
  else if (w.type === 'pan') { work = null; if (w.tap && Math.hypot(w.lx - w.x0, w.ly - w.y0) <= TAP_PX && performance.now() - w.t0 <= TAP_MS) selectGroupAt(w.x0, w.y0); }
  else work = null;
  invalidate();
}
function logGuard(gs) {                    // per-pull guard cost (also in the Geometry Lab and, with ?perf=1, in the phone's measurement log)
  const ms = [...gs.ms].sort((a, b) => a - b), q = p => ms.length ? +ms[Math.min(ms.length - 1, Math.floor(ms.length * p))].toFixed(3) : 0;
  const row = { frames: gs.frames, blocked: gs.blocked, p50: q(0.5), p95: q(0.95), max: q(1), reverted: !!gs.reverted };
  S.guardLog.push(row); if (S.guardLog.length > 400) S.guardLog.splice(0, 200);
  if (PERF) PERF.mark('guard ' + JSON.stringify(row));
}
function cancelWork() {                     // revert the in-flight one-finger action (a second finger arrived, or the system cancelled)
  if (!work) return;
  if (work.type === 'pnode' || work.type === 'pcorner') { polyCancelDrag(); work = null; invalidate(); return; }
  if (work.type === 'draw') finishStroke(false);
  else if (work.type === 'shape') { S.pendingMove = null; const g = S.shape.g, st = E.state; st.edges[g.e].pts = g.base.map(p => ({ x: p.x, y: p.y })); E.propagate(g.e); rebuildPath(); S.hl = null; S.shape = null; }
  work = null; invalidate();
}

/* ================= POLYGON (v5.0) + CONSTRAINED CORNERS (v5.1 · P2) =================
 * The student builds a straight-sided tile on the square grid. A NODE is a point added inside an edge; every edge is paired with another by
 * the transformation, so the node's COPY appears on the paired edge at once — each node adds two sides (4 + 2·3 = 10 at most). Nothing is
 * stored twice: a node edit rewrites the MASTER edge (the one each relation maps FROM) as straight segments through its nodes, sampled so
 * every node is exactly a boundary sample, and engine.propagate() writes the paired edge — the same call a Shape pull makes. Polygon and
 * Shape therefore share one geometry state, and Shape starts from exactly this polygon.
 * v5.1 — the four CORNERS (the cage) move wherever the transformation allows:
 *   Translation, Glide (one pair)  any parallelogram, C = B + D − A. A dragged corner carries the next corner round the tile (A→B, B→C,
 *                                  C→D, D→A): that side slides as one piece and the other two corners stay. Along the side = shear,
 *                                  across it = stretch.
 *   Glide (both pairs)             rectangles only (at every vertex the corners meet as A, C, A, C, so each angle must be 90°): the dragged
 *                                  corner follows the finger, the opposite corner stays, its neighbours slide along the sides.
 *   Rotation 90°                   the quarter-turns about A and C force a square: the corners stay fixed.
 * The relations are recomputed EXACTLY from the four corners (the translation vectors; the unique glide taking A→C and B→D) and the
 * engine is rebuilt from them — registered as data, an extra entry in the engine's construction list (engine.js unchanged). The original
 * square always uses the original construction. Nodes are stored RELATIVE to their edge (s along it, t across it, in edge lengths), so they
 * ride with the edge when a corner moves; their copies come from the new relations. Every candidate (cage + nodes) is checked before it
 * is shown: sides ≥ 0.3 cell, corner angles 30°–150°, orientation kept, inside the drawing area, and an outline that does not cross or
 * touch itself; otherwise the corner (or node) stops at the last valid position. */
const SQUARE = E.CONS.find(c => c.id === 'translation').verts.map(p => P(p.x, p.y));        // the original cell, shared by all square constructions
const CAGE_KIND = { translation: 'parallelogram', glide: 'parallelogram', 'glide-both': 'rectangle', 'rotation-sq-ac': 'fixed', 'rotation-sq-bd': 'fixed' };
const CAGE_MIN_SIDE = 0.3, CAGE_MIN_SIN = 0.5, CAGE_SNAP = 0.02, LIVE_ID = 'cage';           // × cell; sin 30°; snap back to the exact square
const cageKind = id => CAGE_KIND[id] || 'fixed';
const cageNow = () => E.state.cons.verts;                                                   // the corners of the construction in use
const cloneCage = c => c ? c.map(p => P(p.x, p.y)) : null;
const isSquare = c => !c || c.every((p, i) => p.x === SQUARE[i].x && p.y === SQUARE[i].y);
const sameCage = (a, b) => (isSquare(a) && isSquare(b)) || (!!a && !!b && a.every((p, i) => p.x === b[i].x && p.y === b[i].y));
const lerpCage = (a, b, t) => a.map((p, i) => lerpP(p, b[i], t));
const T = (x, y) => ({ type: 'translate', v: [x, y] });
function MIR(P1, P2, Q1, Q2) {             // the orientation-reversing isometry taking P1→Q1 and P2→Q2 (a mirror + slide), as an engine descriptor
  const tp = Math.atan2(P2.y - P1.y, P2.x - P1.x), tq = Math.atan2(Q2.y - Q1.y, Q2.x - Q1.x), phi = (tp + tq) / 2, c2 = Math.cos(2 * phi), s2 = Math.sin(2 * phi);
  const rx = c2 * P1.x + s2 * P1.y, ry = s2 * P1.x - c2 * P1.y, tx = Q1.x - rx, ty = Q1.y - ry, ux = Math.cos(phi), uy = Math.sin(phi), g = tx * ux + ty * uy;
  return { type: 'mirror', p0: P((tx - g * ux) / 2, (ty - g * uy) / 2), phi, g };
}
function cageRels(id, V) {                 // the construction's relations, recomputed exactly from its four corners
  if (id === 'translation') return [{ from: 0, to: 2, d: T(V[3].x - V[0].x, V[3].y - V[0].y), role: 'glue' }, { from: 1, to: 3, d: T(V[0].x - V[1].x, V[0].y - V[1].y), role: 'glue' }];
  if (id === 'glide') return [{ from: 0, to: 2, d: MIR(V[0], V[1], V[2], V[3]), role: 'glue' }, { from: 1, to: 3, d: T(V[0].x - V[1].x, V[0].y - V[1].y), role: 'glue' }];
  if (id === 'glide-both') return [{ from: 0, to: 2, d: MIR(V[0], V[1], V[2], V[3]), role: 'glue' }, { from: 1, to: 3, d: MIR(V[1], V[2], V[3], V[0]), role: 'glue' }];
  throw new Error('corners of ' + id + ' cannot move');
}
function virtCons(id, cage) {              // relation matrices for a candidate cage, without rebuilding the engine (used to test a corner move first)
  const sq = isSquare(cage), verts = sq ? SQUARE : cage, src = sq ? E.CONS.find(c => c.id === id).rels : cageRels(id, cage);
  return { verts, rels: src.filter(r => r.role === 'glue' && r.self === undefined).map(r => { const m = E.descMatrix(r.d), a0 = mapp(m, verts[r.from]), b0 = verts[r.to];
    return { from: r.from, to: r.to, m, inv: minv(m), rev: !(Math.hypot(a0.x - b0.x, a0.y - b0.y) < 1e-9) }; }) };
}
function setCage(id, cage) {               // build the engine for this construction and cage; recompute the neighbour placements
  S.consId = id; S.cageNow = isSquare(cage) ? null : cloneCage(cage);
  if (!S.cageNow) { E.build(id); S.engineId = id; }
  else { let L = E.CONS.find(c => c.id === LIVE_ID);
    if (!L) { L = { id: LIVE_ID, title: 'Polygon cage (current)', prompt: '', verts: [], rels: [] }; E.CONS.push(L); }
    L.verts = cloneCage(S.cageNow); L.rels = cageRels(id, L.verts); E.build(LIVE_ID); S.engineId = LIVE_ID; }
  const { t, f } = makeField(); S.field = t; S.fieldCull = f; S.orientCue = orientCueNow(); S.gridBasis = null; clampCam();
}
const buildCurrent = () => E.build(S.engineId);
function cageProblem(id, V) {              // '' when the four corners form a valid cell for this construction; otherwise why not
  const z = S.unit, kind = cageKind(id);
  for (let i = 0; i < 4; i++) { const a = V[i], b = V[(i + 1) % 4], c = V[(i + 2) % 4], ux = b.x - a.x, uy = b.y - a.y, vx = c.x - b.x, vy = c.y - b.y, lu = Math.hypot(ux, uy), lv = Math.hypot(vx, vy);
    if (lu < CAGE_MIN_SIDE * z) return 'side';
    const cr = ux * vy - uy * vx; if (cr <= 0) return 'fold'; if (cr / (lu * lv) < CAGE_MIN_SIN) return 'angle'; }
  const ex = (V[2].x - V[3].x) - (V[1].x - V[0].x), ey = (V[2].y - V[3].y) - (V[1].y - V[0].y);
  if (Math.hypot(ex, ey) > 1e-9) return 'parallelogram';
  if (kind === 'rectangle') { const ux = V[1].x - V[0].x, uy = V[1].y - V[0].y, vx = V[3].x - V[0].x, vy = V[3].y - V[0].y; if (Math.abs(ux * vx + uy * vy) > 1e-9 * Math.hypot(ux, uy) * Math.hypot(vx, vy)) return 'rectangle'; }
  if (kind === 'fixed' && !isSquare(V)) return 'fixed';
  return '';
}
function cageAfterDrag(id, V0, k, tgt) {   // the corner rule: where all four corners go when corner k is dragged to tgt
  const kind = cageKind(id), V = cloneCage(V0);
  if (kind === 'parallelogram') { const j = (k + 1) % 4, dx = tgt.x - V0[k].x, dy = tgt.y - V0[k].y; V[k] = P(tgt.x, tgt.y); V[j] = P(V0[j].x + dx, V0[j].y + dy);
    const r = k === 2 || j === 2 ? 0 : 2;                                  // keep C − D = B − A exact: re-derive a corner that did not just follow the finger
    if (r === 2) V[2] = P(V[1].x + V[3].x - V[0].x, V[1].y + V[3].y - V[0].y); else V[0] = P(V[1].x + V[3].x - V[2].x, V[1].y + V[3].y - V[2].y);
    return V; }
  if (kind === 'rectangle') { const o = (k + 2) % 4, L = Math.hypot(V0[1].x - V0[0].x, V0[1].y - V0[0].y), e1 = P((V0[1].x - V0[0].x) / L, (V0[1].y - V0[0].y) / L), e2 = P(-e1.y, e1.x), O = V0[o];
    const d1 = (tgt.x - O.x) * e1.x + (tgt.y - O.y) * e1.y, d2 = (tgt.x - O.x) * e2.x + (tgt.y - O.y) * e2.y;
    V[k] = P(O.x + d1 * e1.x + d2 * e2.x, O.y + d1 * e1.y + d2 * e2.y);
    [(k + 1) % 4, (k + 3) % 4].forEach(a => { const ax = V0[a].x - O.x, ay = V0[a].y - O.y, alongE1 = Math.abs(ax * e1.x + ay * e1.y) > Math.abs(ax * e2.x + ay * e2.y);
      V[a] = alongE1 ? P(O.x + d1 * e1.x, O.y + d1 * e1.y) : P(O.x + d2 * e2.x, O.y + d2 * e2.y); });
    return V; }
  return null;
}
const polyRels = () => E.state.rels.filter(r => r.role === 'glue' && r.self === undefined);       // master = r.from, copy edge = r.to
const curK = () => ({ verts: cageNow(), rels: polyRels() });
const frameOf = (V, m) => { const a = V[m], b = V[(m + 1) % V.length]; return { a, dx: b.x - a.x, dy: b.y - a.y }; };
const relToWorld = (f, n) => P(f.a.x + n.s * f.dx - n.t * f.dy, f.a.y + n.s * f.dy + n.t * f.dx);
const worldToRel = (f, p, c) => { const L2 = f.dx * f.dx + f.dy * f.dy, x = p.x - f.a.x, y = p.y - f.a.y; return { s: (x * f.dx + y * f.dy) / L2, t: (y * f.dx - x * f.dy) / L2, c: !!c }; };
function worldNodes(nodes, K) { const o = {}; Object.keys(nodes).forEach(m => { const f = frameOf(K.verts, +m); o[m] = nodes[m].map(n => relToWorld(f, n)); }); return o; }
const nodeWorld = (m, k) => relToWorld(frameOf(cageNow(), m), S.poly.nodes[m][k]);
const cloneNodes = nodes => { const o = {}; Object.keys(nodes).forEach(m => { if (nodes[m].length) o[m] = nodes[m].map(p => ({ s: p.s, t: p.t, c: !!p.c })); }); return o; };
const cloneState = st => ({ consId: st.consId, family: st.family, cage: isSquare(st.cage) ? null : cloneCage(st.cage), nodes: cloneNodes(st.nodes) });
const polyCommitted = () => S.poly.hist[S.poly.hp];
const cageKey = c => isSquare(c) ? 'square' : c.map(p => p.x + ',' + p.y).join(';');
const polyKey = st => st.consId + '|' + cageKey(st.cage) + '|' + Object.keys(st.nodes).sort().filter(m => st.nodes[m].length).map(m => m + ':' + st.nodes[m].map(p => p.s + ',' + p.t).join(';')).join('|');
const nodeCount = nodes => Object.values(nodes).reduce((n, l) => n + l.length, 0);
const sideCount = nodes => 4 + 2 * nodeCount(nodes);
const lerpP = (a, b, t) => P(a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t);
function sampleThrough(a, nodes, b) {      // N+1 points along a → nodes → b; the N segments are shared out by length so every node is a sample
  const V = [a, ...nodes, b], lens = V.slice(1).map((q, i) => Math.hypot(q.x - V[i].x, q.y - V[i].y)), tot = lens.reduce((t, l) => t + l, 0);
  const raw = lens.map(l => N * l / tot), cnt = raw.map(r => Math.max(1, Math.floor(r)));
  let left = N - cnt.reduce((t, c) => t + c, 0); const order = raw.map((r, i) => [r - Math.floor(r), i]).sort((x, y) => y[0] - x[0] || x[1] - y[1]);
  for (let k = 0; left > 0; k = (k + 1) % order.length, left--) cnt[order[k][1]]++;
  for (let over = cnt.reduce((t, c) => t + c, 0) - N; over > 0; over--) cnt[cnt.indexOf(Math.max(...cnt))]--;
  const out = []; V.slice(1).forEach((q, i) => { const p = V[i]; for (let k = 0; k < cnt[i]; k++) out.push(k ? P(p.x + (q.x - p.x) * k / cnt[i], p.y + (q.y - p.y) * k / cnt[i]) : P(p.x, p.y)); });
  out.push(P(b.x, b.y)); return out;
}
function writePolygonEdges(nodes) {        // the polygon → engine edges (masters sampled through their nodes; copies by the exact transformation)
  const st = E.state, V = st.cons.verts, n = V.length, W = worldNodes(nodes, curK());
  polyRels().forEach(r => { const m = r.from; st.edges[m].pts = sampleThrough(V[m], W[m] || [], V[(m + 1) % n]); E.propagate(m); });
  rebuildPath(); rebuildCentroids();
}
function polyVerts(nodes, K) {             // the tile outline as corners + nodes + copies, in boundary order (K: a construction, default the current one)
  K = K || curK(); const V = K.verts, n = V.length, W = worldNodes(nodes, K), out = [];
  for (let e = 0; e < n; e++) {
    out.push({ p: V[e], kind: 'corner', e });
    const asM = K.rels.find(r => r.from === e), asC = K.rels.find(r => r.to === e);
    if (asM) (W[e] || []).forEach((p, k) => out.push({ p, kind: 'node', e, m: e, k, rel: asM, placed: !nodes[e][k].c }));
    else if (asC) { const l = (W[asC.from] || []).map((p, k) => ({ p: mapp(asC.m, p), kind: 'copy', e, m: asC.from, k, rel: asC, placed: !!nodes[asC.from][k].c }));
      (asC.rev ? l.reverse() : l).forEach(v => out.push(v)); }
  }
  return out;
}
function distPS(p, a, b) { const dx = b.x - a.x, dy = b.y - a.y, l = dx * dx + dy * dy, t = l ? Math.max(0, Math.min(1, ((p.x - a.x) * dx + (p.y - a.y) * dy) / l)) : 0; return Math.hypot(p.x - a.x - t * dx, p.y - a.y - t * dy); }
function polyProblem(nodes, K) {           // '' when the polygon is a valid tile; otherwise why not
  const vs = polyVerts(nodes, K).map(v => v.p), n = vs.length, z = S.unit, I = S.ink, mg = 0.02 * I.side;
  for (const p of vs) if (p.x < I.x0 + mg || p.x > I.x0 + I.side - mg || p.y > I.y1 - mg || p.y < I.y1 - I.side + mg) return 'area';   // inside the drawing area
  for (let i = 0; i < n; i++) { const a = vs[i], b = vs[(i + 1) % n]; if (Math.hypot(b.x - a.x, b.y - a.y) < POLY_MIN_SEG * z) return 'short'; }
  for (let i = 0; i < n; i++) for (let j = i + 2; j < n; j++) { if (i === 0 && j === n - 1) continue; const a = vs[i], b = vs[(i + 1) % n], c = vs[j], d = vs[(j + 1) % n];
    if (segX(a.x, a.y, b.x, b.y, c.x, c.y, d.x, d.y)) return 'cross'; }
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) { if (j === i || (j + 1) % n === i) continue; if (distPS(vs[i], vs[j], vs[(j + 1) % n]) < POLY_CLEAR * z) return 'touch'; }
  let a2 = 0; vs.forEach((p, i) => { const q = vs[(i + 1) % n]; a2 += p.x * q.y - q.x * p.y; }); if (a2 <= 0) return 'cross';
  return '';
}
function applyPolyState(st) {               // show a committed polygon state (rebuilding the construction if the transformation or the corners differ)
  if (st.consId !== S.consId || !sameCage(st.cage, S.cageNow)) setCage(st.consId, st.cage);
  S.poly.family = st.family; S.poly.nodes = cloneNodes(st.nodes); S.poly.sel = null; writePolygonEdges(S.poly.nodes); syncPolyUI(); updateTitle(); invalidate();
}
const orientCueNow = () => E.state.rels.some(r => r.role === 'glue' && (Math.abs(r.m[0] - 1) > 1e-9 || Math.abs(r.m[1]) > 1e-9 || Math.abs(r.m[2]) > 1e-9 || Math.abs(r.m[3] - 1) > 1e-9));
const shapeEditsApplied = () => S.history.slice(0, S.hp).filter(a => a.kind === 'shape').length;
// Does changing the polygon now need the student's confirmation? Only when Shape changes are built on exactly this polygon.
const needsConfirm = () => !!S.poly && !!S.shapeBaseKey && !S.restartOK && polyKey(polyCommitted()) === S.shapeBaseKey && shapeEditsApplied() > 0;
function gated(fn) { if (needsConfirm()) askRestart(fn); else fn(); }
function askRestart(then) {
  const n = shapeEditsApplied(), art = S.history.slice(0, S.hp).some(a => a.kind === 'stroke' || a.kind === 'fill');
  ask({ title: 'Change the polygon?',
    html: `<p>Your tile has <b>${n} Shape ${n === 1 ? 'change' : 'changes'}</b> made on this polygon. If you change the polygon, Shape starts again from the new polygon.</p>` +
      `<p>${art ? 'Your sketch and artwork stay exactly as they are.' : 'Nothing else changes.'}</p><p class="mute">The current version is kept: ⋮ menu › Restore previous version brings it back.</p>`,
    yes: 'Change polygon', no: 'Keep Shape changes' }, () => { S.restartOK = true; then && then(); });
}
function captureVersion() {                 // a complete, restorable version: polygon (corners + nodes) + its undo list, Shape boundary + the whole history
  const c = polyCommitted(), key = polyKey(c), handed = S.shapeBaseKey === key;
  let edges, initialSnap = S.initialSnap, baseKey = S.shapeBaseKey;
  if (S.mode === 'polygon') { if (handed && S.refined) edges = S.refined; else { edges = polySnapshot(c); initialSnap = edges; baseKey = key; } }
  else edges = snapshot();
  return { poly: { hist: S.poly.hist.slice(), hp: S.poly.hp }, history: S.history.slice(), hp: S.hp, initialSnap, edges, baseKey,
    shapeEdits: shapeEditsApplied(), sides: sideCount(c.nodes), moved: !isSquare(c.cage) };
}
function polySnapshot(st) {                 // the engine edges of a polygon state, leaving the current construction and edges as they were
  const keep = { id: S.consId, cage: cloneCage(S.cageNow), edges: snapshot() };
  if (st.consId !== S.consId || !sameCage(st.cage, S.cageNow)) setCage(st.consId, st.cage);
  writePolygonEdges(st.nodes); const out = snapshot();
  if (keep.id !== S.consId || !sameCage(keep.cage, S.cageNow)) setCage(keep.id, keep.cage);
  E.setEdges(keep.edges.map(pts => ({ pts }))); rebuildPath(); rebuildCentroids(); return out;
}
function restartShape() {                   // the polygon changes under Shape refinements: keep the whole version, then start Shape again from the new polygon
  S.recovery = captureVersion();
  const before = S.history.slice(0, S.hp).filter(a => a.kind !== 'shape'), after = S.history.slice(S.hp).filter(a => a.kind !== 'shape');
  S.history = before.concat(after); S.hp = before.length; S.shapeBaseKey = null; S.refined = null; syncUndo(); syncRestoreUI();
}
function beforePolyChange(next) {           // called with the state about to be committed
  if (S.shapeBaseKey && polyKey(next) !== S.shapeBaseKey && S.history.some(a => a.kind === 'shape')) restartShape();
}
function polyCommit(next) {
  beforePolyChange(next); const P2 = S.poly; P2.hist = P2.hist.slice(0, P2.hp + 1); P2.hist.push(cloneState(next)); P2.hp = P2.hist.length - 1; applyPolyState(next);
}
function polyHistory(d) {
  const P2 = S.poly, to = P2.hp + d; if (!P2 || to < 0 || to >= P2.hist.length) return;
  if (work) cancelWork();
  gated(() => { beforePolyChange(P2.hist[to]); P2.hp = to; applyPolyState(P2.hist[to]); });
}
function choosePolyCons(id) {               // Translate / Rotate / Glide and their secondary choices (a new transformation starts again from the square)
  const cur = polyCommitted(); if (cur.family && cur.consId === id) return;
  const next = { consId: id, family: POLY_FAMILY_OF[id], cage: null, nodes: cur.family ? {} : cur.nodes }, had = (nodeCount(cur.nodes) > 0 || !isSquare(cur.cage)) && cur.family;
  if (work) cancelWork();
  const cornersHint = () => { if (cageKind(id) !== 'fixed' && !S.seenHint.corners) { S.seenHint.corners = true; toast('You can also drag a corner: the cell reshapes and its neighbours follow', 3400); return true; } return false; };
  if (!cur.family) { S.poly.hist[S.poly.hp] = cloneState(next); applyPolyState(next); if (!cornersHint() && !S.seenHint.polygon) { S.seenHint.polygon = true; toast(HINTS.polygon, 3600); } return; }
  gated(() => { polyCommit(next); if (had) toast('New transformation: the polygon starts again from the square · Undo brings it back', 3200); else cornersHint(); });
}
function polyHit(x, y) {                    // screen point → a node handle, a corner, or a point on a side
  const vs = polyVerts(S.poly.nodes); let best = null;
  vs.forEach(v => { if (v.kind === 'corner') return; const q = w2s(v.p), d = Math.hypot(q.x - x, q.y - y); if (d <= NODE_PX && (!best || d < best.d)) best = { type: 'node', v, d }; });
  if (best) return best;
  const cpx = cageKind(S.consId) === 'fixed' ? CORNER_PX : NODE_PX;
  vs.forEach(v => { if (v.kind !== 'corner') return; const q = w2s(v.p), d = Math.hypot(q.x - x, q.y - y); if (d <= cpx && (!best || d < best.d)) best = { type: 'corner', v, d }; });
  if (best) return best;
  const n = vs.length;
  for (let i = 0; i < n; i++) { const a = w2s(vs[i].p), b = w2s(vs[(i + 1) % n].p), dx = b.x - a.x, dy = b.y - a.y, l2 = dx * dx + dy * dy || 1e-9;
    const t = Math.max(0, Math.min(1, ((x - a.x) * dx + (y - a.y) * dy) / l2)), d = Math.hypot(x - a.x - dx * t, y - a.y - dy * t);
    if (d <= PSIDE_PX && (!best || d < best.d)) best = { type: 'side', i, t, d, vs }; }
  return best;
}
function polyInsertAt(h) {                  // a new node on the touched side (on the straight line, so nothing moves until it is dragged)
  const vs = h.vs, a = vs[h.i].p, b = vs[(h.i + 1) % vs.length].p, e = vs[h.i].e, len = Math.hypot(b.x - a.x, b.y - a.y), z = S.unit;
  if (len < 2.2 * POLY_MIN_SEG * z) { toast('This side is too short for another point', 1800); return null; }
  const m0 = POLY_MIN_SEG * z * 1.05 / len, t = Math.min(1 - m0, Math.max(m0, h.t)), w = lerpP(a, b, t);
  const corner = vs.findIndex(v => v.kind === 'corner' && v.e === e), seg = h.i - corner, rels = polyRels();
  const asM = rels.find(r => r.from === e), asC = rels.find(r => r.to === e), nodes = S.poly.nodes;
  let m, k, q, rel = null;
  if (asM) { m = e; k = seg; q = w; } else { rel = asC; m = asC.from; const K = (nodes[m] || []).length; k = asC.rev ? K - seg : seg; q = mapp(asC.inv, w); }
  (nodes[m] = nodes[m] || []).splice(k, 0, worldToRel(frameOf(cageNow(), m), q, !!rel));
  if (polyProblem(nodes)) { nodes[m].splice(k, 1); if (!nodes[m].length) delete nodes[m]; toast('No room for a point here', 1500); return null; }
  writePolygonEdges(nodes); return { m, k, copy: rel, handle: w };
}
function polyStart(e, x, y) {
  if (!S.poly.family) { toast('First choose Translate, Rotate or Glide', 2000); return; }
  const h = polyHit(x, y); if (S.poly.sel) { S.poly.sel = null; }
  if (!h) { invalidate(); return; }
  const w = s2w(x, y), base = { id: e.pointerId, t0: performance.now(), x0: x, y0: y, lx: x, ly: y, moved: false, blocked: false };
  if (h.type === 'corner') {
    if (cageKind(S.consId) === 'fixed') { S.lockFlash = { k: h.v.e, t: performance.now() }; toast('Quarter-turns need a square: in Rotation the corners stay fixed · add points on the sides', 2800); invalidate(); return; }
    work = Object.assign(base, { type: 'pcorner', k: h.v.e, V0: cloneCage(cageNow()), off: P(h.v.p.x - w.x, h.v.p.y - w.y), gate: needsConfirm() });
  } else if (h.type === 'node') {
    const v = h.v; work = Object.assign(base, { type: 'pnode', m: v.m, k: v.k, copy: v.kind === 'copy' ? v.rel : null, off: P(v.p.x - w.x, v.p.y - w.y), inserted: false, gate: needsConfirm() });
  } else {
    if (needsConfirm()) { askRestart(() => toast('Now change your polygon', 1600)); return; }
    if (nodeCount(S.poly.nodes) >= POLY_MAX_POINTS) { toast(POLY_MAX_POINTS + ' points is the most a tile can have · tap a point to remove it', 2600); return; }
    const ins = polyInsertAt(h); if (!ins) return;
    work = Object.assign(base, { type: 'pnode', m: ins.m, k: ins.k, copy: ins.copy, off: P(ins.handle.x - w.x, ins.handle.y - w.y), inserted: true, gate: false });
  }
  invalidate();
}
function flushPolyMove() {                  // node and corner drags are applied once per frame, kept valid by sliding to the last good position
  const p = S.pendingPoly; S.pendingPoly = null; if (!p || !work || (work.type !== 'pnode' && work.type !== 'pcorner')) return;
  const w = s2w(p.x, p.y), tgt = P(w.x + work.off.x, w.y + work.off.y);
  if (work.type === 'pcorner') { flushCornerMove(tgt); return; }
  const want = work.copy ? mapp(work.copy.inv, tgt) : tgt, f = frameOf(cageNow(), work.m);
  const list = S.poly.nodes[work.m], curRel = list[work.k], cur = relToWorld(f, curRel), set = q => { list[work.k] = worldToRel(f, q, curRel.c); };
  set(want);
  if (!polyProblem(S.poly.nodes)) work.blocked = false;
  else { let lo = 0, hi = 1; for (let i = 0; i < 10; i++) { const m = (lo + hi) / 2; set(lerpP(cur, want, m)); polyProblem(S.poly.nodes) ? hi = m : lo = m; }
    set(lerpP(cur, want, lo)); if (!work.blocked && !S.seenHint.polyBlock) { S.seenHint.polyBlock = true; toast('Sides can’t cross or touch', 1600); } work.blocked = true; }
  if (list[work.k].s !== curRel.s || list[work.k].t !== curRel.t) { work.moved = true; writePolygonEdges(S.poly.nodes); }
}
function flushCornerMove(tgt) {             // the cage follows the corner rule; the relations and the neighbour placements are rebuilt from it
  const id = S.consId, cur = cloneCage(cageNow()); let want = cageAfterDrag(id, work.V0, work.k, tgt); if (!want) return;
  if (want.every((q, i) => Math.hypot(q.x - SQUARE[i].x, q.y - SQUARE[i].y) < CAGE_SNAP * S.unit)) want = cloneCage(SQUARE);   // back to the exact square
  const ok = V => !cageProblem(id, V) && !polyProblem(S.poly.nodes, virtCons(id, V));
  let use = want;
  if (ok(want)) work.blocked = false;
  else { let lo = 0, hi = 1; for (let i = 0; i < 10; i++) { const m = (lo + hi) / 2; ok(lerpCage(cur, want, m)) ? lo = m : hi = m; }
    use = lo > 0 ? lerpCage(cur, want, lo) : cur; if (!work.blocked && !S.seenHint.cageBlock) { S.seenHint.cageBlock = true; toast('That would flatten the cell or make sides cross', 1800); } work.blocked = true; }
  if (!sameCage(use, cur)) { setCage(id, use); writePolygonEdges(S.poly.nodes); work.moved = true; }
}
function polyEndDrag() {
  flushPolyMove(); const w = work; work = null;
  if (w.type === 'pcorner') { if (w.moved) polyCommit(polyCurrentState()); invalidate(); return; }
  const still = Math.hypot(w.lx - w.x0, w.ly - w.y0) <= TAP_PX && performance.now() - w.t0 <= TAP_MS;
  if (w.inserted || w.moved) {               // the node keeps track of which copy the student is working with (filled = the one placed)
    const l = S.poly.nodes[w.m]; l[w.k] = { s: l[w.k].s, t: l[w.k].t, c: !!w.copy }; polyCommit(polyCurrentState());
  } else if (still) S.poly.sel = { m: w.m, k: w.k, copy: !!w.copy };
  invalidate();
}
const polyCurrentState = () => ({ consId: S.consId, family: S.poly.family, cage: cloneCage(S.cageNow), nodes: cloneNodes(S.poly.nodes) });
function polyCancelDrag() { S.pendingPoly = null; applyPolyState(polyCommitted()); }
function removeSelectedNode() {
  const sel = S.poly && S.poly.sel; if (!sel) return; const next = polyCurrentState(); next.nodes[sel.m].splice(sel.k, 1); if (!next.nodes[sel.m].length) delete next.nodes[sel.m];
  if (polyProblem(next.nodes)) { toast('This point can’t go: the straight side would cross another side', 2600); return; }
  gated(() => { S.poly.sel = null; polyCommit(next); });
}
function placeRemoveChip() {
  const b = $('node-remove'), sel = S.mode === 'polygon' && S.poly && S.poly.sel && !work ? S.poly.sel : null; b.hidden = !sel; if (!sel) return;
  const v = polyVerts(S.poly.nodes).find(v => v.m === sel.m && v.k === sel.k && (v.kind === 'copy') === sel.copy); if (!v) { b.hidden = true; return; }
  const q = w2s(v.p); b.style.left = Math.round(Math.min(S.vw - 70, Math.max(70, q.x))) + 'px'; b.style.top = Math.round(Math.max(110, q.y - 16)) + 'px';
}
function cornerLinks(k) {                   // which corners move with corner k, and which sides change together (for the feedback)
  const kind = cageKind(S.consId);
  if (kind === 'parallelogram') { const j = (k + 1) % 4; return { kind, linked: [j], pair: [(k + 3) % 4, j] }; }   // the two sides that stay parallel and equal while k–j slides
  if (kind === 'rectangle') return { kind, linked: [(k + 1) % 4, (k + 3) % 4], pair: [] };
  return { kind, linked: [], pair: [] };
}
function drawPolygonOverlay() {
  if (!S.poly) return; const vs = polyVerts(S.poly.nodes), drag = work && work.type === 'pnode' ? work : null, cw = work && work.type === 'pcorner' ? work : null, V = cageNow();
  const dash = (A, B) => { ctx.save(); ctx.setLineDash([4, 5]); ctx.strokeStyle = 'rgba(255,255,255,.75)'; ctx.lineWidth = 1.2; ctx.beginPath(); ctx.moveTo(A.x, A.y); ctx.lineTo(B.x, B.y); ctx.stroke(); ctx.restore(); };
  if (drag) {                               // the side being changed, its paired side, and the link between the point and its copy
    const r = polyRels().find(r => r.from === drag.m), nd = nodeWorld(drag.m, drag.k);
    strokeEdge(drag.m, COLORS.edgeA, 5, 0.85); strokeEdge(r.to, COLORS.edgeB, 5, 0.85); dash(w2s(nd), w2s(mapp(r.m, nd)));
  }
  let links = null;
  if (cw) {                                 // restrained feedback: the corner(s) moving with it, and the sides that stay parallel and equal (or square)
    links = cornerLinks(cw.k); if (links.pair.length) { strokeEdge(links.pair[0], COLORS.edgeA, 4, 0.7); strokeEdge(links.pair[1], COLORS.edgeB, 4, 0.7); }
    links.linked.forEach(j => dash(w2s(V[cw.k]), w2s(V[j])));
    if (links.kind === 'rectangle') { ctx.save(); ctx.strokeStyle = 'rgba(255,255,255,.8)'; ctx.lineWidth = 1.4;      // right-angle marks: the angles stay 90°
      for (let i = 0; i < 4; i++) { const c = w2s(V[i]), a = w2s(V[(i + 1) % 4]), b = w2s(V[(i + 3) % 4]), ua = Math.hypot(a.x - c.x, a.y - c.y), ub = Math.hypot(b.x - c.x, b.y - c.y), s = 10;
        const pa = P(c.x + (a.x - c.x) / ua * s, c.y + (a.y - c.y) / ua * s), pb = P(c.x + (b.x - c.x) / ub * s, c.y + (b.y - c.y) / ub * s);
        ctx.beginPath(); ctx.moveTo(pa.x, pa.y); ctx.lineTo(pa.x + pb.x - c.x, pa.y + pb.y - c.y); ctx.lineTo(pb.x, pb.y); ctx.stroke(); } ctx.restore(); }
  }
  const fixed = cageKind(S.consId) === 'fixed', lf = S.lockFlash && performance.now() - S.lockFlash.t < 900 ? S.lockFlash : null; if (lf) invalidate(); else S.lockFlash = null;
  ctx.save();
  vs.forEach(v => { const q = w2s(v.p);
    if (v.kind === 'corner') {              // CORNERS are squares (nodes are circles): draggable ones larger; Rotation's fixed ones small
      const on = cw && cw.k === v.e, lk = links && links.linked.includes(v.e), h = fixed ? 4 : on ? 7.5 : 6;
      if (lk) { ctx.beginPath(); ctx.arc(q.x, q.y, 11, 0, TAU); ctx.strokeStyle = COLORS.edgeB; ctx.lineWidth = 2.5; ctx.stroke(); }
      if (lf && lf.k === v.e) { ctx.beginPath(); ctx.arc(q.x, q.y, 12, 0, TAU); ctx.strokeStyle = '#ff7b7b'; ctx.lineWidth = 2.5; ctx.globalAlpha = 1 - (performance.now() - lf.t) / 900; ctx.stroke(); ctx.globalAlpha = 1; }
      ctx.fillStyle = '#1d1b18'; ctx.strokeStyle = on ? (cw.blocked ? '#ff7b7b' : COLORS.edgeA) : 'rgba(255,255,255,.9)'; ctx.lineWidth = on ? 3 : fixed ? 1.5 : 2;
      ctx.beginPath(); ctx.rect(q.x - h, q.y - h, 2 * h, 2 * h); ctx.fill(); ctx.stroke(); return; }
    const on = drag && drag.m === v.m && drag.k === v.k, sel = S.poly.sel && S.poly.sel.m === v.m && S.poly.sel.k === v.k, r = on || sel ? 8.5 : 7;
    if (sel) { ctx.beginPath(); ctx.arc(q.x, q.y, r + 6, 0, TAU); ctx.strokeStyle = 'rgba(255,255,255,.9)'; ctx.lineWidth = 2; ctx.stroke(); }
    ctx.beginPath(); ctx.arc(q.x, q.y, r, 0, TAU);
    if (v.placed) { ctx.fillStyle = COLORS.start; ctx.fill(); ctx.strokeStyle = on && drag.blocked ? '#ff7b7b' : '#fff'; ctx.lineWidth = on && drag.blocked ? 3 : 2; ctx.stroke(); }
    else { ctx.fillStyle = '#fff'; ctx.fill(); ctx.strokeStyle = on && drag.blocked ? '#ff7b7b' : COLORS.start; ctx.lineWidth = 3; ctx.stroke(); }
  });
  ctx.restore();
}
function enterPolygon() {                   // put the Shape boundary aside and show the polygon it was built on
  S.refined = snapshot(); S.restartOK = false; S.hl = null; S.shape = null; S.poly.sel = null; S.poly.nodes = cloneNodes(polyCommitted().nodes); writePolygonEdges(S.poly.nodes);
}
function leavePolygon() {                   // HANDOFF: unchanged polygon → the Shape boundary returns; changed (or first time) → Shape starts from exactly this polygon
  const key = polyKey(polyCommitted()); S.poly.sel = null;
  if (S.shapeBaseKey === key && S.refined) restoreSnapshot(S.refined);
  else { if (S.history.some(a => a.kind === 'shape')) restartShape(); S.initialSnap = snapshot(); S.shapeBaseKey = key; }
  S.refined = null; S.restartOK = false;
}
function restoreVersion() {                 // swap the current version with the kept one (so restoring never loses anything either)
  const v = S.recovery; if (!v || !S.poly) return; if (work) cancelWork();
  const cur = captureVersion();
  S.poly.hist = v.poly.hist.slice(); S.poly.hp = v.poly.hp; const st = polyCommitted();
  if (st.consId !== S.consId || !sameCage(st.cage, S.cageNow)) setCage(st.consId, st.cage);
  S.poly.family = st.family; S.poly.nodes = cloneNodes(st.nodes); S.poly.sel = null;
  S.history = v.history.slice(); S.hp = v.hp; S.initialSnap = v.initialSnap; S.shapeBaseKey = v.baseKey;
  if (S.mode === 'polygon') { S.refined = v.edges; writePolygonEdges(S.poly.nodes); } else restoreSnapshot(v.edges);
  rebuildLayers(); S.recovery = cur; S.restartOK = false; syncUndo(); syncPolyUI(); syncRestoreUI(); updateTitle(); invalidate();
  toast('Previous version restored · the menu can swap back', 2600);
}
function syncPolyUI() {
  $('mode-polygon').setAttribute('aria-disabled', String(!S.poly)); if (!S.poly) return;
  const st = S.poly, fam = st.family, sides = sideCount(st.nodes), movable = cageKind(S.consId) !== 'fixed';
  ['translate', 'rotate', 'glide'].forEach(f => $('pf-' + f).setAttribute('aria-pressed', String(f === fam)));
  $('pb-sec-rotate').hidden = fam !== 'rotate'; $('pb-sec-glide').hidden = fam !== 'glide'; $('pb-hint').hidden = fam === 'rotate' || fam === 'glide';
  document.querySelectorAll('#pb-sec-rotate button, #pb-sec-glide button').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.id === S.consId)));
  $('pb-hint').textContent = !fam ? 'Choose how the tiles repeat' : nodeCount(st.nodes) ? (movable ? 'Drag points or corners' : 'Drag points · tap to remove') : (movable ? 'Tap a side · drag a corner' : 'Tap a side to add a point');   // (CR3: shorter, so they fit beside Sketch)
  const pts = nodeCount(st.nodes), sk = S.polyTool === 'sketch'; void sides;               // CR3: no permanent counter, a quiet one from 30 points
  $('pb-count').hidden = pts < POLY_CUE_FROM; $('pb-count').innerHTML = `<b>${pts}<small>/${POLY_MAX_POINTS}</small></b><span>points</span>`; $('pb-count').classList.toggle('full', pts >= POLY_MAX_POINTS);
  $('pb-sketch').setAttribute('aria-pressed', String(sk)); $('pb-sketch').disabled = !fam;
  if (sk) { $('pb-hint').hidden = true; $('pb-sec-rotate').hidden = true; $('pb-sec-glide').hidden = true; }
  $('pb-next').disabled = !fam;
  syncPolyButtons();
}
function syncRestoreUI() { const v = S.recovery; $('m-restore').hidden = !v; if (v) $('m-restore-sub').textContent = v.sides + ' sides' + (v.moved ? ' · corners moved' : '') + (v.shapeEdits ? ' · ' + v.shapeEdits + (v.shapeEdits === 1 ? ' Shape change' : ' Shape changes') : ''); }
let askCb = null;
function ask(o, onYes) { $('ask-title').textContent = o.title; $('ask-text').innerHTML = o.html; $('ask-yes').textContent = o.yes; $('ask-no').textContent = o.no; $('ask-no').hidden = !o.no; $('ask').hidden = false; askCb = onYes; }
$('ask-yes').onclick = () => { $('ask').hidden = true; const f = askCb; askCb = null; if (f) f(); };
$('ask-no').onclick = () => { $('ask').hidden = true; askCb = null; };
$('node-remove').onclick = () => removeSelectedNode();
['translate', 'rotate', 'glide'].forEach(f => $('pf-' + f).onclick = () => { const cur = polyCommitted(); if (POLY_FAMILY_OF[cur.consId] === f && cur.family) return; choosePolyCons(POLY_FAMILY[f][0]); });
document.querySelectorAll('#pb-sec-rotate button, #pb-sec-glide button').forEach(b => b.onclick = () => choosePolyCons(b.dataset.id));
$('pb-undo').onclick = () => polyUndoRedo(-1); $('pb-redo').onclick = () => polyUndoRedo(1);   // CR3: one timeline (polygon edits + Polygon sketches)
$('pb-next').onclick = () => setMode('shape');

/* ---------------- two-finger navigation ---------------- */
function mid2() { const a = [...ptrs.values()]; return { x: (a[0].x + a[1].x) / 2, y: (a[0].y + a[1].y) / 2, d: Math.hypot(a[0].x - a[1].x, a[0].y - a[1].y) || 1 }; }
function beginNav() { const m = mid2(); nav = { d0: m.d, s0: S.cam.s, anchor: s2w(m.x, m.y) }; }
function updateNav() {
  const m = mid2(), s = S.cam.s; S.cam.s = nav.s0 * m.d / nav.d0; const { minS, maxS } = zoomLimits(); S.cam.s = Math.min(maxS, Math.max(minS, S.cam.s));
  S.cam.x = nav.anchor.x - (m.x - S.cx) / S.cam.s; S.cam.y = nav.anchor.y + (m.y - S.cy) / S.cam.s; clampCam(); void s; invalidate();
}
function zoomAt(x, y, factor) { const a = s2w(x, y); S.cam.s *= factor; const { minS, maxS } = zoomLimits(); S.cam.s = Math.min(maxS, Math.max(minS, S.cam.s));
  S.cam.x = a.x - (x - S.cx) / S.cam.s; S.cam.y = a.y + (y - S.cy) / S.cam.s; clampCam(); invalidate(); }


/* ---------------- pointer plumbing ---------------- */
const overlaysOpen = () => !$('entry').hidden || !$('lab').hidden || !$('about').hidden || !$('ask').hidden || !$('exp').hidden;
const refActive = () => S.mode === 'shape' && !!S.ref.img && S.ref.adjust && !S.ref.locked;   // ONLY in the explicit Move-reference mode does the reference receive touches
function beginRefNav() { const a = [...ptrs.values()], R = S.ref; const mid = { x: (a[0].x + a[1].x) / 2, y: (a[0].y + a[1].y) / 2 };
  refNav = { d0: Math.hypot(a[0].x - a[1].x, a[0].y - a[1].y) || 1, ang0: Math.atan2(a[1].y - a[0].y, a[1].x - a[0].x), mid0: s2w(mid.x, mid.y), r0: { x: R.x, y: R.y, sc: R.sc, rot: R.rot } }; }
function updateRefNav() {                          // two fingers on the REFERENCE: pinch = scale, twist = rotate, drag = move (the view stays put)
  const a = [...ptrs.values()], R = S.ref, mid = s2w((a[0].x + a[1].x) / 2, (a[0].y + a[1].y) / 2), d = Math.hypot(a[0].x - a[1].x, a[0].y - a[1].y) || 1, ang = Math.atan2(a[1].y - a[0].y, a[1].x - a[0].x);
  R.sc = Math.min(R.sc0 * 10, Math.max(R.sc0 * 0.1, refNav.r0.sc * d / refNav.d0)); R.rot = refNav.r0.rot - (ang - refNav.ang0);
  R.x = refNav.r0.x + (mid.x - refNav.mid0.x); R.y = refNav.r0.y + (mid.y - refNav.mid0.y); invalidate();
}
canvas.addEventListener('pointerdown', e => {
  if (overlaysOpen()) return; closeMenu(); closePalette(); closeRefMore(); e.preventDefault();
  try { canvas.setPointerCapture(e.pointerId); } catch (_) {}
  const r = canvas.getBoundingClientRect(), x = e.clientX - r.left, y = e.clientY - r.top; ptrs.set(e.pointerId, { x, y });
  if (ptrs.size === 2) {
    if (refActive()) { cancelWork(); beginRefNav(); lock = true; return; }
    if (work && (work.type === 'draw' || work.type === 'shape' || work.type === 'pnode' || work.type === 'pcorner') && performance.now() - work.t0 > WORK_COMMIT_MS) { endWork(); lock = true; return; }   // a deliberate action was under way: keep it, ignore the new finger
    cancelWork(); beginNav(); lock = true; return;
  }
  if (ptrs.size > 2 || lock) return;
  if (e.pointerType === 'mouse' && (e.button === 1 || e.button === 2)) { work = { type: 'pan', id: e.pointerId, t0: performance.now(), lx: x, ly: y }; return; }
  if (e.pointerType === 'mouse' && e.button !== 0) return;
  startWork(e, x, y);
});
canvas.addEventListener('pointermove', e => {
  const r = canvas.getBoundingClientRect(), x = e.clientX - r.left, y = e.clientY - r.top;
  if (ptrs.has(e.pointerId)) ptrs.set(e.pointerId, { x, y });
  if (refNav && ptrs.size >= 2) { updateRefNav(); e.preventDefault(); return; }
  if (nav && ptrs.size >= 2) { updateNav(); e.preventDefault(); return; }
  if (work && work.id === e.pointerId && ptrs.size === 1) {
    if (work.type === 'shape' && S.opt.coalesce) { S.pendingMove = { x, y }; invalidate(); e.preventDefault(); return; }                  // applied once per frame in render()
    if (work.type === 'pnode' || work.type === 'pcorner') {                                                                            // ditto (flushPolyMove)
      work.lx = x; work.ly = y;
      if (work.gate && Math.hypot(x - work.x0, y - work.y0) > TAP_PX / 2) { cancelWork(); askRestart(() => toast('Now change your polygon', 1600)); e.preventDefault(); return; }
      S.pendingPoly = { x, y }; invalidate(); e.preventDefault(); return; }
    const co = (work.type === 'draw' || !S.opt.coalesce) && e.getCoalescedEvents ? e.getCoalescedEvents().map(c => ({ x: c.clientX - r.left, y: c.clientY - r.top })) : null;
    moveWork(x, y, co); e.preventDefault();
  }
});
function release(e, cancelled) {
  if (!ptrs.has(e.pointerId)) return; ptrs.delete(e.pointerId);
  if (work && work.id === e.pointerId) { cancelled ? cancelWork() : endWork(); }
  if (nav && ptrs.size < 2) nav = null; if (refNav && ptrs.size < 2) refNav = null;
  if (ptrs.size === 0) lock = false;
}
canvas.addEventListener('pointerup', e => release(e, false));
canvas.addEventListener('pointercancel', e => release(e, true));
canvas.addEventListener('contextmenu', e => e.preventDefault());
canvas.addEventListener('wheel', e => {
  e.preventDefault(); const r = canvas.getBoundingClientRect(), x = e.clientX - r.left, y = e.clientY - r.top;
  if (e.ctrlKey) zoomAt(x, y, Math.exp(-e.deltaY * 0.01));
  else if (e.deltaMode !== 0 || (Math.abs(e.deltaY) >= 40 && e.deltaX === 0)) zoomAt(x, y, Math.exp(-e.deltaY * 0.0015));
  else { S.cam.x += e.deltaX / S.cam.s; S.cam.y -= e.deltaY / S.cam.s; clampCam(); invalidate(); }
}, { passive: false });
['gesturestart', 'gesturechange', 'gestureend'].forEach(t => document.addEventListener(t, e => e.preventDefault()));   // stop iOS page-zoom
document.addEventListener('keydown', e => { if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'z') { e.preventDefault(); const d = e.shiftKey ? 1 : -1; S.mode === 'polygon' ? polyUndoRedo(d) : applyHistory(d); } });
window.addEventListener('resize', () => { if (!S.field) return; const prevAspect = S.vw > S.vh; resize(); if (prevAspect !== (S.vw > S.vh)) fitCamera(); else { clampCam(); invalidate(); } });
window.addEventListener('orientationchange', () => setTimeout(() => { if (S.field) { resize(); fitCamera(); } }, 200));
if (window.ResizeObserver) new ResizeObserver(() => { if (S.field) { resize(); invalidate(); } }).observe($('dock'));

/* ---------------- helpers ---------------- */
const hexRgba = (hex, a) => { const n = parseInt(hex.slice(1), 16); return `rgba(${n >> 16},${(n >> 8) & 255},${n & 255},${a})`; };
function toast(msg, ms) { const t = $('toast'); t.textContent = msg; t.classList.add('on'); clearTimeout(toast.h); toast.h = setTimeout(() => t.classList.remove('on'), ms || 3200); }
function closePops() { closePalette(); closeGrp(); closeRefMore(); }
function swatchButtons(box, onPick, extra) {
  box.innerHTML = '';
  if (extra) { const b = document.createElement('button'); b.className = 'chip'; b.textContent = extra.label; b.onclick = () => onPick(null); box.appendChild(b); }
  PALETTE.forEach(c => { const b = document.createElement('button'); b.className = 'sw'; b.style.background = c; b.setAttribute('aria-label', 'Colour ' + c); b.dataset.c = c; b.onclick = () => onPick(c); box.appendChild(b); });
  const l = document.createElement('label'); l.className = 'custom'; l.innerHTML = 'Custom <input type="color" value="#1d1b18" aria-label="Custom colour">'; l.querySelector('input').oninput = ev => onPick(ev.target.value); box.appendChild(l);
}

/* ---------------- dock: three modes, contextual strips ---------------- */
const MODE_BTN = { polygon: 'mode-polygon', shape: 'mode-shape', illustrate: 'mode-illustrate', tessellate: 'mode-tess' };
const MODE_STRIP = { polygon: 'strip-polygon', shape: 'strip-shape', illustrate: 'strip-illustrate', tessellate: 'strip-tess' };
const camKey = m => m === 'polygon' ? 'shape' : m;      // Polygon and Shape share one view, so continuing to Shape shows the same tile in the same place
const HINTS = { polygon: 'Tap a side to add a point · drag points · two fingers move & zoom', shape: 'Pull the boundary · sketch what you see · two fingers move & zoom', illustrate: 'Pen, fill, dots, texture · two fingers move & zoom', tessellate: 'Tap a tile to choose its group · drag to pan · pinch to zoom' };
function setMode(m, quiet) {
  if (m === 'polygon' && !S.poly) { toast('Polygon starts from the square grid · ⋮ › New', 2400); return; }
  if (S.mode === 'polygon' && m !== 'polygon' && S.poly && !S.poly.family) { toast('First choose Translate, Rotate or Glide', 2000); return; }
  if (work) cancelWork(); closePops();
  const changed = m !== S.mode;
  if (S.field && changed) S.camByMode[camKey(S.mode)] = { ...S.cam };
  if (changed && S.mode === 'polygon') leavePolygon();          // handoff: Shape continues from exactly this polygon
  if (changed && m === 'polygon') enterPolygon();
  if (changed && S.mode === 'shape' && S.ref.img && S.ref.adjust) setRefLocked(true);   // leaving Shape never leaves the reference grabbable
  if (changed && S.mode === 'tessellate') S.sel = null;
  S.mode = m;
  Object.entries(MODE_BTN).forEach(([k, id]) => $(id).setAttribute('aria-pressed', String(k === m)));
  Object.entries(MODE_STRIP).forEach(([k, id]) => $(id).classList.toggle('on', k === m));
  document.body.dataset.mode = m;                    // lets the stylesheet show the Shape floating bar vs the Illustrate/Tessellate dock
  $('m-reset').hidden = m === 'polygon';
  if (S.field && changed) {
    const saved = S.camByMode[camKey(m)];
    S.cam = saved ? { ...saved } : (m === 'tessellate' ? { x: S.field.c0.x, y: S.field.c0.y, s: S.fitS * 0.5 } : { x: S.field.c0.x, y: S.field.c0.y, s: S.fitS });
    resize(); clampCam();
  } else resize();
  if (!quiet && !S.seenHint[m]) { S.seenHint[m] = true; toast(HINTS[m]); }
  syncSizeUI(); syncRefUI(true); invalidate();
}
Object.entries(MODE_BTN).forEach(([k, id]) => $(id).onclick = () => setMode(k));

function setShapeTool(t) {
  if (work) cancelWork(); S.shapeTool = t;
  $('st-pull').setAttribute('aria-pressed', String(t === 'pull')); $('st-sketch').setAttribute('aria-pressed', String(t === 'sketch'));
  $('seg-influence').hidden = t !== 'pull'; $('sketch-tools').hidden = t !== 'sketch';   // same box in the bar's second row: nothing moves
  syncSizeUI(); invalidate();
}
$('st-pull').onclick = () => setShapeTool('pull'); $('st-sketch').onclick = () => setShapeTool('sketch');
function setSketchTool(t) { S.sketchTool = t; $('sk-pen').setAttribute('aria-pressed', String(t === 'pen')); $('sk-eraser').setAttribute('aria-pressed', String(t === 'eraser')); }
$('sk-pen').onclick = () => setSketchTool('pen'); $('sk-eraser').onclick = () => setSketchTool('eraser');
function setInfluence(v) {             // 0 = Point … 1 = Wide ('point' / 'narrow' / 'wide' are accepted as v4's named settings)
  v = v === 'point' ? 0 : v === 'narrow' ? INFL_KNOTS[3][0] : v === 'wide' ? 1 : Math.min(1, Math.max(0, +v || 0));
  S.influenceV = v; E.setRadius(influenceRadius(v)); $('infl').value = v; store.set('tessellation.influenceWidth', v);
}
$('infl').oninput = e => { setInfluence(+e.target.value); S.inflPreview = performance.now(); invalidate(); };
$('infl').value = S.influenceV;

/* ---- ILLUSTRATE ---- */
const TOOL_BTN = { pen: 't-pen', eraser: 't-eraser', fill: 't-fill', dot: 't-dot', texture: 't-texture' };
function setTool(t) { S.tool = t; Object.entries(TOOL_BTN).forEach(([k, id]) => $(id).setAttribute('aria-pressed', String(k === t))); $('seg-pattern').hidden = t !== 'texture'; syncSizeUI(); }
Object.entries(TOOL_BTN).forEach(([k, id]) => $(id).onclick = () => setTool(k));
function setPattern(p) { S.pattern = p; document.querySelectorAll('#seg-pattern [data-p]').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.p === p))); syncSizeUI(); }
document.querySelectorAll('#seg-pattern [data-p]').forEach(b => b.onclick = () => setPattern(b.dataset.p));
function drawPreview() {                            // a tiny sample of what the current tool will make (scale, angle, opacity, colour)
  const cv = $('prevc'), c = cv.getContext('2d'), W = cv.width, t = S.tool, v = S.sizes[sizeKey()], D = 4 + 28 * v, a = t === 'eraser' ? 1 : (S.opac[t] == null ? 1 : S.opac[t]);
  c.setTransform(1, 0, 0, 1, 0, 0); c.clearRect(0, 0, W, W); c.fillStyle = '#f7f1e3'; c.fillRect(0, 0, W, W); c.fillStyle = '#e4dcc8';
  for (let y = 0; y < W; y += 11) for (let x = (y / 11) % 2 ? 11 : 0; x < W; x += 22) c.fillRect(x, y, 11, 11);                      // checker, so opacity is visible
  const st = { tool: t, pattern: S.pattern, angle: S.angle, alpha: a, color: S.color, seed: 7 };
  if (t === 'pen') { c.save(); c.globalAlpha = a; c.strokeStyle = S.color; c.lineWidth = D; c.lineCap = 'round'; c.beginPath(); c.moveTo(8, 34); c.quadraticCurveTo(18, 6, 36, 14); c.stroke(); c.restore(); }
  else if (t === 'eraser') { c.strokeStyle = '#8a8372'; c.lineWidth = 2; c.beginPath(); c.arc(W / 2, W / 2, Math.min(D / 2, 19), 0, TAU); c.stroke(); }
  else if (t === 'fill') { c.save(); c.globalAlpha = a; c.fillStyle = S.color; c.fillRect(6, 6, W - 12, W - 12); c.restore(); }
  else if (t === 'dot') { stamp(c, st, 12, 22, Math.min(D, 18), 0); stamp(c, st, 30, 22, Math.min(D, 18), 1); }
  else for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) stamp(c, st, 8 + i * 14, 8 + j * 14, Math.min(D, 22), i * 3 + j);
}
function syncSizeUI() {
  const t = S.tool, key = sizeKey(), sk = S.mode === 'shape', ill = S.mode === 'illustrate';
  $('size-sk').value = S.sizes.sketch; const pv = $('prev-sk'); pv.style.width = pv.style.height = (4 + 34 * S.sizes.sketch) + 'px'; pv.style.background = S.sketchTool === 'eraser' ? '#b9b3a4' : SKETCH_COLOR;
  if (!ill) return;
  $('sl-size').hidden = t === 'fill'; $('sl-angle').hidden = t !== 'texture'; $('sl-opac').hidden = t === 'eraser';
  $('lab-size').textContent = t === 'texture' ? 'Scale' : 'Size';
  $('size-il').value = S.sizes[key]; $('angle-il').value = S.angle; $('opac-il').value = S.opac[t] == null ? 1 : S.opac[t];
  $('colour-dot').style.background = hexRgba(S.color, t === 'eraser' ? 1 : (S.opac[t] == null ? 1 : S.opac[t])); drawPreview(); void sk;
}
const sliderToast = (name, txt) => toast(name + ' ' + txt, 900);
$('size-il').oninput = e => { S.sizes[sizeKey()] = +e.target.value; syncSizeUI(); };
$('size-sk').oninput = e => { S.sizes.sketch = +e.target.value; syncSizeUI(); };
$('angle-il').oninput = e => { S.angle = +e.target.value; syncSizeUI(); sliderToast('Angle', S.angle + '°'); };
$('opac-il').oninput = e => { S.opac[S.tool] = +e.target.value; syncSizeUI(); sliderToast('Opacity', Math.round(S.opac[S.tool] * 100) + '%'); };

function buildPalette() { swatchButtons($('swatches'), c => setColor(c)); }
function setColor(c) {
  if (!c) return; S.color = c; if (S.tool === 'eraser') setTool('pen');
  document.querySelectorAll('#swatches .sw').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.c === c))); const ci = $('swatches').querySelector('input'); if (ci) ci.value = c; syncSizeUI();
}
function closePalette() { if (!$('palette').hidden) { $('palette').hidden = true; $('colour-btn').setAttribute('aria-expanded', 'false'); } }
$('colour-btn').onclick = () => { const open = $('palette').hidden; closePops(); $('palette').hidden = !open; $('colour-btn').setAttribute('aria-expanded', String(open)); };
buildPalette(); setColor(S.color);

/* ---- REFERENCE image — one small Ref button. A practice aid: shown in Shape only; not artwork, not in history, not in the tessellation.
 *   no reference   Ref → choose an image
 *   unlocked       drag = move · two fingers = scale + turn · panel: opacity, Replace, Remove, Lock
 *   LOCKED         completely passive: no controls on screen, every touch goes to the work. Ref → unlock it to reposition / replace / remove ---- */
function setRefLocked(v) {
  const R = S.ref; if (!R.img) { R.locked = false; R.adjust = false; syncRefUI(); return; } R.locked = !!v; R.adjust = !v; syncRefUI();
}
function syncRefUI(quiet) {        // v4.3: editing swaps the bar's contents for  ⋯ | Opacity | Lock ;  locked shows only a quiet 'Ref 🔒'
  const R = S.ref, has = !!R.img, lk = has && R.locked, editing = has && !R.locked && S.mode === 'shape', b = $('ref-btn');
  $('sb-tools').hidden = editing; $('refbar').hidden = !editing; if (!editing) closeRefMore();
  b.classList.toggle('locked', lk); b.innerHTML = lk ? 'Ref ' + LOCK_SVG : 'Ref';
  b.title = !has ? 'Add a reference image' : 'Reference locked — tap to move, replace or remove it';
  b.setAttribute('aria-label', !has ? 'Add a reference image' : 'Reference locked. Tap to edit it');
  if (has) $('ref-op').value = R.alpha;
  if (!quiet) invalidate();
}
function closeRefMore() { const m = $('refmore'); if (!m.hidden) { m.hidden = true; $('ref-more').setAttribute('aria-expanded', 'false'); } }
$('ref-more').onclick = () => { const m = $('refmore'), open = m.hidden; m.hidden = !open; $('ref-more').setAttribute('aria-expanded', String(open)); };
$('ref-btn').onclick = () => {
  const R = S.ref; if (!R.img) { $('reffile').click(); return; }
  if (R.locked) { setRefLocked(false); toast('Drag to move · two fingers to scale and turn · then Lock', 2600); } else lockRef();
};
function lockRef() { setRefLocked(true); if (!S.seenHint.refLock) { S.seenHint.refLock = true; toast('Reference locked · tap Ref to move it again', 2200); } }
function loadRef(file) {
  const url = URL.createObjectURL(file), img = new Image();
  img.onload = () => {
    let src = img; const M = 2048, big = Math.max(img.width, img.height);
    if (big > M) { const c = document.createElement('canvas'), k = M / big; c.width = Math.round(img.width * k); c.height = Math.round(img.height * k); c.getContext('2d').drawImage(img, 0, 0, c.width, c.height); src = c; }   // keep memory sane
    const R = S.ref, c0 = S.field.c0; R.img = src; R.sc0 = R.sc = (S.field.size * 1.3) / Math.max(src.width, src.height); R.x = c0.x; R.y = c0.y; R.rot = 0; R.alpha = 0.45; R.visible = true; R.adjust = true; R.locked = false; R.cache = null;
    R.saved = encodeRef(src, file.type);                        // CR1: a compressed copy for the saved project
    URL.revokeObjectURL(url); if (S.mode !== 'shape') setMode('shape', true); syncRefUI(); toast('Drag to place · two fingers to scale and turn · then Lock', 4200); markDirty();
  };
  img.onerror = () => { URL.revokeObjectURL(url); toast('Could not read that image'); }; img.src = url;
}
$('reffile').onchange = e => { const f = e.target.files && e.target.files[0]; if (f) loadRef(f); e.target.value = ''; };
$('ref-lock').onclick = () => { closeRefMore(); lockRef(); };
$('ref-replace').onclick = () => { closeRefMore(); $('reffile').click(); };
$('ref-remove').onclick = () => { closeRefMore(); const R = S.ref; R.img = null; R.adjust = false; R.locked = false; R.cache = null; syncRefUI(); };
$('ref-op').oninput = e => { S.ref.alpha = +e.target.value; invalidate(); };

/* ---- TESSELLATE: colour treatment buttons now choose the GROUPING; the learner chooses the colours ---- */
const TREAT_BTN = { same: 'tr-same', alt: 'tr-alt', row: 'tr-row', col: 'tr-col' };
function setTreat(t) { S.treat = t; S.sel = null; closeGrp(); Object.entries(TREAT_BTN).forEach(([k, id]) => $(id).setAttribute('aria-pressed', String(k === t))); invalidate(); }
Object.entries(TREAT_BTN).forEach(([k, id]) => $(id).onclick = () => setTreat(k));
function groupProps(create) { if (!S.sel) return null; const m = S.comp[S.sel.mode]; if (!m[S.sel.key] && create) m[S.sel.key] = {}; return m[S.sel.key] || null; }
function setGroupProp(prop, val) {                  // COMPOSITION only: stored per group, applied at draw time, never touches geometry or artwork
  const p = groupProps(true); if (!p) return; if (val === null || val === undefined) delete p[prop]; else p[prop] = val;
  if (!Object.keys(p).length) delete S.comp[S.sel.mode][S.sel.key]; updateTitle(); syncGrpUI(); invalidate();
}
function syncGrpUI() {
  if (!S.sel) return; const p = groupProps(false) || {}, n = S.field.list.filter((m, i) => groupOf(i).key === S.sel.key).length;
  $('grp-title').textContent = S.sel.label + ' · ' + n + (n === 1 ? ' tile' : ' tiles');
  $('grp-bg').firstElementChild.style.background = p.bg || COLORS.fill; $('grp-fig').firstElementChild.style.background = p.fig || 'conic-gradient(#d94b3d,#f2c230,#6aa84f,#3b6fb6,#7a4fa3,#d94b3d)';
  $('grp-op').value = p.alpha == null ? 1 : p.alpha; $('grp-sc').value = p.scale == null ? 1 : p.scale; $('grp-hide').setAttribute('aria-pressed', String(!!p.hidden)); $('grp-hide').textContent = p.hidden ? 'Show' : 'Hide';
}
let grpTarget = null;
function openGroupPop() { closeMenu(); closePalette(); $('grp').hidden = false; $('grp-swatches').hidden = true; grpTarget = null; syncGrpUI(); }
function closeGrp() { if (!$('grp').hidden) $('grp').hidden = true; }
function pickGroupColour(target) {
  grpTarget = target; const box = $('grp-swatches'); box.hidden = false;
  swatchButtons(box, c => { setGroupProp(grpTarget, c); box.hidden = true; }, { label: target === 'bg' ? 'Default tile' : 'Original figure' });
}
$('grp-bg').onclick = () => { if (!$('grp-swatches').hidden && grpTarget === 'bg') $('grp-swatches').hidden = true; else pickGroupColour('bg'); };
$('grp-fig').onclick = () => { if (!$('grp-swatches').hidden && grpTarget === 'fig') $('grp-swatches').hidden = true; else pickGroupColour('fig'); };
$('grp-op').oninput = e => setGroupProp('alpha', +e.target.value >= 0.999 ? null : +e.target.value);
$('grp-sc').oninput = e => setGroupProp('scale', Math.abs(+e.target.value - 1) < 0.015 ? null : +e.target.value);
$('grp-hide').onclick = () => { const p = groupProps(false); setGroupProp('hidden', p && p.hidden ? null : true); };
$('grp-reset').onclick = () => { if (!S.sel) return; delete S.comp[S.sel.mode][S.sel.key]; updateTitle(); syncGrpUI(); invalidate(); };
$('grp-close').onclick = () => { S.sel = null; closeGrp(); invalidate(); };

function setGhost(g) { S.ghost = g; ['off', 'ghost', 'clear'].forEach(k => $('g-' + k).setAttribute('aria-pressed', String(k === g))); invalidate(); }
['off', 'ghost', 'clear'].forEach(k => $('g-' + k).onclick = () => setGhost(k));
$('undo').onclick = () => applyHistory(-1); $('redo').onclick = () => applyHistory(1);
$('sb-undo').onclick = () => applyHistory(-1); $('sb-redo').onclick = () => applyHistory(1);

/* ---------------- menu ---------------- */
function openMenu() { closePops(); $('menu').hidden = false; $('scrim').hidden = false; $('more').setAttribute('aria-expanded', 'true'); }
function closeMenu() { $('menu').hidden = true; $('scrim').hidden = true; $('more').setAttribute('aria-expanded', 'false'); }
$('more').onclick = () => $('menu').hidden ? openMenu() : closeMenu(); $('scrim').onclick = closeMenu;
$('m-start').onclick = () => { S.showStart = !S.showStart; $('m-start-tick').textContent = S.showStart ? 'on' : 'off'; invalidate(); };
$('m-sketch').onclick = () => { S.showSketch = !S.showSketch; syncCR2UI(); invalidate(); };      // CR2: Show sketch (Illustrate only, for tracing)
$('m-resetcomp').onclick = () => { closeMenu(); S.comp = { same: {}, alt: {}, row: {}, col: {} }; S.sel = null; closeGrp(); updateTitle(); invalidate(); };
$('m-fit').onclick = () => { closeMenu(); const m = S.mode; fitCamera(); if (m === 'tessellate') { S.cam.s = Math.max(S.fitS * 0.5, 1); clampCam(); } invalidate(); };
$('m-reset').onclick = () => {                    // restores the BOUNDARY only (v5.0: to the polygon Shape started from); sketch and artwork are untouched; undoable
  closeMenu(); const before = snapshot(), keepHist = S.history.slice(0, S.hp); restoreSnapshot(S.initialSnap);
  S.history = keepHist; S.hp = keepHist.length; pushAction({ kind: 'shape', before, after: snapshot() }); invalidate();
};
function goNew() { closeMenu(); closePops(); showEntry(1); }   // CR1: nothing is replaced until a new shape is chosen, which asks first (and offers Save project)
$('m-restore').onclick = () => { closeMenu(); restoreVersion(); };
$('m-new').onclick = goNew;                         // v4.3: the top-left '‹' (same action) is gone; New lives in the menu
$('m-lab').onclick = () => { closeMenu(); openLab(); }; $('m-about').onclick = () => { closeMenu(); $('about').hidden = false; };
$('about-back').onclick = () => { $('about').hidden = true; };

/* ---------------- entry flow: shape → transformation → workspace ---------------- */
const SHAPES = {
  square:   { name: 'Polygon', polygon: true, hint: 'Start from a square · add points (up to 40) · move corners',
    groups: [ { title: 'Translate', ids: ['translation'] }, { title: 'Rotate', ids: ['rotation-sq-ac', 'rotation-sq-bd'] }, { title: 'Glide Reflect', ids: ['glide', 'glide-both'] } ] },
  triangle: { name: 'Equilateral triangle', hint: 'Three edges, three corners',
    groups: [ { title: 'Rotate', ids: ['rotation-tri'] } ] },
  rhombus:  { name: 'Rhombus', experimental: true, hint: 'A diamond with a mirror line',
    groups: [ { title: 'Mirror', experimental: true, ids: ['reflection'] } ] }
};
const CARD = {
  translation:      { short: 'Square · Translate', title: 'Slide', sub: 'Opposite edges are the same shape, slid across.' },
  'rotation-sq-ac': { short: 'Square · Rotate', title: 'Turn about ↗ corners', sub: 'Neighbouring edges turn onto each other about the bottom-left and top-right corners.' },
  'rotation-sq-bd': { short: 'Square · Rotate (other corners)', title: 'Turn about ↖ corners', sub: 'The same idea about the other two corners.' },
  'rotation-tri':   { short: 'Triangle · Rotate', title: 'Turn', sub: 'Two edges turn about a corner; the third turns about its middle.' },
  glide:            { short: 'Square · Glide Reflect', title: 'Flip + slide · one way', sub: 'Top and bottom flip and slide; the sides just slide.' },
  'glide-both':     { short: 'Square · Glide Reflect (both)', title: 'Flip + slide · both ways', sub: 'Both pairs of edges flip and slide.' },
  reflection:       { short: 'Rhombus · Mirror (experimental)', title: 'Mirror diamond', sub: 'The diamond is symmetric about its long diagonal, then repeated by sliding. It does not make mirrored neighbours.' }
};
const cardInfo = id => CARD[id];

function edgeGroups(c) {            // same colouring rule as the baseline (pairs share a colour)
  const n = c.verts.length, groups = Array(n).fill(-1); let g = 0;
  c.rels.forEach(r => { if (r.role !== 'glue') return; const a = r.self !== undefined ? r.self : r.from, b = r.self !== undefined ? r.self : r.to;
    if (groups[a] < 0) groups[a] = g++; groups[b] = groups[a]; }); return groups;
}
function previewSVG(c) {
  const V = c.verts, xs = V.map(p => p.x), ys = V.map(p => p.y), minx = Math.min(...xs), maxx = Math.max(...xs), miny = Math.min(...ys), maxy = Math.max(...ys);
  const W = 160, H = 120, pad = 22, k = Math.min((W - 2 * pad) / (maxx - minx), (H - 2 * pad) / (maxy - miny));
  const X = x => (W - k * (maxx - minx)) / 2 + (x - minx) * k, Y = y => (H - k * (maxy - miny)) / 2 + (maxy - y) * k, n = V.length, g = edgeGroups(c);
  const cen = P(V.reduce((s, p) => s + p.x, 0) / n, V.reduce((s, p) => s + p.y, 0) / n);
  let s = `<svg viewBox="0 0 ${W} ${H}" aria-hidden="true"><polygon points="${V.map(p => X(p.x) + ',' + Y(p.y)).join(' ')}" fill="rgba(255,255,255,.07)"/>`;
  V.forEach((p, i) => { const q = V[(i + 1) % n]; s += `<line x1="${X(p.x)}" y1="${Y(p.y)}" x2="${X(q.x)}" y2="${Y(q.y)}" stroke="${GROUP_COLORS[g[i] % 4]}" stroke-width="4" stroke-linecap="round"/>`; });
  const mid = i => { const p = V[i], q = V[(i + 1) % n]; return P((p.x + q.x) / 2, (p.y + q.y) / 2); };
  const arrow = (a, b, col, dash) => { const dx = b.x - a.x, dy = b.y - a.y, d = Math.hypot(dx, dy) || 1, ux = dx / d, uy = dy / d, hx = b.x - ux * 7, hy = b.y - uy * 7;
    return `<line x1="${a.x}" y1="${a.y}" x2="${hx}" y2="${hy}" stroke="${col}" stroke-width="1.8" ${dash ? 'stroke-dasharray="4 4"' : ''}/><polygon points="${b.x},${b.y} ${hx - uy * 4},${hy + ux * 4} ${hx + uy * 4},${hy - ux * 4}" fill="${col}"/>`; };
  c.rels.forEach(r => {
    const d = r.d;
    if (d.type === 'translate') { const a = mid(r.from), b = mid(r.to); s += arrow(P(X(a.x), Y(a.y)), P(X(b.x), Y(b.y)), '#e8edf6', true); }
    else if (d.type === 'rotate') {
      const ctr = d.c, th = Math.atan2(Math.sin(d.ang), Math.cos(d.ang)), phi = Math.atan2(cen.y - ctr.y, cen.x - ctr.x), r0 = 15, a0 = phi - th / 2, a1 = phi + th / 2;
      const pt = a => P(X(ctr.x) + r0 * Math.cos(a), Y(ctr.y) - r0 * Math.sin(a));   // y flips on screen
      const p0 = pt(a0), p1 = pt(a1), large = Math.abs(th) > PI ? 1 : 0, sweep = th > 0 ? 0 : 1;
      s += `<circle cx="${X(ctr.x)}" cy="${Y(ctr.y)}" r="3.2" fill="#fff"/><path d="M${p0.x},${p0.y} A${r0},${r0} 0 ${large} ${sweep} ${p1.x},${p1.y}" fill="none" stroke="#fff" stroke-width="1.8"/>`;
      const tdir = th > 0 ? 1 : -1, ta = a1 + tdir * 0.0, tx = -Math.sin(ta) * tdir, ty = -Math.cos(ta) * tdir;   // tangent in screen space
      s += `<polygon points="${p1.x},${p1.y} ${p1.x - tx * 7 + ty * 4},${p1.y - ty * 7 - tx * 4} ${p1.x - tx * 7 - ty * 4},${p1.y - ty * 7 + tx * 4}" fill="#fff"/>`;
    } else if (d.type === 'mirror') {
      const u = P(Math.cos(d.phi), Math.sin(d.phi)), a = P(X(d.p0.x - 3 * u.x), Y(d.p0.y - 3 * u.y)), b = P(X(d.p0.x + 3 * u.x), Y(d.p0.y + 3 * u.y));
      s += `<line x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}" stroke="#a99cff" stroke-width="1.5" stroke-dasharray="5 4"/>`;
      if (d.g) { const t = (cen.x - d.p0.x) * u.x + (cen.y - d.p0.y) * u.y, pos = P(d.p0.x + u.x * t, d.p0.y + u.y * t), Ln = 0.22 * (maxx - minx), sg = Math.sign(d.g);
        s += arrow(P(X(pos.x - u.x * Ln * sg), Y(pos.y - u.y * Ln * sg)), P(X(pos.x + u.x * Ln * sg), Y(pos.y + u.y * Ln * sg)), '#a99cff', false); }
    }
  });
  return s + '</svg>';
}
function showEntry(step, shapeKey) {
  $('lab').hidden = $('about').hidden = true; $('entry').hidden = false; $('entry').scrollTop = 0;
  const body = $('entry-body'); body.innerHTML = ''; S.entryStep = step;
  if (step === 1) {
    $('entry-title').textContent = 'Choose a starting shape'; $('entry-sub').textContent = 'Everything you draw will repeat across the plane.';
    $('entry-back').hidden = !S.field; $('entry-back').onclick = () => { $('entry').hidden = true; };
    resumeCard(body);                                         // CR1: Continue (when work is kept on this device and nothing is open)
    const grid = document.createElement('div'); grid.className = 'grid';
    Object.entries(SHAPES).forEach(([key, sh]) => {
      const rep = CONS.find(c => c.id === sh.groups[0].ids[0]), b = document.createElement('button'); b.className = 'card';
      b.innerHTML = (sh.polygon ? previewPolygonSVG() : previewShapeSVG(rep)) + `<b>${sh.name}${sh.experimental ? '<span class="tag">EXPERIMENTAL</span>' : ''}</b><span>${sh.hint}</span>`;
      b.onclick = () => sh.polygon ? beginNew(startPolygon) : showEntry(2, key); grid.appendChild(b);   // CR1: asks before replacing work
    }); body.appendChild(grid); openRow(body);                 // CR1: Open a project file…
  } else {
    const sh = SHAPES[shapeKey];
    $('entry-title').textContent = 'Choose a transformation'; $('entry-sub').textContent = sh.name + ' — how do neighbouring tiles relate?';
    $('entry-back').hidden = false; $('entry-back').onclick = () => showEntry(1);
    sh.groups.forEach(grp => {
      const h = document.createElement('h2'); h.innerHTML = grp.title + (grp.experimental ? '<span class="tag">EXPERIMENTAL</span>' : ''); body.appendChild(h);
      const grid = document.createElement('div'); grid.className = 'grid';
      grp.ids.forEach(id => { const c = CONS.find(x => x.id === id), info = CARD[id], b = document.createElement('button'); b.className = 'card';
        b.innerHTML = previewSVG(c) + `<b>${info.title}</b><span>${info.sub}</span>`; b.onclick = () => beginNew(() => start(id)); grid.appendChild(b); });
      body.appendChild(grid);
    });
  }
}
function previewPolygonSVG() {         // a square with one point and its copy: what Polygon is about
  const X = x => 52 + x * 56, Y = y => 92 - y * 56, pts = [[0, 0], [0.45, -0.22], [1, 0], [1, 1], [0.45, 0.78], [0, 1]];
  return `<svg viewBox="0 0 160 120" aria-hidden="true"><polygon points="${[[0, 0], [1, 0], [1, 1], [0, 1]].map(p => X(p[0]) + ',' + Y(p[1])).join(' ')}" fill="none" stroke="rgba(255,255,255,.25)" stroke-dasharray="3 4"/>` +
    `<polygon points="${pts.map(p => X(p[0]) + ',' + Y(p[1])).join(' ')}" fill="rgba(247,241,227,.9)" stroke="#1d1b18" stroke-width="2"/>` +
    `<circle cx="${X(0.45)}" cy="${Y(-0.22)}" r="5" fill="${COLORS.start}" stroke="#fff" stroke-width="1.5"/><circle cx="${X(0.45)}" cy="${Y(0.78)}" r="4.5" fill="#fff" stroke="${COLORS.start}" stroke-width="2"/></svg>`;
}
function previewShapeSVG(c) {          // plain outline of the starting cell, no relation overlays
  const V = c.verts, xs = V.map(p => p.x), ys = V.map(p => p.y), minx = Math.min(...xs), maxx = Math.max(...xs), miny = Math.min(...ys), maxy = Math.max(...ys);
  const W = 160, H = 120, pad = 22, k = Math.min((W - 2 * pad) / (maxx - minx), (H - 2 * pad) / (maxy - miny));
  const X = x => (W - k * (maxx - minx)) / 2 + (x - minx) * k, Y = y => (H - k * (maxy - miny)) / 2 + (maxy - y) * k;
  return `<svg viewBox="0 0 ${W} ${H}" aria-hidden="true"><polygon points="${V.map(p => X(p.x) + ',' + Y(p.y)).join(' ')}" fill="rgba(247,241,227,.9)" stroke="#1d1b18" stroke-width="2"/></svg>`;
}


/* ---------------- Geometry Lab (diagnostics preserved, kept out of the creative flow) ---------------- */
let labMarks = true, labAnim = null;
function tileColorDiag(m) { const ang = Math.atan2(m[1], m[0]), k = ((Math.round(ang / (TAU / 12)) % 12) + 12) % 12; return det(m) > 0 ? `hsl(212 55% ${24 + k * 2.4}%)` : `hsl(24 70% ${26 + k * 2.4}%)`; }
function drawLabDiag() {
  const cv = $('lab-diag'), c = cv.getContext('2d'), st = E.state, til = st.tiles, W = cv.width, k = W / (5.2 * til.size), poly = E.polygon(st.edges);
  const X = p => P(W / 2 + (p.x - til.c0.x) * k, W / 2 - (p.y - til.c0.y) * k);
  c.setTransform(1, 0, 0, 1, 0, 0); c.clearRect(0, 0, W, W); c.lineJoin = 'round';
  const trace = m => { c.beginPath(); poly.forEach((p, i) => { const q = X(mapp(m, p)); i ? c.lineTo(q.x, q.y) : c.moveTo(q.x, q.y); }); c.closePath(); };
  til.list.forEach(m => { trace(m); c.fillStyle = tileColorDiag(m); c.fill(); c.strokeStyle = 'rgba(244,202,114,.85)'; c.lineWidth = 1; c.stroke(); });
  const MOTIF = [[0, -0.5], [0, 0.5], [0.35, 0.5], null, [0, 0.08], [0.26, 0.08]]; c.strokeStyle = 'rgba(255,255,255,.75)'; c.lineWidth = 1.6; c.lineCap = 'round';
  til.list.forEach(m => { c.beginPath(); let pen = false; MOTIF.forEach(q => { if (!q) { pen = false; return; } const p = X(mapp(m, P(til.c0.x + q[0] * til.size * 0.2, til.c0.y + q[1] * til.size * 0.2))); pen ? c.lineTo(p.x, p.y) : c.moveTo(p.x, p.y); pen = true; }); c.stroke(); });
  trace(IDM); c.strokeStyle = '#fff'; c.lineWidth = 2.2; c.stroke();
  if (!labMarks) return;
  const half = til.size * 0.5, seen = new Set(), key = (a, b) => [a, b].map(p => Math.round(p.x * 200) + ',' + Math.round(p.y * 200)).sort().join('|');
  st.rels.forEach(r => {
    if (r.d.type === 'mirror') { const u = P(Math.cos(r.d.phi), Math.sin(r.d.phi)), t = (til.c0.x - r.d.p0.x) * u.x + (til.c0.y - r.d.p0.y) * u.y, q = P(r.d.p0.x + u.x * t, r.d.p0.y + u.y * t);
      til.list.forEach(m => { const a = mapp(m, P(q.x - u.x * half, q.y - u.y * half)), b = mapp(m, P(q.x + u.x * half, q.y + u.y * half)), kk = key(a, b); if (seen.has(kk)) return; seen.add(kk);
        const A = X(a), B = X(b); c.setLineDash([7, 5]); c.lineWidth = 1.8; c.strokeStyle = 'rgba(15,12,30,.8)'; c.beginPath(); c.moveTo(A.x, A.y); c.lineTo(B.x, B.y); c.stroke(); c.lineWidth = 1.2; c.strokeStyle = '#d9d1ff'; c.beginPath(); c.moveTo(A.x, A.y); c.lineTo(B.x, B.y); c.stroke(); c.setLineDash([]); }); }
    else if (r.d.type === 'rotate') til.list.forEach(m => { const p = mapp(m, r.d.c), kk = 'c' + Math.round(p.x * 200) + ',' + Math.round(p.y * 200); if (seen.has(kk)) return; seen.add(kk);
      const q = X(p); c.fillStyle = '#fff'; c.strokeStyle = 'rgba(15,12,30,.9)'; c.lineWidth = 1.5; c.beginPath(); c.arc(q.x, q.y, 4, 0, TAU); c.fill(); c.stroke(); });
  });
}
function drawLabCell(t, rel) {
  const cv = $('lab-cell'), c = cv.getContext('2d'), st = E.state, W = cv.width, til = st.tiles, k = W / (3.2 * til.size), poly = E.polygon(st.edges);
  const X = p => P(W / 2 + (p.x - til.c0.x) * k, W / 2 - (p.y - til.c0.y) * k);
  c.setTransform(1, 0, 0, 1, 0, 0); c.clearRect(0, 0, W, W); c.lineJoin = 'round';
  const path = (f) => { c.beginPath(); poly.forEach((p, i) => { const q = X(f(p)); i ? c.lineTo(q.x, q.y) : c.moveTo(q.x, q.y); }); c.closePath(); };
  path(p => p); c.fillStyle = 'rgba(247,241,227,.9)'; c.fill(); c.strokeStyle = '#1d1b18'; c.lineWidth = 2; c.stroke();
  if (rel) { path(p => E.applyAt(rel.d, p, t)); c.setLineDash([8, 6]); c.strokeStyle = '#f4ca72'; c.lineWidth = 2.5; c.stroke(); c.setLineDash([]); }
}
function playLab(i) {
  const rel = E.state.rels[i], t0 = performance.now(); labAnim = { i };
  const step = () => { if (!labAnim || labAnim.i !== i) return; const t = Math.min(1, (performance.now() - t0) / 1800); drawLabCell(t, rel); if (t < 1) { requestAnimationFrame(step); setTimeout(() => { if (labAnim && labAnim.i === i && performance.now() - t0 < 1900) step(); }, 40); } else setTimeout(() => { if (labAnim && labAnim.i === i) { labAnim = null; drawLabCell(0, null); } }, 900); };
  step();
}
function refreshLab() {
  const v = E.verify(), tb = document.querySelector('#lab-rels tbody'), nm = i => 'ABCD'[i] + 'ABCD'[(i + 1) % E.state.cons.verts.length]; tb.innerHTML = '';
  v.rows.forEach(({ r, res }, i) => { const m = E.measure(r.m), tr = document.createElement('tr'), label = r.self !== undefined ? `${nm(r.self)}: half ↔ half` : `${nm(r.from)} ↔ ${nm(r.to)}${r.role === 'constraint' ? ' (mirror twin)' : ''}`;
    tr.innerHTML = `<td>${label}</td><td>${m.text}</td><td>${m.orient}</td><td><span class="pill ${res < 1e-9 ? 'ok' : 'bad'}">${res.toExponential(1)}</span></td><td><button data-i="${i}" style="min-height:36px">▶</button></td>`; tb.appendChild(tr); });
  tb.querySelectorAll('button').forEach(b => b.onclick = () => playLab(+b.dataset.i));
  const good = v.cov.gap < 0.15 && v.cov.overlap < 0.15, goodA = Math.abs(v.areaRatio - 1) < 1e-3;
  $('lab-cover').innerHTML = `<span>Tiling check</span><span class="pill ${good ? 'ok' : 'bad'}">gap ${v.cov.gap.toFixed(2)}% · overlap ${v.cov.overlap.toFixed(2)}%</span><span>Area</span><span class="pill ${goodA ? 'ok' : 'bad'}">${v.areaRatio.toFixed(4)}×</span>`;
  drawLabDiag(); drawLabCell(0, null);
}
function openLab() { $('lab').hidden = false; $('lab').scrollTop = 0; refreshLab(); syncGuardUI(); }
$('lab-back').onclick = () => { $('lab').hidden = true; labAnim = null; invalidate(); };
function syncGuardUI() {
  const b = $('lab-guard'), L = S.guardLog.slice(-30), ms = L.map(r => r.p95).sort((a, c) => a - c);
  b.setAttribute('aria-pressed', String(S.guardShape)); b.textContent = 'Shape guard: ' + (S.guardShape ? 'on' : 'off');
  $('lab-guard-stat').textContent = L.length ? `last ${L.length} pulls · guard time per frame p95 ${ms[Math.floor(ms.length * 0.95)] || 0} ms (worst pull) · stopped at contact in ${L.filter(r => r.blocked).length}` : 'no pulls measured yet';
}
$('lab-guard').onclick = () => { S.guardShape = !S.guardShape; syncGuardUI(); };
$('lab-marks').onclick = e => { labMarks = !labMarks; e.currentTarget.setAttribute('aria-pressed', String(labMarks)); drawLabDiag(); };
function runSelfTestSafely() {            // the engine's selfTest rebuilds every construction; keep the user's shape and influence intact
  const id = S.consId, snap = snapshot(), keepR = E.getRadius(); E.setRadius(0.2);
  try { return E.selfTest(); } finally { E.setRadius(keepR); if (id) { buildCurrent(); restoreSnapshot(snap); } }
}
$('lab-selftest').onclick = () => {
  const res = runSelfTestSafely(), t = $('lab-self'); t.hidden = false;
  t.querySelector('tbody').innerHTML = res.map(r => `<tr><td>${r.title}</td><td>${r.edits}</td><td>${r.maxRes.toExponential(1)}</td><td>${r.gap.toFixed(2)}</td><td>${r.overlap.toFixed(2)}</td><td><span class="pill ${r.ok ? 'ok' : 'bad'}">${r.ok ? 'pass' : 'FAIL'}</span></td></tr>`).join('');
  refreshLab(); invalidate();
};

const proofRow = (label, r) => `<tr><td>${label}</td><td>${r.tiles}</td><td>${r.collisions}</td><td>${r.edgesTwice} / ${r.edgesOnce} / ${r.edgesMore}</td><td>${r.vertsBad} of ${r.vertsChecked}</td><td>${r.maxMismatch.toExponential(1)}</td><td><span class="pill ${r.ok ? 'ok' : 'bad'}">${r.ok ? 'pass' : 'FAIL'}</span></td></tr>`;
function showProof(rows) { const t = $('lab-proof'); t.hidden = false; t.querySelector('tbody').innerHTML = rows.join(''); }
$('lab-proof-now').onclick = () => showProof([proofRow(E.state.cons.id + ' · now', TilingCheck.check())]);
function seededRnd(seed) { let s = seed; return () => (s = (s * 1664525 + 1013904223) % 4294967296) / 4294967296; }
function runProofAll(edits) {                    // rebuilds every construction; the user's shape is restored afterwards
  const id = S.consId, snap = snapshot(), keepR = E.getRadius(), rows = [], rnd = seededRnd(11);
  try {
    E.CONS.filter(c => c.id !== LIVE_ID || S.engineId === LIVE_ID).forEach(c => {
      E.build(c.id); rows.push(proofRow((c.id === LIVE_ID ? 'current moved cage (' + S.consId + ')' : c.id) + ' · straight', TilingCheck.check()));
      ['narrow', 'wide'].forEach(k => { E.build(c.id); E.setRadius(INFLUENCE[k]);
        for (let i = 0; i < edits; i++) { const a = rnd() * TAU, mag = (0.03 + rnd() * 0.07) * E.state.tiles.size; E.applyEdit(Math.floor(rnd() * c.verts.length), 0.15 + rnd() * 0.7, Math.cos(a) * mag, Math.sin(a) * mag); }
        rows.push(proofRow((c.id === LIVE_ID ? 'current moved cage (' + S.consId + ')' : c.id) + ' · ' + edits + ' edits · ' + k, TilingCheck.check())); });
    });
  } finally { E.setRadius(keepR); if (id) { buildCurrent(); restoreSnapshot(snap); } }
  return rows;
}
$('lab-proof-all').onclick = () => showProof(runProofAll(40));


/* ---------------- SVG feasibility (Geometry Lab): can the CURRENT deformed boundary be written as an SVG path
 * that still satisfies the exact linked-edge transformations? Reports the answer; no export UI beyond this. ---------------- */
function catmullBezier(pts) {                      // interpolating cubic Béziers through the edge samples (affine-covariant, reversal-symmetric)
  return pts.slice(0, -1).map((_, i) => { const a = pts[Math.max(0, i - 1)], b = pts[i], c = pts[i + 1], d = pts[Math.min(pts.length - 1, i + 2)];
    const t0 = i === 0 ? P(c.x - b.x, c.y - b.y) : P((c.x - a.x) / 2, (c.y - a.y) / 2), t1 = i + 1 === pts.length - 1 ? P(c.x - b.x, c.y - b.y) : P((d.x - b.x) / 2, (d.y - b.y) / 2);
    return [b, P(b.x + t0.x / 3, b.y + t0.y / 3), P(c.x - t1.x / 3, c.y - t1.y / 3), c]; });
}
function svgBoundary(kind, dec) {
  const edges = E.state.edges, n = edges.length, f = v => v.toFixed(dec), X = p => f(p.x) + ' ' + f(-p.y);   // SVG y points down
  let d;
  if (kind === 'poly') d = edges.flatMap(e => e.pts.slice(0, N)).map((p, i) => (i ? 'L' : 'M') + X(p)).join('') + 'Z';
  else d = 'M' + X(edges[0].pts[0]) + edges.map(e => catmullBezier(e.pts).map(g => 'C' + X(g[1]) + ' ' + X(g[2]) + ' ' + X(g[3])).join('')).join('') + 'Z';
  const all = edges.flatMap(e => e.pts), xs = all.map(p => p.x), ys = all.map(p => -p.y), pad = 0.05, x0 = Math.min(...xs) - pad, y0 = Math.min(...ys) - pad, w = Math.max(...xs) - Math.min(...xs) + 2 * pad, h = Math.max(...ys) - Math.min(...ys) + 2 * pad;
  const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="${f(x0)} ${f(y0)} ${f(w)} ${f(h)}"><path d="${d}" fill="#f7f1e3" stroke="#1d1b18" stroke-width="0.01" stroke-linejoin="round"/></svg>`;
  // exactness: re-read the numbers from the path text and measure every linked-edge relation on what was written
  let mismatch = 0;
  if (kind === 'poly') {
    const nums = [...d.matchAll(/[ML](-?[\d.]+) (-?[\d.]+)/g)].map(m => P(+m[1], -+m[2])), back = [];
    for (let e = 0; e < n; e++) { const pts = nums.slice(e * N, (e + 1) * N); pts.push(nums[((e + 1) * N) % nums.length]); back.push({ pts }); }
    E.state.rels.forEach(rl => {
      if (rl.self !== undefined) { const p = back[rl.self].pts; p.forEach((q, k) => mismatch = Math.max(mismatch, Math.hypot(E.mapp(rl.m, q).x - p[N - k].x, E.mapp(rl.m, q).y - p[N - k].y))); return; }
      const a = back[rl.from].pts, b = back[rl.to].pts; a.forEach((q, k) => { const m = E.mapp(rl.m, q), t = b[rl.rev ? N - k : k]; mismatch = Math.max(mismatch, Math.hypot(m.x - t.x, m.y - t.y)); }); });
  } else {
    E.state.rels.forEach(rl => { if (rl.self !== undefined) return; const A = catmullBezier(edges[rl.from].pts).map(g => g.map(p => E.mapp(rl.m, p))); let B = catmullBezier(edges[rl.to].pts); if (rl.rev) B = B.map(g => [...g].reverse()).reverse();
      A.forEach((g, i) => g.forEach((p, j) => mismatch = Math.max(mismatch, Math.hypot(p.x - B[i][j].x, p.y - B[i][j].y)))); });
  }
  return { d, svg, nodes: kind === 'poly' ? n * N : n * N * 3 + 1, chars: d.length, mismatch };
}
function showSvg(kind) {
  const dec = +$('svg-dec').value, r = svgBoundary(kind, dec), tol = Math.pow(10, -(dec - 1));
  $('svg-text').value = r.svg; $('svg-preview').innerHTML = r.svg.replace('<svg ', '<svg style="width:100%;height:auto" ');
  $('svg-status').innerHTML = `${kind === 'poly' ? 'Polyline' : 'Smooth Bézier'} · ${r.nodes} nodes · ${r.chars} chars · linked-edge mismatch ${r.mismatch.toExponential(1)} ` +
    `<span class="pill ${r.mismatch <= tol ? 'ok' : 'bad'}">${r.mismatch <= tol ? 'exact to ' + dec + ' decimals' : 'rounding visible'}</span>`;
}
$('svg-poly').onclick = () => showSvg('poly'); $('svg-smooth').onclick = () => showSvg('smooth');

/* ================= CR1 · KEEP THE WORK: automatic save, recovery, Save project / Open project… =================
 * captureProject() writes the COMPLETE project (format: CR1_PROJECT_FORMAT.md) from the app's state. applyProject() rebuilds it with the
 * app's own functions: the construction (start + setCage), the boundary written back exactly, and the history REPLAYED through the same
 * deterministic drawing code that Undo uses, so the geometry and the artwork come back identical.
 * Saving on this device happens only when no finger is on the work: about 0.7 s after the last change (at the next pause between strokes
 * once changes have waited 2 s), and at once when the page is hidden. Nothing here runs while a stroke, pull or drag is under way. */
const TP = window.TessProject, SAMPLES = N + 1, BUILD = 'v5.4-cr3';
const STAGES = ['polygon', 'shape', 'illustrate', 'tessellate'], STAGE_NAME = { polygon: 'Polygon', shape: 'Shape', illustrate: 'Illustrate', tessellate: 'Tessellate' };
const RULE_FAMILY = { ...POLY_FAMILY_OF, 'rotation-tri': 'rotate', reflection: 'mirror' };
const keep = { dirty: false, dirtyAt: 0, timer: 0, saving: false, again: false, lastAt: 0, lastOk: null, failNoted: false, retry: 0,
  thumb: null, thumbAt: -1e9, thumbCanvas: null, thumbTimer: 0, thumbMs: 0, touchAt: 0, workAt: 0, stats: [], stored: null, restoreMs: [] };
let restoring = false;

/* ---- encoding: boundaries and stroke points become Float64Arrays (exact); each is made once and reused by every later save ---- */
const encCache = new WeakMap();            // a boundary snapshot or a history step → its encoded form (neither is ever changed once made)
function fnv32(a) { const u = new Uint32Array(a.buffer, a.byteOffset, a.length * 2); let h = 2166136261 >>> 0; for (let i = 0; i < u.length; i++) { h ^= u[i]; h = Math.imul(h, 16777619) >>> 0; } return h; }
function sameF64(a, b) { if (a.length !== b.length) return false; const u = new Uint32Array(a.buffer, a.byteOffset, a.length * 2), v = new Uint32Array(b.buffer, b.byteOffset, b.length * 2); for (let i = 0; i < u.length; i++) if (u[i] !== v[i]) return false; return true; }
function snapEntry(snap) {
  let e = encCache.get(snap); if (e) return e;
  const a = new Float64Array(snap.length * SAMPLES * 2); let k = 0;
  for (const pts of snap) { if (pts.length !== SAMPLES) throw new Error('unexpected boundary sampling'); for (const p of pts) { a[k++] = p.x; a[k++] = p.y; } }
  e = { f64: a, h: fnv32(a) }; encCache.set(snap, e); return e;
}
function ptsF64(pts) { const a = new Float64Array(pts.length * 2); pts.forEach((p, i) => { a[2 * i] = p.x; a[2 * i + 1] = p.y; }); return a; }
function f64Pts(a) { const out = []; for (let i = 0; i < a.length; i += 2) out.push(P(a[i], a[i + 1])); return out; }
function f64Snap(a, sides) { const out = []; for (let s = 0; s < sides; s++) { const pts = []; for (let i = 0; i < SAMPLES; i++) { const k = 2 * (s * SAMPLES + i); pts.push(P(a[k], a[k + 1])); } out.push(pts); } return out; }
const STROKE_KEYS = ['layer', 'tool', 'pattern', 'angle', 'seed', 'color', 'alpha', 'w', 'stage', 'seq'];   // (CR3: stage, seq)
function stepEntry(a) {
  let e = encCache.get(a); if (e) return e;
  if (a.kind === 'stroke') { const o = { kind: 'stroke' }; STROKE_KEYS.forEach(k => { if (a[k] !== undefined) o[k] = a[k]; }); o.pts = ptsF64(a.pts); e = { o, snaps: [] }; }
  else if (a.kind === 'fill') e = { o: Object.assign({ kind: 'fill', color: a.color, alpha: a.alpha, seed: { x: a.seed.x, y: a.seed.y }, respectSketch: !!a.respectSketch }, a.edge ? { edge: 1 } : {}), snaps: a.snap ? [['snap', a.snap]] : [] };
  else if (a.kind === 'shape') e = { o: { kind: 'shape' }, snaps: [['before', a.before], ['after', a.after]] };
  else throw new Error('unknown history step: ' + a.kind);
  encCache.set(a, e); return e;
}
const titleNow = () => (S.poly && !S.poly.family ? 'Polygon' : cardInfo(S.consId).short);
const hasWorkNow = () => !!S.field && (S.history.length > 0 || !!S.recovery || !!S.ref.img || (!!S.poly && S.poly.hist.length > 1) || Object.values(S.comp).some(m => Object.keys(m).length > 0));
const summaryNow = () => ({ title: titleNow(), stage: S.mode, steps: S.hp, sides: S.poly ? sideCount(S.poly.nodes) : E.state.edges.length, cornersMoved: !!S.cageNow, hasWork: hasWorkNow() });

function captureProject() {                // the complete project, as plain data (+ typed arrays); reads the app's state and changes nothing
  const snaps = [], byEntry = new Map(), byHash = new Map();
  const sid = snap => {                    // boundaries are stored once each and referred to by number (most pulls share one with the step before)
    if (!snap) return null; const e = snapEntry(snap); let i = byEntry.get(e); if (i !== undefined) return i;
    const list = byHash.get(e.h) || []; const same = list.find(x => sameF64(x.f64, e.f64));
    if (same) { encCache.set(snap, same); return byEntry.get(same); }
    i = snaps.length; snaps.push(e.f64); byEntry.set(e, i); list.push(e); byHash.set(e.h, list); return i;
  };
  const steps = [], byStep = new Map();
  const step = a => { let i = byStep.get(a); if (i !== undefined) return i; const e = stepEntry(a), o = e.snaps.length ? { ...e.o } : e.o;
    e.snaps.forEach(([k, s]) => { o[k] = sid(s); }); i = steps.length; steps.push(o); byStep.set(a, i); return i; };
  const polyState = st => Object.assign({ construction: st.consId, family: st.family || null, corners: st.cage && !isSquare(st.cage) ? st.cage.map(q => ({ x: q.x, y: q.y })) : null, points: cloneNodes(st.nodes || {}) }, st.seq ? { seq: st.seq } : {});   // (CR3: seq)
  const cam = c => ({ x: c.x, y: c.y, s: c.s }), Pl = S.poly, R = S.ref, V = S.recovery, cameras = {};
  Object.keys(S.camByMode).forEach(k => { if (S.camByMode[k]) cameras[k] = cam(S.camByMode[k]); });
  const p = {
    format: TP.FORMAT, version: TP.VERSION, saved: new Date().toISOString(), app: { name: 'Escher tessellation workspace', build: BUILD },
    summary: summaryNow(),
    geometry: {
      path: Pl ? 'polygon' : 'shape', base: S.cellKind, opened: Pl ? 'translation' : S.consId,
      rule: Pl && !Pl.family ? null : { id: S.consId, family: Pl ? Pl.family : (RULE_FAMILY[S.consId] || null) },
      construction: { id: S.consId, corners: cageNow().map(q => ({ x: q.x, y: q.y })), cornersMoved: !!S.cageNow,
        relations: E.state.rels.map(r => ({ from: r.self !== undefined ? r.self : r.from, to: r.self !== undefined ? r.self : r.to, role: r.role, self: r.self !== undefined, reversed: !!r.rev, matrix: Array.from(r.m) })) },
      points: Pl ? cloneNodes(Pl.nodes) : {},
      unit: { tiles: 1, sharedSides: [] },
      sides: E.state.edges.length, samplesPerSide: SAMPLES,
      boundary: sid(snapshot()), shapeStart: sid(S.initialSnap)
    },
    polygon: Pl ? { history: Pl.hist.map(polyState), position: Pl.hp, shapeBuiltOn: S.shapeBaseKey, shapeAside: sid(S.refined), changeConfirmed: !!S.restartOK } : null,
    history: { steps: S.history.map(step), position: S.hp },
    previousVersion: V ? { polygon: { history: V.poly.hist.map(polyState), position: V.poly.hp }, history: { steps: V.history.map(step), position: V.hp },
      shapeStart: sid(V.initialSnap), boundary: sid(V.edges), shapeBuiltOn: V.baseKey, summary: { shapeEdits: V.shapeEdits, sides: V.sides, cornersMoved: !!V.moved } } : null,
    composition: { grouping: S.treat, groups: JSON.parse(JSON.stringify(S.comp)), outline: S.outline },
    view: { stage: S.mode, camera: cam(S.cam), cameras, neighbours: S.ghost, showStartingShape: !!S.showStart, showSketch: !!S.showSketch },
    tools: { shape: S.shapeTool, sketch: S.sketchTool, illustrate: S.tool, pattern: S.pattern, colour: S.color, sizes: { ...S.sizes }, opacity: { ...S.opac }, textureAngle: S.angle, influence: S.influenceV, guard: !!S.guardShape },
    hints: { ...S.seenHint },
    reference: R.img && R.saved ? { image: { type: R.saved.type, bytes: R.saved.bytes }, x: R.x, y: R.y, scale: R.sc, startScale: R.sc0, rotation: R.rot, opacity: R.alpha, visible: R.visible !== false, locked: !!R.locked } : null
  };
  p.process = captureJournal(step);            // CR3: the process recording (refers to the steps table)
  p.steps = steps; p.snapshots = snaps; return p;
}

/* ---- decoding: every part is checked before anything in the app changes; a damaged project is refused with the reason ---- */
function decodeProject(p) {
  const need = (c, why) => { if (!c) throw new Error(why); }, fin = v => typeof v === 'number' && Number.isFinite(v), obj = v => !!v && typeof v === 'object' && !Array.isArray(v);
  const hex = c => typeof c === 'string' && /^#[0-9a-f]{6}$/i.test(c), unit01 = v => fin(v) && v >= 0 && v <= 1;
  const g = p.geometry; need(obj(g), 'the tile geometry is missing');
  if (g.unit && ((g.unit.tiles || 1) !== 1 || (g.unit.sharedSides || []).length)) throw Object.assign(new Error('it uses a two-tile unit'), { newer: true });
  need(g.samplesPerSide === SAMPLES, 'the boundary is sampled differently');
  const polygon = g.path === 'polygon'; need(polygon || g.path === 'shape', 'the starting path is unknown');
  const C = g.construction; need(obj(C), 'the construction is missing');
  const known = id => typeof id === 'string' && id !== LIVE_ID && CONS.some(c => c.id === id);
  need(known(C.id), 'the construction is unknown'); if (polygon) need(POLY_FAMILY_OF[C.id], 'the construction does not fit a polygon');
  const startId = polygon ? 'translation' : C.id, sides = CONS.find(c => c.id === startId).verts.length;
  need(g.sides === undefined || g.sides === sides, 'the number of sides does not fit the construction');
  const pt = q => { need(obj(q) && fin(q.x) && fin(q.y), 'a corner is damaged'); return P(q.x, q.y); };
  const corners = c => { need(Array.isArray(c) && c.length === sides, 'the corners are damaged'); return c.map(pt); };
  const nodes = v => { need(obj(v), 'the points are damaged'); const o = {};
    Object.keys(v).forEach(m => { need(/^\d$/.test(m) && +m < sides && Array.isArray(v[m]), 'a point is on an unknown side'); if (!v[m].length) return;
      o[m] = v[m].map(n => { need(obj(n) && fin(n.s) && fin(n.t), 'a point is damaged'); return { s: n.s, t: n.t, c: !!n.c }; }); });
    return o; };
  const polyState = st => { need(obj(st) && POLY_FAMILY_OF[st.construction] && (st.family === null || st.family === POLY_FAMILY_OF[st.construction]), 'the polygon history is damaged');
    const o = { consId: st.construction, family: st.family, cage: st.corners ? corners(st.corners) : null, nodes: nodes(st.points || {}) }; if (Number.isInteger(st.seq) && st.seq > 0) o.seq = st.seq; return o; };   // (CR3: seq)
  need(Array.isArray(p.snapshots), 'the boundaries are missing');
  const snaps = p.snapshots.map((a, i) => { need(a instanceof Float64Array && a.length === sides * SAMPLES * 2 && a.every(Number.isFinite), 'boundary ' + (i + 1) + ' is damaged');
    const sn = f64Snap(a, sides); encCache.set(sn, { f64: a, h: fnv32(a) }); return sn; });          // (already encoded: the next save reuses it)
  const snap = (i, optional) => { if (i === null || i === undefined) { need(optional, 'a boundary is missing'); return null; } need(Number.isInteger(i) && i >= 0 && i < snaps.length, 'a boundary is missing'); return snaps[i]; };
  need(Array.isArray(p.steps), 'the history is missing');
  const steps = p.steps.map((o, i) => {
    const bad = 'history step ' + (i + 1) + ' is damaged'; need(obj(o), bad);
    if (o.kind === 'stroke') {
      need((o.layer === 'sketch' || o.layer === 'art') && ['pen', 'eraser', 'dot', 'texture'].includes(o.tool) && hex(o.color) && fin(o.alpha) && fin(o.w) && o.w > 0, bad);
      need(o.pts instanceof Float64Array && o.pts.length >= 2 && o.pts.length % 2 === 0 && o.pts.every(Number.isFinite), bad);
      if (o.tool === 'texture') need(SPACING[o.pattern] !== undefined && fin(o.angle), bad);
      if (o.seed !== undefined) need(Number.isInteger(o.seed) && o.seed >= 0, bad);
      if (o.stage !== undefined) need(o.stage === 'polygon', bad); if (o.seq !== undefined) need(Number.isInteger(o.seq) && o.seq >= 0, bad);   // (CR3)
      const st = { kind: 'stroke' }, eo = { kind: 'stroke' }; STROKE_KEYS.forEach(k => { if (o[k] !== undefined) st[k] = eo[k] = o[k]; }); st.pts = f64Pts(o.pts); eo.pts = o.pts;
      encCache.set(st, { o: eo, snaps: [] }); return st;
    }
    if (o.kind === 'fill') { need(hex(o.color) && fin(o.alpha) && obj(o.seed) && fin(o.seed.x) && fin(o.seed.y), bad);
      const a = { kind: 'fill', color: o.color, alpha: o.alpha, seed: P(o.seed.x, o.seed.y), respectSketch: !!o.respectSketch }, s = snap(o.snap, true); if (o.edge === 1) a.edge = 1; if (s) a.snap = s;   // (CR2: edge)
      encCache.set(a, { o: Object.assign({ kind: 'fill', color: a.color, alpha: a.alpha, seed: { x: a.seed.x, y: a.seed.y }, respectSketch: a.respectSketch }, a.edge ? { edge: 1 } : {}), snaps: s ? [['snap', s]] : [] }); return a; }
    if (o.kind === 'shape') { const a = { kind: 'shape', before: snap(o.before), after: snap(o.after) }; encCache.set(a, { o: { kind: 'shape' }, snaps: [['before', a.before], ['after', a.after]] }); return a; }
    throw new Error(bad);
  });
  const hist = (h, what) => { need(obj(h) && Array.isArray(h.steps) && Number.isInteger(h.position) && h.position >= 0 && h.position <= h.steps.length, what + ' is damaged');
    return { list: h.steps.map(k => { need(Number.isInteger(k) && k >= 0 && k < steps.length, what + ' is damaged'); return steps[k]; }), hp: h.position }; };
  const polyHist = (q, what) => { need(obj(q) && Array.isArray(q.history) && q.history.length > 0 && Number.isInteger(q.position) && q.position >= 0 && q.position < q.history.length, what + ' is damaged');
    return { hist: q.history.map(polyState), hp: q.position }; };
  const cur = { consId: C.id, cage: C.cornersMoved ? corners(C.corners) : null, family: polygon && g.rule ? g.rule.family : null, nodes: polygon ? nodes(g.points || {}) : {} };
  if (polygon) need(cur.family === null || cur.family === POLY_FAMILY_OF[C.id], 'the rule does not fit the construction');
  let poly = null, recovery = null;
  if (polygon) { const q = p.polygon, h = polyHist(q, 'the polygon history');
    poly = { ...h, builtOn: typeof q.shapeBuiltOn === 'string' ? q.shapeBuiltOn : null, aside: snap(q.shapeAside, true), confirmed: !!q.changeConfirmed };
    const V = p.previousVersion;
    if (V) { need(obj(V), 'the previous version is damaged'); const ph = polyHist(V.polygon, 'the previous version'), h2 = hist(V.history, 'the previous version'), sm = obj(V.summary) ? V.summary : {};
      recovery = { poly: ph, history: h2.list, hp: h2.hp, initialSnap: snap(V.shapeStart), edges: snap(V.boundary), baseKey: typeof V.shapeBuiltOn === 'string' ? V.shapeBuiltOn : null,
        shapeEdits: Number.isInteger(sm.shapeEdits) ? sm.shapeEdits : 0, sides: Number.isInteger(sm.sides) ? sm.sides : 4, moved: !!sm.cornersMoved }; } }
  let ref = null; const r = p.reference;
  if (r) { need(obj(r) && obj(r.image) && (r.image.type === 'image/jpeg' || r.image.type === 'image/png') && r.image.bytes instanceof Uint8Array && r.image.bytes.length > 0 && [r.x, r.y, r.scale, r.rotation, r.opacity].every(fin) && r.scale > 0, 'the reference image is damaged');
    ref = { type: r.image.type, bytes: r.image.bytes, x: r.x, y: r.y, sc: r.scale, sc0: fin(r.startScale) && r.startScale > 0 ? r.startScale : r.scale, rot: r.rotation, alpha: Math.min(1, Math.max(0, r.opacity)), visible: r.visible !== false, locked: !!r.locked }; }
  // settings: never a reason to refuse a project; anything missing or odd keeps the current setting
  const soft = { comp: { same: {}, alt: {}, row: {}, col: {} } }, cp = obj(p.composition) ? p.composition : {};
  if (obj(cp.groups)) Object.keys(soft.comp).forEach(m => { const src = cp.groups[m]; if (!obj(src)) return;
    Object.keys(src).forEach(k => { const q = src[k]; if (!obj(q)) return; const o = {}, good = { bg: hex, fig: hex, alpha: unit01, scale: v => fin(v) && v > 0, hidden: v => v === true };
      Object.keys(q).forEach(prop => { if (good[prop] && good[prop](q[prop])) o[prop] = q[prop]; });          // (kept in the saved order)
      if (Object.keys(o).length) soft.comp[m][k] = o; }); });
  soft.treat = TREAT_BTN[cp.grouping] ? cp.grouping : 'same';
  const vw = obj(p.view) ? p.view : {}, camOK = c => obj(c) && fin(c.x) && fin(c.y) && fin(c.s) && c.s > 0;
  let stage = STAGES.includes(vw.stage) ? vw.stage : (polygon ? 'polygon' : 'shape'); if (stage === 'polygon' && !polygon) stage = 'shape'; if (polygon && !cur.family) stage = 'polygon';
  soft.stage = stage; soft.cam = camOK(vw.camera) ? { x: vw.camera.x, y: vw.camera.y, s: vw.camera.s } : null; soft.cams = {};
  if (obj(vw.cameras)) ['shape', 'illustrate', 'tessellate'].forEach(k => { const c = vw.cameras[k]; if (camOK(c)) soft.cams[k] = { x: c.x, y: c.y, s: c.s }; });
  soft.ghost = ['off', 'ghost', 'clear'].includes(vw.neighbours) ? vw.neighbours : S.ghost; soft.showStart = vw.showStartingShape === true; soft.showSketch = vw.showSketch === true;   // (CR1's sketchInTessellate is no longer used)
  soft.outline = unit01(cp.outline) ? cp.outline : OUTLINE_DEFAULT;                               // CR2 (a CR1 file has no outline: today's look)
  const t = obj(p.tools) ? p.tools : {};
  soft.tools = { shape: t.shape === 'sketch' ? 'sketch' : 'pull', sketch: t.sketch === 'eraser' ? 'eraser' : 'pen', illustrate: TOOL_BTN[t.illustrate] ? t.illustrate : S.tool,
    pattern: SPACING[t.pattern] !== undefined ? t.pattern : S.pattern, colour: hex(t.colour) ? t.colour : S.color, angle: fin(t.textureAngle) ? t.textureAngle : S.angle,
    influence: unit01(t.influence) ? t.influence : null, guard: t.guard !== false, sizes: {}, opac: {} };
  Object.keys(S.sizes).forEach(k => { if (obj(t.sizes) && unit01(t.sizes[k])) soft.tools.sizes[k] = t.sizes[k]; });
  Object.keys(S.opac).forEach(k => { if (obj(t.opacity) && unit01(t.opacity[k])) soft.tools.opac[k] = t.opacity[k]; });
  soft.hints = {}; if (obj(p.hints)) Object.keys(p.hints).forEach(k => { if (p.hints[k] === true) soft.hints[k] = true; });
  // CR3: the process recording, if any (never a reason to refuse a project: a damaged recording is dropped)
  let process = null; try { const pr = p.process; if (obj(pr) && Array.isArray(pr.events)) process = { started: typeof pr.started === 'string' ? pr.started : null, complete: pr.complete !== false,
    events: pr.events.map(e => { need(obj(e) && typeof e.kind === 'string' && fin(e.t), 'event'); const o = { t: e.t, stage: e.stage, kind: e.kind };
      Object.keys(e).forEach(k => { if (k in o) return; const v = e[k]; if (k === 'a') { need(Number.isInteger(v) && v >= 0 && v < steps.length, 'event'); o.a = steps[v]; } else if (k === 'st') o.st = polyState(v); else o[k] = v; }); return o; }) }; } catch (_) { process = null; }
  return { startId, polygon, cur, poly, recovery, ref, soft, process, boundary: snap(g.boundary), shapeStart: snap(g.shapeStart), history: hist(p.history, 'the history') };
}
function checkRestored() {                // the rebuilt tile must be a valid tile of its rule, exactly as a saved one always is
  if (E.state.edges.length !== S.initialSnap.length) return 'the boundary does not fit the construction';
  const res = Math.max(0, ...E.state.rels.map(r => E.residual(r))); if (!(res < 1e-7)) return 'the boundary does not repeat correctly';
  if (S.cageNow && cageProblem(S.consId, S.cageNow)) return 'the corners do not fit the rule';
  if (S.poly && polyProblem(polyCommitted().nodes)) return 'the polygon is not a valid tile';
  return '';
}
function applyDecoded(d) {                 // rebuild the project with the app's own functions (throws if the result is not a valid tile)
  if (work) cancelWork(); closeMenu(); closePops(); $('ask').hidden = true;
  start(d.startId, { polygon: d.polygon, quiet: true });
  if (d.polygon) { S.poly.hist = d.poly.hist; S.poly.hp = d.poly.hp; S.poly.family = d.cur.family; S.poly.nodes = cloneNodes(d.cur.nodes); S.poly.sel = null; }
  if (d.cur.consId !== S.consId || !sameCage(d.cur.cage, S.cageNow)) setCage(d.cur.consId, d.cur.cage);
  restoreSnapshot(d.boundary); S.initialSnap = d.shapeStart;
  if (d.polygon) { S.shapeBaseKey = d.poly.builtOn; S.refined = d.poly.aside; S.restartOK = d.poly.confirmed; S.recovery = d.recovery; }
  S.history = d.history.list; S.hp = d.history.hp;
  // CR3: the Undo sequence numbers and the process recording continue where they were
  S.seq = Math.max(0, ...(d.polygon ? d.poly.hist.map(st => st.seq || 0) : []), ...S.history.map(a => a.seq || 0));
  if (d.process) { const evs = d.process.events, lastT = evs.length ? evs[evs.length - 1].t : 0; S.journal = { started: d.process.started || new Date().toISOString(), t0: Date.now() - lastT - 1000, events: evs.slice(), lastPoly: '', complete: d.process.complete }; }
  else S.journal = Object.assign(newJournal(), { complete: false });       // a CR1/CR2 project: the recording starts now
  rebuildLayers();                          // the artwork: every stroke and fill replayed, as Undo does
  const t = d.soft.tools;
  setShapeTool(t.shape); setSketchTool(t.sketch); Object.assign(S.sizes, t.sizes); Object.assign(S.opac, t.opac); S.angle = t.angle;
  setColor(t.colour); setTool(t.illustrate); setPattern(t.pattern); if (t.influence !== null) setInfluence(t.influence); S.guardShape = t.guard;
  S.comp = d.soft.comp; setTreat(d.soft.treat); setGhost(d.soft.ghost);
  S.showStart = d.soft.showStart; $('m-start-tick').textContent = S.showStart ? 'on' : 'off';
  S.showSketch = d.soft.showSketch; S.outline = d.soft.outline; syncCR2UI();
  Object.assign(S.seenHint, d.soft.hints);
  S.mode = 'illustrate'; syncSizeUI();                          // the Illustrate sliders show the restored sizes even while another stage is open
  S.mode = d.soft.stage; setMode(d.soft.stage, true);           // S.mode is set first, so this only shows the stage (no Polygon handoff runs)
  S.camByMode = d.soft.cams; if (d.soft.cam) S.cam = { ...d.soft.cam }; clampCam();
  const problem = checkRestored(); if (problem) throw new Error(problem);
  syncUndo(); syncPolyUI(); syncRestoreUI(); updateTitle(); syncSizeUI(); syncRefUI(); invalidate();
  return d.ref ? restoreRef(d.ref) : Promise.resolve(true);
}
function restoreRef(r) {
  return new Promise(resolve => {
    const url = URL.createObjectURL(new Blob([r.bytes], { type: r.type })), img = new Image();
    img.onload = () => { URL.revokeObjectURL(url); Object.assign(S.ref, { img, x: r.x, y: r.y, sc: r.sc, sc0: r.sc0, rot: r.rot, alpha: r.alpha, visible: r.visible, locked: r.locked, adjust: !r.locked, cache: null, saved: { type: r.type, bytes: r.bytes } }); syncRefUI(); invalidate(); resolve(true); };
    img.onerror = () => { URL.revokeObjectURL(url); toast('The reference image could not be read', 2400); resolve(false); };
    img.src = url;
  });
}
const decodeProblem = e => e.newer ? 'This project was made with a newer version of the app (' + e.message + '), so this version cannot open it.' : 'This project file is damaged: ' + e.message + '.';
async function applyProject(p) {          // → '' when opened; otherwise the reason, and the work that was open is back unchanged
  const chk = TP.checkProject(p); if (chk.problem) return chk.problem; p = chk.project;
  let d; try { d = decodeProject(p); } catch (e) { return decodeProblem(e); }
  const before = S.field ? captureProject() : null, t0 = performance.now(); restoring = true;
  try {
    const wait = applyDecoded(d); keep.restoreMs.push(+(performance.now() - t0).toFixed(1)); restoring = false;
    if (PERF) PERF.mark('restore ' + JSON.stringify({ ms: keep.restoreMs[keep.restoreMs.length - 1], steps: S.history.length }));
    await wait; return '';
  } catch (e) {
    console.warn('restore failed:', e);
    try { if (before) applyDecoded(decodeProject(before)); else { S.field = null; showEntry(1); } } catch (e2) { console.error(e2); }
    restoring = false; return 'This project could not be opened: ' + e.message + '.';
  }
}

/* ---- the reference image is kept as a compressed picture (about 1 MB at most), made once when the image is chosen ---- */
function encodeRef(src, type) {
  try {
    let alpha = false;
    if (!/jpe?g|heic|heif/i.test(type || '')) { const t = document.createElement('canvas'); t.width = t.height = 64; const x = t.getContext('2d', { willReadFrequently: true }); x.drawImage(src, 0, 0, 64, 64);
      const px = x.getImageData(0, 0, 64, 64).data; for (let i = 3; i < px.length; i += 4) if (px[i] < 250) { alpha = true; break; } }
    for (const [side, q] of [[1600, 0.85], [1280, 0.8], [1024, 0.75], [800, 0.7]]) {
      const k = Math.min(1, side / Math.max(src.width, src.height)), c = document.createElement('canvas'); c.width = Math.max(1, Math.round(src.width * k)); c.height = Math.max(1, Math.round(src.height * k));
      c.getContext('2d').drawImage(src, 0, 0, c.width, c.height);
      const url = c.toDataURL(alpha ? 'image/png' : 'image/jpeg', q), b64 = url.slice(url.indexOf(',') + 1), mime = url.slice(5, url.indexOf(';'));
      if (b64.length * 0.75 <= 1.2e6 || side === 800) return { type: mime === 'image/png' ? 'image/png' : 'image/jpeg', bytes: TP.b64ToBytes(b64) };
    }
  } catch (e) { console.warn('the reference image is not kept:', e); }
  return null;
}

/* ---- automatic save on this device ---- */
const idleNow = () => ptrs.size === 0 && !work && !nav && !refNav;
function markDirty() {
  if (!S.field || restoring) return;
  if (!keep.dirty) { keep.dirty = true; keep.dirtyAt = performance.now(); }
  clearTimeout(keep.timer); keep.timer = setTimeout(trySave, performance.now() - keep.dirtyAt > 2000 ? 40 : 700);
}
function trySave() { if (!keep.dirty) return; if (!idleNow()) { clearTimeout(keep.timer); keep.timer = setTimeout(trySave, 400); return; } saveNow(false); }
// The small picture on the Continue card. Copying the screen can wait for the graphics queue, so it is never part of an ordinary save:
// it is taken when the page is hidden, and otherwise at most once a minute after 2.5 s with no touch at all (then only the card is updated).
function thumbNow() {
  if (!$('entry').hidden || !S.field) return keep.thumb; const t0 = performance.now();
  try {
    const n = 192, c = keep.thumbCanvas || (keep.thumbCanvas = mkCanvas(n)), x = c.getContext('2d'), W = canvas.width, H = canvas.height, side = Math.max(1, Math.min(W, H, Math.round(H * 0.62)));
    const sx = Math.min(W - side, Math.max(0, S.cx * S.dpr - side / 2)), sy = Math.min(H - side, Math.max(0, S.cy * S.dpr - side / 2));
    x.fillStyle = COLORS.bg; x.fillRect(0, 0, n, n); x.drawImage(canvas, sx, sy, side, side, 0, 0, n, n);
    keep.thumb = c.toDataURL('image/jpeg', 0.72); keep.thumbAt = performance.now(); keep.thumbMs = +(keep.thumbAt - t0).toFixed(1); if (PERF) PERF.mark('thumb ' + keep.thumbMs);
  } catch (_) {}
  return keep.thumb;
}
function laterThumb() {
  clearTimeout(keep.thumbTimer);
  keep.thumbTimer = setTimeout(() => {
    if (!idleNow() || keep.saving || performance.now() - keep.touchAt < 2500 || !S.field || !$('entry').hidden) { if (performance.now() - keep.thumbAt > 60000) laterThumb(); return; }
    const t = thumbNow(); if (t) TP.setThumb(t);
  }, 2600);
}
window.addEventListener('pointerdown', () => { keep.touchAt = performance.now(); }, true);
async function saveNow(hidden) {
  if (!S.field || restoring) return;
  if (TP.store.ok !== true) { keep.dirty = false;
    if (TP.store.ok === false && !keep.failNoted) { keep.failNoted = true; toast('This browser is not keeping your work on this device · ⋮ › Save project keeps a copy', 4400); }
    return; }
  if (keep.saving) { keep.again = true; return; }
  keep.saving = true; keep.dirty = false; clearTimeout(keep.timer);
  const t0 = performance.now(); let p, info;
  try { p = captureProject(); info = { summary: p.summary, thumb: hidden ? thumbNow() : keep.thumb }; }
  catch (e) { keep.saving = false; console.warn('save: could not read the project', e); return; }
  const t1 = performance.now(); let r = await TP.save(p, info);
  if (!r.ok && /InvalidState|Unknown|TransactionInactive/.test(r.reason || '')) { await TP.openDB(); r = await TP.save(p, info); }   // Safari can drop the storage connection
  const row = { captureMs: +(t1 - t0).toFixed(2), copyMs: +(r.queuedMs || 0).toFixed(2), totalMs: +(performance.now() - t0).toFixed(1), steps: S.history.length, snaps: p.snapshots.length, ok: r.ok, hidden: !!hidden };
  keep.saving = false; keep.stats.push(row); if (keep.stats.length > 400) keep.stats.splice(0, 200); if (PERF) PERF.mark('save ' + JSON.stringify(row));
  if (r.ok) { keep.lastAt = r.at; keep.lastOk = true; keep.retry = 0; keep.workAt = performance.now(); if (performance.now() - keep.thumbAt > 60000) laterThumb(); if (!keep.persistAsked) { keep.persistAsked = true; try { navigator.storage && navigator.storage.persist && navigator.storage.persist().catch(() => {}); } catch (_) {} } }
  else { keep.lastOk = false; keep.dirty = true; keep.lastReason = r.reason;
    if (!keep.failNoted) { keep.failNoted = true; toast('Your latest change could not be kept on this device' + (/Quota/.test(r.reason || '') ? ' (storage is full)' : '') + ' · ⋮ › Save project keeps a copy', 4600); }
    clearTimeout(keep.timer); keep.timer = setTimeout(trySave, Math.min(60000, 5000 * ++keep.retry)); }
  if (keep.again) { keep.again = false; markDirty(); }
  syncKeepUI();
}
function saveOnHide() {                   // the page is being hidden or closed: save now; otherwise just refresh the Continue picture if it is older than the work
  if (!S.field || restoring) return; if (work) cancelWork();
  if (keep.dirty) { saveNow(true); return; }
  if (TP.store.ok && keep.lastAt && keep.thumbAt < keep.workAt) { const t = thumbNow(); if (t) TP.setThumb(t); }
}
['pointerup', 'pointercancel', 'keyup', 'change', 'input'].forEach(t => window.addEventListener(t, markDirty, true));
canvas.addEventListener('wheel', markDirty, { passive: true });
document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'hidden') saveOnHide(); });
window.addEventListener('pagehide', saveOnHide);

/* ---- what the student sees: the ⋮ menu line, the Continue card, Save project / Open project… ---- */
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const two = n => String(n).padStart(2, '0');
const clock = at => { const d = new Date(at); return two(d.getHours()) + ':' + two(d.getMinutes()); };
function when(at) {
  const d = new Date(at), now = new Date(), day = x => x.toDateString(), y = new Date(now); y.setDate(now.getDate() - 1);
  return (day(d) === day(now) ? 'today' : day(d) === day(y) ? 'yesterday' : d.toLocaleDateString([], { day: 'numeric', month: 'short' })) + ' ' + clock(at);
}
const fileStamp = d => d.getFullYear() + '-' + two(d.getMonth() + 1) + '-' + two(d.getDate()) + '-' + two(d.getHours()) + two(d.getMinutes());
function syncKeepUI() {
  const el = $('m-keep'), ok = TP.store.ok; if (!el) return;
  el.textContent = ok === false ? 'Not kept on this device · use Save project' : keep.lastOk === false ? 'The latest change is not kept on this device · use Save project'
    : keep.lastAt ? 'Kept on this device automatically · ' + clock(keep.lastAt) : 'Kept on this device automatically';
  el.classList.toggle('warn', ok === false || keep.lastOk === false);
}
$('more').addEventListener('click', syncKeepUI);
const storedInfo = () => { const m = TP.store.meta; return m && m.latest && m.slots && m.slots[m.latest] ? m.slots[m.latest] : null; };
function resumeCard(body) {               // start screen: Continue (only when nothing is open and work is kept on this device)
  if (TP.store.ok === false) { const n = document.createElement('p'); n.className = 'note'; n.textContent = 'This browser cannot keep your work on this device. Use ⋮ › Save project to keep a copy.'; body.appendChild(n); }
  const info = storedInfo(); if (S.field || !info) return false;
  const sm = info.summary || {}, thumb = typeof info.thumb === 'string' && info.thumb.startsWith('data:image/jpeg;base64,') ? info.thumb : '';
  const h = document.createElement('h2'); h.textContent = 'Continue'; body.appendChild(h);
  const b = document.createElement('button'); b.className = 'card resume'; b.id = 'entry-continue';
  b.innerHTML = (thumb ? `<img src="${thumb}" alt="">` : '<i class="nothumb"></i>') + `<div><b>Continue your tessellation</b><span>${esc(sm.title || 'Tessellation')}${STAGE_NAME[sm.stage] ? ' · ' + STAGE_NAME[sm.stage] : ''}</span><span>Saved ${esc(when(info.at))}</span></div>`;
  b.onclick = continueStored; body.appendChild(b);
  const h2 = document.createElement('h2'); h2.textContent = 'Start something new'; body.appendChild(h2); return true;
}
function openRow(body) { const r = document.createElement('p'); r.className = 'row openrow'; r.innerHTML = '<button id="entry-open">Open a project file…</button>'; body.appendChild(r); r.firstChild.onclick = () => $('projfile').click(); }
async function loadStored() {              // at start-up: read the latest save (kept in memory, so Continue and "Save project first" are instant)
  const m = TP.store.meta; keep.stored = null; if (!m || !m.latest) return;
  for (const slot of [m.latest, m.latest === 'a' ? 'b' : 'a']) {
    if (!m.slots || !m.slots[slot]) continue;
    try { const p = await TP.readSlot(slot); if (p && !TP.checkProject(p).problem) { keep.stored = { slot, project: p }; return; } } catch (_) {}
  }
}
async function continueStored() {
  const m = TP.store.meta; if (!m || !m.latest) return;
  for (const slot of [m.latest, m.latest === 'a' ? 'b' : 'a']) {
    if (!m.slots || !m.slots[slot]) continue;
    let p = keep.stored && keep.stored.slot === slot ? keep.stored.project : null;
    if (!p) { try { p = await TP.readSlot(slot); } catch (_) { p = null; } }
    if (!p) continue;
    const why = await applyProject(p);
    if (!why) { keep.stored = null; keep.lastAt = m.slots[slot].at; keep.lastOk = true; keep.workAt = performance.now(); if (m.slots[slot].thumb) { keep.thumb = m.slots[slot].thumb; keep.thumbAt = -1e9; }
      toast(slot === m.latest ? 'Welcome back · ' + titleNow() : 'The latest save could not be opened · the one before it is back (saved ' + when(m.slots[slot].at) + ')', slot === m.latest ? 1800 : 4600); return; }
    console.warn('continue: slot ' + slot + ':', why);
  }
  tell('Could not continue', 'The tessellation kept on this device could not be opened. It has not been deleted.', true);
}
function tell(title, text, keepNote) { ask({ title, html: '<p>' + esc(text) + '</p>' + (keepNote ? '' : '<p class="mute">Nothing was changed.</p>'), yes: 'OK', no: '' }, null); }
function wireAskSave(fromStore) {          // the "Save project first" button inside a replace question (the question stays open)
  const b = $('ask-save'); if (!b) return;
  b.onclick = () => { const p = fromStore ? keep.stored && keep.stored.project : null; if (fromStore && !p) { toast('The saved tessellation could not be read', 2400); return; }
    saveProjectFile(p).then(ok => { if (ok) { b.textContent = 'Project saved ✓'; b.disabled = true; } }); };
}
function confirmReplace(title, action, then) {   // ask before the open or kept work is replaced, offering to save it first
  const open = hasWorkNow(), info = !S.field ? storedInfo() : null, kept = !!info && (!info.summary || info.summary.hasWork !== false);
  if (!open && !kept) { then(); return; }
  const what = open ? 'The tessellation you have open' : 'Your saved tessellation' + (info.summary && info.summary.title ? ' (' + info.summary.title + ', saved ' + when(info.at) + ')' : '');
  ask({ title, html: `<p>${esc(what)} will be replaced.</p><p><button type="button" id="ask-save">Save project first</button></p><p class="mute">A saved project can be opened again with Open project…</p>`, yes: action, no: 'Cancel' }, then);
  wireAskSave(!open);
}
const beginNew = fn => confirmReplace('Start a new tessellation?', 'Start new', fn);
function saveProjectFile(p) {              // → a promise: true when the file was handed over (share sheet on a phone or tablet, a download elsewhere)
  let text, name;
  try { p = p || captureProject(); text = TP.toFileText(p); name = 'tessellation-' + fileStamp(new Date(Date.parse(p.saved) || Date.now())) + '.json'; }
  catch (e) { console.warn(e); toast('The project file could not be made', 2400); return Promise.resolve(false); }
  const blob = new Blob([text], { type: 'application/json' }), done = () => { toast('Project saved · ' + name, 2800); return true; };
  let file = null; try { file = new File([blob], name, { type: 'application/json' }); } catch (_) {}
  keep.lastFile = { name, bytes: text.length };
  if (navigator.maxTouchPoints > 0 && file && navigator.canShare && navigator.canShare({ files: [file] }))
    return navigator.share({ files: [file] }).then(done, e => (e && e.name === 'AbortError') ? false : (download(blob, name), done()));
  download(blob, name); return Promise.resolve(done());
}
function download(blob, name) { const url = URL.createObjectURL(blob), a = document.createElement('a'); a.href = url; a.download = name; a.hidden = true; document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(url), 60000); }
async function openProjectText(text) {     // a chosen file: check it completely, ask before replacing, then open it
  const r = TP.readProject(text); if (r.problem) { tell('Can’t open this file', r.problem); return 'refused'; }
  try { decodeProject(r.project); } catch (e) { tell('Can’t open this file', decodeProblem(e)); return 'refused'; }
  return new Promise(resolve => confirmReplace('Open this project?', 'Open', async () => {
    const why = await applyProject(r.project);
    if (why) { tell('Can’t open this project', why); resolve('failed'); return; }
    keep.stored = null; toast('Project opened · saved ' + when(Date.parse(r.project.saved) || Date.now()), 2600); markDirty(); resolve('opened');
  }));
}
$('m-save').onclick = () => { closeMenu(); saveProjectFile(null); };
$('m-open').onclick = () => { closeMenu(); $('projfile').click(); };
$('projfile').onchange = async e => {
  const f = e.target.files && e.target.files[0]; e.target.value = ''; if (!f) return;
  if (f.size > 80e6) { tell('Can’t open this file', 'This file is too large to be a tessellation project.'); return; }
  let text; try { text = await f.text(); } catch (_) { tell('Can’t open this file', 'The file could not be read.'); return; }
  openProjectText(text);
};
async function initKeep() {
  const ok = await TP.openDB(); if (ok) { await TP.readMeta(); await loadStored(); }
  syncKeepUI(); if (!S.field && !$('entry').hidden && S.entryStep === 1) showEntry(1);   // now the Continue card (or the notice) can show
}

/* ================= CR2 · SAVE IMAGE (PNG and hybrid SVG), sketch visibility, Tessellate outline =================
 * An image is exactly the canvas on screen (zoom and pan included), without the reference photo, guides, handles or selection marks.
 * PNG: the SAME drawing code as the screen (drawScene) runs once more into an off-screen canvas at 1×, 2× or 4× (S.dpr = scale), so
 *      every coordinate and every line width grows together. Safari refuses canvases above ~16.7 million pixels: a size that would exceed
 *      it is made at the largest safe scale, and the sheet says so (decided 23 Oct, option A).
 * SVG: hybrid (decided 23 Oct, option B). Tile outlines, sketch and illustration strokes, dots and textures are vectors, replayed from the
 *      history at exactly the raster's positions; erasers are masks; Fill regions are embedded as one image. One cell is defined once and
 *      placed in every tile with the tile's own matrix, as on screen.
 * The image is prepared while the sheet is open, so tapping Save hands it over at once (the iPhone share sheet needs that). */
let bleedCache = null;
function bleedPath() {                   // the tile outline pushed out by ¾ of a device pixel (Tessellate): neighbours overlap by a hair instead of leaving a gap
  const d = 0.75 / (S.cam.s * S.dpr); if (bleedCache && bleedCache.src === S.path && Math.abs(bleedCache.d - d) <= d * 0.02) return bleedCache.p;
  const p = new Path2D(); offsetPoly(d).forEach((q, i) => i ? p.lineTo(q.x, q.y) : p.moveTo(q.x, q.y)); p.closePath();
  bleedCache = { src: S.path, d, p }; return p;
}
function offsetPoly(d) {                 // the tile polygon moved outwards by d (cell units); vertex normals averaged (d is tiny)
  const poly = E.polygon(edgesNow()), n = poly.length; let a2 = 0;
  for (let i = 0; i < n; i++) { const p = poly[i], q = poly[(i + 1) % n]; a2 += p.x * q.y - q.x * p.y; }
  const sg = a2 > 0 ? 1 : -1, nrm = (a, b) => { const dx = b.x - a.x, dy = b.y - a.y, l = Math.hypot(dx, dy) || 1; return P(sg * dy / l, -sg * dx / l); };
  return poly.map((c, i) => { const n1 = nrm(poly[(i - 1 + n) % n], c), n2 = nrm(c, poly[(i + 1) % n]); let x = n1.x + n2.x, y = n1.y + n2.y; const l = Math.hypot(x, y);
    if (l < 1e-9) { x = n1.x; y = n1.y; } else { x /= l; y /= l; } return P(c.x + x * d, c.y + y * d); });
}
function syncCR2UI() { const o = $('outline'); if (o) o.value = S.outline; $('m-sketch-tick').textContent = S.showSketch ? 'on' : 'off'; }
$('outline').oninput = e => { S.outline = +e.target.value; invalidate(); if (S.outline === 0) sliderToast('Outline', 'none'); };
$('more').addEventListener('click', () => { $('m-sketch').hidden = S.mode !== 'illustrate'; });   // Show sketch belongs to Illustrate only

const WEBKIT = /AppleWebKit/.test(navigator.userAgent) && !/Chrome|Chromium|CriOS|FxiOS|Edg/.test(navigator.userAgent);
const EXPORT_MAX_PIXELS = WEBKIT ? 16777216 : 50000000;
const expState = { format: 'png', scale: 2, transparent: false, sketch: true, file: null, blob: null, url: null, token: 0, made: null };
(k => { if (!k || typeof k !== 'object') return; if (k.format === 'png' || k.format === 'svg') expState.format = k.format; if ([1, 2, 4].includes(k.scale)) expState.scale = k.scale;
  expState.transparent = k.transparent === true; expState.sketch = k.sketch !== false; })(store.get('tessellation.export', null));
function exportSize(want) {               // the requested scale, or the largest safe one on this device
  const a = S.vw * S.vh; let s = want; if (a * s * s > EXPORT_MAX_PIXELS) s = Math.max(1, Math.floor(Math.sqrt(EXPORT_MAX_PIXELS / a) * 10) / 10);
  return { scale: s, w: Math.round(S.vw * s), h: Math.round(S.vh * s), reduced: s < want };
}
function renderExport(o) {                // → a canvas with the picture at o.scale (o: { scale, transparent, sketch })
  const c = document.createElement('canvas'); c.width = Math.round(S.vw * o.scale); c.height = Math.round(S.vh * o.scale);
  const x = c.getContext('2d'); if (!x) throw new Error('this device cannot make an image this large');
  const keep = { ctx, dpr: S.dpr, fast: S.fast }; ctx = x; S.dpr = o.scale; S.fast = false; EXP = o;
  try { drawScene(c.width, c.height); } finally { ctx = keep.ctx; S.dpr = keep.dpr; S.fast = keep.fast; EXP = null; invalidate(); }
  return c;
}
const toBlobP = (c, type) => new Promise(r => { try { c.toBlob(b => r(b), type); } catch (_) { r(null); } });

/* ---- hybrid SVG ---- */
const fx = v => { const r = Math.round(v * 1e4) / 1e4; return Object.is(r, -0) ? 0 : r; }, fx6 = v => { const r = Math.round(v * 1e6) / 1e6; return Object.is(r, -0) ? 0 : r; };
const ptS = q => fx(q.x) + ' ' + fx(q.y);
const circlePath = (q, r) => `M${fx(q.x - r)} ${fx(q.y)}a${fx(r)} ${fx(r)} 0 1 0 ${fx(2 * r)} 0a${fx(r)} ${fx(r)} 0 1 0 ${fx(-2 * r)} 0`;
function svgPenPath(pts) {                 // the app's pen curve (paintPenFull): quadratic curves through the midpoints, in cell coordinates
  if (pts.length === 2) return `M${ptS(pts[0])}L${ptS(pts[1])}`;
  let d = 'M' + ptS(pts[0]); for (let i = 1; i < pts.length - 1; i++) d += 'Q' + ptS(pts[i]) + ' ' + ptS(mid(pts[i], pts[i + 1]));
  return d + 'L' + ptS(pts[pts.length - 1]);
}
function svgPen(st, opaque, col) {         // a pen, sketch or eraser stroke (one element, so a translucent stroke never darkens where it crosses itself)
  col = col || st.color; const a = (st.tool === 'eraser' || opaque) ? 1 : st.alpha, op = a < 0.999 ? ` opacity="${fx(a)}"` : '';
  if (st.pts.length === 1) return `<path d="${circlePath(st.pts[0], st.w / 2)}" fill="${col}"${op}/>`;
  return `<path d="${svgPenPath(st.pts)}" fill="none" stroke="${col}" stroke-width="${fx(st.w)}" stroke-linecap="round" stroke-linejoin="round"${op}/>`;
}
function svgStamps(st) {                   // dots and textures at exactly the raster's positions (the same walker and seeds as stampStart/stampSeg)
  const L = S.layers.art, k = L.k, I = S.ink, D = st.w * k, W = (x, y) => P(I.x0 + x / k, I.y1 - y / k), circles = [], lines = [];
  const rot = -(st.angle || 0) * PI / 180, c = Math.cos(rot), s = Math.sin(rot), loc = (cx, cy, u, v) => W(cx + u * c - v * s, cy + u * s + v * c);
  const one = (cx, cy, idx) => {
    if (st.tool === 'dot') { circles.push([W(cx, cy), D / 2 / k]); return; }
    const L2 = (u1, v1, u2, v2) => `M${ptS(loc(cx, cy, u1, v1))}L${ptS(loc(cx, cy, u2, v2))}`;
    switch (st.pattern) {
      case 'hatch': lines.push(L2(-D * .45, 0, D * .45, 0)); break;
      case 'cross': lines.push(L2(-D * .45, 0, D * .45, 0) + L2(0, -D * .45, 0, D * .45)); break;
      case 'stipple': { const r = rngFrom(st.seed + idx * 7919); for (let j = 0; j < 4; j++) { const a = r() * TAU, d = Math.sqrt(r()) * D * .5; circles.push([loc(cx, cy, Math.cos(a) * d, Math.sin(a) * d), Math.max(.9, D * .045) / k]); } break; }
      case 'scales': { const R = D * .38, K = 0.5523 * R;     // the canvas arc 0 → π (the lower half circle), as two cubic quarter arcs
        lines.push(`M${ptS(loc(cx, cy, R, 0))}C${ptS(loc(cx, cy, R, K))} ${ptS(loc(cx, cy, K, R))} ${ptS(loc(cx, cy, 0, R))}C${ptS(loc(cx, cy, -K, R))} ${ptS(loc(cx, cy, -R, K))} ${ptS(loc(cx, cy, -R, 0))}`); break; }
      case 'waves': lines.push(`M${ptS(loc(cx, cy, -D * .5, 0))}C${ptS(loc(cx, cy, -D * .25, -D * .35))} ${ptS(loc(cx, cy, D * .25, D * .35))} ${ptS(loc(cx, cy, D * .5, 0))}`); break;
    }
  };
  const p0 = toPx(st.pts[0], L); let idx = 0, carry; one(p0.x, p0.y, idx++); carry = spacingPx(st, D);
  for (let j = 1; j < st.pts.length; j++) { const a = toPx(st.pts[j - 1], L), b = toPx(st.pts[j], L), d = Math.hypot(b.x - a.x, b.y - a.y), sp = spacingPx(st, D);
    if (d < carry) { carry -= d; continue; } let t = carry; while (t <= d) { one(a.x + (b.x - a.x) * t / d, a.y + (b.y - a.y) * t / d, idx++); t += sp; } carry = t - d; }
  const lw = fx(Math.max(1.3, D * 0.07) / k), col = st.color;
  if (st.alpha >= 0.999) return (circles.length ? `<path d="${circles.map(q => circlePath(q[0], q[1])).join('')}" fill="${col}"/>` : '') +
    (lines.length ? `<path d="${lines.join('')}" fill="none" stroke="${col}" stroke-width="${lw}" stroke-linecap="round"/>` : '');
  const op = ` opacity="${fx(st.alpha)}"`;                 // translucent marks: one element each, so overlaps darken as they do on screen
  return circles.map(q => `<path d="${circlePath(q[0], q[1])}" fill="${col}"${op}/>`).join('') + lines.map(d => `<path d="${d}" fill="none" stroke="${col}" stroke-width="${lw}" stroke-linecap="round"${op}/>`).join('');
}
function svgLayer(layer, idp) {            // one layer's strokes in history order (up to the Undo position); an eraser masks what was drawn before it
  const I = S.ink, box = `x="${fx(I.x0)}" y="${fx(I.y1 - I.side)}" width="${fx(I.side)}" height="${fx(I.side)}"`;
  let body = '', defs = '', n = 0;
  for (let h = 0; h < S.hp; h++) { const a = S.history[h]; if (a.kind !== 'stroke' || a.layer !== layer) continue;
    if (a.tool === 'eraser') { const id = idp + 'e' + (n++); defs += `<mask id="${id}" maskUnits="userSpaceOnUse" ${box}><rect ${box} fill="#fff"/>${svgPen(a, true, '#000')}</mask>`; body = `<g mask="url(#${id})">${body}</g>`; }
    else body += (a.tool === 'pen') ? svgPen(a, layer === 'sketch') : svgStamps(a);
  }
  return { defs, body };
}
const pngURL = c => c.toDataURL('image/png');
function svgImage(c, id) { const I = S.ink; return `<g id="${id}" transform="scale(1 -1)"><image x="${fx(I.x0)}" y="${fx(-I.y1)}" width="${fx(I.side)}" height="${fx(I.side)}" preserveAspectRatio="none" xlink:href="${pngURL(c)}"/></g>`; }
function svgMarkLines(alpha) {
  const c0 = S.field.c0, z = S.unit, segs = [[-0.08, -0.15, -0.08, 0.15], [-0.08, 0.15, 0.12, 0.15], [-0.08, 0.02, 0.07, 0.02]];
  return `<path d="${segs.map(g => `M${fx(c0.x + g[0] * z)} ${fx(c0.y + g[1] * z)}L${fx(c0.x + g[2] * z)} ${fx(c0.y + g[3] * z)}`).join('')}" fill="none" stroke="${COLORS.line}" stroke-width="${fx(0.012 * z)}" stroke-linecap="round" opacity="${fx(alpha)}"/>`;
}
const xmlEsc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
function svgExport(o) {                    // → the SVG text of the view on screen (o: { transparent, sketch })
  EXP = o; try {
    const Wd = Math.round(S.vw), Ht = Math.round(S.vh), k = S.cam.s, V = [k, 0, 0, -k, S.cx - S.cam.x * k, S.cy + S.cam.y * k];
    const tess = S.mode === 'tessellate', poly = S.mode === 'polygon', A = layerAlphas(), artEmpty = tess ? !hasArt() : false, ga = tess ? 1 : ghostAlpha();
    const thin = thinOutline(), tileD = 'M' + E.polygon(edgesNow()).map(ptS).join('L') + 'Z', bleedD = thin ? 'M' + offsetPoly(0.5 / k).map(ptS).join('L') + 'Z' : tileD;
    const art = svgLayer('art', 'ma'), sk = A.sketch > 0 ? svgLayer('sketch', 'ms') : { defs: '', body: '' };
    let defs = art.defs + sk.defs + `<clipPath id="clipT"><path d="${tileD}"/></clipPath><clipPath id="clipB"><path d="${bleedD}"/></clipPath>`;
    defs += svgImage(S.layers.fills.big, 'fills') + `<g id="art">${art.body}</g>` + (sk.body ? `<g id="sketch">${sk.body}</g>` : '');
    const variants = new Map();            // one cell drawing per (figure tint, F mark) in use, placed in every tile
    const cellRef = (tint, mark) => { const key = (tint || '') + '|' + mark; if (variants.has(key)) return variants.get(key); const id = 'cell' + variants.size;
      let fillsRef = '#fills'; if (tint) { const tid = 'tint' + variants.size; defs += svgImage(getTint(tint), tid); fillsRef = '#' + tid; }
      defs += `<g id="${id}">` + (mark ? svgMarkLines(mark) : '') + (A.art > 0 ? `<use xlink:href="${fillsRef}" opacity="${fx(A.art)}"/>` : '') +
        (A.sketch > 0 && sk.body ? `<use xlink:href="#sketch" opacity="${fx(A.sketch)}"/>` : '') + (A.art > 0 && art.body ? `<use xlink:href="#art" opacity="${fx(A.art)}"/>` : '') + '</g>';
      variants.set(key, id); return id; };
    let body = o.transparent ? '' : `<rect width="${Wd}" height="${Ht}" fill="${COLORS.bg}"/>`;
    const parts = (m, alpha, active, i) => {   // the same decisions as drawTile → [base, artwork, outline] of one tile
      const cp = tess ? compOf(i) : null; if (cp && cp.hidden) return null;
      const mm = cp && cp.scale != null && Math.abs(cp.scale - 1) > 1e-6 ? mmul(m, scaleAbout(S.cent, cp.scale)) : m, a = alpha * (cp && cp.alpha != null ? cp.alpha : 1);
      const bg = tess ? ((cp && cp.bg) || COLORS.fill) : (S.orientCue && shaping() && det(m) < 0 ? COLORS.fillMirror : COLORS.fill);
      const mark = poly ? 0 : S.orientCue ? (shaping() ? MARK_ALPHA.shape : tess && artEmpty ? MARK_ALPHA.tessellate : 0) : 0, id = cellRef(cp && cp.fig ? cp.fig : null, mark);
      const lw = tess ? outlineWorld() : (active ? (shaping() ? 2.4 : 1.6) : 1.1) / k, op = a < 0.999 ? fx(a) : null, g = `<g transform="matrix(${mmul(V, mm).map(fx6).join(' ')})">`;
      return [g + `<path d="${bleedD}" fill="${bg}"${op ? ` fill-opacity="${op}"` : ''}/></g>`,
        g + `<g clip-path="url(#${thin ? 'clipB' : 'clipT'})"${op ? ` opacity="${op}"` : ''}><use xlink:href="#${id}"/>${poly && S.orientCue ? svgMarkLines(MARK_ALPHA.shape) : ''}</g></g>`,
        lw > 0 ? g + `<path d="${tileD}" fill="none" stroke="${COLORS.line}" stroke-width="${fx(lw)}" stroke-linejoin="round"${op ? ` stroke-opacity="${op}"` : ''}/></g>` : ''];
    };
    const list = S.field.list, margin = 1.1 * S.field.size * k, all = [];
    if (ga > 0) for (let i = 1; i < list.length; i++) { const c = w2s(S.centW[i]); if (c.x < -margin || c.x > S.vw + margin || c.y < -margin || c.y > S.vh + margin) continue; all.push(parts(list[i], ga, false, i)); }
    all.push(parts(IDM, 1, true, 0)); const T = all.filter(Boolean);
    body += thin ? T.map(t => t[0]).join('') + T.map(t => t[1]).join('') + T.map(t => t[2]).join('') : T.map(t => t.join('')).join('');   // passes, as on screen
    return `<?xml version="1.0" encoding="UTF-8"?>\n<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" version="1.1" width="${Wd}" height="${Ht}" viewBox="0 0 ${Wd} ${Ht}">` +
      `<title>${xmlEsc(titleNow() + ' · ' + STAGE_NAME[S.mode])}</title><defs>${defs}</defs>${body}</svg>`;
  } finally { EXP = null; }
}

/* ---- the Save image sheet ---- */
function syncExportUI() {
  const st = expState, sh = shaping();
  $('exp-sub').textContent = STAGE_NAME[S.mode] + ' · the view on screen, without the controls';
  [['exp-format', st.format], ['exp-res', String(st.scale)], ['exp-bg', st.transparent ? 'transparent' : 'current'], ['exp-sk', st.sketch ? 'on' : 'off']]
    .forEach(([id, v]) => $(id).querySelectorAll('button').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.v === v))));
  $('exp-res-row').hidden = st.format !== 'png'; $('exp-sk-row').hidden = !sh;
}
function openExport() {
  closeMenu(); closePops(); if (work) cancelWork(); $('exp').hidden = false; syncExportUI(); prepareExport();
}
function closeExport() { $('exp').hidden = true; expState.token++; if (expState.url) { URL.revokeObjectURL(expState.url); expState.url = null; } $('exp-prev').removeAttribute('src'); expState.file = expState.blob = null; }
async function prepareExport() {           // makes the image now, so Save can hand it over at once
  const st = expState, t = ++st.token, save = $('exp-save'); st.file = st.blob = null; save.disabled = true; save.textContent = 'Preparing…'; $('exp-info').textContent = '';
  store.set('tessellation.export', { format: st.format, scale: st.scale, transparent: st.transparent, sketch: st.sketch });
  await new Promise(r => setTimeout(r, 40)); if (t !== st.token) return;     // let the sheet show first
  const o = { transparent: st.transparent, sketch: shaping() && st.sketch }, name = 'tessellation-' + fileStamp(new Date()) + '-' + S.mode + '.' + st.format, t0 = performance.now();
  try {
    let blob, info;
    if (st.format === 'png') {
      let sz = exportSize(st.scale);
      for (let tries = 0; tries < 3; tries++) {             // a canvas the device silently refuses gives no PNG: try a smaller one
        o.scale = sz.scale; const c = renderExport(o); blob = await toBlobP(c, 'image/png'); c.width = c.height = 0; if (t !== st.token) return;
        if (blob && blob.size > 200) break; blob = null; const s2 = Math.max(1, Math.floor(sz.scale * 0.8 * 10) / 10); sz = { scale: s2, w: Math.round(S.vw * s2), h: Math.round(S.vh * s2), reduced: true };
      }
      if (!blob) throw new Error('the device could not make the PNG');
      info = `PNG · ${sz.w} × ${sz.h} px` + (sz.reduced ? ` · ${st.scale}× is reduced to ${sz.scale}× on this device` : '');
      st.made = { format: 'png', scale: sz.scale, w: sz.w, h: sz.h, reduced: !!sz.reduced, bytes: blob.size, ms: Math.round(performance.now() - t0) };
    } else {
      const text = svgExport(o); blob = new Blob([text], { type: 'image/svg+xml' });
      info = `SVG · vector, ${Math.round(S.vw)} × ${Math.round(S.vh)} · fills embedded as an image · ${Math.max(1, Math.round(blob.size / 1024))} KB`;
      st.made = { format: 'svg', bytes: blob.size, ms: Math.round(performance.now() - t0) };
    }
    if (t !== st.token) return;
    if (st.url) URL.revokeObjectURL(st.url); st.url = URL.createObjectURL(blob); $('exp-prev').src = st.url;
    st.blob = blob; try { st.file = new File([blob], name, { type: blob.type }); } catch (_) { st.file = null; } st.name = name;
    $('exp-info').textContent = info; save.disabled = false; save.textContent = 'Save image';
    if (PERF) PERF.mark('export ' + JSON.stringify(st.made));
  } catch (e) { console.warn(e); if (t === st.token) { $('exp-info').textContent = 'The image could not be made: ' + e.message + '.'; save.textContent = 'Save image'; } }
}
function saveExport() {                     // hands the prepared image over (share sheet on a phone or tablet, a download elsewhere)
  const st = expState, blob = st.blob, name = st.name; if (!blob) return Promise.resolve(false);
  const done = () => { toast('Image saved · ' + name, 2800); closeExport(); return true; };
  if (navigator.maxTouchPoints > 0 && st.file && navigator.canShare && navigator.canShare({ files: [st.file] }))
    return navigator.share({ files: [st.file] }).then(done, e => (e && e.name === 'AbortError') ? false : (download(blob, name), done()));
  download(blob, name); return Promise.resolve(done());
}
[['exp-format', v => { expState.format = v; }], ['exp-res', v => { expState.scale = +v; }], ['exp-bg', v => { expState.transparent = v === 'transparent'; }], ['exp-sk', v => { expState.sketch = v === 'on'; }]]
  .forEach(([id, set]) => $(id).querySelectorAll('button').forEach(b => b.onclick = () => { set(b.dataset.v); syncExportUI(); prepareExport(); }));
$('m-image').onclick = openExport; $('exp-cancel').onclick = closeExport; $('exp-save').onclick = () => saveExport();

/* ================= CR3 · Sketch in Polygon, one Undo timeline in Polygon, process recording, classroom polish =================
 * Polygon › Sketch draws exactly like Shape › Sketch (same layer, same tools). In Polygon, Undo/Redo follow ONE timeline: corner moves,
 * point changes and Polygon sketch strokes, newest first, whichever tool made them (decided 23 Oct, Q3 A). Each polygon state and each
 * Polygon sketch stroke carries a sequence number, saved in the project.
 * PROCESS RECORDING (for the Timelapse checkpoint after CR4): an append-only journal, independent of Undo, written only when an action has
 * finished (never during a drag). It refers to the steps the project already stores, so nothing is duplicated, and it keeps what Undo
 * forgets: undone attempts, Shape refinements removed by a polygon change, Tessellate changes, stage changes and timing. */
S.polyTool = 'edit'; S.seq = 0; S.journal = null;
const newJournal = () => ({ started: new Date().toISOString(), t0: Date.now(), events: [], lastPoly: '', complete: true });
function journal(kind, data) {
  if (restoring || !S.field || !S.journal) return;
  const ev = Object.assign({ t: Date.now() - S.journal.t0, stage: S.mode, kind }, data || {}), evs = S.journal.events, last = evs[evs.length - 1];
  // a slider moving (group opacity or scale, outline) records one event per setting, not one per frame
  if (last && ev.coalesce && last.coalesce === ev.coalesce && ev.t - last.t < 2000) { evs[evs.length - 1] = ev; return; }
  evs.push(ev);
}
function notePoly() {                     // the committed polygon state, whenever it changes (edit, Undo, Redo, a new rule)
  if (!S.poly || !S.journal) return; const st = polyCommitted(), key = polyKey(st) + '#' + S.poly.hp;
  if (key === S.journal.lastPoly) return; S.journal.lastPoly = key;
  journal('poly', { st: { consId: st.consId, family: st.family || null, cage: st.cage ? cloneCage(st.cage) : null, nodes: cloneNodes(st.nodes || {}), seq: st.seq || 0 }, hp: S.poly.hp });
}
// wrap the app's own functions (their names are looked up at call time, so every caller goes through these)
{ const _start = start; start = function (id, opts) { _start(id, opts); S.polyTool = 'edit'; S.seq = 0; S.journal = newJournal(); placeSketchTools();
    journal('start', { construction: id, polygon: !!(opts && opts.polygon) }); }; }
{ const _push = pushAction; pushAction = function (a) {
    if (a && a.stage === 'polygon') { a.seq = ++S.seq; if (S.poly && S.poly.hp < S.poly.hist.length - 1) { S.poly.hist.length = S.poly.hp + 1; } }   // a new action ends the polygon redo branch
    _push(a); journal('step', { a }); }; }
{ const _ah = applyHistory; applyHistory = function (d) { const hp = S.hp; _ah(d); if (S.hp !== hp) journal(d < 0 ? 'undo' : 'redo', { list: 'main' }); }; }
{ const _pc = polyCommit; polyCommit = function (next) {
    const nx = S.history[S.hp]; if (S.hp < S.history.length && nx && nx.stage === 'polygon') { S.history.length = S.hp; syncUndo(); }   // ...and a polygon edit ends a sketch redo branch
    _pc(next); S.poly.hist[S.poly.hp].seq = ++S.seq;
    const le = S.journal && S.journal.events[S.journal.events.length - 1]; if (le && le.kind === 'poly' && le.hp === S.poly.hp) le.st.seq = S.seq;   // (the event was written inside the commit)
    notePoly(); syncPolyButtons(); }; }
{ const _aps = applyPolyState; applyPolyState = function (st) { _aps(st); notePoly(); }; }
{ const _sm = setMode; setMode = function (m, quiet) { const from = S.mode; _sm(m, quiet); placeSketchTools(); if (S.mode !== from) journal('stage', { from, to: S.mode }); }; }
{ const _rv = restoreVersion; restoreVersion = function () { _rv(); journal('restoreVersion'); notePoly(); syncPolyButtons(); }; }
{ const _rs = restartShape; restartShape = function () { _rs(); journal('restartShape'); }; }
{ const _st = setTreat; setTreat = function (t) { const was = S.treat; _st(t); if (t !== was) journal('comp', { op: 'grouping', v: t }); }; }
{ const _gp = setGroupProp; setGroupProp = function (prop, val) { const sel = S.sel; _gp(prop, val); if (sel) journal('comp', { op: 'group', mode: sel.mode, key: sel.key, prop, v: val == null ? null : val, coalesce: 'g|' + sel.mode + '|' + sel.key + '|' + prop }); }; }
{ const _su = syncUndo; syncUndo = function () { _su(); if (S.poly) syncPolyButtons(); }; }
{ const _ap = applyProject; applyProject = async function (p) { const why = await _ap(p);                // a reopened project marks where this session's recording begins
    if (!why && S.journal) { S.journal.lastPoly = S.poly ? polyKey(polyCommitted()) + '#' + S.poly.hp : ''; journal('resume', { at: new Date().toISOString(), earlierRecorded: S.journal.complete }); } return why; }; }
function captureJournal(step) {          // the recording for the project file (steps by their number in the steps table)
  const J = S.journal; if (!J) return null;
  return { format: 1, started: J.started, complete: J.complete, events: J.events.map(e => { const o = { t: e.t, stage: e.stage, kind: e.kind };
    Object.keys(e).forEach(k => { if (k in o || k === 'coalesce') return; const v = e[k];
      if (k === 'a') o.a = step(v);
      else if (k === 'st') o.st = Object.assign({ construction: v.consId, family: v.family || null, corners: v.cage && !isSquare(v.cage) ? v.cage.map(q => ({ x: q.x, y: q.y })) : null, points: cloneNodes(v.nodes || {}) }, v.seq ? { seq: v.seq } : {});
      else o[k] = v; }); return o; }) };
}
$('grp-reset').addEventListener('click', () => { if (S.sel) journal('comp', { op: 'groupReset', mode: S.sel.mode, key: S.sel.key }); });
$('m-resetcomp').addEventListener('click', () => journal('comp', { op: 'resetAll' }));
$('outline').addEventListener('input', () => journal('comp', { op: 'outline', v: S.outline, coalesce: 'outline' }));

/* ---- the one Undo timeline in Polygon ---- */
const topPolySketch = () => { const a = S.hp > 0 ? S.history[S.hp - 1] : null; return a && a.kind === 'stroke' && a.stage === 'polygon' ? a : null; };
const nextPolySketch = () => { const a = S.hp < S.history.length ? S.history[S.hp] : null; return a && a.kind === 'stroke' && a.stage === 'polygon' ? a : null; };
const canPolyUndo = () => !!S.poly && (S.poly.hp > 0 || !!topPolySketch());
const canPolyRedo = () => !!S.poly && (S.poly.hp < S.poly.hist.length - 1 || !!nextPolySketch());
function polyUndoRedo(d) {               // the newest of {the last polygon edit, the last Polygon sketch stroke} — or, for Redo, the earliest undone one
  if (!S.poly) return;
  if (d < 0) { const pe = S.poly.hp > 0 ? (S.poly.hist[S.poly.hp].seq || 0) : -1, sk = topPolySketch(), ss = sk ? (sk.seq || 0) : -1;
    if (pe < 0 && ss < 0) return; if (ss > pe) applyHistory(-1); else polyHistory(-1); }
  else { const pe = S.poly.hp < S.poly.hist.length - 1 ? (S.poly.hist[S.poly.hp + 1].seq || 0) : Infinity, sk = nextPolySketch(), ss = sk ? (sk.seq || 0) : Infinity;
    if (pe === Infinity && ss === Infinity) return; if (ss < pe) applyHistory(1); else polyHistory(1); }
  syncPolyButtons();
}
function syncPolyButtons() { if (!S.poly) return; const u = !canPolyUndo(), r = !canPolyRedo(); $('pb-undo').disabled = u; $('pb-redo').disabled = r; $('pb-redo').classList.toggle('gone', r); }

/* ---- Polygon › Sketch ---- */
function placeSketchTools() {            // the one set of sketch tools sits in whichever bar is showing. In Polygon, Pen / Eraser take the place of
  const tools = $('sketch-tools'), seg = $('seg-sketch'); if (!tools || !seg) return;   // Translate / Rotate / Glide (no rule is chosen while sketching) and the size gets the second row
  const pbSub = document.querySelector('#strip-polygon .pb-sub'), row1 = document.querySelector('#pb-tools .sb-row1'), fam = document.querySelector('#pb-tools .pb-fam');
  if (S.mode === 'polygon' && S.polyTool === 'sketch') {
    if (seg.parentNode !== row1) row1.insertBefore(seg, $('pb-count')); if (tools.parentNode !== pbSub) pbSub.appendChild(tools); tools.hidden = false; fam.hidden = true;
  } else {
    if (seg.parentNode !== tools) tools.insertBefore(seg, tools.firstChild); const home = $('sb-tools').querySelector('.sb-row2'); if (tools.parentNode !== home) home.appendChild(tools);
    tools.hidden = S.shapeTool !== 'sketch'; fam.hidden = false;
  }
}
function setPolyTool(t) {
  if (work) cancelWork(); S.polyTool = t; if (S.poly) S.poly.sel = null; placeSketchTools(); syncPolyUI(); syncSizeUI(); invalidate();
  if (t === 'sketch' && !S.seenHint.polySketch) { S.seenHint.polySketch = true; toast('Sketch on the polygon · tap Sketch again to edit points and corners', 3000); }
}
$('pb-sketch').onclick = () => setPolyTool(S.polyTool === 'sketch' ? 'edit' : 'sketch');

/* ---- ⋮ › Experimental: the Grid Explorer, the Regular Grid Explorer and the Rhombus (unchanged; the Rhombus leaves the start screen) ---- */
delete SHAPES.rhombus;
$('m-exp').onclick = () => { const l = $('m-exp-list'), open = l.hidden; l.hidden = !open; $('m-exp-tick').textContent = open ? '⌄' : '›'; };
$('more').addEventListener('click', () => { if (!$('menu').hidden) { $('m-exp-list').hidden = true; $('m-exp-tick').textContent = '›'; } });   // the menu always opens with Experimental folded
const openPage = url => { closeMenu(); if (S.field) { if (keep.dirty) saveNow(true); } const w = window.open(url, '_blank'); if (!w) location.href = url; };   // a new tab: this one keeps the work
$('m-exp-grid').onclick = () => openPage('explorer.html');
$('m-exp-regular').onclick = () => openPage('regular.html');
$('m-exp-rhombus').onclick = () => { closeMenu(); beginNew(() => start('reflection')); };

/* ---------------- boot ---------------- */
resize(); showEntry(1); initKeep();
window.__ws = { setCage, cageNow, cageAfterDrag, cageProblem, cageKind, virtCons, frameOf, relToWorld, worldToRel, worldNodes, nodeWorld, gridIndex, latticeBasis, SQUARE, polySnapshot, buildCurrent, sameCage, isSquare,
  startPolygon, choosePolyCons, polyHistory, polyProblem, polyVerts, polyRels, polyKey, polyCommitted, polyCurrentState, polyCommit, applyPolyState, writePolygonEdges,
  sampleThrough, removeSelectedNode, restoreVersion, outlineSimple, allRanges, captureVersion, leavePolygon, sideCount, nodeCount,
  setRefLocked, getComposite, paintComposite, patchComposites, syncView, flushStroke, flushShapeMove, runProofAll, S, E, start, render, setMode, setShapeTool, setSketchTool, setTool, setPattern, setTreat, setInfluence, setGhost, setColor, applyHistory, fitCamera, runSelfTestSafely, showEntry, openLab, snapshot, INFLUENCE, influenceRadius, grabArc, lockRef,
  tileAt, doFill, rebuildLayers, svgBoundary, groupOf, layerAlphas, sizeKey, hasArt, getTint, newStroke, widthFor,
  selectGroupAt, setGroupProp, loadRef, drawPreview, compOf, compModified, syncRefUI, openGroupPop, penTest: { paintPenFull, paintStrokeCanonical },
  keep: { captureProject, decodeProject, applyProject, saveNow, markDirty, keep, continueStored, saveProjectFile, openProjectText, hasWorkNow, encodeRef, initKeep, TP },
  cr2: { renderExport, exportSize, svgExport, openExport, closeExport, prepareExport, saveExport, expState, bleedPath, offsetPoly, outlineWorld, syncCR2UI, layerAlphas, EXPORT_MAX_PIXELS, OUTLINE_DEFAULT },
  cr3: { setPolyTool, polyUndoRedo, canPolyUndo, canPolyRedo, captureJournal, notePoly, POLY_MAX_POINTS, polyInsertAt, startPolygon, SHAPES, busy: () => ({ ptrs: [...ptrs.keys()], work: work && work.type, nav: !!nav, refNav: !!refNav, lock, restoring, timer: !!keep.timer }) } };
})();
