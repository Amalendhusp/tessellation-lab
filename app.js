/* tessellation-mobile-workspace-v5.9-f1a2 / app.js  (F1a-2: Mirror · Two figures; a new construction starts with a clear drawing; colours belong to each figure; see F1A2_REPORT.md)
 * v5.8.1-f1-refine / app.js  (F1 refinements: the corners of Two figures move; fills keep to their figure; see F1R_REPORT.md)
 * v5.8-f1a1 / app.js  (F1a-1: Two figures with Slide, Figure A and Figure B sharing every boundary; see F1A1_REPORT.md)
 * v5.7.1-drawfix / app.js  (DA: the drawing area follows the tile; complete touch test; see DRAWFIX_REPORT.md)
 * v5.7-t2 / app.js  (T2: Mirror with two arrangements, Same orientation and Alternating; see T2_REPORT.md)
 * v5.6-t1 / app.js  (T1: Square › Mirror, mirrored drawing, Slide · Turn · Flip · Mirror; see T1_REPORT.md; engine fixes from v5.5-fx)
 * v5.4-classroom-cr3 / app.js  (CR3: 40 points, Translation first, Sketch in Polygon with one Undo timeline, process recording, classroom polish; see CR3_REPORT.md)
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
// T1 · Square › Mirror: the square stood on its corner (a diamond of the same size), mirror-symmetric about its VERTICAL diagonal. Inside the
// tile, the lower-right side is the mirror image of the lower-left, and the upper-right of the upper-left ('constraint', like the Rhombus);
// neighbours are SLID along the diamond's sides ('glue'), never mirrored. Engine data only: engine.js is not changed by T1.
const MIRROR_R = Math.SQRT1_2, MIRROR_AXIS = { type: 'mirror', p0: P(0.5, 0), phi: PI / 2, g: 0 };
if (!CONS.some(c => c.id === 'mirror')) CONS.push({ id: 'mirror', title: 'Mirror · square on its corner',
  prompt: 'The tile is symmetric about its vertical diagonal: each side on the right is the mirror image of the side on the left. Neighbours are slid, not mirrored.',
  verts: [P(0.5, 0.5 - MIRROR_R), P(0.5 + MIRROR_R, 0.5), P(0.5, 0.5 + MIRROR_R), P(0.5 - MIRROR_R, 0.5)],
  rels: [ { from: 0, to: 3, d: MIRROR_AXIS, role: 'constraint' }, { from: 1, to: 2, d: MIRROR_AXIS, role: 'constraint' },
          { from: 0, to: 2, d: { type: 'translate', v: [-MIRROR_R, MIRROR_R] }, role: 'glue' }, { from: 3, to: 1, d: { type: 'translate', v: [MIRROR_R, MIRROR_R] }, role: 'glue' } ] });
// T2 · Mirror, two ARRANGEMENTS of the same tile. The diamond, its mirror inside the tile and every point and pull are shared; only the placing of a
// neighbour across a side differs:
//   'mirror'       Same orientation: the neighbour is slid (translation), as in T1;
//   'mirror-flip'  Alternating: the neighbour is mirrored and slid (a glide reflection: vertical mirror line through the middle of the shared side,
//                  then a slide of √½ upward). The tile is its own mirror image, so each glide puts the OUTLINE exactly where the slide does; only
//                  the drawing inside is mirrored. Verified in ../tessellation-geometry-review/t2 (identical outlines; the only such rule).
// The glides are listed so that the repeat vectors come out in Mirror's order (Tessellate's Row and Column groups keep their tiles).
if (!CONS.some(c => c.id === 'mirror-flip')) CONS.push({ id: 'mirror-flip', title: 'Mirror · alternating',
  prompt: 'The same symmetric tile as Mirror. Each neighbour across a side is its mirror image, slid along: the outlines stay the same, the drawings alternate.',
  verts: [P(0.5, 0.5 - MIRROR_R), P(0.5 + MIRROR_R, 0.5), P(0.5, 0.5 + MIRROR_R), P(0.5 - MIRROR_R, 0.5)],
  rels: [ { from: 0, to: 3, d: MIRROR_AXIS, role: 'constraint' }, { from: 1, to: 2, d: MIRROR_AXIS, role: 'constraint' },
          { from: 3, to: 2, d: { type: 'mirror', p0: P(0.5 - MIRROR_R / 2, 0), phi: PI / 2, g: MIRROR_R }, role: 'glue' },
          { from: 0, to: 1, d: { type: 'mirror', p0: P(0.5 + MIRROR_R / 2, 0), phi: PI / 2, g: MIRROR_R }, role: 'glue' } ] });
const isMirrorId = id => id === 'mirror' || id === 'mirror-flip';
const geoId = id => id === 'mirror-flip' ? 'mirror' : id;               // T2: the two arrangements share one tile geometry
// F1a-1 · TWO FIGURES (Slide). Figure A (the left square) and Figure B (the right square) are ONE repeating unit: the engine tiles it as a
// 6-sided cell, as data (verified in ../tessellation-geometry-review/f1). Every outer side is shared with a figure of the OTHER family in a
// neighbouring unit; the side between A and B inside the unit (the INNER side, from (1,0) up to (1,1)) is the app's own geometry, with its own
// points and pulls. Every boundary is one curve shared by an A and a B: whatever one figure gains, the other loses.
const FG_ID = 'fg-slide', FG_IN = 6;                  // FG_IN: the inner side's index (after the 6 engine sides) in snapshots, points and touches
if (!CONS.some(c => c.id === FG_ID)) CONS.push({ id: FG_ID, title: 'Two figures · Slide', prompt: 'Figure A and Figure B share every boundary: pull one and watch the other change.',
  verts: [P(0, 0), P(1, 0), P(2, 0), P(2, 1), P(1, 1), P(0, 1)],
  rels: [ { from: 1, to: 4, d: { type: 'translate', v: [-1, 1] }, role: 'glue' }, { from: 0, to: 3, d: { type: 'translate', v: [1, 1] }, role: 'glue' },
          { from: 2, to: 5, d: { type: 'translate', v: [-2, 0] }, role: 'glue' } ] });
// F1a-2 · MIRROR · TWO FIGURES (verified in ../tessellation-geometry-review/f1a2-mirror). A below B, one vertical mirror line through both. The unit is
// 8-sided for the engine, as data: A's bottom in two mirrored halves (0, 1), A's right side 2 (free) with its mirror twin 7 (A's left), B's sides 3 and 6
// (slid copies of 7 and 2) and B's top 4, 5 (slid copies of 1 and 0). The MIDDLE side, from corner 3 to corner 7, is the app's own geometry in two
// mirrored halves. Both figures are always mirror-symmetric, and different: where A widens, B narrows.
const FG_MID = 'fg-mirror', FG_MAXIS = { type: 'mirror', p0: P(0.5, 0), phi: PI / 2, g: 0 };
if (!CONS.some(c => c.id === FG_MID)) CONS.push({ id: FG_MID, title: 'Two figures · Mirror', prompt: 'Figure A and Figure B are each symmetric about the dashed line, and share every boundary.',
  verts: [P(0, 0), P(0.5, 0), P(1, 0), P(1, 1), P(1, 2), P(0.5, 2), P(0, 2), P(0, 1)],
  rels: [ { from: 0, to: 1, d: FG_MAXIS, role: 'constraint' }, { from: 2, to: 7, d: FG_MAXIS, role: 'constraint' },
          { from: 0, to: 5, d: { type: 'translate', v: [0, 2] }, role: 'glue' }, { from: 1, to: 4, d: { type: 'translate', v: [0, 2] }, role: 'glue' },
          { from: 2, to: 6, d: { type: 'translate', v: [-1, 1] }, role: 'glue' }, { from: 7, to: 3, d: { type: 'translate', v: [1, 1] }, role: 'glue' } ] });
const isFG = id => id === FG_ID || id === FG_MID, isFGM = id => id === FG_MID, FG_OF = { translate: FG_ID, mirror: FG_MID };
const FG_HOME = CONS.find(c => c.id === FG_ID).verts.map(p => P(p.x, p.y));   // the two squares: the unit's corners until the student moves them (F1r)
const FG_MHOME = CONS.find(c => c.id === FG_MID).verts.map(p => P(p.x, p.y)); // (F1a-2) the two squares stacked
const fgHomeOf = id => isFGM(id) ? FG_MHOME : FG_HOME;
// the two figures of a unit, by its number of corners (a moved cage keeps it): the middle side's ends; A = sides 0…e1−1, middle, e2…n−1; B = e1…e2−1
const fgEndsOf = n => n === 8 ? [3, 7] : [1, 4];
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
const POLY_FAMILY = { translate: ['translation', 'fg-slide'], rotate: ['rotation-sq-ac', 'rotation-sq-bd'], glide: ['glide', 'glide-both'], mirror: ['mirror', 'mirror-flip'] };   // student labels: Slide · Turn · Flip · Mirror (T1)
const POLY_FAMILY_OF = { translation: 'translate', 'rotation-sq-ac': 'rotate', 'rotation-sq-bd': 'rotate', glide: 'glide', 'glide-both': 'glide', mirror: 'mirror', 'mirror-flip': 'mirror', 'fg-slide': 'translate', 'fg-mirror': 'mirror' };
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
S.fg = null; S.fgFocus = 'A';        // F1a-1: { id, inner, … } while two figures are in use (else null); F1a-2: S.fgFocus = the figure being WORKED ON (emphasis only, never colour)
const FG_MIN_SHARE = 0.06;           // F1a-1: neither figure may shrink below 6 % of the unit (a figure never collapses)
const FG_CLEAR = 0.02;               //   and the side between them keeps 2 % of a cell from the other sides (a figure is never pinched in two)
const FG_INK = 3.0, FG_FIT = 1.25;   //   the drawing area (3 × 3 cells about the unit) and the view on entry (the unit across 80 % of the width)
const FG_COL = { A: '#f7f1e3', B: '#cf8a62', figure: '#f7f1e3', ground: '#cf8a62' };   //   (F1a-2) each figure's own plain colour: A light, B darker — never exchanged (figure/ground: the older names)
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
  const size = S.fg ? S.unit : S.field.size, hd = 0.5 * Math.hypot(S.vw, S.vh);                 // (F1a-1: zoom as for one cell)
  const sharp = S.fg && S.ink ? 2 * INK_HALF * S.unit / S.ink.side : S.inkBase && S.ink ? S.inkBase.side / S.ink.side : 1;          // (DA: an enlarged drawing area is less sharp: zoom in less, so it never looks softer than today)
  const minS = Math.max(hd / (fieldRadius() * 0.97), 8), maxS = Math.max(MAX_ZOOM_PX_PER_UNIT * sharp / size, minS * 1.2);
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
  S.fitS = 0.5 * Math.min(S.vw, availH) / (S.fg ? FG_FIT * S.unit : S.field.size);
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
  if (S.fg && S.fg.inner) fgRebuild();     // (F1a-1: A, B and the inner side)
}
function rebuildCentroids() {
  S.cent = polyCentroid(E.polygon(edgesNow()));
  S.centW = S.field.list.map(m => mapp(m, S.cent));
}
const snapshot = () => { const s = edgesNow().map(e => e.pts.map(p => ({ x: p.x, y: p.y }))); if (S.fg) s.push(S.fg.inner.map(p => ({ x: p.x, y: p.y }))); return s; };   // (F1a-1: + the inner side)
function setSnapEdges(snap) {              // the engine's sides from a snapshot, and (two figures) the inner side
  const n = E.state.cons.verts.length; E.setEdges(snap.slice(0, n).map(pts => ({ pts: pts.map(p => ({ x: p.x, y: p.y })) })));
  if (S.fg) S.fg.inner = snap.length > n ? snap[n].map(p => ({ x: p.x, y: p.y })) : straightInner();
}
function restoreSnapshot(snap) { setSnapEdges(snap); rebuildPath(); rebuildCentroids(); fgRefresh(ensureInk()); }   // (DA; F1r)
/* F1a-1 · TWO FIGURES. The unit is Figure A (edges 0, inner, 4, 5) + Figure B (edges 1, 2, 3, inner reversed). The engine repeats the unit; every
 * outer side is shared by an A and a B of neighbouring units, and the inner side by the A and B of one unit. The inner side is one more boundary
 * curve of N + 1 samples from corner 1 to corner 4, kept in S.fg.inner, saved and undone with the engine's sides (as a seventh side). */
const fgIn = () => E.state.cons.verts.length;                                // (F1a-2) the middle side's index: after the engine's sides (6 Slide, 8 Mirror)
const fgEnds = () => fgEndsOf(E.state.cons.verts.length);
const fgAxisX = () => { const r = E.state.rels.find(q => q.role === 'constraint' && q.d.type === 'mirror'); return r ? r.d.p0.x : null; };
const fgMirrorM = c => [-1, 0, 0, 1, 2 * c, 0];                            //   the reflection in the mirror line x = c
const straightInner = () => { const V = E.state.cons.verts, [e1, e2] = fgEnds(), a = V[e1], b = V[e2], out = []; for (let i = 0; i <= N; i++) out.push(P(a.x + (b.x - a.x) * i / N, a.y + (b.y - a.y) * i / N)); return out; };
const sidePts = ei => S.fg && ei === fgIn() ? S.fg.inner : edgesNow()[ei].pts;
function fgPolys() {                       // → { A, B }: the two figures' outlines (counter-clockwise, N samples per side)
  const e = edgesNow(), n = e.length, [e1, e2] = fgEndsOf(n), inn = S.fg.inner, A = [], B = [];
  for (let k = 0; k < e1; k++) for (let i = 0; i < N; i++) A.push(e[k].pts[i]);
  for (let i = 0; i < N; i++) A.push(inn[i]);
  for (let k = e2; k < n; k++) for (let i = 0; i < N; i++) A.push(e[k].pts[i]);
  for (let k = e1; k < e2; k++) for (let i = 0; i < N; i++) B.push(e[k].pts[i]);
  for (let i = N; i > 0; i--) B.push(inn[i]);
  return { A, B };
}
const snapInner = snap => snap.length === 7 || snap.length === 9 ? snap[snap.length - 1] : null;   // (F1a-2) the middle side of a two-figure snapshot (Slide 7, Mirror 9 sides)
const pathOf = (pts, close) => { const p = new Path2D(); pts.forEach((q, i) => i ? p.lineTo(q.x, q.y) : p.moveTo(q.x, q.y)); if (close) p.closePath(); return p; };
function fgLabelAt(poly, path) {           // a point well inside the figure for its label: the inside point furthest from its edge (on a 9 × 9 grid)
  const c = polyCentroid(poly);
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity; poly.forEach(p => { x0 = Math.min(x0, p.x); x1 = Math.max(x1, p.x); y0 = Math.min(y0, p.y); y1 = Math.max(y1, p.y); });
  let best = null, bd = -1;
  for (let i = 1; i < 10; i++) for (let j = 1; j < 10; j++) { const q = P(x0 + (x1 - x0) * i / 10, y0 + (y1 - y0) * j / 10); if (!scratch.isPointInPath(path, q.x, q.y)) continue;
    let d = Infinity; for (let k = 0; k < poly.length; k += 3) d = Math.min(d, Math.hypot(poly[k].x - q.x, poly[k].y - q.y)); if (d > bd) { bd = d; best = q; } }
  return best || c;
}
function fgRebuild() {                     // paths for drawing (rebuilt with the outline, so they follow every pull), the shares and the label places
  const { A, B } = fgPolys(), F = S.fg; S.pathA = pathOf(A, true); S.pathB = pathOf(B, true); S.innerPath = pathOf(F.inner, false);
  F.areaA = E.area(A); F.areaB = E.area(B); F.labelA = fgLabelAt(A, S.pathA); F.labelB = fgLabelAt(B, S.pathB); F.centA = polyCentroid(A); F.centB = polyCentroid(B); syncFgShare();   // (F1a-2: + the centres a figure group scales about)
}
const fgShares = () => { const F = S.fg, t = F.areaA + F.areaB, a = Math.round(100 * F.areaA / t); return { A: a, B: 100 - a, a: F.areaA / t, b: F.areaB / t }; };
const fgColours = () => [FG_COL.A, FG_COL.B];   // → [A, B] (F1a-2: fixed; the figure being worked on changes nothing here)
// The guard for two figures: the inner side may not cross the unit's outline or itself, it keeps FG_CLEAR from the outline away from its two
// corners, and each figure keeps at least FG_MIN_SHARE of the unit. With the outline simple (outlineSimple), A and B are then simple, they fill
// the unit exactly, and the units tile the plane: no gaps, no overlaps.
function fgOK(loose) {                     // (loose: crossings and shares only; used for a pull that starts closer than FG_CLEAR, e.g. a Polygon sliver)
  const inn = S.fg.inner, poly = E.polygon(edgesNow()), n = poly.length, cl = FG_CLEAR * S.unit, V = E.state.cons.verts, [e1, e2] = fgEnds(), c1 = V[e1], c4 = V[e2], away = 3 * cl;
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
  for (const p of inn) { if (!Number.isFinite(p.x) || !Number.isFinite(p.y)) return false; if (p.x < x0) x0 = p.x; if (p.x > x1) x1 = p.x; if (p.y < y0) y0 = p.y; if (p.y > y1) y1 = p.y; }
  x0 -= cl; x1 += cl; y0 -= cl; y1 += cl;                                   // (the box grown by the clearance: only nearby outline segments are tested)
  const far = q => Math.hypot(q.x - c1.x, q.y - c1.y) > away && Math.hypot(q.x - c4.x, q.y - c4.y) > away;
  const cand = []; for (let j = 0; j < n; j++) { const a = poly[j], b = poly[(j + 1) % n];
    if ((a.x < x0 && b.x < x0) || (a.x > x1 && b.x > x1) || (a.y < y0 && b.y < y0) || (a.y > y1 && b.y > y1)) continue; cand.push(j); }
  for (let k = 0; k < N; k++) { const a = inn[k], b = inn[k + 1], mnx = Math.min(a.x, b.x) - cl, mxx = Math.max(a.x, b.x) + cl, mny = Math.min(a.y, b.y) - cl, mxy = Math.max(a.y, b.y) + cl;
    for (const j of cand) { const c = poly[j], d = poly[(j + 1) % n];
      if ((c.x < mnx && d.x < mnx) || (c.x > mxx && d.x > mxx) || (c.y < mny && d.y < mny) || (c.y > mxy && d.y > mxy)) continue;
      if (segX(a.x, a.y, b.x, b.y, c.x, c.y, d.x, d.y)) return false;
      if (loose) continue;
      if (k > 0 && far(a) && distPS(a, c, d) < cl) return false;                                 // an inner sample too close to the outline
      if (far(c) && Math.hypot(c.x - (a.x + b.x) / 2, c.y - (a.y + b.y) / 2) < cl + 0.5 * Math.hypot(b.x - a.x, b.y - a.y) && distPS(c, a, b) < cl) return false; }   // …or an outline sample too close to it
    for (let j = k + 2; j < N; j++) { const c = inn[j], d = inn[j + 1];
      if ((c.x < mnx && d.x < mnx) || (c.x > mxx && d.x > mxx) || (c.y < mny && d.y < mny) || (c.y > mxy && d.y > mxy)) continue;
      if (segX(a.x, a.y, b.x, b.y, c.x, c.y, d.x, d.y)) return false; } }
  const { A, B } = fgPolys(), a = E.area(A), b = E.area(B), t = a + b;
  return a >= FG_MIN_SHARE * t && b >= FG_MIN_SHARE * t;
}
const fgFall = (d, R) => { const t = Math.max(0, Math.min(1, 1 - d / R)); return t * t * (3 - 2 * t); };   // the engine's falloff (smoothstep), for the inner side
function fgStartPull(h, e) {               // Shape › Pull on the inner side: the same grab, falloff and guard as an outer side; its corners stay fixed
  const pts = S.fg.inner, L = E.cumLen(pts), seg = L[h.i + 1] - L[h.i], s0 = grabArc(L, L[h.i] + seg * h.t);
  const g = { inner: true, e: fgIn(), base: pts.map(p => P(p.x, p.y)), L, total: L[N], s: s0, start: h.w, axis: isFGM(S.consId) ? fgAxisX() : null }, c = pointAtArc(pts, L, s0);
  S.shape = { g, before: snapshot(), hitWorld: c, c, ranges: [], lastReq: P(0, 0), blocked: false, gs: { frames: 0, blocked: 0, ms: [] } };
  S.shape.loose = !fgOK(); S.shape.guard = S.guardShape && outlineSimple(allRanges()) && fgOK(S.shape.loose);
  S.hl = { edge: fgIn(), linked: [], active: true, t1: 0 };
  work = { type: 'shape', id: e.pointerId, t0: performance.now() };
}
function fgInnerUpdate(g, req) {
  const R = E.getRadius() * g.total;
  if (g.axis === null) { S.fg.inner = g.base.map((p, i) => { if (i === 0 || i === N) return P(p.x, p.y); const w = fgFall(Math.abs(g.L[i] - g.s), R); return P(p.x + req.x * w, p.y + req.y * w); }); return; }
  // (F1a-2) Mirror: the pull is folded onto the first half (a grab on the second half pulls its mirror image), the middle sample stays on the mirror line,
  // and the second half is the first half reflected — the middle side stays exactly symmetric
  const h = N / 2, c = g.axis, first = g.s <= g.total / 2, s = first ? g.s : g.total - g.s, rq = first ? req : P(-req.x, req.y), out = g.base.map(p => P(p.x, p.y));
  for (let i = 1; i <= h; i++) { const w = fgFall(Math.abs(g.L[i] - s), R); out[i] = P(g.base[i].x + rq.x * w, g.base[i].y + rq.y * w); }
  out[h] = P(c, out[h].y); for (let i = h + 1; i < N; i++) out[i] = P(2 * c - out[N - i].x, out[N - i].y); out[N] = P(g.base[N].x, g.base[N].y);
  S.fg.inner = out;
}
function resampleN(pts, n) {              // n even segments along the polyline (the engine's resample, for any n)
  const L = E.cumLen(pts), total = L[L.length - 1], out = [pts[0]]; let j = 1;
  for (let k = 1; k < n; k++) { const t = total * k / n; while (L[j] < t) j++; const u = (t - L[j - 1]) / ((L[j] - L[j - 1]) || 1); out.push(P(pts[j - 1].x + (pts[j].x - pts[j - 1].x) * u, pts[j - 1].y + (pts[j].y - pts[j - 1].y) * u)); }
  out.push(pts[pts.length - 1]); return out;
}
function fgResample(inner) {              // evenly spaced on release; Mirror: the first half, reflected
  const c = isFGM(S.consId) ? fgAxisX() : null; if (c === null) return E.resample(inner);
  const half = resampleN(inner.slice(0, N / 2 + 1), N / 2); half[N / 2] = P(c, half[N / 2].y);
  return half.concat(half.slice(0, -1).reverse().map(p => P(2 * c - p.x, p.y)));
}


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
function makeInk(side, centre) {          // (DA: side and centre are given when the drawing area is moved to hold the tile; see ensureInk)
  const c0 = centre || S.field.c0; side = side || (S.fg ? FG_INK * S.unit : 2 * INK_HALF * S.field.size); S.ink = { x0: c0.x - side / 2, y1: c0.y + side / 2, side };
  if (!centre) S.inkBase = { side, centre: P(c0.x, c0.y) };                   // today's square: the drawing area whenever the tile fits in it
  S.layers = { sketch: makeLayer(INK_BIG, true), art: makeLayer(INK_BIG, true), fills: makeLayer(FLOOD, true), lines: makeLayer(FLOOD, false) }; S.tint = new Map(); S.compCache = new Map(); S.compPool = { big: [], small: [] }; S.layerVer++;
}
/* DA · THE DRAWING AREA FOLLOWS THE TILE. The drawing layers are square images; today's square (2.5 cells about the starting cell) is kept while the
 * tile fits in it (so every such project is exactly as before). When Shape › Pull carries the tile further, the square is moved and enlarged, in
 * 1/8-cell steps, to hold the whole tile: strokes are stored as points, so the history replays them whole (the replay Undo uses). The area depends
 * only on the tile as it is in Shape (also while Polygon is open), so it is the same after reopening a project. Checked whenever a boundary
 * change settles: the end of a pull, Undo/Redo and Reset (restoreSnapshot), and every stage change. Same pixel size: only an enlarged area is
 * less sharp, and the maximum zoom follows it (zoomLimits). */
function inkFor() {                      // → { side, centre }
  const z = S.unit, base = S.inkBase, m = 0.08 * z, sides = S.mode === 'polygon' && S.refined ? S.refined : edgesNow().map(e => e.pts);
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity; sides.forEach(pts => pts.forEach(p => { if (p.x < x0) x0 = p.x; if (p.x > x1) x1 = p.x; if (p.y < y0) y0 = p.y; if (p.y > y1) y1 = p.y; }));
  const h = base.side / 2; if (x0 - m >= base.centre.x - h && x1 + m <= base.centre.x + h && y0 - m >= base.centre.y - h && y1 + m <= base.centre.y + h) return base;
  const q = 0.125 * z, side = Math.max(base.side, Math.ceil((Math.max(x1 - x0, y1 - y0) + 2 * m) / q - 1e-9) * q);
  return { side, centre: P(Math.round((x0 + x1) / q) * q / 2, Math.round((y0 + y1) / q) * q / 2) };
}
function ensureInk() {                   // → true when the drawing area changed (the layers are then made again and the history replayed)
  if (!S.ink || !S.layers || !S.inkBase || !S.field) return false;
  const want = inkFor(), cx = S.ink.x0 + S.ink.side / 2, cy = S.ink.y1 - S.ink.side / 2;
  if (Math.abs(want.side - S.ink.side) < 1e-9 && Math.abs(want.centre.x - cx) < 1e-9 && Math.abs(want.centre.y - cy) < 1e-9) return false;
  const t0 = performance.now(); makeInk(want.side, want.centre); rebuildLayers(); S.inkMs = performance.now() - t0; clampCam(); invalidate(); return true;
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
  if (st.mirror) { paintPenMirror(L, st, opaque); return; }        // T1: mirrored drawing (see the T1 section)
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
  if (st.mirror) { const c = L.bctx, w2 = newWalker(); c.save(); c.setTransform(...pxMirror(L, st.mirror));   // T1: the same marks again, reflected (exact mirror images)
    stampStart(L, st, st.pts[0], w2, c); for (let i = 1; i < st.pts.length; i++) stampSeg(L, st, st.pts[i - 1], st.pts[i], w2, c); c.restore(); }
}

const sizeKey = () => shaping() ? 'sketch' : (S.tool === 'fill' ? 'pen' : S.tool);   // which remembered size the slider edits
const widthFor = key => { const [a, b] = SIZE_RANGE[key], v = S.sizes[key]; return (a + b * v * v) * S.unit; };
function newStroke() {
  if (shaping()) return Object.assign({ kind: 'stroke', layer: 'sketch', tool: S.sketchTool, color: SKETCH_COLOR, alpha: 1, w: widthFor('sketch') * (S.sketchTool === 'eraser' ? 1.6 : 1), pts: [] }, S.mode === 'polygon' ? { stage: 'polygon' } : {});   // (CR3: Polygon too)
  return Object.assign({ kind: 'stroke', layer: 'art', tool: S.tool, pattern: S.pattern, angle: S.angle, seed: (Math.random() * 4294967295) >>> 0, color: S.color,
    alpha: S.tool === 'eraser' ? 1 : Math.max(MIN_ALPHA, S.opac[S.tool] == null ? 1 : S.opac[S.tool]), w: widthFor(S.tool), pts: [] }, mirrorDrawOn() ? { mirror: mirrorAxisArr() } : {});   // (T1)
}

/* ---- Fill: flood fill on a 1024² grid. Boundaries = outside the CURRENT tile, PEN lines, and (optionally) sketch lines.
 *      The region's old colour is CLEARED first and the new colour (with its opacity) painted into the FILLS layer, which sits
 *      beneath every line — so a region can always be recoloured, and no halo shows beside a line. ---- */
function maskPathFor(snap, L) {
  const path = new Path2D(); let first = true;
  (snapInner(snap) ? snap.slice(0, -1) : snap).forEach(pts => {        // (F1a-1: a two-figure unit's outline, without the inner side)
    for (let k = 0; k < N; k++) { const q = toPx(pts[k], L); first ? path.moveTo(q.x, q.y) : path.lineTo(q.x, q.y); first = false; } });
  path.closePath(); return path;
}
let fillCtx = null;                       // (F1r) while the layers are redone: the masks that stay the same from one fill to the next
function doFill(a, snap) {
  const fig = S.fg ? (a.figure || 'A') : null; if (fig) snap = snapshot();   // (F1r: Two figures — every fill fills its own figure as it is NOW; a fill made in One figure belongs to A)
  const F = S.layers.fills, G = F.size; S.flood = S.flood || mkCanvas(G); S.flood2 = S.flood2 || mkCanvas(G);
  const tc = S.flood.getContext('2d', { willReadFrequently: true }), mask = maskPathFor(snap, F);
  const alphaOf = draw => { tc.setTransform(1, 0, 0, 1, 0, 0); tc.clearRect(0, 0, G, G); draw(); const d = tc.getImageData(0, 0, G, G).data, out = new Uint8Array(G * G); for (let i = 0; i < out.length; i++) out[i] = d[i * 4 + 3]; return out; };
  const inner = snapInner(snap);          // (F1a-1: the side between A and B is cut out of the region, so a fill stays in its figure)
  const cache = fillCtx;                   // (F1r: in Two figures every fill of one redo has the same outline; the pen lines change only with a pen stroke)
  const inside = fig && cache && cache.inside ? cache.inside : alphaOf(() => { tc.fillStyle = '#fff'; tc.fill(mask);
    if (inner) { tc.globalCompositeOperation = 'destination-out'; tc.lineWidth = 2.5; tc.beginPath(); inner.forEach((p, i) => { const q = toPx(p, F); i ? tc.lineTo(q.x, q.y) : tc.moveTo(q.x, q.y); }); tc.stroke(); tc.globalCompositeOperation = 'source-over'; } });
  if (fig && cache) cache.inside = inside;
  const lines = cache && cache.lines ? cache.lines : alphaOf(() => tc.drawImage(S.layers.lines.big, 0, 0)); if (cache) cache.lines = lines;
  const sk = a.respectSketch ? alphaOf(() => tc.drawImage(S.layers.sketch.big, 0, 0, G, G)) : null;
  const figM = fig ? (cache && cache.fig[fig]) || alphaOf(() => { tc.fillStyle = '#fff'; tc.fill(pathOf(F1polyPx(fig, F), true)); }) : null;   // (F1r: the figure itself is the region's limit)
  if (fig && cache) cache.fig[fig] = figM;
  const barrier = i => inside[i] < 128 || (figM && figM[i] < 128) || lines[i] > 24 || (sk && sk[i] > 24);
  const sp = toPx(a.seed, F); let sx = Math.round(sp.x), sy = Math.round(sp.y), seed = -1;
  for (let r = 0; r <= (fig ? 60 : 4) && seed < 0; r++) for (let dy = -r; dy <= r && seed < 0; dy++) for (let dx = -r; dx <= r; dx++) {   // (F1r: the figure may have moved off the tap)
    if (r > 4 && Math.max(Math.abs(dx), Math.abs(dy)) !== r) continue;
    const x = sx + dx, y = sy + dy; if (x < 0 || y < 0 || x >= G || y >= G) continue; if (!barrier(y * G + x)) { seed = y * G + x; break; } }
  if (seed < 0) return false;
  if (!S.fillBuf || S.fillBuf.G !== G) S.fillBuf = { G, region: new Uint8Array(G * G), grown: new Uint8Array(G * G) };   // (F1r: reused, so a redo of many fills makes no garbage)
  const region = S.fillBuf.region.fill(0), stack = [seed]; region[seed] = 1; let count = 0;
  while (stack.length) { const i = stack.pop(); count++; const x = i % G, y = (i - x) / G;
    if (x > 0 && !region[i - 1] && !barrier(i - 1)) { region[i - 1] = 1; stack.push(i - 1); }
    if (x < G - 1 && !region[i + 1] && !barrier(i + 1)) { region[i + 1] = 1; stack.push(i + 1); }
    if (y > 0 && !region[i - G] && !barrier(i - G)) { region[i - G] = 1; stack.push(i - G); }
    if (y < G - 1 && !region[i + G] && !barrier(i + G)) { region[i + G] = 1; stack.push(i + G); } }
  const grown = S.fillBuf.grown; grown.set(region);
  for (let i = 0; i < region.length; i++) if (region[i]) { const x = i % G;
    if (x > 0) grown[i - 1] = 1; if (x < G - 1) grown[i + 1] = 1; if (i >= G) grown[i - G] = 1; if (i < G * G - G) grown[i + G] = 1; }
  if (a.edge) {                     // CR2: a new fill also reaches 3 grid pixels PAST the tile edge (outside the tile only), so where tiles meet the colour runs
    let front = [];                 // under the neighbour's edge instead of fading out before it: no light hairline with the Tessellate outline at 0.
    const reach = (j, to) => { if (j >= 0 && j < grown.length && !grown[j] && inside[j] < 128) { grown[j] = 1; to.push(j); } };   // (F1r: the same pixels, without a small array per pixel)
    for (let i = 0; i < grown.length; i++) if (grown[i] && inside[i] >= 128) { const x = i % G;   // (fills made before CR2 have no `edge` and stay exactly as they were)
      reach(x > 0 ? i - 1 : -1, front); reach(x < G - 1 ? i + 1 : -1, front); reach(i - G, front); reach(i + G, front); }
    for (let pass = 1; pass < 3; pass++) { const next = []; for (const i of front) { const x = i % G;
      reach(x > 0 ? i - 1 : -1, next); reach(x < G - 1 ? i + 1 : -1, next); reach(i - G, next); reach(i + G, next); } front = next; }
  }
  const n = parseInt(a.color.slice(1), 16), R = n >> 16, Gc = (n >> 8) & 255, B = n & 255, fc = S.flood2.getContext('2d'), al = Math.round(255 * Math.max(MIN_ALPHA, a.alpha == null ? 1 : a.alpha));
  let x0 = G, y0 = G, x1 = -1, y1 = -1;     // (F1r: only the region's box is painted: the same pixels as painting the whole raster, which is clear outside it)
  for (let i = 0; i < grown.length; i++) if (grown[i]) { const x = i % G, y = (i - x) / G; if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y; }
  const bw = x1 - x0 + 1, bh = y1 - y0 + 1;
  const img = (fn) => { const id = fc.createImageData(bw, bh); for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) if (grown[y * G + x]) fn(id.data, ((y - y0) * bw + x - x0) * 4); fc.putImageData(id, x0, y0); };
  const c = F.bctx; c.save(); c.setTransform(1, 0, 0, 1, 0, 0); if (!a.edge) c.clip(mask); c.imageSmoothingEnabled = false;
  img((d, o) => { d[o] = d[o + 1] = d[o + 2] = 0; d[o + 3] = 255; }); c.globalCompositeOperation = 'destination-out'; c.drawImage(S.flood2, x0, y0, bw, bh, x0, y0, bw, bh);           // clear the old colour
  img((d, o) => { d[o] = R; d[o + 1] = Gc; d[o + 2] = B; d[o + 3] = al; }); c.globalCompositeOperation = 'source-over'; c.drawImage(S.flood2, x0, y0, bw, bh, x0, y0, bw, bh);       // paint the new one
  c.restore(); touchLayers(); return count > 0;
}

/* ---------------- history: ONE chronological list (sketch strokes, art strokes/erases/dots/textures, fills, shape pulls, shape resets).
 *                  Composition (Tessellate display choices) and the Reference image are deliberately NOT in this history. ---------------- */
function pushAction(a) { S.history.length = S.hp; S.history.push(a); S.hp = S.history.length; syncUndo(); }
function syncUndo() {
  const u = S.hp === 0, r = S.hp >= S.history.length; $('undo').disabled = u; $('redo').disabled = r;
  $('sb-undo').disabled = u; $('sb-redo').disabled = r;   // (PH1: Redo stays visible, dimmed when there is nothing to redo)   // Shape bar: Redo shows only after an Undo (its place is kept, so nothing shifts)
}
function rebuildLayers() {                      // replay, tracking the boundary as it was at each step (fills depend on it)
  Object.values(S.layers).forEach(clearLayer); let snap = S.initialSnap; fillCtx = { fig: {} };          // (F1r: masks reused between fills)
  try { for (let i = 0; i < S.hp; i++) { const a = S.history[i];
    if (a.kind === 'shape') snap = a.after; else if (a.kind === 'stroke') { paintStrokeCanonical(a); if (a.layer === 'art' && isPenLike(a)) fillCtx.lines = null; } else if (a.kind === 'fill') doFill(a, a.snap || snap); } }
  finally { fillCtx = null; }
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
  // (T2: Alternating places its tiles exactly where Mirror does; it uses Mirror's exact repeat vectors, so Row and Column name the same tiles in both
  // arrangements. Its glides carry rounding noise of 1e-16, enough to decide the tie between the two diagonal repeats the other way.)
  const ms = S.consId === 'mirror-flip' ? CONS.find(c => c.id === 'mirror').rels.filter(r => r.role === 'glue').map(r => E.descMatrix(r.d)) : glueRels().map(r => r.m);
  const c0 = S.field.c0, d = ms.map(m => { const q = mapp(m, c0); return P(q.x - c0.x, q.y - c0.y); }), h = v => Math.abs(v.x) / Math.hypot(v.x, v.y);   // (T1: the repeats, i.e. the glue relations)
  const j = Math.max(1, d.findIndex((v, k) => k > 0 && Math.abs(d[0].x * v.y - d[0].y * v.x) > 1e-9)), pair = [d[0], d[j]];   // (F1a-2: the first INDEPENDENT pair; Mirror · Two figures lists the vertical repeat twice)
  let [b1, b2] = h(pair[0]) >= h(pair[1]) ? [pair[0], pair[1]] : [pair[1], pair[0]];          // b1 = the more horizontal repeat (columns), b2 = the other (rows)
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
  S.consId = id; S.fg = null; E.build(id);                          // (F1a-1: two figures are chosen in Polygon)
  const { t, f } = makeField(); S.field = t; S.fieldCull = f;
  S.cellKind = id === 'rotation-tri' ? 'triangle' : id === 'reflection' ? 'rhombus' : 'square';
  S.origVerts = E.state.cons.verts.map(p => P(p.x, p.y));        // original cage, stored independently of the live boundary
  S.orientCue = orientCueNow();   // some neighbours turned/mirrored (not pure translation)
  makeInk(); S.history = []; S.hp = 0; S.hl = null; S.shape = null; S.stroke = null; S.artVer = 0; S.camByMode = {}; work = null; nav = refNav = null;
  S.comp = { same: {}, alt: {}, row: {}, col: {} }; S.sel = null; S.ref.img = null; S.ref.adjust = false; S.ref.locked = false; syncUndo();
  S.outline = OUTLINE_DEFAULT; S.showSketch = false; syncCR2UI();                                  // CR2
  // v5.0: a square-grid start opens in POLYGON (no transformation chosen yet: the plain square grid); triangle / rhombus open in Shape as before
  S.poly = opts && opts.polygon ? { family: null, nodes: {}, hist: [{ consId: id, family: null, nodes: {} }], hp: 0, sel: null } : null;
  S.shapeBaseKey = null; S.refined = null; S.recovery = null; S.consLink = null; S.restartOK = false; S.pendingPoly = null;
  S.cageNow = null; S.engineId = id; S.unit = S.field.size; S.gridBasis = null; S.lockFlash = null;
  rebuildPath(); rebuildCentroids(); E.setRadius(influenceRadius(S.influenceV)); S.initialSnap = snapshot();
  const mode = S.poly ? 'polygon' : 'shape';
  $('entry').hidden = true; S.mode = mode; resize(); fitCamera(); setMode(mode, true); syncRefUI(); syncPolyUI(); syncRestoreUI(); updateTitle();
  if (!(opts && opts.quiet)) toast(S.poly ? 'Polygon · choose how the tiles repeat' : cardInfo(id).short, 2000);   // the construction name: briefly on entry, and as the menu's heading (CR1: not when a saved project is rebuilt)
}
const startPolygon = () => {                  // CR3: the square Polygon starts with Translation chosen (Free polygon, later, will start with none)
  start('translation', { polygon: true, quiet: true });
  const st = { consId: 'translation', family: 'translate', cage: null, nodes: {} }; S.poly.hist[0] = st; applyPolyState(st);
  if (!S.seenHint.polygon) { S.seenHint.polygon = true; toast(HINTS.polygon, 3600); } else toast('Quad · Translate', 1600);
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
  if (e.tint && e.tint.startsWith('fg:') && S.fg) { const t = e.tint.slice(3).split('|'), fig = f => { x.save(); x.setTransform(1, 0, 0, 1, 0, 0); x.beginPath(); offsetPolygon(fgPolys()[f], 1 / k).forEach((p, j) => { const q = P((p.x - i.x0) * k, (i.y1 - p.y) * k); j ? x.lineTo(q.x, q.y) : x.moveTo(q.x, q.y); }); x.closePath(); x.clip(); };
    ['A', 'B'].forEach((f, j) => { fig(f); layer(t[j] ? getTint(t[j]) : L.fills.view, e.A.art); x.restore(); }); }   // (F1a-2: each figure's fills in its own group's fill colour, or as drawn)
  else layer(e.tint ? getTint(e.tint) : L.fills.view, e.A.art);
  layer(L.sketch.view, e.A.sketch); layer(L.art.view, e.A.art);
  x.restore();
}
function patchComposites(r) {          // patch the composites in use (this or the previous frame); recycle the rest — they are rebuilt if needed again
  S.compCache.forEach((e, key) => { if (S.frameNo - e.used <= 1) { paintComposite(e, r); return; }
    S.compCache.delete(key); const pool = S.compPool[e.c.width === INK_BIG ? 'big' : 'small']; if (pool.length < 3) pool.push(e.c); });
}
function getComposite(big, A, tint, mark) {
  const key = [A.sketch, A.art, tint || '', mark || 0, big ? 1 : 0, mark ? S.field.c0.x + ',' + S.field.c0.y : ''].join('|'); let e = S.compCache.get(key);   // (F1a-2: a two-figure tint names both figures' colours)   // v5.1: the F sits at the cage centre
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
  if (S.fg && S.mode === 'tessellate') { drawFgTile(m, alpha, i, A, part); return; }                // (F1a-2: each figure has its own group)
  const tess = S.mode === 'tessellate', cp = tess ? compOf(i) : null, size = S.field.size * S.cam.s;
  if (cp && cp.hidden) {                                                 // hidden: draw only a faint outline so the tile can be tapped and shown again
    if (EXP || !(all || part === 'line')) return;                        // (CR2: that outline is a control, not part of an exported picture)
    ctx.save(); ctx.setTransform(...mmul(worldToScreenMatrix(), m)); ctx.globalAlpha = 0.18; ctx.setLineDash([4 / S.cam.s, 5 / S.cam.s]); ctx.strokeStyle = '#fff'; ctx.lineWidth = 1 / S.cam.s; ctx.stroke(S.path); ctx.restore(); drawSelection(m, i); return;
  }
  const mm = cp && cp.scale != null && Math.abs(cp.scale - 1) > 1e-6 ? mmul(m, scaleAbout(S.cent, cp.scale)) : m;
  ctx.save(); ctx.globalAlpha = alpha * (cp && cp.alpha != null ? cp.alpha : 1); ctx.setTransform(...mmul(worldToScreenMatrix(), mm));
  const tp = all ? S.path : bleedPath();
  if (all || part === 'bg') { const base = tess ? ((cp && cp.bg) || COLORS.fill) : (S.orientCue && shaping() && det(m) < 0 ? COLORS.fillMirror : COLORS.fill);
    if (S.fg) { const [ca, cb] = fgColours(); ctx.fillStyle = cb; ctx.fill(tp); ctx.fillStyle = ca; ctx.fill(S.pathA); }   // (F1a-1: B, then A over it; F1a-2: fixed colours)
    else { ctx.fillStyle = base; ctx.fill(tp); } }
  if (all || part === 'art') {
    ctx.save(); ctx.clip(tp);
    const poly = S.mode === 'polygon';         // v5.1: in Polygon the cage (and so the F's place) can change every frame: draw the F as lines, not in the cached composite
    drawComposite(size, A, cp && cp.fig ? cp.fig : null, poly ? 0 : S.orientCue ? (shaping() ? MARK_ALPHA.shape : tess && artEmpty ? MARK_ALPHA.tessellate : 0) : 0);
    if (poly && S.orientCue) drawMarkLines(MARK_ALPHA.shape);
    ctx.restore();
    if (S.fg && active && !EXP) { ctx.fillStyle = S.mode === 'illustrate' ? 'rgba(19,28,45,.16)' : 'rgba(19,28,45,.24)'; ctx.fill(S.fgFocus === 'A' ? S.pathB : S.pathA); }   // (F1a-2: Working on — the other figure quietly dimmed; never exported)
  }
  if (all || part === 'line') {
    const lw = tess ? outlineWorld() : (active ? (shaping() ? 2.4 : 1.6) : 1.1) / S.cam.s;        // CR2: Tessellate's outline is part of the artwork (adjustable, 0 = none)
    if (lw > 0) { ctx.lineJoin = 'round'; ctx.strokeStyle = COLORS.line; ctx.lineWidth = lw; ctx.stroke(S.path); if (S.fg) ctx.stroke(S.innerPath); }   // (F1a-1: + the side between A and B)
  }
  ctx.restore(); if (tess && !EXP && (all || part === 'line')) drawSelection(mm, i);
}
/* F1a-2 · TESSELLATE IN TWO FIGURES. Groups belong to a FIGURE: the grouping (Same / Alternate / Row / Column) groups the units, and each unit's A and
 * its B are in separate groups, keyed 'A:' or 'B:' + the unit group's key. A tap selects the group of the figure tapped; its Colour (the figure's
 * plain colour), Fill colour (its fills recoloured), Opacity, Scale (about the figure's centre) and Hide act on that figure only. */
const fgPlain = cp => !cp || (!cp.hidden && cp.alpha == null && (cp.scale == null || Math.abs(cp.scale - 1) <= 1e-6));
const fgTintKey = (a, b) => a || b ? 'fg:' + (a || '') + '|' + (b || '') : null;
function fgComp(i) { const g = groupOf(i).key, m = S.comp[S.treat]; return { A: m['A:' + g] || null, B: m['B:' + g] || null, key: g }; }
const fgGroupLabel = g => S.treat === 'same' ? 'all' : S.treat === 'alt' ? 'Alternate ' + (g.key === 'p0' ? 1 : 2) : g.label;
function drawFgTile(m, alpha, i, A, part) {
  const all = part === 'all', c = fgComp(i), size = S.field.size * S.cam.s, F = S.fg, W = worldToScreenMatrix(), tint = fgTintKey(c.A && c.A.fig, c.B && c.B.fig);
  const bg = f => (c[f] && c[f].bg) || FG_COL[f], lw = outlineWorld();
  if (fgPlain(c.A) && fgPlain(c.B)) {      // the usual case: the unit in one piece, as before (no seam between A and B)
    ctx.save(); ctx.globalAlpha = alpha; ctx.setTransform(...mmul(W, m)); const tp = all ? S.path : bleedPath();
    if (all || part === 'bg') { ctx.fillStyle = bg('B'); ctx.fill(tp); ctx.fillStyle = bg('A'); ctx.fill(S.pathA); }
    if (all || part === 'art') { ctx.save(); ctx.clip(tp); drawComposite(size, A, tint, 0); ctx.restore(); }
    if ((all || part === 'line') && lw > 0) { ctx.lineJoin = 'round'; ctx.strokeStyle = COLORS.line; ctx.lineWidth = lw; ctx.stroke(S.path); ctx.stroke(S.innerPath); }
    ctx.restore();
  } else for (const f of ['B', 'A']) {    // a figure group with its own opacity, scale or Hide: each figure on its own
    const cp = c[f], path = f === 'A' ? S.pathA : S.pathB;
    if (cp && cp.hidden) { if (EXP || !(all || part === 'line')) continue;     // hidden: a faint outline, so it can be tapped and shown again (not exported)
      ctx.save(); ctx.setTransform(...mmul(W, m)); ctx.globalAlpha = 0.18; ctx.setLineDash([4 / S.cam.s, 5 / S.cam.s]); ctx.strokeStyle = '#fff'; ctx.lineWidth = 1 / S.cam.s; ctx.stroke(path); ctx.restore(); continue; }
    const mm = cp && cp.scale != null && Math.abs(cp.scale - 1) > 1e-6 ? mmul(m, scaleAbout(F['cent' + f], cp.scale)) : m;
    ctx.save(); ctx.globalAlpha = alpha * (cp && cp.alpha != null ? cp.alpha : 1); ctx.setTransform(...mmul(W, mm));
    if (all || part === 'bg') { ctx.fillStyle = bg(f); ctx.fill(path); }
    if (all || part === 'art') { ctx.save(); ctx.clip(path); drawComposite(size, A, tint, 0); ctx.restore(); }
    if ((all || part === 'line') && lw > 0) { ctx.lineJoin = 'round'; ctx.strokeStyle = COLORS.line; ctx.lineWidth = lw; ctx.stroke(path); }
    ctx.restore();
  }
  if (!EXP && (all || part === 'line')) drawFgSelection(m, c);
}
function drawFgSelection(m, c) {           // the selected figure group: that figure outlined in every unit of the group
  const s = S.sel; if (!s || !s.fig || s.mode !== S.treat || c.key !== s.unitKey) return; const cp = c[s.fig];
  const mm = cp && !cp.hidden && cp.scale != null && Math.abs(cp.scale - 1) > 1e-6 ? mmul(m, scaleAbout(S.fg['cent' + s.fig], cp.scale)) : m;
  ctx.save(); ctx.setTransform(...mmul(worldToScreenMatrix(), mm)); ctx.lineJoin = 'round'; ctx.strokeStyle = COLORS.edgeA; ctx.lineWidth = 3 / S.cam.s; ctx.globalAlpha = 0.95; ctx.stroke(s.fig === 'A' ? S.pathA : S.pathB); ctx.restore();
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
  const r = rEmpty(), pad = strokePad(st), ms = st.mirror ? mirrorLive(s) : null;      // T1: with mirrored drawing the reflected half is drawn live too
  for (let j = Math.max(0, s.painted - 2); j < n; j++) { rAddPt(r, st.pts[j], pad); if (ms) rAddPt(r, ms.pts[j], pad); }
  s.views.forEach(L => {
    if (!isPenLike(st)) { for (let j = s.painted; j < n; j++) j === 0 ? stampStart(L, st, st.pts[0], s.wk, L.vctx) : stampSeg(L, st, st.pts[j - 1], st.pts[j], s.wk, L.vctx);
      if (ms) { const c = L.vctx; s.wkM = s.wkM || newWalker(); c.save(); c.setTransform(...pxMirror(L, st.mirror));
        for (let j = s.painted; j < n; j++) j === 0 ? stampStart(L, st, st.pts[0], s.wkM, c) : stampSeg(L, st, st.pts[j - 1], st.pts[j], s.wkM, c); c.restore(); }
      return; }
    if (!s.mask) { for (let j = s.painted; j < n; j++) { paintPenPiece(L.vctx, L, st, j, false); if (ms) paintPenPiece(L.vctx, L, ms, j, false); } return; }
    // translucent pen: the stroke is drawn OPAQUE into a mask, then (inside r) the view = truth-before-stroke + mask × opacity — joins never darken
    const mc = s.mask.getContext('2d'); for (let j = s.painted; j < n; j++) { paintPenPiece(mc, L, st, j, true); if (ms) paintPenPiece(mc, L, ms, j, true); }
    const q = rPx(r, L.size, 2); if (!q) return; L.vctx.putImageData(L.bctx.getImageData(q.x, q.y, q.w, q.h), q.x, q.y);
    L.vctx.save(); L.vctx.beginPath(); L.vctx.rect(q.x, q.y, q.w, q.h); L.vctx.clip(); L.vctx.globalAlpha = st.alpha; L.vctx.drawImage(s.mask, q.x, q.y, q.w, q.h, q.x, q.y, q.w, q.h); L.vctx.restore();
  });
  s.painted = n; rAdd(s.dirty, r); patchComposites(r);
}
function finishStroke(commit) {         // the finger lifted (commit) or the stroke was cancelled
  const s = S.stroke; S.stroke = null; if (!s) return; const pad = strokePad(s.st); s.st.pts.forEach(p => rAddPt(s.dirty, p, pad));
  if (s.st.mirror) mirrorPts(s.st).forEach(p => rAddPt(s.dirty, p, pad));          // (T1)
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
  const sh = S.shape, g = sh.g; let use = req;
  // F1a-1: the inner side is moved by the app; with two figures the guard also keeps A and B whole (fgOK)
  const apply = q => g.inner ? fgInnerUpdate(g, q) : E.updateGesture(g, q), good = () => (g.inner || outlineSimple(sh.ranges)) && (!S.fg || fgOK(sh.loose));
  apply(req);
  if (sh.guard) {
    const t0 = performance.now(); sh.gs.frames++;
    if (!good()) {
      const a = sh.lastReq; let lo = 0, hi = 1;
      for (let k = 0; k < 7; k++) { const m = (lo + hi) / 2; apply(P(a.x + (req.x - a.x) * m, a.y + (req.y - a.y) * m)); good() ? lo = m : hi = m; }
      use = P(a.x + (req.x - a.x) * lo, a.y + (req.y - a.y) * lo); apply(use); sh.blocked = true; sh.gs.blocked++;
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
  if (ga > 0 && !(EXP && EXP.tileOnly)) for (let i = 1; i < list.length; i++) {   // (PH2: a Gallery tile picture has no neighbours)
    const c = w2s(S.centW[i]); if (c.x < -margin || c.x > S.vw + margin || c.y < -margin || c.y > S.vh + margin) continue;
    shown.push(i); if (PERF && !EXP) PERF.n('tiles');
  }
  const pass = part => { shown.forEach(i => drawTile(list[i], ga, false, i, A, artEmpty, part)); drawTile(IDM, 1, true, 0, A, artEmpty, part); };
  if (thinOutline()) { pass('bg'); pass('art'); pass('line'); } else pass('all');
  if (EXP) return;
  drawReference();
  ctx.setTransform(S.dpr, 0, 0, S.dpr, 0, 0);
  if (S.showStart) drawStartShape();
  if ((isMirrorId(S.consId) && (S.mode === 'polygon' || S.mode === 'shape' || (S.mode === 'illustrate' && S.mirrorDraw))) || (isFGM(S.consId) && shaping())) drawMirrorAxis();   // (T1; F1a-2)
  if (S.mode === 'shape') { drawHighlights(); drawInfluencePreview(); }
  if (S.fg && shaping()) drawFigureLabels();                                    // (F1a-1)
  if (S.mode === 'polygon' && S.poly) drawPolygonOverlay();   // (PH1: Tri's Polygon view has no handles)
}
function drawFigureLabels() {             // a quiet 'A' and 'B' in the starting unit, so the student always knows which figure is which
  const F = S.fg; if (!F.labelA) return; ctx.save(); ctx.font = '600 13px -apple-system, system-ui, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  [['A', F.labelA], ['B', F.labelB]].forEach(([t, w]) => { const q = w2s(w), on = S.fgFocus === t;            // (F1a-2: A dark on light, B light on dark; the one worked on is clear)
    ctx.globalAlpha = on ? 1 : 0.55; ctx.fillStyle = t === 'A' ? 'rgba(29,27,24,.62)' : 'rgba(255,248,240,.92)'; ctx.fillText(t, q.x, q.y);
    if (on) { ctx.fillRect(q.x - 6, q.y + 9, 12, 2); } });
  ctx.restore();
}
function drawStartShape() {
  ctx.save(); ctx.setLineDash([3, 6]); ctx.lineCap = 'round'; ctx.lineWidth = 1.6; ctx.strokeStyle = COLORS.start; ctx.globalAlpha = .85;
  ctx.beginPath(); S.origVerts.forEach((p, i) => { const q = w2s(p); i ? ctx.lineTo(q.x, q.y) : ctx.moveTo(q.x, q.y); }); ctx.closePath(); ctx.stroke(); ctx.restore();
}
function linkedEdges(e) {
  if (isMirrorId(S.consId)) return [0, 1, 2, 3].filter(i => i !== e);    // T1: in Mirror every side moves with every other (mirror twin + slides)
  if (isFGM(S.consId) && e < E.state.edges.length) { const o = orbitRels(), mr = o.find(r => r.to === e), m = mr ? mr.from : e; return [m, ...o.filter(r => r.from === m).map(r => r.to)].filter(i => i !== e); }   // (F1a-2)
  const out = new Set(); E.state.rels.forEach(r => { if (r.self !== undefined) { if (r.self === e) out.add(e); } else if (r.from === e) out.add(r.to); else if (r.to === e) out.add(r.from); }); return [...out];
}
function strokeEdge(ei, color, width, alpha) {
  const pts = sidePts(ei); ctx.save(); ctx.lineCap = 'round'; ctx.lineJoin = 'round'; ctx.strokeStyle = color; ctx.lineWidth = width; ctx.globalAlpha = alpha;
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
  edgesNow().map(e => e.pts).concat(S.fg ? [S.fg.inner] : []).forEach(ep => { const L = E.cumLen(ep), m = L[N] / 2, lo = m - r * L[N], hi = m + r * L[N], pts = [pointAtArc(ep, L, lo)];   // (F1a-1: + the inner side)
    for (let i = 1; i < N; i++) if (L[i] > lo && L[i] < hi) pts.push(ep[i]); pts.push(pointAtArc(ep, L, hi));
    ctx.beginPath(); pts.forEach((p, k) => { const q = w2s(p); k ? ctx.lineTo(q.x, q.y) : ctx.moveTo(q.x, q.y); });
    ctx.globalAlpha = 0.3 * a; ctx.lineWidth = 12; ctx.stroke(); ctx.globalAlpha = 0.95 * a; ctx.lineWidth = 3.5; ctx.stroke(); });
  ctx.restore();
}

/* ---------------- picking ---------------- */
function hitEdge(sx, sy) {
  let best = null;
  edgesNow().map(e => e.pts).concat(S.fg ? [S.fg.inner] : []).forEach((pts, ei) => { for (let i = 0; i < N; i++) {   // (F1a-1: + the inner side)
    const a = w2s(pts[i]), b = w2s(pts[i + 1]), abx = b.x - a.x, aby = b.y - a.y, l2 = abx * abx + aby * aby || 1e-9;
    const t = Math.max(0, Math.min(1, ((sx - a.x) * abx + (sy - a.y) * aby) / l2)), px = a.x + abx * t, py = a.y + aby * t, d = Math.hypot(sx - px, sy - py);
    if (d > HIT_PX || (best && d >= best.d)) continue;
    if ((i === 0 && t < 1e-6) || (i === N - 1 && t > 1 - 1e-6)) continue;
    best = { ei, i, t, d, w: s2w(px, py) }; } });
  return best;
}
// Which drawn tile contains this world point? Uses the CURRENT deformed tile (never the original polygon). `all` ignores the Neighbours: Off setting.
function tileAt(wp, all) {
  // DA: every tile that can reach the point (no tile reaches further from its centre than the base tile does), nearest first. Tiles never overlap,
  // so the answer is the same as before wherever the 8 nearest held it; a long tile's far tip is now found too.
  const c = S.cent; let reach = 0; edgesNow().forEach(e => e.pts.forEach(p => { const d = Math.hypot(p.x - c.x, p.y - c.y); if (d > reach) reach = d; }));
  const order = S.field.list.map((m, i) => ({ i, d: Math.hypot(S.centW[i].x - wp.x, S.centW[i].y - wp.y) })).filter(o => o.d <= reach + 1e-9).sort((a, b) => a.d - b.d);
  for (const { i } of order) {
    if (i > 0 && S.ghost === 'off' && !all) continue;
    const inv = minv(S.field.list[i]), lp = mapp(inv, wp);
    if (scratch.isPointInPath(S.path, lp.x, lp.y)) return { m: S.field.list[i], inv, i };
  }
  return null;
}

/* ---------------- one-finger work ---------------- */
function startWork(e, x, y) {
  if (S.mode === 'polygon' && (S.polyTool !== 'sketch' || !S.poly)) { if (S.poly) polyStart(e, x, y); else triPolyNote(); return; }   // (PH1: nothing to edit in Tri's Polygon view)      // CR3: with Sketch on, Polygon draws like Shape › Sketch
  if (S.mode === 'tessellate') { work = { type: 'pan', tap: true, id: e.pointerId, t0: performance.now(), x0: x, y0: y, lx: x, ly: y }; return; }
  if (refActive()) { work = { type: 'refmove', id: e.pointerId, t0: performance.now(), lx: x, ly: y }; return; }
  if (S.mode === 'shape' && S.shapeTool === 'pull') {
    const h = hitEdge(x, y); if (!h) return;
    E.setRadius(influenceRadius(S.influenceV));
    if (S.fg && h.ei === fgIn()) fgStartPull(h, e); else {                 // (F1a-1: the inner side is pulled by the app itself)
    const pts = edgesNow()[h.ei].pts, L = E.cumLen(pts), seg = L[h.i + 1] - L[h.i], s0 = grabArc(L, L[h.i] + seg * h.t), g = E.startGesture(h.ei, s0);
    g.start = h.w;                                   // the pull follows the finger from where it touched (unchanged)
    const c = pointAtArc(pts, L, s0);                // the boundary point the pull is centred on (= h.w unless snapped)
    S.shape = { g, before: snapshot(), hitWorld: c, c, ranges: movedRanges(g), lastReq: P(0, 0), blocked: false, gs: { frames: 0, blocked: 0, ms: [] } };
    if (S.fg) S.shape.loose = !fgOK(); S.shape.guard = S.guardShape && outlineSimple(allRanges()) && (!S.fg || fgOK(S.shape.loose));   // (F1a-1: + the figures) (a boundary that already crosses itself — impossible with the guard on — is left unguarded)
    S.hl = { edge: h.ei, linked: linkedEdges(h.ei), active: true, t1: 0 };
    work = { type: 'shape', id: e.pointerId, t0: performance.now() }; }
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
  if (S.fg) act.figure = fgFigureAt(act.seed);                              // (F1r: the fill belongs to the figure that was tapped)
  if (mirrorDrawOn()) act.mirror = mirrorAxisArr();                        // T1: mirrored drawing fills the mirror-image region too
  if (doFill(act, act.snap)) { syncView(S.layers.fills, ALL); patchComposites(ALL); pushAction(act); S.artVer++; }
}
function selectGroupAt(x, y) {                       // Tessellate: tap a tile → its GROUP under the active grouping (Same / Alternate / Row / Column)
  const t = tileAt(s2w(x, y), true);
  if (!t) { S.sel = null; closePops(); invalidate(); return; }
  const g = groupOf(t.i);
  if (S.fg) { const f = fgFigureAt(mapp(t.inv, s2w(x, y))); S.sel = { mode: S.treat, key: f + ':' + g.key, unitKey: g.key, fig: f, label: 'Figure ' + f + ' · ' + fgGroupLabel(g) }; openGroupPop(); invalidate(); return; }   // (F1a-2)
  S.sel = { mode: S.treat, key: g.key, label: g.label }; openGroupPop(); invalidate();
}
function endWork() {
  if (!work) return; const w = work; if (PERF) PERF.mark('end ' + w.type);
  if (w.type === 'draw') {
    const st = S.stroke.st; work = null; finishStroke(true);   // the final pixels are the CANONICAL ones, identical to any replay
    pushAction(st); if (st.layer === 'art') S.artVer++;
  } else if (w.type === 'shape') {
    flushShapeMove(); const sh = S.shape; if (sh.g.inner) S.fg.inner = fgResample(S.fg.inner); else E.endGesture(sh.g);   // (F1a-1: the inner side, evenly spaced on release)
    if (sh.guard) {                         // the release evens out the spacing of the moved edges; in the rare case that makes them touch, keep the shape before the pull
      const t0 = performance.now(), ok = sh.g.inner ? fgOK(sh.loose) : outlineSimple(movedRanges(sh.g, true)) && (!S.fg || fgOK(sh.loose)); sh.gs.ms.push(performance.now() - t0);
      if (!ok) { restoreSnapshot(sh.before); sh.gs.reverted = true; toast('That pull would make the edges cross', 1800); }
      logGuard(sh.gs);
    }
    rebuildPath(); rebuildCentroids();
    if (!sh.gs.reverted) { pushAction({ kind: 'shape', before: sh.before, after: snapshot() }); fgRefresh(ensureInk()); }   // (DA; F1r)
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
  else if (work.type === 'shape') { S.pendingMove = null; const g = S.shape.g, st = E.state; if (g.inner) S.fg.inner = g.base.map(p => ({ x: p.x, y: p.y })); else { st.edges[g.e].pts = g.base.map(p => ({ x: p.x, y: p.y })); E.propagate(g.e); } rebuildPath(); S.hl = null; S.shape = null; }
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
const CAGE_KIND = { translation: 'parallelogram', glide: 'parallelogram', 'glide-both': 'rectangle', 'rotation-sq-ac': 'fixed', 'rotation-sq-bd': 'fixed', 'fg-slide': 'hexagon', 'fg-mirror': 'mirror2' };   // (F1r: Two figures)
const CAGE_MIN_SIDE = 0.3, CAGE_MIN_SIN = 0.5, CAGE_SNAP = 0.02, LIVE_ID = 'cage';           // × cell; sin 30°; snap back to the exact square
const cageKind = id => CAGE_KIND[id] || 'fixed';
const cageNow = () => E.state.cons.verts;                                                   // the corners of the construction in use
const cloneCage = c => c ? c.map(p => P(p.x, p.y)) : null;
const homeCage = c => c && c.length === 6 ? FG_HOME : c && c.length === 8 ? FG_MHOME : SQUARE;                                   // (F1r: a six-cornered cage belongs to Two figures)
const isSquare = c => !c || (c.length === homeCage(c).length && c.every((p, i) => p.x === homeCage(c)[i].x && p.y === homeCage(c)[i].y));   // the cage is its construction's original (square, or the two squares)
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
  if (isFGM(id)) { const M = { type: 'mirror', p0: P(V[1].x, 0), phi: PI / 2, g: 0 }, t = (a, b) => T(V[b].x - V[a].x, V[b].y - V[a].y);     // (F1a-2)
    return [{ from: 0, to: 1, d: M, role: 'constraint' }, { from: 2, to: 7, d: M, role: 'constraint' }, { from: 0, to: 5, d: t(0, 6), role: 'glue' }, { from: 1, to: 4, d: t(1, 5), role: 'glue' },
            { from: 2, to: 6, d: t(2, 7), role: 'glue' }, { from: 7, to: 3, d: t(7, 4), role: 'glue' }]; }
  if (isFG(id)) return [{ from: 1, to: 4, d: T(V[5].x - V[1].x, V[5].y - V[1].y), role: 'glue' }, { from: 0, to: 3, d: T(V[4].x - V[0].x, V[4].y - V[0].y), role: 'glue' }, { from: 2, to: 5, d: T(V[0].x - V[2].x, V[0].y - V[2].y), role: 'glue' }];   // (F1r)
  throw new Error('corners of ' + id + ' cannot move');
}
function virtCons(id, cage) {              // relation matrices for a candidate cage, without rebuilding the engine (used to test a corner move first)
  const sq = isSquare(cage), verts = sq ? (isFG(id) ? fgHomeOf(id) : SQUARE) : cage, src = sq ? E.CONS.find(c => c.id === id).rels : cageRels(id, cage);
  if (src.some(r => r.role === 'constraint')) return { verts, rels: orbitsOf(verts, src.filter(r => r.self === undefined).map(r => { const m = E.descMatrix(r.d); return { from: r.from, to: r.to, m, inv: minv(m) }; })) };   // (F1a-2: a mirror inside the unit, as in polyRels)
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
  if (kind === 'hexagon') return fgCageProblem(V);                          // (F1r: Two figures)
  if (kind === 'mirror2') return fgMCageProblem(V);                          // (F1a-2: Mirror · Two figures)
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
  if (kind === 'hexagon') return fgCageAfterDrag(V0, k, tgt);              // (F1r: Two figures)
  if (kind === 'mirror2') return fgMCageAfterDrag(V0, k, tgt);              // (F1a-2)
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
const glueRels = () => E.state.rels.filter(r => r.role === 'glue' && r.self === undefined);       // the repeats: master = r.from, copy edge = r.to
// T1: with a mirror inside the tile (Mirror), a side's copies come from glue AND mirror links, so the points live on one master side and the
// other three sides are its copies (orbitRels); the existing rules have glue links only and are unchanged
const polyRels = () => E.state.rels.some(r => r.role === 'constraint') ? orbitRels() : glueRels();
const curK = () => ({ verts: cageNow(), rels: polyRels() });
const frameOf = (V, m) => { const en = fgEndsOf(V.length), a = m >= V.length ? V[en[0]] : V[m], b = m >= V.length ? V[en[1]] : V[(m + 1) % V.length]; return { a, dx: b.x - a.x, dy: b.y - a.y }; };   // (F1a-1: side FG_IN = the inner side, corner 1 → corner 4)
const relToWorld = (f, n) => P(f.a.x + n.s * f.dx - n.t * f.dy, f.a.y + n.s * f.dy + n.t * f.dx);
const worldToRel = (f, p, c) => { const L2 = f.dx * f.dx + f.dy * f.dy, x = p.x - f.a.x, y = p.y - f.a.y; return { s: (x * f.dx + y * f.dy) / L2, t: (y * f.dx - x * f.dy) / L2, c: !!c }; };
function worldNodes(nodes, K) { const o = {}; Object.keys(nodes).forEach(m => { const f = frameOf(K.verts, +m); o[m] = nodes[m].map(n => relToWorld(f, n)); }); return o; }
const nodeWorld = (m, k) => relToWorld(frameOf(cageNow(), m), S.poly.nodes[m][k]);
const cloneNodes = nodes => { const o = {}; Object.keys(nodes).forEach(m => { if (nodes[m].length) o[m] = nodes[m].map(p => ({ s: p.s, t: p.t, c: !!p.c })); }); return o; };
const cloneState = st => ({ consId: st.consId, family: st.family, cage: isSquare(st.cage) ? null : cloneCage(st.cage), nodes: cloneNodes(st.nodes) });
const polyCommitted = () => S.poly.hist[S.poly.hp];
const cageKey = c => isSquare(c) ? 'square' : c.map(p => p.x + ',' + p.y).join(';');
const polyKey = st => geoId(st.consId) + '|' + cageKey(st.cage) + '|' + Object.keys(st.nodes).sort().filter(m => st.nodes[m].length).map(m => m + ':' + st.nodes[m].map(p => p.s + ',' + p.t).join(';')).join('|');
const nodeCount = nodes => Object.values(nodes).reduce((n, l) => n + l.length, 0);
const sideCount = nodes => { const rels = polyRels(); let s = E.state.cons.verts.length;   // (F1a-1: the unit has 6)
   Object.keys(nodes).forEach(m => { s += nodes[m].length * (1 + rels.filter(r => r.from === +m).length); }); return s; };   // (T1: a Mirror point appears on all four sides)
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
  [...new Set(polyRels().map(r => r.from))].forEach(m => { st.edges[m].pts = sampleThrough(V[m], W[m] || [], V[(m + 1) % n]); E.propagate(m); });   // (T1: each master once)
  if (S.fg) S.fg.inner = fgInnerFrom(V, nodes[n] || []);                                                                                        // (F1a-1; F1a-2)
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
// F1a-2 · the middle side's points. Slide: points along it, in order. Mirror: points on its first half (s < ½ along corner 3 → corner 7), each shown
// with its mirror twin, plus at most one point ON the mirror line (s = ½ exactly) that moves up and down only; the side is sampled half by half.
const fgMirrorParts = (V, list) => { const f = frameOf(V, V.length), ax = list.find(q => q.s === 0.5), half = list.filter(q => q.s !== 0.5).slice().sort((a, b) => a.s - b.s);
  return { f, half: half.map(q => relToWorld(f, q)), M: relToWorld(f, { s: 0.5, t: ax ? ax.t : 0 }) }; };
function sampleThroughN(a, nodes, b, n) {  // sampleThrough with n segments instead of N
  const V = [a, ...nodes, b], lens = V.slice(1).map((q, i) => Math.hypot(q.x - V[i].x, q.y - V[i].y)), tot = lens.reduce((t, l) => t + l, 0);
  const raw = lens.map(l => n * l / tot), cnt = raw.map(r => Math.max(1, Math.floor(r)));
  let left = n - cnt.reduce((t, c) => t + c, 0); const order = raw.map((r, i) => [r - Math.floor(r), i]).sort((x, y) => y[0] - x[0] || x[1] - y[1]);
  for (let k = 0; left > 0; k = (k + 1) % order.length, left--) cnt[order[k][1]]++;
  for (let over = cnt.reduce((t, c) => t + c, 0) - n; over > 0; over--) cnt[cnt.indexOf(Math.max(...cnt))]--;
  const out = []; V.slice(1).forEach((q, i) => { const p = V[i]; for (let k = 0; k < cnt[i]; k++) out.push(k ? P(p.x + (q.x - p.x) * k / cnt[i], p.y + (q.y - p.y) * k / cnt[i]) : P(p.x, p.y)); });
  out.push(P(b.x, b.y)); return out;
}
function fgInnerFrom(V, list) {            // the middle side, sampled through its points (N + 1 samples)
  const en = fgEndsOf(V.length);
  if (V.length !== 8) { const f = frameOf(V, V.length); return sampleThrough(V[en[0]], list.map(q => relToWorld(f, q)), V[en[1]]); }
  const { half, M } = fgMirrorParts(V, list), c = M.x, first = sampleThroughN(V[en[0]], half, M, N / 2); first[N / 2] = P(c, M.y);
  return first.concat(first.slice(0, -1).reverse().map(p => P(2 * c - p.x, p.y)));
}
function fgInnerVerts(nodes, K) {          // the middle side as a polygon line (its corners and points, in order)
  const V = (K || curK()).verts, en = fgEndsOf(V.length), list = nodes[V.length] || [];
  if (V.length !== 8) { const f = frameOf(V, V.length); return [V[en[0]], ...list.map(q => relToWorld(f, q)), V[en[1]]]; }
  const { half, M } = fgMirrorParts(V, list), c = M.x; return [V[en[0]], ...half, M, ...half.slice().reverse().map(p => P(2 * c - p.x, p.y)), V[en[1]]];
}
function fgNodeHandles(nodes) {            // the middle side's handles: Slide its points; Mirror its points, their twins and the point on the mirror line
  if (!S.fg) return []; const V = cageNow(), m = V.length, list = nodes[m] || [];
  if (m !== 8) return fgInnerVerts(nodes).slice(1, -1).map((p, k) => ({ p, kind: 'node', e: m, m, k, rel: null, placed: true }));
  const f = frameOf(V, m), c = relToWorld(f, { s: 0.5, t: 0 }).x, R = fgMirrorM(c), rel = { m: R, inv: R }, out = [];
  list.forEach((q, k) => { const p = relToWorld(f, q); if (q.s === 0.5) { out.push({ p, kind: 'node', e: m, m, k, rel: null, placed: true, axis: true }); return; }
    out.push({ p, kind: 'node', e: m, m, k, rel: null, placed: !q.c }, { p: mapp(R, p), kind: 'copy', e: m, m, k, rel, placed: !!q.c }); });
  if (!list.some(q => q.s === 0.5)) out.push({ p: relToWorld(f, { s: 0.5, t: 0 }), kind: 'node', e: m, m, k: -1, rel: null, placed: true, axis: true });   // (the straight middle: a handle to start from)
  return out;
}
function polyProblem(nodes, K) {           // '' when the polygon is a valid tile; otherwise why not
  const all = polyVerts(nodes, K), why = polyCheck(all.map(v => v.p)); if (why || !S.fg) return why;
  // F1a-1: two figures. A and B must each be a valid polygon too (inner points included), and neither may collapse.
  const en = fgEndsOf((K || curK()).verts.length), vs = all.map(v => v.p), i1 = all.findIndex(v => v.kind === 'corner' && v.e === en[0]), i4 = all.findIndex(v => v.kind === 'corner' && v.e === en[1]), mid = fgInnerVerts(nodes, K).slice(1, -1);
  const A = vs.slice(0, i1 + 1).concat(mid, vs.slice(i4)), B = vs.slice(i1, i4 + 1).concat(mid.slice().reverse());
  const wa = polyCheck(A) || polyCheck(B); if (wa) return wa;
  const ar = q => { let a2 = 0; q.forEach((p, i) => { const r = q[(i + 1) % q.length]; a2 += p.x * r.y - r.x * p.y; }); return a2 / 2; }, a = ar(A), b = ar(B);
  return a < FG_MIN_SHARE * (a + b) || b < FG_MIN_SHARE * (a + b) ? 'small' : '';
}
function polyCheck(vs) {                   // the checks for one closed polygon (the tile; with two figures also each figure)
  const n = vs.length, z = S.unit, I = S.ink, mg = 0.02 * I.side;
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
      `<p>${art ? 'Your sketch and artwork stay exactly as they are.' : 'Nothing else changes.'}</p><p class="mute">The current version is kept: ☰ menu › Restore previous version brings it back.</p>`,
    yes: 'Change polygon', no: 'Keep Shape changes' }, () => { S.restartOK = true; then && then(); });
}
function captureVersion() {                 // a complete, restorable version: polygon (corners + nodes) + its undo list, Shape boundary + the whole history
  const c = polyCommitted(), key = polyKey(c), handed = S.shapeBaseKey === key;
  let edges, initialSnap = S.initialSnap, baseKey = S.shapeBaseKey;
  if (S.mode === 'polygon') { if (handed && S.refined) edges = S.refined; else { edges = polySnapshot(c); initialSnap = edges; baseKey = key; } }
  else edges = snapshot();
  return { poly: { hist: S.poly.hist.slice(), hp: S.poly.hp }, history: S.history.slice(), hp: S.hp, initialSnap, edges, baseKey,
    shapeEdits: shapeEditsApplied(), sides: sideCount(c.nodes), moved: !isSquare(c.cage), consId: c.consId, drawn: drawnSteps() };   // (F1a-2: + construction, drawing)
}
function polySnapshot(st) {                 // the engine edges of a polygon state, leaving the current construction and edges as they were
  const keep = { id: S.consId, cage: cloneCage(S.cageNow), edges: snapshot() }; S.fgQuiet = true;
  try {
    if (st.consId !== S.consId || !sameCage(st.cage, S.cageNow)) setCage(st.consId, st.cage);
    writePolygonEdges(st.nodes); const out = snapshot();
    if (keep.id !== S.consId || !sameCage(keep.cage, S.cageNow)) setCage(keep.id, keep.cage);
    setSnapEdges(keep.edges); rebuildPath(); rebuildCentroids(); return out;           // (F1a-1: + the inner side)
  } finally { S.fgQuiet = false; }
}
function restartShape() {                   // the polygon changes under Shape refinements: keep the whole version, then start Shape again from the new polygon
  S.recovery = captureVersion(); S.consLink = null;                          // (F1a-2: the kept version is now this one)
  const before = S.history.slice(0, S.hp).filter(a => a.kind !== 'shape'), after = S.history.slice(S.hp).filter(a => a.kind !== 'shape');
  S.history = before.concat(after); S.hp = before.length; S.shapeBaseKey = null; S.refined = null; syncUndo(); syncRestoreUI();
}
function beforePolyChange(next) {           // called with the state about to be committed
  if (S.shapeBaseKey && polyKey(next) !== S.shapeBaseKey && S.history.some(a => a.kind === 'shape')) restartShape();
}
function polyCommit(next) {
  if (S.consLink === 'redo') S.consLink = null;                              // (F1a-2: an edit on the restored version ends the way forward; the menu still swaps)
  beforePolyChange(next); const P2 = S.poly; P2.hist = P2.hist.slice(0, P2.hp + 1); P2.hist.push(cloneState(next)); P2.hp = P2.hist.length - 1; applyPolyState(next);
}
function polyHistory(d) {
  const P2 = S.poly, to = P2.hp + d; if (!P2 || to < 0 || to >= P2.hist.length) return;
  if (work) cancelWork();
  const go = () => { beforePolyChange(P2.hist[to]); P2.hp = to; applyPolyState(P2.hist[to]); };
  if (polyKey(P2.hist[to]) === polyKey(polyCommitted())) go(); else gated(go);      // (T2: Undo of an arrangement change keeps Shape as it is)
}
/* F1a-2 · A NEW CONSTRUCTION STARTS WITH A CLEAR TILE. Changing the rule (Slide · Turn · Flip · Mirror, Turn's corners, Flip's one way / both ways),
 * One ↔ Two figures, or Slide ↔ Mirror in Two figures begins a NEW construction. When the tile has a drawing (strokes, fills, dots, textures or
 * sketch), one question first; then the whole current version (polygon, Shape steps and drawing) becomes the previous version and the new
 * construction starts with no drawing. Polygon ↶ right after it swaps back, and ↷ returns: S.consLink says which button brings the kept version
 * back ('undo' or 'redo'; null when the kept version is not the other side of a new construction). Refining — points, corners, Shape pulls,
 * Mirror's Same ↔ Alternating, Working on A | B — keeps the drawing, as before. */
const drawnSteps = () => S.history.slice(0, S.hp).filter(a => a.kind === 'stroke' || a.kind === 'fill').length;
const consLabel = id => CARD[id] ? CARD[id].short.replace(/^(Quad|Tri) · /, '') : String(id);
const consBack = d => S.consLink === d && !!S.recovery && !!S.poly;
function askNewConstruction(id, then) {
  ask({ title: 'Start a new construction?',
    html: `<p><b>${consLabel(id)}</b> is a new construction. Your drawing (strokes, fills, dots, textures and sketch) belongs to this tile and will be cleared.</p>` +
      `<p class="mute">The current tile and its drawing are kept: <b>↶</b> brings them back, or ☰ menu › Restore previous version.</p>`,
    yes: 'Start new construction', no: 'Cancel' }, then);
}
function newConstruction(next, cur) {
  const cleared = drawnSteps(); S.recovery = captureVersion(); S.consLink = 'undo';
  S.history = []; S.hp = 0; S.shapeBaseKey = null; S.refined = null; S.restartOK = false;
  const st = cloneState(next); st.seq = ++S.seq; S.poly.hist = [st]; S.poly.hp = 0;
  applyPolyState(st); S.initialSnap = snapshot(); if (!ensureInk()) rebuildLayers();
  syncUndo(); syncRestoreUI(); syncPolyButtons(); updateTitle(); invalidate(); markDirty();
  journal('newConstruction', { from: cur.consId, to: next.consId, cleared });
  toast(consLabel(next.consId) + ' · a clear tile · ↶ brings back the previous one with its drawing', 3600);
}
function choosePolyCons(id) {               // Translate / Rotate / Glide and their secondary choices (a new transformation starts again from the square)
  const cur = polyCommitted(); if (cur.family && cur.consId === id) return;
  if (cur.family && isMirrorId(cur.consId) && isMirrorId(id)) {        // T2: Same ↔ Alternating changes only how neighbours are placed
    if (work) cancelWork(); polyCommit({ consId: id, family: 'mirror', cage: null, nodes: cloneNodes(cur.nodes) }); arrangementNote(id); return; }
  const next = { consId: id, family: POLY_FAMILY_OF[id], cage: null, nodes: cur.family ? {} : cur.nodes }, had = (nodeCount(cur.nodes) > 0 || !isSquare(cur.cage)) && cur.family;
  if (work) cancelWork();
  const cornersHint = () => { if (cageKind(id) !== 'fixed' && !S.seenHint.corners) { S.seenHint.corners = true; toast('You can also drag a corner: the cell reshapes and its neighbours follow', 3400); return true; } return false; };
  if (!cur.family) { S.poly.hist[S.poly.hp] = cloneState(next); applyPolyState(next); if (!cornersHint() && !S.seenHint.polygon) { S.seenHint.polygon = true; toast(HINTS.polygon, 3600); } return; }
  if (drawnSteps()) { askNewConstruction(id, () => newConstruction(next, cur)); return; }   // (F1a-2: a drawing → the question, a clear tile, the version kept)
  gated(() => { polyCommit(next); if (S.hp < S.history.length) { S.history.length = S.hp; syncUndo(); }   // (F1a-2: undone drawing does not come back on a new construction)
    if (fgNote(id, cur.consId, had)) return; if (had) toast('New rule: the polygon starts again · Undo brings it back', 3200); else cornersHint(); });   // (F1a-1: fgNote)
}
function polyHit(x, y) {                    // screen point → a node handle, a corner, or a point on a side
  const vs = polyVerts(S.poly.nodes); let best = null;
  vs.concat(fgNodeHandles(S.poly.nodes)).forEach(v => { if (v.kind === 'corner') return; const q = w2s(v.p), d = Math.hypot(q.x - x, q.y - y); if (d <= NODE_PX && (!best || d < best.d)) best = { type: 'node', v, d }; });   // (F1a-1: + inner points)
  if (best) return best;
  const cpx = cageKind(S.consId) === 'fixed' ? CORNER_PX : NODE_PX;
  vs.forEach(v => { if (v.kind !== 'corner') return; const q = w2s(v.p), d = Math.hypot(q.x - x, q.y - y); if (d <= cpx && (!best || d < best.d)) best = { type: 'corner', v, d }; });
  if (best) return best;
  const n = vs.length;
  for (let i = 0; i < n; i++) { const a = w2s(vs[i].p), b = w2s(vs[(i + 1) % n].p), dx = b.x - a.x, dy = b.y - a.y, l2 = dx * dx + dy * dy || 1e-9;
    const t = Math.max(0, Math.min(1, ((x - a.x) * dx + (y - a.y) * dy) / l2)), d = Math.hypot(x - a.x - dx * t, y - a.y - dy * t);
    if (d <= PSIDE_PX && (!best || d < best.d)) best = { type: 'side', i, t, d, vs }; }
  if (S.fg) { const iv = fgInnerVerts(S.poly.nodes);                              // (F1a-1: the inner side)
    for (let i = 0; i < iv.length - 1; i++) { const a = w2s(iv[i]), b = w2s(iv[i + 1]), dx = b.x - a.x, dy = b.y - a.y, l2 = dx * dx + dy * dy || 1e-9;
      const t = Math.max(0, Math.min(1, ((x - a.x) * dx + (y - a.y) * dy) / l2)), d = Math.hypot(x - a.x - dx * t, y - a.y - dy * t);
      if (d <= PSIDE_PX && (!best || d < best.d)) best = { type: 'side', i, t, d, vs, inner: iv }; } }
  return best;
}
function polyInsertAt(h) {                  // a new node on the touched side (on the straight line, so nothing moves until it is dragged)
  if (h.inner) {                            // (F1a-1: a point on the inner side; it has no copy. F1a-2 Mirror: a point and its mirror twin)
    const iv = h.inner, a = iv[h.i], b = iv[h.i + 1], len = Math.hypot(b.x - a.x, b.y - a.y), z = S.unit, nodes = S.poly.nodes, V = cageNow(), m = V.length;
    if (len < 2.2 * POLY_MIN_SEG * z) { toast('This side is too short for another point', 1800); return null; }
    const m0 = POLY_MIN_SEG * z * 1.05 / len, w = lerpP(a, b, Math.min(1 - m0, Math.max(m0, h.t))), f = frameOf(V, m);
    if (m !== 8) { (nodes[m] = nodes[m] || []).splice(h.i, 0, worldToRel(f, w, false));
      if (polyProblem(nodes)) { nodes[m].splice(h.i, 1); if (!nodes[m].length) delete nodes[m]; toast('No room for a point here', 1500); return null; }
      writePolygonEdges(nodes); return { m, k: h.i, copy: null, handle: w }; }
    let r = worldToRel(f, w, false), copy = null; const c = relToWorld(f, { s: 0.5, t: 0 }).x, R = fgMirrorM(c), ms = POLY_MIN_SEG * z / Math.hypot(f.dx, f.dy);
    if (r.s > 0.5) { r = worldToRel(f, mapp(R, w), true); copy = { m: R, inv: R }; }                        // tapped on the second half: the point is stored on the first, as the twin
    if (r.s > 0.5 - ms) { toast('Use the point on the mirror line here', 1600); return null; }
    const list = (nodes[m] = nodes[m] || []); list.push(r); list.sort((x, y) => (x.s === 0.5) - (y.s === 0.5) || x.s - y.s); const k = list.indexOf(r);
    if (polyProblem(nodes)) { list.splice(k, 1); if (!list.length) delete nodes[m]; toast('No room for a point here', 1500); return null; }
    writePolygonEdges(nodes); return { m, k, copy, handle: w };
  }
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
  if (!S.poly.family) { toast('First choose a construction method', 2000); return; }
  const h = polyHit(x, y); if (S.poly.sel) { S.poly.sel = null; }
  if (!h) { invalidate(); return; }
  const w = s2w(x, y), base = { id: e.pointerId, t0: performance.now(), x0: x, y0: y, lx: x, ly: y, moved: false, blocked: false };
  if (h.type === 'corner') {
    if (cageKind(S.consId) === 'fixed') { S.lockFlash = { k: h.v.e, t: performance.now() }; toast(isMirrorId(S.consId) ? 'Reflection keeps the square on its corner: its corners stay fixed · add points on the sides' : 'Rotate needs the square: its corners stay fixed · add points on the sides', 2800); invalidate(); return; }
    work = Object.assign(base, { type: 'pcorner', k: h.v.e, V0: cloneCage(cageNow()), off: P(h.v.p.x - w.x, h.v.p.y - w.y), gate: needsConfirm() });
    if (S.fg && isFGM(S.consId) && !S.seenHint.fgmCorners) { S.seenHint.fgmCorners = true; toast(h.v.e === 1 || h.v.e === 5 ? 'On the mirror line: up and down only' : 'Twin corners move mirrored · up and down makes A and B taller together', 3200); }   // (F1a-2)
    else if (S.fg && !isFGM(S.consId) && !S.seenHint.fgCorners) { S.seenHint.fgCorners = true; toast(h.v.e === 1 || h.v.e === 4 ? 'Where A meets B: the opposite corner moves with it, mirrored' : 'A corner slides its side · the opposite side slides back', 3000); }   // (F1r)
  } else if (h.type === 'node') {
    const v = h.v; let k = v.k, inserted = false;
    if (v.axis && k < 0) { if (needsConfirm()) { askRestart(() => toast('Now change your polygon', 1600)); return; }     // (F1a-2) the mirror-line point of a straight middle side: made on first touch
      const list = (S.poly.nodes[v.m] = S.poly.nodes[v.m] || []); list.push({ s: 0.5, t: 0, c: false }); k = list.length - 1; inserted = true; }
    work = Object.assign(base, { type: 'pnode', m: v.m, k, copy: v.kind === 'copy' ? v.rel : null, off: P(v.p.x - w.x, v.p.y - w.y), inserted, axisNew: inserted, gate: inserted ? false : needsConfirm() });
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
  const want = work.copy ? mapp(work.copy.inv, tgt) : tgt, f = frameOf(cageNow(), work.m), fm = S.fg && work.m === 8 && cageNow().length === 8;   // (F1a-2: Mirror's middle side)
  const ms = fm ? POLY_MIN_SEG * S.unit / Math.hypot(f.dx, f.dy) : 0;
  const list = S.poly.nodes[work.m], curRel = list[work.k], cur = relToWorld(f, curRel), set = q => { const r = worldToRel(f, q, curRel.c);
    if (fm && curRel.s === 0.5) { r.s = 0.5; r.c = false; } else if (fm) r.s = Math.min(0.5 - ms, r.s);      // the mirror-line point moves up and down only; a half's point stays on its half
    list[work.k] = r; };
  set(want);
  if (!polyProblem(S.poly.nodes)) work.blocked = false;
  else { let lo = 0, hi = 1; for (let i = 0; i < 10; i++) { const m = (lo + hi) / 2; set(lerpP(cur, want, m)); polyProblem(S.poly.nodes) ? hi = m : lo = m; }
    set(lerpP(cur, want, lo)); if (!work.blocked && !S.seenHint.polyBlock) { S.seenHint.polyBlock = true; toast('Sides can’t cross or touch', 1600); } work.blocked = true; }
  if (list[work.k].s !== curRel.s || list[work.k].t !== curRel.t) { work.moved = true; writePolygonEdges(S.poly.nodes); }
}
function flushCornerMove(tgt) {             // the cage follows the corner rule; the relations and the neighbour placements are rebuilt from it
  const id = S.consId, cur = cloneCage(cageNow()); let want = cageAfterDrag(id, work.V0, work.k, tgt); if (!want) return;
  const home = isFG(id) ? fgHomeOf(id) : SQUARE;                             // (F1r: the two squares for Two figures)
  if (want.every((q, i) => Math.hypot(q.x - home[i].x, q.y - home[i].y) < CAGE_SNAP * S.unit)) want = cloneCage(home);   // back to the exact square
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
  if (w.axisNew && !w.moved) { const l = S.poly.nodes[w.m]; l.splice(w.k, 1); if (!l.length) delete S.poly.nodes[w.m]; writePolygonEdges(S.poly.nodes); invalidate(); return; }   // (F1a-2)
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
  const v = polyVerts(S.poly.nodes).concat(fgNodeHandles(S.poly.nodes)).find(v => v.m === sel.m && v.k === sel.k && (v.kind === 'copy') === sel.copy); if (!v) { b.hidden = true; return; }   // (F1a-1: + inner points; F1r: the check after it had been swallowed by this comment)
  const q = w2s(v.p); b.style.left = Math.round(Math.min(S.vw - 70, Math.max(70, q.x))) + 'px'; b.style.top = Math.round(Math.max(110, q.y - 16)) + 'px';
}
function cornerLinks(k) {                   // which corners move with corner k, and which sides change together (for the feedback)
  const kind = cageKind(S.consId);
  if (kind === 'parallelogram') { const j = (k + 1) % 4; return { kind, linked: [j], pair: [(k + 3) % 4, j] }; }   // the two sides that stay parallel and equal while k–j slides
  if (kind === 'rectangle') return { kind, linked: [(k + 1) % 4, (k + 3) % 4], pair: [] };
  if (kind === 'mirror2') return { kind, linked: { 0: [2, 4, 6], 2: [0, 4, 6], 4: [6, 0, 2], 6: [4, 0, 2], 3: [7], 7: [3], 1: [5], 5: [1] }[k] || [], pair: [] };   // (F1a-2) twins and copies
  if (kind === 'hexagon') return k === 1 || k === 4 ? { kind, linked: [(k + 3) % 6], pair: [] }          // (F1r) an end of the middle side: its opposite corner, mirrored
    : { kind, linked: [(k + 1) % 6, (k + 3) % 6, (k + 4) % 6], pair: [k, (k + 3) % 6] };                   //       an outer corner: its side and the opposite side slide
  return { kind, linked: [], pair: [] };
}
const axisCorner = e => cageKind(S.consId) === 'mirror2' && (e === 1 || e === 5);   // (F1a-2) the two corners on the mirror line
function drawPolygonOverlay() {
  if (!S.poly) return; const vs = polyVerts(S.poly.nodes), drag = work && work.type === 'pnode' ? work : null, cw = work && work.type === 'pcorner' ? work : null, V = cageNow();
  const dash = (A, B) => { ctx.save(); ctx.setLineDash([4, 5]); ctx.strokeStyle = 'rgba(255,255,255,.75)'; ctx.lineWidth = 1.2; ctx.beginPath(); ctx.moveTo(A.x, A.y); ctx.lineTo(B.x, B.y); ctx.stroke(); ctx.restore(); };
  if (drag) {                               // the side being changed, its paired side, and the link between the point and its copy
    const rs = polyRels().filter(r => r.from === drag.m), nd = nodeWorld(drag.m, drag.k);       // (T1: every copy; Mirror has three)
    strokeEdge(drag.m, COLORS.edgeA, 5, 0.85); rs.forEach(r => { strokeEdge(r.to, COLORS.edgeB, 5, 0.85); dash(w2s(nd), w2s(mapp(r.m, nd))); });
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
  vs.concat(fgNodeHandles(S.poly.nodes)).forEach(v => { const q = w2s(v.p);           // (F1a-1: + inner points)
    if (v.kind === 'corner') {              // CORNERS are squares (nodes are circles): draggable ones larger; Rotation's fixed ones small
      const on = cw && cw.k === v.e, lk = links && links.linked.includes(v.e), h = fixed ? 4 : on ? 7.5 : 6;
      if (lk) { ctx.beginPath(); ctx.arc(q.x, q.y, 11, 0, TAU); ctx.strokeStyle = COLORS.edgeB; ctx.lineWidth = 2.5; ctx.stroke(); }
      if (lf && lf.k === v.e) { ctx.beginPath(); ctx.arc(q.x, q.y, 12, 0, TAU); ctx.strokeStyle = '#ff7b7b'; ctx.lineWidth = 2.5; ctx.globalAlpha = 1 - (performance.now() - lf.t) / 900; ctx.stroke(); ctx.globalAlpha = 1; }
      ctx.fillStyle = '#1d1b18'; ctx.strokeStyle = on ? (cw.blocked ? '#ff7b7b' : COLORS.edgeA) : 'rgba(255,255,255,.9)'; ctx.lineWidth = on ? 3 : fixed ? 1.5 : 2;
      ctx.beginPath(); if (axisCorner(v.e)) { const d = h * 1.35; ctx.moveTo(q.x, q.y - d); ctx.lineTo(q.x + d, q.y); ctx.lineTo(q.x, q.y + d); ctx.lineTo(q.x - d, q.y); ctx.closePath(); } else ctx.rect(q.x - h, q.y - h, 2 * h, 2 * h);   // (F1a-2: on the mirror line, a diamond)
      ctx.fill(); ctx.stroke(); return; }
    if (v.axis) { const on = drag && drag.m === v.m && drag.k === v.k, sel = S.poly.sel && S.poly.sel.m === v.m && S.poly.sel.k === v.k, d = on || sel ? 10 : 8.5;   // (F1a-2) the middle side's point on the mirror line
      if (sel) { ctx.beginPath(); ctx.arc(q.x, q.y, d + 5, 0, TAU); ctx.strokeStyle = 'rgba(255,255,255,.9)'; ctx.lineWidth = 2; ctx.stroke(); }
      ctx.beginPath(); ctx.moveTo(q.x, q.y - d); ctx.lineTo(q.x + d, q.y); ctx.lineTo(q.x, q.y + d); ctx.lineTo(q.x - d, q.y); ctx.closePath();
      if (v.k < 0) { ctx.fillStyle = 'rgba(29,27,24,.55)'; ctx.fill(); ctx.setLineDash([3, 3]); ctx.strokeStyle = '#e58bb0'; ctx.lineWidth = 2; ctx.stroke(); ctx.setLineDash([]); }
      else { ctx.fillStyle = COLORS.start; ctx.fill(); ctx.strokeStyle = on && drag.blocked ? '#ff7b7b' : '#fff'; ctx.lineWidth = on && drag.blocked ? 3 : 2; ctx.stroke(); }
      return; }
    const on = drag && drag.m === v.m && drag.k === v.k, sel = S.poly.sel && S.poly.sel.m === v.m && S.poly.sel.k === v.k, r = on || sel ? 8.5 : 7;
    if (sel) { ctx.beginPath(); ctx.arc(q.x, q.y, r + 6, 0, TAU); ctx.strokeStyle = 'rgba(255,255,255,.9)'; ctx.lineWidth = 2; ctx.stroke(); }
    ctx.beginPath(); ctx.arc(q.x, q.y, r, 0, TAU);
    if (v.placed) { ctx.fillStyle = COLORS.start; ctx.fill(); ctx.strokeStyle = on && drag.blocked ? '#ff7b7b' : '#fff'; ctx.lineWidth = on && drag.blocked ? 3 : 2; ctx.stroke(); }
    else { ctx.fillStyle = '#fff'; ctx.fill(); ctx.strokeStyle = on && drag.blocked ? '#ff7b7b' : COLORS.start; ctx.lineWidth = 3; ctx.stroke(); }
  });
  ctx.restore();
}
function enterPolygon() {                   // put the Shape boundary aside and show the polygon it was built on
  if (!S.poly) return;                       // (PH1: Tri's Polygon view shows the tile as it is: nothing is set aside or saved differently)
  S.refined = snapshot(); S.restartOK = false; S.hl = null; S.shape = null; S.poly.sel = null; S.poly.nodes = cloneNodes(polyCommitted().nodes); writePolygonEdges(S.poly.nodes); fgRefresh(false);   // (F1r)
}
function leavePolygon() {                   // HANDOFF: unchanged polygon → the Shape boundary returns; changed (or first time) → Shape starts from exactly this polygon
  if (!S.poly) return;                       // (PH1)
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
  const link = S.consLink; if (link) S.consLink = link === 'undo' ? 'redo' : 'undo';            // (F1a-2: ↶ and ↷ swap the two constructions)
  if (!ensureInk()) rebuildLayers(); S.recovery = cur;                                            // (F1a-2: the drawing area of the version restored, from ITS tile — as reopening it would give) S.restartOK = false; syncUndo(); syncPolyUI(); syncRestoreUI(); updateTitle(); invalidate();
  toast(link === 'undo' ? 'The previous construction is back, with its drawing · ↷ returns to the new one' : link === 'redo' ? 'The new construction again · ↶ goes back to the previous one' : 'Previous version restored · the menu can swap back', 2800);
}
function syncPolyUI() {
  $('mode-polygon').setAttribute('aria-disabled', String(!S.poly && !triView())); if (!S.poly) return;   // (PH1)
  const st = S.poly, fam = st.family, sides = sideCount(st.nodes), movable = cageKind(S.consId) !== 'fixed';
  ['translate', 'rotate', 'glide', 'mirror'].forEach(f => $('pf-' + f).setAttribute('aria-pressed', String(f === fam)));   // (T1: + Mirror)
  const twoM = isFGM(st.consId) || (fam === 'mirror' && isFG(S.consId));                   // (F1a-2: Same | Alternating belong to one figure; hidden with Two figures)
  $('pb-sec-rotate').hidden = fam !== 'rotate'; $('pb-sec-glide').hidden = fam !== 'glide'; $('pb-sec-mirror').hidden = fam !== 'mirror' || twoM; $('pb-hint').hidden = fam === 'rotate' || fam === 'glide' || (fam === 'mirror' && !twoM);   // (T2: + Mirror's arrangements)
  document.querySelectorAll('#pb-sec-rotate button, #pb-sec-glide button, #pb-sec-mirror button').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.id === S.consId)));
  $('pb-hint').textContent = !fam ? 'Choose how the tiles repeat' : twoM ? (nodeCount(st.nodes) ? 'Drag points or corners' : 'Tap a side · drag a corner')   // (F1a-2)
    : fam === 'mirror' ? (nodeCount(st.nodes) ? 'Drag a point: its twin mirrors it' : 'Tap a side: its mirror twin follows')   // (T1)
    : nodeCount(st.nodes) ? (movable ? 'Drag points or corners' : 'Drag points · tap to remove') : (movable ? 'Tap a side · drag a corner' : 'Tap a side to add a point');   // (CR3: shorter, so they fit beside Sketch)
  const pts = nodeCount(st.nodes), sk = S.polyTool === 'sketch'; void sides;               // CR3: no permanent counter, a quiet one from 30 points
  $('pb-count').hidden = pts < POLY_CUE_FROM; $('pb-count').innerHTML = `<b>${pts}<small>/${POLY_MAX_POINTS}</small></b><span>points</span>`; $('pb-count').classList.toggle('full', pts >= POLY_MAX_POINTS);
  $('pb-sketch').setAttribute('aria-pressed', String(sk)); $('pb-sketch').disabled = !fam;
  if (sk) { $('pb-hint').hidden = true; $('pb-sec-rotate').hidden = true; $('pb-sec-glide').hidden = true; $('pb-sec-mirror').hidden = true; }
  $('pb-next').disabled = !fam;
  syncPolyButtons(); syncFgUI();
}
function syncRestoreUI() { const v = S.recovery; $('m-restore').hidden = !v; if (v) $('m-restore-sub').textContent = (v.consId && v.consId !== S.consId ? consLabel(v.consId) + ' · ' : '') + (v.drawn ? 'with its drawing · ' : '') + v.sides + ' sides' + (v.moved ? ' · corners moved' : '') + (v.shapeEdits ? ' · ' + v.shapeEdits + (v.shapeEdits === 1 ? ' Shape change' : ' Shape changes') : ''); }
let askCb = null;
function ask(o, onYes) { $('ask-title').textContent = o.title; $('ask-text').innerHTML = o.html; $('ask-yes').textContent = o.yes; $('ask-no').textContent = o.no; $('ask-no').hidden = !o.no; $('ask').hidden = false; askCb = onYes; }
$('ask-yes').onclick = () => { $('ask').hidden = true; const f = askCb; askCb = null; if (f) f(); };
$('ask-no').onclick = () => { $('ask').hidden = true; askCb = null; };
$('node-remove').onclick = () => removeSelectedNode();
['translate', 'rotate', 'glide', 'mirror', 'fg'].forEach(f => $('pf-' + f).onclick = () => chooseMethod(f));   // (PH1: five methods; Figure & Ground has its own Translate | Reflection)
document.querySelectorAll('#pb-sec-rotate button, #pb-sec-glide button, #pb-sec-mirror button, #pb-sec-fg button').forEach(b => b.onclick = () => choosePolyCons(b.dataset.id));
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
  if (m === 'polygon' && !S.poly && !triView()) { toast('Polygon is not available for this shape · ☰ › New', 2400); return; }   // (PH1: Tri's Polygon is a view)
  if (S.mode === 'polygon' && m !== 'polygon' && S.poly && !S.poly.family) { toast('First choose a construction method', 2000); return; }
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
  if (!S.sel) return; const p = groupProps(false) || {}, fig = S.sel.fig || null, uk = S.sel.unitKey || S.sel.key, n = S.field.list.filter((m, i) => groupOf(i).key === uk).length;
  $('grp-title').textContent = S.sel.label + ' · ' + n + (fig ? '' : n === 1 ? ' tile' : ' tiles');
  $('grp-bg').lastChild.textContent = fig ? 'Colour' : 'Tile colour'; $('grp-fig').lastChild.textContent = fig ? 'Fill colour' : 'Figure colour';   // (F1a-2: a figure's own colour and its fills)
  $('grp-bg').firstElementChild.style.background = p.bg || (fig ? FG_COL[fig] : COLORS.fill); $('grp-fig').firstElementChild.style.background = p.fig || 'conic-gradient(#d94b3d,#f2c230,#6aa84f,#3b6fb6,#7a4fa3,#d94b3d)';
  $('grp-op').value = p.alpha == null ? 1 : p.alpha; $('grp-sc').value = p.scale == null ? 1 : p.scale; $('grp-hide').setAttribute('aria-pressed', String(!!p.hidden)); $('grp-hide').textContent = p.hidden ? 'Show' : 'Hide';
}
let grpTarget = null;
function openGroupPop() { closeMenu(); closePalette(); $('grp').hidden = false; $('grp-swatches').hidden = true; grpTarget = null; syncGrpUI(); }
function closeGrp() { if (!$('grp').hidden) $('grp').hidden = true; }
function pickGroupColour(target) {
  grpTarget = target; const box = $('grp-swatches'); box.hidden = false;
  swatchButtons(box, c => { setGroupProp(grpTarget, c); box.hidden = true; }, { label: target === 'bg' ? (S.sel && S.sel.fig ? 'Figure ' + S.sel.fig + ' default' : 'Default tile') : (S.sel && S.sel.fig ? 'Fills as drawn' : 'Original figure') });
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
  square:   { name: 'Quad', polygon: true, hint: 'Translate, Rotate, Glide reflection, Reflection or Figure & Ground · add points (up to 40)',
    groups: [ { title: 'Translate', ids: ['translation'] }, { title: 'Rotate', ids: ['rotation-sq-ac', 'rotation-sq-bd'] }, { title: 'Glide reflection', ids: ['glide', 'glide-both'] }, { title: 'Reflection', ids: ['mirror'] } ] },
  triangle: { name: 'Tri', hint: 'Triangle · starts equilateral',
    groups: [ { title: 'Rotate', ids: ['rotation-tri'] } ] },
  rhombus:  { name: 'Rhombus', experimental: true, hint: 'A diamond with a mirror line',
    groups: [ { title: 'Reflection', experimental: true, ids: ['reflection'] } ] }
};
const CARD = {
  translation:      { short: 'Quad · Translate', title: 'Translate', sub: 'Opposite sides are the same shape, translated (slid) across.' },
  'rotation-sq-ac': { short: 'Quad · Rotate (↗ corners)', title: 'Rotate about ↗ corners', sub: 'Neighbouring sides rotate onto each other about the bottom-left and top-right corners.' },
  'rotation-sq-bd': { short: 'Quad · Rotate (↖ corners)', title: 'Rotate about ↖ corners', sub: 'The same idea about the other two corners.' },
  'rotation-tri':   { short: 'Tri · Rotate', title: 'Rotate', sub: 'Two sides rotate about a corner; the third rotates about its middle.' },
  glide:            { short: 'Quad · Glide reflection (one pair)', title: 'Glide reflection · one pair', sub: 'Top and bottom are reflected and slid; the sides are translated.' },
  'glide-both':     { short: 'Quad · Glide reflection (both pairs)', title: 'Glide reflection · both pairs', sub: 'Both pairs of sides are reflected and slid.' },
  'fg-slide':       { short: 'Quad · Figure & Ground · Translate', title: 'Figure & Ground · Translate', sub: 'Figure A and Figure B share every boundary.' },   // (F1a-1)
  'fg-mirror':      { short: 'Quad · Figure & Ground · Reflection', title: 'Figure & Ground · Reflection', sub: 'Figure A and Figure B are each symmetric about the dashed line, and share every boundary.' },   // (F1a-2)
  'mirror-flip':    { short: 'Quad · Reflection · Mirrored', title: 'Reflection · Mirrored', sub: 'The same symmetric tile; each neighbour across a side is its mirror image, slid along.' },   // (T2)
  mirror:           { short: 'Quad · Reflection · Same', title: 'Reflection · Same', sub: 'The square stands on its corner and is symmetric about the vertical line; neighbours are translated.' },   // (T1)
  reflection:       { short: 'Rhombus · mirror diamond (experimental)', title: 'Mirror diamond (experimental)', sub: 'The diamond is symmetric about its long diagonal, then repeated by sliding. It does not make mirrored neighbours.' }
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
const TP = window.TessProject, SAMPLES = N + 1, BUILD = 'v5.11-ph2';
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
const STROKE_KEYS = ['layer', 'tool', 'pattern', 'angle', 'seed', 'color', 'alpha', 'w', 'stage', 'seq', 'mirror'];   // (CR3: stage, seq; T1: mirror = [x, y, angle] of the axis)
function stepEntry(a) {
  let e = encCache.get(a); if (e) return e;
  if (a.kind === 'stroke') { const o = { kind: 'stroke' }; STROKE_KEYS.forEach(k => { if (a[k] !== undefined) o[k] = a[k]; }); o.pts = ptsF64(a.pts); e = { o, snaps: [] }; }
  else if (a.kind === 'fill') e = { o: Object.assign({ kind: 'fill', color: a.color, alpha: a.alpha, seed: { x: a.seed.x, y: a.seed.y }, respectSketch: !!a.respectSketch }, a.edge ? { edge: 1 } : {}, a.mirror ? { mirror: a.mirror.slice() } : {}, a.figure ? { figure: a.figure } : {}), snaps: a.snap ? [['snap', a.snap]] : [] };   // (T1: mirror; F1r: figure)
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
      unit: S.fg ? (() => { const n = fgIn(), [e1, e2] = fgEnds(), r = (a, b) => Array.from({ length: b - a }, (_, i) => a + i); return { tiles: 2, sharedSides: [n], figures: { A: [...r(0, e1), n, ...r(e2, n)], B: [...r(e1, e2), n] } }; })() : { tiles: 1, sharedSides: [] },   // (F1a-1: format 5; F1a-2: Mirror too)
      sides: E.state.edges.length + (S.fg ? 1 : 0), samplesPerSide: SAMPLES,
      boundary: sid(snapshot()), shapeStart: sid(S.initialSnap)
    },
    polygon: Pl ? { history: Pl.hist.map(polyState), position: Pl.hp, shapeBuiltOn: S.shapeBaseKey, shapeAside: sid(S.refined), changeConfirmed: !!S.restartOK } : null,
    history: { steps: S.history.map(step), position: S.hp },
    previousVersion: V ? { polygon: { history: V.poly.hist.map(polyState), position: V.poly.hp }, history: { steps: V.history.map(step), position: V.hp },
      shapeStart: sid(V.initialSnap), boundary: sid(V.edges), shapeBuiltOn: V.baseKey, summary: Object.assign({ shapeEdits: V.shapeEdits, sides: V.sides, cornersMoved: !!V.moved }, V.consId ? { construction: V.consId, drawing: V.drawn || 0 } : {}),
      ...(S.consLink ? { newConstruction: S.consLink } : {}) } : null,   // (F1a-2: format 7)
    composition: { grouping: S.treat, groups: JSON.parse(JSON.stringify(S.comp)), outline: S.outline },
    view: Object.assign({ stage: S.mode, camera: cam(S.cam), cameras, neighbours: S.ghost, showStartingShape: !!S.showStart, showSketch: !!S.showSketch }, S.fg ? { figureFocus: S.fgFocus } : {}),
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
  const twoFig = !!g.unit && g.unit.tiles === 2 && g.construction && isFG(g.construction.id) && g.path === 'polygon';      // (F1a-1: format 5; F1a-2)
  if (g.unit && !twoFig && ((g.unit.tiles || 1) !== 1 || (g.unit.sharedSides || []).length)) throw Object.assign(new Error('it uses a two-tile unit'), { newer: true });
  need(g.samplesPerSide === SAMPLES, 'the boundary is sampled differently');
  const polygon = g.path === 'polygon'; need(polygon || g.path === 'shape', 'the starting path is unknown');
  const C = g.construction; need(obj(C), 'the construction is missing');
  const known = id => typeof id === 'string' && id !== LIVE_ID && CONS.some(c => c.id === id);
  need(known(C.id), 'the construction is unknown'); if (polygon) need(POLY_FAMILY_OF[C.id], 'the construction does not fit a polygon');
  const startId = polygon ? 'translation' : C.id, sides = CONS.find(c => c.id === startId).verts.length;
  const sidesOf = id => CONS.find(c => c.id === id).verts.length + (isFG(id) ? 1 : 0), curSides = sidesOf(C.id);   // (F1a-1: + the inner side)
  need(g.sides === undefined || g.sides === curSides, 'the number of sides does not fit the construction');
  const pt = q => { need(obj(q) && fin(q.x) && fin(q.y), 'a corner is damaged'); return P(q.x, q.y); };
  const corners = (c, id) => { const n = CONS.find(x => x.id === (id || startId)).verts.length; need(Array.isArray(c) && c.length === n, 'the corners are damaged'); return c.map(pt); };   // (F1r: six for Two figures)
  const nodes = (v, id) => { need(obj(v), 'the points are damaged'); const o = {}, lim = id ? sidesOf(id) : sides;
    Object.keys(v).forEach(m => { need(/^\d$/.test(m) && +m < lim && Array.isArray(v[m]), 'a point is on an unknown side'); if (!v[m].length) return;
      o[m] = v[m].map(n => { need(obj(n) && fin(n.s) && fin(n.t), 'a point is damaged'); return { s: n.s, t: n.t, c: !!n.c }; }); });
    return o; };
  const polyState = st => { need(obj(st) && POLY_FAMILY_OF[st.construction] && (st.family === null || st.family === POLY_FAMILY_OF[st.construction]), 'the polygon history is damaged');
    const o = { consId: st.construction, family: st.family, cage: st.corners ? corners(st.corners, st.construction) : null, nodes: nodes(st.points || {}, st.construction) }; if (Number.isInteger(st.seq) && st.seq > 0) o.seq = st.seq; return o; };   // (CR3: seq)
  need(Array.isArray(p.snapshots), 'the boundaries are missing');
  const snaps = p.snapshots.map((a, i) => { const k = a instanceof Float64Array ? a.length / (SAMPLES * 2) : 0;      // (F1a-1: 4 sides, or 7 for two figures)
    need(Number.isInteger(k) && k >= 3 && k <= 12 && a.every(Number.isFinite), 'boundary ' + (i + 1) + ' is damaged');
    const sn = f64Snap(a, k); encCache.set(sn, { f64: a, h: fnv32(a) }); return sn; });          // (already encoded: the next save reuses it)
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
      if (o.mirror !== undefined) need(Array.isArray(o.mirror) && o.mirror.length === 3 && o.mirror.every(fin) && o.layer === 'art', bad);   // (T1)
      const st = { kind: 'stroke' }, eo = { kind: 'stroke' }; STROKE_KEYS.forEach(k => { if (o[k] !== undefined) st[k] = eo[k] = o[k]; }); st.pts = f64Pts(o.pts); eo.pts = o.pts;
      encCache.set(st, { o: eo, snaps: [] }); return st;
    }
    if (o.kind === 'fill') { need(hex(o.color) && fin(o.alpha) && obj(o.seed) && fin(o.seed.x) && fin(o.seed.y), bad);
      const a = { kind: 'fill', color: o.color, alpha: o.alpha, seed: P(o.seed.x, o.seed.y), respectSketch: !!o.respectSketch }, s = snap(o.snap, true); if (o.edge === 1) a.edge = 1; if (s) a.snap = s;   // (CR2: edge)
      if (o.mirror !== undefined) { need(Array.isArray(o.mirror) && o.mirror.length === 3 && o.mirror.every(fin), bad); a.mirror = o.mirror.slice(); }   // (T1)
      if (o.figure !== undefined) { need(o.figure === 'A' || o.figure === 'B', bad); a.figure = o.figure; }                                       // (F1r)
      encCache.set(a, { o: Object.assign({ kind: 'fill', color: a.color, alpha: a.alpha, seed: { x: a.seed.x, y: a.seed.y }, respectSketch: a.respectSketch }, a.edge ? { edge: 1 } : {}, a.mirror ? { mirror: a.mirror.slice() } : {}, a.figure ? { figure: a.figure } : {}), snaps: s ? [['snap', s]] : [] }); return a; }
    if (o.kind === 'shape') { const a = { kind: 'shape', before: snap(o.before), after: snap(o.after) }; encCache.set(a, { o: { kind: 'shape' }, snaps: [['before', a.before], ['after', a.after]] }); return a; }
    throw new Error(bad);
  });
  const hist = (h, what) => { need(obj(h) && Array.isArray(h.steps) && Number.isInteger(h.position) && h.position >= 0 && h.position <= h.steps.length, what + ' is damaged');
    return { list: h.steps.map(k => { need(Number.isInteger(k) && k >= 0 && k < steps.length, what + ' is damaged'); return steps[k]; }), hp: h.position }; };
  const polyHist = (q, what) => { need(obj(q) && Array.isArray(q.history) && q.history.length > 0 && Number.isInteger(q.position) && q.position >= 0 && q.position < q.history.length, what + ' is damaged');
    return { hist: q.history.map(polyState), hp: q.position }; };
  const cur = { consId: C.id, cage: C.cornersMoved ? corners(C.corners, C.id) : null, family: polygon && g.rule ? g.rule.family : null, nodes: polygon ? nodes(g.points || {}, C.id) : {} };
  if (polygon) need(cur.family === null || cur.family === POLY_FAMILY_OF[C.id], 'the rule does not fit the construction');
  let poly = null, recovery = null;
  if (polygon) { const q = p.polygon, h = polyHist(q, 'the polygon history');
    poly = { ...h, builtOn: typeof q.shapeBuiltOn === 'string' ? q.shapeBuiltOn : null, aside: snap(q.shapeAside, true), confirmed: !!q.changeConfirmed };
    const V = p.previousVersion;
    if (V) { need(obj(V), 'the previous version is damaged'); const ph = polyHist(V.polygon, 'the previous version'), h2 = hist(V.history, 'the previous version'), sm = obj(V.summary) ? V.summary : {};
      recovery = { poly: ph, history: h2.list, hp: h2.hp, initialSnap: snap(V.shapeStart), edges: snap(V.boundary), baseKey: typeof V.shapeBuiltOn === 'string' ? V.shapeBuiltOn : null,
        shapeEdits: Number.isInteger(sm.shapeEdits) ? sm.shapeEdits : 0, sides: Number.isInteger(sm.sides) ? sm.sides : 4, moved: !!sm.cornersMoved,
        consId: ph.hist[ph.hp].consId, drawn: Number.isInteger(sm.drawing) && sm.drawing >= 0 ? sm.drawing : 0,
        link: V.newConstruction === 'undo' || V.newConstruction === 'redo' ? V.newConstruction : null }; } }   // (F1a-2)
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
  soft.fgFocus = vw.figureFocus === 'B' ? 'B' : 'A';                                              // (F1a-1)
  const boundary = snap(g.boundary), shapeStart = snap(g.shapeStart);
  need(boundary.length === curSides && shapeStart.length === curSides, 'the boundary does not fit the construction');
  return { startId, polygon, cur, poly, recovery, ref, soft, process, boundary, shapeStart, history: hist(p.history, 'the history') };
}
function checkRestored() {                // the rebuilt tile must be a valid tile of its rule, exactly as a saved one always is
  if (E.state.edges.length + (S.fg ? 1 : 0) !== S.initialSnap.length) return 'the boundary does not fit the construction';
  if (S.fg) { const V = E.state.cons.verts, a = S.fg.inner[0], b = S.fg.inner[N];                       // (F1a-1: the inner side joins its two corners)
    const en = fgEnds(); if (S.fg.inner.length !== SAMPLES || Math.hypot(a.x - V[en[0]].x, a.y - V[en[0]].y) > 1e-9 || Math.hypot(b.x - V[en[1]].x, b.y - V[en[1]].y) > 1e-9) return 'the two figures do not fit the unit'; }
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
  if (d.polygon) { S.shapeBaseKey = d.poly.builtOn; S.refined = d.poly.aside; S.restartOK = d.poly.confirmed; S.recovery = d.recovery;
    S.consLink = d.recovery ? d.recovery.link || null : null; if (d.recovery) delete d.recovery.link; }   // (F1a-2)
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
    if (TP.store.ok === false && !keep.failNoted) { keep.failNoted = true; toast('This browser is not keeping your work on this device · ☰ › Save project file keeps a copy', 4400); }
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
    if (!keep.failNoted) { keep.failNoted = true; toast('Your latest change could not be kept on this device' + (/Quota/.test(r.reason || '') ? ' (storage is full)' : '') + ' · ☰ › Save project file keeps a copy', 4600); }
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

/* ---- what the student sees: the ☰ menu line, the Continue card, Save project / Open project… ---- */
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
  if (TP.store.ok === false) { const n = document.createElement('p'); n.className = 'note'; n.textContent = 'This browser cannot keep your work on this device. Use ☰ › Save project file to keep a copy.'; body.appendChild(n); }
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
    const fgP = S.fg ? fgPolys() : null, fgA = S.fg ? 'M' + fgP.A.map(ptS).join('L') + 'Z' : '', fgB = S.fg ? 'M' + fgP.B.map(ptS).join('L') + 'Z' : '', fgInD = S.fg ? 'M' + S.fg.inner.map(ptS).join('L') : '';   // (F1a-1; F1a-2: + B)
    const art = svgLayer('art', 'ma'), sk = A.sketch > 0 ? svgLayer('sketch', 'ms') : { defs: '', body: '' };
    let defs = art.defs + sk.defs + `<clipPath id="clipT"><path d="${tileD}"/></clipPath><clipPath id="clipB"><path d="${bleedD}"/></clipPath>`;
    defs += svgImage(S.layers.fills.big, 'fills') + `<g id="art">${art.body}</g>` + (sk.body ? `<g id="sketch">${sk.body}</g>` : '');
    if (S.fg) ['A', 'B'].forEach(f => { defs += `<clipPath id="fgc${f}"><path d="M${offsetPolygon(fgP[f], 0.5 / k).map(ptS).join('L')}Z"/></clipPath><clipPath id="fgx${f}"><path d="${f === 'A' ? fgA : fgB}"/></clipPath>`; });   // (F1r; F1a-2: + each figure exactly)
    const variants = new Map();            // one cell drawing per (figure tint, F mark) in use, placed in every tile
    const cellRef = (tint, mark) => { const key = (tint || '') + '|' + mark; if (variants.has(key)) return variants.get(key); const id = 'cell' + variants.size;
      let fillsRef = '#fills', fgRef = null;
      if (tint && tint.startsWith('fg:')) { fgRef = {}; tint.slice(3).split('|').forEach((t, j) => { const f = j ? 'B' : 'A'; if (!t) { fgRef[f] = '#fills'; return; } const tid = 'tint' + variants.size + f; defs += svgImage(getTint(t), tid); fgRef[f] = '#' + tid; }); }   // (F1a-2)
      else if (tint) { const tid = 'tint' + variants.size; defs += svgImage(getTint(tint), tid); fillsRef = '#' + tid; }
      const fillsUse = !(A.art > 0) ? '' : fgRef ? ['A', 'B'].map(f => `<g clip-path="url(#fgc${f})"><use xlink:href="${fgRef[f]}" opacity="${fx(A.art)}"/></g>`).join('') : `<use xlink:href="${fillsRef}" opacity="${fx(A.art)}"/>`;
      defs += `<g id="${id}">` + (mark ? svgMarkLines(mark) : '') + fillsUse +
        (A.sketch > 0 && sk.body ? `<use xlink:href="#sketch" opacity="${fx(A.sketch)}"/>` : '') + (A.art > 0 && art.body ? `<use xlink:href="#art" opacity="${fx(A.art)}"/>` : '') + '</g>';
      variants.set(key, id); return id; };
    let body = o.transparent ? '' : `<rect width="${Wd}" height="${Ht}" fill="${COLORS.bg}"/>`;
    const fgParts = (m, alpha, i) => {        // (F1a-2) the same decisions as drawFgTile
      const c = fgComp(i), id = cellRef(fgTintKey(c.A && c.A.fig, c.B && c.B.fig), 0), bg = f => (c[f] && c[f].bg) || FG_COL[f], lw = outlineWorld(), G = mm => `<g transform="matrix(${mmul(V, mm).map(fx6).join(' ')})">`;
      const line = (d, op) => `<path d="${d}" fill="none" stroke="${COLORS.line}" stroke-width="${fx(lw)}" stroke-linejoin="round"${op ? ` stroke-opacity="${op}"` : ''}/>`;
      if (fgPlain(c.A) && fgPlain(c.B)) { const g = G(m), op = alpha < 0.999 ? fx(alpha) : null, fo = op ? ` fill-opacity="${op}"` : '';
        return [g + `<path d="${bleedD}" fill="${bg('B')}"${fo}/><path d="${fgA}" fill="${bg('A')}"${fo}/></g>`, g + `<g clip-path="url(#${thin ? 'clipB' : 'clipT'})"${op ? ` opacity="${op}"` : ''}><use xlink:href="#${id}"/></g></g>`, lw > 0 ? g + line(tileD + fgInD, op) + '</g>' : '']; }
      const out = ['', '', ''];
      ['B', 'A'].forEach(f => { const cp = c[f]; if (cp && cp.hidden) return; const mm = cp && cp.scale != null && Math.abs(cp.scale - 1) > 1e-6 ? mmul(m, scaleAbout(S.fg['cent' + f], cp.scale)) : m, a = alpha * (cp && cp.alpha != null ? cp.alpha : 1);
        const g = G(mm), op = a < 0.999 ? fx(a) : null, d = f === 'A' ? fgA : fgB;
        out[0] += g + `<path d="${d}" fill="${bg(f)}"${op ? ` fill-opacity="${op}"` : ''}/></g>`; out[1] += g + `<g clip-path="url(#fgx${f})"${op ? ` opacity="${op}"` : ''}><use xlink:href="#${id}"/></g></g>`; if (lw > 0) out[2] += g + line(d, op) + '</g>'; });
      return out.some(Boolean) ? out : null;
    };
    const parts = (m, alpha, active, i) => {   // the same decisions as drawTile → [base, artwork, outline] of one tile
      if (S.fg && tess) return fgParts(m, alpha, i);
      const cp = tess ? compOf(i) : null; if (cp && cp.hidden) return null;
      const mm = cp && cp.scale != null && Math.abs(cp.scale - 1) > 1e-6 ? mmul(m, scaleAbout(S.cent, cp.scale)) : m, a = alpha * (cp && cp.alpha != null ? cp.alpha : 1);
      const bg = tess ? ((cp && cp.bg) || COLORS.fill) : (S.orientCue && shaping() && det(m) < 0 ? COLORS.fillMirror : COLORS.fill);
      const mark = poly ? 0 : S.orientCue ? (shaping() ? MARK_ALPHA.shape : tess && artEmpty ? MARK_ALPHA.tessellate : 0) : 0, id = cellRef(cp && cp.fig ? cp.fig : null, mark);
      const lw = tess ? outlineWorld() : (active ? (shaping() ? 2.4 : 1.6) : 1.1) / k, op = a < 0.999 ? fx(a) : null, g = `<g transform="matrix(${mmul(V, mm).map(fx6).join(' ')})">`;
      const fo = op ? ` fill-opacity="${op}"` : '', fc = S.fg ? fgColours() : null;                // (F1a-1: B under the whole unit, then A)
      return [g + (fc ? `<path d="${bleedD}" fill="${fc[1]}"${fo}/><path d="${fgA}" fill="${fc[0]}"${fo}/>` : `<path d="${bleedD}" fill="${bg}"${fo}/>`) + '</g>',
        g + `<g clip-path="url(#${thin ? 'clipB' : 'clipT'})"${op ? ` opacity="${op}"` : ''}><use xlink:href="#${id}"/>${poly && S.orientCue ? svgMarkLines(MARK_ALPHA.shape) : ''}</g></g>`,
        lw > 0 ? g + `<path d="${tileD}${S.fg ? fgInD : ''}" fill="none" stroke="${COLORS.line}" stroke-width="${fx(lw)}" stroke-linejoin="round"${op ? ` stroke-opacity="${op}"` : ''}/></g>` : ''];
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
const canPolyUndo = () => !!S.poly && (S.poly.hp > 0 || !!topPolySketch() || consBack('undo'));                      // (F1a-2: + back to the previous construction)
const canPolyRedo = () => !!S.poly && (S.poly.hp < S.poly.hist.length - 1 || !!nextPolySketch() || consBack('redo'));   // (F1a-2: + forward to the new one)
function polyUndoRedo(d) {               // the newest of {the last polygon edit, the last Polygon sketch stroke} — or, for Redo, the earliest undone one
  if (!S.poly) return;
  if (d < 0) { const pe = S.poly.hp > 0 ? (S.poly.hist[S.poly.hp].seq || 0) : -1, sk = topPolySketch(), ss = sk ? (sk.seq || 0) : -1;
    if (pe < 0 && ss < 0) { if (consBack('undo')) restoreVersion(); return; } if (ss > pe) applyHistory(-1); else polyHistory(-1); }
  else { const pe = S.poly.hp < S.poly.hist.length - 1 ? (S.poly.hist[S.poly.hp + 1].seq || 0) : Infinity, sk = nextPolySketch(), ss = sk ? (sk.seq || 0) : Infinity;
    if (pe === Infinity && ss === Infinity) { if (consBack('redo')) restoreVersion(); return; } if (ss < pe) applyHistory(1); else polyHistory(1); }
  syncPolyButtons();
}
function syncPolyButtons() { if (!S.poly) return; const u = !canPolyUndo(), r = !canPolyRedo(); $('pb-undo').disabled = u; $('pb-redo').disabled = r; }   // (PH1: always visible)

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

/* ---- ☰ › Experimental: the Grid Explorer, the Regular Grid Explorer and the Rhombus (unchanged; the Rhombus leaves the start screen) ---- */
delete SHAPES.rhombus;
$('m-exp').onclick = () => { const l = $('m-exp-list'), open = l.hidden; l.hidden = !open; $('m-exp-tick').textContent = open ? '⌄' : '›'; };
$('more').addEventListener('click', () => { if (!$('menu').hidden) { $('m-exp-list').hidden = true; $('m-exp-tick').textContent = '›'; } });   // the menu always opens with Experimental folded
const openPage = url => { closeMenu(); if (S.field) { if (keep.dirty) saveNow(true); } const w = window.open(url, '_blank'); if (!w) location.href = url; };   // a new tab: this one keeps the work
$('m-exp-grid').onclick = () => openPage('explorer.html');
$('m-exp-regular').onclick = () => openPage('regular.html');
$('m-exp-rhombus').onclick = () => { closeMenu(); beginNew(() => start('reflection')); };

/* ================= T1 · Square › Mirror, mirrored drawing, one vocabulary (Slide · Turn · Flip · Mirror) =================
 * MIRROR (see the construction at the top): one side is free; its mirror twin follows across the vertical axis and both are slid onto the
 * opposite sides. In Polygon the points live on side 0 and appear on all four sides (orbitRels). The corners are fixed in T1.
 * MIRRORED DRAWING (Illustrate, Mirror only, off by default): a stroke or fill made while it is on carries the axis ([x, y, angle], cell
 * coordinates) and is painted twice, as drawn and reflected. It is part of the history step, so Undo, replay, saving and SVG all repeat it
 * exactly; free drawing stays the default, so geometric symmetry (the outline) and illustration symmetry (the drawing) can be compared. */
let orbitCache = null;
function orbitsOf(V, rels) {              // every side as a copy of the first side of its group of linked sides (rels with m and inv)
  const n = V.length, R = Array(n), out = [];
  for (let s0 = 0; s0 < n; s0++) { if (R[s0]) continue; R[s0] = IDM; const q = [s0];
    while (q.length) { const e = q.shift();
      rels.forEach(r => { if (r.self !== undefined) return; let f, m;
        if (r.from === e) { f = r.to; m = r.m; } else if (r.to === e) { f = r.from; m = r.inv; } else return;
        if (R[f]) return; R[f] = mmul(m, R[e]); q.push(f);
        const a0 = mapp(R[f], V[s0]); out.push({ from: s0, to: f, m: R[f], inv: minv(R[f]), rev: !(Math.hypot(a0.x - V[f].x, a0.y - V[f].y) < 1e-9), role: 'glue' }); }); } }
  return out;
}
function orbitRels() {                    // (T1) the current construction's orbits (glue AND mirror links)
  const st = E.state; if (orbitCache && orbitCache.rels === st.rels) return orbitCache.out;
  const out = orbitsOf(st.cons.verts, st.rels); orbitCache = { rels: st.rels, out }; return out;
}
S.mirrorDraw = false;
const mirrorRel = () => E.state.rels.find(r => r.role === 'constraint' && r.d.type === 'mirror');
const mirrorAxisArr = () => { const r = mirrorRel(); return r ? [r.d.p0.x, r.d.p0.y, r.d.phi] : null; };
const mirrorDrawOn = () => S.mirrorDraw && isMirrorId(S.consId) && S.mode === 'illustrate' && !!mirrorRel();
const reflM = ax => { const c2 = Math.cos(2 * ax[2]), s2 = Math.sin(2 * ax[2]), x = ax[0], y = ax[1]; return [c2, s2, s2, -c2, x - (c2 * x + s2 * y), y - (s2 * x - c2 * y)]; };
const mirrorPts = st => { const m = reflM(st.mirror); return st.pts.map(p => mapp(m, p)); };
function pxMirror(L, ax) {                // the reflection in a raster's own pixel coordinates (toPx ∘ reflection ∘ toPx⁻¹)
  const k = L.k, I = S.ink; return mmul([k, 0, 0, -k, -k * I.x0, k * I.y1], mmul(reflM(ax), [1 / k, 0, 0, -1 / k, I.x0, I.y1])); }
function mirrorLive(s) {                  // the reflected half of the stroke being drawn (its points grow with the stroke)
  const st = s.st; if (!s.mst) s.mst = Object.assign({}, st, { pts: [], mirror: undefined });
  const m = reflM(st.mirror); while (s.mst.pts.length < st.pts.length) s.mst.pts.push(mapp(m, st.pts[s.mst.pts.length])); return s.mst;
}
function paintPenMirror(L, st, opaque) {  // ONE path with two parts (the stroke and its reflection): a translucent pen never darkens where they cross
  const c = L.bctx, parts = [st.pts, mirrorPts(st)]; penPrep(c, L, st, opaque); c.beginPath(); const r = c.lineWidth / 2;
  if (st.pts.length === 1) { parts.forEach(pts => { const q = toPx(pts[0], L); c.moveTo(q.x + r, q.y); c.arc(q.x, q.y, r, 0, TAU); }); c.fill(); }
  else { parts.forEach(pts => { const q = pts.map(p => toPx(p, L)); c.moveTo(q[0].x, q[0].y);
      if (q.length === 2) c.lineTo(q[1].x, q[1].y);
      else { for (let i = 1; i < q.length - 1; i++) { const m = mid(q[i], q[i + 1]); c.quadraticCurveTo(q[i].x, q[i].y, m.x, m.y); } c.lineTo(q[q.length - 1].x, q[q.length - 1].y); } });
    c.stroke(); }
  c.restore();
}
{ const _df = doFill; doFill = function (a, snap) {                     // a mirrored fill colours the mirror-image region as well
    const r1 = _df(a, snap); if (!a.mirror) return r1;
    const b = Object.assign({}, a, { seed: mapp(reflM(a.mirror), a.seed) }); delete b.mirror; return _df(b, snap) || r1; }; }
{ const _sp = svgPen; svgPen = function (st, opaque, col) {             // SVG: the same two-part path
    if (!st.mirror) return _sp(st, opaque, col);
    col = col || st.color; const a = (st.tool === 'eraser' || opaque) ? 1 : st.alpha, op = a < 0.999 ? ` opacity="${fx(a)}"` : '', mp = mirrorPts(st);
    if (st.pts.length === 1) return `<path d="${circlePath(st.pts[0], st.w / 2)}${circlePath(mp[0], st.w / 2)}" fill="${col}"${op}/>`;
    return `<path d="${svgPenPath(st.pts)}${svgPenPath(mp)}" fill="none" stroke="${col}" stroke-width="${fx(st.w)}" stroke-linecap="round" stroke-linejoin="round"${op}/>`; }; }
{ const _ss = svgStamps; svgStamps = function (st) {                    // SVG: the marks again inside a reflection
    const s = _ss(st); if (!st.mirror) return s; const m = reflM(st.mirror);
    return s + `<g transform="matrix(${m.map(v => fx6(v)).join(' ')})">${s}</g>`; }; }
function drawMirrorAxis() {               // the mirror line through the tile (Polygon, Shape; Illustrate while mirrored drawing is on)
  const ax = mirrorAxisArr(); if (!ax) return; const u = P(Math.cos(ax[2]), Math.sin(ax[2])), poly = E.polygon(edgesNow());
  let lo = Infinity, hi = -Infinity; poly.forEach(p => { const t = (p.x - ax[0]) * u.x + (p.y - ax[1]) * u.y; lo = Math.min(lo, t); hi = Math.max(hi, t); });
  const ext = 0.08 * (hi - lo), a = w2s(P(ax[0] + u.x * (lo - ext), ax[1] + u.y * (lo - ext))), b = w2s(P(ax[0] + u.x * (hi + ext), ax[1] + u.y * (hi + ext)));
  ctx.save(); ctx.setLineDash([7, 6]); ctx.lineCap = 'round'; ctx.strokeStyle = '#e58bb0'; ctx.lineWidth = 2; ctx.globalAlpha = 0.9;
  ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke(); ctx.restore();
}
function syncMirrorUI() {
  const b = $('t-mirror'); if (!b) return; b.hidden = !isMirrorId(S.consId); b.setAttribute('aria-pressed', String(!!S.mirrorDraw));
}
$('t-mirror').onclick = () => { S.mirrorDraw = !S.mirrorDraw; syncMirrorUI(); invalidate();
  if (S.mirrorDraw && S.consId === 'mirror-flip' && !S.seenHint.flipSym) { S.seenHint.flipSym = true; toast(FLIP_SYM_NOTE, 4200); }   // (T2)
  else if (S.mirrorDraw && !S.seenHint.mirrorDraw) { S.seenHint.mirrorDraw = true; toast('Mirrored drawing: what you draw on one side appears on the other · tap again for free drawing', 3600); }
  else toast(S.mirrorDraw ? 'Mirrored drawing on' : 'Free drawing', 1400); };
{ const _sc = setCage; setCage = function (id, cage) { _sc(id, cage);                     // the starting shape of Mirror is the diamond
    if (S.poly) S.origVerts = (isMirrorId(id) ? CONS.find(c => c.id === 'mirror').verts : SQUARE).map(p => P(p.x, p.y)); syncMirrorUI(); }; }
{ const _st = start; start = function (id, opts) { S.mirrorDraw = false; _st(id, opts); syncMirrorUI(); }; }
{ const _sm = setMode; setMode = function (m, quiet) { _sm(m, quiet); syncMirrorUI(); }; }
{ const _cp = captureProject; captureProject = function () { const p = _cp(); p.tools.mirrorDraw = !!S.mirrorDraw; return p; }; }
{ const _dp = decodeProject; decodeProject = function (p) { const d = _dp(p); d.soft.tools.mirrorDraw = !!(p.tools && p.tools.mirrorDraw === true); return d; }; }
{ const _ad = applyDecoded; applyDecoded = function (d) { const r = _ad(d); S.mirrorDraw = !!d.soft.tools.mirrorDraw; syncMirrorUI(); return r; }; }
// learning information: the four rules with their mathematical names (Polygon bar ⓘ, and About)
const RULES_INFO = [
  { id: 'translation', name: 'Translate', math: 'translation, a slide', text: 'Every tile is the same figure moved along (slid), never turned or flipped. A bump on one side appears in the same place on the opposite side.' },
  { id: 'rotation-sq-ac', name: 'Rotate', math: 'rotation, a turn', text: 'Neighbouring tiles are the figure turned about a corner (a quarter-turn) or about the middle of a side (a half-turn). A bump on one side turns onto the next side.' },
  { id: 'glide', name: 'Glide reflection', math: 'a flip and a slide', text: 'Neighbouring tiles are the figure reflected (flipped over) and slid along: mirror images that do not face each other across a line. A bump on one side appears on the opposite side, flipped.' },
  { id: 'mirror', name: 'Reflection', math: 'a mirror', text: 'The tile itself is symmetric: one half is the mirror image of the other across the dashed line. Two arrangements, Same and Mirrored, below. Mirrored drawing in Illustrate makes your drawing symmetric too.' }
];
function openRules() {
  const body = $('rules-body'); body.innerHTML = RULES_INFO.map(r => `<div class="rule"><div class="rule-pic">${previewSVG(CONS.find(c => c.id === r.id))}</div><div><h3>${r.name} <span>· ${r.math}</span></h3><p>${r.text}</p></div></div>`).join('');
  body.insertAdjacentHTML('beforeend', ARRANGE_INFO);                // T2: reflection inside the tile vs reflection of the neighbouring drawings
  body.insertAdjacentHTML('beforeend', FG_INFO);                     // F1a-1: Two figures
  $('rules').hidden = false;
}
$('pb-info').onclick = openRules; $('rules-back').onclick = () => { $('rules').hidden = true; }; $('about-rules').onclick = e => { e.preventDefault(); $('about').hidden = true; openRules(); };

/* ================= T2 · Mirror with two arrangements: Same orientation and Alternating =================
 * The choice is Mirror's second row in the Polygon bar (the rule lives in Polygon, spec §3.5). Changing it is one step on the Polygon Undo timeline:
 * the tile, its points, the Shape pulls (the key polyKey ignores the arrangement, so Shape is never restarted), the drawing and the Tessellate groups
 * are all kept; only the neighbour placements are rebuilt. Shape shows the mirrored copies (shading and the orientation F, as for Flip); Tessellate
 * shows them in the drawings themselves (or the F while nothing is drawn). */
const FLIP_SYM_NOTE = 'With a symmetric drawing, Mirrored looks the same as Same · draw freely to see the mirrored neighbours';
const artMirrored = () => S.history.slice(0, S.hp).some(a => !!a.mirror);
function arrangementNote(id) {
  if (id === 'mirror-flip' && (S.mirrorDraw || artMirrored()) && !S.seenHint.flipSym) { S.seenHint.flipSym = true; toast(FLIP_SYM_NOTE, 4200); return; }
  toast(id === 'mirror-flip' ? 'Mirrored · each neighbour across a side is mirrored and slid · the outline stays the same' : 'Same · every neighbour is slid, none is mirrored', 2600);
}
{ const _sm0 = setMode; setMode = function (m, quiet) { _sm0(m, quiet); ensureInk(); }; }   // (DA)
{ const _sm = setMode; setMode = function (m, quiet) { const from = S.mode, first = !quiet && !S.seenHint[m]; _sm(m, quiet);
    if (quiet || first || S.mode === from || S.consId !== 'mirror-flip') return;     // (a stage's own first hint goes first)
    if (m === 'shape' && !S.seenHint.flipShape) { S.seenHint.flipShape = true; toast('Shaded tiles are mirrored · the F shows which way each one faces', 3200); }
    else if (m === 'tessellate' && !S.seenHint.flipTess) { S.seenHint.flipTess = true; toast('Mirrored · the neighbour across each side is the mirror image · the outlines stay the same', 3400); } }; }
function arrangeSVG(flip) {               // five tiles of the Mirror diamond with the orientation F: the starting tile and its four side neighbours
  const r = MIRROR_R, V = CONS.find(c => c.id === 'mirror').verts, F = [[-0.08, -0.15, -0.08, 0.15], [-0.08, 0.15, 0.12, 0.15], [-0.08, 0.02, 0.07, 0.02]], z = 1.7;
  const f = v => (Math.round(v * 1000) / 1000).toString(), tiles = [[0, 0], [r, r], [-r, r], [r, -r], [-r, -r]];
  let s = '';
  tiles.forEach(([dx, dy], i) => { const mir = flip && i > 0, cx = 0.5 + dx, cy = 0.5 + dy;
    s += `<path d="${V.map((q, k) => (k ? 'L' : 'M') + f(q.x + dx) + ' ' + f(-(q.y + dy))).join('')}Z" fill="${mir ? COLORS.fillMirror : COLORS.fill}" stroke="#1d1b18" stroke-width="0.02"/>`;
    F.forEach(g => { const x1 = cx + (mir ? -1 : 1) * g[0] * z, x2 = cx + (mir ? -1 : 1) * g[2] * z; s += `<path d="M${f(x1)} ${f(-(cy + g[1] * z))}L${f(x2)} ${f(-(cy + g[3] * z))}" stroke="#1d1b18" stroke-width="0.045" stroke-linecap="round"/>`; }); });
  s += `<path d="M0.5 ${f(-(0.5 + r + 0.08))}L0.5 ${f(-(0.5 - r - 0.08))}" stroke="#e58bb0" stroke-width="0.03" stroke-dasharray="0.07 0.05"/>`;
  return `<svg viewBox="${f(0.5 - 2 * r - 0.05)} ${f(-(0.5 + 2 * r + 0.05))} ${f(4 * r + 0.1)} ${f(4 * r + 0.1)}" aria-hidden="true">${s}</svg>`;
}
const ARRANGE_INFO = `<div class="arrange"><h3>Reflection · Same or Mirrored</h3>
  <p><b>Inside the tile</b>, the mirror makes the outline symmetric (the dashed line). That is the same in both arrangements.</p>
  <div class="arrange-pics"><figure>${arrangeSVG(false)}<figcaption><b>Same</b> · each neighbour is slid: every drawing faces the same way <span>(translation)</span></figcaption></figure>
  <figure>${arrangeSVG(true)}<figcaption><b>Mirrored</b> · each neighbour across a side is mirrored and slid: the drawings alternate, the outlines stay the same <span>(glide reflection)</span></figcaption></figure></div>
  <p class="mute">A symmetric drawing looks the same both ways. Draw something that faces one way to see the difference.</p></div>`;

/* ================= F1a-1 · TWO FIGURES: Figure A and Figure B (Slide) =================
 * One figure / Two figures is its own choice, separate from the rule (Slide · Turn · Flip · Mirror): a small floating control above the Polygon bar
 * (two figures work with Slide for now). Choosing it is one step on the Polygon Undo timeline and starts the polygon again from the two-square unit.
 * The same floating place shows the shares in Shape (A 56% · B 44%) and, in every stage, Swap: which figure is emphasised (geometry unchanged). */
/* F1r · THE CORNERS OF TWO FIGURES (verified in ../tessellation-geometry-review/f1-corners). The repeats stay exact exactly when opposite sides stay
 * equal and parallel, i.e. the six corners are point-symmetric about the unit's centre; then every simple unit tiles (A always meets B). The rule
 * (the student's choice): an OUTER corner (0, 2, 3, 5) slides its side, as in One figure, and the opposite side slides back the same amount; an
 * END OF THE MIDDLE SIDE (1, 4) moves with its opposite corner mirrored through the centre. Together they reach every valid unit. */
const FG_CAGE_MIN_SIDE = 0.2, FG_CAGE_ANGLES = [20, 340];             // × cell; degrees (a corner may point inwards, as long as the outline stays simple)
function fgCageAfterDrag(V0, k, tgt) {
  const d = P(tgt.x - V0[k].x, tgt.y - V0[k].y), V = cloneCage(V0), mv = (i, s) => { V[i] = P(V[i].x + s * d.x, V[i].y + s * d.y); };
  if (k === 1 || k === 4) { mv(k, 1); mv((k + 3) % 6, -1); } else { mv(k, 1); mv((k + 1) % 6, 1); mv((k + 3) % 6, -1); mv((k + 4) % 6, -1); }
  const c = P((V0[0].x + V0[3].x) / 2, (V0[0].y + V0[3].y) / 2);       // both rules keep the centre: re-derive 3, 4, 5 from it so the symmetry is exact
  for (const i of [0, 1, 2]) V[i + 3] = P(2 * c.x - V[i].x, 2 * c.y - V[i].y);
  return V;
}
function fgCageProblem(V) {
  const z = S.unit, n = 6; if (!V || V.length !== n) return 'fixed';
  const c = P((V[0].x + V[3].x) / 2, (V[0].y + V[3].y) / 2);
  for (const i of [1, 2]) if (Math.hypot((V[i].x + V[i + 3].x) / 2 - c.x, (V[i].y + V[i + 3].y) / 2 - c.y) > 1e-9) return 'symmetric';
  let a2 = 0; for (let i = 0; i < n; i++) { const p = V[i], q = V[(i + 1) % n]; a2 += p.x * q.y - q.x * p.y; if (Math.hypot(q.x - p.x, q.y - p.y) < FG_CAGE_MIN_SIDE * z) return 'side'; }
  if (a2 <= 0) return 'fold';
  for (let i = 0; i < n; i++) { const a = V[(i + n - 1) % n], b = V[i], q = V[(i + 1) % n], ux = a.x - b.x, uy = a.y - b.y, wx = q.x - b.x, wy = q.y - b.y;
    let t = Math.atan2(wx * uy - wy * ux, wx * ux + wy * uy) * 180 / PI; if (t <= 0) t += 360; if (t < FG_CAGE_ANGLES[0] || t > FG_CAGE_ANGLES[1]) return 'angle'; }
  for (let i = 0; i < n; i++) for (let j = i + 2; j < n; j++) { if (i === 0 && j === n - 1) continue; const a = V[i], b = V[(i + 1) % n], q = V[j], r = V[(j + 1) % n];
    if (segX(a.x, a.y, b.x, b.y, q.x, q.y, r.x, r.y)) return 'cross'; }
  return '';
}
/* F1r · FILLS BELONG TO A FIGURE. A fill made in Two figures records the figure that was tapped; it is replayed as a flood of THAT figure as it is now,
 * from the same place (or the nearest place still inside the figure), bounded by the figure and by the pen lines drawn before it. So a fill never
 * reaches the other figure and always follows its own figure when a side or a corner moves (the student's choice, 29 Oct). The fills are redone when
 * the boundary settles: the end of a pull, Undo/Redo, Reset, a Polygon change, entering or leaving Polygon. One figure keeps its own rule. */
let fgHold = 0;
function fgRefresh(rebuilt) {             // → true when the fills were redone
  if (!S.fg || !S.layers || rebuilt || fgHold || restoring || !S.history.slice(0, S.hp).some(a => a.kind === 'fill')) return false;
  const t0 = performance.now(); if (S.history.slice(0, S.hp).some(a => a.kind === 'fill' && a.respectSketch)) rebuildLayers(); else fgRefillLayers();
  S.fgRefillMs = performance.now() - t0; invalidate(); return true;
}
function fgRefillLayers() {               // only the fills change with the boundary: redo them (and the pen lines they stop at); strokes stay as they are
  const L = S.layers; clearLayer(L.fills); clearLayer(L.lines); fillCtx = { fig: {} };
  try { for (let i = 0; i < S.hp; i++) { const a = S.history[i];
    if (a.kind === 'stroke' && a.layer === 'art' && isPenLike(a)) { paintPenFull(L.lines, a, true); fillCtx.lines = null; }
    else if (a.kind === 'fill') doFill(a, a.snap || S.initialSnap); } }
  finally { fillCtx = null; }
  syncView(L.fills, ALL); S.compCache.forEach(e => paintComposite(e, null)); S.artVer++; touchLayers();
}
function fgFigureAt(p) {                  // which figure a point of the unit is in (a point on the middle side: the nearest)
  const inA = q => scratch.isPointInPath(S.pathA, q.x, q.y), inB = q => scratch.isPointInPath(S.pathB, q.x, q.y);
  if (inA(p)) return 'A'; if (inB(p)) return 'B';
  for (const r of [0.004, 0.01, 0.02]) for (let k = 0; k < 8; k++) { const q = P(p.x + r * S.unit * Math.cos(k * PI / 4), p.y + r * S.unit * Math.sin(k * PI / 4)); if (inA(q)) return 'A'; if (inB(q)) return 'B'; }
  return 'A';
}
const F1polyPx = (f, L) => fgPolys()[f].map(p => toPx(p, L));
function offsetPolygon(poly, d) {         // a polygon moved outwards by d (vertex normals averaged; d is tiny) — as offsetPoly, for any outline
  const n = poly.length; let a2 = 0; for (let i = 0; i < n; i++) { const p = poly[i], q = poly[(i + 1) % n]; a2 += p.x * q.y - q.x * p.y; }
  const sg = a2 > 0 ? 1 : -1, nrm = (a, b) => { const dx = b.x - a.x, dy = b.y - a.y, l = Math.hypot(dx, dy) || 1; return P(sg * dy / l, -sg * dx / l); };
  return poly.map((c, i) => { const n1 = nrm(poly[(i - 1 + n) % n], c), n2 = nrm(c, poly[(i + 1) % n]); let x = n1.x + n2.x, y = n1.y + n2.y; const l = Math.hypot(x, y);
    if (l < 1e-9) { x = n1.x; y = n1.y; } else { x /= l; y /= l; } return P(c.x + x * d, c.y + y * d); });
}
{ const _rv = restoreVersion; restoreVersion = function () { fgHold++; try { _rv(); } finally { fgHold--; } }; }   // (it redraws the layers itself)
/* F1a-2 · THE CORNERS OF MIRROR · TWO FIGURES. Five numbers make the unit: the half-widths at A's bottom (e0) and at the middle (e1), the height h of
 * each figure (the repeat forces A and B to the same height), and the heights of the two points on the mirror line (p for A's bottom, q for the middle
 * side, which is a point of the middle side). Twin corners move mirrored; up and down changes h (A and B together); the mirror-line points move up
 * and down only. Everything else — a corner without its twin, a point off the line, unequal heights, a tilted line — the engine refuses (verified). */
const fgMCage = (c, y0, e0, e1, h, p) => [P(c - e0, y0), P(c, y0 + p), P(c + e0, y0), P(c + e1, y0 + h), P(c + e0, y0 + 2 * h), P(c, y0 + 2 * h + p), P(c - e0, y0 + 2 * h), P(c - e1, y0 + h)];
const fgMParams = V => ({ c: V[1].x, y0: V[0].y, e0: V[2].x - V[1].x, e1: V[3].x - V[1].x, h: V[3].y - V[0].y, p: V[1].y - V[0].y });
function fgMCageAfterDrag(V0, k, tgt) {
  const q = fgMParams(V0), d = P(tgt.x - V0[k].x, tgt.y - V0[k].y), sx = k === 2 || k === 3 || k === 4 ? 1 : -1;
  if (k === 0 || k === 2) { q.e0 += sx * d.x; q.y0 += d.y; q.h -= d.y; }          // A's bottom corners (the middle corners stay)
  else if (k === 3 || k === 7) { q.e1 += sx * d.x; q.h += d.y; }                  // the ends of the middle side
  else if (k === 4 || k === 6) { q.e0 += sx * d.x; q.h += d.y / 2; }              // B's top corners (the next A's bottom corners)
  else q.p += d.y;                                                                 // 1 and 5: on the mirror line, up and down only
  return fgMCage(q.c, q.y0, q.e0, q.e1, q.h, q.p);
}
function fgMCageProblem(V) {
  if (!V || V.length !== 8) return 'fixed'; const q = fgMParams(V), W = fgMCage(q.c, q.y0, q.e0, q.e1, q.h, q.p), z = S.unit;
  if (V.some((p, i) => Math.hypot(p.x - W[i].x, p.y - W[i].y) > 1e-9)) return 'symmetric';
  if (q.e0 < 0.1 * z || q.e1 < 0.1 * z || q.h < 0.3 * z) return 'side';
  let a2 = 0; for (let i = 0; i < 8; i++) { const a = V[i], b = V[(i + 1) % 8]; a2 += a.x * b.y - b.x * a.y; if (Math.hypot(b.x - a.x, b.y - a.y) < 0.1 * z) return 'side'; }
  if (a2 <= 0) return 'fold';
  for (let i = 0; i < 8; i++) for (let j = i + 2; j < 8; j++) { if (i === 0 && j === 7) continue; const a = V[i], b = V[(i + 1) % 8], c = V[j], d = V[(j + 1) % 8]; if (segX(a.x, a.y, b.x, b.y, c.x, c.y, d.x, d.y)) return 'cross'; }
  for (let i = 0; i < 8; i++) { const a = V[(i + 7) % 8], b = V[i], c = V[(i + 1) % 8], ux = a.x - b.x, uy = a.y - b.y, wx = c.x - b.x, wy = c.y - b.y;
    let t = Math.atan2(wx * uy - wy * ux, wx * ux + wy * uy) * 180 / PI; if (t <= 0) t += 360; if (t < 15 || t > 345) return 'angle'; }
  return '';
}
function fgHomeInk() {                     // the drawing area of the construction now in use (around the unit, or the square's), as large as the tile needs
  const V = S.fg ? fgHomeOf(S.consId) : SQUARE, c = P(V.reduce((t, q) => t + q.x, 0) / V.length, V.reduce((t, q) => t + q.y, 0) / V.length);
  S.inkBase = { side: (S.fg ? FG_INK : 2 * INK_HALF) * S.unit, centre: c }; const want = inkFor();
  makeInk(want.side, want.centre); rebuildLayers(); clampCam();
}
{ const _sc = setCage; setCage = function (id, cage) {
    const was = S.fg ? S.fg.id : null; _sc(id, cage); const now = isFG(id) ? id : null;
    if (now && (!S.fg || S.fg.id !== now)) S.fg = { id: now, inner: straightInner() }; else if (!now) S.fg = null;
    if (now) S.origVerts = fgHomeOf(now).map(q => P(q.x, q.y));             // (F1r: also after a corner move; T1's wrapper sets the square)
    if (was === now) return;
    if (S.fgQuiet || !S.layers) return;                                       // (polySnapshot: a look at another state changes nothing else)
    fgHomeInk(); fitCamera(); syncFgUI();
  }; }
function fgNote(id, from, had) {           // the note when two figures are switched on or off (→ true when it was shown)
  if (!isFG(id) && !isFG(from)) return false;
  const again = had ? ' · the polygon starts again · Undo brings it back' : '';
  if (isFG(id) && !S.seenHint.fg) { S.seenHint.fg = true; toast('Figure & Ground · Figure A and Figure B share every side: change one and the other changes too' + (had ? ' · Undo brings your polygon back' : ''), 4400); }
  else toast((isFG(id) ? 'Figure & Ground' : 'One figure') + again, 2600);
  return true;
}
function syncFgShare() {
  if (!S.fg || S.fg.areaA === undefined) return; const sh = fgShares(), t = 'A ' + sh.A + '% · B ' + sh.B + '%', el = $('fg-share');
  if (el.textContent !== t) { el.textContent = t; el.setAttribute('aria-label', 'Figure A ' + sh.A + ' percent, Figure B ' + sh.B + ' percent of the unit'); }
}
function syncFgUI() {
  const on = !!S.fg, st = S.poly && S.poly.family ? polyCommitted() : null, inPoly = S.mode === 'polygon' && !!st;
  const work = on && S.mode !== 'tessellate';                                // (F1a-2: Working on A | B while shaping and illustrating; Tessellate colours by tapping a figure)
  $('fg-bar').hidden = !S.field || !(inPoly || work); $('fg-bar').classList.toggle('compact', inPoly);
  $('fg-mode').hidden = !inPoly; $('fg-work').hidden = !work; $('fg-share').hidden = !(on && S.mode === 'shape');
  $('fg-one').setAttribute('aria-pressed', String(!on)); $('fg-two').setAttribute('aria-pressed', String(on));
  $('fg-two').setAttribute('aria-disabled', String(!!st && !FG_OF[st.family]));                    // (F1a-2: Slide and Mirror)
  $('fg-wa').setAttribute('aria-pressed', String(S.fgFocus === 'A')); $('fg-wb').setAttribute('aria-pressed', String(S.fgFocus === 'B'));
  syncFgShare();
}
function setWorkingOn(f) {                 // (F1a-2) the figure being worked on: emphasis only (the other is quietly dimmed); identities and colours never change
  if (!S.fg || (f !== 'A' && f !== 'B') || S.fgFocus === f) return; S.fgFocus = f; syncFgUI(); invalidate(); markDirty(); journal('figure', { focus: f });
  if (!S.seenHint.fgWork) { S.seenHint.fgWork = true; toast('Working on Figure ' + f + ' · the other is dimmed · the colours stay as they are', 2600); } else toast('Working on Figure ' + f, 1000);
}
const swapFigures = () => setWorkingOn(S.fgFocus === 'A' ? 'B' : 'A');     // (kept for the test suites)
$('fg-one').onclick = () => { if (S.mode === 'polygon' && S.fg) choosePolyCons(isFGM(S.consId) ? 'mirror' : 'translation'); };   // (F1a-2: back to Mirror's one figure)
$('fg-two').onclick = () => { const st = S.poly && S.poly.family ? polyCommitted() : null; if (!st || S.fg) return;
  if (!FG_OF[st.family]) { toast('Figure & Ground works with Translate and Reflection', 2200); return; } choosePolyCons(FG_OF[st.family]); };
$('fg-wa').onclick = () => setWorkingOn('A'); $('fg-wb').onclick = () => setWorkingOn('B');
{ const _st = start; start = function (id, opts) { S.fgFocus = 'A'; _st(id, opts); syncFgUI(); }; }
{ const _ad = applyDecoded; applyDecoded = function (d) { const r = _ad(d); S.fgFocus = S.fg && d.soft.fgFocus === 'B' ? 'B' : 'A'; syncFgUI(); invalidate(); return r; }; }   // (after start(), which begins with A)
{ const _aps = applyPolyState; applyPolyState = function (st) { _aps(st); syncFgUI(); fgRefresh(false); }; }   // (F1r: a Polygon change redoes the fills)
{ const _sm = setMode; setMode = function (m, quiet) { const from = S.mode; _sm(m, quiet); syncFgUI();
    if (!quiet && S.fg && S.mode !== from && m === 'shape' && !S.seenHint.fgShape) { S.seenHint.fgShape = true; toast('Pull any boundary: Figure A and Figure B change together · two fingers move & zoom', 3600); } }; }
function fgInfoSVG() {                     // a few units of a two-figure Slide tiling, with one curved inner side and one bump: A and B interlock
  const n = 24, f = v => (Math.round(v * 1000) / 1000).toString(), seg = (fn) => { const o = []; for (let i = 0; i <= n; i++) o.push(fn(i / n)); return o; };
  const e0 = seg(t => [t, 0]), e1 = seg(t => [1 + t, -0.16 * Math.sin(PI * t)]), e2 = seg(t => [2, t]), e3 = seg(t => [2 - t, 1]), e4 = seg(t => [1 - t, 1 - 0.16 * Math.sin(PI * (1 - t))]), e5 = seg(t => [0, 1 - t]);
  const inn = seg(t => [1 + 0.2 * Math.sin(2 * PI * t), t]), A = [...e0, ...inn, ...e4, ...e5], B = [...e1, ...e2, ...e3, ...inn.slice().reverse()];
  const d = (pts, dx, dy) => 'M' + pts.map(q => f(q[0] + dx) + ' ' + f(-(q[1] + dy))).join('L') + 'Z';
  let s = '';
  for (let i = -3; i <= 3; i++) for (let j = -3; j <= 3; j++) { const dx = i + j, dy = i - j; if (Math.abs(dx - 1) > 3 || Math.abs(dy) > 3) continue;
    s += `<path d="${d(A, dx, dy)}" fill="${FG_COL.figure}"/><path d="${d(B, dx, dy)}" fill="${FG_COL.ground}"/><path d="${d(A, dx, dy)}${d(B, dx, dy)}" fill="none" stroke="#1d1b18" stroke-width="0.025" stroke-linejoin="round"/>`; }
  s += `<text x="0.45" y="-0.42" font-size="0.32" font-weight="600" text-anchor="middle" fill="rgba(29,27,24,.6)">A</text><text x="1.6" y="-0.42" font-size="0.32" font-weight="600" text-anchor="middle" fill="rgba(255,248,240,.9)">B</text>`;
  return `<svg viewBox="-0.7 -1.8 3.4 2.6" aria-hidden="true">${s}</svg>`;
}
const FG_INFO = `<div class="arrange"><h3>Figure &amp; Ground <span>· two complementary figures, not a transformation</span></h3>
  <p>Choose <b>Figure &amp; Ground</b> in the Polygon panel, then how the units repeat: <b>Translate</b> or <b>Reflection</b>. The unit is two squares, <b>Figure A</b> and <b>Figure B</b>, and every boundary belongs to both: an A always meets a B.</p>
  <div class="arrange-pics"><figure>${fgInfoSVG()}<figcaption>Push a boundary into A and B grows by exactly as much: <span>the shares in Shape always add up to 100%</span></figcaption></figure></div>
  <p><b>Figure &amp; Ground · Reflection</b> stacks A below B with one mirror line through both: each figure is symmetric, and they are different — where A widens, B narrows. Twin corners move together; up and down makes A and B taller together.</p>
  <p class="mute">Working on A | B chooses the figure you are working on; the other is dimmed, and no colour changes. In Translate, an outer corner slides its side (the opposite side slides back), and the two corners where A meets B move with their opposite, mirrored. In Tessellate, tap a figure to colour its group.</p></div>`;


/* ================= PH1 · v5.10 · Phase 1: the interface reorganised (design: ../tessellation-development-phases/phase1/) =================
 * Interface only: the constructions and their ids, the engine, both histories and the project format are v5.9's.
 *   • Starting shape Tri · Quad · Hex (Hex: coming later). Changing it starts a new tessellation after the usual question (as ☰ › New).
 *   • Construction method Translate · Rotate · Glide reflection · Reflection │ Figure & Ground, each with its sub-method row. A method a shape
 *     cannot use is shown and explained: 'no' = not possible with this shape (with the reason), 'later' = possible, not in this app yet.
 *   • Tri enters Polygon as a VIEW: corners and sides stay fixed, as in v5.9; nothing is set aside, saved differently or redrawn.
 *   • Undo / Redo: one pair at the top-left of the panel in every stage, always visible; each says what it would undo or redo.
 *   • Menu: ☰, a main page and two sub-pages; the later phases' features are listed, marked "Coming later", and do nothing. */
function triView() { return !S.poly && S.cellKind === 'triangle' && !!S.field; }
const METHOD_NAME = { translate: 'Translate', rotate: 'Rotate', glide: 'Glide reflection', mirror: 'Reflection', fg: 'Figure & Ground' };
const TRI_AVAIL = { translate: 'no', rotate: null, glide: 'later', mirror: 'later', fg: 'later' };
const TRI_NOTE = {
  translate: 'Translate is not possible with Tri: a single triangle has no pair of opposite sides, so translation alone cannot repeat it. Two triangles together can: Figure & Ground (coming later).',
  glide: 'Glide reflection with Tri is possible (glides on two sides, a half-turn on the third), but it is not in this app yet.',
  mirror: 'Reflection with Tri is possible only if one side stays straight; it is not in this app yet.',
  fg: 'Figure & Ground with Tri (an up and a down triangle) is possible, but it is not in this app yet.' };
const HEX_NOTE = 'Hex (hexagon) is coming later: its geometry and interactions are not built yet.';
const methodOf = st => !st || !st.family ? null : isFG(st.consId) ? 'fg' : st.family;
let triNoteAt = -1e9;
function triPolyNote() { if (S.cellKind !== 'triangle' || performance.now() - triNoteAt < 3000) return; triNoteAt = performance.now(); toast('Tri: its corners and sides stay fixed here · continue to Shape › to pull the sides', 2600); }
function chooseMethod(f) {
  if (triView()) { if (TRI_AVAIL[f]) toast(TRI_NOTE[f], 5200); return; }
  if (!S.poly) return;
  const cur = polyCommitted(); if (cur.family && methodOf(cur) === f) return;
  choosePolyCons(f === 'fg' ? (isFG(S.lastFg) ? S.lastFg : FG_ID) : POLY_FAMILY[f][0]);
}
function startTri() {                       // Tri: the equilateral triangle with the app's Rotate (as v5.9), entering Polygon first
  start('rotation-tri', { quiet: true }); S.polyTool = 'edit'; setMode('polygon', true);
  if (!S.seenHint.tri) { S.seenHint.tri = true; toast('Tri · Rotate · its corners and sides stay fixed here · continue to Shape › to pull the sides', 3400); } else toast('Tri · Rotate', 1400);
}
function chooseShape(k) {
  if (k === 'hex') { toast(HEX_NOTE, 3600); return; }
  if ((k === 'tri' && S.cellKind === 'triangle') || (k === 'quad' && S.poly)) return;
  const label = k === 'tri' ? 'Tri' : 'Quad';
  confirmReplace('Start again with ' + label + '?', 'Start with ' + label, k === 'tri' ? startTri : startPolygon);
}
['tri', 'quad', 'hex'].forEach(k => { $('ps-' + k).onclick = () => chooseShape(k); });
{ const _st = start; start = function (id, opts) { S.lastFg = null; _st(id, opts); }; }   // a new tessellation (or an opened project) starts Figure & Ground on Translate
// what each Undo / Redo would change, in words (the histories themselves are untouched)
function histLabel(a) {
  if (!a) return '';
  if (a.kind === 'shape') return 'Shape pull';
  if (a.kind === 'fill') return 'fill';
  if (a.kind === 'stroke') { if (a.layer === 'sketch') return a.tool === 'eraser' ? 'sketch eraser' : 'sketch line';
    return { pen: 'pen line', eraser: 'eraser', dot: 'dots', texture: 'texture' }[a.tool] || 'drawing'; }
  return 'step';
}
function polyStepLabel(a, b) {
  if (!a || !b) return 'Polygon change';
  if (a.consId !== b.consId) return isMirrorId(a.consId) && isMirrorId(b.consId) ? 'Same / Mirrored' : 'construction change';
  const na = nodeCount(a.nodes || {}), nb = nodeCount(b.nodes || {});
  return nb > na ? 'point added' : nb < na ? 'point removed' : !sameCage(a.cage, b.cage) ? 'corner moved' : 'point moved';
}
function polyNext(d) {                      // mirrors polyUndoRedo's choice between the last polygon edit and the last Polygon sketch line
  if (!S.poly) return '';
  if (d < 0) { const pe = S.poly.hp > 0 ? (S.poly.hist[S.poly.hp].seq || 0) : -1, sk = topPolySketch(), ss = sk ? (sk.seq || 0) : -1;
    if (pe < 0 && ss < 0) return consBack('undo') ? 'back to the previous construction' : '';
    return ss > pe ? histLabel(sk) : polyStepLabel(S.poly.hist[S.poly.hp - 1], S.poly.hist[S.poly.hp]); }
  const pe = S.poly.hp < S.poly.hist.length - 1 ? (S.poly.hist[S.poly.hp + 1].seq || 0) : Infinity, sk = nextPolySketch(), ss = sk ? (sk.seq || 0) : Infinity;
  if (pe === Infinity && ss === Infinity) return consBack('redo') ? 'forward to the new construction' : '';
  return ss < pe ? histLabel(sk) : polyStepLabel(S.poly.hist[S.poly.hp], S.poly.hist[S.poly.hp + 1]);
}
function syncHistLabels() {
  const set = (id, verb, what, tail) => { const b = $(id); if (!b) return; const t = b.disabled || !what ? 'Nothing to ' + verb.toLowerCase() : verb + ' ' + what + (tail || ''); b.setAttribute('aria-label', t); b.title = t; };
  const tri = triView(); set('pb-undo', 'Undo', tri ? '' : polyNext(-1)); set('pb-redo', 'Redo', tri ? '' : polyNext(1));
  const mu = histLabel(S.hp > 0 ? S.history[S.hp - 1] : null), mr = histLabel(S.hp < S.history.length ? S.history[S.hp] : null), tail = S.mode === 'tessellate' ? ' (drawing)' : '';
  set('sb-undo', 'Undo', mu); set('sb-redo', 'Redo', mr); set('undo', 'Undo', mu, tail); set('redo', 'Redo', mr, tail);
}
function stepMain(d) {                      // Shape · Illustrate · Tessellate: exactly v5.9's history step, then a short note saying what changed
  const a = d < 0 ? (S.hp > 0 ? S.history[S.hp - 1] : null) : (S.hp < S.history.length ? S.history[S.hp] : null), hp = S.hp;
  applyHistory(d); if (S.hp !== hp && a) toast((d < 0 ? 'Undone: ' : 'Redone: ') + histLabel(a) + (S.mode === 'tessellate' ? ' (drawing)' : ''), 1400);
}
function stepPoly(d) {                      // Polygon: exactly v5.9's Polygon timeline (and its swap back to the previous construction, which has its own note)
  if (!S.poly) return; const what = polyNext(d), swap = /construction$/.test(what), key = () => [S.poly && S.poly.hp, S.hp, S.consId].join('|'), before = key();
  polyUndoRedo(d); if (what && !swap && key() !== before) toast((d < 0 ? 'Undone: ' : 'Redone: ') + what, 1400);
}
$('pb-undo').onclick = () => stepPoly(-1); $('pb-redo').onclick = () => stepPoly(1);
$('sb-undo').onclick = () => stepMain(-1); $('sb-redo').onclick = () => stepMain(1);
$('undo').onclick = () => stepMain(-1); $('redo').onclick = () => stepMain(1);
{ const _su = syncUndo; syncUndo = function () { _su(); syncHistLabels(); }; }
{ const _sp = syncPolyButtons; syncPolyButtons = function () { _sp(); syncHistLabels(); }; }
// the fitted view clears the (taller) Polygon panel: on a short screen a tall unit is zoomed out just enough; the centre never moves, so Polygon
// and Shape keep sharing one view (v4.4), and the Tessellate view and the exports (fitS) are exactly v5.9's
let polyPanelH = 152;
{ const _fc = fitCamera; fitCamera = function () {
    _fc(); if (!S.field || (S.mode !== 'polygon' && S.mode !== 'shape')) return;
    const st = $('strip-polygon'); if (S.mode === 'polygon' && st.offsetHeight) polyPanelH = st.offsetHeight;
    const lower = S.vh - 10 - polyPanelH - 6, upper = $('stagenav').getBoundingClientRect().bottom + 6;
    const pts = S.fg ? (() => { const f = fgPolys(); return f.A.concat(f.B); })() : edgesNow().flatMap(e => e.pts); let lo = -Infinity, hi = Infinity;
    pts.forEach(p => { const y = w2s(p).y; if (y > lo) lo = y; if (y < hi) hi = y; });
    const k = Math.min(1, lo > S.cy ? (lower - S.cy) / (lo - S.cy) : 1, hi < S.cy ? (S.cy - upper) / (S.cy - hi) : 1);
    if (k < 1 && k > 0.4) { S.cam.s *= k; clampCam(); invalidate(); }
  }; }
function placeHist() {                      // Illustrate and Tessellate share one Undo / Redo pair: it sits at the top-left of whichever panel is showing
  const t = S.mode === 'tessellate' ? $('hist-ts') : $('hist-il'); if ($('undo').parentNode !== t) { t.appendChild($('undo')); t.appendChild($('redo')); }
}
// the Polygon panel: starting shape, method, sub-method; what is unavailable is shown and explained
function ph1Sync() {
  const tri = triView(), st = S.poly && S.poly.family ? polyCommitted() : null, m = tri ? 'rotate' : methodOf(st), sk = S.mode === 'polygon' && S.polyTool === 'sketch' && !!S.poly;
  $('ps-tri').setAttribute('aria-pressed', String(S.cellKind === 'triangle')); $('ps-quad').setAttribute('aria-pressed', String(S.cellKind === 'square'));
  $('ps-shape').classList.toggle('compact', !$('pb-count').hidden);
  Object.keys(METHOD_NAME).forEach(f => { const b = $('pf-' + f), av = tri ? TRI_AVAIL[f] : null;
    b.setAttribute('aria-pressed', String(f === m));
    if (av) { b.dataset.avail = av; b.setAttribute('aria-disabled', 'true'); } else { delete b.dataset.avail; b.removeAttribute('aria-disabled'); }
    b.setAttribute('aria-label', METHOD_NAME[f] + (f === 'fg' ? ': two complementary figures' : '') + (av === 'no' ? ' (not possible with Tri)' : av === 'later' ? ' (not in this app yet)' : '')); });
  if (S.poly) {
    const fg = !!st && isFG(st.consId); if (fg) S.lastFg = st.consId;
    $('pb-sec-fg').hidden = !fg || sk; if (fg) { $('pb-sec-mirror').hidden = true; $('pb-hint').hidden = true; }
    document.querySelectorAll('#pb-sec-fg button').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.id === S.consId)));
  } else if (tri) {
    ['rotate', 'glide', 'mirror', 'fg'].forEach(k => { $('pb-sec-' + k).hidden = true; });
    $('pb-hint').hidden = false; $('pb-hint').textContent = '60° about a corner · half-turn on the third side · fixed here';
    $('pb-sketch').disabled = true; $('pb-sketch').setAttribute('aria-pressed', 'false'); $('pb-next').disabled = false; $('pb-count').hidden = true;
    $('pb-undo').disabled = true; $('pb-redo').disabled = true;
  }
  syncHistLabels();
}
{ const _spu = syncPolyUI; syncPolyUI = function () { _spu(); ph1Sync(); }; }
placeSketchTools = function () {            // (PH1) Polygon › Sketch: Pen / Eraser take the starting shape's place; the methods dim; the size uses row 3
  const tools = $('sketch-tools'), seg = $('seg-sketch'); if (!tools || !seg) return;
  const pbSub = document.querySelector('#strip-polygon .pb-sub'), row1 = document.querySelector('#pb-tools .pb-row1'), meth = document.querySelector('#pb-tools .pb-methods'), shapes = $('ps-shape');
  if (S.mode === 'polygon' && S.polyTool === 'sketch' && S.poly) {
    if (seg.parentNode !== row1) row1.insertBefore(seg, shapes); if (tools.parentNode !== pbSub) pbSub.appendChild(tools); tools.hidden = false; shapes.hidden = true; meth.classList.add('off');
  } else {
    if (seg.parentNode !== tools) tools.insertBefore(seg, tools.firstChild); const home = $('sb-tools').querySelector('.sb-row2'); if (tools.parentNode !== home) home.appendChild(tools);
    tools.hidden = S.shapeTool !== 'sketch'; shapes.hidden = false; meth.classList.remove('off');
  }
};
{ const _sm = setMode; setMode = function (m, quiet) {
    const from = S.mode; _sm(m, quiet); placeHist();
    if (S.mode === 'polygon') { if (triView()) { if (S.polyTool === 'sketch') { S.polyTool = 'edit'; placeSketchTools(); } if (!quiet && from !== 'polygon') triPolyNote(); } syncPolyUI(); }
    syncHistLabels(); }; }
// the menu: ☰ › main page · Construction settings · Help / About
function menuPage(id) { ['menu-main', 'menu-settings', 'menu-help'].forEach(k => { $(k).hidden = k !== id; }); $('menu').scrollTop = 0; }
$('m-settings').onclick = () => menuPage('menu-settings'); $('m-help').onclick = () => menuPage('menu-help');
$('m-back-s').onclick = () => menuPage('menu-main'); $('m-back-h').onclick = () => menuPage('menu-main');
$('more').addEventListener('click', () => { if (!$('menu').hidden) menuPage('menu-main'); });   // the menu always opens on its main page
$('scrim').addEventListener('pointerup', () => { if (!$('menu').hidden) closeMenu(); });   // (iOS Safari gives no click on this layer: a tap outside the menu closes it on release)
$('m-rules').onclick = () => { closeMenu(); openRules(); };
const LATER = { 'm-gallery': 'My Gallery is coming later (Phase 2) · for now, Save project file keeps a copy', 'm-backup': 'Backup / Restore is coming later (Phase 2) · for now, Save project file keeps a copy', 'm-test': 'Test mode is coming later (Phase 5)' };
Object.keys(LATER).forEach(id => { $(id).onclick = () => { closeMenu(); toast(LATER[id], 3400); }; });
$('m-version').textContent = 'Version ' + BUILD + ' · classroom release';
function shapeName() {
  if (S.cellKind === 'triangle') return 'Triangle'; if (S.cellKind === 'rhombus') return 'Rhombus (experimental)'; if (S.fg) return 'Quadrilateral';
  let k = 'square'; try { if (S.cageNow && !isSquare(S.cageNow)) k = cageKind(S.consId) === 'rectangle' ? 'rectangle' : 'parallelogram'; } catch (_) {}
  return 'Quadrilateral (' + k + ')';
}
updateTitle = function () { $('menu-title').textContent = shapeName() + ' · ' + (S.poly && !S.poly.family ? 'choose a method' : consLabel(S.consId)) + (compModified() ? ' · composed' : ''); };
{ const _cp = captureProject; captureProject = function () { const p = _cp(); if (triView() && p && p.view && p.view.stage === 'polygon') p.view.stage = 'shape'; return p; }; }   // (Tri's Polygon view is saved as Shape, as v5.9 would)
// the start screen: Tri · Quad · Hex (coming later)
function hexPreviewSVG() { return '<svg viewBox="0 0 160 120" aria-hidden="true"><path d="M58 22h44l22 38-22 38H58L36 60Z" fill="rgba(247,241,227,.28)" stroke="rgba(255,255,255,.45)" stroke-width="2" stroke-dasharray="5 4"/></svg>'; }
const STARTS = [
  { key: 'tri', label: 'Tri', full: 'Triangle · starts equilateral', hint: 'Rotate · more methods later', pic: () => previewShapeSVG(CONS.find(c => c.id === 'rotation-tri')), go: () => startTri() },
  { key: 'quad', label: 'Quad', full: 'Quadrilateral · starts as a square', hint: 'Five construction methods; the corners follow each method', pic: () => previewPolygonSVG(), go: () => startPolygon() },
  { key: 'hex', label: 'Hex', full: 'Hexagon', hint: 'Coming later', later: true, pic: hexPreviewSVG } ];
{ const _se = showEntry; showEntry = function (step, key) {
    if (step !== 1) return _se(step, key);
    $('lab').hidden = $('about').hidden = true; $('entry').hidden = false; $('entry').scrollTop = 0;
    const body = $('entry-body'); body.innerHTML = ''; S.entryStep = 1;
    $('entry-title').textContent = 'Choose a starting shape'; $('entry-sub').textContent = 'Everything you draw will repeat across the plane.';
    $('entry-back').hidden = !S.field; $('entry-back').onclick = () => { $('entry').hidden = true; };
    resumeCard(body);
    const grid = document.createElement('div'); grid.className = 'grid';
    STARTS.forEach(sh => { const b = document.createElement('button'); b.className = 'card' + (sh.later ? ' later' : ''); b.id = 'start-' + sh.key;
      b.setAttribute('aria-label', sh.label + ': ' + sh.full + (sh.later ? ', coming later' : '')); if (sh.later) b.setAttribute('aria-disabled', 'true');
      b.innerHTML = sh.pic() + `<b>${sh.label}${sh.later ? '<span class="tag">COMING LATER</span>' : ''}</b><span><span class="full">${sh.full}</span><br>${sh.hint}</span>`;
      b.onclick = sh.later ? () => toast(HEX_NOTE, 3600) : () => beginNew(sh.go); grid.appendChild(b); });
    body.appendChild(grid); openRow(body);
  }; }

/* ================= PH2 · MY GALLERY, OPEN, ONE RECOVERY STATE, BACKUP / RESTORE (v5.11, approved 1 Nov) =================
 * Design: tessellation-development-phases/phase2/PHASE2_PROPOSAL.md (rev 1) with your refinements of 1 Nov.
 *   • Unfinished work is the automatic save, UNCHANGED: project.js and its database are untouched, and so are the Continue card and its picture.
 *     Its slot information also remembers which Gallery entry the work belongs to: { gallery: { id, name, updated, check } } (older builds ignore it).
 *   • My Gallery is gallery.js, a database of its own. Only Save to Gallery, Rename, Duplicate, Delete and Restore change it.
 *   • "Changed since saved" compares contentCheck(): the project's file text without its view, tools, hints, time, summary and process recording,
 *     so moving the view, changing stage or tool is not a change; drawing, shaping, the polygon, fills, colours and the reference photo are.
 *   • The pictures are drawn by drawScene into an off-screen canvas framed on the tile (as image export does), never copied from the screen.
 *   • Nothing in the Gallery changes until a whole file, a whole restore or a whole save has been checked; each change is one transaction. */
const GAL = window.TessGallery, BACKUP_FORMAT = 'tessellation-gallery-backup', BACKUP_VERSION = 1, THUMB = 320;
S.gallery = null; S.importName = '';
let galCards = [], galMode = 'gallery', galView = store.get('tessellation.galleryView', 'tile') === 'pattern' ? 'pattern' : 'tile';
const VOLATILE = ['saved', 'app', 'summary', 'view', 'tools', 'hints', 'process'];
function hashF64(a) { if (!(a instanceof Float64Array)) return 'x'; const u = new Uint32Array(a.buffer, a.byteOffset, a.length * 2); let h = 0x811c9dc5; for (let i = 0; i < u.length; i++) { h ^= u[i]; h = Math.imul(h, 0x01000193) >>> 0; } return h.toString(16) + ':' + a.length; }
function contentCheck(p) {                 // what the learner made, independent of the view and of the stage they happen to be in
  const snaps = p.snapshots || [], ref = i => i === null || i === undefined ? null : 's' + hashF64(snaps[i]);   // boundaries by their content, not their place in the table
  const o = {}; Object.keys(p).forEach(k => { if (!VOLATILE.includes(k) && k !== 'snapshots') o[k] = p[k]; });
  if (p.geometry) { const g = Object.assign({}, p.geometry), poly = p.polygon ? Object.assign({}, p.polygon) : null;
    if (poly && poly.shapeAside !== null && poly.shapeAside !== undefined) g.boundary = poly.shapeAside;   // the Polygon view sets Shape's curves aside and Shape brings them back: not a change
    g.boundary = ref(g.boundary); g.shapeStart = poly ? null : ref(g.shapeStart); o.geometry = g;   // (with a polygon, Shape's starting outline is the polygon when Shape was built: it follows from the polygon's history)
    if (poly) { poly.shapeAside = null; delete poly.shapeBuiltOn; delete poly.changeConfirmed; o.polygon = poly; } }   // (bookkeeping of the Polygon → Shape handoff; a real polygon change is in its history)
  if (Array.isArray(p.steps)) o.steps = p.steps.map(st => { if (!st || !('before' in st || 'after' in st || 'snap' in st)) return st; const c = Object.assign({}, st); ['before', 'after', 'snap'].forEach(k => { if (k in c) c[k] = ref(c[k]); }); return c; });
  if (p.previousVersion) { const v = Object.assign({}, p.previousVersion); v.shapeStart = ref(v.shapeStart); v.boundary = ref(v.boundary); o.previousVersion = v; }
  return GAL.fnv(TP.toFileText(o));
}
const checkMemo = new WeakMap();
const contentOf = p => { let c = checkMemo.get(p); if (!c) { c = contentCheck(p); checkMemo.set(p, c); } return c; };
const fin = v => typeof v === 'number' && Number.isFinite(v);
const cleanName = (s, d) => { const t = typeof s === 'string' ? s.replace(/[\u0000-\u001f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 80) : ''; return t || d; };
const fileBase = s => (s.replace(/[\\/:*?"<>|\u0000-\u001f]+/g, '-').replace(/\s+/g, ' ').trim().slice(0, 60) || 'tessellation');
function shapeKeyOf(p) {
  const g = p && p.geometry, b = g && g.base, id = g && g.construction && g.construction.id;
  return b === 'triangle' || id === 'rotation-tri' ? 'tri' : b === 'rhombus' || id === 'reflection' ? 'rhombus' : 'quad';
}
function labelOf(p) {
  const g = p.geometry, id = g && g.construction && g.construction.id, sh = shapeKeyOf(p), head = sh === 'tri' ? 'Tri' : sh === 'rhombus' ? 'Rhombus' : 'Quad';
  if (g && g.path === 'polygon' && !g.rule) return head + ' · Polygon';
  return CARD[id] ? CARD[id].short.replace(' (experimental)', '') : head + ' · ' + id;
}
const stageOf = p => (p.view && STAGE_NAME[p.view.stage]) ? p.view.stage : 'shape';
function uniqueName(base, skipId) {
  const names = new Set(galCards.filter(c => c.id !== skipId).map(c => c.name.toLowerCase())); if (!names.has(base.toLowerCase())) return base;
  for (let k = 2; k < 1000; k++) { const n = base + ' ' + k; if (!names.has(n.toLowerCase())) return n; } return base;
}
const okThumb = s => typeof s === 'string' && s.length < 600000 && /^data:image\/(jpeg|png);base64,[A-Za-z0-9+/]+=*$/.test(s);
const NO_PIC = 'data:image/svg+xml;charset=utf-8,' + encodeURIComponent('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 10 10"><rect width="10" height="10" fill="#0d1422"/></svg>');
const picOf = c => { const t = c.thumbs || {}; return okThumb(t[galView]) ? t[galView] : okThumb(t.tile) ? t.tile : NO_PIC; };

/* ---- the pictures: the developed tile (Tile) and the repeated pattern (Pattern), drawn from the tile with the app's own drawing ---- */
function drawThumb(kind) {
  if (!S.field || !S.path) return null;
  const c = document.createElement('canvas'); c.width = c.height = THUMB; const x = c.getContext('2d'); if (!x) return null;
  const tile = kind === 'tile', poly = E.polygon(edgesNow()); let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
  poly.forEach(p => { if (p.x < x0) x0 = p.x; if (p.x > x1) x1 = p.x; if (p.y < y0) y0 = p.y; if (p.y > y1) y1 = p.y; });
  const hidden = tile && (S.fg ? (() => { const f = fgComp(0); return !!(f.A && f.A.hidden && f.B && f.B.hidden); })() : !!(compOf(0) && compOf(0).hidden));
  const sv = { ctx, dpr: S.dpr, fast: S.fast, vw: S.vw, vh: S.vh, cx: S.cx, cy: S.cy, cam: S.cam, mode: S.mode, sel: S.sel, exp: EXP }; let ok = false;
  try {
    ctx = x; S.dpr = 1; S.fast = false; S.vw = S.vh = THUMB; S.cx = S.cy = THUMB / 2; S.sel = null;
    S.mode = hidden ? 'illustrate' : 'tessellate'; EXP = { scale: 1, transparent: false, sketch: false, tileOnly: tile };
    if (tile) { const w = Math.max(x1 - x0, y1 - y0) || 1; S.cam = { x: (x0 + x1) / 2, y: (y0 + y1) / 2, s: THUMB * 0.84 / w }; }
    else { const size = S.fg ? FG_FIT * S.unit : S.field.size; S.cam = { x: S.cent.x, y: S.cent.y, s: THUMB / (2.6 * size) }; }
    drawScene(THUMB, THUMB); ok = true;
  } catch (e) { console.warn('thumbnail:', e); }
  finally { ctx = sv.ctx; S.dpr = sv.dpr; S.fast = sv.fast; S.vw = sv.vw; S.vh = sv.vh; S.cx = sv.cx; S.cy = sv.cy; S.cam = sv.cam; S.mode = sv.mode; S.sel = sv.sel; EXP = sv.exp; invalidate(); }
  if (!ok) return null; try { return c.toDataURL('image/jpeg', 0.85); } catch (_) { return null; }
}
const thumbsNow = () => ({ tile: drawThumb('tile'), pattern: drawThumb('pattern') });
function outlineThumb(p) {                 // only when a picture is missing or damaged: the tile's outline from the boundary stored in the project
  try {
    const g = p.geometry, a = p.snapshots && p.snapshots[g.boundary], n = g.samplesPerSide, sides = g.sides; if (!(a instanceof Float64Array) || !n || !sides) return null;
    const two = !!g.unit && g.unit.tiles === 2, outer = two ? sides - 1 : sides, pt = (s, i) => P(a[2 * (s * n + i)], a[2 * (s * n + i) + 1]), pts = [];
    for (let s = 0; s < outer; s++) for (let i = 0; i < n - 1; i++) pts.push(pt(s, i));
    let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity; pts.forEach(q => { x0 = Math.min(x0, q.x); x1 = Math.max(x1, q.x); y0 = Math.min(y0, q.y); y1 = Math.max(y1, q.y); });
    const k = THUMB * 0.84 / (Math.max(x1 - x0, y1 - y0) || 1), X = q => THUMB / 2 + (q.x - (x0 + x1) / 2) * k, Y = q => THUMB / 2 - (q.y - (y0 + y1) / 2) * k;
    const c = document.createElement('canvas'); c.width = c.height = THUMB; const x = c.getContext('2d');
    x.fillStyle = COLORS.bg; x.fillRect(0, 0, THUMB, THUMB); x.beginPath(); pts.forEach((q, i) => i ? x.lineTo(X(q), Y(q)) : x.moveTo(X(q), Y(q))); x.closePath();
    x.fillStyle = COLORS.fill; x.fill(); x.lineJoin = 'round'; x.lineWidth = 2; x.strokeStyle = COLORS.line; x.stroke();
    if (two) { x.beginPath(); for (let i = 0; i < n; i++) { const q = pt(outer, i); i ? x.lineTo(X(q), Y(q)) : x.moveTo(X(q), Y(q)); } x.stroke(); }
    return c.toDataURL('image/jpeg', 0.85);
  } catch (_) { return null; }
}

/* ---- the Gallery list and the link between the open work and its Gallery entry ---- */
const validCard = c => !!c && typeof c.id === 'string' && typeof c.name === 'string' && fin(c.updated);
async function galRefresh() {
  if (GAL.state.ok !== true) { galCards = []; syncGalMenu(); return galCards; }
  try { galCards = (await GAL.list()).filter(validCard).sort((a, b) => b.updated - a.updated); } catch (e) { console.warn('gallery:', e); galCards = []; }
  syncGalMenu(); return galCards;
}
function linkState(p) {                    // the open work: 'none' (not from the Gallery) · 'gone' (its entry was deleted) · 'saved' · 'changed'
  const L = S.gallery; if (!L || !S.field) return 'none'; if (!galCards.some(c => c.id === L.id)) return 'gone';
  return contentCheck(p || captureProject()) === L.check ? 'saved' : 'changed';
}
function storedState() {                   // the kept unfinished work, seen from the start screen: 'none' · 'out' (not in the Gallery) · 'saved' · 'changed'
  const info = storedInfo(); if (!info) return 'none'; const L = info.gallery;
  if (!L || typeof L.id !== 'string' || !galCards.some(c => c.id === L.id)) return 'out';
  const p = keep.stored && keep.stored.project; return p && contentOf(p) === L.check ? 'saved' : 'changed';
}
function syncGalMenu(deep) {
  const n = galCards.length; $('m-gallery-n').textContent = GAL.state.ok === false ? 'not available' : n ? String(n) : '';
  const el = $('m-gstat'); if (!S.field) { el.hidden = true; return; } el.hidden = false;
  const st = deep ? linkState() : (S.gallery ? (galCards.some(c => c.id === S.gallery.id) ? 'linked' : 'gone') : 'none');
  el.classList.toggle('warn', st === 'changed');
  el.textContent = st === 'saved' ? 'Saved in My Gallery as “' + S.gallery.name + '”' : st === 'changed' ? 'Changes to “' + S.gallery.name + '” not saved to My Gallery'
    : st === 'linked' ? 'In My Gallery as “' + S.gallery.name + '”' : 'Not in My Gallery · ☰ › Save to Gallery keeps it';
}
$('more').addEventListener('click', () => { if (!$('menu').hidden) syncGalMenu(true); });

/* ---- one dialog for every Gallery question: buttons with ids; resolves { id, value } (Cancel → id null) ---- */
let gAskEnd = null;
function gAsk(o) {
  return new Promise(resolve => {
    if (gAskEnd) gAskEnd(null);
    $('gdlg-title').textContent = o.title; const body = $('gdlg-body'); body.innerHTML = o.html || ''; const acts = $('gdlg-acts'); acts.innerHTML = '';
    const inp = body.querySelector('input');
    const end = id => { if (gAskEnd !== end) return; gAskEnd = null; const value = inp ? inp.value : ''; $('gdlg').hidden = true; if (o.now) o.now(id); resolve({ id, value }); };   // (o.now runs inside the tap itself, as v5.10's questions did)
    gAskEnd = end;
    const add = (id, label, cls, sub) => { const b = document.createElement('button'); b.id = 'gdlg-' + id; if (cls) b.className = cls; b.innerHTML = esc(label) + (sub ? '<small>' + esc(sub) + '</small>' : ''); b.onclick = () => end(id === 'cancel' ? null : id); acts.appendChild(b); return b; };
    (o.buttons || []).forEach(b => add(b.id, b.label, b.kind, b.sub));
    if (o.cancel !== false) add('cancel', o.cancel || 'Cancel');
    if (o.link) add(o.link.id, o.link.label, 'link');
    $('gdlg').hidden = false;
    if (inp) { inp.addEventListener('keydown', e => { if (e.key !== 'Enter') return; e.preventDefault(); const p = (o.buttons || []).find(b => b.kind === 'primary'); if (p) end(p.id); });
      setTimeout(() => { try { inp.focus(); inp.setSelectionRange(0, inp.value.length); } catch (_) {} }, 60); }
  });
}
function handFile(parts, name) {           // share sheet on a phone or tablet, a download elsewhere → true when handed over
  const blob = new Blob(Array.isArray(parts) ? parts : [parts], { type: 'application/json' }); let file = null;
  try { file = new File([blob], name, { type: 'application/json' }); } catch (_) {}
  if (navigator.maxTouchPoints > 0 && file && navigator.canShare && navigator.canShare({ files: [file] }))
    return navigator.share({ files: [file] }).then(() => true, e => (e && e.name === 'AbortError') ? false : (download(blob, name), true));
  download(blob, name); return Promise.resolve(true);
}
const failSentence = r => /Quota/.test(r.reason || '') ? 'My Gallery is full on this device. Save a backup, then delete projects you no longer need.' : 'It could not be written (' + (r.reason || 'unknown reason') + ').';

/* ---- Save to Gallery: always visible, never silent ---- */
async function writeEntry(id, name, p, thumbs, created, content) {
  const now = Math.max(Date.now(), (galCards.find(c => c.id === id) || {}).updated + 1 || 0), text = TP.toFileText(p);
  const card = { id, name, created: created || now, updated: now, label: labelOf(p), shape: shapeKeyOf(p), construction: p.geometry.construction.id, stage: stageOf(p),
    build: BUILD, bytes: text.length, check: GAL.fnv(text), content, thumbs: { tile: thumbs.tile || outlineThumb(p), pattern: thumbs.pattern || null } };
  const r = await GAL.putEntry(card, p); if (!r.ok) { tell('Not saved to My Gallery', failSentence(r), true); return null; }
  await galRefresh(); return card;
}
async function saveToGallery(o) {          // → true when the work is in My Gallery (saved now, or already up to date)
  o = o || {};
  if (!S.field) { toast('Nothing is open to save', 2000); return false; }
  if (work) cancelWork(); closeMenu();
  if (GAL.state.ok !== true) {
    const r = await gAsk({ title: 'My Gallery is not available', html: '<p>This browser is not keeping My Gallery' + (GAL.state.reason === 'VersionError' || GAL.state.reason === 'newer' ? ' (it was updated by a newer version of the app)' : '') + '. A project file keeps a copy instead.</p>', buttons: [{ id: 'file', label: 'Save as a file…', kind: 'primary' }] });
    if (r.id === 'file') saveProjectFile(null); return false;
  }
  await galRefresh();
  const p = captureProject(), chk = contentCheck(p), thumbs = thumbsNow();
  let L = S.gallery, card = null; if (L) { try { card = await GAL.getCard(L.id); } catch (_) {} if (!card) L = null; }
  const pic = `<div class="gprev"><img src="${thumbs.tile || NO_PIC}" alt=""><div>`;
  const fileLink = { id: 'file', label: 'Save as a file instead…' };
  const asFile = name => { if (name) handFile(TP.toFileText(p), fileBase(name) + '.json').then(ok => ok && toast('Project file saved · ' + fileBase(name) + '.json', 2800)); else saveProjectFile(p); };
  const askName = async (title, def, button) => {
    const r = await gAsk({ title, html: pic + '<b>This picture goes in My Gallery</b>drawn from the tile itself</div></div><label class="gname" for="gdlg-name">Name</label>' +
      `<input type="text" id="gdlg-name" maxlength="80" value="${esc(def)}" autocomplete="off" autocapitalize="sentences" spellcheck="false" enterkeyhint="done">`,
      buttons: [{ id: 'save', label: button || 'Save', kind: 'primary' }], link: fileLink });
    if (r.id === 'file') { asFile(cleanName(r.value, def)); return null; }
    return r.id === 'save' ? cleanName(r.value, def) : null;
  };
  const saveNew = async (name) => {
    const c = await writeEntry(GAL.newId(), name, p, thumbs, 0, chk); if (!c) return false;
    S.gallery = { id: c.id, name: c.name, updated: c.updated, check: chk }; S.importName = ''; markDirty(); syncGalMenu(); toast('Saved to My Gallery · ' + c.name, 2600); return true;
  };
  const update = async () => {
    const c = await writeEntry(card.id, card.name, p, thumbs, card.created, chk); if (!c) return false;
    S.gallery = { id: c.id, name: c.name, updated: c.updated, check: chk }; markDirty(); syncGalMenu(); toast('Updated in My Gallery · ' + c.name, 2600); return true;
  };
  if (!L) { const name = await askName('Save to Gallery', uniqueName(S.importName || labelOf(p))); return name ? saveNew(name) : false; }
  const elsewhere = card.updated !== L.updated, changed = chk !== L.check, nm = esc(card.name);
  if (!elsewhere && !changed) {
    if (o.first) return true;
    const r = await gAsk({ title: 'Save to Gallery', html: pic + `<b>“${nm}” is up to date</b>saved in My Gallery ${esc(when(card.updated))}</div></div>`,
      buttons: [{ id: 'new', label: 'Save as new…' }], cancel: 'Close', link: fileLink });
    if (r.id === 'file') { asFile(card.name); return true; }
    if (r.id !== 'new') return true;
    const name = await askName('Save as new', uniqueName(card.name)); return name ? saveNew(name) : false;
  }
  const html = pic + (elsewhere ? `<b>“${nm}” was changed in My Gallery</b>since you opened it (in another tab, or by a restore). Saved there ${esc(when(card.updated))}.</div></div>`
    : `<b>Opened from “${nm}”</b>saved ${esc(when(card.updated))}<br>You have changed it since.</div></div>`);
  const r = await gAsk({ title: 'Save to Gallery', html, link: fileLink, buttons: elsewhere
    ? [{ id: 'new', label: 'Save as new…', kind: 'primary' }, { id: 'update', label: 'Update “' + card.name + '”…' }]
    : [{ id: 'update', label: 'Update “' + card.name + '”', kind: 'primary', sub: 'replaces the saved version' }, { id: 'new', label: 'Save as new…' }] });
  if (r.id === 'file') { asFile(card.name); return false; }
  if (r.id === 'new') { const name = await askName('Save as new', uniqueName(card.name)); return name ? saveNew(name) : false; }
  if (r.id !== 'update') return false;
  if (elsewhere) { const c2 = await gAsk({ title: 'Replace the newer version?', html: `<p>The version of “${nm}” saved in My Gallery ${esc(when(card.updated))} will be replaced by the work you have open.</p><p class="warn">The replaced version cannot be brought back.</p>`,
    buttons: [{ id: 'yes', label: 'Replace it', kind: 'danger' }] }); if (c2.id !== 'yes') return false; }
  return update();
}

/* ---- opening and starting new never silently discard unsaved work ---- */
confirmReplace = function (title, action, then) {
  const open = hasWorkNow(), info = !S.field ? storedInfo() : null, kept = !!info && (!info.summary || info.summary.hasWork !== false);
  if (!open && !kept) { then(); return; }
  let what;
  if (open) { const st = linkState(); if (st === 'saved') { then(); return; }
    what = st === 'changed' ? 'Your changes to “' + esc(S.gallery.name) + '” are not saved in My Gallery.' : 'Your unfinished work is not in My Gallery.'; }
  else { const st = storedState(); if (st === 'saved') { then(); return; } const sm = info.summary || {};
    what = (st === 'changed' ? 'Your changes to “' + esc(info.gallery.name) + '”' : 'Your unfinished work' + (sm.title ? ' (' + esc(sm.title) + ')' : '')) + ', kept ' + esc(when(info.at)) + ', ' + (st === 'changed' ? 'are' : 'is') + ' not saved in My Gallery.'; }
  gAsk({ title, html: `<p>${what}</p><p class="mute">${esc(action)} will replace it.</p>`, now: id => { if (id === 'go') then(); },
    buttons: [{ id: 'save', label: 'Save to Gallery first', kind: 'primary' }, { id: 'go', label: action + ' without saving' }] }).then(async r => {
    if (r.id !== 'save') return;
    if (!open) { await continueStored(); if (!S.field) return; }      // the kept work is opened (as Continue would), so its picture can be drawn
    if (await saveToGallery({ first: true })) then();
  });
};

/* ---- the start screen: Continue says where the unfinished work stands; Open… leads to the Gallery and Import ---- */
{ const _rc = resumeCard; resumeCard = function (body) {
    const shown = _rc(body), b = $('entry-continue'); if (!b) return shown;
    const info = storedInfo(), st = storedState(), name = info && info.gallery ? info.gallery.name : '', d = b.querySelector('div'), s = document.createElement('span');
    s.className = 'gst' + (st === 'saved' ? ' gok' : ''); s.id = 'entry-gst';
    s.textContent = st === 'saved' ? 'Saved in My Gallery' : st === 'changed' ? 'Changes not saved to My Gallery' : 'Not in My Gallery';
    if (name && st !== 'out') d.querySelector('b').textContent = 'Continue “' + name + '”';
    d.insertBefore(s, d.lastChild); const last = d.lastChild; if (last && /^Saved /.test(last.textContent)) last.textContent = last.textContent.replace(/^Saved /, 'Kept automatically ');   // (not "Saved": the Gallery is where work is saved)
    return shown; }; }
openRow = function (body) { const r = document.createElement('p'); r.className = 'row openrow'; r.innerHTML = '<button id="entry-open">Open… <span class="mute">My Gallery or a project file</span></button>'; body.appendChild(r); r.firstChild.onclick = () => openGallery('open'); };

/* ---- My Gallery and Open: one sheet over one collection ---- */
function openGallery(mode) {
  galMode = mode === 'open' ? 'open' : 'gallery'; closeMenu();
  $('gal-title').textContent = galMode === 'open' ? 'Open' : 'My Gallery'; $('gal-import').hidden = galMode !== 'open';
  $('gallery').hidden = false; $('gallery').scrollTop = 0; hidePop(); renderGallery(); galRefresh().then(renderGallery);
}
function closeGallery() { $('gallery').hidden = true; hidePop(); }
async function renderGallery() {
  const cards = galCards, grid = $('gal-grid'), off = GAL.state.ok !== true; grid.innerHTML = '';
  $('gal-sub').textContent = galMode === 'open' ? 'Open a project saved in My Gallery, or import a project file.' : 'Projects you saved with Save to Gallery, newest first.';
  $('gal-count').textContent = 'My Gallery · ' + cards.length;
  $('gal-v-tile').setAttribute('aria-pressed', String(galView === 'tile')); $('gal-v-pattern').setAttribute('aria-pressed', String(galView === 'pattern'));
  $('gal-note').hidden = !off; if (off) $('gal-note').textContent = 'My Gallery is not available in this browser' + (GAL.state.reason === 'VersionError' || GAL.state.reason === 'newer' ? ' (a newer version of the app updated it; it is left unchanged)' : '') + '. Import project file… and Save as a file still work.';
  cards.forEach(c => {
    const d = document.createElement('div'); d.className = 'gcard' + (S.gallery && S.field && S.gallery.id === c.id ? ' linked' : ''); d.dataset.id = c.id;
    d.innerHTML = `<button class="gopen" aria-label="Open ${esc(c.name)}"><img src="${picOf(c)}" alt=""></button><b>${esc(c.name)}</b><span>${esc(c.label || '')}</span><span>Saved ${esc(when(c.updated))}</span><button class="gmore" aria-label="More for ${esc(c.name)}">···</button>`;
    d.querySelector('.gopen').onclick = () => openFromGallery(c.id);
    d.querySelector('.gmore').onclick = e => { e.stopPropagation(); showPop(c, e.currentTarget); };
    grid.appendChild(d);
  });
  $('gal-empty').hidden = cards.length > 0 || off;
  let bk = null; if (!off) { try { bk = await GAL.getMeta('backup'); } catch (_) {} }
  const newest = cards.length ? cards[0].updated : 0, since = bk && fin(bk.at) && newest > bk.at;
  $('gal-foot').innerHTML = 'My Gallery is kept in this browser on this device. ' + (!bk || !fin(bk.at) ? (cards.length ? '<b>Last backup: never</b>' : 'Last backup: never')
    : since ? '<b>Changed since the last backup (' + esc(when(bk.at)) + ')</b>' : 'Last backup: ' + esc(when(bk.at))) + ' · ☰ › Backup / Restore keeps a safety copy.';
}
$('gal-back').onclick = closeGallery;
$('gal-import').onclick = () => $('projfile').click();
$('gal-v-tile').onclick = () => { galView = 'tile'; store.set('tessellation.galleryView', galView); renderGallery(); };
$('gal-v-pattern').onclick = () => { galView = 'pattern'; store.set('tessellation.galleryView', galView); renderGallery(); };
async function openFromGallery(id) {
  hidePop(); let card = null, p = null;
  try { [card, p] = await Promise.all([GAL.getCard(id), GAL.getProject(id)]); } catch (_) {}
  if (!card || !p) { tell('Can’t open this project', 'It could not be read from My Gallery.'); return 'refused'; }
  const chk = TP.checkProject(p); if (chk.problem) { tell('Can’t open this project', chk.problem); return 'refused'; }
  try { decodeProject(chk.project); } catch (e) { tell('Can’t open this project', decodeProblem(e)); return 'refused'; }
  if (S.field && S.gallery && S.gallery.id === id && linkState() === 'saved') { closeGallery(); toast('Already open · ' + card.name, 1800); return 'open'; }
  return new Promise(resolve => confirmReplace('Open “' + card.name + '”?', 'Open', async () => {
    const why = await applyProject(chk.project);
    if (why) { tell('Can’t open this project', why); resolve('failed'); return; }
    keep.stored = null; S.gallery = { id, name: card.name, updated: card.updated, check: contentCheck(captureProject()) };
    closeGallery(); markDirty(); syncGalMenu(); toast('Opened · ' + card.name, 1800); resolve('opened');
  }));
}
// ⋯ on a card: Rename · Duplicate · Save as file… · Delete…
let popCard = null, popFile = null, popSwallow = false;
function showPop(c, btn) {
  const pop = $('gpop'), sh = $('gallery'); popCard = c; popFile = null; pop.hidden = false;
  const r = btn.getBoundingClientRect(), s = sh.getBoundingClientRect(), w = pop.offsetWidth, h = pop.offsetHeight;
  let top = r.bottom - s.top + sh.scrollTop + 4; if (r.bottom + h + 8 > s.bottom) top = r.top - s.top + sh.scrollTop - h - 4;
  pop.style.left = Math.max(8, Math.min(sh.clientWidth - w - 8, r.right - s.left - w)) + 'px'; pop.style.top = Math.max(8, top) + 'px';
  GAL.getProject(c.id).then(p => { if (popCard === c && p) popFile = { id: c.id, text: TP.toFileText(p) }; }).catch(() => {});   // ready before Save as file… is tapped (the share sheet needs that)
}
function hidePop() { $('gpop').hidden = true; popCard = null; }
$('gallery').addEventListener('pointerdown', e => { popSwallow = false; if (!$('gpop').hidden && !e.target.closest('#gpop') && !e.target.closest('.gmore')) { hidePop(); popSwallow = true; } }, true);
$('gallery').addEventListener('click', e => { if (popSwallow) { popSwallow = false; e.stopPropagation(); e.preventDefault(); } }, true);
$('gpop').addEventListener('click', e => { const b = e.target.closest('button'); if (!b || !popCard) return; const c = popCard, act = b.dataset.act;
  if (act === 'file') { if (popFile && popFile.id === c.id) { const n = fileBase(c.name) + '.json', t = popFile.text; hidePop(); handFile(t, n).then(ok => ok && toast('Project file saved · ' + n, 2800)); } else toast('Preparing the file… tap again', 1600); return; }
  hidePop(); ({ rename: renameEntry, duplicate: duplicateEntry, delete: deleteEntry })[act](c.id); });
async function renameEntry(id) {
  const c0 = galCards.find(c => c.id === id); if (!c0) return;
  const r = await gAsk({ title: 'Rename', html: `<label class="gname" for="gdlg-name">Name</label><input type="text" id="gdlg-name" maxlength="80" value="${esc(c0.name)}" autocomplete="off" autocapitalize="sentences" spellcheck="false" enterkeyhint="done">`,
    buttons: [{ id: 'ok', label: 'Rename', kind: 'primary' }] });
  if (r.id !== 'ok') return; const name = cleanName(r.value, c0.name); if (name === c0.name) return;
  const card = await GAL.getCard(id); if (!card) return; const w = await GAL.write([{ store: 'cards', put: Object.assign({}, card, { name }), key: id }]);
  if (!w.ok) { tell('Not renamed', failSentence(w), true); return; }
  if (S.gallery && S.gallery.id === id) { S.gallery.name = name; markDirty(); }
  await galRefresh(); renderGallery(); toast('Renamed · ' + name, 1800);
}
async function duplicateEntry(id) {
  let card = null, p = null; try { [card, p] = await Promise.all([GAL.getCard(id), GAL.getProject(id)]); } catch (_) {}
  if (!card || !p) { tell('Not duplicated', 'The project could not be read from My Gallery.'); return; }
  const now = Date.now(), copy = Object.assign({}, card, { id: GAL.newId(), name: uniqueName(cleanName(card.name + ' copy', 'copy')), created: now, updated: now });
  const w = await GAL.putEntry(copy, p); if (!w.ok) { tell('Not duplicated', failSentence(w), true); return; }
  await galRefresh(); renderGallery(); toast('Duplicated · ' + copy.name, 1800);
}
async function deleteEntry(id) {
  const c0 = galCards.find(c => c.id === id); if (!c0) return; const nm = esc(c0.name); let bk0 = null; try { bk0 = await GAL.getMeta('backup'); } catch (_) {}
  const inBackup = bk0 && fin(bk0.at) && fin(c0.created) && bk0.at >= c0.created;
  const r = await gAsk({ title: 'Delete “' + c0.name + '”?', html: `<p>This permanently deletes “${nm}” from My Gallery on this device.</p><p class="warn"><b>It cannot be undone.</b></p><p class="mute">${inBackup ? 'The Gallery backup saved ' + esc(when(bk0.at)) + ' still contains it, as it was then.' : 'No Gallery backup contains it.'}</p>`,
    buttons: [{ id: 'del', label: 'Delete permanently', kind: 'danger' }] });
  if (r.id !== 'del') return;
  const w = await GAL.delEntry(id); if (!w.ok) { tell('Not deleted', failSentence(w), true); return; }
  if (S.gallery && S.gallery.id === id) { S.gallery = null; markDirty(); }          // the open work stays open, as unfinished work
  await galRefresh(); renderGallery(); toast('Deleted · ' + c0.name, 1800);
}

/* ---- Import project file… (opens it for editing; Save to Gallery adds it) — a backup chosen here goes to Restore ---- */
const sniff = text => { const h = text.slice(0, 600); return /^\s*\{\s*"format"\s*:\s*"tessellation-gallery-backup"/.test(h) ? 'backup' : /"format"\s*:\s*"tessellation-project"/.test(h) ? 'project' : 'other'; };
$('projfile').onchange = async e => {
  const f = e.target.files && e.target.files[0]; e.target.value = ''; if (!f) return;
  if (f.size > 300e6) { tell('Can’t open this file', 'This file is too large to be a tessellation project.'); return; }
  let text; try { text = await f.text(); } catch (_) { tell('Can’t open this file', 'The file could not be read.'); return; }
  if (sniff(text) === 'backup') { const n = (/"count"\s*:\s*(\d+)/.exec(text.slice(0, 600)) || [])[1];
    const r = await gAsk({ title: 'This is a Gallery backup', html: `<p>“${esc(f.name)}” is a backup of My Gallery${n ? ' with ' + n + ' project' + (n === '1' ? '' : 's') : ''}, not a single project.</p><p class="mute">Restore adds its projects to My Gallery; you see them first.</p>`,
      buttons: [{ id: 'restore', label: 'Restore…', kind: 'primary' }] });
    if (r.id === 'restore') { closeGallery(); startRestore(text, f.name); } return; }
  if (f.size > 80e6) { tell('Can’t open this file', 'This file is too large to be a tessellation project.'); return; }
  const res = await openProjectText(text);
  if (res === 'opened') { S.importName = cleanName(f.name.replace(/\.json$/i, ''), ''); closeGallery(); syncGalMenu(); toast('Opened for editing · ☰ › Save to Gallery keeps it in My Gallery', 3600); }
};

/* ---- Backup: one versioned file with every Gallery project (unfinished work that is only kept automatically is not in it) ---- */
let bk = null;
const mb = n => n < 1e6 ? Math.max(1, Math.round(n / 1e3)) + ' KB' : (n / 1e6).toFixed(1) + ' MB';
async function openBackup() {
  closeMenu(); $('gbackup').hidden = false; $('gbackup').scrollTop = 0; bk = null; const btn = $('gb-save'), note = $('gb-note');
  btn.disabled = true; btn.textContent = 'Preparing…'; note.hidden = true;
  if (GAL.state.ok !== true) { $('gb-what').textContent = 'My Gallery is not available in this browser.'; btn.textContent = 'Nothing to back up'; return; }
  await galRefresh(); const n = galCards.length, bytes = galCards.reduce((s, c) => s + (c.bytes || 0), 0); let last = null; try { last = await GAL.getMeta('backup'); } catch (_) {}
  $('gb-what').innerHTML = `<b>My Gallery · ${n} project${n === 1 ? '' : 's'}</b>${n ? ' · about ' + mb(bytes) : ''}<br><span class="mute">Last backup: ${last && fin(last.at) ? esc(when(last.at)) : 'never'}</span>`;
  const openOut = S.field && hasWorkNow() && linkState() !== 'saved', keptOut = !S.field && storedInfo() && storedState() !== 'saved' && storedState() !== 'none';
  if (openOut || keptOut) { note.hidden = false; note.innerHTML = (openOut && S.gallery && linkState() === 'changed' ? 'Your changes to “' + esc(S.gallery.name) + '” are' : 'Your unfinished work is') + ' not saved in My Gallery, so ' + (openOut && S.gallery && linkState() === 'changed' ? 'they' : 'it') + ' will not be in the backup' + (openOut ? ' · <u id="gb-savefirst" role="button">Save to Gallery first</u>' : '') + '.';
    const sf = $('gb-savefirst'); if (sf) sf.onclick = async () => { $('gbackup').hidden = true; if (await saveToGallery()) openBackup(); }; }
  if (!n) { btn.textContent = 'Nothing to back up yet'; return; }
  try { bk = await buildBackup(); btn.disabled = false; btn.textContent = 'Save backup…'; } catch (e) { console.warn('backup:', e); btn.textContent = 'The backup could not be made'; }
}
async function buildBackup() {
  const cards = galCards.slice(), saved = new Date(), parts = [], head = JSON.stringify({ format: BACKUP_FORMAT, version: BACKUP_VERSION, saved: saved.toISOString(), app: { name: 'Escher tessellation workspace', build: BUILD }, count: cards.length });
  parts.push(head.slice(0, -1) + ',"projects":['); let bytes = 0;
  for (let k = 0; k < cards.length; k++) {
    const c = cards[k], p = await GAL.getProject(c.id); if (!p) throw new Error('the project “' + c.name + '” could not be read');
    const text = TP.toFileText(p), meta = JSON.stringify({ id: c.id, name: c.name, created: c.created, updated: c.updated, label: c.label, shape: c.shape, construction: c.construction, stage: c.stage, build: c.build, check: GAL.fnv(text), thumbs: c.thumbs || {} });
    parts.push((k ? ',' : '') + meta.slice(0, -1) + ',"project":' + text + '}'); bytes += text.length;
  }
  parts.push(']}');
  return { parts, name: 'tessellation-gallery-backup-' + fileStamp(saved) + '.json', count: cards.length, bytes };
}
$('gb-back').onclick = () => { $('gbackup').hidden = true; };
$('gb-save').onclick = () => { if (!bk) return; const b = bk;
  handFile(b.parts, b.name).then(async ok => { if (!ok) return; await GAL.setMeta('backup', { at: Date.now(), count: b.count, name: b.name }); toast('Backup saved · ' + b.name, 3200);
    if (!$('gbackup').hidden) { const s = $('gb-what').querySelector('.mute'); if (s) s.textContent = 'Last backup: ' + when(Date.now()); } }); };
$('gb-restore').onclick = () => $('gbfile').click();
$('gbfile').onchange = async e => {
  const f = e.target.files && e.target.files[0]; e.target.value = ''; if (!f) return;
  if (f.size > 300e6) { tell('Can’t restore this file', 'This file is too large to be a Gallery backup.'); return; }
  let text; try { text = await f.text(); } catch (_) { tell('Can’t restore this file', 'The file could not be read.'); return; }
  if (sniff(text) === 'project') { const r = await gAsk({ title: 'This is a single project', html: `<p>“${esc(f.name)}” is one project file, not a Gallery backup.</p><p class="mute">You can open it for editing, then Save to Gallery.</p>`, buttons: [{ id: 'open', label: 'Open it for editing', kind: 'primary' }] });
    if (r.id === 'open') { const res = await openProjectText(text); if (res === 'opened') { S.importName = cleanName(f.name.replace(/\.json$/i, ''), ''); $('gbackup').hidden = true; syncGalMenu(); toast('Opened for editing · ☰ › Save to Gallery keeps it in My Gallery', 3600); } } return; }
  startRestore(text, f.name);
};

/* ---- Restore: the whole file is checked, then previewed; nothing in My Gallery changes before you confirm, and then all at once ---- */
async function planRestore(text) {         // → { B, items } or { problem } — reads and checks only; changes nothing
  let B; try { B = JSON.parse(text); } catch (_) { return { problem: 'This file is not a Gallery backup, or it is damaged (it could not be read completely). Nothing was changed.' }; }
  if (!B || typeof B !== 'object' || Array.isArray(B)) return { problem: 'This file is not a Gallery backup. Nothing was changed.' };
  if (B.format === TP.FORMAT) return { problem: 'This is a single project file, not a Gallery backup. Use Open… › Import project file… to open it. Nothing was changed.' };
  if (B.format !== BACKUP_FORMAT) return { problem: 'This file is not a Gallery backup. Nothing was changed.' };
  if (!Number.isInteger(B.version) || B.version < 1) return { problem: 'This backup is damaged (it has no format version). Nothing was changed.' };
  if (B.version > BACKUP_VERSION) return { problem: 'This backup was made by a newer version of the app, so this version cannot restore it. Nothing was changed.' };
  if (!Array.isArray(B.projects)) return { problem: 'This backup is damaged (its list of projects is missing). Nothing was changed.' };
  if (Number.isInteger(B.count) && B.count !== B.projects.length) return { problem: 'This backup is damaged: it should hold ' + B.count + ' projects but holds ' + B.projects.length + '. Nothing was changed.' };
  if (GAL.state.ok !== true) return { problem: 'My Gallery is not available in this browser, so nothing can be restored into it.' };
  await galRefresh(); const mine = new Map(galCards.map(c => [c.id, c])), seen = new Map(), items = [];
  B.projects.forEach((e, i) => {
    const it = { i, name: cleanName(e && e.name, 'Project ' + (i + 1)), status: 'bad', why: '', thumbs: {} };
    try {
      if (!e || typeof e !== 'object' || !e.project || typeof e.project !== 'object') throw new Error('its project data is missing');
      const t = JSON.stringify(e.project);
      if (typeof e.check !== 'string') throw new Error('it has no checksum');
      if (GAL.fnv(t) !== e.check) throw new Error('its data does not match its checksum');
      const r = TP.readProject(t); if (r.problem) throw Object.assign(new Error(r.problem), { plain: true });
      decodeProject(r.project);
      const p = r.project; it.project = p; it.content = contentCheck(p); it.check = e.check; it.label = labelOf(p); it.shape = shapeKeyOf(p); it.construction = p.geometry.construction.id; it.stage = stageOf(p);
      it.created = fin(e.created) ? e.created : (Date.parse(p.saved) || Date.now()); it.updated = fin(e.updated) ? e.updated : it.created; it.build = typeof e.build === 'string' ? e.build.slice(0, 40) : '';
      const th = e.thumbs && typeof e.thumbs === 'object' ? e.thumbs : {}; it.thumbs = { tile: okThumb(th.tile) ? th.tile : outlineThumb(p), pattern: okThumb(th.pattern) ? th.pattern : null };
      const id = typeof e.id === 'string' && /^[\w-]{1,64}$/.test(e.id) ? e.id : null; it.id = id;
      if (id && seen.has(id)) { if (seen.get(id).content === it.content) it.status = 'dupe'; else { it.status = 'new'; it.newId = true; } }
      else if (id && mine.has(id)) { const m = mine.get(id); it.mine = m; it.status = (m.content ? m.content === it.content : m.check === it.check) ? 'same' : 'diff'; }
      else { it.status = 'new'; if (!id) it.newId = true; }
      if (id && !seen.has(id)) seen.set(id, it);
    } catch (err) { it.status = 'bad'; it.why = err.newer ? 'made by a newer version of the app' : err.plain ? err.message : 'damaged: ' + err.message; it.project = null; }
    items.push(it);
  });
  return { B, items };
}
let rplan = null, rconf = 'both';
async function startRestore(text, fileName) {
  $('gbackup').hidden = true; const plan = await planRestore(text);
  if (plan.problem) { tell('Can’t restore this file', plan.problem, true); return plan; }
  rplan = Object.assign(plan, { fileName }); rconf = 'both'; showRestore(); return plan;
}
const CHIP = { new: ['new', 'New'], same: ['same', 'Already in My Gallery'], diff: ['diff', 'Different version'], dupe: ['same', 'Repeated in this backup'], bad: ['gbad', 'Can’t be restored'] };
const restoreCount = () => rplan ? rplan.items.filter(it => it.status === 'new' || (it.status === 'diff' && rconf !== 'skip')).length : 0;
function showRestore() {
  const { B, items, fileName } = rplan, diffs = items.filter(it => it.status === 'diff');
  $('gr-sub').innerHTML = esc(fileName || 'backup') + '<br>made by ' + esc((B.app && B.app.build) || 'an unknown version') + (Date.parse(B.saved) ? ' on ' + esc(when(Date.parse(B.saved))) : '') + ' · ' + items.length + ' project' + (items.length === 1 ? '' : 's') + ' · checked';
  $('gr-list').innerHTML = items.map(it => `<div class="grr${it.status === 'bad' ? ' gbad' : ''}"><img src="${it.thumbs.tile || NO_PIC}" alt=""><div class="n"><b>${esc(it.name)}</b><span>${it.status === 'bad' ? esc(it.why) : esc(it.label) + ' · ' + esc(when(it.updated))}</span></div><span class="gchip ${CHIP[it.status][0]}">${CHIP[it.status][1]}</span></div>`).join('');
  $('gr-conf').hidden = !diffs.length;
  if (diffs.length) { $('gr-conf-t').textContent = diffs.length === 1 ? '“' + diffs[0].name + '” differs from yours' : diffs.length + ' projects differ from yours';
    ['both', 'skip', 'replace'].forEach(k => $('gr-c-' + k).setAttribute('aria-pressed', String(rconf === k)));
    $('gr-conf-note').textContent = rconf === 'both' ? 'Keep both adds the backup’s copy as “' + diffs[0].name + ' (backup ' + shortDay(Date.now()) + ')”' + (diffs.length > 1 ? ', and so on' : '') + '. Yours stays as it is.'
      : rconf === 'skip' ? 'Your versions stay as they are; the backup’s versions are not added.' : 'Your versions will be replaced by the backup’s. You will be asked to confirm.'; }
  const n = restoreCount(); $('gr-go').disabled = !n; $('gr-go').textContent = n ? 'Restore ' + n + ' project' + (n === 1 ? '' : 's') : 'Nothing new to restore';
  $('grestore').hidden = false; $('grestore').scrollTop = 0;
}
const shortDay = at => new Date(at).toLocaleDateString([], { day: 'numeric', month: 'short' });
['both', 'skip', 'replace'].forEach(k => { $('gr-c-' + k).onclick = () => { rconf = k; showRestore(); }; });
$('gr-back').onclick = $('gr-cancel').onclick = () => { $('grestore').hidden = true; rplan = null; };
$('gr-go').onclick = () => doRestore();
async function doRestore() {
  if (!rplan) return null; const items = rplan.items, diffs = items.filter(it => it.status === 'diff'), B = rplan.B;
  if (rconf === 'replace' && diffs.length) {
    const r = await gAsk({ title: 'Replace ' + diffs.length + ' project' + (diffs.length === 1 ? '' : 's') + '?', html: '<p>Your versions of ' + diffs.map(d => '“' + esc(d.mine.name) + '”').join(', ') + ' will be replaced by the backup’s.</p><p class="warn"><b>Your versions cannot be brought back.</b></p>',
      buttons: [{ id: 'yes', label: 'Replace and restore', kind: 'danger' }] });
    if (r.id !== 'yes') return null;
  }
  const ops = [], used = new Set(galCards.map(c => c.id)), stamp = ' (backup ' + shortDay(Date.now()) + ')', added = [];
  items.forEach(it => {
    if (it.status !== 'new' && !(it.status === 'diff' && rconf !== 'skip')) return;
    let id = it.id, name = it.name;
    if (it.status === 'diff' && rconf === 'both') { id = null; name = cleanName(it.name + stamp, it.name); }
    if (!id || it.newId || (it.status === 'new' && used.has(id))) id = GAL.newId();
    used.add(id);
    const card = { id, name, created: it.created, updated: it.updated, label: it.label, shape: it.shape, construction: it.construction, stage: it.stage, build: it.build || ((B.app && B.app.build) || ''),
      bytes: TP.toFileText(it.project).length, check: it.check, content: it.content, thumbs: it.thumbs };
    ops.push({ store: 'projects', put: it.project, key: id }, { store: 'cards', put: card, key: id }); added.push(name);
  });
  if (!ops.length) return null;
  const w = await GAL.write(ops);                                          // one transaction: every project, or none
  if (!w.ok) { tell('Nothing was restored', failSentence(w) + ' My Gallery is unchanged.', true); return w; }
  $('grestore').hidden = true; rplan = null; await galRefresh();
  toast('Restored ' + added.length + ' project' + (added.length === 1 ? '' : 's') + ' to My Gallery', 3000); openGallery('gallery'); return w;
}

/* ---- the automatic save remembers the Gallery link; Continue brings it back; a new tessellation has none ---- */
{ const _save = TP.save; TP.save = (p, info) => _save(p, S.gallery ? Object.assign({}, info, { gallery: Object.assign({}, S.gallery) }) : info); }
{ const _cs = continueStored; continueStored = async function () {
    const m = TP.store.meta; await _cs(); if (!S.field || !m || !m.slots) return;
    const slot = [m.latest, m.latest === 'a' ? 'b' : 'a'].find(s => m.slots[s] && m.slots[s].at === keep.lastAt), L = slot && m.slots[slot].gallery;
    S.gallery = L && typeof L.id === 'string' ? { id: L.id, name: cleanName(L.name, 'Untitled'), updated: fin(L.updated) ? L.updated : 0, check: String(L.check || '') } : null; syncGalMenu(); }; }
{ const _st = start; start = function (id, opts) { S.gallery = null; S.importName = ''; _st(id, opts); }; }
{ const _ik = initKeep; initKeep = async function () {
    const g = GAL.open().then(ok => ok ? galRefresh() : null).catch(() => {});
    await _ik(); await g; syncGalMenu();
    if (!S.field && !$('entry').hidden && S.entryStep === 1) showEntry(1); }; }
$('m-gallery').onclick = () => openGallery('gallery');
$('m-save').onclick = () => saveToGallery();
$('m-open').onclick = () => openGallery('open');
$('m-backup').onclick = () => openBackup();

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
window.__ws.t1 = { orbitRels, glueRels, mirrorAxisArr, mirrorDrawOn, reflM, mirrorPts, pxMirror, syncMirrorUI, openRules, RULES_INFO, linkedEdges, sideCount, get mirrorDraw() { return S.mirrorDraw; }, set mirrorDraw(v) { S.mirrorDraw = !!v; syncMirrorUI(); } };
window.__ws.da = { inkFor, ensureInk, get ink() { return S.ink; }, get inkBase() { return S.inkBase; }, get inkMs() { return S.inkMs; }, zoomLimits };
window.__ws.f1a2 = { FG_MID, isFGM, fgEndsOf, fgIn, fgEnds, fgAxisX, fgMCage, fgMParams, fgMCageAfterDrag, fgMCageProblem, fgInnerFrom, fgResample, orbitsOf, setWorkingOn, fgComp, fgTintKey, fgPlain, fgGroupLabel,
  drawnSteps, consLabel, newConstruction, askNewConstruction, get consLink() { return S.consLink; }, FG_MHOME };
window.__ws.f1 = { FG_ID, FG_IN, FG_MIN_SHARE, FG_COL, FG_INK, FG_HOME, fgCageAfterDrag, fgCageProblem, fgRefresh, fgFigureAt, offsetPolygon, get refillMs() { return S.fgRefillMs; }, fgOK, fgPolys, fgShares, fgRebuild, fgColours, straightInner, fgInnerVerts, fgNodeHandles, syncFgUI, swapFigures, fgHomeInk, hitEdge, polyHit, sidePts, fgInfoSVG,
  get fg() { return S.fg; }, get focus() { return S.fgFocus; } };
window.__ws.ph1 = { triView, chooseMethod, chooseShape, startTri, ph1Sync, histLabel, polyNext, syncHistLabels, stepMain, stepPoly, menuPage, shapeName, METHOD_NAME, TRI_AVAIL, TRI_NOTE, HEX_NOTE, STARTS,
  get lastFg() { return S.lastFg; } };
window.__ws.t2 = { isMirrorId, geoId, arrangementNote, arrangeSVG, ARRANGE_INFO, FLIP_SYM_NOTE, artMirrored, orientCueNow, arrangement: () => S.consId === 'mirror-flip' ? 'alternating' : isMirrorId(S.consId) ? 'same' : null };
window.__ws.ph2 = { contentCheck, labelOf, shapeKeyOf, stageOf, drawThumb, thumbsNow, outlineThumb, okThumb, galRefresh, linkState, storedState, syncGalMenu, gAsk, saveToGallery, writeEntry, openFromGallery, openGallery, closeGallery, renderGallery,
  showPop, hidePop, renameEntry, duplicateEntry, deleteEntry, buildBackup, openBackup, planRestore, startRestore, showRestore, doRestore, handFile, sniff, uniqueName, GAL, BACKUP_FORMAT, BACKUP_VERSION, THUMB, VOLATILE,
  get gallery() { return S.gallery; }, set gallery(v) { S.gallery = v; }, get importName() { return S.importName; }, cards: () => galCards, get rplan() { return rplan; }, get rconf() { return rconf; }, set rconf(v) { rconf = v; }, get bk() { return bk; }, get popFile() { return popFile; } };
})();
