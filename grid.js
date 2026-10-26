/* tessellation-mobile-workspace-v6.1-grid-m2a / grid.js — M1's grid.js (md5 a58201c6…) with ONE marked change, carried over from the
 * verified M2 feasibility study (and one more, below): the image test of the 'transformations' check is applied only between faces of the SAME class
 * ("M2 FEASIBILITY PATCH"), so grids with several face classes validate. A second marked change ("M2A PATCH") makes the
 * patch-topology check count only real holes (a clockwise loop inside the core window), not the pinched rim of a finite test patch.
 * Square grids (one class), and so the Grid Lab, behave exactly as in M1. M1's own file is untouched.
 *
 * tessellation-mobile-workspace-v6.0-grid-m1 / grid.js · GRID GEOMETRY FOUNDATION (M1)
 *
 * An explicit representation of a tessellating grid. It is developed ALONGSIDE the v5.1 engine: engine.js and app.js are unchanged.
 * It is pure geometry, with no DOM and no dependence on the engine. It runs in the browser (window.TessGrid) and in Node
 * (module.exports), so it can be verified on its own.
 *
 * Two levels:
 *
 *   QUOTIENT · the finite, editable description of a periodic grid.
 *     - lattice: two translation vectors b1, b2. A grid element at lattice offset [i, j] is its representative moved by
 *       i·b1 + j·b2.
 *     - vertices: one VERTEX CLASS per orbit of grid vertices, at an absolute position.
 *     - edges: each EDGE CLASS joins vertex class v0 (at offset [0,0]) to v1 (at offset `shift`). It carries the edge's FORM:
 *         · polygon `nodes` (v5.1's points);
 *         · optionally a dense `curve` (v5.1's Shape boundary).
 *       Both are stored edge-relative ({s along, t across}, in edge lengths, exactly as v5.1 stores nodes), so they ride with
 *       the vertices when the lattice changes.
 *     - faces: each FACE CLASS is a counter-clockwise cycle of SIDES. A side names an edge class, a direction (+1 along v0→v1,
 *       −1 back) and the lattice offset `at` of the edge instance it uses.
 *     - The transformation relationship carried by an edge class follows from the two sides that use it: one runs along it,
 *       the other runs back, at another offset. For the square under translation this reproduces v5.1's relations
 *       e0 → e2 (by b2) and e1 → e3 (by −b1).
 *
 *   PATCH · an explicit finite piece of the grid built from the quotient (lattice offsets −n..n).
 *     - It has vertices, edges, polygonal faces and HALF-EDGES (next, prev, twin).
 *     - Every shared edge is one object, referenced by the two faces on its two sides.
 *     - Neighbouring faces are explicit, each with the transformation that carries this face onto that neighbour.
 *     - A permitted change (a vertex move, an edge's form) changes geometry only. refreshGeometry() keeps the topology as it is.
 *
 * VALIDATE does not trust the patch's own bookkeeping.
 *   1. It rechecks the quotient and the half-edge topology.
 *   2. It re-derives every face independently from the quotient and compares it across each shared edge.
 *   3. It works from the face outlines alone, as drawn:
 *      - every segment must be matched by exactly one reversed segment of another face;
 *      - no two segments may cross or touch;
 *      - the angles at every vertex must add up to 360°;
 *      - sample points must each be covered exactly once, including probes 10⁻⁷ from every segment and vertex;
 *      - the adjacency found this way must equal the explicit one.
 *
 * Conventions (shared with engine.js): points {x, y}, y up. Matrices [a,b,c,d,e,f] mean x' = a x + c y + e,
 * y' = b x + d y + f. Faces run counter-clockwise.
 *
 * Scope of M1: ONE grid is built and verified — the square grid under translation (v5.1's "Translation"). That includes v5.1's
 * permitted corner moves (any parallelogram) and its polygon nodes. The structures accept any number of vertex, edge and face
 * classes; triangle, semiregular and mixed grids are quotients of the same kind. But nothing beyond the square is built here.
 */
(function (root, factory) {
  const G = factory();
  if (typeof module === 'object' && module.exports) module.exports = G; else root.TessGrid = G;
})(typeof self !== 'undefined' ? self : globalThis, function () {
'use strict';

/* ---------------- points and matrices (same convention and formulas as engine.js) ---------------- */
const P = (x, y) => ({ x, y });
const TAU = 2 * Math.PI;
const IDM = [1, 0, 0, 1, 0, 0];
const mmul = (m, n) => [m[0]*n[0]+m[2]*n[1], m[1]*n[0]+m[3]*n[1], m[0]*n[2]+m[2]*n[3], m[1]*n[2]+m[3]*n[3],
  m[0]*n[4]+m[2]*n[5]+m[4], m[1]*n[4]+m[3]*n[5]+m[5]];
const det = m => m[0]*m[3] - m[1]*m[2];
const minv = m => { const d = det(m), a = m[3]/d, b = -m[1]/d, c = -m[2]/d, e = m[0]/d;
  return [a, b, c, e, -(a*m[4]+c*m[5]), -(b*m[4]+e*m[5])]; };
const mapp = (m, p) => P(m[0]*p.x + m[2]*p.y + m[4], m[1]*p.x + m[3]*p.y + m[5]);
const translation = v => [1, 0, 0, 1, v.x, v.y];
const mdiff = (m, n) => m.reduce((w, v, i) => Math.max(w, Math.abs(v - n[i])), 0);
const dist = (a, b) => Math.hypot(b.x - a.x, b.y - a.y);
const cross = (ax, ay, bx, by) => ax * by - ay * bx;
const lerpP = (a, b, t) => P(a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t);
const clone = o => JSON.parse(JSON.stringify(o));
function seeded(seed) { let s = seed >>> 0; return () => (s = (s * 1664525 + 1013904223) % 4294967296) / 4294967296; }   // the engine's LCG

/* ---------------- lattice ---------------- */
const addAt = (a, b) => [a[0] + b[0], a[1] + b[1]];
const subAt = (a, b) => [a[0] - b[0], a[1] - b[1]];
const sameAt = (a, b) => a[0] === b[0] && a[1] === b[1];
const latVec = (L, at) => P(at[0] * L.b1.x + at[1] * L.b2.x, at[0] * L.b1.y + at[1] * L.b2.y);
const latDet = L => L.b1.x * L.b2.y - L.b1.y * L.b2.x;
const toLat = (L, p) => { const d = latDet(L); return [(p.x * L.b2.y - p.y * L.b2.x) / d, (L.b1.x * p.y - L.b1.y * p.x) / d]; };   // world → (u, v)
const fromLat = (L, u, v) => P(u * L.b1.x + v * L.b2.x, u * L.b1.y + v * L.b2.y);

/* ---------------- edge-relative coordinates (v5.1's frameOf / relToWorld / worldToRel, app.js lines 788–790, written out again) ---------------- */
const relToWorld = (a, b, n) => { const dx = b.x - a.x, dy = b.y - a.y; return P(a.x + n.s * dx - n.t * dy, a.y + n.s * dy + n.t * dx); };
const worldToRel = (a, b, p) => { const dx = b.x - a.x, dy = b.y - a.y, L2 = dx * dx + dy * dy, x = p.x - a.x, y = p.y - a.y;
  return { s: (x * dx + y * dy) / L2, t: (y * dx - x * dy) / L2 }; };

/* ---------------- permitted-move limits (v5.1's values; unit = the original cell size) ---------------- */
const LIMITS = {
  unit: 1,
  minSide: 0.3,     // CAGE_MIN_SIDE: every side of the cell ≥ 0.3 cell
  minSin: 0.5,      // CAGE_MIN_SIN: corner angles 30°–150°
  minSeg: 0.04,     // POLY_MIN_SEG: shortest polygon side
  clear: 0.015,     // POLY_CLEAR: closest a corner/node may come to a side it is not on
  maxSides: 10,     // POLY_MAX_SIDES (a Polygon-stage rule, not a tiling rule)
  domain: null,     // v5.1's drawing area {x0, y1, side} (app.js makeInk); null = unlimited
  snap: 0.02        // CAGE_SNAP: corners within 0.02 of the original square snap back to it
};

/* ================= QUOTIENT ================= */
const vcls = (g, id) => g.vertices.find(v => v.id === id);
const ecls = (g, id) => g.edges.find(e => e.id === id);
const fcls = (g, id) => g.faces.find(f => f.id === id);
const vpos = (g, id, at) => { const v = vcls(g, id), d = latVec(g.lattice, at); return P(v.pos.x + d.x, v.pos.y + d.y); };
const elKey = (cls, at) => cls + '@' + at[0] + ',' + at[1];

// The square grid of v5.1's Translation construction: cell A(0,0) B(1,0) C(1,1) D(0,1).
// One vertex class (v: every grid vertex is v moved by i·b1 + j·b2; the cell's corners A, B, C, D are v at offsets (0,0), (1,0), (1,1), (0,1)),
// two edge classes, one face class: V − E + F = 1 − 2 + 1 = 0, as for every lattice quotient (a torus).
function squareGrid(opts) {
  opts = opts || {};
  return {
    kind: 'square', symmetry: 'translation', version: 1,
    lattice: { b1: P(1, 0), b2: P(0, 1) },
    vertices: [{ id: 'v', pos: P(0, 0) }],
    edges: [
      { id: 'a', v0: 'v', v1: 'v', shift: [1, 0], nodes: [], curve: null },     // horizontal: v → v + b1 (A → B)
      { id: 'b', v0: 'v', v1: 'v', shift: [0, 1], nodes: [], curve: null }      // vertical:   v → v + b2 (B → C at offset [1,0])
    ],
    faces: [{ id: 'F', sides: [
      { edge: 'a', dir: 1, at: [0, 0] },     // side 0  A → B   (v5.1 edge e0, master of the pair a)
      { edge: 'b', dir: 1, at: [1, 0] },     // side 1  B → C   (e1, master of the pair b)
      { edge: 'a', dir: -1, at: [0, 1] },    // side 2  C → D   (e2 = e0 moved by b2, run backwards)
      { edge: 'b', dir: -1, at: [0, 0] }     // side 3  D → A   (e3 = e1 moved by −b1, run backwards)
    ] }],
    limits: Object.assign({}, LIMITS, opts.limits || {})
  };
}

// start and end vertex (class, lattice offset) of side k of face class fc placed at offset off
function sideEnds(g, fc, k, off) {
  const s = fc.sides[k], e = ecls(g, s.edge), at = addAt(off, s.at);
  const p = { cls: e.v0, at }, q = { cls: e.v1, at: addAt(at, e.shift) };
  return s.dir > 0 ? [p, q] : [q, p];
}
function edgeEnds(g, e, at) { return [vpos(g, e.v0, at), vpos(g, e.v1, addAt(at, e.shift))]; }
// world polyline of an edge instance, in the edge class's direction (v0 → v1): its curve if it has one, otherwise straight through its nodes
function edgeLine(g, e, at) {
  const [a, b] = edgeEnds(g, e, at), inner = e.curve || e.nodes;
  return [P(a.x, a.y), ...inner.map(n => relToWorld(a, b, n)), P(b.x, b.y)];
}
function edgeNodes(g, e, at) { const [a, b] = edgeEnds(g, e, at); return e.nodes.map(n => relToWorld(a, b, n)); }

// A face derived DIRECTLY from the quotient (no patch): its boundary points, its polygon (corners + nodes) and each side's polyline.
function faceOutline(g, fc, at) {
  const pts = [], poly = [], sides = [];
  fc.sides.forEach((s, k) => {
    const e = ecls(g, s.edge), eat = addAt(at, s.at);
    let line = edgeLine(g, e, eat), nodes = edgeNodes(g, e, eat).map((p, i) => ({ p, index: i }));
    if (s.dir < 0) { line = line.reverse(); nodes = nodes.reverse(); }
    sides.push(line);
    for (let i = 0; i < line.length - 1; i++) pts.push(line[i]);
    poly.push({ p: line[0], kind: 'corner', side: k });
    nodes.forEach(n => poly.push({ p: n.p, kind: 'node', side: k, edge: s.edge, index: n.index }));
  });
  return { pts, poly, sides };
}
const faceCorners = (g, fc, at) => fc.sides.map((s, k) => { const [p] = sideEnds(g, fc, k, at || [0, 0]); return vpos(g, p.cls, p.at); });

// The transformation relationship carried by each edge class: the side that runs along it (from) and the side that runs back (to).
// For a translation quotient, `to` is `from` moved by a lattice vector, traversed in the opposite direction (v5.1's rev = true).
function pairings(g) {
  return g.edges.map(e => {
    const u = []; g.faces.forEach(f => f.sides.forEach((s, k) => { if (s.edge === e.id) u.push({ face: f.id, side: k, dir: s.dir, at: s.at }); }));
    const from = u.find(x => x.dir > 0), to = u.find(x => x.dir < 0);
    if (u.length !== 2 || !from || !to) return { edge: e.id, from: from || null, to: to || null, m: null, uses: u.length };
    const lat = subAt(to.at, from.at), v = latVec(g.lattice, lat), m = translation(v);
    return { edge: e.id, from, to, lattice: lat, vector: v, m, inv: minv(m), rev: from.dir !== to.dir, uses: 2 };
  });
}

// Quotient consistency: sides chain round each face, every edge class separates exactly two face sides (opposite directions),
// the lattice is non-degenerate and counter-clockwise, and V − E + F = 0.
function checkQuotient(g) {
  const errors = [], D = latDet(g.lattice);
  if (!(D > 0)) errors.push(`lattice basis degenerate or reversed (det ${D})`);
  const uses = new Map(g.edges.map(e => [e.id, []]));
  g.vertices.forEach(v => { if (!v.pos || !isFinite(v.pos.x) || !isFinite(v.pos.y)) errors.push(`vertex ${v.id} has no position`); });
  g.faces.forEach(f => {
    const n = f.sides.length; if (n < 3) errors.push(`face ${f.id} has ${n} sides`);
    f.sides.forEach((s, k) => {
      const e = ecls(g, s.edge); if (!e) { errors.push(`face ${f.id} side ${k}: unknown edge ${s.edge}`); return; }
      if (!vcls(g, e.v0) || !vcls(g, e.v1)) errors.push(`edge ${e.id}: unknown vertex class`);
      uses.get(e.id).push({ face: f.id, side: k, dir: s.dir });
    });
    for (let k = 0; k < n; k++) {
      if (!ecls(g, f.sides[k].edge) || !ecls(g, f.sides[(k + 1) % n].edge)) continue;
      const [, q] = sideEnds(g, f, k, [0, 0]), [p] = sideEnds(g, f, (k + 1) % n, [0, 0]);
      if (q.cls !== p.cls || !sameAt(q.at, p.at)) errors.push(`face ${f.id}: side ${k} ends at ${elKey(q.cls, q.at)} but side ${(k + 1) % n} starts at ${elKey(p.cls, p.at)}`);
    }
  });
  uses.forEach((u, id) => {
    if (u.length !== 2) errors.push(`edge ${id} is used by ${u.length} face side(s); a grid edge separates exactly two`);
    else if (u[0].dir === u[1].dir) errors.push(`edge ${id} is run in the same direction by both its sides (the two faces would lie on the same side of it)`);
  });
  const euler = g.vertices.length - g.edges.length + g.faces.length;
  if (euler !== 0) errors.push(`V − E + F = ${euler} in the quotient; a periodic grid (a torus) needs 0`);
  return { ok: !errors.length, errors, euler, det: D };
}

/* ---------------- quotient edits (each returns a NEW grid; the old one is untouched) ---------------- */
// The cell as its four corners (square grid only): A, B = A + b1, C = A + b1 + b2, D = A + b2.
const cellCorners = g => faceCorners(g, g.faces[0], [0, 0]);
// A new grid with this cell. The lattice is read from A, B, D, and C is DERIVED, so the cell is a parallelogram by construction.
// Nodes and curves are edge-relative and ride along.
function withCell(g, V) {
  const h = clone(g);
  vcls(h, 'v').pos = P(V[0].x, V[0].y);
  h.lattice = { b1: P(V[1].x - V[0].x, V[1].y - V[0].y), b2: P(V[3].x - V[0].x, V[3].y - V[0].y) };
  return h;
}
// v5.1's Translation corner rule (app.js cageAfterDrag, 'parallelogram'): the dragged corner k carries the next corner
// counter-clockwise (A→B, B→C, C→D, D→A); the other two corners stay.
function cornerRule(g0, k, target) {
  const V0 = cellCorners(g0), j = (k + 1) % 4, dx = target.x - V0[k].x, dy = target.y - V0[k].y, V = V0.map(p => P(p.x, p.y));
  V[k] = P(target.x, target.y); V[j] = P(V0[j].x + dx, V0[j].y + dy);
  return withCell(g0, V);
}
function lerpCell(a, b, t) { const A = cellCorners(a), B = cellCorners(b); return withCell(b, A.map((p, i) => lerpP(p, B[i], t))); }
const SQUARE_CELL = [P(0, 0), P(1, 0), P(1, 1), P(0, 1)];
// The constrained corner drag (v5.1 flushCornerMove):
//   - the rule is applied from the cell at the start of the drag;
//   - near the original square it snaps to it exactly;
//   - an invalid candidate is never returned: the corner stops at the last valid position, found by halving the step
//     (10 halvings, as v5.1).
function dragCorner(gStart, gCur, k, target) {
  let want = cornerRule(gStart, k, target);
  const z = gCur.limits.unit, W = cellCorners(want);
  if (W.every((q, i) => dist(q, SQUARE_CELL[i]) < gCur.limits.snap * z)) want = withCell(want, SQUARE_CELL);
  if (!problem(want)) return { grid: want, blocked: false };
  let lo = 0, hi = 1; for (let i = 0; i < 10; i++) { const m = (lo + hi) / 2; problem(lerpCell(gCur, want, m)) ? hi = m : lo = m; }
  return { grid: lo > 0 ? lerpCell(gCur, want, lo) : gCur, blocked: true };
}
// Moving a vertex CLASS moves every vertex of its orbit. With one vertex class (the square) this is a rigid translation of the
// whole grid. It is kept because it is the natural vertex move for grids with several vertex classes (M2+).
function moveVertexClass(g, id, pos) { const h = clone(g); vcls(h, id).pos = P(pos.x, pos.y); return h; }
function setNodes(g, edgeId, nodes) { const h = clone(g); ecls(h, edgeId).nodes = nodes.map(n => Object.assign({}, n)); return h; }
function insertNode(g, edgeId, index, rel) { const l = ecls(g, edgeId).nodes.slice(); l.splice(index, 0, Object.assign({}, rel)); return setNodes(g, edgeId, l); }
function moveNode(g, edgeId, index, rel) { const l = ecls(g, edgeId).nodes.slice(); l[index] = Object.assign({}, l[index], { s: rel.s, t: rel.t }); return setNodes(g, edgeId, l); }
function removeNode(g, edgeId, index) { const l = ecls(g, edgeId).nodes.slice(); l.splice(index, 1); return setNodes(g, edgeId, l); }
function setCurve(g, edgeId, curve) { const h = clone(g); ecls(h, edgeId).curve = curve ? curve.map(n => ({ s: n.s, t: n.t })) : null; return h; }
// a world point on (or near) the instance of an edge class at lattice offset `at` → that edge's relative coordinates
function relOnEdge(g, edgeId, at, p) { const [a, b] = edgeEnds(g, ecls(g, edgeId), at); return worldToRel(a, b, p); }
const nodeCount = g => g.edges.reduce((n, e) => n + e.nodes.length, 0);
const sideCount = g => g.faces[0].sides.length + 2 * nodeCount(g);   // each node appears on both sides that use its edge

/* ---------------- permitted changes (v5.1's limits, with v5.1's reasons) ---------------- */
// segX: v5.1's proper-crossing test (app.js line 494), written out again
function segX(ax, ay, bx, by, cx, cy, dx, dy) {
  const o1 = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax), o2 = (bx - ax) * (dy - ay) - (by - ay) * (dx - ax);
  if ((o1 > 1e-13 && o2 > 1e-13) || (o1 < -1e-13 && o2 < -1e-13)) return false;
  const o3 = (dx - cx) * (ay - cy) - (dy - cy) * (ax - cx), o4 = (dx - cx) * (by - cy) - (dy - cy) * (bx - cx);
  return ((o1 > 1e-13 && o2 < -1e-13) || (o1 < -1e-13 && o2 > 1e-13)) && ((o3 > 1e-13 && o4 < -1e-13) || (o3 < -1e-13 && o4 > 1e-13));
}
function distPS(p, a, b) { const dx = b.x - a.x, dy = b.y - a.y, l = dx * dx + dy * dy, t = l ? Math.max(0, Math.min(1, ((p.x - a.x) * dx + (p.y - a.y) * dy) / l)) : 0; return Math.hypot(p.x - a.x - t * dx, p.y - a.y - t * dy); }
// '' when the cell's corners are a permitted cell; otherwise why not ('side' | 'fold' | 'angle'), as v5.1 cageProblem
function cellProblem(g) {
  const lim = g.limits, z = lim.unit;
  for (const fc of g.faces) { const V = faceCorners(g, fc, [0, 0]), n = V.length;
    for (let i = 0; i < n; i++) { const a = V[i], b = V[(i + 1) % n], c = V[(i + 2) % n], ux = b.x - a.x, uy = b.y - a.y, vx = c.x - b.x, vy = c.y - b.y, lu = Math.hypot(ux, uy), lv = Math.hypot(vx, vy);
      if (lu < lim.minSide * z) return 'side';
      const cr = ux * vy - uy * vx; if (cr <= 0) return 'fold'; if (cr / (lu * lv) < lim.minSin) return 'angle'; } }
  return '';
}
// '' when every face class's polygon (corners + nodes) is a permitted tile; otherwise why not ('area' | 'short' | 'cross' | 'touch' | 'sides'),
// as v5.1 polyProblem
function polygonProblem(g) {
  const lim = g.limits, z = lim.unit, I = lim.domain;
  if (sideCount(g) > lim.maxSides) return 'sides';
  for (const fc of g.faces) {
    const vs = faceOutline(g, fc, [0, 0]).poly.map(v => v.p), n = vs.length;
    if (I) { const mg = 0.02 * I.side; for (const p of vs) if (p.x < I.x0 + mg || p.x > I.x0 + I.side - mg || p.y > I.y1 - mg || p.y < I.y1 - I.side + mg) return 'area'; }
    for (let i = 0; i < n; i++) { const a = vs[i], b = vs[(i + 1) % n]; if (Math.hypot(b.x - a.x, b.y - a.y) < lim.minSeg * z) return 'short'; }
    for (let i = 0; i < n; i++) for (let j = i + 2; j < n; j++) { if (i === 0 && j === n - 1) continue; const a = vs[i], b = vs[(i + 1) % n], c = vs[j], d = vs[(j + 1) % n];
      if (segX(a.x, a.y, b.x, b.y, c.x, c.y, d.x, d.y)) return 'cross'; }
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) { if (j === i || (j + 1) % n === i) continue; if (distPS(vs[i], vs[j], vs[(j + 1) % n]) < lim.clear * z) return 'touch'; }
    let a2 = 0; vs.forEach((p, i) => { const q = vs[(i + 1) % n]; a2 += p.x * q.y - q.x * p.y; }); if (a2 <= 0) return 'cross';
  }
  return '';
}
function problem(g) {
  const q = checkQuotient(g);
  if (q.errors.some(e => !/^lattice/.test(e))) return 'structure';
  return cellProblem(g) || (q.ok ? polygonProblem(g) : 'fold');          // a reversed lattice is v5.1's 'fold'
}
// The constrained node drag (v5.1 flushPolyMove): an invalid position is never returned. The node stops at the last valid
// position on the way from where it is to where it is wanted.
function dragNode(g, edgeId, index, rel) {
  const want = moveNode(g, edgeId, index, rel); if (!problem(want)) return { grid: want, blocked: false };
  const cur = ecls(g, edgeId).nodes[index]; let lo = 0, hi = 1;
  const at = m => moveNode(g, edgeId, index, { s: cur.s + (rel.s - cur.s) * m, t: cur.t + (rel.t - cur.t) * m });
  for (let i = 0; i < 10; i++) { const m = (lo + hi) / 2; problem(at(m)) ? hi = m : lo = m; }
  return { grid: lo > 0 ? at(lo) : g, blocked: true };
}

/* ================= PATCH: the explicit grid ================= */
function signedArea(pts) { let a = 0; for (let i = 0, n = pts.length; i < n; i++) { const p = pts[i], q = pts[(i + 1) % n]; a += p.x * q.y - q.x * p.y; } return a / 2; }
function centroid(pts) { let a = 0, cx = 0, cy = 0; for (let i = 0, n = pts.length; i < n; i++) { const p = pts[i], q = pts[(i + 1) % n], w = p.x * q.y - q.x * p.y; a += w; cx += (p.x + q.x) * w; cy += (p.y + q.y) * w; }
  return Math.abs(a) < 1e-300 ? P(pts[0].x, pts[0].y) : P(cx / (3 * a), cy / (3 * a)); }

// The patch size a grid needs. A tile may reach well beyond its lattice cell: points pulled out, or a thin sheared cell.
// n is chosen so that every core face is surrounded by faces that are present.
function patchSize(g) {
  let u0 = Infinity, u1 = -Infinity, v0 = Infinity, v1 = -Infinity;
  g.faces.forEach(fc => faceOutline(g, fc, [0, 0]).pts.forEach(p => { const [u, v] = toLat(g.lattice, p); u0 = Math.min(u0, u); u1 = Math.max(u1, u); v0 = Math.min(v0, v); v1 = Math.max(v1, v); }));
  const reach = Math.max(u1 - u0, v1 - v0); return isFinite(reach) ? Math.max(3, Math.ceil(reach) + 2) : 3;
}
// Faces at lattice offsets [i, j], |i|, |j| ≤ n, for every face class. opts.omit lists face keys to leave out (used by the negative tests).
function buildPatch(g, opts) {
  opts = opts || {};
  const n = opts.n === undefined ? patchSize(g) : opts.n, omit = new Set(opts.omit || []);
  const V = [], E = [], F = [], H = [], vIx = new Map(), eIx = new Map(), fIx = new Map();
  const vertex = (cls, at) => { const key = elKey(cls, at); let id = vIx.get(key);
    if (id === undefined) { id = V.length; V.push({ id, key, cls, at: at.slice(), pos: null, out: [] }); vIx.set(key, id); } return id; };
  const edge = (ec, at) => { const key = elKey(ec.id, at); let id = eIx.get(key);
    if (id === undefined) { id = E.length; E.push({ id, key, cls: ec.id, at: at.slice(), v0: vertex(ec.v0, at), v1: vertex(ec.v1, addAt(at, ec.shift)), half: [], pts: null, nodes: null }); eIx.set(key, id); }
    return id; };
  g.faces.forEach(fc => { for (let i = -n; i <= n; i++) for (let j = -n; j <= n; j++) {
    const at = [i, j], key = elKey(fc.id, at); if (omit.has(key)) continue;
    const f = { id: F.length, key, cls: fc.id, at, g: null, half: [], corners: [], neighbours: [], outline: null, poly: null, centroid: null };
    F.push(f); fIx.set(key, f.id);
    fc.sides.forEach((s, side) => { const e = edge(ecls(g, s.edge), addAt(at, s.at)), ed = E[e];
      const h = { id: H.length, face: f.id, side, edge: e, dir: s.dir, origin: s.dir > 0 ? ed.v0 : ed.v1, target: s.dir > 0 ? ed.v1 : ed.v0, twin: -1, next: -1, prev: -1 };
      H.push(h); f.half.push(h.id); ed.half.push(h.id); f.corners.push(h.origin); V[h.origin].out.push(h.id); });
    const m = f.half.length; f.half.forEach((h, k) => { H[h].next = f.half[(k + 1) % m]; H[h].prev = f.half[(k + m - 1) % m]; });
  } });
  E.forEach(e => { if (e.half.length === 2) { const [a, b] = e.half; H[a].twin = b; H[b].twin = a; } });
  F.forEach(f => f.half.forEach(hid => { const h = H[hid];
    f.neighbours.push(h.twin < 0 ? { side: h.side, face: -1, edge: h.edge } : { side: h.side, face: H[h.twin].face, theirSide: H[h.twin].side, edge: h.edge, T: null }); }));
  const ref = fIx.get(elKey(g.faces[0].id, [0, 0]));
  const patch = { grid: g, n, vertices: V, edges: E, faces: F, half: H, index: { vertex: vIx, edge: eIx, face: fIx }, ref: ref === undefined ? -1 : ref };
  return refreshGeometry(patch, g);
}
// Geometry from the quotient, topology untouched: vertex positions, edge polylines (in their class direction), face outlines and
// polygons (assembled from the SHARED edge objects), placements and the transformation to each neighbour.
function refreshGeometry(patch, g) {
  patch.grid = g;
  patch.vertices.forEach(v => { v.pos = vpos(g, v.cls, v.at); });
  patch.edges.forEach(e => { const ec = ecls(g, e.cls); e.pts = edgeLine(g, ec, e.at); e.nodes = edgeNodes(g, ec, e.at); });
  patch.faces.forEach(f => {
    f.g = translation(latVec(g.lattice, f.at));            // carries the face class's representative (offset [0,0]) onto this face
    f.outline = []; f.poly = [];
    f.half.forEach(hid => { const h = patch.half[hid], e = patch.edges[h.edge], line = h.dir > 0 ? e.pts : e.pts.slice().reverse();
      for (let i = 0; i < line.length - 1; i++) f.outline.push(line[i]);
      f.poly.push({ p: line[0], kind: 'corner', side: h.side, vertex: h.origin });
      const nd = e.nodes.map((p, i) => ({ p, index: i })); if (h.dir < 0) nd.reverse();
      nd.forEach(x => f.poly.push({ p: x.p, kind: 'node', side: h.side, edge: e.cls, index: x.index })); });
    f.centroid = centroid(f.outline);
  });
  patch.faces.forEach(f => f.neighbours.forEach(nb => { if (nb.face >= 0) nb.T = mmul(patch.faces[nb.face].g, minv(f.g)); }));
  return patch;
}
const faceAt = (patch, cls, at) => { const id = patch.index.face.get(elKey(cls, at)); return id === undefined ? null : patch.faces[id]; };

// Face placements (the transformation relationships at the level of the whole grid) that move a point by at most R — v5.1's cull
// rule for its tile field. Enumerated analytically, without building geometry; used to compare with that field.
function placements(g, R) {
  const L = g.lattice, out = [], hmin = Math.abs(latDet(L)) / Math.max(Math.hypot(L.b1.x, L.b1.y), Math.hypot(L.b2.x, L.b2.y));
  const k = Math.ceil(R / hmin) + 2;
  for (let i = -k; i <= k; i++) for (let j = -k; j <= k; j++) { const v = latVec(L, [i, j]), d = Math.hypot(v.x, v.y); if (d <= R) out.push({ at: [i, j], m: translation(v), d }); }
  return out;
}

/* ================= VALIDATION ================= */
// tolerance-based point identity (shared points computed along different routes may differ in the last bits)
function PointIndex(tol) { this.tol = tol; this.c = tol * 1000; this.map = new Map(); this.pts = []; }
PointIndex.prototype.id = function (p) {
  const cx = Math.floor(p.x / this.c), cy = Math.floor(p.y / this.c);
  for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) { const l = this.map.get((cx + dx) + ',' + (cy + dy)); if (l) for (const id of l) { const q = this.pts[id]; if (Math.abs(q.x - p.x) <= this.tol && Math.abs(q.y - p.y) <= this.tol) return id; } }
  const id = this.pts.length; this.pts.push(p); const k = cx + ',' + cy, l = this.map.get(k); if (l) l.push(id); else this.map.set(k, [id]); return id;
};
function winding(pts, p) {
  let w = 0;
  for (let i = 0, n = pts.length; i < n; i++) { const a = pts[i], b = pts[(i + 1) % n];
    if (a.y <= p.y) { if (b.y > p.y && cross(b.x - a.x, b.y - a.y, p.x - a.x, p.y - a.y) > 0) w++; }
    else if (b.y <= p.y && cross(b.x - a.x, b.y - a.y, p.x - a.x, p.y - a.y) < 0) w--; }
  return w;
}
const interiorAngle = (a, p, b) => { let t = Math.atan2(cross(b.x - p.x, b.y - p.y, a.x - p.x, a.y - p.y), (b.x - p.x) * (a.x - p.x) + (b.y - p.y) * (a.y - p.y)); if (t <= 0) t += TAU; return t; };
function bbox(pts) { let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity; for (const p of pts) { if (p.x < x0) x0 = p.x; if (p.x > x1) x1 = p.x; if (p.y < y0) y0 = p.y; if (p.y > y1) y1 = p.y; } return { x0, y0, x1, y1 }; }

/* checkTiling — GEOMETRY ONLY. Input: closed outlines (as drawn), the ids of the core faces (whose surroundings are fully present),
 * and a sampling window. Nothing about lattices, classes or half-edges is used.
 *   faces    every outline counter-clockwise, no repeated point, no zero-length segment
 *   matching every segment of a core face has exactly one REVERSED copy in another face and none in the same direction
 *   adjacency the face pairs found by that matching
 *   crossings no two distinct segments cross or touch anywhere, other than consecutive segments meeting at their shared end
 *   angles   at every point of a core outline, the angles of all faces having a corner there add up to 360°
 *   coverage every sample point in the window lies inside exactly ONE face, with winding exactly 1 (stratified samples + probes
 *            10⁻⁷ from every core segment and around every core vertex) */
function checkTiling(faces, opts) {
  const scale = opts.scale || 1, tol = (opts.tol || 1e-9) * scale, eps = (opts.eps || 1e-7) * scale, core = opts.core, inWin = opts.window.contains;
  const out = { faces: { ok: true, bad: [] }, matching: { ok: true, segments: 0, unmatched: 0, sameDirection: 0, multiple: 0, worst: [] }, adjacency: new Map(),
    crossings: { ok: true, tested: 0, count: 0, worst: [] }, angles: { ok: true, vertices: 0, bad: 0, worstDeg: 0, worst: [] }, coverage: { ok: true, probes: 0, gaps: 0, overlaps: 0, worst: [] } };
  const pix = new PointIndex(tol), rings = faces.map(f => f.pts.map(p => pix.id(p)));
  // faces
  faces.forEach((f, i) => { const r = rings[i], A = signedArea(f.pts), seen = new Set(); let rep = false, zero = false;
    r.forEach((id, k) => { if (seen.has(id)) rep = true; seen.add(id); if (id === r[(k + 1) % r.length]) zero = true; });
    if (!(A > 0) || rep || zero) { out.faces.ok = false; out.faces.bad.push({ face: f.id, area: A, repeated: rep, zeroLength: zero, at: centroid(f.pts) }); } });
  // directed segments
  const dir = new Map(); rings.forEach((r, i) => r.forEach((a, k) => { const b = r[(k + 1) % r.length], key = a + '>' + b; const l = dir.get(key); if (l) l.push(i); else dir.set(key, [i]); }));
  rings.forEach((r, i) => { if (!core.has(faces[i].id)) return;
    r.forEach((a, k) => { const b = r[(k + 1) % r.length], same = dir.get(a + '>' + b).length - 1, rev = (dir.get(b + '>' + a) || []).filter(j => j !== i); out.matching.segments++;
      const mid = lerpP(pix.pts[a], pix.pts[b], 0.5);
      if (same > 0) { out.matching.sameDirection++; out.matching.worst.length < 12 && out.matching.worst.push({ kind: 'same-direction', at: mid, face: faces[i].id }); }
      if (rev.length === 0) { out.matching.unmatched++; out.matching.worst.length < 12 && out.matching.worst.push({ kind: 'unmatched', at: mid, face: faces[i].id }); }
      else if (rev.length > 1) { out.matching.multiple++; out.matching.worst.length < 12 && out.matching.worst.push({ kind: 'multiple', at: mid, face: faces[i].id }); }
      else { const j = rev[0], s = out.adjacency.get(faces[i].id) || new Set(); s.add(faces[j].id); out.adjacency.set(faces[i].id, s); } }); });
  out.matching.ok = out.matching.unmatched === 0 && out.matching.sameDirection === 0 && out.matching.multiple === 0;
  // crossings: every distinct undirected segment against every other, through a uniform grid
  const segs = [], segSeen = new Set();
  rings.forEach(r => r.forEach((a, k) => { const b = r[(k + 1) % r.length], key = a < b ? a + '-' + b : b + '-' + a; if (a === b || segSeen.has(key)) return; segSeen.add(key); segs.push([a, b]); }));
  let total = 0; segs.forEach(([a, b]) => { total += dist(pix.pts[a], pix.pts[b]); });
  const cell = Math.max(2 * total / Math.max(1, segs.length), scale / 64), grid = new Map(), sb = segs.map(([a, b]) => bbox([pix.pts[a], pix.pts[b]]));
  segs.forEach((s, i) => { const B = sb[i]; for (let cx = Math.floor((B.x0 - tol) / cell); cx <= Math.floor((B.x1 + tol) / cell); cx++) for (let cy = Math.floor((B.y0 - tol) / cell); cy <= Math.floor((B.y1 + tol) / cell); cy++) {
    const k = cx + ',' + cy, l = grid.get(k); if (l) l.push(i); else grid.set(k, [i]); } });
  grid.forEach((l, k) => { if (l.length < 2) return; const [cx, cy] = k.split(',').map(Number);
    for (let x = 0; x < l.length; x++) for (let y = x + 1; y < l.length; y++) { const i = l[x], j = l[y], A = sb[i], B = sb[j];
      if (A.x1 < B.x0 - tol || B.x1 < A.x0 - tol || A.y1 < B.y0 - tol || B.y1 < A.y0 - tol) continue;
      if (Math.floor((Math.max(A.x0, B.x0) - tol) / cell) !== cx || Math.floor((Math.max(A.y0, B.y0) - tol) / cell) !== cy) continue;   // each pair once: in the first cell both are in
      out.crossings.tested++;
      const c = segConflict(segs[i], segs[j], pix.pts, tol);
      if (c) { out.crossings.count++; out.crossings.worst.length < 12 && out.crossings.worst.push({ kind: c, at: lerpP(pix.pts[segs[i][0]], pix.pts[segs[i][1]], 0.5) }); } } });
  out.crossings.ok = out.crossings.count === 0;
  // angle sums
  const corners = new Map(); rings.forEach((r, i) => r.forEach((id, k) => { const n = r.length, a = pix.pts[r[(k + n - 1) % n]], p = pix.pts[id], b = pix.pts[r[(k + 1) % n]];
    const l = corners.get(id) || []; l.push({ face: faces[i].id, ang: interiorAngle(a, p, b) }); corners.set(id, l); }));
  const coreVerts = new Set(); rings.forEach((r, i) => { if (core.has(faces[i].id)) r.forEach(id => coreVerts.add(id)); });
  coreVerts.forEach(id => { const sum = corners.get(id).reduce((s, c) => s + c.ang, 0), d = Math.abs(sum - TAU); out.angles.vertices++;
    if (d * 180 / Math.PI > out.angles.worstDeg) out.angles.worstDeg = d * 180 / Math.PI;
    if (d > 1e-9) { out.angles.bad++; out.angles.worst.length < 12 && out.angles.worst.push({ at: pix.pts[id], sumDeg: sum * 180 / Math.PI, faces: corners.get(id).map(c => c.face) }); } });
  out.angles.ok = out.angles.bad === 0;
  // coverage
  // probes: both sides of every core segment, and a ring round every core vertex. Dense curves are thinned to about 4000 segments,
  // but sharp corners (angle away from 180°) are always probed.
  const fb = faces.map(f => bbox(f.pts)), rnd = seeded(opts.seed || 20261009), probes = [];
  (opts.window.samples(rnd, opts.samples || 2500)).forEach(p => probes.push(p));
  let coreSegs = 0; rings.forEach((r, i) => { if (core.has(faces[i].id)) coreSegs += r.length; });
  const stride = Math.max(1, Math.floor(coreSegs / 4000)); out.coverage.stride = stride;
  if (opts.probes !== false) rings.forEach((r, i) => { if (!core.has(faces[i].id)) return; const n = r.length;
    r.forEach((id, k) => { const a = pix.pts[id], b = pix.pts[r[(k + 1) % n]], z = pix.pts[r[(k + n - 1) % n]], L = dist(a, b);
      const sharp = Math.abs(interiorAngle(z, a, b) - Math.PI) > 1e-3; if (!sharp && k % stride) return;
      if (L >= 4 * eps) { const m = lerpP(a, b, 0.5), nx = -(b.y - a.y) / L, ny = (b.x - a.x) / L; probes.push(P(m.x + nx * eps, m.y + ny * eps), P(m.x - nx * eps, m.y - ny * eps)); }
      for (let q = 0; q < 8; q++) { const t = (q + 0.37) * TAU / 8; probes.push(P(a.x + 10 * eps * Math.cos(t), a.y + 10 * eps * Math.sin(t))); } }); });
  // Counted face by face, NOT as a sum of winding numbers. When every edge is shared in opposite directions the windings always add
  // up to 1, even where a folded tile covers its neighbours (+1 −1 +1). So the rule is: exactly one face contains the point, with
  // winding exactly 1.
  probes.forEach(p => { if (!inWin(p)) return; out.coverage.probes++; let c = 0, odd = 0;
    for (let i = 0; i < faces.length; i++) { const B = fb[i]; if (p.x < B.x0 || p.x > B.x1 || p.y < B.y0 || p.y > B.y1) continue; const w = winding(faces[i].pts, p); if (w) { c++; if (w !== 1) odd++; } }
    if (c === 0) { out.coverage.gaps++; out.coverage.worst.length < 12 && out.coverage.worst.push({ kind: 'gap', at: p }); }
    else if (c !== 1 || odd) { out.coverage.overlaps++; out.coverage.worst.length < 12 && out.coverage.worst.push({ kind: odd ? 'folded / reversed' : 'overlap ×' + c, at: p }); } });
  out.coverage.ok = out.coverage.gaps === 0 && out.coverage.overlaps === 0 && out.coverage.probes > 0;
  return out;
}
// '' when two distinct segments meet correctly (not at all, or end-to-end at a shared point without folding back); otherwise the conflict
function segConflict(s, t, pts, tol) {
  const shared = s[0] === t[0] || s[0] === t[1] ? s[0] : s[1] === t[0] || s[1] === t[1] ? s[1] : -1;
  if (shared >= 0) {
    const p = pts[shared], q1 = pts[s[0] === shared ? s[1] : s[0]], q2 = pts[t[0] === shared ? t[1] : t[0]];
    if (distPS(q1, p, q2) <= tol || distPS(q2, p, q1) <= tol) return 'overlap';    // folded back along each other
    return '';
  }
  const a = pts[s[0]], b = pts[s[1]], c = pts[t[0]], d = pts[t[1]];
  const o1 = cross(b.x - a.x, b.y - a.y, c.x - a.x, c.y - a.y), o2 = cross(b.x - a.x, b.y - a.y, d.x - a.x, d.y - a.y);
  const o3 = cross(d.x - c.x, d.y - c.y, a.x - c.x, a.y - c.y), o4 = cross(d.x - c.x, d.y - c.y, b.x - c.x, b.y - c.y);
  if (((o1 > 0 && o2 < 0) || (o1 < 0 && o2 > 0)) && ((o3 > 0 && o4 < 0) || (o3 < 0 && o4 > 0))) return 'cross';
  if (Math.min(distPS(a, c, d), distPS(b, c, d), distPS(c, a, b), distPS(d, a, b)) <= tol) return 'touch';
  return '';
}

// The sampling window and the core faces of a patch: a box in lattice coordinates on which EVERY face that could cover a point
// is inside the patch. A face at offset i covers u ∈ [i + umin, i + umax]; so a point is safe when [u − umax, u − umin] ⊆ [−n, n].
function patchWindow(patch) {
  const g = patch.grid, L = g.lattice, n = patch.n; let u0 = Infinity, u1 = -Infinity, v0 = Infinity, v1 = -Infinity;
  g.faces.forEach(fc => faceOutline(g, fc, [0, 0]).pts.forEach(p => { const [u, v] = toLat(L, p); u0 = Math.min(u0, u); u1 = Math.max(u1, u); v0 = Math.min(v0, v); v1 = Math.max(v1, v); }));
  const eta = 1e-6, lo = [-n + u1 + eta, -n + v1 + eta], hi = [n + u0 - eta, n + v0 - eta];
  const contains = p => { const [u, v] = toLat(L, p); return u >= lo[0] && u <= hi[0] && v >= lo[1] && v <= hi[1]; };
  const samples = (rnd, count) => { const k = Math.max(2, Math.round(Math.sqrt(count))), out = [];
    for (let i = 0; i < k; i++) for (let j = 0; j < k; j++) out.push(fromLat(L, lo[0] + (hi[0] - lo[0]) * (i + rnd()) / k, lo[1] + (hi[1] - lo[1]) * (j + rnd()) / k)); return out; };
  const core = new Set(patch.faces.filter(f => f.outline.every(contains)).map(f => f.id));
  return { lo, hi, contains, samples, core, ok: lo[0] < hi[0] && lo[1] < hi[1] && core.size > 0, overhang: { u: [u0, u1], v: [v0, v1] } };
}

/* validate — the full report on a patch (as drawn) and the quotient it claims to come from. */
function validate(patch, opts) {
  opts = opts || {};
  const g = patch.grid, V = patch.vertices, E = patch.edges, F = patch.faces, H = patch.half, rows = [], add = (name, ok, detail) => rows.push({ name, ok: !!ok, detail });
  const scale = Math.sqrt(Math.abs(latDet(g.lattice))) || 1, tol = 1e-9 * scale;
  // 1. quotient
  const q = checkQuotient(g); add('quotient', q.ok, { euler: q.euler, det: q.det, errors: q.errors });
  // 2. half-edges
  const heErr = [];
  F.forEach(f => { const m = f.half.length; f.half.forEach((hid, k) => { const h = H[hid];
    if (h.next !== f.half[(k + 1) % m] || H[h.next].prev !== hid) heErr.push(`face ${f.key}: broken next/prev at side ${k}`);
    if (h.target !== H[h.next].origin) heErr.push(`face ${f.key}: side ${k} ends at vertex ${h.target}, side ${(k + 1) % m} starts at ${H[h.next].origin}`); }); });
  E.forEach(e => { if (e.half.length < 1 || e.half.length > 2) heErr.push(`edge ${e.key} has ${e.half.length} half-edges`);
    if (e.half.length === 2) { const [a, b] = e.half.map(i => H[i]); if (a.twin !== b.id || b.twin !== a.id) heErr.push(`edge ${e.key}: twins not mutual`); if (a.dir === b.dir) heErr.push(`edge ${e.key}: both faces run it the same way`);
      if (a.origin !== b.target || a.target !== b.origin) heErr.push(`edge ${e.key}: twins do not join the same vertices`); } });
  add('half-edges', !heErr.length, { faces: F.length, edges: E.length, vertices: V.length, interiorEdges: E.filter(e => e.half.length === 2).length, errors: heErr.slice(0, 12) });
  // 3. patch topology: a disc (V − E + F = 1) bounded by ONE counter-clockwise cycle; a hole shows as a clockwise boundary cycle
  const bnd = H.filter(h => h.twin < 0), seen = new Set(), cycles = [];
  bnd.forEach(h0 => { if (seen.has(h0.id)) return; const cyc = []; let h = h0, guard = 0;
    while (!seen.has(h.id) && guard++ < bnd.length + 5) { seen.add(h.id); cyc.push(h); let x = H[h.next], g2 = 0; while (x.twin >= 0 && g2++ < 64) x = H[H[x.twin].next]; h = x; }
    const pts = cyc.map(c => V[c.origin].pos); cycles.push({ area: signedArea(pts), pts }); });
  // M2A PATCH: a HOLE is a clockwise boundary loop reaching into the core window (where every point must be covered). The finite
  // patch's own rim may pinch into several counter-clockwise loops (or pockets outside the window) when shapes are long or slanted.
  // That is a property of the test patch, not of the tiling (M1's square grids never produced it).
  const chi = V.length - E.length + F.length, win0 = patchWindow(patch), holes = cycles.filter(c => c.area < 0 && c.pts.some(win0.contains)).length;
  add('patch-topology', holes === 0 && cycles.some(c => c.area > 0), { euler: chi, boundaryCycles: cycles.length, holes, rimLoops: cycles.filter(c => c.area > 0).length, rimPockets: cycles.filter(c => c.area < 0).length - holes });
  // 4. vertex stars: around every interior vertex the rotation next(twin(h)) visits each outgoing half-edge once, turning clockwise
  //    through exactly 360° (the explicit topology agrees with the geometry's order)
  let interiorV = 0; const starErr = [], degrees = {};
  V.forEach(v => { if (!v.out.every(h => H[h].twin >= 0)) return; interiorV++; degrees[v.out.length] = (degrees[v.out.length] || 0) + 1;
    const dirOf = h => { const e = E[H[h].edge], line = H[h].dir > 0 ? e.pts : e.pts.slice().reverse(); return Math.atan2(line[1].y - line[0].y, line[1].x - line[0].x); };
    let h = v.out[0], turn = 0, broken = false; const visit = new Set();
    for (let k = 0; k < v.out.length; k++) { visit.add(h); const tw = H[h].twin, nx = tw >= 0 ? H[tw].next : -1;
      if (nx < 0 || H[nx].origin !== v.id) { broken = true; break; }        // the rotation leaves this vertex: the topology is inconsistent
      let d = dirOf(h) - dirOf(nx); while (d <= 0) d += TAU; while (d > TAU) d -= TAU; turn += d; h = nx; }
    if (broken || h !== v.out[0] || visit.size !== v.out.length || Math.abs(turn - TAU) > 1e-9) starErr.push({ vertex: v.key, degree: v.out.length, turnDeg: turn * 180 / Math.PI, broken, at: v.pos }); });
  add('vertex-stars', !starErr.length && interiorV > 0, { interiorVertices: interiorV, degrees, errors: starErr.slice(0, 12) });
  // 5. shared edges and vertices, against an INDEPENDENT derivation of every face from the quotient
  let edgeDev = 0, vertDev = 0, faceDev = 0, worstEdge = null; const derived = new Map();
  if (q.ok) {
    F.forEach(f => { const d = faceOutline(g, fcls(g, f.cls), f.at); derived.set(f.id, d);
      d.sides.forEach((line, k) => { const vtx = V[f.corners[k]].pos; vertDev = Math.max(vertDev, dist(line[0], vtx)); });
      if (d.pts.length !== f.outline.length) faceDev = Infinity; else d.pts.forEach((p, i) => { faceDev = Math.max(faceDev, dist(p, f.outline[i])); }); });
    E.forEach(e => { if (e.half.length !== 2) return; const [a, b] = e.half.map(i => H[i]), la = derived.get(a.face).sides[a.side], lb = derived.get(b.face).sides[b.side];
      if (la.length !== lb.length) { edgeDev = Infinity; return; }
      la.forEach((p, i) => { const d = dist(p, lb[lb.length - 1 - i]); if (d > edgeDev) { edgeDev = d; worstEdge = { edge: e.key, at: p }; } }); });
  }
  add('shared-edges', q.ok && edgeDev <= tol && vertDev <= tol && faceDev <= tol, { maxSharedEdgeDev: edgeDev, maxVertexDev: vertDev, maxFaceVsDerivationDev: faceDev, worst: worstEdge });
  // 6. transformations: each neighbour placement is an isometry (here a lattice translation) and carries the face exactly onto the neighbour
  let tDev = 0, tLat = 0, notIso = 0, notTrans = 0, asym = 0, linked = 0;
  F.forEach(f => f.neighbours.forEach(nb => { if (nb.face < 0) return; linked++; const T = nb.T, o = F[nb.face];
    if (Math.abs(T[0] * T[0] + T[1] * T[1] - 1) > 1e-9 || Math.abs(T[2] * T[2] + T[3] * T[3] - 1) > 1e-9 || Math.abs(T[0] * T[2] + T[1] * T[3]) > 1e-9) notIso++;
    else if (mdiff([T[0], T[1], T[2], T[3]], [1, 0, 0, 1]) > 1e-9) notTrans++;            // M1: translation grids only
    const uv = toLat(g.lattice, P(T[4], T[5])); tLat = Math.max(tLat, Math.abs(uv[0] - Math.round(uv[0])), Math.abs(uv[1] - Math.round(uv[1])));
    if (!o.neighbours.some(x => x.face === f.id && x.edge === nb.edge)) asym++;
    if (o.cls !== f.cls) return;                     // M2 FEASIBILITY PATCH (kept in M2A): a neighbour of ANOTHER face class is not an image of this face
    if (o.outline.length !== f.outline.length) tDev = Infinity; else f.outline.forEach((p, i) => { tDev = Math.max(tDev, dist(mapp(T, p), o.outline[i])); }); }));
  add('transformations', notIso === 0 && notTrans === 0 && asym === 0 && tLat < 1e-9 && tDev <= tol, { links: linked, notIsometry: notIso, notTranslation: notTrans, asymmetric: asym, offLattice: tLat, maxImageDev: tDev });
  // 7–11. geometry only
  const win = patchWindow(patch);
  if (!win.ok) add('window', false, 'patch too small for its tile: no core faces');
  const geo = checkTiling(F.map(f => ({ id: f.id, pts: f.outline })), { core: win.core, window: win, scale, samples: opts.samples, probes: opts.probes, seed: opts.seed });
  add('faces', geo.faces.ok, { bad: geo.faces.bad.slice(0, 12) });
  add('edge-matching', geo.matching.ok, { coreSegments: geo.matching.segments, unmatched: geo.matching.unmatched, sameDirection: geo.matching.sameDirection, multiple: geo.matching.multiple, worst: geo.matching.worst });
  let adjBad = 0; win.core.forEach(fid => { const ex = new Set(F[fid].neighbours.filter(x => x.face >= 0).map(x => x.face)), gm = geo.adjacency.get(fid) || new Set();
    if (ex.size !== gm.size || [...ex].some(x => !gm.has(x))) adjBad++; });
  add('adjacency', adjBad === 0 && win.core.size > 0, { coreFaces: win.core.size, facesWhoseNeighboursDiffer: adjBad });
  add('intersections', geo.crossings.ok, { pairsTested: geo.crossings.tested, conflicts: geo.crossings.count, worst: geo.crossings.worst });
  add('vertex-angles', geo.angles.ok && geo.angles.vertices > 0, { vertices: geo.angles.vertices, bad: geo.angles.bad, worstDeg: geo.angles.worstDeg, worst: geo.angles.worst });
  add('coverage', geo.coverage.ok, { probes: geo.coverage.probes, gaps: geo.coverage.gaps, overlaps: geo.coverage.overlaps, worst: geo.coverage.worst });
  // 12. area: the face classes fill one lattice cell exactly
  const areaSum = g.faces.reduce((s, fc) => s + signedArea(faceOutline(g, fc, [0, 0]).pts), 0), cellA = Math.abs(latDet(g.lattice));
  add('area', Math.abs(areaSum - cellA) <= 1e-9 * cellA, { faceClassArea: areaSum, latticeCellArea: cellA });
  const problems = [].concat(geo.matching.worst, geo.crossings.worst, geo.angles.worst.map(w => Object.assign({ kind: 'angle sum ' + w.sumDeg.toFixed(3) + '°' }, w)), geo.coverage.worst, geo.faces.bad.map(b => ({ kind: 'face', at: b.at })), starErr.map(s => ({ kind: 'star', at: s.at })));
  return { ok: rows.every(r => r.ok), rows, problems, window: win };
}

/* ---------------- summary ---------------- */
function describe(g, patch) {
  const pr = pairings(g);
  return { kind: g.kind, symmetry: g.symmetry, quotient: { vertices: g.vertices.length, edges: g.edges.length, faces: g.faces.length, euler: g.vertices.length - g.edges.length + g.faces.length },
    lattice: g.lattice, cellArea: latDet(g.lattice), nodes: nodeCount(g), sides: sideCount(g),
    pairings: pr.map(p => ({ edge: p.edge, from: p.from && p.from.side, to: p.to && p.to.side, by: p.vector, lattice: p.lattice })),
    patch: patch ? { n: patch.n, vertices: patch.vertices.length, edges: patch.edges.length, faces: patch.faces.length, halfEdges: patch.half.length } : null };
}

return {
  P, TAU, IDM, mmul, det, minv, mapp, translation, mdiff, dist, lerpP, clone, seeded,
  latVec, latDet, toLat, fromLat, relToWorld, worldToRel, LIMITS, SQUARE_CELL,
  squareGrid, vcls, ecls, fcls, vpos, sideEnds, edgeEnds, edgeLine, edgeNodes, faceOutline, faceCorners, cellCorners, pairings, checkQuotient,
  withCell, cornerRule, lerpCell, dragCorner, moveVertexClass, setNodes, insertNode, moveNode, removeNode, dragNode, setCurve, relOnEdge, nodeCount, sideCount,
  segX, distPS, cellProblem, polygonProblem, problem,
  signedArea, centroid, patchSize, buildPatch, refreshGeometry, faceAt, placements,
  winding, checkTiling, segConflict, patchWindow, validate, describe, elKey
};
});
