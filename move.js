/* tessellation-mobile-workspace-v6.6-grid-m2b-split / move.js · EDITING THE GRID (M2B): move, add and remove points, merge two junctions,
 * and now ADD AN EDGE THAT SPLITS A SHAPE
 *
 * THE STATE  { block, removed, moves, dissolved, nodes, identified [, x] }
 *   block, removed  as in M2A (merge.js): the repeat block and the removed edge classes of the triangular grid. They fix which shapes
 *                   there are and which shapes meet: the ARRANGEMENT — as long as there is no x.
 *   x               (only after a NEW edge has been added) the arrangement stored EXPLICITLY: its vertices [id, x, y], its edges
 *                   [id, v0, v1, shiftX, shiftY] and its faces [id, [[edge, dir, atX, atY], …]], plus a counter for new names and the
 *                   list of added edges. From then on merging and splitting edit these lists directly; block still gives the repeat
 *                   lattice, removed is only what had been removed before. Everything below (moves, nodes, dissolved, identified)
 *                   works on either description in the same way.
 *   moves           [[vertex, dx, dy], …]: how far each structural vertex has moved from its base place. A vertex is a class of the
 *                   repeat block, so every copy moves the same way (checkpoint 1).
 *   nodes           [[edge, [[s, t], …]], …]: points ADDED on an edge, at most 3 per edge, in the edge's own frame (s along it from its
 *                   first end, t across it, both in units of the edge). They move with the edge's ends. Each edge is one object shared
 *                   by the two shapes on its sides, repeated with the grid.
 *   dissolved       [vertex, …]: structural points REMOVED. Only a point where exactly two shapes meet (two edges) can be removed
 *                   without changing the arrangement; its two edges then form one boundary between the same two shapes. Its last
 *                   position stays the frame of the added points on those two edges.
 *   identified      [[u, w, ox, oy], …]: MERGED vertices: vertex u (its copy at offset [0, 0]) is the same point as vertex w's copy at
 *                   offset (ox, oy). Made by dragging one junction onto a neighbouring one joined to it by an edge: that edge shrinks to
 *                   nothing (edge contraction), in every copy. A union-find with lattice offsets turns the list into merged points.
 *
 * ADDING AN EDGE (split): a straight edge between two points on the boundary of ONE shape, inside it. The shape becomes two shapes;
 *   one edge more, one face more (and one vertex more for every end that was not a vertex yet), in every copy.
 *     restore   the two ends are neighbours in the triangular grid (or lie on one grid line with only removed edges and edge-less grid
 *               points between them): the removed edges come back — `removed` shrinks, nothing else is needed, and M2A's judges
 *               apply as they are. Grid points on the way stay out of sight (dissolved), so the edge is one straight boundary.
 *     new       any other pair. The triangular grid has no such edge, so the arrangement can no longer be written as "the grid minus
 *               edges": it is stored explicitly (x) from then on. An end that is an added point, or any place on an edge, first
 *               becomes a structural vertex (the edge it lies on is cut in two there: both shapes beside that edge get the corner).
 *   NOT possible, and refused with the reason: two points on different shapes; two neighbouring corners (already joined by a straight
 *   edge); a straight edge that would lie along a side, pass through another corner, or leave the shape (across a dent); and anything
 *   the checks below reject (a corner under 6°, an edge shorter than 0.2, an edge closer than 0.05 to a side it does not meet).
 *
 * MERGING TWO JUNCTIONS (contract): u and w become one point where deg(u) + deg(w) − 2 edges meet; the edge between them disappears; the
 *   two faces beside it each lose a side; every other face keeps its sides. Possible only when
 *     - u and w are joined by an edge (otherwise a shape would be pinched in two, or the shapes between them would collapse),
 *     - they are not copies of the same vertex (a repeat vector would collapse to zero),
 *     - neither face beside the edge drops below 3 corners (a triangle would collapse to a two-sided sliver),
 *     - the merged grid passes the same checks as everything else.
 *   This CHANGES the arrangement (vertex types), unlike adding, moving or removing points.
 *
 * WHAT IS A VERTEX HERE (and what can be removed)
 *   junction       a point where 3 or more shapes meet (3 or more edges): a vertex of the arrangement. It CANNOT be removed without
 *                  changing the arrangement: its edges would have to disappear (shapes merge) or end at another junction (two junctions
 *                  fuse; vertex types change, and a triangle beside it would collapse to two sides). removePoint() refuses and says why.
 *   point          a structural point where exactly two shapes meet (left by merges): not a vertex of the arrangement; removable.
 *   added point    a node on an edge: not a vertex of the arrangement; it can be added (where there is room, up to 3 per original
 *                  edge), moved and removed.
 *   Adding, moving and removing points never changes the arrangement (topology), only the shapes (geometry). Removing never merges.
 *
 * THE BOUNDARIES AS DRAWN (structure + geometry)
 *   Between two junctions or kept points runs one boundary: one original edge, or several joined at dissolved points (a chain). The
 *   drawn grid (gridOf) has one edge per boundary, with all its added points as nodes (relative to the boundary's ends), and one face
 *   per face of the arrangement (same ids). It is a grid.js / topo.js grid, so M1's validator and classify.js apply to it unchanged.
 *
 * VALID, ALWAYS (checked on every drag frame, every added or removed point, every merge, every split):
 *   (a) every face touching what changed is a simple, counter-clockwise polygon (through its added points), with no corner under 6° or
 *       over 354°, no straight edge shorter than 0.2 and no segment between added points shorter than 0.06, no side within 0.05 of a
 *       side it does not meet (these margins are checked where something changed);
 *   (b) round every vertex at the ends of what changed, the faces' corners add up to exactly 360° (the edges keep their order);
 *   (c) the areas of all faces add up to the repeat block's area.
 *   (a)+(b) make the drawing one-to-one near every point; (c) makes it cover the plane once: no gaps, overlaps or crossings. When a
 *   drag ends, checkAll() repeats (a)-(c) for the whole grid; M1's 13 checks (judge) follow as an independent audit. A drag follows the
 *   finger in small steps and stops (or slides) at the last valid place. No snapping. */
(function (root, factory) {
  const M = factory(root);
  if (typeof module === 'object' && module.exports) module.exports = M; else root.TessMove = M;
})(typeof self !== 'undefined' ? self : globalThis, function (root) {
'use strict';
const node = typeof module === 'object' && module.exports;
const G = node ? require('./grid.js') : root.TessGrid, T = node ? require('./topo.js') : root.TessTopo, Mg = node ? require('./merge.js') : root.TessMerge;
const C = () => node ? require('./classify.js') : root.TessClassify;
const P = G.P, TAU = 2 * Math.PI;
const add2 = (a, b) => [a[0] + b[0], a[1] + b[1]], sub2 = (a, b) => [a[0] - b[0], a[1] - b[1]], plus = (p, q) => P(p.x + q.x, p.y + q.y);
const LIMITS = { minEdge: 0.2, minSeg: 0.06, minAngle: 6 * Math.PI / 180, clear: 0.05, step: 0.04, sumTol: 1e-7, areaTol: 1e-7, maxNodes: 3 };
const BASIC = { minEdge: 1e-9, minSeg: 1e-9, minAngle: 1e-9, clear: 1e-12 };     // plain validity, without the comfort margins

/* ---------------- states ---------------- */
const byKey = (x, y) => x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : 0;
const baseOf = s => ({ block: s.block, removed: s.removed });
function newState(key) { return { block: key, removed: [], moves: [], dissolved: [], nodes: [], identified: [] }; }
const copy = (s, o) => { const n = Object.assign({ block: s.block, removed: s.removed, moves: s.moves || [], dissolved: s.dissolved || [], nodes: s.nodes || [], identified: s.identified || [] }, s.x ? { x: s.x } : null, o); if (!n.x) delete n.x; return n; };
const movesOf = s => new Map((s.moves || []).map(([v, x, y]) => [v, P(x, y)]));
const nodesOf = s => new Map((s.nodes || []).map(([e, l]) => [e, l.map(([a, b]) => ({ s: a, t: b }))]));
// (an explicit arrangement x is never changed in place: its text is worked out once)
const xKeys = new WeakMap(), xKey = x => { let k = xKeys.get(x); if (!k) { k = JSON.stringify(x); xKeys.set(x, k); } return k; };
const structKey = s => Mg.stateKey(s) + '|' + (s.dissolved || []).join(',') + '|' + (s.identified || []).map(x => x.join(',')).join(';') + (s.x ? '|x' + xKey(s.x) : '');
const stateKey = s => structKey(s) + '|' + (s.moves || []).map(m => m.join(',')).join(';') + '|' + (s.nodes || []).map(([e, l]) => e + ':' + l.map(n => n.join(',')).join(' ')).join(';');
function withMove(s, vid, d) { const m = (s.moves || []).filter(x => x[0] !== vid); if (Math.hypot(d.x, d.y) > 1e-12) m.push([vid, d.x, d.y]); return copy(s, { moves: m.sort(byKey) }); }
function withNodes(s, edge, list) { const n = (s.nodes || []).filter(x => x[0] !== edge); if (list.length) n.push([edge, list.map(x => [x.s, x.t])]); return copy(s, { nodes: n.sort(byKey) }); }
const offsetOf = (s, vid) => { const m = (s.moves || []).find(x => x[0] === vid); return m ? P(m[1], m[2]) : P(0, 0); };

/* ---------------- the arrangement: the triangular grid minus edges (merge.js), or the explicit lists of x ---------------- */
const xGrids = new WeakMap();
function baseGrid(s) {
  if (!s.x) return Mg.gridOf(baseOf(s));
  let c = xGrids.get(s.x); if (c && c.block === s.block) return c.g;
  const x = s.x, g = { lattice: Mg.base(s.block).sc.lattice, vertices: x.v.map(([id, px, py]) => ({ id, pos: P(px, py) })), edges: x.e.map(([id, v0, v1, sx, sy]) => ({ id, v0, v1, shift: [sx, sy] })),
    faces: x.f.map(([id, sides]) => ({ id, sides: sides.map(([edge, dir, ax, ay]) => ({ edge, dir, at: [ax, ay] })) })) };
  xGrids.set(x, { block: s.block, g }); return g;
}

/* ---------------- structure: the boundaries between shapes (cached) ---------------- */
const structCache = new Map();
function structure(s) {
  const k = structKey(s); let st = structCache.get(k); if (st) return st;
  const gm = baseGrid(s), present = new Set(gm.vertices.map(v => v.id)), base = new Map(gm.vertices.map(v => [v.id, v.pos]));
  let problem = null;
  // 1. merged vertices: union-find with lattice offsets (v at x is root at x + o); the smaller name is the root
  const par = new Map(gm.vertices.map(v => [v.id, { p: v.id, o: [0, 0] }]));
  const find = v => { let o = [0, 0], x = v; while (par.get(x).p !== x) { o = add2(o, par.get(x).o); x = par.get(x).p; } return { r: x, o }; };
  (s.identified || []).forEach(([a, b, ox, oy]) => { if (!present.has(a) || !present.has(b)) return; const fa = find(a), fb = find(b), d = sub2(add2([ox, oy], fb.o), fa.o);   // root(a) at 0 is root(b) at d
    if (fa.r === fb.r) { if (d[0] || d[1]) problem = problem || 'collapse'; return; }
    if (fa.r < fb.r) par.set(fb.r, { p: fa.r, o: [-d[0], -d[1]] }); else par.set(fa.r, { p: fb.r, o: d }); });
  // 2. the grid with merged vertices: an edge whose two ends became the same point is gone; faces lose those sides
  const gcE = [], collapsed = new Set();
  gm.edges.forEach(e => { const a = find(e.v0), b = find(e.v1), sh = sub2(add2(e.shift, b.o), a.o);
    if (a.r === b.r && !sh[0] && !sh[1]) { collapsed.add(e.id); return; }
    gcE.push({ id: e.id, v0: a.r, v1: b.r, shift: sh, o0: a.o }); });
  const E = new Map(gcE.map(e => [e.id, e])), roots = gm.vertices.filter(v => find(v.id).r === v.id && gcE.some(e => e.v0 === v.id || e.v1 === v.id));
  const gcF = gm.faces.map(f => ({ id: f.id, sides: f.sides.filter(x => !collapsed.has(x.edge)).map(x => ({ edge: x.edge, dir: x.dir, at: add2(x.at, E.get(x.edge).o0) })) }));
  if (gcF.some(f => f.sides.length < 2)) problem = problem || 'collapse';
  // 3. the order of the edges round every point, from the faces (a face arriving along h_in leaves along h_out: then the twin of h_in
  //    follows h_out counter-clockwise). One cycle per point; two cycles = the point is pinched (two fans touching)
  const hk2 = (e, d) => e + (d > 0 ? '>' : '<'), succ = new Map();
  gcF.forEach(f => { const n = f.sides.length; f.sides.forEach((x, i) => { const p = f.sides[(i - 1 + n) % n]; succ.set(hk2(x.edge, x.dir), { e: p.edge, d: -p.dir }); }); });
  const outC = new Map();
  roots.forEach(v => { const all = []; gcE.forEach(e => { if (e.v0 === v.id) all.push({ e: e.id, d: 1 }); if (e.v1 === v.id) all.push({ e: e.id, d: -1 }); });
    const cyc = []; let h = all[0], guard = 0; if (!h) return;
    do { cyc.push(h); h = succ.get(hk2(h.e, h.d)); } while (h && !(h.e === all[0].e && h.d === all[0].d) && ++guard < 1000);
    if (!h || cyc.length !== all.length) problem = problem || 'pinch';
    outC.set(v.id, cyc); });
  const D = new Set((s.dissolved || []).filter(v => present.has(v) && find(v).r === v));
  const inc = new Map(roots.map(v => [v.id, []])); gcE.forEach(e => { inc.get(e.v0).push({ e: e.id, d: 1 }); inc.get(e.v1).push({ e: e.id, d: -1 }); });
  // walk from every kept vertex along each of its edges, through dissolved points, to the next kept vertex: one boundary
  const edges = [], byId = new Map(), partOf = new Map();
  roots.forEach(v => { if (D.has(v.id)) return; inc.get(v.id).forEach(h0 => {
    const parts = []; let h = h0, o = [0, 0], end = null;
    for (let guard = 0; ; guard++) { if (guard > 10000) { problem = problem || 'collapse'; return; }
      const e = E.get(h.e); parts.push({ edge: h.e, dir: h.d, v0off: h.d > 0 ? o.slice() : sub2(o, e.shift) });
      const nx = h.d > 0 ? e.v1 : e.v0; o = h.d > 0 ? add2(o, e.shift) : sub2(o, e.shift);
      if (!D.has(nx)) { end = nx; break; }
      h = inc.get(nx).find(x => !(x.e === h.e && x.d === -h.d)); }
    if (parts.length === 1 && h0.d < 0) return;                          // a single edge: once, in its own direction
    const fwd = parts.map(p => p.edge + (p.dir > 0 ? '>' : '<')).join('+'), rev = parts.slice().reverse().map(p => p.edge + (p.dir > 0 ? '<' : '>')).join('+');
    if (parts.length > 1 && fwd > rev) return;                           // a chain: once, in the direction with the smaller name
    const id = parts.length === 1 ? parts[0].edge : fwd; if (byId.has(id)) return;
    const ge = { id, v0: v.id, v1: end, shift: o, parts }; edges.push(ge); byId.set(id, ge);
    parts.forEach((p, i) => partOf.set(p.edge, { ge, i, dir: p.dir, v0off: p.v0off }));
  }); });
  // the faces of the merge grid, their sides along the boundaries (consecutive original edges of one chain become one side)
  const faces = gcF.map(f => {
    const raw = f.sides.map(x => { const q = partOf.get(x.edge); return { ge: q.ge, fwd: x.dir === q.dir, at: sub2(x.at, q.v0off) }; });
    const same = (a, b) => a.ge === b.ge && a.fwd === b.fwd && a.at[0] === b.at[0] && a.at[1] === b.at[1];
    const k0 = raw.findIndex((x, i) => !same(x, raw[(i - 1 + raw.length) % raw.length])); if (k0 < 0) { problem = problem || 'collapse'; return { id: f.id, sides: [] }; }
    const sides = []; for (let j = 0; j < raw.length; j++) { const x = raw[(k0 + j) % raw.length]; if (!sides.length || !same(x, sides[sides.length - 1].raw)) sides.push({ edge: x.ge.id, dir: x.fwd ? 1 : -1, at: x.at.slice(), raw: x }); }
    return { id: f.id, sides: sides.map(({ edge, dir, at }) => ({ edge, dir, at })) };
  });
  // the order of the boundaries round each kept vertex (from the faces, above)
  const out = new Map();
  roots.forEach(v => { if (D.has(v.id) || !outC.has(v.id)) return; out.set(v.id, outC.get(v.id).map(h => { const q = partOf.get(h.e); return { e: q.ge.id, dir: h.d === q.dir ? 1 : -1 }; })); });
  const edgeFaces = new Map(edges.map(e => [e.id, []])); faces.forEach(f => f.sides.forEach(x => { const l = edgeFaces.get(x.edge); if (!l.includes(f)) l.push(f); }));
  const incident = new Map(), facesOf = new Map(), nbrs = new Map();
  edges.forEach(e => [e.v0, e.v1].forEach(v => { if (!incident.has(v)) incident.set(v, new Set()); incident.get(v).add(e.id); }));
  incident.forEach((es, v) => { const fs = new Set(), nb = new Set(); es.forEach(id => { edgeFaces.get(id).forEach(f => fs.add(f)); const e = byId.get(id); [e.v0, e.v1].forEach(w => { if (w !== v) nb.add(w); }); }); facesOf.set(v, fs); nbrs.set(v, nb); });
  st = { gm, E, D, inc, edges, byId, partOf, faces, out, edgeFaces, incident, facesOf, nbrs, det: Math.abs(G.latDet(gm.lattice)), L: gm.lattice, vertices: roots.filter(v => !D.has(v.id)), base, find, collapsed, problem,
    gc: { vertices: roots, edges: gcE, faces: gcF } };                    // the arrangement with merged vertices applied (what explicit() stores)
  structCache.set(k, st); if (structCache.size > 200) structCache.delete(structCache.keys().next().value); return st;
}

/* ---------------- geometry: where everything is ---------------- */
const latP = (st, at) => G.latVec(st.L, at);
function vertexPositions(s, st) { const mv = movesOf(s), pos = new Map(); st.gm.vertices.forEach(v => { const d = mv.get(v.id); pos.set(v.id, d ? P(v.pos.x + d.x, v.pos.y + d.y) : v.pos); }); return pos; }   // (a merged point: its root's)
// the frame of an original edge in its boundary's copy at offset [0, 0]: its two ends
function edgeFrame(st, pos, edgeId) { const q = st.partOf.get(edgeId), e = st.E.get(edgeId); return [plus(pos.get(e.v0), latP(st, q.v0off)), plus(pos.get(e.v1), latP(st, add2(q.v0off, e.shift)))]; }
// the added points of a boundary in its order, in the world, each with the original edge it belongs to
function boundaryPoints(st, ge, pos, ln) {
  const out = [];
  ge.parts.forEach((p, i) => { const list = ln.get(p.edge); if (!list || !list.length) return; const [a, b] = edgeFrame(st, pos, p.edge);
    const w = list.map((n, k) => ({ p: G.relToWorld(a, b, n), edge: p.edge, index: k, part: i })); if (p.dir < 0) w.reverse(); out.push(...w); });
  return out;
}
// the boundary's added points relative to its own two ends (grid.js's convention for an edge's nodes)
function boundaryNodes(st, ge, pos, ln) {
  if (ge.parts.length === 1) { const l = ln.get(ge.id) || []; return { nodes: l.map(n => ({ s: n.s, t: n.t })), refs: l.map((n, k) => ({ edge: ge.id, index: k })) }; }
  const pts = boundaryPoints(st, ge, pos, ln), A = pos.get(ge.v0), B = plus(pos.get(ge.v1), latP(st, ge.shift));
  return { nodes: pts.map(x => G.worldToRel(A, B, x.p)), refs: pts.map(x => ({ edge: x.edge, index: x.index })) };
}
// working geometry: vertex positions, original edges' added points, and every boundary's nodes
function work(s, st) { const pos = vertexPositions(s, st), ln = nodesOf(s), nodes = new Map(); st.edges.forEach(ge => nodes.set(ge.id, boundaryNodes(st, ge, pos, ln).nodes)); return { pos, ln, nodes }; }
const refresh = (st, w, ids) => ids.forEach(id => w.nodes.set(id, boundaryNodes(st, st.byId.get(id), w.pos, w.ln).nodes));
// the grid as drawn: a grid.js / topo.js grid (faces keep the merge grid's ids)
const gridCache = new Map();
function gridOf(s) {
  const k = stateKey(s); let g = gridCache.get(k); if (g) return g;
  const st = structure(s), pos = vertexPositions(s, st), ln = nodesOf(s);
  g = { kind: 'grid', symmetry: 'translation', version: 1, lattice: st.L, vertices: st.vertices.map(v => ({ id: v.id, pos: pos.get(v.id) })),
    edges: st.edges.map(ge => { const n = boundaryNodes(st, ge, pos, ln); return { id: ge.id, v0: ge.v0, v1: ge.v1, shift: ge.shift, nodes: n.nodes, curve: null, refs: n.refs, parts: ge.parts }; }), faces: st.faces };
  gridCache.set(k, g); if (gridCache.size > 300) gridCache.delete(gridCache.keys().next().value); return g;
}

/* ---------------- the checks ---------------- */
// a face's outline as drawn; every point tagged with the vertex it is (v) or the boundary whose added point it is (e)
function outline(st, f, w) {
  const pts = [], tag = [], seg = [];
  f.sides.forEach(x => { const ge = st.byId.get(x.edge), A = plus(w.pos.get(ge.v0), latP(st, x.at)), B = plus(w.pos.get(ge.v1), latP(st, add2(x.at, ge.shift))), ns = w.nodes.get(ge.id);
    let line = [{ p: A, v: ge.v0 }].concat(ns.map(n => ({ p: G.relToWorld(A, B, n), e: ge.id })), [{ p: B, v: ge.v1 }]); if (x.dir < 0) line = line.reverse();
    for (let i = 0; i < line.length - 1; i++) { pts.push(line[i].p); tag.push(line[i]); seg.push(ns.length === 0); } });
  return { pts, tag, seg };
}
const cross = (ax, ay, bx, by) => ax * by - ay * bx;
function segDist(a, b, c, d) {      // distance between segments ab and cd (0 if they cross)
  const d1 = cross(b.x - a.x, b.y - a.y, c.x - a.x, c.y - a.y), d2 = cross(b.x - a.x, b.y - a.y, d.x - a.x, d.y - a.y), d3 = cross(d.x - c.x, d.y - c.y, a.x - c.x, a.y - c.y), d4 = cross(d.x - c.x, d.y - c.y, b.x - c.x, b.y - c.y);
  if (((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) && ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0))) return 0;
  return Math.min(G.distPS(a, c, d), G.distPS(b, c, d), G.distPS(c, a, b), G.distPS(d, a, b));
}
// (a) for one face; the margins apply where something moved (isMoved: which points changed)
function faceProblem(st, f, w, isMoved, lim) {
  const o = outline(st, f, w), pts = o.pts, n = pts.length, mv = o.tag.map(isMoved);
  if (G.signedArea(pts) <= 1e-9) return 'fold';
  const ang = T.cornerAngles(pts);
  for (let i = 0; i < n; i++) { const i0 = (i + n - 1) % n, i2 = (i + 1) % n;
    if ((mv[i] || mv[i0] || mv[i2]) && (ang[i] < lim.minAngle || ang[i] > TAU - lim.minAngle)) return 'angle';
    if ((mv[i] || mv[i2]) && G.dist(pts[i], pts[i2]) < (o.seg[i] ? lim.minEdge : lim.minSeg)) return 'edge'; }
  for (let i = 0; i < n; i++) { const i2 = (i + 1) % n; if (!mv[i] && !mv[i2]) continue;
    for (let j = 0; j < n; j++) { const j2 = (j + 1) % n; if (j === i || j2 === i || j === i2) continue;
      if (segDist(pts[i], pts[i2], pts[j], pts[j2]) < lim.clear) return 'cross'; } }
  return null;
}
// (b) round one vertex: each boundary leaves it towards its first point (an added point, or its other end)
function angleSum(st, u, w) {
  const l = st.out.get(u), p = w.pos.get(u); if (!l || l.length < 2) return TAU;
  const th = l.map(h => { const ge = st.byId.get(h.e), ns = w.nodes.get(ge.id); let q;
    if (h.dir > 0) { const B = plus(w.pos.get(ge.v1), latP(st, ge.shift)); q = ns.length ? G.relToWorld(p, B, ns[0]) : B; }
    else { const A = plus(w.pos.get(ge.v0), latP(st, [-ge.shift[0], -ge.shift[1]])); q = ns.length ? G.relToWorld(A, p, ns[ns.length - 1]) : A; }
    return Math.atan2(q.y - p.y, q.x - p.x); });
  let s = 0; for (let i = 0; i < th.length; i++) { let d = th[(i + 1) % th.length] - th[i]; while (d <= 0) d += TAU; while (d > TAU) d -= TAU; s += d; } return s;
}
function totalArea(st, w) { let a = 0; st.faces.forEach(f => { a += G.signedArea(outline(st, f, w).pts); }); return a; }
// (a)-(c) after a change: `changed` = the boundaries that changed, `vertex` = the structural vertex that moved (or null)
function checkChange(st, w, changed, vertex, lim) {
  const vs = vertex instanceof Set ? vertex : null, isMoved = t => (t.v !== undefined && (vs ? vs.has(t.v) : t.v === vertex)) || (t.e !== undefined && changed.has(t.e));
  const faces = new Set(); changed.forEach(id => st.edgeFaces.get(id).forEach(f => faces.add(f)));
  for (const f of faces) { const why = faceProblem(st, f, w, isMoved, lim); if (why) return { ok: false, why, face: f.id }; }
  const verts = new Set(vs ? vs : vertex ? [vertex] : []); changed.forEach(id => { const e = st.byId.get(id); verts.add(e.v0); verts.add(e.v1); });
  for (const u of verts) if (Math.abs(angleSum(st, u, w) - TAU) > LIMITS.sumTol) return { ok: false, why: 'order', vertex: u };
  if (Math.abs(totalArea(st, w) - st.det) > LIMITS.areaTol * Math.max(1, st.det)) return { ok: false, why: 'cover' };
  return { ok: true };
}
// (a)-(c) for the whole grid, without the comfort margins: used when a drag ends and after merges
function checkAll(s) {
  const st = structure(s); if (st.problem) return { ok: false, why: st.problem };
  const w = work(s, st), all = () => true;
  for (const f of st.faces) { const why = faceProblem(st, f, w, all, BASIC); if (why) return { ok: false, why, face: f.id }; }
  for (const v of st.vertices) if (Math.abs(angleSum(st, v.id, w) - TAU) > LIMITS.sumTol) return { ok: false, why: 'order', vertex: v.id };
  return Math.abs(totalArea(st, w) - st.det) > LIMITS.areaTol * Math.max(1, st.det) ? { ok: false, why: 'cover' } : { ok: true };
}
const WHY = { pinch: 'a shape would touch itself at a merged point', collapse: 'a shape or the repeat would collapse', fold: 'a shape would fold over', angle: 'a corner would become too sharp (under 6°)', edge: 'a side would become too short', cross: 'a side would cross or touch another side',
  order: 'edges would cross at a vertex', cover: 'shapes would overlap or leave a gap' };

/* ---------------- drags: follow the finger as far as the grid stays valid ---------------- */
function follower(cur0, ok) {
  let cur = cur0, checks = 0;
  const lerp = (a, b, t) => P(a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t), test = p => { checks++; return ok(p); };
  const march = (from, to) => { const n = Math.max(1, Math.ceil(G.dist(from, to) / LIMITS.step)); let last = from;
    for (let k = 1; k <= n; k++) { const p = lerp(from, to, k / n); if (!test(p)) { let lo = 0, hi = 1; for (let it = 0; it < 12; it++) { const m = (lo + hi) / 2; if (test(lerp(last, p, m))) lo = m; else hi = m; } return { p: lerp(last, p, lo), blocked: true }; } last = p; }
    return { p: to, blocked: false }; };
  return { step(want) {
      checks = 0; let best = march(cur, want);
      if (best.blocked) { const dx = want.x - cur.x, dy = want.y - cur.y;     // slide along the limit, towards the finger
        for (const a of [0.4, -0.4, 0.8, -0.8, 1.2, -1.2]) { const c = Math.cos(a), sn = Math.sin(a), t = P(cur.x + (dx * c - dy * sn) * c, cur.y + (dx * sn + dy * c) * c), r = march(cur, t);
          if (G.dist(r.p, want) < G.dist(best.p, want) - 1e-12) best = { p: r.p, blocked: true }; } }
      cur = best.p; return { p: cur, blocked: best.blocked, checks }; },
    get cur() { return cur; } };
}
// a structural vertex (all its copies): offsets from its place in the triangular grid
function session(s, vid) {
  const st = structure(s), w = work(s, st), base = st.gm.vertices.find(v => v.id === vid).pos, changed = st.incident.get(vid) || new Set();
  const apply = d => { w.pos.set(vid, P(base.x + d.x, base.y + d.y)); refresh(st, w, changed); };
  const f = follower(offsetOf(s, vid), d => { apply(d); return checkChange(st, w, changed, vid, LIMITS).ok; });
  return { kind: 'vertex', vid, base, st, w, changed, step(want) { const r = f.step(want); apply(r.p); return { offset: r.p, blocked: r.blocked, checks: r.checks }; },
    get offset() { return f.cur; }, result() { return withMove(s, vid, f.cur); } };
}
// an added point (all its copies): positions in the world, for its boundary's copy at offset [0, 0]
function nodeSession(s, ref) {
  const st = structure(s), w = work(s, st), q = st.partOf.get(ref.edge), ge = q.ge, changed = new Set([ge.id]), [a, b] = edgeFrame(st, w.pos, ref.edge);
  const apply = p => { const l = w.ln.get(ref.edge).slice(); l[ref.index] = G.worldToRel(a, b, p); w.ln.set(ref.edge, l); refresh(st, w, changed); };
  const f = follower(G.relToWorld(a, b, w.ln.get(ref.edge)[ref.index]), p => { apply(p); return checkChange(st, w, changed, null, LIMITS).ok; });
  return { kind: 'node', ref, st, w, changed, step(want) { const r = f.step(want); apply(r.p); return { point: r.p, blocked: r.blocked, checks: r.checks }; },
    get point() { return f.cur; }, result() { return withNodes(s, ref.edge, w.ln.get(ref.edge)); } };
}
// whole drags in one call (tests): from where it is towards `want`, in finger-sized steps
function dragTo(s, vid, want, opts) {
  const ses = session(s, vid), from = offsetOf(s, vid), n = Math.max(1, Math.ceil(G.dist(from, want) / ((opts && opts.fingerStep) || 0.25))); let r = null, blocked = false;
  for (let k = 1; k <= n; k++) { r = ses.step(P(from.x + (want.x - from.x) * k / n, from.y + (want.y - from.y) * k / n)); blocked = blocked || r.blocked; }
  return { state: ses.result(), offset: ses.offset, blocked: r.blocked, everBlocked: blocked };
}
function dragNode(s, ref, want, opts) {
  const ses = nodeSession(s, ref), from = ses.point, n = Math.max(1, Math.ceil(G.dist(from, want) / ((opts && opts.fingerStep) || 0.1))); let r = null, blocked = false;
  for (let k = 1; k <= n; k++) { r = ses.step(P(from.x + (want.x - from.x) * k / n, from.y + (want.y - from.y) * k / n)); blocked = blocked || r.blocked; }
  return { state: ses.result(), point: ses.point, blocked: r.blocked, everBlocked: blocked };
}
function validOffset(s, vid, d) { const st = structure(s), w = work(s, st), b = st.gm.vertices.find(v => v.id === vid).pos, ch = st.incident.get(vid) || new Set(); w.pos.set(vid, P(b.x + d.x, b.y + d.y)); refresh(st, w, ch); return checkChange(st, w, ch, vid, LIMITS); }
function validNode(s, ref, p) { const st = structure(s), w = work(s, st), [a, b] = edgeFrame(st, w.pos, ref.edge), ge = st.partOf.get(ref.edge).ge, l = w.ln.get(ref.edge).slice(); l[ref.index] = G.worldToRel(a, b, p); w.ln.set(ref.edge, l); refresh(st, w, [ge.id]); return checkChange(st, w, new Set([ge.id]), null, LIMITS); }

/* ---------------- adding and removing points ---------------- */
const latticeEdgeOf = (s, gid) => { const ge = structure(s).byId.get(gid); return ge ? ge.parts[0].edge : null; };
const nodeCount = (s, edge) => { const l = (s.nodes || []).find(x => x[0] === edge); return l ? l[1].length : 0; };
// add a point on a boundary, at the place nearest to `wpt` (a world point, for the boundary's copy at offset [0, 0])
function addNode(s, gid, wpt) {
  const st = structure(s), ge = st.byId.get(gid); if (!ge) return { ok: false, message: 'That is not an edge.' };
  const w0 = work(s, st), A = w0.pos.get(ge.v0), B = plus(w0.pos.get(ge.v1), latP(st, ge.shift)), bp = boundaryPoints(st, ge, w0.pos, w0.ln);
  const line = [A].concat(bp.map(x => x.p), [B]);
  let best = null; for (let j = 0; j < line.length - 1; j++) { const a = line[j], b = line[j + 1], dx = b.x - a.x, dy = b.y - a.y, l2 = dx * dx + dy * dy || 1e-12, t = Math.max(0, Math.min(1, ((wpt.x - a.x) * dx + (wpt.y - a.y) * dy) / l2)), q = P(a.x + dx * t, a.y + dy * t), d = G.dist(q, wpt);
    if (!best || d < best.d) best = { j, q, d, a, b }; }
  const { j, a, b } = best, len = G.dist(a, b);
  if (len < 3 * LIMITS.minSeg) return { ok: false, message: 'There is no room for another point on this part of the edge.' };
  let q = best.q; if (G.dist(q, a) < 1.5 * LIMITS.minSeg || G.dist(q, b) < 1.5 * LIMITS.minSeg) q = P((a.x + b.x) / 2, (a.y + b.y) / 2);
  // which original edge receives it: one of those the segment runs along, with fewest added points
  const lp = j === 0 ? 0 : bp[j - 1].part, rp = j === bp.length ? ge.parts.length - 1 : bp[j].part;
  let c = -1; for (let i = lp; i <= rp; i++) { const n = nodeCount(s, ge.parts[i].edge); if (n < LIMITS.maxNodes && (c < 0 || n < nodeCount(s, ge.parts[c].edge))) c = i; }
  if (c < 0) return { ok: false, full: true, message: `This edge already has ${LIMITS.maxNodes} added points (the limit for each edge of the triangular grid).` };
  const part = ge.parts[c], edge = part.edge, list = (w0.ln.get(edge) || []).slice(), before = bp.slice(0, j).filter(x => x.part === c).length, idx = part.dir > 0 ? before : list.length - before;
  const [fa, fb] = edgeFrame(st, w0.pos, edge); list.splice(idx, 0, G.worldToRel(fa, fb, q));
  const ns = withNodes(s, edge, list), st2 = structure(ns), w = work(ns, st2), r = checkChange(st2, w, new Set([gid]), null, LIMITS);
  if (!r.ok) return { ok: false, message: `A point here would not keep the tiling valid: ${WHY[r.why]}.` };
  return { ok: true, state: ns, ref: { edge, index: idx }, point: q, count: list.length, max: LIMITS.maxNodes };
}
function removeNode(s, ref) {
  const st = structure(s), q = st.partOf.get(ref.edge), list = (nodesOf(s).get(ref.edge) || []).slice(); if (!q || ref.index < 0 || ref.index >= list.length) return { ok: false, message: 'There is no added point there.' };
  // (the boundary's two ends count as changed, so that the straightened boundary is checked against every other side of the two shapes)
  list.splice(ref.index, 1); const ns = withNodes(s, ref.edge, list), w = work(ns, st), r = checkChange(st, w, new Set([q.ge.id]), new Set([q.ge.v0, q.ge.v1]), LIMITS);
  return r.ok ? { ok: true, state: ns } : { ok: false, why: r.why, message: `This point cannot be removed here: the edge would straighten and ${WHY[r.why]}. Move the point closer to the straight line first.` };
}
// what a structural point is, and whether it can go
function pointInfo(s, vid) {
  const st = structure(s), k = (st.out.get(vid) || []).length;
  if (k >= 3) return { kind: 'junction', shapes: k, removable: false,
    message: `${k} shapes meet at this point, so it is a junction. Removing it would change which shapes meet (the arrangement). You can drag it onto a neighbouring junction to merge the two (where that is possible), or merge shapes by tapping an edge.` };
  return { kind: 'point', shapes: 2, removable: true, message: 'Only two shapes meet here, so this is not a junction: removing it keeps every shape and every neighbour. The two edges become one.' };
}
function removePoint(s, vid) {
  const info = pointInfo(s, vid); if (!info.removable) return Object.assign({ ok: false }, info);
  const st0 = structure(s), l = st0.inc.get(vid); if (l.length !== 2 || l[0].e === l[1].e) return Object.assign({ ok: false }, info, { message: 'This point cannot be removed: its two edges are one edge round the repeat.' });
  const ns = copy(s, { dissolved: [...new Set((s.dissolved || []).concat([vid]))].sort() }), st = structure(ns), gid = st.partOf.get(l[0].e).ge.id, w = work(ns, st), r = checkChange(st, w, new Set([gid]), new Set([st.byId.get(gid).v0, st.byId.get(gid).v1]), LIMITS);
  // (a shape with a bent side can be drawn with two sides only; as an arrangement it needs three)
  if (st.faces.some(f => f.sides.length < 3)) return Object.assign({ ok: false }, info, { why: 'sides', message: 'This point cannot be removed: a shape beside it would be left with only two sides.' });
  // in the triangular grid's own geometry (nothing moved or added here) a refusal means an edge already lies along the straight line
  const ge = st.byId.get(gid), touched = new Set([vid, ge.v0, ge.v1]), here = (s.moves || []).some(m => touched.has(m[0])) || ge.parts.some(p => nodeCount(s, p.edge));
  return r.ok ? Object.assign({ ok: true, state: ns }, info) : Object.assign({ ok: false }, info, { why: r.why, message: `This point cannot be removed: its two edges would become one straight edge, and ${WHY[r.why]}.` +
    (here ? ' Moving the points of this edge closer to the straight line between its ends may help.' : r.why === 'cross' ? ' Another side of the shape is in the way.' : ' Another edge already lies along that straight line.') });
}

/* ---------------- merging two junctions (edge contraction) ---------------- */
// Dropping vertex u (its copy at uAt) onto vertex w (its copy at wAt): what would happen, and the new state if it is possible.
const sameV = (a, b) => a[0] === b[0] && a[1] === b[1];
const corners = (st, w, f) => { const o = outline(st, f, w), a = T.cornerAngles(o.pts); return a.filter(t => Math.abs(t - Math.PI) > 1e-7).length; };
function contract(s, u, uAt, wv, wAt) {
  const st = structure(s), rel = sub2(wAt, uAt), fail = (kind, message, extra) => Object.assign({ ok: false, kind, message }, extra || {});
  if (u === wv) return fail('copy', 'These are two copies of the same vertex: merging them would collapse the repeat.');
  const kU = (st.out.get(u) || []).length, kW = (st.out.get(wv) || []).length;
  if (!kU || !kW) return fail('point', 'Only junctions and points of the grid can be merged.');
  // the drawn edges joining exactly these two copies
  const joining = st.edges.filter(ge => (ge.v0 === u && ge.v1 === wv && sameV(ge.shift, rel)) || (ge.v0 === wv && ge.v1 === u && sameV(ge.shift, [-rel[0], -rel[1]])));
  if (!joining.length) {
    const vs = f => { const l = []; f.sides.forEach(x => { const ge = st.byId.get(x.edge); l.push([ge.v0, x.at], [ge.v1, add2(x.at, ge.shift)]); }); return l; };
    const common = st.faces.some(f => { const l = vs(f); return l.some(([a, at]) => a === u && l.some(([b, bt]) => b === wv && sameV(sub2(bt, at), rel))); });
    return common ? fail('pinch', 'These two points are not joined by an edge: merging them would pinch a shape in two.') : fail('apart', 'These two points are not neighbours: the shapes between them would have to collapse.');
  }
  // the new state: every point along the joining edge(s) becomes one point (dissolved points on a chain included); edges between them vanish
  const ids = [], absorbed = new Set();
  joining.forEach(ge => { let o = [0, 0]; ge.parts.forEach((p, i) => { const e = st.E.get(p.edge); o = p.dir > 0 ? add2(o, e.shift) : sub2(o, e.shift); const x = p.dir > 0 ? e.v1 : e.v0; if (i < ge.parts.length - 1) absorbed.add(x); ids.push([ge.v0, x, o[0], o[1]]); }); });
  const lattice = new Set(joining.flatMap(ge => ge.parts.map(p => p.edge))), w0 = work(s, st), target = plus(w0.pos.get(wv), latP(st, wAt)), uPos = plus(w0.pos.get(u), latP(st, uAt));
  let ns = copy(s, { identified: (s.identified || []).concat(ids).sort(byKey), nodes: (s.nodes || []).filter(x => !lattice.has(x[0])), dissolved: (s.dissolved || []).filter(v => !absorbed.has(v)) });
  const st2 = structure(ns); if (st2.problem) return fail(st2.problem, st2.problem === 'pinch' ? 'Merging these two would make a shape touch itself at the merged point.' : 'Merging these two would collapse a shape.');
  // the merged point stays where w is (all copies): its root gets the move that puts w's copy there
  const R = st2.find(wv), Rbase = st2.base.get(R.r), want = P(target.x - G.latVec(st2.L, add2(wAt, R.o)).x, target.y - G.latVec(st2.L, add2(wAt, R.o)).y);
  const group = st.gm.vertices.map(v => v.id).filter(v => st2.find(v).r === R.r);
  ns = copy(ns, { moves: (ns.moves || []).filter(m => !group.includes(m[0])) }); if (G.dist(want, Rbase) > 1e-12) ns = withMove(ns, R.r, P(want.x - Rbase.x, want.y - Rbase.y));
  // faces beside the joining edge(s): their corners before and after
  const st3 = structure(ns), w3 = work(ns, st3), beside = [...new Set(joining.flatMap(ge => st.edgeFaces.get(ge.id).map(f => f.id)))];
  const before = beside.map(id => corners(st, w0, st.faces.find(f => f.id === id))), after = beside.map(id => { const f = st3.faces.find(x => x.id === id); return f && f.sides.length ? corners(st3, w3, f) : 0; });
  const change = { from: [kU, kW], to: (st3.out.get(R.r) || []).length, faces: beside, before, after, edgesGone: lattice.size, at: target, u: uPos };
  if (after.some(n => n < 3)) return fail('triangle', 'A triangle beside this edge would collapse to two sides, so these two cannot be merged.', { change });
  // (a three-sided shape with a bent side keeps three corners as drawn, but as an arrangement it would be left with two sides)
  if (st3.faces.some(f => f.sides.length < 3)) return fail('triangle', 'A shape beside this edge would be left with only two sides, so these two cannot be merged.', { change });
  const all = checkAll(ns); if (!all.ok) return fail('geometry', `Merging here would not keep the tiling valid: ${WHY[all.why]}.`, { change });
  const ch = checkChange(st3, w3, st3.incident.get(R.r) || new Set(), R.r, LIMITS); if (!ch.ok) return fail('geometry', `Merging here would not keep the tiling valid: ${WHY[ch.why]}.`, { change });
  return { ok: true, kind: 'merge', state: ns, root: R.r, change };
}

/* ---------------- adding an edge: splitting a shape ---------------- */
// The arrangement of a state written out explicitly (with merged vertices applied): what a NEW edge needs, because the triangular grid
// has no such edge to bring back. The drawing, the names and every later edit stay the same.
function explicit(s) {
  if (s.x && !(s.identified || []).length) return s;
  const st = structure(s); if (st.problem) return null;
  const V = new Set(st.gc.vertices.map(v => v.id)), E = new Set(st.gc.edges.map(e => e.id));
  const x = { n: s.x ? s.x.n : 0, v: st.gc.vertices.map(v => [v.id, v.pos.x, v.pos.y]), e: st.gc.edges.map(e => [e.id, e.v0, e.v1, e.shift[0], e.shift[1]]),
    f: st.gc.faces.map(f => [f.id, f.sides.map(sd => [sd.edge, sd.dir, sd.at[0], sd.at[1]])]), cuts: s.x ? s.x.cuts.filter(id => E.has(id)) : [] };
  return copy(s, { x, identified: [], moves: (s.moves || []).filter(m => V.has(m[0])), dissolved: [...st.D].sort(), nodes: (s.nodes || []).filter(n => E.has(n[0])) });
}
// A new structural vertex on edge `eid` of an explicit state, at world point q (for the edge's own copy at offset [0, 0]): the edge
// becomes two edges, and both shapes beside it get the corner. `k` of the edge's added points stay before the new vertex; with `drop`,
// added point k itself is what becomes the vertex. Nothing moves.
function pinAt(s, eid, k, q, drop) {
  const x = s.x, e = x.e.find(r => r[0] === eid), st = structure(s), pos = vertexPositions(s, st), A = pos.get(e[1]), B = plus(pos.get(e[2]), latP(st, [e[3], e[4]]));
  const wl = (nodesOf(s).get(eid) || []).map(n => G.relToWorld(A, B, n)), n = x.n + 1, vid = 'p' + n, ea = vid + 'a', eb = vid + 'b';
  const before = wl.slice(0, k).map(p => G.worldToRel(A, q, p)), after = wl.slice(drop ? k + 1 : k).map(p => G.worldToRel(q, B, p));
  const nx = { n, v: x.v.concat([[vid, q.x, q.y]]), e: x.e.filter(r => r[0] !== eid).concat([[ea, e[1], vid, 0, 0], [eb, vid, e[2], e[3], e[4]]]),
    f: x.f.map(([id, sides]) => [id, sides.flatMap(sd => sd[0] !== eid ? [sd] : sd[1] > 0 ? [[ea, 1, sd[2], sd[3]], [eb, 1, sd[2], sd[3]]] : [[eb, -1, sd[2], sd[3]], [ea, -1, sd[2], sd[3]]])]),
    cuts: x.cuts.flatMap(id => id === eid ? [ea, eb] : [id]) };
  let ns = copy(s, { x: nx, nodes: (s.nodes || []).filter(r => r[0] !== eid) }); if (before.length) ns = withNodes(ns, ea, before); if (after.length) ns = withNodes(ns, eb, after);
  return { state: ns, v: vid };
}
// What lies at a world point: a structural vertex, an added point, or a place on a boundary (with the copy it belongs to)
function locate(s, pw, tol) {
  const st = structure(s), w = work(s, st), L = st.L; tol = tol || 1e-7;
  for (const v of st.vertices) { const p = w.pos.get(v.id), uv = G.toLat(L, P(pw.x - p.x, pw.y - p.y)), at = [Math.round(uv[0]), Math.round(uv[1])]; if (G.dist(plus(p, latP(st, at)), pw) <= tol) return { kind: 'vertex', v: v.id, at }; }
  let best = null;
  for (const ge of st.edges) { const A = w.pos.get(ge.v0), B = plus(w.pos.get(ge.v1), latP(st, ge.shift)), bp = boundaryPoints(st, ge, w.pos, w.ln), line = [A].concat(bp.map(x => x.p), [B]);
    const uv = G.toLat(L, P(pw.x - (A.x + B.x) / 2, pw.y - (A.y + B.y) / 2)), o0 = [Math.round(uv[0]), Math.round(uv[1])];
    for (let di = -2; di <= 2; di++) for (let dj = -2; dj <= 2; dj++) { const at = [o0[0] + di, o0[1] + dj], d = latP(st, at), p = P(pw.x - d.x, pw.y - d.y);
      for (let j = 0; j < line.length - 1; j++) { const dd = G.distPS(p, line[j], line[j + 1]); if (dd <= tol && (!best || dd < best.d)) best = { d: dd, ge, at, j, p, bp }; } } }
  if (!best) return null;
  const hit = best.bp.find(x => G.dist(x.p, best.p) <= tol);
  return hit ? { kind: 'node', ge: best.ge.id, at: best.at, part: hit.part, index: hit.index, p: hit.p } : { kind: 'edge', ge: best.ge.id, at: best.at, j: best.j, p: best.p, bp: best.bp };
}
// the place on a boundary nearest to a touched point where a new corner has room (for the copy at offset `at`)
function edgePoint(s, gid, at, wpt) {
  const st = structure(s), ge = st.byId.get(gid); if (!ge) return { ok: false, message: 'That is not an edge.' };
  const w = work(s, st), d = latP(st, at), p = P(wpt.x - d.x, wpt.y - d.y), A = w.pos.get(ge.v0), B = plus(w.pos.get(ge.v1), latP(st, ge.shift)), line = [A].concat(boundaryPoints(st, ge, w.pos, w.ln).map(x => x.p), [B]);
  let best = null; for (let j = 0; j < line.length - 1; j++) { const dd = G.distPS(p, line[j], line[j + 1]); if (!best || dd < best.d) best = { j, d: dd }; }
  const j = best.j, a = line[j], b = line[j + 1], len = G.dist(a, b), ma = (j === 0 ? LIMITS.minEdge : LIMITS.minSeg) * 1.25, mb = (j === line.length - 2 ? LIMITS.minEdge : LIMITS.minSeg) * 1.25;
  if (len < ma + mb + 1e-9) return { ok: false, message: 'There is no room for a new corner on this part of the edge.' };
  const t = Math.max(ma / len, Math.min(1 - mb / len, ((p.x - a.x) * (b.x - a.x) + (p.y - a.y) * (b.y - a.y)) / (len * len)));
  return { ok: true, p: P(a.x + (b.x - a.x) * t + d.x, a.y + (b.y - a.y) * t + d.y) };
}
// make the grid element at world point pw a structural vertex (an explicit state); a vertex stays as it is
function pinPoint(s, pw) {
  const loc = locate(s, pw); if (!loc) return { ok: false, kind: 'off', message: 'That point is not on an edge of the grid.' };
  if (loc.kind === 'vertex') return { ok: true, state: s, v: loc.v, at: loc.at, created: false };
  const st = structure(s), ge = st.byId.get(loc.ge); let part, k, drop = false;
  if (loc.kind === 'node') { part = ge.parts[loc.part]; k = loc.index; drop = true; }
  else { const c = loc.j === 0 ? 0 : loc.bp[loc.j - 1].part, nb = loc.bp.slice(0, loc.j).filter(x => x.part === c).length; part = ge.parts[c]; k = part.dir > 0 ? nb : nodeCount(s, part.edge) - nb; }
  const q = st.partOf.get(part.edge), d = latP(st, q.v0off), r = pinAt(s, part.edge, k, P(loc.p.x - d.x, loc.p.y - d.y), drop);
  const st2 = structure(r.state), w2 = work(r.state, st2), ch = checkChange(st2, w2, st2.incident.get(r.v) || new Set(), r.v, LIMITS);       // room on both sides, as for every vertex
  if (!ch.ok) return { ok: false, kind: 'room', why: ch.why, message: ch.why === 'edge' ? 'This point is too close to a corner to become a corner itself.' : `A corner here would not keep the tiling valid: ${WHY[ch.why]}.` };
  return { ok: true, state: r.state, v: r.v, at: add2(loc.at, q.v0off), created: true };
}
// the faces that have both vertex copies as corners (normally one), and whether the two are neighbours on it
function commonCorners(s, e0, e1) {
  const st = structure(s), w = work(s, st), rel = sub2(e1.at, e0.at), out = [];
  st.faces.forEach(f => { const n = f.sides.length, cs = f.sides.map(x => { const ge = st.byId.get(x.edge); return x.dir > 0 ? { v: ge.v0, at: x.at } : { v: ge.v1, at: add2(x.at, ge.shift) }; });
    for (let i = 0; i < n; i++) { if (cs[i].v !== e0.v) continue;
      for (let j = 0; j < n; j++) { if (j === i || cs[j].v !== e1.v || !sameV(sub2(cs[j].at, cs[i].at), rel)) continue;
        const adj = j === (i + 1) % n ? i : i === (j + 1) % n ? j : -1;
        out.push({ face: f.id, i, j, at: cs[i].at, adjacent: adj >= 0, nodes: adj >= 0 ? boundaryPoints(st, st.byId.get(f.sides[adj].edge), w.pos, w.ln).map(x => x.p) : [] }); } } });
  return out;
}
// a straight edge between two points of an outline: null if it runs inside the polygon, otherwise why not
function chordWhy(pts, ia, ib) {
  const n = pts.length, a = pts[ia], b = pts[ib], dx = b.x - a.x, dy = b.y - a.y, len = Math.hypot(dx, dy), eps = 1e-9 * Math.max(1, len);
  for (const [i, o, sg] of [[ia, a, 1], [ib, b, -1]]) for (const k of [(i + 1) % n, (i + n - 1) % n]) { const p = pts[k]; if (Math.abs(cross(dx, dy, p.x - o.x, p.y - o.y)) <= eps * G.dist(o, p) + 1e-12 && sg * (dx * (p.x - o.x) + dy * (p.y - o.y)) > 0) return 'along'; }
  for (let k = 0; k < n; k++) { if (k === ia || k === ib) continue; if (G.distPS(pts[k], a, b) <= 1e-9) return 'through'; }
  for (let k = 0; k < n; k++) { const k2 = (k + 1) % n; if (k === ia || k === ib || k2 === ia || k2 === ib) continue; if (segDist(a, b, pts[k], pts[k2]) === 0) return 'outside'; }
  return G.winding(pts, P((a.x + b.x) / 2, (a.y + b.y) / 2)) === 0 ? 'outside' : null;
}
const CHORD = { along: 'A straight edge between these two points would lie along the side of the shape.', through: 'A straight edge between these two points would pass through another corner. Add it in two steps, corner to corner.',
  outside: 'A straight edge between these two points would leave the shape.' };
const MARGIN = { angle: 'The new edge would make a corner sharper than 6°.', edge: 'These two points are too close together for an edge.', cross: 'The new edge would pass too close to another side or corner.' };
// the new edge and the two faces, in an explicit state (c: a face and its two corners, from commonCorners)
function cutAt(s, c, e0, e1) {
  const x = s.x, E = new Map(x.e.map(r => [r[0], r])), fi = x.f.findIndex(r => r[0] === c.face), sides = x.f[fi][1], rel = sub2(e1.at, e0.at), B = add2(c.at, rel);
  const start = sd => { const e = E.get(sd[0]); return sd[1] > 0 ? [e[1], sd[2], sd[3]] : [e[2], sd[2] + e[3], sd[3] + e[4]]; };
  const at = (v, o) => sides.findIndex(sd => { const t = start(sd); return t[0] === v && t[1] === o[0] && t[2] === o[1]; }), i = at(e0.v, c.at), j = at(e1.v, B);
  if (i < 0 || j < 0 || i === j) return null;
  const n = x.n + 1, id = 'k' + n, fid = 'g' + n, m = sides.length, arc = (p, q) => { const l = []; for (let t = p; t !== q; t = (t + 1) % m) l.push(sides[t]); return l; };
  // going round the old face from the first point to the second, then back along the new edge: one face; the rest and the new edge: the other
  const f1 = arc(i, j).concat([[id, -1, c.at[0], c.at[1]]]), f2 = arc(j, i).concat([[id, 1, c.at[0], c.at[1]]]);
  const nx = { n, v: x.v, e: x.e.concat([[id, e0.v, e1.v, rel[0], rel[1]]]), f: x.f.slice(0, fi).concat([[c.face, f1], [fid, f2]], x.f.slice(fi + 1)), cuts: x.cuts.concat([id]) };
  return { state: copy(s, { x: nx }), edge: id };
}
// RESTORE: the two vertices lie on one line of the triangular grid, with only removed edges and edge-less grid points between them
const LDIR = { '1,0': ['a', 1], '-1,0': ['a', -1], '0,1': ['b', 1], '0,-1': ['b', -1], '-1,1': ['c', 1], '1,-1': ['c', -1] };
function gridRun(s, e0, e1) {
  if (s.x || (s.identified || []).length) return null;
  const isL = id => /^v@-?\d+,-?\d+$/.test(id); if (!isL(e0.v) || !isL(e1.v)) return null;
  const red = Mg.base(s.block).sc.super.red, M = Mg.blockOf(s.block).M, lat = (id, at) => { const r = id.slice(2).split(',').map(Number); return [r[0] + at[0] * M[0][0] + at[1] * M[1][0], r[1] + at[0] * M[0][1] + at[1] * M[1][1]]; };
  const pa = lat(e0.v, e0.at), d = sub2(lat(e1.v, e1.at), pa), k = Math.max(Math.abs(d[0]), Math.abs(d[1])); if (!k) return null;
  const u = [d[0] / k, d[1] / k], D = LDIR[u.join(',')]; if (!D) return null;
  const removed = new Set(s.removed), present = new Set(Mg.gridOf(baseOf(s)).vertices.map(v => v.id)), edges = [], mids = [];
  for (let t = 0; t < k; t++) { const p0 = add2(pa, [u[0] * t, u[1] * t]); edges.push(D[0] + '@' + red(D[1] > 0 ? p0 : add2(p0, u)).r.join(',')); if (t) mids.push('v@' + red(p0).r.join(',')); }
  if (new Set(edges).size !== k || new Set(mids).size !== mids.length || !edges.every(e => removed.has(e)) || mids.some(v => present.has(v))) return null;
  return { k, edges, mids };
}
function restoreAt(s, run, e0, e1) {
  const gone = new Set(run.edges), ns = copy(s, { removed: s.removed.filter(e => !gone.has(e)), dissolved: [...new Set((s.dissolved || []).concat(run.mids))].sort() });
  if (Mg.gridOf(baseOf(ns)).errors.length || Mg.topologyProblems(Mg.gridOf(baseOf(ns))).length) return null;
  const st = structure(ns); if (st.problem) return null;
  const rel = sub2(e1.at, e0.at), ge = st.edges.find(g => g.parts.every(p => gone.has(p.edge)) && ((g.v0 === e0.v && g.v1 === e1.v && sameV(g.shift, rel)) || (g.v0 === e1.v && g.v1 === e0.v && sameV(g.shift, [-rel[0], -rel[1]]))));
  return ge ? { state: ns, edge: ge.id } : null;
}
// one face of `cur` split between two of its corners (c from commonCorners). `orig` is the state the participant started from: when
// nothing had to be made a vertex first, a line of removed grid edges is brought back instead of a new edge.
function splitFace(orig, cur, c, e0, e1, pins) {
  const fail = (kind, message, extra) => Object.assign({ ok: false, kind, message }, extra || {});
  const st = structure(cur), w = work(cur, st), F = st.faces.find(f => f.id === c.face), o = outline(st, F, w), startIdx = []; let idx = 0;
  F.sides.forEach(x => { startIdx.push(idx); idx += w.nodes.get(x.edge).length + 1; });
  const ia = startIdx[c.i], ib = startIdx[c.j], ends = [o.pts[ia], o.pts[ib]], why = chordWhy(o.pts, ia, ib); if (why) return fail(why, CHORD[why], { ends });
  const run = !pins && cur === orig ? gridRun(orig, e0, e1) : null; let made = run ? restoreAt(orig, run, e0, e1) : null; const kind = made ? 'restore' : 'new';
  if (!made) { const ex = explicit(cur); made = ex && cutAt(ex, c, e0, e1); if (!made) return fail('broken', 'These two points could not be joined inside one shape.', { ends }); }
  const ns = made.state, st2 = structure(ns); if (st2.problem) return fail(st2.problem, `The new edge would not keep the tiling valid: ${WHY[st2.problem]}.`, { ends });
  const w2 = work(ns, st2), all = checkAll(ns); if (!all.ok) return fail('geometry', all.why === 'fold' || all.why === 'order' ? CHORD.outside : `The new edge would not keep the tiling valid: ${WHY[all.why]}.`, { ends, why: all.why });
  const gid = st2.partOf.get(st2.byId.has(made.edge) ? st2.byId.get(made.edge).parts[0].edge : made.edge).ge.id, ch = checkChange(st2, w2, new Set([gid]), new Set([e0.v, e1.v]), LIMITS);
  if (!ch.ok) return fail('margin', MARGIN[ch.why] || `The new edge would not keep the tiling valid: ${WHY[ch.why]}.`, { ends, why: ch.why });
  const parts = st2.edgeFaces.get(gid).map(f => f.id); if (parts.length !== 2 || st2.faces.length !== st.faces.length + 1) return fail('broken', 'These two points could not be joined inside one shape.', { ends });
  return { ok: true, kind, stored: ns.x ? 'explicit' : 'grid', state: ns, edge: gid, faces: parts,
    change: { before: corners(st, w, F), after: parts.map(id => corners(st2, w2, st2.faces.find(f => f.id === id))), pins, restored: made && kind === 'restore' ? run.k : 0, ends } };
}
// ADD AN EDGE between two points on the boundary of one shape. Each end is { v, at } (a structural vertex and its copy) or { p } (a
// world point on the grid: an added point, or any place on an edge). Returns the new state, the new boundary and the two faces — or why
// it is not possible, with the state untouched.
function split(s, A, B) {
  const fail = (kind, message, extra) => Object.assign({ ok: false, kind, message }, extra || {});
  let cur = s, pins = 0; const ends = [];
  for (const X of [A, B]) {
    if (X.v !== undefined) { ends.push({ v: X.v, at: X.at }); continue; }
    const loc = locate(cur, X.p); if (!loc) return fail('off', 'That point is not on an edge of the grid.');
    if (loc.kind === 'vertex') { ends.push({ v: loc.v, at: loc.at }); continue; }
    const ex = explicit(cur), r = ex ? pinPoint(ex, X.p) : { ok: false, kind: 'broken', message: 'The grid could not be read.' }; if (!r.ok) return fail(r.kind, r.message);
    cur = r.state; if (r.created) pins++; ends.push({ v: r.v, at: r.at }); }
  const [e0, e1] = ends; if (e0.v === e1.v && sameV(e0.at, e1.at)) return fail('same', 'Choose two different points.');
  let cand = commonCorners(cur, e0, e1); if (!cand.length) return fail('apart', 'These two points are not on the same shape: an edge can only split one shape.');
  // neighbours along a BENT edge: its added points become corners, so the piece cut off has three sides or more
  const bent = cand.find(c => c.adjacent && c.nodes.length);
  if (bent) { cur = explicit(cur); for (const pw of bent.nodes) { const r = pinPoint(cur, pw); if (!r.ok) return fail(r.kind, r.message); cur = r.state; if (r.created) pins++; } cand = commonCorners(cur, e0, e1); }
  let first = null;
  for (const c of cand) {
    if (c.adjacent) { first = first || fail('joined', 'These two points are already joined by an edge.'); continue; }
    const r = splitFace(s, cur, c, e0, e1, pins); if (r.ok) return r; if (!first || first.kind === 'joined') first = r; }
  return first;
}
const beside = (s, gid) => (structure(s).edgeFaces.get(gid) || []).map(f => f.id);

/* ---------------- an explicit arrangement: merging two shapes, a bigger block, and an independent check ---------------- */
// Merging the two shapes beside an edge (what merge.js does for the triangular grid): their whole shared boundary goes.
function mergeX(s0, edgeId, opts) {
  const s = explicit(s0); if (!s) return { ok: false, kind: 'topology', message: Mg.MESSAGES.topology, state: s0 };
  const x = s.x, faces = baseGrid(s).faces, cb = Mg.commonBoundary({ faces }, edgeId);
  if (!cb) return { ok: false, kind: 'no-edge', message: 'That is not an edge between two shapes.', state: s0 };
  const refuse = (kind, extra) => Object.assign({ ok: false, agree: kind !== 'disagree', kind, message: Mg.MESSAGES[kind] || Mg.MESSAGES.topology, state: s0, boundary: cb }, extra || {});
  if (cb.sameShape) return refuse(cb.delta[0] || cb.delta[1] ? 'wrap' : 'slit');
  const S = new Set(cb.edges), FA = faces.find(f => f.id === cb.A), FB = faces.find(f => f.id === cb.B);
  const rest = f => { const n = f.sides.length, m = f.sides.map(sd => S.has(sd.edge)), c = m.filter(Boolean).length; if (!c || c === n) return null;
    let k = 0; while (!(m[k] && !m[(k - 1 + n) % n])) k++;                       // the first shared side after a kept one
    for (let t = 0; t < c; t++) if (!m[(k + t) % n]) return null;                // the shared sides are not one run: the shapes meet in two places
    const out = []; for (let t = c; t < n; t++) out.push(f.sides[(k + t) % n]); return out; };
  const ra = rest(FA), rb = rest(FB); if (!ra || !rb) return refuse('hole');
  const sides = ra.map(sd => [sd.edge, sd.dir, sd.at[0], sd.at[1]]).concat(rb.map(sd => [sd.edge, sd.dir, sd.at[0] + cb.delta[0], sd.at[1] + cb.delta[1]]));
  const e = x.e.filter(r => !S.has(r[0])), deg = new Map(); e.forEach(r => { deg.set(r[1], (deg.get(r[1]) || 0) + 1); deg.set(r[2], (deg.get(r[2]) || 0) + 1); });
  const nx = { n: x.n, v: x.v.filter(r => deg.has(r[0])), e, f: x.f.filter(r => r[0] !== cb.B).map(r => r[0] === cb.A ? [cb.A, sides] : r), cuts: x.cuts.filter(id => !S.has(id)) };
  const ns = copy(s, { x: nx, moves: (s.moves || []).filter(m => deg.has(m[0])), dissolved: (s.dissolved || []).filter(v => deg.get(v) === 2), nodes: (s.nodes || []).filter(n => !S.has(n[0])) });
  // the same kinds of check as a merge in the triangular grid: the arrangement, the drawn geometry, M1's validator
  const tp = Mg.topologyProblems(Object.assign({ errors: [] }, baseGrid(ns))); if (tp.length) return refuse(tp[0].kind);
  const c = checkAll(ns); if (!c.ok) return refuse(c.why === 'pinch' ? 'pinch' : 'disagree', { moved: c });
  const j = judge(ns, opts); if (!j.ok) return refuse('disagree', { judged: j });
  return { ok: true, agree: true, kind: null, message: '', state: ns, boundary: cb, topology: [], validator: j.validator, independent: { ok: j.independent } };
}
// The same explicit arrangement described with a bigger repeat block: every vertex, edge and face once for each copy of the old block
// inside the new one (named id~i,j).
function refineX(s, toKey) {
  if (!Mg.refinable(s.block, toKey)) return null;
  const f = explicit(s); if (!f) return null;
  const A = Mg.blockOf(s.block).M, B = Mg.blockOf(toKey).M, dA = A[0][0] * A[1][1] - A[0][1] * A[1][0], rd = v => Math.round(v);
  const a = rd((B[0][0] * A[1][1] - B[0][1] * A[1][0]) / dA), b = rd((B[0][1] * A[0][0] - B[0][0] * A[0][1]) / dA), c = rd((B[1][0] * A[1][1] - B[1][1] * A[1][0]) / dA), d = rd((B[1][1] * A[0][0] - B[1][0] * A[0][1]) / dA), det = a * d - b * c;
  const red = p => { const X = Math.floor((p[0] * d - p[1] * c) / det), Y = Math.floor((a * p[1] - b * p[0]) / det); return { r: [p[0] - X * a - Y * c, p[1] - X * b - Y * d], q: [X, Y] }; };
  const reps = new Map(), K = Math.abs(a) + Math.abs(b) + Math.abs(c) + Math.abs(d) + 1; for (let i = -K; i <= K; i++) for (let j = -K; j <= K; j++) { const r = red([i, j]).r; reps.set(r.join(','), r); }
  if (reps.size !== det) return null;
  const R = [...reps.values()].sort((p, q) => p[1] - q[1] || p[0] - q[0]), L = Mg.base(s.block).sc.lattice, nm = (id, r) => id + '~' + r.join(','), x = f.x;
  const v = [], e = [], fc = [], moves = [], dissolved = [], nodes = [], cuts = [];
  R.forEach(r => { const o = G.latVec(L, r);
    x.v.forEach(([id, px, py]) => v.push([nm(id, r), px + o.x, py + o.y]));
    x.e.forEach(([id, v0, v1, sx, sy]) => { const t = red([r[0] + sx, r[1] + sy]); e.push([nm(id, r), nm(v0, r), nm(v1, t.r), t.q[0], t.q[1]]); });
    x.f.forEach(([id, sides]) => fc.push([nm(id, r), sides.map(([ed, dir, ax, ay]) => { const t = red([r[0] + ax, r[1] + ay]); return [nm(ed, t.r), dir, t.q[0], t.q[1]]; })]));
    (f.moves || []).forEach(([id, dx, dy]) => moves.push([nm(id, r), dx, dy])); (f.dissolved || []).forEach(id => dissolved.push(nm(id, r)));
    (f.nodes || []).forEach(([id, l]) => nodes.push([nm(id, r), l.map(n => n.slice())])); x.cuts.forEach(id => cuts.push(nm(id, r))); });
  const nb = Mg.refine(baseOf(s), toKey);
  return { block: toKey, removed: nb ? nb.removed : [], moves: moves.sort(byKey), dissolved: dissolved.sort(), nodes: nodes.sort(byKey), identified: [], x: { n: x.n, v, e, f: fc, cuts } };
}
// The independent judge of an explicit arrangement (the triangle count of merge.js no longer applies): from the lists alone, without
// any geometry — every edge has exactly one face on each side, every face closes and passes no vertex twice, the corners round every
// vertex form ONE ring through all its edges (a manifold junction), and V − E + F = 0.
function manifold(s) {
  const f = explicit(s); if (!f) return { ok: false, problems: ['the arrangement could not be read'] };
  const x = f.x, E = new Map(x.e.map(e => [e[0], e])), V = new Set(x.v.map(v => v[0])), problems = [], use = new Map(), succ = new Map(), hk = (e, d) => e + (d > 0 ? '>' : '<');
  x.e.forEach(e => { if (!V.has(e[1]) || !V.has(e[2])) problems.push(`edge ${e[0]} ends at a missing vertex`); });
  x.f.forEach(([id, sides]) => { const n = sides.length, seen = new Set(); if (n < 3) problems.push(`face ${id} has fewer than three sides`);
    sides.forEach((sd, i) => { const e = E.get(sd[0]); if (!e) { problems.push(`face ${id} uses a missing edge`); return; }
      const k = hk(sd[0], sd[1]); use.set(k, (use.get(k) || 0) + 1);
      const from = sd[1] > 0 ? [e[1], sd[2], sd[3]] : [e[2], sd[2] + e[3], sd[3] + e[4]], to = sd[1] > 0 ? [e[2], sd[2] + e[3], sd[3] + e[4]] : [e[1], sd[2], sd[3]];
      const nx = sides[(i + 1) % n], e2 = E.get(nx[0]); if (e2) { const s2 = nx[1] > 0 ? [e2[1], nx[2], nx[3]] : [e2[2], nx[2] + e2[3], nx[3] + e2[4]]; if (s2.join() !== to.join()) problems.push(`face ${id} does not close`); }
      const vk = from.join(); if (seen.has(vk)) problems.push(`face ${id} passes a vertex twice`); seen.add(vk);
      const p = sides[(i - 1 + n) % n]; succ.set(k, hk(p[0], -p[1])); }); });
  x.e.forEach(e => { if (use.get(e[0] + '>') !== 1 || use.get(e[0] + '<') !== 1) problems.push(`edge ${e[0]} does not have exactly one face on each side`); });
  x.v.forEach(([v]) => { const all = []; x.e.forEach(e => { if (e[1] === v) all.push(e[0] + '>'); if (e[2] === v) all.push(e[0] + '<'); });
    if (all.length < 2) { problems.push(`vertex ${v} has fewer than two edges`); return; }
    let h = all[0], n = 0; do { h = succ.get(h); n++; } while (h && h !== all[0] && n <= all.length);
    if (h !== all[0] || n !== all.length) problems.push(`vertex ${v} is not surrounded by one ring of faces`); });
  const euler = x.v.length - x.e.length + x.f.length; if (euler !== 0) problems.push(`V − E + F = ${euler}, not 0`);
  return { ok: !problems.length, problems, V: x.v.length, E: x.e.length, F: x.f.length };
}

/* ---------------- the full judges on the drawn geometry ---------------- */
function judge(s, opts) {
  opts = opts || {};
  const st = structure(s); if (st.problem) return { ok: false, topology: false, validator: { ok: false, failing: [st.problem] }, independent: false };
  const g = gridOf(s), sig = f => f.sides.map(x => x.edge + (x.dir > 0 ? '>' : '<')).sort().join(' ');
  // topology: faces re-derived from the drawn positions must be exactly the grid's faces (nothing folded over)
  const d = T.makeGrid({ lattice: g.lattice, vertices: g.vertices, edges: g.edges.map(e => ({ id: e.id, v0: e.v0, v1: e.v1, shift: e.shift, nodes: e.nodes })) }, 'drawn');
  const want = new Set(st.faces.map(sig)), have = d.faces.map(sig), topoOK = !d.errors.length && have.length === want.size && have.every(x => want.has(x)) && !Mg.topologyProblems(d).length;
  const r = G.validate(G.buildPatch(g, { n: Math.max(2, G.patchSize(g) - 1) }), { samples: opts.samples || 700 }), indep = s.x ? manifold(s) : Mg.polyiamonds(s.block, s.removed);
  return { ok: topoOK && r.ok && indep.ok, topology: topoOK, validator: { ok: r.ok, failing: r.rows.filter(x => !x.ok).map(x => x.name) }, independent: indep.ok, independentBy: s.x ? 'arrangement' : 'triangles', problems: indep.problems };
}

/* ---------------- merging, bigger blocks ---------------- */
function merge(s, edgeId, opts) {
  if (s.x) return mergeX(s, edgeId, opts);
  const r = Mg.merge(baseOf(s), edgeId, opts); if (!r.ok) return Object.assign(r, { state: s });
  const gm = Mg.gridOf(r.state), keepV = new Set(gm.vertices.map(v => v.id)), keepE = new Set(gm.edges.map(e => e.id)), deg = new Map();
  gm.edges.forEach(e => { deg.set(e.v0, (deg.get(e.v0) || 0) + 1); deg.set(e.v1, (deg.get(e.v1) || 0) + 1); });
  const ns = { block: r.state.block, removed: r.state.removed, moves: (s.moves || []).filter(m => keepV.has(m[0])), dissolved: (s.dissolved || []).filter(v => keepV.has(v) && deg.get(v) === 2), nodes: (s.nodes || []).filter(x => keepE.has(x[0])),
    identified: (s.identified || []).filter(x => keepV.has(x[0]) && keepV.has(x[1])) };
  // the three judges decided on the arrangement; the drawn geometry is checked as a whole too (fast). M1's 13 checks (judge) can follow.
  if (ns.moves.length || ns.nodes.length || ns.dissolved.length || ns.identified.length) { const c = checkAll(ns); r.moved = c;
    if (!c.ok) return Object.assign(r, { ok: false, agree: c.why !== 'pinch', kind: c.why === 'pinch' ? 'pinch' : 'disagree', message: c.why === 'pinch' ? 'This would make a shape touch itself at a merged point.' : Mg.MESSAGES.disagree, state: s }); }
  return Object.assign(r, { state: ns });
}
function refine(s, toKey) {
  if (s.x) return refineX(s, toKey);
  const nb = Mg.refine(baseOf(s), toKey); if (!nb) return null;
  const oldRed = Mg.base(s.block).sc.super.red, sc = Mg.base(toKey).sc, gm = Mg.gridOf(nb), presentV = new Set(gm.vertices.map(v => v.id)), presentE = new Set(gm.edges.map(e => e.id));
  const old = x => x.base + '@' + oldRed(x.rep).r.join(','), mv = movesOf(s), D = new Set(s.dissolved || []), ln = new Map((s.nodes || []).map(x => [x[0], x[1]]));
  const moves = sc.vertices.filter(v => presentV.has(v.id)).map(v => { const d = mv.get(old(v)); return d ? [v.id, d.x, d.y] : null; }).filter(Boolean).sort(byKey);
  const dissolved = sc.vertices.filter(v => presentV.has(v.id) && D.has(old(v))).map(v => v.id).sort();
  const nodes = sc.edges.filter(e => presentE.has(e.id)).map(e => { const l = ln.get(old(e)); return l ? [e.id, l.map(x => x.slice())] : null; }).filter(Boolean).sort(byKey);
  // a merge u@0 = w@o of the old block, for every copy of u in the new block: the point of w it meant, named in the new block
  const Mo = Mg.blockOf(s.block).M, newRed = sc.super.red, repOf = id => id.split('@')[1].split(',').map(Number), identified = [];
  (s.identified || []).forEach(([a, b, ox, oy]) => { const pa = repOf(a), pb = repOf(b), d = [pb[0] - pa[0] + ox * Mo[0][0] + oy * Mo[1][0], pb[1] - pa[1] + ox * Mo[0][1] + oy * Mo[1][1]];
    sc.vertices.filter(v => presentV.has(v.id) && old(v) === a).forEach(v => { const t = newRed([v.rep[0] + d[0], v.rep[1] + d[1]]); identified.push([v.id, 'v@' + t.r.join(','), t.q[0], t.q[1]]); }); });
  return { block: toKey, removed: nb.removed, moves, dissolved, nodes, identified: identified.sort(byKey) };
}

/* ---------------- description (for people): merge.js's, on the drawn grid ---------------- */
function describe(s) {
  // (how many triangles of the grid a shape is made of: only while the arrangement is the triangular grid minus edges)
  const g = gridOf(s), shB = s.x ? null : T.shapes(Mg.gridOf(baseOf(s))), cl = C().classify(g), inv = T.invariants(g), area = Math.sqrt(3) / 4, blk = Mg.blockOf(s.block), D = new Set(s.dissolved || []);
  const cutIds = new Set(s.x ? s.x.cuts : []), cuts = structure(s).edges.filter(ge => ge.parts.every(p => cutIds.has(p.edge))).length;
  const faces = g.faces.map(f => { const sb = shB && shB.faces.find(x => x.id === f.id), pf = cl.geometry.perFace[f.id];
    return { id: f.id, triangles: sb ? Math.round(sb.area / area) : 0, corners: pf.corners, sides: inv.faceSizes[f.id], name: pf.name, polygon: Mg.polyName(pf.corners), regular: pf.regular }; });
  const groups = cl.geometry.shapes.map(c => ({ name: c.name, polygon: Mg.polyName(c.corners), corners: c.corners, faces: c.count, regular: c.regular, angles: c.angles, sides: c.sides, triangles: faces.find(f => f.id === c.faces[0]).triangles }))
    .sort((a, b) => a.corners - b.corners || a.triangles - b.triangles);
  groups.forEach(x => { x.label = `${x.faces} ${x.faces > 1 ? C().plural(x.name) : x.name}` + (x.triangles > 1 ? ` of ${x.triangles} triangles` : ''); });
  return { block: blk, trianglesPerBlock: 2 * (blk.M[0][0] * blk.M[1][1] - blk.M[0][1] * blk.M[1][0]), merges: s.removed.length, moved: (s.moves || []).filter(m => !D.has(m[0])).length,
    added: (s.nodes || []).reduce((n, x) => n + x[1].length, 0), dissolved: D.size, merged: (s.identified || []).length, explicit: !!s.x, cuts, shapesPerBlock: g.faces.length, faces, groups,
    vertexTypes: inv.vertexTypes, arrangement: cl.topology.arrangement, classification: cl, name: cl.name, tilingVertices: inv.V, points: inv.nodes };
}
function positions(s) { return vertexPositions(s, structure(s)); }

return { LIMITS, BASIC, WHY, newState, withMove, withNodes, offsetOf, stateKey, structKey, baseOf, gridOf, structure, positions, work, checkChange, checkAll,
  validOffset, validNode, session, nodeSession, dragTo, dragNode, latticeEdgeOf, nodeCount, addNode, removeNode, pointInfo, removePoint, contract, judge, merge, refine, describe,
  explicit, split, edgePoint, locate, beside, manifold, baseGrid, gridRun };
});
