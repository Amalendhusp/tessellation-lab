/* tessellation-mobile-workspace-v6.2-grid-m2b / merge.js · STRUCTURAL GRID EXPLORATION: merging faces of the triangular grid
 *   (M2A's engine, unchanged; M2B changes only describe(), which now reports classify.js's three levels)
 *
 * THE STATE
 *   - a repeat block: a sublattice of the triangular lattice, given by an integer matrix M whose rows are the block's translations
 *     in triangle-lattice steps;
 *   - the set of edge classes removed so far.
 *   The grid is the triangular grid described with that block (topo.supercell), minus the removed edges. Its faces are derived
 *   from the remaining edges (topo.deriveFaces). A state is a few bytes of JSON, so Undo/Redo restores it exactly.
 *
 * A MERGE (a tap on an edge)
 *   - The edge separates two faces, A and B.
 *   - Their WHOLE shared boundary is removed: every edge class A and B share in the same relative position. Usually that is one
 *     edge; it is several when they already meet along a bent boundary.
 *   - The removal applies to the class, so to every copy in the repeating grid.
 *
 * VALIDATION, before anything is committed. Three independent judges must agree that the candidate is a valid tiling:
 *   1. topology: faces re-derived from the remaining edges; no face may wrap round the repeat (an endless strip), have a hole,
 *      touch itself at a corner (a pinch) or contain an edge on both its sides (a slit or dangling edge); every face must run
 *      counter-clockwise;
 *   2. M1's validator: the 13 checks on an explicit patch (shared edges, crossings, angle sums, coverage, …);
 *   3. an independent count of polyiamonds: triangles joined across the removed edges by union-find, with lattice offsets. Each
 *      group must be finite, its boundary one simple closed loop, and no kept edge may lie inside it.
 *      This uses only the triangle grid and the removed set: no derived faces, no half-edges.
 *   A refused merge leaves the state untouched and says why, in plain words.
 *
 * CLASSIFICATION (M2B) is separate: describe() asks classify.js for the arrangement (topology), the shapes (geometry) and the
 * regularity conditions. The judges never call it, so validity never depends on a name, and unfamiliar arrangements are allowed. */
(function (root, factory) {
  const M = factory(root);
  if (typeof module === 'object' && module.exports) module.exports = M; else root.TessMerge = M;
})(typeof self !== 'undefined' ? self : globalThis, function (root) {
'use strict';
const node = typeof module === 'object' && module.exports;
const G = node ? require('./grid.js') : root.TessGrid, T = node ? require('./topo.js') : root.TessTopo, P = G.P;
const C = () => node ? require('./classify.js') : root.TessClassify;     // used by describe() only, never by the judges
const add2 = (a, b) => [a[0] + b[0], a[1] + b[1]], sub2 = (a, b) => [a[0] - b[0], a[1] - b[1]];

// repeat blocks (rows: the block's translations in steps of the triangular lattice). Triangles per block = 2 × det.
const BLOCKS = [
  { key: '1', name: '1 × 1', M: [[1, 0], [0, 1]] },
  { key: 'r3', name: '√3', M: [[1, 1], [-1, 2]] },
  { key: '2', name: '2 × 2', M: [[2, 0], [0, 2]] },
  { key: '2s', name: '2 × 2 slanted', M: [[2, 0], [1, 2]] },
  { key: 'c6', name: '6-cell', M: [[3, 1], [-3, 1]] },
  { key: 'r7', name: '√7', M: [[2, 1], [-1, 3]] },
  { key: '3', name: '3 × 3', M: [[3, 0], [0, 3]] },
  { key: 'c12', name: '12-cell', M: [[4, -1], [0, 3]] },
  { key: 'r13', name: '√13', M: [[3, 1], [-1, 4]] },
  { key: '4', name: '4 × 4', M: [[4, 0], [0, 4]] }
];
const blockOf = key => BLOCKS.find(b => b.key === key);
const detM = M => M[0][0] * M[1][1] - M[0][1] * M[1][0];
const NAMES = { '3.3.3.3.3.3': 'triangular', '4.4.4.4': 'square', '6.6.6': 'hexagonal', '3.6.3.6': 'trihexagonal', '3.3.3.3.6': 'snub hexagonal',
  '3.3.3.4.4': 'elongated triangular', '3.3.4.3.4': 'snub square', '3.4.6.4': 'rhombitrihexagonal', '4.8.8': 'truncated square', '3.12.12': 'truncated hexagonal', '4.6.12': 'truncated trihexagonal' };
const POLY = { 3: 'triangle', 4: 'quadrilateral', 5: 'pentagon', 6: 'hexagon', 7: 'heptagon', 8: 'octagon', 9: 'nonagon', 10: 'decagon', 11: 'hendecagon', 12: 'dodecagon' };
const polyName = n => POLY[n] || n + '-gon';

/* ---------------- the base grid of a block, and the grid of a state (both cached) ---------------- */
const baseCache = new Map(), gridCache = new Map();
function base(key) { let b = baseCache.get(key); if (!b) { const bl = blockOf(key), sc = T.supercell(T.triangleGrid(), bl.M, 'triangular grid, block ' + bl.name); b = { block: bl, sc }; baseCache.set(key, b); } return b; }
const stateKey = s => s.block + '|' + s.removed.join(' ');
function newState(key) { if (!blockOf(key)) throw new Error('unknown block ' + key); return { block: key, removed: [] }; }
function gridOf(s) { const k = stateKey(s); let g = gridCache.get(k); if (!g) { g = T.removeEdges(base(s.block).sc, s.removed, 'grid'); gridCache.set(k, g); if (gridCache.size > 400) gridCache.delete(gridCache.keys().next().value); } return g; }
function sidesOf(g) { const m = new Map(); g.faces.forEach(f => f.sides.forEach(s => { const l = m.get(s.edge) || []; l.push({ face: f.id, dir: s.dir, at: s.at }); m.set(s.edge, l); })); return m; }

/* ---------------- judge 1: topology of the derived faces ---------------- */
function topologyProblems(g) {
  const out = g.errors.map(e => ({ kind: /wraps/.test(e) ? 'wrap' : /dangling/.test(e) ? 'slit' : /counter-clockwise/.test(e) ? 'hole' : 'topology', detail: e }));
  const E = new Map(g.edges.map(e => [e.id, e]));
  g.faces.forEach(f => { const seenV = new Set(), seenE = new Set();
    f.sides.forEach(s => { const e = E.get(s.edge), v = s.dir > 0 ? e.v0 : e.v1, at = s.dir > 0 ? s.at : add2(s.at, e.shift), vk = v + '@' + at, ek = s.edge + '@' + s.at;
      if (seenV.has(vk)) out.push({ kind: 'pinch', detail: `face ${f.id} passes vertex ${v} twice` }); seenV.add(vk);
      if (seenE.has(ek)) out.push({ kind: 'slit', detail: `face ${f.id} has edge ${s.edge} on both sides` }); seenE.add(ek); }); });
  return out;
}

/* ---------------- judge 3: independent polyiamond count (triangles + removed edges only) ---------------- */
// ▲ at lattice point p: p, p+(1,0), p+(0,1).  ▼ at p: p+(1,0), p+(1,1), p+(0,1).
// a@p: p→p+(1,0) separates ▲p | ▼(p−(0,1));  b@p: p→p+(0,1) separates ▲p | ▼(p−(1,0));  c@p: p→p+(−1,1) separates ▲(p−(1,0)) | ▼(p−(1,0)).
function polyiamonds(key, removed) {
  const { block, sc } = base(key), M = block.M, red = sc.super.red, rm = new Set(removed);
  const tid = (t, p) => { const r = red(p); return { cls: t + r.r.join(','), off: r.q }; };
  const sides = (e, p) => e === 'a' ? [tid('U', p), tid('D', sub2(p, [0, 1]))] : e === 'b' ? [tid('U', p), tid('D', sub2(p, [1, 0]))] : [tid('U', sub2(p, [1, 0])), tid('D', sub2(p, [1, 0]))];
  const reps = sc.super.reps, classes = []; reps.forEach(r => { classes.push('U' + r.join(','), 'D' + r.join(',')); });
  const parent = new Map(classes.map(c => [c, c])), offs = new Map(classes.map(c => [c, [0, 0]])), problems = [];
  const find = c => { let off = [0, 0], x = c; while (parent.get(x) !== x) { off = add2(off, offs.get(x)); x = parent.get(x); } return { root: x, off }; };   // off: c's instance relative to the root's
  const edgesAll = []; reps.forEach(r => ['a', 'b', 'c'].forEach(e => edgesAll.push({ id: e + '@' + r.join(','), e, p: r })));
  edgesAll.forEach(x => { if (!rm.has(x.id)) return; const [s, t] = sides(x.e, x.p), fs = find(s.cls), ft = find(t.cls);
    const want = add2(sub2(t.off, s.off), sub2(fs.off, ft.off));                  // t's instance (relative to its root) placed relative to s's root
    if (fs.root === ft.root) { if (want[0] || want[1]) problems.push({ kind: 'wrap', detail: `${s.cls} meets its own copy across ${x.id}` }); }
    else { parent.set(ft.root, fs.root); offs.set(ft.root, want); } });
  // kept edges inside one group (same instance on both sides) = a slit
  edgesAll.forEach(x => { if (rm.has(x.id)) return; const [s, t] = sides(x.e, x.p), fs = find(s.cls), ft = find(t.cls);
    if (fs.root === ft.root) { const d = add2(sub2(t.off, s.off), sub2(fs.off, ft.off)); if (!d[0] && !d[1]) problems.push({ kind: 'slit', detail: `kept edge ${x.id} lies inside one shape` }); } });
  // each group: its triangles, in the plane, and its boundary
  const groups = new Map(); classes.forEach(c => { const f = find(c), l = groups.get(f.root) || []; l.push({ c, off: f.off }); groups.set(f.root, l); });
  const out = [];
  if (!problems.some(p => p.kind === 'wrap')) groups.forEach((members, rootId) => {
    const cnt = new Map(), pt = (c, off) => { const t = c[0], r = c.slice(1).split(',').map(Number), p = add2(r, [off[0] * M[0][0] + off[1] * M[1][0], off[0] * M[0][1] + off[1] * M[1][1]]); return { t, p }; };
    const ek = (u, w) => (u[0] < w[0] || (u[0] === w[0] && u[1] < w[1])) ? u + '|' + w : w + '|' + u;
    members.forEach(m => { const { t, p } = pt(m.c, m.off), vs = t === 'U' ? [p, add2(p, [1, 0]), add2(p, [0, 1])] : [add2(p, [1, 0]), add2(p, [1, 1]), add2(p, [0, 1])];
      for (let i = 0; i < 3; i++) { const k = ek(vs[i], vs[(i + 1) % 3]); cnt.set(k, (cnt.get(k) || 0) + 1); } });
    const bnd = [...cnt].filter(([, n]) => n === 1).map(([k]) => k.split('|')), deg = new Map(), adj = new Map();
    bnd.forEach(([u, w]) => { [u, w].forEach(x => deg.set(x, (deg.get(x) || 0) + 1)); (adj.get(u) || adj.set(u, []).get(u)).push(w); (adj.get(w) || adj.set(w, []).get(w)).push(u); });
    const pinch = [...deg].filter(([, d]) => d !== 2);
    let loops = 0; const seen = new Set(); if (!pinch.length) for (const v of deg.keys()) { if (seen.has(v)) continue; loops++; let x = v, prev = null; do { seen.add(x); const nx = adj.get(x).find(y => y !== prev && !seen.has(y)) || adj.get(x).find(y => y !== prev); prev = x; x = nx; } while (x !== v && !seen.has(x)); }
    if (pinch.length) problems.push({ kind: 'pinch', detail: `shape ${rootId} touches itself at ${pinch.length} corner(s)` });
    else if (loops !== 1) problems.push({ kind: 'hole', detail: `shape ${rootId} has ${loops} boundary loops (a hole)` });
    out.push({ root: rootId, triangles: members.length, boundaryEdges: bnd.length }); });
  return { ok: !problems.length, problems, shapes: out, groups: groups.size };
}

/* ---------------- merging ---------------- */
// The two faces on the sides of an edge, and every edge class they share in the same relative position.
function commonBoundary(g, edgeId) {
  const sm = sidesOf(g), u = sm.get(edgeId); if (!u || u.length !== 2) return null;
  const A = u.find(x => x.dir > 0) || u[0], B = u.find(x => x !== A), delta = sub2(A.at, B.at), list = [];
  sm.forEach((l, id) => { if (l.length !== 2) return; const [x, y] = l;
    const match = (p, q) => p.face === A.face && q.face === B.face && sub2(p.at, q.at)[0] === delta[0] && sub2(p.at, q.at)[1] === delta[1];
    if (match(x, y) || match(y, x)) list.push(id); });
  return { A: A.face, B: B.face, sameShape: A.face === B.face, delta, edges: list.sort() };
}
const MESSAGES = {
  wrap: 'These are copies of the same shape: joining them would join every copy into one endless strip. Try a bigger repeat block.',
  hole: 'This would make a shape with a hole in it (it would surround another shape).',
  pinch: 'This would make a shape that touches itself at a corner.',
  slit: 'This would leave an edge sticking into a shape.',
  topology: 'This would break how the shapes fit together.',
  geometry: 'This would break the tiling (an independent check failed).',
  disagree: 'The checks disagree about this merge, so it is refused (please report this).'
};
function judge(key, removed, opts) {
  opts = opts || {};
  const g = T.removeEdges(base(key).sc, removed, 'candidate'), topo = topologyProblems(g), indep = polyiamonds(key, removed);
  let geo = null; if (!topo.length || opts.always) { const n = Math.max(2, G.patchSize(g) - 1), r = G.validate(G.buildPatch(g, { n }), { samples: opts.samples || 700 }); geo = { ok: r.ok, failing: r.rows.filter(x => !x.ok).map(x => x.name) }; }
  const topoOK = !topo.length, geoOK = !!geo && geo.ok, indepOK = indep.ok;
  const ok = topoOK && geoOK && indepOK, agree = (topoOK && geoOK) === indepOK;
  const kind = ok ? null : !agree ? 'disagree' : (indep.problems[0] || topo[0] || { kind: 'geometry' }).kind;
  return { ok, agree, kind, message: kind ? MESSAGES[kind] || MESSAGES.topology : '', grid: g, topology: topo, independent: indep, validator: geo };
}
function merge(state, edgeId, opts) {
  const g = gridOf(state), cb = commonBoundary(g, edgeId);
  if (!cb) return { ok: false, kind: 'no-edge', message: 'That is not an edge between two shapes.', state };
  const removed = [...new Set(state.removed.concat(cb.edges))].sort(), j = judge(state.block, removed, opts);
  return Object.assign(j, { state: j.ok ? { block: state.block, removed } : state, boundary: cb });
}

/* ---------------- a bigger block (the same grid, a finer repeat) ---------------- */
function refinable(fromKey, toKey) { const A = blockOf(fromKey).M, B = blockOf(toKey).M, d = detM(A);
  const K = [[(B[0][0] * A[1][1] - B[0][1] * A[1][0]) / d, (B[0][1] * A[0][0] - B[0][0] * A[0][1]) / d], [(B[1][0] * A[1][1] - B[1][1] * A[1][0]) / d, (B[1][1] * A[0][0] - B[1][0] * A[0][1]) / d]];
  return K.flat().every(x => Math.abs(x - Math.round(x)) < 1e-9) && detM(K) > 0 && toKey !== fromKey; }   // B = K·A: every repeat of B is a repeat of A
function refine(state, toKey) {
  if (!refinable(state.block, toKey)) return null;
  const oldRed = base(state.block).sc.super.red, rm = new Set(state.removed), sc = base(toKey).sc;
  const removed = sc.edges.filter(e => rm.has(e.base + '@' + oldRed(e.rep).r.join(','))).map(e => e.id).sort();
  return { block: toKey, removed };
}

/* ---------------- description (for people) ---------------- */
// The three levels of classify.js, plus what only this grid knows (triangles per shape). `uniform` is kept for M2A's tests: it is
// the ARRANGEMENT (topology) only, never the tiling's name; the name is classification.name.
function describe(state) {
  const g = gridOf(state), inv = T.invariants(g), sh = T.shapes(g), cl = C().classify(g), area = Math.sqrt(3) / 4;
  const faces = g.faces.map(f => { const s = sh.faces.find(x => x.id === f.id), pf = cl.geometry.perFace[f.id];
    return { id: f.id, triangles: Math.round(s.area / area), corners: pf.corners, sides: inv.faceSizes[f.id], convex: s.convex, name: pf.name, polygon: polyName(pf.corners), regular: pf.regular }; });
  const groups = cl.geometry.shapes.map(c => ({ name: c.name, polygon: polyName(c.corners), corners: c.corners, faces: c.count, regular: c.regular, angles: c.angles, sides: c.sides, triangles: faces.find(f => f.id === c.faces[0]).triangles }))
    .sort((a, b) => a.corners - b.corners || a.triangles - b.triangles);
  groups.forEach(x => { x.label = `${x.faces} ${x.faces > 1 ? C().plural(x.name) : x.name}` + (x.triangles > 1 ? ` of ${x.triangles} triangles` : ''); });
  const types = inv.vertexTypes, uniform = types.length === 1 && NAMES[types[0]] ? NAMES[types[0]] : null;
  // what a participant SEES at each vertex where 3 or more shapes meet: the number of corners of each shape around it
  const cornersOf = new Map(faces.map(f => [f.id, f.corners])), faceOf = new Map(); g.faces.forEach(f => f.sides.forEach(x => faceOf.set(x.edge + (x.dir > 0 ? '>' : '<'), f.id)));
  const out = T.outgoing(g), seen = new Set(); out.forEach(l => { if (l.length >= 3) seen.add(T.canon(l.map(h => cornersOf.get(faceOf.get(h.e + (h.dir > 0 ? '>' : '<')))))); });
  const seenTypes = [...seen].sort();
  return { block: blockOf(state.block), trianglesPerBlock: 2 * detM(blockOf(state.block).M), merges: state.removed.length, shapesPerBlock: g.faces.length, faces, groups, vertexTypes: types, seenTypes,
    uniform, arrangement: cl.topology.arrangement, classification: cl, name: cl.name, tilingVertices: inv.V, points: inv.nodes };
}

return { BLOCKS, blockOf, NAMES, polyName, base, newState, gridOf, stateKey, sidesOf, commonBoundary, topologyProblems, polyiamonds, judge, merge, refinable, refine, describe, MESSAGES };
});
