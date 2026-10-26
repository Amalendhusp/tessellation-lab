/* tessellation-mobile-workspace-v6.1-grid-m2a / topo.js — the topology tools of the M2 feasibility study (grid-m2-feasibility/lib/topo.js),
 * unchanged except for the wrapper that lets the same file run in the browser (window.TessTopo) and in Node.
 *
 * A grid is given by its VERTICES and EDGES only (positions + lattice shifts). Its FACES are derived from the embedding: the
 * cyclic order of edges at each vertex (the rotation system). Faces are never declared, so a topological operation (delete an
 * edge, delete a vertex, add an edge) cannot be described inconsistently. The result is a grid.js quotient, which M1's validator
 * checks.
 *
 * Contents:
 *   deriveFaces / makeGrid       vertices + edges → faces; rejects faces that wrap round the torus, or that are not counter-clockwise
 *   supercell                    the same grid described with a larger period (k = det M classes for every class)
 *   removeEdges / removeVertices topological merges
 *   invariants                   valences, combinatorial face sizes, vertex types (e.g. 3.4.6.4), F/V, mean valence and face size
 *   shapes                       geometric corners, reflex corners, convexity, congruence classes
 *   triangleGrid                 the regular triangular grid (p1: 1 vertex class, 3 edge classes, 2 face classes)
 *   unitGrid                     a grid from vertex positions: the edges are the pairs at distance 1 (for regular-faced targets)
 *   dual                         face centres joined across edges (Laves tilings: Cairo, prismatic, floret pentagons)
 *   certificate                  triangulate every face so that EVERY vertex has degree 6 → proof that the grid is the triangle grid
 *                                with edges/vertices removed
 *   latticeMap                   for a 6-regular triangulation, its triangle-lattice coordinates and supercell matrix
 *   regularize                   Levenberg–Marquardt on vertex positions + lattice: unit edges, regular faces
 */
(function (root, factory) {
  const T = factory(root);
  if (typeof module === 'object' && module.exports) module.exports = T; else root.TessTopo = T;
})(typeof self !== 'undefined' ? self : globalThis, function (root) {
'use strict';
const G = (typeof module === 'object' && module.exports) ? require('./grid.js') : root.TessGrid, { P, latVec, relToWorld } = G;
const TAU = 2 * Math.PI, S3 = Math.sqrt(3) / 2;
const add2 = (a, b) => [a[0] + b[0], a[1] + b[1]], sub2 = (a, b) => [a[0] - b[0], a[1] - b[1]], neg2 = a => [-a[0], -a[1]];
const clone = o => JSON.parse(JSON.stringify(o));
const LIMITS = Object.assign({}, G.LIMITS, { maxSides: 1e9 });

/* ---------------- faces from the rotation system ---------------- */
function outgoing(g) {        // per vertex class: outgoing half-edges sorted counter-clockwise by the direction of their first segment
  const V = new Map(g.vertices.map(v => [v.id, v])), out = new Map(g.vertices.map(v => [v.id, []]));
  g.edges.forEach(e => {
    const a = V.get(e.v0).pos, d = latVec(g.lattice, e.shift), b = P(V.get(e.v1).pos.x + d.x, V.get(e.v1).pos.y + d.y);
    const inner = (e.curve || e.nodes || []).map(n => relToWorld(a, b, n)), first = inner.length ? inner[0] : b, last = inner.length ? inner[inner.length - 1] : a;
    out.get(e.v0).push({ e: e.id, dir: 1, ang: Math.atan2(first.y - a.y, first.x - a.x) });
    out.get(e.v1).push({ e: e.id, dir: -1, ang: Math.atan2(last.y - b.y, last.x - b.x) });
  });
  out.forEach(l => l.sort((p, q) => p.ang - q.ang));
  return out;
}
const hk = (e, d) => e + (d > 0 ? '>' : '<');
function deriveFaces(g) {
  const E = new Map(g.edges.map(e => [e.id, e])), out = outgoing(g), where = new Map(), errors = [];
  out.forEach((l, v) => {
    l.forEach((h, i) => where.set(hk(h.e, h.dir), { v, i }));
    for (let i = 0; i < l.length; i++) { const d = l[(i + 1) % l.length].ang - l[i].ang; if (l.length > 1 && Math.abs(d) < 1e-12) errors.push(`two edges leave vertex ${v} in the same direction`); }
  });
  const target = h => h.dir > 0 ? E.get(h.e).v1 : E.get(h.e).v0;
  const next = h => { const l = out.get(target(h)), t = where.get(hk(h.e, -h.dir)); return l[(t.i - 1 + l.length) % l.length]; };
  const seen = new Set(), faces = [];
  out.forEach(l => l.forEach(h0 => {
    if (seen.has(hk(h0.e, h0.dir))) return;
    const sides = []; let h = h0, o = [0, 0], guard = 0;
    do { seen.add(hk(h.e, h.dir)); const e = E.get(h.e);
      if (h.dir > 0) { sides.push({ edge: h.e, dir: 1, at: o.slice() }); o = add2(o, e.shift); }
      else { o = sub2(o, e.shift); sides.push({ edge: h.e, dir: -1, at: o.slice() }); }
      h = next(h); if (++guard > 20000) { errors.push('runaway face'); break; }
    } while (!(h.e === h0.e && h.dir === h0.dir));
    if (o[0] || o[1]) errors.push(`a "face" wraps round the torus (lattice shift ${o}): it is an infinite strip, not a polygon`);
    faces.push({ id: 'f' + faces.length, sides });
  }));
  return { faces, errors };
}
function makeGrid(spec, name) {
  const g = { kind: name || spec.kind || 'grid', symmetry: 'translation', version: 1, lattice: clone(spec.lattice),
    vertices: spec.vertices.map(v => ({ id: v.id, pos: P(v.pos.x, v.pos.y) })),
    edges: spec.edges.map(e => ({ id: e.id, v0: e.v0, v1: e.v1, shift: e.shift.slice(), nodes: (e.nodes || []).map(n => ({ s: n.s, t: n.t })), curve: e.curve || null })),
    faces: [], limits: Object.assign({}, LIMITS) };
  const val = new Map(g.vertices.map(v => [v.id, 0])); g.edges.forEach(e => { val.set(e.v0, val.get(e.v0) + 1); val.set(e.v1, val.get(e.v1) + 1); });
  const errors = []; val.forEach((n, v) => { if (n === 1) errors.push(`vertex ${v} has a single edge (a dangling edge)`); if (n === 0) errors.push(`vertex ${v} has no edge`); });
  const d = deriveFaces(g); g.faces = d.faces; errors.push(...d.errors);
  if (!d.errors.length) g.faces.forEach(f => { const a = G.signedArea(G.faceOutline(g, f, [0, 0]).pts); if (!(a > 0)) errors.push(`face ${f.id} is not counter-clockwise (area ${a.toExponential(2)}): the embedding is not planar`); });
  g.errors = errors; return g;
}
const spec = g => ({ lattice: g.lattice, vertices: g.vertices, edges: g.edges });

/* ---------------- grids ---------------- */
function triangleGrid() {      // p1: v; a: v → v + b1, b: v → v + b2, c: v → v + b2 − b1. V − E + F = 1 − 3 + 2 = 0
  return makeGrid({ lattice: { b1: P(1, 0), b2: P(0.5, S3) }, vertices: [{ id: 'v', pos: P(0, 0) }],
    edges: [{ id: 'a', v0: 'v', v1: 'v', shift: [1, 0] }, { id: 'b', v0: 'v', v1: 'v', shift: [0, 1] }, { id: 'c', v0: 'v', v1: 'v', shift: [-1, 1] }] }, 'triangle');
}
// edges = all pairs of vertices at distance `len` (for regular-faced targets drawn with unit edges)
function unitGrid(lattice, pts, name, len) {
  len = len || 1; const vs = pts.map((p, i) => ({ id: 'p' + i, pos: P(p.x, p.y) })), edges = [], seen = new Set();
  for (let i = 0; i < vs.length; i++) for (let j = 0; j < vs.length; j++) for (let s = -3; s <= 3; s++) for (let t = -3; t <= 3; t++) {
    const d = latVec(lattice, [s, t]), q = P(vs[j].pos.x + d.x - vs[i].pos.x, vs[j].pos.y + d.y - vs[i].pos.y);
    if (Math.abs(Math.hypot(q.x, q.y) - len) > 1e-9) continue;
    const k1 = i + ',' + j + ',' + s + ',' + t, k2 = j + ',' + i + ',' + (-s) + ',' + (-t); if (seen.has(k1) || seen.has(k2)) continue; seen.add(k1);
    edges.push({ id: 'e' + edges.length, v0: vs[i].id, v1: vs[j].id, shift: [s, t] }); }
  return makeGrid({ lattice, vertices: vs, edges }, name);
}
// M: rows are the new basis vectors in old lattice coordinates (integer, det > 0). Every class becomes det M classes.
function supercell(g, M, name) {
  const [[a, b], [c, d]] = M, det = a * d - b * c; if (det <= 0) throw new Error('supercell needs det > 0');
  const red = p => { const x = Math.floor((p[0] * d - p[1] * c) / det), y = Math.floor((a * p[1] - b * p[0]) / det); return { r: [p[0] - x * a - y * c, p[1] - x * b - y * d], q: [x, y] }; };
  const reps = new Map(), K = Math.abs(a) + Math.abs(b) + Math.abs(c) + Math.abs(d) + 1;
  for (let i = -K; i <= K; i++) for (let j = -K; j <= K; j++) { const r = red([i, j]).r; reps.set(r.join(','), r); }
  if (reps.size !== det) throw new Error('coset count ' + reps.size + ' ≠ ' + det);
  const R = [...reps.values()].sort((p, q) => p[1] - q[1] || p[0] - q[0]), L = g.lattice;
  const B1 = latVec(L, [a, b]), B2 = latVec(L, [c, d]), id = (x, r) => x + '@' + r.join(',');
  const vertices = [], edges = [];
  g.vertices.forEach(v => R.forEach(r => { const o = latVec(L, r); vertices.push({ id: id(v.id, r), pos: P(v.pos.x + o.x, v.pos.y + o.y), base: v.id, rep: r }); }));
  g.edges.forEach(e => R.forEach(r => { const t = red(add2(r, e.shift)); edges.push({ id: id(e.id, r), v0: id(e.v0, r), v1: id(e.v1, t.r), shift: t.q, nodes: e.nodes, curve: e.curve, base: e.id, rep: r }); }));
  const h = makeGrid({ lattice: { b1: B1, b2: B2 }, vertices, edges }, name || g.kind + ' ×' + det);
  h.vertices.forEach((v, i) => { v.base = vertices[i].base; v.rep = vertices[i].rep; }); h.edges.forEach((e, i) => { e.base = edges[i].base; e.rep = edges[i].rep; });
  h.super = { M, det, reps: R, red }; return h;
}
function removeEdges(g, ids, name) {
  const drop = new Set(ids), edges = g.edges.filter(e => !drop.has(e.id)), used = new Set(); edges.forEach(e => { used.add(e.v0); used.add(e.v1); });
  const h = makeGrid({ lattice: g.lattice, vertices: g.vertices.filter(v => used.has(v.id)), edges }, name);
  h.removed = { edges: ids.length, vertices: g.vertices.length - h.vertices.length }; return h;
}
function removeVertices(g, ids, name) { const drop = new Set(ids); return removeEdges(g, g.edges.filter(e => drop.has(e.v0) || drop.has(e.v1)).map(e => e.id), name); }

/* ---------------- invariants ---------------- */
const canon = seq => { const n = seq.length, all = []; for (const s of [seq, seq.slice().reverse()]) for (let i = 0; i < n; i++) all.push(s.slice(i).concat(s.slice(0, i)));   // smallest numerically: 3.12.12, 4.6.12
  all.sort((x, y) => { for (let k = 0; k < n; k++) if (x[k] !== y[k]) return x[k] - y[k]; return 0; }); return all[0].join('.'); };
function invariants(g) {
  const E = new Map(g.edges.map(e => [e.id, e])), val = new Map(g.vertices.map(v => [v.id, 0]));
  g.edges.forEach(e => { val.set(e.v0, val.get(e.v0) + 1); val.set(e.v1, val.get(e.v1) + 1); });
  const origin = s => { const e = E.get(s.edge); return s.dir > 0 ? e.v0 : e.v1; }, isV = v => val.get(v) >= 3;
  const faceSize = new Map(), faceOf = new Map();
  g.faces.forEach(f => { faceSize.set(f.id, f.sides.filter(s => isV(origin(s))).length); f.sides.forEach(s => faceOf.set(hk(s.edge, s.dir), f.id)); });
  const out = outgoing(g), vtype = {}, tv = g.vertices.filter(v => isV(v.id));
  tv.forEach(v => { vtype[v.id] = canon(out.get(v.id).map(h => faceSize.get(faceOf.get(hk(h.e, h.dir))))); });
  const ftype = {}; g.faces.forEach(f => { ftype[f.id] = canon(f.sides.map(origin).filter(isV).map(v => val.get(v))); });
  const types = [...new Set(Object.values(vtype))].sort(), sizes = [...faceSize.values()];
  const vbar = tv.reduce((s, v) => s + val.get(v.id), 0) / tv.length, fbar = sizes.reduce((s, n) => s + n, 0) / sizes.length;
  return { V: tv.length, nodes: g.vertices.length - tv.length, E: g.edges.length, F: g.faces.length, valence: Object.fromEntries([...val]), vertexTypes: types, vtype, ftype,
    faceSizes: Object.fromEntries(g.faces.map(f => [f.id, faceSize.get(f.id)])), FperV: g.faces.length / tv.length, vbar, fbar, euler: g.vertices.length - g.edges.length + g.faces.length,
    eulerMeans: 1 / vbar + 1 / fbar };
}

/* ---------------- shapes ---------------- */
function cornerAngles(pts) { const n = pts.length; return pts.map((p, i) => { const a = pts[(i + n - 1) % n], b = pts[(i + 1) % n];
  let t = Math.atan2((b.x - p.x) * (a.y - p.y) - (b.y - p.y) * (a.x - p.x), (b.x - p.x) * (a.x - p.x) + (b.y - p.y) * (a.y - p.y)); if (t <= 0) t += TAU; return t; }); }
function shapes(g) {
  const per = g.faces.map(f => { const pts = G.faceOutline(g, f, [0, 0]).pts, ang = cornerAngles(pts), idx = ang.map((t, i) => i).filter(i => Math.abs(ang[i] - Math.PI) > 1e-7);
    const cp = idx.map(i => pts[i]), ca = idx.map(i => ang[i]), sides = cp.map((p, k) => G.dist(p, cp[(k + 1) % cp.length]));
    return { id: f.id, corners: cp.length, reflex: ca.filter(t => t > Math.PI + 1e-7).length, convex: ca.every(t => t < Math.PI - 1e-7), area: G.signedArea(pts), sig: { a: ca, s: sides }, cp }; });
  // congruence: same corner count and, up to rotation and reflection, the same sequence of (side, angle)
  const same = (x, y) => { const n = x.a.length; if (n !== y.a.length) return false;
    for (const rev of [false, true]) for (let o = 0; o < n; o++) { let ok = true;
      for (let k = 0; k < n && ok; k++) { const i = rev ? (o - k + 2 * n) % n : (o + k) % n, sa = y.a[i], ss = rev ? y.s[(i - 1 + n) % n] : y.s[i];
        if (Math.abs(sa - x.a[k]) > 1e-7 || Math.abs(ss - x.s[k]) > 1e-7) ok = false; }
      if (ok) return true; }
    return false; };
  const classes = []; per.forEach(f => { const c = classes.find(c => same(c.sig, f.sig)); if (c) c.faces.push(f.id); else classes.push({ sig: f.sig, corners: f.corners, faces: [f.id] }); });
  return { faces: per, congruenceClasses: classes.map(c => ({ corners: c.corners, faces: c.faces })), allConvex: per.every(f => f.convex), reflexTotal: per.reduce((s, f) => s + f.reflex, 0) };
}

/* ---------------- duals (Laves tilings) ---------------- */
function dual(g, name) {
  const verts = g.faces.map(f => ({ id: 'd' + f.id, pos: G.centroid(G.faceOutline(g, f, [0, 0]).pts) })), use = new Map();
  g.faces.forEach(f => f.sides.forEach(s => { const l = use.get(s.edge) || []; l.push({ f: f.id, dir: s.dir, at: s.at }); use.set(s.edge, l); }));
  const edges = g.edges.map(e => { const [p, q] = use.get(e.id), A = p.dir > 0 ? p : q, Bq = A === p ? q : p;
    return { id: 'd' + e.id, v0: 'd' + A.f, v1: 'd' + Bq.f, shift: sub2(A.at, Bq.at) }; });   // the face holding e at offset 0 sits at −at
  return makeGrid({ lattice: g.lattice, vertices: verts, edges }, name || 'dual of ' + g.kind);
}

/* ---------------- 6-regular triangulation certificate ---------------- */
function triangulations(n) {     // all triangulations of a convex n-gon (vertices 0..n−1) as lists of diagonals [i, j]
  const memo = new Map();
  const rec = (i, j) => { if (j - i < 2) return [[]]; const k0 = i + ',' + j; if (memo.has(k0)) return memo.get(k0); const out = [];
    for (let k = i + 1; k < j; k++) { const L = rec(i, k), R = rec(k, j);
      for (const l of L) for (const r of R) { const d = l.concat(r); if (k - i > 1) d.push([i, k]); if (j - k > 1) d.push([k, j]); out.push(d); } }
    memo.set(k0, out); return out; };
  return rec(0, n - 1);
}
function certificate(g, opts) {
  opts = opts || {};
  const E = new Map(g.edges.map(e => [e.id, e])), val = new Map(g.vertices.map(v => [v.id, 0]));
  g.edges.forEach(e => { val.set(e.v0, val.get(e.v0) + 1); val.set(e.v1, val.get(e.v1) + 1); });
  const ids = g.vertices.map(v => v.id), ix = new Map(ids.map((v, i) => [v, i])), need = ids.map(v => 6 - val.get(v));
  if (need.some(x => x < 0)) return { ok: false, why: 'a vertex already has more than 6 edges' };
  const corners = f => { let o = [0, 0]; return f.sides.map(s => { const e = E.get(s.edge), v = s.dir > 0 ? e.v0 : e.v1, at = s.dir > 0 ? s.at : add2(s.at, e.shift); o = at; return { v, at: o }; }); };
  const opt = g.faces.map(f => { const cs = corners(f), n = cs.length, list = [];
    triangulations(n).forEach(ds => { const deg = new Array(ids.length).fill(0); ds.forEach(([i, j]) => { deg[ix.get(cs[i].v)]++; deg[ix.get(cs[j].v)]++; });
      list.push({ deg, diag: ds.map(([i, j]) => ({ v0: cs[i].v, v1: cs[j].v, shift: sub2(cs[j].at, cs[i].at) })), fan: null }); });
    if (n === 6 && opts.fans !== false) { const deg = new Array(ids.length).fill(0); cs.forEach(c => deg[ix.get(c.v)]++); list.push({ deg, diag: [], fan: cs }); }   // a new centre of degree 6
    return { f: f.id, n, list }; }).sort((x, y) => x.list.length - y.list.length);
  const ek = (u, w, s) => (u < w || (u === w && (s[0] > 0 || (s[0] === 0 && s[1] > 0)))) ? u + '|' + w + '|' + s : w + '|' + u + '|' + neg2(s);
  const base = new Set(g.edges.map(e => ek(e.v0, e.v1, e.shift)));
  const last = opt[opt.length - 1], byDeg = new Map(); last.list.forEach(c => { const k = c.deg.join(','); (byDeg.get(k) || byDeg.set(k, []).get(k)).push(c); });
  let tried = 0, found = null; const pick = [], rem = need.slice(), sols = [], max = opts.max || 1;
  const valid = choice => {             // no edge doubled in the plane: the triangulation must be a simple graph
    const seen = new Set(base); for (const c of choice) for (const d of c.diag) { const k = ek(d.v0, d.v1, d.shift); if (seen.has(k)) return false; seen.add(k); } return true; };
  const rec = k => {
    if (found) return;
    if (k === opt.length - 1) { tried++; const l = byDeg.get(rem.join(',')); if (l) for (const c of l) { const ch = pick.concat([c]); if (valid(ch)) { sols.push(ch.map((x, i) => ({ face: (i < pick.length ? opt[i] : last).f, ...x }))); if (sols.length >= max) { found = true; return; } } } return; }
    for (const c of opt[k].list) { let ok = true; for (let i = 0; i < rem.length; i++) if (c.deg[i] > rem[i]) { ok = false; break; } if (!ok) continue;
      for (let i = 0; i < rem.length; i++) rem[i] -= c.deg[i]; pick.push(c); rec(k + 1); pick.pop(); for (let i = 0; i < rem.length; i++) rem[i] += c.deg[i]; if (found) return; } };
  rec(0);
  if (!sols.length) return { ok: false, why: 'no triangulation of the faces gives every vertex degree 6 at this period', tried };
  const all = sols.map(sol => buildCertificate(g, sol)), first = all.find(c => c.ok) || all[0];
  return Object.assign({ tried, solutions: all }, first);
}
function buildCertificate(g, found) {   // the triangulated grid, checked: all faces triangles, every vertex degree 6, a simple graph
  const vs = g.vertices.map(v => ({ id: v.id, pos: v.pos })), es = g.edges.map(e => ({ id: e.id, v0: e.v0, v1: e.v1, shift: e.shift })), added = [], centres = [];
  found.forEach((c, i) => { c.diag.forEach((d, k) => { const id = 'x' + i + '_' + k; es.push({ id, v0: d.v0, v1: d.v1, shift: d.shift }); added.push(id); });
    if (c.fan) { const cid = 'c' + i, F = g.faces.find(f => f.id === c.face), ctr = G.centroid(G.faceOutline(g, F, [0, 0]).pts); vs.push({ id: cid, pos: ctr }); centres.push(cid);
      c.fan.forEach((cn, k) => { const id = 'y' + i + '_' + k; es.push({ id, v0: cid, v1: cn.v, shift: cn.at }); added.push(id); }); } });
  const T = makeGrid({ lattice: g.lattice, vertices: vs, edges: es }, 'triangulated ' + g.kind), inv = invariants(T);
  const ok = !T.errors.length && T.faces.every(f => f.sides.length === 3) && Object.values(inv.valence).every(n => n === 6);
  return { ok, tri: T, added, centres, choice: found.map(c => ({ face: c.face, diagonals: c.diag.length, fan: !!c.fan })), errors: T.errors };
}

/* ---------------- a continuous path between two geometries of one grid, through convex placements (Tutte) ----------------
 * Each vertex is placed at a weighted average of its neighbours (lattice shifts included). With positive weights, a 3-connected
 * periodic planar grid is then embedded without crossings, with convex faces (Tutte; periodic form: Delgado-Friedrichs 2005).
 * Weights that reproduce a given geometry exist when no vertex has an angle above 180° (mean-value weights; a straight angle
 * gives the two collinear neighbours). Interpolating the weights and the lattice gives a path whose every point is such a placement. */
function tutteWeights(g) {
  const V = new Map(g.vertices.map(v => [v.id, v.pos])), E = new Map(g.edges.map(e => [e.id, e])), out = outgoing(g), W = new Map();
  for (const v of g.vertices) { const l = out.get(v.id), x = v.pos, nb = l.map(h => { const e = E.get(h.e), sh = latVec(g.lattice, h.dir > 0 ? e.shift : neg2(e.shift)), w = V.get(h.dir > 0 ? e.v1 : e.v0); return P(w.x + sh.x, w.y + sh.y); });
    const n = nb.length, ang = nb.map((p, k) => { const q = nb[(k + 1) % n]; let t = Math.atan2(q.y - x.y, q.x - x.x) - Math.atan2(p.y - x.y, p.x - x.x); while (t <= 0) t += TAU; return t; });
    if (ang.some(t => t > Math.PI + 1e-9)) return null;                                  // a vertex outside its neighbours' hull: no convex weights
    const st = ang.findIndex(t => Math.abs(t - Math.PI) <= 1e-9), w = new Array(n).fill(0);
    if (st >= 0) { const u = nb[st], z = nb[(st + 1) % n], L = G.dist(u, z); w[st] = G.dist(x, z) / L; w[(st + 1) % n] = G.dist(x, u) / L; }
    else nb.forEach((p, k) => { w[k] = (Math.tan(ang[(k - 1 + n) % n] / 2) + Math.tan(ang[k] / 2)) / G.dist(x, p); });
    const sum = w.reduce((a, b) => a + b, 0); W.set(v.id, w.map(t => t / sum)); }
  return W;
}
function tuttePlace(g, W, lattice, anchor) {
  const ids = g.vertices.map(v => v.id), ix = new Map(ids.map((v, i) => [v, i])), E = new Map(g.edges.map(e => [e.id, e])), out = outgoing(g), n = ids.length;
  const A = Array.from({ length: n }, () => new Array(n).fill(0)), bx = new Array(n).fill(0), by = new Array(n).fill(0);
  ids.forEach((v, i) => { const l = out.get(v), w = W.get(v); l.forEach((h, k) => { const e = E.get(h.e), j = ix.get(h.dir > 0 ? e.v1 : e.v0), sh = latVec(lattice, h.dir > 0 ? e.shift : neg2(e.shift));
    A[i][i] += w[k]; A[i][j] -= w[k]; bx[i] += w[k] * sh.x; by[i] += w[k] * sh.y; }); });
  A[0] = new Array(n).fill(0); A[0][0] = 1; bx[0] = anchor.x; by[0] = anchor.y;
  const x = solve(A.map(r => r.slice()), bx), y = solve(A.map(r => r.slice()), by), pos = {}; ids.forEach((v, i) => { pos[v] = P(x[i], y[i]); });
  return withGeometry(g, pos, lattice);
}
// lattice A → lattice B without ever passing through a degenerate cell: the linear map taking A to B, split into a rotation and a
// positive-definite stretch (polar decomposition); the rotation angle and the stretch are interpolated, so the determinant stays > 0
function latticePath(LA, LB) {
  const inv = m => { const d = m[0] * m[3] - m[1] * m[2]; return [m[3] / d, -m[1] / d, -m[2] / d, m[0] / d]; }, mul = (a, b) => [a[0] * b[0] + a[1] * b[2], a[0] * b[1] + a[1] * b[3], a[2] * b[0] + a[3] * b[2], a[2] * b[1] + a[3] * b[3]];
  const M = mul([LB.b1.x, LB.b2.x, LB.b1.y, LB.b2.y], inv([LA.b1.x, LA.b2.x, LA.b1.y, LA.b2.y])), th = Math.atan2(M[2] - M[1], M[0] + M[3]);
  const R = t => [Math.cos(th * t), -Math.sin(th * t), Math.sin(th * t), Math.cos(th * t)], S = mul(R(-1), M);
  const Mt = t => mul(R(t), [1 - t + t * S[0], t * S[1], t * S[2], 1 - t + t * S[3]]), ap = (m, p) => P(m[0] * p.x + m[1] * p.y, m[2] * p.x + m[3] * p.y);
  return { map: Mt, at: t => { const m = Mt(t); return { b1: ap(m, LA.b1), b2: ap(m, LA.b2) }; }, apply: ap };
}
function tuttePath(gA, gB) {             // a function t → grid, or null if an end has a vertex outside its neighbours' hull
  const WA = tutteWeights(gA), WB = tutteWeights(gB); if (!WA || !WB) return null;
  const LP = latticePath(gA.lattice, gB.lattice);
  return t => { const W = new Map(); WA.forEach((w, v) => W.set(v, w.map((a, k) => a + (WB.get(v)[k] - a) * t)));
    const a0 = gA.vertices[0].pos, b0 = gB.vertices[0].pos; return tuttePlace(gA, W, LP.at(t), P(a0.x + (b0.x - a0.x) * t, a0.y + (b0.y - a0.y) * t)); };
}

/* ---------------- the triangle-lattice coordinates of a 6-regular triangulation ---------------- */
const DIRS = [[1, 0], [0, 1], [-1, 1], [-1, 0], [0, -1], [1, -1]];
function latticeMap(T) {
  const out = outgoing(T), E = new Map(T.edges.map(e => [e.id, e])), rot = new Map(), first = T.vertices[0].id;
  rot.set(first, 0); const q = [first];
  const dirOf = (v, e, d) => { const l = out.get(v), i = l.findIndex(h => h.e === e && h.dir === d); return (rot.get(v) + i) % 6; };
  while (q.length) { const v = q.shift(); out.get(v).forEach(h => { const e = E.get(h.e), w = h.dir > 0 ? e.v1 : e.v0, dv = dirOf(v, h.e, h.dir), want = (dv + 3) % 6;
    const l = out.get(w), j = l.findIndex(x => x.e === h.e && x.dir === -h.dir), r = ((want - j) % 6 + 6) % 6;
    if (!rot.has(w)) { rot.set(w, r); q.push(w); } else if (rot.get(w) !== r) throw new Error('inconsistent directions: not a triangular lattice'); }); }
  // coordinates on the universal cover: BFS over (class, offset) until both lattice translations of the first class are known
  const C = new Map(), key = (v, o) => v + '#' + o.join(','), queue = [[first, [0, 0]]]; C.set(key(first, [0, 0]), [0, 0]);
  const need = [key(first, [1, 0]), key(first, [0, 1])];
  const seenCls = new Set([first]);
  while (queue.length && !(need.every(k => C.has(k)) && seenCls.size === T.vertices.length)) { const [v, o] = queue.shift(), c = C.get(key(v, o)); seenCls.add(v);
    out.get(v).forEach(h => { const e = E.get(h.e), w = h.dir > 0 ? e.v1 : e.v0, ow = h.dir > 0 ? add2(o, e.shift) : sub2(o, e.shift), d = DIRS[dirOf(v, h.e, h.dir)], cw = add2(c, d);
      if (Math.abs(ow[0]) > 8 || Math.abs(ow[1]) > 8) return; const k = key(w, ow); if (!C.has(k)) { C.set(k, cw); queue.push([w, ow]); seenCls.add(w); } }); }
  const S1 = C.get(need[0]), S2 = C.get(need[1]); if (!S1 || !S2) throw new Error('lattice translations not reached');
  const S = [S1, S2], at = (v, o) => { const c = C.get(key(v, o)); return c; };
  const coord = {}; T.vertices.forEach(v => { let c = at(v.id, [0, 0]); if (!c) { for (const [k, val] of C) { const [vv, oo] = k.split('#'); if (vv === v.id) { const o = oo.split(',').map(Number); c = sub2(val, add2([o[0] * S1[0], o[0] * S1[1]], [o[1] * S2[0], o[1] * S2[1]])); break; } } } coord[v.id] = c; });
  // every edge must be ONE unit step of the triangular lattice, consistently
  let bad = 0; T.edges.forEach(e => { const c0 = coord[e.v0], c1 = add2(coord[e.v1], add2([e.shift[0] * S1[0], e.shift[0] * S1[1]], [e.shift[1] * S2[0], e.shift[1] * S2[1]])), d = sub2(c1, c0);
    if (!DIRS.some(x => x[0] === d[0] && x[1] === d[1])) bad++; });
  const det = S1[0] * S2[1] - S1[1] * S2[0];
  return { M: S, det, coord, bad, ok: bad === 0 && det === T.vertices.length };
}
const triWorld = c => P(c[0] + 0.5 * c[1], S3 * c[1]);

/* ---------------- regular faces, unit edges (Levenberg–Marquardt) ---------------- */
function regularize(g, opts) {
  opts = opts || {};
  const ids = g.vertices.map(v => v.id), ix = new Map(ids.map((v, i) => [v, i])), E = new Map(g.edges.map(e => [e.id, e]));
  const terms = [];             // [i, j, shift, length]: |pos_j + shift − pos_i| = length
  g.edges.forEach(e => terms.push([ix.get(e.v0), ix.get(e.v1), e.shift, 1]));
  g.faces.forEach(f => { let o = [0, 0]; const cs = f.sides.map(s => { const e = E.get(s.edge), v = s.dir > 0 ? e.v0 : e.v1, at = s.dir > 0 ? s.at : add2(s.at, e.shift); o = at; return { i: ix.get(v), at: o }; }), n = cs.length;
    for (let a = 0; a < n; a++) for (let b = a + 2; b < n; b++) { if (a === 0 && b === n - 1) continue; const k = b - a; terms.push([cs[a].i, cs[b].i, sub2(cs[b].at, cs[a].at), Math.sin(k * Math.PI / n) / Math.sin(Math.PI / n)]); } });
  let x = []; g.vertices.forEach(v => x.push(v.pos.x, v.pos.y)); x.push(g.lattice.b1.x, g.lattice.b1.y, g.lattice.b2.x, g.lattice.b2.y);
  const nv = ids.length, resid = x => terms.map(([i, j, s, L]) => { const L1 = P(x[2 * nv], x[2 * nv + 1]), L2 = P(x[2 * nv + 2], x[2 * nv + 3]);
    const px = x[2 * j] + s[0] * L1.x + s[1] * L2.x - x[2 * i], py = x[2 * j + 1] + s[0] * L1.y + s[1] * L2.y - x[2 * i + 1]; return Math.hypot(px, py) - L; })
    .concat([x[0] - g.vertices[0].pos.x, x[1] - g.vertices[0].pos.y, x[2 * nv + 1] * (opts.fixAngle === false ? 0 : 1)]);   // gauge: first vertex fixed, b1 horizontal
  const norm = r => Math.sqrt(r.reduce((s, v) => s + v * v, 0));
  let r = resid(x), lam = 1e-3, it = 0;
  for (; it < (opts.iters || 400) && norm(r) > 1e-14; it++) {
    const m = r.length, n = x.length, J = Array.from({ length: m }, () => new Array(n).fill(0)), h = 1e-7;
    for (let k = 0; k < n; k++) { const xp = x.slice(); xp[k] += h; const rp = resid(xp); for (let i = 0; i < m; i++) J[i][k] = (rp[i] - r[i]) / h; }
    const A = Array.from({ length: n }, (_, p) => Array.from({ length: n }, (_, q) => J.reduce((s, row) => s + row[p] * row[q], 0))), gvec = Array.from({ length: n }, (_, p) => J.reduce((s, row, i) => s + row[p] * r[i], 0));
    let improved = false;
    for (let tries = 0; tries < 12 && !improved; tries++) {
      const M = A.map((row, p) => row.map((v, q) => v + (p === q ? lam * (1 + A[p][p]) : 0))), b = gvec.map(v => -v), d = solve(M, b);
      const xn = x.map((v, k) => v + d[k]), rn = resid(xn);
      if (norm(rn) < norm(r)) { x = xn; r = rn; lam = Math.max(lam / 4, 1e-12); improved = true; } else lam *= 8; }
    if (!improved) break;
  }
  const h2 = clone(spec(g)); h2.vertices.forEach((v, i) => { v.pos = P(x[2 * i], x[2 * i + 1]); }); h2.lattice = { b1: P(x[2 * nv], x[2 * nv + 1]), b2: P(x[2 * nv + 2], x[2 * nv + 3]) };
  const out = makeGrid(h2, g.kind); out.residual = norm(r); out.iterations = it; return out;
}
function solve(A, b) { const n = b.length, M = A.map((r, i) => r.concat([b[i]]));
  for (let c = 0; c < n; c++) { let p = c; for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r; [M[c], M[p]] = [M[p], M[c]];
    const d = M[c][c] || 1e-300; for (let r = 0; r < n; r++) { if (r === c) continue; const f = M[r][c] / d; if (f) for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k]; } }
  return M.map((r, i) => r[n] / (r[i] || 1e-300)); }

// the same combinatorics with new positions and lattice (for morphing between two geometries of one grid)
function withGeometry(g, pos, lattice, name) { const h = clone(spec(g)); h.vertices.forEach(v => { v.pos = P(pos[v.id].x, pos[v.id].y); }); h.lattice = clone(lattice); return makeGrid(h, name || g.kind); }
function lerpGeometry(gA, gB, t) { const pos = {}; gA.vertices.forEach((v, i) => { const w = gB.vertices[i]; pos[v.id] = P(v.pos.x + (w.pos.x - v.pos.x) * t, v.pos.y + (w.pos.y - v.pos.y) * t); });
  const L = k => P(gA.lattice[k].x + (gB.lattice[k].x - gA.lattice[k].x) * t, gA.lattice[k].y + (gB.lattice[k].y - gA.lattice[k].y) * t);
  return withGeometry(gA, pos, { b1: L('b1'), b2: L('b2') }); }

return { G, S3, TAU, P, clone, deriveFaces, makeGrid, outgoing, triangleGrid, unitGrid, supercell, removeEdges, removeVertices, invariants, shapes, cornerAngles, dual,
  triangulations, certificate, buildCertificate, tutteWeights, tuttePlace, tuttePath, latticePath, latticeMap, triWorld, DIRS, regularize, withGeometry, lerpGeometry, canon };
});
