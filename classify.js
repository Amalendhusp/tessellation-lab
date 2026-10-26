/* tessellation-mobile-workspace-v6.2-grid-m2b / classify.js · TESSELLATION CLASSIFICATION (M2B), in three separate levels
 *
 *   1. TOPOLOGY (the arrangement): which faces meet at each vertex, and which faces are neighbours. Computed from the vertices
 *      and edges alone: positions, lengths and angles play no part, so it is kept under any deformation that keeps the arrangement.
 *      A vertex of the arrangement is a point where 3 or more edges meet; a point with 2 edges lies on a side and is not one.
 *   2. GEOMETRY (the shapes): each shape's real corners (angles other than 180°), its side lengths and its angles, measured.
 *   3. REGULARITY: the conditions of a regular or Archimedean tiling, each checked numerically:
 *        R1 every shape is a regular polygon (equal sides, equal angles);
 *        R2 edge-to-edge: the shapes' corners are exactly the vertices (no vertex on the straight side of a shape, no corner
 *           where only two shapes meet);
 *        R3 every edge has the same length;
 *        R4 every vertex has the same arrangement (one vertex type).
 *      R1–R4 with one kind of polygon = a regular tiling; with several kinds = an Archimedean (semiregular) tiling. By the
 *      classical theorem (Grünbaum & Shephard 2.1.3) these are exactly the 11 tilings of NAMES.
 *
 * THE NAME follows only from what was verified:
 *   R1–R4 hold → the regular or Archimedean name, e.g. "Trihexagonal tessellation (3.6.3.6)";
 *   otherwise  → the polygon family from the real corners, e.g. "Quadrilateral tessellation", "Triangle–hexagon tessellation".
 *   The arrangement is still recognised and reported separately (e.g. "every vertex 4.4.4.4: the arrangement of the square tiling").
 *
 * Tolerances: angles TOL.angle radians, lengths TOL.length × the mean side length (so the result does not depend on scale,
 * rotation or position). Far above floating-point noise, far below anything visible.
 *
 * VALIDITY IS NOT DECIDED HERE. Whether a grid is a tiling at all is decided by merge.js's three judges (and M1's validator);
 * this module assumes a valid tiling and never changes that verdict. A valid tiling need not be regular, semiregular or named. */
(function (root, factory) {
  const C = factory(root);
  if (typeof module === 'object' && module.exports) module.exports = C; else root.TessClassify = C;
})(typeof self !== 'undefined' ? self : globalThis, function (root) {
'use strict';
const node = typeof module === 'object' && module.exports;
const G = node ? require('./grid.js') : root.TessGrid, T = node ? require('./topo.js') : root.TessTopo;
const TOL = { angle: 1e-6, length: 1e-6 };
const DEG = 180 / Math.PI;

// the 11 tilings with one vertex type by regular polygons (3 regular + 8 Archimedean), keyed by vertex type
const NAMES = { '3.3.3.3.3.3': 'triangular', '4.4.4.4': 'square', '6.6.6': 'hexagonal', '3.6.3.6': 'trihexagonal', '3.3.3.3.6': 'snub hexagonal',
  '3.3.3.4.4': 'elongated triangular', '3.3.4.3.4': 'snub square', '3.4.6.4': 'rhombitrihexagonal', '4.8.8': 'truncated square', '3.12.12': 'truncated hexagonal', '4.6.12': 'truncated trihexagonal' };
const REGULAR = new Set(['3.3.3.3.3.3', '4.4.4.4', '6.6.6']);
// their duals (Laves tilings), keyed by face type: the numbers of edges at the vertices going round every face
const LAVES = { '6.6.6': 'triangular', '4.4.4.4': 'square', '3.3.3.3.3.3': 'hexagonal', '3.6.3.6': 'rhombille', '3.3.3.3.6': 'floret pentagonal',
  '3.3.3.4.4': 'prismatic pentagonal', '3.3.4.3.4': 'Cairo pentagonal', '3.4.6.4': 'deltoidal trihexagonal', '4.8.8': 'tetrakis square', '3.12.12': 'triakis triangular', '4.6.12': 'kisrhombille' };
const POLY = { 3: 'triangle', 4: 'quadrilateral', 5: 'pentagon', 6: 'hexagon', 7: 'heptagon', 8: 'octagon', 9: 'nonagon', 10: 'decagon', 11: 'hendecagon', 12: 'dodecagon' };
const polyName = n => POLY[n] || n + '-gon';
const cap = s => s.charAt(0).toUpperCase() + s.slice(1);
const plural = s => /rhombus$/.test(s) ? s.replace(/rhombus$/, 'rhombi') : s + 's';
const article = s => (/^[aeiou]/i.test(s) ? 'an ' : 'a ') + s;
const deg = a => +(a * DEG).toFixed(1);

/* ---------------- 1. topology: vertices and edges only ---------------- */
function topology(g) {
  const inv = T.invariants(g), E = new Map(g.edges.map(e => [e.id, e])), val = inv.valence, isV = v => val[v] >= 3;
  const origin = s => { const e = E.get(s.edge); return s.dir > 0 ? e.v0 : e.v1; }, owner = new Map();
  g.faces.forEach(f => f.sides.forEach(s => owner.set(s.edge + ':' + s.dir, f.id)));
  // going round each face, the size of the neighbour across each side of the arrangement (a side runs from vertex to vertex;
  // points with 2 edges on it border the same neighbour, so the side's first edge decides)
  const adjacency = {}; g.faces.forEach(f => { adjacency[f.id] = T.canon(f.sides.filter(s => isV(origin(s))).map(s => inv.faceSizes[owner.get(s.edge + ':' + (-s.dir))])); });
  const faceTypes = [...new Set(Object.values(inv.ftype))].sort(), types = inv.vertexTypes;
  let arrangement = null;
  if (types.length === 1 && NAMES[types[0]]) arrangement = { name: NAMES[types[0]], notation: types[0], by: 'vertex' };
  else if (faceTypes.length === 1 && LAVES[faceTypes[0]]) arrangement = { name: LAVES[faceTypes[0]], notation: '[' + faceTypes[0] + ']', by: 'face' };
  // kinds of face of the arrangement: number of vertices + neighbours going round
  const kinds = new Map(); g.faces.forEach(f => { const k = inv.faceSizes[f.id] + '|' + adjacency[f.id], x = kinds.get(k) || { vertices: inv.faceSizes[f.id], neighbours: adjacency[f.id], faces: [] }; x.faces.push(f.id); kinds.set(k, x); });
  return { vertexTypes: types, faceTypes, arrangement, vertices: inv.V, points: inv.nodes, faces: g.faces.length, faceSizes: inv.faceSizes, adjacency,
    faceKinds: [...kinds.values()].sort((a, b) => a.vertices - b.vertices || (a.neighbours < b.neighbours ? -1 : 1)), valence: val };
}

/* ---------------- 2. geometry: real corners, sides and angles ---------------- */
// every point on a face's outline, and the vertex (class id) where each side starts
function outline(g, f) {
  const E = new Map(g.edges.map(e => [e.id, e])), o = G.faceOutline(g, f, [0, 0]), at = [];
  let i = 0; f.sides.forEach((s, k) => { const e = E.get(s.edge); at[i] = s.dir > 0 ? e.v0 : e.v1; i += o.sides[k].length - 1; });
  return { pts: o.pts, vertexAt: at, curved: f.sides.some(s => E.get(s.edge).curve) };
}
function shapeName(n, a, s, cp, eqS, eqA) {
  const allS = s.every(v => eqS(v, s[0])), allA = a.every(v => eqA(v, a[0])), convex = a.every(v => v < Math.PI - TOL.angle);
  if (allS && allA) return n === 3 ? 'equilateral triangle' : n === 4 ? 'square' : 'regular ' + polyName(n);
  if (n === 3) { const iso = eqS(s[0], s[1]) || eqS(s[1], s[2]) || eqS(s[2], s[0]), right = a.some(v => eqA(v, Math.PI / 2)); return (right ? 'right ' : '') + (iso ? 'isosceles' : 'scalene') + ' triangle'; }
  if (n === 4) {
    const v = k => ({ x: cp[(k + 1) % 4].x - cp[k].x, y: cp[(k + 1) % 4].y - cp[k].y }), par = (i, j) => { const p = v(i), q = v(j); return Math.abs(p.x * q.y - p.y * q.x) / (Math.hypot(p.x, p.y) * Math.hypot(q.x, q.y)) <= TOL.angle; };
    const kite = (eqS(s[0], s[1]) && eqS(s[2], s[3])) || (eqS(s[1], s[2]) && eqS(s[3], s[0]));
    if (!convex) return kite ? 'dart' : 'concave quadrilateral';
    if (allA) return 'rectangle'; if (allS) return 'rhombus';
    const p02 = par(0, 2), p13 = par(1, 3);
    if (p02 && p13) return 'parallelogram'; if (kite) return 'kite';
    if (p02) return eqS(s[1], s[3]) ? 'isosceles trapezoid' : 'trapezoid'; if (p13) return eqS(s[0], s[2]) ? 'isosceles trapezoid' : 'trapezoid';
    return 'irregular quadrilateral';
  }
  if (allS) return (convex ? '' : 'concave ') + 'equilateral ' + polyName(n);
  if (allA) return 'equiangular ' + polyName(n);
  return (convex ? 'irregular ' : 'concave ') + polyName(n);
}
function geometry(g, topo) {
  const val = topo.valence, isV = v => v !== undefined && val[v] >= 3;
  const raw = g.faces.map(f => { const o = outline(g, f), ang = T.cornerAngles(o.pts), n = o.pts.length;
    const idx = ang.map((t, i) => i).filter(i => Math.abs(ang[i] - Math.PI) > TOL.angle);
    const seg = i => G.dist(o.pts[i], o.pts[(i + 1) % n]), sides = idx.map((i, k) => { let L = 0; for (let j = i; j !== idx[(k + 1) % idx.length]; j = (j + 1) % n) L += seg(j); return L; });
    // edges of the arrangement along this face (vertex to vertex), for R3
    const vIdx = o.vertexAt.map((v, i) => isV(v) ? i : -1).filter(i => i >= 0), edgeLens = vIdx.map((i, k) => { let L = 0; for (let j = i; j !== vIdx[(k + 1) % vIdx.length]; j = (j + 1) % n) L += seg(j); return L; });
    return { id: f.id, n: idx.length, cp: idx.map(i => o.pts[i]), angles: idx.map(i => ang[i]), sides, edgeLens, curved: o.curved,
      straightVertices: o.vertexAt.filter((v, i) => isV(v) && Math.abs(ang[i] - Math.PI) <= TOL.angle).length,    // vertices on a straight side
      loneCorners: idx.filter(i => !isV(o.vertexAt[i])).length };                                                   // corners where only 2 shapes meet
  });
  const all = raw.flatMap(f => f.sides), scale = all.reduce((s, v) => s + v, 0) / (all.length || 1);
  const eqS = (x, y) => Math.abs(x - y) <= TOL.length * scale, eqA = (x, y) => Math.abs(x - y) <= TOL.angle;
  raw.forEach(f => { const n = f.n, ideal = (n - 2) * Math.PI / n, mean = f.sides.reduce((s, v) => s + v, 0) / n;
    f.equilateral = f.sides.every(v => eqS(v, f.sides[0])); f.equiangular = f.angles.every(v => eqA(v, f.angles[0])); f.convex = f.angles.every(v => v < Math.PI - TOL.angle);
    f.regular = !f.curved && f.equilateral && f.equiangular;
    f.angleDev = Math.max(...f.angles.map(v => Math.abs(v - ideal))); f.sideDev = (Math.max(...f.sides) - Math.min(...f.sides)) / mean;
    f.name = f.curved ? 'shape with curved sides' : shapeName(n, f.angles, f.sides, f.cp, eqS, eqA); });
  // congruent shapes (up to rotation and reflection), by the cyclic sequence of (angle, side)
  const same = (x, y) => { const n = x.n; if (n !== y.n) return false;
    for (const rev of [false, true]) for (let o = 0; o < n; o++) { let ok = true;
      for (let k = 0; k < n && ok; k++) { const i = rev ? (o - k + 2 * n) % n : (o + k) % n, s = rev ? y.sides[(i - 1 + n) % n] : y.sides[i]; if (!eqA(y.angles[i], x.angles[k]) || !eqS(s, x.sides[k])) ok = false; }
      if (ok) return true; }
    return false; };
  const classes = []; raw.forEach(f => { const c = classes.find(c => same(c.f, f)); if (c) c.faces.push(f.id); else classes.push({ f, faces: [f.id] }); });
  const unit = Math.min(...all), shapes = classes.map(({ f, faces }) => ({ corners: f.n, name: f.name, faces, count: faces.length, regular: f.regular, equilateral: f.equilateral, equiangular: f.equiangular, convex: f.convex,
    angles: [...new Set(f.angles.map(deg))].sort((a, b) => a - b), sides: [...new Set(f.sides.map(v => +(v / unit).toFixed(3)))].sort((a, b) => a - b), angleDev: f.angleDev, sideDev: f.sideDev }))
    .sort((a, b) => a.corners - b.corners || a.name.localeCompare(b.name));
  const kinds = [...new Set(raw.map(f => f.n))].sort((a, b) => a - b);
  const family = kinds.length <= 3 ? kinds.map((n, i) => i ? polyName(n) : cap(polyName(n))).join('–') + ' tessellation' : 'Mixed-polygon tessellation';
  const straight = raw.reduce((s, f) => s + f.straightVertices, 0), lone = raw.reduce((s, f) => s + f.loneCorners, 0), edgeLens = raw.flatMap(f => f.edgeLens);
  return { shapes, kinds, family, perFace: Object.fromEntries(raw.map(f => [f.id, { corners: f.n, name: f.name, regular: f.regular }])),
    edgeToEdge: !straight && !lone, straightVertices: straight, loneCorners: lone, curved: raw.some(f => f.curved),
    edgeSpread: (Math.max(...edgeLens) - Math.min(...edgeLens)) / scale, edgeLengths: [...new Set(edgeLens.map(v => +(v / unit).toFixed(3)))].sort((a, b) => a - b), scale };
}

/* ---------------- 3. regularity: R1–R4, numerically ---------------- */
const fmtDeg = a => { const d = a * DEG; return d >= 0.1 ? +d.toFixed(1) : +d.toPrecision(2); };
const fmtPct = r => { const p = 100 * r; return p >= 0.1 ? +p.toFixed(1) : +p.toPrecision(2); };
function regularity(topo, geo) {
  // how far each irregular shape is from the regular polygon with the same number of corners
  const off = geo.shapes.filter(s => !s.regular).map(s => `${s.name}: ` + [s.angleDev > TOL.angle ? `an angle is off by ${fmtDeg(s.angleDev)}°` : '', s.sideDev > TOL.length ? `sides differ by ${fmtPct(s.sideDev)}%` : '', s.angleDev <= TOL.angle && s.sideDev <= TOL.length ? 'curved sides' : ''].filter(Boolean).join(', '));
  const conditions = [
    { key: 'R1', label: 'every shape is a regular polygon', ok: !off.length,
      detail: !off.length ? 'equal sides and equal angles in every shape' : off.slice(0, 3).join('; ') + (off.length > 3 ? `; and ${off.length - 3} more` : '') },
    { key: 'R2', label: 'shapes meet corner to corner (edge-to-edge)', ok: geo.edgeToEdge,
      detail: geo.edgeToEdge ? 'every corner is a vertex and every vertex is a corner of each shape there' : [geo.straightVertices ? `${geo.straightVertices} vertex-in-side contact${geo.straightVertices > 1 ? 's' : ''} per block (a vertex on the straight side of a shape)` : '', geo.loneCorners ? `${geo.loneCorners} corner${geo.loneCorners > 1 ? 's' : ''} where only two shapes meet` : ''].filter(Boolean).join('; ') },
    { key: 'R3', label: 'every edge has the same length', ok: geo.edgeSpread <= TOL.length, detail: geo.edgeLengths.length === 1 ? 'all edges equal' : `edge lengths ${geo.edgeLengths.join(', ')}` },
    { key: 'R4', label: 'every vertex has the same arrangement', ok: topo.vertexTypes.length === 1, detail: topo.vertexTypes.length === 1 ? 'every vertex ' + topo.vertexTypes[0] : `${topo.vertexTypes.length} vertex types: ${topo.vertexTypes.join(', ')}` }
  ];
  const ok = k => conditions.find(c => c.key === k).ok, type = topo.vertexTypes[0];
  let kind = 'none';
  if (ok('R1') && ok('R2') && ok('R3')) kind = !ok('R4') ? 'regular-polygons' : !NAMES[type] ? 'unlisted' : REGULAR.has(type) ? 'regular' : 'archimedean';
  const named = kind === 'regular' || kind === 'archimedean';
  const verdict = kind === 'regular' ? `a regular tiling: the ${NAMES[type]} tiling ${type}`
    : kind === 'archimedean' ? `an Archimedean (semiregular) tiling: the ${NAMES[type]} tiling ${type}`
    : kind === 'regular-polygons' ? `a tiling by regular polygons with ${topo.vertexTypes.length} vertex types: not Archimedean`
    : kind === 'unlisted' ? 'regular polygons and one vertex type, but not one of the 11 (please report this)'
    : 'neither regular nor Archimedean';
  return { conditions, kind, named, name: named ? NAMES[type] : null, notation: named ? type : null, verdict };
}

/* ---------------- all three, and the name ---------------- */
function classify(g) {
  const topo = topology(g), geo = geometry(g, topo), reg = regularity(topo, geo);
  const name = reg.named ? `${cap(reg.name)} tessellation (${reg.notation})` : geo.family;
  const arrangementText = topo.arrangement ? (topo.arrangement.by === 'vertex' ? `every vertex ${topo.arrangement.notation}: the arrangement of the ${topo.arrangement.name} tiling`
    : `every face ${topo.arrangement.notation}: the arrangement of the ${topo.arrangement.name} tiling`)
    : topo.vertexTypes.length === 1 ? `every vertex ${topo.vertexTypes[0]}` : `${topo.vertexTypes.length} vertex types: ${topo.vertexTypes.join(', ')}`;
  return { name, topology: topo, geometry: geo, regularity: reg, arrangementText, tolerance: Object.assign({}, TOL) };
}

return { TOL, NAMES, LAVES, REGULAR, POLY, polyName, plural, article, topology, geometry, regularity, classify, shapeName };
});
