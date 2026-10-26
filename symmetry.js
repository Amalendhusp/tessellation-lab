/* tessellation-mobile-workspace-v6.8-square-reflection / symmetry.js · REPEAT RULES AS SYMMETRIES OF A REGULAR GRID
 *
 * A regular grid keeps its junctions; only its edges are pushed and pulled. So every symmetry of an edited tiling is a symmetry of the
 * regular grid it started from. A REPEAT RULE is a set of such symmetries (generators) together with the repeat block (the lattice of the
 * grid `g`, a translation quotient as in grid.js). Everything else follows from how the generators move the EDGES of the block:
 *
 *   orbit        the edge classes a generator chain carries onto each other. One of them (the representative) holds the boundary; the
 *                others are its images. With the edge-relative coordinates of grid.js (s along the edge from its first end, t to its left):
 *                    a translation or rotation   direction kept: (s, t)        direction reversed: (1 − s, −t)
 *                    a reflection or glide        direction kept: (s, −t)       direction reversed: (1 − s,  t)
 *                written here as two bits (r: s → 1 − s and the order reversed; n: t → −t).
 *   constraint   when a chain brings an edge back onto ITSELF (or onto a translated copy, which is the same boundary) with a map that is
 *                not the identity, the boundary must be its own image:
 *                    n          the edge lies on a mirror line            → it must stay STRAIGHT (nothing to push or pull)
 *                    r          a mirror line crosses it at its middle    → it must be SYMMETRIC about its middle
 *                    r and n    a half-turn centre sits at its middle     → it must be POINT-SYMMETRIC (an S-shape)
 *                    two of them → all three → straight
 *
 * A boundary that satisfies its constraint, carried round its orbit, gives a drawing with exactly the chosen symmetries. It is a tiling as
 * long as no side crosses another: that is checked by grid.js (the quick guard during a drag, the full validator before a commit).
 * invariant() is an independent check of the symmetry itself: it reflects or turns the drawn shapes and looks for each image among the
 * drawn shapes; it does not use the orbits.
 *
 * mirrorPairing() is the rule of this checkpoint: REFLECTION ON THE SQUARE GRID. Two edges chosen by the participant are mirror images in
 * the square grid only across one of three kinds of line, and each kind has its own consequences (see SYMMETRY_FEASIBILITY.md):
 *     diagonal   through a corner: the two sides at that corner are twins; every square keeps a mirror line through itself; block 1 square
 *     mid-line   through the middle of a square: its two opposite sides are twins, the two sides it crosses must be symmetric; two
 *                different shapes alternate; block 2 squares
 *     side       on a grid line: the squares on both sides are mirror images; the sides on the line must stay straight, the sides that
 *                continue each other across it are twins; block 2 squares */
(function (root, factory) {
  const S = factory(root);
  if (typeof module === 'object' && module.exports) module.exports = S; else root.TessSymmetry = S;
})(typeof self !== 'undefined' ? self : globalThis, function (root) {
'use strict';
const node = typeof module === 'object' && module.exports;
const G = node ? require('./grid.js') : root.TessGrid, T = node ? require('./topo.js') : root.TessTopo;
const P = G.P, TOL = 1e-7, MAX_NODES = 3;
const addAt = (a, b) => [a[0] + b[0], a[1] + b[1]], sameAt = (a, b) => a[0] === b[0] && a[1] === b[1];

/* ---------------- isometries: [a, b, c, d, e, f] takes (x, y) to (a x + c y + e, b x + d y + f), as grid.js ---------------- */
const ISO = {
  translate: v => [1, 0, 0, 1, v.x, v.y],
  rotate: (c, deg) => { const t = deg * Math.PI / 180, k = Math.cos(t), s = Math.sin(t); return [k, s, -s, k, c.x - k * c.x + s * c.y, c.y - s * c.x - k * c.y]; },
  // the mirror line through p with direction d; slide ≠ 0 makes it a glide reflection (mirror, then that far along the line)
  mirror: (p, d, slide) => { const l = Math.hypot(d.x, d.y), ux = d.x / l, uy = d.y / l, a = 2 * ux * ux - 1, b = 2 * ux * uy, g = slide || 0;
    return [a, b, b, -a, p.x - a * p.x - b * p.y + g * ux, p.y - b * p.x + a * p.y + g * uy]; }
};
const flips = m => G.det(m) < 0;

/* ---------------- how one symmetry moves the vertices, edges and faces of a block ---------------- */
function locateVertex(g, p) {
  for (const u of g.vertices) { const uv = G.toLat(g.lattice, P(p.x - u.pos.x, p.y - u.pos.y)), at = [Math.round(uv[0]), Math.round(uv[1])], d = G.latVec(g.lattice, at);
    if (Math.hypot(u.pos.x + d.x - p.x, u.pos.y + d.y - p.y) < TOL) return { cls: u.id, at }; }
  return null;
}
// the edge instance an edge instance is carried onto: its class, its copy, and whether its direction is reversed
function edgeImage(g, e, at, m) {
  const [A, B] = G.edgeEnds(g, e, at), a = locateVertex(g, G.mapp(m, A)), b = locateVertex(g, G.mapp(m, B)); if (!a || !b) return null;
  for (const f of g.edges) {
    if (f.v0 === a.cls && f.v1 === b.cls && sameAt(addAt(a.at, f.shift), b.at)) return { edge: f.id, at: a.at, r: 0 };
    if (f.v0 === b.cls && f.v1 === a.cls && sameAt(addAt(b.at, f.shift), a.at)) return { edge: f.id, at: b.at, r: 1 };
  }
  return null;
}
// the edge instance that joins two junctions (world points), if there is one
function edgeBetween(g, A, B) {
  const a = locateVertex(g, A), b = locateVertex(g, B); if (!a || !b) return null;
  for (const f of g.edges) {
    if (f.v0 === a.cls && f.v1 === b.cls && sameAt(addAt(a.at, f.shift), b.at)) return { id: f.id, at: a.at, r: 0 };
    if (f.v0 === b.cls && f.v1 === a.cls && sameAt(addAt(b.at, f.shift), a.at)) return { id: f.id, at: b.at, r: 1 };
  }
  return null;
}
const faceCentre = (g, f, at) => { const V = G.faceCorners(g, f, at); return P(V.reduce((s, p) => s + p.x, 0) / V.length, V.reduce((s, p) => s + p.y, 0) / V.length); };
function faceImage(g, f, m) {
  const c = G.mapp(m, faceCentre(g, f, [0, 0]));
  for (const h of g.faces) { const c0 = faceCentre(g, h, [0, 0]), uv = G.toLat(g.lattice, P(c.x - c0.x, c.y - c0.y)), at = [Math.round(uv[0]), Math.round(uv[1])], d = G.latVec(g.lattice, at);
    if (Math.hypot(c0.x + d.x - c.x, c0.y + d.y - c.y) < TOL) return h.id; }
  return null;
}

/* ---------------- orbits and constraints ---------------- */
const KIND_TEXT = { free: 'free', straight: 'straight (on a mirror line)', mirror: 'symmetric about its middle', turn: 'point-symmetric about its middle' };
const cache = new Map();
function analyse(g, gens) {
  const key = JSON.stringify([g.lattice, g.vertices, g.edges.map(e => [e.id, e.v0, e.v1, e.shift]), g.faces.map(f => [f.id, f.sides]), gens]); let an = cache.get(key); if (an) return an;
  const errors = [], L = g.lattice;
  gens.forEach((m, k) => { // the symmetry must carry the repeat lattice onto itself
    [L.b1, L.b2].forEach(b => { const uv = G.toLat(L, P(m[0] * b.x + m[2] * b.y, m[1] * b.x + m[3] * b.y)); if (Math.abs(uv[0] - Math.round(uv[0])) > TOL || Math.abs(uv[1] - Math.round(uv[1])) > TOL) errors.push(`symmetry ${k} does not keep the repeat block`); });
    if (Math.abs(Math.abs(G.det(m)) - 1) > TOL) errors.push(`symmetry ${k} is not an isometry`); });
  const act = gens.map((m, k) => { const row = new Map(); g.edges.forEach(e => { const im = edgeImage(g, e, [0, 0], m); if (!im) errors.push(`symmetry ${k} does not carry edge ${e.id} onto an edge of the grid`); else row.set(e.id, { edge: im.edge, r: im.r, n: (flips(m) ? 1 : 0) ^ im.r }); }); return row; });
  const of = new Map(), orbits = [];
  if (!errors.length) g.edges.forEach(e0 => { if (of.has(e0.id)) return;
    const orb = { rep: e0.id, members: new Map([[e0.id, { r: 0, n: 0 }]]), stab: new Set() }, queue = [e0.id]; of.set(e0.id, orb);
    while (queue.length) { const id = queue.shift(), mu = orb.members.get(id);
      act.forEach(row => { const im = row.get(id), kappa = { r: mu.r ^ im.r, n: mu.n ^ im.n }, seen = orb.members.get(im.edge);
        if (!seen) { orb.members.set(im.edge, kappa); of.set(im.edge, orb); queue.push(im.edge); }
        else { const c = (seen.r ^ kappa.r ? 'r' : '') + (seen.n ^ kappa.n ? 'n' : ''); if (c) orb.stab.add(c); } }); }
    orb.kind = orb.stab.has('n') || orb.stab.size > 1 ? 'straight' : orb.stab.has('r') ? 'mirror' : orb.stab.has('rn') ? 'turn' : 'free';
    orbits.push(orb); });
  // the shapes: how many different kinds of tile the symmetries leave (1 = every tile is a copy of one tile)
  const fo = new Map(g.faces.map(f => [f.id, f.id])), root = id => { while (fo.get(id) !== id) id = fo.get(id); return id; };
  if (!errors.length) gens.forEach((m, k) => g.faces.forEach(f => { const im = faceImage(g, f, m); if (!im) errors.push(`symmetry ${k} does not carry face ${f.id} onto a face`); else { const a = root(f.id), b = root(im); if (a !== b) fo.set(a, b); } }));
  an = { ok: !errors.length, errors, orbits, of, act, tileKinds: new Set(g.faces.map(f => root(f.id))).size, tilesPerBlock: g.faces.length };
  cache.set(key, an); if (cache.size > 60) cache.delete(cache.keys().next().value); return an;
}
const mapNode = (mu, n) => ({ s: mu.r ? 1 - n.s : n.s, t: mu.n ? -n.t : n.t });
const mapNodes = (mu, nodes) => { const l = nodes.map(n => mapNode(mu, n)); return mu.r ? l.reverse() : l; };
// a boundary made to satisfy its constraint: its first half decides (a middle point of a symmetric boundary sits at s = ½)
function enforce(nodes, kind) {
  if (kind === 'free') return nodes.map(n => ({ s: n.s, t: n.t }));
  if (kind === 'straight') return [];
  const sorted = nodes.slice().sort((a, b) => a.s - b.s), left = sorted.filter(n => n.s < 0.5 - 1e-9), mid = kind === 'mirror' ? sorted.find(n => Math.abs(n.s - 0.5) <= 1e-9) : null, sg = kind === 'turn' ? -1 : 1;
  return left.map(n => ({ s: n.s, t: n.t })).concat(mid ? [{ s: 0.5, t: mid.t }] : [], left.slice().reverse().map(n => ({ s: 1 - n.s, t: sg * n.t })));
}
const sameNodes = (a, b, tol) => a.length === b.length && a.every((n, i) => Math.abs(n.s - b[i].s) <= (tol || 1e-9) && Math.abs(n.t - b[i].t) <= (tol || 1e-9));
// every boundary of every orbit from its representative. `asIs`: the representative is taken exactly as it stands (during a drag its
// points must not be put back in order: a point dragged through its own mirror image has to show as a crossing, and be stopped)
function derive(g, an, asIs) {
  const h = G.clone(g);
  an.orbits.forEach(orb => { const own = G.ecls(h, orb.rep).nodes, master = asIs ? own.map(n => ({ s: n.s, t: n.t })) : enforce(own, orb.kind); orb.members.forEach((mu, id) => { G.ecls(h, id).nodes = mapNodes(mu, master); }); });
  return h;
}
// does the drawn grid already obey the rule? (each boundary against the image of its representative, and each constraint)
function conforms(g, an) {
  const out = [];
  an.orbits.forEach(orb => { const rep = G.ecls(g, orb.rep).nodes; if (!sameNodes(rep, enforce(rep, orb.kind), 1e-9)) out.push({ edge: orb.rep, why: orb.kind });
    orb.members.forEach((mu, id) => { if (!sameNodes(G.ecls(g, id).nodes, mapNodes(mu, rep), 1e-9)) out.push({ edge: id, why: 'twin' }); }); });
  return out;
}

/* ---------------- the independent check: turn or reflect the drawing and look for every shape again ---------------- */
function invariant(g, gens, opts) {
  opts = opts || {};
  const n = opts.n || Math.max(4, G.patchSize(g) + 1), patch = G.buildPatch(g, { n }), L = g.lattice, key = p => Math.round(p.x * 1e5) + ',' + Math.round(p.y * 1e5), index = new Map();
  patch.faces.forEach(f => { const k = key(f.centroid), l = index.get(k); if (l) l.push(f); else index.set(k, [f]); });
  const mid = P((L.b1.x + L.b2.x) / 2, (L.b1.y + L.b2.y) / 2), reach = 1.6 * Math.max(Math.hypot(L.b1.x, L.b1.y), Math.hypot(L.b2.x, L.b2.y)), core = patch.faces.filter(f => Math.hypot(f.centroid.x - mid.x, f.centroid.y - mid.y) <= reach);
  const same = (pts, q) => { const m = q.length; if (pts.length !== m) return false; const i0 = q.findIndex(p => Math.hypot(p.x - pts[0].x, p.y - pts[0].y) < 1e-9); if (i0 < 0) return false;
    for (let k = 0; k < m; k++) { const p = q[(i0 + k) % m]; if (Math.hypot(p.x - pts[k].x, p.y - pts[k].y) > 1e-9) return false; } return true; };
  const bad = []; let tested = 0;
  gens.forEach((m, gi) => core.forEach(f => { tested++; let pts = f.outline.map(p => G.mapp(m, p)); if (flips(m)) pts = pts.reverse();          // a mirror image runs the other way round
    const c = G.centroid(pts); let found = false;
    for (let dx = -1; dx <= 1 && !found; dx++) for (let dy = -1; dy <= 1 && !found; dy++) { const l = index.get((Math.round(c.x * 1e5) + dx) + ',' + (Math.round(c.y * 1e5) + dy)); if (l && l.some(h => same(pts, h.outline))) found = true; }
    if (!found) bad.push({ symmetry: gi, face: f.key, at: f.centroid }); }));
  return { ok: !bad.length && tested > 0, tested, bad: bad.slice(0, 8) };
}

/* ---------------- editing under a rule (the rule is stored with the grid: g.repeat = { rule, gens, … }) ---------------- */
const ruleOf = g => g.repeat && g.repeat.gens && g.repeat.gens.length ? g.repeat : null;
function role(g, edgeId) {
  const R = ruleOf(g); if (!R) return { kind: 'free', twins: [] };
  const an = analyse(g, R.gens), orb = an.of.get(edgeId); return { kind: orb.kind, rep: orb.rep, twins: [...orb.members.keys()].filter(id => id !== edgeId), map: orb.members.get(edgeId) };
}
// a boundary's point in its representative's frame; and which point of the representative it is
function toRep(orb, edgeId, n, index, rel) { const mu = orb.members.get(edgeId); return { mu, index: mu.r ? n - 1 - index : index, rel: rel ? mapNode(mu, rel) : null }; }
const withRep = (g, an, orb, nodes) => { const h = G.clone(g); G.ecls(h, orb.rep).nodes = nodes; return derive(h, an, true); };
function moveRep(nodes, kind, i, rel) {
  const l = nodes.map(n => ({ s: n.s, t: n.t })), n = l.length, j = n - 1 - i;
  if (kind === 'free') { l[i] = { s: rel.s, t: rel.t }; return l; }
  if (kind === 'straight') return l;
  const sg = kind === 'turn' ? -1 : 1;
  if (i === j) { l[i] = { s: 0.5, t: kind === 'turn' ? 0 : rel.t }; return l; }
  l[i] = { s: rel.s, t: rel.t }; l[j] = { s: 1 - rel.s, t: sg * rel.t }; return l;
}
// the guarded drag of grid.js (dragNode), with the twins following: an invalid position is never returned
function move(g, edgeId, index, at, point) {
  const R = ruleOf(g), an = analyse(g, R.gens), orb = an.of.get(edgeId), rep = G.ecls(g, orb.rep).nodes, q = toRep(orb, edgeId, rep.length, index, G.relOnEdge(g, edgeId, at, point));
  if (orb.kind === 'straight' || !rep[q.index]) return { grid: g, blocked: true };
  const cur = rep[q.index], cand = m => withRep(g, an, orb, moveRep(rep, orb.kind, q.index, { s: cur.s + (q.rel.s - cur.s) * m, t: cur.t + (q.rel.t - cur.t) * m }));
  const want = cand(1); if (!G.problem(want)) return { grid: want, blocked: false };
  let lo = 0, hi = 1; for (let i = 0; i < 10; i++) { const m = (lo + hi) / 2; G.problem(cand(m)) ? hi = m : lo = m; }
  return { grid: lo > 0 ? cand(lo) : g, blocked: true };
}
function insert(g, edgeId, at, point, verify) {
  const R = ruleOf(g), an = analyse(g, R.gens), orb = an.of.get(edgeId), rep = G.ecls(g, orb.rep).nodes, mu = orb.members.get(edgeId), rel = mapNode(mu, G.relOnEdge(g, edgeId, at, point));
  if (orb.kind === 'straight') return { ok: false, locked: true, message: 'This edge lies on a mirror line, so it has to stay straight.' };
  let nodes = null, pick = null;
  const room = (list, s) => { let k = list.findIndex(n => n.s > s); if (k < 0) k = list.length; const lo = k ? list[k - 1].s : 0, hi = k < list.length ? list[k].s : 1; return hi - lo < 0.12 ? null : { k, s: Math.max(lo + 0.06, Math.min(hi - 0.06, s)) }; };
  if (orb.kind === 'free') { if (rep.length >= MAX_NODES) return { ok: false, message: 'This edge already has three added points.' };
    const r = room(rep, rel.s); if (!r) return { ok: false, message: 'There is not enough room between these points.' };
    nodes = rep.slice(); nodes.splice(r.k, 0, { s: r.s, t: rel.t }); pick = r.k; }
  else { const sg = orb.kind === 'turn' ? -1 : 1, hasMid = rep.length % 2 === 1, left = rep.slice(0, Math.floor(rep.length / 2));
    if (orb.kind === 'mirror' && Math.abs(rel.s - 0.5) < 0.09) {      // a point on the mirror line itself: one point, at the middle
      if (hasMid || rep.length + 1 > MAX_NODES) return { ok: false, message: hasMid ? 'This edge already has a point on the mirror line.' : 'This edge already has three added points.' };
      if (left.length && 0.5 - left[left.length - 1].s < 0.12) return { ok: false, message: 'There is not enough room between these points.' };
      nodes = enforce(left.concat([{ s: 0.5, t: rel.t }]), 'mirror'); pick = left.length; }
    else { if (rep.length + 2 > MAX_NODES) return { ok: false, message: 'Points on this edge come in pairs (one on each side of its middle), and there is room for three points only.' };
      const right = rel.s > 0.5, s0 = right ? 1 - rel.s : rel.s, t0 = right ? sg * rel.t : rel.t, half = left.concat([{ s: 0.5, t: 0 }]), r = room(half, s0);
      if (!r || r.s > 0.44) return { ok: false, message: 'There is not enough room between these points.' };
      const l2 = left.slice(); l2.splice(r.k, 0, { s: r.s, t: t0 }); nodes = enforce(l2.concat(hasMid ? [rep[left.length]] : []), orb.kind); pick = right ? nodes.length - 1 - r.k : r.k; } }
  const cand = withRep(g, an, orb, nodes), why = G.problem(cand);
  if (why) return { ok: false, message: 'A point here would make the boundary invalid (' + why + ').' };
  if (verify) { const full = verify(cand); if (!full.ok) return { ok: false, message: 'A point here would break the tiling (' + full.failing.join(', ') + ').' }; }
  return { ok: true, grid: cand, index: mu.r ? nodes.length - 1 - pick : pick, added: orb.kind === 'free' || nodes.length - rep.length === 1 ? 1 : 2 };
}
function remove(g, edgeId, index, verify) {
  const R = ruleOf(g), an = analyse(g, R.gens), orb = an.of.get(edgeId), rep = G.ecls(g, orb.rep).nodes, q = toRep(orb, edgeId, rep.length, index);
  if (!rep[q.index]) return { ok: false, message: 'That point is no longer on this edge.' };
  const j = rep.length - 1 - q.index, nodes = rep.filter((n, k) => k !== q.index && !(orb.kind !== 'free' && k === j)), cand = withRep(g, an, orb, nodes), why = G.problem(cand);
  if (why) return { ok: false, message: 'Straightening this edge would make an invalid shape (' + why + ').' };
  if (verify) { const full = verify(cand); if (!full.ok) return { ok: false, message: 'Straightening this edge would break the tiling (' + full.failing.join(', ') + ').' }; }
  return { ok: true, grid: cand, removed: rep.length - nodes.length };
}

/* ---------------- REFLECTION ON THE SQUARE GRID: from two chosen edges to the mirror line and its consequences ---------------- */
const MIRRORS = {
  diagonal: { name: 'diagonal mirror', block: [[1, 0], [0, 1]] },
  midline: { name: 'mirror through the middle of the squares', block: null },
  side: { name: 'mirror on the grid lines', block: null }
};
const isUnitSquare = g => g.kind === 'square' && g.vertices.length === 1 && g.edges.length === 2 && Math.abs(g.lattice.b1.x - 1) < TOL && Math.abs(g.lattice.b1.y) < TOL && Math.abs(g.lattice.b2.x) < TOL && Math.abs(g.lattice.b2.y - 1) < TOL;
// the orientation-reversing isometry that takes p → p2 and q → q2: a mirror line, or a mirror with a slide (a glide reflection)
function reversing(p, q, p2, q2) {
  const a1 = Math.atan2(q.y - p.y, q.x - p.x), a2 = Math.atan2(q2.y - p2.y, q2.x - p2.x), th = (a1 + a2) / 2, d = P(Math.cos(th), Math.sin(th)), m0 = ISO.mirror(P(0, 0), d), ip = G.mapp(m0, p), tr = P(p2.x - ip.x, p2.y - ip.y);
  const slide = tr.x * d.x + tr.y * d.y, off = P(tr.x - slide * d.x, tr.y - slide * d.y);
  return { d, p: P(off.x / 2, off.y / 2), slide };          // the line through `p` along `d`; slide ≠ 0: not a mirror
}
// E1, E2: { id, at } edge instances of the unit square grid. Returns the proposal (ok, the new grid, what each edge becomes, the text),
// or ok: false with the reason. Nothing is changed.
function mirrorPairing(g, E1, E2) {
  const fail = (kind, message, extra) => Object.assign({ ok: false, kind, message }, extra || {});
  if (!isUnitSquare(g) || ruleOf(g)) return fail('block', 'A mirror can be chosen on the square grid while it repeats by translation with a block of one square.');
  if (E1.id === E2.id && sameAt(E1.at, E2.at)) return fail('same', 'Choose two different edges.');
  const [p, q] = G.edgeEnds(g, G.ecls(g, E1.id), E1.at), [p2, q2] = G.edgeEnds(g, G.ecls(g, E2.id), E2.at);
  const cands = [reversing(p, q, p2, q2), reversing(p, q, q2, p2)], m = cands.find(c => Math.abs(c.slide) < TOL);
  if (!m) return fail('none', 'No mirror line carries one of these edges onto the other: they are related by a slide, or by a mirror together with a slide (a glide reflection). Choose two edges that meet at a corner, two opposite sides of one square, or two sides that continue each other.');
  const diag = Math.abs(Math.abs(m.d.x) - Math.abs(m.d.y)) < TOL, vertical = Math.abs(m.d.x) < TOL, c = vertical ? m.p.x : m.p.y, half = Math.abs(c - Math.round(c)) > 0.25;
  const type = diag ? 'diagonal' : half ? 'midline' : 'side', M = diag ? [[1, 0], [0, 1]] : vertical ? [[2, 0], [0, 1]] : [[1, 0], [0, 2]];
  // the block the rule needs (one square for a diagonal, two squares side by side across the mirror otherwise), with today's boundaries
  let h = diag ? G.clone(g) : T.supercell(g, M, 'square'); h.kind = 'square'; h.limits = Object.assign({}, g.limits);
  const gen = ISO.mirror(m.p, m.d), an = analyse(h, [gen]); if (!an.ok) return fail('none', 'That line is not a mirror line of the square grid.', { errors: an.errors });
  // the two chosen edges in the new block
  const cls = E => { if (diag) return E.id; const [a, b] = G.edgeEnds(g, G.ecls(g, E.id), E.at), u = locateVertex(h, a), w = locateVertex(h, b), e = h.edges.find(f => (f.v0 === u.cls && f.v1 === w.cls && sameAt(addAt(u.at, f.shift), w.at))); return e.id; };
  const c1 = cls(E1), c2 = cls(E2), orb = an.of.get(c1);
  const axis = { p: m.p, d: m.d, type, family: diag ? (m.d.x * m.d.y > 0 ? 'diagonal-up' : 'diagonal-down') : vertical ? 'vertical' : 'horizontal', offset: diag ? 0 : half ? 0.5 : 0 };
  if (orb.kind === 'straight') return fail('straight', 'These two edges are mirror images across the grid line between them, but with the smallest repeat every grid line in that direction is a mirror, including the lines these two edges lie on. They would both have to stay straight, so there would be nothing to push or pull.', { axis });
  if (c1 === c2 || orb.kind !== 'free') return fail('copy', 'These two edges are copies of one boundary in the smallest repeat with this mirror: the mirror crosses each of them at its middle. Choose two opposite sides of one square instead.', { axis });
  if (an.of.get(c2) !== orb) return fail('none', 'That mirror does not carry the first edge onto the second.', { axis });
  // today's geometry against the rule: the first edge chosen keeps its shape; an edge that would have to change must be straight now
  const conflicts = [], nodesOf = id => G.ecls(h, id).nodes;
  // (one edge leads each orbit: its shape is kept and the others become its images. Of the two chosen edges it is the first, unless only
  //  the second has added points)
  let leadChosen = c1;
  an.orbits.forEach(o => { const lead = o === orb ? (leadChosen = nodesOf(c1).length || !nodesOf(c2).length ? c1 : c2) : ([...o.members.keys()].find(id => nodesOf(id).length) || o.rep), mu0 = o.members.get(lead), master = mapNodes(mu0, nodesOf(lead));   // the representative as the lead sees it
    if (o.kind === 'straight') { if ([...o.members.keys()].some(id => nodesOf(id).length)) conflicts.push({ edges: [...o.members.keys()], why: 'straight' }); return; }
    if (!sameNodes(master, enforce(master, o.kind), 1e-9)) { conflicts.push({ edges: [...o.members.keys()], why: o.kind }); return; }
    o.members.forEach((mu, id) => { const want = mapNodes(mu, master), have = nodesOf(id); if (have.length && !sameNodes(have, want, 1e-9) && !(diag ? false : sameNodes(have, nodesOf(lead), 1e-12))) conflicts.push({ edges: [lead, id], why: 'twin' }); });
    G.ecls(h, o.rep).nodes = master; });
  if (conflicts.length) { const c0 = conflicts[0], n = c0.edges.reduce((s, id) => s + nodesOf(id).length, 0);
    return fail('geometry', c0.why === 'straight' ? `The sides on this mirror line have to stay straight, but they have ${n === 1 ? 'an added point' : 'added points'}. Remove ${n === 1 ? 'it' : 'them'} first.`
      : c0.why === 'mirror' ? 'This mirror crosses a side that has added points, and they are not symmetric about its middle. Remove them first.'
      : 'Both of these sides already have added points, and they are not mirror images of each other. Remove the points of one of them first.', { axis, conflicts }); }
  const out = derive(h, an); out.repeat = { rule: 'reflection', type, family: axis.family, offset: axis.offset, gens: [gen], axis: { p: { x: m.p.x, y: m.p.y }, d: { x: m.d.x, y: m.d.y } }, lead: leadChosen };   // lead: the twin whose shape was kept (drawn amber)
  const roles = {}; an.orbits.forEach(o => o.members.forEach((mu, id) => { roles[id] = { kind: o.kind, rep: o.rep, twins: [...o.members.keys()].filter(x => x !== id) }; }));
  const why = G.problem(out); if (why) return fail('geometry', 'With this mirror the boundaries would make an invalid shape (' + why + ').', { axis });
  return { ok: true, type, axis, grid: out, roles, chosen: [c1, c2], lead: leadChosen, tileKinds: an.tileKinds, tilesPerBlock: an.tilesPerBlock, text: describeMirror(type, axis, an) };
}
function describeMirror(type, axis, an) {
  const v = axis.family === 'vertical', pair = v ? 'left and right' : 'top and bottom', crossed = v ? 'top and bottom' : 'left and right';
  if (type === 'diagonal') return 'Diagonal mirror through this corner. The two sides that meet on it are mirror twins, in every square. One tile shape; the repeat block stays one square.';
  if (type === 'midline') return `Mirror through the middle of the square. Its ${pair} sides are mirror twins. The ${crossed} sides are crossed by the mirror, so their points come in mirrored pairs. Two shapes alternate; the repeat block becomes two squares.`;
  return 'Mirror on the grid line between these two squares, and on every line parallel to it. Neighbouring squares are mirror images. Sides on a mirror line stay straight; the other sides are twins. The repeat block becomes two squares.';
}
// stop mirroring: the drawing stays; a two-square block becomes one square again if both squares are the same
function toTranslation(g) {
  const h = G.clone(g); delete h.repeat;
  if (h.kind === 'square' && h.edges.length === 4 && h.vertices.length === 2) { const horiz = Math.abs(h.lattice.b1.x - 2) < TOL, byDir = d => h.edges.filter(e => { const [a, b] = G.edgeEnds(h, e, [0, 0]); return d === 'h' ? Math.abs(a.y - b.y) < TOL : Math.abs(a.x - b.x) < TOL; });
    const hs = byDir('h'), vs = byDir('v'); if (hs.length === 2 && vs.length === 2 && sameNodes(hs[0].nodes, hs[1].nodes, 1e-12) && sameNodes(vs[0].nodes, vs[1].nodes, 1e-12)) { const b = G.squareGrid(); b.kind = 'square'; b.limits = Object.assign({}, g.limits); G.ecls(b, 'a').nodes = hs[0].nodes.map(n => ({ s: n.s, t: n.t })); G.ecls(b, 'b').nodes = vs[0].nodes.map(n => ({ s: n.s, t: n.t })); return b; } }
  return h;
}

return { ISO, MAX_NODES, KIND_TEXT, MIRRORS, analyse, derive, conforms, enforce, mapNode, mapNodes, sameNodes, invariant, ruleOf, role, move, insert, remove, edgeImage, edgeBetween, locateVertex,
  mirrorPairing, describeMirror, toTranslation, isUnitSquare, reversing };
});
