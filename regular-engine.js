/* Regular Grid Boundary Explorer (v6.7), with REFLECTION ON THE SQUARE GRID (v6.8).
 * One edge class is one geometric boundary shared by its two faces. All edits repeat by the lattice translations. A grid may also carry
 * a repeat rule (g.repeat, set by symmetry.js mirrorPairing): then some edges are mirror twins, some must stay straight, some must be
 * symmetric, and every edit goes through symmetry.js so that the twins follow. Without a rule nothing here differs from v6.7.
 */
(function (root, factory) {
  const R = factory(root);
  if (typeof module === 'object' && module.exports) module.exports = R; else root.TessRegular = R;
})(typeof self !== 'undefined' ? self : globalThis, function (root) {
'use strict';
const G = typeof module === 'object' && module.exports ? require('./grid.js') : root.TessGrid;
const T = typeof module === 'object' && module.exports ? require('./topo.js') : root.TessTopo;
const Sym = typeof module === 'object' && module.exports ? require('./symmetry.js') : root.TessSymmetry;
const P = G.P, S = Math.sqrt(3) / 2;
const TYPES = { square: 'Square', triangle: 'Equilateral triangle', hexagon: 'Regular hexagon' };
function base(type) {
  let g;
  if (type === 'square') g = G.squareGrid();
  else if (type === 'triangle') g = T.triangleGrid();
  else if (type === 'hexagon') g = T.makeGrid({
    lattice: { b1: P(1.5, S), b2: P(0, 2 * S) },
    vertices: [{ id: 'A', pos: P(1, 0) }, { id: 'B', pos: P(0.5, S) }],
    edges: [{ id: 'u', v0: 'A', v1: 'B', shift: [0, 0] },
      { id: 'v', v0: 'A', v1: 'B', shift: [1, -1] },
      { id: 'w', v0: 'A', v1: 'B', shift: [0, -1] }]
  }, 'hexagon');
  else throw new Error('Unknown grid ' + type);
  g.kind = type;
  g.limits = Object.assign({}, g.limits || G.LIMITS, { maxSides: 1e9, domain: null });
  return g;
}
function quick(g) { return G.problem(g); }
// The full check before anything is kept: grid.js's validator (a tiling: no gaps, overlaps or crossings, shared edges, periodic copies)
// and, under a repeat rule, two checks of the rule itself: every boundary is the stated image of its twin (edge correspondence), and the
// drawing reflected in its mirror line is the same drawing (found shape by shape, without using the correspondence).
function verify(g, samples) {
  const p = G.buildPatch(g, { n: Math.max(3, G.patchSize(g) - 1) });
  const r = G.validate(p, { samples: samples || 500 }), failing = r.rows.filter(x => !x.ok).map(x => x.name), rule = Sym.ruleOf(g);
  let symmetry = null;
  if (rule) { const an = Sym.analyse(g, rule.gens), conf = an.ok ? Sym.conforms(g, an) : [{ why: 'rule' }], inv = an.ok ? Sym.invariant(g, rule.gens) : { ok: false };
    symmetry = { ok: an.ok && !conf.length && inv.ok, correspondence: conf, invariant: inv };
    if (conf.length) failing.push('edge correspondence'); if (!inv.ok) failing.push('mirror symmetry'); }
  return { ok: r.ok && (!symmetry || symmetry.ok), failing, report: r, symmetry };
}
function count(g) { return g.edges.reduce((n, e) => n + e.nodes.length, 0); }
function insert(g, id, at, point) {
  if (Sym.ruleOf(g)) return Sym.insert(g, id, at, point, x => verify(x, 300));
  const e = G.ecls(g, id);
  if (!e) return { ok: false, message: 'Choose an edge.' };
  if (e.nodes.length >= 3) return { ok: false, message: 'This edge already has three added points.' };
  const rel = G.relOnEdge(g, id, at, point), l = e.nodes;
  let index = l.findIndex(n => n.s > rel.s); if (index < 0) index = l.length;
  const lo = index ? l[index - 1].s : 0, hi = index < l.length ? l[index].s : 1;
  if (hi - lo < 0.12) return { ok: false, message: 'There is not enough room between these points.' };
  const n = { s: Math.max(lo + 0.06, Math.min(hi - 0.06, rel.s)), t: rel.t };
  const candidate = G.insertNode(g, id, index, n);
  const why = quick(candidate);
  if (why) return { ok: false, message: 'A point here would make the boundary invalid (' + why + ').' };
  const full = verify(candidate, 300);
  if (!full.ok) return { ok: false, message: 'A point here would break the tiling (' + full.failing.join(', ') + ').' };
  return { ok: true, grid: candidate, index };
}
function remove(g, id, index) {
  if (Sym.ruleOf(g)) return Sym.remove(g, id, index, x => verify(x, 300));
  const e = G.ecls(g, id);
  if (!e || index < 0 || index >= e.nodes.length) return { ok: false, message: 'That point is no longer on this edge.' };
  const candidate = G.removeNode(g, id, index), why = quick(candidate);
  if (why) return { ok: false, message: 'Straightening this edge would make an invalid shape (' + why + ').' };
  const full = verify(candidate, 300);
  if (!full.ok) return { ok: false, message: 'Straightening this edge would break the tiling (' + full.failing.join(', ') + ').' };
  return { ok: true, grid: candidate };
}
function move(g, id, index, at, point) {
  if (Sym.ruleOf(g)) return Sym.move(g, id, index, at, point);
  const rel = G.relOnEdge(g, id, at, point);
  const r = G.dragNode(g, id, index, rel);
  return { grid: r.grid, blocked: r.blocked };
}
// the name of a grid's repeat rule, for people
function ruleName(g) {
  const r = Sym.ruleOf(g), tiles = g.faces.length, sq = g.kind === 'square' ? (tiles === 1 ? '' : ` · block of ${tiles} squares`) : '';
  if (!r) return 'translation repeat' + sq;
  return 'reflection · ' + (r.type === 'diagonal' ? 'mirror on a diagonal' : r.type === 'midline' ? 'mirror through the middle of the squares' : 'mirror on the grid lines') + sq;
}
return { TYPES, base, quick, verify, count, insert, remove, move, ruleName, Sym };
});
