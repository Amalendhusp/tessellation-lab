/* v6.8 · Regular grid boundaries, with REFLECTION ON THE SQUARE GRID. Structural tools remain in explorer.html.
 *   - As in v6.7: choose a square, triangle or hexagon grid; tap a line to add a point, drag it to push or pull, tap it to remove it;
 *     two fingers zoom and pan; Undo / Redo; Repeat outlines the repeat block. The default rule is translation repeat.
 *   - Rule › Reflection (square grid): tap two edges that should be mirror images of each other. The page works out the one mirror line
 *     of the square grid that carries the first onto the second (symmetry.js mirrorPairing) and shows what it would mean before anything
 *     is changed: the mirror lines, the twin edges, the edges that would have to stay straight or be symmetric, and the repeat block.
 *     “Use this mirror” keeps it — only if the full checks pass — and “Cancel” leaves the grid as it was. Pairs that no mirror line
 *     relates, or that the present boundaries rule out, are refused with the reason.
 *   - Under a mirror rule, pushing or pulling an edge moves its mirror twin in the same frame, on every copy. Edges on a mirror line
 *     cannot take points. Undo / Redo cover choosing the mirror and every edit after it. */
(() => {
'use strict';
const G = window.TessGrid, C = window.TessClassify, R = window.TessRegular, S = window.TessSymmetry, P = G.P;
const $ = id => document.getElementById(id), cv = $('cv'), ctx = cv.getContext('2d');
const X = { history: [R.base('square')], index: 0, view: { x: 0.5, y: 0.5, s: 54 }, block: false, hit: { nodes: [], edges: [] }, down: null, drag: null, fingers: new Map(), pinch: null, pair: null, lastDrag: null, lastPair: null };
const cur = () => X.history[X.index];
const shown = () => X.drag ? X.drag.grid : X.pair ? (X.pair.proposal && X.pair.proposal.ok ? X.pair.proposal.grid : X.pair.base) : cur();
const screen = p => P(cv.clientWidth / 2 + (p.x - X.view.x) * X.view.s, cv.clientHeight / 2 - (p.y - X.view.y) * X.view.s);
const world = (x, y) => P(X.view.x + (x - cv.clientWidth / 2) / X.view.s, X.view.y - (y - cv.clientHeight / 2) / X.view.s);
const add = (a, b) => P(a.x + b.x, a.y + b.y);
const COL = { twinA: '#e8860c', twinB: '#0f9f8f', sym: '#7b5cd6', lock: '#7c8794', mirror: '#c2378a', bad: '#e34444' };
function fit() { const d = Math.min(devicePixelRatio || 1, 3); cv.width = Math.round(innerWidth * d); cv.height = Math.round(innerHeight * d); ctx.setTransform(d, 0, 0, d, 0, 0); draw(); }
function range(g) {
  const pts = [world(0, 0), world(cv.clientWidth, 0), world(0, cv.clientHeight), world(cv.clientWidth, cv.clientHeight)].map(p => G.toLat(g.lattice, p));
  return { i0: Math.floor(Math.min(...pts.map(p => p[0]))) - 3, i1: Math.ceil(Math.max(...pts.map(p => p[0]))) + 3,
    j0: Math.floor(Math.min(...pts.map(p => p[1]))) - 3, j1: Math.ceil(Math.max(...pts.map(p => p[1]))) + 3 };
}
function path(pts) { if (!pts.length) return; const a = screen(pts[0]); ctx.beginPath(); ctx.moveTo(a.x, a.y); for (let k = 1; k < pts.length; k++) { const b = screen(pts[k]); ctx.lineTo(b.x, b.y); } ctx.closePath(); }
const line = (a, b) => { ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke(); };
// what each edge class of a grid is under its rule: a twin (and which of the pair), symmetric, or locked on a mirror line
function rolesOf(g) {
  const rule = S.ruleOf(g), m = new Map(); if (!rule) return m; const an = S.analyse(g, rule.gens);
  an.orbits.forEach(o => { const lead = o.members.has(rule.lead) ? rule.lead : o.rep;        // amber: the twin whose shape was kept when the mirror was chosen
    o.members.forEach((mu, id) => m.set(id, { kind: o.kind, lead: id === lead, twin: o.members.size > 1 })); });
  return m;
}
// every mirror line of the rule that crosses the screen
function mirrorLines(rule) {
  const c = [world(0, 0), world(cv.clientWidth, 0), world(0, cv.clientHeight), world(cv.clientWidth, cv.clientHeight)], xs = c.map(p => p.x), ys = c.map(p => p.y), x0 = Math.min(...xs), x1 = Math.max(...xs), y0 = Math.min(...ys), y1 = Math.max(...ys), out = [], o = rule.offset || 0;
  if (rule.family === 'vertical') for (let k = Math.floor(x0) - 1; k <= Math.ceil(x1); k++) out.push([P(k + o, y0), P(k + o, y1)]);
  else if (rule.family === 'horizontal') for (let k = Math.floor(y0) - 1; k <= Math.ceil(y1); k++) out.push([P(x0, k + o), P(x1, k + o)]);
  else if (rule.family === 'diagonal-up') for (let k = Math.floor(y0 - x1) - 1; k <= Math.ceil(y1 - x0); k++) out.push([P(x0, x0 + k), P(x1, x1 + k)]);
  else for (let k = Math.floor(x0 + y0) - 1; k <= Math.ceil(x1 + y1); k++) out.push([P(x0, k - x0), P(x1, k - x1)]);
  return out;
}
function draw() {
  const g = shown(), d = Math.min(devicePixelRatio || 1, 3); ctx.setTransform(d, 0, 0, d, 0, 0); const W = cv.clientWidth, H = cv.clientHeight;
  ctx.clearRect(0, 0, W, H); ctx.fillStyle = '#f7f3e9'; ctx.fillRect(0, 0, W, H);
  const r = range(g), hits = { nodes: [], edges: [] }; X.hit = hits;
  const base = { square: ['#d7ebe4', '#c5dfee'], triangle: ['#f8e7b9', '#f3dca1'], hexagon: ['#dbe5f4'] }[g.kind];
  for (let i = r.i0; i <= r.i1; i++) for (let j = r.j0; j <= r.j1; j++) for (let f = 0; f < g.faces.length; f++) {
    const pts = G.faceOutline(g, g.faces[f], [i, j]).pts, scr = pts.map(screen);
    if (!scr.some(p => p.x > -130 && p.x < W + 130 && p.y > -130 && p.y < H + 130)) continue;
    path(pts); ctx.fillStyle = base[f % base.length]; ctx.fill(); ctx.lineWidth = 2.15; ctx.strokeStyle = '#292724'; ctx.stroke();
  }
  const rule = S.ruleOf(g), preview = !!(X.pair && X.pair.proposal && X.pair.proposal.ok), roles = rule ? rolesOf(g) : null, showRoles = roles && (preview || X.block), marks = [];
  for (let i = r.i0; i <= r.i1; i++) for (let j = r.j0; j <= r.j1; j++) for (const e of g.edges) {
    const pl = G.edgeLine(g, e, [i, j]).map(screen);
    if (!pl.some(p => p.x > -40 && p.x < W + 40 && p.y > -40 && p.y < H + 40)) continue;
    for (let k = 0; k < pl.length - 1; k++) hits.edges.push({ id: e.id, at: [i, j], a: pl[k], b: pl[k + 1] });
    if (showRoles) marks.push({ role: roles.get(e.id), pl });
    for (let k = 0; k < e.nodes.length; k++) hits.nodes.push({ id: e.id, index: k, at: [i, j], x: pl[k + 1].x, y: pl[k + 1].y });
  }
  // the rule made visible: twin edges in two colours (one of each pair amber, its mirror image teal), symmetric edges violet, edges
  // that must stay straight grey
  if (showRoles) { ctx.save(); ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    marks.forEach(({ role, pl }) => { ctx.setLineDash(role.kind === 'mirror' ? [5, 4] : []); ctx.lineWidth = role.kind === 'straight' ? 5 : 4.2;
      ctx.strokeStyle = role.kind === 'straight' ? COL.lock : role.kind === 'mirror' ? COL.sym : role.lead ? COL.twinA : COL.twinB;
      ctx.beginPath(); pl.forEach((p, k) => k ? ctx.lineTo(p.x, p.y) : ctx.moveTo(p.x, p.y)); ctx.stroke(); }); ctx.restore(); }
  if (rule) { ctx.save(); ctx.setLineDash([9, 6]); ctx.strokeStyle = COL.mirror; ctx.lineWidth = preview ? 2.6 : 1.5; ctx.globalAlpha = preview || X.block ? 1 : 0.75; mirrorLines(rule).forEach(([a, b]) => line(screen(a), screen(b))); ctx.restore(); }
  hits.nodes.forEach(q => { ctx.fillStyle = '#19bba4'; ctx.strokeStyle = '#183733'; ctx.lineWidth = 1.8; ctx.fillRect(q.x - 5.5, q.y - 5.5, 11, 11); ctx.strokeRect(q.x - 5.5, q.y - 5.5, 11, 11); });
  if (X.block || preview) {
    const L = g.lattice, v = [P(0, 0), L.b1, add(L.b1, L.b2), L.b2].map(screen);
    ctx.save(); ctx.beginPath(); ctx.moveTo(v[0].x, v[0].y); for (let k = 1; k < 4; k++) ctx.lineTo(v[k].x, v[k].y); ctx.closePath(); ctx.setLineDash([7, 5]); ctx.strokeStyle = '#d07627'; ctx.lineWidth = 3; ctx.stroke(); ctx.restore();
  }
  // choosing a mirror: the first edge, the edges that can be its mirror image, and a refused second edge
  if (X.pair) { const A = X.pair, seg = (E, colour, w, dash) => { const e = S.edgeBetween(g, ...ends(E)); if (!e) return; const pl = G.edgeLine(g, G.ecls(g, e.id), e.at).map(screen);
      ctx.save(); ctx.setLineDash(dash || []); ctx.lineCap = 'round'; ctx.lineJoin = 'round'; ctx.strokeStyle = colour; ctx.lineWidth = w; ctx.beginPath(); pl.forEach((p, k) => k ? ctx.lineTo(p.x, p.y) : ctx.moveTo(p.x, p.y)); ctx.stroke(); ctx.restore(); };
    if (!preview) { if (A.a && !A.b) A.options.forEach(E => seg(E, COL.twinB, 5, [3, 7])); if (A.a) seg(A.a, COL.twinA, 7); if (A.b) seg(A.b, COL.bad, 7, [6, 6]); }
    else { [A.a, A.b].forEach(E => { const [p, q] = ends(E).map(screen); ctx.save(); ctx.fillStyle = '#fff'; ctx.strokeStyle = '#292724'; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc((p.x + q.x) / 2, (p.y + q.y) / 2, 7, 0, 2 * Math.PI); ctx.fill(); ctx.stroke(); ctx.restore(); }); } }
  if (X.drag) { const q = hits.nodes.find(h => h.id === X.drag.id && h.index === X.drag.index && h.at[0] === X.drag.at[0] && h.at[1] === X.drag.at[1]); if (q) { ctx.beginPath(); ctx.arc(q.x, q.y, 10, 0, 2 * Math.PI); ctx.strokeStyle = X.drag.blocked ? '#e34444' : '#e89418'; ctx.lineWidth = 3; ctx.stroke(); } }
}
function toast(s, bad, ms) { const t = $('toast'); t.textContent = s; t.classList.toggle('bad', !!bad); t.style.display = 'block'; clearTimeout(toast.timer); toast.timer = setTimeout(() => t.style.display = 'none', ms || (bad ? 4000 : 2200)); }
function hidePop() { $('pop').hidden = true; }
function pop(x, y, title, message, buttons) {
  const p = $('pop'); p.innerHTML = ''; const strong = document.createElement('strong'); strong.textContent = title; p.appendChild(strong);
  if (message) { const q = document.createElement('p'); q.textContent = message; p.appendChild(q); }
  buttons.forEach(b => { const q = document.createElement('button'); q.textContent = b.text; q.onclick = () => { hidePop(); b.fn(); }; p.appendChild(q); });
  p.hidden = false; p.style.left = Math.max(10, Math.min(x - 130, innerWidth - p.offsetWidth - 10)) + 'px';
  p.style.top = Math.min(Math.max(80, y - p.offsetHeight - 25), innerHeight - p.offsetHeight - 12) + 'px';
}
function commit(g, message) { X.history = X.history.slice(0, X.index + 1); X.history.push(g); X.index++; sync(); draw(); if (message) toast(message); }
const RULE_NOTE = { diagonal: 'Mirror lines run along one diagonal of every square. The two sides that meet on a mirror line are mirror twins.',
  midline: 'Mirror lines run through the middle of every square. Opposite sides are mirror twins; the sides the mirror crosses are symmetric about it. Two shapes alternate.',
  side: 'Mirror lines lie on the grid lines of one direction. Neighbouring squares are mirror images; the sides on the mirror lines stay straight.' };
function sync() {
  const g = cur(), cl = C.classify(g), rule = S.ruleOf(g); $('name').textContent = R.TYPES[g.kind] + ' grid'; $('shape').textContent = cl.name + ' · ' + R.count(g) + ' boundary point' + (R.count(g) === 1 ? '' : 's');
  $('rule').textContent = 'Rule: ' + R.ruleName(g); $('undo').disabled = X.index === 0; $('redo').disabled = X.index >= X.history.length - 1;
  $('block').setAttribute('aria-pressed', String(X.block)); $('block').textContent = X.block ? 'Hide block' : 'Repeat'; $('rules').setAttribute('aria-pressed', String(!!X.pair));
  $('info-body').innerHTML = '<div class="kv">Starting grid: <b>' + R.TYPES[g.kind] + '</b></div><div class="kv">Current polygons: <b>' + cl.name + '</b></div>' +
    '<div class="kv">Tessellation: <b>valid</b></div><div class="kv">Repeat rule: <b>' + R.ruleName(g) + '</b></div><p>Your boundary edits are shared by neighbouring polygons and repeat across the grid.' + (rule ? ' ' + RULE_NOTE[rule.type] : '') + '</p>';
  $('details-body').innerHTML = '<div class="kv">Topology: <b>' + cl.arrangementText + '</b></div>' +
    '<div class="kv">Geometry: <b>' + cl.geometry.shapes.map(s => s.name).join(' · ') + '</b></div>' +
    '<div class="kv">Regularity: <b>' + cl.regularity.verdict + '</b></div>' +
    '<div class="kv">Repeat rule: <b>' + R.ruleName(g) + '</b></div>' +
    (rule ? '<div class="kv">Mirror symmetry: <b>checked</b> — the drawing reflected in its mirror line is the same drawing, and every twin edge is the mirror image of its partner</div>' : '') +
    '<p class="fine">The numerical regularity check is separate from tessellation validity. Reflection is available on the square grid. Rotation and glide reflection, and rules for the triangle and hexagon grids, are not active in this checkpoint. Structural editing stays in the separate Grid Explorer.</p>';
  // the rule sheet
  const square = g.kind === 'square';
  $('rule-list').innerHTML = '<button id="rule-translation"' + (rule ? '' : ' disabled') + '>Translation<small>' + (rule ? 'stop mirroring: the drawing stays, and the edges are no longer twins' : 'the current rule: every copy is slid, never turned or flipped') + '</small></button>' +
    '<button id="rule-reflection"' + (square ? '' : ' disabled') + '>Reflection…<small>' + (square ? 'tap two edges that should be mirror images of each other' : 'ready for the square grid only in this version') + '</small></button>' +
    '<p class="fine">Rotation and glide reflection are not in this version.</p>';
  $('rule-translation').onclick = () => { $('sheet-rule').hidden = true; commit(S.toTranslation(cur()), 'Translation repeat: the drawing stays; edges are no longer mirror twins'); };
  $('rule-reflection').onclick = () => { $('sheet-rule').hidden = true; startPair(); };
}
function hitEdge(x, y) {
  let edge = null, ed = 16; for (const q of X.hit.edges) { const dx = q.b.x - q.a.x, dy = q.b.y - q.a.y, t = Math.max(0, Math.min(1, ((x - q.a.x) * dx + (y - q.a.y) * dy) / (dx * dx + dy * dy))), px = q.a.x + t * dx, py = q.a.y + t * dy, d = Math.hypot(px - x, py - y); if (d < ed) { edge = { ...q, px, py }; ed = d; } }
  return edge ? { kind: 'edge', q: edge } : null;
}
function hit(x, y) {
  let node = null, nd = 18; for (const q of X.hit.nodes) { const d = Math.hypot(q.x - x, q.y - y); if (d < nd) { node = q; nd = d; } }
  return node ? { kind: 'node', q: node } : hitEdge(x, y);
}
const ROLE_TEXT = { free: 'A new point will appear on this edge and every repeating copy.',
  twin: 'This edge has a mirror twin. A new point will appear on both, and on every repeating copy.',
  mirror: 'A mirror line crosses the middle of this edge, so its points come in mirrored pairs (or sit on the mirror line).' };
function tap(x, y, h) {
  if (!h) { hidePop(); return; }
  const role = S.role(cur(), h.q.id), twin = role.twins.length > 0;
  if (h.kind === 'node') { const q = h.q; pop(x, y, 'Added boundary point', twin || role.kind === 'mirror' ? 'It has a mirror image. Both belong to the polygons beside their edges and to every repeating copy.' : 'It belongs to both polygons beside this edge and to every repeating copy.', [
    { text: 'Remove this point', fn: () => { const z = R.remove(cur(), q.id, q.index); if (z.ok) commit(z.grid, z.removed > 1 || twin ? 'Point and its mirror image removed throughout the grid' : 'Point removed throughout the grid'); else toast(z.message, true); } }, { text: 'Cancel', fn: () => {} }]); }
  else if (role.kind === 'straight') pop(x, y, 'Edge on a mirror line', 'It has to stay straight: a point pulled off the mirror line would not be its own mirror image. Push or pull the other edges instead.', [{ text: 'OK', fn: () => {} }]);
  else { const q = h.q; pop(x, y, twin ? 'Mirror twin edge' : role.kind === 'mirror' ? 'Edge crossed by a mirror line' : 'Shared edge', role.kind === 'mirror' ? ROLE_TEXT.mirror : twin ? ROLE_TEXT.twin : ROLE_TEXT.free, [
    { text: 'Add a point here', fn: () => { const z = R.insert(cur(), q.id, q.at, world(q.px, q.py)); if (z.ok) commit(z.grid, twin || role.kind === 'mirror' ? 'Point added with its mirror image: drag either teal square' : 'Point added: drag the teal square to push or pull'); else toast(z.message, true); } }, { text: 'Cancel', fn: () => {} }]); }
}

/* ---------------- choosing a mirror: two edges, the proposal, then keep it or cancel ---------------- */
const PAIR_FIRST = 'Reflection: tap the first of two edges that should be mirror images of each other.';
const ends = E => E.id === 'a' ? [P(E.at[0], E.at[1]), P(E.at[0] + 1, E.at[1])] : [P(E.at[0], E.at[1]), P(E.at[0], E.at[1] + 1)];
const sameEdge = (a, b) => a && b && a.id === b.id && a.at[0] === b.at[0] && a.at[1] === b.at[1];
// an edge of whatever is drawn, as an edge of the one-square grid (the junctions never move)
function baseEdge(g, q) { const [p, r] = G.edgeEnds(g, G.ecls(g, q.id), q.at); return Math.abs(p.y - r.y) < 1e-9 ? { id: 'a', at: [Math.round(Math.min(p.x, r.x)), Math.round(p.y)] } : { id: 'b', at: [Math.round(p.x), Math.round(Math.min(p.y, r.y))] }; }
function pairBar(text, bad, canKeep) { const b = $('pairbar'); b.hidden = false; $('hint').hidden = true; b.classList.toggle('bad', !!bad); $('pair-text').textContent = text; $('pair-ok').disabled = !canKeep; }
function startPair() {
  const g = cur(), base = S.ruleOf(g) ? S.toTranslation(g) : g; hidePop();
  if (g.kind !== 'square') { toast('Reflection is ready for the square grid only in this version.', true); return; }
  if (!S.isUnitSquare(base)) { toast('This drawing repeats with a block of two squares, so another mirror cannot be chosen from it. Undo, or choose Grid › Square to start again.', true, 5200); return; }
  X.pair = { base, a: null, b: null, proposal: null, options: [] }; pairBar(PAIR_FIRST, false, false); sync(); draw();
}
function cancelPair(quiet) { if (!X.pair) return; X.pair = null; $('pairbar').hidden = true; $('hint').hidden = false; sync(); if (!quiet) draw(); }
// the edges next to the first one that a mirror line of the grid relates to it, with today's boundaries: the four that meet it at a
// corner, the two opposite sides, the two that continue it (edges further away that qualify can be tapped too; they are not marked)
function optionsFor(E) { const out = [], mid = F => { const [p, q] = ends(F); return P((p.x + q.x) / 2, (p.y + q.y) / 2); }, m = mid(E);
  for (const id of ['a', 'b']) for (let i = -1; i <= 1; i++) for (let j = -1; j <= 1; j++) { const F = { id, at: [E.at[0] + i, E.at[1] + j] }, c = mid(F); if (sameEdge(E, F) || Math.hypot(c.x - m.x, c.y - m.y) >= 1.01) continue; const pr = S.mirrorPairing(X.pair.base, E, F); if (pr.ok) out.push(Object.assign(F, { type: pr.type })); } return out; }
const PARTNER = { diagonal: 'a side that meets it at a corner', midline: 'the opposite side of the square', side: 'the side that continues it' };
// the second step of choosing a mirror: which partners the boundaries allow, or why there are none
function partnerText(opts) { const kinds = ['diagonal', 'midline', 'side'].filter(t => opts.some(F => F.type === t));
  if (!kinds.length) return 'No mirror can pair this edge with the boundaries as they are now: each mirror would need a side to stay straight, to be symmetric about its middle, or to copy a side that already has a different shape. Tap Cancel and remove or move points first, or tap this edge again to choose another.';
  return 'Now tap the edge that should be its mirror image. Dotted: the partners the boundaries allow — ' + kinds.map(t => PARTNER[t]).join(', ') + '.' + (kinds.length < 3 ? ' The others would change a side that is already bent.' : ''); }
function pairTap(x, y) {
  const A = X.pair, h = hitEdge(x, y); if (!h) return; const E = baseEdge(shown(), h.q);
  if (sameEdge(E, A.a)) { A.a = null; A.b = null; A.proposal = null; A.options = []; pairBar(PAIR_FIRST, false, false); draw(); return; }        // the first edge again: let go of it
  if (!A.a) { A.a = E; const t0 = performance.now(); A.options = optionsFor(E); A.optionsMs = +(performance.now() - t0).toFixed(1);
    pairBar(partnerText(A.options), !A.options.length, false); draw(); return; }
  A.b = E; const t0 = performance.now(), pr = S.mirrorPairing(A.base, A.a, E); pr.ms = +(performance.now() - t0).toFixed(1); A.proposal = pr;
  if (pr.ok) pairBar(pr.text + (R.count(A.base) ? ' Amber keeps its shape; teal takes the mirror image.' : ' Amber and teal: the twins.'), false, true);
  else pairBar(pr.message + ' Nothing has changed: tap another second edge, or Cancel.', true, false);
  draw();
}
// “Use this mirror”: the full checks first (the tiling validator, the edge correspondence, the mirror symmetry); only then is it kept
function confirmPair() {
  const A = X.pair, pr = A && A.proposal; if (!pr || !pr.ok) return; const t0 = performance.now(), v = R.verify(pr.grid);
  X.lastPair = { ok: v.ok, type: pr.type, family: pr.axis.family, previewMs: pr.ms, optionsMs: A.optionsMs, verifyMs: +(performance.now() - t0).toFixed(1), failing: v.failing, tiles: pr.tilesPerBlock, shapes: pr.tileKinds };
  if (!v.ok) { A.proposal = null; pairBar('This mirror cannot be used (' + v.failing.join(', ') + '). Nothing has changed.', true, false); draw(); return; }
  cancelPair(true); commit(pr.grid, 'Mirror set: push or pull an edge and its twin follows');
}

function wrapView() { const L = shown().lattice, uv = G.toLat(L, P(X.view.x, X.view.y)), a = Math.floor(uv[0]), b = Math.floor(uv[1]); if (a || b) { const d = G.latVec(L, [a, b]); X.view.x -= d.x; X.view.y -= d.y; } }
function pinchStart() { const [a, b] = [...X.fingers.values()], mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2; X.pinch = { dist: Math.max(10, Math.hypot(a.x - b.x, a.y - b.y)), scale: X.view.s, anchor: world(mx, my) }; X.drag = null; X.down = null; hidePop(); draw(); }
function pinchMove() { const [a, b] = [...X.fingers.values()], mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2; X.view.s = Math.max(24, Math.min(135, X.pinch.scale * Math.hypot(a.x - b.x, a.y - b.y) / X.pinch.dist)); X.view.x = X.pinch.anchor.x - (mx - cv.clientWidth / 2) / X.view.s; X.view.y = X.pinch.anchor.y + (my - cv.clientHeight / 2) / X.view.s; if (!X.pair) wrapView(); draw(); }
cv.addEventListener('pointerdown', e => { try { cv.setPointerCapture(e.pointerId); } catch (_) {} X.fingers.set(e.pointerId, P(e.clientX, e.clientY)); if (X.fingers.size === 2) { pinchStart(); return; } if (X.fingers.size !== 1 || X.pinch) return; hidePop();
  X.down = X.pair ? { x: e.clientX, y: e.clientY, pair: true } : { x: e.clientX, y: e.clientY, hit: hit(e.clientX, e.clientY), moved: false, original: cur() }; });
cv.addEventListener('pointermove', e => { if (!X.fingers.has(e.pointerId)) return; X.fingers.set(e.pointerId, P(e.clientX, e.clientY)); if (X.fingers.size === 2) { pinchMove(); return; } const d = X.down; if (!d || d.pair || !d.hit || d.hit.kind !== 'node') return;
  if (Math.hypot(e.clientX - d.x, e.clientY - d.y) > 5) d.moved = true; if (!d.moved) return;
  const t0 = performance.now(), q = d.hit.q; if (!X.drag) X.drag = { id: q.id, index: q.index, at: q.at, grid: d.original, blocked: false, frames: [], steps: [] };
  const z = R.move(X.drag.grid, q.id, q.index, q.at, world(e.clientX, e.clientY)), t1 = performance.now(); X.drag.grid = z.grid; X.drag.blocked = z.blocked; draw(); X.drag.steps.push(t1 - t0); X.drag.frames.push(performance.now() - t0); });
const stats = a => { const s = a.slice().sort((x, y) => x - y); return s.length ? { n: s.length, mean: +(s.reduce((x, y) => x + y, 0) / s.length).toFixed(2), p95: +s[Math.min(s.length - 1, Math.floor(s.length * 0.95))].toFixed(2), max: +s[s.length - 1].toFixed(2) } : { n: 0 }; };
function end(e, cancel) { if (!X.fingers.has(e.pointerId)) return; X.fingers.delete(e.pointerId); if (X.pinch) { if (X.fingers.size < 2) { X.pinch = null; X.down = null; } return; }
  const d = X.down; X.down = null; if (!d) return;
  if (d.pair) { if (!cancel && X.pair && Math.hypot(e.clientX - d.x, e.clientY - d.y) <= 12) pairTap(e.clientX, e.clientY); return; }
  if (X.drag) { const D = X.drag, candidate = D.grid; X.drag = null; X.lastDrag = { rule: R.ruleName(d.original), frames: stats(D.frames), steps: stats(D.steps), blockedAtEnd: D.blocked };
    if (cancel || candidate === d.original) { draw(); return; }
    const t0 = performance.now(), v = R.verify(candidate); X.lastDrag.verifyMs = +(performance.now() - t0).toFixed(1); X.lastDrag.kept = v.ok;
    if (v.ok) commit(candidate, S.ruleOf(candidate) ? 'Boundary and its mirror image updated throughout the grid' : 'Boundary updated throughout the grid'); else { draw(); toast('That pull would break the tiling (' + v.failing.join(', ') + ').', true); } return; }
  if (!cancel && Math.hypot(e.clientX - d.x, e.clientY - d.y) <= 12) tap(e.clientX, e.clientY, d.hit); }
cv.addEventListener('pointerup', e => end(e, false)); cv.addEventListener('pointercancel', e => end(e, true));
$('undo').onclick = () => { cancelPair(true); if (X.index > 0) { X.index--; sync(); draw(); } }; $('redo').onclick = () => { cancelPair(true); if (X.index < X.history.length - 1) { X.index++; sync(); draw(); } };
$('block').onclick = () => { X.block = !X.block; sync(); draw(); };
$('grid').onclick = () => { cancelPair(); $('sheet-grid').hidden = false; }; $('info').onclick = () => { sync(); $('sheet-info').hidden = false; };
$('rules').onclick = () => { if (X.pair) { cancelPair(); return; } hidePop(); sync(); $('sheet-rule').hidden = false; };
$('pair-cancel').onclick = () => cancelPair(); $('pair-ok').onclick = confirmPair;
$('grid-list').innerHTML = Object.entries(R.TYPES).map(([k, name]) => '<button data-type="' + k + '">' + name + '</button>').join('');
$('grid-list').onclick = e => { const b = e.target.closest('[data-type]'); if (!b) return; $('sheet-grid').hidden = true; hidePop(); const g = R.base(b.dataset.type); commit(g, nameOf(g) + ' grid selected'); const p = G.centroid(G.faceOutline(g, g.faces[0], [0, 0]).pts); X.view.x = p.x; X.view.y = p.y; draw(); };
const nameOf = g => R.TYPES[g.kind]; document.querySelectorAll('[data-close]').forEach(b => b.onclick = () => { $(b.dataset.close).hidden = true; });
window.addEventListener('keydown', e => { if (e.key === 'Escape') cancelPair(); });
window.addEventListener('resize', fit); sync(); fit();
window.__regular = { X, R, G, S, C, cur, shown, draw, hit, hitEdge, commit, world, screen, startPair, cancelPair, pairTap, confirmPair, baseEdge, sync, capture: () => cv.toDataURL('image/png') };
})();
