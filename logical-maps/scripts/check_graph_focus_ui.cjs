// NODE_PATH=/path/to/node_modules node scripts/check_graph_focus_ui.cjs (requires jsdom).
// Selecting principles on the graph dims the arrows that touch none of them, as hovering
// a box does; hovering takes over while it lasts, and the shading of the boxes stays.
const fs = require('node:fs'), path = require('node:path'), assert = require('node:assert/strict');
const {JSDOM, VirtualConsole} = require('jsdom');
const root = path.resolve(__dirname, '..');
const template = fs.readFileSync(path.join(root, 'viewer/template.html'), 'utf8');
const errors = [];
const certificate = {source_id: 'paper', lean: 'none', produced_by: 'Fixture author', checked_by: []};
const rule = (id, premises, conclusion) => ({id, premises, conclusion, status: 'proved', certificate, sources: ['Fixture proof']});
const data = {
  topic: {id: 'focus', title: 'Focus fixture', background: [], source_catalog: [{id: 'paper', name: 'A paper', kind: 'published-paper'}]},
  principles: [...'abcd'].map(id => ({id, name: id.toUpperCase(), statement: `Principle ${id}`})),
  results: [rule('a-b', ['a'], 'b'), rule('c-d', ['c'], 'd')],
  // A model of A and C, and one of A without C: C is consistent with A and A with C, A can fail C.
  models: [{id: 'both', name: 'Both', satisfies: ['a', 'c'], violates: [], status: 'proved', certificate, sources: ['Fixture model']},
    {id: 'a-only', name: 'A only', satisfies: ['a'], violates: ['c'], status: 'proved', certificate, sources: ['Fixture model']}],
};
const vc = new VirtualConsole(); vc.on('jsdomError', e => errors.push(e));
const dom = new JSDOM(template.replace('/*__PMAP_DATA__*/null', () => JSON.stringify(data)), {url: 'https://maps.example/', runScripts: 'dangerously', pretendToBeVisual: true, virtualConsole: vc});
const w = dom.window, d = w.document;
try {
  const node = id => [...d.querySelectorAll('#graph .node[data-members]')].find(n => n.dataset.members.split(',').includes(id));
  const edge = id => d.querySelector(`#graph .edge-g[data-from="${node(id).dataset.class}"]`);
  assert.ok(edge('a') && edge('c'), 'Both arrows are drawn');
  assert.equal(d.querySelectorAll('#graph .edge-g.dim').length, 0, 'Nothing is dimmed to begin with');

  w.select({type: 'principle', id: 'a'});
  assert.equal(edge('a').classList.contains('dim'), false, 'The selected principle’s arrow stays bright');
  assert.equal(edge('c').classList.contains('dim'), true, 'The other is dimmed');
  assert.equal(d.querySelectorAll('#graph .node.dim').length, 0, 'Boxes keep their shading, undimmed');
  assert.equal(edge('a').classList.contains('hot'), false, 'Not as heavy as a hover');
  assert.equal(edge('a').classList.contains('near'), true, 'But heavier than at rest');

  w.select({type: 'principle', id: 'c'}, true);
  assert.equal(d.querySelectorAll('#graph .edge-g.dim').length, 0, 'Two selected principles keep both arrows');

  w.select({type: 'principle', id: 'a'});
  w.hover({node: node('c').dataset.class});
  assert.equal(edge('a').classList.contains('dim'), true, 'Hovering takes over');
  assert.equal(edge('c').classList.contains('dim'), false);
  assert.equal(node('a').classList.contains('dim'), true, 'As before, hovering dims boxes too');
  w.hover(null);
  assert.equal(edge('a').classList.contains('dim'), false, 'The selection’s focus returns when the pointer leaves');
  assert.equal(edge('c').classList.contains('dim'), true);
  assert.equal(d.querySelectorAll('#graph .node.dim').length, 0);

  w.select(null);
  assert.equal(d.querySelectorAll('#graph .edge-g.dim, #graph .edge-g.near').length, 0, 'Clearing the selection clears the focus');

  // The pane sends a selection to the Theory explorer as its assumptions, in place of its own.
  w.select({type: 'principle', id: 'a'}); w.select({type: 'principle', id: 'c'}, true);
  w.eval("theory.positive.add('d')");
  d.getElementById('pop').querySelector('[data-selection-action="explorer"]').click();
  assert.equal(d.querySelector('.tab[data-tab="models"]').getAttribute('aria-selected'), 'true');
  assert.deepEqual(JSON.parse(w.eval('JSON.stringify([[...theory.positive].sort(), [...theory.negative]])')), [['a', 'c'], []]);
  assert.deepEqual([...d.querySelectorAll('#ex-assumptions [data-assumed]')].map(li => li.dataset.assumed), ['a', 'c']);
  d.querySelector('.tab[data-tab="graph"]').click();

  // The pane, not the line, offers the lattice: drawn from the selection on the graph, pared
  // down to the selection on the lattice itself.
  w.select({type: 'principle', id: 'a'}); w.select({type: 'principle', id: 'c'}, true);
  assert.equal(d.getElementById('relation-legend').querySelector('[data-selection-action="lattice"]'), null, 'Not on the line');
  const toLattice = d.getElementById('pop').querySelector('[data-selection-action="lattice"]');
  assert.equal(toLattice.textContent, 'Show in Lattice');
  toLattice.click();
  assert.equal(w.eval('state.tab'), 'lattice');
  assert.deepEqual(JSON.parse(w.eval('JSON.stringify(lattice.shown)')), ['a', 'c']);
  assert.equal(d.getElementById('pop').hidden, false, 'The pane shows the selection, as if made here');
  assert.equal(d.getElementById('pop').querySelector('.pop-t').textContent, 'A ∧ C');
  w.eval("lattice.shown = ['a', 'c', 'd']; lattice.selected = null; renderLattice()");
  w.select({type: 'principle', id: 'a'});
  const pare = d.getElementById('pop').querySelector('[data-selection-action="lattice"]');
  assert.equal(pare.textContent, 'Hide others');
  pare.click();
  assert.deepEqual(JSON.parse(w.eval('JSON.stringify(lattice.shown)')), ['a'], 'Only the selection and its conjunctions remain');
  w.select(null);
  d.querySelector('.tab[data-tab="graph"]').click();

  // In the pane one principle gives way to its negation; and when a selected principle is off
  // the diagram the line offers Show in place of Hide.
  w.select({type: 'principle', id: 'a'}); w.select({type: 'principle', id: 'c'}, true);
  d.getElementById('pop').querySelector('[data-negate-selection="c"]').click();
  assert.deepEqual(JSON.parse(w.eval('JSON.stringify(state.focus)')), ['a', '!c']);
  assert.deepEqual([...d.querySelectorAll('#pop .selection-list .name')].map(b => b.textContent), ['A', '¬C']);
  const legend = d.getElementById('relation-legend');
  assert.ok(legend.querySelector('[data-selection-action="show"]'), '¬C is not drawn, so the line offers Show');
  assert.equal(legend.querySelector('[data-selection-action="hide"]'), null);
  legend.querySelector('[data-selection-action="show"]').click();
  assert.equal(w.eval("state.negativeShown.has('c')"), true, 'Show draws it');
  assert.ok(legend.querySelector('[data-selection-action="hide"]'), 'And the line offers Hide again');
  assert.deepEqual(JSON.parse(w.eval('JSON.stringify(state.focus)')), ['a', '!c'], 'The selection is kept');
  w.select(null);

  // On the lattice the heavy arrows rise from the node the whole selection generates, so they
  // follow the selection as it grows, shrinks and clears, however it was made.
  d.querySelector('[data-tab="lattice"]').click();
  w.eval("lattice.shown = ['a', 'c']; lattice.selected = null; renderLattice()");
  const selGens = () => { const n = d.querySelector('#lat-graph .lat-node.sel'); return n ? JSON.parse(w.eval(`JSON.stringify(lattice.byId.get(${JSON.stringify(n.dataset.latNode)}).generators)`)).sort() : null; };
  const near = () => d.querySelectorAll('#lat-graph [data-lat-edge].near').length;
  w.select({type: 'principle', id: 'a'});
  assert.deepEqual(selGens(), ['a'], 'One principle: its own node');
  assert.ok(near() > 0, 'With its arrows heavy');
  w.select({type: 'principle', id: 'c'}, true);
  assert.deepEqual(selGens(), ['a', 'c'], 'Two: their conjunction');
  w.select({type: 'principle', id: 'a'}, true);
  assert.deepEqual(selGens(), ['c'], 'Dropping one moves the focus to what is left');
  w.select({type: 'principle', id: 'c'}, true);
  assert.equal(selGens(), null, 'Dropping the last clears it');
  assert.equal(near(), 0);
  assert.equal(d.querySelectorAll('#lat-graph [data-lat-edge].far').length, 0);
  assert.equal(w.eval('lattice.selected'), null);

  // Against a selection the lattice takes the graph's colours; with none, no colour at all.
  w.eval("lattice.shown = ['a', 'c', 'd']; lattice.selected = null; renderLattice()");
  const relOf = gens => { const id = JSON.parse(w.eval(`JSON.stringify(lattice.nodes.filter(n => JSON.stringify([...n.generators].sort()) === ${JSON.stringify(JSON.stringify(gens))}).map(n => n.id))`))[0]; const el = d.querySelector(`#lat-graph [data-lat-node="${id}"]`); return [...el.classList].filter(c => c.startsWith('rel-')).join(' '); };
  assert.equal(d.querySelectorAll('#lat-graph [data-lat-node][class*="rel-"]').length, 0, 'Nothing selected, nothing coloured');
  w.select({type: 'principle', id: 'c'});
  assert.equal(relOf(['c']), 'rel-base');
  assert.equal(relOf(['d']), 'rel-entailed', 'C entails D: green');
  assert.equal(relOf(['a']), 'rel-consistent', 'A is consistent with C, not entailed, and no model fails it: the green half');
  assert.equal(relOf(['a', 'c']), 'rel-consistent');
  const latLegend = d.getElementById('lat-legend');
  assert.match(latLegend.textContent, /entailed 1/, 'D alone: ⊤ is not counted'); assert.match(latLegend.textContent, /excluded 0/, 'Nor ⊥');
  assert.match(latLegend.textContent, /consistent [1-9]/);
  w.select({type: 'principle', id: 'a'});
  assert.equal(relOf(['c']), 'rel-independent', 'A neither entails nor excludes C, and models go both ways: split');
  w.select(null);
  assert.equal(d.querySelectorAll('#lat-graph [data-lat-node][class*="rel-"]').length, 0, 'Clearing the selection clears the colours');
  assert.deepEqual(errors, []);
  console.log('PASS: a graph selection keeps its arrows bright and dims the rest, hovering takes over and hands back, clearing the selection clears the focus; the lattice focuses the node the whole selection generates as it grows, shrinks and clears, and colours its nodes by their relation to the selection, and only then.');
} finally { w.close(); }
