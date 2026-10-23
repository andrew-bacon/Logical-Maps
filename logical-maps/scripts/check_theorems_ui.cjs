// NODE_PATH=/path/to/node_modules node scripts/check_theorems_ui.cjs (requires jsdom).
// The Results tab: every proved result among the principles the sidebar shows, grouped by
// what it concludes, narrowed to a principle by name in a chosen role or to some words.
const fs = require('node:fs'), path = require('node:path'), assert = require('node:assert/strict');
const {JSDOM, VirtualConsole} = require('jsdom');
const root = path.resolve(__dirname, '..');
const template = fs.readFileSync(path.join(root, 'viewer/template.html'), 'utf8');
const errors = [];
const certificate = {source_id: 'paper', lean: 'none', produced_by: 'Fixture author', checked_by: []};
const rule = (id, premises, conclusion, status = 'proved') => ({id, premises, conclusion, status, certificate, sources: ['Fixture proof']});
const data = {
  topic: {id: 'theorems', title: 'Results fixture', background: [], source_catalog: [{id: 'paper', name: 'A paper', kind: 'published-paper'}]},
  principles: [...'abce'].map(id => ({id, name: id.toUpperCase(), statement: `Principle ${id}`})),
  results: [rule('a-b', ['a'], 'b'), rule('b-c', ['b'], 'c'), rule('c-a', ['c'], 'a'), rule('ae-false', ['a', 'e'], 'false'), rule('guess', ['e'], 'c', 'conjectured')],
  models: [],
};
const vc = new VirtualConsole(); vc.on('jsdomError', e => errors.push(e));
const dom = new JSDOM(template.replace('/*__PMAP_DATA__*/null', () => JSON.stringify(data)), {url: 'https://maps.example/', runScripts: 'dangerously', pretendToBeVisual: true, virtualConsole: vc});
const w = dom.window, d = w.document;
const $ = s => d.querySelector(s), $$ = s => [...d.querySelectorAll(s)];
const groups = () => $$('#theorems details.theorems-group').map(g => [g.dataset.conclusion, [...g.querySelectorAll('tr[data-result]')].map(tr => tr.dataset.result)]);
const type = value => { const input = $('#theorems-find'); input.value = value; input.dispatchEvent(new w.Event('input', {bubbles: true})); w.flushTheorems(); };
try {
  $('.tab[data-tab="theorems"]').click();
  assert.equal(d.getElementById('pane-theorems').dataset.active, 'true');
  assert.ok(d.getElementById('pane-theorems').contains(d.getElementById('graph-sidebar')), 'The tab shares the sidebar');
  $('#pr-all').click();
  assert.deepEqual(groups(), [['a', ['c-a']], ['b', ['a-b']], ['c', ['b-c']], ['false', ['ae-false']]], 'Proved results by conclusion, incompatibilities last; no conjecture');
  assert.match($('#theorems .theorems-count').textContent, /^4 results$/);

  // The sidebar's principles bound the list: a result is listed only among shown principles.
  $('#pr-filters [data-show-positive="a"]').click();
  assert.deepEqual(groups(), [['c', ['b-c']]], 'Hiding A drops every result that mentions it');
  $('#pr-reset').click(); $('#pr-all').click();
  assert.equal(groups().length, 4);

  // Text anywhere in a statement; the exact roles wait for a principle's name.
  assert.ok($$('[data-theorems-role]:not([data-theorems-role="either"])').every(b => b.disabled), 'The exact roles wait for a principle');
  assert.equal($('[data-theorems-role="either"]').disabled, false);
  const box = $('#theorems-find');
  type('B');
  assert.equal($('#theorems-find'), box, 'Typing keeps the search box, so its suggestions are not rebuilt at each keystroke');
  assert.deepEqual(groups(), [['b', ['a-b']], ['c', ['b-c']]], 'Anywhere: the text in any name');
  assert.match($('#theorems .theorems-count').textContent, /2 results matching “B”/);
  $('[data-theorems-role="conclusion"]').click();
  assert.deepEqual(groups(), [['b', ['a-b']]], 'Concluding exactly it');
  assert.match($('#theorems .theorems-count').textContent, /1 result concluding B/);
  $('[data-theorems-role="premise"]').click();
  assert.deepEqual(groups(), [['c', ['b-c']]], 'Using exactly it');
  assert.equal($('[data-theorems-role="premise"]').getAttribute('aria-pressed'), 'true');
  type('a ∧ e');
  assert.deepEqual(groups(), [['false', ['ae-false']]], 'Text that names no principle matches anywhere, whatever role is pressed');
  $('[data-theorems-role="either"]').click();
  type('nothing like this');
  assert.ok($('#theorems .empty'));

  // A closed group stays closed across a change.
  type('');
  const groupC = $('#theorems details.theorems-group[data-conclusion="c"]'); groupC.open = false;
  type('x'); type('');
  assert.equal($('#theorems details.theorems-group[data-conclusion="c"]').open, false);

  // One control opens every group, then closes them all; headings name the conclusion alone.
  assert.equal($('#theorems [data-theorems-expand]').textContent, 'expand all', 'One group closed: offer to open all');
  $('#theorems [data-theorems-expand]').click();
  assert.ok($$('#theorems details.theorems-group').every(g => g.open));
  assert.equal($('#theorems [data-theorems-expand]').textContent, 'collapse all');
  $('#theorems [data-theorems-expand]').click();
  assert.ok($$('#theorems details.theorems-group').every(g => !g.open));
  $('#theorems [data-theorems-expand]').click();
  assert.equal($('#theorems details.theorems-group[data-conclusion="b"] > summary').textContent.trim(), 'B 1');

  // A row opens the result's pop-up.
  $('#theorems tr[data-result="a-b"]').click();
  assert.equal(d.getElementById('pop').hidden, false);
  assert.match(d.getElementById('pop').textContent, /A ⇒ B/);
  // A box or diamond is part of the text searched for: □A does not find A.
  assert.equal(w.eval('findText("□ Actuality")'), '□actuality');
  assert.equal(w.eval('findText("A ∧ ◇B")'), 'a ◇b');
  assert.deepEqual(errors, []);
  console.log('PASS: the Results tab lists proved results among the shown principles by conclusion, narrows to a principle in a role or to words, keeps closed groups closed, and opens a result.');
} finally { w.close(); }
