// NODE_PATH=/path/to/node_modules node scripts/check_theory_assumptions_ui.cjs (requires jsdom).
// The Theory explorer's Assumptions box: what is assumed, in the explorer's own words;
// what the other assumptions already settle, with proofs; what further follows beyond
// what the fixed background gives by itself; and the contradiction, when there is one.
const fs = require('node:fs'), path = require('node:path'), assert = require('node:assert/strict');
const {JSDOM, VirtualConsole} = require('jsdom');
const root = path.resolve(__dirname, '..');
const template = fs.readFileSync(path.join(root, 'viewer/template.html'), 'utf8');
const errors = [], pages = [];
const certificate = {source_id: 'paper', lean: 'none', produced_by: 'Fixture author', checked_by: []};
const rule = (id, premises, conclusion, status = 'proved') => ({id, premises, conclusion, status, certificate, sources: ['Fixture proof']});
const model = (id, satisfies, violates) => ({id, name: id, satisfies, violates, status: 'proved', certificate, sources: ['Fixture model']});
const data = {
  topic: {id: 'assumptions', title: 'Assumptions fixture', background: ['z'], source_catalog: [{id: 'paper', name: 'A paper', kind: 'published-paper'}],
    background_presets: [{id: 'pk', name: 'PK', category: 'packages', principles: ['a']}]},
  principles: [...[...'zabcdet'].map(id => ({id, name: id.toUpperCase(), statement: `Principle ${id}`})),
    // Names with a leading symbol, and with a suffix, to fix the order of names.
    {id: 'box-a', name: '□A', statement: 'Necessarily A'}, {id: 'a-t', name: 'A (type t)', statement: 'A at type t'}],
  // Z is fixed and gives T; D holds outright; A, B and C form a cycle; A and E clash.
  results: [rule('z-t', ['z'], 't'), rule('top-d', [], 'd'), rule('a-b', ['a'], 'b'), rule('b-c', ['b'], 'c'), rule('c-a', ['c'], 'a'), rule('ae-false', ['a', 'e'], 'false')],
  models: [model('fits', ['a'], ['e']), model('other', [], ['a'])],
};
function page(url = 'https://maps.example/?theory=') {
  const vc = new VirtualConsole(); vc.on('jsdomError', e => errors.push(e));
  const dom = new JSDOM(template.replace('/*__PMAP_DATA__*/null', () => JSON.stringify(data)), {url, runScripts: 'dangerously', pretendToBeVisual: true, virtualConsole: vc,
    beforeParse(w) { w.matchMedia = () => ({matches: false, addEventListener() {}}); },
  });
  pages.push(dom); return dom;
}
const dom = page(), w = dom.window, doc = w.document;
const $ = selector => doc.querySelector(selector), $$ = selector => [...doc.querySelectorAll(selector)];
const click = selector => { const el = $(selector); assert.ok(el, selector); el.click(); };
const text = selector => { const el = $(selector); assert.ok(el, selector); return el.textContent.trim(); };
const headText = () => [...$('#ex-assumptions .ex-head').childNodes].filter(n => n.nodeName !== 'BUTTON').map(n => n.textContent).join('').trim();
const listed = kind => $$(`#ex-assumptions details[data-ex-list="${kind}"] li > button[data-principle]`).map(b => b.textContent.trim());
const proofOf = el => [...el.querySelectorAll('ol li button[data-result]')].map(b => b.textContent);
const lines = el => [...el.querySelectorAll('ol li')].map(li => li.textContent.replace(/\s+/g, ' ').trim().split(' ').slice(0, 3).join(' '));
const why = id => $(`#model-principles [data-assumption-row="${id}"] details[data-why="row:${id}"]`);
try {
  click('[data-tab="models"]');
  // The box heads the model column, in the explorer's own words.
  assert.ok($('#models .ex > .ex-assumptions'), 'The box is a column of its own');
  assert.equal(headText(), 'Assumptions 0');
  assert.equal(text('#models [data-theory-preset="pk"]'), 'Assume PK');
  assert.equal(text('#ex-clear'), 'clear assumptions');
  assert.ok($('#ex-clear').closest('.ex-head') && $('#ex-clear').classList.contains('lnk'), 'A plain link on the heading line');
  assert.ok($('#models .ex-principles > .explorer-packages:last-child [data-theory-preset="pk"]'), 'The packages wait at the foot of the list');
  assert.equal($('#ex-assumptions [data-assumed="z"]'), null, 'The fixed background goes without saying');
  assert.match(text('#ex-assumptions .ex-status'), /No further principles follow/, 'What the background gives by itself is not counted');
  assert.match(text('#ex-assumptions .ex-status'), /No principles ruled out/);

  click('#models [data-assume-positive="a"]');
  assert.equal(headText(), 'Assumptions 1');
  assert.ok($('#ex-assumptions [data-assumed="a"]').classList.contains('in'));
  assert.equal(text('#ex-assumptions details[data-ex-list="follow"] > summary'), '2 further principles follow');
  assert.deepEqual(listed('follow'), ['B', 'C'], 'Neither T (from the fixed background) nor D (outright) is listed');
  // Each listed consequence says why, in place, as the principle list does.
  assert.deepEqual(lines($('#ex-assumptions details[data-why="box:c"]')), ['✓ A assumed', 'A ⇒ B', 'B ⇒ C']);
  assert.match($('#ex-assumptions details[data-why="box:e"]').textContent, /Contradicts what is assumed/);
  assert.equal(text('#ex-assumptions details[data-ex-list="excluded"] > summary'), '1 principle ruled out');
  assert.deepEqual(listed('excluded'), ['E']);
  assert.equal($('#ex-assumptions [data-why^="also:"]'), null, 'A lone assumption is settled by nothing');
  // A row the assumptions settle says why, in place, starting from what is assumed.
  assert.equal(why('c').querySelector('summary').textContent, 'why');
  assert.match(why('c').textContent, /Follows from what is assumed/);
  assert.deepEqual(lines(why('c')), ['✓ A assumed', 'A ⇒ B', 'B ⇒ C']);
  assert.match(why('e').textContent, /Contradicts what is assumed/);
  assert.deepEqual(lines(why('e')), ['E supposed, to', '✓ A assumed', 'A ∧ E'], 'A failure starts from the supposition');
  assert.match(why('d').textContent, /Holds with nothing assumed/);
  assert.deepEqual(lines(why('t')), ['Z standing background', 'Z ⇒ T']);
  assert.equal($('#model-principles [data-assumption-row="a"] details[data-why]'), null, 'What is assumed has no why on the left; the box flags it when redundant');
  assert.equal($('#model-principles [data-assumption-row="z"] details[data-why]'), null);
  // Clicking a why toggles it alone; the category it sits in stays as it was.
  const category = why('d').closest('details[data-category]');
  assert.equal(category.open, true);
  const clickOnWhy = new w.MouseEvent('click', {bubbles: true, cancelable: true});
  assert.equal(why('d').querySelector('summary').dispatchEvent(clickOnWhy), true, 'The list does not cancel the click');
  assert.equal(category.open, true, 'And does not collapse the category');
  assert.equal(w.eval("state.collapsed.has('all')"), false);
  why('d').open = true;
  assert.match($('.explorer-models').textContent, /Matching models/);
  assert.ok($('.explorer-models [data-open-model="fits"]'));

  // An assumption the others settle says so, with its proof; equivalents name each other.
  $('#ex-assumptions details[data-ex-list="follow"]').open = true;
  click('#models [data-assume-positive="c"]');
  assert.equal($('#ex-assumptions details[data-ex-list="follow"]').open, true, 'An open list stays open across a change');
  assert.equal(why('d').open, true, 'So does an open why in the principle list');
  assert.equal(text('#ex-assumptions details[data-ex-list="follow"] > summary'), '1 further principle follows');
  assert.deepEqual(listed('follow'), ['B']);
  const alsoC = $('#ex-assumptions [data-why="also:c"]');
  assert.ok(alsoC, 'C follows from A');
  assert.equal(alsoC.querySelector('summary').textContent, 'also follows');
  assert.deepEqual(proofOf(alsoC), ['A ⇒ B', 'B ⇒ C']);
  assert.match(alsoC.textContent, /Equivalent to A given the rest/);
  const alsoA = $('#ex-assumptions [data-why="also:a"]');
  assert.match(alsoA.textContent, /Equivalent to C given the rest/);
  assert.deepEqual(proofOf(alsoA), ['C ⇒ A']);
  alsoA.open = true;
  click('#models [data-assume-negative="e"]');
  assert.equal($('#ex-assumptions [data-why="also:a"]').open, true, 'An open proof stays open too');

  // A denied principle is settled when the others contradict it.
  const rowE = $('#ex-assumptions [data-assumed="e"]');
  assert.ok(rowE.classList.contains('out'));
  assert.equal(rowE.querySelector('[data-principle]').textContent, '¬E');
  const alsoE = rowE.querySelector('[data-why="also:e"]');
  assert.match(alsoE.textContent, /contradicts the other assumptions/);
  assert.doesNotMatch(alsoE.textContent, /Equivalent/, 'A and C each settle it alone');
  assert.deepEqual(proofOf(alsoE), ['A ∧ E ⇒ ⊥']);
  assert.deepEqual(lines(alsoE), ['E supposed, to', '✓ A assumed', 'A ∧ E']);
  assert.deepEqual(lines(alsoC), ['✓ A assumed', 'A ⇒ B', 'B ⇒ C']);
  assert.match(text('#ex-assumptions .ex-status'), /No principles ruled out/, 'What is assumed is not also counted as ruled out');

  // The box opens the lattice of its assumptions, negations included.
  click('#ex-assumptions [data-theory-lattice]');
  assert.equal(w.eval('state.tab'), 'lattice');
  assert.deepEqual(JSON.parse(w.eval('JSON.stringify(lattice.shown)')), ['a', 'c', '!e']);
  assert.equal($('#pop').hidden, false, 'And selects them, so the pane reads as for a selection made there');
  assert.equal($('#pop .pop-t').textContent, 'A ∧ C ∧ ¬E');
  click('[data-tab="models"]');

  // Negating in the box swaps the sign of one assumption; the rest stay.
  click('#ex-assumptions [data-flip-assumption="c"]');
  assert.deepEqual(JSON.parse(w.eval("JSON.stringify([theory.positive.has('c'), theory.negative.has('c'), theory.positive.has('a')])")), [false, true, true]);
  assert.ok($('#ex-assumptions [data-assumed="c"]').classList.contains('out'));
  click('#ex-assumptions [data-flip-assumption="c"]');
  assert.ok($('#ex-assumptions [data-assumed="c"]').classList.contains('in'), 'And back');

  // Removing from the box is the same as unmarking on the left; flags follow the change.
  click('#ex-assumptions [data-drop-assumption="c"]');
  assert.equal(w.eval("inTheory('c')"), false);
  assert.equal($('#ex-assumptions [data-assumed="c"]'), null);
  assert.equal($('#ex-assumptions [data-why="also:a"]'), null, 'A follows from nothing now');
  assert.ok($('#ex-assumptions [data-why="also:e"]'), 'A alone still settles ¬E');
  assert.equal($('#models [data-assume-positive="c"]').getAttribute('aria-pressed'), 'false');
  assert.match(w.location.search, /theory=a/);

  // Inconsistency is a state of the box; the model column waits.
  click('#models [data-assume-positive="e"]');
  assert.match(text('#ex-assumptions .ex-bad'), /assumptions are inconsistent/);
  assert.equal($('#ex-assumptions .ex-status'), null);
  assert.equal($('#ex-assumptions [data-why^="also:"]'), null, 'Nothing is called redundant in a contradiction');
  assert.ok($$('#ex-assumptions .ex-bad li button').some(b => b.textContent === 'A ∧ E ⇒ ⊥'));
  assert.equal($$('.explorer-models .ex-m').length, 0);
  assert.match($('.explorer-models').textContent, /Matching models/);
  click('#ex-clear');
  assert.equal(headText(), 'Assumptions 0');
  assert.equal($('#ex-assumptions .ex-bad'), null);
  assert.ok($('.explorer-models [data-open-model="other"]'));

  // Lists of principles go by name, a leading symbol counting right after the bare name.
  assert.deepEqual($$('#model-principles [data-assumption-row]').map(li => li.dataset.assumptionRow), ['a', 'box-a', 'a-t', 'b', 'c', 'd', 'e', 't', 'z']);
  click('#models [data-assume-positive="box-a"]'); click('#models [data-assume-positive="a-t"]');
  assert.deepEqual($$('#ex-assumptions [data-assumed]').map(li => li.dataset.assumed), ['box-a', 'a-t'], 'The box too');
  click('#ex-clear');

  // A principle's page lists the results concluding it before those using it, incompatibilities last.
  w.eval('openPage({type: "principle", id: "a"})');
  const heads = $$('#page h3.verdict-group').map(h => h.textContent.trim());
  assert.deepEqual(heads, ['Concluding it 1', 'Using it as a premise 2']);
  const tables = $$('#page table.results');
  assert.deepEqual([...tables[0].querySelectorAll('tr[data-result]')].map(tr => tr.dataset.result), ['c-a']);
  assert.deepEqual([...tables[1].querySelectorAll('tr[data-result]')].map(tr => tr.dataset.result), ['a-b', 'ae-false']);
  w.eval('pageBack()'); click('[data-tab="models"]');

  // In the explorer a name opens the principle's page; its statement shows on focus (and, after a
  // delay, on hover) in a preview with nothing to click.
  const nameB = $('#model-principles [data-assumption-row="b"] button[data-principle]');
  nameB.dispatchEvent(new w.FocusEvent('focusin', {bubbles: true}));
  const previewEl = $('#preview');
  assert.ok(previewEl && !previewEl.hidden, 'Focus shows the preview');
  assert.match(previewEl.textContent, /Principle b/);
  assert.equal(previewEl.querySelector('button, a'), null, 'Nothing in it to click');
  nameB.dispatchEvent(new w.FocusEvent('focusout', {bubbles: true}));
  assert.equal(previewEl.hidden, true, 'And leaving hides it');
  nameB.click();
  assert.equal(doc.getElementById('pane-page').dataset.active, 'true', 'A click opens the page');
  assert.equal(text('#page h1'), 'B');
  w.eval('pageBack()'); click('[data-tab="models"]');

  // In the lattice sidebar a name selects the principle, as on the graph.
  click('[data-tab="lattice"]');
  click('#lat-filters .principle-name[data-principle="b"]');
  assert.deepEqual(JSON.parse(w.eval("JSON.stringify([state.selected.type, state.selected.id])")), ['principle', 'b']);
  assert.equal($('#lat-filters .principle-name[data-principle="b"]').getAttribute('aria-pressed'), 'true');
  w.eval('select(null)'); click('[data-tab="models"]');

  // A package button assumes its principles and then rests.
  click('#models [data-theory-preset="pk"]');
  assert.ok($('#ex-assumptions [data-assumed="a"]'));
  assert.equal($('#models [data-theory-preset="pk"]').disabled, true);

  // Only the principle list offers the category expander; the box does not compete with it.
  assert.equal($$('#models .ex-head [data-expand-categories]').length <= 1, true);

  assert.deepEqual(errors, []);
  console.log("PASS: the Assumptions box lists the explorer's assumptions in its own words, flags what the others settle with proofs, counts what follows beyond the fixed background, keeps its disclosures open, and holds the contradiction; the principle list says why a settled principle follows or is ruled out; names sort with a leading symbol after the bare name; a principle's page lists the results concluding it before those using it.");
} finally { pages.forEach(p => p.window.close()); }
