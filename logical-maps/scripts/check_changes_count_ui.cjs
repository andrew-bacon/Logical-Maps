// NODE_PATH=/path/to/node_modules node scripts/check_changes_count_ui.cjs
// The Changes tab counts what is new since the reader's last visit, searches with the Results
// tab's normalised text after typing pauses, and pages long lists.
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {JSDOM,VirtualConsole}=require('jsdom');
const root=path.resolve(__dirname,'..');
const template=fs.readFileSync(path.join(root,'viewer/template.html'),'utf8');
const cert={source_id:'paper',lean:'none',produced_by:'Fixture',checked_by:[],date:'2026-01-01'};
const many=Array.from({length:320},(_,i)=>({id:'p'+i,name:'Principle '+i,statement:'Statement number '+i,date:'2025-06-01'}));
const data={topic:{id:'count',title:'Changes count fixture',background:[],source_catalog:[{id:'paper',name:'Paper',kind:'published-paper'}]},
  principles:[{id:'a',name:'A',statement:'Statement of A',date:'2026-01-01',changes:[
      {date:'2026-02-01',by:'Fixture',summary:'Corrected the statement.'},
      {date:'2026-03-01',by:'Fixture',summary:'Reworded the notes.',minor:true}]},
    {id:'b',name:'B',statement:'Statement of □B',date:'2026-01-01'},...many],
  results:[{id:'ab',premises:['a'],conclusion:'b',status:'proved',certificate:cert,sources:['Fixture'],source_names:['Fixture']}],
  models:[]};
const errors=[],vc=new VirtualConsole();vc.on('jsdomError',e=>errors.push(e));
const dom=new JSDOM(template.replace('/*__PMAP_DATA__*/null',()=>JSON.stringify(data)),{url:'https://maps.example/',runScripts:'dangerously',pretendToBeVisual:true,virtualConsole:vc,
  beforeParse(window){window.localStorage.setItem('logical-maps:count:last-visit','2026-01-15');}});
const w=dom.window,d=w.document;
try{
  d.querySelector('.tab[data-tab="results"]').click();
  const rows=()=>[...d.querySelectorAll('#results tr')].map(tr=>tr.querySelector('.stmt').textContent.replace(/\s+/g,' ').trim());
  assert.equal(d.getElementById('n-results').textContent,'1','One non-minor entry is dated since the stored visit');
  assert.match(d.getElementById('changes-summary').textContent,/^1 change since your last visit on 15 January 2026 · \d+ in all$/);
  assert.equal(d.querySelectorAll('#results tr.new').length,1,'That entry is marked new');
  assert.match(w.localStorage.getItem('logical-maps:count:last-visit'),/^\d{4}-\d{2}-\d{2}$/,'This visit is remembered');
  // Paging: 324 rows shown (325 less one minor), the first 300 at once, the rest on request.
  assert.equal(rows().length,300,'The first page');
  const more=d.getElementById('changes-more');
  assert.ok(more&&/Show the next 24 of 24 more/.test(more.textContent),'A button for the rest');
  more.click();
  assert.equal(rows().length,324,'All rows after the button');
  // Search: shared normalisation, redrawn after typing pauses.
  const box=d.getElementById('search');
  box.value='□b';box.dispatchEvent(new w.Event('input',{bubbles:true}));
  assert.equal(rows().length,324,'Nothing changes while typing');
  w.flushChanges();
  assert.deepEqual(rows(),['B Statement of □B'],'□B finds the statement with the box, as the Results tab would');
  assert.match(d.getElementById('changes-summary').textContent,/· 1 matching$/);
  box.value='corrected';box.dispatchEvent(new w.Event('input',{bubbles:true}));
  w.flushChanges();
  assert.deepEqual(rows(),['A Corrected the statement.','A Statement of A'],'A revision is found by its summary, with its record');
  assert.equal(d.getElementById('n-results').textContent,'1','The badge does not follow the search');
  assert.deepEqual(errors.map(String),[]);
  console.log('PASS: the Changes tab counts what is new since the last visit, searches like the Results tab, and pages.');
}finally{w.close();}
