// NODE_PATH=/path/to/node_modules node scripts/check_minor_changes_ui.cjs
// The Changes tab hides changes entries marked minor (housekeeping) unless asked.
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {JSDOM,VirtualConsole}=require('jsdom');
const root=path.resolve(__dirname,'..');
const template=fs.readFileSync(path.join(root,'viewer/template.html'),'utf8');
const cert={source_id:'paper',lean:'none',produced_by:'Fixture',checked_by:[],date:'2026-01-01'};
const data={topic:{id:'minor',title:'Minor changes fixture',background:[],source_catalog:[{id:'paper',name:'Paper',kind:'published-paper'}]},
  principles:[{id:'a',name:'A',statement:'Statement of A',date:'2026-01-01',changes:[
      {date:'2026-02-01',by:'Fixture',summary:'Corrected the statement.'},
      {date:'2026-03-01',by:'Fixture',summary:'Reworded the notes.',minor:true}]},
    {id:'b',name:'B',statement:'Statement of B',date:'2026-01-01'}],
  results:[{id:'ab',premises:['a'],conclusion:'b',status:'proved',certificate:cert,sources:['Fixture'],source_names:['Fixture'],
    changes:[{date:'2026-03-02',by:'Fixture',summary:'Linked the boxed form.',minor:true}]}],
  models:[]};
const errors=[],vc=new VirtualConsole();vc.on('jsdomError',e=>errors.push(e));
const dom=new JSDOM(template.replace('/*__PMAP_DATA__*/null',()=>JSON.stringify(data)),{url:'https://maps.example/',runScripts:'dangerously',pretendToBeVisual:true,virtualConsole:vc});
const w=dom.window,d=w.document;
try{
  d.querySelector('.tab[data-tab="results"]').click();
  const rows=()=>[...d.querySelectorAll('#results tr')].map(tr=>tr.querySelector('.stmt').textContent.replace(/\s+/g,' ').trim());
  const toggle=d.getElementById('show-minor');
  assert.equal(toggle.checked,false,'Minor changes start hidden');
  assert.ok(!rows().some(r=>/Reworded|Linked/.test(r)),'Minor entries are not listed');
  assert.ok(rows().some(r=>/Corrected the statement/.test(r)),'Other entries are');
  assert.equal(d.getElementById('n-results').textContent,String(rows().length),'The tab counts what it shows');
  assert.equal(d.getElementById('n-minor').textContent,'2','The checkbox says how many it hides');
  toggle.checked=true;toggle.dispatchEvent(new w.Event('change',{bubbles:true}));
  assert.ok(rows().some(r=>/Reworded the notes/.test(r))&&rows().some(r=>/Linked the boxed form/.test(r)),'Checking it lists them');
  assert.equal(d.querySelectorAll('#results tr.minor').length,2,'Marked as minor');
  assert.equal(d.getElementById('n-results').textContent,String(rows().length));
  assert.deepEqual(errors.map(String),[]);
  console.log('PASS: the Changes tab hides minor changes entries unless asked, says how many, and counts what it shows.');
}finally{w.close();}
