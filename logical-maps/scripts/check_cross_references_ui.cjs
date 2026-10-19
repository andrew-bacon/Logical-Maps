// NODE_PATH=/path/to/node_modules node scripts/check_cross_references_ui.cjs
// [[id]] or [[id|text]] in a record's prose links to another record's page, and
// each page lists the records whose prose refers to it.
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {JSDOM,VirtualConsole}=require('jsdom');
const root=path.resolve(__dirname,'..');
const template=fs.readFileSync(path.join(root,'viewer/template.html'),'utf8');
const cert={source_id:'paper',lean:'none',produced_by:'Fixture',checked_by:[]};
const rule=(id,premises,conclusion,proof)=>({id,premises,conclusion,status:'proved',certificate:cert,sources:['Fixture'],source_names:['Fixture'],proof});
const data={topic:{id:'xref',title:'Cross-reference fixture',background:[],source_catalog:[{id:'paper',name:'Paper',kind:'published-paper'}]},
  principles:['a','b','na','nb'].map(id=>({id,name:id.replace(/^n/,'□').toUpperCase(),statement:'Statement of '+id})),
  results:[rule('ab',['a'],'b','Direct.'),
    rule('nanb',['na'],'nb','The boxed form of [[ab]]; see also [[m|the model]], [[na]] and [[missing]].')],
  models:[{id:'m',name:'Fixture model',status:'proved',satisfies:['a'],violates:[],certificate:cert,sources:['Fixture'],source_names:['Fixture'],description:'Compare [[ab]].'}]};
const errors=[],vc=new VirtualConsole();vc.on('jsdomError',e=>errors.push(e));
const dom=new JSDOM(template.replace('/*__PMAP_DATA__*/null',()=>JSON.stringify(data)),
  {url:'https://maps.example/',runScripts:'dangerously',pretendToBeVisual:true,virtualConsole:vc});
const w=dom.window,d=w.document;
try{
  w.eval('openPage({type:"result", id:"nanb"})');
  const page=d.getElementById('page');
  const links=[...page.querySelectorAll('.prose button.xref')];
  assert.deepEqual(links.map(b=>Object.keys(b.dataset)[0]),['openResult','openModel','openPrinciple'],'Each reference opens the page of its kind');
  assert.equal(links[0].textContent.replace(/\s+/g,' ').trim(),'A ⇒ B','A result is labelled by its statement');
  assert.equal(links[1].textContent,'the model','Given text replaces the label');
  assert.equal(links[2].textContent,'□A','A principle by its name');
  assert.match(page.querySelector('.prose').textContent,/and missing\./,'An unknown id is left as text');
  links[0].click();
  assert.equal(page.querySelector('h1').textContent.replace(/\s+/g,' ').trim(),'A ⇒ B','The link opens the result');
  const back=[...page.querySelectorAll('h2')].find(h=>h.textContent==='Referenced by');
  assert.ok(back,'The referred-to page lists who refers to it');
  const refs=[...back.nextElementSibling.querySelectorAll('button.xref')];
  assert.deepEqual(refs.map(b=>b.dataset.openResult||b.dataset.openModel),['nanb','m']);
  page.querySelector('#page-back').click();
  assert.equal(page.querySelector('h1').textContent.replace(/\s+/g,' ').trim(),'□A ⇒ □B','← back returns to the referring page');
  w.eval('openPage({type:"principle", id:"b"})');
  assert.ok(![...page.querySelectorAll('h2')].some(h=>h.textContent==='Referenced by'),'No section when nothing refers to the page');
  assert.equal(errors.length,0,errors.map(String).join('\n'));
  console.log('check_cross_references_ui: OK');
}finally{w.close();}
