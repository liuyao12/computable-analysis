// A partly verified mathematical plan is not a fully extracted proof graph.
const cartwrightOriginalBundle = showBundle;
const cartwrightOriginalEdge = showEdge;
showBundle = function(id) {
  cartwrightOriginalBundle(id);
  if(!entry.outlineGraph)return;
  const bundle=model.bundles[id],panel=document.querySelector('#map-detail');
  if(!bundle.declarations.length)panel.querySelector('.bundle-lean')?.remove();
  const status=node('p',bundle.proofStatus==='checked'?
    'Checked arithmetic component. This does not certify the planned moment or irrationality theorem.':
    'Planned mathematical step. No Lean proof or measured proof length is claimed for this node.','map-missing');
  panel.querySelector('h2').after(status);
  document.querySelectorAll('[data-route]').forEach((button,i)=>{
    button.hidden=false;button.textContent=['All proposed routes','Direct (planned)','FTC (planned)','Mathlib (planned)'][i];
  });
  document.querySelector('.map-legend').replaceChildren(node('span','Green: checked arithmetic'),node('span','Outline: planned'),node('span','Dashed arrows: proposed uses'));
  if(!document.querySelector('#cartwright-costs')){
    const costs=model.cartwrightPlan.metrics.sharedUnion;
    const section=node('section',undefined,'pm-comparison');section.id='cartwright-costs';
    const f=n=>Number(n).toLocaleString('en-US');
    section.append(node('strong','Measured common arithmetic'),node('p',f(costs.declarations)+' referenced declarations · '+f(costs.mappedLOC)+' mapped project LOC · '+f(costs.mappedDeclarations)+' / '+f(costs.declarations)+' declarations source-mapped.'),
      node('p','Middle proof lengths: direct — · FTC — · Mathlib —. These routes are not yet implemented; no complete irrationality proof is measured.'));
    const link=node('a','Detailed accounting and mathematical boundary ↗');link.href='cartwright.html#cost';link.target='_blank';link.rel='noopener';section.append(link);
    document.querySelector('.map-toolbar').after(section);
  }
};
showEdge = function(raw) {
  if(!entry.outlineGraph){cartwrightOriginalEdge(raw);return;}
  const [s,t]=raw.split('->');
  const records=model.witnesses.filter(e=>e.map===entry.id&&e.source===s&&e.target===t&&(route==='all'||e.route===null||String(e.route)===route));
  const panel=document.querySelector('#map-detail');panel.replaceChildren();
  for(const e of records){
    panel.append(node('span',e.planned?'PROPOSED USE — NOT A CHECKED DEPENDENCY':'CHECKED ARITHMETIC DEPENDENCY','role'),node('h2',e.label),node('p',e.note,'strategy'));
    if(e.witness.length){const list=node('ol',undefined,'edge-list');for(const name of e.witness)list.append(node('li',name));panel.append(list);}
  }
};
