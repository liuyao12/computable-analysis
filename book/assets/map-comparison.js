/* Paired theorem costs beside the graph, independent of selected display nodes. */
'use strict';
window.ProofMapComparison = (() => {
  let names={direct:'Direct inequalities',ftc:'Concave FTC',mathlib:'Mathlib + bridges'};
  const origins={native:'Computable-analysis',bridge:'Comparison bridges',mathlib:'Mathlib',lean:'Lean / Std',other:'Other dependencies'};
  let data,panel,config,active='all';
  const el=(tag,text,cls)=>{const e=document.createElement(tag);if(text!==undefined)e.textContent=text;if(cls)e.className=cls;return e;};
  const fmt=n=>Number(n).toLocaleString('en-US');
  const query=s=>panel.querySelector(s);
  function select(id,label,options){
    const l=el('label',label),s=el('select');s.id=id;
    for(const [value,text] of options){const o=el('option',text);o.value=value;s.append(o);}
    s.addEventListener('change',draw);l.append(s);return l;
  }
  function row(body,title,values,cls){
    const tr=el('tr',undefined,cls);tr.append(el('th',title));
    for(const v of values)tr.append(el('td',v));body.append(tr);
  }
  function draw(){
    const c=data.cases[query('#pm-case').value],base=query('#pm-baseline').value;
    const cards=query('.pm-cards');cards.replaceChildren();
    for(const r of data.routeOrder){
      const x=c.routes[r].costs[base],card=el('div',undefined,'pm-card');card.dataset.pmRoute=r;
      card.append(el('h2',names[r]));
      const numbers=el('p',undefined,'pm-numbers');
      numbers.append(el('strong',fmt(x.declarations),'pm-declarations'),el('span',' declarations'));
      numbers.append(el('br'),el('strong',fmt(x.codeLines),'pm-loc'),el('span',' mapped LOC'));
      card.append(numbers,el('p',fmt(x.mappedDeclarations)+' / '+fmt(x.declarations)+' declarations source-mapped','pm-coverage'));cards.append(card);
    }
    const detail=query('#pm-breakdown');detail.replaceChildren();
    const scroll=el('div',undefined,'pm-table-scroll'),table=el('table'),head=el('thead'),body=el('tbody');
    const hr=el('tr');hr.append(el('th','Measured source component'));
    for(const r of data.routeOrder){const th=el('th',names[r]+' — declarations / LOC');hr.append(th);}head.append(hr);
    row(body,'Final theorem declaration(s): LOC',data.routeOrder.map(r=>fmt(c.routes[r].finalApplication.codeLines)));
    for(const [o,label] of Object.entries(origins)){
      row(body,label,data.routeOrder.map(r=>{const s=c.routes[r].costs[base].origins[o];return fmt(s.declarations)+' / '+(s.mappedDeclarations?fmt(s.codeLines):s.declarations?'unmapped':'0');}));
    }
    row(body,'Total at this baseline',data.routeOrder.map(r=>{const s=c.routes[r].costs[base];return fmt(s.declarations)+' / '+fmt(s.codeLines);}), 'pm-total');
    row(body,'Declarations without source coverage',data.routeOrder.map(r=>fmt(c.routes[r].costs[base].unmappedDeclarations)));
    table.append(head,body);scroll.append(table);detail.append(scroll);
    const baseline=(data.baselineDescriptions||{full:'Full transitive type/body dependencies, including the objects in the statement.',
      'statement-free':`The statement’s prerequisite union (${fmt(c.baselines.statementDeclarations)} declarations) is treated as already available.`,
      'shared-free':`The common prerequisite intersection (${fmt(c.baselines.sharedDeclarations)} declarations) is treated as already available.`})[base];
    detail.append(el('p',baseline+' Each referenced declaration is counted once. Source LOC unions overlapping ranges and excludes blank lines and comments. It includes supporting definitions and proof scripts, not only the final theorem.','pm-method'));
    detail.append(el('p','LOC is partial where compiler source ranges or source files are unavailable; “unmapped” is not zero work. Generated helpers are included in declaration counts. These measurements do not rank conceptual simplicity, and an import count is not used as a substitute.','pm-method'));
    if(query('#pm-case').value==='combined')detail.append(el('p','Identity plus convergence is one calculus example with two obligations. Dependencies shared by those obligations are charged once.','pm-method'));
    const links=el('p',undefined,'pm-method');
    for(const [href,text] of [['proof-bench/','Full comparison protocol'],[config.url,'Exact values and source coverage']]){
      const a=el('a',text);a.href=href;a.target='_blank';a.rel='noopener';links.append(a,document.createTextNode('  '));
    }
    links.append(document.createTextNode('Source '+data.sourceCommit.slice(0,12)));detail.append(links);setRoute(active);
  }
  function setRoute(route){active=route;if(!panel)return;
    for(const e of panel.querySelectorAll('[data-pm-route]'))e.classList.toggle('pm-active',route!=='all'&&e.dataset.pmRoute===['direct','ftc','mathlib'][Number(route)]);
  }
  async function init(model,entry){
    config=entry.comparison||(entry.id==='thm:c3-primitive'?model.mapComparison:null);if(!config)return;
    panel=el('section',undefined,'pm-comparison');panel.id='proof-comparison';panel.setAttribute('aria-label','Declaration and source line comparison');
    document.querySelector('.map-toolbar').after(panel);
    try{
      const response=await fetch(config.url);if(!response.ok)throw Error('HTTP '+response.status);
      data=await response.json();if(data.routeLabels)names=data.routeLabels;if(data.sourceCommit!==model.sourceCommit)throw Error('Different source revisions; reload the page.');
      const controls=el('div',undefined,'pm-controls');controls.append(el('strong','Proof comparison'));
      controls.append(select('pm-case','Obligation',data.caseOptions||[
        ['identity','Endpoint identity'],['validity','Convergence certificate'],['combined','Identity + convergence']]));
      controls.append(select('pm-baseline','Count',data.baselineOptions||[
        ['full','Full used library'],['statement-free','Beyond statement prerequisites'],['shared-free','Beyond shared prerequisites']]));
      const cards=el('div',undefined,'pm-cards');cards.style.gridTemplateColumns='repeat('+data.routeOrder.length+',minmax(0,1fr))';
      const more=el('details',undefined,'pm-more');more.id='pm-more';more.append(el('summary','Breakdown, source coverage, and counting method'));
      const breakdown=el('div');breakdown.id='pm-breakdown';more.append(breakdown);
      panel.append(controls,cards,more);if(config.defaultCase)query('#pm-case').value=config.defaultCase;draw();
    }catch(e){panel.replaceChildren(el('p','Comparison unavailable: '+e.message+'. No cached numbers are substituted.','pm-error'));}
  }
  return {init,setRoute};
})();

// Mount independently: the proof explorer can render even if metrics fail.
async function mountProofMapComparison(){
  try{
    const response=await fetch('reading/maps.json');if(!response.ok)return;
    const model=await response.json();
    const id=new URLSearchParams(location.search).get('theorem')||'thm:c3-primitive';
    const entry=model.theorems[id];if(!entry)return;
    await window.ProofMapComparison.init(model,entry);
    const holder=document.querySelector('#svg-holder');
    if(holder){
      const sync=()=>window.ProofMapComparison.setRoute(holder.dataset.view||'all');
      new MutationObserver(sync).observe(holder,{attributes:true,attributeFilter:['data-view']});sync();
    }
  }catch(e){console.warn('Map comparison could not be initialized:',e.message);}
}
if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',mountProofMapComparison,{once:true});
else mountProofMapComparison();
