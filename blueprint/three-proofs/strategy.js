'use strict';
// Decorate the existing blueprint box, preserving the exact Lean snippets and
// their highlighting/copy behavior. The first thing shown remains Lean code.
const originalAddLeanPanel = addLeanPanel;
addLeanPanel = function(modal,id) {
  originalAddLeanPanel(modal,id);
  const item=proofGraphData.nodeDetails[id],guide=item.strategy;
  if(!guide)return;
  const panel=modal.querySelector('.bp-lean-panel');
  for(const record of item.declarations){
    const card=[...panel.querySelectorAll('.bp-declaration-card')].find(c=>c.dataset.declaration===record.name);
    if(!card||!record.ownerModule)continue;
    card.querySelector('.bp-card-footer').after(element('p','Namespace: '+(record.namespace||'(root)')+' · Source module: '+record.ownerModule,'bp-note bp-provenance'));
    if(record.namespace==='ComputableAnalysis.CosinePrimitive' && ['A','pi','inversePi','S','C','integral','endpoint'].includes(record.name.split('.').pop()))
      card.append(element('p','CosinePrimitive is a namespace, not a call to the primitive theorem. This definition is in the proof-independent data module.','bp-note bp-namespace'));
    const note=card.querySelector('.bp-companion-note');
    if(note)note.textContent='Shown for explanation; not referenced by name in the three measured proof closures. A definitionally identical underlying program may still be used.';
  }
  const strategy=element('section',undefined,'bp-strategy');
  strategy.append(element('strong',guide.role),element('p',guide.summary));
  if(guide.formula){
    const relation=element('details',undefined,'bp-key-relation');
    const formula=guide.formula.replaceAll('\\llbracket','\\lbrack\\!\\lbrack').replaceAll('\\rrbracket','\\rbrack\\!\\rbrack');
    relation.append(element('summary','Key relation (LaTeX)'),element('div','\\['+formula+'\\]'));
    relation.ontoggle=()=>{if(relation.open&&window.MathJax?.typesetPromise)window.MathJax.typesetPromise([relation]).catch(()=>{});};
    strategy.append(relation);
  }
  const first=panel.querySelector('.bp-declaration-card');first.after(strategy);
  for(const [index,group] of [...panel.querySelectorAll('.bp-declaration-group')].entries()){
    const note=element('p',guide.groups[group.dataset.group],'bp-step-purpose');
    if(index===0)strategy.after(note);else group.querySelector('.bp-group-heading').after(note);
  }
  const nav=element('nav',undefined,'bp-node-navigation');nav.setAttribute('aria-label','Navigate proof strategy');
  for(const [heading,field,match] of [['Prerequisites','source','target'],['Used next by','target','source']]){
    const labels=[...new Set(proofGraphData.witnesses.filter(e=>e[match]===id&&(view==='all'||view==='companions'||String(e.route)===view)).map(e=>e[field]))];
    if(!labels.length)continue;
    nav.append(element('strong',heading));
    for(const label of labels){
      const b=element('button',proofGraphData.nodeDetails[label].title);b.type='button';
      b.onclick=()=>{
        const node=[...document.querySelectorAll('#graph .node')].find(g=>g.querySelector('title').textContent.trim()===label);
        if(node)node.dispatchEvent(new MouseEvent('click',{bubbles:true}));
      };
      nav.append(b);
    }
  }
  panel.append(nav);
};
