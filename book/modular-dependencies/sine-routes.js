'use strict';
let sineFocus=null,sineProofPromise=null;
function sine(id='sine-entire-result',focus=null){route='sine';sineFocus=focus;expandedRoots=null;select(id)}
function sineControls(){
  const nav=el('nav');nav.className='sine-route-controls';nav.setAttribute('aria-label','Compare sine proof routes');
  for(const [label,id,focus] of [['Both routes','sine-entire-result',null],['Finite-prefix route','sine-finite-result','sine-finite-result'],['ODE comparison core','sine-ode-core','sine-ode-core'],['Entire ODE identity','sine-entire-result','sine-entire-result'],['Applied ODE route','sine-applied','sine-applied']]){
    const b=el('button',label);b.setAttribute('aria-pressed',String(sineFocus===focus));b.onclick=()=>sine(id,focus);nav.append(b)
  }
  return nav;
}
function sineProofData(){
  if(!sineProofPromise)sineProofPromise=fetch(M.sineFlow.proofDependencies.path).then(r=>{if(!r.ok)throw Error('Checked theorem dependencies unavailable');return r.json()});
  return sineProofPromise;
}
function dependencyNames(data,name,proofOnly=false){
  const seen=new Set(),todo=[name];
  while(todo.length){const x=todo.pop();if(seen.has(x))continue;seen.add(x);const info=data.declarations[x];if(info)todo.push(...info.proofDependencies,...(proofOnly?[]:info.typeDependencies))}
  return seen;
}
function theoremDependencyView(name){
  const d=$('detail');d.replaceChildren(el('h2','Checked declaration dependencies'),el('pre',name),el('p','Loading the extracted Lean proof dependencies…'));
  sineProofData().then(data=>{
    const info=data.declarations[name];if(!info)throw Error('Declaration is outside this exported proof closure.');
    d.replaceChildren(el('h2',info.kind==='theorem'?'Theorem proof dependencies':'Definition dependencies'),el('pre',name),el('p',data.scope));
    const back=el('button','Back to mathematical bundle');back.onclick=()=>select(selected);d.append(back);
    const source=el('button','Inspect defining source module');source.onclick=()=>moduleView(info.module);d.append(source,el('p','Defining module: '+info.module));
    const refs=(title,names)=>{
      const detail=el('details'),sm=el('summary',title+' ('+names.length+')');detail.open=true;detail.append(sm);
      for(const dep of names){const b=el('button',dep);b.className='module';b.onclick=()=>theoremDependencyView(dep);detail.append(b)}
      if(!names.length)detail.append(el('p','No project constants in this part of the declaration.'));
      d.append(detail);
    };
    refs(info.kind==='theorem'?'Direct proof-body dependencies':'Direct definition-body dependencies',info.proofDependencies);
    refs('Constants in the declaration type',info.typeDependencies);
    const closure=dependencyNames(data,name),more=el('details');more.append(el('summary','Search the transitive declaration closure ('+closure.size+')'));
    const search=el('input');search.placeholder='Filter checked declarations';search.setAttribute('aria-label','Filter checked declaration dependencies');
    const list=el('div');function fill(){list.replaceChildren();const found=Array.from(closure).sort().filter(n=>n.toLowerCase().includes(search.value.toLowerCase()));list.append(el('p',found.length+' matches; showing up to 100.'));for(const dep of found.slice(0,100)){const b=el('button',dep);b.className='module';b.onclick=()=>theoremDependencyView(dep);list.append(b)}}
    search.oninput=fill;fill();more.append(search,list);d.append(more);
    if(name==='ComputableAnalysis.ElementarySineODE.computations_agree_global')d.append(el('p','The checked complete project closure, including private proof helpers, contains no earlier elementary sine-agreement theorem. The two solution laws, their initial values and the global uniqueness law are genuine proof dependencies.'));
  }).catch(e=>d.append(el('p',e.message)));
}
function appendSineDetails(n,d){
  d.prepend(sineControls());
  const scope=el('p',M.sineFlow.scope);scope.className='flow-status';d.append(scope);
  const parents=el('section');parents.append(el('h3','Required mathematical bundles'));
  if(!n.parents.length)parents.append(el('p','Foundation bundle.'));
  for(const id of n.parents){const p=M.sineFlow.nodes.find(x=>x.id===id),b=el('button',p.title);b.onclick=()=>select(id);parents.append(b)}
  d.append(parents);
  const users=M.sineFlow.nodes.filter(x=>x.parents.includes(n.id));if(users.length){const next=el('section');next.append(el('h3','Used by'));for(const x of users){const b=el('button',x.title);b.onclick=()=>select(x.id);next.append(b)}d.append(next)}
  if(n.theorems.length){const ts=el('section');ts.append(el('h3','Probe the checked theorem dependencies'));for(const name of n.theorems){const b=el('button',name);b.className='module';b.onclick=()=>theoremDependencyView(name);ts.append(b)}d.append(ts)}
  const trace=el('button','Show only this bundle and its requirements');trace.onclick=()=>sine(n.id,n.id);d.append(trace);
  for(const [title,path] of [['Read the ODE proof and independence audit','sine-ode-audit.txt'],['Read the finite-prefix theorem audit','sine-finite-prefix-audit.txt'],['Read the worked comparison','sine-comparison.html']]){const p=el('p'),a=el('a',title);a.href=path;p.append(a);d.append(p)}
}
