'use strict';
const $=s=>document.querySelector(s), fmt=n=>Number(n).toLocaleString('en-US');
const labels={direct:'Direct inequalities',ftc:'Native FTC',mathlib:'Mathlib + bridges'};
let data;
function el(tag,text,cls){const n=document.createElement(tag);if(text!==undefined)n.textContent=text;if(cls)n.className=cls;return n;}
function addRow(title,values,cls){const tr=el('tr',undefined,cls);tr.append(el('td',title));for(const v of values)tr.append(el('td',v));$('#rows').append(tr);}
function draw(){
 const caseId=$('#case').value,baseline=$('#baseline').value,weight=$('#weight').value;
 const c=data.cases[caseId],routes=Object.keys(c.routes),rr=routes.map(r=>c.routes[r]);
 $('#case-title').textContent=c.contract.title;$('#contract').textContent=c.contract.contract;$('#obligation').textContent=c.contract.obligation;
 $('#theorem-type').textContent=rr[0].type;
 $('#baseline-note').textContent={full:'Full cost includes the specified algorithms and all used prerequisites, including the existing Lean and Mathlib libraries.',
 'statement-free':`The union of the identical statement types’ reference closures is available first: ${fmt(c.statementBaseline.declarations)} declarations. Each route is charged only for references outside that baseline.`,
 'shared-free':`The intersection shared by every alternative in this case is available first: ${fmt(c.sharedBaseline.declarations)} declarations. This shows route-specific material, not total proof cost.`}[baseline];
 $('#head').replaceChildren();const head=el('tr');head.append(el('th','Measured component'));for(const r of routes)head.append(el('th',labels[r]||r));$('#head').append(head);$('#rows').replaceChildren();
 addRow('Final proof: tree / distinct nodes',rr.map(r=>fmt(r.finalBody.bodyTree)+' / '+fmt(r.finalBody.bodyDag)));
 for(const [key,title] of [['native','Native project'],['bridge','Representation / comparison layer'],['mathlib','Mathlib prerequisites'],['lean','Lean / Std prerequisites'],['other','Other dependencies']]){
  addRow(title,rr.map(r=>fmt(r.sizes[baseline].origins[key][weight])),key==='mathlib'?'mathlib-cell':undefined);
 }
 addRow('Total at selected baseline',rr.map(r=>fmt(r.sizes[baseline][weight])),'total');
 addRow('Named declarations',rr.map(r=>fmt(r.sizes[baseline].declarations)));
 addRow('Mapped source code lines',rr.map(r=>fmt(r.sizes[baseline].source.nonblankCodeLines)));
 addRow('Source-mapped / unmapped declarations',rr.map(r=>fmt(r.sizes[baseline].source.mappedDeclarations)+' / '+fmt(r.sizes[baseline].source.unmappedDeclarations)));
 addRow('Axioms: standard / native-computation / other',rr.map(r=>[r.axiomClasses.standard.length,r.axiomClasses.nativeComputation.length,r.axiomClasses.other.length].join(' / ')));
 $('#accounting').textContent='Weight: '+$('#weight').selectedOptions[0].textContent+'. Final proof counts are always local body counts. Axiom lists describe the full proof, independently of the accounting baseline. Source coverage is explicit; unmapped declarations are not treated as zero-code proofs.';
 $('#root-details').replaceChildren();for(const r of rr){const d=el('details');d.append(el('summary',(labels[r.route]||r.route)+': inspect costs and trust'),el('pre',r.root),el('p','Largest supporting bodies outside the statement prerequisites (distinct subexpressions; definitions and generated helpers included):'));
  const list=el('ol');for(const n of r.largestBodies)list.append(el('li',fmt(n.bodyDag)+' · '+n.name));d.append(list);
  const a=el('details');a.append(el('summary','All '+r.axioms.length+' collected axiom dependencies'));const al=el('ul');for(const n of r.axioms)al.append(el('li',n));a.append(al);d.append(a);$('#root-details').append(d);
 }
 $('#portfolio').replaceChildren();for(const [route,p] of Object.entries(data.portfolio)){const tr=el('tr');tr.append(el('td',labels[route]||route));for(const s of p.steps)tr.append(el('td',fmt(s.added[weight])));tr.append(el('td',fmt(p.total[weight])),el('td',$('#weight').selectedOptions[0].textContent));$('#portfolio').append(tr);}
}
async function init(){try{const response=await fetch('data.json');if(!response.ok)throw Error('HTTP '+response.status);data=await response.json();$('#revision').textContent='Lean '+data.leanVersion+' · checked source '+data.sourceCommit.slice(0,12)+' · '+fmt(data.uniqueMeasuredDeclarations)+' distinct referenced declarations across the suite';
 for(const [key,c] of Object.entries(data.cases)){const o=el('option',c.contract.title);o.value=key;$('#case').append(o);}$('#case').value='cosine-primitive';
 for(const r of data.roadmap){const block=el('article',undefined,'roadmap-item');const title=el('h3',r.title);title.append(el('span','PLANNED — NOT MEASURED','badge'));block.append(title,el('p',r.contract),el('p',r.reason,'muted'));$('#roadmap').append(block);}
 for(const name of ['case','baseline','weight'])$('#'+name).onchange=draw;draw();
}catch(e){$('#error').hidden=false;$('#error').textContent='Unable to load the checked comparison: '+e.message;}}
init();
