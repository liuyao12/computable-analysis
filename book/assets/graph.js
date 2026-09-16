'use strict';
const $=s=>document.querySelector(s),NS='http://www.w3.org/2000/svg';
let model,entry,route='all',svg,initialBox,box,drag,selected,request=0;
function node(tag,text,cls){const e=document.createElement(tag);if(text!==undefined)e.textContent=text;if(cls)e.className=cls;return e;}
function se(tag,attrs,text){const e=document.createElementNS(NS,tag);for(const[k,v]of Object.entries(attrs))e.setAttribute(k,v);if(text!==undefined)e.textContent=text;return e;}
function latex(element){if(window.MathJax?.typesetPromise)window.MathJax.typesetPromise([element]).catch(()=>{});else setTimeout(()=>{if(element.isConnected&&window.MathJax?.typesetPromise)window.MathJax.typesetPromise([element]).catch(()=>{});},800);}
function leanText(d){let t=d.kind+' '+d.name+' : '+d.type;if(d.value!==null&&d.value!==undefined)t+=' :=\n'+d.value;return t;}
function showBundle(id){
 selected=id;document.querySelectorAll('[data-node]').forEach(n=>n.classList.toggle('selected',n.dataset.node===id));
 const panel=$('#map-detail');panel.replaceChildren();
 if(!entry.checkedComparison){const d=entry.nodes.find(x=>x.id===id);panel.append(node('span','EDITORIAL READING OUTLINE','role'),node('h2',d.title));if(d.mathHtml){const body=node('div',undefined,'math-body');body.innerHTML=d.mathHtml;panel.append(body);latex(body);}panel.append(node('p',d.text,'strategy'),node('p','This map explains the manuscript argument. It is not an extracted Lean dependency graph. No Mathlib comparison is registered for this statement yet.','map-missing'));if(id==='conclusion'&&entry.proofIdea){const details=node('details');details.append(node('summary','Original proof idea'));const div=node('div',undefined,'math-body');div.innerHTML=entry.proofIdea;details.append(div);details.ontoggle=()=>{if(details.open)latex(div);};panel.append(details);}return;}
 const d=model.bundles[id];if(!d)return;
 panel.append(node('span',d.strategy?.role||'MATHEMATICAL BUNDLE','role'),node('h2',d.title));
 if(d.mathHtml){const div=node('div',undefined,'math-body');div.innerHTML=d.mathHtml;panel.append(div);latex(div);}
 if(d.strategy?.summary)panel.append(node('p',d.strategy.summary,'strategy'));
 const details=node('details',undefined,'bundle-lean');details.append(node('summary',`Exact Lean statements (${d.declarations.length})`));
 for(const group of d.groups){const section=node('section',undefined,'lean-group');section.append(node('h3',group.title));
  if(d.strategy?.groups[group.title])section.append(node('p',d.strategy.groups[group.title],'strategy'));
  for(const name of group.names){const dec=d.declarations.find(x=>x.name===name);if(!dec)continue;
   const card=node('div',undefined,'lean-card'+(dec.realDependencyPath?.length?' mathlib':''));
   const top=node('div',undefined,'card-top'),label=node('span',dec.realDependencyPath?.length?'Uses Mathlib’s real':'Native / no Mathlib-real reference'),copy=node('button','Copy');top.append(label,copy);card.append(top);
   const pre=node('pre'),code=node('code',leanText(dec));pre.append(code);card.append(pre);window.LeanSnippet?.highlight(code);
   copy.onclick=async()=>{try{await navigator.clipboard.writeText(code.textContent);copy.textContent='Copied';setTimeout(()=>copy.textContent='Copy',1000);}catch{copy.textContent='Select text to copy';}};
   const a=node('a','Pinned Lean source ↗','source');a.href=dec.sourceUrl;a.target='_blank';a.rel='noopener';card.append(a,node('p',dec.ownerModule||'', 'module'));section.append(card);
  }details.append(section);
 }panel.append(details);
 if(id==='thm:c3-primitive'){const a=node('a','Compare the size and dependencies of these proofs ↗','map-compare');a.href='proof-bench/';a.target='_top';panel.append(a);}
 const p=node('p','Proof snapshot '+model.proofSourceCommit.slice(0,12),'');p.id='map-status';panel.append(p);
}
function showEdge(raw){
 const [s,t]=raw.split('->');
 const paths=model.witnesses.filter(e=>e.source===s&&e.target===t&&
   (e.kind==='statement'||route==='all'||String(e.route)===route));
 const statement=paths.some(e=>e.kind==='statement'),proof=paths.some(e=>e.kind==='proof');
 const panel=$('#map-detail');
 panel.replaceChildren(node('span',statement?'USED IN THE STATEMENT':proof?'USED IN A PROOF':'CONSTRUCTING THE OBJECTS','role'),
   node('h2',statement?'What the theorem is about':proof?'A step in the proof':'A definition dependency'));
 panel.append(node('p',statement?
   'These gray dashed arrows explain the objects occurring in the common proposition. Their paths unfold definitions only; no proof of the theorem is used. They remain visible in every proof route.':proof?
   'This colored arrow records use in a proof or certificate body, not merely a reference in its theorem type. Intermediate declarations can be hidden by the bundle. It does not assert that this prerequisite is logically indispensable.':
   'This neutral arrow belongs to the construction of an object or to the type of a declaration, rather than a chosen proof route.','strategy'));
 for(const e of paths){
  const label=e.kind==='statement'?({S:'Sine in the endpoint',C:'Cosine in the integral',pi:'The arctangent-defined pi',integral:'The integral computation'}[e.input]):
    e.route===null?'Companion':['Direct','Native FTC','Mathlib'][e.route];
  panel.append(node('h3',label));
  if(e.note)panel.append(node('p',e.note,'strategy'));
  const details=node('details'),list=node('ol',undefined,'edge-list');
  details.append(node('summary','Exact declaration path'));
  for(const name of e.witness)list.append(node('li',name));
  details.append(list);panel.append(details);
 }
 if(!paths.length)panel.append(node('p','No witness for this display edge.','map-missing'));
}
function useBox(){svg?.setAttribute('viewBox',box.join(' '));}
function zoom(f){box=[box[0]+box[2]*(1-f)/2,box[1]+box[3]*(1-f)/2,box[2]*f,box[3]*f];useBox();}
function fit(){box=[...initialBox];useBox();}
function attach(){svg=$('#svg-holder svg');initialBox=svg.getAttribute('viewBox').split(/[ ,]+/).map(Number);fit();
 for(const g of svg.querySelectorAll('[data-node]')){g.addEventListener('click',()=>showBundle(g.dataset.node));g.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();showBundle(g.dataset.node);}});}
 for(const e of svg.querySelectorAll('[data-edge]')){e.addEventListener('click',()=>showEdge(e.dataset.edge));e.addEventListener('keydown',x=>{if(x.key==='Enter')showEdge(e.dataset.edge);});}
 svg.addEventListener('wheel',e=>{e.preventDefault();zoom(Math.exp(e.deltaY*.001));},{passive:false});
 svg.addEventListener('pointerdown',e=>{if(e.target.closest('[data-node],[data-edge]'))return;drag={x:e.clientX,y:e.clientY,box:[...box]};svg.setPointerCapture(e.pointerId);svg.classList.add('dragging');});
 svg.addEventListener('pointermove',e=>{if(!drag)return;const r=svg.getBoundingClientRect(),scale=Math.max(box[2]/r.width,box[3]/r.height);box=[drag.box[0]-(e.clientX-drag.x)*scale,drag.box[1]-(e.clientY-drag.y)*scale,...drag.box.slice(2)];useBox();});
 for(const ev of ['pointerup','pointercancel'])svg.addEventListener(ev,()=>{drag=null;svg.classList.remove('dragging');});
}
async function render(){const ticket=++request;if(entry.checkedComparison){const r=await fetch(entry.views[route]);if(!r.ok)throw Error('Could not load graph');const text=await r.text();if(ticket!==request)return;$('#svg-holder').innerHTML=text;}else{
 const s=se('svg',{viewBox:`0 0 480 ${entry.nodes.length*160+50}`,'aria-label':'Editorial mathematical outline'});const defs=se('defs',{}),marker=se('marker',{id:'arrow',viewBox:'0 0 10 10',refX:8,refY:5,markerWidth:5,markerHeight:5,orient:'auto'});marker.append(se('path',{d:'M0,0L10,5L0,10Z',fill:'#89968f'}));defs.append(marker);s.append(defs);
 entry.nodes.forEach((n,i)=>{if(i)s.append(se('path',{d:`M240 ${i*160-45} L240 ${i*160+15}`,stroke:'#89968f','stroke-dasharray':'4 3','marker-end':'url(#arrow)'}));const g=se('g',{'data-node':n.id,tabindex:0,role:'button','aria-label':n.title,class:'node concept-node',transform:`translate(75,${i*160+20})`});g.append(se('rect',{width:330,height:94,rx:5}));const words=n.title.split(' '),lines=[''];for(const word of words){if((lines.at(-1)+' '+word).length>34)lines.push('');lines[lines.length-1]+=(lines.at(-1)?' ':'')+word;}lines.forEach((t,j)=>g.append(se('text',{x:165,y:43+j*19},t)));s.append(g);});$('#svg-holder').replaceChildren(s);
 }attach();$('#svg-holder').dataset.view=route;showBundle(entry.checkedComparison?'thm:c3-primitive':'conclusion');}
async function init(){try{const r=await fetch('reading/maps.json');if(!r.ok)throw Error('No proof map data');model=await r.json();const id=new URLSearchParams(location.search).get('theorem')||'thm:c3-primitive';entry=model.theorems[id];if(!entry)throw Error('This theorem does not yet have a registered map. Return to the chapter.');$('#map-title').textContent=entry.title;$('#map-subtitle').textContent=entry.status;$('#return-text').href=entry.page+'#'+entry.id; if(window.parent!==window)$('#return-text').onclick=e=>{e.preventDefault();window.parent.postMessage('close-proof-map',location.origin);}; document.title=entry.title+' · Proof map';
 if(!entry.checkedComparison){for(const b of document.querySelectorAll('[data-route]'))b.hidden=true;document.querySelector('.map-legend').replaceChildren(node('span','Editorial arrows · not a checked dependency claim'));}
 for(const b of document.querySelectorAll('[data-route]'))b.onclick=()=>{route=b.dataset.route;document.querySelectorAll('[data-route]').forEach(x=>x.classList.toggle('active',x===b));render().catch(fail);};
 $('#zoom-in').onclick=()=>zoom(.76);$('#zoom-out').onclick=()=>zoom(1/.76);$('#reset-map').onclick=fit;
 window.addEventListener('keydown',e=>{if(e.key==='Escape'&&window.parent!==window)window.parent.postMessage('close-proof-map',location.origin);});
 await render();
}catch(e){fail(e);}}
function fail(e){$('#map-detail').replaceChildren(node('p',e.message,'graph-error'));console.error(e);}
init();
