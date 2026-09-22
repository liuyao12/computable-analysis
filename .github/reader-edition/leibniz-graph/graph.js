'use strict';
const model=JSON.parse(document.querySelector('#graph-data').textContent),NS='http://www.w3.org/2000/svg';
const colors=['#a45032','#326493','#7755a0','#397858'];
const $=s=>document.querySelector(s);let route='all',svg,box,initialBox,drag;
function el(tag,text,cls){const n=document.createElement(tag);if(text!==undefined)n.textContent=text;if(cls)n.className=cls;return n;}
function se(tag,attrs,text){const n=document.createElementNS(NS,tag);for(const[k,v]of Object.entries(attrs))n.setAttribute(k,v);if(text!==undefined)n.textContent=text;return n;}
function showBundle(id){const d=model.nodes.find(n=>n.id===id);document.querySelectorAll('[data-node]').forEach(n=>{n.classList.toggle('selected',n.dataset.node===id);n.setAttribute('aria-pressed',String(n.dataset.node===id));});
 const p=$('#map-detail');p.replaceChildren(el('span',d.tag.toUpperCase(),'role'),el('h2',d.title),el('p',d.formula,'formula'),el('p',d.body,'strategy'));
 const details=el('details'),list=el('ul',undefined,'source-list');details.append(el('summary','Formal sources ('+d.refs.length+')'));
 for(const r of d.refs){const li=el('li'),a=el('a',r.label+' ↗');a.href=r.url;a.target='_blank';a.rel='noopener';li.append(a);list.append(li);}details.append(list);p.append(details);
 if(d.routes.includes(2))p.append(el('p','This branch uses Mathlib’s completed real numbers. The graph does not claim a formal bridge to our interval programs.','native-boundary'));
 if(id==='historical'){const a=el('a','Read the historical reconstruction →');a.href='leibniz-transmutation.html';p.append(a);}
}
function showEdge(e){const a=model.nodes.find(n=>n.id===e.source),b=model.nodes.find(n=>n.id===e.target),p=$('#map-detail');p.replaceChildren(el('span','MATHEMATICAL DEPENDENCY','role'),el('h2',a.title+' → '+b.title),el('p','This arrow summarizes how the prerequisite bundle contributes to the argument. Its source references are available in the two bundles; it is not an extracted declaration-path witness.','strategy'));
 for(const d of [a,b]){const bt=el('button','Open '+d.title);bt.onclick=()=>showBundle(d.id);p.append(bt);}if(e.target==='historical'&&e.source==='bounds')p.append(el('p','Power integration is shared with the Taylor/FTC route. The geometric comparison is supplied by finite transmutation.'));
}
function useBox(){svg.setAttribute('viewBox',box.join(' '));}function fit(){box=[...initialBox];useBox();}function zoom(f){box=[box[0]+box[2]*(1-f)/2,box[1]+box[3]*(1-f)/2,box[2]*f,box[3]*f];useBox();}
function render(){const ns=model.nodes.filter(n=>route==='all'||n.routes.includes(+route)),ids=new Set(ns.map(n=>n.id)),es=model.edges.filter(e=>ids.has(e.source)&&ids.has(e.target));const positions=new Map();
 if(route==='all'){for(const n of ns)positions.set(n.id,{x:25+n.col*285,y:40+n.row*122,w:260+(n.span-1)*285,h:82});initialBox=[0,0,1165,760];}
 else{for(let row=0;row<6;row++){const rn=ns.filter(n=>n.row===row);rn.forEach((n,i)=>positions.set(n.id,{x:25+i*295,y:35+row*122,w:270,h:82}));}const cols=Math.max(...[0,1,2,3,4,5].map(r=>ns.filter(n=>n.row===r).length));initialBox=[0,0,cols*295+25,755];}
 svg=se('svg',{'aria-label':'Mathematical dependencies of the Leibniz proofs',role:'group'});const defs=se('defs',{});for(let i=0;i<4;i++){const m=se('marker',{id:'arrow-'+i,viewBox:'0 0 10 10',refX:9,refY:5,markerWidth:5,markerHeight:5,orient:'auto'});m.append(se('path',{d:'M0 0L10 5L0 10z',fill:colors[i]}));defs.append(m);}svg.append(defs);
 for(const e of es){const a=positions.get(e.source),b=positions.get(e.target),common=model.nodes.find(n=>n.id===e.source).routes.filter(r=>model.nodes.find(n=>n.id===e.target).routes.includes(r));const rs=route==='all'?common:[+route];const g=se('g',{class:'edge','data-edge':e.source+'->'+e.target,tabindex:0,role:'button','aria-label':'Inspect dependency'});const x=a.x+a.w/2,y=a.y+a.h,X=b.x+b.w/2,Y=b.y-3;let d;
 if(Y-y<80)d=`M${x} ${y}C${x} ${y+18} ${X} ${Y-18} ${X} ${Y}`;
 else{const channel=(a.x<=b.x?Math.min(a.x,b.x)-10:Math.max(a.x+a.w,b.x+b.w)+10);d=`M${x} ${y}L${x} ${y+10}L${channel} ${y+10}L${channel} ${Y-10}L${X} ${Y-10}L${X} ${Y}`;}
 rs.forEach((r,i)=>g.append(se('path',{d,transform:`translate(${(i-(rs.length-1)/2)*2},0)`,fill:'none',stroke:colors[r],'stroke-width':1.3,'marker-end':`url(#arrow-${r})`})));
 g.append(se('path',{d,fill:'none',class:'hit'}));g.onclick=()=>showEdge(e);g.onkeydown=x=>{if(x.key==='Enter'||x.key===' '){x.preventDefault();showEdge(e);}};svg.append(g);}
 for(const n of ns){const p=positions.get(n.id),g=se('g',{class:'node','data-node':n.id,'data-family':n.routes.includes(2)?'mathlib':'native',transform:`translate(${p.x},${p.y})`,role:'button',tabindex:0,'aria-label':n.title,'aria-pressed':'false'});g.append(se('rect',{width:p.w,height:p.h,rx:5}));const words=n.title.split(' '),lines=[''];for(const w of words){if((lines.at(-1)+' '+w).length>(p.w>300?60:29))lines.push('');lines[lines.length-1]+=(lines.at(-1)?' ':'')+w;}lines.forEach((t,i)=>g.append(se('text',{x:p.w/2,y:lines.length===1?33:25+i*18},t)));g.append(se('text',{x:p.w/2,y:65,class:'subtitle'},n.subtitle));g.onclick=()=>showBundle(n.id);g.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();showBundle(n.id);}};svg.append(g);}
 $('#svg-holder').replaceChildren(svg);fit();svg.onwheel=e=>{e.preventDefault();zoom(Math.exp(e.deltaY*.001));};svg.onpointerdown=e=>{if(e.target.closest('[data-node],[data-edge]'))return;drag={x:e.clientX,y:e.clientY,box:[...box]};svg.setPointerCapture(e.pointerId);};svg.onpointermove=e=>{if(!drag)return;const r=svg.getBoundingClientRect(),scale=Math.max(box[2]/r.width,box[3]/r.height);box=[drag.box[0]-(e.clientX-drag.x)*scale,drag.box[1]-(e.clientY-drag.y)*scale,...drag.box.slice(2)];useBox();};for(const ev of ['pointerup','pointercancel'])svg.addEventListener(ev,()=>drag=null);
 showBundle(({0:'computational',1:'taylor',2:'mathlib',3:'historical'})[route]||'historical');
}
function setRoute(r){route=r;document.querySelectorAll('[data-route]').forEach(b=>{b.classList.toggle('active',b.dataset.route===r);b.setAttribute('aria-pressed',String(b.dataset.route===r));});render();}
for(const b of document.querySelectorAll('[data-route]'))b.onclick=()=>setRoute(b.dataset.route);
$('#zoom-in').onclick=()=>zoom(.76);$('#zoom-out').onclick=()=>zoom(1/.76);$('#reset-map').onclick=fit;
const requested=new URLSearchParams(location.search).get('route');setRoute(['0','1','2','3'].includes(requested)?requested:'all');
