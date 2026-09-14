'use strict';
const $ = s => document.querySelector(s), NS='http://www.w3.org/2000/svg';
const fmt = n => Number(n).toLocaleString('en-US');
const colors={shared:'#54796d',direct:'#a25336',ftc:'#385fa3',auxiliary:'#8c729e'};
let data, nodes, mode='overview', selected=null, focusIds=[], baseBox, box, dragging=null;
function el(tag,attrs={},text){const e=document.createElementNS(NS,tag);for(const [k,v] of Object.entries(attrs))e.setAttribute(k,v);if(text!==undefined)e.textContent=text;return e;}
function html(tag,text,cls){const e=document.createElement(tag);if(text!==undefined)e.textContent=text;if(cls)e.className=cls;return e;}
function role(n){return n.direct&&n.ftc?'shared':n.direct?'direct':n.ftc?'ftc':'auxiliary';}
function refs(n){return [...new Set([...n.bodyRefs,...n.typeRefs])];}
function allow(n){const r=$('#route').value;return r==='both'||(r==='shared'?n.direct&&n.ftc:n[r]);}
function sourceURL(n){return n.project?`https://github.com/${data.repository}/blob/${data.sourceCommit}/${n.sourcePath}${n.sourceRange?'#L'+n.sourceRange.start+'-L'+n.sourceRange.end:''}`:`https://github.com/leanprover/lean4/blob/v${data.leanVersion}/src/${n.module.replaceAll('.','/')}.lean`;}
function metrics(){
 const d=data.summary.direct,f=data.summary.ftc;
 const rows=[
 ['Final proof: Expr tree nodes','rootTreeNodes','Stored body only; named prerequisites are not unfolded.',false],
 ['Final proof: distinct subexpressions','rootDagNodes','Structural sharing within that body.',false],
 ['Project declarations in closure','projectDeclarations','Includes root, definitions, and compiler-generated helpers.',false],
 ['Exclusive project declarations','exclusiveProjectDeclarations','Absent from the other proof’s closure.',false],
 ['Closure body size: distinct subexpressions','projectBodyDagNodes','Sum per declaration, each declaration counted once.',false],
 ['Closure body size: expanded tree nodes','projectBodyTreeNodes','Counts repeated subexpressions with multiplicity.',true],
 ['Exclusive body size: distinct subexpressions','exclusiveBodyDagNodes','Only declarations exclusive to this path.',true],
 ['Reachable declaration source lines','reachableSourceLines','Union of mapped ranges; blank lines and comments excluded.',true],
 ['Exclusive declaration source lines','exclusiveSourceLines','Union over exclusive declarations; formatting-dependent.',true],
 ['Final theorem source lines','rootSourceLines','Includes the signature; comments and blank lines excluded.',true],
 ['All referenced declarations','allDeclarations','Also includes Lean’s external arithmetic and logical library.',true],
 ['Collected axiom dependencies','axiomCount','Standard Lean and existing native-computation assumptions.',true],
 ['Final proof kernel recheck (median)','kernelMedianMs','11 synchronous trials, loaded prerequisites; not a cold build.',true]
 ];
 const body=$('#metrics tbody');body.replaceChildren();
 for(const [label,key,desc,extra] of rows){const tr=html('tr');if(extra)tr.className='extra';for(const v of [label,key==='kernelMedianMs'?d[key].toFixed(3)+' ms':fmt(d[key]),key==='kernelMedianMs'?f[key].toFixed(3)+' ms':fmt(f[key]),desc])tr.append(html('td',v));body.append(tr);}
 $('#interpretation').textContent=`${fmt(data.summary.shared.projectDeclarations)} project declarations are shared (${(100*data.summary.shared.jaccard).toFixed(1)}% of the union). The final direct proof is smaller, but expanding repeated subexpressions reverses the closure-size comparison. There is no single “shorter proof” score.`;
}
function showNode(id){
 const n=nodes.get(id);if(!n)return;selected=id;
 document.querySelectorAll('.node').forEach(g=>g.classList.toggle('selected',g.dataset.id===id));
 const p=$('#inspector');p.replaceChildren();p.append(html('p',role(n).replace('auxiliary','companion result').replace('shared','shared dependency'),'tag'),html('h3',n.name.split('.').pop()),html('p',n.name,'name'));
 const a=html('a','Open pinned Lean source');a.href=sourceURL(n);a.target='_blank';a.rel='noopener';p.append(a);
 const dl=html('dl');for(const [k,v] of [['Module',n.module],['Declaration',n.kind],['Stored body: tree nodes',fmt(n.bodyTreeNodes)],['Stored body: distinct subexpressions',fmt(n.bodyDagNodes)],['Direct body references',fmt(n.bodyRefs.length)],['Type-only references',fmt(n.typeRefs.filter(x=>!n.bodyRefs.includes(x)).length)],['Mapped source lines',n.sourceRange?fmt(n.sourceLines):'No source range (usually generated)']]){dl.append(html('dt',k),html('dd',v));}p.append(dl);
 if(role(n)==='auxiliary')p.append(html('p','This is a companion consequence, outside both final proof closures. It is not charged to either proof.','note'));
 const b=html('button','Explore this declaration');b.onclick=()=>{focusIds=[id];setMode('detail');};p.append(b);
 const usedBy=[...nodes.values()].filter(v=>refs(v).includes(id)&&v.project);
 p.append(html('h3','Referenced project declarations'));
 for(const x of refs(n).map(x=>nodes.get(x)).filter(v=>v?.project))appendDep(p,x);
 p.append(html('h3','Project users'));
 for(const x of usedBy.slice(0,30))appendDep(p,x);
 if(usedBy.length>30)p.append(html('p',`Showing 30 of ${usedBy.length} users.`,'note'));
 const bench=data.summary[n.direct&&!n.ftc?'direct':'ftc'];
 if(data.roots.includes(id)){
  const details=html('details'),s=html('summary',`Trust report: ${bench.axiomCount} collected axioms`);details.append(s);
  for(const ax of bench.axioms)details.append(html('p',ax,'name'));p.append(details);
 }
}
function appendDep(p,n){const b=html('button',n.name.replace('ComputableAnalysis.',''),'dep-link');b.onclick=()=>showNode(n.id);p.append(b);}
function showEdge(e){const p=$('#inspector');p.replaceChildren();p.append(html('h3',e.witness.length===2?'Direct reference':'Contracted reference path'));
 p.append(html('p',`${e.witness.length-1} reference edge${e.witness.length>2?'s':''}. Every next declaration’s stored body or type references the previous declaration. This is syntactic dependence, not a claim that no alternative proof exists.`));
 const list=html('ol');for(const id of e.witness){const li=html('li'),n=nodes.get(id);const b=html('button',n.name.replace('ComputableAnalysis.',''),'dep-link');b.onclick=()=>showNode(id);li.append(b);list.append(li);}p.append(list);}
function setMode(m){mode=m;document.querySelectorAll('[data-mode]').forEach(x=>x.classList.toggle('active',x.dataset.mode===m));$('#depth-label').hidden=m!=='detail';render();}
function neighborhood(){
 const roots=focusIds.length?focusIds:data.roots.filter(id=>allow(nodes.get(id)));
 const depth=Number($('#depth').value),dist=new Map(),queue=[];
 for(const r of roots){dist.set(r,0);queue.push(r);}
 let truncated=false;
 for(let i=0;i<queue.length;i++){
  const id=queue[i],level=dist.get(id);if(level>=depth)continue;
  for(const dep of refs(nodes.get(id))){const n=nodes.get(dep);if(!n?.project||(!allow(n)&&!roots.includes(dep)))continue;
   if(!dist.has(dep)){if(dist.size>=160){truncated=true;continue;}dist.set(dep,level+1);queue.push(dep);}
  }
 }
 const layers=Array.from({length:depth+1},()=>[]);for(const [id,d] of dist)layers[d].push(id);
 for(const row of layers)row.sort((a,b)=>role(nodes.get(a)).localeCompare(role(nodes.get(b)))||nodes.get(a).name.localeCompare(nodes.get(b).name));
 const width=Math.max(600,...layers.map(l=>l.length*210));let ns=[];
 layers.forEach((row,l)=>row.forEach((id,i)=>ns.push({id,label:nodes.get(id).name.split('.').slice(-1)[0],x:(width-row.length*210)/2+i*210+105,y:l*160+45,w:195,h:62})));
 const edges=[];for(const [id] of dist)for(const dep of refs(nodes.get(id)))if(dist.has(dep))edges.push({source:dep,target:id,witness:[dep,id],type:!nodes.get(id).bodyRefs.includes(dep)});
 return {width,height:(depth+1)*160,nodes:ns,edges,truncated};
}
function render(){
 if(!data)return;
 let g=mode==='overview'?($('#companions').checked?data.overviewSupplement:data.overview):neighborhood();
 let ns=g.nodes.filter(n=>mode==='detail'||allow(nodes.get(n.id))||(role(nodes.get(n.id))==='auxiliary'&&$('#companions').checked&&$('#route').value==='both'));
 const ids=new Set(ns.map(n=>n.id)),edges=g.edges.filter(e=>ids.has(e.source)&&ids.has(e.target));
 const svg=$('#graph');svg.replaceChildren(el('title',{},'Measured dependencies of two Lean proofs'));
 const defs=el('defs'),marker=el('marker',{id:'arrow',viewBox:'0 0 10 10',refX:9,refY:5,markerWidth:6,markerHeight:6,orient:'auto-start-reverse'});marker.append(el('path',{d:'M 0 0 L 10 5 L 0 10 z',fill:'#9ca9b0'}));defs.append(marker);svg.append(defs);
 const bypos=new Map(ns.map(n=>[n.id,n]));
 for(const e of edges){const s=bypos.get(e.source),t=bypos.get(e.target);const up=s.y>t.y;const y1=s.y+(up?-s.h/2:s.h/2),y2=t.y+(up?t.h/2:-t.h/2),mid=(y1+y2)/2;
  const path=el('path',{d:`M${s.x},${y1} C${s.x},${mid} ${t.x},${mid} ${t.x},${y2}`,class:'edge'+(e.type?' type':''),'marker-end':'url(#arrow)'});path.onclick=ev=>{ev.stopPropagation();showEdge(e);};path.append(el('title',{},`${e.witness.length-1} actual reference edge(s); click for witness`));svg.append(path);
 }
 for(const n of ns){const info=nodes.get(n.id),r=role(info),group=el('g',{class:'node'+(selected===n.id?' selected':''),transform:`translate(${n.x-n.w/2},${n.y-n.h/2})`,tabindex:0,role:'button','aria-label':info.name,'data-id':n.id});
 group.append(el('rect',{width:n.w,height:n.h,rx:6,stroke:colors[r]}));group.append(el('rect',{width:4,height:n.h-16,x:0,y:8,style:`fill:${colors[r]};stroke:none`} ));
 const words=n.label.replaceAll('_',' ').replace(/([a-z])([A-Z])/g,'$1 $2').split(' ').flatMap(w=>w.match(/.{1,27}/g)||[]);let lines=[''];for(const word of words){if((lines[lines.length-1]+' '+word).length>29&&lines[lines.length-1])lines.push('');lines[lines.length-1]+=(lines[lines.length-1]?' ':'')+word;}
 if(lines.length>3)lines[2]=lines[2].slice(0,26)+'…';
 lines=lines.slice(0,3);const txt=el('text',{x:n.w/2,y:n.h/2-(lines.length-1)*7+1,'text-anchor':'middle'});lines.forEach((s,i)=>txt.append(el('tspan',{x:n.w/2,dy:i?14:0},s)));group.append(txt);
 group.append(el('title',{},`${info.name}\n${fmt(info.bodyTreeNodes)} stored body tree nodes\n${r}`));
 group.onclick=e=>{e.stopPropagation();showNode(n.id);};group.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();showNode(n.id);}};svg.append(group);}
 if(ns.length){const xmin=Math.min(...ns.map(n=>n.x-n.w/2))-20,xmax=Math.max(...ns.map(n=>n.x+n.w/2))+20,ymin=Math.min(...ns.map(n=>n.y-n.h/2))-25,ymax=Math.max(...ns.map(n=>n.y+n.h/2))+25;baseBox=[xmin,ymin,xmax-xmin,ymax-ymin];}else baseBox=[0,0,600,400];
 fit();$('#graph-status').textContent=`${ns.length} visible declarations · ${edges.length} ${mode==='overview'?'contracted paths':'direct reference edges'}${g.truncated?' · capped at 160 nodes; focus or reduce depth':''}`;
 $('#view-note').textContent=mode==='overview'?'An overview of selected milestones. Edges may pass through hidden declarations; click any edge for its exact witness. The shared statement is shown above, not duplicated as two different integrals.':'Actual body/type references within the selected neighborhood. Dashed edges occur in the declaration type only. External Lean declarations remain in the downloadable full graph and search.';
}
function zoom(factor){if(!box)return;box=[box[0]+box[2]*(1-factor)/2,box[1]+box[3]*(1-factor)/2,box[2]*factor,box[3]*factor];applyBox();}
function fit(){if(!baseBox)return;box=[...baseBox];applyBox();}
function applyBox(){$('#graph').setAttribute('viewBox',box.join(' '));}
function bind(){
 document.querySelectorAll('[data-mode]').forEach(b=>b.onclick=()=>{if(b.dataset.mode==='detail'&&mode!=='detail')focusIds=[];setMode(b.dataset.mode);});
 for(const id of ['route','companions','depth'])$('#'+id).onchange=()=>{if(id==='route')focusIds=[];render();};
 $('#zoom-in').onclick=()=>zoom(.72);$('#zoom-out').onclick=()=>zoom(1/.72);$('#fit').onclick=fit;$('#toggle-metrics').onclick=()=>{$('#metrics').classList.toggle('more');$('#toggle-metrics').textContent=$('#metrics').classList.contains('more')?'Fewer measurements':'More measurements';};
 $('#fullscreen').onclick=()=>{$('#graph-section').classList.toggle('expanded');$('#fullscreen').textContent=$('#graph-section').classList.contains('expanded')?'Close expanded graph':'Expand graph';fit();};
 document.addEventListener('keydown',e=>{if(e.key==='Escape'){$('#graph-section').classList.remove('expanded');$('#fullscreen').textContent='Expand graph';$('#search-results').style.display='none';}});
 $('#search').oninput=()=>{const q=$('#search').value.trim().toLowerCase(),p=$('#search-results');p.replaceChildren();p.style.display=q?'block':'none';if(!q)return;const result=[...nodes.values()].filter(n=>n.name.toLowerCase().includes(q)).sort((a,b)=>Number(b.project)-Number(a.project)||a.name.length-b.name.length).slice(0,24);for(const n of result){const b=html('button',n.name);b.onclick=()=>{p.style.display='none';showNode(n.id);focusIds=[n.id];$('#route').value='both';setMode('detail');};p.append(b);}if(!result.length)p.append(html('p','No declaration matches.'));};
 const svg=$('#graph');svg.addEventListener('wheel',e=>{e.preventDefault();if(!box)return;const r=svg.getBoundingClientRect(),factor=Math.exp(e.deltaY*.001);const px=(e.clientX-r.left)/r.width,py=(e.clientY-r.top)/r.height;box=[box[0]+box[2]*px*(1-factor),box[1]+box[3]*py*(1-factor),box[2]*factor,box[3]*factor];applyBox();},{passive:false});
 svg.onpointerdown=e=>{if(e.target.closest('.node')||e.target.closest('.edge'))return;dragging={x:e.clientX,y:e.clientY,box:[...box]};svg.setPointerCapture(e.pointerId);svg.classList.add('dragging');};svg.onpointermove=e=>{if(!dragging)return;const r=svg.getBoundingClientRect(),scale=Math.max(box[2]/r.width,box[3]/r.height);box=[dragging.box[0]-(e.clientX-dragging.x)*scale,dragging.box[1]-(e.clientY-dragging.y)*scale,...dragging.box.slice(2)];applyBox();};svg.onpointerup=()=>{dragging=null;svg.classList.remove('dragging');};svg.onpointercancel=svg.onpointerup;
}
async function init(){try{const r=await fetch('data.json');if(!r.ok)throw Error(`Measurements returned HTTP ${r.status}`);data=await r.json();nodes=new Map(data.nodes.map(n=>[n.id,n]));$('#provenance').replaceChildren(html('span',`Lean ${data.leanVersion} · Measured source `));const a=html('a',data.sourceCommit.slice(0,12));a.href=`https://github.com/${data.repository}/commit/${data.sourceCommit}`;$('#provenance').append(a,html('span',' · pinned proof snapshot, not a whole-repository build badge'));for(const text of ['Identical theorem types','Neither proof calls the other','No sorryAx in either closure'])$('#checks').append(html('span',text));metrics();bind();render();showNode(data.roots[1]);}catch(e){$('#fatal').hidden=false;$('#fatal').textContent='Could not load proof measurements: '+e.message;}}
init();
