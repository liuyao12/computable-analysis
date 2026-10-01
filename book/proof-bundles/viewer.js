'use strict';
const catalogue=JSON.parse(document.querySelector('#proof-bundle-data').textContent),$=s=>document.querySelector(s),NS='http://www.w3.org/2000/svg';
let graph,route='all',selected,graphWidth=900;
function el(tag,text,cls){const e=document.createElement(tag);if(text!==undefined)e.textContent=text;if(cls)e.className=cls;return e;}
function se(tag,attrs,text){const e=document.createElementNS(NS,tag);for(const[k,v]of Object.entries(attrs))e.setAttribute(k,v);if(text!==undefined)e.textContent=text;return e;}
function number(n){return n.toLocaleString('en-US');}
function locLabel(n){return n.loc.codeLines===null?'LOC pending':number(n.loc.codeLines)+(n.loc.scope==='Source files'?' file LOC':' linked LOC');}
function selectNode(id){selected=id;const n=graph.nodes.find(n=>n.id===id),panel=$('#bundle-detail');document.querySelectorAll('.bundle-node').forEach(e=>e.setAttribute('aria-pressed',String(e.dataset.node===id)));
 panel.replaceChildren(el('span',n.status==='pending'?'PROOF PENDING':n.status.toUpperCase(),'classic-tag'),el('h3',n.title),el('p',locLabel(n),'bundle-loc'),el('p',n.body));
 if(n.boundary)panel.append(el('p',n.boundary));
 if(n.mathHtml){const math=el('div');math.innerHTML=n.mathHtml;panel.append(math);window.MathJax?.typesetPromise?.([math]).catch(()=>{});}
 if(n.sources.length){const details=el('details'),ul=el('ul');details.open=true;details.append(el('summary','Counted sources ('+n.loc.measuredSources+' files)'));
  for(const ref of n.sources){const li=el('li'),a=el('a',ref.label);a.href=ref.url+(ref.start===null?'':'#L'+ref.start+'-L'+ref.end);a.target='_blank';a.rel='noopener';li.append(a,el('div',ref.start===null?'Whole source file':'Recorded span: lines '+ref.start+'–'+ref.end));const record=catalogue.sources[ref.url];li.append(el('span',record?'SHA-256 '+record.sha256:'Source not measured','bundle-hash'));ul.append(li);}details.append(ul);panel.append(details);}
 if(n.declarations.length){const d=el('details');d.append(el('summary','Declaration names ('+n.declarations.length+')'));for(const name of n.declarations){const p=el('p');p.append(el('code',name));d.append(p);}panel.append(d);}
 if(n.status==='pending')panel.append(el('p','No completed proof is claimed for this bundle.'));
}
function ranks(nodes,edges){const rank=new Map(nodes.map(n=>[n.id,0]));for(let k=0;k<nodes.length;k++){let changed=false;for(const e of edges){const r=rank.get(e.source)+1;if(rank.get(e.target)<r){rank.set(e.target,r);changed=true;}}if(!changed)return rank;}throw Error('The bundled graph contains a cycle.');}
function render(){try{
 const nodes=graph.nodes.filter(n=>route==='all'||n.routes.includes(route)),ids=new Set(nodes.map(n=>n.id)),edges=graph.edges.filter(e=>ids.has(e.source)&&ids.has(e.target));const rank=ranks(nodes,edges),positions=new Map();let row=0,maxColumns=1;
 for(const level of [...new Set(rank.values())].sort((a,b)=>a-b)){const ns=nodes.filter(n=>rank.get(n.id)===level);ns.forEach((n,i)=>positions.set(n.id,{x:20+(i%3)*290,y:25+(row+Math.floor(i/3))*155}));row+=Math.ceil(ns.length/3);maxColumns=Math.max(maxColumns,Math.min(3,ns.length));}
 const width=maxColumns*290+10,height=Math.max(190,row*155+25),svg=se('svg',{viewBox:'0 0 '+width+' '+height,role:'group','aria-label':'Bundled dependencies of '+graph.title});svg.style.width=graphWidth+'px';
 const defs=se('defs',{}),m=se('marker',{id:'bundle-arrow',viewBox:'0 0 10 10',refX:9,refY:5,markerWidth:5,markerHeight:5,orient:'auto'});m.append(se('path',{d:'M0 0L10 5L0 10z',fill:'#96a99c'}));defs.append(m);svg.append(defs);
 for(const e of edges){const a=positions.get(e.source),b=positions.get(e.target),x=a.x+130,y=a.y+118,X=b.x+130,Y=b.y;const p=se('path',{d:`M${x} ${y} C${x} ${y+20} ${X} ${Y-20} ${X} ${Y}`,class:'bundle-edge'+(graph.nodes.find(n=>n.id===e.target).status==='pending'?' pending':''),'marker-end':'url(#bundle-arrow)','data-edge':e.source+'->'+e.target});p.append(se('title',{},'Prerequisite: '+e.source+' → '+e.target));svg.append(p);}
 const max=Math.max(1,...nodes.map(n=>n.loc.codeLines||0));
 for(const n of nodes){const p=positions.get(n.id),g=se('g',{transform:`translate(${p.x},${p.y})`,class:'bundle-node','data-node':n.id,'data-status':n.status,'data-family':n.sources.some(r=>r.url.includes('leanprover-community'))?'mathlib':'native',tabindex:0,role:'button','aria-label':n.title+'; '+locLabel(n),'aria-pressed':'false'});g.append(se('rect',{width:260,height:118,rx:5,class:'bundle-card'}));
 const lines=[''];for(const w of n.title.split(' ')){if((lines.at(-1)+' '+w).length>30)lines.push('');lines[lines.length-1]+=(lines.at(-1)?' ':'')+w;}lines.slice(0,3).forEach((t,i)=>g.append(se('text',{x:13,y:25+i*18},t)));
 g.append(se('text',{x:13,y:86,class:'bundle-badge'},locLabel(n)),se('text',{x:247,y:86,class:'bundle-node-status','text-anchor':'end'},n.status==='registered'?'Source linked':n.status));
 if(n.loc.codeLines!==null){g.append(se('rect',{x:13,y:99,width:234,height:5,class:'bundle-bar-bg'}));g.append(se('rect',{x:13,y:99,width:234*n.loc.codeLines/max,height:5,class:'bundle-bar'}));}
 g.onclick=()=>selectNode(n.id);g.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();selectNode(n.id);}};svg.append(g);}
 $('#bundle-canvas').replaceChildren(svg);
 const total=route==='all'?graph.loc:graph.routes.find(r=>r.id===route).loc;
 $('#bundle-total').textContent=(total.codeLines===null?'No complete LOC inventory':'Measured sources: '+number(total.codeLines)+' unique LOC')+' · '+total.pendingBundles+' pending bundles · '+total.unmeasuredBundles+' unmeasured bundles. Shared lines counted once; imports are not included automatically.';
 selectNode(nodes.some(n=>n.id===selected)?selected:nodes.at(-1).id);
 }catch(e){$('#bundle-canvas').replaceChildren(el('p',e.message,'bundle-error'));}}
function setRoute(id){route=id;for(const b of document.querySelectorAll('[data-bundle-route]'))b.setAttribute('aria-pressed',String(b.dataset.bundleRoute===route));const u=new URL(location.href);u.searchParams.set('theorem',graph.id);if(id==='all')u.searchParams.delete('route');else u.searchParams.set('route',id);history.replaceState(null,'',u);render();}
function setGraph(id,requested='all'){graph=catalogue.graphs.find(g=>g.id===id)||catalogue.graphs[0];$('#bundle-theorem').value=graph.id;$('#bundle-title').textContent=graph.title;$('#bundle-status').textContent=graph.status;$('#bundle-return').href=graph.page+'#'+graph.anchor;$('#bundle-semantics').textContent=graph.edgeSemantics;
 const toolbar=$('#bundle-routes');toolbar.replaceChildren();for(const r of [{id:'all',name:'All routes'},...graph.routes]){const b=el('button',r.name+(r.status==='pending'?' · pending':''));b.type='button';b.dataset.bundleRoute=r.id;b.onclick=()=>setRoute(r.id);toolbar.append(b);}selected=undefined;setRoute(graph.routes.some(r=>r.id===requested)?requested:'all');document.title=graph.title+' · Bundled proofs';}
for(const g of catalogue.graphs){const option=el('option',g.title+' — '+g.page);option.value=g.id;$('#bundle-theorem').append(option);const li=el('li'),a=el('a',g.title);a.href='proof-bundles.html?theorem='+encodeURIComponent(g.id);li.append(a);$('#bundle-index').append(li);}
$('#bundle-theorem').onchange=e=>setGraph(e.target.value);$('#bundle-zoom-in').onclick=()=>{graphWidth=Math.min(2400,graphWidth*1.2);$('#bundle-canvas svg').style.width=graphWidth+'px';};$('#bundle-zoom-out').onclick=()=>{graphWidth=Math.max(520,graphWidth/1.2);$('#bundle-canvas svg').style.width=graphWidth+'px';};$('#bundle-fit').onclick=()=>{graphWidth=Math.max(520,$('#bundle-canvas').clientWidth-4);$('#bundle-canvas svg').style.width=graphWidth+'px';};
const params=new URLSearchParams(location.search);setGraph(params.get('theorem')||'showcase:zeta-zeros',params.get('route')||'all');
