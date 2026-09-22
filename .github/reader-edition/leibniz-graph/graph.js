'use strict';
(async function () {
  const root = document.getElementById('graph');
  const panel = document.getElementById('detail-content');
  const NS = 'http://www.w3.org/2000/svg';
  const model = JSON.parse(document.getElementById('graph-data').textContent);
  const byId = new Map(model.nodes.map(n => [n.id, n]));
  let route = 'all', selected = null;
  const el = (tag, text, cls) => { const e = document.createElement(tag); if (text !== undefined) e.textContent = text; if (cls) e.className = cls; return e; };
  const svgEl = (tag, attrs, text) => { const e = document.createElementNS(NS, tag); Object.entries(attrs).forEach(([k,v]) => e.setAttribute(k,v)); if (text !== undefined) e.textContent = text; return e; };
  const family = n => n.routes.length > 1 ? 'shared' : ['native','ftc','mathlib'][n.routes[0]];
  const wrap = (s, length) => { const lines = ['']; for (const w of s.split(' ')) { if ((lines.at(-1)+' '+w).length > length && lines.at(-1)) lines.push(''); lines[lines.length-1] += (lines.at(-1) ? ' ' : '')+w; } return lines; };
  const visible = () => model.nodes.filter(n => route === 'all' || n.routes.includes(Number(route)));
  function highlight() {
    const ancestors = new Set();
    function visit(id) { if (ancestors.has(id)) return; ancestors.add(id); model.edges.filter(e => e.target===id).forEach(e => visit(e.source)); }
    if (selected) visit(selected);
    root.querySelectorAll('.node').forEach(g => { g.classList.toggle('selected',g.dataset.node===selected); g.classList.toggle('dim',Boolean(selected)&&!ancestors.has(g.dataset.node)); g.setAttribute('aria-pressed',String(g.dataset.node===selected)); });
    root.querySelectorAll('.edge').forEach(p => { const on=ancestors.has(p.dataset.source)&&ancestors.has(p.dataset.target); p.classList.toggle('dim',Boolean(selected)&&!on); p.classList.toggle('active',Boolean(selected)&&on); });
  }
  function select(id, scroll=false) {
    selected=id; const n=byId.get(id); panel.replaceChildren(el('p',n.tag,'eyebrow'),el('h2',n.title),el('p',n.formula,'formula'),el('p',n.body));
    for (const [heading,edges,key] of [['Builds on',model.edges.filter(e=>e.target===id),'source'],['Used to establish',model.edges.filter(e=>e.source===id),'target']]) {
      if (!edges.length) continue; const section=el('div',undefined,'dependencies'); section.append(el('h3',heading));
      for (const edge of edges) { const target=byId.get(edge[key]); const button=el('button',target.title); button.onclick=()=>{ if(route!=='all'&&!target.routes.includes(Number(route))) setRoute('all'); select(target.id); }; section.append(button); }
      panel.append(section);
    }
    const sources=el('details',undefined,'source-detail'); sources.append(el('summary','Supporting Lean sources')); const list=el('ul',undefined,'source-list');
    for (const ref of n.refs) { const li=el('li'); const a=el('a',ref.label+' ↗'); a.href=ref.url; a.target='_blank'; a.rel='noopener'; li.append(a); list.append(li); } sources.append(list); panel.append(sources);
    highlight();
    if (scroll && innerWidth <=760) document.getElementById('bundle-details').scrollIntoView({behavior:matchMedia('(prefers-reduced-motion: reduce)').matches?'auto':'smooth'});
  }
  function render() {
    const nodes=visible(); const single=route!=='all'; const pos=new Map();
    const width=single?410:960; const gap=single?126:133; const height=single?nodes.length*gap+28:6*gap+35;
    nodes.forEach((n,i)=>pos.set(n.id,{x:single?27:18+n.col*318,y:single?14+i*gap:30+n.row*gap,w:single?350:(n.span===2?606:288),h:104}));
    root.classList.toggle('single',single);
    const svg=svgEl('svg',{viewBox:`0 0 ${width} ${height}`,role:'group','aria-label':single?model.routes[Number(route)].name+' mathematical dependencies':'Three mathematical proof routes'});
    const defs=svgEl('defs',{}); const marker=svgEl('marker',{id:'arrow',viewBox:'0 0 10 10',refX:9,refY:5,markerWidth:6,markerHeight:6,orient:'auto-start-reverse'}); marker.append(svgEl('path',{d:'M0 0 L10 5 L0 10 z',fill:'#82958a'})); defs.append(marker); svg.append(defs);
    if (!single) model.routes.forEach((r,i)=>svg.append(svgEl('text',{x:24+i*318,y:16,class:'lane-title'},r.name.toUpperCase())));
    for (const [i,e] of model.edges.entries()) {
      const a=pos.get(e.source),b=pos.get(e.target); if (!a||!b)continue;
      const ax=a.x+a.w/2,ay=a.y+a.h+1,bx=b.x+b.w/2,by=b.y-3;
      let path;
      if(by-ay<gap-10) path=`M${ax} ${ay} C${ax} ${ay+14} ${bx} ${by-14} ${bx} ${by}`;
      else { const side=(i%2===0?1:-1); const channel=side===1?Math.max(a.x+a.w,b.x+b.w)+7:Math.min(a.x,b.x)-7; path=`M${ax} ${ay} L${ax} ${ay+9} L${channel} ${ay+9} L${channel} ${by-10} L${bx} ${by-10} L${bx} ${by}`; }
      svg.append(svgEl('path',{d:path,class:'edge '+family(byId.get(e.target)),'data-source':e.source,'data-target':e.target,'marker-end':'url(#arrow)'}));
    }
    for (const n of nodes) {
      const p=pos.get(n.id); const g=svgEl('g',{class:'node'+(n.tag==='Conclusion'?' result':''),'data-node':n.id,'data-family':family(n),transform:`translate(${p.x} ${p.y})`,role:'button',tabindex:0,'aria-label':n.title+': '+n.subtitle,'aria-pressed':'false'});
      g.append(svgEl('rect',{width:p.w,height:p.h,rx:7})); g.append(svgEl('text',{x:14,y:20,class:'tag'},n.tag.toUpperCase()));
      const titles=wrap(n.title,p.w>400?60:33); titles.forEach((t,j)=>g.append(svgEl('text',{x:14,y:43+j*19,class:'title'},t)));
      const subtitles=wrap(n.subtitle,p.w>400?75:43); subtitles.forEach((t,j)=>g.append(svgEl('text',{x:14,y:titles.length>1?80+j*14:68+j*14,class:'subtitle'},t)));
      g.append(svgEl('text',{x:p.w-21,y:21,class:'open-mark'},'+'));
      g.addEventListener('click',()=>select(n.id,true)); g.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();select(n.id,true);}});svg.append(g);
    }
    root.replaceChildren(svg); highlight();
  }
  function setRoute(value) { route=value; selected=null; document.querySelectorAll('[data-route]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.route===route)));render();document.getElementById('graph-scroll').scrollTo(0,0);document.getElementById('map-help').textContent=route==='all'?'Read arrows from premises to conclusions. Shared bundles feed both native routes.':'One route, including its shared prerequisites. Select a bundle for its mathematical contents.'; }
  document.querySelectorAll('[data-route]').forEach(b=>b.onclick=()=>{setRoute(b.dataset.route);select(route==='all'?'computational':['computational','taylor','mathlib'][Number(route)]);});
  document.getElementById('reset-selection').onclick=()=>{selected=null;highlight();panel.replaceChildren(el('p','Explore the argument','eyebrow'),el('h2','Select a mathematical bundle'),el('p','Select any node to highlight the ideas it builds on and read its explanation. Use the route buttons to follow one proof at a time.'));};
  window.addEventListener('beforeprint',()=>{document.getElementById('reading-outline').open=true;});
  render();
})();
