'use strict';
const container = d3.select('#graph');
let view = 'all', activeModal = null, returnFocus = null;
const renderer = container.graphviz({useWorker: true}).fit(true);

function nodeStatus(id) {
  const item = proofGraphData.nodeDetails?.[id];
  if (!item) return 'native';
  if (id === 'thm:c3-primitive' && ['0','1','2'].includes(view)) {
    return item.paths[item.anchors[Number(view)]].length ? 'mathlib' : 'native';
  }
  return item.classification;
}

function element(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function closeStatement() {
  if (activeModal) activeModal.style.display = 'none';
  activeModal = null;
  document.getElementById('statements').style.display = 'none';
  document.body.classList.remove('statement-open');
  if (returnFocus?.isConnected) returnFocus.focus({preventScroll:true});
}

function declarationCard(record, highlighted) {
  const card = element('article', undefined, 'bp-declaration-card');
  const status = record.realDependencyPath.length ? 'mathlib' : 'native';
  card.dataset.declaration = record.name;
  card.dataset.foundation = status;
  if (highlighted) card.classList.add('selected-route');
  const bar = element('div', undefined, 'bp-lean-toolbar');
  bar.append(element('h4', record.name.split('.').pop()));
  const copy = element('button', 'Copy', 'bp-copy');
  copy.type = 'button';
  copy.setAttribute('aria-label', 'Copy '+record.name);
  bar.append(copy); card.append(bar);
  const pre = element('pre', undefined, 'bp-lean-code');
  pre.tabIndex = 0;
  pre.setAttribute('aria-label', 'Exact Lean declaration: '+record.name);
  const code = element('code');
  // These are the exported strings, not client-side paraphrases of the type.
  code.textContent = record.kind+' '+record.name+':\n'+record.type
    +(record.value !== null ? ' :=\n'+record.value : '');
  code.dataset.declaration = record.name;
  pre.append(code); card.append(pre);
  copy.onclick = async () => {
    try { await navigator.clipboard.writeText(code.textContent); copy.textContent='Copied'; }
    catch (_) {
      const range=document.createRange(); range.selectNodeContents(code);
      const selection=window.getSelection(); selection.removeAllRanges();
      selection.addRange(range); copy.textContent='Selected';
    }
  };
  const footer = element('div', undefined, 'bp-card-footer');
  const source = element('a', 'Pinned Lean source', 'bp-formal-source');
  source.href=record.sourceUrl; source.target='_blank'; source.rel='noopener';
  footer.append(source, element('span', status==='mathlib'?'Uses Mathlib ℝ':'Mathlib-free', 'foundation-badge '+status));
  if (highlighted) footer.append(element('span','Selected proof route','bp-route-badge'));
  card.append(footer);
  if (record.displayOnly) {
    card.append(element('p', 'Supporting/companion result: not a prerequisite in the three measured proof closures.', 'bp-note bp-companion-note'));
  }
  if (record.realDependencyPath.length) {
    const details=element('details',undefined,'bp-dependency-details');
    details.append(element('summary','Mathlib ℝ dependency path'));
    const list=element('ol');
    for (const name of record.realDependencyPath) list.append(element('li',name));
    details.append(list);card.append(details);
  }
  return card;
}

function addLeanPanel(modal, id) {
  const item=proofGraphData.nodeDetails?.[id];
  if (!item) return;
  const content=modal.querySelector('.dep-modal-content');
  content.querySelector('.bp-lean-panel')?.remove();
  // Preserve the original blueprint text, but keep the formal declarations first.
  let explanation=content.querySelector(':scope > .bp-math-explanation');
  if (!explanation) {
    explanation=element('details',undefined,'bp-math-explanation');
    explanation.append(element('summary','Mathematical explanation (LaTeX)'));
    for (const child of [...content.children]) {
      if (!child.classList.contains('dep-closebtn')) explanation.append(child);
    }
    content.append(explanation);
    explanation.ontoggle=()=>{
      if (explanation.open && window.MathJax?.typesetPromise) {
        window.MathJax.typesetPromise([explanation]).catch(()=>{});
      }
    };
  }
  explanation.open=false;
  let heading=content.querySelector(':scope > .bp-statement-heading');
  if (!heading) {
    heading=element('h2',undefined,'bp-statement-heading');
    content.insertBefore(heading,explanation);
  }
  heading.textContent=item.title;
  const panel=element('section',undefined,'bp-lean-panel');
  panel.setAttribute('aria-label','Grouped exact Lean declarations');
  panel.append(element('p',item.declarations.length+' checked Lean declarations, grouped by their role in this node.','bp-group-count'));
  const navigation=element('nav',undefined,'bp-group-navigation');
  navigation.setAttribute('aria-label','Declaration groups');
  const byName=new Map(item.declarations.map(record=>[record.name,record]));
  const selectedName=id==='thm:c3-primitive'&&['0','1','2'].includes(view)
    ? item.anchors[Number(view)] : null;
  panel.append(navigation);
  for (const [index,group] of item.groups.entries()) {
    const section=element('section',undefined,'bp-declaration-group');
    section.id=id+'-group-'+index;
    section.dataset.group=group.title;
    const title=element('h3',group.title+' ('+group.names.length+')','bp-group-heading');
    section.append(title);
    const link=element('a',group.title,'bp-group-link');
    link.href='#'+section.id;
    link.onclick=e=>{
      e.preventDefault();
      content.scrollTop+=section.getBoundingClientRect().top-content.getBoundingClientRect().top-16;
      section.querySelector('pre')?.focus({preventScroll:true});
    };
    navigation.append(link);
    for (const name of group.names) {
      const record=byName.get(name);
      if (!record) throw new Error('Missing checked declaration: '+name);
      section.append(declarationCard(record,name===selectedName));
    }
    panel.append(section);
  }
  panel.append(element('p','Types are exported from Lean’s checked environment. Selected definition bodies are included; theorem proof bodies are omitted. All declarations stay visible together—no one-at-a-time selector.','bp-note'));
  if (id==='thm:c3-primitive') {
    panel.append(element('p','The proposition and two native proofs are Mathlib-free. Only the Mathlib proof uses Mathlib’s reals; the background of each declaration records that distinction.','bp-note'));
  }
  content.insertBefore(panel,explanation);
  content.scrollTop=0;
}

function showNode() {
  const id = d3.select(this).select('title').text().trim();
  const modal = document.getElementById(id+'_modal');
  if (!modal) return;
  if (activeModal) activeModal.style.display='none';
  returnFocus = this;
  activeModal = modal;
  const statements = document.getElementById('statements');
  statements.style.display='block';
  modal.style.display='block';
  modal.setAttribute('role','dialog'); modal.setAttribute('aria-modal','true');
  modal.setAttribute('aria-label',proofGraphData.nodeDetails?.[id]?.title || 'Lean statement');
  modal.querySelectorAll('.dep-modal-content,.thm,.thm_thmcontent,.thm_thmheading').forEach(e=>e.style.display='block');
  const close = modal.querySelector('.dep-closebtn');
  close.textContent='×'; close.setAttribute('aria-label','Close statement'); close.onclick=closeStatement;
  addLeanPanel(modal,id);
  document.body.classList.add('statement-open');
  modal.querySelector('.dep-modal-content').scrollTop = 0;
  close.focus({preventScroll:true});
  if (window.MathJax?.typesetPromise) window.MathJax.typesetPromise([modal]).catch(()=>{});
}

function attachInteractions() {
  d3.selectAll('#graph .node').attr('tabindex',0).attr('role','button')
    .each(function(){ const id=d3.select(this).select('title').text(); this.setAttribute('data-foundation',nodeStatus(id)); })
    .on('click',showNode).on('keydown',function(e){
      e=d3.event||e;
      if(e.key==='Enter'||e.key===' '){e.preventDefault();showNode.call(this);}
    });
  d3.selectAll('#graph .edge').style('cursor','pointer').on('click',function(){
    const pair=d3.select(this).select('title').text().split('->');
    const records=proofGraphData.witnesses.filter(e=>e.source===pair[0]&&e.target===pair[1]&&(view==='all'||view==='companions'||String(e.route)===view));
    const content=document.getElementById('proof-edge-content'); content.replaceChildren();
    for(const e of records){
      content.append(element('h3',e.route===null?'Companion':['Direct inequalities','Native FTC','Mathlib + bridges'][e.route]));
      content.append(element('p',(e.witness.length-1)+' actual type/body references, shown prerequisite first.'));
      const list=element('ol'); for(const n of e.witness)list.append(element('li',n)); content.append(list);
    }
    document.getElementById('proof-edge-dialog').hidden=false;
    document.getElementById('proof-edge-close').focus();
  });
}

function render() {
  closeStatement();
  renderer.width(container.node().clientWidth).height(container.node().clientHeight)
    .renderDot(proofGraphData.views[view]).on('end',attachInteractions);
}

document.querySelectorAll('[data-view]').forEach(b=>b.onclick=()=>{
  view=b.dataset.view;
  document.querySelectorAll('[data-view]').forEach(x=>x.classList.toggle('active',x===b));render();
});
document.getElementById('proof-fit').onclick=()=>renderer.resetZoom();
document.getElementById('proof-edge-close').onclick=()=>document.getElementById('proof-edge-dialog').hidden=true;
document.getElementById('statements').addEventListener('click',e=>{if(!e.target.closest('.dep-modal-content'))closeStatement();});
document.addEventListener('keydown',e=>{
  if(e.key==='Escape') {document.getElementById('proof-edge-dialog').hidden=true;closeStatement();}
  if(e.key==='Tab'&&activeModal){
    const items=[...activeModal.querySelectorAll('button,a[href],select,summary,[tabindex="0"]')].filter(n=>n.getClientRects().length);
    const first=items[0],last=items[items.length-1];
    if(e.shiftKey&&document.activeElement===first){e.preventDefault();last.focus();}
    else if(!e.shiftKey&&document.activeElement===last){e.preventDefault();first.focus();}
  }
});
const checks=proofGraphData.info.checks;
document.getElementById('proof-checks').textContent=Object.values(checks).every(Boolean)?'Type equality, separation, and no-sorryAx checks passed.':'';
for(const [i,m] of proofGraphData.info.metrics.entries()){
  const row=element('tr');
  for(const value of [['Direct inequalities','Native FTC','Mathlib + bridges'][i],m.bodyTreeNodes+' / '+m.bodyDagNodes,m.native,m.bridge,m.mathlib,m.leanOrOther,m.axioms.length])row.append(element('td',value));
  document.getElementById('proof-metrics').append(row);
}
render();
