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

function addLeanPanel(modal, id) {
  const item = proofGraphData.nodeDetails?.[id];
  if (!item) return;
  const content = modal.querySelector('.dep-modal-content');
  content.querySelector('.bp-lean-panel')?.remove();
  const panel = element('section', undefined, 'bp-lean-panel');
  const status = nodeStatus(id);
  const labels = {native:'No Mathlib ℝ dependency', mathlib:'Depends on Mathlib ℝ', mixed:'Mathlib ℝ only in the third proof'};
  panel.append(element('p', labels[status], 'foundation-badge '+status));
  if (id === 'thm:c3-primitive') {
    panel.append(element('p', 'The common statement is Mathlib-free. The direct and native FTC proofs do not use Mathlib’s reals; the Mathlib proof does.', 'bp-note'));
  }
  const bar = element('div', undefined, 'bp-lean-toolbar');
  const title = element('h3', 'Lean statement');
  const copy = element('button', 'Copy', 'bp-copy');
  copy.type = 'button';
  bar.append(title, copy);
  panel.append(bar);
  const pre = element('pre', undefined, 'bp-lean-code');
  const code = element('code'); pre.append(code);
  const source = element('a', 'Open pinned Lean source', 'bp-formal-source');
  source.target = '_blank'; source.rel = 'noopener';
  let selected = item.declarations[0];
  function display(record) {
    selected = record;
    code.textContent = record.kind+' '+record.name+' :\n  '+record.type.replaceAll('\n','\n  ')
      +(record.value !== null ? ' :=\n  '+record.value.replaceAll('\n','\n  ') : '');
    source.href = record.sourceUrl;
    pre.scrollTop = 0;
    copy.textContent = 'Copy';
  }
  if (item.declarations.length > 1) {
    const label = element('label', 'Declaration', 'bp-declaration-label');
    const select = element('select'); select.setAttribute('aria-label','Lean declaration');
    for (const record of item.declarations) {
      const option = element('option', record.name); option.value = record.name; select.append(option);
    }
    select.onchange = () => display(item.declarations.find(d=>d.name===select.value));
    label.append(select); panel.append(label);
  }
  copy.onclick = async () => {
    try { await navigator.clipboard.writeText(code.textContent); copy.textContent='Copied'; }
    catch (_) { const range=document.createRange(); range.selectNodeContents(code); const selection=window.getSelection(); selection.removeAllRanges(); selection.addRange(range); copy.textContent='Selected'; }
  };
  panel.append(pre,source);
  const provenance = element('p', 'Exported from Lean’s checked elaborated declaration. Theorem proof bodies are omitted.', 'bp-note');
  panel.append(provenance);
  const paths = Object.entries(item.paths).filter(([_,path])=>path.length);
  if (paths.length) {
    const details = element('details', undefined, 'bp-dependency-details');
    details.append(element('summary','Why this node has a Mathlib ℝ background'));
    details.append(element('p','These are actual transitive references in stored declaration types or bodies—not import-list guesses.'));
    for (const [name,path] of paths) {
      details.append(element('p',name,'bp-dependency-name'));
      const list=element('ol'); for (const dep of path) list.append(element('li',dep));
      details.append(list);
    }
    panel.append(details);
  }
  content.append(panel);
  display(selected);
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
