'use strict';
const container=d3.select('#graph');
let view='all';
const renderer=container.graphviz({useWorker:true}).fit(true);
function attachInteractions(){
  d3.selectAll('.node').attr('tabindex',0).attr('role','button').on('click',showNode).on('keydown',function(e){e=d3.event||e;if(e.key==='Enter'||e.key===' '){e.preventDefault();showNode.call(this);}});
  d3.selectAll('.edge').style('cursor','pointer').on('click',function(){
    const name=d3.select(this).select('title').text(),pair=name.split('->');
    const records=proofGraphData.witnesses.filter(e=>e.source===pair[0]&&e.target===pair[1]&&(view==='all'||view==='companions'||String(e.route)===view));
    const content=document.getElementById('proof-edge-content');content.replaceChildren();
    for(const e of records){const h=document.createElement('h3');h.textContent=e.route===null?'Companion':['Direct inequalities','Native FTC','Mathlib + bridges'][e.route];content.append(h);const p=document.createElement('p');p.textContent=(e.witness.length-1)+' actual type/body references, shown prerequisite first.';content.append(p);const list=document.createElement('ol');for(const n of e.witness){const li=document.createElement('li');li.textContent=n;list.append(li);}content.append(list);}
    document.getElementById('proof-edge-dialog').hidden=false;
  });
  d3.selectAll('.dep-closebtn').on('click',function(){this.closest('.dep-modal-container').style.display='none';});
}
function showNode(){
  const title=d3.select(this).select('title').text().trim();
  document.querySelectorAll('#statements > div').forEach(e=>e.style.display='none');
  const modal=document.getElementById(title+'_modal');if(!modal)return;
  modal.style.display='block';modal.querySelectorAll('.dep-modal-content,.thm,.thm_thmcontent,.thm_thmheading').forEach(e=>e.style.display='block');
  document.getElementById('statements').style.display='block';
}
function render(){
 renderer.width(container.node().clientWidth).height(container.node().clientHeight).renderDot(proofGraphData.views[view]).on('end',attachInteractions);
}
document.querySelectorAll('[data-view]').forEach(b=>b.onclick=()=>{view=b.dataset.view;document.querySelectorAll('[data-view]').forEach(x=>x.classList.toggle('active',x===b));render();});
document.getElementById('proof-fit').onclick=()=>renderer.resetZoom();
document.getElementById('proof-edge-close').onclick=()=>document.getElementById('proof-edge-dialog').hidden=true;
document.addEventListener('keydown',e=>{if(e.key==='Escape'){document.getElementById('proof-edge-dialog').hidden=true;document.querySelectorAll('.dep-modal-container').forEach(x=>x.style.display='none');}});
const checks=proofGraphData.info.checks;
document.getElementById('proof-checks').textContent=Object.values(checks).every(Boolean)?'Type equality, separation, and no-sorryAx checks passed.':'';
for(const [i,m] of proofGraphData.info.metrics.entries()){
 const row=document.createElement('tr');for(const value of [['Direct inequalities','Native FTC','Mathlib + bridges'][i],m.bodyTreeNodes+' / '+m.bodyDagNodes,m.native,m.bridge,m.mathlib,m.leanOrOther,m.axioms.length]){const c=document.createElement('td');c.textContent=value;row.append(c);}document.getElementById('proof-metrics').append(row);
}
render();
