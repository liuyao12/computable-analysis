(()=>{
'use strict';
const root=document.getElementById('rational-ball-demo');if(!root)return;
const canvas=document.getElementById('ball-canvas'),ctx=canvas.getContext('2d');
const controls={stage:document.getElementById('ball-stage'),inner:document.getElementById('ball-inner'),outer:document.getElementById('ball-outer'),sphere:document.getElementById('ball-sphere')};
let yaw=.65,pitch=-.35,drag=null,queued=false;
const stages=window.rationalBallStages;
function project(p){const cy=Math.cos(yaw),sy=Math.sin(yaw),cp=Math.cos(pitch),sp=Math.sin(pitch),q=p.map(x=>x-.5);const x=cy*q[0]+sy*q[2],z=-sy*q[0]+cy*q[2],scale=Math.min(canvas.width,canvas.height)*.66;return [canvas.width/2+x*scale,canvas.height/2-(cp*q[1]-sp*z)*scale,sp*q[1]+cp*z];}
function edge(a,b,color,width=1){ctx.strokeStyle=color;ctx.lineWidth=width;ctx.beginPath();ctx.moveTo(a[0],a[1]);ctx.lineTo(b[0],b[1]);ctx.stroke();}
function mesh(model,side){const ps=model.vertices.map(project);if(side==='inner'){
 const fs=model.faces.map(f=>({f,z:f.reduce((s,i)=>s+ps[i][2],0)/3})).sort((a,b)=>a.z-b.z);
 for(const {f,z} of fs){ctx.beginPath();ctx.moveTo(ps[f[0]][0],ps[f[0]][1]);for(const i of f.slice(1))ctx.lineTo(ps[i][0],ps[i][1]);ctx.closePath();ctx.fillStyle=`rgba(42,116,94,${.17+.13*(z+1)/2})`;ctx.fill();}
}
 const edges=new Map((model.edges||[]).map(([a,b])=>[[a,b].join(','),[a,b]]));if(!model.edges)for(const f of model.faces)for(let j=0;j<3;j++){const a=f[j],b=f[(j+1)%3],key=[a,b].sort((x,y)=>x-y).join(',');edges.set(key,[a,b]);}
 for(const [a,b] of edges.values())edge(ps[a],ps[b],side==='inner'?'rgba(36,104,83,.64)':'rgba(183,105,31,.62)',side==='outer'?1.3:.7);
 if(side==='inner')for(const p of ps){ctx.beginPath();ctx.arc(p[0],p[1],2,0,Math.PI*2);ctx.fillStyle='#286f59';ctx.fill();}
}
function draw(){queued=false;const rect=canvas.getBoundingClientRect(),ratio=Math.min(devicePixelRatio||1,2);canvas.width=Math.round(rect.width*ratio);canvas.height=Math.round(rect.height*ratio);ctx.clearRect(0,0,canvas.width,canvas.height);
 const s=stages[Number(controls.stage.value)];if(controls.inner.checked)mesh(s.inner,'inner');
 if(controls.sphere.checked){for(let k=0;k<=8;k++){const lat=k*Math.PI/16;let prev=null;for(let j=0;j<=80;j++){const t=j*Math.PI/160,p=project([Math.cos(lat)*Math.cos(t),Math.sin(lat),Math.cos(lat)*Math.sin(t)]);if(prev)edge(prev,p,'rgba(91,100,102,.42)',.75);prev=p;}}
 for(let k=0;k<=8;k++){const lon=k*Math.PI/16;let prev=null;for(let j=0;j<=80;j++){const t=j*Math.PI/160,p=project([Math.cos(t)*Math.cos(lon),Math.sin(t),Math.cos(t)*Math.sin(lon)]);if(prev)edge(prev,p,'rgba(91,100,102,.42)',.75);prev=p;}}}
 if(controls.outer.checked)mesh(s.outer,'outer');
}
function schedule(){if(!queued){queued=true;requestAnimationFrame(draw);}}
function texFraction(q){const parts=q.split('/');return parts.length===1?parts[0]:`\\frac{${parts[0]}}{${parts[1]}}`;}
let typesetChain=Promise.resolve();
function update(){const s=stages[Number(controls.stage.value)];document.getElementById('ball-summary').textContent=`${s.samples} rational boundary points (${s.addedPoints} added at this stage) · ${s.tangents} tangent planes, including all 3 axis tangents · 3 coordinate planes · ${s.inner.faces.length} inner triangles · ${s.outer.faces.length} outer triangles`;
 const b=document.getElementById('ball-bounds'),e=document.getElementById('ball-exact'),u=document.getElementById('ball-update');
 typesetChain=typesetChain.then(async()=>{if(window.MathJax?.startup?.promise)await MathJax.startup.promise;if(window.MathJax?.typesetClear)MathJax.typesetClear([b,e,u]);b.textContent=`\\[${s.decimalLower}\\le v_3\\le ${s.decimalUpper}\\]`;e.textContent=`\\[\\ell_{${s.stage}}=${texFraction(s.inner.volume)},\\qquad u_{${s.stage}}=${texFraction(s.outer.volume)}\\]`;u.textContent=s.stage===0?'\\[\\ell_0=1/6,\\qquad u_0=1\\]':`\\[\\ell_{${s.stage}}=\\ell_{${s.stage-1}}+${texFraction(s.innerAdded)},\\qquad u_{${s.stage}}=u_{${s.stage-1}}-${texFraction(s.outerRemoved)}\\]`;if(window.MathJax?.typesetPromise)await MathJax.typesetPromise([b,e,u]);}).catch(err=>console.error(err));schedule();}
controls.stage.addEventListener('change',update);for(const key of ['inner','outer','sphere'])controls[key].addEventListener('change',schedule);
document.getElementById('ball-reset').addEventListener('click',()=>{yaw=.65;pitch=-.35;schedule();});
canvas.addEventListener('pointerdown',e=>{drag=[e.clientX,e.clientY];canvas.setPointerCapture(e.pointerId);});canvas.addEventListener('pointermove',e=>{if(!drag)return;yaw+=(e.clientX-drag[0])*.009;pitch+=(e.clientY-drag[1])*.009;drag=[e.clientX,e.clientY];schedule();});for(const event of ['pointerup','pointercancel'])canvas.addEventListener(event,()=>drag=null);
canvas.addEventListener('keydown',e=>{const offsets={ArrowLeft:[-.12,0],ArrowRight:[.12,0],ArrowUp:[0,-.12],ArrowDown:[0,.12]};if(offsets[e.key]){e.preventDefault();yaw+=offsets[e.key][0];pitch+=offsets[e.key][1];schedule();}});new ResizeObserver(schedule).observe(canvas);update();
})();
