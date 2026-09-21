(function(){
  'use strict';
  const E=window.ODEEngine, $=id=>document.getElementById(id), NS='http://www.w3.org/1998/Math/MathML';
  const state={id:'exponential',N:4,component:0,initial:[1],force:0};
  let cache, pending=false, modelVersion=0;
  const mobile=matchMedia('(max-width: 800px)');
  function fmt(x,d=6){if(!Number.isFinite(x))return 'outside display range';if(x===0)return '0';if(Math.abs(x)<1e-4||Math.abs(x)>=1e5)return x.toExponential(4);return x.toFixed(d).replace(/\.?0+$/,'');}
  function loadModel(id,defaults=true){
    if(!E.models[id])return;
    const version=++modelVersion;
    state.id=id;cache=E.build(id);const m=cache.model;
    if(defaults){state.initial=[...m.initial];state.force=m.force;state.N=m.N;state.component=0;$('time').value=65;}
    $('model').value=id;$('iterations').value=state.N;$('force').value=state.force;
    $('force').disabled=id==='exponential';
    $('model-equation').innerHTML=$('eq-'+id).innerHTML;
    $('component').replaceChildren(...m.labels.map((label,i)=>{const o=document.createElement('option');o.value=i;o.textContent=label;return o;}));
    $('component').value=state.component;
    $('initial-controls').replaceChildren(...m.labels.map((label,i)=>{
      const wrap=document.createElement('label');wrap.append(label+'(0)');
      const input=document.createElement('input');input.type='number';input.step='1';input.min='-3';input.max='3';input.value=state.initial[i];input.setAttribute('aria-label',`Initial ${label}`);
      input.addEventListener('change',()=>{if(version!==modelVersion)return;const v=Number(input.value);state.initial[i]=Number.isFinite(v)?Math.max(-3,Math.min(3,Math.round(v))):0;input.value=state.initial[i];queue();});wrap.append(input);return wrap;
    }));
    $('forcing-description').textContent=m.forcing;
    $('reference-label').textContent=id==='airy'?'Dashed: 120-degree reference series':'Dashed: closed-form solution';
    render();
  }
  function queue(){if(!pending){pending=true;requestAnimationFrame(()=>{pending=false;render();});}}
  function mathPolynomial(p,label,N){
    const nonzero=p.map((q,k)=>({q,k})).filter(({q})=>q.p!==0n), shown=nonzero.slice(0,7);
    let inner='';
    if(!shown.length)inner='<mn>0</mn>';
    shown.forEach(({q,k},i)=>{
      if(q.p<0n)inner+='<mo>−</mo>';else if(i)inner+='<mo>+</mo>';
      q=q.abs();let coeff='';
      if(k===0||q.cmp(1)!==0)coeff=q.q===1n?`<mn>${q.p}</mn>`:`<mfrac><mn>${q.p}</mn><mn>${q.q}</mn></mfrac>`;
      const power=k===0?'':k===1?'<mi>t</mi>':`<msup><mi>t</mi><mn>${k}</mn></msup>`;
      inner+=`<mrow>${coeff}${power}</mrow>`;
    });
    if(nonzero.length>shown.length)inner+='<mo>+</mo><mo>⋯</mo>';
    const left=`<msup><mi>${label}</mi><mrow><mo>[</mo><mn>${N}</mn><mo>]</mo></mrow></msup><mo>(</mo><mi>t</mi><mo>)</mo><mo>=</mo>`;
    return {html:`<math xmlns="${NS}"><mrow>${left}${inner}</mrow></math>`,total:nonzero.length,shown:shown.length};
  }
  function matrixMarkup(S,t){
    const d=cache.model.A.length,rows=S.slice(0,d).map(row=>'<mtr>'+row.slice(0,d).map(p=>`<mtd><mn>${fmt(E.evaluate(p,t).number(),5)}</mn></mtd>`).join('')+'</mtr>').join('');
    return `<math xmlns="${NS}"><mrow><mo>(</mo><mtable columnspacing="1em" rowspacing="0.45em">${rows}</mtable><mo>)</mo></mrow></math>`;
  }
  function ticks(lo,hi,count=5){
    const raw=(hi-lo)/count,mag=10**Math.floor(Math.log10(raw)),r=raw/mag,step=(r<=1?1:r<=2?2:r<=5?5:10)*mag;
    const out=[];for(let x=Math.ceil(lo/step)*step;x<=hi+step*1e-8;x+=step)out.push(Math.abs(x)<step*1e-8?0:x);return out;
  }
  function draw(current,previous,ref,tNow){
    const W=520,H=290,left=53,right=503,top=18,bottom=248,T=cache.model.T.number(),component=state.component;
    const ts=Array.from({length:221},(_,i)=>T*i/220),cc=E.numericCoefficients(current),vals=ts.map(t=>E.evalFloat(cc,t)),rv=ts.map(t=>ref(t)[component]);
    let lo=Math.min(0,...vals,...rv),hi=Math.max(0,...vals,...rv);if(hi-lo<1e-10){lo-=1;hi+=1;}
    const pad=(hi-lo)*.09;lo-=pad;hi+=pad;
    const X=t=>left+(right-left)*t/T,Y=v=>bottom-(bottom-top)*(v-lo)/(hi-lo);
    const path=(v)=>v.map((y,i)=>(i?'L':'M')+X(ts[i]).toFixed(3)+','+Y(y).toFixed(3)).join(' ');
    let s='<title>Picard iteration '+state.N+' for '+cache.model.id+'</title><desc>Solid: current exact polynomial, evaluated for drawing. Pale curves: up to three earlier iterates. Dashed: reference solution. Horizontal axis: time.</desc>';
    s+='<defs><clipPath id="plot-clip"><rect x="53" y="18" width="450" height="230"/></clipPath></defs>';
    s+=`<g stroke="#d3d8d1" stroke-width="1"><path d="M${left},${top}V${bottom}"/><path d="M${left},${Y(0)}H${right}"/></g>`;
    s+='<g fill="#72807e" font-family="system-ui,sans-serif" font-size="10">';
    ticks(lo,hi).forEach(v=>{s+=`<path d="M${left-4},${Y(v)}h4" stroke="#bac5bf"/><text x="${left-9}" y="${Y(v)+3}" text-anchor="end">${fmt(v,3)}</text>`;});
    ticks(0,T,4).forEach(t=>{s+=`<path d="M${X(t)},${bottom}v4" stroke="#bac5bf"/><text x="${X(t)}" y="${bottom+19}" text-anchor="middle">${fmt(t,2)}</text>`;});
    s+=`<text x="${right}" y="${bottom+36}" text-anchor="end">time t</text></g>`;
    s+='<g clip-path="url(#plot-clip)" fill="none" stroke-linecap="round" stroke-linejoin="round">';
    previous.forEach(p=>{const a=E.numericCoefficients(p);s+=`<path d="${path(ts.map(t=>E.evalFloat(a,t)))}" stroke="#b7c8c1" stroke-width="1.25"/>`;});
    s+=`<path d="${path(rv)}" stroke="#ad5b37" stroke-width="1.7" stroke-dasharray="5 5"/>`;
    s+=`<path d="${path(vals)}" stroke="#12685e" stroke-width="2.5"/>`;
    s+=`<path d="M${X(tNow)},${top}V${bottom}" stroke="#c6cec7" stroke-width="1" stroke-dasharray="2 4"/>`;
    s+=`<circle cx="${X(tNow)}" cy="${Y(E.evalFloat(cc,tNow))}" r="4" fill="#12685e" stroke="#f7f5f0" stroke-width="1.5"/></g>`;
    $('plot').innerHTML=s;
  }
  function render(){
    if(!cache)return;
    const m=cache.model,N=state.N,component=state.component,t=m.T.mul(new E.Q(Number($('time').value),100));
    const x=E.solutionPolynomials(cache,N,state.initial,state.force),bound=E.solutionBound(cache,N,state.initial,state.force,x),up=E.upperScientific(bound);
    const prev=[];for(let k=Math.max(0,N-3);k<N;k++)prev.push(E.solutionPolynomials(cache,k,state.initial,state.force)[component]);
    draw(x[component],prev,E.reference(m,state.initial,state.force),t.number());
    $('n-label').textContent=N;$('time-label').textContent=fmt(t.number(),3);$('force-label').textContent=state.force;
    $('minus').disabled=N===0;$('plus').disabled=N===36;
    $('value-name').textContent=`${m.labels[component]} at t = ${fmt(t.number(),3)}`;
    $('value').textContent='≈ '+fmt(E.evaluate(x[component],t).number());
    $('bound').innerHTML=up.zero?'0 <small>(exact)</small>':`≤ ${up.mantissa}${up.exponent===0?'':` × 10<sup>${up.exponent}</sup>`}`;
    $('bound-note').textContent=up.zero?'The polynomial residual is identically zero: this iterate is the exact solution.':`For every t in [0, ${fmt(m.T.number(),3)}], all coordinates. A conservative exact-series bound, rounded upward; drawing errors are not included.`;
    const p=mathPolynomial(x[component],m.labels[component],N);$('polynomial').innerHTML=p.html;
    $('poly-note').textContent=(p.total>p.shown?`First ${p.shown} of ${p.total} nonzero terms shown. `:'All terms shown. ')+`N counts Picard iterations, not polynomial degree (here ${x[component].length-1}).`;
    $('matrix-value').innerHTML=matrixMarkup(cache.sums[N],t);
  }
  $('model').addEventListener('change',()=>{$('follow').checked=false;loadModel($('model').value);});
  $('iterations').addEventListener('input',()=>{state.N=Number($('iterations').value);queue();});
  $('time').addEventListener('input',queue);
  $('component').addEventListener('change',()=>{state.component=Number($('component').value);queue();});
  $('force').addEventListener('input',()=>{state.force=Number($('force').value);queue();});
  $('minus').addEventListener('click',()=>{state.N=Math.max(0,state.N-1);$('iterations').value=state.N;queue();});
  $('plus').addEventListener('click',()=>{state.N=Math.min(36,state.N+1);$('iterations').value=state.N;queue();});
  $('reset').addEventListener('click',()=>loadModel(state.id));
  const chapters=[...document.querySelectorAll('section[data-scene]')];
  let scrollPending=false;
  function scrollUpdate(){
    scrollPending=false;
    const total=document.documentElement.scrollHeight-innerHeight;
    $('progress').style.width=(total>0?100*scrollY/total:0)+'%';
    if(!$('follow').checked||mobile.matches)return;
    let active=chapters[0];
    for(const chapter of chapters){if(chapter.getBoundingClientRect().top<=innerHeight*.36)active=chapter;else break;}
    if(active.dataset.scene!==state.id)loadModel(active.dataset.scene);
  }
  addEventListener('scroll',()=>{if(!scrollPending){scrollPending=true;requestAnimationFrame(scrollUpdate);}},{passive:true});
  $('follow').addEventListener('change',scrollUpdate);
  function layoutNotebook(){const lab=$('lab');if(mobile.matches)document.querySelector('.hero').insertAdjacentElement('afterend',lab);else document.querySelector('.layout').append(lab);}
  mobile.addEventListener('change',()=>{layoutNotebook();scrollUpdate();});
  layoutNotebook();loadModel('exponential');scrollUpdate();
  // Exposed only for local automated checks; no state or network persistence.
  window.FundamentalMatrixNotebook={state,loadModel,render};
})();
