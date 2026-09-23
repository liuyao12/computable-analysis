(() => {
  'use strict';
  const panel = document.querySelector('.cauchy-example');
  if (!panel) return;
  const $ = id => document.getElementById(id);
  const plot = $('cauchy-plot'), output = $('example-readout');
  const radius = $('example-radius'), mesh = $('example-mesh'), circuit = $('example-circuit');
  const orientation = $('example-orientation'), follow = $('example-follow');
  const buttons = [...panel.querySelectorAll('[data-example-view]')];
  let mode = 'coefficients', queue = Promise.resolve(), revision = 0;
  const C = (x,y) => ({x,y}), add = (a,b) => C(a.x+b.x,a.y+b.y);
  const sub = (a,b) => C(a.x-b.x,a.y-b.y), scale = (a,t) => C(a.x*t,a.y*t);
  const mul = (a,b) => C(a.x*b.x-a.y*b.y,a.x*b.y+a.y*b.x);
  const mid = (a,b) => scale(add(a,b),.5);
  const fmt = x => (Math.abs(x)<.0000005 ? 0 : x).toFixed(5);
  const texComplex = z => `${fmt(z.x)}${z.y<0?'-':'+'}${fmt(Math.abs(z.y))}i`;
  const x = a => 165+75*a, y = b => 140-75*b;
  const line = (a,b,color='var(--line)',w=1) => `<line x1="${x(a.x)}" y1="${y(a.y)}" x2="${x(b.x)}" y2="${y(b.y)}" stroke="${color}" stroke-width="${w}"/>`;
  const path = (pts,color='var(--green)',w=2) => `<polyline points="${pts.map(p=>`${x(p.x)},${y(p.y)}`).join(' ')}" fill="none" stroke="${color}" stroke-width="${w}"/>`;
  function square(r) {return [C(r,0),C(r,r),C(0,r),C(-r,r),C(-r,0),C(-r,-r),C(0,-r),C(r,-r),C(r,0)];}
  function quadrature(points,n,f) {
    let total=C(0,0);
    for(let e=0;e<points.length-1;e++) {
      const step=scale(sub(points[e+1],points[e]),1/n);
      for(let j=0;j<n;j++) total=add(total,mul(f(add(points[e],scale(step,j+.5))),step));
    }
    return total;
  }
  function triangles(a,b,c,n) {
    if(!n) return path([a,b,c,a],'var(--line)',.7);
    const ab=mid(a,b),bc=mid(b,c),ca=mid(c,a);
    return triangles(a,ab,ca,n-1)+triangles(ab,b,bc,n-1)+triangles(ca,bc,c,n-1)+triangles(ab,bc,ca,n-1);
  }
  function bessel(z) {
    let term=C(1,0),j=C(1,0),h=0,regular=C(0,0);
    const zz=mul(z,z);
    for(let k=1;k<=32;k++) {
      term=scale(mul(term,zz),-1/(4*k*k));h+=1/k;
      j=add(j,term);regular=sub(regular,scale(term,h));
    }
    return {j,regular};
  }
  function continuedArgument(z,sign,t) {
    if(t===0) return 0;
    if(t===1) return sign*2*Math.PI;
    let arg=Math.atan2(z.y,z.x);
    if(sign>0&&arg<0) arg+=2*Math.PI;
    if(sign<0&&arg>0) arg-=2*Math.PI;
    return arg;
  }
  function typeset(html) {
    const mine=++revision;
    queue=queue.then(async()=>{
      if(mine!==revision) return;
      if(window.MathJax?.startup?.promise) await MathJax.startup.promise;
      if(window.MathJax?.typesetClear) MathJax.typesetClear([output]);
      output.innerHTML=html;
      if(window.MathJax?.typesetPromise) await MathJax.typesetPromise([output]);
    }).catch(err=>{output.textContent='Mathematical rendering unavailable.';console.error(err);});
  }
  function render() {
    const r=Number(radius.value),depth=Number(mesh.value),n=2**depth,sign=Number(orientation.value);
    $('radius-label').textContent=r.toFixed(2);$('mesh-label').textContent=depth;
    $('circuit-label').textContent=circuit.value+'%';
    $('mesh-control').hidden=mode==='coefficients'||mode==='solutions';
    $('orientation-control').hidden=mode==='coefficients'||mode==='triangles';
    $('circuit-control').hidden=mode!=='solutions';
    let drawing='<title id="cauchy-plot-title">'+({coefficients:'The coefficient singularity',triangles:'Triangle subdivision and cancellation',contour:'A square contour around the pole',solutions:'Continuation along a square contour'})[mode]+'</title><desc id="cauchy-plot-description">The controls and numerical readout below describe the selected calculation.</desc>';
    drawing+=line(C(-1.9,0),C(1.9,0))+line(C(0,-1.65),C(0,1.65));
    drawing+='<text x="235" y="158">real part</text><text x="175" y="24">imaginary part</text>';
    const pts=square(r).map(z=>C(z.x,sign*z.y));
    let html='',caption='';
    if(mode==='triangles') {
      const a=C(0,0),b=C(r,0),c=C(0,r);
      drawing+=triangles(a,b,c,depth)+path([a,b,c,a]);
      const total=quadrature([a,b,c,a],n,z=>mul(z,z));
      html=`<p>\\(f(z)=z^2q(z)=z^2\\)</p><p>\\(S_n\\approx ${texComplex(total)}\\)</p><p>\\(\\lVert S_n\\rVert_1\\approx ${fmt(Math.abs(total.x)+Math.abs(total.y))}\\)</p>`;
      caption='Each interior edge has two opposite orientations. Refine to see the boundary midpoint error decrease for the regular coefficient.';
    } else {
      drawing+=path(pts);
      drawing+=line(C(-.05,-.05),C(.05,.05),'var(--purple)',2)+line(C(-.05,.05),C(.05,-.05),'var(--purple)',2);
      drawing+='<text x="175" y="132">pole</text>';
      if(mode==='coefficients') {
        html=`<p>\\(zp(z)=1\\)</p><p>\\(z^2q(z)=z^2\\)</p><p>\\(\\lvert z^2q(z)\\rvert\\le ${fmt(2*r*r)}\\quad(z\\in S)\\)</p>`;
        caption='The first coefficient has a simple pole. After scaling, both coefficients extend across the origin. Shrinking the square makes the bound on the second coefficient smaller.';
      } else if(mode==='contour') {
        const total=quadrature(pts,n,z=>scale(C(z.x,-z.y),1/(z.x*z.x+z.y*z.y)));
        for(let e=0;e<8;e++)for(let k=0;k<n;k++) {
          const z=add(pts[e],scale(sub(pts[e+1],pts[e]),(k+.5)/n));
          drawing+=`<circle cx="${x(z.x)}" cy="${y(z.y)}" r="1.7" fill="var(--green)"/>`;
        }
        const arrow=pts[1];drawing+=`<path d="M ${x(arrow.x)-5} ${y(arrow.y)+sign*12} l 5 ${-sign*7} l 5 ${sign*7}" fill="none" stroke="var(--green)" stroke-width="2"/>`;
        html=`<p>\\(S_n\\approx ${texComplex(total)}\\)</p><p>\\(S_n/(2\\pi i)\\approx ${fmt(total.y/(2*Math.PI))}\\)</p>`;
        caption='Changing size leaves the kernel integral unchanged. Reversing orientation changes its sign. Refinement approaches one signed turn.';
      } else {
        const t=Number(circuit.value)/100,part=Math.min(7,Math.floor(t*8)),u=t===1?1:t*8-part;
        const z=add(pts[part],scale(sub(pts[part+1],pts[part]),u));
        const arg=continuedArgument(z,sign,t);
        const b=bessel(z),value=add(mul(b.j,C(Math.log(Math.hypot(z.x,z.y)),arg)),b.regular);
        drawing+=`<circle cx="${x(z.x)}" cy="${y(z.y)}" r="5" fill="var(--purple)"/>`;
        html=`<p>\\(\\arg z\\approx ${fmt(arg)}\\)</p><p>\\(Y_*(z)\\approx ${texComplex(value)}\\)</p><p>\\(\\Delta Y_*=${sign<0?'-':''}2\\pi iJ_0\\)</p>`;
        caption='The marker returns to its start after a circuit, but the continued logarithmic solution acquires the displayed multiple of the regular solution.';
      }
    }
    plot.innerHTML=drawing;$('example-caption').textContent=caption;
    typeset(html);panel.dataset.mode=mode;
  }
  function choose(next,manual=false) {
    mode=next;if(manual)follow.checked=false;
    buttons.forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.exampleView===mode)));
    render();
  }
  buttons.forEach(b=>b.addEventListener('click',()=>choose(b.dataset.exampleView,true)));
  [radius,mesh,circuit,orientation].forEach(el=>el.addEventListener('input',render));
  const headings=[...document.querySelectorAll('article [data-example]')];
  let waiting=false;
  window.addEventListener('scroll',()=>{
    if(waiting||!follow.checked||innerWidth<=1050)return;
    waiting=true;requestAnimationFrame(()=>{
      waiting=false;let chosen=headings[0];
      for(const h of headings)if(h.getBoundingClientRect().top<innerHeight*.45)chosen=h;
      if(chosen&&chosen.dataset.example!==mode)choose(chosen.dataset.example);
    });
  },{passive:true});
  const page=document.querySelector('.page'),anchor=document.querySelector('article > .showcase-statement');
  const media=matchMedia('(max-width:1050px)');
  function place(){if(media.matches)anchor.after(panel);else page.append(panel);}
  media.addEventListener('change',place);place();render();
  window.CauchyExample={bessel,quadrature,square,continuedArgument,get mode(){return mode;}};
})();
