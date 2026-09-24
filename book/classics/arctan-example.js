(() => {
  'use strict';
  const panel=document.querySelector('.arctan-example');if(!panel)return;
  const $=id=>document.getElementById(id),input=$('arctan-input'),terms=$('arctan-terms'),plot=$('arctan-plot'),out=$('arctan-readout'),follow=$('arctan-follow');
  let mode='graph',queue=Promise.resolve(),revision=0;
  function partial(x,n){let p=x,s=0;for(let k=0;k<n;k++){s+=p/(2*k+1);p*=-x*x;}return s;}
  function term(x,n){return (-1)**n*x**(2*n+1)/(2*n+1);}
  function tex(x){if(x===0)return '0';const a=Math.abs(x);if(a>=1e5||a<1e-5){const [m,e]=x.toExponential(4).split('e');return `${m}\\times10^{${Number(e)}}`;}return x.toFixed(6);}
  const path=(points,color,width=2)=>`<polyline points="${points.map(p=>p.join(',')).join(' ')}" stroke="${color}" stroke-width="${width}" fill="none"/>`;
  const line=(x1,y1,x2,y2,color='var(--line)',dash='')=>`<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}" stroke="${color}" ${dash?`stroke-dasharray="${dash}"`:''}/>`;
  function math(html){const mine=++revision;queue=queue.then(async()=>{if(mine!==revision)return;if(window.MathJax?.startup?.promise)await MathJax.startup.promise;if(window.MathJax?.typesetClear)MathJax.typesetClear([out]);out.innerHTML=html;if(window.MathJax?.typesetPromise)await MathJax.typesetPromise([out]);}).catch(e=>{out.textContent='Mathematical rendering unavailable.';console.error(e);});}
  function render(){
    const x=Number(input.value),n=Number(terms.value),sum=partial(x,n),value=Math.atan(x),error=Math.abs(sum-value),r=Math.abs(x);
    $('arctan-input-label').textContent=x.toFixed(2);$('arctan-terms-label').textContent=n;
    panel.querySelectorAll('[data-arctan-x]').forEach(b=>b.setAttribute('aria-pressed',String(Number(b.dataset.arctanX)===x)));
    const kind=r<1?'inside':r===1?'boundary':'outside';$('arctan-status').dataset.kind=kind;$('arctan-status').textContent={inside:'Converges inside the interval',boundary:'Converges at the endpoint — slowly',outside:'Diverges: successive sums do not settle'}[kind];
    let svg='<title id="arctan-plot-title">'+{graph:'Arctangent and its Taylor polynomial',sequence:'Successive Taylor sums at the selected input',plane:'Complex singularities and the disk of convergence'}[mode]+'</title><desc id="arctan-plot-description">The green curve or line is the arctangent value. The purple marks show the Taylor approximation. Read the numerical values and explanation below.</desc>';
    let caption='';
    if(mode==='graph'){
      const sx=t=>165+70*t,sy=t=>130-52*Math.max(-200,Math.min(200,t));
      svg+='<defs><clipPath id="arctan-clip"><rect x="15" y="12" width="300" height="232"/></clipPath></defs>';
      svg+='<rect x="95" y="12" width="140" height="232" fill="var(--green)" opacity=".055"/>';
      svg+=line(15,130,315,130)+line(165,12,165,244)+line(95,12,95,244,'var(--line)','4 4')+line(235,12,235,244,'var(--line)','4 4');
      const xs=Array.from({length:501},(_,j)=>-2+j/125);
      svg+='<g clip-path="url(#arctan-clip)">'+path(xs.map(t=>[sx(t),sy(Math.atan(t))]),'var(--green)')+path(xs.map(t=>[sx(t),sy(partial(t,n))]),'var(--purple)');
      svg+=line(sx(x),sy(value),sx(x),sy(sum),'var(--purple)','3 3');
      svg+=`<circle cx="${sx(x)}" cy="${sy(value)}" r="4" fill="var(--green)"/><circle cx="${sx(x)}" cy="${sy(sum)}" r="4" fill="var(--purple)"/></g><text x="276" y="148">input</text><text x="175" y="24">value</text>`;
      caption='The shaded band is the convergence interval. The graph keeps a fixed vertical scale; diverging polynomial values can leave the frame.';
    }else if(mode==='sequence'){
      const points=Array.from({length:n+1},(_,j)=>partial(x,j)),scale=Math.max(1.1,Math.abs(value)*1.3,...points.map(t=>Math.abs(t)*1.1));
      const sx=j=>25+280*j/n,sy=t=>130-103*t/scale;
      svg+=line(25,130,310,130)+line(25,15,25,240)+line(25,sy(value),310,sy(value),'var(--green)');
      svg+=path(points.map((t,j)=>[sx(j),sy(t)]),'var(--purple)',1.2);
      points.forEach((t,j)=>{svg+=`<circle cx="${sx(j)}" cy="${sy(t)}" r="2" fill="var(--purple)"/>`;});
      svg+='<text x="240" y="255">term count</text><text x="32" y="20">partial sum</text>';
      caption='Every point is a consecutive partial sum, starting with the empty sum. The vertical scale adapts to keep all sums visible.';
    }else{
      const sx=t=>165+66*t,sy=t=>130-66*t;
      svg+=`<circle cx="165" cy="130" r="66" fill="var(--green)" opacity=".06"/><circle cx="165" cy="130" r="66" fill="none" stroke="var(--green)" stroke-dasharray="4 4"/>`;
      svg+=line(15,130,315,130)+line(165,15,165,245);
      [1,-1].forEach(t=>{svg+=line(sx(-.06),sy(t-.06),sx(.06),sy(t+.06),'var(--purple)')+line(sx(-.06),sy(t+.06),sx(.06),sy(t-.06),'var(--purple)');});
      svg+=line(165,130,sx(x),130,'var(--green)')+`<circle cx="${sx(x)}" cy="130" r="5" fill="var(--green)"/><text x="235" y="148">real axis</text><text x="175" y="24">imaginary axis</text>`;
      caption='The crosses mark the derivative’s two poles. The selected input stays on the real axis; the circle shows how far the origin-centered expansion reaches.';
    }
    plot.innerHTML=svg;
    panel.querySelector('.arctan-legend').hidden=mode==='plane';$('arctan-caption').textContent=caption;
    let html=`<p>\\(x=${tex(x)},\\quad N=${n}\\)</p>`;
    if(mode==='plane')html+='<p>\\(z=\\pm i,\\qquad |z|=1\\)</p>';
    html+=`<p>\\(A(x)\\approx ${tex(value)}\\)</p><p>\\(S_N(x)\\approx ${tex(sum)}\\)</p>`;
    if(r<=1){const bound=r**(2*n+1)/(2*n+1);html+=`<p>\\(|A(x)-S_N(x)|\\le B_N(x)\\approx ${tex(bound)}\\)</p>`;if(error<1e-14)html+='<p class="example-note">The browser difference is near floating-point precision; use the theoretical bound above.</p>';else html+=`<p>Observed error: \\( ${tex(error)}\\)</p>`;}
    else html+=`<p>\\(|S_{N+1}-S_N|\\approx ${tex(Math.abs(term(x,n)))}\\)</p><p>\\(|S_{N+1}-S_N|\\ge\\delta(x)\\approx ${tex(r*(r*r-1)/3)}\\)</p>`;
    math(html);panel.dataset.mode=mode;panel.dataset.kind=kind;
  }
  function choose(m,manual=false){mode=m;if(manual)follow.checked=false;panel.querySelectorAll('[data-arctan-mode]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.arctanMode===mode)));render();}
  panel.querySelectorAll('[data-arctan-mode]').forEach(b=>b.addEventListener('click',()=>choose(b.dataset.arctanMode,true)));
  panel.querySelectorAll('[data-arctan-x]').forEach(b=>b.addEventListener('click',()=>{input.value=b.dataset.arctanX;render();}));
  [input,terms].forEach(e=>e.addEventListener('input',render));
  const headings=[...document.querySelectorAll('article [data-arctan-view]')];let pending=false;
  window.addEventListener('scroll',()=>{if(pending||!follow.checked||innerWidth<=1050)return;pending=true;requestAnimationFrame(()=>{pending=false;let h=headings[0];for(const x of headings)if(x.getBoundingClientRect().top<innerHeight*.45)h=x;if(h&&h.dataset.arctanView!==mode)choose(h.dataset.arctanView);});},{passive:true});
  const media=matchMedia('(max-width:1050px)'),page=document.querySelector('.page'),anchor=document.querySelector('article > .classic-scope');
  function place(){if(media.matches)anchor.after(panel);else page.append(panel);}media.addEventListener('change',place);place();render();
  window.ArctanExample={partial,term,get mode(){return mode;}};
})();
