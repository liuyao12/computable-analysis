(() => {
  'use strict';
  const panel=document.querySelector('.fuchs-story-example');
  if(!panel)return;
  const $=id=>document.getElementById(id),plot=$('story-plot'),out=$('story-readout');
  const progress=$('story-progress'),orientation=$('story-orientation'),radius=$('story-radius'),follow=$('story-follow');
  const buttons=[...panel.querySelectorAll('[data-story-view]')];
  let mode='patches',queue=Promise.resolve(),revision=0;
  const fmt=x=>(Math.abs(x)<1e-8?0:x).toFixed(4);
  const X=x=>165+95*x,Y=y=>140-95*y;
  const vertices=[[1,0],[1,1],[-1,1],[-1,-1],[1,-1],[1,0]];
  // Equal-arclength positions, with the base point midway up the right side.
  function square(t,sign=1){
    const d=((t%1)+1)%1*8;
    let z;
    if(d<=1)z=[1,d];else if(d<=3)z=[2-d,1];else if(d<=5)z=[-1,4-d];else if(d<=7)z=[d-6,-1];else z=[1,d-8];
    return [z[0],sign*z[1]];
  }
  function continuedLog(t,sign=1){
    const z=square(t,sign),turns=Math.floor(t),fraction=t-turns;
    let arg=fraction===0?0:Math.atan2(z[1],z[0]);
    if(sign>0&&arg<0)arg+=2*Math.PI;
    if(sign<0&&arg>0)arg-=2*Math.PI;
    return {z,re:Math.log(Math.hypot(...z)),im:arg+sign*turns*2*Math.PI};
  }
  function typeset(html){
    const mine=++revision;
    queue=queue.then(async()=>{
      if(mine!==revision)return;
      if(window.MathJax?.startup?.promise)await MathJax.startup.promise;
      window.MathJax?.typesetClear?.([out]);out.innerHTML=html;
      if(window.MathJax?.typesetPromise)await MathJax.typesetPromise([out]);
    }).catch(e=>{out.textContent='Mathematical rendering unavailable.';console.error(e);});
  }
  function render(){
    $('story-route-controls').hidden=mode==='growth';$('story-growth-controls').hidden=mode!=='growth';
    const sign=Number(orientation.value),t=Number(progress.value)/100,L=continuedLog(t,sign);
    $('story-progress-label').textContent=progress.value+'%';
    let svg='',html='',caption='';
    if(mode==='growth'){
      const r=10**(-Number(radius.value)/100),u=-Math.log(r);
      $('story-radius-label').textContent=r.toFixed(3);
      const xx=x=>35+265*x/Math.log(10),yy=v=>246-20*v;
      svg='<title id="story-plot-title">Compare growth as the radius decreases</title><desc id="story-plot-desc">Height is log of one plus the magnitude. The exponential of reciprocal radius rises faster than the logarithm or the chosen power.</desc>';
      svg+='<path d="M35 20V246H307" fill="none" stroke="var(--line)"/><text x="42" y="18">logarithmic height</text><text x="180" y="273">closer to zero</text>';
      for(const [f,color] of [[x=>Math.log1p(x),'var(--green)'],[x=>Math.log1p(Math.exp(2*x)),'#987d3f'],[x=>Math.log1p(Math.exp(Math.exp(x))),'var(--purple)']]){
        const points=Array.from({length:101},(_,j)=>{const x=j*Math.log(10)/100;return `${xx(x)},${yy(f(x))}`;}).join(' ');
        svg+=`<polyline points="${points}" fill="none" stroke="${color}" stroke-width="2"/><circle cx="${xx(u)}" cy="${yy(f(u))}" r="4" fill="${color}"/>`;
      }
      html=`<p>Height: \\(\\log(1+|y|)\\)</p><p>\\(r=${fmt(r)}\\)</p><p class="story-key">\\(|\\log r|=${fmt(u)}\\)</p><p class="story-key power">\\(r^{-2}=${fmt(r**-2)}\\)</p><p class="story-key irregular">\\(e^{1/r}\\approx${Math.exp(1/r).toPrecision(5)}\\)</p>`;
      caption='A finite plot illustrates growth; the claim about every power requires the limiting estimate in the text.';
    }else{
      svg='<title id="story-plot-title">'+(mode==='patches'?'Overlapping local logarithm neighborhoods':'A continued logarithm around the origin')+'</title><desc id="story-plot-desc">The marker travels around a square. At each full circuit it returns to the base point while the continued imaginary part changes by one signed period.</desc>';
      svg+=`<path d="M18 140H313M165 16V265" stroke="var(--line)" fill="none"/><polyline points="${vertices.map(z=>`${X(z[0])},${Y(sign*z[1])}`).join(' ')}" stroke="var(--green)" fill="none" stroke-width="2"/>`;
      if(mode==='patches'){
        const j=Math.floor((t%1)*64);
        for(const k of [j-1,j,j+1]){
          const c=square(k/64,sign),half=1/6;
          svg+=`<rect x="${X(c[0]-half)}" y="${Y(c[1]+half)}" width="${190*half}" height="${190*half}" fill="${k===j?'var(--green)':'var(--purple)'}" fill-opacity=".12" stroke="${k===j?'var(--green)':'var(--purple)'}"/><circle cx="${X(c[0])}" cy="${Y(c[1])}" r="2" fill="var(--green)"/>`;
        }
        html='<p>\\(L_{c,b}(z)=b+\\ell((z-c)/c)\\)</p><p>Carry the value at the next center; compare the functions on an open overlap.</p>';
        caption='Three of the overlapping rectangles are shown. The origin lies outside every rectangle. Local series do not need one disk covering the whole route.';
      }else{
        html=`<p>\\(L(z)\\approx ${fmt(L.re)}${L.im<0?'-':'+'}${fmt(Math.abs(L.im))}i\\)</p><p>After one complete circuit:</p><p>\\(M_\\gamma=\\begin{pmatrix}1&${sign<0?'-':''}2\\pi i\\\\0&1\\end{pmatrix}\\)</p>`;
        caption='The branch is carried continuously along the route. At one or two full circuits, the point returns but the imaginary part retains the accumulated period.';
      }
      svg+=`<circle cx="165" cy="140" r="4" fill="var(--purple)"/><text x="174" y="135">singularity</text><circle cx="${X(1)}" cy="${Y(0)}" r="6" fill="none" stroke="var(--green)"/><text x="268" y="158">start</text><circle cx="${X(L.z[0])}" cy="${Y(L.z[1])}" r="4" fill="var(--purple)"/>`;
    }
    plot.innerHTML=svg;$('story-caption').textContent=caption;typeset(html);panel.dataset.mode=mode;
  }
  function choose(next,manual=false){mode=next;if(manual)follow.checked=false;buttons.forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.storyView===mode)));render();}
  buttons.forEach(b=>b.addEventListener('click',()=>choose(b.dataset.storyView,true)));
  [progress,orientation,radius].forEach(e=>e.addEventListener('input',render));
  const headings=[...document.querySelectorAll('article [data-story]')];let waiting=false;
  window.addEventListener('scroll',()=>{if(waiting||!follow.checked||innerWidth<=1050)return;waiting=true;requestAnimationFrame(()=>{waiting=false;let chosen=headings[0];for(const h of headings)if(h.getBoundingClientRect().top<innerHeight*.45)chosen=h;if(chosen&&chosen.dataset.story!==mode)choose(chosen.dataset.story);});},{passive:true});
  const page=document.querySelector('.page'),anchor=document.querySelector('article > .showcase-statement'),media=matchMedia('(max-width:1050px)');
  function place(){if(media.matches)anchor.after(panel);else page.append(panel);}
  media.addEventListener('change',place);place();render();
  window.FuchsStory={square,continuedLog,get mode(){return mode;}};
})();
