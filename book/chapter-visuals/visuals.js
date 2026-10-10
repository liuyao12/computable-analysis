/* Diagram coordinates use floating point only for drawing. Exact finite stage
   readouts use BigInt fractions. These illustrations add no Lean claims. */
'use strict';
(() => {
const colors={ink:'#283c42',green:'#287b61',blue:'#296da8',orange:'#b56932',gray:'#b7c2c4',fill:'#dcebe4',bg:'#faf9f6'};
const gcd=(a,b)=>{a=a<0n?-a:a;while(b){[a,b]=[b,a%b]}return a};
const rat=(n,d=1n)=>{n=BigInt(n);d=BigInt(d);if(d<0n){n=-n;d=-d}const g=gcd(n,d);return {n:n/g,d:d/g}};
const add=(a,b)=>rat(a.n*b.d+b.n*a.d,a.d*b.d);
const sub=(a,b)=>rat(a.n*b.d-b.n*a.d,a.d*b.d);
const mul=(a,b)=>rat(a.n*b.n,a.d*b.d);
const pow=(a,k)=>rat(a.n**BigInt(k),a.d**BigInt(k));
const frac=a=>a.d===1n?String(a.n):`\\frac{${a.n}}{${a.d}}`;
const fact=n=>{let a=1n;for(let j=2;j<=n;j++)a*=BigInt(j);return a};
const polyPoints=(f,a,b,n=240)=>Array.from({length:n+1},(_,j)=>{const x=a+(b-a)*j/n;return [x,f(x)]});
function painter(canvas){
 const box=canvas.getBoundingClientRect(),w=box.width||600,h=box.height||300,dpr=devicePixelRatio||1;
 canvas.width=Math.round(w*dpr);canvas.height=Math.round(h*dpr);const ctx=canvas.getContext('2d');ctx.scale(dpr,dpr);ctx.clearRect(0,0,w,h);
 ctx.lineJoin='round';ctx.lineCap='round';ctx.font='13px system-ui';
 const text=(s,x,y,color=colors.ink)=>{ctx.fillStyle=color;ctx.fillText(s,x,y)};
 const line=(points,color=colors.ink,width=2,dash=[])=>{ctx.beginPath();points.forEach(([x,y],j)=>j?ctx.lineTo(x,y):ctx.moveTo(x,y));ctx.strokeStyle=color;ctx.lineWidth=width;ctx.setLineDash(dash);ctx.stroke();ctx.setLineDash([])};
 const fill=(points,color)=>{ctx.beginPath();points.forEach(([x,y],j)=>j?ctx.lineTo(x,y):ctx.moveTo(x,y));ctx.closePath();ctx.fillStyle=color;ctx.fill()};
 const dot=(x,y,color=colors.green,r=4)=>{ctx.beginPath();ctx.arc(x,y,r,0,2*Math.PI);ctx.fillStyle=color;ctx.fill()};
 const circle=(x,y,r,color,filled=false)=>{ctx.beginPath();ctx.arc(x,y,r,0,2*Math.PI);ctx.strokeStyle=color;ctx.lineWidth=2;if(filled){ctx.fillStyle=colors.fill;ctx.fill()}ctx.stroke()};
 function plot(xmin,xmax,ymin,ymax,xlabel='input',ylabel='value'){
  const left=43,right=w-22,top=26,bottom=h-50;
  const X=x=>left+(x-xmin)/(xmax-xmin)*(right-left),Y=y=>bottom-(y-ymin)/(ymax-ymin)*(bottom-top);
  const y0=Y(Math.max(ymin,Math.min(ymax,0))),x0=X(Math.max(xmin,Math.min(xmax,0)));
  line([[left,y0],[right,y0]],colors.gray,1);line([[x0,top],[x0,bottom]],colors.gray,1);
  text(xlabel,Math.max(left,right-ctx.measureText(xlabel).width),h-9);text(ylabel,7,17);
  for(let j=0;j<=4;j++){const x=xmin+(xmax-xmin)*j/4;line([[X(x),bottom],[X(x),bottom+4]],colors.gray,1);text(Number(x.toFixed(2)).toString(),X(x)-7,bottom+20)}
  const curve=(f,color,a=xmin,b=xmax,dash=[])=>{ctx.save();ctx.beginPath();ctx.rect(left,top,right-left,bottom-top);ctx.clip();line(polyPoints(f,a,b).map(([x,y])=>[X(x),Y(y)]),color,2,dash);ctx.restore()};
  const area=(f,a,b,color)=>fill([[X(a),Y(0)],...polyPoints(f,a,b).map(([x,y])=>[X(x),Y(y)]),[X(b),Y(0)]],color);
  return {X,Y,curve,area,left,right,top,bottom};
 }
 return {w,h,ctx,text,line,fill,dot,circle,plot};
}
const renderers={
 angles(p,s){
  const x=s/32,a=Math.PI*x,cx=p.w*.5,cy=p.h*.57,r=Math.min(p.w*.32,p.h*.35);
  p.circle(cx,cy,r,colors.gray);const arc=Array.from({length:61},(_,j)=>[cx+r*Math.cos(a*j/60),cy-r*Math.sin(a*j/60)]);
  p.fill([[cx,cy],...arc],colors.fill);p.line(arc,colors.green,3);
  const px=cx+r*Math.cos(a),py=cy-r*Math.sin(a);p.line([[cx,cy],[px,py]],colors.green,2);p.line([[px,py],[px,cy]],colors.blue,2,[5,4]);p.line([[cx,cy],[px,cy]],colors.orange,3);p.dot(px,py);
  p.text('Vertical coordinate',12,28,colors.blue);p.text('Horizontal coordinate',12,p.h-13,colors.orange);
  return `x=${frac(rat(s,32))},\\qquad \\text{sector area}=\\frac{\\pi x}{2},\\quad (C(x),S(x))=(\\cos(\\pi x),\\sin(\\pi x)).`;
 },
 rectangles(p,s){
  const N=2**s,a=p.plot(0,1,0,1.12,'input','height');let lo=rat(0),hi=rat(0);
  for(let j=0;j<N;j++){const l=j/N,r=(j+1)/N;lo=add(lo,rat(j*j,N**3));hi=add(hi,rat((j+1)**2,N**3));
   p.fill([[a.X(l),a.Y(0)],[a.X(r),a.Y(0)],[a.X(r),a.Y(r*r)],[a.X(l),a.Y(r*r)]],'#f0dac8');
   p.fill([[a.X(l),a.Y(0)],[a.X(r),a.Y(0)],[a.X(r),a.Y(l*l)],[a.X(l),a.Y(l*l)]],colors.fill);
   p.line([[a.X(l),a.Y(r*r)],[a.X(r),a.Y(r*r)]],colors.orange,1);
  }a.curve(x=>x*x,colors.ink);return `N=${N},\\quad L_N=${frac(lo)},\\quad U_N=${frac(hi)},\\quad U_N-L_N=${frac(sub(hi,lo))}.`;
 },
 secants(p,s){
  const h=1/2**s,a=p.plot(0,2,0,4.3,'input','squared value');a.curve(x=>x*x,colors.gray);
  a.curve(x=>1+(2-h)*(x-1),colors.green,1-h,1);a.curve(x=>1+(2+h)*(x-1),colors.blue,1,1+h);
  a.curve(x=>1+2*(x-1),colors.orange,.35,1.65,[5,4]);for(const x of [1-h,1,1+h])p.dot(a.X(x),a.Y(x*x));
  return `h=${frac(rat(1,2**s))},\\quad 2-h=${frac(sub(rat(2),rat(1,2**s)))},\\quad 2+h=${frac(add(rat(2),rat(1,2**s)))},\\quad \\text{slope gap}=2h.`;
 },
 series(p,N){
  const a=p.plot(0,2,0,1,'sum','');let x=0;
  for(let j=0;j<N;j++){const v=2**(-j);p.fill([[a.X(x),a.Y(.22)],[a.X(x+v),a.Y(.22)],[a.X(x+v),a.Y(.7)],[a.X(x),a.Y(.7)]],j%2?'#b6d8cb':'#8ebfad');p.line([[a.X(x),a.Y(.22)],[a.X(x),a.Y(.7)]],colors.bg,2);x+=v}
  p.fill([[a.X(x),a.Y(.22)],[a.X(2),a.Y(.22)],[a.X(2),a.Y(.7)],[a.X(x),a.Y(.7)]],'#f0dac8');p.text('Included terms',a.left,42,colors.green);p.text('Remaining tail',Math.max(a.left,p.w-155),p.h-47,colors.orange);
  return `S_{${N}}=\\sum_{j=0}^{${N-1}}2^{-j}=${frac(sub(rat(2),rat(1,2**(N-1))))},\\quad 2-S_{${N}}=${frac(rat(1,2**(N-1)))}.`;
 },
 growth(p,s){
  const N=2**s,a=p.plot(0,1,1,2.85,'elapsed time','growth');a.curve(Math.exp,colors.gray);
  let points=[];for(let j=0;j<=N;j++){const y=(1+1/N)**j;points.push([a.X(j/N),a.Y(y)]);p.dot(a.X(j/N),a.Y(y),colors.green,3)}p.line(points,colors.green,2);
  const val=pow(rat(N+1,N),N);return `N=${N},\\quad \\left(1+\\frac1N\\right)^N=${frac(val)}.\\qquad \\text{More periods approach }E(1).`;
 },
 root(p,s){
  let lo=rat(1),hi=rat(2);for(let j=0;j<s;j++){const m=mul(add(lo,hi),rat(1,2));if(m.n*m.n<=2n*m.d*m.d)lo=m;else hi=m}
  const a=p.plot(1,2,1,4.2,'positive root','square');a.curve(x=>x*x,colors.gray);a.curve(()=>2,colors.orange,1,2,[5,4]);
  const l=Number(lo.n)/Number(lo.d),r=Number(hi.n)/Number(hi.d);p.fill([[a.X(l),a.top],[a.X(r),a.top],[a.X(r),a.bottom],[a.X(l),a.bottom]],colors.fill);a.curve(x=>x*x,colors.green,l,r);
  return `\\sqrt2\\in\\left[${frac(lo)},${frac(hi)}\\right],\\qquad \\text{width}=${frac(sub(hi,lo))}.`;
 },
 charts(p,s){
  const d=s/10,R=Math.min(p.w*.3,p.h*.36),cx=p.w*.43,cy=p.h*.53;
  p.circle(cx,cy,R,colors.gray);p.circle(cx+d*R,cy,(1-d)*R,colors.green,true);p.dot(cx,cy,colors.gray);p.dot(cx+d*R,cy);
  p.line([[cx,cy],[cx+d*R,cy]],colors.orange,2);p.text('Original disk',12,25);p.text('Recentered disk stays inside',12,p.h-15,colors.green);
  return `R=1,\\quad d_0=${frac(rat(s,10))},\\quad R_{\\mathrm{new}}=1-d_0=${frac(rat(10-s,10))}.`;
 },
 path(p,s){
  const a=2*Math.PI*s/24,cx=p.w*.5,cy=p.h*.53,r=Math.min(p.w*.3,p.h*.34);
  p.circle(cx,cy,r,colors.gray);p.dot(cx,cy,colors.orange);p.text('Excluded origin',cx-43,cy+23,colors.orange);
  const pts=Array.from({length:145},(_,j)=>[cx+r*Math.cos(a*j/144),cy-r*Math.sin(a*j/144)]);p.line(pts,colors.green,3);const [x,y]=pts.at(-1);p.dot(x,y,colors.blue,6);p.text('Start and end coincide after one turn',12,p.h-12);
  return `\\theta=2\\pi\\cdot${frac(rat(s,24))},\\quad z=e^{i\\theta},\\quad \\operatorname{Log}_{\\mathrm{continued}}(z)=i\\theta.`;
 },
 tails(p,k){
  const eps=2**(-k),T=k+1,a=p.plot(0,T+3,0,.42,'integration variable','density');const f=t=>t*Math.exp(-t);
  a.area(f,eps,T,colors.fill);a.area(f,0,eps,'#c9dced');a.area(f,T,T+3,'#f0dac8');a.curve(f,colors.ink);p.line([[a.X(T),a.top],[a.X(T),a.bottom]],colors.orange,1,[4,4]);p.text('Computed middle',80,37,colors.green);
  return `\\varepsilon=${frac(rat(1,2**k))},\\quad T=${T},\\quad e_0\\le${frac(rat(1,2**(2*k+1)))},\\quad e_\\infty\\le${frac(rat(T+1,2**T))}.`;
 },
 fourier(p,s){
  const N=2**s,a=p.plot(-1,1,0,N*1.1,'period coordinate','kernel height');const f=t=>Math.abs(t)<1e-8?N:(Math.sin(N*Math.PI*t/2)**2)/(N*Math.sin(Math.PI*t/2)**2);
  a.area(f,-1,1,colors.fill);a.curve(f,colors.green);for(const x of [-.25,.25])p.line([[a.X(x),a.top],[a.X(x),a.bottom]],colors.orange,1,[4,4]);
  return `N=${N},\\quad K_N(0)=N,\\quad \\frac12\\int_{-1}^{1}K_N(t)\\,dt=1,\\quad |t|\\ge\\frac14\\Longrightarrow K_N(t)\\le${frac(rat(16,N))}.`;
 },
 pulse(p,s){
  const eps=2**(-s),a=p.plot(-.25,1.25,0,17,'test input','pulse height');p.fill([[a.X(0),a.Y(0)],[a.X(eps),a.Y(0)],[a.X(eps),a.Y(1/eps)],[a.X(0),a.Y(1/eps)]],colors.fill);p.line([[a.X(0),a.Y(0)],[a.X(0),a.Y(1/eps)],[a.X(eps),a.Y(1/eps)],[a.X(eps),a.Y(0)]],colors.green,2);
  p.text('Area stays one',Math.max(50,p.w-140),p.h-52,colors.orange);
  return `\\varepsilon=${frac(rat(1,2**s))},\\quad \\text{height}=${2**s},\\quad \\int p_{\\varepsilon,0}=1,\\quad \\phi(t)=1+t:\\quad \\int p_{\\varepsilon,0}\\phi=1+${frac(rat(1,2**(s+1)))}.`;
 },
 evolution(p,s,choice){
  const t=s/16,a=p.plot(0,2,-1.5,1.5,'time','position');const u=x=>Math.cos(Math.PI*x),v=x=>Math.sin(Math.PI*x);
  a.curve(u,colors.green);a.curve(v,colors.blue,0,2,[5,4]);const c=choice==='sum'?1:choice==='first'?0:1,b=choice==='second'?0:1;
  const f=x=>b*u(x)+c*v(x);if(choice==='sum')a.curve(f,colors.orange);
  p.line([[a.X(t),a.top],[a.X(t),a.bottom]],colors.gray,1);p.dot(a.X(t),a.Y(f(t)),colors.orange,5);
  return `t=${frac(rat(s,16))},\\quad y''+\\pi^2y=0,\\quad y(t)=${b?'C(t)':''}${b&&c?'+':''}${c?'S(t)':''}.`;
 },
 bessel(p,N){
  const a=p.plot(0,4,-.9,1.15,'argument','series value');const prefix=(x,k)=>{let term=1,sum=1;for(let j=1;j<=k;j++){term*=-(x*x/4)/(j*j);sum+=term}return sum};
  a.curve(x=>prefix(x,18),colors.gray);a.curve(x=>prefix(x,N),colors.green);
  const q=rat(4,(N+2)**2),first=rat(4n**BigInt(N+1),fact(N+1)**2n),error=mul(first,rat(q.d,q.d-q.n));
  return `P_${N}(z)=\\sum_{j=0}^{${N}}\\frac{(-1)^j(z^2/4)^j}{(j!)^2},\\quad |z|\\le4:\\quad |J_0(z)-P_${N}(z)|\\le${frac(error)}.`;
 },
 zeta(p,N){
  const a=p.plot(1,12,0,1.1,'term index','term size');a.curve(x=>1/(x*x),colors.gray);
  for(let j=1;j<=Math.min(N,11);j++)p.fill([[a.X(j),a.Y(0)],[a.X(j+1),a.Y(0)],[a.X(j+1),a.Y(1/(j*j))],[a.X(j),a.Y(1/(j*j))]],colors.fill);
  let sum=rat(0);for(let j=1;j<=N;j++)sum=add(sum,rat(1,j*j));p.text(N>11?'Further included terms extend beyond this view':'Included terms in green',60,27,colors.green);
  return `S_${N}=\\sum_{j=1}^{${N}}\\frac1{j^2},\\qquad \\frac1{${N+1}}\\le\\zeta(2)-S_${N}\\le\\frac1{${N}}.`;
 },
 elliptic(p,s){
  const m=s/10,a=p.plot(0,1,0,4.8,'sampling coordinate','integrand height');
  a.curve(x=>1/Math.sqrt((1-x*x)*(1-m*x*x)),colors.orange,0,.975,[5,4]);a.curve(u=>2/Math.sqrt((1+u*u)**2-4*m*u*u),colors.green);
  p.text('Original: rises at the endpoint',60,27,colors.orange);p.text('Transformed: bounded',60,49,colors.green);
  return `m=${frac(rat(s,10))},\\quad x=\\frac{2u}{1+u^2},\\quad g_m(1)=\\frac1{\\sqrt{1-m}}<\\infty.`;
 }
};
function init(figure){
 const canvas=figure.querySelector('canvas'),input=figure.querySelector('input'),select=figure.querySelector('select'),output=figure.querySelector('.visual-output'),value=figure.querySelector('[data-stage-value]');
 let scheduled=false,revision=0;
 async function update(){
  const current=++revision,s=Number(input.value);value.textContent=input.dataset.values?JSON.parse(input.dataset.values)[s]:String(s);
  const math=renderers[figure.dataset.visual](painter(canvas),s,select?.value);figure.dataset.stage=String(s);output.dataset.latex=math;
  // Serialize MathJax work so rapid input cannot typeset a superseded stage.
  figure._typeset=(figure._typeset||Promise.resolve()).then(async()=>{
   if(current!==revision)return;
   await window.MathJax?.startup?.promise;if(current!==revision)return;
   window.MathJax?.typesetClear?.([output]);const shown=innerWidth<600?'\\begin{gathered}'+math.split(/\\(?:qquad|quad)\s*/).map(part=>part.replace(/[,;]\s*$/, '')).join('\\\\')+'\\end{gathered}':math;output.textContent='\\['+shown+'\\]';await window.MathJax?.typesetPromise?.([output]);
  }).catch(e=>console.error('Chapter visual typesetting:',e));
 }
 function schedule(){if(!scheduled){scheduled=true;requestAnimationFrame(()=>{scheduled=false;update()})}}
 figure.querySelector('[data-visual-reset]').addEventListener('click',()=>{input.value=input.defaultValue;if(select)select.value='sum';schedule()});
 input.addEventListener('input',schedule);select?.addEventListener('change',schedule);new ResizeObserver(schedule).observe(canvas);update();
}
document.querySelectorAll('[data-visual]').forEach(init);
})();
