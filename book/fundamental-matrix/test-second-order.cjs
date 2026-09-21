'use strict';
// Finite polynomial identities, not sampled plots or a numerical ODE solver.
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path');
const E=require('./engine.js'),{Q,poly,add,scale,mul,integral,derivative,samePoly}=E;
const J=f=>integral(integral(f)),one=poly(1),t=poly(0,1);
const q=(p,d=1)=>new Q(p,d);let checks=0;
const eq=(a,b,label)=>{assert.ok(samePoly(a,b),label);checks++;};
const ok=(v,label)=>{assert.ok(v,label);checks++;};
const coeff=(f,n)=>f[n]||q(0);
function series(entries){const p=Array.from({length:1+Math.max(0,...entries.map(([k])=>k))},()=>q(0));for(const [k,v] of entries)p[k]=v;return p;}
function fact(n){let f=1n;for(let i=2;i<=n;i++)f*=BigInt(i);return f;}
function initial(f,a,b){ok(coeff(f,0).cmp(a)===0,'initial position');ok(coeff(f,1).cmp(b)===0,'initial velocity');}
for(let k=0;k<=20;k++)eq(J(series([[k,q(1)]])),series([[k+2,q(1,(k+1)*(k+2))]]),'two integrations of monomial');
let u=one,v=t;
for(let n=0;n<=8;n++){
  eq(u,series(Array.from({length:n+1},(_,k)=>[2*k,q((-1n)**BigInt(k),fact(2*k))])),'cosine iterate');
  eq(v,series(Array.from({length:n+1},(_,k)=>[2*k+1,q((-1n)**BigInt(k),fact(2*k+1))])),'sine iterate');
  initial(u,1,0);initial(v,0,1);
  u=add(one,scale(J(u),-1));v=add(t,scale(J(v),-1));
}
u=one;v=t;let eu=one,ev=t,cu=q(1),cv=q(1);
for(let n=1;n<=6;n++){
  u=add(one,J(mul(t,u)));v=add(t,J(mul(t,v)));
  cu=cu.div((3*n-1)*(3*n));cv=cv.div((3*n)*(3*n+1));
  eu=add(eu,series([[3*n,cu]]));ev=add(ev,series([[3*n+1,cv]]));
  eq(u,eu,'Airy position iteration');eq(v,ev,'Airy velocity iteration');initial(u,1,0);initial(v,0,1);
}
let p=one;
const nonlinear=[];
for(let n=0;n<=3;n++){nonlinear.push(p);initial(p,1,0);p=add(one,J(mul(p,p)));}
eq(nonlinear[1],poly(1,0,q(1,2)),'first nonlinear iterate');
eq(nonlinear[2],series([[0,q(1)],[2,q(1,2)],[4,q(1,12)],[6,q(1,120)]]),'second nonlinear iterate');
eq(nonlinear[3],series([[0,q(1)],[2,q(1,2)],[4,q(1,12)],[6,q(1,72)],[8,q(1,560)],[10,q(11,64800)],[12,q(1,95040)],[14,q(1,2620800)]]),'complete third nonlinear iterate');
// The nonlinear solution's Taylor coefficients are computed independently.
let c=[q(1),q(0)];
for(let k=0;k<8;k++)c[k+2]=coeff(mul(c,c),k).div((k+1)*(k+2));
ok(coeff(c,6).cmp(q(1,72))===0,'Taylor t^6 coefficient differs from second Picard iterate');
ok(q(4).mul(q(1,2).pow(2)).div(2).cmp(q(1,2))===0,'nonlinear contraction constant');
let w=poly(0),ew=poly(0),cw=q(1);
for(let n=1;n<=5;n++){
  w=J(add(mul(t,w),one));cw=cw.div((3*n-2)*(3*n-1));
  ew=add(ew,series([[3*n-1,cw]]));eq(w,ew,'forced Airy iterate');initial(w,0,0);
}
// Resonant response: exact Taylor identity for y''+y=cos t.
const sin=series(Array.from({length:10},(_,k)=>[2*k+1,q((-1n)**BigInt(k),fact(2*k+1))]));
const cos=series(Array.from({length:10},(_,k)=>[2*k,q((-1n)**BigInt(k),fact(2*k))]));
const resonant=scale(mul(t,sin),q(1,2)),constant=add(one,scale(cos,-1));
for(let k=0;k<=16;k++){
  ok(coeff(add(derivative(derivative(resonant)),resonant),k).cmp(coeff(cos,k))===0,'resonance ODE');
  ok(coeff(add(derivative(derivative(constant)),constant),k).cmp(k===0?1:0)===0,'constant forced oscillator');
}
initial(resonant,0,0);initial(constant,0,0);
// The matrix and scalar iteration have different finite-stage numbering.
const cache=E.build('oscillator',12);u=one;v=t;
for(let n=0;n<=5;n++){
 eq(cache.sums[2*n][0][0],u,'two scalar integrations versus two state iterations for u');
 eq(cache.sums[2*n+1][0][1],v,'stage shift for initial velocity');
 u=add(one,scale(J(u),-1));v=add(t,scale(J(v),-1));
}
const text=fs.readFileSync(path.join(__dirname,'index.template.html'),'utf8');
for(const latex of [String.raw`\frac{t^6}{120}`,String.raw`\frac{t^6}{72}`,String.raw`\frac{11t^{10}}{64800}`,String.raw`\frac{t^{12}}{95040}`,String.raw`\frac{t^{14}}{2620800}`,String.raw`\frac{t^8}{2240}`,String.raw`\frac{u(s)v(t)-v(s)u(t)}{W(s)}`])ok(text.includes(latex),'checked formula is present in authored text');
const sections=['iteration','oscillator','nonlinear','airy','matrix','forcing','convergence'];
let last=-1;for(const id of sections){const at=text.indexOf(`<section id="${id}">`);ok(at>last,`narrative order: ${id}`);last=at;}
ok(!/<script\b|<input\b|<select\b|<svg\b/.test(text),'no notebook or plotting assets');
console.log(`PASS: ${checks} exact second-order algebra and authored-content checks (no numerical sampling).`);
