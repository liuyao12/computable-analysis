/* Exact rational port of piMachin.compute and nBallVolumeModelInterval.
   Browser code is regression checked against Lean, not extracted or verified JS. */
(function (root) {
  'use strict';
  const gcd = (a,b) => { a=a<0n?-a:a; while(b){const t=a%b;a=b;b=t;} return a; };
  function Q(a,b=1n) {
    a=BigInt(a);b=BigInt(b);
    if (!b) throw Error('The denominator must be nonzero.');
    if(b<0n){a=-a;b=-b;} const g=gcd(a,b); return {a:a/g,b:b/g};
  }
  const add=(x,y)=>Q(x.a*y.b+y.a*x.b,x.b*y.b);
  const sub=(x,y)=>Q(x.a*y.b-y.a*x.b,x.b*y.b);
  const mul=(x,y)=>Q(x.a*y.a,x.b*y.b);
  const div=(x,y)=>Q(x.a*y.b,x.b*y.a);
  const pow=(x,n)=>Q(x.a**BigInt(n),x.b**BigInt(n));
  const cmp=(x,y)=>{const d=x.a*y.b-y.a*x.b;return d<0n?-1:d>0n?1:0;};
  const str=x=>x.b===1n?String(x.a):`${x.a}/${x.b}`;
  const tex=x=>x.b===1n?String(x.a):`\\frac{${x.a}}{${x.b}}`;
  function parse(s) {
    s=s.trim();
    if(s.length>40) throw Error('Use at most 40 characters for the radius.');
    if(/^\d+\/\d+$/.test(s)){const [a,b]=s.split('/');return Q(a,b);}
    if(!/^(\d+\.?\d*|\.\d+)$/.test(s)) throw Error('Enter a nonnegative decimal or fraction, such as 1.5 or 3/2.');
    const [a,b='']=s.split('.');
    if(b.length>12) throw Error('Use at most 12 decimal places.');
    return Q((a||'0')+b,10n**BigInt(b.length));
  }
  function atanInv(d,n){
    const y=Q(1,d), yy=mul(y,y); let lo=Q(0),hi=y,p=mul(yy,y);
    for(let i=0;i<n;i++){
      lo=sub(hi,div(p,Q(4*i+3)));p=mul(p,yy);
      hi=add(lo,div(p,Q(4*i+5)));p=mul(p,yy);
    }
    return {lo,hi};
  }
  const piCache=new Map();
  function piBox(stage){
    if(!Number.isInteger(stage)||stage<1||stage>80)throw Error('Precision stage must be between 1 and 80.');
    if(!piCache.has(stage)){
      const a=atanInv(5,stage),b=atanInv(239,stage);
      piCache.set(stage,{lo:sub(mul(Q(16),a.lo),mul(Q(4),b.hi)),hi:sub(mul(Q(16),a.hi),mul(Q(4),b.lo))});
    }
    return piCache.get(stage);
  }
  function coeff(n){let c=Q(n%2?2:1);for(let k=n%2+2;k<=n;k+=2)c=mul(Q(2,k),c);return c;}
  function gammaCoeff(n){let c=Q(n%2?1:1,n%2?2:1);for(let k=n%2+2;k<=n;k+=2)c=mul(Q(k,2),c);return c;}
  function model(n,p,r){return mul(mul(coeff(n),pow(p,Math.floor(n/2))),pow(r,n));}
  function stageVolume(n,r,stage){const p=piBox(stage);return {lo:model(n,p.lo,r),hi:model(n,p.hi,r)};}
  function decimal(x,digits,up=false){
    // Nonnegative endpoints only. Round outwards, never to nearest.
    if(x.a<0n)throw Error('Expected a nonnegative bound.');
    const scale=10n**BigInt(digits),num=x.a*scale;
    let k=num/x.b;if(up&&num%x.b)k++;
    const s=k.toString().padStart(digits+1,'0');
    return digits?s.slice(0,-digits)+'.'+s.slice(-digits):s;
  }
  function compute(n,r,digits=8){
    if(!Number.isInteger(n)||n<0||n>64)throw Error('Choose an integer dimension from 0 to 64.');
    if(cmp(r,Q(0))<0||cmp(r,Q(10))>0)throw Error('Choose a radius between zero and ten.');
    if(![4,8,12].includes(digits))throw Error('Choose 4, 8 or 12 decimal places.');
    const target=Q(1,10n**BigInt(digits+1));
    for(let stage=2;stage<=80;stage+=2){
      const volume=stageVolume(n,r,stage);
      const area=n>0&&r.a>0n?{lo:div(mul(Q(n),volume.lo),r),hi:div(mul(Q(n),volume.hi),r)}:null;
      if(cmp(sub(volume.hi,volume.lo),target)<=0&&(!area||cmp(sub(area.hi,area.lo),target)<=0))return {n,r,digits,stage,volume,area,pi:piBox(stage)};
    }
    throw Error('Precision limit reached. Reduce dimension, radius or decimal places.');
  }
  const api={Q,add,sub,mul,div,pow,cmp,str,tex,parse,coeff,gammaCoeff,piBox,model,stageVolume,decimal,compute};
  if(typeof module!=='undefined'&&module.exports)module.exports=api;
  root.NBallCalculator=api;
})(globalThis);
