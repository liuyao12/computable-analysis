/* Exact rational polynomial Peano–Baker engine. No numerical ODE solver. */
(function (root) {
  'use strict';
  function gcd(a, b) { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a,b] = [b,a%b]; return a; }
  class Q {
    constructor(p = 0n, q = 1n) {
      p = BigInt(p); q = BigInt(q);
      if (!q) throw new RangeError('A rational denominator cannot be zero.');
      if (q < 0n) { p=-p; q=-q; }
      const g = gcd(p,q); this.p=p/g; this.q=q/g;
    }
    static of(x) { return x instanceof Q ? x : new Q(x); }
    add(x) { x=Q.of(x); return new Q(this.p*x.q+x.p*this.q,this.q*x.q); }
    sub(x) { x=Q.of(x); return new Q(this.p*x.q-x.p*this.q,this.q*x.q); }
    mul(x) { x=Q.of(x); return new Q(this.p*x.p,this.q*x.q); }
    div(x) { x=Q.of(x); if(!x.p) throw new RangeError('Division by zero.'); return new Q(this.p*x.q,this.q*x.p); }
    abs() { return this.p<0n ? new Q(-this.p,this.q) : this; }
    neg() { return new Q(-this.p,this.q); }
    cmp(x) { x=Q.of(x); const d=this.p*x.q-x.p*this.q; return d<0n?-1:d>0n?1:0; }
    pow(n) { if(!Number.isInteger(n)||n<0) throw new RangeError('A power must be a nonnegative integer.'); return new Q(this.p**BigInt(n),this.q**BigInt(n)); }
    number() {
      const p=Number(this.p), q=Number(this.q); if(Number.isFinite(p)&&Number.isFinite(q)) return p/q;
      if(!this.p) return 0;
      const a=(this.p<0n?-this.p:this.p).toString(), b=this.q.toString();
      return (this.p<0n?-1:1)*(Number(a.slice(0,16))/Number(b.slice(0,16)))*10**((a.length-Math.min(16,a.length))-(b.length-Math.min(16,b.length)));
    }
    toString() { return this.q===1n?String(this.p):`${this.p}/${this.q}`; }
  }
  const Z=new Q(), O=new Q(1), ZERO=()=>[Z], ONE=()=>[O];
  const poly=(...xs)=>trim(xs.map(Q.of));
  function trim(p) { while(p.length>1&&!p[p.length-1].p)p.pop(); return p; }
  function add(a,b) { const r=Array.from({length:Math.max(a.length,b.length)},(_,i)=>(a[i]||Z).add(b[i]||Z)); return trim(r); }
  function scale(a,q) { q=Q.of(q); return !q.p?ZERO():trim(a.map(x=>x.mul(q))); }
  function mul(a,b) {
    if(isZero(a)||isZero(b)) return ZERO();
    const c=Array.from({length:a.length+b.length-1},()=>Z);
    for(let i=0;i<a.length;i++)if(a[i].p)for(let j=0;j<b.length;j++)if(b[j].p)c[i+j]=c[i+j].add(a[i].mul(b[j]));
    return trim(c);
  }
  function integral(a) { return trim([Z,...a.map((x,i)=>x.div(i+1))]); }
  function derivative(a) { return a.length===1?ZERO():trim(a.slice(1).map((x,i)=>x.mul(i+1))); }
  function evaluate(a,t) { t=Q.of(t); let v=Z; for(let i=a.length-1;i>=0;i--)v=v.mul(t).add(a[i]); return v; }
  function numericCoefficients(a) { return a.map(x=>x.number()); }
  function evalFloat(a,t) { let v=0;for(let i=a.length-1;i>=0;i--)v=v*t+a[i];return v; }
  function isZero(a) { return a.every(x=>!x.p); }
  function samePoly(a,b) { return isZero(add(a,scale(b,-1))); }
  function identity(d) {return Array.from({length:d},(_,i)=>Array.from({length:d},(_,j)=>i===j?ONE():ZERO()));}
  function matMul(a,b) {
    return a.map(row=>b[0].map((_,j)=>row.reduce((s,p,k)=>add(s,mul(p,b[k][j])),ZERO())));
  }
  function matAdd(a,b) {return a.map((row,i)=>row.map((p,j)=>add(p,b[i][j])));}
  function matIntegral(a) {return a.map(row=>row.map(integral));}
  function absoluteBound(p,T) {return evaluate(p.map(x=>x.abs()),T);}
  function matrixBound(A,T) {return A.reduce((m,row)=>{const v=row.reduce((s,p)=>s.add(absoluteBound(p,T)),Z);return v.cmp(m)>0?v:m;},Z);}
  function vectorBound(b,T) {return b.reduce((m,p)=>{const v=absoluteBound(p,T);return v.cmp(m)>0?v:m;},Z);}
  function maxAbs(xs) {return xs.reduce((m,x)=>{x=Q.of(x).abs();return x.cmp(m)>0?x:m;},Z);}
  function factorial(n) {let r=1n;for(let j=2;j<=n;j++)r*=BigInt(j);return r;}
  function tailBound(N,z) {
    if(!Number.isInteger(N)||N<0) throw new RangeError('N must be nonnegative.');
    z=Q.of(z);if(z.p<0n)throw new RangeError('The norm bound must be nonnegative.');
    if(!z.p)return Z;
    let k=N+1, term=z.pow(k).div(new Q(factorial(k))), total=Z;
    // Sum finitely until a positive geometric majorant is available.
    while(z.cmp(k+1)>=0){total=total.add(term);k++;term=term.mul(z).div(k);}
    return total.add(term.div(O.sub(z.div(k+1))));
  }
  const models={
    exponential:{id:'exponential',A:[[poly(1)]],b:[poly(0)],initial:[1],force:0,T:new Q(2),N:4,labels:['y'],forcing:'There is no forcing in this introductory example.'},
    scalar:{id:'scalar',A:[[poly(0,2)]],b:[poly(0,2)],initial:[0],force:1,T:new Q(3,2),N:5,labels:['y'],forcing:'The fixed forcing profile is 2t. Its amplitude is λ.'},
    oscillator:{id:'oscillator',A:[[poly(0),poly(1)],[poly(-1),poly(0)]],b:[poly(0),poly(1)],initial:[0,0],force:1,T:new Q(6),N:12,labels:['y','y′'],forcing:'The forcing in y″ + y = λ is constant. The resonant cosine forcing is worked out in the text.'},
    triangular:{id:'triangular',A:[[poly(0),poly(1),poly(0)],[poly(0),poly(0),poly(0,1)],[poly(0),poly(0),poly(0)]],b:[poly(0),poly(0),poly(1)],initial:[0,0,1],force:0,T:new Q(3),N:1,labels:['x₁','x₂','x₃'],forcing:'A constant input λ enters the third coordinate. Try initial state (0,0,0), λ = 1 and N = 3.'},
    airy:{id:'airy',A:[[poly(0),poly(1)],[poly(0,1),poly(0)]],b:[poly(0),poly(1)],initial:[1,0],force:0,T:new Q(5,2),N:6,labels:['y','y′'],forcing:'The equation is y″ = ty + λ. Initial data (1,0) gives u, (0,1) gives v; (0,0) with λ = 1 gives w.'}
  };
  const caches=new Map();
  function build(id,maxN=36) {
    if(!models[id])throw new RangeError('Unknown example.');
    const key=`${id}:${maxN}`;if(caches.has(key))return caches.get(key);
    const model=models[id],d=model.A.length;
    const aug=model.A.map((row,i)=>[...row,model.b[i]]);aug.push(Array.from({length:d+1},ZERO));
    let p=identity(d+1),s=p;const terms=[p],sums=[s];
    for(let n=1;n<=maxN;n++){p=matIntegral(matMul(aug,p));s=matAdd(s,p);terms.push(p);sums.push(s);}
    const out={model,terms,sums,aug,M:matrixBound(model.A,model.T),B:vectorBound(model.b,model.T)};
    caches.set(key,out);return out;
  }
  function solutionPolynomials(cache,N,initial,force) {
    const d=cache.model.A.length;
    if(initial.length!==d||!Number.isInteger(N)||N<0||N>=cache.sums.length)throw new RangeError('Invalid state or iteration count.');
    const z=[...initial,force].map(Q.of);
    return cache.sums[N].slice(0,d).map(row=>row.reduce((s,p,j)=>add(s,scale(p,z[j])),ZERO()));
  }
  function residual(model,x,force) {
    return x.map((p,i)=>{
      const rhs=model.A[i].reduce((s,a,j)=>add(s,mul(a,x[j])),scale(model.b[i],force));
      return add(derivative(p),scale(rhs,-1));
    });
  }
  function solutionBound(cache,N,initial,force,x) {
    if(residual(cache.model,x,force).every(isZero))return Z;
    // A zero matrix term forces every subsequent term to vanish as well.
    if(cache.terms[cache.terms.length-1].flat().every(isZero)){
      const exact=solutionPolynomials(cache,cache.sums.length-1,initial,force);
      return vectorBound(exact.map((p,i)=>add(p,scale(x[i],-1))),cache.model.T);
    }
    const R=maxAbs(initial),B=cache.B.mul(Q.of(force).abs()),M=cache.M,T=cache.model.T;
    if(!M.p)return N===0?B.mul(T):Z;
    return R.add(B.div(M)).mul(tailBound(N,M.mul(T)));
  }
  function reference(model,initial,force) {
    const a=initial.map(Number),f=Number(force);
    if(model.id==='exponential')return t=>[a[0]*Math.exp(t)];
    if(model.id==='scalar')return t=>[(a[0]+f)*Math.exp(t*t)-f];
    if(model.id==='oscillator')return t=>[a[0]*Math.cos(t)+a[1]*Math.sin(t)+f*(1-Math.cos(t)),-a[0]*Math.sin(t)+a[1]*Math.cos(t)+f*Math.sin(t)];
    if(model.id==='triangular')return t=>[a[0]+a[1]*t+a[2]*t**3/6+f*t**4/12,a[1]+a[2]*t*t/2+f*t**3/3,a[2]+f*t];
    // Independent scalar coefficient recurrence, not the matrix iteration.
    const c=Array.from({length:121},()=>Z);c[0]=Q.of(initial[0]);c[1]=Q.of(initial[1]);c[2]=Q.of(force).div(2);
    for(let n=1;n<=118;n++)c[n+2]=c[n-1].div((n+1)*(n+2));
    const u=numericCoefficients(c),v=numericCoefficients(derivative(c));
    return t=>[evalFloat(u,t),evalFloat(v,t)];
  }
  // Three significant digits, rounded UP using integers, not floating-point logs.
  function upperScientific(q,digits=3) {
    q=Q.of(q);if(!q.p)return {zero:true,mantissa:'0',exponent:0};
    if(q.p<0n)throw new RangeError('An error bound cannot be negative.');
    let e=q.p.toString().length-q.q.toString().length;
    const gePower=k=>k>=0?q.p>=q.q*10n**BigInt(k):q.p*10n**BigInt(-k)>=q.q;
    if(!gePower(e))e--;else if(gePower(e+1))e++;
    const shift=digits-1-e;
    let p=q.p,d=q.q;if(shift>=0)p*=10n**BigInt(shift);else d*=10n**BigInt(-shift);
    let v=(p+d-1n)/d;
    if(v>=10n**BigInt(digits)){v=(v+9n)/10n;e++;}
    const str=v.toString().padStart(digits,'0');
    return {zero:false,mantissa:str[0]+'.'+str.slice(1),exponent:e};
  }
  const api={Q,Z,O,poly,add,scale,mul,integral,derivative,evaluate,numericCoefficients,evalFloat,isZero,samePoly,identity,matMul,matAdd,matIntegral,models,build,solutionPolynomials,solutionBound,residual,reference,tailBound,upperScientific};
  if(typeof module!=='undefined'&&module.exports)module.exports=api;
  else root.ODEEngine=api;
})(typeof globalThis!=='undefined'?globalThis:this);
