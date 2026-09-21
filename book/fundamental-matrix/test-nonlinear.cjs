'use strict';
const assert=require('node:assert/strict'), E=require('./nonlinear.js');
let tests=0;
const check=(v,m)=>{assert.ok(v,m);tests++;};
const eq=(a,b,m)=>check(E.samePoly(a,b),m);
const q=(a,b=1)=>new E.Q(a,b), p=(...xs)=>E.poly(...xs);
const growth=E.build('growth'), saturation=E.build('saturation');
eq(growth.iterates[2],p(1,1,1,q(1,3)),'Actual second Picard iterate');
eq(growth.iterates[3],p(1,1,1,1,q(2,3),q(1,3),q(1,9),q(1,63)),'Exact third growth iterate');
eq(saturation.iterates[3],p(0,1,0,q(-1,3),0,q(2,15),0,q(-1,63)),'Exact third saturation iterate');
check(growth.iterates[2][3].cmp(1)!==0,'Picard is not Taylor truncation');
for(const cache of [growth,saturation]){
  const {model:m,iterates:ps}=cache;
  check(E.build(m.id)===cache,'Cached nonlinear iterates');
  assert.throws(()=>E.build(m.id,8),RangeError);
  assert.throws(()=>E.solutionPolynomials(cache,1,[5],0),RangeError);
  assert.throws(()=>E.solutionPolynomials(cache,1,m.initial,1),RangeError);
  let previousBound;
  for(let N=0;N<=m.maxN;N++){
    const x=E.solutionPolynomials(cache,N,m.initial,0);
    check(E.evaluate(x[0],q(0)).cmp(m.initial[0])===0,'Initial data');
    if(N){
      const square=E.mul(ps[N-1],ps[N-1]);
      eq(E.derivative(x[0]),m.id==='growth'?square:E.add(p(1),E.scale(square,-1)),'Exact Picard recurrence');
      check(x[0].length===2**N,'Full degree, without Taylor truncation');
    }
    const bound=E.solutionBound(cache,N,m.initial,0,x);
    check(bound.cmp(0)>0,'Positive nonlinear bound');
    if(previousBound)check(bound.cmp(previousBound)<=0,'Uniform bound improves');
    previousBound=bound;
    if(m.id==='growth'){
      ps[N].forEach(c=>check(c.cmp(0)>=0&&c.cmp(1)<=0,'Coefficient between zero and one'));
      for(let j=0;j<=N;j++)check(ps[N][j].cmp(1)===0,'First N+1 coefficients stabilize');
    }
    for(let j=0;j<=40;j++){
      const t=m.T.mul(q(j,40)),a=E.evaluate(x[0],t);
      if(m.id==='growth'){
        const exact=E.O.div(E.O.sub(t)),error=exact.sub(a);
        check(error.cmp(0)>=0&&error.cmp(bound)<=0,'Exact rational sampled growth error');
        const geometric=m.T.pow(N+1).div(E.O.sub(m.T));
        check(error.cmp(geometric)<=0,'Exact rational sampled geometric estimate');
      }else{
        check(a.cmp(0)>=0&&a.cmp(t)<=0,'Sampled invariant range');
        const reference=Math.tanh(t.number());
        check(Math.abs(a.number()-reference)<=bound.number()+2e-14,'Sampled saturation error consistency');
        if(N){
          const b=E.evaluate(ps[N-1],t),lo=a.cmp(b)<=0?a:b,hi=a.cmp(b)<=0?b:a;
          check(lo.number()<=reference+2e-14&&reference<=hi.number()+2e-14,'Adjacent iterates bracket reference at samples');
        }
      }
    }
  }
}
// Loading the extension must not change the existing matrix path.
for(const id of ['exponential','scalar','oscillator','triangular','airy']){
 const c=E.build(id),m=c.model,x=E.solutionPolynomials(c,m.N,m.initial,m.force);
 check(!c.iterates&&c.sums.length===37,'Linear cache retained');
 check(E.solutionBound(c,m.N,m.initial,m.force,x).cmp(0)>=0,'Linear bound retained');
}
console.log(`PASS: ${tests} nonlinear exact-algebra and explicitly sampled consistency checks.`);
