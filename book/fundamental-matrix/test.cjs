'use strict';
const assert=require('node:assert/strict'),E=require('./engine.js');
let tests=0;const check=(x,m)=>{assert.ok(x,m);tests++;};
const eq=(a,b,m)=>check(E.samePoly(a,b),m);
const p=(...x)=>E.poly(...x),q=(a,b=1)=>new E.Q(a,b);
check(q(2,4).toString()==='1/2','Reduction');check(q(-1,-3).toString()==='1/3','Sign');
for(const id of Object.keys(E.models)){
  const start=performance.now(),cache=E.build(id),m=cache.model,d=m.A.length;
  console.log(id,'cache ms',Math.round(performance.now()-start));
  for(let n=1;n<=36;n++){
    const rhs=E.matMul(cache.aug,cache.terms[n-1]);
    for(let i=0;i<=d;i++)for(let j=0;j<=d;j++){
      eq(E.derivative(cache.terms[n][i][j]),rhs[i][j],`${id}: exact recursive derivative at ${n}`);
      check(E.evaluate(cache.terms[n][i][j],q(0)).p===0n,'Positive terms start at zero');
    }
  }
  for(const initial of [m.initial,m.initial.map(()=>0),m.initial.map((_,i)=>i%2?-2:3)])for(const force of [-2,0,1,2]){
    const ref=E.reference(m,initial,force);
    for(const N of [0,1,2,4,8,16,24,36]){
      const x=E.solutionPolynomials(cache,N,initial,force),bound=E.solutionBound(cache,N,initial,force,x).number();
      for(let j=0;j<=20;j++){
        const t=m.T.mul(q(j,20)),v=ref(t.number());
        for(let i=0;i<d;i++){
          const observed=Math.abs(E.evaluate(x[i],t).number()-v[i]);
          check(observed<=bound+1e-10*(1+Math.abs(v[i])),`${id} N=${N}, t=${t}: sampled consistency of the proven bound`);
        }
      }
      if(N<36){
        const next=E.solutionPolynomials(cache,N+1,initial,force);
        for(let i=0;i<d;i++){
          const rhs=m.A[i].reduce((s,a,j)=>E.add(s,E.mul(a,x[j])),E.scale(m.b[i],force));
          eq(next[i],E.add(p(initial[i]),E.integral(rhs)),`${id}: Picard and matrix iteration agree`);
        }
      }
    }
  }
}
let c=E.build('triangular');
eq(c.sums[2][0][2],p(0,0,0,q(1,6)),'Ordered t^3/6, not t^3/4');
check(c.terms[4].flat().every(E.isZero),'Augmented triangular series terminates');
let x=E.solutionPolynomials(c,3,[0,0,0],1);
eq(x[0],p(0,0,0,0,q(1,12)),'Forced triangular coordinate 1');eq(x[1],p(0,0,0,q(1,3)),'Forced triangular coordinate 2');eq(x[2],p(0,1),'Forced triangular coordinate 3');
check(E.solutionBound(c,3,[0,0,0],1,x).p===0n,'Exact residual gives zero error');
c=E.build('airy');x=E.solutionPolynomials(c,12,[0,0],1);
for(const [k,den] of [[2,2],[5,40],[8,2240],[11,246400]])check(x[0][k].cmp(q(1,den))===0,'Forced Airy coefficients');
for(const [val,m,e] of [[q(1001,1000),'1.01',0],[q(99999,10000),'1.00',1],[q(1,3000),'3.34',-4],[q(1,10**6),'1.00',-6]]){
 const up=E.upperScientific(val);check(up.mantissa===m&&up.exponent===e,'Outward bound formatting');
}
console.log(`PASS: ${tests} exact algebraic or explicitly sampled numerical checks.`);
