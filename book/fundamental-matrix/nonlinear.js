/* Scalar nonlinear Picard iteration. Every iterate is an exact polynomial. */
(function (root) {
  'use strict';
  const E = typeof module !== 'undefined' && module.exports ? require('./engine.js') : root.ODEEngine;
  const {Q, O, Z, poly, add, scale, mul, integral, evaluate} = E;
  const linear = {build:E.build, solutionPolynomials:E.solutionPolynomials,
    solutionBound:E.solutionBound, reference:E.reference};
  const models = {
    growth: {id:'growth', nonlinear:true, initial:[1], force:0, T:new Q(3,4),
      N:3, maxN:7, labels:['y'], forcing:'Initial value fixed at y(0) = 1.'},
    saturation: {id:'saturation', nonlinear:true, initial:[0], force:0, T:new Q(1),
      N:3, maxN:7, labels:['y'], forcing:'Initial value fixed at y(0) = 0.'}
  };
  Object.assign(E.models, models);
  const caches = new Map();
  function next(id, p) {
    if(id==='growth') return add(poly(1), integral(mul(p,p)));
    if(id==='saturation') return add(poly(0,1), scale(integral(mul(p,p)), -1));
    throw new RangeError('Unknown nonlinear example.');
  }
  function validate(cache, N, initial, force) {
    const m=cache.model;
    if(!Number.isInteger(N)||N<0||N>=cache.iterates.length)
      throw new RangeError('Invalid nonlinear iteration count.');
    if(initial.length!==1||Q.of(initial[0]).cmp(m.initial[0])!==0||Q.of(force).cmp(0)!==0)
      throw new RangeError('The nonlinear examples have fixed initial data and no forcing control.');
  }
  E.build = function(id, maxN) {
    if(!models[id]) return linear.build(id, maxN);
    const m=models[id], n=maxN===undefined?m.maxN:maxN;
    if(!Number.isInteger(n)||n<0||n>m.maxN) throw new RangeError('Nonlinear iteration limit exceeded.');
    const key=id+':'+n;
    if(caches.has(key))return caches.get(key);
    const iterates=[poly(m.initial[0])];
    for(let k=1;k<=n;k++)iterates.push(next(id,iterates[k-1]));
    const cache={model:m, iterates}; caches.set(key,cache);return cache;
  };
  E.solutionPolynomials = function(cache,N,initial,force) {
    if(!cache.model.nonlinear)return linear.solutionPolynomials(cache,N,initial,force);
    validate(cache,N,initial,force);return [cache.iterates[N]];
  };
  E.solutionBound = function(cache,N,initial,force,x) {
    if(!cache.model.nonlinear)return linear.solutionBound(cache,N,initial,force,x);
    validate(cache,N,initial,force);
    const {id,T}=cache.model;
    // Growth: 0 <= y - p_N and its derivative is nonnegative on [0,T].
    // Thus its maximum is exactly the rational endpoint error.
    if(id==='growth')return O.div(O.sub(T)).sub(evaluate(cache.iterates[N],T));
    // Saturation: even iterates increase, odd iterates decrease on [0,1].
    // Consecutive iterates bracket the solution and their gap increases in t.
    // The endpoint gap is a uniform bound, independent of the tanh reference.
    if(N===0)return T;
    return evaluate(add(cache.iterates[N],scale(cache.iterates[N-1],-1)),T).abs();
  };
  E.reference = function(model,initial,force) {
    if(model.id==='growth')return t=>[1/(1-t)];
    if(model.id==='saturation')return t=>[Math.tanh(t)];
    return linear.reference(model,initial,force);
  };
  E.nonlinearNext=next;
  E.nonlinearBoundNote=function(id,N) {
    if(id==='growth')return 'Uniform on [0, 3/4]: the error increases with t, so this is the exact error at 3/4, rounded upward. The solution blows up at t = 1. Drawing errors are not included.';
    return 'Uniform on [0, 1]: '+(N===0?'0 ≤ y(t) ≤ t.':'consecutive Picard iterates bracket the solution; their largest gap is at t = 1.')+' Drawing errors are not included.';
  };
  if(typeof module!=='undefined'&&module.exports)module.exports=E;
})(typeof globalThis!=='undefined'?globalThis:this);
