(() => {
  'use strict';
  const $ = id => document.getElementById(id);
  let mathQueue = Promise.resolve();
  function formula(el, latex) {
    mathQueue = mathQueue.then(async () => {
      if (window.MathJax?.startup?.promise) await MathJax.startup.promise;
      if (window.MathJax?.typesetClear) MathJax.typesetClear([el]);
      el.textContent = `\\(${latex}\\)`;
      if (window.MathJax?.typesetPromise) await MathJax.typesetPromise([el]);
    });
  }
  const line = (x1,y1,x2,y2) => `<line class="axis" x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}"/>`;
  const dot = (x,y,c='point',r=5) => `<circle class="${c}" cx="${x}" cy="${y}" r="${r}"/>`;
  function zeros() {
    const count = Number($('zero-count').value);
    $('zero-plot').innerHTML = '<title>Zeros approaching the excluded origin at the left endpoint</title>' +
      line(28,55,612,55) + Array.from({length:count},(_,k)=>dot(28+1750/((k+1)*Math.PI),55,'zero',4)).join('') + dot(28,55,'excluded',6);
    formula($('zero-readout'), `N=${count},\\quad z_N=\\frac{1}{${count}\\pi}\\approx ${(1/(count*Math.PI)).toFixed(5)},\\quad 0\\notin D`);
  }
  function loops() {
    const mode=$('loop-function').value, angle=Number($('loop-angle').value), t=angle*Math.PI/180;
    const value = u => mode==='log' ? [0,u] : mode==='sqrt' ? [Math.cos(u/2),Math.sin(u/2)] : [Math.cos(u),-Math.sin(u)];
    const scale=mode==='log' ? 8 : 85;
    const input=[155+85*Math.cos(t),125-85*Math.sin(t)], v=value(t), output=[480+scale*v[0],125-scale*v[1]];
    const count=Math.max(1,Math.ceil(angle/2));
    const path=Array.from({length:count+1},(_,k)=>{const w=value(t*k/count);return `${k?'L':'M'}${480+scale*w[0]},${125-scale*w[1]}`;}).join(' ');
    $('loop-plot').innerHTML='<title>Circular input on the left and the continued value on the right</title>'+line(35,125,275,125)+line(155,15,155,235)+line(365,125,600,125)+line(480,15,480,235)+
      '<circle class="guide" cx="155" cy="125" r="85"/>'+`<path class="trace" d="${path}"/>`+dot(...input)+dot(...output)+dot(155,125,'excluded',4);
    const val = mode==='log' ? `L(z(t))=it` : mode==='sqrt' ? `S(z(t))=e^{it/2}` : `f(z(t))=e^{-it}`;
    const terminal = angle===360 ? (mode==='log'?'2\\pi i':mode==='sqrt'?'-1':'1') : angle===720 ? (mode==='log'?'4\\pi i':'1') : null;
    formula($('loop-readout'), `t=${(angle/360).toFixed(3)}\\cdot2\\pi,\\quad ${val}${terminal?'='+terminal:''}`);
    $('loop-plot').dataset.turns=String(angle/360);
    $('loop-plot').dataset.valueReal=String(v[0]);
    $('loop-plot').dataset.valueImag=String(v[1]);
  }
  $('zero-count').addEventListener('input',zeros);
  $('loop-angle').addEventListener('input',loops);
  $('loop-function').addEventListener('change',loops);
  zeros();loops();
})();
