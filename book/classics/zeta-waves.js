(() => {
  'use strict';
  const $ = id => document.getElementById(id);
  let queue = Promise.resolve();
  const pair = (beta, gamma, u) => -2 * Math.exp(beta * u) *
    (beta * Math.cos(gamma * u) + gamma * Math.sin(gamma * u)) / (beta * beta + gamma * gamma);
  const normalized = (beta, gamma, u) => pair(beta, gamma, u) * Math.exp(-u / 2);
  const envelope = (beta, gamma, u) => 2 * Math.exp((beta - .5) * u) / Math.hypot(beta, gamma);
  function formulas(entries) {
    queue = queue.then(async () => {
      if (window.MathJax?.startup?.promise) await MathJax.startup.promise;
      for (const [el, latex] of entries) {
        if (window.MathJax?.typesetClear) MathJax.typesetClear([el]);
        el.textContent = `\\(${latex}\\)`;
      }
      if (window.MathJax?.typesetPromise) await MathJax.typesetPromise(entries.map(([el]) => el));
    });
  }
  function render() {
    const beta = Number($('wave-beta').value), gamma = Number($('wave-gamma').value);
    const lo = Math.log(2), hi = Math.log(1000);
    const bound = envelope(beta, gamma, hi) * 1.15;
    const path = f => Array.from({length:1201}, (_, k) => {
      const u = lo + (hi - lo) * k / 1200;
      return `${k ? 'L' : 'M'}${(20 + 600 * k / 1200).toFixed(3)},${(120 - 100 * f(u) / bound).toFixed(3)}`;
    }).join(' ');
    $('wave-plot').innerHTML = '<title>Hypothetical conjugate pair: normalized wave and amplitude envelope</title>' +
      '<line class="axis" x1="20" y1="120" x2="620" y2="120"/>' +
      `<path class="envelope" d="${path(u => envelope(beta, gamma, u))}"/>` +
      `<path class="envelope" d="${path(u => -envelope(beta, gamma, u))}"/>` +
      `<path class="wave" d="${path(u => normalized(beta, gamma, u))}"/>`;
    $('wave-plot').dataset.beta = String(beta);
    $('wave-plot').dataset.gamma = String(gamma);
    $('wave-plot').dataset.verticalBound = String(bound);
    formulas([
      [$('wave-readout'), String.raw`\beta=${beta.toFixed(2)},\quad\gamma=${gamma},\quad\text{envelope}=\frac{2e^{(\beta-1/2)u}}{\sqrt{\beta^2+\gamma^2}}`],
      [$('wave-scale'), String.raw`\text{Vertical range: }[-${bound.toFixed(3)},\,${bound.toFixed(3)}]`]
    ]);
  }
  $('wave-beta').addEventListener('input', render);
  $('wave-gamma').addEventListener('input', render);
  window.ZetaWaves = {pair, normalized, envelope};
  render();
})();
