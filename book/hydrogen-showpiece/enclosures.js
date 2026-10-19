/* Display saved, Lean-checked intervals; no numerical physics is evaluated here. */
(async () => {
  const root = document.getElementById('hydrogen-enclosure');
  const coupling = document.getElementById('hydrogen-coupling');
  const precision = document.getElementById('hydrogen-precision');
  const selection = document.getElementById('hydrogen-selection');
  const result = document.getElementById('hydrogen-result');
  const width = document.getElementById('hydrogen-width');
  const nodes = [selection, result, width];
  try {
    const response = await fetch('enclosures.json');
    if (!response.ok) throw new Error('Enclosure data unavailable');
    const { rows } = await response.json();
    await window.MathJax.startup.promise;
    const decimal = integer => {
      const digits = String(integer).padStart(10, '0');
      return `${digits.slice(0, -9)}.${digits.slice(-9)}`;
    };
    const render = async () => {
      const d = Number(coupling.value), p = Number(precision.value);
      const row = rows.find(r => r.alphaDenominator === d && r.precisionPower === p);
      if (!row) throw new Error('Missing checked enclosure');
      window.MathJax.typesetClear(nodes);
      selection.textContent = String.raw`\[\alpha=\frac1{${d}},\qquad\varepsilon=2^{-${p}}\]`;
      result.textContent = String.raw`\[\begin{aligned}${decimal(row.lowerNano)}&\leq R(1/${d}),\\R(1/${d})&\leq${decimal(row.upperNano)}.\end{aligned}\]`;
      width.textContent = String.raw`\[\operatorname{width}(I)=${decimal(row.widthNano)}\]`;
      await window.MathJax.typesetPromise(nodes);
      root.dataset.alphaDenominator = String(d);
      root.dataset.precisionPower = String(p);
      root.dataset.rendered = 'true';
    };
    let pending = Promise.resolve();
    const schedule = () => {
      pending = pending.then(render).catch(error => {
        result.textContent = 'Unable to display the selected enclosure. The checked endpoints are available in the data link below.';
        console.error(error);
      });
    };
    coupling.addEventListener('change', schedule);
    precision.addEventListener('change', schedule);
    schedule();
  } catch (error) {
    console.error(error);
  }
})();
