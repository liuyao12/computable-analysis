(() => {
  const image = document.getElementById('archimedes-sections');
  const button = document.getElementById('archimedes-motion');
  if (!image || !button) return;
  const still = image.getAttribute('src');
  const gif = still.replace(/\.png$/, '.gif');
  function setMotion(active) {
    image.src = active ? gif : still;
    button.textContent = active ? 'Pause animation' : 'Play animation';
    button.setAttribute('aria-pressed', String(active));
  }
  const preference = matchMedia('(prefers-reduced-motion: reduce)');
  setMotion(!preference.matches);
  button.addEventListener('click', () => setMotion(button.getAttribute('aria-pressed') !== 'true'));
  preference.addEventListener('change', event => setMotion(!event.matches));
})();
