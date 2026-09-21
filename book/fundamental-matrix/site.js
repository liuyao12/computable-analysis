/* Measure the actual header height; do not obscure the notebook at browser zoom. */
(function () {
  'use strict';
  const header = document.querySelector('.topbar');
  const menu = document.querySelector('.book-menu');
  const measure = () => document.documentElement.style.setProperty('--header-height', `${Math.ceil(header.getBoundingClientRect().height)}px`);
  new ResizeObserver(measure).observe(header);
  measure();
  document.addEventListener('keydown', event => {
    if (event.key === 'Escape' && menu.open) {
      menu.open = false;
      menu.querySelector('summary').focus();
    }
  });
  document.addEventListener('click', event => {
    if (menu.open && !menu.contains(event.target)) menu.open = false;
  });
})();
