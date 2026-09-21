/* Keep anchor targets and the notebook below the actual, possibly wrapped header. */
(function () {
  'use strict';
  const header = document.querySelector('.topbar');
  const measure = () => document.documentElement.style.setProperty('--header-height', `${Math.ceil(header.getBoundingClientRect().height)}px`);
  new ResizeObserver(measure).observe(header);
  measure();
})();
