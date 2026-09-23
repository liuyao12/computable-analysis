'use strict';
const controls=[...document.querySelectorAll('[data-square-route]')];
function selectRoute(route){
 for(const b of controls)b.setAttribute('aria-pressed',String(b.dataset.squareRoute===route));
 for(const node of document.querySelectorAll('[data-proof-route]'))node.hidden=route!=='all'&&node.dataset.proofRoute!==route;
 const url=new URL(location.href);if(route==='all')url.searchParams.delete('route');else url.searchParams.set('route',route);history.replaceState(null,'',url);
}
for(const b of controls)b.addEventListener('click',()=>selectRoute(b.dataset.squareRoute));
const requested=new URLSearchParams(location.search).get('route');selectRoute(['symmetry','ftc'].includes(requested)?requested:'all');
