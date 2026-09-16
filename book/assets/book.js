'use strict';
const menu=document.querySelector('#menu-button'),nav=document.querySelector('#book-nav');
menu?.addEventListener('click',()=>{const open=nav.classList.toggle('open');menu.setAttribute('aria-expanded',String(open));});
const dialog=document.querySelector('#proof-dialog'),frame=document.querySelector('#proof-frame');
let opener;
function closeProof(){dialog.close();frame.src='about:blank';opener?.focus();}
document.querySelectorAll('[data-proof-map]').forEach(link=>link.addEventListener('click',e=>{
 if(e.metaKey||e.ctrlKey||e.shiftKey||e.altKey)return;
 e.preventDefault();opener=link;frame.src=link.href+'&embedded=1';dialog.showModal();
}));
document.querySelector('#close-proof')?.addEventListener('click',closeProof);
dialog?.addEventListener('cancel',()=>{frame.src='about:blank';opener?.focus();});
window.addEventListener('message',e=>{if(e.origin===location.origin&&e.source===frame.contentWindow&&e.data==='close-proof-map')closeProof();});

document.querySelectorAll('[data-animation]').forEach(figure=>{
 const id=figure.dataset.animation,img=figure.querySelector('img'),button=figure.querySelector('[data-animation-toggle]');
 let playing=!matchMedia('(prefers-reduced-motion: reduce)').matches;
 function apply(){img.src='reading/animations/'+id+(playing?'.gif':'.png');button.textContent=playing?'Pause animation':'Play animation';button.setAttribute('aria-pressed',String(playing));}
 button.onclick=()=>{playing=!playing;apply();};apply();
});
