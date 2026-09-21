// Compile authored LaTeX to native MathML. The published essay has no JavaScript.
// mathjax-full 3.2.1 is a build-time dependency only; no font assets are copied.
'use strict';
const fs=require('node:fs'),path=require('node:path');
const base=path.dirname(require.resolve('mathjax-full/js/mathjax.js'));
const {mathjax}=require(base+'/mathjax.js'),{TeX}=require(base+'/input/tex.js');
const {SVG}=require(base+'/output/svg.js'),{liteAdaptor}=require(base+'/adaptors/liteAdaptor.js');
const {RegisterHTMLHandler}=require(base+'/handlers/html.js'),{AllPackages}=require(base+'/input/tex/AllPackages.js');
const {SerializedMmlVisitor}=require(base+'/core/MmlTree/SerializedMmlVisitor.js'),{STATE}=require(base+'/core/MathItem.js');
RegisterHTMLHandler(liteAdaptor());
const document=mathjax.document('',{InputJax:new TeX({packages:AllPackages}),OutputJax:new SVG({fontCache:'none'})});
const visitor=new SerializedMmlVisitor();let count=0;
function convert(tex,display){
  tex=tex.replaceAll('&lt;','<').replaceAll('&gt;','>').replaceAll('&amp;','&');
  const root=document.convert(tex,{display,end:STATE.COMPILED});
  let mml=visitor.visitTree(root);
  if(mml.includes('<merror'))throw new Error('TeX compilation error: '+tex+'\n'+mml);
  if(!display)mml=mml.replace('<math ','<math display="inline" ');
  count++;return mml;
}
let html=fs.readFileSync(path.join(__dirname,'index.template.html'),'utf8');
html=html.replace(/\\\[([\s\S]*?)\\\]/g,(_,s)=>convert(s,true));
html=html.replace(/\\\(([\s\S]*?)\\\)/g,(_,s)=>convert(s,false));
html=html.replace('/*__STYLE__*/',()=>fs.readFileSync(path.join(__dirname,'style.css'),'utf8'));
if(/<script\b|<input\b|<canvas\b|<svg\b|__STYLE__/.test(html))throw new Error('Unexpected interactive asset in the static essay.');
const dest=process.argv[2]||path.join(__dirname,'..','fundamental-matrix.html');
fs.mkdirSync(path.dirname(dest),{recursive:true});fs.writeFileSync(dest,html);
console.log(`Built ${dest}; ${count} equations, ${Buffer.byteLength(html)} bytes; no runtime scripts.`);
