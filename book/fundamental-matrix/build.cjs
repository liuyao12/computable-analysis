// Compile authored LaTeX to native MathML, then inline the exact engine and UI.
// Requires mathjax-full 3.2.1 at build time only. No font assets are copied.
const fs=require('node:fs'),path=require('node:path');
const mj=require.resolve('mathjax-full/js/mathjax.js');
const base=path.dirname(mj),{mathjax}=require(mj),{TeX}=require(base+'/input/tex.js');
const {SVG}=require(base+'/output/svg.js'),{liteAdaptor}=require(base+'/adaptors/liteAdaptor.js');
const {RegisterHTMLHandler}=require(base+'/handlers/html.js'),{AllPackages}=require(base+'/input/tex/AllPackages.js');
const {SerializedMmlVisitor}=require(base+'/core/MmlTree/SerializedMmlVisitor.js'),{STATE}=require(base+'/core/MathItem.js');
RegisterHTMLHandler(liteAdaptor());
const document=mathjax.document('',{InputJax:new TeX({packages:AllPackages}),OutputJax:new SVG({fontCache:'none'})});
const visitor=new SerializedMmlVisitor();
let count=0;
function convert(tex,display){
  tex=tex.replaceAll('&lt;','<').replaceAll('&gt;','>').replaceAll('&amp;','&');
  const root=document.convert(tex,{display,end:STATE.COMPILED});
  let mml=visitor.visitTree(root);
  if(mml.includes('<merror'))throw new Error('TeX compilation error: '+tex+'\n'+mml);
  if(!display)mml=mml.replace('<math ','<math display="inline" ');
  count++;return mml;
}
let html=fs.readFileSync(path.join(__dirname,'index.template.html'),'utf8');
html=html.replace('<!--__NONLINEAR_EXAMPLES__-->',()=>fs.readFileSync(path.join(__dirname,'nonlinear.html'),'utf8'));
html=html.replace(/\\\[([\s\S]*?)\\\]/g,(_,s)=>convert(s,true));
html=html.replace(/\\\(([\s\S]*?)\\\)/g,(_,s)=>convert(s,false));
for(const [marker,file] of [['STYLE','style.css'],['ENGINE','engine.js'],['NONLINEAR','nonlinear.js'],['APP','app.js']])html=html.replace(`/*__${marker}__*/`,()=>fs.readFileSync(path.join(__dirname,file),'utf8'));
const dest=process.argv[2]||path.join(__dirname,'..','fundamental-matrix.html');
fs.writeFileSync(dest,html);console.log(`Built ${dest}; ${count} equations, ${Buffer.byteLength(html)} bytes.`);
