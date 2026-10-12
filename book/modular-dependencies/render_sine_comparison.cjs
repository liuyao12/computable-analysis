// Render the existing worked comparison with its mathematical delimiters intact.
const fs=require('node:fs'),path=require('node:path');
const {marked}=require('marked');
const root=path.resolve(__dirname,'..');
let text=fs.readFileSync(path.join(root,'skills/function-computation-identity/references/sine-comparison.md'),'utf8');
text=text.replace(/\]\(\.\.\/\.\.\/\.\.\/ComputableAnalysis\/([^)]*?)\.lean\)/g,(_,name)=>`](modular-proofs.html#sine-source:ComputableAnalysis.${name.replaceAll('/','.')})`);
const math=[];
text=text.replace(/\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\]/g,m=>{math.push(m);return 'SINE-MATH-'+(math.length-1)+'-TOKEN'});
let body=marked.parse(text);
body=body.replace(/SINE-MATH-(\d+)-TOKEN/g,(_,i)=>math[Number(i)].replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;'));
const template=fs.readFileSync(path.join(root,'book/modular-dependencies/index.html'),'utf8');
const mathScripts=template.slice(template.indexOf('<script>window.MathJax'),template.indexOf('<style>'));
const html=`<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Sine comparison · Worked strategy test</title>${mathScripts}<style>body{max-width:850px;margin:30px auto;padding:0 22px;color:#243c34;background:#f5f6f2;font:17px/1.65 system-ui}h1,h2{font-family:Georgia;line-height:1.25}a{color:#235b73}pre{overflow-x:auto;padding:16px;background:#eaf0ea}code{font-size:.85em}mjx-container{max-width:100%;overflow-x:auto;overflow-y:hidden}</style></head><body><nav><a href="modular-proofs.html#sine">Explore the sine proof routes</a></nav>${body}</body></html>`;
fs.writeFileSync(path.join(root,'book/modular-dependencies/sine-comparison.html'),html);
console.log('Rendered worked comparison with preserved LaTeX and graph source links.');
