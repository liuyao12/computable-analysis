(function(){
  'use strict';
  const A=window.NBallCalculator,$=s=>document.querySelector(s);
  const math=s=>'\\('+s+'\\)';
  let queue=Promise.resolve();
  function typeset(el){
    queue=queue.catch(()=>{}).then(async()=>{
      if(window.MathJax?.startup?.promise){await MathJax.startup.promise;await MathJax.typesetPromise([el]);}
    });
  }
  function unitFormula(n){const c=A.coeff(n),k=Math.floor(n/2);return (c.a===c.b&&k?'':A.tex(c))+(k?'\\pi'+(k>1?'^{'+k+'}':''):'');}
  function clear(el){if(window.MathJax?.typesetClear)MathJax.typesetClear([el]);}
  function render(){
    const err=$('#error');err.textContent='';
    try{
      const result=A.compute(Number($('#dimension').value),A.parse($('#radius').value),Number($('#digits').value));
      const {n,r,digits,volume,area,stage}=result,box=$('#result');clear(box);
      const interval=v=>`\\left[${A.decimal(v.lo,digits)},\\;${A.decimal(v.hi,digits,true)}\\right]`;
      box.innerHTML='<p class="eyebrow">Volume enclosure · rounded outwards</p><div class="answer">'+math('V_{'+n+'}('+A.tex(r)+')\\in '+interval(volume))+'</div>'+
        '<p>Exact expression: '+math('V_{'+n+'}('+A.tex(r)+')='+unitFormula(n)+(n?'\\left('+A.tex(r)+'\\right)^{'+n+'}':''))+'</p>'+
        (area?'<p>Boundary area: '+math('A_{'+(n-1)+'}('+A.tex(r)+')\\in '+interval(area))+'</p>':'<p class="small">Boundary area is displayed for positive radius and positive dimension.</p>')+
        '<p>Gamma value: '+math('\\Gamma\\!\\left('+A.tex(A.Q(n+2,2))+ '\\right)='+A.tex(A.gammaCoeff(n))+(n%2?'\\sqrt{\\pi}':''))+'</p>'+
        '<p class="small">Computed with exact rational arithmetic at refinement stage '+stage+'. Decimal endpoints are rounded down and up respectively.</p>';
      const raw=$('#rational-bounds');raw.textContent=JSON.stringify({dimension:n,radius:A.str(r),stage,pi:{lower:A.str(result.pi.lo),upper:A.str(result.pi.hi)},volume:{lower:A.str(volume.lo),upper:A.str(volume.hi)}},null,2);
      typeset(box);$('#result').hidden=false;
    }catch(e){err.textContent=e.message;$('#result').hidden=true;$('#rational-bounds').textContent='';}
  }
  $('#calculator').addEventListener('submit',e=>{e.preventDefault();render();});
  $('#examples').addEventListener('click',e=>{const b=e.target.closest('button[data-n]');if(!b)return;$('#dimension').value=b.dataset.n;$('#radius').value=b.dataset.r;render();});
  const body=$('#dimension-table');
  for(let n=0;n<=12;n++){
    const tr=document.createElement('tr'),v=A.compute(n,A.Q(1),4);
    tr.innerHTML='<td>'+math(String(n))+'</td><td>'+math(unitFormula(n))+'</td><td>'+math(A.tex(A.gammaCoeff(n))+(n%2?'\\sqrt{\\pi}':''))+'</td><td>'+math('['+A.decimal(v.volume.lo,4)+',\\;'+A.decimal(v.volume.hi,4,true)+']')+'</td>';
    body.append(tr);
  }
  render();typeset(body);
})();
