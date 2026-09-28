const assert=require('node:assert/strict'),fs=require('node:fs');
const A=require('./n-ball/calculator.js');
const exactDecimal=s=>A.Q(s.replace('.',''),10n**BigInt(s.split('.')[1]?.length||0));
const log=fs.readFileSync(process.argv[2],'utf8');
let fixtures=0;
for(const line of log.split('\n')){
  const s=line.split('|');
  if(s[0]==='PI'){
    const p=A.piBox(+s[1]);assert.equal(A.str(p.lo),s[2]);assert.equal(A.str(p.hi),s[3]);fixtures++;
  }else if(s[0]==='BALL'){
    const v=A.stageVolume(+s[2],A.parse(s[3]),+s[1]);assert.equal(A.str(v.lo),s[4]);assert.equal(A.str(v.hi),s[5]);fixtures++;
  }else if(s[0]==='COEFF'){
    assert.equal(A.str(A.coeff(+s[1])),s[2]);assert.equal(A.str(A.gammaCoeff(+s[1])),s[3]);fixtures++;
  }
}
assert.equal(fixtures,213);
for(let n=0;n<=64;n++)assert.equal(A.str(A.mul(A.coeff(n),A.gammaCoeff(n))),'1');
for(const n of [0,1,2,3,5,20,64])for(const r of ['0','1/1000','1','3/2','10']){
  const result=A.compute(n,A.parse(r),12),v=result.volume;
  assert(A.cmp(v.lo,v.hi)<=0);
  const fine=A.stageVolume(n,A.parse(r),result.stage+1);
  assert(A.cmp(v.lo,fine.lo)<=0&&A.cmp(fine.hi,v.hi)<=0);
  for(const box of [v,result.area].filter(Boolean)){
    assert(A.cmp(A.sub(box.hi,box.lo),A.Q(1,10n**13n))<=0);
    assert(A.cmp(exactDecimal(A.decimal(box.lo,12)),box.lo)<=0);
    assert(A.cmp(box.hi,exactDecimal(A.decimal(box.hi,12,true)))<=0);
  }
}
assert.equal(A.decimal(A.Q(1,3),4),'0.3333');assert.equal(A.decimal(A.Q(1,3),4,true),'0.3334');
assert.equal(A.str(A.parse('.125')),'1/8');
for(const r of ['-1','1/0','Infinity','1e3','<script>','1.2.3'])assert.throws(()=>A.parse(r));
for(const n of [-1,1.5,65,NaN])assert.throws(()=>A.compute(n,A.Q(1)));
assert.throws(()=>A.compute(3,A.Q(11)));
console.log(JSON.stringify({passed:true,leanFixtures:fixtures,allDimensionsCoefficientIdentity:true,edgeCasesAndOutwardRounding:true}));
