import ComputableAnalysis.ModularForms.WideEulerLogarithmicDerivative
import ComputableAnalysis.ModularForms.LambertPowers
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The literal factor slope satisfies a denominator-free Lambert identity on the wider disk. -/
theorem tauEulerFactorSlope_wide_lambert (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    (mul q.val (tauEulerFactorSlope q N).val).Equiv
      (neg (scaleRat 24 (mul (tauEulerFactorValue q N).val
        (weightedLambertTerm q (1/64) 1 N)))) := by
  let B := (tauEulerFactorMap N).eval q trivial
  let L : Scalar := ⟨nomeLambertPower q (1/64) N,
    nomeLambertPower_valid q (1/64) (by decide +kernel) (by decide +kernel) hq N⟩
  have hl := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid B.property L.property)
    (hright := LocalODE.power_valid _ q.property (N+1))
    (nomeLambertPower_multiplication q (1/64) (by decide +kernel) (by decide +kernel) hq N)
  have ht := weightedLambertTerm_valid q (1/64) 1 (by decide +kernel) (by decide +kernel) hq N
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid q.property (tauEulerFactorSlope q N).property)
    (hright := neg_valid (scaleRat_valid (mul_valid (tauEulerFactorValue q N).property ht)))
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let b := ComplexRawQuotient.ofRaw B.val B.property
  let l := ComplexRawQuotient.ofRaw L.val L.property
  let p := ComplexRawQuotient.ofRaw (LocalODE.power q.val N) (LocalODE.power_valid _ q.property N)
  let c := ((N+1:Nat):Rat)
  change b*l=p*Q at hl
  change Q*(ComplexRawQuotient.scaleRat 24
    (ComplexRawQuotient.ofRaw (LocalODE.power B.val 23) (LocalODE.power_valid _ B.property 23)*
      (-ComplexRawQuotient.scaleRat c p)))=
    -(ComplexRawQuotient.scaleRat 24
      (ComplexRawQuotient.ofRaw (LocalODE.power B.val 24) (LocalODE.power_valid _ B.property 24)*
        ComplexRawQuotient.scaleRat (c^1) l))
  rw [ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power,Rat.pow_one]
  change Q*(ComplexRawQuotient.scaleRat 24 (b^23*(-ComplexRawQuotient.scaleRat c p)))=
    -(ComplexRawQuotient.scaleRat 24 (b^24*ComplexRawQuotient.scaleRat c l))
  simp only [ComplexRawQuotient.mul_scaleRat,ComplexRawQuotient.neg_scaleRat,
    ComplexRawQuotient.scaleRat_scaleRat]
  rw [show (24:Rat)*(-c)= -(24*c) by grind only]
  congr 1
  have hp : b^24=b^23*b := by grind only
  rw [hp]
  grind only

/-- Actual whole finite Euler products satisfy the wider finite Lambert differential identity. -/
theorem finiteDiscriminantEulerSlope_wide_lambert (q : Scalar)
    (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    (mul q.val (finiteDiscriminantEulerSlope q N).val).Equiv
      (neg (scaleRat 24 (mul (finiteDiscriminantEulerProduct q N).val
        (ScalarSeries.block (weightedLambertTerm q (1/64) 1) 0 N)))) := by
  have ht := weightedLambertTerm_valid q (1/64) 1 (by decide +kernel) (by decide +kernel) hq
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid q.property (finiteDiscriminantEulerSlope q 0).property)
      (hright := neg_valid (scaleRat_valid (mul_valid (finiteDiscriminantEulerProduct q 0).property
        (ScalarSeries.block_valid _ ht 0 0))))
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    change Q*0= -(ComplexRawQuotient.scaleRat 24 (1*0))
    have hz : Q*0= -(0:ComplexRawQuotient.Value) := by grind only
    have hs := ComplexRawQuotient.scaleRat_zero (24:Rat)
    have he : (1:ComplexRawQuotient.Value)*0=0 := by grind only
    rw [he]
    exact Eq.mpr (congrArg (fun x => Q*0 = -x) hs) hz
  | succ N ih =>
    let P := finiteDiscriminantEulerProduct q N
    let D := finiteDiscriminantEulerSlope q N
    let F := tauEulerFactorValue q N
    let G := tauEulerFactorSlope q N
    let S : Scalar := ⟨ScalarSeries.block (weightedLambertTerm q (1/64) 1) 0 N,
      ScalarSeries.block_valid _ ht 0 N⟩
    let T : Scalar := ⟨weightedLambertTerm q (1/64) 1 N,ht N⟩
    have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid q.property D.property)
      (hright := neg_valid (scaleRat_valid (mul_valid P.property S.property))) ih
    have hg := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid q.property G.property)
      (hright := neg_valid (scaleRat_valid (mul_valid F.property T.property)))
      (tauEulerFactorSlope_wide_lambert q hq N)
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid q.property (finiteDiscriminantEulerSlope q (N+1)).property)
      (hright := neg_valid (scaleRat_valid (mul_valid (finiteDiscriminantEulerProduct q (N+1)).property
        (ScalarSeries.block_valid _ ht 0 (N+1)))))
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    let p := ComplexRawQuotient.ofRaw P.val P.property
    let d := ComplexRawQuotient.ofRaw D.val D.property
    let f := ComplexRawQuotient.ofRaw F.val F.property
    let g := ComplexRawQuotient.ofRaw G.val G.property
    let s := ComplexRawQuotient.ofRaw S.val S.property
    let t := ComplexRawQuotient.ofRaw T.val T.property
    change Q*d= -(ComplexRawQuotient.scaleRat 24 (p*s)) at hd
    change Q*g= -(ComplexRawQuotient.scaleRat 24 (f*t)) at hg
    simp only [ScalarSeries.block,Nat.zero_add]
    change Q*(d*f+p*g)= -(ComplexRawQuotient.scaleRat 24 ((p*f)*(s+t)))
    have he : Q*(d*f+p*g)=(Q*d)*f+p*(Q*g) := by grind only
    rw [he,hd,hg,ComplexRawQuotient.neg_scaleRat,ComplexRawQuotient.neg_scaleRat,
      ←ComplexRawQuotient.scaleRat_mul,ComplexRawQuotient.mul_scaleRat,
      ComplexRawQuotient.neg_scaleRat,←ComplexRawQuotient.scaleRat_add]
    congr 1
    grind only

end ComputableAnalysis.ModularForms
