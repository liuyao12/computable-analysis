import ComputableAnalysis.ModularForms.TauLambertProductLimit

/-! Exact differential identity for the actual infinite Euler product. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Passage of the actual finite derivative identity through all three
represented limits gives the infinite Euler-Lambert differential identity. -/
theorem tauEulerNomeDerivative_lambert_identity (q : Scalar) (hq : tauEulerNomeDomain q) :
    (mul q.val (tauEulerNomeDerivativeCandidate q hq).val).Equiv
      (neg (scaleRat 24 (mul (tauEulerNomeMap.eval q hq).val (tauLambertValue q hq).val))) := by
  let D := tauEulerNomeDerivativeCandidate q hq
  let P := tauEulerNomeMap.eval q hq
  let L := tauLambertValue q hq
  let A : Scalar := ⟨mul q.val D.val,mul_valid q.property D.property⟩
  let B : Scalar := ⟨neg (scaleRat 24 (mul P.val L.val)),neg_valid (scaleRat_valid (mul_valid P.property L.property))⟩
  let e := fun N => (2*(1/1024:Rat))*tauEulerDerivativeTail (1/1024) N+24*tauLambertProductError N
  have he : ShrinksToZero e := RepresentedCauchySum.sum_shrinks _ _
    (SeriesLimitLaws.shrinks_scale _
      (tauEulerDerivativeTail_shrinks (1/1024) (by decide +kernel) Rat.le_refl)
      (2*(1/1024)) (by decide +kernel))
    (SeriesLimitLaws.shrinks_scale _ tauLambertProductError_shrinks 24 (by decide +kernel))
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 e he
  intro N
  let DN := finiteDiscriminantEulerSlope q N
  let PN := finiteDiscriminantEulerProduct q N
  have ht := weightedLambertTerm_valid q (1/1024) 1 (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq)
  let LN : Scalar := ⟨ScalarSeries.block (weightedLambertTerm q (1/1024) 1) 0 N,
    ScalarSeries.block_valid _ ht 0 N⟩
  let X : Scalar := ⟨mul q.val DN.val,mul_valid q.property DN.property⟩
  let Y : Scalar := ⟨sub (mul P.val L.val) (mul PN.val LN.val),
    sub_valid (mul_valid P.property L.property) (mul_valid PN.property LN.property)⟩
  have htail : 0≤tauEulerDerivativeTail (1/1024) N := by
    unfold tauEulerDerivativeTail
    exact Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))
  have hs := Small.mul q.property (sub_valid D.property DN.property)
    (show (0:Rat)≤1/1024 by decide +kernel) htail (LocalODE.interior_bound _ q hq)
    (tauEulerDerivativeValue_close_prefix q (1/1024) (by decide +kernel) Rat.le_refl
      (LocalODE.interior_bound _ q hq) N)
  have hd : Small (sub A.val X.val) ((2*(1/1024:Rat))*tauEulerDerivativeTail (1/1024) N) := by
    have heq : (mul q.val (sub D.val DN.val)).Equiv (sub A.val X.val) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := mul_valid q.property (sub_valid D.property DN.property)) (hright := sub_valid A.property X.property)
      let Q := ComplexRawQuotient.ofRaw q.val q.property
      let d := ComplexRawQuotient.ofRaw D.val D.property
      let dn := ComplexRawQuotient.ofRaw DN.val DN.property
      change Q*(d-dn)=Q*d-Q*dn
      grind only
    exact Small.congr (mul_valid q.property (sub_valid D.property DN.property)) (sub_valid A.property X.property) heq hs
  have hy := LocalODE.small_scale (show (0:Rat)≤24 by decide +kernel)
    (tauEulerLambertProduct_close_prefix q hq N)
  have hf := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := X.property)
    (hright := neg_valid (scaleRat_valid (mul_valid PN.property LN.property)))
    (finiteDiscriminantEulerSlope_lambert_identity q hq N)
  have heq : (add (sub A.val X.val) (scaleRat 24 Y.val)).Equiv (sub A.val B.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid A.property X.property) (scaleRat_valid Y.property))
      (hright := sub_valid A.property B.property)
    let a := ComplexRawQuotient.ofRaw A.val A.property
    let x := ComplexRawQuotient.ofRaw X.val X.property
    let p := ComplexRawQuotient.ofRaw (mul P.val L.val) (mul_valid P.property L.property)
    let pn := ComplexRawQuotient.ofRaw (mul PN.val LN.val) (mul_valid PN.property LN.property)
    change x= -(ComplexRawQuotient.scaleRat 24 pn) at hf
    change (a-x)+ComplexRawQuotient.scaleRat 24 (p-pn)=a-(-ComplexRawQuotient.scaleRat 24 p)
    rw [hf]
    change (a-(-ComplexRawQuotient.scaleRat 24 pn))+ComplexRawQuotient.scaleRat 24 (p+(-pn))=a-(-ComplexRawQuotient.scaleRat 24 p)
    rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.neg_eq_scaleRat_neg_one pn,
      ComplexRawQuotient.scaleRat_scaleRat,show (24:Rat)*(-1)= -24 by decide +kernel,
      ←ComplexRawQuotient.neg_scaleRat]
    grind only
  have h := Small.congr (add_valid (sub_valid A.property X.property) (scaleRat_valid Y.property))
    (sub_valid A.property B.property) heq (LocalODE.small_add hd hy)
  simpa only [Rat.zero_add,e] using h

end ComputableAnalysis.ModularForms
