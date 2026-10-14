import ComputableAnalysis.ModularForms.NomeWeightedDifference
import ComputableAnalysis.RiemannHilbert.DomainDerivativeBounds

/-! Finite weighted differences pass to supplied justified represented limits. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem nomeCoefficient_difference_limit (z : Scalar) (a : Nat → Scalar) (s d : Scalar)
    (e f b : Nat → Rat) (he : ShrinksToZero e) (hf : ShrinksToZero f) (hb : ShrinksToZero b)
    (hen : ∀ N, 0≤e N)
    (hs : ∀ N, Small (sub s.val (nomeCoefficientPrefix z a N)) (e N))
    (hd : ∀ N, Small (sub d.val (nomeCoefficientPrefix z (nomeCoefficientDifference a) N)) (f N))
    (hboundary : ∀ N, Small (mul (a N).val (LocalODE.power z.val (N+1))) (b N)) :
    (mul (sub (ofQComplex QComplex.one) z.val) s.val).Equiv
      (add d.val (mul (a 0).val z.val)) := by
  let c : Scalar := ⟨sub (ofQComplex QComplex.one) z.val,sub_valid (ofQComplex_valid _) z.property⟩
  let v := mul (a 0).val z.val
  have vv := mul_valid (a 0).property z.property
  have hC : 0≤2*scalarBound c := Rat.mul_nonneg (by decide) (Rat.le_of_lt (scalarBound_pos c))
  have ht := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ (SeriesLimitLaws.shrinks_scale e he _ hC) hf) hb
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun N => (2*scalarBound c*e N+f N)+b N) ht
  intro N
  let p := nomeCoefficientPrefix z a N
  let q := nomeCoefficientPrefix z (nomeCoefficientDifference a) N
  let w := mul (a N).val (LocalODE.power z.val (N+1))
  have vp := nomeCoefficientPrefix_valid z a N
  have vq := nomeCoefficientPrefix_valid z (nomeCoefficientDifference a) N
  have vw := mul_valid (a N).property (LocalODE.power_valid _ z.property (N+1))
  have h1 := Small.mul c.property (sub_valid s.property vp)
    (Rat.le_of_lt (scalarBound_pos c)) (hen N) (scalar_small c) (hs N)
  have h2 := SeriesLimitLaws.small_sub h1 (hd N)
  have h3 := SeriesLimitLaws.small_sub h2 (hboundary N)
  have hfin := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid c.property vp)
    (hright := add_valid (sub_valid vq vw) vv) (nomeCoefficientPrefix_difference_identity z a N)
  have hid : (sub (sub (mul c.val (sub s.val p)) (sub d.val q)) w).Equiv
      (sub (mul c.val s.val) (add d.val v)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (sub_valid (mul_valid c.property (sub_valid s.property vp))
        (sub_valid d.property vq)) vw)
      (hright := sub_valid (mul_valid c.property s.property) (add_valid d.property vv))
    let C := ComplexRawQuotient.ofRaw c.val c.property
    let S := ComplexRawQuotient.ofRaw s.val s.property
    let D := ComplexRawQuotient.ofRaw d.val d.property
    let P := ComplexRawQuotient.ofRaw p vp
    let Q := ComplexRawQuotient.ofRaw q vq
    let W := ComplexRawQuotient.ofRaw w vw
    let V := ComplexRawQuotient.ofRaw v vv
    change C*P=(Q-W)+V at hfin
    change (C*(S-P)-(D-Q))-W=C*S-(D+V)
    generalize C=c,S=s,D=d,P=p,Q=q,W=w,V=v at hfin ⊢
    grind only
  have h := Small.congr
    (sub_valid (sub_valid (mul_valid c.property (sub_valid s.property vp)) (sub_valid d.property vq)) vw)
    (sub_valid (mul_valid c.property s.property) (add_valid d.property vv)) hid h3
  simpa only [Rat.zero_add] using h

end ComputableAnalysis.ModularForms
