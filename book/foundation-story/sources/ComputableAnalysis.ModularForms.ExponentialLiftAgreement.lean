import ComputableAnalysis.ModularForms.ExponentialLiftCandidateError

/-! Agreement for all bounded represented complex inputs, proved from the
actual moving-center candidates and shrinking errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert LocalODE SeriesLimitLaws

theorem entireExponential_legacy_lift {C : Rat}
    (A : ComplexExponentialLift.BoundedInput C) :
    (entireExponentialValue ⟨A.raw,A.valid⟩).val.Equiv
      (ComplexExponentialLift.BoundedInput.exponential A) := by
  let z : Scalar := ⟨A.raw,A.valid⟩
  let R := exponentialInputRadius z
  let M := exponentialBudget (exponentialRatio R)
  let q := 2*exponentialRatio R*R.val
  let start := RationalMajorant.factorialTailStart C
  let e := exponentialCenterError z
  let f := fun (n : Nat) => 4*M*q^(start+n)
  let g := centerError (ComplexExponentialLift.BoundedInput.exponential A)
  have hM : 0 ≤ M := exponentialBudget_nonnegative _ (exponentialRatio_positive R)
  have hq : 0 ≤ q := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
    (Rat.le_of_lt (exponentialRatio_positive R))) (Rat.le_of_lt R.property)
  have hlocal : q ≤ (1 : Rat)/2 := by
    have h := exponentialRatio_local R
    dsimp [q]
    grind
  have he : ShrinksToZero e := exponentialCenterError_shrinks z
  have hf : ShrinksToZero f := by
    have h := shrinks_shift _ (tail_bound_shrinks M q hM hq hlocal) start
    simpa only [f,Nat.add_comm] using h
  have hg : ShrinksToZero g := legacy_lift_candidate_error_shrinks A
  have hv := (entireExponentialValue z).property
  have hl := ComplexExponentialLift.BoundedInput.exponential_valid A
  apply equiv_of_small_sub_zero
  apply small_closed _ 0 (fun n => e n+f n+g n)
    (RepresentedCauchySum.sum_shrinks _ _ (RepresentedCauchySum.sum_shrinks _ _ he hf) hg)
  intro n
  let a := (entireExponentialValue (rationalCenter z n)).val
  let p := ofQComplex (ComplexExponentialApproximation.expPrefix (A.raw.compute n).center (start+n))
  have ha : a.Valid := (entireExponentialValue (rationalCenter z n)).property
  have hp : p.Valid := ofQComplex_valid _
  have hs := small_add
    (small_add (exponential_center_error z n) (entire_center_candidate_error z start n))
    (small_neg (legacy_lift_candidate_error A n))
  have heq : (add (add (sub (entireExponentialValue z).val a) (sub a p))
      (neg (sub (ComplexExponentialLift.BoundedInput.exponential A) p))).Equiv
      (sub (entireExponentialValue z).val (ComplexExponentialLift.BoundedInput.exponential A)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (add_valid (sub_valid hv ha) (sub_valid ha hp))
        (neg_valid (sub_valid hl hp))) (hright := sub_valid hv hl)
    change ((ComplexRawQuotient.ofRaw (entireExponentialValue z).val hv - ComplexRawQuotient.ofRaw a ha) +
      (ComplexRawQuotient.ofRaw a ha - ComplexRawQuotient.ofRaw p hp)) +
      -(ComplexRawQuotient.ofRaw (ComplexExponentialLift.BoundedInput.exponential A) hl -
        ComplexRawQuotient.ofRaw p hp) =
      ComplexRawQuotient.ofRaw (entireExponentialValue z).val hv -
        ComplexRawQuotient.ofRaw (ComplexExponentialLift.BoundedInput.exponential A) hl
    grind
  have hb := Small.congr (add_valid (add_valid (sub_valid hv ha) (sub_valid ha hp))
    (neg_valid (sub_valid hl hp))) (sub_valid hv hl) heq hs
  simpa only [Rat.zero_add] using hb

end ComputableAnalysis.ModularForms
