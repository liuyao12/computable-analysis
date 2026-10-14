import ComputableAnalysis.ModularForms.ExponentialLiftCandidateError
import ComputableAnalysis.ModularForms.RepresentedRotationCandidate
import ComputableAnalysis.GeometricPiRotation

/-! Agreement for all bounded represented complex inputs, proved from the
actual moving-center candidates and shrinking errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert LocalODE SeriesLimitLaws

theorem entireExponential_represented_rotation
    (A : RotationLift.HalfPiInput) :
    (entireExponentialValue ⟨ComplexRaw.imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩).val.Equiv
      (RotationLift.HalfPiInput.rotation A) := by
  let z : Scalar := ⟨ComplexRaw.imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩
  let R := exponentialInputRadius z
  let M := exponentialBudget (exponentialRatio R)
  let q := 2*exponentialRatio R*R.val
  let terms := RotationSeries.uniformRotationTailTerms
  let e := exponentialCenterError z
  let f := fun (n : Nat) => 4*M*q^(terms n)
  let g := centerError (RotationLift.HalfPiInput.rotation A)
  have hM : 0 ≤ M := exponentialBudget_nonnegative _ (exponentialRatio_positive R)
  have hq : 0 ≤ q := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
    (Rat.le_of_lt (exponentialRatio_positive R))) (Rat.le_of_lt R.property)
  have hlocal : q ≤ (1 : Rat)/2 := by
    have h := exponentialRatio_local R
    dsimp [q]
    grind
  have he : ShrinksToZero e := exponentialCenterError_shrinks z
  have hf : ShrinksToZero f := by
    intro eps
    obtain ⟨N,hN⟩ := tail_bound_shrinks M q hM hq hlocal eps
    refine ⟨N,?_⟩
    intro n hn
    exact hN (terms n) (by dsimp [terms,RotationSeries.uniformRotationTailTerms]; omega)
  have hg : ShrinksToZero g := represented_rotation_candidate_error_shrinks A
  have hv := (entireExponentialValue z).property
  have hl := RotationLift.HalfPiInput.rotation_valid A
  apply equiv_of_small_sub_zero
  apply small_closed _ 0 (fun n => e n+f n+g n)
    (RepresentedCauchySum.sum_shrinks _ _ (RepresentedCauchySum.sum_shrinks _ _ he hf) hg)
  intro n
  let a := (entireExponentialValue (rationalCenter z n)).val
  let p := ofQComplex (RotationSeries.uniformRotationCenter (A.raw.compute n).midpoint n)
  have ha : a.Valid := (entireExponentialValue (rationalCenter z n)).property
  have hp : p.Valid := ofQComplex_valid _
  have hidx : terms n-n+n=terms n := by
    dsimp [terms,RotationSeries.uniformRotationTailTerms]
    omega
  have hprefix : ComplexExponentialApproximation.expPrefix (z.val.compute n).center (terms n) =
      RotationSeries.uniformRotationCenter (A.raw.compute n).midpoint n := by
    change ComplexExponentialApproximation.expPrefix
      ((ComplexRaw.imaginaryAxis A.raw).compute n).center (RotationSeries.uniformRotationTailTerms n) = _
    rw [imaginaryAxis_center, ComplexExponentialApproximation.expPrefix_eq_complexSeries_expPartial]
    exact RotationSeries.expPartial_imaginary_even_split _ _
  have htail := entire_center_candidate_error z (terms n-n) n
  rw [hidx,hprefix] at htail
  have hs := small_add
    (small_add (exponential_center_error z n) htail)
    (small_neg (represented_rotation_candidate_error A n))
  have heq : (add (add (sub (entireExponentialValue z).val a) (sub a p))
      (neg (sub (RotationLift.HalfPiInput.rotation A) p))).Equiv
      (sub (entireExponentialValue z).val (RotationLift.HalfPiInput.rotation A)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (add_valid (sub_valid hv ha) (sub_valid ha hp))
        (neg_valid (sub_valid hl hp))) (hright := sub_valid hv hl)
    change ((ComplexRawQuotient.ofRaw (entireExponentialValue z).val hv - ComplexRawQuotient.ofRaw a ha) +
      (ComplexRawQuotient.ofRaw a ha - ComplexRawQuotient.ofRaw p hp)) +
      -(ComplexRawQuotient.ofRaw (RotationLift.HalfPiInput.rotation A) hl -
        ComplexRawQuotient.ofRaw p hp) =
      ComplexRawQuotient.ofRaw (entireExponentialValue z).val hv -
        ComplexRawQuotient.ofRaw (RotationLift.HalfPiInput.rotation A) hl
    grind
  have hb := Small.congr (add_valid (add_valid (sub_valid hv ha) (sub_valid ha hp))
    (neg_valid (sub_valid hl hp))) (sub_valid hv hl) heq hs
  simpa only [Rat.zero_add] using hb

theorem entireExponential_geometric_halfPi_rotation :
    (entireExponentialValue
      ⟨GeometricPiRotation.imaginaryHalf,GeometricPiRotation.imaginaryHalf_valid⟩).val.Equiv
      GeometricPiRotation.rotation :=
  entireExponential_represented_rotation GeometricPiRotation.halfPiInput

end ComputableAnalysis.ModularForms
