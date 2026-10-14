import ComputableAnalysis.ModularForms.ExponentialCenterApproximation

/-! Value error against the actual moving-center candidate retained by the
older represented exponential lift. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem legacy_lift_candidate_error {C : Rat}
    (A : ComplexExponentialLift.BoundedInput C) (n : Nat) :
    Small (sub (ComplexExponentialLift.BoundedInput.exponential A)
      (ofQComplex (ComplexExponentialApproximation.expPrefix (A.raw.compute n).center
        (RationalMajorant.factorialTailStart C+n))))
      (centerError (ComplexExponentialLift.BoundedInput.exponential A) n) := by
  have hv := ComplexExponentialLift.BoundedInput.exponential_valid A
  have hp := ComplexExponentialLift.BoundedInput.exponential_contains_current_candidate A n
  apply point_in_box_error _ hv _ n _ hp
  · have hh := (hv.1 n).2
    unfold centerError
    grind
  · have hw := (hv.1 n).1
    unfold centerError
    grind

theorem legacy_lift_candidate_error_shrinks {C : Rat}
    (A : ComplexExponentialLift.BoundedInput C) :
    ShrinksToZero (centerError (ComplexExponentialLift.BoundedInput.exponential A)) :=
  centerError_shrinks _ (ComplexExponentialLift.BoundedInput.exponential_valid A)

theorem entire_center_candidate_error (z : Scalar) (start n : Nat) :
    Small (sub (entireExponentialValue (rationalCenter z n)).val
      (ofQComplex (ComplexExponentialApproximation.expPrefix (z.val.compute n).center (start+n))))
      (4*exponentialBudget (exponentialRatio (exponentialInputRadius z))*
        (2*exponentialRatio (exponentialInputRadius z)*(exponentialInputRadius z).val)^(start+n)) := by
  let R := exponentialInputRadius z
  let a := rationalCenter z n
  have ha := rationalCenter_chart z n
  have hC := exponentialBudget_nonnegative _ (exponentialRatio_positive R)
  have hK := Rat.le_of_lt (exponentialRatio_positive R)
  have hR := Rat.le_of_lt R.property
  have hlocal : 2*exponentialRatio R*R.val ≤ (1 : Rat)/2 := by
    have h := exponentialRatio_local R
    grind
  have hb := BoundedSeries.sumValue_close_prefix exponentialCoefficients a.val
    exponentialCoefficients_valid a.property
    (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val hC hK hR
    (exponentialCoefficients_small _ (exponentialRatio_positive R))
    (LocalODE.interior_bound R.val a ha) hlocal (start+n)
  rw [BoundedSeries.valueBlock_as_terms] at hb
  have hv := (exponentialChart R).valid a ha
  have hp := ScalarSeries.block_valid _
    (LocalODE.seriesTerm_valid _ _ exponentialCoefficients_valid a.property) 0 (start+n)
  exact Small.congr (sub_valid hv hp)
    (sub_valid (entireExponentialValue a).property (ofQComplex_valid _))
    (FunctionTheory.sub_congr (entireExponential_chart R a ha)
      (rational_exponential_prefix_equiv (z.val.compute n).center (start+n))) hb

end ComputableAnalysis.ModularForms
