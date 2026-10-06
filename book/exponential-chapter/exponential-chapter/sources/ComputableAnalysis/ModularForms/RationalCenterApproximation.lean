import ComputableAnalysis.ModularForms.ExponentialLegacyTail
import ComputableAnalysis.ModularForms.ExponentialLegacyAgreement
import ComputableAnalysis.ComplexExponentialLift

/-! Rational center approximations with explicit shrinking value errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def centerError (z : ComplexRaw) (n : Nat) : Rat :=
  (z.compute n).width+(z.compute n).height

theorem centerError_nonnegative (z : ComplexRaw) (hz : z.Valid) (n : Nat) :
    0 ≤ centerError z n := Rat.add_nonneg (hz.1 n).1 (hz.1 n).2

theorem rational_center_error (z : ComplexRaw) (hz : z.Valid) (n : Nat) :
    Small (sub z (ofQComplex (z.compute n).center)) (centerError z n) := by
  apply point_in_box_error z hz _ n _ (QBox.center_mem (valid_ordered hz n))
  · have hh := (hz.1 n).2
    unfold centerError
    grind
  · have hw := (hz.1 n).1
    unfold centerError
    grind

theorem centerError_shrinks (z : ComplexRaw) (hz : z.Valid) :
    ShrinksToZero (centerError z) := by
  intro eps
  let half : QPos := ⟨eps.val/2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  obtain ⟨N,hN⟩ := hz.2.2 half
  refine ⟨N,?_⟩
  intro n hn
  have h := hN n hn
  change (z.compute n).width+(z.compute n).height ≤ eps.val
  dsimp [half] at h
  have he : eps.val/2+eps.val/2=eps.val := by grind [Rat.div_def]
  grind

/-- The older represented lift agrees with the entire evaluator on every
exact rational input, for every justified input budget. -/
theorem entireExponential_legacy_rational_lift (z : QComplex) (C : Rat)
    (hC : 0 ≤ C) (hzC : QComplex.normBound z ≤ C) :
    (entireExponentialValue ⟨ofQComplex z,ofQComplex_valid z⟩).val.Equiv
      (ComplexExponentialLift.BoundedInput.exponential
        (ComplexExponentialLift.BoundedInput.ofQComplex z C hC hzC)) := by
  have hnew := entireExponential_legacy_rational z C hC hzC
  have hold := ComplexExponentialLift.BoundedInput.exponential_ofQComplex_equiv_exponentialRawAt z C hC hzC
  exact equiv_trans (entireExponentialValue ⟨ofQComplex z,ofQComplex_valid z⟩).property
    (ComplexExponentialApproximation.exponentialRawAt_valid hC hzC)
    (ComplexExponentialLift.BoundedInput.exponential_valid _)
    hnew (equiv_symm hold)

end ComputableAnalysis.ModularForms
