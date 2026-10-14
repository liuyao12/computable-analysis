import ComputableAnalysis.ModularForms.PairedEntireIntegerLocalBound

/-! Quantitative bounds for actual Riccati values times rational Cauchy kernels. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedEntireRiccatiMap_squared_kernel_bound (z : Scalar) (q : QComplex)
    (R : Rat) (hR : 0<R)
    (hq : R≤q.re ∨ q.re≤ -R ∨ R≤q.im ∨ q.im≤ -R) :
    Small (mul (pairedEntireRiccatiMap.eval z trivial).val
      (mul (ofQComplex (RationalReciprocal.inverse q))
        (ofQComplex (RationalReciprocal.inverse q)))) (21479360*(1/R)*(1/R)) := by
  have hi := (BoxApproximation.rational_small (RationalReciprocal.inverse q)).mono
    (rationalSeparated_inverse_coordinate_bound q R hR hq)
  have hn : 0≤(1:Rat)/R := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr hR))
  have hs := Small.mul (ofQComplex_valid _) (ofQComplex_valid _) hn hn hi hi
  have hp := Small.mul (pairedEntireRiccatiMap.eval z trivial).property
    (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))
    (show (0:Rat)≤5369840 by decide +kernel)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hn) hn)
    (pairedEntireRiccatiMap_global_bound z) hs
  exact hp.mono (by grind only)

end ComputableAnalysis.ModularForms
