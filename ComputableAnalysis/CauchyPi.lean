import ComputableAnalysis.IntegralIdentities

/-!
# The full-line Cauchy integral computation of pi

This module keeps the full-line route separate from the large presentation
registry.  The program compactifies the two rational tails of
`1 / (1 + x^2)` onto `[0,1]`; at every stage its box is exactly the box of
four times the unit-interval rectangle computation.  The final comparison is
therefore a direct chain of interval certificates to the circle-area raw real.
-/

namespace ComputableAnalysis

namespace CauchyPi

/-- The unit-interval rectangle computation, scaled to the full Cauchy
integral. -/
def rectangleRaw : RealRaw :=
  IntegralIdentities.PiFromArctanIntegral
    IntegralIdentities.arctanIntegralRectangleForAtOne

theorem rectangleRaw_valid : rectangleRaw.Valid := by
  unfold rectangleRaw IntegralIdentities.PiFromArctanIntegral
  exact RealRaw.natScale_valid 4
    IntegralIdentities.arctanIntegralRectangleForAtOne_valid

theorem piCircleArea_valid : piCircleArea.Valid := by
  change RealRaw.ValidCompute piCircleArea.compute
  have hcompute : piCircleArea.compute =
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).compute := by
    funext n
    exact (ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n).symm
  rw [hcompute]
  exact ArctanGeometry.four_arctanGeom_one_valid

/-- Four rectangle integrals of `1 / (1+t^2)` agree with the geometric
circle-area computation of pi. -/
theorem rectangleRaw_equiv_piCircleArea : rectangleRaw.Equiv piCircleArea := by
  have hscaled : rectangleRaw.Equiv
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) := by
    unfold rectangleRaw IntegralIdentities.PiFromArctanIntegral
    exact RealRaw.natScale_equiv 4
      IntegralIdentities.arctanIntegralRectangleForAtOne_equiv_arctanGeom_one
  exact RealRaw.equiv_trans rectangleRaw_valid
    ArctanGeometry.four_arctanGeom_one_valid
    piCircleArea_valid
    hscaled
    ArctanGeometry.four_arctanGeom_one_equiv_piCircleArea

/-- The full-line rational Cauchy algorithm.  Its density is split by
evenness and the reciprocal substitution before any limit is taken. -/
def raw : RealRaw := IntegralIdentities.cauchyFullLineIntegral

theorem raw_valid : raw.Valid :=
  IntegralIdentities.cauchyFullLineIntegral_valid

/-- The compactified full-line computation and the scaled unit rectangle
computation have identical rational boxes stage by stage. -/
theorem raw_compute_eq_rectangleRaw (n : Nat) :
    raw.compute n = rectangleRaw.compute n := by
  unfold raw rectangleRaw IntegralIdentities.PiFromArctanIntegral
  exact IntegralIdentities.cauchyFullLineIntegral_compute_eq_four_rectangle n

/-- The full-line Cauchy integral is a certified computation of the same pi
as the rational circle-area algorithm. -/
theorem raw_equiv_piCircleArea : raw.Equiv piCircleArea := by
  intro n
  apply (RealRaw.compareAt_overlap_iff raw piCircleArea n n).2
  rw [raw_compute_eq_rectangleRaw n]
  exact (RealRaw.compareAt_overlap_iff rectangleRaw piCircleArea n n).1
    (rectangleRaw_equiv_piCircleArea n)

end CauchyPi

end ComputableAnalysis
