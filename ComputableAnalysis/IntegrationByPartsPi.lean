import ComputableAnalysis.ArctanRectanglePi
import ComputableAnalysis.CauchyPi
import ComputableAnalysis.IntegralIdentities

/-!
# A finite integration-by-parts mesh computation of pi

This module exposes the literal rational mesh algorithm behind the finite
integration-by-parts animation.  Its candidate uses the corner budget from a
common subdivision; prefix stabilization then makes a valid raw real.  The
result agrees with the reciprocal-square rectangle computation, independently
of the separate arctangent--logarithm endpoint formula.
-/

namespace ComputableAnalysis

namespace IntegrationByPartsPi

/-- Four times the stabilized finite integration-by-parts mesh computation. -/
def raw : RealRaw := IntegralIdentities.piFromArctanIntegrationByPartsMesh

theorem raw_valid : raw.Valid :=
  IntegralIdentities.piFromArctanIntegrationByPartsMesh_valid

/-- The mesh algorithm reaches the exact reciprocal-square rectangle raw
through its explicit finite corner-error certificate. -/
theorem raw_equiv_rectangleRaw : raw.Equiv ArctanRectanglePi.raw := by
  unfold raw ArctanRectanglePi.raw
  exact RealRaw.natScale_equiv 4
    IntegralIdentities.arctanIntegrationByPartsMesh_equiv_rectangleAtOne

/-- The finite integration-by-parts mesh is a certified computation of
geometric circle-area pi. -/
theorem raw_equiv_piCircleArea : raw.Equiv piCircleArea := by
  exact RealRaw.equiv_trans raw_valid ArctanRectanglePi.raw_valid
    CauchyPi.piCircleArea_valid raw_equiv_rectangleRaw
    ArctanRectanglePi.raw_equiv_piCircleArea

end IntegrationByPartsPi

end ComputableAnalysis
