import ComputableAnalysis.ArctanGeometry

/-!
# The reciprocal-square rectangle computation of pi

This small bridge packages the first integral computation in the blueprint:
the exact left/right rational rectangle enclosure of `1 / (1 + t^2)` on
`[0,1]`.  Its proof reaches the circle-area representative through the
geometric arctangent computation, without importing the pi-presentation
registry.
-/

namespace ComputableAnalysis

namespace ArctanRectanglePi

/-- Four times the exact rational rectangle computation of
`1 / (1 + t^2)` on `[0,1]`. -/
def raw : RealRaw :=
  (4 : Nat) * ArctanGeometry.arctanIntegralRectangleRawAtOne

theorem raw_valid : raw.Valid := by
  unfold raw
  exact RealRaw.natScale_valid 4
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid

/-- The reciprocal-square rectangle computation agrees with four times the
geometric sector-area arctangent at the unit endpoint. -/
theorem raw_equiv_four_arctanGeom_one :
    raw.Equiv ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat)) := by
  unfold raw
  exact RealRaw.natScale_equiv 4
    ArctanGeometry.arctanIntegralRectangleRawAtOne_equiv_arctanGeom_one

/-- The direct rectangle integral computes the same raw real as the
circle-area algorithm.  The route is a finite chain of interval-overlap
certificates, not a completeness or general integration theorem. -/
theorem raw_equiv_piCircleArea : raw.Equiv piCircleArea := by
  have harea : piCircleArea.Valid := by
    change RealRaw.ValidCompute piCircleArea.compute
    have hcompute : piCircleArea.compute =
        ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).compute := by
      funext n
      exact (ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n).symm
    rw [hcompute]
    exact ArctanGeometry.four_arctanGeom_one_valid
  exact RealRaw.equiv_trans raw_valid
    ArctanGeometry.four_arctanGeom_one_valid
    harea
    raw_equiv_four_arctanGeom_one
    ArctanGeometry.four_arctanGeom_one_equiv_piCircleArea

end ArctanRectanglePi

end ComputableAnalysis
