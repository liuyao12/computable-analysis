import ComputableAnalysis.PiProofs
import ComputableAnalysis.Logarithm

/-!
# Direct Stieltjes square-substitution pi bridge

This module exposes the literal finite Stieltjes mesh behind the existing
square-substitution logarithm as a named pi computation.  The evaluator uses
only finite rational Stieltjes sums and stabilization radii at runtime; the
reciprocal-log integral is used only for its certificate and equivalence.
-/

namespace ComputableAnalysis

namespace PiProofs

/-- The arctangent triangle plus direct square-Stieltjes logarithm evaluator.

Its second summand is the finite mesh computation whose terms are
(xᵢ₊₁² - xᵢ²) / (1 + xᵢ²), stabilized by an explicit rational radius.
It is a supplementary executable view of the already checked square
substitution, not an additional coverage-suite capability. -/
def piTriangleLogSquareStieltjes : RealRaw :=
  (4 : Nat) * Logarithm.arctanIntegralTriangle +
    (2 : Nat) * Logarithm.logTwoSquareStieltjesRaw

theorem piTriangleLogSquareStieltjes_valid :
    piTriangleLogSquareStieltjes.Valid := by
  unfold piTriangleLogSquareStieltjes
  exact RealRaw.add_valid
    (RealRaw.natScale_valid 4 Logarithm.arctanIntegralTriangle_valid)
    (RealRaw.natScale_valid 2 Logarithm.logTwoSquareStieltjesRaw_valid)

/-- The direct Stieltjes substitution and reciprocal-log versions of the
supplied arctangent formula agree. -/
theorem piTriangleLogSquareStieltjes_equiv_piTriangleLogReciprocalIntegral :
    piTriangleLogSquareStieltjes.Equiv
      Logarithm.piTriangleLogReciprocalIntegral := by
  have htriangle : ((4 : Nat) * Logarithm.arctanIntegralTriangle).Valid :=
    RealRaw.natScale_valid 4 Logarithm.arctanIntegralTriangle_valid
  have hstieltjes : ((2 : Nat) * Logarithm.logTwoSquareStieltjesRaw).Valid :=
    RealRaw.natScale_valid 2 Logarithm.logTwoSquareStieltjesRaw_valid
  have hreciprocal :
      ((2 : Nat) * Logarithm.logTwoReciprocalIntegral).Valid :=
    RealRaw.natScale_valid 2 Logarithm.logTwoReciprocalIntegral_valid
  unfold piTriangleLogSquareStieltjes
    Logarithm.piTriangleLogReciprocalIntegral
  exact RealRaw.add_equiv htriangle htriangle hstieltjes hreciprocal
    (RealRaw.equiv_refl ((4 : Nat) * Logarithm.arctanIntegralTriangle)
      htriangle)
    (RealRaw.natScale_equiv 2
      Logarithm.logTwoSquareStieltjesRaw_equiv_reciprocalIntegral)

/-- The direct square-Stieltjes computation is pi by the independently
certified reciprocal-log integration-by-parts bridge. -/
theorem piTriangleLogSquareStieltjes_equiv_piCircleArea :
    piTriangleLogSquareStieltjes.Equiv piCircleArea := by
  exact RealRaw.equiv_trans
    piTriangleLogSquareStieltjes_valid
    Logarithm.piTriangleLogReciprocalIntegral_valid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    piTriangleLogSquareStieltjes_equiv_piTriangleLogReciprocalIntegral
    piTriangleLogReciprocalIntegral_equiv_piCircleArea

namespace pi

/-- The literal finite Stieltjes implementation of the checked square
substitution, available as a supplementary view of the abstract pi value. -/
def squareStieltjes : Real.Representation value where
  raw := piTriangleLogSquareStieltjes
  valid := piTriangleLogSquareStieltjes_valid
  agrees := piTriangleLogSquareStieltjes_equiv_piCircleArea

theorem squareStieltjes_equiv_squareSubstitution :
    squareStieltjes.raw.Equiv squareSubstitution.raw :=
  representations_equiv squareStieltjes squareSubstitution

end pi

end PiProofs

end ComputableAnalysis
