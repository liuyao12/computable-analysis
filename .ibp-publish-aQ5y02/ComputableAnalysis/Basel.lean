import ComputableAnalysis.DirichletSeries
import ComputableAnalysis.Pi
import ComputableAnalysis.PiProofs

/-!
# Euler Basel problem

This file sets up the computable statement of zeta(2) = pi^2 / 6.
The zeta algorithms and their validity proofs live in DirichletSeries;
this file keeps the Basel-specific comparison with the pi algorithms.
-/

namespace ComputableAnalysis

namespace Basel

/-- Project-facing name for the Basel-series raw algorithm. -/
def baselSeriesRaw : RealRaw :=
  DirichletSeries.zetaTwoRaw

theorem baselSeriesRaw_valid : baselSeriesRaw.Valid := by
  simpa [baselSeriesRaw] using DirichletSeries.zetaTwoRaw_validCompute

def baselSeries : Real :=
  Real.ofRaw baselSeriesRaw baselSeriesRaw_valid

/-- Raw interval algorithm for `pi^2 / 6`, using any chosen raw pi
representative. -/
def piSquaredOverSixRaw (pi : RealRaw) : RealRaw :=
  RealRaw.scaleRat (1 / 6) (pi * pi)

theorem piSquaredOverSixRaw_valid_of_nonneg_bounded
    {pi : RealRaw} (hpi : pi.Valid) {B : Rat} (hB : 0 < B)
    (hbounds : forall n, 0 <= (pi.compute n).lo ∧ (pi.compute n).hi <= B) :
    (piSquaredOverSixRaw pi).Valid := by
  unfold piSquaredOverSixRaw
  exact RealRaw.scaleRat_valid_of_nonneg
    (by native_decide : (0 : Rat) <= 1 / 6)
    (RealRaw.mulSelf_valid_of_nonneg_bounded hpi hB hbounds)

/-- The right-hand side of Basel using the current geometric area definition
of pi. -/
def geometricPiSquaredOverSixRaw : RealRaw :=
  piSquaredOverSixRaw piCircleArea

theorem piCircleArea_nonneg_bounded_by_four (n : Nat) :
    0 <= (piCircleArea.compute n).lo ∧ (piCircleArea.compute n).hi <= 4 := by
  have hvalid : piCircleArea.Valid := by
    simpa [PiProofs.AreaValid] using PiProofs.AreaLoopValidity.areaValid
  have hnested := hvalid.2.1 0 n (Nat.zero_le n)
  constructor
  · have hlow : (piCircleArea.compute 0).lo <= (piCircleArea.compute n).lo :=
      hnested.1
    rw [piCircleArea_compute_zero] at hlow
    grind
  · have hhigh : (piCircleArea.compute n).hi <= (piCircleArea.compute 0).hi :=
      hnested.2.2
    rw [piCircleArea_compute_zero] at hhigh
    simpa using hhigh

theorem geometricPiSquaredOverSixRaw_valid :
    geometricPiSquaredOverSixRaw.Valid := by
  unfold geometricPiSquaredOverSixRaw
  exact piSquaredOverSixRaw_valid_of_nonneg_bounded
    (by simpa [PiProofs.AreaValid] using PiProofs.AreaLoopValidity.areaValid)
    (by native_decide : (0 : Rat) < 4)
    piCircleArea_nonneg_bounded_by_four

/- Put the cursor here to compare with the zeta-side interval above. -/
#eval! geometricPiSquaredOverSixRaw.decimalAt 12
  5

/-- Euler's Basel theorem as equality of computable raw reals. -/
def EulerBaselStatement (pi : RealRaw) : Prop :=
  DirichletSeries.zetaTwoRaw.Equiv (piSquaredOverSixRaw pi)

/-- Euler's Basel theorem statement for the geometric area definition of pi.

This is the analytic theorem still to be proved constructively; possible
routes include Euler's sine-product argument, Fourier series for a concrete
piecewise polynomial, or a contour/argument-principle route once the complex
function theory layer is mature. -/
def eulerBasel_geometricPi : Prop :=
  EulerBaselStatement piCircleArea

end Basel

end ComputableAnalysis
