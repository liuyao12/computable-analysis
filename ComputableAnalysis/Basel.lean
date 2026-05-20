import ComputableAnalysis.DirichletSeries
import ComputableAnalysis.Pi

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

def intervalScaleRat (r : Rat) (I : QInterval) : QInterval :=
  if 0 <= r then
    { lo := r * I.lo, hi := r * I.hi }
  else
    { lo := r * I.hi, hi := r * I.lo }

def intervalMul (I J : QInterval) : QInterval :=
  QBox.mulRealInterval I.lo I.hi J.lo J.hi

/-- Raw interval algorithm for `pi^2 / 6`, using any chosen raw pi
representative. -/
def piSquaredOverSixRaw (pi : RealRaw) : RealRaw where
  compute := fun n =>
    intervalScaleRat (1 / 6) (intervalMul (pi.compute n) (pi.compute n))

/-- The right-hand side of Basel using the current geometric area definition
of pi. -/
def geometricPiSquaredOverSixRaw : RealRaw :=
  piSquaredOverSixRaw piCircleArea

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
