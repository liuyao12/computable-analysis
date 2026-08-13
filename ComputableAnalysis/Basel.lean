import ComputableAnalysis.DirichletSeries
import ComputableAnalysis.Pi
import ComputableAnalysis.PiProofs
import ComputableAnalysis.CircumferenceBridge

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

theorem baselSeriesRaw_compute_eq (n : Nat) :
    baselSeriesRaw.compute n = DirichletSeries.zetaTwoInterval n := by
  rfl

theorem baselSeriesRaw_validCompute :
    RealRaw.ValidCompute baselSeriesRaw.compute := by
  simpa [baselSeriesRaw] using DirichletSeries.zetaTwoRaw_validCompute

/-- The project-facing Basel evaluator reaches every positive rational
precision request through an explicit finite stage.  This is a potential-
infinity statement about the interval algorithm, not an attained zeta value
or Euler's Basel identity. -/
theorem baselSeriesRaw_reaches_of_positive_tolerance (eps : QPos) :
    ∃ n : Nat, (baselSeriesRaw.compute n).width <= eps.val := by
  refine ⟨eps.val.den + 1, ?_⟩
  rw [baselSeriesRaw_compute_eq]
  exact DirichletSeries.zetaTwoInterval_width_le_of_denominator_budget
    eps.property (Nat.le_refl (eps.val.den + 1))

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

/-- Squaring and scaling preserve a pi equivalence when both rational interval
representatives have nonnegative lower endpoints.  This is a finite interval
calculation, so it does not identify raw reals by an ambient completed field. -/
theorem piSquaredOverSixRaw_equiv_of_nonneg
    {pi pi' : RealRaw} (hpi : pi.Valid) (hpi' : pi'.Valid)
    (hpi_nonneg : forall n, 0 <= (pi.compute n).lo)
    (hpi'_nonneg : forall n, 0 <= (pi'.compute n).lo)
    (hequiv : pi.Equiv pi') :
    (piSquaredOverSixRaw pi).Equiv (piSquaredOverSixRaw pi') := by
  unfold piSquaredOverSixRaw
  apply RealRaw.scaleRat_equiv_of_nonneg (by native_decide)
  exact RealRaw.mul_equiv_of_nonneg hpi hpi' hpi hpi'
    hpi_nonneg hpi'_nonneg hpi_nonneg hpi'_nonneg hequiv hequiv

/-- The right-hand side of Basel using the current geometric area definition
of pi. -/
def geometricPiSquaredOverSixRaw : RealRaw :=
  piSquaredOverSixRaw piCircleArea

/-- The Basel right-hand side computed from the original square-root
circumference evaluator. -/
def circumferencePiSquaredOverSixRaw : RealRaw :=
  piSquaredOverSixRaw piCircumference

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

theorem circumferencePiSquaredOverSixRaw_valid :
    circumferencePiSquaredOverSixRaw.Valid := by
  unfold circumferencePiSquaredOverSixRaw
  exact piSquaredOverSixRaw_valid_of_nonneg_bounded
    PiProofs.piCircumference_valid
    (by native_decide : (0 : Rat) < 4)
    PiProofs.piCircumference_nonneg_bounded_by_four

/-- The two certified geometric pi computations give the same Basel
right-hand side.  This is not Euler's Basel theorem: the independent zeta-two
series comparison remains a separate analytic result. -/
theorem circumferencePiSquaredOverSixRaw_equiv_geometric :
    circumferencePiSquaredOverSixRaw.Equiv geometricPiSquaredOverSixRaw := by
  exact piSquaredOverSixRaw_equiv_of_nonneg
    PiProofs.piCircumference_valid
    (by simpa [PiProofs.AreaValid] using PiProofs.AreaLoopValidity.areaValid)
    (fun n => (PiProofs.piCircumference_nonneg_bounded_by_four n).1)
    (fun n => (piCircleArea_nonneg_bounded_by_four n).1)
    PiProofs.piCircumferenceDirect_equiv_piCircleArea

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

/-- Euler's Basel statement with pi supplied by the original certified
circumference computation. -/
def eulerBasel_circumferencePi : Prop :=
  EulerBaselStatement piCircumference

/-- The geometric Basel target can be proved by showing that the two valid
raw algorithms overlap at every pair of finite stages.  This is the native
computable-real form of the remaining theorem; it does not invoke a
completed zeta value or classical completeness. -/
theorem eulerBasel_geometric_iff_allStagesOverlap :
    eulerBasel_geometricPi ↔
      DirichletSeries.zetaTwoRaw.AllStagesOverlap
        (piSquaredOverSixRaw piCircleArea) := by
  unfold eulerBasel_geometricPi EulerBaselStatement
  exact RealRaw.equiv_iff_allStagesOverlap
    DirichletSeries.zetaTwoRaw_validCompute
    geometricPiSquaredOverSixRaw_valid

/-- The circumference-based Basel target has the same all-stage-overlap
criterion, independently of the chosen certified pi representative. -/
theorem eulerBasel_circumference_iff_allStagesOverlap :
    eulerBasel_circumferencePi ↔
      DirichletSeries.zetaTwoRaw.AllStagesOverlap
        (piSquaredOverSixRaw piCircumference) := by
  unfold eulerBasel_circumferencePi EulerBaselStatement
  exact RealRaw.equiv_iff_allStagesOverlap
    DirichletSeries.zetaTwoRaw_validCompute
    circumferencePiSquaredOverSixRaw_valid

/-- The unresolved Basel theorem is independent of which certified geometric
pi evaluator supplies its squared right-hand side. -/
theorem eulerBasel_circumference_iff_geometric :
    eulerBasel_circumferencePi ↔ eulerBasel_geometricPi := by
  constructor
  · intro h
    exact RealRaw.equiv_trans
      DirichletSeries.zetaTwoRaw_validCompute
      circumferencePiSquaredOverSixRaw_valid
      geometricPiSquaredOverSixRaw_valid
      h
      circumferencePiSquaredOverSixRaw_equiv_geometric
  · intro h
    exact RealRaw.equiv_trans
      DirichletSeries.zetaTwoRaw_validCompute
      geometricPiSquaredOverSixRaw_valid
      circumferencePiSquaredOverSixRaw_valid
      h
      (RealRaw.equiv_symm circumferencePiSquaredOverSixRaw_equiv_geometric)

end Basel

end ComputableAnalysis
