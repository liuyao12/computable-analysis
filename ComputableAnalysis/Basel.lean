import ComputableAnalysis.DirichletSeries
import ComputableAnalysis.Pi
import ComputableAnalysis.ArctanGeometry

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
  change RealRaw.ValidCompute DirichletSeries.zetaTwoInterval
  exact DirichletSeries.zetaTwoRaw_validCompute

theorem baselSeriesRaw_compute_eq (n : Nat) :
    baselSeriesRaw.compute n = DirichletSeries.zetaTwoInterval n := by
  rfl

theorem baselSeriesRaw_validCompute :
    RealRaw.ValidCompute baselSeriesRaw.compute := by
  change RealRaw.ValidCompute DirichletSeries.zetaTwoInterval
  exact DirichletSeries.zetaTwoRaw_validCompute

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

theorem piCircleArea_nonneg_bounded_by_four (n : Nat) :
    0 <= (piCircleArea.compute n).lo ∧ (piCircleArea.compute n).hi <= 4 := by
  have hvalid : piCircleArea.Valid := by
    change RealRaw.ValidCompute piCircleArea.compute
    have hcompute :
        (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).compute) =
          piCircleArea.compute := by
      funext k
      exact ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute k
    rw [← hcompute]
    exact ArctanGeometry.four_arctanGeom_one_valid
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
    (by
      change RealRaw.ValidCompute piCircleArea.compute
      have hcompute :
          (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).compute) =
            piCircleArea.compute := by
        funext n
        exact ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n
      rw [← hcompute]
      exact ArctanGeometry.four_arctanGeom_one_valid)
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

/-- A stagewise rational-witness criterion for the geometric Basel identity.
The future analytic proof only has to construct these finite witnesses; no
completed real number or classical completeness principle is required here. -/
theorem eulerBasel_geometric_of_stagewise_witness
    (h : forall n m : Nat, ∃ q : Rat,
      (DirichletSeries.zetaTwoRaw.compute n).lo <= q ∧
        q <= (DirichletSeries.zetaTwoRaw.compute n).hi ∧
      ((piSquaredOverSixRaw piCircleArea).compute m).lo <= q ∧
        q <= ((piSquaredOverSixRaw piCircleArea).compute m).hi) :
    eulerBasel_geometricPi := by
  unfold eulerBasel_geometricPi EulerBaselStatement
  apply RealRaw.allStagesOverlap_equiv
  intro n m
  apply (RealRaw.compareAt_overlap_iff
    DirichletSeries.zetaTwoRaw (piSquaredOverSixRaw piCircleArea) n m).2
  rcases h n m with ⟨q, hzl, hzh, hpl, hph⟩
  constructor <;> grind

end Basel

end ComputableAnalysis
