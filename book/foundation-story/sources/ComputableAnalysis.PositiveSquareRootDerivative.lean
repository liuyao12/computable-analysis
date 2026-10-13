import ComputableAnalysis.PositiveSquareRootDifferential
import ComputableAnalysis.RepresentedHeatKernelFirstJet
import ComputableAnalysis.PositiveReciprocal
import ComputableAnalysis.FiniteDerivativeLimit

/-!
# Direct positive square-root calculus on a rational chart

This module presents the already nested rational square-root bisection as a
`FunctionOnInterval`, constructs the represented candidate `1/(2*sqrt t)` by
positive interval inversion, and identifies the value evaluator with the
guarded represented square root used by the direct heat-kernel jet.

The final `HasDerivativeOnInterval` certificate is assembled from finite
midpoint witnesses.  Its quantitative scheduler is kept separate from these
value and representation bridges.
-/

namespace ComputableAnalysis
namespace PositiveSquareRootDerivative

open RepresentedHeatKernelFirstJet
open RepresentedPositiveSquareRoot

abbrev PositiveTimeChart :=
  RepresentedHeatKernelFirstJet.PositiveTimeChart

def rootLower (chart : PositiveTimeChart) : Rat := chart.margin / 2

theorem rootLower_pos (chart : PositiveTimeChart) : 0 < rootLower chart := by
  unfold rootLower
  rw [Rat.div_def]
  exact Rat.mul_pos chart.margin_pos
    ((Rat.inv_pos).2 (by decide +kernel))

theorem sqrtDomainAt (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) : sqrtDomain t := by
  unfold sqrtDomain
  have hm0 : 0 <= chart.margin := Rat.le_of_lt chart.margin_pos
  have hsq0 : 0 <= sq chart.margin := by
    unfold sq
    exact Rat.mul_nonneg hm0 hm0
  have ht0 : 0 <= t :=
    Rat.le_trans hsq0
      (Rat.le_trans chart.margin_sq_le_lower ht.1)
  grind

/-- Direct nested rational bisection of `sqrt t`. -/
def rootAt (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) : RealRaw :=
  sqrtRaw t (sqrtDomainAt chart t ht)

theorem rootAt_valid (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) :
    (rootAt chart t ht).Valid :=
  sqrtRaw_valid t (sqrtDomainAt chart t ht)

theorem margin_sq_le_time (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) :
    sq chart.margin <= t :=
  Rat.le_trans chart.margin_sq_le_lower ht.1

/-- A simple chart-wide upper bound for every finite square-root endpoint. -/
theorem rootAt_hi_le_chartBound (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (n : Nat) :
    ((rootAt chart t ht).compute n).hi <= (chart.bound + 1 : Nat) := by
  have htBound : t <= (chart.bound : Rat) :=
    Rat.le_trans ht.2 chart.upper_le_bound
  have hsqrtBound : sqrtUpperBound t <= (chart.bound + 1 : Nat) := by
    unfold sqrtUpperBound maxRat
    by_cases h : (1 : Rat) <= t
    · rw [if_pos h]
      exact Rat.le_trans htBound (by exact_mod_cast Nat.le_succ chart.bound)
    · rw [if_neg h]
      exact_mod_cast Nat.succ_pos chart.bound
  exact Rat.le_trans
    (by
      simpa [rootAt, sqrtRaw] using
        sqrtApproxOnDomain_hi_le_upperBound t
          (sqrtDomainAt chart t ht) n)
    hsqrtBound

theorem rootAt_endpoint_sum_le (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (n : Nat) :
    ((rootAt chart t ht).compute n).hi +
        ((rootAt chart t ht).compute n).lo <=
      2 * (chart.bound + 1 : Nat) := by
  have hspec := sqrtRaw_stage_spec t (sqrtDomainAt chart t ht) n
  have hlo := Rat.le_trans hspec.2.1 (rootAt_hi_le_chartBound chart t ht n)
  have hhi := rootAt_hi_le_chartBound chart t ht n
  exact Rat.le_trans (rat_add_le_add hhi hlo) (by grind)

/-- Pointwise executable stage making the direct square-root box narrower
than a requested positive rational tolerance. -/
def rootWidthStage (t : Rat) (eps : QPos) : Nat :=
  RationalMajorant.natRateStage (sqrtWidthConstant t : Rat) eps

theorem rootAt_width_le_of_rootWidthStage_le
    (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (eps : QPos)
    {stage : Nat} (hstage : rootWidthStage t eps <= stage) :
    ((rootAt chart t ht).compute stage).width <= eps.val := by
  have hraw := sqrtApproxOnDomain_width_le_nat_over_succ t
    (sqrtDomainAt chart t ht) stage
  have hrate := RationalMajorant.natRateStage_spec_of_le
    (bound := (sqrtWidthConstant t : Rat)) Rat.natCast_nonneg eps hstage
  exact Rat.le_trans (by simpa [rootAt, sqrtRaw] using hraw) hrate

theorem rootLower_le_rootAt_hi (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (n : Nat) :
    rootLower chart <= ((rootAt chart t ht).compute n).hi := by
  have hhalf : rootLower chart <= chart.margin := by
    unfold rootLower
    rw [Rat.div_def]
    have hm0 := Rat.le_of_lt chart.margin_pos
    have hinv : (2 : Rat)⁻¹ <= 1 := by decide +kernel
    simpa only [Rat.mul_one] using
      Rat.mul_le_mul_of_nonneg_left hinv hm0
  exact Rat.le_trans hhalf
    ((sqrtRaw_stage_spec t (sqrtDomainAt chart t ht) n).le_hi_of_sq_le
      (margin_sq_le_time chart t ht))

/-- Represented derivative candidate `1/(2*sqrt t)`, using positive clipping
at the public lower root margin. -/
def derivativeAt (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) : RealRaw :=
  RealRaw.scaleRat (1 / 2)
    (RealRaw.positiveReciprocal (rootAt chart t ht) (rootLower chart))

theorem derivativeAt_valid (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) :
    (derivativeAt chart t ht).Valid := by
  apply RealRaw.scaleRat_valid
  exact RealRaw.positiveReciprocal_valid
    (rootAt chart t ht) (rootLower chart)
    (rootAt_valid chart t ht) (rootLower_pos chart)
    (rootLower_le_rootAt_hi chart t ht)

/-- The exact rational witness used for the derivative certificate at a
finite square-root stage. -/
def derivativeWitness (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (n : Nat) : Rat :=
  (1 / 2) * (1 / ((rootAt chart t ht).compute n).midpoint)

/-- Once the bisection width is at most half the chart margin, its midpoint
is bounded below by that same half-margin.  This is the finite positivity
fact needed before rational inversion. -/
theorem rootLower_le_rootAt_midpoint_of_width_le
    (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (n : Nat)
    (hwidth : ((rootAt chart t ht).compute n).width <= rootLower chart) :
    rootLower chart <= ((rootAt chart t ht).compute n).midpoint := by
  let I := (rootAt chart t ht).compute n
  have hspec : SqrtIntervalSpec t I :=
    sqrtRaw_stage_spec t (sqrtDomainAt chart t ht) n
  have hlo : chart.margin - I.width <= I.lo :=
    hspec.sub_width_le_lo_of_sq_le (margin_sq_le_time chart t ht)
  have hhalf : rootLower chart <= chart.margin - I.width := by
    unfold rootLower at hwidth ⊢
    grind [Rat.div_def]
  exact Rat.le_trans (Rat.le_trans hhalf hlo)
    (QInterval.midpoint_mem hspec.2.1).1

/-- The rational value `1/(2m)`, where `m` is the square-root interval
midpoint, belongs to the represented reciprocal derivative box once the
finite root interval is narrower than the positive chart guard. -/
theorem derivativeWitness_mem (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (n : Nat)
    (hwidth : ((rootAt chart t ht).compute n).width <= rootLower chart) :
    let D := (derivativeAt chart t ht).compute n
    D.lo <= derivativeWitness chart t ht n /\
      derivativeWitness chart t ht n <= D.hi := by
  let I := (rootAt chart t ht).compute n
  have hspec : SqrtIntervalSpec t I :=
    sqrtRaw_stage_spec t (sqrtDomainAt chart t ht) n
  have hmid := QInterval.midpoint_mem hspec.2.1
  have hlowerMid : rootLower chart <= I.midpoint := by
    exact rootLower_le_rootAt_midpoint_of_width_le chart t ht n hwidth
  have hrootPos := rootLower_pos chart
  have hmidPos : 0 < I.midpoint := by grind
  have hmaxPos : 0 < maxRat2 I.lo (rootLower chart) := by
    unfold maxRat2
    by_cases h : I.lo <= rootLower chart
    · simp [h, rootLower_pos chart]
    · rw [if_neg h]
      grind
  have hmaxMid : maxRat2 I.lo (rootLower chart) <= I.midpoint := by
    unfold maxRat2
    by_cases h : I.lo <= rootLower chart
    · simpa [h] using hlowerMid
    · simpa [h] using hmid.1
  have hrecip :
      ({ lo := 1 / I.hi,
         hi := 1 / maxRat2 I.lo (rootLower chart) } : QInterval).lo <=
          1 / I.midpoint /\
        1 / I.midpoint <=
          ({ lo := 1 / I.hi,
             hi := 1 / maxRat2 I.lo (rootLower chart) } : QInterval).hi := by
    exact ⟨
      RealRaw.one_div_antitone_of_pos hmidPos hmid.2,
      RealRaw.one_div_antitone_of_pos hmaxPos hmaxMid⟩
  have hscaled := QInterval.scaleRat_mem (r := (1 / 2 : Rat)) hrecip
  dsimp only
  change
    ((RealRaw.scaleRat (1 / 2)
      (RealRaw.positiveReciprocal (rootAt chart t ht)
        (rootLower chart))).compute n).lo <=
        derivativeWitness chart t ht n /\
      derivativeWitness chart t ht n <=
        ((RealRaw.scaleRat (1 / 2)
          (RealRaw.positiveReciprocal (rootAt chart t ht)
            (rootLower chart))).compute n).hi
  dsimp [RealRaw.scaleRat, RealRaw.scaleRatCompute]
  rw [RealRaw.positiveReciprocal_compute
    (rootAt chart t ht) (rootLower chart) (rootLower_pos chart) n]
  simpa [derivativeWitness, I, QInterval.scaleRat] using hscaled

/-! ## Explicit runtime-width schedule -/

def rootGuardTolerance (chart : PositiveTimeChart) : QPos where
  val := rootLower chart
  property := rootLower_pos chart

def quotientWidthTolerance (h : Rat) (hh : h ≠ 0) (n : Nat) : QPos where
  val := (precisionAtStage n).val * qabs h / 2
  property := by
    rw [Rat.div_def]
    exact Rat.mul_pos
      (Rat.mul_pos (precisionAtStage n).property (qabs_pos_of_ne hh))
      ((Rat.inv_pos).2 (by decide +kernel))

def derivativeWidthTolerance (chart : PositiveTimeChart) (n : Nat) : QPos where
  val := 2 * (precisionAtStage n).val *
    (rootLower chart * rootLower chart)
  property := by
    exact Rat.mul_pos
      (Rat.mul_pos (by decide +kernel) (precisionAtStage n).property)
      (Rat.mul_pos (rootLower_pos chart) (rootLower_pos chart))

/-- One evaluator stage synchronizing the guard needed for reciprocal
membership, both endpoint widths after division by a nonzero step, and the
reciprocal derivative-box width. -/
def widthEvalPrecision (chart : PositiveTimeChart)
    (x h : Rat) (n : Nat) : Nat :=
  let guardStage := rootWidthStage x (rootGuardTolerance chart)
  let derivativeStage := rootWidthStage x (derivativeWidthTolerance chart n)
  if hh : h = 0 then Nat.max guardStage derivativeStage else
    let quotientTolerance := quotientWidthTolerance h hh n
    Nat.max guardStage
      (Nat.max derivativeStage
        (Nat.max
          (rootWidthStage x quotientTolerance)
          (rootWidthStage (x + h) quotientTolerance)))

theorem widthEvalPrecision_guard_width
    (chart : PositiveTimeChart) (x h : Rat) (n : Nat)
    (hx : inDomainInterval chart.lower chart.upper x) :
    ((rootAt chart x hx).compute (widthEvalPrecision chart x h n)).width <=
      rootLower chart := by
  apply rootAt_width_le_of_rootWidthStage_le chart x hx
    (rootGuardTolerance chart)
  unfold widthEvalPrecision
  by_cases hh : h = 0
  · rw [dif_pos hh]
    exact Nat.le_max_left _ _
  · rw [dif_neg hh]
    exact Nat.le_max_left _ _

theorem widthEvalPrecision_quotient_budget
    (chart : PositiveTimeChart) (x h : Rat) (n : Nat)
    (hx : inDomainInterval chart.lower chart.upper x)
    (hxh : inDomainInterval chart.lower chart.upper (x + h))
    (hh : h ≠ 0) :
    qabs (1 / h) *
        (((rootAt chart (x + h) hxh).compute
            (widthEvalPrecision chart x h n)).width +
          ((rootAt chart x hx).compute
            (widthEvalPrecision chart x h n)).width) <=
      (precisionAtStage n).val := by
  let tolerance := quotientWidthTolerance h hh n
  let stage := widthEvalPrecision chart x h n
  have hxStage : rootWidthStage x tolerance <= stage := by
    dsimp [stage]
    unfold widthEvalPrecision
    rw [dif_neg hh]
    exact Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _)
  have hxhStage : rootWidthStage (x + h) tolerance <= stage := by
    dsimp [stage]
    unfold widthEvalPrecision
    rw [dif_neg hh]
    exact Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _)
  have hxWidth := rootAt_width_le_of_rootWidthStage_le
    chart x hx tolerance hxStage
  have hxhWidth := rootAt_width_le_of_rootWidthStage_le
    chart (x + h) hxh tolerance hxhStage
  have hsum := rat_add_le_add hxhWidth hxWidth
  have hcancel : qabs (1 / h) * qabs h = 1 := by
    have hmul : (1 / h) * h = 1 := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
    have habs := qabs_mul (1 / h) h
    rw [hmul] at habs
    have hone : qabs (1 : Rat) = 1 := by decide +kernel
    rw [hone] at habs
    exact habs.symm
  calc
    qabs (1 / h) *
        (((rootAt chart (x + h) hxh).compute stage).width +
          ((rootAt chart x hx).compute stage).width) <=
        qabs (1 / h) * (tolerance.val + tolerance.val) :=
      Rat.mul_le_mul_of_nonneg_left hsum (qabs_nonneg _)
    _ = (precisionAtStage n).val := by
      dsimp [tolerance, quotientWidthTolerance]
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem widthEvalPrecision_derivative_budget
    (chart : PositiveTimeChart) (x h : Rat) (n : Nat)
    (hx : inDomainInterval chart.lower chart.upper x) :
    ((derivativeAt chart x hx).compute
      (widthEvalPrecision chart x h n)).width <=
        (precisionAtStage n).val := by
  let tolerance := derivativeWidthTolerance chart n
  let stage := widthEvalPrecision chart x h n
  have hderivativeStage : rootWidthStage x tolerance <= stage := by
    dsimp [stage]
    unfold widthEvalPrecision
    by_cases hh : h = 0
    · rw [dif_pos hh]
      exact Nat.le_max_right _ _
    · rw [dif_neg hh]
      exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hrootWidth := rootAt_width_le_of_rootWidthStage_le
    chart x hx tolerance hderivativeStage
  have hrecipWidth := RealRaw.positiveReciprocal_compute_width_le
    (rootAt chart x hx) (rootLower chart)
    (rootAt_valid chart x hx) (rootLower_pos chart)
    (rootLower_le_rootAt_hi chart x hx) stage
  rw [derivativeAt,
    RealRaw.scaleRat_width_of_nonneg (by decide +kernel : (0 : Rat) <= 1 / 2)]
  calc
    (1 / 2) *
        ((RealRaw.positiveReciprocal (rootAt chart x hx)
          (rootLower chart)).compute stage).width <=
      (1 / 2) *
        (((rootAt chart x hx).compute stage).width /
          (rootLower chart * rootLower chart)) :=
      Rat.mul_le_mul_of_nonneg_left hrecipWidth (by decide +kernel)
    _ <= (1 / 2) *
        (tolerance.val / (rootLower chart * rootLower chart)) := by
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_left
        (Rat.mul_le_mul_of_nonneg_right hrootWidth
          (Rat.le_of_lt ((Rat.inv_pos).2
            (Rat.mul_pos (rootLower_pos chart) (rootLower_pos chart)))))
        (by decide +kernel)
    _ = (precisionAtStage n).val := by
      dsimp [tolerance, derivativeWidthTolerance]
      rw [Rat.div_def, Rat.div_def]
      have hLne : rootLower chart * rootLower chart ≠ 0 :=
        Rat.ne_of_gt (Rat.mul_pos (rootLower_pos chart) (rootLower_pos chart))
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-! ## Curvature and finite square-residual schedule -/

def secantOuterCoefficient (chart : PositiveTimeChart) : Rat :=
  1 / (2 * rootLower chart)

def secantCurvatureCoefficient (chart : PositiveTimeChart) : Rat :=
  secantOuterCoefficient chart * (chart.margin⁻¹ + 2) *
    (chart.margin⁻¹ + 2)

theorem secantOuterCoefficient_pos (chart : PositiveTimeChart) :
    0 < secantOuterCoefficient chart := by
  unfold secantOuterCoefficient
  rw [Rat.div_def]
  exact Rat.mul_pos (by decide +kernel)
    ((Rat.inv_pos).2 (Rat.mul_pos (by decide +kernel) (rootLower_pos chart)))

theorem secantCurvatureCoefficient_nonneg (chart : PositiveTimeChart) :
    0 <= secantCurvatureCoefficient chart := by
  unfold secantCurvatureCoefficient
  have hmInv0 : 0 <= chart.margin⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 chart.margin_pos)
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.le_of_lt (secantOuterCoefficient_pos chart))
      (by grind)) (by grind)

def secantStepPrecision (chart : PositiveTimeChart) (n : Nat) : Nat :=
  RationalMajorant.dyadicStepPrecision
    (2 * secantCurvatureCoefficient chart) (precisionAtStage n)

def secantResidualTolerance (chart : PositiveTimeChart)
    (h : Rat) (hh : h ≠ 0) (n : Nat) : QPos where
  val := (precisionAtStage n).val * qabs h /
    (8 * secantOuterCoefficient chart * (chart.bound + 1 : Nat))
  property := by
    rw [Rat.div_def]
    exact Rat.mul_pos
      (Rat.mul_pos (precisionAtStage n).property (qabs_pos_of_ne hh))
      ((Rat.inv_pos).2
        (Rat.mul_pos
          (Rat.mul_pos (by decide +kernel) (secantOuterCoefficient_pos chart))
          ((Rat.natCast_pos).2 (Nat.succ_pos chart.bound))))

/-- The secant-stage root width pays both the `O(width/|h|)` square residual
and the `width <= |h|` hypothesis used to reduce the curvature term. -/
def secantRootTolerance (chart : PositiveTimeChart)
    (h : Rat) (hh : h ≠ 0) (n : Nat) : QPos where
  val := minRat (qabs h) (secantResidualTolerance chart h hh n).val
  property := by
    unfold minRat
    by_cases hle : qabs h <= (secantResidualTolerance chart h hh n).val
    · simp [hle, qabs_pos_of_ne hh]
    · simp [hle, (secantResidualTolerance chart h hh n).property]

theorem secantRootTolerance_le_step
    (chart : PositiveTimeChart) (h : Rat) (hh : h ≠ 0) (n : Nat) :
    (secantRootTolerance chart h hh n).val <= qabs h := by
  unfold secantRootTolerance minRat
  by_cases hle : qabs h <= (secantResidualTolerance chart h hh n).val
  · simp [hle]
  · simp [hle]
    grind

theorem secantRootTolerance_le_residual
    (chart : PositiveTimeChart) (h : Rat) (hh : h ≠ 0) (n : Nat) :
    (secantRootTolerance chart h hh n).val <=
      (secantResidualTolerance chart h hh n).val := by
  unfold secantRootTolerance minRat
  by_cases hle : qabs h <= (secantResidualTolerance chart h hh n).val
  · simp [hle]
  · simp [hle]

/-- Final evaluator stage for the positive square-root derivative.  The
zero-step branch is arbitrary because derivative certificates assume a
nonzero rational step. -/
def evalPrecision (chart : PositiveTimeChart)
    (x h : Rat) (n : Nat) : Nat :=
  if hh : h = 0 then widthEvalPrecision chart x h n else
    let tolerance := secantRootTolerance chart h hh n
    Nat.max (widthEvalPrecision chart x h n)
      (Nat.max (rootWidthStage x tolerance)
        (rootWidthStage (x + h) tolerance))

theorem widthEvalPrecision_le_evalPrecision
    (chart : PositiveTimeChart) (x h : Rat) (n : Nat) :
    widthEvalPrecision chart x h n <= evalPrecision chart x h n := by
  unfold evalPrecision
  by_cases hh : h = 0
  · rw [dif_pos hh]
    exact Nat.le_refl _
  · rw [dif_neg hh]
    exact Nat.le_max_left _ _

theorem evalPrecision_root_width_le_secantTolerance
    (chart : PositiveTimeChart) (x h : Rat) (n : Nat)
    (hx : inDomainInterval chart.lower chart.upper x)
    (hxh : inDomainInterval chart.lower chart.upper (x + h))
    (hh : h ≠ 0) :
    ((rootAt chart x hx).compute (evalPrecision chart x h n)).width <=
        (secantRootTolerance chart h hh n).val /\
      ((rootAt chart (x + h) hxh).compute
        (evalPrecision chart x h n)).width <=
          (secantRootTolerance chart h hh n).val := by
  let tolerance := secantRootTolerance chart h hh n
  have hxStage : rootWidthStage x tolerance <= evalPrecision chart x h n := by
    unfold evalPrecision
    rw [dif_neg hh]
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hxhStage : rootWidthStage (x + h) tolerance <=
      evalPrecision chart x h n := by
    unfold evalPrecision
    rw [dif_neg hh]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact ⟨
    rootAt_width_le_of_rootWidthStage_le chart x hx tolerance hxStage,
    rootAt_width_le_of_rootWidthStage_le chart (x + h) hxh tolerance hxhStage⟩

/-- The arithmetic budget consumed by the width-aware square-root secant
estimate.  This theorem contains no represented values: all inputs are
finite rational interval widths and endpoint sums. -/
theorem secantBudgetExpression_le
    (chart : PositiveTimeChart) (h : Rat) (hh : h ≠ 0) (n : Nat)
    {wI wJ sumI sumJ : Rat}
    (hwI0 : 0 <= wI) (hwJ0 : 0 <= wJ)
    (hsumI0 : 0 <= sumI) (hsumJ0 : 0 <= sumJ)
    (hwI : wI <= (secantRootTolerance chart h hh n).val)
    (hwJ : wJ <= (secantRootTolerance chart h hh n).val)
    (hsumI : sumI <= 2 * (chart.bound + 1 : Nat))
    (hsumJ : sumJ <= 2 * (chart.bound + 1 : Nat))
    (hsmall : qabs h <=
      1 / ((secantStepPrecision chart n : Nat) : Rat)) :
    secantOuterCoefficient chart * qabs (1 / h) *
        ((chart.margin⁻¹ * qabs h + wI + wJ) *
            (chart.margin⁻¹ * qabs h + wI + wJ) +
          (wJ * sumJ + wI * sumI)) <=
      (precisionAtStage n).val := by
  let delta := (secantRootTolerance chart h hh n).val
  let H := qabs h
  let A := secantOuterCoefficient chart
  let B : Rat := (chart.bound + 1 : Nat)
  let R := chart.margin⁻¹ + 2
  have hH0 : 0 <= H := qabs_nonneg _
  have hHpos : 0 < H := qabs_pos_of_ne hh
  have hA0 : 0 <= A := Rat.le_of_lt (secantOuterCoefficient_pos chart)
  have hBpos : 0 < B := by
    dsimp [B]
    exact (Rat.natCast_pos).2 (Nat.succ_pos chart.bound)
  have hB0 : 0 <= B := Rat.le_of_lt hBpos
  have hmInv0 : 0 <= chart.margin⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 chart.margin_pos)
  have hR0 : 0 <= R := by dsimp [R]; grind
  have hdeltaH : delta <= H := by
    exact secantRootTolerance_le_step chart h hh n
  have hdeltaResidual : delta <=
      (secantResidualTolerance chart h hh n).val :=
    secantRootTolerance_le_residual chart h hh n
  have hdistance :
      chart.margin⁻¹ * H + wI + wJ <= R * H := by
    calc
      chart.margin⁻¹ * H + wI + wJ <=
          chart.margin⁻¹ * H + delta + delta := by
        exact rat_add_le_add (rat_add_le_add (by exact Rat.le_refl) hwI) hwJ
      _ <= chart.margin⁻¹ * H + H + H := by
        exact rat_add_le_add (rat_add_le_add (by exact Rat.le_refl) hdeltaH) hdeltaH
      _ = R * H := by
        dsimp [R]
        grind [Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  have hdistance0 : 0 <= chart.margin⁻¹ * H + wI + wJ :=
    Rat.add_nonneg (Rat.add_nonneg (Rat.mul_nonneg hmInv0 hH0) hwI0) hwJ0
  have hsquare :
      (chart.margin⁻¹ * H + wI + wJ) *
          (chart.margin⁻¹ * H + wI + wJ) <=
        (R * R) * (H * H) := by
    have hmul := rat_mul_le_mul_of_nonneg
      hdistance0 hdistance hdistance0 hdistance
    exact Rat.le_trans hmul (by
      grind [Rat.mul_assoc, Rat.mul_comm])
  have hresI : wI * sumI <= delta * (2 * B) :=
    rat_mul_le_mul_of_nonneg hwI0 hwI hsumI0 (by simpa [B] using hsumI)
  have hresJ : wJ * sumJ <= delta * (2 * B) :=
    rat_mul_le_mul_of_nonneg hwJ0 hwJ hsumJ0 (by simpa [B] using hsumJ)
  have hresidual : wJ * sumJ + wI * sumI <= 4 * B * delta := by
    exact Rat.le_trans (rat_add_le_add hresJ hresI) (by
      grind [Rat.mul_assoc, Rat.mul_comm])
  have hinside :
      (chart.margin⁻¹ * H + wI + wJ) *
            (chart.margin⁻¹ * H + wI + wJ) +
          (wJ * sumJ + wI * sumI) <=
        (R * R) * (H * H) + 4 * B * delta :=
    rat_add_le_add hsquare hresidual
  have houter0 : 0 <= A * qabs (1 / h) :=
    Rat.mul_nonneg hA0 (qabs_nonneg _)
  have hcancel : qabs (1 / h) * H = 1 := by
    have hmul : (1 / h) * h = 1 := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
    have habs := qabs_mul (1 / h) h
    rw [hmul] at habs
    have hone : qabs (1 : Rat) = 1 := by decide +kernel
    rw [hone] at habs
    exact habs.symm
  have hcurvatureStep := RationalMajorant.dyadicStepPrecision_spec
    (bound := 2 * secantCurvatureCoefficient chart)
    (Rat.mul_nonneg (by decide +kernel)
      (secantCurvatureCoefficient_nonneg chart))
    (precisionAtStage n) hsmall
  have hcurvature : secantCurvatureCoefficient chart * H <=
      (precisionAtStage n).val / 2 := by
    apply Rat.le_of_mul_le_mul_left (c := (2 : Rat))
    · calc
        2 * (secantCurvatureCoefficient chart * H) =
            H * (2 * secantCurvatureCoefficient chart) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= (precisionAtStage n).val := hcurvatureStep
        _ = 2 * ((precisionAtStage n).val / 2) := by grind
    · decide +kernel
  have hresidualScaled :
      A * qabs (1 / h) * (4 * B * delta) <=
        (precisionAtStage n).val / 2 := by
    have hscale0 : 0 <= A * qabs (1 / h) * (4 * B) :=
      Rat.mul_nonneg
        (Rat.mul_nonneg hA0 (qabs_nonneg _))
        (Rat.mul_nonneg (by decide +kernel) hB0)
    have hscaled := Rat.mul_le_mul_of_nonneg_left hdeltaResidual hscale0
    calc
      A * qabs (1 / h) * (4 * B * delta) =
          (A * qabs (1 / h) * (4 * B)) * delta := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= (A * qabs (1 / h) * (4 * B)) *
          (secantResidualTolerance chart h hh n).val := hscaled
      _ = (precisionAtStage n).val / 2 := by
        dsimp [secantResidualTolerance, A, B]
        rw [Rat.div_def, Rat.div_def]
        have hAne : secantOuterCoefficient chart ≠ 0 :=
          Rat.ne_of_gt (secantOuterCoefficient_pos chart)
        have hBne : ((chart.bound + 1 : Nat) : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos chart.bound))
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  calc
    A * qabs (1 / h) *
        ((chart.margin⁻¹ * H + wI + wJ) *
            (chart.margin⁻¹ * H + wI + wJ) +
          (wJ * sumJ + wI * sumI)) <=
      A * qabs (1 / h) *
        ((R * R) * (H * H) + 4 * B * delta) :=
      Rat.mul_le_mul_of_nonneg_left hinside houter0
    _ = secantCurvatureCoefficient chart * H +
        A * qabs (1 / h) * (4 * B * delta) := by
      dsimp [secantCurvatureCoefficient, R, A]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
    _ <= (precisionAtStage n).val / 2 +
        (precisionAtStage n).val / 2 :=
      rat_add_le_add hcurvature hresidualScaled
    _ = (precisionAtStage n).val := by grind

/-- The midpoint witnesses selected by `evalPrecision` satisfy the complete
finite square-root secant budget. -/
theorem evalPrecision_secant_error
    (chart : PositiveTimeChart) (x h : Rat) (n : Nat)
    (hx : inDomainInterval chart.lower chart.upper x)
    (hxh : inDomainInterval chart.lower chart.upper (x + h))
    (hh : h ≠ 0)
    (hsmall : qabs h <=
      1 / ((secantStepPrecision chart n : Nat) : Rat)) :
    let stage := evalPrecision chart x h n
    let I := (rootAt chart x hx).compute stage
    let J := (rootAt chart (x + h) hxh).compute stage
    qabs (((J.midpoint - I.midpoint) / h) -
      derivativeWitness chart x hx stage) <=
        (precisionAtStage n).val := by
  dsimp only
  let stage := evalPrecision chart x h n
  let I := (rootAt chart x hx).compute stage
  let J := (rootAt chart (x + h) hxh).compute stage
  have hspecI : SqrtIntervalSpec x I :=
    sqrtRaw_stage_spec x (sqrtDomainAt chart x hx) stage
  have hspecJ : SqrtIntervalSpec (x + h) J :=
    sqrtRaw_stage_spec (x + h) (sqrtDomainAt chart (x + h) hxh) stage
  have hwidths := evalPrecision_root_width_le_secantTolerance
    chart x h n hx hxh hh
  have hguardStage : rootWidthStage x (rootGuardTolerance chart) <= stage := by
    have hbase : rootWidthStage x (rootGuardTolerance chart) <=
        widthEvalPrecision chart x h n := by
      unfold widthEvalPrecision
      rw [dif_neg hh]
      exact Nat.le_max_left _ _
    exact Nat.le_trans hbase
      (widthEvalPrecision_le_evalPrecision chart x h n)
  have hguardWidth : I.width <= rootLower chart := by
    exact rootAt_width_le_of_rootWidthStage_le chart x hx
      (rootGuardTolerance chart) hguardStage
  have hroot : rootLower chart <= I.midpoint :=
    rootLower_le_rootAt_midpoint_of_width_le chart x hx stage hguardWidth
  have hstepNe : (x + h) - x ≠ 0 := by grind [Rat.sub_eq_add_neg]
  have hfinite :=
    PositiveSquareRootDifferential.sqrtCertificate_approximate_secant_error_le
      (rootLower_pos chart) chart.margin_pos hspecI hspecJ
      (margin_sq_le_time chart x hx)
      (margin_sq_le_time chart (x + h) hxh)
      hroot hstepNe
  have hstepEq : (x + h) - x = h := by grind [Rat.sub_eq_add_neg]
  have hderivativeEq :
      PositiveSquareRootDifferential.derivative I.midpoint =
        derivativeWitness chart x hx stage := by
    unfold PositiveSquareRootDifferential.derivative derivativeWitness
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.one_mul,
      Rat.inv_mul_rev]
    grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hstepEq, hderivativeEq] at hfinite
  have hsumI0 : 0 <= I.hi + I.lo := by
    exact Rat.add_nonneg (Rat.le_trans hspecI.1 hspecI.2.1) hspecI.1
  have hsumJ0 : 0 <= J.hi + J.lo := by
    exact Rat.add_nonneg (Rat.le_trans hspecJ.1 hspecJ.2.1) hspecJ.1
  have hbudget := secantBudgetExpression_le chart h hh n
    (by unfold QInterval.width; grind [hspecI.2.1, Rat.sub_eq_add_neg])
    (by unfold QInterval.width; grind [hspecJ.2.1, Rat.sub_eq_add_neg])
    hsumI0 hsumJ0 hwidths.1 hwidths.2
    (rootAt_endpoint_sum_le chart x hx stage)
    (rootAt_endpoint_sum_le chart (x + h) hxh stage)
    hsmall
  exact Rat.le_trans hfinite
    (by simpa [stage, I, J, secantOuterCoefficient,
      Rat.mul_assoc, Rat.mul_comm] using hbudget)

theorem rawWidth_antitone {r : RealRaw} (hr : r.Valid)
    {n m : Nat} (hnm : n <= m) :
    (r.compute m).width <= (r.compute n).width := by
  have hnested := hr.2.1 n m hnm
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem evalPrecision_guard_width
    (chart : PositiveTimeChart) (x h : Rat) (n : Nat)
    (hx : inDomainInterval chart.lower chart.upper x) :
    ((rootAt chart x hx).compute (evalPrecision chart x h n)).width <=
      rootLower chart := by
  exact Rat.le_trans
    (rawWidth_antitone (rootAt_valid chart x hx)
      (widthEvalPrecision_le_evalPrecision chart x h n))
    (widthEvalPrecision_guard_width chart x h n hx)

theorem evalPrecision_quotient_budget
    (chart : PositiveTimeChart) (x h : Rat) (n : Nat)
    (hx : inDomainInterval chart.lower chart.upper x)
    (hxh : inDomainInterval chart.lower chart.upper (x + h))
    (hh : h ≠ 0) :
    qabs (1 / h) *
        (((rootAt chart (x + h) hxh).compute
            (evalPrecision chart x h n)).width +
          ((rootAt chart x hx).compute
            (evalPrecision chart x h n)).width) <=
      (precisionAtStage n).val := by
  have hstage := widthEvalPrecision_le_evalPrecision chart x h n
  have hstep := rawWidth_antitone (rootAt_valid chart (x + h) hxh) hstage
  have hbase := rawWidth_antitone (rootAt_valid chart x hx) hstage
  have hsum := rat_add_le_add hstep hbase
  exact Rat.le_trans
    (Rat.mul_le_mul_of_nonneg_left hsum (qabs_nonneg _))
    (widthEvalPrecision_quotient_budget chart x h n hx hxh hh)

theorem evalPrecision_derivative_budget
    (chart : PositiveTimeChart) (x h : Rat) (n : Nat)
    (hx : inDomainInterval chart.lower chart.upper x) :
    ((derivativeAt chart x hx).compute
      (evalPrecision chart x h n)).width <=
        (precisionAtStage n).val := by
  exact Rat.le_trans
    (rawWidth_antitone (derivativeAt_valid chart x hx)
      (widthEvalPrecision_le_evalPrecision chart x h n))
    (widthEvalPrecision_derivative_budget chart x h n hx)

theorem evalPrecision_differenceQuotient_width
    (chart : PositiveTimeChart) (x h : Rat) (n : Nat)
    (hx : inDomainInterval chart.lower chart.upper x)
    (hxh : inDomainInterval chart.lower chart.upper (x + h))
    (hh : h ≠ 0) :
    (QInterval.differenceQuotient
      ((rootAt chart (x + h) hxh).compute (evalPrecision chart x h n))
      ((rootAt chart x hx).compute (evalPrecision chart x h n)) h).width <=
        (precisionAtStage n).val := by
  rw [QInterval.differenceQuotient_width]
  exact evalPrecision_quotient_budget chart x h n hx hxh hh

def rootOn (chart : PositiveTimeChart) : FunctionOnInterval where
  raw :=
    { definedAt := fun t => inDomainInterval chart.lower chart.upper t
      compute := fun t ht n => (rootAt chart t ht).compute n }
  lower := chart.lower
  upper := chart.upper
  defined_on := fun _ ht => ht
  valid_on := fun t ht => rootAt_valid chart t ht

def derivativeOn (chart : PositiveTimeChart) : FunctionOnInterval where
  raw :=
    { definedAt := fun t => inDomainInterval chart.lower chart.upper t
      compute := fun t ht n => (derivativeAt chart t ht).compute n }
  lower := chart.lower
  upper := chart.upper
  defined_on := fun _ ht => ht
  valid_on := fun t ht => derivativeAt_valid chart t ht

@[simp] theorem rootOn_compute (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (n : Nat) :
    (rootOn chart).compute t ht n = (rootAt chart t ht).compute n := rfl

@[simp] theorem derivativeOn_compute (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (n : Nat) :
    (derivativeOn chart).compute t ht n =
      (derivativeAt chart t ht).compute n := rfl

/-! ## Complete finite derivative certificate -/

/-- Total rational witness function; outside the square-root domain its
value is irrelevant to the derivative certificate. -/
def totalRootMidpoint (t : Rat) (stage : Nat) : Rat :=
  if hneg : t < 0 then 0 else ((sqrtRaw t hneg).compute stage).midpoint

theorem totalRootMidpoint_eq_rootAt
    (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (stage : Nat) :
    totalRootMidpoint t stage = ((rootAt chart t ht).compute stage).midpoint := by
  unfold totalRootMidpoint
  rw [dif_neg (sqrtDomainAt chart t ht)]
  rfl

def totalDerivativeWitness (t : Rat) (stage : Nat) : Rat :=
  (1 / 2) * (1 / totalRootMidpoint t stage)

theorem totalDerivativeWitness_eq_derivativeWitness
    (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) (stage : Nat) :
    totalDerivativeWitness t stage = derivativeWitness chart t ht stage := by
  unfold totalDerivativeWitness derivativeWitness
  rw [totalRootMidpoint_eq_rootAt chart t ht stage]

/-- The explicit rational schedules and midpoint witnesses form a complete
finite-model derivative certificate for positive square root. -/
def finiteModel (chart : PositiveTimeChart) :
    FiniteModelDerivativeOnInterval (rootOn chart) (derivativeOn chart) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := secantStepPrecision chart
  evalPrecision := evalPrecision chart
  baseValue := fun x h n =>
    totalRootMidpoint x (evalPrecision chart x h n)
  stepValue := fun x h n =>
    totalRootMidpoint (x + h) (evalPrecision chart x h n)
  derivativeValue := fun x h n =>
    totalDerivativeWitness x (evalPrecision chart x h n)
  base_mem := by
    intro x h n hx _hxh
    change
      ((rootAt chart x hx).compute (evalPrecision chart x h n)).lo <=
          totalRootMidpoint x (evalPrecision chart x h n) /\
        totalRootMidpoint x (evalPrecision chart x h n) <=
          ((rootAt chart x hx).compute (evalPrecision chart x h n)).hi
    rw [totalRootMidpoint_eq_rootAt chart x hx]
    exact QInterval.midpoint_mem
      (RealRaw.interval_order_of_valid (rootAt chart x hx)
        (rootAt_valid chart x hx) (evalPrecision chart x h n))
  step_mem := by
    intro x h n _hx hxh
    change
      ((rootAt chart (x + h) hxh).compute (evalPrecision chart x h n)).lo <=
          totalRootMidpoint (x + h) (evalPrecision chart x h n) /\
        totalRootMidpoint (x + h) (evalPrecision chart x h n) <=
          ((rootAt chart (x + h) hxh).compute
            (evalPrecision chart x h n)).hi
    rw [totalRootMidpoint_eq_rootAt chart (x + h) hxh]
    exact QInterval.midpoint_mem
      (RealRaw.interval_order_of_valid (rootAt chart (x + h) hxh)
        (rootAt_valid chart (x + h) hxh) (evalPrecision chart x h n))
  derivative_mem := by
    intro x h n hdx
    change
      ((derivativeAt chart x hdx).compute (evalPrecision chart x h n)).lo <=
          totalDerivativeWitness x (evalPrecision chart x h n) /\
        totalDerivativeWitness x (evalPrecision chart x h n) <=
          ((derivativeAt chart x hdx).compute
            (evalPrecision chart x h n)).hi
    rw [totalDerivativeWitness_eq_derivativeWitness chart x hdx]
    exact derivativeWitness_mem chart x hdx (evalPrecision chart x h n)
      (evalPrecision_guard_width chart x h n hdx)
  secant_error := by
    intro x h n hx hxh hh hsmall
    rw [totalRootMidpoint_eq_rootAt chart x hx,
      totalRootMidpoint_eq_rootAt chart (x + h) hxh,
      totalDerivativeWitness_eq_derivativeWitness chart x hx]
    exact evalPrecision_secant_error chart x h n hx hxh hh hsmall
  quotient_width := by
    intro x h n hx hxh hh _hsmall
    exact evalPrecision_differenceQuotient_width chart x h n hx hxh hh
  derivative_width := by
    intro x h n hdx
    exact evalPrecision_derivative_budget chart x h n hdx

/-- Positive square root is differentiable on every rational chart uniformly
separated from zero, with represented derivative `1/(2*sqrt t)`. -/
def hasDerivativeOnInterval (chart : PositiveTimeChart) :
    HasDerivativeOnInterval (rootOn chart) (derivativeOn chart) :=
  (finiteModel chart).toHasDerivativeOnInterval

/-! ## Agreement with the represented heat-kernel root -/

theorem representedRoot_realPart_spec (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) :
    SqrtRealRawSpec t
      ((PositiveInput.awayRootRaw (chart.inputAt t ht)).realPart) := by
  let A := chart.inputAt t ht
  constructor
  · exact ComplexRaw.realPart_valid (PositiveInput.awayRootRaw_valid A)
  · intro n
    let stage := n + PositiveInput.guardShift chart.bound chart.margin
    let I := PositiveInput.approximation A stage
    have hspec : SqrtIntervalSpec t I := by
      have hs := PositiveInput.approximation_spec A stage
      have hcenter : (A.raw.compute stage).midpoint = t := by
        dsimp [A]
        change (t + t) / 2 = t
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel 2 (by decide +kernel : (2 : Rat) ≠ 0)]
      simpa [hcenter] using hs
    have hcontains :=
      PositiveInput.awayRootRaw_contains_shifted_approximation A n
    have hguard := PositiveInput.awayRootRaw_nested_guard A n
    have hhalf0 : 0 <= chart.margin / 2 :=
      Rat.le_of_lt (rootLower_pos chart)
    have hawayLo0 :
        0 <= ((PositiveInput.awayRootRaw A).compute n).lo.re := by
      unfold QBox.ofRealInterval QBox.NestedIn at hguard
      simp only [QComplex.le_def] at hguard
      exact Rat.le_trans hhalf0 hguard.1.1
    have hlo :
        sq ((PositiveInput.awayRootRaw A).compute n).lo.re <= t := by
      have hle : ((PositiveInput.awayRootRaw A).compute n).lo.re <= I.lo := by
        unfold PositiveInput.candidate QBox.ofRealInterval QBox.NestedIn at hcontains
        simp only [QComplex.le_def] at hcontains
        exact hcontains.1.1
      exact Rat.le_trans
        (sq_le_sq_of_nonneg_le hawayLo0 hle) hspec.2.2.1
    have hhi0 : 0 <= I.hi := Rat.le_trans hspec.1 hspec.2.1
    have hhi :
        t <= sq ((PositiveInput.awayRootRaw A).compute n).hi.re := by
      have hle : I.hi <= ((PositiveInput.awayRootRaw A).compute n).hi.re := by
        unfold PositiveInput.candidate QBox.ofRealInterval QBox.NestedIn at hcontains
        simp only [QComplex.le_def] at hcontains
        exact hcontains.2.1
      exact Rat.le_trans hspec.2.2.2
        (sq_le_sq_of_nonneg_le hhi0 hle)
    change 0 <= ((PositiveInput.awayRootRaw A).compute n).lo.re /\
      ((PositiveInput.awayRootRaw A).compute n).lo.re <=
        ((PositiveInput.awayRootRaw A).compute n).hi.re /\
      sq ((PositiveInput.awayRootRaw A).compute n).lo.re <= t /\
      t <= sq ((PositiveInput.awayRootRaw A).compute n).hi.re
    exact ⟨hawayLo0,
      (ComplexRaw.valid_ordered (PositiveInput.awayRootRaw_valid A) n).1,
      hlo, hhi⟩

theorem rootAt_equiv_representedRoot (chart : PositiveTimeChart) (t : Rat)
    (ht : inDomainInterval chart.lower chart.upper t) :
    (rootAt chart t ht).Equiv
      ((PositiveInput.awayRootRaw (chart.inputAt t ht)).realPart) :=
  sqrt_spec_equiv_of_spec
    (sqrtRaw_spec t (sqrtDomainAt chart t ht))
    (representedRoot_realPart_spec chart t ht)

end PositiveSquareRootDerivative
end ComputableAnalysis
