import ComputableAnalysis.Exp
import ComputableAnalysis.FTC

/-!
# Proof targets for the exponential algorithms

`Exp.lean` is the public computation file.  This companion file keeps the
proof-facing names and the finite interval facts that are immediate from the
display wrapper around the two algorithms.

The remaining analytic work is deliberately isolated as finite nesting and
agreement statements: once those are supplied, the `RealRaw.Valid` and
`RealRaw.Equiv` theorems below close without touching the readable algorithms.
-/

namespace ComputableAnalysis

namespace ExpProofs

def PowerSeriesValid (x : Rat) : Prop :=
  (expPowerSeries x).Valid

def EulerValid (x : Rat) : Prop :=
  (expEuler x).Valid

def EPowerSeriesValid : Prop :=
  ePowerSeries.Valid

def EEulerValid : Prop :=
  eEuler.Valid

def ECompoundInterestValid : Prop :=
  eCompoundInterest.Valid

def EPowerSeriesEqEuler : Prop :=
  ePowerSeries.Equiv eEuler

def EPowerSeriesEqCompoundInterest : Prop :=
  ePowerSeries.Equiv eCompoundInterest

/-- Three-way agreement target for the definitions of `e`: power series,
compound interest, and an externally supplied inverse-log-integral
representative. -/
def EThreeWayAgreement (eLogIntegral : RealRaw) : Prop :=
  ePowerSeries.Equiv eCompoundInterest /\
  ePowerSeries.Equiv eLogIntegral /\
  eCompoundInterest.Equiv eLogIntegral

/-- Remaining estimates needed to close the three definitions of `e` for a
chosen inverse-log-integral representative. -/
structure EThreeWayRemainders (eLogIntegral : RealRaw) where
  powerSeries_eq_compoundInterest : EPowerSeriesEqCompoundInterest
  powerSeries_eq_logIntegral : ePowerSeries.Equiv eLogIntegral
  compoundInterest_eq_logIntegral : eCompoundInterest.Equiv eLogIntegral

theorem eThreeWayAgreement_of_remainders {eLogIntegral : RealRaw}
    (remainders : EThreeWayRemainders eLogIntegral) :
    EThreeWayAgreement eLogIntegral :=
  ⟨remainders.powerSeries_eq_compoundInterest,
   remainders.powerSeries_eq_logIntegral,
   remainders.compoundInterest_eq_logIntegral⟩

def PowerSeriesRatioBound (x : Rat) : Prop :=
  forall n, expPowerSeriesTailRatioBound x n < 1

def powerSeriesCenter (x : Rat) (n : Nat) : Rat :=
  (expPowerSeriesPartialAndTailBound x n).1

def powerSeriesTailRadius (x : Rat) (n : Nat) : Rat :=
  (expPowerSeriesPartialAndTailBound x n).2

def eulerCenter (x : Rat) (n : Nat) : Rat := Id.run do
  let m : Nat := (n + 1) * (n + 1)
  let mut value : Rat := 1
  for _ in List.range m do
    value := value * (1 + x / (m : Rat))
  return value

def stageRadius (n : Nat) : Rat :=
  if n = 0 then 1 else 1 / (((2 * n : Nat) : Rat))

def intervalAround (center radius : Rat) : QInterval :=
  { lo := center - radius, hi := center + radius }

def stageWidth (n : Nat) : Rat :=
  if n = 0 then 2 else 1 / (n : Rat)

theorem expPowerSeries_compute_eq (x : Rat) (n : Nat) :
    (expPowerSeries x).compute n =
      intervalAround (powerSeriesCenter x n)
        (powerSeriesTailRadius x n) := by
  rfl

theorem expEuler_compute_eq (x : Rat) (n : Nat) :
    (expEuler x).compute n =
      intervalAround (eulerCenter x n) (stageRadius n) := by
  rfl

theorem eCompoundInterest_compute_eq (n : Nat) :
    eCompoundInterest.compute n = eCompoundInterestStage n := by
  rfl

theorem intervalAround_width (center radius : Rat) :
    (intervalAround center radius).width = radius + radius := by
  unfold intervalAround QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem intervalAround_ordered
    (center radius : Rat) (hradius : 0 <= radius) :
    (intervalAround center radius).lo <=
      (intervalAround center radius).hi := by
  unfold intervalAround
  grind [Rat.sub_eq_add_neg]

theorem powerSeriesTailRadius_nonneg_of_ratioBound
    (x : Rat) (hratio : PowerSeriesRatioBound x) (n : Nat) :
    0 <= powerSeriesTailRadius x n := by
  unfold powerSeriesTailRadius expPowerSeriesPartialAndTailBound
  simp
  rw [Rat.div_def]
  have hdenpos :
      0 <
        1 - expPowerSeriesTailRatioBound x n := by
    have h := hratio n
    grind [Rat.sub_eq_add_neg]
  exact Rat.mul_nonneg
    (qabs_nonneg _)
    (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))

theorem stageRadius_nonneg (n : Nat) : 0 <= stageRadius n := by
  by_cases hn : n = 0
  case pos =>
    simp [stageRadius, hn]
    native_decide
  case neg =>
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hdenpos : (0 : Rat) < 2 * (n : Rat) :=
      Rat.mul_pos (by native_decide : (0 : Rat) < 2)
        ((Rat.natCast_pos).2 hnpos)
    have hpos : 0 < 1 / (2 * (n : Rat)) := by
      rw [Rat.div_def, Rat.one_mul]
      exact (Rat.inv_pos).2 hdenpos
    unfold stageRadius
    simp [hn]
    exact Rat.le_of_lt hpos

private theorem two_inv_two_mul_nat (n : Nat) (hn : Not (n = 0)) :
    1 / (2 * (n : Rat)) + 1 / (2 * (n : Rat)) =
      1 / (n : Rat) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have h2pos : (0 : Rat) < 2 * (n : Rat) := by
    exact Rat.mul_pos (by native_decide : (0 : Rat) < 2)
      ((Rat.natCast_pos).2 hnpos)
  have h2n_ne : Not (2 * (n : Rat) = 0) := Rat.ne_of_gt h2pos
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.mul_inv_cancel,
    Rat.inv_mul_cancel]

theorem stageRadius_double (n : Nat) :
    stageRadius n + stageRadius n = stageWidth n := by
  by_cases hn : n = 0
  case pos =>
    simp [stageRadius, stageWidth, hn]
    native_decide
  case neg =>
    simp [stageRadius, stageWidth, hn]
    exact two_inv_two_mul_nat n hn

theorem stageRadius_antitone {n m : Nat} (hnm : n <= m) :
    stageRadius m <= stageRadius n := by
  by_cases hn0 : n = 0
  case pos =>
    subst n
    by_cases hm0 : m = 0
    case pos =>
      simp [stageRadius, hm0]
    case neg =>
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hdenpos : 0 < 2 * m :=
        Nat.mul_pos (by omega : 0 < 2) hmpos
      have honepos : 0 < (1 : Nat) := by omega
      have hle : 1 <= 2 * m := by omega
      have h :=
        FTC.one_div_nat_antitone honepos hdenpos hle
      have hone : (1 / (((1 : Nat) : Rat)) : Rat) = 1 := by
        native_decide
      rw [hone] at h
      simpa [stageRadius, hm0] using h
  case neg =>
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hmpos : 0 < m := Nat.lt_of_lt_of_le hnpos hnm
    have hn2pos : 0 < 2 * n :=
      Nat.mul_pos (by omega : 0 < 2) hnpos
    have hm2pos : 0 < 2 * m :=
      Nat.mul_pos (by omega : 0 < 2) hmpos
    have h2le : 2 * n <= 2 * m := by omega
    have h :=
      FTC.one_div_nat_antitone hn2pos hm2pos h2le
    have hm0 : Not (m = 0) := Nat.ne_of_gt hmpos
    simpa [stageRadius, hn0, hm0] using h

theorem stageRadius_drop_nonneg {n m : Nat} (hnm : n <= m) :
    0 <= stageRadius n - stageRadius m := by
  have h := stageRadius_antitone hnm
  grind [Rat.sub_eq_add_neg]

theorem stageWidth_nonneg (n : Nat) : 0 <= stageWidth n := by
  by_cases hn : n = 0
  case pos =>
    simp [stageWidth, hn]
    native_decide
  case neg =>
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hpos : 0 < 1 / (n : Rat) := one_div_nat_pos hnpos
    simp [stageWidth, hn]
    exact Rat.le_of_lt hpos

theorem stageWidth_shrink : ShrinksToZero stageWidth := by
  intro eps
  let N : Nat := eps.val.den + 1
  exact Exists.intro N (by
    intro n hn
    have hNpos : 0 < N := Nat.succ_pos eps.val.den
    have hNbound : 1 / (N : Rat) <= eps.val := by
      dsimp [N]
      exact FTC.one_div_den_succ_le_of_pos eps.property
    by_cases hn0 : n = 0
    case pos =>
      subst n
      omega
    case neg =>
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hanti : 1 / (n : Rat) <= 1 / (N : Rat) :=
        FTC.one_div_nat_antitone hNpos hnpos hn
      calc
        stageWidth n = 1 / (n : Rat) := by simp [stageWidth, hn0]
        _ <= 1 / (N : Rat) := hanti
        _ <= eps.val := hNbound)

theorem expPowerSeries_width_eq (x : Rat) (n : Nat) :
    ((expPowerSeries x).compute n).width =
      powerSeriesTailRadius x n + powerSeriesTailRadius x n := by
  rw [expPowerSeries_compute_eq, intervalAround_width]

theorem expEuler_width_eq (x : Rat) (n : Nat) :
    ((expEuler x).compute n).width = stageWidth n := by
  rw [expEuler_compute_eq, intervalAround_width, stageRadius_double]

theorem expPowerSeries_ordered
    (x : Rat) (hratio : PowerSeriesRatioBound x) (n : Nat) :
    0 <= ((expPowerSeries x).compute n).width := by
  rw [expPowerSeries_width_eq]
  exact Rat.add_nonneg
    (powerSeriesTailRadius_nonneg_of_ratioBound x hratio n)
    (powerSeriesTailRadius_nonneg_of_ratioBound x hratio n)

theorem expEuler_ordered (x : Rat) (n : Nat) :
    0 <= ((expEuler x).compute n).width := by
  rw [expEuler_width_eq]
  exact stageWidth_nonneg n

def PowerSeriesWidthsShrink (x : Rat) : Prop :=
  RealRaw.WidthsShrinkToZero (expPowerSeries x).compute

theorem expPowerSeries_widths_shrink_of_tailRadius_shrink
    (x : Rat)
    (hshrink :
      ShrinksToZero
        (fun n => powerSeriesTailRadius x n + powerSeriesTailRadius x n)) :
    RealRaw.WidthsShrinkToZero (expPowerSeries x).compute := by
  intro eps
  match hshrink eps with
  | Exists.intro N hN =>
      exact Exists.intro N (by
        intro n hn
        rw [expPowerSeries_width_eq]
        exact hN n hn)

theorem expEuler_widths_shrink (x : Rat) :
    RealRaw.WidthsShrinkToZero (expEuler x).compute := by
  intro eps
  match stageWidth_shrink eps with
  | Exists.intro N hN =>
      exact Exists.intro N (by
        intro n hn
        rw [expEuler_width_eq]
        exact hN n hn)

def PowerSeriesNested (x : Rat) : Prop :=
  forall n m, n <= m ->
    ((expPowerSeries x).compute n).lo <= ((expPowerSeries x).compute m).lo /\
    ((expPowerSeries x).compute m).lo <= ((expPowerSeries x).compute m).hi /\
    ((expPowerSeries x).compute m).hi <= ((expPowerSeries x).compute n).hi

def EulerNested (x : Rat) : Prop :=
  forall n m, n <= m ->
    ((expEuler x).compute n).lo <= ((expEuler x).compute m).lo /\
    ((expEuler x).compute m).lo <= ((expEuler x).compute m).hi /\
    ((expEuler x).compute m).hi <= ((expEuler x).compute n).hi

def CenterMovementBound (center radius : Nat -> Rat) : Prop :=
  forall n m, n <= m ->
    center m - center n <= radius n - radius m /\
    center n - center m <= radius n - radius m

def CenterStepMovementBound (center radius : Nat -> Rat) : Prop :=
  forall n,
    center (n + 1) - center n <= radius n - radius (n + 1) /\
    center n - center (n + 1) <= radius n - radius (n + 1)

theorem centerMovementBound_of_stepMovementBound
    {center radius : Nat -> Rat}
    (hstep : CenterStepMovementBound center radius) :
    CenterMovementBound center radius := by
  intro n m hnm
  induction hnm with
  | refl =>
      constructor <;> grind [Rat.sub_eq_add_neg]
  | step hnm ih =>
      rename_i k
      have hnext := hstep k
      constructor
      · calc
          center (k + 1) - center n =
              (center k - center n) +
                (center (k + 1) - center k) := by
                grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
          _ <= (radius n - radius k) +
                (radius k - radius (k + 1)) := by
                grind
          _ = radius n - radius (k + 1) := by
                grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      · calc
          center n - center (k + 1) =
              (center n - center k) +
                (center k - center (k + 1)) := by
                grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
          _ <= (radius n - radius k) +
                (radius k - radius (k + 1)) := by
                grind
          _ = radius n - radius (k + 1) := by
                grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem centerNested_of_movementBound
    {center radius : Nat -> Rat}
    (hmove : CenterMovementBound center radius) :
    forall n m, n <= m ->
      center n - radius n <= center m - radius m /\
      center m + radius m <= center n + radius n := by
  intro n m hnm
  have h := hmove n m hnm
  constructor
  case left =>
    have hleft := h.2
    grind [Rat.sub_eq_add_neg]
  case right =>
    have hright := h.1
    grind [Rat.sub_eq_add_neg]

def PowerSeriesCenterMovement (x : Rat) : Prop :=
  CenterMovementBound (powerSeriesCenter x) (powerSeriesTailRadius x)

def EulerCenterMovement (x : Rat) : Prop :=
  CenterMovementBound (eulerCenter x) stageRadius

def PowerSeriesCenterStepMovement (x : Rat) : Prop :=
  CenterStepMovementBound (powerSeriesCenter x) (powerSeriesTailRadius x)

def EulerCenterStepMovement (x : Rat) : Prop :=
  CenterStepMovementBound (eulerCenter x) stageRadius

theorem powerSeriesCenterMovement_of_stepMovement
    {x : Rat} (hstep : PowerSeriesCenterStepMovement x) :
    PowerSeriesCenterMovement x :=
  centerMovementBound_of_stepMovementBound hstep

theorem eulerCenterMovement_of_stepMovement
    {x : Rat} (hstep : EulerCenterStepMovement x) :
    EulerCenterMovement x :=
  centerMovementBound_of_stepMovementBound hstep

theorem powerSeriesNested_of_centerMovement
    (x : Rat) (hratio : PowerSeriesRatioBound x)
    (hmove : PowerSeriesCenterMovement x) :
    PowerSeriesNested x := by
  intro n m hnm
  have hnested :=
    centerNested_of_movementBound hmove n m hnm
  constructor
  case left =>
    rw [expPowerSeries_compute_eq, expPowerSeries_compute_eq]
    exact hnested.1
  case right =>
    constructor
    case left =>
      rw [expPowerSeries_compute_eq]
      exact intervalAround_ordered
        (powerSeriesCenter x m) (powerSeriesTailRadius x m)
        (powerSeriesTailRadius_nonneg_of_ratioBound x hratio m)
    case right =>
      rw [expPowerSeries_compute_eq, expPowerSeries_compute_eq]
      exact hnested.2

theorem eulerNested_of_centerMovement
    (x : Rat) (hmove : EulerCenterMovement x) :
    EulerNested x := by
  intro n m hnm
  have hnested :=
    centerNested_of_movementBound hmove n m hnm
  constructor
  case left =>
    rw [expEuler_compute_eq, expEuler_compute_eq]
    exact hnested.1
  case right =>
    constructor
    case left =>
      rw [expEuler_compute_eq]
      exact intervalAround_ordered
        (eulerCenter x m) (stageRadius m)
        (stageRadius_nonneg m)
    case right =>
      rw [expEuler_compute_eq, expEuler_compute_eq]
      exact hnested.2

theorem expPowerSeries_valid_of_nested_and_shrinking
    (x : Rat) (hratio : PowerSeriesRatioBound x)
    (hnested : PowerSeriesNested x)
    (hshrink : PowerSeriesWidthsShrink x) : PowerSeriesValid x := by
  unfold PowerSeriesValid RealRaw.Valid RealRaw.ValidCompute
  constructor
  case left =>
    exact expPowerSeries_ordered x hratio
  case right =>
    constructor
    case left =>
      exact hnested
    case right =>
      exact hshrink

theorem expEuler_valid_of_nested
    (x : Rat) (hnested : EulerNested x) : EulerValid x := by
  unfold EulerValid RealRaw.Valid RealRaw.ValidCompute
  constructor
  case left =>
    exact expEuler_ordered x
  case right =>
    constructor
    case left =>
      exact hnested
    case right =>
      exact expEuler_widths_shrink x

def EPowerSeriesNested : Prop :=
  PowerSeriesNested 1

def EEulerNested : Prop :=
  EulerNested 1

def EPowerSeriesCenterMovement : Prop :=
  PowerSeriesCenterMovement 1

def EEulerCenterMovement : Prop :=
  EulerCenterMovement 1

def EPowerSeriesCenterStepMovement : Prop :=
  PowerSeriesCenterStepMovement 1

def EEulerCenterStepMovement : Prop :=
  EulerCenterStepMovement 1

def EPowerSeriesRatioBound : Prop :=
  PowerSeriesRatioBound 1

def EPowerSeriesWidthsShrink : Prop :=
  PowerSeriesWidthsShrink 1

theorem ePowerSeries_valid_of_nested
    (hratio : EPowerSeriesRatioBound)
    (hnested : EPowerSeriesNested)
    (hshrink : EPowerSeriesWidthsShrink) : EPowerSeriesValid := by
  simpa [EPowerSeriesValid, EPowerSeriesNested, ePowerSeries] using
    expPowerSeries_valid_of_nested_and_shrinking 1 hratio hnested hshrink

theorem eEuler_valid_of_nested
    (hnested : EEulerNested) : EEulerValid := by
  simpa [EEulerValid, EEulerNested, eEuler] using
    expEuler_valid_of_nested 1 hnested

theorem ePowerSeries_valid_of_centerMovement
    (hratio : EPowerSeriesRatioBound)
    (hmove : EPowerSeriesCenterMovement)
    (hshrink : EPowerSeriesWidthsShrink) : EPowerSeriesValid :=
  ePowerSeries_valid_of_nested
    hratio
    (powerSeriesNested_of_centerMovement 1 hratio hmove)
    hshrink

theorem eEuler_valid_of_centerMovement
    (hmove : EEulerCenterMovement) : EEulerValid :=
  eEuler_valid_of_nested
    (eulerNested_of_centerMovement 1 hmove)

theorem ePowerSeries_valid_of_centerStepMovement
    (hratio : EPowerSeriesRatioBound)
    (hstep : EPowerSeriesCenterStepMovement)
    (hshrink : EPowerSeriesWidthsShrink) : EPowerSeriesValid :=
  ePowerSeries_valid_of_centerMovement
    hratio
    (powerSeriesCenterMovement_of_stepMovement hstep)
    hshrink

theorem eEuler_valid_of_centerStepMovement
    (hstep : EEulerCenterStepMovement) : EEulerValid :=
  eEuler_valid_of_centerMovement
    (eulerCenterMovement_of_stepMovement hstep)

def CentersOverlap (x : Rat) : Prop :=
  forall n,
    powerSeriesCenter x n - powerSeriesTailRadius x n <=
      eulerCenter x n + stageRadius n /\
    eulerCenter x n - stageRadius n <=
      powerSeriesCenter x n + powerSeriesTailRadius x n

theorem expPowerSeries_eq_expEuler_of_centersOverlap
    (x : Rat) (hoverlap : CentersOverlap x) :
    (expPowerSeries x).Equiv (expEuler x) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have h := hoverlap n
  apply (RealRaw.compareAt_overlap_iff
    (expPowerSeries x) (expEuler x) n n).2
  rw [expPowerSeries_compute_eq, expEuler_compute_eq]
  exact h

def ECentersOverlap : Prop :=
  CentersOverlap 1

theorem ePowerSeries_eq_eEuler_of_centersOverlap
    (hoverlap : ECentersOverlap) : EPowerSeriesEqEuler := by
  simpa [EPowerSeriesEqEuler, ECentersOverlap, ePowerSeries, eEuler]
    using expPowerSeries_eq_expEuler_of_centersOverlap 1 hoverlap

structure ExpProofRemainders where
  powerSeries_ratio_bound : EPowerSeriesRatioBound
  powerSeries_center_step_movement : EPowerSeriesCenterStepMovement
  powerSeries_widths_shrink : EPowerSeriesWidthsShrink
  euler_center_step_movement : EEulerCenterStepMovement
  centers_overlap : ECentersOverlap

structure ExpProofsComplete where
  powerSeries_valid : EPowerSeriesValid
  euler_valid : EEulerValid
  powerSeries_eq_euler : EPowerSeriesEqEuler

theorem eEuler_eq_ePowerSeries_of_complete
    (proofs : ExpProofsComplete) :
    eEuler.Equiv ePowerSeries :=
  RealRaw.equiv_symm proofs.powerSeries_eq_euler

theorem complete_of_remainders
    (remainders : ExpProofRemainders) : ExpProofsComplete where
  powerSeries_valid :=
    ePowerSeries_valid_of_centerStepMovement
      remainders.powerSeries_ratio_bound
      remainders.powerSeries_center_step_movement
      remainders.powerSeries_widths_shrink
  euler_valid :=
    eEuler_valid_of_centerStepMovement
      remainders.euler_center_step_movement
  powerSeries_eq_euler :=
    ePowerSeries_eq_eEuler_of_centersOverlap
      remainders.centers_overlap

end ExpProofs

end ComputableAnalysis
