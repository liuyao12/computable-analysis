import ComputableAnalysis.Exp
import ComputableAnalysis.FTC
import ComputableAnalysis.ElementaryFunctions

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

def EEulerEqCompoundInterest : Prop :=
  eEuler.Equiv eCompoundInterest

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

theorem eCompoundInterestStage_width_eq (n : Nat) :
    (eCompoundInterestStage n).width =
      (1 + 1 / ((n + 1 : Nat) : Rat)) ^ (n + 1) *
        (1 / ((n + 1 : Nat) : Rat)) := by
  unfold eCompoundInterestStage QInterval.width
  let m : Nat := n + 1
  let base : Rat := 1 + 1 / (m : Rat)
  have heq :
      base ^ m * base - base ^ m = base ^ m * (base - 1) := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
  have hfactor : base - 1 = 1 / (m : Rat) := by
    dsimp [base]
    grind [Rat.sub_eq_add_neg]
  change base ^ m * base - base ^ m =
    base ^ m * (1 / (m : Rat))
  rw [heq, hfactor]

theorem eCompoundInterestStage_ordered (n : Nat) :
    0 <= (eCompoundInterestStage n).width := by
  rw [eCompoundInterestStage_width_eq]
  have hmpos : 0 < n + 1 := Nat.succ_pos n
  have hone_div_nonneg : 0 <= 1 / ((n + 1 : Nat) : Rat) :=
    Rat.le_of_lt (one_div_nat_pos hmpos)
  have hbase_nonneg :
      0 <= (1 + 1 / ((n + 1 : Nat) : Rat)) := by
    grind
  exact Rat.mul_nonneg
    (Rat.pow_nonneg hbase_nonneg)
    hone_div_nonneg

theorem eCompoundInterest_ordered :
    forall n, 0 <= (eCompoundInterest.compute n).width := by
  intro n
  rw [eCompoundInterest_compute_eq]
  exact eCompoundInterestStage_ordered n

def ECompoundInterestStageBound (C : Nat) : Prop :=
  forall n,
    (1 + 1 / ((n + 1 : Nat) : Rat)) ^ (n + 1) <= (C : Rat)

def ECompoundInterestNested : Prop :=
  forall n m, n <= m ->
    (eCompoundInterest.compute n).lo <= (eCompoundInterest.compute m).lo /\
    (eCompoundInterest.compute m).lo <= (eCompoundInterest.compute m).hi /\
    (eCompoundInterest.compute m).hi <= (eCompoundInterest.compute n).hi

private theorem rat_mul_pow (a b : Rat) (n : Nat) :
    (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ, ih, Rat.pow_succ, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem one_add_nat_mul_le_pow_one_add
    (x : Rat) (hx : 0 <= x) (n : Nat) :
    1 + (n : Rat) * x <= (1 + x)^n := by
  induction n with
  | zero =>
      simp
      native_decide
  | succ n ih =>
      rw [Rat.pow_succ]
      have hbase_nonneg : 0 <= 1 + x := by grind
      have hnx_nonneg : 0 <= (n : Rat) * x := by
        exact Rat.mul_nonneg (by exact_mod_cast (Nat.zero_le n)) hx
      have hone_le_pow : 1 <= (1 + x)^n := by grind
      have hx_le_powx : x <= (1 + x)^n * x := by
        have h := Rat.mul_le_mul_of_nonneg_right hone_le_pow hx
        simpa [Rat.one_mul] using h
      calc
        1 + ((n + 1 : Nat) : Rat) * x =
            (1 + (n : Rat) * x) + x := by
          have hcast :
              (((n + 1 : Nat) : Rat)) = (n : Rat) + 1 := by
            exact_mod_cast (by omega : n + 1 = n + 1)
          rw [hcast]
          grind [Rat.add_mul, Rat.add_assoc, Rat.add_comm]
        _ <= (1 + x)^n + x := by grind
        _ <= (1 + x)^n + (1 + x)^n * x := by grind
        _ = (1 + x)^n * (1 + x) := by
          grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

private theorem one_add_step_factor_mul_next {M : Rat} (hMpos : 0 < M) :
    (1 + 1 / (M * (M + 2))) * (1 + 1 / (M + 1)) =
      1 + 1 / M := by
  have hMne : M ≠ 0 := Rat.ne_of_gt hMpos
  have hM1pos : 0 < M + 1 := by grind
  have hM2pos : 0 < M + 2 := by grind
  have hM1ne : M + 1 ≠ 0 := Rat.ne_of_gt hM1pos
  have hM2ne : M + 2 ≠ 0 := Rat.ne_of_gt hM2pos
  have hdenne : M * (M + 2) ≠ 0 := by
    exact Rat.ne_of_gt (Rat.mul_pos hMpos hM2pos)
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel, Rat.inv_mul_cancel]

private theorem one_div_m_add_one_le_m_add_one_div_m_mul_m_add_two
    {M : Rat} (hMpos : 0 < M) :
    1 / (M + 1) <= (M + 1) / (M * (M + 2)) := by
  have hM1pos : 0 < M + 1 := by grind
  have hM2pos : 0 < M + 2 := by grind
  have hdenpos : 0 < M * (M + 2) := Rat.mul_pos hMpos hM2pos
  have hM1ne : M + 1 ≠ 0 := Rat.ne_of_gt hM1pos
  have hdenne : M * (M + 2) ≠ 0 := Rat.ne_of_gt hdenpos
  have hprodpos : 0 < (M + 1) * (M * (M + 2)) :=
    Rat.mul_pos hM1pos hdenpos
  apply Rat.le_of_mul_le_mul_right (c := (M + 1) * (M * (M + 2)))
  · calc
      (1 / (M + 1)) * ((M + 1) * (M * (M + 2))) =
          M * (M + 2) := by
        rw [Rat.div_def]
        have hcancel : (M + 1) * (M + 1)⁻¹ = 1 :=
          Rat.mul_inv_cancel (M + 1) hM1ne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= (M + 1) * (M + 1) := by
        have hdiff :
            (M + 1) * (M + 1) = M * (M + 2) + 1 := by
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]
        rw [hdiff]
        grind
      _ = ((M + 1) / (M * (M + 2))) *
            ((M + 1) * (M * (M + 2))) := by
        rw [Rat.div_def]
        have hcancel :
            (M * (M + 2)) * (M * (M + 2))⁻¹ = 1 :=
          Rat.mul_inv_cancel (M * (M + 2)) hdenne
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hprodpos

private theorem compoundInterestUpper_step (m : Nat) (hm : 0 < m) :
    (1 + 1 / (((m + 1 : Nat) : Rat))) ^ (m + 2) <=
      (1 + 1 / ((m : Nat) : Rat)) ^ (m + 1) := by
  let M : Rat := (m : Rat)
  let A : Rat := 1 + 1 / (M * (M + 2))
  let B : Rat := 1 + 1 / (M + 1)
  let C : Rat := 1 + 1 / M
  have hMpos : 0 < M := by
    dsimp [M]
    exact (Rat.natCast_pos).2 hm
  have hM1cast : M + 1 = (((m + 1 : Nat) : Rat)) := by
    dsimp [M]
    have hcast : (((m + 1 : Nat) : Rat)) = (m : Rat) + 1 := by
      exact_mod_cast (by omega : m + 1 = m + 1)
    exact hcast.symm
  have hx_nonneg : 0 <= 1 / (M * (M + 2)) := by
    have hM2pos : 0 < M + 2 := by grind
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos hMpos hM2pos))
  have hB_nonneg : 0 <= B := by
    have hM1pos : 0 < M + 1 := by grind
    have hinv : 0 <= 1 / (M + 1) := by
      rw [Rat.div_def, Rat.one_mul]
      exact Rat.le_of_lt ((Rat.inv_pos).2 hM1pos)
    dsimp [B]
    grind
  have hB_le_linear :
      B <= 1 + ((m + 1 : Nat) : Rat) *
        (1 / (M * (M + 2))) := by
    have hdiv :=
      one_div_m_add_one_le_m_add_one_div_m_mul_m_add_two hMpos
    dsimp [B]
    calc
      1 + 1 / (M + 1) <=
          1 + (M + 1) / (M * (M + 2)) := by grind
      _ = 1 + ((m + 1 : Nat) : Rat) *
            (1 / (M * (M + 2))) := by
        rw [← hM1cast]
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hB_le_Apow : B <= A ^ (m + 1) := by
    have hbern :=
      one_add_nat_mul_le_pow_one_add
        (1 / (M * (M + 2))) hx_nonneg (m + 1)
    dsimp [A]
    exact Rat.le_trans hB_le_linear hbern
  have hpowB_nonneg : 0 <= B ^ (m + 1) :=
    Rat.pow_nonneg hB_nonneg
  have hmul :=
    Rat.mul_le_mul_of_nonneg_left hB_le_Apow hpowB_nonneg
  have hAB : A * B = C := by
    dsimp [A, B, C]
    exact one_add_step_factor_mul_next hMpos
  have hcalc : B ^ (m + 2) <= C ^ (m + 1) := by
    calc
      B ^ (m + 2) = B ^ (m + 1) * B := by
        rw [show m + 2 = m + 1 + 1 by omega, Rat.pow_succ]
      _ <= B ^ (m + 1) * A ^ (m + 1) := hmul
      _ = A ^ (m + 1) * B ^ (m + 1) := by grind [Rat.mul_comm]
      _ = (A * B) ^ (m + 1) := by
        rw [rat_mul_pow]
      _ = C ^ (m + 1) := by rw [hAB]
  rw [← hM1cast]
  change B ^ (m + 2) <= C ^ (m + 1)
  exact hcalc

private theorem pow_mul_one_sub_nat_mul_le_one
    (x : Rat) (hx : 0 <= x) (n : Nat)
    (hsmall : (n : Rat) * x < 1) :
    (1 + x)^n * (1 - (n : Rat) * x) <= 1 := by
  induction n with
  | zero =>
      simp
      native_decide
  | succ n ih =>
      have hcast_le : (n : Rat) <= ((n + 1 : Nat) : Rat) := by
        exact_mod_cast (Nat.le_succ n)
      have hnx_le :
          (n : Rat) * x <= ((n + 1 : Nat) : Rat) * x :=
        Rat.mul_le_mul_of_nonneg_right hcast_le hx
      have hnsmall : (n : Rat) * x < 1 := by grind
      have ih' := ih hnsmall
      have hbase_nonneg : 0 <= 1 + x := by grind
      have hpow_nonneg : 0 <= (1 + x)^n :=
        Rat.pow_nonneg hbase_nonneg
      have hfactor_le :
          (1 + x) * (1 - ((n + 1 : Nat) : Rat) * x) <=
            1 - (n : Rat) * x := by
        have hcast :
            (((n + 1 : Nat) : Rat)) = (n : Rat) + 1 := by
          exact_mod_cast (by omega : n + 1 = n + 1)
        have hx2_nonneg : 0 <= x * x := Rat.mul_nonneg hx hx
        have hcoeff_nonneg : 0 <= (((n + 1 : Nat) : Rat)) := by
          exact_mod_cast (Nat.zero_le (n + 1))
        have hdrop :
            0 <= (((n + 1 : Nat) : Rat)) * (x * x) :=
          Rat.mul_nonneg hcoeff_nonneg hx2_nonneg
        calc
          (1 + x) * (1 - ((n + 1 : Nat) : Rat) * x) =
              (1 - (n : Rat) * x) -
                ((n + 1 : Nat) : Rat) * (x * x) := by
            rw [hcast]
            grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
              Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
          _ <= 1 - (n : Rat) * x := by
            grind [Rat.sub_eq_add_neg]
      have hmul :=
        Rat.mul_le_mul_of_nonneg_left hfactor_le hpow_nonneg
      calc
        (1 + x)^(n + 1) *
            (1 - ((n + 1 : Nat) : Rat) * x) =
            (1 + x)^n *
              ((1 + x) *
                (1 - ((n + 1 : Nat) : Rat) * x)) := by
          rw [Rat.pow_succ]
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= (1 + x)^n * (1 - (n : Rat) * x) := hmul
        _ <= 1 := ih'

private theorem pow_le_inv_one_sub_nat_mul
    (x : Rat) (hx : 0 <= x) (n : Nat)
    (hsmall : (n : Rat) * x < 1) :
    (1 + x)^n <= 1 / (1 - (n : Rat) * x) := by
  have hdpos : 0 < 1 - (n : Rat) * x := by
    grind [Rat.sub_eq_add_neg]
  have hdne : 1 - (n : Rat) * x ≠ 0 := Rat.ne_of_gt hdpos
  apply Rat.le_of_mul_le_mul_right (c := 1 - (n : Rat) * x)
  · calc
      (1 + x)^n * (1 - (n : Rat) * x) <= 1 :=
        pow_mul_one_sub_nat_mul_le_one x hx n hsmall
      _ = (1 / (1 - (n : Rat) * x)) *
            (1 - (n : Rat) * x) := by
        rw [Rat.div_def]
        have hcancel :
            (1 - (n : Rat) * x) *
                (1 - (n : Rat) * x)⁻¹ = 1 :=
          Rat.mul_inv_cancel (1 - (n : Rat) * x) hdne
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hdpos

private theorem stepFactor_pow_le_next (m : Nat) (hm : 0 < m) :
    (1 + 1 / (((m : Nat) : Rat) * (((m : Nat) : Rat) + 2))) ^ m <=
      1 + 1 / (((m + 1 : Nat) : Rat)) := by
  let M : Rat := (m : Rat)
  let x : Rat := 1 / (M * (M + 2))
  have hMpos : 0 < M := by
    dsimp [M]
    exact (Rat.natCast_pos).2 hm
  have hM2pos : 0 < M + 2 := by grind
  have hx_nonneg : 0 <= x := by
    dsimp [x]
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos hMpos hM2pos))
  have hMx : (m : Rat) * x = 1 / (M + 2) := by
    dsimp [x, M]
    rw [Rat.div_def]
    have hcancel : ((m : Rat)) * ((m : Rat))⁻¹ = 1 :=
      Rat.mul_inv_cancel ((m : Rat))
        (Rat.ne_of_gt ((Rat.natCast_pos).2 hm))
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hone_div_lt_one : 1 / (M + 2) < 1 := by
    rw [Rat.div_lt_iff hM2pos]
    grind
  have hsmall : (m : Rat) * x < 1 := by
    rw [hMx]
    exact hone_div_lt_one
  have hpow := pow_le_inv_one_sub_nat_mul x hx_nonneg m hsmall
  have htarget :
      1 / (1 - (m : Rat) * x) =
        1 + 1 / (((m + 1 : Nat) : Rat)) := by
    rw [hMx]
    have hcast : (((m + 1 : Nat) : Rat)) = M + 1 := by
      dsimp [M]
      exact_mod_cast (by omega : m + 1 = m + 1)
    rw [hcast]
    rw [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  dsimp [x, M] at hpow
  rw [htarget] at hpow
  exact hpow

private theorem compoundInterestLower_step (m : Nat) (hm : 0 < m) :
    (1 + 1 / ((m : Nat) : Rat)) ^ m <=
      (1 + 1 / (((m + 1 : Nat) : Rat))) ^ (m + 1) := by
  let M : Rat := (m : Rat)
  let A : Rat := 1 + 1 / (M * (M + 2))
  let B : Rat := 1 + 1 / (M + 1)
  let C : Rat := 1 + 1 / M
  have hMpos : 0 < M := by
    dsimp [M]
    exact (Rat.natCast_pos).2 hm
  have hM1cast : M + 1 = (((m + 1 : Nat) : Rat)) := by
    dsimp [M]
    have hcast : (((m + 1 : Nat) : Rat)) = (m : Rat) + 1 := by
      exact_mod_cast (by omega : m + 1 = m + 1)
    exact hcast.symm
  have hB_nonneg : 0 <= B := by
    have hM1pos : 0 < M + 1 := by grind
    have hinv : 0 <= 1 / (M + 1) := by
      rw [Rat.div_def, Rat.one_mul]
      exact Rat.le_of_lt ((Rat.inv_pos).2 hM1pos)
    dsimp [B]
    grind
  have hA_pow_le_B : A ^ m <= B := by
    have hstep := stepFactor_pow_le_next m hm
    dsimp [A, B, M]
    rw [hM1cast]
    exact hstep
  have hpowB_nonneg : 0 <= B ^ m := Rat.pow_nonneg hB_nonneg
  have hmul :=
    Rat.mul_le_mul_of_nonneg_right hA_pow_le_B hpowB_nonneg
  have hAB : A * B = C := by
    dsimp [A, B, C]
    exact one_add_step_factor_mul_next hMpos
  have hcalc : C ^ m <= B ^ (m + 1) := by
    calc
      C ^ m = (A * B) ^ m := by rw [← hAB]
      _ = A ^ m * B ^ m := by rw [rat_mul_pow]
      _ <= B * B ^ m := by simpa [Rat.mul_comm] using hmul
      _ = B ^ (m + 1) := by
        rw [Rat.pow_succ]
        grind [Rat.mul_comm]
  rw [← hM1cast]
  change C ^ m <= B ^ (m + 1)
  exact hcalc

theorem eCompoundInterestStage_hi_eq (n : Nat) :
    (eCompoundInterestStage n).hi =
      (1 + 1 / ((n + 1 : Nat) : Rat)) ^ (n + 2) := by
  unfold eCompoundInterestStage
  rw [show n + 2 = n + 1 + 1 by omega, Rat.pow_succ]

theorem eCompoundInterestStage_hi_antitone_succ (n : Nat) :
    (eCompoundInterestStage (n + 1)).hi <=
      (eCompoundInterestStage n).hi := by
  rw [eCompoundInterestStage_hi_eq, eCompoundInterestStage_hi_eq]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    compoundInterestUpper_step (n + 1) (Nat.succ_pos n)

theorem eCompoundInterestStage_hi_le_four (n : Nat) :
    (eCompoundInterestStage n).hi <= (4 : Rat) := by
  induction n with
  | zero =>
      unfold eCompoundInterestStage
      native_decide
  | succ n ih =>
      exact Rat.le_trans (eCompoundInterestStage_hi_antitone_succ n) ih

theorem eCompoundInterestStage_lo_eq (n : Nat) :
    (eCompoundInterestStage n).lo =
      (1 + 1 / ((n + 1 : Nat) : Rat)) ^ (n + 1) := by
  rfl

theorem eCompoundInterestStage_lo_mono_succ (n : Nat) :
    (eCompoundInterestStage n).lo <=
      (eCompoundInterestStage (n + 1)).lo := by
  rw [eCompoundInterestStage_lo_eq, eCompoundInterestStage_lo_eq]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    compoundInterestLower_step (n + 1) (Nat.succ_pos n)

theorem eCompoundInterestStage_lo_le_hi (n : Nat) :
    (eCompoundInterestStage n).lo <= (eCompoundInterestStage n).hi := by
  have h := eCompoundInterestStage_ordered n
  unfold QInterval.width at h
  grind [Rat.sub_eq_add_neg]

theorem eCompoundInterestStage_lo_mono {n m : Nat} (hnm : n <= m) :
    (eCompoundInterestStage n).lo <= (eCompoundInterestStage m).lo := by
  induction hnm with
  | refl =>
      exact Rat.le_refl
  | step hnm ih =>
      exact Rat.le_trans ih (eCompoundInterestStage_lo_mono_succ _)

theorem eCompoundInterestStage_hi_antitone {n m : Nat} (hnm : n <= m) :
    (eCompoundInterestStage m).hi <= (eCompoundInterestStage n).hi := by
  induction hnm with
  | refl =>
      exact Rat.le_refl
  | step hnm ih =>
      exact Rat.le_trans (eCompoundInterestStage_hi_antitone_succ _) ih

theorem eCompoundInterest_nested : ECompoundInterestNested := by
  intro n m hnm
  rw [eCompoundInterest_compute_eq, eCompoundInterest_compute_eq]
  exact ⟨eCompoundInterestStage_lo_mono hnm,
    eCompoundInterestStage_lo_le_hi m,
    eCompoundInterestStage_hi_antitone hnm⟩

theorem eCompoundInterestStageBound_four :
    ECompoundInterestStageBound 4 := by
  intro n
  rw [← eCompoundInterestStage_lo_eq n]
  exact Rat.le_trans (eCompoundInterestStage_lo_le_hi n)
    (eCompoundInterestStage_hi_le_four n)

theorem eCompoundInterest_width_le_of_stageBound
    {C : Nat} (hbound : ECompoundInterestStageBound C) (n : Nat) :
    (eCompoundInterest.compute n).width <=
      (C : Rat) / ((n + 1 : Nat) : Rat) := by
  rw [eCompoundInterest_compute_eq, eCompoundInterestStage_width_eq]
  have hfactor_nonneg :
      0 <= 1 / ((n + 1 : Nat) : Rat) :=
    Rat.le_of_lt (one_div_nat_pos (Nat.succ_pos n))
  have hmul :=
    Rat.mul_le_mul_of_nonneg_right (hbound n) hfactor_nonneg
  simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using hmul

theorem eCompoundInterest_widths_shrink_of_stageBound
    {C : Nat} (hbound : ECompoundInterestStageBound C) :
    RealRaw.WidthsShrinkToZero eCompoundInterest.compute := by
  intro eps
  refine ⟨C * (eps.val.den + 1), ?_⟩
  intro n hn
  have hwidth := eCompoundInterest_width_le_of_stageBound hbound n
  have htail :
      (C : Rat) / ((n + 1 : Nat) : Rat) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : (C : Rat) * B <= A := by
      dsimp [A, B]
      exact_mod_cast (by omega :
        C * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        ((C : Rat) / A) * (A * B) = (C : Rat) * B := by
          rw [Rat.div_def]
          have hcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          have hcancel : B * B⁻¹ = 1 := Rat.mul_inv_cancel B hBne
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hABpos
  exact Rat.le_trans (Rat.le_trans hwidth htail)
    (FTC.one_div_den_succ_le_of_pos eps.property)

theorem eCompoundInterest_widths_shrink :
    RealRaw.WidthsShrinkToZero eCompoundInterest.compute :=
  eCompoundInterest_widths_shrink_of_stageBound
    eCompoundInterestStageBound_four

theorem eCompoundInterest_valid_of_nested_and_stageBound
    {C : Nat} (hnested : ECompoundInterestNested)
    (hbound : ECompoundInterestStageBound C) :
    ECompoundInterestValid := by
  unfold ECompoundInterestValid RealRaw.Valid RealRaw.ValidCompute
  constructor
  · exact eCompoundInterest_ordered
  · constructor
    · exact hnested
    · exact eCompoundInterest_widths_shrink_of_stageBound hbound

theorem eCompoundInterest_valid_of_nested
    (hnested : ECompoundInterestNested) : ECompoundInterestValid :=
  eCompoundInterest_valid_of_nested_and_stageBound hnested
    eCompoundInterestStageBound_four

theorem eCompoundInterest_valid : ECompoundInterestValid :=
  eCompoundInterest_valid_of_nested eCompoundInterest_nested

/-- The verified compound-interest boxes for `e` have the uniform positive
lower bound `2`.  This is the concrete positivity certificate needed to use
the Euler base as the input of the project's repeated-natural-power and later
rational-power interfaces. -/
theorem eCompoundInterest_lower_bound_two (n : Nat) :
    (2 : Rat) <= (eCompoundInterest.compute n).lo := by
  rw [eCompoundInterest_compute_eq]
  have hmono := eCompoundInterestStage_lo_mono (n := 0) (m := n)
    (Nat.zero_le n)
  have hzero : (eCompoundInterestStage 0).lo = (2 : Rat) := by
    native_decide
  rw [hzero] at hmono
  exact hmono

/-- The certified positive base underlying the compound-interest presentation
of Euler's number.  Its value is still the direct rational interval algorithm
`eCompoundInterest`; no logarithm, root operation, or completed real number
is used to establish positivity. -/
def ePositive : exp.PositiveRealRaw where
  value := eCompoundInterest
  valid := eCompoundInterest_valid
  lower_bound := 2
  lower_bound_pos := by native_decide
  lower_bound_le := eCompoundInterest_lower_bound_two

/-- The literal repeated-multiplication powers of the certified positive
Euler base.  The generic positive-base API proves each such power valid and
keeps its rational lower bound explicit. -/
def eNaturalPower (n : Nat) : RealRaw :=
  ePositive.natPow n

theorem eNaturalPower_valid (n : Nat) :
    (eNaturalPower n).Valid :=
  ePositive.natPow_valid n

theorem eNaturalPower_lower_bound (n stage : Nat) :
    (2 : Rat) ^ n <= ((eNaturalPower n).compute stage).lo :=
  ePositive.natPow_lower_bound n stage

theorem eNaturalPower_upper_bound (n stage : Nat) :
    ((eNaturalPower n).compute stage).hi <= (4 : Rat) ^ n := by
  have hbase : exp.PositiveRealRaw.upperBound ePositive = (4 : Rat) := by
    unfold exp.PositiveRealRaw.upperBound ePositive
    rw [eCompoundInterest_compute_eq]
    native_decide
  rw [← hbase]
  exact ePositive.natPow_upper_bound n stage

private def repeatedMulLoop (a : Rat) (xs : List Nat) (value : Rat) : Rat :=
  Id.run do
    let mut value : Rat := value
    for _ in xs do
      value := value * a
    return value

private theorem repeatedMulLoop_eq_foldl
    (a : Rat) (xs : List Nat) (value : Rat) :
    repeatedMulLoop a xs value =
      xs.foldl (fun acc _ => acc * a) value := by
  induction xs generalizing value with
  | nil => rfl
  | cons _ xs ih =>
      calc
        repeatedMulLoop a (_ :: xs) value =
            repeatedMulLoop a xs (value * a) := by
          simp [repeatedMulLoop]
        _ = xs.foldl (fun acc _ => acc * a) (value * a) := by
          exact ih (value * a)
        _ = (_ :: xs).foldl (fun acc _ => acc * a) value := by
          rfl

private theorem foldl_repeatedMul_eq_mul_pow
    (a : Rat) (xs : List Nat) (value : Rat) :
    xs.foldl (fun acc _ => acc * a) value = value * a ^ xs.length := by
  induction xs generalizing value with
  | nil =>
      simp
  | cons _ xs ih =>
      calc
        (_ :: xs).foldl (fun acc _ => acc * a) value =
            xs.foldl (fun acc _ => acc * a) (value * a) := by
          rfl
        _ = (value * a) * a ^ xs.length := by
          exact ih (value * a)
        _ = value * a ^ ((_ :: xs).length) := by
          simp only [List.length_cons]
          rw [Rat.pow_succ]
          grind [Rat.mul_assoc, Rat.mul_comm]

private theorem repeatedMulLoop_one_eq_pow
    (a : Rat) (xs : List Nat) :
    repeatedMulLoop a xs 1 = a ^ xs.length := by
  rw [repeatedMulLoop_eq_foldl, foldl_repeatedMul_eq_mul_pow]
  grind

private theorem eulerCenter_eq_repeatedMulLoop (x : Rat) (n : Nat) :
    eulerCenter x n =
      repeatedMulLoop
        (1 + x / ((((n + 1) * (n + 1) : Nat) : Rat)))
        (List.range ((n + 1) * (n + 1))) 1 := by
  rfl

/-- Falling factorials over rational arithmetic. Keeping the parameter
rational lets the finite binomial algebra below be used directly at the
Euler mesh `m` without importing a combinatorics library. -/
def fallingFactorialRat (M : Rat) : Nat -> Rat
  | 0 => 1
  | k + 1 => fallingFactorialRat M k * (M - (k : Rat))

private theorem fallingFactorialRat_succ (M : Rat) (k : Nat) :
    fallingFactorialRat M (k + 1) =
      fallingFactorialRat M k * (M - (k : Rat)) :=
  rfl

/-- The falling-factorial form of Pascal's identity. This is a finite
rational polynomial identity, not an analytic use of the binomial theorem. -/
private theorem fallingFactorialRat_pascal_succ (M : Rat) (k : Nat) :
    fallingFactorialRat (M + 1) (k + 1) =
      fallingFactorialRat M (k + 1) +
        ((k + 1 : Nat) : Rat) * fallingFactorialRat M k := by
  induction k with
  | zero =>
      simp [fallingFactorialRat, Rat.sub_eq_add_neg]
      grind [Rat.sub_eq_add_neg]
  | succ k ih =>
      rw [fallingFactorialRat_succ (M + 1) (k + 1),
        fallingFactorialRat_succ M (k + 1), ih,
        fallingFactorialRat_succ M k]
      have hcast1 : (((k + 1 : Nat) : Rat)) = (k : Rat) + 1 := by
        exact_mod_cast (by omega : k + 1 = k + 1)
      have hcast2 : (((k + 2 : Nat) : Rat)) = (k : Rat) + 2 := by
        exact_mod_cast (by omega : k + 2 = k + 2)
      rw [hcast1, hcast2]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.add_assoc, Rat.add_comm, Rat.mul_comm]

/-- The `k`th term of the finite binomial expansion of `(1 + x)^M` when the
exponent `M` is a natural number embedded in the rationals. -/
def eulerBinomialTerm (M x : Rat) (k : Nat) : Rat :=
  fallingFactorialRat M k / factorialRat k * x ^ k

 /-- A finite prefix of the rational binomial expansion.  At the natural
endpoint `M = m`, the prefix of `m + 1` terms is exactly `(1 + x)^m`. -/
def eulerBinomialPrefix (M x : Rat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      eulerBinomialPrefix M x count + eulerBinomialTerm M x count

private theorem eulerBinomialTerm_zero (M x : Rat) :
    eulerBinomialTerm M x 0 = 1 := by
  unfold eulerBinomialTerm fallingFactorialRat factorialRat factorial
  grind [Rat.div_def]

/-- The coefficient identity needed to expand one more finite Euler
factor.  The factorial denominator cancels entirely by rational algebra. -/
private theorem eulerBinomialTerm_pascal_succ (M x : Rat) (k : Nat) :
    eulerBinomialTerm (M + 1) x (k + 1) =
      eulerBinomialTerm M x (k + 1) + x * eulerBinomialTerm M x k := by
  unfold eulerBinomialTerm
  rw [fallingFactorialRat_pascal_succ, FormalPowerSeries.factorialRat_succ,
    Rat.pow_succ, Rat.div_def, Rat.div_def, Rat.div_def]
  have hkpos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by
    exact_mod_cast Nat.succ_pos k
  have hfactpos : (0 : Rat) < factorialRat k :=
    RationalMajorant.factorialRat_pos k
  have hkne : ((k + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hkpos
  have hfactne : factorialRat k ≠ 0 := Rat.ne_of_gt hfactpos
  rw [Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.mul_inv_cancel]

private theorem eulerBinomialPrefix_succ (M x : Rat) (count : Nat) :
    eulerBinomialPrefix M x (count + 1) =
      eulerBinomialPrefix M x count + eulerBinomialTerm M x count :=
  rfl

/-- Summing Pascal's identity over a finite prefix. -/
private theorem eulerBinomialPrefix_pascal (M x : Rat) (count : Nat) :
    eulerBinomialPrefix (M + 1) x (count + 1) =
      eulerBinomialPrefix M x (count + 1) +
        x * eulerBinomialPrefix M x count := by
  induction count with
  | zero =>
      grind [eulerBinomialPrefix, eulerBinomialTerm_zero]
  | succ count ih =>
      calc
        eulerBinomialPrefix (M + 1) x ((count + 1) + 1) =
            eulerBinomialPrefix (M + 1) x (count + 1) +
              eulerBinomialTerm (M + 1) x (count + 1) := rfl
        _ = (eulerBinomialPrefix M x (count + 1) +
              x * eulerBinomialPrefix M x count) +
            (eulerBinomialTerm M x (count + 1) +
              x * eulerBinomialTerm M x count) := by
              rw [ih, eulerBinomialTerm_pascal_succ]
        _ = (eulerBinomialPrefix M x (count + 1) +
              eulerBinomialTerm M x (count + 1)) +
            x * eulerBinomialPrefix M x (count + 1) := by
              rw [eulerBinomialPrefix_succ M x count]
              grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.mul_assoc,
                Rat.mul_comm]
        _ = eulerBinomialPrefix M x ((count + 1) + 1) +
            x * eulerBinomialPrefix M x (count + 1) := rfl

private theorem fallingFactorialRat_nat_succ_zero (m : Nat) :
    fallingFactorialRat (m : Rat) (m + 1) = 0 := by
  rw [fallingFactorialRat_succ]
  have hcast : ((m : Nat) : Rat) = (m : Rat) := rfl
  rw [hcast]
  grind [Rat.sub_eq_add_neg]

private theorem eulerBinomialTerm_nat_succ_zero (m : Nat) (x : Rat) :
    eulerBinomialTerm (m : Rat) x (m + 1) = 0 := by
  unfold eulerBinomialTerm
  rw [fallingFactorialRat_nat_succ_zero]
  grind [Rat.div_def]

/-- The finite binomial expansion used to compare the Euler powers with
factorial-series prefixes. -/
theorem euler_binomial_prefix_nat_expansion (m : Nat) (x : Rat) :
    eulerBinomialPrefix (m : Rat) x (m + 1) = (1 + x) ^ m := by
  induction m with
  | zero =>
      grind [eulerBinomialPrefix, eulerBinomialTerm_zero]
  | succ m ih =>
      have hcast : (((m + 1 : Nat) : Rat)) = (m : Rat) + 1 := by
        exact_mod_cast (by omega : m + 1 = m + 1)
      rw [hcast, eulerBinomialPrefix_pascal, eulerBinomialPrefix_succ,
        eulerBinomialTerm_nat_succ_zero, ih, Rat.pow_succ]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.mul_assoc,
        Rat.mul_comm]

private def powerSeriesLoopStep (x : Rat) (s : Rat × Rat)
    (k : Nat) : Rat × Rat :=
  (s.1 + s.2, s.2 * x / ((k : Rat) + 1))

private def powerSeriesLoopPairFrom (x : Rat) (xs : List Nat)
    (sum term : Rat) : Rat × Rat :=
  Id.run do
    let mut sum : Rat := sum
    let mut term : Rat := term
    for k in xs do
      sum := sum + term
      term := term * x / ((k + 1 : Nat) : Rat)
    return (sum, term)

private def powerSeriesLoopPair (x : Rat) (xs : List Nat) :
    Rat × Rat :=
  powerSeriesLoopPairFrom x xs 0 1

private theorem powerSeriesLoopPairFrom_eq_foldl
    (x : Rat) (xs : List Nat) (sum term : Rat) :
    powerSeriesLoopPairFrom x xs sum term =
      xs.foldl (powerSeriesLoopStep x) (sum, term) := by
  induction xs generalizing sum term with
  | nil => rfl
  | cons k ks ih =>
      calc
        powerSeriesLoopPairFrom x (k :: ks) sum term =
            powerSeriesLoopPairFrom x ks
              (sum + term) (term * x / ((k : Rat) + 1)) := by
          simp [powerSeriesLoopPairFrom]
        _ = ks.foldl (powerSeriesLoopStep x)
            (sum + term, term * x / ((k : Rat) + 1)) := by
          exact ih (sum + term) (term * x / ((k : Rat) + 1))
        _ = (k :: ks).foldl (powerSeriesLoopStep x) (sum, term) := by
          rfl

private theorem powerSeriesLoopPair_eq_foldl
    (x : Rat) (xs : List Nat) :
    powerSeriesLoopPair x xs =
      xs.foldl (powerSeriesLoopStep x) (0, 1) := by
  unfold powerSeriesLoopPair
  exact powerSeriesLoopPairFrom_eq_foldl x xs 0 1

private def powerSeriesState (x : Rat) (N : Nat) : Rat × Rat :=
  (List.range N).foldl (powerSeriesLoopStep x) (0, 1)

private theorem powerSeriesState_succ (x : Rat) (N : Nat) :
    powerSeriesState x (N + 1) =
      powerSeriesLoopStep x (powerSeriesState x N) N := by
  unfold powerSeriesState
  rw [List.range_succ, List.foldl_append]
  rfl

/-- At the zero input the finite series state is exactly `(1, 0)` as soon as
at least one term has been processed.  This is a finite-loop fact, kept
separate from convergence or any completed-real interpretation. -/
private theorem powerSeriesState_zero_of_pos (N : Nat) (hN : 0 < N) :
    powerSeriesState (0 : Rat) N = (1, 0) := by
  cases N with
  | zero => omega
  | succ N =>
      by_cases hzero : N = 0
      · subst N
        native_decide
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hzero
        rw [powerSeriesState_succ,
          powerSeriesState_zero_of_pos N hNpos]
        simp [powerSeriesLoopStep, Rat.div_def]
        grind [Rat.add_zero]

private theorem expPowerSeries_center_eq_state
    (x : Rat) (n : Nat) :
    powerSeriesCenter x n =
      (powerSeriesState x (expPowerSeriesTerms x n)).1 := by
  unfold powerSeriesCenter
  rw [show (expPowerSeriesPartialAndTailBound x n).1 =
      (powerSeriesLoopPair x
        (List.range (expPowerSeriesTerms x n))).1 by rfl]
  rw [powerSeriesLoopPair_eq_foldl]
  rfl

private theorem expPowerSeries_tailRadius_eq_state
    (x : Rat) (n : Nat) :
    powerSeriesTailRadius x n =
      qabs (powerSeriesState x (expPowerSeriesTerms x n)).2 /
        (1 - expPowerSeriesTailRatioBound x n) := by
  unfold powerSeriesTailRadius
  rw [show (expPowerSeriesPartialAndTailBound x n).2 =
      qabs (powerSeriesLoopPair x
        (List.range (expPowerSeriesTerms x n))).2 /
        (1 - expPowerSeriesTailRatioBound x n) by rfl]
  rw [powerSeriesLoopPair_eq_foldl]
  rfl

private theorem ePowerSeriesTerms_eq (n : Nat) :
    expPowerSeriesTerms (1 : Rat) n = n + 10 := by
  unfold expPowerSeriesTerms
  change n + 8 + 2 * 1 = n + 10
  omega

private def ePowerSeriesTermAtTerms (N : Nat) : Rat :=
  (powerSeriesState (1 : Rat) N).2

private def ePowerSeriesCenterAtTerms (N : Nat) : Rat :=
  (powerSeriesState (1 : Rat) N).1

private def ePowerSeriesTailRadiusAtTerms (N : Nat) : Rat :=
  ePowerSeriesTermAtTerms N / (1 - 1 / ((N : Rat) + 1))

private theorem qabs_eq_self_of_nonneg {q : Rat} (hq : 0 <= q) :
    qabs q = q := by
  unfold qabs
  by_cases hlt : q < 0
  · have : ¬ 0 <= q := by grind
    contradiction
  · simp [hlt]

private theorem ePowerSeries_term_succ (N : Nat) :
    ePowerSeriesTermAtTerms (N + 1) =
      ePowerSeriesTermAtTerms N / ((N : Rat) + 1) := by
  unfold ePowerSeriesTermAtTerms
  rw [powerSeriesState_succ]
  simp [powerSeriesLoopStep]

private theorem ePowerSeries_center_succ (N : Nat) :
    ePowerSeriesCenterAtTerms (N + 1) =
      ePowerSeriesCenterAtTerms N + ePowerSeriesTermAtTerms N := by
  unfold ePowerSeriesCenterAtTerms ePowerSeriesTermAtTerms
  rw [powerSeriesState_succ]
  simp [powerSeriesLoopStep]

private theorem ePowerSeries_term_nonneg (N : Nat) :
    0 <= ePowerSeriesTermAtTerms N := by
  induction N with
  | zero =>
      unfold ePowerSeriesTermAtTerms powerSeriesState
      native_decide
  | succ N ih =>
      rw [ePowerSeries_term_succ]
      rw [Rat.div_def]
      have hdenpos : 0 < (N : Rat) + 1 := by
        exact_mod_cast Nat.succ_pos N
      exact Rat.mul_nonneg ih
        (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))

/-- At the Euler input `1/m`, one binomial term is obtained from the
previous one by the factorial-series ratio `1/(k+1)` multiplied by the
finite correction `(m-k)/m`. -/
private theorem eulerBinomialTerm_one_div_succ
    (m k : Nat) (hm : 0 < m) :
    eulerBinomialTerm (m : Rat) (1 / (m : Rat)) (k + 1) =
      eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
        (((m : Rat) - (k : Rat)) / (m : Rat)) /
          ((k : Rat) + 1) := by
  unfold eulerBinomialTerm
  rw [fallingFactorialRat_succ, FormalPowerSeries.factorialRat_succ,
    Rat.pow_succ, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def,
    Rat.div_def]
  have hmrat : (0 : Rat) < (m : Rat) := by
    exact_mod_cast hm
  have hmne : (m : Rat) ≠ 0 := Rat.ne_of_gt hmrat
  have hkpos : (0 : Rat) < (k : Rat) + 1 := by
    exact_mod_cast Nat.succ_pos k
  have hkne : (k : Rat) + 1 ≠ 0 := Rat.ne_of_gt hkpos
  have hfactpos : (0 : Rat) < factorialRat k :=
    RationalMajorant.factorialRat_pos k
  have hfactne : factorialRat k ≠ 0 := Rat.ne_of_gt hfactpos
  rw [Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
    Rat.inv_mul_cancel]

/-- Before the finite binomial expansion terminates, its correction factor is
an ordinary rational number in the unit interval. -/
private theorem eulerBinomialCorrection_bounds
    (m k : Nat) (hm : 0 < m) (hkm : k <= m) :
    0 <= (((m : Rat) - (k : Rat)) / (m : Rat)) /\
      (((m : Rat) - (k : Rat)) / (m : Rat)) <= 1 := by
  have hmrat : (0 : Rat) < (m : Rat) := by
    exact_mod_cast hm
  have hkmrat : (k : Rat) <= (m : Rat) := by
    exact_mod_cast hkm
  have hdiff : 0 <= (m : Rat) - (k : Rat) := by
    grind [Rat.sub_eq_add_neg]
  constructor
  · rw [Rat.div_def]
    exact Rat.mul_nonneg hdiff
      (Rat.le_of_lt ((Rat.inv_pos).2 hmrat))
  · apply Rat.le_of_mul_le_mul_right (c := (m : Rat))
    · rw [Rat.div_def]
      have hmne : (m : Rat) ≠ 0 := Rat.ne_of_gt hmrat
      calc
        ((m : Rat) - (k : Rat)) * (m : Rat)⁻¹ * (m : Rat) =
            (m : Rat) - (k : Rat) := by
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
        _ <= 1 * (m : Rat) := by grind [Rat.sub_eq_add_neg]
    · exact hmrat

/-- Each nonzero Euler-binomial term is nonnegative and no larger than the
matching factorial-series term.  The only input is that the finite correction
factor is in `[0,1]`. -/
private theorem eulerBinomialTerm_one_div_nonneg_le_seriesTerm
    (m : Nat) (hm : 0 < m) :
    forall k, k <= m ->
      0 <= eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k /\
        eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k <=
          ePowerSeriesTermAtTerms k := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [eulerBinomialTerm_zero]
      constructor
      · native_decide
      · unfold ePowerSeriesTermAtTerms powerSeriesState
        native_decide
  | succ k ih =>
      intro hsucc
      have hk : k <= m := by omega
      have hprev := ih hk
      have hcor := eulerBinomialCorrection_bounds m k hm hk
      have hdenpos : (0 : Rat) < (k : Rat) + 1 := by
        exact_mod_cast Nat.succ_pos k
      have hdeninv : 0 <= ((k : Rat) + 1)⁻¹ :=
        Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
      have hscaled_nonneg :
          0 <= eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
            (((m : Rat) - (k : Rat)) / (m : Rat)) :=
        Rat.mul_nonneg hprev.1 hcor.1
      have hscaled_le_prev :
          eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
            (((m : Rat) - (k : Rat)) / (m : Rat)) <=
          eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k := by
        calc
          eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
              (((m : Rat) - (k : Rat)) / (m : Rat)) <=
            eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k * 1 :=
              Rat.mul_le_mul_of_nonneg_left hcor.2 hprev.1
          _ = eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k := by
              grind
      have hscaled_le_series :
          eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
            (((m : Rat) - (k : Rat)) / (m : Rat)) <=
          ePowerSeriesTermAtTerms k :=
        Rat.le_trans hscaled_le_prev hprev.2
      constructor
      · rw [eulerBinomialTerm_one_div_succ m k hm, Rat.div_def]
        exact Rat.mul_nonneg hscaled_nonneg hdeninv
      · rw [eulerBinomialTerm_one_div_succ m k hm,
          ePowerSeries_term_succ, Rat.div_def, Rat.div_def]
        exact Rat.mul_le_mul_of_nonneg_right hscaled_le_series hdeninv

/-- Summing the termwise Euler-binomial bound gives a finite prefix bound.
The `m + 1` cutoff is exactly where the natural binomial expansion stops. -/
private theorem eulerBinomialPrefix_one_div_le_seriesCenter
    (m : Nat) (hm : 0 < m) :
    forall N, N <= m + 1 ->
      eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) N <=
        ePowerSeriesCenterAtTerms N := by
  intro N
  induction N with
  | zero =>
      intro _
      unfold eulerBinomialPrefix ePowerSeriesCenterAtTerms powerSeriesState
      native_decide
  | succ N ih =>
      intro hN
      have hNle : N <= m := by omega
      have hprev :
          eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) N <=
            ePowerSeriesCenterAtTerms N :=
        ih (by omega)
      have hterm :=
        (eulerBinomialTerm_one_div_nonneg_le_seriesTerm m hm N hNle).2
      rw [eulerBinomialPrefix_succ, ePowerSeries_center_succ]
      grind

/-- The difference between matching factorial-series and Euler-binomial
terms has a one-step recurrence with an explicit `k/m` loss. -/
private theorem eulerBinomialTerm_deficit_succ
    (m k : Nat) (hm : 0 < m) :
    ePowerSeriesTermAtTerms (k + 1) -
        eulerBinomialTerm (m : Rat) (1 / (m : Rat)) (k + 1) =
      (ePowerSeriesTermAtTerms k -
          eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k +
        eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
          ((k : Rat) / (m : Rat))) /
        ((k : Rat) + 1) := by
  rw [ePowerSeries_term_succ, eulerBinomialTerm_one_div_succ m k hm]
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def,
    Rat.div_def, Rat.div_def]
  have hmrat : (0 : Rat) < (m : Rat) := by
    exact_mod_cast hm
  have hmne : (m : Rat) ≠ 0 := Rat.ne_of_gt hmrat
  have hkpos : (0 : Rat) < (k : Rat) + 1 := by
    exact_mod_cast Nat.succ_pos k
  have hkne : (k : Rat) + 1 ≠ 0 := Rat.ne_of_gt hkpos
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.mul_comm, Rat.mul_inv_cancel, Rat.inv_mul_cancel]

/-- The loss in the `k`th Euler-binomial coefficient is at most the familiar
quadratic finite-mesh correction `k(k-1)/(2m)` times the factorial term. -/
private theorem eulerBinomialTerm_deficit_nonneg_le_quadratic
    (m : Nat) (hm : 0 < m) :
    forall k, k <= m ->
      0 <= ePowerSeriesTermAtTerms k -
          eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k /\
        ePowerSeriesTermAtTerms k -
          eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k <=
          ((k : Rat) * ((k : Rat) - 1) / (2 * (m : Rat))) *
            ePowerSeriesTermAtTerms k := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [eulerBinomialTerm_zero]
      unfold ePowerSeriesTermAtTerms powerSeriesState
      grind [Rat.div_def]
  | succ k ih =>
      intro hsucc
      have hk : k <= m := by omega
      have hprev := ih hk
      have hterm :=
        eulerBinomialTerm_one_div_nonneg_le_seriesTerm m hm k hk
      have hmrat : (0 : Rat) < (m : Rat) := by
        exact_mod_cast hm
      have hkrat : (0 : Rat) <= (k : Rat) := Rat.natCast_nonneg
      have hratio_nonneg : 0 <= (k : Rat) / (m : Rat) := by
        rw [Rat.div_def]
        exact Rat.mul_nonneg hkrat
          (Rat.le_of_lt ((Rat.inv_pos).2 hmrat))
      have hratio_scale :
          eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
            ((k : Rat) / (m : Rat)) <=
          ePowerSeriesTermAtTerms k * ((k : Rat) / (m : Rat)) :=
        Rat.mul_le_mul_of_nonneg_right hterm.2 hratio_nonneg
      have hquad_nonneg :
          0 <= (k : Rat) * ((k : Rat) - 1) / (2 * (m : Rat)) := by
        by_cases hkzero : k = 0
        · subst k
          grind [Rat.div_def]
        · have hkpos : (0 : Rat) < (k : Rat) := by
            exact_mod_cast Nat.pos_of_ne_zero hkzero
          have hkone : (1 : Rat) <= (k : Rat) := by
            exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hkzero)
          have hdenpos : 0 < 2 * (m : Rat) := by grind
          rw [Rat.div_def]
          exact Rat.mul_nonneg
            (Rat.mul_nonneg hkrat (by grind [Rat.sub_eq_add_neg]))
            (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))
      have hnumer_nonneg :
          0 <= ePowerSeriesTermAtTerms k -
              eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k +
            eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
              ((k : Rat) / (m : Rat)) :=
        Rat.add_nonneg hprev.1
          (Rat.mul_nonneg hterm.1 hratio_nonneg)
      have hnumer_bound :
          ePowerSeriesTermAtTerms k -
              eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k +
            eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
              ((k : Rat) / (m : Rat)) <=
            (((k : Rat) * ((k : Rat) - 1) / (2 * (m : Rat))) +
              (k : Rat) / (m : Rat)) * ePowerSeriesTermAtTerms k := by
        calc
          ePowerSeriesTermAtTerms k -
              eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k +
            eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
              ((k : Rat) / (m : Rat)) <=
            ((k : Rat) * ((k : Rat) - 1) / (2 * (m : Rat))) *
                ePowerSeriesTermAtTerms k +
              ePowerSeriesTermAtTerms k * ((k : Rat) / (m : Rat)) := by
              grind
          _ = (((k : Rat) * ((k : Rat) - 1) / (2 * (m : Rat))) +
              (k : Rat) / (m : Rat)) * ePowerSeriesTermAtTerms k := by
              grind [Rat.mul_add, Rat.add_mul, Rat.mul_comm]
      have hdenpos : (0 : Rat) < (k : Rat) + 1 := by
        exact_mod_cast Nat.succ_pos k
      have hdeninv : 0 <= ((k : Rat) + 1)⁻¹ :=
        Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
      have hcast : (((k + 1 : Nat) : Rat)) = (k : Rat) + 1 := by
        exact_mod_cast (by omega : k + 1 = k + 1)
      rw [hcast, eulerBinomialTerm_deficit_succ m k hm,
        ePowerSeries_term_succ, Rat.div_def, Rat.div_def]
      constructor
      · exact Rat.mul_nonneg hnumer_nonneg hdeninv
      · have hscaled :=
          Rat.mul_le_mul_of_nonneg_right hnumer_bound hdeninv
        have htarget :
            (ePowerSeriesTermAtTerms k -
                eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k +
              eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
                ((k : Rat) / (m : Rat))) * ((k : Rat) + 1)⁻¹ <=
              (((k : Rat) + 1) * (k : Rat) / (2 * (m : Rat))) *
                (ePowerSeriesTermAtTerms k * ((k : Rat) + 1)⁻¹) := by
          calc
            (ePowerSeriesTermAtTerms k -
                  eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k +
                eulerBinomialTerm (m : Rat) (1 / (m : Rat)) k *
                  ((k : Rat) / (m : Rat))) * ((k : Rat) + 1)⁻¹ <=
              ((((k : Rat) * ((k : Rat) - 1) / (2 * (m : Rat))) +
                (k : Rat) / (m : Rat)) * ePowerSeriesTermAtTerms k) *
                  ((k : Rat) + 1)⁻¹ := hscaled
            _ = (((k : Rat) + 1) * (k : Rat) / (2 * (m : Rat))) *
                  (ePowerSeriesTermAtTerms k * ((k : Rat) + 1)⁻¹) := by
                  have hmne : (m : Rat) ≠ 0 := Rat.ne_of_gt hmrat
                  have htwomne : (2 : Rat) * (m : Rat) ≠ 0 := by
                    exact Rat.ne_of_gt (Rat.mul_pos (by native_decide) hmrat)
                  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
                    Rat.inv_mul_cancel]
        have hsub : (k : Rat) + 1 - 1 = (k : Rat) := by
          grind [Rat.sub_eq_add_neg]
        rw [hsub]
        simpa [Rat.div_def] using htarget

private theorem eulerBinomialTerm_deficit_le_shiftedSeriesTerm
    (m k : Nat) (hm : 0 < m) (hk : k + 2 <= m) :
    ePowerSeriesTermAtTerms (k + 2) -
        eulerBinomialTerm (m : Rat) (1 / (m : Rat)) (k + 2) <=
      (1 / (m : Rat)) * ePowerSeriesTermAtTerms k := by
  have hquad :=
    (eulerBinomialTerm_deficit_nonneg_le_quadratic m hm (k + 2) hk).2
  have hmrat : (0 : Rat) < (m : Rat) := by
    exact_mod_cast hm
  have hmne : (m : Rat) ≠ 0 := Rat.ne_of_gt hmrat
  have hk1pos : (0 : Rat) < (k : Rat) + 1 := by
    exact_mod_cast Nat.succ_pos k
  have hk2pos : (0 : Rat) < (k : Rat) + 2 := by
    exact_mod_cast (by omega : 0 < k + 2)
  have hk1ne : (k : Rat) + 1 ≠ 0 := Rat.ne_of_gt hk1pos
  have hk2ne : (k : Rat) + 2 ≠ 0 := Rat.ne_of_gt hk2pos
  have hcast1 : (((k + 1 : Nat) : Rat)) = (k : Rat) + 1 := by
    exact_mod_cast (by omega : k + 1 = k + 1)
  have hcast2 : (((k + 2 : Nat) : Rat)) = (k : Rat) + 2 := by
    exact_mod_cast (by omega : k + 2 = k + 2)
  have hterm :
      ePowerSeriesTermAtTerms (k + 2) =
        ePowerSeriesTermAtTerms k /
          (((k : Rat) + 1) * ((k : Rat) + 2)) := by
    rw [show k + 2 = (k + 1) + 1 by omega,
      ePowerSeries_term_succ, ePowerSeries_term_succ, hcast1]
    have hsum : (k : Rat) + 1 + 1 = (k : Rat) + 2 := by
      grind
    rw [hsum]
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_rev]
  have hcoefficient :
      ((k + 2 : Nat) : Rat) * (((k + 2 : Nat) : Rat) - 1) /
          (2 * (m : Rat)) * ePowerSeriesTermAtTerms (k + 2) =
        (1 / (2 * (m : Rat))) * ePowerSeriesTermAtTerms k := by
    rw [hcast2, hterm, Rat.div_def, Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel, Rat.inv_mul_cancel]
  have hhalf_le : 1 / (2 * (m : Rat)) <= 1 / (m : Rat) := by
    apply Rat.le_of_mul_le_mul_right (c := 2 * (m : Rat))
    · have htwomne : (2 : Rat) * (m : Rat) ≠ 0 :=
        Rat.ne_of_gt (Rat.mul_pos (by native_decide) hmrat)
      calc
        (1 / (2 * (m : Rat))) * (2 * (m : Rat)) = 1 := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
        _ <= 2 := by native_decide
        _ = (1 / (m : Rat)) * (2 * (m : Rat)) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact Rat.mul_pos (by native_decide) hmrat
  have hscaled := Rat.mul_le_mul_of_nonneg_right hhalf_le
    (ePowerSeries_term_nonneg k)
  calc
    ePowerSeriesTermAtTerms (k + 2) -
        eulerBinomialTerm (m : Rat) (1 / (m : Rat)) (k + 2) <=
        ((k + 2 : Nat) : Rat) * (((k + 2 : Nat) : Rat) - 1) /
          (2 * (m : Rat)) * ePowerSeriesTermAtTerms (k + 2) := hquad
    _ = (1 / (2 * (m : Rat))) * ePowerSeriesTermAtTerms k := hcoefficient
    _ <= (1 / (m : Rat)) * ePowerSeriesTermAtTerms k := hscaled

/-- A finite accumulator for the coefficient-loss budget.  Its delayed
index matches the fact that the first two Euler-binomial coefficients agree
with the factorial series exactly. -/
private def eulerBinomialDeficitMajorant (m : Nat) : Nat -> Rat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | k + 3 =>
      eulerBinomialDeficitMajorant m (k + 2) +
        (1 / (m : Rat)) * ePowerSeriesTermAtTerms k

private theorem eulerBinomialDeficitMajorant_eq_shiftedCenter
    (m k : Nat) :
    eulerBinomialDeficitMajorant m (k + 2) =
      (1 / (m : Rat)) * ePowerSeriesCenterAtTerms k := by
  induction k with
  | zero =>
      unfold eulerBinomialDeficitMajorant ePowerSeriesCenterAtTerms
        powerSeriesState
      grind
  | succ k ih =>
      rw [show k + 1 + 2 = k + 3 by omega,
        eulerBinomialDeficitMajorant, ih, ePowerSeries_center_succ]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc]

/-- The total difference of any finite series prefix and its Euler-binomial
counterpart is bounded by the delayed factorial-prefix budget. -/
private theorem eulerBinomialPrefix_deficit_le_majorant
    (m : Nat) (hm : 0 < m) :
    forall N, N <= m + 1 ->
      ePowerSeriesCenterAtTerms N -
          eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) N <=
        eulerBinomialDeficitMajorant m N := by
  intro N
  induction N with
  | zero =>
      intro _
      unfold ePowerSeriesCenterAtTerms eulerBinomialPrefix
        eulerBinomialDeficitMajorant powerSeriesState
      grind
  | succ N ih =>
      intro hN
      cases N with
      | zero =>
          rw [ePowerSeries_center_succ, eulerBinomialPrefix_succ,
            eulerBinomialTerm_zero]
          unfold eulerBinomialDeficitMajorant eulerBinomialPrefix
            ePowerSeriesTermAtTerms
            ePowerSeriesCenterAtTerms powerSeriesState
          grind
      | succ N =>
          cases N with
          | zero =>
              have hprev :
                  ePowerSeriesCenterAtTerms 1 -
                      eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) 1 <= 0 := by
                have h := ih (by omega)
                simpa [eulerBinomialDeficitMajorant] using h
              have hterm :
                  ePowerSeriesTermAtTerms 1 -
                      eulerBinomialTerm (m : Rat) (1 / (m : Rat)) 1 <= 0 := by
                have h :=
                  (eulerBinomialTerm_deficit_nonneg_le_quadratic m hm 1
                    (by omega : 1 <= m)).2
                grind [Rat.div_def]
              rw [show 1 + 1 = 2 by rfl,
                ePowerSeries_center_succ, eulerBinomialPrefix_succ]
              unfold eulerBinomialDeficitMajorant
              grind [Rat.sub_eq_add_neg]
          | succ k =>
              have hprev :
                  ePowerSeriesCenterAtTerms (k + 2) -
                      eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) (k + 2) <=
                    eulerBinomialDeficitMajorant m (k + 2) :=
                ih (by omega)
              have hterm :=
                eulerBinomialTerm_deficit_le_shiftedSeriesTerm m k hm
                  (by omega : k + 2 <= m)
              rw [show k + 2 + 1 = k + 3 by omega,
                ePowerSeries_center_succ, eulerBinomialPrefix_succ,
                eulerBinomialDeficitMajorant]
              grind [Rat.sub_eq_add_neg]

private theorem eulerBinomialPrefix_one_div_mono
    (m : Nat) (hm : 0 < m) (N M : Nat)
    (hNM : N <= M) (hM : M <= m + 1) :
    eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) N <=
      eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) M := by
  induction hNM with
  | refl => exact Rat.le_refl
  | step hNM ih =>
      rename_i K
      have hK : K <= m := by omega
      have hterm :=
        (eulerBinomialTerm_one_div_nonneg_le_seriesTerm m hm K hK).1
      rw [eulerBinomialPrefix_succ]
      grind

private theorem ePowerSeries_tailRadiusAtTerms_nonneg
    (N : Nat) (hN : 0 < N) :
    0 <= ePowerSeriesTailRadiusAtTerms N := by
  have hNrat : (0 : Rat) < (N : Rat) := by
    exact_mod_cast hN
  have hN1pos : (0 : Rat) < (N : Rat) + 1 := by grind
  have hratio : 1 / ((N : Rat) + 1) < 1 := by
    rw [Rat.div_lt_iff hN1pos]
    grind
  have hden : 0 < 1 - 1 / ((N : Rat) + 1) := by
    grind [Rat.sub_eq_add_neg]
  unfold ePowerSeriesTailRadiusAtTerms
  rw [Rat.div_def]
  exact Rat.mul_nonneg (ePowerSeries_term_nonneg N)
    (Rat.le_of_lt ((Rat.inv_pos).2 hden))

private theorem ePowerSeries_term_le_one_div
    (N : Nat) (hN : 0 < N) :
    ePowerSeriesTermAtTerms N <= 1 / (N : Rat) := by
  induction N with
  | zero =>
      omega
  | succ N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp [ePowerSeries_term_succ]
        native_decide
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
        have ihN := ih hNpos
        rw [ePowerSeries_term_succ]
        have hdenpos : 0 < (N : Rat) + 1 := by
          exact_mod_cast Nat.succ_pos N
        have hinvnonneg : 0 <= ((N : Rat) + 1)⁻¹ :=
          Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
        have hmul := Rat.mul_le_mul_of_nonneg_right ihN hinvnonneg
        have hone_div_le_one : 1 / (N : Rat) <= (1 : Rat) := by
          have honepos : 0 < (1 : Nat) := by omega
          have h :=
            FTC.one_div_nat_antitone honepos hNpos (by omega : 1 <= N)
          have hone :
              (1 / (((1 : Nat) : Rat)) : Rat) = 1 := by
            native_decide
          change 1 / (N : Rat) <= 1 / (((1 : Nat) : Rat)) at h
          rw [hone] at h
          exact h
        have hmul2 :=
          Rat.mul_le_mul_of_nonneg_right hone_div_le_one hinvnonneg
        calc
          ePowerSeriesTermAtTerms N / ((N : Rat) + 1) <=
              (1 / (N : Rat)) / ((N : Rat) + 1) := by
            simpa [Rat.div_def] using hmul
          _ <= 1 / ((N : Rat) + 1) := by
            simpa [Rat.div_def] using hmul2
          _ = 1 / ((N + 1 : Nat) : Rat) := by
            have hcast :
                (((N + 1 : Nat) : Rat)) = (N : Rat) + 1 := by
              exact_mod_cast (by omega : N + 1 = N + 1)
            rw [hcast]

private theorem ePowerSeries_center_stage_eq (n : Nat) :
    powerSeriesCenter (1 : Rat) n =
      ePowerSeriesCenterAtTerms (n + 10) := by
  rw [expPowerSeries_center_eq_state, ePowerSeriesTerms_eq]
  rfl

private theorem ePowerSeries_tailRadius_stage_eq (n : Nat) :
    powerSeriesTailRadius (1 : Rat) n =
      ePowerSeriesTailRadiusAtTerms (n + 10) := by
  rw [expPowerSeries_tailRadius_eq_state, ePowerSeriesTerms_eq]
  change qabs (ePowerSeriesTermAtTerms (n + 10)) /
      (1 - expPowerSeriesTailRatioBound 1 n) =
    ePowerSeriesTailRadiusAtTerms (n + 10)
  rw [qabs_eq_self_of_nonneg (ePowerSeries_term_nonneg (n + 10))]
  unfold ePowerSeriesTailRadiusAtTerms
  unfold expPowerSeriesTailRatioBound
  rw [ePowerSeriesTerms_eq]
  have hcast :
      (((n + 10 + 1 : Nat) : Rat)) = ((n + 10 : Nat) : Rat) + 1 := by
    exact_mod_cast (by omega : n + 10 + 1 = n + 10 + 1)
  rw [hcast]
  have hqabs : qabs (1 : Rat) = 1 := by native_decide
  rw [hqabs]

private theorem ePowerSeries_tailRadius_drop_minus_term_eq
    {T M : Rat} (hM : 0 < M) :
    T / (1 - 1 / (M + 1)) -
        (T / (M + 1)) / (1 - 1 / (M + 2)) - T =
      T / (M * (M + 1) * (M + 1)) := by
  have hMne : M ≠ 0 := Rat.ne_of_gt hM
  have hM1pos : 0 < M + 1 := by grind
  have hM2pos : 0 < M + 2 := by grind
  have hM1ne : M + 1 ≠ 0 := Rat.ne_of_gt hM1pos
  have hM2ne : M + 2 ≠ 0 := Rat.ne_of_gt hM2pos
  have hden1 : 1 - 1 / (M + 1) = M / (M + 1) := by
    rw [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel, Rat.inv_mul_cancel]
  have hden2 : 1 - 1 / (M + 2) = (M + 1) / (M + 2) := by
    rw [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel, Rat.inv_mul_cancel]
  rw [hden1, hden2]
  rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel, Rat.inv_mul_cancel]

private theorem ePowerSeries_term_le_tailRadius_drop
    (N : Nat) (hN : 0 < N) :
    ePowerSeriesTermAtTerms N <=
      ePowerSeriesTailRadiusAtTerms N -
        ePowerSeriesTailRadiusAtTerms (N + 1) := by
  let T := ePowerSeriesTermAtTerms N
  have hT : 0 <= T := by
    dsimp [T]
    exact ePowerSeries_term_nonneg N
  have hM : 0 < (N : Rat) := (Rat.natCast_pos).2 hN
  have hdrop :=
    ePowerSeries_tailRadius_drop_minus_term_eq
      (T := T) (M := (N : Rat)) hM
  have hdenpos :
      0 < (N : Rat) * ((N : Rat) + 1) * ((N : Rat) + 1) := by
    exact Rat.mul_pos
      (Rat.mul_pos hM (by grind))
      (by grind)
  have hnonneg :
      0 <= T / ((N : Rat) * ((N : Rat) + 1) * ((N : Rat) + 1)) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hT
      (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))
  have hdiff_nonneg :
      0 <=
        ePowerSeriesTailRadiusAtTerms N -
          ePowerSeriesTailRadiusAtTerms (N + 1) -
            ePowerSeriesTermAtTerms N := by
    unfold ePowerSeriesTailRadiusAtTerms
    rw [ePowerSeries_term_succ]
    have hsuccDen :
        (((N + 1 : Nat) : Rat)) + 1 = ((N : Rat) + 2) := by
      exact_mod_cast (by omega : N + 1 + 1 = N + 2)
    rw [hsuccDen]
    dsimp [T] at hdrop
    simpa [Rat.add_assoc, Rat.add_comm] using
      (show
        0 <=
          ePowerSeriesTermAtTerms N / (1 - 1 / ((N : Rat) + 1)) -
            (ePowerSeriesTermAtTerms N / ((N : Rat) + 1)) /
              (1 - 1 / ((N : Rat) + 2)) -
            ePowerSeriesTermAtTerms N from by
          rw [hdrop]
          exact hnonneg)
  grind [Rat.sub_eq_add_neg]

/-- Adding the certified tail to a factorial-series prefix is antitone in
the number of retained terms.  This is a finite telescoping argument over
the explicit one-term tail budget. -/
private theorem ePowerSeries_center_add_tail_antitone
    (N M : Nat) (hN : 0 < N) (hNM : N <= M) :
    ePowerSeriesCenterAtTerms M + ePowerSeriesTailRadiusAtTerms M <=
      ePowerSeriesCenterAtTerms N + ePowerSeriesTailRadiusAtTerms N := by
  induction hNM with
  | refl => exact Rat.le_refl
  | step hNM ih =>
      rename_i K
      have hKpos : 0 < K := Nat.lt_of_lt_of_le hN hNM
      have hdrop := ePowerSeries_term_le_tailRadius_drop K hKpos
      rw [ePowerSeries_center_succ]
      grind [Rat.sub_eq_add_neg]

private theorem ePowerSeries_center_le_center_add_tail
    (N M : Nat) (hN : 0 < N) (hNM : N <= M) :
    ePowerSeriesCenterAtTerms M <=
      ePowerSeriesCenterAtTerms N + ePowerSeriesTailRadiusAtTerms N := by
  have htailM := ePowerSeries_tailRadiusAtTerms_nonneg M
    (Nat.lt_of_lt_of_le hN hNM)
  calc
    ePowerSeriesCenterAtTerms M <=
        ePowerSeriesCenterAtTerms M + ePowerSeriesTailRadiusAtTerms M := by
          grind
    _ <= ePowerSeriesCenterAtTerms N + ePowerSeriesTailRadiusAtTerms N :=
      ePowerSeries_center_add_tail_antitone N M hN hNM

/-- A deliberately simple finite global bound for factorial-series prefixes.
The prefix-plus-tail envelope at one retained term is exactly `3`. -/
private theorem ePowerSeries_centerAtTerms_le_three
    (N : Nat) (hN : 0 < N) :
    ePowerSeriesCenterAtTerms N <= (3 : Rat) := by
  have htail := ePowerSeries_tailRadiusAtTerms_nonneg N hN
  have hant := ePowerSeries_center_add_tail_antitone 1 N
    (by omega : 0 < 1) (by omega : 1 <= N)
  have hone :
      ePowerSeriesCenterAtTerms 1 + ePowerSeriesTailRadiusAtTerms 1 =
        (3 : Rat) := by
    native_decide
  calc
    ePowerSeriesCenterAtTerms N <=
        ePowerSeriesCenterAtTerms N + ePowerSeriesTailRadiusAtTerms N := by
          grind
    _ <= ePowerSeriesCenterAtTerms 1 + ePowerSeriesTailRadiusAtTerms 1 :=
      hant
    _ = (3 : Rat) := hone

/-- Summing the quadratic coefficient loss gives a uniform `3/m` bound on
the difference between a factorial-series prefix and its Euler-binomial
prefix. -/
private theorem ePowerSeriesCenter_sub_eulerBinomialPrefix_le_three_div
    (m N : Nat) (hm : 0 < m) (hNthree : 3 <= N) (hNM : N <= m + 1) :
    ePowerSeriesCenterAtTerms N -
        eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) N <=
      3 / (m : Rat) := by
  have hdef := eulerBinomialPrefix_deficit_le_majorant m hm N hNM
  let K : Nat := N - 2
  have hK : K + 2 = N := by
    dsimp [K]
    omega
  have hKpos : 0 < K := by
    dsimp [K]
    omega
  have hmajorant :
      eulerBinomialDeficitMajorant m N =
        (1 / (m : Rat)) * ePowerSeriesCenterAtTerms K := by
    rw [← hK]
    exact eulerBinomialDeficitMajorant_eq_shiftedCenter m K
  have hcenter := ePowerSeries_centerAtTerms_le_three K hKpos
  have hmrat : (0 : Rat) < (m : Rat) := by
    exact_mod_cast hm
  have hinvnonneg : 0 <= 1 / (m : Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by native_decide)
      (Rat.le_of_lt ((Rat.inv_pos).2 hmrat))
  have hscaled := Rat.mul_le_mul_of_nonneg_left hcenter hinvnonneg
  calc
    ePowerSeriesCenterAtTerms N -
        eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) N <=
        eulerBinomialDeficitMajorant m N := hdef
    _ = (1 / (m : Rat)) * ePowerSeriesCenterAtTerms K := hmajorant
    _ <= (1 / (m : Rat)) * 3 := hscaled
    _ = 3 / (m : Rat) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem ePowerSeriesCenter_le_eulerProduct_add_three_div
    (m N : Nat) (hm : 0 < m) (hNthree : 3 <= N) (hNM : N <= m + 1) :
    ePowerSeriesCenterAtTerms N <=
      (1 + 1 / (m : Rat)) ^ m + 3 / (m : Rat) := by
  have hdef := ePowerSeriesCenter_sub_eulerBinomialPrefix_le_three_div
    m N hm hNthree hNM
  have hprefix := eulerBinomialPrefix_one_div_mono m hm N (m + 1)
    hNM (Nat.le_refl _)
  calc
    ePowerSeriesCenterAtTerms N <=
        eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) N + 3 / (m : Rat) := by
          grind [Rat.sub_eq_add_neg]
    _ <= eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) (m + 1) +
          3 / (m : Rat) := by
      grind
    _ = (1 + 1 / (m : Rat)) ^ m + 3 / (m : Rat) := by
      rw [euler_binomial_prefix_nat_expansion]

/-- The finite Euler product is below the series prefix plus its explicit
tail budget.  This is the upper half of the eventual raw-real overlap. -/
private theorem eulerProduct_one_div_le_series_upper
    (m N : Nat) (hm : 0 < m) (hN : 0 < N) (hNM : N <= m + 1) :
    (1 + 1 / (m : Rat)) ^ m <=
      ePowerSeriesCenterAtTerms N + ePowerSeriesTailRadiusAtTerms N := by
  calc
    (1 + 1 / (m : Rat)) ^ m =
        eulerBinomialPrefix (m : Rat) (1 / (m : Rat)) (m + 1) := by
          exact (euler_binomial_prefix_nat_expansion m (1 / (m : Rat))).symm
    _ <= ePowerSeriesCenterAtTerms (m + 1) :=
      eulerBinomialPrefix_one_div_le_seriesCenter m hm (m + 1)
        (Nat.le_refl _)
    _ <= ePowerSeriesCenterAtTerms N + ePowerSeriesTailRadiusAtTerms N :=
      ePowerSeries_center_le_center_add_tail N (m + 1) hN hNM

private theorem ePowerSeries_tailRadius_le_two_mul_term
    {T M : Rat} (hT : 0 <= T) (hM : 1 <= M) :
    T / (1 - 1 / (M + 1)) <= 2 * T := by
  have hMpos : 0 < M := by grind
  have hMne : M ≠ 0 := Rat.ne_of_gt hMpos
  have hM1pos : 0 < M + 1 := by grind
  have hM1ne : M + 1 ≠ 0 := Rat.ne_of_gt hM1pos
  have hden : 1 - 1 / (M + 1) = M / (M + 1) := by
    rw [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel, Rat.inv_mul_cancel]
  have hratio : (M + 1) / M <= (2 : Rat) := by
    apply Rat.le_of_mul_le_mul_right (c := M)
    · calc
        ((M + 1) / M) * M = M + 1 := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
            Rat.inv_mul_cancel]
        _ <= 2 * M := by grind
    · exact hMpos
  rw [hden, Rat.div_def, Rat.div_def]
  have hmul := Rat.mul_le_mul_of_nonneg_left hratio hT
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
    Rat.inv_mul_cancel]

private theorem ePowerSeries_tailRadiusAtTerms_le_two_div
    (N : Nat) (hN : 0 < N) :
    ePowerSeriesTailRadiusAtTerms N <= 2 / (N : Rat) := by
  have hterm_nonneg := ePowerSeries_term_nonneg N
  have hterm_bound := ePowerSeries_term_le_one_div N hN
  have hMone : (1 : Rat) <= (N : Rat) := by
    exact_mod_cast (Nat.succ_le_of_lt hN)
  have htail :=
    ePowerSeries_tailRadius_le_two_mul_term
      (T := ePowerSeriesTermAtTerms N) (M := (N : Rat))
      hterm_nonneg hMone
  have hscale :=
    Rat.mul_le_mul_of_nonneg_left hterm_bound
      (by native_decide : (0 : Rat) <= 2)
  calc
    ePowerSeriesTailRadiusAtTerms N <=
        2 * ePowerSeriesTermAtTerms N := by
      simpa [ePowerSeriesTailRadiusAtTerms] using htail
    _ <= 2 * (1 / (N : Rat)) := hscale
    _ = 2 / (N : Rat) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem four_div_four_mul_succ (d : Nat) :
    (4 : Rat) / (((4 * (d + 1) : Nat) : Rat)) =
      1 / (((d + 1 : Nat) : Rat)) := by
  have hdpos : 0 < ((d + 1 : Nat) : Rat) := by
    exact_mod_cast Nat.succ_pos d
  have hdne : (((d + 1 : Nat) : Rat)) ≠ 0 := Rat.ne_of_gt hdpos
  have h4ne : (4 : Rat) ≠ 0 := by native_decide
  rw [Rat.div_def, Rat.div_def]
  have hcast :
      (((4 * (d + 1) : Nat) : Rat)) =
        (4 : Rat) * (((d + 1 : Nat) : Rat)) := by
    exact_mod_cast (by omega : 4 * (d + 1) = 4 * (d + 1))
  rw [hcast]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
    Rat.inv_mul_cancel]

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

/-- The finite power-series loop at zero has already consumed its initial
constant term at every public stage. -/
private theorem expPowerSeriesTerms_zero_pos (n : Nat) :
    0 < expPowerSeriesTerms (0 : Rat) n := by
  unfold expPowerSeriesTerms
  change 0 < n + 8 + 2 * 0
  omega

theorem expPowerSeries_zero_center (n : Nat) :
    powerSeriesCenter (0 : Rat) n = 1 := by
  rw [expPowerSeries_center_eq_state,
    powerSeriesState_zero_of_pos
      (expPowerSeriesTerms (0 : Rat) n)
      (expPowerSeriesTerms_zero_pos n)]

theorem expPowerSeries_zero_tailRadius (n : Nat) :
    powerSeriesTailRadius (0 : Rat) n = 0 := by
  rw [expPowerSeries_tailRadius_eq_state,
    powerSeriesState_zero_of_pos
      (expPowerSeriesTerms (0 : Rat) n)
      (expPowerSeriesTerms_zero_pos n)]
  have habs : qabs (0 : Rat) = 0 := by native_decide
  rw [habs]
  grind [expPowerSeriesTailRatioBound, Rat.div_def]

/-- The rational exponential power series has the exact initial value one at
zero, stage by stage. -/
theorem expPowerSeries_zero_compute_eq (n : Nat) :
    (expPowerSeries (0 : Rat)).compute n = (RealRaw.ofRat 1).compute n := by
  rw [expPowerSeries_compute_eq, expPowerSeries_zero_center,
    expPowerSeries_zero_tailRadius, RealRaw.ofRat_compute]
  native_decide

theorem expPowerSeries_zero_equiv_one :
    (expPowerSeries (0 : Rat)).Equiv (RealRaw.ofRat 1) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (expPowerSeries (0 : Rat)) (RealRaw.ofRat 1) n n).2
  rw [expPowerSeries_zero_compute_eq, RealRaw.ofRat_compute]
  simp [QInterval.Overlaps]

theorem eulerCenter_zero (n : Nat) : eulerCenter (0 : Rat) n = 1 := by
  rw [eulerCenter_eq_repeatedMulLoop]
  have hbase :
      1 + (0 : Rat) / ((((n + 1) * (n + 1) : Nat) : Rat)) = 1 := by
    grind [Rat.div_def, Rat.sub_eq_add_neg]
  rw [hbase, repeatedMulLoop_one_eq_pow]
  have hone_pow : forall m : Nat, (1 : Rat) ^ m = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [Rat.pow_succ, ih]
        grind
  exact hone_pow _

/-- The repeated-multiplication exponential centers also satisfy the exact
initial condition.  Their public boxes retain their explicit radius, so this
theorem records overlap with one rather than claiming those boxes are point
intervals. -/
theorem expEuler_zero_compute_eq (n : Nat) :
    (expEuler (0 : Rat)).compute n = intervalAround 1 (stageRadius n) := by
  rw [expEuler_compute_eq, eulerCenter_zero]

theorem expEuler_zero_equiv_one :
    (expEuler (0 : Rat)).Equiv (RealRaw.ofRat 1) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (expEuler (0 : Rat)) (RealRaw.ofRat 1) n n).2
  rw [expEuler_zero_compute_eq, RealRaw.ofRat_compute]
  unfold intervalAround QInterval.Overlaps
  have hradius : 0 <= stageRadius n := stageRadius_nonneg n
  constructor <;> grind [Rat.sub_eq_add_neg]

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

private theorem eulerCenter_one_eq_squareProduct (n : Nat) :
    eulerCenter 1 n =
      (1 + 1 / ((((n + 1) * (n + 1) : Nat) : Rat))) ^
        ((n + 1) * (n + 1)) := by
  rw [eulerCenter_eq_repeatedMulLoop, repeatedMulLoop_one_eq_pow]
  simp

theorem eulerCenter_one_eq_compoundInterestStage_lo_square
    (n : Nat) :
    eulerCenter 1 n =
      (eCompoundInterestStage (((n + 1) * (n + 1)) - 1)).lo := by
  let m : Nat := (n + 1) * (n + 1)
  have hmpos : 0 < m := by
    dsimp [m]
    exact Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)
  have hm : m - 1 + 1 = m := by omega
  unfold eulerCenter eCompoundInterestStage
  change repeatedMulLoop (1 + 1 / (m : Rat)) (List.range m) 1 =
    let m' : Nat := m - 1 + 1
    let base : Rat := 1 + 1 / (m' : Rat)
    base ^ m'
  rw [repeatedMulLoop_one_eq_pow]
  simp [List.length_range, hm]

private theorem squareSubOne_mono {n m : Nat} (hnm : n <= m) :
    ((n + 1) * (n + 1)) - 1 <= ((m + 1) * (m + 1)) - 1 := by
  have hsucc : n + 1 <= m + 1 := Nat.succ_le_succ hnm
  have hsquare : (n + 1) * (n + 1) <= (m + 1) * (m + 1) :=
    Nat.mul_le_mul hsucc hsucc
  exact Nat.sub_le_sub_right hsquare 1

theorem eEulerCenter_mono {n m : Nat} (hnm : n <= m) :
    eulerCenter 1 n <= eulerCenter 1 m := by
  rw [eulerCenter_one_eq_compoundInterestStage_lo_square n,
    eulerCenter_one_eq_compoundInterestStage_lo_square m]
  exact eCompoundInterestStage_lo_mono (squareSubOne_mono hnm)

theorem eEulerCenter_step_mono (n : Nat) :
    eulerCenter 1 n <= eulerCenter 1 (n + 1) :=
  eEulerCenter_mono (Nat.le_succ n)

theorem eEuler_eq_eCompoundInterest :
    EEulerEqCompoundInterest := by
  unfold EEulerEqCompoundInterest
  apply RealRaw.sameStageOverlap_equiv
  intro n
  let k : Nat := ((n + 1) * (n + 1)) - 1
  have hnk : n <= k := by
    have hsucc_le_square :
        n + 1 <= (n + 1) * (n + 1) :=
      Nat.le_mul_of_pos_right (n + 1) (Nat.succ_pos n)
    dsimp [k]
    omega
  have hcenter :
      eulerCenter 1 n = (eCompoundInterestStage k).lo := by
    simpa [k] using
      eulerCenter_one_eq_compoundInterestStage_lo_square n
  have hradius : 0 <= stageRadius n := stageRadius_nonneg n
  have hlo_mono :
      (eCompoundInterestStage n).lo <=
        (eCompoundInterestStage k).lo :=
    eCompoundInterestStage_lo_mono hnk
  have hhi_anti :
      (eCompoundInterestStage k).hi <=
        (eCompoundInterestStage n).hi :=
    eCompoundInterestStage_hi_antitone hnk
  have hk_order :
      (eCompoundInterestStage k).lo <=
        (eCompoundInterestStage k).hi :=
    eCompoundInterestStage_lo_le_hi k
  apply (RealRaw.compareAt_overlap_iff eEuler eCompoundInterest n n).2
  rw [eEuler, expEuler_compute_eq, eCompoundInterest_compute_eq]
  unfold intervalAround QInterval.Overlaps
  constructor
  · calc
      eulerCenter 1 n - stageRadius n <= eulerCenter 1 n := by
        grind
      _ = (eCompoundInterestStage k).lo := hcenter
      _ <= (eCompoundInterestStage k).hi := hk_order
      _ <= (eCompoundInterestStage n).hi := hhi_anti
  · calc
      (eCompoundInterestStage n).lo <=
          (eCompoundInterestStage k).lo := hlo_mono
      _ = eulerCenter 1 n := hcenter.symm
      _ <= eulerCenter 1 n + stageRadius n := by
        grind

theorem eCompoundInterest_eq_eEuler :
    eCompoundInterest.Equiv eEuler :=
  RealRaw.equiv_symm eEuler_eq_eCompoundInterest

/-- A deliberately generous rational radius for the direct
repeated-multiplication computation of `e`.  The center at stage `n` is
`(1 + 1/(n+1)^2)^(n+1)^2`; the radius is chosen so that the resulting boxes
are themselves nested, rather than needing a later prefix stabilization. -/
def eEulerNestedRadius (n : Nat) : Rat :=
  8 / (((n + 1 : Nat) : Rat))

/-- A direct valid raw representative of `e` evaluated by repeated
multiplication.  Each stage performs only the finite rational calculation
`(1 + 1/(n+1)^2)^(n+1)^2`; the enclosing radius is explicit rational data. -/
def eEulerNested : RealRaw where
  compute := fun n =>
    intervalAround (eulerCenter (1 : Rat) n) (eEulerNestedRadius n)

theorem eEulerNested_compute_eq (n : Nat) :
    eEulerNested.compute n =
      intervalAround (eulerCenter (1 : Rat) n) (eEulerNestedRadius n) := by
  rfl

theorem eEulerNestedRadius_nonneg (n : Nat) :
    0 <= eEulerNestedRadius n := by
  unfold eEulerNestedRadius
  have hpos : 0 < (((n + 1 : Nat) : Rat)) :=
    (Rat.natCast_pos).2 (Nat.succ_pos n)
  rw [Rat.div_def]
  exact Rat.mul_nonneg (by native_decide) (Rat.le_of_lt ((Rat.inv_pos).2 hpos))

private theorem eulerBinomialError_le_eEulerNestedRadius (n : Nat) :
    (3 : Rat) / ((((n + 1) * (n + 1) : Nat) : Rat)) <=
      eEulerNestedRadius n := by
  let A : Rat := ((n + 1 : Nat) : Rat)
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have hAone : (1 : Rat) <= A := by
    dsimp [A]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hcast : (((n + 1) * (n + 1) : Nat) : Rat) = A * A := by
    dsimp [A]
    exact_mod_cast (by omega : (n + 1) * (n + 1) = (n + 1) * (n + 1))
  rw [hcast]
  unfold eEulerNestedRadius
  apply Rat.le_of_mul_le_mul_right (c := A * A)
  · rw [Rat.div_def, Rat.div_def]
    calc
      (3 * (A * A)⁻¹) * (A * A) = 3 := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= 8 * A := by grind
      _ = (8 * A⁻¹) * (A * A) := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos hApos hApos

theorem eEulerNestedRadius_antitone {n m : Nat} (hnm : n <= m) :
    eEulerNestedRadius m <= eEulerNestedRadius n := by
  unfold eEulerNestedRadius
  have hnpos : 0 < n + 1 := Nat.succ_pos n
  have hmpos : 0 < m + 1 := Nat.succ_pos m
  have hsucc : n + 1 <= m + 1 := Nat.succ_le_succ hnm
  have hrecip :
      1 / (((m + 1 : Nat) : Rat)) <= 1 / (((n + 1 : Nat) : Rat)) :=
    FTC.one_div_nat_antitone hnpos hmpos hsucc
  simpa [Rat.div_def] using
    Rat.mul_le_mul_of_nonneg_left hrecip (by native_decide : (0 : Rat) <= 8)

private theorem eEulerSquareStageWidth_le_eEulerNestedRadius_drop (n : Nat) :
    (4 : Rat) /
        ((((n + 1) * (n + 1) : Nat) : Rat)) <=
      eEulerNestedRadius n - eEulerNestedRadius (n + 1) := by
  let A : Rat := (((n + 1 : Nat) : Rat))
  let B : Rat := (((n + 2 : Nat) : Rat))
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hBpos : 0 < B := by
    dsimp [B]
    exact (Rat.natCast_pos).2 (by omega)
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
  have hcast : (((n + 1) * (n + 1) : Nat) : Rat) = A * A := by
    dsimp [A]
    exact_mod_cast (by omega : (n + 1) * (n + 1) = (n + 1) * (n + 1))
  have hnext : (((n + 1 + 1 : Nat) : Rat)) = B := by
    dsimp [B]
  have hB_eq : B = A + 1 := by
    dsimp [A, B]
    exact_mod_cast (by omega : n + 2 = n + 1 + 1)
  have hB_le : B <= 2 * A := by
    rw [hB_eq]
    have hAone : (1 : Rat) <= A := by
      dsimp [A]
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    grind
  have hCpos : 0 < A * A * B :=
    Rat.mul_pos (Rat.mul_pos hApos hApos) hBpos
  rw [hcast]
  unfold eEulerNestedRadius
  rw [hnext]
  apply Rat.le_of_mul_le_mul_right (c := A * A * B)
  · rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have hAinv : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
    have hBinv : B * B⁻¹ = 1 := Rat.mul_inv_cancel B hBne
    calc
      (4 * (A * A)⁻¹) * (A * A * B) = 4 * B := by
        rw [Rat.inv_mul_rev]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= 8 * A := by
        have h := Rat.mul_le_mul_of_nonneg_left hB_le
          (by native_decide : (0 : Rat) <= 4)
        grind
      _ = (8 * A⁻¹ - 8 * B⁻¹) * (A * A * B) := by
        grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_add, Rat.add_mul]
  · exact hCpos

theorem eEulerNested_width_eq (n : Nat) :
    (eEulerNested.compute n).width =
      (16 : Rat) / (((n + 1 : Nat) : Rat)) := by
  rw [eEulerNested_compute_eq, intervalAround_width]
  unfold eEulerNestedRadius
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add]

theorem eEulerNested_widths_shrink :
    RealRaw.WidthsShrinkToZero eEulerNested.compute := by
  apply shrinksToZero_of_natOverSuccBound (C := 16)
  intro n
  have h16 : (16 : Rat) = ((16 : Nat) : Rat) := by native_decide
  rw [eEulerNested_width_eq, h16]
  exact Rat.le_refl

theorem eEulerNested_nested :
    forall n m, n <= m ->
      (eEulerNested.compute n).lo <= (eEulerNested.compute m).lo /\
      (eEulerNested.compute m).lo <= (eEulerNested.compute m).hi /\
      (eEulerNested.compute m).hi <= (eEulerNested.compute n).hi := by
  intro n m hnm
  rw [eEulerNested_compute_eq, eEulerNested_compute_eq]
  by_cases hsame : m = n
  · subst m
    exact ⟨Rat.le_refl,
      intervalAround_ordered _ _ (eEulerNestedRadius_nonneg n), Rat.le_refl⟩
  · have hsuccm : n + 1 <= m := by omega
    have hcenter_mono : eulerCenter (1 : Rat) n <= eulerCenter (1 : Rat) m :=
      eEulerCenter_mono hnm
    have hradius_mono :
        eEulerNestedRadius m <= eEulerNestedRadius (n + 1) :=
      eEulerNestedRadius_antitone hsuccm
    let k : Nat := ((n + 1) * (n + 1)) - 1
    let l : Nat := ((m + 1) * (m + 1)) - 1
    have hkl : k <= l := by
      simpa [k, l] using squareSubOne_mono hnm
    have hcenter_n :
        eulerCenter (1 : Rat) n = (eCompoundInterestStage k).lo := by
      simpa [k] using eulerCenter_one_eq_compoundInterestStage_lo_square n
    have hcenter_m :
        eulerCenter (1 : Rat) m = (eCompoundInterestStage l).lo := by
      simpa [l] using eulerCenter_one_eq_compoundInterestStage_lo_square m
    have hlo_hi :
        (eCompoundInterestStage l).lo <= (eCompoundInterestStage k).hi :=
      Rat.le_trans (eCompoundInterestStage_lo_le_hi l)
        (eCompoundInterestStage_hi_antitone hkl)
    have hcenter_gap_stage :
        eulerCenter (1 : Rat) m - eulerCenter (1 : Rat) n <=
          (eCompoundInterestStage k).hi - (eCompoundInterestStage k).lo := by
      rw [hcenter_n, hcenter_m]
      grind [Rat.sub_eq_add_neg]
    have hcenter_gap :
        eulerCenter (1 : Rat) m - eulerCenter (1 : Rat) n <=
          (eCompoundInterest.compute k).width := by
      rw [eCompoundInterest_compute_eq]
      simpa [QInterval.width] using hcenter_gap_stage
    have hden :
        (((k + 1 : Nat) : Rat)) =
          ((((n + 1) * (n + 1) : Nat) : Rat)) := by
      dsimp [k]
      have hpos : 0 < (n + 1) * (n + 1) :=
        Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)
      exact_mod_cast (by omega : ((n + 1) * (n + 1) - 1) + 1 =
        (n + 1) * (n + 1))
    have hgap :
        eulerCenter (1 : Rat) m - eulerCenter (1 : Rat) n <=
          eEulerNestedRadius n - eEulerNestedRadius (n + 1) := by
      calc
        eulerCenter (1 : Rat) m - eulerCenter (1 : Rat) n <=
            (eCompoundInterest.compute k).width := hcenter_gap
        _ <= (4 : Rat) / (((k + 1 : Nat) : Rat)) :=
          eCompoundInterest_width_le_of_stageBound
            eCompoundInterestStageBound_four k
        _ = (4 : Rat) /
            ((((n + 1) * (n + 1) : Nat) : Rat)) := by rw [hden]
        _ <= eEulerNestedRadius n - eEulerNestedRadius (n + 1) :=
          eEulerSquareStageWidth_le_eEulerNestedRadius_drop n
    constructor
    · unfold intervalAround
      grind [Rat.sub_eq_add_neg]
    · constructor
      · exact intervalAround_ordered _ _ (eEulerNestedRadius_nonneg m)
      · unfold intervalAround
        grind [Rat.sub_eq_add_neg]

theorem eEulerNested_valid : eEulerNested.Valid := by
  unfold RealRaw.Valid RealRaw.ValidCompute
  constructor
  · intro n
    rw [eEulerNested_compute_eq, intervalAround_width]
    exact Rat.add_nonneg (eEulerNestedRadius_nonneg n)
      (eEulerNestedRadius_nonneg n)
  · exact ⟨eEulerNested_nested, eEulerNested_widths_shrink⟩

theorem eEulerNested_equiv_eCompoundInterest :
    eEulerNested.Equiv eCompoundInterest := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  let k : Nat := ((n + 1) * (n + 1)) - 1
  have hnk : n <= k := by
    have hsucc_le_square :
        n + 1 <= (n + 1) * (n + 1) :=
      Nat.le_mul_of_pos_right (n + 1) (Nat.succ_pos n)
    dsimp [k]
    omega
  have hcenter :
      eulerCenter (1 : Rat) n = (eCompoundInterestStage k).lo := by
    simpa [k] using eulerCenter_one_eq_compoundInterestStage_lo_square n
  have hradius : 0 <= eEulerNestedRadius n := eEulerNestedRadius_nonneg n
  have hlo_mono :
      (eCompoundInterestStage n).lo <=
        (eCompoundInterestStage k).lo :=
    eCompoundInterestStage_lo_mono hnk
  have hhi_anti :
      (eCompoundInterestStage k).hi <=
        (eCompoundInterestStage n).hi :=
    eCompoundInterestStage_hi_antitone hnk
  have hk_order :
      (eCompoundInterestStage k).lo <=
        (eCompoundInterestStage k).hi :=
    eCompoundInterestStage_lo_le_hi k
  apply (RealRaw.compareAt_overlap_iff eEulerNested eCompoundInterest n n).2
  rw [eEulerNested_compute_eq, eCompoundInterest_compute_eq]
  unfold intervalAround QInterval.Overlaps
  constructor
  · calc
      eulerCenter 1 n - eEulerNestedRadius n <= eulerCenter 1 n := by grind
      _ = (eCompoundInterestStage k).lo := hcenter
      _ <= (eCompoundInterestStage k).hi := hk_order
      _ <= (eCompoundInterestStage n).hi := hhi_anti
  · calc
      (eCompoundInterestStage n).lo <=
          (eCompoundInterestStage k).lo := hlo_mono
      _ = eulerCenter 1 n := hcenter.symm
      _ <= eulerCenter 1 n + eEulerNestedRadius n := by grind

private theorem ePowerSeriesTerms_le_squareEulerTerms
    (n : Nat) (hn : 3 <= n) :
    n + 10 <= (n + 1) * (n + 1) + 1 := by
  have hfour : 4 <= n + 1 := by omega
  have hmul : (n + 1) * 4 <= (n + 1) * (n + 1) :=
    Nat.mul_le_mul_left (n + 1) hfour
  have hmul' : 4 * (n + 1) <= (n + 1) * (n + 1) := by
    simpa [Nat.mul_comm] using hmul
  have hlinear : n + 10 <= 4 * (n + 1) + 1 := by omega
  exact Nat.le_trans hlinear (Nat.succ_le_succ hmul')

private theorem eEulerNested_lower_le_ePowerSeries_upper (n : Nat) :
    eulerCenter (1 : Rat) n - eEulerNestedRadius n <=
      powerSeriesCenter (1 : Rat) n + powerSeriesTailRadius (1 : Rat) n := by
  by_cases hn : 3 <= n
  · let M : Nat := (n + 1) * (n + 1)
    let N : Nat := n + 10
    have hMpos : 0 < M := by
      dsimp [M]
      exact Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)
    have hNpos : 0 < N := by
      dsimp [N]
      omega
    have hNM : N <= M + 1 := by
      dsimp [N, M]
      exact ePowerSeriesTerms_le_squareEulerTerms n hn
    have hbound := eulerProduct_one_div_le_series_upper M N hMpos hNpos hNM
    have hcenter := eulerCenter_one_eq_squareProduct n
    have hseriesCenter := ePowerSeries_center_stage_eq n
    have hseriesTail := ePowerSeries_tailRadius_stage_eq n
    calc
      eulerCenter (1 : Rat) n - eEulerNestedRadius n <=
          eulerCenter (1 : Rat) n := by
            have hradius := eEulerNestedRadius_nonneg n
            grind [Rat.sub_eq_add_neg]
      _ = (1 + 1 / (M : Rat)) ^ M := by
            simpa [M] using hcenter
      _ <= ePowerSeriesCenterAtTerms N + ePowerSeriesTailRadiusAtTerms N :=
            hbound
      _ = powerSeriesCenter (1 : Rat) n + powerSeriesTailRadius (1 : Rat) n := by
            rw [hseriesCenter, hseriesTail]
  · have hcases : n = 0 \/ n = 1 \/ n = 2 := by omega
    rcases hcases with rfl | rfl | rfl <;> native_decide

private theorem ePowerSeries_lower_le_eEulerNested_upper (n : Nat) :
    powerSeriesCenter (1 : Rat) n - powerSeriesTailRadius (1 : Rat) n <=
      eulerCenter (1 : Rat) n + eEulerNestedRadius n := by
  by_cases hn : 3 <= n
  · let M : Nat := (n + 1) * (n + 1)
    let N : Nat := n + 10
    have hMpos : 0 < M := by
      dsimp [M]
      exact Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)
    have hNpos : 0 < N := by
      dsimp [N]
      omega
    have hNthree : 3 <= N := by
      dsimp [N]
      omega
    have hNM : N <= M + 1 := by
      dsimp [N, M]
      exact ePowerSeriesTerms_le_squareEulerTerms n hn
    have hbound :=
      ePowerSeriesCenter_le_eulerProduct_add_three_div M N hMpos hNthree hNM
    have herror := eulerBinomialError_le_eEulerNestedRadius n
    have htail := ePowerSeries_tailRadiusAtTerms_nonneg N hNpos
    have hcenter := eulerCenter_one_eq_squareProduct n
    have hseriesCenter := ePowerSeries_center_stage_eq n
    have hseriesTail := ePowerSeries_tailRadius_stage_eq n
    calc
      powerSeriesCenter (1 : Rat) n - powerSeriesTailRadius (1 : Rat) n =
          ePowerSeriesCenterAtTerms N - ePowerSeriesTailRadiusAtTerms N := by
            rw [hseriesCenter, hseriesTail]
      _ <= ePowerSeriesCenterAtTerms N := by
            grind [Rat.sub_eq_add_neg]
      _ <= (1 + 1 / (M : Rat)) ^ M + 3 / (M : Rat) := hbound
      _ = eulerCenter (1 : Rat) n + 3 / (M : Rat) := by
            rw [hcenter]
      _ <= eulerCenter (1 : Rat) n + eEulerNestedRadius n := by
            apply (Rat.add_le_add_left).2
            simpa [M] using herror
  · have hcases : n = 0 \/ n = 1 \/ n = 2 := by omega
    rcases hcases with rfl | rfl | rfl <;> native_decide

/-- The valid factorial-series raw for `e` agrees directly with the nested
repeated-multiplication raw.  The proof is a finite binomial coefficient and
tail-budget comparison, independent of real-number completeness. -/
theorem ePowerSeries_equiv_eEulerNested :
    ePowerSeries.Equiv eEulerNested := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff ePowerSeries eEulerNested n n).2
  rw [ePowerSeries, expPowerSeries_compute_eq, eEulerNested_compute_eq]
  unfold intervalAround QInterval.Overlaps
  exact ⟨ePowerSeries_lower_le_eEulerNested_upper n,
    eEulerNested_lower_le_ePowerSeries_upper n⟩

/-- Public rational radius for certifying the literal repeated-multiplication
Euler computation.  Evaluation of the resulting stabilized representative
uses only Euler prefixes and this rational schedule; the compound-interest
enclosure is a proof-side anchor. -/
def eEulerStabilizationRadius (n : Nat) : Rat :=
  4 / (((n + 1 : Nat) : Rat))

theorem eEulerStabilizationRadius_covers_compoundInterest (n : Nat) :
    (eCompoundInterest.compute n).width <= eEulerStabilizationRadius n := by
  simpa [eEulerStabilizationRadius] using
    eCompoundInterest_width_le_of_stageBound
      eCompoundInterestStageBound_four n

theorem eEulerStabilizationRadius_shrinks :
    ShrinksToZero eEulerStabilizationRadius := by
  apply shrinksToZero_of_natOverSuccBound (C := 4)
  intro n
  exact Rat.le_refl

/-- A valid direct-only representative of `e` whose runtime is finite prefixes
of the literal repeated-multiplication Euler computation.  This normalization
does not prove the original Euler boxes nested. -/
def eEulerStabilized : RealRaw :=
  RealRaw.prefixStabilize eEuler eEulerStabilizationRadius

theorem eEulerStabilized_valid : eEulerStabilized.Valid := by
  unfold eEulerStabilized
  have hshrink : RealRaw.WidthsShrinkToZero eEuler.compute := by
    simpa [eEuler] using expEuler_widths_shrink (1 : Rat)
  exact RealRaw.prefixStabilize_valid
    hshrink
    eCompoundInterest_valid
    eEuler_eq_eCompoundInterest
    eEulerStabilizationRadius_covers_compoundInterest
    eEulerStabilizationRadius_shrinks

/-- The direct repeated-multiplication candidate overlaps its certified
prefix-stabilized representative at every common stage. -/
theorem eEuler_equiv_eEulerStabilized :
    eEuler.Equiv eEulerStabilized := by
  unfold eEulerStabilized
  exact RealRaw.candidate_equiv_prefixStabilize
    eCompoundInterest_valid
    eEuler_eq_eCompoundInterest
    eEulerStabilizationRadius_covers_compoundInterest

/-- The certified repeated-multiplication representation agrees with the
sharp compound-interest enclosure for `e`. -/
theorem eEulerStabilized_equiv_eCompoundInterest :
    eEulerStabilized.Equiv eCompoundInterest := by
  unfold eEulerStabilized
  exact RealRaw.prefixStabilize_equiv_anchor
    eCompoundInterest_valid
    eEuler_eq_eCompoundInterest
    eEulerStabilizationRadius_covers_compoundInterest

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

def EEulerCenterForwardStepMovement : Prop :=
  forall n,
    eulerCenter 1 (n + 1) - eulerCenter 1 n <=
      stageRadius n - stageRadius (n + 1)

def EEulerCenterForwardStepMovementUpTo (N : Nat) : Prop :=
  forall n, n <= N ->
    eulerCenter 1 (n + 1) - eulerCenter 1 n <=
      stageRadius n - stageRadius (n + 1)

def EEulerCenterStepMovementUpTo (N : Nat) : Prop :=
  forall n, n <= N ->
    eulerCenter 1 (n + 1) - eulerCenter 1 n <=
        stageRadius n - stageRadius (n + 1) /\
      eulerCenter 1 n - eulerCenter 1 (n + 1) <=
        stageRadius n - stageRadius (n + 1)

def EPowerSeriesRatioBound : Prop :=
  PowerSeriesRatioBound 1

def EPowerSeriesWidthsShrink : Prop :=
  PowerSeriesWidthsShrink 1

theorem eEulerCenter_reverse_step_bound (n : Nat) :
    eulerCenter 1 n - eulerCenter 1 (n + 1) <=
      stageRadius n - stageRadius (n + 1) := by
  have hmono := eEulerCenter_step_mono n
  have hnonpos : eulerCenter 1 n - eulerCenter 1 (n + 1) <= 0 := by
    grind [Rat.sub_eq_add_neg]
  have hdrop : 0 <= stageRadius n - stageRadius (n + 1) :=
    stageRadius_drop_nonneg (Nat.le_succ n)
  exact Rat.le_trans hnonpos hdrop

theorem eEuler_center_step_movement_of_forward_bound
    (hforward : EEulerCenterForwardStepMovement) :
    EEulerCenterStepMovement := by
  intro n
  exact ⟨hforward n, eEulerCenter_reverse_step_bound n⟩

theorem eEulerCenterForwardStepMovementUpToFifty :
    EEulerCenterForwardStepMovementUpTo 50 := by
  unfold EEulerCenterForwardStepMovementUpTo
  native_decide

theorem eEulerCenterStepMovementUpTo_of_forward
    {N : Nat} (hforward : EEulerCenterForwardStepMovementUpTo N) :
    EEulerCenterStepMovementUpTo N := by
  intro n hn
  exact ⟨hforward n hn, eEulerCenter_reverse_step_bound n⟩

theorem eEulerCenterStepMovementUpToFifty :
    EEulerCenterStepMovementUpTo 50 :=
  eEulerCenterStepMovementUpTo_of_forward
    eEulerCenterForwardStepMovementUpToFifty

theorem ePowerSeries_center_step_movement :
    EPowerSeriesCenterStepMovement := by
  intro n
  let N : Nat := n + 10
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  have hcenter0 := ePowerSeries_center_stage_eq n
  have hcenter1 := ePowerSeries_center_stage_eq (n + 1)
  have hradius0 := ePowerSeries_tailRadius_stage_eq n
  have hradius1 := ePowerSeries_tailRadius_stage_eq (n + 1)
  have hNsucc : n + 1 + 10 = N + 1 := by
    dsimp [N]
  have hcenterSucc :
      powerSeriesCenter (1 : Rat) (n + 1) =
        powerSeriesCenter (1 : Rat) n +
          ePowerSeriesTermAtTerms N := by
    rw [hcenter0, hcenter1, hNsucc, ePowerSeries_center_succ]
  have hdrop :=
    ePowerSeries_term_le_tailRadius_drop N hNpos
  constructor
  · rw [hcenterSucc, hradius0, hradius1, hNsucc]
    grind [Rat.sub_eq_add_neg]
  · rw [hcenterSucc, hradius0, hradius1, hNsucc]
    have hterm_nonneg := ePowerSeries_term_nonneg N
    grind [Rat.sub_eq_add_neg]

theorem ePowerSeries_widths_shrink :
    EPowerSeriesWidthsShrink := by
  unfold EPowerSeriesWidthsShrink PowerSeriesWidthsShrink
  intro eps
  let B : Nat := eps.val.den + 1
  let N0 : Nat := 4 * B
  exact Exists.intro N0 (by
    intro n hn
    have hBpos : 0 < B := by
      dsimp [B]
      omega
    have hN0pos : 0 < N0 := by
      dsimp [N0]
      exact Nat.mul_pos (by omega : 0 < 4) hBpos
    have hn10pos : 0 < n + 10 := by omega
    have hN0_le_n10 : N0 <= n + 10 := by omega
    have hanti : 1 / (((n + 10 : Nat) : Rat)) <=
        1 / ((N0 : Nat) : Rat) :=
      FTC.one_div_nat_antitone hN0pos hn10pos hN0_le_n10
    have hfour_nonneg : (0 : Rat) <= 4 := by native_decide
    have hmul :=
      Rat.mul_le_mul_of_nonneg_left hanti hfour_nonneg
    have hfour_terms :
        (4 : Rat) / (((n + 10 : Nat) : Rat)) <=
          (4 : Rat) / ((N0 : Nat) : Rat) := by
      simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using hmul
    have hfour_N0 :
        (4 : Rat) / ((N0 : Nat) : Rat) =
          1 / ((B : Nat) : Rat) := by
      dsimp [N0, B]
      simpa using four_div_four_mul_succ eps.val.den
    have hBbound : 1 / ((B : Nat) : Rat) <= eps.val := by
      dsimp [B]
      exact FTC.one_div_den_succ_le_of_pos eps.property
    rw [expPowerSeries_width_eq, ePowerSeries_tailRadius_stage_eq]
    have hrad :=
      ePowerSeries_tailRadiusAtTerms_le_two_div (n + 10) hn10pos
    have hsum :
        ePowerSeriesTailRadiusAtTerms (n + 10) +
            ePowerSeriesTailRadiusAtTerms (n + 10) <=
          (2 : Rat) / (((n + 10 : Nat) : Rat)) +
            (2 : Rat) / (((n + 10 : Nat) : Rat)) :=
      by grind
    calc
      ePowerSeriesTailRadiusAtTerms (n + 10) +
          ePowerSeriesTailRadiusAtTerms (n + 10) <=
          (2 : Rat) / (((n + 10 : Nat) : Rat)) +
            (2 : Rat) / (((n + 10 : Nat) : Rat)) := hsum
      _ = (4 : Rat) / (((n + 10 : Nat) : Rat)) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add]
      _ <= (4 : Rat) / ((N0 : Nat) : Rat) := hfour_terms
      _ = 1 / ((B : Nat) : Rat) := hfour_N0
      _ <= eps.val := hBbound)

private theorem rat_le_num_natAbs_succ (q : Rat) :
    q <= (((q.num.natAbs : Nat) : Rat) + 1) := by
  by_cases hqpos : 0 < q
  · have hdenpos : 0 < ((q.den : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
    apply Rat.le_of_mul_le_mul_right (c := ((q.den : Nat) : Rat))
    · rw [Rat.mul_comm q ((q.den : Nat) : Rat), rat_den_mul_self]
      have hnumpos : 0 < q.num := rat_num_pos_of_pos hqpos
      have hnum_nonneg : 0 <= q.num := Int.le_of_lt hnumpos
      have hcast : (((q.num.natAbs : Nat) : Rat)) = (q.num : Rat) := by
        exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
      calc
        (q.num : Rat) = ((q.num.natAbs : Nat) : Rat) := by rw [hcast]
        _ <= (((q.num.natAbs : Nat) : Rat) + 1) := by
          exact_mod_cast (Nat.le_succ q.num.natAbs)
        _ <= (((q.num.natAbs : Nat) : Rat) + 1) *
            ((q.den : Nat) : Rat) := by
          exact_mod_cast (Nat.le_mul_of_pos_right (q.num.natAbs + 1)
            (Nat.pos_of_ne_zero q.den_nz))
    · exact hdenpos
  · have hqnonpos : q <= 0 := by grind
    have hzero : (0 : Rat) <= (((q.num.natAbs : Nat) : Rat) + 1) := by
      exact_mod_cast (Nat.zero_le (q.num.natAbs + 1))
    exact Rat.le_trans hqnonpos hzero

private theorem qabs_le_num_natAbs_succ (q : Rat) :
    qabs q <= (((q.num.natAbs : Nat) : Rat) + 1) := by
  unfold qabs
  by_cases hneg : q < 0
  · simp [hneg]
    have h := rat_le_num_natAbs_succ (-q)
    have hnum : (-q).num.natAbs = q.num.natAbs := by
      cases q
      simp
    simpa [hnum] using h
  · simp [hneg]
    exact rat_le_num_natAbs_succ q

private theorem qabs_lt_expPowerSeriesTailDen (x : Rat) (n : Nat) :
    qabs x < ((expPowerSeriesTerms x n + 1 : Nat) : Rat) := by
  have hle := qabs_le_num_natAbs_succ x
  have hnat : x.num.natAbs + 1 < expPowerSeriesTerms x n + 1 := by
    unfold expPowerSeriesTerms
    omega
  have hlt : (((x.num.natAbs : Nat) : Rat) + 1) <
      ((expPowerSeriesTerms x n + 1 : Nat) : Rat) := by
    exact_mod_cast hnat
  grind

theorem expPowerSeries_ratio_bound (x : Rat) :
    PowerSeriesRatioBound x := by
  intro n
  unfold expPowerSeriesTailRatioBound
  let D : Nat := expPowerSeriesTerms x n + 1
  have hDposNat : 0 < D := by
    dsimp [D]
    omega
  have hDpos : (0 : Rat) < (D : Rat) :=
    (Rat.natCast_pos).2 hDposNat
  have hnum : qabs x < (D : Rat) := by
    dsimp [D]
    exact qabs_lt_expPowerSeriesTailDen x n
  rw [Rat.div_lt_iff hDpos]
  simpa [D] using hnum

/-- The term immediately following a finite exponential power-series prefix.
This private finite-state view is used to prove that the public boxes are
nested for every rational input, not only at the special value `x = 1`. -/
private def powerSeriesTermAtTerms (x : Rat) (terms : Nat) : Rat :=
  (powerSeriesState x terms).2

private def powerSeriesCenterAtTerms (x : Rat) (terms : Nat) : Rat :=
  (powerSeriesState x terms).1

private def powerSeriesTailRadiusAtTerms (x : Rat) (terms : Nat) : Rat :=
  qabs (powerSeriesTermAtTerms x terms) /
    (1 - qabs x / ((terms : Rat) + 1))

private theorem powerSeriesTermAtTerms_succ (x : Rat) (terms : Nat) :
    powerSeriesTermAtTerms x (terms + 1) =
      powerSeriesTermAtTerms x terms * x / ((terms : Rat) + 1) := by
  unfold powerSeriesTermAtTerms
  rw [powerSeriesState_succ]
  simp [powerSeriesLoopStep]

private theorem powerSeriesCenterAtTerms_succ (x : Rat) (terms : Nat) :
    powerSeriesCenterAtTerms x (terms + 1) =
      powerSeriesCenterAtTerms x terms + powerSeriesTermAtTerms x terms := by
  unfold powerSeriesCenterAtTerms powerSeriesTermAtTerms
  rw [powerSeriesState_succ]
  simp [powerSeriesLoopStep]

private theorem powerSeriesCenter_stage_eq (x : Rat) (n : Nat) :
    powerSeriesCenter x n =
      powerSeriesCenterAtTerms x (expPowerSeriesTerms x n) := by
  rw [expPowerSeries_center_eq_state]
  rfl

private theorem powerSeriesTailRadius_stage_eq (x : Rat) (n : Nat) :
    powerSeriesTailRadius x n =
      powerSeriesTailRadiusAtTerms x (expPowerSeriesTerms x n) := by
  rw [expPowerSeries_tailRadius_eq_state]
  have hcast : ((expPowerSeriesTerms x n + 1 : Nat) : Rat) =
      (expPowerSeriesTerms x n : Rat) + 1 := by
    exact_mod_cast (show expPowerSeriesTerms x n + 1 =
      expPowerSeriesTerms x n + 1 by rfl)
  unfold powerSeriesTailRadiusAtTerms powerSeriesTermAtTerms
    expPowerSeriesTailRatioBound
  rw [hcast]

private theorem powerSeriesTermAtTerms_abs_succ (x : Rat) (terms : Nat) :
    qabs (powerSeriesTermAtTerms x (terms + 1)) =
      qabs (powerSeriesTermAtTerms x terms) *
        (qabs x / ((terms : Rat) + 1)) := by
  rw [powerSeriesTermAtTerms_succ, Rat.div_def, qabs_mul, qabs_mul]
  have hdenpos : (0 : Rat) < (terms : Rat) + 1 := by
    exact_mod_cast Nat.succ_pos terms
  rw [qabs_eq_self_of_nonneg
    (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))]
  rw [Rat.div_def]
  rw [Rat.mul_assoc]

private theorem expPowerSeriesTerms_succ (x : Rat) (n : Nat) :
    expPowerSeriesTerms x (n + 1) = expPowerSeriesTerms x n + 1 := by
  unfold expPowerSeriesTerms
  omega

private theorem expPowerSeriesTermRatio_le_half_at_terms
    (x : Rat) (terms : Nat)
    (hterms : expPowerSeriesTerms x 0 <= terms) :
    qabs x / ((terms : Rat) + 1) <= (1 : Rat) / 2 := by
  have hqabs := qabs_le_num_natAbs_succ x
  have htermsNat : 2 * x.num.natAbs + 2 <= terms + 1 := by
    unfold expPowerSeriesTerms at hterms
    omega
  have htermsRat :
      ((2 * x.num.natAbs + 2 : Nat) : Rat) <= (terms : Rat) + 1 := by
    exact_mod_cast htermsNat
  have htwoPos : (0 : Rat) < 2 := by native_decide
  have hdenPos : (0 : Rat) < (terms : Rat) + 1 := by
    exact_mod_cast Nat.succ_pos terms
  have htwice : 2 * qabs x <= (terms : Rat) + 1 := by
    calc
      2 * qabs x <= 2 * (((x.num.natAbs : Nat) : Rat) + 1) :=
        Rat.mul_le_mul_of_nonneg_left hqabs (Rat.le_of_lt htwoPos)
      _ = ((2 * x.num.natAbs + 2 : Nat) : Rat) := by
        exact_mod_cast (by omega : 2 * (x.num.natAbs + 1) = 2 * x.num.natAbs + 2)
      _ <= (terms : Rat) + 1 := htermsRat
  apply Rat.le_of_mul_le_mul_right (c := 2 * ((terms : Rat) + 1))
  · rw [Rat.div_def, Rat.div_def]
    have htwoNe : (2 : Rat) ≠ 0 := Rat.ne_of_gt htwoPos
    have hdenNe : (terms : Rat) + 1 ≠ 0 := Rat.ne_of_gt hdenPos
    calc
      (qabs x * ((terms : Rat) + 1)⁻¹) *
          (2 * ((terms : Rat) + 1)) = 2 * qabs x := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (terms : Rat) + 1 := htwice
      _ = ((1 : Rat) * 2⁻¹) * (2 * ((terms : Rat) + 1)) := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos htwoPos hdenPos

/-- Dividing a nonnegative rational by a larger positive denominator can only
decrease it.  This deliberately finite rational lemma keeps the tail proof
independent of an ordered-field import. -/
private theorem rat_div_den_antitone {a d e : Rat}
    (ha : 0 <= a) (hd : 0 < d) (hde : d <= e) :
    a / e <= a / d := by
  have he : 0 < e := by grind
  have hdne : d ≠ 0 := Rat.ne_of_gt hd
  have hene : e ≠ 0 := Rat.ne_of_gt he
  apply Rat.le_of_mul_le_mul_right (c := d * e)
  · calc
      (a / e) * (d * e) = a * d := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= a * e := Rat.mul_le_mul_of_nonneg_left hde ha
      _ = (a / d) * (d * e) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos hd he

private theorem tail_radius_absorbs_next_term
    {T r s : Rat} (hT : 0 <= T) (hr0 : 0 <= r) (hr : r < 1)
    (hs : s < 1) (hsle : s <= r) :
    T <= T / (1 - r) - (T * r) / (1 - s) := by
  have hdenr : 0 < 1 - r := by grind [Rat.sub_eq_add_neg]
  have hdens : 0 < 1 - s := by grind [Rat.sub_eq_add_neg]
  have hdenle : 1 - r <= 1 - s := by grind [Rat.sub_eq_add_neg]
  have hinv : 1 / (1 - s) <= 1 / (1 - r) :=
    rat_div_den_antitone (a := 1) (d := 1 - r) (e := 1 - s)
      (by native_decide) hdenr hdenle
  have hTr0 : 0 <= T * r := Rat.mul_nonneg hT hr0
  have hnext : (T * r) / (1 - s) <= (T * r) / (1 - r) := by
    calc
      (T * r) / (1 - s) = (T * r) * (1 / (1 - s)) := by
        rw [Rat.div_def, Rat.div_def, Rat.one_mul]
      _ <= (T * r) * (1 / (1 - r)) :=
        Rat.mul_le_mul_of_nonneg_left hinv hTr0
      _ = (T * r) / (1 - r) := by
        rw [Rat.div_def, Rat.div_def, Rat.one_mul]
  have hsum : T + (T * r) / (1 - r) = T / (1 - r) := by
    have hdenne : 1 - r ≠ 0 := Rat.ne_of_gt hdenr
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel, Rat.inv_mul_cancel]
  have hbound : T + (T * r) / (1 - s) <= T / (1 - r) := by
    calc
      T + (T * r) / (1 - s) <= T + (T * r) / (1 - r) :=
        by grind
      _ = T / (1 - r) := hsum
  grind [Rat.sub_eq_add_neg]

private theorem powerSeriesAbsTerm_le_tailRadius_drop
    (x : Rat) (n : Nat) :
    qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x n)) <=
      powerSeriesTailRadiusAtTerms x (expPowerSeriesTerms x n) -
        powerSeriesTailRadiusAtTerms x (expPowerSeriesTerms x n + 1) := by
  let N : Nat := expPowerSeriesTerms x n
  let T : Rat := qabs (powerSeriesTermAtTerms x N)
  let a : Rat := qabs x
  have hN1 : 0 < (N : Rat) + 1 := by
    dsimp [N]
    exact_mod_cast Nat.succ_pos (expPowerSeriesTerms x n)
  have ha0 : 0 <= a := by
    dsimp [a]
    exact qabs_nonneg x
  have ha : a < (N : Rat) + 1 := by
    dsimp [a, N]
    have h := qabs_lt_expPowerSeriesTailDen x n
    have hcast : ((expPowerSeriesTerms x n + 1 : Nat) : Rat) =
        (expPowerSeriesTerms x n : Rat) + 1 := by
      exact_mod_cast (show expPowerSeriesTerms x n + 1 =
        expPowerSeriesTerms x n + 1 by rfl)
    rwa [hcast] at h
  have hT0 : 0 <= T := by
    dsimp [T]
    exact qabs_nonneg _
  let r : Rat := a / ((N : Rat) + 1)
  let s : Rat := a / ((N : Rat) + 2)
  have hN2 : 0 < (N : Rat) + 2 := by grind
  have hr0 : 0 <= r := by
    dsimp [r]
    rw [Rat.div_def]
    exact Rat.mul_nonneg ha0 (Rat.le_of_lt ((Rat.inv_pos).2 hN1))
  have hr : r < 1 := by
    dsimp [r]
    rw [Rat.div_lt_iff hN1]
    simpa using ha
  have ha2 : a < (N : Rat) + 2 := by grind
  have hs : s < 1 := by
    dsimp [s]
    rw [Rat.div_lt_iff hN2]
    simpa using ha2
  have hdenle : (N : Rat) + 1 <= (N : Rat) + 2 := by grind
  have hsle : s <= r := by
    dsimp [s, r]
    exact rat_div_den_antitone ha0 hN1 hdenle
  have htail := tail_radius_absorbs_next_term
    (T := T) (r := r) (s := s) hT0 hr0 hr hs hsle
  unfold powerSeriesTailRadiusAtTerms
  rw [powerSeriesTermAtTerms_abs_succ]
  have hsuccDen : (((N + 1 : Nat) : Rat)) + 1 = (N : Rat) + 2 := by
    exact_mod_cast (show N + 1 + 1 = N + 2 by omega)
  rw [hsuccDen]
  dsimp [T, a, r, s] at htail
  exact htail

/-- Every public exponential power-series box is nested in the preceding one.
The proof is entirely about finite rational partial sums and their certified
geometric tails. -/
theorem expPowerSeries_center_step_movement (x : Rat) :
    PowerSeriesCenterStepMovement x := by
  intro n
  let N : Nat := expPowerSeriesTerms x n
  have hNsucc : expPowerSeriesTerms x (n + 1) = N + 1 := by
    dsimp [N]
    exact expPowerSeriesTerms_succ x n
  have hcenter0 := powerSeriesCenter_stage_eq x n
  have hcenter1 := powerSeriesCenter_stage_eq x (n + 1)
  have hradius0 := powerSeriesTailRadius_stage_eq x n
  have hradius1 := powerSeriesTailRadius_stage_eq x (n + 1)
  have hcenterSucc :
      powerSeriesCenter x (n + 1) =
        powerSeriesCenter x n + powerSeriesTermAtTerms x N := by
    rw [hcenter0, hcenter1, hNsucc, powerSeriesCenterAtTerms_succ]
  have hdrop := powerSeriesAbsTerm_le_tailRadius_drop x n
  constructor
  · rw [hcenterSucc, hradius0, hradius1, hNsucc]
    have hterm := self_le_qabs (powerSeriesTermAtTerms x N)
    grind [Rat.sub_eq_add_neg]
  · rw [hcenterSucc, hradius0, hradius1, hNsucc]
    have hterm := neg_qabs_le_self (powerSeriesTermAtTerms x N)
    grind [Rat.sub_eq_add_neg]

private theorem expPowerSeriesTerms_zero_le (x : Rat) (n : Nat) :
    expPowerSeriesTerms x 0 <= expPowerSeriesTerms x n := by
  unfold expPowerSeriesTerms
  omega

/-- After its computable start, the magnitude of each newly omitted term is
bounded by a geometric sequence of ratio one half. -/
private theorem powerSeries_absTerm_stage_le_geometric (x : Rat) :
    forall n,
      qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x n)) <=
        qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x 0)) *
          ((1 : Rat) / 2) ^ n
  | 0 => by simp
  | n + 1 => by
      have hratio := expPowerSeriesTermRatio_le_half_at_terms x
        (expPowerSeriesTerms x n) (expPowerSeriesTerms_zero_le x n)
      rw [expPowerSeriesTerms_succ, powerSeriesTermAtTerms_abs_succ]
      calc
        qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x n)) *
            (qabs x / ((expPowerSeriesTerms x n : Rat) + 1)) <=
          qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x n)) *
            ((1 : Rat) / 2) :=
          Rat.mul_le_mul_of_nonneg_left hratio (qabs_nonneg _)
        _ <=
            (qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x 0)) *
              ((1 : Rat) / 2) ^ n) * ((1 : Rat) / 2) :=
          Rat.mul_le_mul_of_nonneg_right
            (powerSeries_absTerm_stage_le_geometric x n)
            (by native_decide : (0 : Rat) <= 1 / 2)
        _ =
            qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x 0)) *
              ((1 : Rat) / 2) ^ (n + 1) := by
          rw [Rat.pow_succ]
          grind [Rat.mul_assoc]

private theorem powerSeriesTailRadiusAtTerms_le_two_mul_absTerm
    (x : Rat) (terms : Nat)
    (hratio : qabs x / ((terms : Rat) + 1) <= (1 : Rat) / 2) :
    powerSeriesTailRadiusAtTerms x terms <=
      2 * qabs (powerSeriesTermAtTerms x terms) := by
  let T : Rat := qabs (powerSeriesTermAtTerms x terms)
  let r : Rat := qabs x / ((terms : Rat) + 1)
  have hT : 0 <= T := by
    dsimp [T]
    exact qabs_nonneg _
  have hr : r <= (1 : Rat) / 2 := by
    exact hratio
  have hden : 0 < 1 - r := by
    have hhalf : (1 : Rat) / 2 < 1 := by native_decide
    grind [Rat.sub_eq_add_neg]
  have hfactor : 1 <= 2 * (1 - r) := by
    have hhalf : (1 : Rat) / 2 <= 1 - r := by
      grind [Rat.sub_eq_add_neg]
    calc
      (1 : Rat) = 2 * ((1 : Rat) / 2) := by native_decide
      _ <= 2 * (1 - r) :=
        Rat.mul_le_mul_of_nonneg_left hhalf (by native_decide)
  apply Rat.le_of_mul_le_mul_right (c := 1 - r)
  · rw [powerSeriesTailRadiusAtTerms]
    dsimp [T, r]
    rw [Rat.div_def]
    have hdenne : 1 - qabs x / ((terms : Rat) + 1) ≠ 0 := by
      dsimp [r] at hden
      exact Rat.ne_of_gt hden
    calc
      qabs (powerSeriesTermAtTerms x terms) *
          (1 - qabs x / ((terms : Rat) + 1))⁻¹ *
            (1 - qabs x / ((terms : Rat) + 1)) =
          qabs (powerSeriesTermAtTerms x terms) := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= qabs (powerSeriesTermAtTerms x terms) *
          (2 * (1 - qabs x / ((terms : Rat) + 1))) := by
        dsimp [T, r] at hfactor
        simpa using
          Rat.mul_le_mul_of_nonneg_left hfactor (qabs_nonneg _)
      _ = (2 * qabs (powerSeriesTermAtTerms x terms)) *
          (1 - qabs x / ((terms : Rat) + 1)) := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hden

private theorem powerSeriesTailRadius_stage_le_two_mul_absTerm
    (x : Rat) (n : Nat) :
    powerSeriesTailRadius x n <=
      2 * qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x n)) := by
  rw [powerSeriesTailRadius_stage_eq]
  exact powerSeriesTailRadiusAtTerms_le_two_mul_absTerm x
    (expPowerSeriesTerms x n)
    (expPowerSeriesTermRatio_le_half_at_terms x
      (expPowerSeriesTerms x n) (expPowerSeriesTerms_zero_le x n))

private theorem rat_pow_add (q : Rat) (m n : Nat) :
    q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show m + (n + 1) = m + n + 1 by omega]
      rw [Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem half_pow_antitone_at_or_after (N n : Nat) (hN : N <= n) :
    ((1 : Rat) / 2) ^ n <= ((1 : Rat) / 2) ^ N := by
  let k := n - N
  have hNk : N + k = n := by
    dsimp [k]
    exact Nat.add_sub_of_le hN
  rw [← hNk, rat_pow_add]
  have hhalf0 : (0 : Rat) <= 1 / 2 := by native_decide
  have hhalf1 : (1 : Rat) / 2 <= 1 := by native_decide
  have hpow0 : 0 <= ((1 : Rat) / 2) ^ N := Rat.pow_nonneg hhalf0
  have hpow1 : ((1 : Rat) / 2) ^ k <= 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Rat.pow_succ]
        calc
          ((1 : Rat) / 2) ^ k * ((1 : Rat) / 2) <=
              ((1 : Rat) / 2) ^ k * 1 :=
            Rat.mul_le_mul_of_nonneg_left hhalf1
              (Rat.pow_nonneg hhalf0)
          _ = ((1 : Rat) / 2) ^ k := by rw [Rat.mul_one]
          _ <= 1 := ih
  calc
    ((1 : Rat) / 2) ^ N * ((1 : Rat) / 2) ^ k <=
        ((1 : Rat) / 2) ^ N * 1 :=
      Rat.mul_le_mul_of_nonneg_left hpow1 hpow0
    _ = ((1 : Rat) / 2) ^ N := by rw [Rat.mul_one]

private theorem expPowerSeries_width_le_geometric (x : Rat) (n : Nat) :
    ((expPowerSeries x).compute n).width <=
      (4 * qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x 0))) *
        ((1 : Rat) / 2) ^ n := by
  have hrad := powerSeriesTailRadius_stage_le_two_mul_absTerm x n
  have hterm := powerSeries_absTerm_stage_le_geometric x n
  rw [expPowerSeries_width_eq]
  calc
    powerSeriesTailRadius x n + powerSeriesTailRadius x n <=
        2 * qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x n)) +
          2 * qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x n)) := by
      grind
    _ = 4 * qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x n)) := by
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc]
    _ <= 4 *
          (qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x 0)) *
            ((1 : Rat) / 2) ^ n) :=
      Rat.mul_le_mul_of_nonneg_left hterm (by native_decide)
    _ = (4 * qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x 0))) *
          ((1 : Rat) / 2) ^ n := by
      grind [Rat.mul_assoc]

/-- The finite exponential power-series evaluator has an executable width
modulus at every rational input. -/
theorem expPowerSeries_widths_shrink (x : Rat) :
    PowerSeriesWidthsShrink x := by
  unfold PowerSeriesWidthsShrink RealRaw.WidthsShrinkToZero
  intro eps
  let bound : Rat :=
    4 * qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x 0))
  let N : Nat := RationalMajorant.halfDecayShift bound eps
  refine ⟨N, ?_⟩
  intro n hn
  have hbound0 : 0 <= bound := by
    dsimp [bound]
    exact Rat.mul_nonneg (by native_decide) (qabs_nonneg _)
  have hwidth := expPowerSeries_width_le_geometric x n
  have hpow := half_pow_antitone_at_or_after N n hn
  have hscaled : bound * ((1 : Rat) / 2) ^ n <=
      bound * ((1 : Rat) / 2) ^ N :=
    Rat.mul_le_mul_of_nonneg_left hpow hbound0
  have hfinal := RationalMajorant.halfDecayShift_spec hbound0 eps
  dsimp [N] at hpow hscaled hfinal ⊢
  dsimp [bound] at hwidth hscaled hfinal
  exact Rat.le_trans hwidth (Rat.le_trans hscaled hfinal)

theorem ePowerSeries_ratio_bound : EPowerSeriesRatioBound := by
  simpa [EPowerSeriesRatioBound] using expPowerSeries_ratio_bound (1 : Rat)

theorem expPowerSeries_tailRadius_nonneg (x : Rat) (n : Nat) :
    0 <= powerSeriesTailRadius x n :=
  powerSeriesTailRadius_nonneg_of_ratioBound
    x (expPowerSeries_ratio_bound x) n

theorem expPowerSeries_intervals_ordered (x : Rat) :
    forall n, 0 <= ((expPowerSeries x).compute n).width := by
  intro n
  exact expPowerSeries_ordered x (expPowerSeries_ratio_bound x) n

theorem ePowerSeries_tailRadius_nonneg (n : Nat) :
    0 <= powerSeriesTailRadius (1 : Rat) n :=
  expPowerSeries_tailRadius_nonneg (1 : Rat) n

theorem ePowerSeries_ordered :
    forall n, 0 <= (ePowerSeries.compute n).width := by
  intro n
  simpa [ePowerSeries] using
    expPowerSeries_intervals_ordered (1 : Rat) n

theorem expPowerSeries_valid_of_nested_and_shrinking_autoRatio
    (x : Rat) (hnested : PowerSeriesNested x)
    (hshrink : PowerSeriesWidthsShrink x) : PowerSeriesValid x :=
  expPowerSeries_valid_of_nested_and_shrinking
    x (expPowerSeries_ratio_bound x) hnested hshrink

theorem powerSeriesNested_of_centerMovement_autoRatio
    (x : Rat) (hmove : PowerSeriesCenterMovement x) :
    PowerSeriesNested x :=
  powerSeriesNested_of_centerMovement x (expPowerSeries_ratio_bound x) hmove

/-- Explicit geometric convergence metadata for the rational-input
exponential power-series evaluator. -/
def expPowerSeriesRate (x : Rat) :
    RealRaw.Rate (expPowerSeries x).compute :=
  .geometric 0
    (4 * qabs (powerSeriesTermAtTerms x (expPowerSeriesTerms x 0)))
    ((1 : Rat) / 2)
    (by native_decide)
    (by native_decide)
    (fun n _ => expPowerSeries_width_le_geometric x n)

/-- The literal finite power-series evaluator for `exp x` is a valid raw real
for every rational input.  Its proof uses only rational interval arithmetic,
finite sums, and the executable half-ratio tail bound. -/
theorem expPowerSeries_valid (x : Rat) : PowerSeriesValid x :=
  expPowerSeries_valid_of_nested_and_shrinking_autoRatio x
    (powerSeriesNested_of_centerMovement_autoRatio x
      (powerSeriesCenterMovement_of_stepMovement
        (expPowerSeries_center_step_movement x)))
    (expPowerSeries_widths_shrink x)

/-- The exact zero-input series computation is therefore a valid raw real,
in addition to being stagewise equal to the rational constant one. -/
theorem expPowerSeries_zero_valid : (expPowerSeries (0 : Rat)).Valid := by
  simpa [PowerSeriesValid] using expPowerSeries_valid (0 : Rat)

theorem ePowerSeries_valid_of_nested
    (hnested : EPowerSeriesNested)
    (hshrink : EPowerSeriesWidthsShrink) : EPowerSeriesValid := by
  simpa [EPowerSeriesValid, EPowerSeriesNested, ePowerSeries] using
    expPowerSeries_valid_of_nested_and_shrinking_autoRatio
      (1 : Rat) hnested hshrink

theorem eEuler_valid_of_nested
    (hnested : EEulerNested) : EEulerValid := by
  simpa [EEulerValid, EEulerNested, eEuler] using
    expEuler_valid_of_nested 1 hnested

theorem ePowerSeries_valid_of_centerMovement
    (hmove : EPowerSeriesCenterMovement)
    (hshrink : EPowerSeriesWidthsShrink) : EPowerSeriesValid :=
  ePowerSeries_valid_of_nested
    (powerSeriesNested_of_centerMovement_autoRatio (1 : Rat) hmove)
    hshrink

theorem eEuler_valid_of_centerMovement
    (hmove : EEulerCenterMovement) : EEulerValid :=
  eEuler_valid_of_nested
    (eulerNested_of_centerMovement 1 hmove)

theorem ePowerSeries_valid_of_centerStepMovement
    (hstep : EPowerSeriesCenterStepMovement)
    (hshrink : EPowerSeriesWidthsShrink) : EPowerSeriesValid :=
  ePowerSeries_valid_of_centerMovement
    (powerSeriesCenterMovement_of_stepMovement hstep)
    hshrink

theorem ePowerSeries_valid : EPowerSeriesValid :=
  ePowerSeries_valid_of_centerStepMovement
    ePowerSeries_center_step_movement
    ePowerSeries_widths_shrink

/-- The factorial-series and compound-interest computations of `e` are now
directly equivalent through the nested repeated-multiplication bridge. -/
theorem ePowerSeries_equiv_eCompoundInterest :
    EPowerSeriesEqCompoundInterest :=
  RealRaw.equiv_trans
    ePowerSeries_valid
    eEulerNested_valid
    eCompoundInterest_valid
    ePowerSeries_equiv_eEulerNested
    eEulerNested_equiv_eCompoundInterest

/-- The abstract Euler-base handle now lists all three certified finite
computations: compound-interest intervals, nested repeated multiplication,
and the factorial power series. -/
def eCertified : Real :=
  ((Real.withAlternative
    (Real.ofRaw eCompoundInterest eCompoundInterest_valid)
    eEulerNested eEulerNested_valid
    eEulerNested_equiv_eCompoundInterest).withAlternative
      eEulerStabilized eEulerStabilized_valid
      eEulerStabilized_equiv_eCompoundInterest).withAlternative
        ePowerSeries ePowerSeries_valid
        ePowerSeries_equiv_eCompoundInterest

abbrev e : Real := eCertified

theorem eEulerNested_mem_eCertified_alternatives :
    eEulerNested ∈ eCertified.alternatives := by
  simp [eCertified, Real.withAlternative]

theorem eEulerStabilized_mem_eCertified_alternatives :
    eEulerStabilized ∈ eCertified.alternatives := by
  simp [eCertified, Real.withAlternative]

theorem ePowerSeries_mem_eCertified_alternatives :
    ePowerSeries ∈ eCertified.alternatives := by
  simp [eCertified, Real.withAlternative]

/-- The preferred compound-interest view of the abstract `e` handle. -/
def eCompoundInterestRepresentation : Real.Representation e :=
  Real.preferredRepresentation eCertified

def eRepeatedMultiplicationRepresentation : Real.Representation e where
  raw := eEulerNested
  valid := eEulerNested_valid
  agrees := eEulerNested_equiv_eCompoundInterest

def eRepeatedMultiplicationStabilizedRepresentation : Real.Representation e where
  raw := eEulerStabilized
  valid := eEulerStabilized_valid
  agrees := eEulerStabilized_equiv_eCompoundInterest

/-- The certified factorial-series view of the same abstract Euler base. -/
def ePowerSeriesRepresentation : Real.Representation e where
  raw := ePowerSeries
  valid := ePowerSeries_valid
  agrees := ePowerSeries_equiv_eCompoundInterest

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

theorem ePowerSeries_eq_eCompoundInterest_of_complete
    (proofs : ExpProofsComplete) :
    EPowerSeriesEqCompoundInterest :=
  RealRaw.equiv_trans
    proofs.powerSeries_valid
    proofs.euler_valid
    eCompoundInterest_valid
    proofs.powerSeries_eq_euler
    eEuler_eq_eCompoundInterest

theorem complete_of_remainders
    (remainders : ExpProofRemainders) : ExpProofsComplete where
  powerSeries_valid :=
    ePowerSeries_valid_of_centerStepMovement
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