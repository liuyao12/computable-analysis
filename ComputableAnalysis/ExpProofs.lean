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
