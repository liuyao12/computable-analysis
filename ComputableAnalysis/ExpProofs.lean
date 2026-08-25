import ComputableAnalysis.Exp
import ComputableAnalysis.FTC
import ComputableAnalysis.ElementaryFunctions
import ComputableAnalysis.FinitePolynomialCalculus
import ComputableAnalysis.FiniteInverseSearchInterface

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

This is a literal rational loop state.  It is public so that finite Taylor
algebra can be related to the evaluator without making a convergence or
derivative claim. -/
def powerSeriesTermAtTerms (x : Rat) (terms : Nat) : Rat :=
  (powerSeriesState x terms).2

/-- The finite partial-sum coordinate of the factorial-series loop. -/
def powerSeriesCenterAtTerms (x : Rat) (terms : Nat) : Rat :=
  (powerSeriesState x terms).1

private def powerSeriesTailRadiusAtTerms (x : Rat) (terms : Nat) : Rat :=
  qabs (powerSeriesTermAtTerms x terms) /
    (1 - qabs x / ((terms : Rat) + 1))

theorem powerSeriesTermAtTerms_succ (x : Rat) (terms : Nat) :
    powerSeriesTermAtTerms x (terms + 1) =
      powerSeriesTermAtTerms x terms * x / ((terms : Rat) + 1) := by
  unfold powerSeriesTermAtTerms
  rw [powerSeriesState_succ]
  simp [powerSeriesLoopStep]

theorem powerSeriesCenterAtTerms_succ (x : Rat) (terms : Nat) :
    powerSeriesCenterAtTerms x (terms + 1) =
      powerSeriesCenterAtTerms x terms + powerSeriesTermAtTerms x terms := by
  unfold powerSeriesCenterAtTerms powerSeriesTermAtTerms
  rw [powerSeriesState_succ]
  simp [powerSeriesLoopStep]

/-- Each finite loop term is exactly the corresponding factorial Taylor
monomial.  This is an identity in rational arithmetic. -/
theorem powerSeriesTermAtTerms_eq_expCoeff_monomial (x : Rat) :
    forall terms : Nat,
      powerSeriesTermAtTerms x terms =
        FormalPowerSeries.expCoeff terms * x ^ terms
  | 0 => by
      simp [powerSeriesTermAtTerms, powerSeriesState,
        FormalPowerSeries.expCoeff, factorialRat, factorial]
      native_decide
  | terms + 1 => by
      rw [powerSeriesTermAtTerms_succ,
        powerSeriesTermAtTerms_eq_expCoeff_monomial]
      unfold FormalPowerSeries.expCoeff
      rw [Rat.pow_succ, FormalPowerSeries.factorialRat_succ,
        Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem expCoeff_succ_monomial (x : Rat) (terms : Nat) :
    FormalPowerSeries.expCoeff (terms + 1) * x ^ (terms + 1) =
      FormalPowerSeries.expCoeff terms *
        (x ^ (terms + 1) / ((terms + 1 : Nat) : Rat)) := by
  unfold FormalPowerSeries.expCoeff
  rw [FormalPowerSeries.factorialRat_succ,
    Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The executable finite factorial-series sum is the finite Taylor prefix
with the same coefficients.  It is intentionally a finite identity: the
separately certified tail remains responsible for the raw-real evaluator. -/
theorem powerSeriesCenterAtTerms_eq_expTaylorPrefix (x : Rat) :
    forall terms : Nat,
      powerSeriesCenterAtTerms x (terms + 1) =
        FinitePolynomial.expTaylorPrefix terms x
  | 0 => by
      simp [powerSeriesCenterAtTerms, powerSeriesState, powerSeriesLoopStep,
        FinitePolynomial.expTaylorPrefix,
        FinitePolynomial.integratedTaylorPrefix]
      native_decide
  | terms + 1 => by
      rw [powerSeriesCenterAtTerms_succ,
        powerSeriesCenterAtTerms_eq_expTaylorPrefix,
        powerSeriesTermAtTerms_eq_expCoeff_monomial,
        expCoeff_succ_monomial]
      simp only [FinitePolynomial.expTaylorPrefix,
        FinitePolynomial.integratedTaylorPrefix]
      grind [Rat.add_assoc]

/-- The finite derivative polynomial of the factorial prefix is exactly the
preceding finite factorial center.  This is a finite identity; it prepares the
comparison of the Taylor secant polynomial with the common raw tail box. -/
theorem expTaylorDerivativePrefix_eq_powerSeriesCenterAtTerms (x : Rat) :
    forall terms : Nat,
      FinitePolynomial.expTaylorDerivativePrefix terms x =
        powerSeriesCenterAtTerms x terms
  | 0 => by
      simp [FinitePolynomial.expTaylorDerivativePrefix,
        FinitePolynomial.taylorDerivativePrefix,
        powerSeriesCenterAtTerms, powerSeriesState]
  | terms + 1 => by
      rw [show FinitePolynomial.expTaylorDerivativePrefix (terms + 1) x =
          FinitePolynomial.taylorDerivativePrefix FormalPowerSeries.expCoeff terms x +
            FormalPowerSeries.expCoeff terms * x ^ terms by
            rfl]
      change FinitePolynomial.expTaylorDerivativePrefix terms x +
          FormalPowerSeries.expCoeff terms * x ^ terms =
        powerSeriesCenterAtTerms x (terms + 1)
      rw [expTaylorDerivativePrefix_eq_powerSeriesCenterAtTerms]
      rw [powerSeriesCenterAtTerms_succ,
        powerSeriesTermAtTerms_eq_expCoeff_monomial]

/-!
## A uniform bounded-input exponential schedule

The ordinary power-series evaluator chooses its factorial start from the
particular rational input.  For a difference quotient, the two inputs `x`
and `x + h` must instead share one finite prefix and one tail budget.  The
following raw evaluator fixes the majorant at `2`; it is the rational
building block for the later self-derivative certificate on any subinterval
of `[-2,2]`.
-/

/-- The common factorial start for every real input with absolute value at
most two. -/
def uniformExpTailStart : Nat :=
  RationalMajorant.factorialTailStart 2

/-- The finite number of factorial terms used by the common stage. -/
def uniformExpTailTerms (n : Nat) : Nat :=
  uniformExpTailStart + n

/-- The scalar factorial majorant at the common stage. -/
def uniformExpTailMagnitude (n : Nat) : Rat :=
  RationalMajorant.factorialTailTerm 2 (uniformExpTailTerms n)

/-- Twice the omitted-term majorant.  The factor two absorbs the finite
center update and makes the literal rational boxes nested. -/
def uniformExpTailRadius (n : Nat) : Rat :=
  2 * uniformExpTailMagnitude n

/-- The finite factorial prefix attached to the common bounded-input stage. -/
def uniformExpCenter (x : Rat) (n : Nat) : Rat :=
  powerSeriesCenterAtTerms x (uniformExpTailTerms n)

/-! A symmetric-input bound for the finite center.  Unlike the monotonicity
lemma below, this uses only a finite absolute-value majorant, so it remains
available on negative inputs. -/

theorem uniformExpCenter_qabs_le (x : Rat) (hx : qabs x <= 2) (n : Nat) :
    qabs (uniformExpCenter x n) <=
      1 + RationalMajorant.factorialTailPartial 2 1
        (uniformExpTailTerms n - 1) := by
  have hstart : 1 <= uniformExpTailStart := by
    unfold uniformExpTailStart
    native_decide
  have hterms : uniformExpTailTerms n =
      (uniformExpTailTerms n - 1) + 1 := by
    unfold uniformExpTailTerms
    omega
  rw [uniformExpCenter, hterms,
    powerSeriesCenterAtTerms_eq_expTaylorPrefix]
  unfold FinitePolynomial.expTaylorPrefix
  have hprefix := FinitePolynomial.qabs_integratedExpTaylorPrefix_le
    (C := (2 : Rat)) (x := x) (by native_decide) hx
      (uniformExpTailTerms n - 1)
  calc
    qabs (1 +
        FinitePolynomial.integratedTaylorPrefix
          FormalPowerSeries.expCoeff (uniformExpTailTerms n - 1) x) <=
        qabs (1 : Rat) +
          qabs (FinitePolynomial.integratedTaylorPrefix
            FormalPowerSeries.expCoeff (uniformExpTailTerms n - 1) x) :=
      qabs_add_le _ _
    _ <= 1 + RationalMajorant.factorialTailPartial 2 1
        (uniformExpTailTerms n - 1) := by
      rw [qabs_eq_self_of_nonneg (by native_decide)]
      exact rat_add_le_add (by native_decide) hprefix

theorem uniformExpCenter_qabs_le_nine (x : Rat) (hx : qabs x <= 2)
    (n : Nat) : qabs (uniformExpCenter x n) <= 9 := by
  have hbound := uniformExpCenter_qabs_le x hx n
  have hstart : 1 <= uniformExpTailStart := by
    unfold uniformExpTailStart
    native_decide
  have hterms : uniformExpTailTerms n =
      (uniformExpTailTerms n - 1) + 1 := by
    unfold uniformExpTailTerms
    omega
  have hsplit := RationalMajorant.factorialTailPartial_add
    (2 : Rat) 0 1 (uniformExpTailTerms n - 1)
  have hsplit' :
      RationalMajorant.factorialTailPartial 2 0
          (uniformExpTailTerms n) =
        RationalMajorant.factorialTailPartial 2 0 1 +
          RationalMajorant.factorialTailPartial 2 1
            (uniformExpTailTerms n - 1) := by
    rw [hterms]
    simpa [Nat.add_comm] using hsplit
  have hpartial :
      RationalMajorant.factorialTailPartial 2 1
        (uniformExpTailTerms n - 1) <= 8 := by
    have hzero : RationalMajorant.factorialTailPartial 2 0 1 = 1 := by
      native_decide
    have htotal :
        RationalMajorant.factorialTailPartial 2 0
            (uniformExpTailTerms n) <= 8 := by
      exact RationalMajorant.factorialTailPartial_two_le_eight _
    have hnonneg : forall k,
        0 <= RationalMajorant.factorialTailPartial 2 1 k := by
      intro k
      induction k with
      | zero => simp [RationalMajorant.factorialTailPartial]
      | succ k ih =>
          rw [RationalMajorant.factorialTailPartial]
          exact Rat.add_nonneg ih
            (RationalMajorant.factorialTailTerm_nonneg (by native_decide) _)
    rw [hsplit', hzero] at htotal
    grind [hnonneg (uniformExpTailTerms n - 1)]
  calc
    qabs (uniformExpCenter x n) <=
        1 + RationalMajorant.factorialTailPartial 2 1
          (uniformExpTailTerms n - 1) := hbound
    _ <= 1 + 8 := by
      grind
    _ = 9 := by native_decide

theorem uniformExpCenter_mono_on_unit
    (n : Nat) {x y : Rat}
    (hx : 0 <= x) (hy : y <= 1) (hxy : x <= y) :
    uniformExpCenter x n <= uniformExpCenter y n := by
  have hterms : uniformExpTailTerms n =
      (uniformExpTailTerms n - 1) + 1 := by
    have hstart : 1 <= uniformExpTailStart := by native_decide
    unfold uniformExpTailTerms
    omega
  have hback : uniformExpTailTerms n - 1 + 1 - 1 =
      uniformExpTailTerms n - 1 := by omega
  have hcenter_x :
      powerSeriesCenterAtTerms x (uniformExpTailTerms n) =
        FinitePolynomial.expTaylorPrefix
          (uniformExpTailTerms n - 1) x := by
    rw [hterms, powerSeriesCenterAtTerms_eq_expTaylorPrefix, hback]
  have hcenter_y :
      powerSeriesCenterAtTerms y (uniformExpTailTerms n) =
        FinitePolynomial.expTaylorPrefix
          (uniformExpTailTerms n - 1) y := by
    rw [hterms, powerSeriesCenterAtTerms_eq_expTaylorPrefix, hback]
  change powerSeriesCenterAtTerms x (uniformExpTailTerms n) <=
    powerSeriesCenterAtTerms y (uniformExpTailTerms n)
  rw [hcenter_x, hcenter_y]
  exact FinitePolynomial.expTaylorPrefix_mono_on_unit
    (uniformExpTailTerms n - 1) hx hy hxy

/-! The finite exponential center does not become flatter than the identity
on the unit interval.  This is the quantitative separation fact needed by
the inverse algorithm; it is proved from the positive finite prefix, before
any limiting or completeness argument is invoked. -/
set_option maxHeartbeats 1200000 in
theorem uniformExpCenter_difference_ge_input
    (n : Nat) {x y : Rat}
    (hx : 0 <= x) (hy : y <= 1) (hxy : x <= y) :
    y - x <= uniformExpCenter y n - uniformExpCenter x n := by
  have hterms : uniformExpTailTerms n =
      (uniformExpTailTerms n - 1) + 1 := by
    have hstart : 1 <= uniformExpTailStart := by
      unfold uniformExpTailStart
      native_decide
    unfold uniformExpTailTerms
    omega
  have hback : uniformExpTailTerms n - 1 + 1 - 1 =
      uniformExpTailTerms n - 1 := by omega
  have hcenter_x :
      uniformExpCenter x n =
        FinitePolynomial.expTaylorPrefix
          (uniformExpTailTerms n - 1) x := by
    unfold uniformExpCenter
    rw [hterms, powerSeriesCenterAtTerms_eq_expTaylorPrefix, hback]
  have hcenter_y :
      uniformExpCenter y n =
        FinitePolynomial.expTaylorPrefix
          (uniformExpTailTerms n - 1) y := by
    unfold uniformExpCenter
    rw [hterms, powerSeriesCenterAtTerms_eq_expTaylorPrefix, hback]
  have hcoeff : forall k, 0 <= FormalPowerSeries.expCoeff k := by
    intro k
    unfold FormalPowerSeries.expCoeff
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2
      (RationalMajorant.factorialRat_pos k))
  have hzero : 1 <= FormalPowerSeries.expCoeff 0 := by
    unfold FormalPowerSeries.expCoeff
    native_decide
  have hterms_two : 1 <= uniformExpTailTerms n - 1 := by
    have hstart : 2 <= uniformExpTailStart := by
      unfold uniformExpTailStart
      native_decide
    unfold uniformExpTailTerms
    omega
  have hprefix_index : uniformExpTailTerms n - 1 =
      (uniformExpTailTerms n - 1 - 1) + 1 := by omega
  rw [hcenter_x, hcenter_y]
  have hprefix :=
    FinitePolynomial.integratedTaylorPrefix_succ_difference_ge
      (coeffs := FormalPowerSeries.expCoeff)
      (hcoeff := hcoeff) (hzero := hzero)
      (n := uniformExpTailTerms n - 1 - 1) hx hy hxy
  unfold FinitePolynomial.expTaylorPrefix
  rw [hprefix_index]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem uniformExpCenter_one_le_three (n : Nat) :
    uniformExpCenter 1 n <= (3 : Rat) := by
  change ePowerSeriesCenterAtTerms (uniformExpTailTerms n) <= (3 : Rat)
  have hstart : 0 < uniformExpTailStart := by
    unfold uniformExpTailStart
    native_decide
  exact ePowerSeries_centerAtTerms_le_three _ (by
    unfold uniformExpTailTerms
    omega)

private theorem uniformExpCenter_zero (n : Nat) :
    uniformExpCenter 0 n = (1 : Rat) := by
  unfold uniformExpCenter
  have hterms : uniformExpTailTerms n =
      (uniformExpTailTerms n - 1) + 1 := by
    have hstart : 1 <= uniformExpTailStart := by
      unfold uniformExpTailStart
      native_decide
    unfold uniformExpTailTerms
    omega
  rw [hterms, powerSeriesCenterAtTerms_eq_expTaylorPrefix]
  unfold FinitePolynomial.expTaylorPrefix
  have hzero : forall m,
      FinitePolynomial.integratedTaylorPrefix
          FormalPowerSeries.expCoeff m 0 = 0 := by
    intro m
    induction m with
    | zero => simp [FinitePolynomial.integratedTaylorPrefix]
    | succ m ih =>
        have hpow : 0 ^ (m + 1) = (0 : Rat) := by
          induction m with
          | zero => native_decide
          | succ m ihm => simp [Rat.pow_succ, ihm]
        change FinitePolynomial.integratedTaylorPrefix
            FormalPowerSeries.expCoeff m 0 +
          FormalPowerSeries.expCoeff m *
            (0 ^ (m + 1) / ((m + 1 : Nat) : Rat)) = 0
        rw [ih, hpow, Rat.div_def, Rat.zero_mul,
          Rat.mul_zero, Rat.zero_add]
  rw [hzero]
  grind

theorem uniformExpCenter_nonneg_on_unit
    (n : Nat) {x : Rat} (hx : 0 <= x) (hx1 : x <= 1) :
    0 <= uniformExpCenter x n := by
  have hmono := uniformExpCenter_mono_on_unit n (x := 0) (y := x)
    (by native_decide) hx1 hx
  rw [uniformExpCenter_zero] at hmono
  grind

theorem uniformExpCenter_le_three_on_unit
    (n : Nat) {x : Rat} (hx : 0 <= x) (hx1 : x <= 1) :
    uniformExpCenter x n <= (3 : Rat) := by
  have hmono : uniformExpCenter x n <= uniformExpCenter 1 n :=
    uniformExpCenter_mono_on_unit n hx (by native_decide) hx1
  calc
    uniformExpCenter x n <= uniformExpCenter 1 n := hmono
    _ <= (3 : Rat) := uniformExpCenter_one_le_three n

/-- A symmetric rational box around the common finite exponential prefix. -/
def uniformExpBox (x : Rat) (n : Nat) : QInterval :=
  intervalAround (uniformExpCenter x n) (uniformExpTailRadius n)

def uniformExpCellRange (a b : Rat) (n : Nat) : QInterval :=
  { lo := uniformExpCenter a n - uniformExpTailRadius n,
    hi := uniformExpCenter b n + uniformExpTailRadius n }

theorem uniformExpCellRange_width (a b : Rat) (n : Nat) :
    (uniformExpCellRange a b n).width =
      uniformExpCenter b n - uniformExpCenter a n +
        2 * uniformExpTailRadius n := by
  unfold uniformExpCellRange QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem uniformExpBox_contains_cellRange
    (n : Nat) {a b x : Rat}
    (ha : 0 <= a) (hb : b <= 1)
    (hax : a <= x) (hxb : x <= b) :
    (uniformExpCellRange a b n).ContainsInterval
      (uniformExpBox x n) := by
  have hleft := uniformExpCenter_mono_on_unit n ha (by
    exact Rat.le_trans hxb hb) hax
  have hright := uniformExpCenter_mono_on_unit n (by
    exact Rat.le_trans ha hax) hb hxb
  unfold uniformExpCellRange uniformExpBox intervalAround
    QInterval.ContainsInterval
  constructor <;> grind

private theorem uniform_exp_tail_start (n : Nat) :
    (2 : Rat) <= (((uniformExpTailTerms n + 1 : Nat) : Rat) / 2) := by
  simpa [uniformExpTailTerms, uniformExpTailStart] using
    RationalMajorant.factorialTailStart_mono (2 : Rat)
      (RationalMajorant.factorialTailStart 2) n
      (RationalMajorant.factorialTailStart_satisfies (2 : Rat))

private theorem uniformExpTailMagnitude_nonneg (n : Nat) :
    0 <= uniformExpTailMagnitude n := by
  unfold uniformExpTailMagnitude
  exact RationalMajorant.factorialTailTerm_nonneg (by native_decide) _

private theorem uniformExpTailMagnitude_next_le_half (n : Nat) :
    uniformExpTailMagnitude (n + 1) <=
      uniformExpTailMagnitude n * ((1 : Rat) / 2) := by
  have h := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := (2 : Rat)) (N := uniformExpTailTerms n)
    (by native_decide) (uniform_exp_tail_start n) 1
  change RationalMajorant.factorialTailTerm 2 (uniformExpTailTerms (n + 1)) <=
      RationalMajorant.factorialTailTerm 2 (uniformExpTailTerms n) *
        ((1 : Rat) / 2)
  have hterms : uniformExpTailTerms (n + 1) = uniformExpTailTerms n + 1 := by
    unfold uniformExpTailTerms
    omega
  rw [hterms]
  simpa using h

private theorem uniformExpTailRadius_drop_majorizes (n : Nat) :
    uniformExpTailMagnitude n <=
      uniformExpTailRadius n - uniformExpTailRadius (n + 1) := by
  have hnext := uniformExpTailMagnitude_next_le_half n
  unfold uniformExpTailRadius
  have hrewrite : (2 : Rat) * (uniformExpTailMagnitude n * ((1 : Rat) / 2)) =
      uniformExpTailMagnitude n := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  have htwice : 2 * uniformExpTailMagnitude (n + 1) <=
      uniformExpTailMagnitude n := by
    calc
      2 * uniformExpTailMagnitude (n + 1) <=
          2 * (uniformExpTailMagnitude n * ((1 : Rat) / 2)) :=
        Rat.mul_le_mul_of_nonneg_left hnext (by native_decide)
      _ = uniformExpTailMagnitude n := hrewrite
  calc
    uniformExpTailMagnitude n =
        2 * uniformExpTailMagnitude n - uniformExpTailMagnitude n := by
          grind [Rat.sub_eq_add_neg]
    _ <= 2 * uniformExpTailMagnitude n -
        2 * uniformExpTailMagnitude (n + 1) :=
      by grind [Rat.sub_eq_add_neg]

private theorem uniformExpCenter_step_qabs_le (x : Rat)
    (hx : qabs x <= 2) (n : Nat) :
    qabs (uniformExpCenter x (n + 1) - uniformExpCenter x n) <=
      uniformExpTailMagnitude n := by
  have hterms : uniformExpTailTerms (n + 1) = uniformExpTailTerms n + 1 := by
    unfold uniformExpTailTerms
    omega
  rw [uniformExpCenter, uniformExpCenter, hterms,
    powerSeriesCenterAtTerms_succ]
  have hcancel :
      powerSeriesCenterAtTerms x (uniformExpTailTerms n) +
          powerSeriesTermAtTerms x (uniformExpTailTerms n) -
        powerSeriesCenterAtTerms x (uniformExpTailTerms n) =
      powerSeriesTermAtTerms x (uniformExpTailTerms n) := by
    grind [Rat.sub_eq_add_neg]
  have hterm := FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm
    (C := (2 : Rat)) (x := x) (by native_decide) hx (uniformExpTailTerms n)
  rw [hcancel, powerSeriesTermAtTerms_eq_expCoeff_monomial]
  simpa [uniformExpTailMagnitude] using hterm

theorem uniformExpCenter_step_bounds (x : Rat)
    (hx : qabs x <= 2) (n : Nat) :
    -uniformExpTailMagnitude n <=
      uniformExpCenter x (n + 1) - uniformExpCenter x n /\
    uniformExpCenter x (n + 1) - uniformExpCenter x n <=
      uniformExpTailMagnitude n := by
  have h := uniformExpCenter_step_qabs_le x hx n
  exact ⟨Rat.le_trans (Rat.neg_le_neg h) (neg_qabs_le_self _),
    Rat.le_trans (self_le_qabs _) h⟩

/-- The difference between any two finite factorial prefixes is bounded by
the corresponding finite factorial tail.  This is a finite rational sum
identity, used to compare a common bounded-input prefix with an adaptive
input-specific prefix. -/
private theorem qabs_uniformExpCenter_add_sub_le_factorialTailPartial
    (x : Rat) (hx : qabs x <= 2) (N k : Nat) :
    qabs (powerSeriesCenterAtTerms x (N + k) -
      powerSeriesCenterAtTerms x N) <=
      RationalMajorant.factorialTailPartial 2 N k := by
  induction k with
  | zero =>
      rw [Nat.add_zero, RationalMajorant.factorialTailPartial]
      have hzero : powerSeriesCenterAtTerms x N - powerSeriesCenterAtTerms x N = 0 := by
        grind [Rat.sub_eq_add_neg]
      rw [hzero, qabs_eq_self_of_nonneg (by native_decide)]
      exact Rat.le_refl
  | succ k ih =>
      rw [show N + (k + 1) = N + k + 1 by omega,
        powerSeriesCenterAtTerms_succ,
        RationalMajorant.factorialTailPartial]
      have hrewrite :
          (powerSeriesCenterAtTerms x (N + k) +
              powerSeriesTermAtTerms x (N + k)) -
            powerSeriesCenterAtTerms x N =
          (powerSeriesCenterAtTerms x (N + k) -
              powerSeriesCenterAtTerms x N) +
            powerSeriesTermAtTerms x (N + k) := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      rw [hrewrite]
      have hterm := FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm
        (C := (2 : Rat)) (x := x) (by native_decide) hx (N + k)
      rw [powerSeriesTermAtTerms_eq_expCoeff_monomial]
      calc
        qabs ((powerSeriesCenterAtTerms x (N + k) -
            powerSeriesCenterAtTerms x N) +
            FormalPowerSeries.expCoeff (N + k) * x ^ (N + k)) <=
            qabs (powerSeriesCenterAtTerms x (N + k) -
              powerSeriesCenterAtTerms x N) +
              qabs (FormalPowerSeries.expCoeff (N + k) * x ^ (N + k)) :=
          qabs_add_le _ _
        _ <= RationalMajorant.factorialTailPartial 2 N k +
            RationalMajorant.factorialTailTerm 2 (N + k) :=
          rat_add_le_add ih hterm

theorem uniformExpBox_width (x : Rat) (n : Nat) :
    (uniformExpBox x n).width = 2 * uniformExpTailRadius n := by
  unfold uniformExpBox
  rw [intervalAround_width]
  grind [Rat.mul_assoc]

/-! A deliberately loose reciprocal tail budget after a fixed finite warm-up.
It is useful when an ordinary interval-regular adapter must read a public
stage itself, rather than the sharper adaptive stage used by the FTC
evaluator. -/
theorem uniformExpTailMagnitude_le_reciprocalHundred_shifted (n : Nat) :
    uniformExpTailMagnitude (n + 4) <=
      1 / (100 * ((n + 1 : Nat) : Rat)) := by
  induction n with
  | zero => native_decide
  | succ n ih =>
      have hnext := uniformExpTailMagnitude_next_le_half (n + 4)
      have hscaled := Rat.mul_le_mul_of_nonneg_right ih
        (by native_decide : (0 : Rat) <= 1 / 2)
      have hA : (0 : Rat) < 100 * ((n + 1 : Nat) : Rat) := by
        exact Rat.mul_pos (by native_decide)
          ((Rat.natCast_pos).2 (Nat.succ_pos n))
      have hB : (0 : Rat) < 100 * ((n + 2 : Nat) : Rat) := by
        exact Rat.mul_pos (by native_decide)
          ((Rat.natCast_pos).2 (by omega))
      have hhalf :
          (1 / (100 * ((n + 1 : Nat) : Rat))) * (1 / 2) <=
            1 / (100 * ((n + 2 : Nat) : Rat)) := by
        apply Rat.le_of_mul_le_mul_right (c :=
          2 * (100 * ((n + 1 : Nat) : Rat)) *
            (100 * ((n + 2 : Nat) : Rat)))
        · rw [Rat.div_def, Rat.div_def, Rat.div_def]
          have hAne : (100 * ((n + 1 : Nat) : Rat)) ≠ 0 :=
            Rat.ne_of_gt hA
          have hBne : (100 * ((n + 2 : Nat) : Rat)) ≠ 0 :=
            Rat.ne_of_gt hB
          have htwo : (2 : Rat) ≠ 0 := by native_decide
          have hAcancel := Rat.mul_inv_cancel
            (100 * ((n + 1 : Nat) : Rat)) hAne
          have hBcancel := Rat.mul_inv_cancel
            (100 * ((n + 2 : Nat) : Rat)) hBne
          have htwocancel := Rat.mul_inv_cancel (2 : Rat) htwo
          grind [Rat.mul_assoc, Rat.mul_comm]
        · exact Rat.mul_pos (Rat.mul_pos (by native_decide : (0 : Rat) < 2) hA) hB
      calc
        uniformExpTailMagnitude (n + 1 + 4) <=
            uniformExpTailMagnitude (n + 4) * ((1 : Rat) / 2) := by
          simpa [Nat.add_assoc] using hnext
        _ <= (1 / (100 * ((n + 1 : Nat) : Rat))) * (1 / 2) := hscaled
        _ <= 1 / (100 * ((n + 2 : Nat) : Rat)) := hhalf

private theorem uniformExpBox_ordered (x : Rat) (n : Nat) :
    0 <= (uniformExpBox x n).width := by
  rw [uniformExpBox_width]
  exact Rat.mul_nonneg (by native_decide)
    (Rat.mul_nonneg (by native_decide) (uniformExpTailMagnitude_nonneg n))

private theorem uniformExpBox_nested_step (x : Rat)
    (hx : qabs x <= 2) (n : Nat) :
    (uniformExpBox x n).lo <= (uniformExpBox x (n + 1)).lo /\
      (uniformExpBox x (n + 1)).hi <= (uniformExpBox x n).hi := by
  have hcenter := uniformExpCenter_step_bounds x hx n
  have hdrop := uniformExpTailRadius_drop_majorizes n
  unfold uniformExpBox intervalAround
  constructor <;> grind [Rat.sub_eq_add_neg]

private theorem uniformExpBox_nested (x : Rat) (hx : qabs x <= 2) :
    forall n m : Nat, n <= m ->
      (uniformExpBox x n).lo <= (uniformExpBox x m).lo /\
        (uniformExpBox x m).hi <= (uniformExpBox x n).hi
  | n, 0, hnm => by
      have hn : n = 0 := by omega
      subst n
      exact ⟨Rat.le_refl, Rat.le_refl⟩
  | n, m + 1, hnm => by
      by_cases hlast : n = m + 1
      · subst n
        exact ⟨Rat.le_refl, Rat.le_refl⟩
      · have hnm' : n <= m := by omega
        have hstep := uniformExpBox_nested_step x hx m
        have hprev := uniformExpBox_nested x hx n m hnm'
        exact ⟨Rat.le_trans hprev.1 hstep.1,
          Rat.le_trans hstep.2 hprev.2⟩

private theorem uniformExpBox_width_le_geometric (x : Rat) (n : Nat) :
    (uniformExpBox x n).width <=
      (4 * uniformExpTailMagnitude 0) * ((1 : Rat) / 2) ^ n := by
  rw [uniformExpBox_width]
  have htail := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := (2 : Rat)) (N := uniformExpTailTerms 0)
    (by native_decide) (uniform_exp_tail_start 0) n
  change 2 * (2 * RationalMajorant.factorialTailTerm 2 (uniformExpTailTerms n)) <= _
  have hterms : uniformExpTailTerms n = uniformExpTailTerms 0 + n := by
    unfold uniformExpTailTerms
    omega
  rw [hterms]
  calc
    2 * (2 * RationalMajorant.factorialTailTerm 2
        (uniformExpTailTerms 0 + n)) <=
        2 * (2 * (RationalMajorant.factorialTailTerm 2 (uniformExpTailTerms 0) *
          ((1 : Rat) / 2) ^ n)) :=
      Rat.mul_le_mul_of_nonneg_left
        (Rat.mul_le_mul_of_nonneg_left htail (by native_decide)) (by native_decide)
    _ = (4 * uniformExpTailMagnitude 0) * ((1 : Rat) / 2) ^ n := by
      unfold uniformExpTailMagnitude
      grind [Rat.mul_assoc]

/-- The scalar factorial tail itself has the same fixed geometric schedule as
the enclosing boxes. -/
private theorem uniformExpTailMagnitude_le_geometric (n : Nat) :
    uniformExpTailMagnitude n <=
      uniformExpTailMagnitude 0 * ((1 : Rat) / 2) ^ n := by
  have htail := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := (2 : Rat)) (N := uniformExpTailTerms 0)
    (by native_decide) (uniform_exp_tail_start 0) n
  change RationalMajorant.factorialTailTerm 2 (uniformExpTailTerms n) <= _
  have hterms : uniformExpTailTerms n = uniformExpTailTerms 0 + n := by
    unfold uniformExpTailTerms
    omega
  rw [hterms]
  simpa [uniformExpTailMagnitude] using htail

def uniformExpCellPieces (eps : QPos) : Nat :=
  200 * (eps.val.den + 1)

theorem uniformExpCellPieces_pos (eps : QPos) :
    0 < uniformExpCellPieces eps := by
  unfold uniformExpCellPieces
  omega

theorem uniformExpCellMesh_le (eps : QPos) :
    mesh 0 1 (uniformExpCellPieces eps) <= eps.val / 200 := by
  have hp := uniformExpCellPieces_pos eps
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hp)]
  have hden :
      1 / (((eps.val.den + 1 : Nat) : Rat)) <= eps.val :=
    FTC.one_div_den_succ_le_of_pos eps.property
  have hscaled := Rat.mul_le_mul_of_nonneg_left hden
    (show 0 <= (1 / 200 : Rat) by native_decide)
  -- The deliberately generous factor `200` leaves room for the polynomial
  -- secant constant and the tail contribution in the cell-range width.
  calc
    (1 - 0) / ((uniformExpCellPieces eps : Nat) : Rat) =
        (1 / 200 : Rat) /
          (((eps.val.den + 1 : Nat) : Rat)) := by
      unfold uniformExpCellPieces
      rw [show (1 : Rat) - 0 = 1 by grind, Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (1 / 200 : Rat) * eps.val := by
      simpa [Rat.div_def, Rat.mul_assoc] using hscaled
    _ = eps.val / 200 := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

def uniformExpCellStage (eps : QPos) : Nat :=
  RationalMajorant.halfDecayShift
    (((uniformExpCellPieces eps : Nat) : Rat) *
      (4 * uniformExpTailMagnitude 0))
    { val := eps.val / 2
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide)) }

theorem uniformExpCellTailSum_le_half (eps : QPos) :
    (uniformExpCellPieces eps : Rat) *
        (2 * uniformExpTailRadius (uniformExpCellStage eps)) <=
      eps.val / 2 := by
  let pieces : Nat := uniformExpCellPieces eps
  let bound : Rat := (pieces : Rat) * (4 * uniformExpTailMagnitude 0)
  let half : QPos := ⟨eps.val / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide))⟩
  let stage : Nat := RationalMajorant.halfDecayShift bound half
  have hbound : 0 <= bound := by
    dsimp [bound]
    exact Rat.mul_nonneg (by exact_mod_cast (Nat.zero_le pieces))
      (Rat.mul_nonneg (by native_decide)
        (uniformExpTailMagnitude_nonneg 0))
  have htail := uniformExpTailMagnitude_le_geometric stage
  have hshift := RationalMajorant.halfDecayShift_spec hbound half
  have hscaled : (pieces : Rat) *
      (4 * uniformExpTailMagnitude stage) <= half.val := by
    calc
      (pieces : Rat) * (4 * uniformExpTailMagnitude stage) <=
          (pieces : Rat) *
            (4 * (uniformExpTailMagnitude 0 * ((1 : Rat) / 2) ^ stage)) := by
        exact Rat.mul_le_mul_of_nonneg_left
          (Rat.mul_le_mul_of_nonneg_left htail (by native_decide))
          (by exact_mod_cast (Nat.zero_le pieces))
      _ = bound * ((1 : Rat) / 2) ^ stage := by
        dsimp [bound]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= half.val := hshift
  have hscaled' :
      (uniformExpCellPieces eps : Rat) *
          (4 * uniformExpTailMagnitude (uniformExpCellStage eps)) <=
        eps.val / 2 := by
    simpa [pieces, stage, uniformExpCellStage, bound, half,
      uniformExpCellPieces, Rat.mul_assoc, Rat.mul_comm] using hscaled
  unfold uniformExpTailRadius
  have hfactor :
      2 * (2 * uniformExpTailMagnitude (uniformExpCellStage eps)) =
        4 * uniformExpTailMagnitude (uniformExpCellStage eps) := by
    grind
  rw [hfactor]
  exact hscaled'

/-- The positive rational tail allowance assigned to a quotient with a
nonzero rational step.  It reserves one twenty-fourth of the requested output
precision times `|h|`, so all tail widths remain controlled after division by
that step. -/
def uniformExpQuotientTailTolerance (h : Rat) (hh : h ≠ 0) (n : Nat) : QPos :=
  { val := (precisionAtStage n).val * qabs h / 24
    property := by
      rw [Rat.div_def]
      exact Rat.mul_pos
        (Rat.mul_pos (precisionAtStage n).property
          (qabs_pos_of_ne hh))
        ((Rat.inv_pos).2 (by native_decide)) }

/-- The common factorial stage used to evaluate both endpoints of a
difference quotient.  Its input is the rational step and desired output
precision, never an ambient real number. -/
def uniformExpQuotientPrecision (h : Rat) (hh : h ≠ 0) (n : Nat) : Nat :=
  RationalMajorant.halfDecayShift (uniformExpTailMagnitude 0)
    (uniformExpQuotientTailTolerance h hh n)

theorem uniformExpQuotientPrecision_congr
    {h₁ h₂ : Rat} (heq : h₁ = h₂)
    (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) (n : Nat) :
    uniformExpQuotientPrecision h₁ hh₁ n =
      uniformExpQuotientPrecision h₂ hh₂ n := by
  cases heq
  rfl

/-- A total evaluator-stage function for the derivative interface.  Its value
at the unused zero step is arbitrary; every quotient proof supplies `h ≠ 0`
and therefore takes the common-tail branch. -/
def uniformExpSelfDerivativeEvalPrecision (h : Rat) (n : Nat) : Nat :=
  if hh : h = 0 then 0 else uniformExpQuotientPrecision h hh n

private theorem uniformExpSelfDerivativeEvalPrecision_of_ne
    (h : Rat) (hh : h ≠ 0) (n : Nat) :
    uniformExpSelfDerivativeEvalPrecision h n =
      uniformExpQuotientPrecision h hh n := by
  simp [uniformExpSelfDerivativeEvalPrecision, hh]

theorem uniformExpSelfDerivativeEvalPrecision_eq_quotient
    (h : Rat) (hh : h ≠ 0) (n : Nat) :
    uniformExpSelfDerivativeEvalPrecision h n =
      uniformExpQuotientPrecision h hh n := by
  exact uniformExpSelfDerivativeEvalPrecision_of_ne h hh n

/-- At the selected quotient stage, the scalar factorial tail is at most the
explicit `|h|`-scaled tolerance.  This is the computable tail transport that
will be combined with the uniform finite secant bound. -/
theorem uniformExpTailMagnitude_le_quotientTolerance
    (h : Rat) (hh : h ≠ 0) (n : Nat) :
    uniformExpTailMagnitude (uniformExpQuotientPrecision h hh n) <=
      (uniformExpQuotientTailTolerance h hh n).val := by
  let eps := uniformExpQuotientTailTolerance h hh n
  let stage := uniformExpQuotientPrecision h hh n
  have hbound : 0 <= uniformExpTailMagnitude 0 :=
    uniformExpTailMagnitude_nonneg 0
  have htail := uniformExpTailMagnitude_le_geometric stage
  have hshift := RationalMajorant.halfDecayShift_spec hbound eps
  exact Rat.le_trans htail hshift

/-! A quotient-selected stage makes the two endpoint boxes disjoint.  This is
the operational form of strict monotonicity used by a computable inverse
search: the stage depends only on the rational gap and the requested output
precision. -/
theorem uniformExpOnUnit_box_separated
    (n : Nat) {x y : Rat}
    (hx : 0 <= x) (hy : y <= 1) (hxy : x < y) :
    (uniformExpBox x
      (uniformExpQuotientPrecision (y - x)
        (Rat.ne_of_gt ((Rat.lt_iff_sub_pos x y).mp hxy)) n)).hi <
      (uniformExpBox y
        (uniformExpQuotientPrecision (y - x)
          (Rat.ne_of_gt ((Rat.lt_iff_sub_pos x y).mp hxy)) n)).lo := by
  let h : Rat := y - x
  have hpos : 0 < h := by
    dsimp [h]
    exact (Rat.lt_iff_sub_pos x y).mp hxy
  have hh : h ≠ 0 := Rat.ne_of_gt hpos
  let stage : Nat := uniformExpQuotientPrecision h hh n
  have htail := uniformExpTailMagnitude_le_quotientTolerance h hh n
  have hqabs : qabs h = h := qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)
  have htail' :
      uniformExpTailMagnitude stage <=
        (precisionAtStage n).val * h / 24 := by
    simpa [stage, uniformExpQuotientTailTolerance, hqabs] using htail
  have hp : 0 <= (precisionAtStage n).val :=
    Rat.le_of_lt (precisionAtStage n).property
  have hpone : (precisionAtStage n).val <= 1 := by
    by_cases hn : n = 0
    · simp [precisionAtStage, hn]
    · rw [precisionAtStage, dif_neg hn]
      change 1 / (n : Rat) <= 1
      have h := FTC.one_div_nat_antitone (n := 1) (m := n)
        (by native_decide) (Nat.pos_of_ne_zero hn)
        (Nat.one_le_iff_ne_zero.mpr hn)
      have h' : 1 / (n : Rat) <= 1 / (1 : Rat) := h
      calc
        1 / (n : Rat) <= 1 / (1 : Rat) := h'
        _ = 1 := by native_decide
  have htail4 : 4 * uniformExpTailMagnitude stage <= h / 6 := by
    have hscaled := Rat.mul_le_mul_of_nonneg_left htail'
      (by native_decide : (0 : Rat) <= 4)
    have hph := Rat.mul_le_mul_of_nonneg_right hpone
      (Rat.le_of_lt hpos)
    calc
      4 * uniformExpTailMagnitude stage <=
          4 * ((precisionAtStage n).val * h / 24) := hscaled
      _ = ((precisionAtStage n).val * h) / 6 := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= h / 6 := by
        have := Rat.mul_le_mul_of_nonneg_left hph hp
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hcenter := uniformExpCenter_difference_ge_input
    stage hx hy (Rat.le_of_lt hxy)
  have hstrict : h / 6 < h := by
    have := hpos
    grind
  have hrad : 2 * uniformExpTailRadius stage <= h / 6 := by
    unfold uniformExpTailRadius
    calc
      2 * (2 * uniformExpTailMagnitude stage) =
          4 * uniformExpTailMagnitude stage := by grind
      _ <= h / 6 := htail4
  have hdiff : 2 * uniformExpTailRadius stage <
      uniformExpCenter y stage - uniformExpCenter x stage :=
    by grind
  have hdiff' :
      2 * uniformExpTailRadius
          (uniformExpQuotientPrecision (y - x)
            (Rat.ne_of_gt ((Rat.lt_iff_sub_pos x y).mp hxy)) n) <
        uniformExpCenter y
            (uniformExpQuotientPrecision (y - x)
              (Rat.ne_of_gt ((Rat.lt_iff_sub_pos x y).mp hxy)) n) -
          uniformExpCenter x
            (uniformExpQuotientPrecision (y - x)
              (Rat.ne_of_gt ((Rat.lt_iff_sub_pos x y).mp hxy)) n) := by
    simpa [stage, h] using hdiff
  unfold uniformExpBox intervalAround
  grind [Rat.sub_eq_add_neg]

/-- The dyadic step schedule for the eventual two-sided self-derivative
certificate.  The coefficient `68` reserves half of the requested precision
for the uniform finite secant error `34 |h|`. -/
def uniformExpSelfDerivativeStepPrecision (n : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift (68 : Rat) (precisionAtStage n)

/-- A step selected by `uniformExpSelfDerivativeStepPrecision` spends at most
half the requested tolerance on the uniform finite Taylor secant error. -/
theorem uniformExpSelfDerivative_finite_error_le_half_precision
    {h : Rat} (n : Nat)
    (hsmall : qabs h <=
      1 / ((uniformExpSelfDerivativeStepPrecision n : Nat) : Rat)) :
    qabs h * 34 <= (precisionAtStage n).val / 2 := by
  let shift : Nat := RationalMajorant.halfDecayShift (68 : Rat)
    (precisionAtStage n)
  have hsmall' : qabs h <= 1 / (((2 ^ shift : Nat) : Rat)) := by
    simpa [uniformExpSelfDerivativeStepPrecision, shift] using hsmall
  have hscaled : qabs h * 68 <= 1 / (((2 ^ shift : Nat) : Rat)) * 68 :=
    Rat.mul_le_mul_of_nonneg_right hsmall' (by native_decide)
  have hgeometric : (68 : Rat) * ((1 : Rat) / 2) ^ shift <=
      (precisionAtStage n).val := by
    simpa [shift] using RationalMajorant.halfDecayShift_spec
      (by native_decide : (0 : Rat) <= 68) (precisionAtStage n)
  have hsixtyEight : qabs h * 68 <= (precisionAtStage n).val := by
    calc
      qabs h * 68 <= 1 / (((2 ^ shift : Nat) : Rat)) * 68 := hscaled
      _ = 68 * ((1 : Rat) / 2) ^ shift := by
        rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
        grind [Rat.mul_comm]
      _ <= (precisionAtStage n).val := hgeometric
  calc
    qabs h * 34 = (qabs h * 68) / 2 := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (precisionAtStage n).val / 2 :=
      Rat.mul_le_mul_of_nonneg_right hsixtyEight (Rat.le_of_lt
        ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2)))

/-- Interval quotient algebra for two equal-radius boxes over a positive
rational step.  The hypotheses separate the rational center error from the
two interval-width budgets; this is the endpoint calculation used in the
uniform exponential derivative certificate. -/
private theorem intervalAround_differenceQuotient_near_intervalAround_of_pos
    (c0 c1 d r h E : Rat) (eps : QPos)
    (hpos : 0 < h) (hr : 0 <= r)
    (herror : qabs ((c1 - c0) / h - d) <= E)
    (hbudget : E + 2 * r / h + r <= eps.val)
    (hquotientWidth : 4 * r / h <= eps.val)
    (hderivativeWidth : 2 * r <= eps.val) :
    QInterval.NearAt
      (QInterval.differenceQuotient (intervalAround c1 r)
        (intervalAround c0 r) h)
      (intervalAround d r) eps := by
  have hh : h ≠ 0 := Rat.ne_of_gt hpos
  have hinvpos : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have htwoRdiv : 0 <= 2 * r / h := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) hr)
      (Rat.le_of_lt ((Rat.inv_pos).2 hpos))
  have hEeps : E <= eps.val := by
    grind [Rat.sub_eq_add_neg]
  let q : Rat := (c1 - c0) / h
  have hupper : q - d <= E := by
    dsimp [q]
    exact Rat.le_trans (self_le_qabs _) herror
  have hlower : d - q <= E := by
    dsimp [q]
    calc
      d - (c1 - c0) / h = -((c1 - c0) / h - d) := by
        grind [Rat.sub_eq_add_neg]
      _ <= qabs (-((c1 - c0) / h - d)) := self_le_qabs _
      _ = qabs ((c1 - c0) / h - d) := qabs_neg _
      _ <= E := herror
  have hlo : (1 / h) * ((c1 - r) - (c0 + r)) = q - 2 * r / h := by
    dsimp [q]
    rw [Rat.div_def, Rat.div_def]
    have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hh
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  have hhi : (1 / h) * ((c1 + r) - (c0 - r)) = q + 2 * r / h := by
    dsimp [q]
    rw [Rat.div_def, Rat.div_def]
    have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hh
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  unfold QInterval.NearAt QInterval.differenceQuotient QInterval.divRat
    QInterval.sub QInterval.scaleRat intervalAround QInterval.width
  rw [if_pos hinvpos]
  dsimp
  change
    (1 / h) * ((c1 - r) - (c0 + r)) <= d + r + eps.val /\
      d - r <= (1 / h) * ((c1 + r) - (c0 - r)) + eps.val /\
      (1 / h) * ((c1 + r) - (c0 - r)) -
        (1 / h) * ((c1 - r) - (c0 + r)) <= eps.val /\
      d + r - (d - r) <= eps.val
  rw [hlo, hhi]
  have hqlo : q - 2 * r / h <= q := by
    grind
  have hqhi : q <= q + 2 * r / h := by
    grind
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor
  · grind [Rat.sub_eq_add_neg]
  · grind [Rat.sub_eq_add_neg]

/-- The preceding quotient calculation is two-sided: reversing a negative
step also reverses the two interval endpoints, reducing it to the positive
case without choosing an orientation for the derivative. -/
private theorem intervalAround_differenceQuotient_near_intervalAround
    (c0 c1 d r h E : Rat) (eps : QPos)
    (hh : h ≠ 0) (hr : 0 <= r)
    (herror : qabs ((c1 - c0) / h - d) <= E)
    (hbudget : E + 2 * r / qabs h + r <= eps.val)
    (hquotientWidth : 4 * r / qabs h <= eps.val)
    (hderivativeWidth : 2 * r <= eps.val) :
    QInterval.NearAt
      (QInterval.differenceQuotient (intervalAround c1 r)
        (intervalAround c0 r) h)
      (intervalAround d r) eps := by
  by_cases hpos : 0 < h
  · have hqabs : qabs h = h := qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)
    rw [hqabs] at hbudget hquotientWidth
    exact intervalAround_differenceQuotient_near_intervalAround_of_pos
      c0 c1 d r h E eps hpos hr herror hbudget hquotientWidth
      hderivativeWidth
  · have hneg : h < 0 := by grind
    have hkpos : 0 < -h := by grind
    have hqabs : qabs h = -h := qabs_eq_neg_of_nonpos (Rat.le_of_lt hneg)
    rw [hqabs] at hbudget hquotientWidth
    have hnegInv : (-h)⁻¹ = -h⁻¹ := by
      have hnegmul : (-h) * (-h⁻¹) = 1 := by
        have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
        grind [Rat.mul_assoc, Rat.mul_comm]
      calc
        (-h)⁻¹ = (-h)⁻¹ * 1 := by grind
        _ = (-h)⁻¹ * ((-h) * (-h⁻¹)) := by rw [hnegmul]
        _ = ((-h)⁻¹ * (-h)) * (-h⁻¹) := by
          grind [Rat.mul_assoc]
        _ = 1 * (-h⁻¹) := by
          rw [Rat.inv_mul_cancel (-h) (by grind)]
        _ = -h⁻¹ := by rw [Rat.one_mul]
    have hquotient : (c0 - c1) / (-h) = (c1 - c0) / h := by
      rw [Rat.div_def, Rat.div_def, hnegInv]
      grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]
    have herror' : qabs ((c0 - c1) / (-h) - d) <= E := by
      rw [hquotient]
      exact herror
    have hreverse := QInterval.differenceQuotient_reverse_of_pos
      (A := intervalAround c0 r) (B := intervalAround c1 r) (h := -h) hkpos
    have hdouble : -(-h) = h := by grind
    rw [hdouble] at hreverse
    rw [hreverse]
    exact intervalAround_differenceQuotient_near_intervalAround_of_pos
      c1 c0 d r (-h) E eps hkpos hr herror' hbudget hquotientWidth
      hderivativeWidth

/-- Absolute value commutes with division by a nonzero rational step.  This
small sign split keeps all later quotient-tail estimates in terms of the
orientation-free quantity `|h|`. -/
private theorem qabs_div_eq_div_qabs (a h : Rat) (hh : h ≠ 0) :
    qabs (a / h) = qabs a / qabs h := by
  by_cases hpos : 0 < h
  · have hnonneg : 0 <= h := Rat.le_of_lt hpos
    rw [Rat.div_def, qabs_mul, qabs_eq_self_of_nonneg hnonneg]
    have hinvpos : 0 < h⁻¹ := (Rat.inv_pos).2 hpos
    rw [qabs_eq_self_of_nonneg (Rat.le_of_lt hinvpos), Rat.div_def]
  · have hneg : h < 0 := by grind
    have hnonpos : h <= 0 := Rat.le_of_lt hneg
    have hnegInv : (-h)⁻¹ = -h⁻¹ := by
      have hnegmul : (-h) * (-h⁻¹) = 1 := by
        have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
        grind [Rat.mul_assoc, Rat.mul_comm]
      calc
        (-h)⁻¹ = (-h)⁻¹ * 1 := by grind
        _ = (-h)⁻¹ * ((-h) * (-h⁻¹)) := by rw [hnegmul]
        _ = ((-h)⁻¹ * (-h)) * (-h⁻¹) := by grind [Rat.mul_assoc]
        _ = 1 * (-h⁻¹) := by rw [Rat.inv_mul_cancel (-h) (by grind)]
        _ = -h⁻¹ := by rw [Rat.one_mul]
    have hinvneg : h⁻¹ < 0 := by
      have hposinv : 0 < (-h)⁻¹ := (Rat.inv_pos).2 (by grind)
      rw [hnegInv] at hposinv
      grind
    rw [Rat.div_def, qabs_mul, qabs_eq_neg_of_nonpos hnonpos,
      qabs_eq_neg_of_nonpos (Rat.le_of_lt hinvneg)]
    rw [Rat.div_def, hnegInv]

/-- The quotient of the two common finite centers differs from the center at
the left endpoint by the uniform finite error plus two explicitly bounded
factorial-tail contributions. -/
theorem uniformExpCenter_secant_error_le
    {x h : Rat} (hh : h ≠ 0) (hx : qabs x <= 2)
    (hxh : qabs (x + h) <= 2) (n : Nat) :
    qabs
      ((uniformExpCenter (x + h) n - uniformExpCenter x n) / h -
        uniformExpCenter x n) <=
      qabs h * 34 + 2 * uniformExpTailMagnitude n / qabs h := by
  have hfinite : qabs
      ((FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
        FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) / h -
        uniformExpCenter x n) <= qabs h * 34 := by
    change qabs
        ((FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
          FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) / h -
          powerSeriesCenterAtTerms x (uniformExpTailTerms n)) <= _
    rw [← expTaylorDerivativePrefix_eq_powerSeriesCenterAtTerms]
    exact FinitePolynomial.expTaylorPrefix_secant_error_le_thirty_four
      (x := x) (h := h) hh hx hxh (uniformExpTailTerms n)
  have hprefix (z : Rat) (hz : qabs z <= 2) :
      qabs (FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) z -
        uniformExpCenter z n) <= uniformExpTailMagnitude n := by
    rw [← powerSeriesCenterAtTerms_eq_expTaylorPrefix]
    unfold uniformExpCenter
    rw [powerSeriesCenterAtTerms_succ]
    have hcancel :
        powerSeriesCenterAtTerms z (uniformExpTailTerms n) +
            powerSeriesTermAtTerms z (uniformExpTailTerms n) -
          powerSeriesCenterAtTerms z (uniformExpTailTerms n) =
            powerSeriesTermAtTerms z (uniformExpTailTerms n) := by
      grind [Rat.sub_eq_add_neg]
    rw [hcancel, powerSeriesTermAtTerms_eq_expCoeff_monomial]
    simpa [uniformExpTailMagnitude] using
      FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm
        (C := (2 : Rat)) (x := z) (by native_decide) hz
        (uniformExpTailTerms n)
  have hright := hprefix (x + h) hxh
  have hleft := hprefix x hx
  have hdecomp :
      ((uniformExpCenter (x + h) n - uniformExpCenter x n) / h -
        uniformExpCenter x n) =
        (((FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
            FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) / h -
            uniformExpCenter x n) +
          ((uniformExpCenter (x + h) n -
              FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
              (uniformExpCenter x n -
                FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x)) / h)) := by
    rw [Rat.div_def]
    have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hdecomp]
  let tailError : Rat :=
    uniformExpCenter (x + h) n -
      FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
      (uniformExpCenter x n -
        FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x)
  have htailNumerator : qabs tailError <= 2 * uniformExpTailMagnitude n := by
    dsimp [tailError]
    calc
      qabs
          ((uniformExpCenter (x + h) n -
              FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h)) -
            (uniformExpCenter x n -
              FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x)) <=
          qabs
            (uniformExpCenter (x + h) n -
              FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h)) +
            qabs
              (-(uniformExpCenter x n -
                FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x)) := by
              rw [show
                  (uniformExpCenter (x + h) n -
                    FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h)) -
                  (uniformExpCenter x n -
                    FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) =
                    (uniformExpCenter (x + h) n -
                      FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h)) +
                    -(uniformExpCenter x n -
                      FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) by
                    grind [Rat.sub_eq_add_neg]]
              exact qabs_add_le _ _
      _ = qabs
            (uniformExpCenter (x + h) n -
              FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h)) +
            qabs
              (uniformExpCenter x n -
                FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) := by
              rw [qabs_neg]
      _ = qabs
            (FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
              uniformExpCenter (x + h) n) +
            qabs
              (FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x -
                uniformExpCenter x n) := by
              rw [show uniformExpCenter (x + h) n -
                    FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) =
                    -(FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
                      uniformExpCenter (x + h) n) by
                    grind [Rat.sub_eq_add_neg], qabs_neg]
              rw [show uniformExpCenter x n -
                    FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x =
                    -(FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x -
                      uniformExpCenter x n) by
                    grind [Rat.sub_eq_add_neg], qabs_neg]
      _ <= uniformExpTailMagnitude n + uniformExpTailMagnitude n :=
        rat_add_le_add hright hleft
      _ = 2 * uniformExpTailMagnitude n := by grind [Rat.mul_add]
  have htailQuotient : qabs (tailError / h) <=
      2 * uniformExpTailMagnitude n / qabs h := by
    rw [qabs_div_eq_div_qabs tailError h hh]
    exact Rat.mul_le_mul_of_nonneg_right htailNumerator (Rat.le_of_lt
      ((Rat.inv_pos).2 (qabs_pos_of_ne hh)))
  change qabs
      (((FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
          FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) / h -
          uniformExpCenter x n) + tailError / h) <= _
  calc
    qabs
        (((FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
            FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) / h -
            uniformExpCenter x n) + tailError / h) <=
        qabs
          ((FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
            FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) / h -
            uniformExpCenter x n) + qabs (tailError / h) := qabs_add_le _ _
    _ <= qabs h * 34 + 2 * uniformExpTailMagnitude n / qabs h :=
      rat_add_le_add hfinite htailQuotient

/-! A symmetric-cell range estimate.  The endpoint centers need not be
monotone: the absolute secant certificate and the finite global center bound
already give a shrinking interval over every short rational cell. -/

theorem uniformExpCenter_difference_qabs_le
    {a b : Rat} (n : Nat)
    (ha : qabs a <= 2) (hb : qabs b <= 2) (hab : a < b) :
    qabs (uniformExpCenter b n - uniformExpCenter a n) <=
      9 * (b - a) + 34 * (b - a) ^ 2 +
        2 * uniformExpTailMagnitude n := by
  let h : Rat := b - a
  have hpos : 0 < h := by
    dsimp [h]
    exact (Rat.lt_iff_sub_pos a b).mp hab
  have hh : h ≠ 0 := Rat.ne_of_gt hpos
  have hab_eq : a + h = b := by
    dsimp [h]
    grind
  have hb' : qabs (a + h) <= 2 := by
    rw [hab_eq]
    exact hb
  have hsec := uniformExpCenter_secant_error_le
    (x := a) (h := h) hh ha hb' n
  have hqabs : qabs h = h :=
    qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)
  have hsec' :
      qabs ((uniformExpCenter b n - uniformExpCenter a n) / h -
        uniformExpCenter a n) <=
        h * 34 + 2 * uniformExpTailMagnitude n / h := by
    rw [hab_eq] at hsec
    simpa [hqabs] using hsec
  have hquot :
      qabs ((uniformExpCenter b n - uniformExpCenter a n) / h) <=
        9 + h * 34 + 2 * uniformExpTailMagnitude n / h := by
    have hsplit :
        (uniformExpCenter b n - uniformExpCenter a n) / h =
          uniformExpCenter a n +
            ((uniformExpCenter b n - uniformExpCenter a n) / h -
              uniformExpCenter a n) := by
      grind [Rat.div_def, Rat.mul_assoc, Rat.sub_eq_add_neg]
    rw [hsplit]
    calc
      qabs (uniformExpCenter a n +
          ((uniformExpCenter b n - uniformExpCenter a n) / h -
            uniformExpCenter a n)) <=
          qabs (uniformExpCenter a n) +
            qabs ((uniformExpCenter b n - uniformExpCenter a n) / h -
              uniformExpCenter a n) := qabs_add_le _ _
      _ <= 9 + (h * 34 +
          2 * uniformExpTailMagnitude n / h) := by
        exact rat_add_le_add
          (uniformExpCenter_qabs_le_nine a ha n) hsec'
      _ = 9 + h * 34 +
          2 * uniformExpTailMagnitude n / h := by grind
  have hdiff :
      qabs (uniformExpCenter b n - uniformExpCenter a n) =
        h * qabs ((uniformExpCenter b n - uniformExpCenter a n) / h) := by
    have hdiv := qabs_div_eq_div_qabs
      (uniformExpCenter b n - uniformExpCenter a n) h hh
    rw [hdiv, hqabs, Rat.div_def]
    have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
    grind [Rat.mul_assoc]
  rw [hdiff]
  have hnonneg : 0 <= h := Rat.le_of_lt hpos
  have hmul := Rat.mul_le_mul_of_nonneg_left hquot hnonneg
  calc
    h * qabs ((uniformExpCenter b n - uniformExpCenter a n) / h) <=
        h * (9 + h * 34 + 2 * uniformExpTailMagnitude n / h) := hmul
    _ = 9 * (b - a) + 34 * (b - a) ^ 2 +
        2 * uniformExpTailMagnitude n := by
      dsimp [h]
      have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem uniformExpCenter_difference_le
    {a b : Rat} (n : Nat)
    (ha : 0 <= a) (hb : b <= 1) (hab : a < b) :
    uniformExpCenter b n - uniformExpCenter a n <=
      3 * (b - a) + 34 * (b - a) ^ 2 +
        2 * uniformExpTailMagnitude n := by
  let h : Rat := b - a
  have hpos : 0 < h := by
    dsimp [h]
    exact (Rat.lt_iff_sub_pos a b).mp hab
  have hh : h ≠ 0 := Rat.ne_of_gt hpos
  have ha1 : a <= 1 := Rat.le_trans (Rat.le_of_lt hab) hb
  have hxh : qabs (a + h) <= 2 := by
    have hab_eq : a + h = b := by
      dsimp [h]
      grind
    have hbnonneg : 0 <= b := Rat.le_trans ha (Rat.le_of_lt hab)
    rw [hab_eq, qabs_eq_self_of_nonneg hbnonneg]
    exact Rat.le_trans hb (by native_decide)
  have hx : qabs a <= 2 := by
    rw [qabs_eq_self_of_nonneg ha]
    exact Rat.le_trans ha1 (by native_decide)
  have hsec := uniformExpCenter_secant_error_le
    (x := a) (h := h) hh hx hxh n
  have hcenter : 0 <= uniformExpCenter a n :=
    uniformExpCenter_nonneg_on_unit n ha ha1
  have hcenter_le : uniformExpCenter a n <= (3 : Rat) :=
    uniformExpCenter_le_three_on_unit n ha ha1
  have hqabs : qabs h = h := qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)
  have hsec' :
      qabs ((uniformExpCenter (a + h) n - uniformExpCenter a n) / h -
        uniformExpCenter a n) <=
        h * 34 + 2 * uniformExpTailMagnitude n / h := by
    simpa [hqabs] using hsec
  have hquot :
      qabs ((uniformExpCenter (a + h) n - uniformExpCenter a n) / h) <=
        3 + h * 34 + 2 * uniformExpTailMagnitude n / h := by
    have hsplit :
        (uniformExpCenter (a + h) n - uniformExpCenter a n) / h =
          uniformExpCenter a n +
            ((uniformExpCenter (a + h) n - uniformExpCenter a n) / h -
              uniformExpCenter a n) := by
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc,
        Rat.mul_comm]
    rw [hsplit]
    calc
      qabs (uniformExpCenter a n +
          ((uniformExpCenter (a + h) n - uniformExpCenter a n) / h -
            uniformExpCenter a n)) <=
          qabs (uniformExpCenter a n) +
            qabs ((uniformExpCenter (a + h) n - uniformExpCenter a n) / h -
              uniformExpCenter a n) := qabs_add_le _ _
      _ <= 3 + (h * 34 + 2 * uniformExpTailMagnitude n / h) := by
        rw [qabs_eq_self_of_nonneg hcenter]
        exact rat_add_le_add hcenter_le hsec'
      _ = 3 + h * 34 + 2 * uniformExpTailMagnitude n / h := by
        grind [Rat.add_assoc]
  have hdiff_qabs :
      qabs (uniformExpCenter b n - uniformExpCenter a n) =
        h * qabs ((uniformExpCenter b n - uniformExpCenter a n) / h) := by
    have hdiv := qabs_div_eq_div_qabs
      (uniformExpCenter b n - uniformExpCenter a n) h hh
    rw [hdiv, hqabs, Rat.div_def]
    have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
    grind [Rat.mul_assoc]
  have hdiff_nonneg :
      0 <= uniformExpCenter b n - uniformExpCenter a n := by
    have hmono := uniformExpCenter_mono_on_unit n ha hb (Rat.le_of_lt hab)
    grind [Rat.sub_eq_add_neg]
  have hdiff_eq :
      uniformExpCenter b n - uniformExpCenter a n =
        h * qabs ((uniformExpCenter b n - uniformExpCenter a n) / h) := by
    rw [← hdiff_qabs, qabs_eq_self_of_nonneg hdiff_nonneg]
  have hqbound := Rat.mul_le_mul_of_nonneg_left hquot (Rat.le_of_lt hpos)
  rw [show a + h = b by dsimp [h]; grind] at hqbound
  calc
    uniformExpCenter b n - uniformExpCenter a n =
        h * qabs ((uniformExpCenter b n - uniformExpCenter a n) / h) := hdiff_eq
    _ <=
        h * (3 + h * 34 + 2 * uniformExpTailMagnitude n / h) := hqbound
    _ = 3 * h + 34 * h ^ 2 + 2 * uniformExpTailMagnitude n := by
      rw [Rat.div_def]
      have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
      grind [Rat.mul_assoc, Rat.mul_comm,
        Rat.pow_succ]

theorem uniformExpCellRange_width_le
    {a b : Rat} (n : Nat)
    (ha : 0 <= a) (hb : b <= 1) (hab : a <= b) :
    (uniformExpCellRange a b n).width <=
      3 * (b - a) + 34 * (b - a) ^ 2 +
        6 * uniformExpTailMagnitude n := by
  by_cases heq : a = b
  · subst heq
    rw [uniformExpCellRange_width]
    simp only [Rat.sub_self, Rat.zero_add]
    unfold uniformExpTailRadius
    have htail : 0 <= uniformExpTailMagnitude n :=
      uniformExpTailMagnitude_nonneg n
    grind
  · have hlt : a < b := (Rat.lt_iff_le_and_ne).2 ⟨hab, heq⟩
    rw [uniformExpCellRange_width]
    have hcenter := uniformExpCenter_difference_le n ha hb hlt
    unfold uniformExpTailRadius
    have htail : 0 <= uniformExpTailMagnitude n :=
      uniformExpTailMagnitude_nonneg n
    calc
      uniformExpCenter b n - uniformExpCenter a n +
          2 * (2 * uniformExpTailMagnitude n) <=
          (3 * (b - a) + 34 * (b - a) ^ 2 +
            2 * uniformExpTailMagnitude n) +
            2 * (2 * uniformExpTailMagnitude n) :=
        rat_add_le_add hcenter Rat.le_refl
      _ <= 3 * (b - a) + 34 * (b - a) ^ 2 +
          6 * uniformExpTailMagnitude n := by
        grind

def uniformExpFTCInputPrecision (eps : QPos) : QPos :=
  { val := eps.val / 5
    property := by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide)) }

def uniformExpFTCIndex (eps : QPos) : Nat :=
  (uniformExpFTCInputPrecision eps).val.den + 1

def uniformExpFTCPieces (eps : QPos) : Nat :=
  200 * uniformExpFTCIndex eps *
    uniformExpSelfDerivativeStepPrecision (uniformExpFTCIndex eps)

theorem uniformExpFTCIndex_pos (eps : QPos) :
    0 < uniformExpFTCIndex eps := by
  unfold uniformExpFTCIndex
  omega

theorem uniformExpFTCPrecisionAtIndex (eps : QPos) :
    (precisionAtStage (uniformExpFTCIndex eps)).val =
      1 / ((uniformExpFTCIndex eps : Nat) : Rat) := by
  have hn : uniformExpFTCIndex eps ≠ 0 :=
    Nat.ne_of_gt (uniformExpFTCIndex_pos eps)
  simp [precisionAtStage, hn]

theorem uniformExpFTCPrecision_le_input (eps : QPos) :
    (precisionAtStage (uniformExpFTCIndex eps)).val <=
      (uniformExpFTCInputPrecision eps).val := by
  rw [uniformExpFTCPrecisionAtIndex]
  exact FTC.one_div_den_succ_le_of_pos
    (uniformExpFTCInputPrecision eps).property

theorem uniformExpFTCPieces_pos (eps : QPos) :
    0 < uniformExpFTCPieces eps := by
  unfold uniformExpFTCPieces
  have hi := uniformExpFTCIndex_pos eps
  have hs : 0 < uniformExpSelfDerivativeStepPrecision
      (uniformExpFTCIndex eps) := by
    unfold uniformExpSelfDerivativeStepPrecision
    exact Nat.pow_pos (by native_decide)
  exact Nat.mul_pos (Nat.mul_pos (by native_decide) hi) hs

theorem uniformExpFTCPieces_ge_step (eps : QPos) :
    uniformExpSelfDerivativeStepPrecision (uniformExpFTCIndex eps) <=
      uniformExpFTCPieces eps := by
  unfold uniformExpFTCPieces
  have hi := uniformExpFTCIndex_pos eps
  have hs : 1 <= uniformExpSelfDerivativeStepPrecision
      (uniformExpFTCIndex eps) := by
    unfold uniformExpSelfDerivativeStepPrecision
    exact Nat.one_le_pow _ _ (by native_decide)
  exact Nat.le_mul_of_pos_left
      (uniformExpSelfDerivativeStepPrecision (uniformExpFTCIndex eps))
      (Nat.mul_pos (by native_decide) hi)

theorem uniformExpFTCPieces_mesh_le (eps : QPos) :
    mesh 0 1 (uniformExpFTCPieces eps) <=
      (precisionAtStage (uniformExpFTCIndex eps)).val / 200 := by
  have hp := uniformExpFTCPieces_pos eps
  have hi := uniformExpFTCIndex_pos eps
  have hprod : 0 < 200 * uniformExpFTCIndex eps := by omega
  have hle : 200 * uniformExpFTCIndex eps <= uniformExpFTCPieces eps := by
    unfold uniformExpFTCPieces
    have hs : 1 <= uniformExpSelfDerivativeStepPrecision
        (uniformExpFTCIndex eps) := by
      unfold uniformExpSelfDerivativeStepPrecision
      exact Nat.one_le_pow _ _ (by native_decide)
    exact Nat.le_mul_of_pos_right
      (200 * uniformExpFTCIndex eps) hs
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hp)]
  have hanti := FTC.one_div_nat_antitone hprod hp hle
  rw [show (1 : Rat) - 0 = 1 by grind]
  calc
    1 / ((uniformExpFTCPieces eps : Nat) : Rat) <=
        1 / ((200 * uniformExpFTCIndex eps : Nat) : Rat) := hanti
    _ = (1 / 200 : Rat) /
        ((uniformExpFTCIndex eps : Nat) : Rat) := by
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (precisionAtStage (uniformExpFTCIndex eps)).val / 200 := by
      rw [uniformExpFTCPrecisionAtIndex, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem uniformExpFTCPieces_step_le (eps : QPos) :
    mesh 0 1 (uniformExpFTCPieces eps) <=
      1 / ((uniformExpSelfDerivativeStepPrecision
        (uniformExpFTCIndex eps) : Nat) : Rat) := by
  have hp := uniformExpFTCPieces_pos eps
  have hs := uniformExpFTCPieces_ge_step eps
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hp)]
  rw [show (1 : Rat) - 0 = 1 by grind]
  exact FTC.one_div_nat_antitone
    (by
      change 0 < uniformExpSelfDerivativeStepPrecision
        (uniformExpFTCIndex eps)
      unfold uniformExpSelfDerivativeStepPrecision
      exact Nat.pow_pos (by native_decide))
    hp hs

theorem uniformExpCellRange_width_le_at_quotient_stage
    (n : Nat) {a b : Rat}
    (ha : 0 <= a) (hb : b <= 1) (hab : a < b)
    (hstep : b - a <= (precisionAtStage n).val / 200) :
    (uniformExpCellRange a b
      (uniformExpQuotientPrecision (b - a)
        (Rat.ne_of_gt ((Rat.lt_iff_sub_pos a b).mp hab)) n)).width <=
      (precisionAtStage n).val / 2 := by
  let h : Rat := b - a
  have hpos : 0 < h := by
    dsimp [h]
    exact (Rat.lt_iff_sub_pos a b).mp hab
  have hh : h ≠ 0 := Rat.ne_of_gt hpos
  let hstage : Nat := uniformExpQuotientPrecision h hh n
  have hwidth := uniformExpCellRange_width_le hstage ha hb (Rat.le_of_lt hab)
  have htail := uniformExpTailMagnitude_le_quotientTolerance h hh n
  have hqabs : qabs h = h := qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)
  have htail' :
      uniformExpTailMagnitude hstage <=
        (precisionAtStage n).val * h / 24 := by
    simpa [hstage, uniformExpQuotientTailTolerance, hqabs] using htail
  have hnonneg : 0 <= h := Rat.le_of_lt hpos
  have hleone : h <= 1 := by
    dsimp [h]
    grind
  have hcenter :
      3 * h + 34 * h ^ 2 <= (precisionAtStage n).val / 4 := by
    have hsq : h ^ 2 <= h := by
      rw [show h ^ 2 = h * h by simp [Rat.pow_succ]]
      have := Rat.mul_le_mul_of_nonneg_left hleone hnonneg
      grind
    have hlin : 3 * h + 34 * h ^ 2 <= 37 * h := by
      have := Rat.mul_le_mul_of_nonneg_left hsq
        (by native_decide : (0 : Rat) <= 34)
      grind
    have hscaled := Rat.mul_le_mul_of_nonneg_left hstep
      (by native_decide : (0 : Rat) <= 37)
    calc
      3 * h + 34 * h ^ 2 <= 37 * h := hlin
      _ <= 37 * ((precisionAtStage n).val / 200) := hscaled
      _ <= (precisionAtStage n).val / 4 := by grind
  have htailwidth :
      6 * uniformExpTailMagnitude hstage <=
        (precisionAtStage n).val / 4 := by
    have hmul := Rat.mul_le_mul_of_nonneg_left htail'
      (by native_decide : (0 : Rat) <= 6)
    have hpnonneg : 0 <= (precisionAtStage n).val :=
      Rat.le_of_lt (precisionAtStage n).property
    have hph := Rat.mul_le_mul_of_nonneg_left hleone hpnonneg
    calc
      6 * uniformExpTailMagnitude hstage <=
          6 * ((precisionAtStage n).val * h / 24) := hmul
      _ <= (precisionAtStage n).val / 4 := by
        calc
          6 * ((precisionAtStage n).val * h / 24) =
              (precisionAtStage n).val * h / 4 := by
                grind [Rat.mul_assoc, Rat.mul_comm]
          _ <= (precisionAtStage n).val / 4 := by
            grind [Rat.mul_assoc, Rat.mul_comm]
  dsimp [hstage, h] at hwidth hcenter htailwidth ⊢
  calc
    (uniformExpCellRange a b
      (uniformExpQuotientPrecision (b - a)
        (Rat.ne_of_gt ((Rat.lt_iff_sub_pos a b).mp hab)) n)).width <=
        3 * (b - a) + 34 * (b - a) ^ 2 +
          6 * uniformExpTailMagnitude
            (uniformExpQuotientPrecision (b - a)
              (Rat.ne_of_gt ((Rat.lt_iff_sub_pos a b).mp hab)) n) := hwidth
    _ <= (precisionAtStage n).val / 4 +
        (precisionAtStage n).val / 4 :=
      rat_add_le_add hcenter htailwidth
    _ <= (precisionAtStage n).val / 2 := by grind

theorem uniformExpExpandedCellRange_width_le
    (n : Nat) {a b : Rat}
    (ha : 0 <= a) (hb : b <= 1) (hab : a < b)
    (hstep : b - a <= (precisionAtStage n).val / 200) :
    (QInterval.expand
      (uniformExpCellRange a b
        (uniformExpQuotientPrecision (b - a)
          (Rat.ne_of_gt ((Rat.lt_iff_sub_pos a b).mp hab)) n))
      (2 * (precisionAtStage n).val)).width <=
      9 * (precisionAtStage n).val / 2 := by
  have hrange := uniformExpCellRange_width_le_at_quotient_stage
    n ha hb hab hstep
  rw [QInterval.expand_width]
  have hp : 0 <= (precisionAtStage n).val :=
    Rat.le_of_lt (precisionAtStage n).property
  calc
    (uniformExpCellRange a b
        (uniformExpQuotientPrecision (b - a)
          (Rat.ne_of_gt ((Rat.lt_iff_sub_pos a b).mp hab)) n)).width +
        2 * (2 * (precisionAtStage n).val) <=
        (precisionAtStage n).val / 2 +
          2 * (2 * (precisionAtStage n).val) :=
      rat_add_le_add hrange Rat.le_refl
    _ <= 9 * (precisionAtStage n).val / 2 := by grind

theorem uniformExpExpandedCellRange_width_le_eps
    (eps : QPos) (n : Nat) {a b : Rat}
    (ha : 0 <= a) (hb : b <= 1) (hab : a < b)
    (hstep : b - a <= (precisionAtStage n).val / 200)
    (hprecision : (precisionAtStage n).val <= eps.val / 5) :
    (QInterval.expand
      (uniformExpCellRange a b
        (uniformExpQuotientPrecision (b - a)
          (Rat.ne_of_gt ((Rat.lt_iff_sub_pos a b).mp hab)) n))
      (2 * (precisionAtStage n).val)).width <= eps.val := by
  have hw := uniformExpExpandedCellRange_width_le n ha hb hab hstep
  have hw' :
      (uniformExpCellRange a b
          (uniformExpQuotientPrecision (b - a)
            (Rat.ne_of_gt ((Rat.lt_iff_sub_pos a b).mp hab)) n)).width +
        2 * (2 * (precisionAtStage n).val) <=
      9 * (precisionAtStage n).val / 2 := by
    simpa [QInterval.expand_width] using hw
  have heps : 0 <= eps.val := Rat.le_of_lt eps.property
  rw [QInterval.expand_width]
  calc
    (uniformExpCellRange a b
        (uniformExpQuotientPrecision (b - a)
          (Rat.ne_of_gt ((Rat.lt_iff_sub_pos a b).mp hab)) n)).width +
        2 * (2 * (precisionAtStage n).val) <=
        9 * (precisionAtStage n).val / 2 := hw'
    _ <= eps.val := by grind

theorem uniformExpFTCLeftPoint_bounds (eps : QPos) (k : Nat)
    (hk : k < uniformExpFTCPieces eps) :
    0 <= leftPoint 0 1 (uniformExpFTCPieces eps) k /\
      leftPoint 0 1 (uniformExpFTCPieces eps) (k + 1) <= 1 := by
  have hn := uniformExpFTCPieces_pos eps
  constructor
  · have h0 := leftPoint_monotone hn (by native_decide : (0 : Rat) <= 1)
        (Nat.zero_le k)
    simpa [leftPoint_zero] using h0
  · have h1 := leftPoint_monotone hn (by native_decide : (0 : Rat) <= 1)
        (Nat.succ_le_of_lt hk)
    have hend := leftPoint_endpoint (a := (0 : Rat)) (b := 1) hn
    calc
      leftPoint 0 1 (uniformExpFTCPieces eps) (k + 1) <=
          leftPoint 0 1 (uniformExpFTCPieces eps)
            (uniformExpFTCPieces eps) := h1
      _ = 1 := hend

theorem uniformExpFTCLeftPoint_strict (eps : QPos) (k : Nat)
    (hk : k < uniformExpFTCPieces eps) :
    leftPoint 0 1 (uniformExpFTCPieces eps) k <
      leftPoint 0 1 (uniformExpFTCPieces eps) (k + 1) := by
  apply (Rat.lt_iff_sub_pos _ _).mpr
  rw [leftPoint_step]
  unfold mesh
  rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps)), Rat.div_def]
  exact Rat.mul_pos (by native_decide)
    ((Rat.inv_pos).2 ((Rat.natCast_pos).2
      (uniformExpFTCPieces_pos eps)))

theorem uniformExpFTCLeftPoint_step_le (eps : QPos) (k : Nat)
    (hk : k < uniformExpFTCPieces eps) :
    leftPoint 0 1 (uniformExpFTCPieces eps) (k + 1) -
        leftPoint 0 1 (uniformExpFTCPieces eps) k <=
      (precisionAtStage (uniformExpFTCIndex eps)).val / 200 := by
  rw [leftPoint_step]
  exact uniformExpFTCPieces_mesh_le eps

theorem uniformExpFTCMesh_ne (eps : QPos) :
    mesh 0 1 (uniformExpFTCPieces eps) ≠ 0 := by
  unfold mesh
  rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
  exact Rat.ne_of_gt (by
    rw [Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2
        (uniformExpFTCPieces_pos eps))))

theorem uniformExpEndpointBox_width_le_at_quotient_stage
    (n : Nat) {a b : Rat}
    (ha : 0 <= a) (hb : b <= 1) (hab : a < b) :
    (uniformExpBox a
      (uniformExpQuotientPrecision (b - a)
        (Rat.ne_of_gt ((Rat.lt_iff_sub_pos a b).mp hab)) n)).width +
      (uniformExpBox b
        (uniformExpQuotientPrecision (b - a)
          (Rat.ne_of_gt ((Rat.lt_iff_sub_pos a b).mp hab)) n)).width <=
      (precisionAtStage n).val / 3 := by
  let h : Rat := b - a
  have hpos : 0 < h := by
    dsimp [h]
    exact (Rat.lt_iff_sub_pos a b).mp hab
  have hh : h ≠ 0 := Rat.ne_of_gt hpos
  let stage : Nat := uniformExpQuotientPrecision h hh n
  have htail := uniformExpTailMagnitude_le_quotientTolerance h hh n
  have hqabs : qabs h = h := qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)
  have htail' :
      uniformExpTailMagnitude stage <=
        (precisionAtStage n).val * h / 24 := by
    simpa [stage, uniformExpQuotientTailTolerance, hqabs] using htail
  have hleone : h <= 1 := by
    dsimp [h]
    grind
  have hp : 0 <= (precisionAtStage n).val :=
    Rat.le_of_lt (precisionAtStage n).property
  have hbox :
      2 * uniformExpTailRadius stage <=
        (precisionAtStage n).val / 6 := by
    unfold uniformExpTailRadius
    have hmul := Rat.mul_le_mul_of_nonneg_left htail'
      (by native_decide : (0 : Rat) <= 4)
    calc
      2 * (2 * uniformExpTailMagnitude stage) <=
          4 * uniformExpTailMagnitude stage := by grind
      _ <=
          4 * ((precisionAtStage n).val * h / 24) := hmul
      _ = (precisionAtStage n).val * h / 6 := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= (precisionAtStage n).val / 6 := by
        have := Rat.mul_le_mul_of_nonneg_left hleone hp
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hsum :
      (uniformExpBox a stage).width +
          (uniformExpBox b stage).width <= (precisionAtStage n).val / 3 := by
    rw [uniformExpBox_width, uniformExpBox_width]
    calc
      2 * uniformExpTailRadius stage + 2 * uniformExpTailRadius stage <=
          (precisionAtStage n).val / 6 +
            (precisionAtStage n).val / 6 := rat_add_le_add hbox hbox
      _ <= (precisionAtStage n).val / 3 := by grind
  simpa [stage, h] using hsum

theorem uniformExpCellRange_width_le_eps
    (eps : QPos) {a b : Rat}
    (ha : 0 <= a) (hb : b <= 1) (hab : a <= b)
    (hstep : b - a <= eps.val / 200) :
    (uniformExpCellRange a b (uniformExpCellStage eps)).width <= eps.val := by
  have hwidth := uniformExpCellRange_width_le
    (uniformExpCellStage eps) ha hb hab
  have hnonneg : 0 <= b - a := by
    grind [Rat.sub_eq_add_neg]
  have hleone : b - a <= 1 := by
    grind [Rat.sub_eq_add_neg]
  have hsq : (b - a) ^ 2 <= b - a := by
    rw [show (b - a) ^ 2 = (b - a) * (b - a) by
      simp [Rat.pow_succ]]
    have hmul := Rat.mul_le_mul_of_nonneg_left hleone hnonneg
    grind
  have hcenter :
      3 * (b - a) + 34 * (b - a) ^ 2 <= eps.val / 4 := by
    have hlinear : 3 * (b - a) + 34 * (b - a) ^ 2 <=
        37 * (b - a) := by
      have hsq' := Rat.mul_le_mul_of_nonneg_left hsq
        (by native_decide : (0 : Rat) <= 34)
      grind
    have hscaled := Rat.mul_le_mul_of_nonneg_left hstep
      (by native_decide : (0 : Rat) <= 37)
    calc
      3 * (b - a) + 34 * (b - a) ^ 2 <= 37 * (b - a) := hlinear
      _ <= 37 * (eps.val / 200) := hscaled
      _ <= eps.val / 4 := by grind
  have htail := uniformExpCellTailSum_le_half eps
  have hpieces : 1 <= (uniformExpCellPieces eps : Rat) := by
    have hp := uniformExpCellPieces_pos eps
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp))
  have hradius_nonneg :
      0 <= 2 * uniformExpTailRadius (uniformExpCellStage eps) := by
    unfold uniformExpTailRadius
    exact Rat.mul_nonneg (by native_decide)
      (Rat.mul_nonneg (by native_decide)
        (uniformExpTailMagnitude_nonneg _))
  have hradius :
      2 * uniformExpTailRadius (uniformExpCellStage eps) <= eps.val / 2 := by
    calc
      2 * uniformExpTailRadius (uniformExpCellStage eps) =
          1 * (2 * uniformExpTailRadius (uniformExpCellStage eps)) := by
            grind
      _ <= (uniformExpCellPieces eps : Rat) *
          (2 * uniformExpTailRadius (uniformExpCellStage eps)) := by
            exact Rat.mul_le_mul_of_nonneg_right hpieces hradius_nonneg
      _ <= eps.val / 2 := htail
  unfold uniformExpTailRadius at hwidth
  have htailwidth :
      6 * uniformExpTailMagnitude (uniformExpCellStage eps) <=
        3 * eps.val / 4 := by
    have hscaled := Rat.mul_le_mul_of_nonneg_left hradius
      (by native_decide : (0 : Rat) <= 3 / 2)
    calc
      6 * uniformExpTailMagnitude (uniformExpCellStage eps) =
          (3 / 2 : Rat) *
            (2 * (2 * uniformExpTailMagnitude (uniformExpCellStage eps))) := by
              grind
      _ <= (3 / 2 : Rat) * (eps.val / 2) := hscaled
      _ = 3 * eps.val / 4 := by grind
  calc
    (uniformExpCellRange a b (uniformExpCellStage eps)).width <=
        3 * (b - a) + 34 * (b - a) ^ 2 +
          6 * uniformExpTailMagnitude (uniformExpCellStage eps) := hwidth
    _ <= eps.val / 4 + 3 * eps.val / 4 :=
      rat_add_le_add hcenter htailwidth
    _ <= eps.val := by grind

theorem uniformExpUniformCellRange_width_le_eps
    (eps : QPos) (k : Nat)
    (hk : k < uniformExpCellPieces eps) :
    (uniformExpCellRange
      ((RationalPartition.uniform 0 1 (uniformExpCellPieces eps)
        (uniformExpCellPieces_pos eps) (by native_decide)).cell k hk).lower
      ((RationalPartition.uniform 0 1 (uniformExpCellPieces eps)
        (uniformExpCellPieces_pos eps) (by native_decide)).cell k hk).upper
      (uniformExpCellStage eps)).width <= eps.val := by
  let P := RationalPartition.uniform 0 1 (uniformExpCellPieces eps)
    (uniformExpCellPieces_pos eps) (by native_decide)
  let C := P.cell k hk
  have hstep : C.upper - C.lower <= eps.val / 200 := by
    rw [show C.upper - C.lower = mesh 0 1 (uniformExpCellPieces eps) by
      dsimp [C, P]
      exact RationalPartition.uniform_cell_width 0 1
        (uniformExpCellPieces eps) (uniformExpCellPieces_pos eps)
        (by native_decide) k hk]
    exact uniformExpCellMesh_le eps
  exact uniformExpCellRange_width_le_eps eps C.lower_mem C.upper_mem
    C.ordered hstep

/-- The `ε |h| / 24` tail allowance simultaneously controls the center tail
in a quotient, the quotient-box width, and the derivative-box width whenever
both rational endpoints lie in a unit interval. -/
private theorem uniformExp_tail_transport_budgets
    {h t : Rat} (hh : h ≠ 0) (habs : qabs h <= 1)
    (eps : QPos) (ht : t <= eps.val * qabs h / 24) :
    6 * t / qabs h + 2 * t <= eps.val / 3 /\
      8 * t / qabs h <= eps.val / 3 /\
      4 * t <= eps.val / 6 := by
  have hApos : 0 < qabs h := qabs_pos_of_ne hh
  have hAinv0 : 0 <= (qabs h)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hApos)
  have hcancel : qabs h * (qabs h)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ (Rat.ne_of_gt hApos)
  have htdiv : t / qabs h <= eps.val / 24 := by
    calc
      t / qabs h = t * (qabs h)⁻¹ := Rat.div_def _ _
      _ <= (eps.val * qabs h / 24) * (qabs h)⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right ht hAinv0
      _ = eps.val / 24 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hsix : 6 * t / qabs h <= eps.val / 4 := by
    calc
      6 * t / qabs h = 6 * (t / qabs h) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc]
      _ <= 6 * (eps.val / 24) :=
        Rat.mul_le_mul_of_nonneg_left htdiv (by native_decide)
      _ = eps.val / 4 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have height : 8 * t / qabs h <= eps.val / 3 := by
    calc
      8 * t / qabs h = 8 * (t / qabs h) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc]
      _ <= 8 * (eps.val / 24) :=
        Rat.mul_le_mul_of_nonneg_left htdiv (by native_decide)
      _ = eps.val / 3 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have heps12pos : 0 < eps.val / 12 := by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide))
  have htwo : 2 * t <= eps.val / 12 := by
    calc
      2 * t <= 2 * (eps.val * qabs h / 24) :=
        Rat.mul_le_mul_of_nonneg_left ht (by native_decide)
      _ = (eps.val / 12) * qabs h := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= (eps.val / 12) * 1 :=
        Rat.mul_le_mul_of_nonneg_left habs (Rat.le_of_lt heps12pos)
      _ = eps.val / 12 := by rw [Rat.mul_one]
  have hfour : 4 * t <= eps.val / 6 := by
    calc
      4 * t = 2 * (2 * t) := by grind [Rat.mul_assoc]
      _ <= 2 * (eps.val / 12) :=
        Rat.mul_le_mul_of_nonneg_left htwo (by native_decide)
      _ = eps.val / 6 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  constructor
  · calc
      6 * t / qabs h + 2 * t <= eps.val / 4 + eps.val / 12 :=
        rat_add_le_add hsix htwo
      _ = eps.val / 3 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  exact ⟨height, hfour⟩

/-- The same tail allowance remains sufficient when both endpoints are in a
diameter-two interval.  The center budget is intentionally looser than on a
unit interval, while the quotient and output-box widths retain the same
step-scaled estimates. -/
private theorem uniformExp_tail_transport_budgets_of_step_le_two
    {h t : Rat} (hh : h ≠ 0) (habs : qabs h <= 2)
    (eps : QPos) (ht : t <= eps.val * qabs h / 24) :
    6 * t / qabs h + 2 * t <= eps.val / 2 /\
      8 * t / qabs h <= eps.val / 3 /\
      4 * t <= eps.val / 3 := by
  have hApos : 0 < qabs h := qabs_pos_of_ne hh
  have hAinv0 : 0 <= (qabs h)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hApos)
  have hcancel : qabs h * (qabs h)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ (Rat.ne_of_gt hApos)
  have htdiv : t / qabs h <= eps.val / 24 := by
    calc
      t / qabs h = t * (qabs h)⁻¹ := Rat.div_def _ _
      _ <= (eps.val * qabs h / 24) * (qabs h)⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right ht hAinv0
      _ = eps.val / 24 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hsix : 6 * t / qabs h <= eps.val / 4 := by
    calc
      6 * t / qabs h = 6 * (t / qabs h) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc]
      _ <= 6 * (eps.val / 24) :=
        Rat.mul_le_mul_of_nonneg_left htdiv (by native_decide)
      _ = eps.val / 4 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have height : 8 * t / qabs h <= eps.val / 3 := by
    calc
      8 * t / qabs h = 8 * (t / qabs h) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc]
      _ <= 8 * (eps.val / 24) :=
        Rat.mul_le_mul_of_nonneg_left htdiv (by native_decide)
      _ = eps.val / 3 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have heps12pos : 0 < eps.val / 12 := by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide))
  have htwo : 2 * t <= eps.val / 6 := by
    calc
      2 * t <= 2 * (eps.val * qabs h / 24) :=
        Rat.mul_le_mul_of_nonneg_left ht (by native_decide)
      _ = (eps.val / 12) * qabs h := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= (eps.val / 12) * 2 :=
        Rat.mul_le_mul_of_nonneg_left habs (Rat.le_of_lt heps12pos)
      _ = eps.val / 6 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hfour : 4 * t <= eps.val / 3 := by
    calc
      4 * t = 2 * (2 * t) := by grind [Rat.mul_assoc]
      _ <= 2 * (eps.val / 6) :=
        Rat.mul_le_mul_of_nonneg_left htwo (by native_decide)
      _ = eps.val / 3 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  constructor
  · calc
      6 * t / qabs h + 2 * t <= eps.val / 4 + eps.val / 6 :=
        rat_add_le_add hsix htwo
      _ <= eps.val / 2 := by
        have heps : 0 <= eps.val := Rat.le_of_lt eps.property
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  exact ⟨height, hfour⟩

private theorem uniformExp_rat_pow_add (q : Rat) (m n : Nat) :
    q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show m + (n + 1) = m + n + 1 by omega]
      rw [Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem uniformExp_half_pow_antitone (N n : Nat) (hN : N <= n) :
    ((1 : Rat) / 2) ^ n <= ((1 : Rat) / 2) ^ N := by
  let k := n - N
  have hNk : N + k = n := by
    dsimp [k]
    exact Nat.add_sub_of_le hN
  rw [← hNk, uniformExp_rat_pow_add]
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
            Rat.mul_le_mul_of_nonneg_left hhalf1 (Rat.pow_nonneg hhalf0)
          _ = ((1 : Rat) / 2) ^ k := by rw [Rat.mul_one]
          _ <= 1 := ih
  calc
    ((1 : Rat) / 2) ^ N * ((1 : Rat) / 2) ^ k <=
        ((1 : Rat) / 2) ^ N * 1 :=
      Rat.mul_le_mul_of_nonneg_left hpow1 hpow0
    _ = ((1 : Rat) / 2) ^ N := by rw [Rat.mul_one]

private theorem uniformExpBox_widths_shrink (x : Rat) :
    RealRaw.WidthsShrinkToZero (uniformExpBox x) := by
  intro eps
  let bound : Rat := 4 * uniformExpTailMagnitude 0
  let N : Nat := RationalMajorant.halfDecayShift bound eps
  refine ⟨N, ?_⟩
  intro n hn
  have hbound : 0 <= bound := by
    dsimp [bound]
    exact Rat.mul_nonneg (by native_decide) (uniformExpTailMagnitude_nonneg 0)
  have hwidth := uniformExpBox_width_le_geometric x n
  have hpow := uniformExp_half_pow_antitone N n hn
  have hscaled : bound * ((1 : Rat) / 2) ^ n <=
      bound * ((1 : Rat) / 2) ^ N :=
    Rat.mul_le_mul_of_nonneg_left hpow hbound
  have hfinal := RationalMajorant.halfDecayShift_spec hbound eps
  exact Rat.le_trans hwidth (Rat.le_trans hscaled hfinal)

/-- A certified factorial-series evaluator with one common stage schedule for
all rational inputs in the box `|x| <= 2`. -/
def uniformExpRaw (x : Rat) : RealRaw where
  compute := uniformExpBox x
  rate := .geometric 0 (4 * uniformExpTailMagnitude 0) ((1 : Rat) / 2)
    (by native_decide) (by native_decide)
    (fun n _ => uniformExpBox_width_le_geometric x n)

theorem uniformExpRaw_compute (x : Rat) (n : Nat) :
    (uniformExpRaw x).compute n = uniformExpBox x n := rfl

def uniformExpSymmetricCellRadius (a b : Rat) (n : Nat) : Rat :=
  9 * (b - a) + 34 * (b - a) ^ 2 +
    2 * uniformExpTailMagnitude n + uniformExpTailRadius n

def uniformExpSymmetricCellRange (a b : Rat) (n : Nat) : QInterval :=
  intervalAround (uniformExpCenter a n)
    (uniformExpSymmetricCellRadius a b n)

theorem uniformExpSymmetricCellRange_contains
    {a b x : Rat} (n : Nat)
    (ha : -1 <= a) (hb : b <= 1) (hab : a < b)
    (hax : a <= x) (hxb : x <= b) :
    (uniformExpSymmetricCellRange a b n).ContainsInterval
      ((uniformExpRaw x).compute n) := by
  have hqa : qabs a <= 2 := by
    unfold qabs
    by_cases hneg : a < 0
    · rw [if_pos hneg]
      grind
    · rw [if_neg hneg]
      exact Rat.le_trans (Rat.le_trans hax hxb)
        (Rat.le_trans hb (by native_decide))
  have hqx : qabs x <= 2 := by
    unfold qabs
    by_cases hneg : x < 0
    · rw [if_pos hneg]
      grind
    · rw [if_neg hneg]
      exact Rat.le_trans hxb (Rat.le_trans hb (by native_decide))
  have hxa : 0 <= x - a := by grind
  have hba : 0 <= b - a := by grind
  have hvar :
      qabs (uniformExpCenter x n - uniformExpCenter a n) <=
        9 * (b - a) + 34 * (b - a) ^ 2 +
          2 * uniformExpTailMagnitude n := by
    by_cases hxeq : x = a
    · subst hxeq
      have hp : 0 <= (b - x) ^ 2 := Rat.pow_nonneg hba
      have hlin : 0 <= 9 * (b - x) :=
        Rat.mul_nonneg (by native_decide) hba
      have htail : 0 <= 2 * uniformExpTailMagnitude n :=
        Rat.mul_nonneg (by native_decide)
          (uniformExpTailMagnitude_nonneg n)
      have hR : 0 <= 9 * (b - x) + 34 * (b - x) ^ 2 +
          2 * uniformExpTailMagnitude n := by
        grind
      have hzero : qabs (uniformExpCenter x n - uniformExpCenter x n) = 0 := by
        rw [Rat.sub_self]
        native_decide
      rw [hzero]
      exact hR
    · have haxlt : a < x := (Rat.lt_iff_le_and_ne).2 ⟨hax, by grind⟩
      have hsmall := uniformExpCenter_difference_qabs_le n hqa hqx haxlt
      have hsq : (x - a) ^ 2 <= (b - a) ^ 2 := by
        have hsq1 := Rat.mul_le_mul_of_nonneg_right
          (show x - a <= b - a by grind) hxa
        have hsq2 := Rat.mul_le_mul_of_nonneg_left
          (show x - a <= b - a by grind) hba
        calc
          (x - a) ^ 2 = (x - a) * (x - a) := by
            rw [show 2 = 1 + 1 by omega, Rat.pow_succ, Rat.pow_succ]
            simp
          _ <= (b - a) * (x - a) := hsq1
          _ <= (b - a) * (b - a) := hsq2
          _ = (b - a) ^ 2 := by
            rw [show 2 = 1 + 1 by omega, Rat.pow_succ, Rat.pow_succ]
            simp
      have hlin := Rat.mul_le_mul_of_nonneg_left
        (show x - a <= b - a by grind) (by native_decide : (0 : Rat) <= 9)
      have hquad := Rat.mul_le_mul_of_nonneg_left hsq
        (by native_decide : (0 : Rat) <= 34)
      calc
        qabs (uniformExpCenter x n - uniformExpCenter a n) <=
            9 * (x - a) + 34 * (x - a) ^ 2 +
              2 * uniformExpTailMagnitude n := hsmall
        _ <= 9 * (b - a) + 34 * (b - a) ^ 2 +
              2 * uniformExpTailMagnitude n := by
          exact rat_add_le_add (rat_add_le_add hlin hquad)
            Rat.le_refl
  rw [uniformExpRaw_compute]
  unfold uniformExpSymmetricCellRange uniformExpSymmetricCellRadius
  unfold uniformExpBox intervalAround QInterval.ContainsInterval
  have htail : 0 <= uniformExpTailRadius n := by
    unfold uniformExpTailRadius
    exact Rat.mul_nonneg (by native_decide)
      (uniformExpTailMagnitude_nonneg n)
  have hlo0 : uniformExpCenter a n - uniformExpCenter x n <=
      qabs (uniformExpCenter x n - uniformExpCenter a n) := by
    calc
      uniformExpCenter a n - uniformExpCenter x n =
          -(uniformExpCenter x n - uniformExpCenter a n) := by grind
      _ <= qabs (-(uniformExpCenter x n - uniformExpCenter a n)) :=
        self_le_qabs _
      _ = qabs (uniformExpCenter x n - uniformExpCenter a n) := qabs_neg _
  have hhi0 : uniformExpCenter x n - uniformExpCenter a n <=
      qabs (uniformExpCenter x n - uniformExpCenter a n) :=
    self_le_qabs _
  have hlo := Rat.le_trans hlo0 hvar
  have hhi := Rat.le_trans hhi0 hvar
  grind

theorem uniformExpSymmetricCellRange_width (a b : Rat) (n : Nat) :
    (uniformExpSymmetricCellRange a b n).width =
      2 * (9 * (b - a) + 34 * (b - a) ^ 2 +
        2 * uniformExpTailMagnitude n + uniformExpTailRadius n) := by
  unfold uniformExpSymmetricCellRange uniformExpSymmetricCellRadius
  rw [intervalAround_width]
  grind

def uniformExpSymmetricFTCPieces (eps : QPos) : Nat :=
  2 * uniformExpFTCPieces eps

theorem uniformExpSymmetricFTCPieces_pos (eps : QPos) :
    0 < uniformExpSymmetricFTCPieces eps := by
  unfold uniformExpSymmetricFTCPieces
  exact Nat.mul_pos (by native_decide) (uniformExpFTCPieces_pos eps)

def uniformExpSymmetricFTCPartition (eps : QPos) :
    RationalPartition (-1 : Rat) 1 :=
  RationalPartition.uniform (-1) 1
    (uniformExpSymmetricFTCPieces eps)
    (uniformExpSymmetricFTCPieces_pos eps) (by native_decide)

theorem uniformExpSymmetricFTCPartition_cell_width
    (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition eps).pieces) :
    ((uniformExpSymmetricFTCPartition eps).cell k hk).width =
      mesh 0 1 (uniformExpFTCPieces eps) := by
  have hk' : k < uniformExpSymmetricFTCPieces eps := by
    exact hk
  unfold uniformExpSymmetricFTCPartition
  rw [RationalPartition.uniform_cell_width (-1) 1
    (uniformExpSymmetricFTCPieces eps)
    (uniformExpSymmetricFTCPieces_pos eps) (by native_decide) k hk']
  unfold uniformExpSymmetricFTCPieces mesh
  rw [if_neg (by
    exact Nat.ne_of_gt (uniformExpSymmetricFTCPieces_pos eps))]
  rw [if_neg (by
    exact Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem uniformExpSymmetricFTCPartition_cell_endpoints
    (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition eps).pieces) :
    ((uniformExpSymmetricFTCPartition eps).cell k hk).lower =
        leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) k ∧
      ((uniformExpSymmetricFTCPartition eps).cell k hk).upper =
        leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) (k + 1) := by
  constructor <;> rfl

/-- At a common stage, the next finite Taylor prefix differs from the raw-box
center by exactly one factorial monomial. -/
theorem qabs_expTaylorPrefix_sub_uniformExpCenter_le (x : Rat)
    (hx : qabs x <= 2) (n : Nat) :
    qabs (FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x -
      uniformExpCenter x n) <= uniformExpTailMagnitude n := by
  rw [← powerSeriesCenterAtTerms_eq_expTaylorPrefix]
  unfold uniformExpCenter
  rw [powerSeriesCenterAtTerms_succ]
  have hcancel :
      powerSeriesCenterAtTerms x (uniformExpTailTerms n) +
          powerSeriesTermAtTerms x (uniformExpTailTerms n) -
        powerSeriesCenterAtTerms x (uniformExpTailTerms n) =
      powerSeriesTermAtTerms x (uniformExpTailTerms n) := by
    grind [Rat.sub_eq_add_neg]
  rw [hcancel, powerSeriesTermAtTerms_eq_expCoeff_monomial]
  simpa [uniformExpTailMagnitude] using
    FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm
      (C := (2 : Rat)) (x := x) (by native_decide) hx
      (uniformExpTailTerms n)

/-- The common finite exponential prefix has its matching common raw-box
center as the finite Taylor derivative polynomial.  Its remaining secant
error is the explicit finite coefficient supplied by
`SecantDerivativeBound`. -/
theorem uniformExpTaylorPrefix_secant_error
    {x h : Rat} (hh : h ≠ 0) (hx : qabs x <= 2)
    (hxh : qabs (x + h) <= 2) (n : Nat) :
    qabs
      ((FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
        FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) / h -
        uniformExpCenter x n) <=
      qabs h *
        (FinitePolynomial.expTaylorPrefixSecantBound 2
          (uniformExpTailTerms n) (by native_decide)).errorCoefficient := by
  have hfinite :=
    (FinitePolynomial.expTaylorPrefixSecantBound 2
      (uniformExpTailTerms n) (by native_decide)).error_bound
      x h hh hx hxh
  change qabs
      ((FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
        FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) / h -
        powerSeriesCenterAtTerms x (uniformExpTailTerms n)) <= _
  rw [← expTaylorDerivativePrefix_eq_powerSeriesCenterAtTerms]
  exact hfinite

/-- The finite exponential secant error in the common bounded-input schedule
has one coefficient, `34`, for every stage.  The bound is independent of the
factorial prefix length, which is what makes a single step modulus possible. -/
theorem uniformExpTaylorPrefix_secant_error_le_thirty_four
    {x h : Rat} (hh : h ≠ 0) (hx : qabs x <= 2)
    (hxh : qabs (x + h) <= 2) (n : Nat) :
    qabs
      ((FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
        FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) / h -
        uniformExpCenter x n) <=
      qabs h * 34 := by
  have hfinite := FinitePolynomial.expTaylorPrefix_secant_error_le_thirty_four
    (x := x) (h := h) hh hx hxh (uniformExpTailTerms n)
  change qabs
      ((FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) (x + h) -
        FinitePolynomial.expTaylorPrefix (uniformExpTailTerms n) x) / h -
        powerSeriesCenterAtTerms x (uniformExpTailTerms n)) <= _
  rw [← expTaylorDerivativePrefix_eq_powerSeriesCenterAtTerms]
  exact hfinite

theorem uniformExpRaw_valid (x : Rat) (hx : qabs x <= 2) :
    (uniformExpRaw x).Valid := by
  unfold RealRaw.Valid RealRaw.ValidCompute uniformExpRaw
  constructor
  · exact uniformExpBox_ordered x
  · constructor
    · intro n m hnm
      have hnest := uniformExpBox_nested x hx n m hnm
      have hwidth := uniformExpBox_ordered x m
      have hordered : (uniformExpBox x m).lo <= (uniformExpBox x m).hi := by
        unfold QInterval.width at hwidth
        grind [Rat.sub_eq_add_neg]
      exact ⟨hnest.1, hordered, hnest.2⟩
    · exact uniformExpBox_widths_shrink x

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

private theorem uniformExpTailTerms_le_powerSeriesTerms (x : Rat) (n : Nat) :
    uniformExpTailTerms n <= expPowerSeriesTerms x n := by
  have hstart : uniformExpTailStart = 5 := by native_decide
  unfold uniformExpTailTerms expPowerSeriesTerms
  rw [hstart]
  omega

/-- The fixed bounded-input exponential boxes overlap the project’s existing
adaptive factorial-series boxes at every common stage.  The proof compares
only two finite rational prefixes; the remaining finite gap is paid for by
the common factorial tail radius. -/
theorem uniformExpRaw_equiv_expPowerSeries (x : Rat) (hx : qabs x <= 2) :
    (uniformExpRaw x).Equiv (expPowerSeries x) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  rw [RealRaw.compareAt_overlap_iff]
  let N : Nat := uniformExpTailTerms n
  let M : Nat := expPowerSeriesTerms x n
  have hNM : N <= M := by
    dsimp [N, M]
    exact uniformExpTailTerms_le_powerSeriesTerms x n
  obtain ⟨k, hMk⟩ := Nat.exists_eq_add_of_le hNM
  have hcenter :
      qabs (powerSeriesCenterAtTerms x M - powerSeriesCenterAtTerms x N) <=
        uniformExpTailRadius n := by
    rw [hMk]
    calc
      qabs (powerSeriesCenterAtTerms x (N + k) -
          powerSeriesCenterAtTerms x N) <=
          RationalMajorant.factorialTailPartial 2 N k :=
        qabs_uniformExpCenter_add_sub_le_factorialTailPartial x hx N k
      _ <= 2 * RationalMajorant.factorialTailTerm 2 N :=
        RationalMajorant.factorialTailPartial_bound (C := (2 : Rat))
          (N := N) (by native_decide) (by simpa [N] using uniform_exp_tail_start n) k
      _ = uniformExpTailRadius n := by
        unfold uniformExpTailRadius uniformExpTailMagnitude
        dsimp [N]
  have hright :
      powerSeriesCenterAtTerms x M - powerSeriesCenterAtTerms x N <=
        uniformExpTailRadius n :=
    Rat.le_trans (self_le_qabs _) hcenter
  have hleft :
      powerSeriesCenterAtTerms x N - powerSeriesCenterAtTerms x M <=
        uniformExpTailRadius n := by
    calc
      powerSeriesCenterAtTerms x N - powerSeriesCenterAtTerms x M =
          -(powerSeriesCenterAtTerms x M - powerSeriesCenterAtTerms x N) := by
            grind [Rat.sub_eq_add_neg]
      _ <= qabs (-(powerSeriesCenterAtTerms x M -
          powerSeriesCenterAtTerms x N)) := self_le_qabs _
      _ = qabs (powerSeriesCenterAtTerms x M -
          powerSeriesCenterAtTerms x N) := qabs_neg _
      _ <= uniformExpTailRadius n := hcenter
  have hrad : 0 <= powerSeriesTailRadius x n :=
    powerSeriesTailRadius_nonneg_of_ratioBound x (expPowerSeries_ratio_bound x) n
  rw [uniformExpRaw_compute, expPowerSeries_compute_eq,
    powerSeriesCenter_stage_eq]
  change QInterval.Overlaps
    (intervalAround (powerSeriesCenterAtTerms x N) (uniformExpTailRadius n))
    (intervalAround (powerSeriesCenterAtTerms x M) (powerSeriesTailRadius x n))
  unfold QInterval.Overlaps intervalAround
  constructor <;> grind [Rat.sub_eq_add_neg]

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

/-- The already-certified rational-input power-series evaluator, packaged as
a total partial real function.  This is a representation layer only: it makes
the pointwise raw algorithms available to derivative and ODE certificates
without asserting an analytic derivative law. -/
def expPowerSeriesFunction : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ => (expPowerSeries x).compute

/-- The function wrapper evaluates definitionally to the original finite
power-series raw algorithm. -/
theorem expPowerSeriesFunction_evalRaw_eq (x : Rat)
    (hx : expPowerSeriesFunction.definedAt x) :
    expPowerSeriesFunction.evalRaw x hx = expPowerSeries x :=
  rfl

/-- Every rational input of the packaged series function has a valid raw
interval computation. -/
theorem expPowerSeriesFunction_valid (x : Rat)
    (hx : expPowerSeriesFunction.definedAt x) :
    RealRaw.ValidCompute (expPowerSeriesFunction.compute x hx) := by
  change RealRaw.ValidCompute ((expPowerSeries x).compute)
  exact expPowerSeries_valid x

/-- Stable façade for the certified rational-input exponential evaluator.
The algorithm does not depend on a proof that the input is in its domain. -/
def stableExpPowerSeries : StablePartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x => (expPowerSeries x).compute
  rate := expPowerSeriesRate

theorem stableExpPowerSeries_valid (x : Rat) :
    RealRaw.ValidCompute (stableExpPowerSeries.compute x) := by
  change RealRaw.ValidCompute ((expPowerSeries x).compute)
  exact expPowerSeries_valid x

/-- Restrict the certified power-series exponential to a rational closed
interval.  This is the input object for a future proof of `d/dx exp = exp`.
It currently provides validity and totality, not a derivative certificate. -/
def expPowerSeriesOnInterval (a b : Rat) : FunctionOnInterval where
  raw := expPowerSeriesFunction
  lower := a
  upper := b
  defined_on := fun _ _ => trivial
  valid_on := expPowerSeriesFunction_valid

/-- The common-prefix exponential representation on the unit interval.  Its
fixed factorial stage is shared by all rational samples in the interval, so
it is the preferred input for the later two-point difference-quotient proof. -/
def uniformExpOnUnit : FunctionOnInterval where
  raw :=
    { definedAt := fun x => (0 : Rat) <= x /\ x <= 1
      compute := fun x _ => (uniformExpRaw x).compute }
  lower := 0
  upper := 1
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    have hqabs : qabs x <= 2 := by
      rw [qabs_eq_self_of_nonneg hx.1]
      exact Rat.le_trans hx.2 (by native_decide)
    exact uniformExpRaw_valid x hqabs

theorem uniformExpOnUnit_compute (x : Rat)
    (hx : inDomainInterval (0 : Rat) 1 x) (n : Nat) :
    uniformExpOnUnit.compute x hx n = (uniformExpRaw x).compute n := rfl

/-! The common-prefix exponential also carries the weak monotonicity needed
by its inverse search.  The finite center is monotone on `[0,1]`, and both
endpoint boxes use the same symmetric tail radius, so the interval order is
preserved at every stage. -/
def uniformExpOnUnit_nondecreasing :
    NondecreasingOnInterval uniformExpOnUnit := by
  intro x y hx hy hxy n
  have hx' : 0 <= x := by
    have h := hx.1
    change 0 <= x at h
    exact h
  have hy' : y <= 1 := by
    have h := hy.2
    change y <= 1 at h
    exact h
  have hxy' : x <= y := hxy
  have hcenter := uniformExpCenter_mono_on_unit n hx' hy' hxy'
  have hcomputeX : uniformExpOnUnit.compute x hx n = uniformExpBox x n := by
    rfl
  have hcomputeY : uniformExpOnUnit.compute y hy n = uniformExpBox y n := by
    rfl
  rw [hcomputeX, hcomputeY]
  unfold uniformExpBox intervalAround
  have htail : 0 <= uniformExpTailMagnitude n :=
    uniformExpTailMagnitude_nonneg n
  have hradius : 0 <= uniformExpTailRadius n := by
    unfold uniformExpTailRadius
    exact Rat.mul_nonneg (by native_decide) htail
  exact by grind [Rat.sub_eq_add_neg]

/-! The exponential exposes the gap-aware certificate directly.  An inverse
search can therefore choose its factorial stage from the rational bracket
width, rather than from an unobservable limiting value. -/
def uniformExpOnUnit_gapAwareSeparation :
    GapAwareInverseSeparation uniformExpOnUnit where
  kind := .nondecreasing
  outputPrecision := fun {x y} hxy n =>
    uniformExpQuotientPrecision (y - x)
      (Rat.ne_of_gt ((Rat.lt_iff_sub_pos x y).mp hxy)) n
  separated := by
    intro x y hx hy hxy n
    have hx0 := hx.1
    have hy1 := hy.2
    change 0 <= x at hx0
    change y <= 1 at hy1
    have hbox := uniformExpOnUnit_box_separated n hx0 hy1 hxy
    dsimp
    let p : Nat := uniformExpQuotientPrecision (y - x)
      (Rat.ne_of_gt ((Rat.lt_iff_sub_pos x y).mp hxy)) n
    have hcx : uniformExpOnUnit.compute x hx p = uniformExpBox x p := by
      rfl
    have hcy : uniformExpOnUnit.compute y hy p = uniformExpBox y p := by
      rfl
    rw [hcx, hcy]
    simpa [p] using hbox

/-! A public warm-stage façade for inverse search.  It is the same common
factorial computation as `uniformExpOnUnit`, with four finite tail terms
reserved in every requested stage. -/
def uniformExpOnUnitWarm : FunctionOnInterval where
  raw :=
    { definedAt := fun x => (0 : Rat) <= x /\ x <= 1
      compute := fun x _ n => (uniformExpRaw x).compute (n + 4) }
  lower := 0
  upper := 1
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    have hqabs : qabs x <= 2 := by
      rw [qabs_eq_self_of_nonneg hx.1]
      exact Rat.le_trans hx.2 (by native_decide)
    let sigma : RealRaw.StageSchedule :=
      { stage := fun n => n + 4
        monotone := by intro i j hij; omega
        cofinal := by intro target; exact ⟨target, by omega⟩ }
    have hvalid := RealRaw.schedule_valid (uniformExpRaw x)
      (uniformExpRaw_valid x hqabs) sigma
    change RealRaw.Valid (RealRaw.schedule sigma (uniformExpRaw x))
    exact hvalid

theorem uniformExpOnUnitWarm_compute (x : Rat)
    (hx : inDomainInterval (0 : Rat) 1 x) (n : Nat) :
    uniformExpOnUnitWarm.compute x hx n =
      (uniformExpRaw x).compute (n + 4) := rfl

def uniformExpOnUnitWarm_intervalRegular :
    IntervalRegularOn uniformExpOnUnitWarm := by
  refine
    { evalInterval := fun I _ n =>
        uniformExpCellRange I.lo I.hi (n + 4)
      inputPrecision := fun n => 1000 * (n + 1)
      inputPrecision_pos := by
        intro n
        omega
      output_width := ?_
      contains_point_values := ?_ }
  · intro I hI n hwidth
    rcases hI with ⟨hlo, hord, hhi⟩
    have hnonneg : 0 <= I.hi - I.lo := by grind
    have hstep : I.hi - I.lo <=
        1 / ((1000 * (n + 1) : Nat) : Rat) := by
      simpa [QInterval.width] using hwidth
    have hdenpos : 0 < 1000 * (n + 1) := by omega
    have hdenone : 1 <= 1000 * (n + 1) := by omega
    have hleone : I.hi - I.lo <= 1 := by
      have hanti := FTC.one_div_nat_antitone (n := 1)
        (m := 1000 * (n + 1)) (by omega) hdenpos hdenone
      exact Rat.le_trans hstep (by
        simpa only [show ((1 : Nat) : Rat) = 1 by native_decide,
          show (1 : Rat) / 1 = 1 by native_decide] using hanti)
    have hsq : (I.hi - I.lo) ^ 2 <= I.hi - I.lo := by
      rw [show (I.hi - I.lo) ^ 2 =
        (I.hi - I.lo) * (I.hi - I.lo) by simp [Rat.pow_succ]]
      simpa using Rat.mul_le_mul_of_nonneg_left hleone hnonneg
    have hcenter :
        3 * (I.hi - I.lo) + 34 * (I.hi - I.lo) ^ 2 <=
          37 / ((1000 * (n + 1) : Nat) : Rat) := by
      have hlinear :
          3 * (I.hi - I.lo) + 34 * (I.hi - I.lo) ^ 2 <=
            37 * (I.hi - I.lo) := by
        have hsq' := Rat.mul_le_mul_of_nonneg_left hsq
          (by native_decide : (0 : Rat) <= 34)
        grind
      have hscaled := Rat.mul_le_mul_of_nonneg_left hstep
        (by native_decide : (0 : Rat) <= 37)
      calc
        3 * (I.hi - I.lo) + 34 * (I.hi - I.lo) ^ 2 <=
            37 * (I.hi - I.lo) := hlinear
        _ <= 37 * (1 / ((1000 * (n + 1) : Nat) : Rat)) := hscaled
        _ = 37 / ((1000 * (n + 1) : Nat) : Rat) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]
    have hrange := uniformExpCellRange_width_le (n + 4) hlo hhi hord
    have htail := uniformExpTailMagnitude_le_reciprocalHundred_shifted n
    have htail' :
        6 * uniformExpTailMagnitude (n + 4) <=
          6 / (100 * ((n + 1 : Nat) : Rat)) :=
      by simpa [Rat.div_def] using
        Rat.mul_le_mul_of_nonneg_left htail (by native_decide)
    have hresult :
        37 / ((1000 * (n + 1) : Nat) : Rat) +
            6 / (100 * ((n + 1 : Nat) : Rat)) <=
          1 / ((n + 1 : Nat) : Rat) := by
      simp only [Rat.natCast_mul]
      let N : Rat := ((n + 1 : Nat) : Rat)
      change 37 / ((1000 : Rat) * N) +
          6 / ((100 : Rat) * N) <= 1 / N
      have hn : (0 : Rat) < ((n + 1 : Nat) : Rat) :=
        (Rat.natCast_pos).2 (by omega)
      have hne : ((n + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hn
      have h1000 : (1000 : Rat) ≠ 0 := by native_decide
      have h100 : (100 : Rat) ≠ 0 := by native_decide
      have hNcancel := Rat.mul_inv_cancel N (by simpa [N] using hne)
      have h1000cancel := Rat.mul_inv_cancel (1000 : Rat) h1000
      have h100cancel := Rat.mul_inv_cancel (100 : Rat) h100
      apply Rat.le_of_mul_le_mul_right (c :=
        (1000 : Rat) * 100 * N)
      · rw [Rat.div_def, Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      · exact Rat.mul_pos (Rat.mul_pos (by native_decide) (by native_decide))
          (by simpa [N] using hn)
    have hmono := uniformExpCenter_mono_on_unit (n + 4)
      hlo hhi hord
    have htailnonneg := uniformExpTailMagnitude_nonneg (n + 4)
    constructor
    · unfold uniformExpCellRange QInterval.width
      unfold uniformExpTailRadius
      have hdiff : 0 <= uniformExpCenter I.hi (n + 4) -
          uniformExpCenter I.lo (n + 4) := by
        grind [Rat.sub_eq_add_neg]
      have htail4 : 0 <= 4 * uniformExpTailMagnitude (n + 4) := by
        exact Rat.mul_nonneg (by native_decide) htailnonneg
      dsimp
      grind [Rat.sub_eq_add_neg]
    · calc
        (uniformExpCellRange I.lo I.hi (n + 4)).width <=
            3 * (I.hi - I.lo) + 34 * (I.hi - I.lo) ^ 2 +
              6 * uniformExpTailMagnitude (n + 4) := hrange
        _ <= 37 / ((1000 * (n + 1) : Nat) : Rat) +
              6 / (100 * ((n + 1 : Nat) : Rat)) :=
          rat_add_le_add hcenter htail'
        _ <= 1 / ((n + 1 : Nat) : Rat) := hresult
  · intro I hI x hx n hIlo hIhi
    change QInterval.ContainsInterval
      (uniformExpCellRange I.lo I.hi (n + 4))
      ((uniformExpRaw x).compute (n + 4))
    rw [uniformExpRaw_compute]
    exact uniformExpBox_contains_cellRange (n + 4)
      hI.1 hI.2.2 hIlo hIhi

def uniformExpOnUnitWarm_nondecreasing :
    NondecreasingOnInterval uniformExpOnUnitWarm := by
  intro x y hx hy hxy n
  change 0 <= x /\ x <= 1 at hx
  change 0 <= y /\ y <= 1 at hy
  change ((uniformExpRaw x).compute (n + 4)).lo <=
    ((uniformExpRaw y).compute (n + 4)).hi
  rw [uniformExpRaw_compute, uniformExpRaw_compute]
  change (uniformExpBox x (n + 4)).lo <=
    (uniformExpBox y (n + 4)).hi
  unfold uniformExpBox intervalAround
  have hcenter : uniformExpCenter x (n + 4) <=
      uniformExpCenter y (n + 4) :=
    uniformExpCenter_mono_on_unit (n + 4) hx.1 hy.2 hxy
  have htail := uniformExpTailMagnitude_nonneg (n + 4)
  have hdiff : 0 <= uniformExpCenter y (n + 4) -
      uniformExpCenter x (n + 4) := by
    grind [Rat.sub_eq_add_neg]
  change uniformExpCenter x (n + 4) -
      2 * uniformExpTailMagnitude (n + 4) <=
    uniformExpCenter y (n + 4) +
      2 * uniformExpTailMagnitude (n + 4)
  grind [Rat.sub_eq_add_neg]

def uniformExpOnUnitWarm_gapAwareSeparation :
    GapAwareInverseSeparation uniformExpOnUnitWarm where
  kind := .nondecreasing
  outputPrecision := fun {x y} hxy n =>
    uniformExpQuotientPrecision (y - x)
      (Rat.ne_of_gt ((Rat.lt_iff_sub_pos x y).mp hxy)) n
  separated := by
    intro x y hx hy hxy n
    change 0 <= x /\ x <= 1 at hx
    change 0 <= y /\ y <= 1 at hy
    let p := uniformExpQuotientPrecision (y - x)
      (Rat.ne_of_gt ((Rat.lt_iff_sub_pos x y).mp hxy)) n
    have hsep := uniformExpOnUnit_box_separated n hx.1 hy.2 hxy
    have hnx := uniformExpBox_nested x (by
      rw [qabs_eq_self_of_nonneg hx.1]
      exact Rat.le_trans hx.2 (by native_decide)) p (p + 4) (by omega)
    have hny := uniformExpBox_nested y (by
      rw [qabs_eq_self_of_nonneg hy.1]
      exact Rat.le_trans hy.2 (by native_decide)) p (p + 4) (by omega)
    change (uniformExpBox x (p + 4)).hi <
      (uniformExpBox y (p + 4)).lo
    apply (Rat.lt_iff_sub_pos _ _).mpr
    have hsep' := (Rat.lt_iff_sub_pos _ _).mp hsep
    grind [Rat.sub_eq_add_neg]

def uniformExpOnUnitWarm_continuous :
    ContinuousFunctionOnInterval where
  function := uniformExpOnUnitWarm
  regular := uniformExpOnUnitWarm_intervalRegular

def uniformExpOnUnitWarm_gapAwareInvertible :
    GapAwareInvertibleFunctionOnInterval where
  continuous := uniformExpOnUnitWarm_continuous
  source_ordered := by native_decide
  monotone := MonotoneOnInterval.ofNondecreasing
    uniformExpOnUnitWarm_nondecreasing
  separation := uniformExpOnUnitWarm_gapAwareSeparation
  orientation := trivial

/-! The first concrete target for the gap-aware inverse branch is the exact
rational value `1`. Its preimage is the exact rational point `0`; this is the
smallest regression case for the future logarithm evaluator. -/
def uniformExpOnUnitWarm_one_target :
    GapAwareInRangeRaw uniformExpOnUnitWarm_gapAwareInvertible where
  value := RealRaw.ofRat 1
  value_valid := RealRaw.ofRat_valid 1
  rangePrecision := fun n => n
  in_range := by
    intro n
    have h0 : inDomainInterval uniformExpOnUnitWarm.lower
        uniformExpOnUnitWarm.upper 0 := by
      change 0 <= (0 : Rat) /\ (0 : Rat) <= 1
      native_decide
    have h1 : inDomainInterval uniformExpOnUnitWarm.lower
        uniformExpOnUnitWarm.upper 1 := by
      change 0 <= (1 : Rat) /\ (1 : Rat) <= 1
      native_decide
    change (uniformExpOnUnitWarm.compute 0
      h0 n).lo <= 1 /\
      1 <= (uniformExpOnUnitWarm.compute 1
        h1 n).hi
    change ((uniformExpRaw 0).compute (n + 4)).lo <= 1 /\
      1 <= ((uniformExpRaw 1).compute (n + 4)).hi
    rw [uniformExpRaw_compute, uniformExpRaw_compute]
    unfold uniformExpBox intervalAround
    unfold uniformExpTailRadius
    constructor
    · rw [uniformExpCenter_zero]
      have htail := uniformExpTailMagnitude_nonneg (n + 4)
      grind [Rat.sub_eq_add_neg]
    · have hcenter := uniformExpCenter_mono_on_unit (n + 4)
        (x := 0) (y := 1) (by native_decide) (by native_decide)
          (by native_decide)
      rw [uniformExpCenter_zero] at hcenter
      have htail := uniformExpTailMagnitude_nonneg (n + 4)
      grind [Rat.sub_eq_add_neg]

def uniformExpOnUnitWarm_one_search :
    GapAwareInverseBisectionSearch
      uniformExpOnUnitWarm_gapAwareInvertible
      uniformExpOnUnitWarm_one_target where
  compute_preimage := fun _ => { lo := 0, hi := 0 }
  valid_preimage := by
    change RealRaw.ValidCompute (fun _ : Nat => { lo := 0, hi := 0 })
    exact RealRaw.ofRat_valid 0
  preimage_subinterval := by
    intro n
    exact ⟨by native_decide, by native_decide, by native_decide⟩
  value_overlaps := by
    intro n
    change QInterval.Overlaps
      (uniformExpOnUnitWarm_intervalRegular.evalInterval
        { lo := 0, hi := 0 } ⟨by native_decide, by native_decide, by native_decide⟩ n)
      ((RealRaw.ofRat 1).compute n)
    unfold uniformExpOnUnitWarm_intervalRegular
    rw [RealRaw.ofRat_compute]
    change QInterval.Overlaps
      (uniformExpCellRange 0 0 (n + 4)) { lo := 1, hi := 1 }
    unfold uniformExpCellRange
    rw [uniformExpCenter_zero]
    unfold uniformExpTailRadius QInterval.Overlaps
    have htail := uniformExpTailMagnitude_nonneg (n + 4)
    constructor <;> grind [Rat.sub_eq_add_neg]

theorem uniformExpOnUnitWarm_one_preimage_equiv_zero :
    ({ compute := uniformExpOnUnitWarm_one_search.compute_preimage } : RealRaw).Equiv
      (RealRaw.ofRat 0) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  rw [RealRaw.ofRat_compute]
  change QInterval.Overlaps { lo := 0, hi := 0 } { lo := 0, hi := 0 }
  unfold QInterval.Overlaps
  constructor <;> native_decide

/-! A whole family of exact inverse regressions.  The target is the warm-stage
forward computation at a rational source point `r`; the inverse search can
then return the degenerate interval `{r,r}`.  This is the branch-local
computable analogue of the elementary identity `log (exp r) = r`, without
introducing a completed real or pretending that a general target search has
already been implemented. -/
def uniformExpOnUnitWarm_forward_target (r : Rat)
    (hr : inDomainInterval uniformExpOnUnitWarm.lower
      uniformExpOnUnitWarm.upper r) :
    GapAwareInRangeRaw uniformExpOnUnitWarm_gapAwareInvertible where
  value := RealRaw.schedule
    ({ stage := fun n => n + 4
       monotone := by intro i j hij; omega
       cofinal := by intro target; exact ⟨target, by omega⟩ }
      : RealRaw.StageSchedule)
    (uniformExpRaw r)
  value_valid := by
    let sigma : RealRaw.StageSchedule :=
      { stage := fun n => n + 4
        monotone := by intro i j hij; omega
        cofinal := by intro target; exact ⟨target, by omega⟩ }
    change (RealRaw.schedule sigma (uniformExpRaw r)).Valid
    apply RealRaw.schedule_valid
    exact uniformExpRaw_valid r (by
      have hqabs : qabs r <= 2 := by
        rw [qabs_eq_self_of_nonneg hr.1]
        exact Rat.le_trans hr.2 (by native_decide)
      exact hqabs)
  rangePrecision := fun n => n
  in_range := by
    intro n
    change ((uniformExpRaw 0).compute (n + 4)).lo <=
      ((uniformExpRaw r).compute (n + 4)).lo /\
      ((uniformExpRaw r).compute (n + 4)).hi <=
      ((uniformExpRaw 1).compute (n + 4)).hi
    rw [uniformExpRaw_compute, uniformExpRaw_compute,
      uniformExpRaw_compute]
    unfold uniformExpBox intervalAround
    constructor
    · rw [uniformExpCenter_zero]
      have hcenter := uniformExpCenter_mono_on_unit (n + 4)
        (x := 0) (y := r) (by native_decide) hr.2 hr.1
      rw [uniformExpCenter_zero] at hcenter
      have htail := uniformExpTailMagnitude_nonneg (n + 4)
      grind [Rat.sub_eq_add_neg]
    · have hcenter := uniformExpCenter_mono_on_unit (n + 4)
        (x := r) (y := 1) hr.1 (by native_decide) hr.2
      have htail := uniformExpTailMagnitude_nonneg (n + 4)
      grind [Rat.sub_eq_add_neg]

def uniformExpOnUnitWarm_forward_search (r : Rat)
    (hr : inDomainInterval uniformExpOnUnitWarm.lower
      uniformExpOnUnitWarm.upper r) :
    GapAwareInverseBisectionSearch
      uniformExpOnUnitWarm_gapAwareInvertible
      (uniformExpOnUnitWarm_forward_target r hr) where
  compute_preimage := fun _ => { lo := r, hi := r }
  valid_preimage := by
    change RealRaw.ValidCompute (fun _ : Nat => { lo := r, hi := r })
    exact RealRaw.ofRat_valid r
  preimage_subinterval := by
    intro n
    exact ⟨hr.1, Rat.le_refl, hr.2⟩
  value_overlaps := by
    intro n
    change QInterval.Overlaps
      (uniformExpOnUnitWarm_intervalRegular.evalInterval
        { lo := r, hi := r } ⟨hr.1, Rat.le_refl, hr.2⟩ n)
      ((uniformExpRaw r).compute (n + 4))
    unfold uniformExpOnUnitWarm_intervalRegular
    rw [uniformExpRaw_compute]
    change QInterval.Overlaps
      (uniformExpCellRange r r (n + 4))
      (uniformExpBox r (n + 4))
    unfold uniformExpCellRange
    unfold uniformExpBox intervalAround
    have htail := uniformExpTailMagnitude_nonneg (n + 4)
    unfold uniformExpTailRadius at htail ⊢
    constructor <;> grind [Rat.sub_eq_add_neg]

theorem uniformExpOnUnitWarm_forward_preimage_equiv
    (r : Rat) (hr : inDomainInterval uniformExpOnUnitWarm.lower
      uniformExpOnUnitWarm.upper r) :
    ({ compute := (uniformExpOnUnitWarm_forward_search r hr).compute_preimage }
      : RealRaw).Equiv (RealRaw.ofRat r) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  rw [RealRaw.ofRat_compute]
  change QInterval.Overlaps { lo := r, hi := r } { lo := r, hi := r }
  constructor <;> exact Rat.le_refl

/-! A first genuinely target-driven inverse regression.  Here the target is
the rational value `3/2`, so the finite center itself can be used as the
decision map.  The certificate is deliberately finite: it records the
initial endpoint bracket and a requested number of exact rational midpoint
decisions, while the general raw inverse still requires the gap-aware stage
schedule above. -/
def uniformExpCenter_threeHalves_map : Rat -> Rat :=
  fun x => uniformExpCenter x 8

def uniformExpCenter_threeHalves_certificate (k : Nat) :
    FiniteInverseSearchCertificate where
  map := uniformExpCenter_threeHalves_map
  target := 3 / 2
  initialInterval := { lo := 0, hi := 1 }
  stage := k
  ordered := by native_decide
  lower_bracket := by
    change uniformExpCenter 0 8 <= 3 / 2
    rw [uniformExpCenter_zero]
    native_decide
  upper_bracket := by
    change 3 / 2 <= uniformExpCenter 1 8
    native_decide

theorem uniformExpCenter_threeHalves_finite_bisection
    (k : Nat) :
    let C := uniformExpCenter_threeHalves_certificate k
    C.map C.output.lo <= C.target /\
      C.target <= C.map C.output.hi /\
      C.output.width = 1 / (2 ^ k : Rat) := by
  intro C
  refine ⟨C.output_bracket.1, C.output_bracket.2, ?_⟩
  calc
    C.output.width = C.initialInterval.width / (2 ^ C.stage : Rat) :=
      C.output_width
    _ = 1 / (2 ^ k : Rat) := by
      change (1 - 0) / (2 ^ k : Rat) = 1 / (2 ^ k : Rat)
      have h : (1 : Rat) - 0 = 1 := by native_decide
      rw [h]

theorem uniformExpCenter_threeHalves_output_forward_overlap
    (k : Nat) :
    let C := uniformExpCenter_threeHalves_certificate k
    QInterval.Overlaps
      (uniformExpCellRange C.output.lo C.output.hi 8)
      ({ lo := 3 / 2, hi := 3 / 2 } : QInterval) := by
  intro C
  have hbrlo := C.output_bracket.1
  have hbrhi := C.output_bracket.2
  change uniformExpCenter C.output.lo 8 <= 3 / 2 at hbrlo
  change 3 / 2 <= uniformExpCenter C.output.hi 8 at hbrhi
  unfold uniformExpCellRange QInterval.Overlaps
  have htail := uniformExpTailMagnitude_nonneg 8
  unfold uniformExpTailRadius at htail ⊢
  constructor <;> grind [Rat.sub_eq_add_neg]

private theorem uniformExpOnUnit_scheduledRegular_width
    (n : Nat) {I : QInterval}
    (hI : subintervalOf I (0 : Rat) 1)
    (hwidth : I.width <=
      1 / ((200 * (n + 1) : Nat) : Rat)) :
    (uniformExpCellRange I.lo I.hi
      (uniformExpCellStage (precisionAtStage (n + 1)))).width <=
      1 / ((n + 1 : Nat) : Rat) := by
  rcases hI with ⟨hlo, hord, hhi⟩
  have hstep : I.hi - I.lo <=
      (precisionAtStage (n + 1)).val / 200 := by
    have hprec : (precisionAtStage (n + 1)).val =
        1 / ((n + 1 : Nat) : Rat) := by
      simp [precisionAtStage]
    rw [show I.hi - I.lo = I.width by rfl, hprec]
    calc
      I.width <= 1 / ((200 * (n + 1) : Nat) : Rat) := hwidth
      _ = (1 / ((n + 1 : Nat) : Rat)) / 200 := by
        rw [Rat.div_def, Rat.div_def]
        rw [show ((200 * (n + 1) : Nat) : Rat) =
          (200 : Rat) * ((n + 1 : Nat) : Rat) by
            exact Rat.natCast_mul 200 (n + 1)]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hregular := uniformExpCellRange_width_le_eps
    (precisionAtStage (n + 1)) hlo hhi hord hstep
  simpa [precisionAtStage] using hregular

/-! The exponential has an adaptive interval-regularity certificate.  Its
native point evaluator is retained unchanged; the cell evaluator selects a
factorial stage from the requested output tolerance. -/
def uniformExpOnUnit_scheduledIntervalRegular :
    ScheduledIntervalRegularOn uniformExpOnUnit where
  evalInterval := fun I _I n =>
    uniformExpCellRange I.lo I.hi
      (uniformExpCellStage (precisionAtStage (n + 1)))
  evalPrecision := fun n =>
    uniformExpCellStage (precisionAtStage (n + 1))
  inputPrecision := fun n => 200 * (n + 1)
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hwidth
    have h := uniformExpOnUnit_scheduledRegular_width n hI hwidth
    have htail := uniformExpTailMagnitude_nonneg
      (uniformExpCellStage (precisionAtStage (n + 1)))
    have hradius : 0 <= uniformExpTailRadius
        (uniformExpCellStage (precisionAtStage (n + 1))) := by
      unfold uniformExpTailRadius
      exact Rat.mul_nonneg (by native_decide) htail
    have hmono := uniformExpCenter_mono_on_unit
      (uniformExpCellStage (precisionAtStage (n + 1)))
      hI.1 hI.2.2 hI.2.1
    have hcenter : 0 <=
        uniformExpCenter I.hi
          (uniformExpCellStage (precisionAtStage (n + 1))) -
        uniformExpCenter I.lo
          (uniformExpCellStage (precisionAtStage (n + 1))) := by
      grind [Rat.sub_eq_add_neg]
    exact ⟨by
      unfold uniformExpCellRange QInterval.width
      grind [Rat.sub_eq_add_neg], h⟩
  contains_point_values := by
    intro I hI x hx n hxlo hxhi
    change QInterval.ContainsInterval
      (uniformExpCellRange I.lo I.hi
        (uniformExpCellStage (precisionAtStage (n + 1))))
      ((uniformExpRaw x).compute
        (uniformExpCellStage (precisionAtStage (n + 1))))
    rw [uniformExpRaw_compute]
    exact uniformExpBox_contains_cellRange
      (uniformExpCellStage (precisionAtStage (n + 1)))
      hI.1 hI.2.2 hxlo hxhi

/-! The generic FTC layer consumes `RealFunRaw`, while the derivative layer
uses `FunctionOnInterval`.  This adapter exposes the same certified common
prefix evaluator at the former interface without changing its algorithm. -/

def uniformExpOnUnitRealFunRaw : RealFunRaw where
  domain := fun x => 0 <= x /\ x <= (1 : Rat)
  compute := fun x n => (uniformExpRaw x).compute n

theorem uniformExpOnUnitRealFunRaw_valid :
    uniformExpOnUnitRealFunRaw.Valid := by
  intro x hx
  exact uniformExpRaw_valid x (by
    rw [qabs_eq_self_of_nonneg hx.1]
    exact Rat.le_trans hx.2 (by native_decide))

theorem uniformExpOnUnitRealFunRaw_compute_contains_cellRange
    (n : Nat) {a b x : Rat}
    (ha : 0 <= a) (hb : b <= 1)
    (hax : a <= x) (hxb : x <= b) :
    (uniformExpCellRange a b n).ContainsInterval
      (uniformExpOnUnitRealFunRaw.compute x n) := by
  change (uniformExpCellRange a b n).ContainsInterval
    ((uniformExpRaw x).compute n)
  rw [uniformExpRaw_compute]
  exact uniformExpBox_contains_cellRange n ha hb hax hxb

def uniformExpFTCStage (eps : QPos) : Nat :=
  uniformExpSelfDerivativeEvalPrecision
    (mesh 0 1 (uniformExpFTCPieces eps))
    (uniformExpFTCIndex eps)

theorem uniformExpFTCStage_eq_quotient (eps : QPos) :
    uniformExpFTCStage eps =
      uniformExpQuotientPrecision
        (mesh 0 1 (uniformExpFTCPieces eps))
        (by
          unfold mesh
          rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
          exact Rat.ne_of_gt (by
            rw [Rat.div_def]
            exact Rat.mul_pos (by native_decide)
              ((Rat.inv_pos).2 ((Rat.natCast_pos).2
                (uniformExpFTCPieces_pos eps)))))
        (uniformExpFTCIndex eps) := by
  have hne :
      mesh 0 1 (uniformExpFTCPieces eps) ≠ 0 := by
    unfold mesh
    rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
    exact Rat.ne_of_gt (by
      rw [Rat.div_def]
      exact Rat.mul_pos (by native_decide)
        ((Rat.inv_pos).2 ((Rat.natCast_pos).2
          (uniformExpFTCPieces_pos eps))))
  simp [uniformExpFTCStage, uniformExpSelfDerivativeEvalPrecision, hne]

theorem uniformExpSymmetricCellRange_width_le_half_eps (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition eps).pieces) :
    (uniformExpSymmetricCellRange
      ((uniformExpSymmetricFTCPartition eps).cell k hk).lower
      ((uniformExpSymmetricFTCPartition eps).cell k hk).upper
      (uniformExpFTCStage eps)).width <= eps.val / 2 := by
  let C := (uniformExpSymmetricFTCPartition eps).cell k hk
  let p : Rat := mesh 0 1 (uniformExpFTCPieces eps)
  have hp : 0 < p := by
    dsimp [p]
    unfold mesh
    rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2
        (uniformExpFTCPieces_pos eps)))
  have hpone : p <= 1 := by
    have hP := uniformExpFTCPieces_pos eps
    have hanti := FTC.one_div_nat_antitone
      (n := 1) (m := uniformExpFTCPieces eps)
      (by native_decide) hP
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hP))
    dsimp [p]
    unfold mesh
    rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
    rw [show (1 : Rat) - 0 = 1 by grind]
    calc
      1 / ((uniformExpFTCPieces eps : Nat) : Rat) <= 1 / (1 : Rat) := hanti
      _ = 1 := by native_decide
  have hprec := uniformExpFTCPrecision_le_input eps
  have hmesh := uniformExpFTCPieces_mesh_le eps
  have hne : p ≠ 0 := Rat.ne_of_gt hp
  have htail := uniformExpTailMagnitude_le_quotientTolerance
    p hne (uniformExpFTCIndex eps)
  have htail' :
      uniformExpTailMagnitude (uniformExpFTCStage eps) <=
        (precisionAtStage (uniformExpFTCIndex eps)).val * p / 24 := by
    rw [uniformExpFTCStage_eq_quotient eps]
    have hpabs : qabs p = p := qabs_eq_self_of_nonneg (Rat.le_of_lt hp)
    simpa [uniformExpQuotientTailTolerance, hpabs, p] using htail
  have hcell : C.width = p := by
    dsimp [C]
    exact uniformExpSymmetricFTCPartition_cell_width eps k hk
  rw [uniformExpSymmetricCellRange_width]
  change 2 * (9 * C.width + 34 * C.width ^ 2 +
      2 * uniformExpTailMagnitude (uniformExpFTCStage eps) +
      uniformExpTailRadius (uniformExpFTCStage eps)) <= eps.val / 2
  rw [hcell]
  unfold uniformExpTailRadius
  have heps : 0 <= eps.val := Rat.le_of_lt eps.property
  calc
    2 * (9 * p + 34 * p ^ 2 +
        2 * uniformExpTailMagnitude (uniformExpFTCStage eps) +
        2 * uniformExpTailMagnitude (uniformExpFTCStage eps)) <=
        18 * p + 68 * p +
          8 * ((precisionAtStage (uniformExpFTCIndex eps)).val * p / 24) := by
      have hsq : p ^ 2 <= p := by
        have hsq' := Rat.mul_le_mul_of_nonneg_left hpone
          (Rat.le_of_lt hp)
        calc
          p ^ 2 = p * p := by
            rw [show 2 = 1 + 1 by omega, Rat.pow_succ]
            simp
          _ <= p * 1 := hsq'
          _ = p := by simp
      have htailmul := Rat.mul_le_mul_of_nonneg_left htail'
        (by native_decide : (0 : Rat) <= 8)
      grind
    _ <= eps.val / 2 := by
      have hpmesh : p <= (precisionAtStage (uniformExpFTCIndex eps)).val / 200 := by
        simpa [p] using hmesh
      have hinput : (uniformExpFTCInputPrecision eps).val = eps.val / 5 := rfl
      rw [hinput] at hprec
      let q : Rat := (precisionAtStage (uniformExpFTCIndex eps)).val
      have hqpos : 0 < q := by
        dsimp [q]
        exact (precisionAtStage (uniformExpFTCIndex eps)).property
      have h1 : 18 * p <= 18 * (q / 200) := by
        exact Rat.mul_le_mul_of_nonneg_left hpmesh (by native_decide)
      have h2 : 68 * p <= 68 * (q / 200) := by
        exact Rat.mul_le_mul_of_nonneg_left hpmesh (by native_decide)
      have hqp : q * p <= q := by
        dsimp [q]
        have hqnonneg := Rat.le_of_lt
          (precisionAtStage (uniformExpFTCIndex eps)).property
        simpa using Rat.mul_le_mul_of_nonneg_left hpone hqnonneg
      have h3 : 8 * (q * p / 24) <= q / 3 := by
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
      have hsum := rat_add_le_add (rat_add_le_add h1 h2) h3
      have hqeps : q <= eps.val / 5 := by
        dsimp [q]
        exact hprec
      change 18 * p + 68 * p + 8 * (q * p / 24) <= eps.val / 2
      have hsum' : 18 * p + 68 * p + 8 * (q * p / 24) <=
          18 * (q / 200) + 68 * (q / 200) + q / 3 := by
        exact hsum
      have hqeps' := Rat.mul_le_mul_of_nonneg_left hqeps
        (by native_decide : (0 : Rat) <= (18 / 200 : Rat) + 68 / 200 + 1 / 3)
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

theorem uniformExpSymmetricCellRange_width_le_eps (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition eps).pieces) :
    (uniformExpSymmetricCellRange
      ((uniformExpSymmetricFTCPartition eps).cell k hk).lower
      ((uniformExpSymmetricFTCPartition eps).cell k hk).upper
      (uniformExpFTCStage eps)).width <= eps.val := by
  exact Rat.le_trans (uniformExpSymmetricCellRange_width_le_half_eps eps k hk)
    (by
      have heps : 0 <= eps.val := Rat.le_of_lt eps.property
      grind [Rat.div_def])

theorem uniformExpSymmetricCellRange_width_le_eps_leftPoint
    (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition eps).pieces) :
    (uniformExpSymmetricCellRange
      (leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) k)
      (leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) (k + 1))
      (uniformExpFTCStage eps)).width <= eps.val := by
  have h := uniformExpSymmetricCellRange_width_le_eps eps k hk
  rw [show ((uniformExpSymmetricFTCPartition eps).cell k hk).lower =
      leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) k by rfl,
    show ((uniformExpSymmetricFTCPartition eps).cell k hk).upper =
      leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) (k + 1) by rfl] at h
  exact h

theorem uniformExpSymmetricCellRange_width_le_half_eps_leftPoint
    (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition eps).pieces) :
    (uniformExpSymmetricCellRange
      (leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) k)
      (leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) (k + 1))
      (uniformExpFTCStage eps)).width <= eps.val / 2 := by
  have h := uniformExpSymmetricCellRange_width_le_half_eps eps k hk
  rw [show ((uniformExpSymmetricFTCPartition eps).cell k hk).lower =
      leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) k by rfl,
    show ((uniformExpSymmetricFTCPartition eps).cell k hk).upper =
      leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) (k + 1) by rfl] at h
  exact h

def uniformExpSymmetricFTCIndexedBound (eps : QPos) (k : Nat) : QInterval :=
  uniformExpSymmetricCellRange
    (leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) k)
    (leftPoint (-1) 1 (uniformExpSymmetricFTCPieces eps) (k + 1))
    (uniformExpFTCStage eps)

theorem uniformExpSymmetricFTCIndexedBound_width_le (eps : QPos) (k : Nat)
    (hk : k < uniformExpSymmetricFTCPieces eps) :
    (uniformExpSymmetricFTCIndexedBound eps k).width <= eps.val / 2 := by
  unfold uniformExpSymmetricFTCIndexedBound
  have h := uniformExpSymmetricCellRange_width_le_half_eps_leftPoint eps k hk
  exact h

theorem uniformExpSymmetricFTCIndexedBound_contains_raw
    (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition eps).pieces)
    (x : Rat) (hx : ((uniformExpSymmetricFTCPartition eps).cell k hk).contains x) :
    QInterval.ContainsInterval (uniformExpSymmetricFTCIndexedBound eps k)
      ((uniformExpRaw x).compute (uniformExpFTCStage eps)) := by
  let C := (uniformExpSymmetricFTCPartition eps).cell k hk
  have hpos : 0 < C.width := by
    rw [show C.width = mesh 0 1 (uniformExpFTCPieces eps) by
      dsimp [C]
      exact uniformExpSymmetricFTCPartition_cell_width eps k hk]
    unfold mesh
    rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
    rw [show (1 : Rat) - 0 = 1 by grind, Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2
        (uniformExpFTCPieces_pos eps)))
  have hab : C.lower < C.upper := by
    apply (Rat.lt_iff_sub_pos _ _).mpr
    simpa [RationalSubinterval.width] using hpos
  have hrange := uniformExpSymmetricCellRange_contains
    (n := uniformExpFTCStage eps) (a := C.lower) (b := C.upper) (x := x)
    C.lower_mem C.upper_mem hab hx.1 hx.2
  have hend := uniformExpSymmetricFTCPartition_cell_endpoints eps k hk
  unfold uniformExpSymmetricFTCIndexedBound
  rw [← hend.1, ← hend.2]
  exact hrange

theorem uniformExpFTC_endpoint_width_le (eps : QPos) :
    (endpointDifferenceInterval uniformExpOnUnitRealFunRaw 0 1
      (uniformExpFTCStage eps)).width <= eps.val := by
  let h : Rat := mesh 0 1 (uniformExpFTCPieces eps)
  have hpos : 0 < h := by
    dsimp [h]
    unfold mesh
    rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
    rw [show (1 : Rat) - 0 = 1 by grind, Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2
        (uniformExpFTCPieces_pos eps)))
  have hh : h ≠ 0 := Rat.ne_of_gt hpos
  have hqabs : qabs h = h := qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)
  have htail := uniformExpTailMagnitude_le_quotientTolerance
    h hh (uniformExpFTCIndex eps)
  have htail' :
      uniformExpTailMagnitude (uniformExpFTCStage eps) <=
        (precisionAtStage (uniformExpFTCIndex eps)).val * h / 24 := by
    rw [uniformExpFTCStage_eq_quotient eps]
    simpa [uniformExpQuotientTailTolerance, hqabs] using htail
  have hleone : h <= 1 := by
    have hp : 0 < uniformExpFTCPieces eps := uniformExpFTCPieces_pos eps
    have hanti := FTC.one_div_nat_antitone
      (n := 1) (m := uniformExpFTCPieces eps)
      (by native_decide) hp
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp))
    dsimp [h]
    unfold mesh
    rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
    rw [show (1 : Rat) - 0 = 1 by grind]
    calc
      1 / ((uniformExpFTCPieces eps : Nat) : Rat) <= 1 / (1 : Rat) := hanti
      _ = 1 := by native_decide
  have hp : 0 <= (precisionAtStage (uniformExpFTCIndex eps)).val :=
    Rat.le_of_lt (precisionAtStage (uniformExpFTCIndex eps)).property
  have hbox :
      2 * uniformExpTailRadius (uniformExpFTCStage eps) <=
        (precisionAtStage (uniformExpFTCIndex eps)).val / 6 := by
    unfold uniformExpTailRadius
    have hmul := Rat.mul_le_mul_of_nonneg_left htail'
      (by native_decide : (0 : Rat) <= 4)
    calc
      2 * (2 * uniformExpTailMagnitude (uniformExpFTCStage eps)) <=
          4 * ((precisionAtStage (uniformExpFTCIndex eps)).val * h / 24) := by
            exact Rat.le_trans (by grind) hmul
      _ = (precisionAtStage (uniformExpFTCIndex eps)).val * h / 6 := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= (precisionAtStage (uniformExpFTCIndex eps)).val / 6 := by
        have := Rat.mul_le_mul_of_nonneg_left hleone hp
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hboxsum :
      (uniformExpBox 0 (uniformExpFTCStage eps)).width +
          (uniformExpBox 1 (uniformExpFTCStage eps)).width <=
        (precisionAtStage (uniformExpFTCIndex eps)).val / 3 := by
    rw [uniformExpBox_width, uniformExpBox_width]
    calc
      2 * uniformExpTailRadius (uniformExpFTCStage eps) +
          2 * uniformExpTailRadius (uniformExpFTCStage eps) <=
          (precisionAtStage (uniformExpFTCIndex eps)).val / 6 +
            (precisionAtStage (uniformExpFTCIndex eps)).val / 6 :=
        rat_add_le_add hbox hbox
      _ <= (precisionAtStage (uniformExpFTCIndex eps)).val / 3 := by grind
  rw [endpointDifferenceInterval_width]
  have hactual :
      (uniformExpOnUnitRealFunRaw.compute 0 (uniformExpFTCStage eps)).width +
          (uniformExpOnUnitRealFunRaw.compute 1 (uniformExpFTCStage eps)).width <=
        (precisionAtStage (uniformExpFTCIndex eps)).val / 3 := by
    simpa [uniformExpOnUnitRealFunRaw, uniformExpRaw_compute] using hboxsum
  exact Rat.le_trans hactual (by
    have hp' := uniformExpFTCPrecision_le_input eps
    have heps : 0 <= eps.val := Rat.le_of_lt eps.property
    have hinput : (uniformExpFTCInputPrecision eps).val = eps.val / 5 := rfl
    rw [hinput] at hp'
    grind)

def uniformExpFTCPartition (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (uniformExpFTCPieces eps)
    (uniformExpFTCPieces_pos eps) (by native_decide)

theorem uniformExpFTCPartition_cell_mesh_pos (eps : QPos) (k : Nat)
    (hk : k < (uniformExpFTCPartition eps).pieces) :
    0 < ((uniformExpFTCPartition eps).cell k hk).width := by
  rw [show ((uniformExpFTCPartition eps).cell k hk).width =
      mesh 0 1 (uniformExpFTCPieces eps) by
    exact RationalPartition.uniform_cell_width 0 1
      (uniformExpFTCPieces eps) (uniformExpFTCPieces_pos eps)
      (by native_decide) k hk]
  unfold mesh
  rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
  rw [Rat.div_def]
  exact Rat.mul_pos (by native_decide)
    ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (uniformExpFTCPieces_pos eps)))

theorem uniformExpFTCPartition_cell_width (eps : QPos) (k : Nat)
    (hk : k < (uniformExpFTCPartition eps).pieces) :
    ((uniformExpFTCPartition eps).cell k hk).width =
      mesh 0 1 (uniformExpFTCPieces eps) := by
  unfold uniformExpFTCPartition
  exact RationalPartition.uniform_cell_width 0 1
    (uniformExpFTCPieces eps) (uniformExpFTCPieces_pos eps)
    (by native_decide) k hk

theorem uniformExpFTCPartition_cell_strict (eps : QPos) (k : Nat)
    (hk : k < (uniformExpFTCPartition eps).pieces) :
    ((uniformExpFTCPartition eps).cell k hk).lower <
      ((uniformExpFTCPartition eps).cell k hk).upper := by
  apply (Rat.lt_iff_sub_pos _ _).mpr
  simpa [RationalSubinterval.width] using
    uniformExpFTCPartition_cell_mesh_pos eps k hk

def uniformExpFTCIndexedStep (eps : QPos) (k : Nat) : Rat :=
  leftPoint 0 1 (uniformExpFTCPieces eps) (k + 1) -
    leftPoint 0 1 (uniformExpFTCPieces eps) k

theorem uniformExpFTCIndexedStep_pos (eps : QPos) (k : Nat) :
    0 < uniformExpFTCIndexedStep eps k := by
  unfold uniformExpFTCIndexedStep
  rw [leftPoint_step]
  unfold mesh
  rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps)), Rat.div_def]
  exact Rat.mul_pos (by native_decide)
    ((Rat.inv_pos).2 ((Rat.natCast_pos).2
      (uniformExpFTCPieces_pos eps)))

theorem uniformExpFTCIndexedStep_ne (eps : QPos) (k : Nat) :
    uniformExpFTCIndexedStep eps k ≠ 0 :=
  Rat.ne_of_gt (uniformExpFTCIndexedStep_pos eps k)

theorem uniformExpFTCIndexedStep_eq_mesh (eps : QPos) (k : Nat) :
    uniformExpFTCIndexedStep eps k =
      mesh 0 1 (uniformExpFTCPieces eps) := by
  unfold uniformExpFTCIndexedStep
  exact leftPoint_step 0 1 (uniformExpFTCPieces eps) k

def uniformExpFTCIndexedBound (eps : QPos) (k : Nat) : QInterval :=
  QInterval.expand
    (uniformExpCellRange
      (leftPoint 0 1 (uniformExpFTCPieces eps) k)
      (leftPoint 0 1 (uniformExpFTCPieces eps) (k + 1))
      (uniformExpFTCStage eps))
    (2 * (precisionAtStage (uniformExpFTCIndex eps)).val)

attribute [irreducible] uniformExpFTCIndexedBound

theorem uniformExpFTCIndexedBound_eq (eps : QPos) (k : Nat) :
    uniformExpFTCIndexedBound eps k =
      QInterval.expand
        (uniformExpCellRange
          (leftPoint 0 1 (uniformExpFTCPieces eps) k)
          (leftPoint 0 1 (uniformExpFTCPieces eps) (k + 1))
          (uniformExpFTCStage eps))
        (2 * (precisionAtStage (uniformExpFTCIndex eps)).val) := by
  unfold uniformExpFTCIndexedBound
  rfl

def uniformExpFTCQuotientBound (eps : QPos) (k : Nat)
    (hh : uniformExpFTCIndexedStep eps k ≠ 0) : QInterval :=
  QInterval.expand
    (uniformExpCellRange
      (leftPoint 0 1 (uniformExpFTCPieces eps) k)
      (leftPoint 0 1 (uniformExpFTCPieces eps) (k + 1))
      (uniformExpQuotientPrecision
        (uniformExpFTCIndexedStep eps k) hh (uniformExpFTCIndex eps)))
    (2 * (precisionAtStage (uniformExpFTCIndex eps)).val)

theorem uniformExpQuotientBound_eq_indexedBound (eps : QPos) (k : Nat)
    (hh : uniformExpFTCIndexedStep eps k ≠ 0) :
    uniformExpFTCQuotientBound eps k hh =
      uniformExpFTCIndexedBound eps k := by
  unfold uniformExpFTCQuotientBound uniformExpFTCIndexedBound
  have hq := uniformExpQuotientPrecision_congr
    (uniformExpFTCIndexedStep_eq_mesh eps k) hh
    (by exact uniformExpFTCMesh_ne eps) (uniformExpFTCIndex eps)
  rw [hq]
  rw [uniformExpFTCStage_eq_quotient eps]

theorem uniformExpFTCQuotientBound_width_le (eps : QPos) (k : Nat)
    (hk : k < uniformExpFTCPieces eps) :
    (uniformExpFTCQuotientBound eps k
      (uniformExpFTCIndexedStep_ne eps k)).width <= eps.val := by
  unfold uniformExpFTCQuotientBound
  exact uniformExpExpandedCellRange_width_le_eps eps
    (uniformExpFTCIndex eps)
    (uniformExpFTCLeftPoint_bounds eps k hk).1
    (uniformExpFTCLeftPoint_bounds eps k hk).2
    (uniformExpFTCLeftPoint_strict eps k hk)
    (uniformExpFTCLeftPoint_step_le eps k hk)
    (uniformExpFTCPrecision_le_input eps)

theorem uniformExpFTCIndexedBound_width_le (eps : QPos) (k : Nat)
    (hk : k < uniformExpFTCPieces eps) :
    (uniformExpFTCIndexedBound eps k).width <= eps.val := by
  rw [← uniformExpQuotientBound_eq_indexedBound]
  exact uniformExpFTCQuotientBound_width_le eps k hk

theorem uniformExpFTCIndexedBound_contains
    (eps : QPos) (k : Nat) (hk : k < (uniformExpFTCPartition eps).pieces)
    (x : Rat) (hx : ((uniformExpFTCPartition eps).cell k hk).contains x) :
    QInterval.ContainsInterval (uniformExpFTCIndexedBound eps k)
      (uniformExpOnUnitRealFunRaw.compute x (uniformExpFTCStage eps)) := by
  let C := (uniformExpFTCPartition eps).cell k hk
  change C.contains x at hx
  have hrange := uniformExpOnUnitRealFunRaw_compute_contains_cellRange
    (n := uniformExpFTCStage eps) (a := C.lower) (b := C.upper) (x := x)
    C.lower_mem C.upper_mem hx.1 hx.2
  unfold uniformExpFTCIndexedBound
  change QInterval.ContainsInterval
    (QInterval.expand (uniformExpCellRange C.lower C.upper
      (uniformExpFTCStage eps))
      (2 * (precisionAtStage (uniformExpFTCIndex eps)).val))
    (uniformExpOnUnitRealFunRaw.compute x (uniformExpFTCStage eps))
  unfold QInterval.ContainsInterval QInterval.expand
  rcases hrange with ⟨hlo, hhi⟩
  have hp := (precisionAtStage (uniformExpFTCIndex eps)).property
  have hr : 0 <= 2 * (precisionAtStage (uniformExpFTCIndex eps)).val :=
    Rat.mul_nonneg (by native_decide) (Rat.le_of_lt hp)
  exact ⟨by grind, by grind⟩

/-- On the unit interval the common-prefix representation and the selected
adaptive representation are pointwise equivalent. -/
theorem uniformExpOnUnit_equivalent_expPowerSeriesOnUnit :
    FunctionOnInterval.Equivalent uniformExpOnUnit
      (expPowerSeriesOnInterval 0 1) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x hxuniform hxadaptive
  change (uniformExpRaw x).Equiv (expPowerSeries x)
  change (0 : Rat) <= x /\ x <= 1 at hxuniform
  have hx : (0 : Rat) <= x /\ x <= 1 := hxuniform
  apply uniformExpRaw_equiv_expPowerSeries x
  rw [qabs_eq_self_of_nonneg hx.1]
  exact Rat.le_trans hx.2 (by native_decide)

/-- The common-prefix exponential on the unit interval satisfies its own
two-sided interval derivative certificate.  At every nonzero rational step,
both endpoints use one factorial prefix selected from `ε |h| / 24`; the
uniform finite secant budget and the quotient-tail boxes then fit inside the
requested output interval. -/
def uniformExpOnUnit_hasDerivativeOnInterval :
    HasDerivativeOnInterval uniformExpOnUnit uniformExpOnUnit where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := uniformExpSelfDerivativeStepPrecision
  evalPrecision := fun _x h n => uniformExpSelfDerivativeEvalPrecision h n
  close := by
    intro x h n hx hxh _hdx hh hsmall
    change (0 : Rat) <= x /\ x <= 1 at hx
    change (0 : Rat) <= x + h /\ x + h <= 1 at hxh
    have hx' : (0 : Rat) <= x /\ x <= 1 := hx
    have hxh' : (0 : Rat) <= x + h /\ x + h <= 1 := hxh
    have hqx : qabs x <= 2 := by
      rw [qabs_eq_self_of_nonneg hx'.1]
      exact Rat.le_trans hx'.2 (by native_decide)
    have hqxh : qabs (x + h) <= 2 := by
      rw [qabs_eq_self_of_nonneg hxh'.1]
      exact Rat.le_trans hxh'.2 (by native_decide)
    have habs : qabs h <= 1 := by
      by_cases hnonneg : 0 <= h
      · rw [qabs_eq_self_of_nonneg hnonneg]
        grind [Rat.sub_eq_add_neg]
      · have hnonpos : h <= 0 := by grind
        rw [qabs_eq_neg_of_nonpos hnonpos]
        grind [Rat.sub_eq_add_neg]
    let eps : QPos := precisionAtStage n
    let stage : Nat := uniformExpQuotientPrecision h hh n
    have hstage : uniformExpSelfDerivativeEvalPrecision h n = stage := by
      dsimp [stage]
      exact uniformExpSelfDerivativeEvalPrecision_of_ne h hh n
    have htail : uniformExpTailMagnitude stage <=
        eps.val * qabs h / 24 := by
      dsimp [stage, eps]
      simpa [uniformExpQuotientTailTolerance] using
        uniformExpTailMagnitude_le_quotientTolerance h hh n
    have hfinite : qabs h * 34 <= eps.val / 2 := by
      dsimp [eps]
      exact uniformExpSelfDerivative_finite_error_le_half_precision n hsmall
    have htransport := uniformExp_tail_transport_budgets hh habs eps htail
    have hbudget :
        (qabs h * 34 + 2 * uniformExpTailMagnitude stage / qabs h) +
            2 * uniformExpTailRadius stage / qabs h +
              uniformExpTailRadius stage <= eps.val := by
      have htailBudget : 6 * uniformExpTailMagnitude stage / qabs h +
          2 * uniformExpTailMagnitude stage <= eps.val / 3 := htransport.1
      calc
        (qabs h * 34 + 2 * uniformExpTailMagnitude stage / qabs h) +
            2 * uniformExpTailRadius stage / qabs h +
              uniformExpTailRadius stage =
            qabs h * 34 +
              (6 * uniformExpTailMagnitude stage / qabs h +
                2 * uniformExpTailMagnitude stage) := by
                unfold uniformExpTailRadius
                grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
        _ <= eps.val / 2 + eps.val / 3 := rat_add_le_add hfinite htailBudget
        _ <= eps.val := by
          have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hquotientWidth :
        4 * uniformExpTailRadius stage / qabs h <= eps.val := by
      have htailWidth : 8 * uniformExpTailMagnitude stage / qabs h <=
          eps.val / 3 := htransport.2.1
      calc
        4 * uniformExpTailRadius stage / qabs h =
            8 * uniformExpTailMagnitude stage / qabs h := by
              unfold uniformExpTailRadius
              grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
        _ <= eps.val / 3 := htailWidth
        _ <= eps.val := by
          have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hderivativeWidth : 2 * uniformExpTailRadius stage <= eps.val := by
      have htailWidth : 4 * uniformExpTailMagnitude stage <= eps.val / 6 :=
        htransport.2.2
      calc
        2 * uniformExpTailRadius stage =
            4 * uniformExpTailMagnitude stage := by
              unfold uniformExpTailRadius
              grind [Rat.mul_assoc]
        _ <= eps.val / 6 := htailWidth
        _ <= eps.val := by
          have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcenter := uniformExpCenter_secant_error_le hh hqx hqxh stage
    rw [hstage]
    change QInterval.NearAt
      (QInterval.differenceQuotient
        (uniformExpBox (x + h) stage) (uniformExpBox x stage) h)
      (uniformExpBox x stage) eps
    unfold uniformExpBox
    exact intervalAround_differenceQuotient_near_intervalAround
      (uniformExpCenter x stage) (uniformExpCenter (x + h) stage)
      (uniformExpCenter x stage) (uniformExpTailRadius stage) h
      (qabs h * 34 + 2 * uniformExpTailMagnitude stage / qabs h) eps
      hh (by
        unfold uniformExpTailRadius
        exact Rat.mul_nonneg (by native_decide)
          (uniformExpTailMagnitude_nonneg stage)) hcenter hbudget
      hquotientWidth hderivativeWidth

theorem uniformExpCell_endpoint_contained_of_step
    {a b : Rat} (n : Nat)
    (ha : 0 <= a) (hb : b <= 1) (hab : a < b)
    (hsmall : qabs (b - a) <=
      1 / ((uniformExpOnUnit_hasDerivativeOnInterval.stepPrecision n : Nat) : Rat)) :
    let h := b - a
    let stage := uniformExpSelfDerivativeEvalPrecision h n
    QInterval.ContainsInterval
      (QInterval.scaleByRat h
        (QInterval.expand (uniformExpCellRange a b stage)
          (2 * (precisionAtStage n).val)))
      (endpointDifferenceInterval uniformExpOnUnitRealFunRaw a b stage) := by
  let h : Rat := b - a
  let stage : Nat := uniformExpSelfDerivativeEvalPrecision h n
  have hpos : 0 < h := by
    dsimp [h]
    exact (Rat.lt_iff_sub_pos a b).mp hab
  have hh : h ≠ 0 := Rat.ne_of_gt hpos
  have ha1 : a <= 1 := Rat.le_trans (Rat.le_of_lt hab) hb
  have hclose := uniformExpOnUnit_hasDerivativeOnInterval.close
    a h n ⟨ha, ha1⟩
    (by
      have : a + h = b := by dsimp [h]; grind
      rw [this]
      exact ⟨Rat.le_trans ha (Rat.le_of_lt hab), hb⟩)
    (by exact ⟨ha, ha1⟩) hh hsmall
  change QInterval.NearAt
    (QInterval.differenceQuotient
      (uniformExpBox (a + h) stage) (uniformExpBox a stage) h)
    (uniformExpBox a stage) (precisionAtStage n) at hclose
  have hscaledBox :=
    QInterval.scaleByRat_expand_contains_subInterval_of_differenceQuotient_near
      (A := uniformExpBox a stage) (B := uniformExpBox (a + h) stage)
      (D := uniformExpBox a stage) (h := h) (eps := precisionAtStage n)
      hpos hclose
  have hrangeBox := uniformExpBox_contains_cellRange stage ha hb
    Rat.le_refl (Rat.le_of_lt hab)
  have hexpand :
      (QInterval.expand (uniformExpCellRange a b stage)
        (2 * (precisionAtStage n).val)).ContainsInterval
        (QInterval.expand (uniformExpBox a stage)
          (2 * (precisionAtStage n).val)) := by
    unfold QInterval.ContainsInterval QInterval.expand at *
    grind
  have hscaledRange := QInterval.scaleByRat_contains_of_nonneg
    (Rat.le_of_lt hpos) hexpand
  have hcombined := hscaledRange.trans hscaledBox
  have hab_eq : a + h = b := by
    dsimp [h]
    grind
  rw [hab_eq] at hcombined
  change QInterval.ContainsInterval
    (QInterval.scaleByRat h
      (QInterval.expand (uniformExpCellRange a b stage)
        (2 * (precisionAtStage n).val)))
    (endpointDifferenceInterval uniformExpOnUnitRealFunRaw a b stage)
  simpa [h, endpointDifferenceInterval, uniformExpOnUnitRealFunRaw,
    uniformExpRaw_compute, QInterval.subInterval] using hcombined

theorem uniformExpFTCIndexedBound_local_endpoint_contained
    (eps : QPos) (k : Nat)
    (hk : k < (uniformExpFTCPartition eps).pieces) :
    QInterval.ContainsInterval
      (((uniformExpFTCPartition eps).cell k hk).scaleBound
        (uniformExpFTCIndexedBound eps k))
      (endpointDifferenceInterval uniformExpOnUnitRealFunRaw
        ((uniformExpFTCPartition eps).cell k hk).lower
        ((uniformExpFTCPartition eps).cell k hk).upper
        (uniformExpFTCStage eps)) := by
  let C := (uniformExpFTCPartition eps).cell k hk
  have hpos : 0 < C.width := by
    dsimp [C]
    exact uniformExpFTCPartition_cell_mesh_pos eps k hk
  have hab : C.lower < C.upper := by
    apply (Rat.lt_iff_sub_pos _ _).mpr
    simpa [RationalSubinterval.width] using hpos
  have htransport := uniformExpCell_endpoint_contained_of_step
    (n := uniformExpFTCIndex eps) C.lower_mem C.upper_mem hab
    (by
      rw [qabs_eq_self_of_nonneg
        (Rat.le_of_lt ((Rat.lt_iff_sub_pos _ _).mp hab))]
      change C.width <= 1 /
        ((uniformExpOnUnit_hasDerivativeOnInterval.stepPrecision
          (uniformExpFTCIndex eps) : Nat) : Rat)
      rw [show C.width = mesh 0 1 (uniformExpFTCPieces eps) by
        dsimp [C]
        exact uniformExpFTCPartition_cell_width eps k hk]
      exact uniformExpFTCPieces_step_le eps)
  have hstage :
      uniformExpSelfDerivativeEvalPrecision (C.upper - C.lower)
          (uniformExpFTCIndex eps) = uniformExpFTCStage eps := by
    have heq : C.upper - C.lower =
        mesh 0 1 (uniformExpFTCPieces eps) := by
      dsimp [C, RationalSubinterval.width]
      exact uniformExpFTCPartition_cell_width eps k hk
    rw [heq]
    rw [uniformExpSelfDerivativeEvalPrecision_eq_quotient]
    rw [uniformExpFTCStage_eq_quotient eps]
  unfold uniformExpFTCIndexedBound
  change QInterval.ContainsInterval
    (C.scaleBound
      (QInterval.expand (uniformExpCellRange C.lower C.upper
        (uniformExpFTCStage eps))
        (2 * (precisionAtStage (uniformExpFTCIndex eps)).val)))
    (endpointDifferenceInterval uniformExpOnUnitRealFunRaw
      C.lower C.upper (uniformExpFTCStage eps))
  unfold RationalSubinterval.scaleBound RationalSubinterval.width
  rw [← hstage]
  exact htransport

theorem uniformExpFTCIndexedSum_width_le_of_cell_bounds (eps : QPos)
    (hbound : forall k, k < uniformExpFTCPieces eps ->
      (uniformExpFTCIndexedBound eps k).width <= eps.val) :
    ((uniformExpFTCPartition eps).boundIntegralSum
      (fun k _ => uniformExpFTCIndexedBound eps k)).width <= eps.val := by
  have hsum := RationalPartition.uniform_boundIntegralSum_width_le_indexed
    (a := (0 : Rat)) (b := 1) (uniformExpFTCPieces eps)
    (uniformExpFTCPieces_pos eps) (by native_decide)
    (fun k => uniformExpFTCIndexedBound eps k) eps.val hbound
  change ((RationalPartition.uniform 0 1 (uniformExpFTCPieces eps)
    (uniformExpFTCPieces_pos eps) (by native_decide)).boundIntegralSum
    (fun k _ => uniformExpFTCIndexedBound eps k)).width <= eps.val
  exact Rat.le_trans hsum (by grind)

theorem uniformExpFTCIndexedSum_width_le (eps : QPos) :
    ((uniformExpFTCPartition eps).boundIntegralSum
      (fun k _ => uniformExpFTCIndexedBound eps k)).width <= eps.val := by
  exact uniformExpFTCIndexedSum_width_le_of_cell_bounds eps
    (fun k hk => uniformExpFTCIndexedBound_width_le eps k
      (by exact hk))

def uniformExpOnUnit_selectedStageFTCIndexed :
    SelectedStageCandidateDerivativeFTCIndexed
      uniformExpOnUnitRealFunRaw uniformExpOnUnitRealFunRaw 0 1 where
  primitive_valid := uniformExpOnUnitRealFunRaw_valid
  choosePartition := uniformExpFTCPartition
  chooseStage := uniformExpFTCStage
  derivativeBound := uniformExpFTCIndexedBound
  primitive_domain_on := by
    intro eps i hi
    exact (uniformExpFTCPartition eps).point_in_bounds hi
  candidate_domain_on := by
    intro eps k hk x hx
    exact RationalSubinterval.contains_inDomain
      ((uniformExpFTCPartition eps).cell k hk) hx
  candidate_contained := by
    intro eps k hk x hx
    exact uniformExpFTCIndexedBound_contains eps k hk x hx
  local_endpoint_contained := by
    intro eps k hk
    exact uniformExpFTCIndexedBound_local_endpoint_contained eps k hk
  riemann_width := uniformExpFTCIndexedSum_width_le
  endpoint_width := uniformExpFTC_endpoint_width_le

theorem uniformExpOnUnit_selectedStageFTCIndexed_equiv_endpoint :
    (uniformExpOnUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw).Equiv
      uniformExpOnUnit_selectedStageFTCIndexed.toSelected.endpointRaw := by
  exact selectedStageCandidateDerivativeFTCIndexed
    uniformExpOnUnit_selectedStageFTCIndexed

/-! Public spelling of the first completed effective FTC instance.  Its
endpoint raw is the certified stage-indexed evaluator for
`uniformExpOnUnitRealFunRaw 1 - uniformExpOnUnitRealFunRaw 0`; the generic
`endpointDifferenceRaw_equiv_sub_apply` bridge in `Calculus` identifies that
interval construction with ordinary raw subtraction whenever a direct
endpoint-difference schedule is desired. -/

theorem uniformExpOnUnit_effectiveFTC :
    (uniformExpOnUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw).Equiv
      uniformExpOnUnit_selectedStageFTCIndexed.toSelected.endpointRaw :=
  uniformExpOnUnit_selectedStageFTCIndexed_equiv_endpoint

/-- The common-prefix unit-interval evaluator has the exact exponential
initial value at zero.  This makes its analytic derivative certificate a
constructive initial-value solution, ready for the separate uniqueness
bridge. -/
theorem uniformExpOnUnit_zero_equiv_one :
    (PartialRealFunRaw.apply uniformExpOnUnit.raw uniformExpOnUnit.valid_on
      (0 : Rat)
      (uniformExpOnUnit.defined_on 0 (by
        constructor <;> native_decide))).Equiv (RealRaw.ofRat 1) := by
  change (uniformExpRaw (0 : Rat)).Equiv (RealRaw.ofRat 1)
  have hone : (RealRaw.ofRat (1 : Rat)).Valid := by
    change RealRaw.ValidCompute (fun _ => { lo := 1, hi := 1 })
    exact RealRaw.ofRat_valid (1 : Rat)
  apply RealRaw.equiv_trans
    (uniformExpRaw_valid 0 (by native_decide))
    (expPowerSeries_valid 0)
    hone
  · exact uniformExpRaw_equiv_expPowerSeries 0 (by native_decide)
  · exact expPowerSeries_zero_equiv_one

/-- The common-prefix exponential is a certified solution of `f' = f` on the
unit interval.  Constructive uniqueness is deliberately a separate theorem:
this record supplies exactly its derivative and initial-value hypotheses. -/
def uniformExpOnUnit_solvesSelfDerivative :
    SolvesSelfDerivativeOnInterval uniformExpOnUnit where
  derivative_self := uniformExpOnUnit_hasDerivativeOnInterval
  initial := 0
  initial_mem := by
    constructor <;> native_decide
  initial_value := RealRaw.ofRat 1
  initial_value_valid := by
    change RealRaw.ValidCompute (fun _ => { lo := 1, hi := 1 })
    exact RealRaw.ofRat_valid (1 : Rat)
  initial_value_equiv := by
    exact uniformExpOnUnit_zero_equiv_one

/-! Once a finite uniqueness provider is supplied, the exponential certificate
immediately identifies the common-prefix evaluator with every other certified
solution having the same rational initial point and raw initial value.  The
provider is intentionally an argument: no classical ODE existence or
completeness principle is smuggled into this assembly theorem. -/

theorem uniformExpOnUnit_equivalent_of_selfDerivative_unique
    (hunique : SelfDerivativeInitialValueUnique)
    (f : FunctionOnInterval)
    (hf : SolvesSelfDerivativeOnInterval f)
    (hinitial : hf.initial = 0)
    (hvalue : hf.initial_value.Equiv (RealRaw.ofRat 1)) :
    FunctionOnInterval.Equivalent uniformExpOnUnit f := by
  let he := uniformExpOnUnit_solvesSelfDerivative
  apply hunique uniformExpOnUnit f he hf
  · change (0 : Rat) = hf.initial
    exact hinitial.symm
  · change (RealRaw.ofRat 1).Equiv hf.initial_value
    exact RealRaw.equiv_symm hvalue

/-- The same common-prefix evaluator, now exposed on the centered interval
`[-1, 1]`.  This is the natural local chart for analytic identities that need
both positive and negative rational inputs. -/
def uniformExpOnSymmetricUnit : FunctionOnInterval where
  raw :=
    { definedAt := fun x => (-1 : Rat) <= x /\ x <= 1
      compute := fun x _ => (uniformExpRaw x).compute }
  lower := -1
  upper := 1
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    have hx' : (-1 : Rat) <= x /\ x <= 1 := by
      simpa [inDomainInterval] using hx
    have hqabsOne : qabs x <= 1 :=
      qabs_le_of_neg_le_le hx'.1 hx'.2
    exact uniformExpRaw_valid x (Rat.le_trans hqabsOne (by native_decide))

theorem uniformExpOnSymmetricUnit_compute (x : Rat)
    (hx : inDomainInterval (-1 : Rat) 1 x) (n : Nat) :
    uniformExpOnSymmetricUnit.compute x hx n = (uniformExpRaw x).compute n := rfl

/-! The symmetric chart is also exposed at the `RealFunRaw` layer consumed by
the effective FTC.  Keeping this wrapper separate from `FunctionOnInterval`
does not add a second exponential: it only records the same evaluator with
the explicit rational domain needed by endpoint and derivative certificates. -/

def uniformExpOnSymmetricUnitRealFunRaw : RealFunRaw where
  domain := fun x => (-1 : Rat) <= x /\ x <= 1
  compute := fun x n => (uniformExpRaw x).compute n
  rate := fun _ _ => .unknown

theorem uniformExpOnSymmetricUnitRealFunRaw_valid :
    uniformExpOnSymmetricUnitRealFunRaw.Valid := by
  intro x hx
  have hqabs : qabs x <= 1 := qabs_le_of_neg_le_le hx.1 hx.2
  change (uniformExpRaw x).Valid
  exact uniformExpRaw_valid x (Rat.le_trans hqabs (by native_decide))

theorem uniformExpSymmetricFTCIndexedBound_contains
    (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition eps).pieces)
    (x : Rat) (hx : ((uniformExpSymmetricFTCPartition eps).cell k hk).contains x) :
    QInterval.ContainsInterval (uniformExpSymmetricFTCIndexedBound eps k)
      (uniformExpOnSymmetricUnitRealFunRaw.compute x (uniformExpFTCStage eps)) := by
  change QInterval.ContainsInterval (uniformExpSymmetricFTCIndexedBound eps k)
    ((uniformExpRaw x).compute (uniformExpFTCStage eps))
  exact uniformExpSymmetricFTCIndexedBound_contains_raw eps k hk x hx

theorem uniformExpSymmetricFTCIndexedSum_width_le (eps : QPos) :
    ((uniformExpSymmetricFTCPartition eps).boundIntegralSum
      (fun k _ => uniformExpSymmetricFTCIndexedBound eps k)).width <= eps.val := by
  have hsum := RationalPartition.uniform_boundIntegralSum_width_le_indexed
    (a := (-1 : Rat)) (b := 1) (uniformExpSymmetricFTCPieces eps)
    (uniformExpSymmetricFTCPieces_pos eps) (by native_decide)
    (fun k => uniformExpSymmetricFTCIndexedBound eps k) (eps.val / 2) (by
      intro k hk
      exact uniformExpSymmetricFTCIndexedBound_width_le eps k hk)
  change ((RationalPartition.uniform (-1) 1
    (uniformExpSymmetricFTCPieces eps)
    (uniformExpSymmetricFTCPieces_pos eps) (by native_decide)).boundIntegralSum
    (fun k _ => uniformExpSymmetricFTCIndexedBound eps k)).width <= eps.val
  exact Rat.le_trans hsum (by grind)

theorem uniformExpSymmetricFTC_endpoint_width_le (eps : QPos) :
    (endpointDifferenceInterval uniformExpOnSymmetricUnitRealFunRaw (-1) 1
      (uniformExpFTCStage eps)).width <= eps.val := by
  have h : 0 < mesh 0 1 (uniformExpFTCPieces eps) := by
    unfold mesh
    rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos eps))]
    rw [show (1 : Rat) - 0 = 1 by grind, Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2
        (uniformExpFTCPieces_pos eps)))
  have hh : mesh 0 1 (uniformExpFTCPieces eps) ≠ 0 := Rat.ne_of_gt h
  have htail := uniformExpTailMagnitude_le_quotientTolerance
    (mesh 0 1 (uniformExpFTCPieces eps)) hh (uniformExpFTCIndex eps)
  have htail' : uniformExpTailMagnitude (uniformExpFTCStage eps) <=
      (precisionAtStage (uniformExpFTCIndex eps)).val *
        mesh 0 1 (uniformExpFTCPieces eps) / 24 := by
    rw [uniformExpFTCStage_eq_quotient eps]
    have hq : qabs (mesh 0 1 (uniformExpFTCPieces eps)) =
        mesh 0 1 (uniformExpFTCPieces eps) :=
      qabs_eq_self_of_nonneg (Rat.le_of_lt h)
    simpa [uniformExpQuotientTailTolerance, hq] using htail
  have hmesh : mesh 0 1 (uniformExpFTCPieces eps) <= 1 := by
    have hp := uniformExpFTCPieces_pos eps
    have hanti := FTC.one_div_nat_antitone (n := 1)
      (m := uniformExpFTCPieces eps) (by native_decide) hp
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp))
    unfold mesh
    rw [if_neg (Nat.ne_of_gt hp), show (1 : Rat) - 0 = 1 by grind]
    calc
      1 / ((uniformExpFTCPieces eps : Nat) : Rat) <= 1 / (1 : Rat) := hanti
      _ = 1 := by native_decide
  have hprec := uniformExpFTCPrecision_le_input eps
  have hbox : 2 * uniformExpTailRadius (uniformExpFTCStage eps) <=
      (precisionAtStage (uniformExpFTCIndex eps)).val / 6 := by
    unfold uniformExpTailRadius
    have hm := Rat.mul_le_mul_of_nonneg_left htail'
      (by native_decide : (0 : Rat) <= 4)
    calc
      2 * (2 * uniformExpTailMagnitude (uniformExpFTCStage eps)) <=
          4 * ((precisionAtStage (uniformExpFTCIndex eps)).val *
            mesh 0 1 (uniformExpFTCPieces eps) / 24) := by grind
      _ = (precisionAtStage (uniformExpFTCIndex eps)).val *
            mesh 0 1 (uniformExpFTCPieces eps) / 6 := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= (precisionAtStage (uniformExpFTCIndex eps)).val / 6 := by
        have hp := Rat.le_of_lt
          (precisionAtStage (uniformExpFTCIndex eps)).property
        have := Rat.mul_le_mul_of_nonneg_left hmesh hp
        grind [Rat.mul_assoc, Rat.mul_comm]
  rw [endpointDifferenceInterval_width]
  have hsum :
      (uniformExpBox (-1) (uniformExpFTCStage eps)).width +
          (uniformExpBox 1 (uniformExpFTCStage eps)).width <=
        (precisionAtStage (uniformExpFTCIndex eps)).val / 3 := by
    rw [uniformExpBox_width, uniformExpBox_width]
    calc
      2 * uniformExpTailRadius (uniformExpFTCStage eps) +
          2 * uniformExpTailRadius (uniformExpFTCStage eps) <=
          (precisionAtStage (uniformExpFTCIndex eps)).val / 6 +
            (precisionAtStage (uniformExpFTCIndex eps)).val / 6 :=
        rat_add_le_add hbox hbox
      _ <= (precisionAtStage (uniformExpFTCIndex eps)).val / 3 := by grind
  have hactual :
      (uniformExpOnSymmetricUnitRealFunRaw.compute (-1)
        (uniformExpFTCStage eps)).width +
          (uniformExpOnSymmetricUnitRealFunRaw.compute 1
            (uniformExpFTCStage eps)).width <=
        (precisionAtStage (uniformExpFTCIndex eps)).val / 3 := by
    simpa [uniformExpOnSymmetricUnitRealFunRaw, uniformExpRaw_compute] using hsum
  exact Rat.le_trans hactual (by
    have heps : 0 <= eps.val := Rat.le_of_lt eps.property
    rw [show (uniformExpFTCInputPrecision eps).val = eps.val / 5 by rfl] at hprec
    grind)

theorem uniformExpOnSymmetricUnitRealFunRaw_compute (x : Rat)
    (hx : uniformExpOnSymmetricUnitRealFunRaw.domain x) (n : Nat) :
    uniformExpOnSymmetricUnitRealFunRaw.compute x n =
      (uniformExpRaw x).compute n := rfl

/-! This is the exact remaining centered-FTC boundary.  Any finite partition
schedule satisfying `EffectiveDerivativeBoundFTC` immediately yields the
endpoint equivalence; the theorem does not introduce completeness or a
classical integral. -/

theorem uniformExpOnSymmetricUnit_effectiveFTC_of_certificate
    (h : EffectiveDerivativeBoundFTC
      uniformExpOnSymmetricUnitRealFunRaw
      uniformExpOnSymmetricUnitRealFunRaw (-1) 1) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact effectiveDerivativeBoundFTC h

/-- On the centered unit interval the common-prefix representation and the
selected adaptive exponential are pointwise equivalent. -/
theorem uniformExpOnSymmetricUnit_equivalent_expPowerSeries :
    FunctionOnInterval.Equivalent uniformExpOnSymmetricUnit
      (expPowerSeriesOnInterval (-1) 1) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x hxuniform hxadaptive
  change (uniformExpRaw x).Equiv (expPowerSeries x)
  change (-1 : Rat) <= x /\ x <= 1 at hxuniform
  have hx : (-1 : Rat) <= x /\ x <= 1 := hxuniform
  apply uniformExpRaw_equiv_expPowerSeries x
  exact Rat.le_trans (qabs_le_of_neg_le_le hx.1 hx.2) (by native_decide)

/-- The common-prefix exponential satisfies its own two-sided interval
derivative certificate on `[-1,1]`.  The only new estimate beyond the unit
chart is `|h| <= 2`; the `ε |h| / 24` tail stage still pays every quotient and
output-box error. -/
def uniformExpOnSymmetricUnit_hasDerivativeOnInterval :
    HasDerivativeOnInterval uniformExpOnSymmetricUnit uniformExpOnSymmetricUnit where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := uniformExpSelfDerivativeStepPrecision
  evalPrecision := fun _x h n => uniformExpSelfDerivativeEvalPrecision h n
  close := by
    intro x h n hx hxh _hdx hh hsmall
    change (-1 : Rat) <= x /\ x <= 1 at hx
    change (-1 : Rat) <= x + h /\ x + h <= 1 at hxh
    have hx' : (-1 : Rat) <= x /\ x <= 1 := hx
    have hxh' : (-1 : Rat) <= x + h /\ x + h <= 1 := hxh
    have hqx : qabs x <= 2 :=
      Rat.le_trans (qabs_le_of_neg_le_le hx'.1 hx'.2) (by native_decide)
    have hqxh : qabs (x + h) <= 2 :=
      Rat.le_trans (qabs_le_of_neg_le_le hxh'.1 hxh'.2) (by native_decide)
    have habs : qabs h <= 2 := by
      by_cases hnonneg : 0 <= h
      · rw [qabs_eq_self_of_nonneg hnonneg]
        grind [Rat.sub_eq_add_neg]
      · have hnonpos : h <= 0 := by grind
        rw [qabs_eq_neg_of_nonpos hnonpos]
        grind [Rat.sub_eq_add_neg]
    let eps : QPos := precisionAtStage n
    let stage : Nat := uniformExpQuotientPrecision h hh n
    have hstage : uniformExpSelfDerivativeEvalPrecision h n = stage := by
      dsimp [stage]
      exact uniformExpSelfDerivativeEvalPrecision_of_ne h hh n
    have htail : uniformExpTailMagnitude stage <=
        eps.val * qabs h / 24 := by
      dsimp [stage, eps]
      simpa [uniformExpQuotientTailTolerance] using
        uniformExpTailMagnitude_le_quotientTolerance h hh n
    have hfinite : qabs h * 34 <= eps.val / 2 := by
      dsimp [eps]
      exact uniformExpSelfDerivative_finite_error_le_half_precision n hsmall
    have htransport :=
      uniformExp_tail_transport_budgets_of_step_le_two hh habs eps htail
    have hbudget :
        (qabs h * 34 + 2 * uniformExpTailMagnitude stage / qabs h) +
            2 * uniformExpTailRadius stage / qabs h +
              uniformExpTailRadius stage <= eps.val := by
      have htailBudget : 6 * uniformExpTailMagnitude stage / qabs h +
          2 * uniformExpTailMagnitude stage <= eps.val / 2 := htransport.1
      calc
        (qabs h * 34 + 2 * uniformExpTailMagnitude stage / qabs h) +
            2 * uniformExpTailRadius stage / qabs h +
              uniformExpTailRadius stage =
            qabs h * 34 +
              (6 * uniformExpTailMagnitude stage / qabs h +
                2 * uniformExpTailMagnitude stage) := by
                unfold uniformExpTailRadius
                grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
        _ <= eps.val / 2 + eps.val / 2 := rat_add_le_add hfinite htailBudget
        _ <= eps.val := by
          have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hquotientWidth :
        4 * uniformExpTailRadius stage / qabs h <= eps.val := by
      have htailWidth : 8 * uniformExpTailMagnitude stage / qabs h <=
          eps.val / 3 := htransport.2.1
      calc
        4 * uniformExpTailRadius stage / qabs h =
            8 * uniformExpTailMagnitude stage / qabs h := by
              unfold uniformExpTailRadius
              grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
        _ <= eps.val / 3 := htailWidth
        _ <= eps.val := by
          have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hderivativeWidth : 2 * uniformExpTailRadius stage <= eps.val := by
      have htailWidth : 4 * uniformExpTailMagnitude stage <= eps.val / 3 :=
        htransport.2.2
      calc
        2 * uniformExpTailRadius stage =
            4 * uniformExpTailMagnitude stage := by
              unfold uniformExpTailRadius
              grind [Rat.mul_assoc]
        _ <= eps.val / 3 := htailWidth
        _ <= eps.val := by
          have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcenter := uniformExpCenter_secant_error_le hh hqx hqxh stage
    rw [hstage]
    change QInterval.NearAt
      (QInterval.differenceQuotient
        (uniformExpBox (x + h) stage) (uniformExpBox x stage) h)
      (uniformExpBox x stage) eps
    unfold uniformExpBox
    exact intervalAround_differenceQuotient_near_intervalAround
      (uniformExpCenter x stage) (uniformExpCenter (x + h) stage)
      (uniformExpCenter x stage) (uniformExpTailRadius stage) h
      (qabs h * 34 + 2 * uniformExpTailMagnitude stage / qabs h) eps
      hh (by
        unfold uniformExpTailRadius
        exact Rat.mul_nonneg (by native_decide)
          (uniformExpTailMagnitude_nonneg stage)) hcenter hbudget
      hquotientWidth hderivativeWidth

theorem uniformExpSymmetricCell_endpoint_contained_of_step
    {a b : Rat} (n : Nat)
    (ha : -1 <= a) (hb : b <= 1) (hab : a < b)
    (hsmall : qabs (b - a) <=
      1 / ((uniformExpOnSymmetricUnit_hasDerivativeOnInterval.stepPrecision n : Nat) : Rat)) :
    let h := b - a
    let stage := uniformExpSelfDerivativeEvalPrecision h n
    QInterval.ContainsInterval
      (QInterval.scaleByRat h
        (QInterval.expand (uniformExpSymmetricCellRange a b stage)
          (2 * (precisionAtStage n).val)))
      (endpointDifferenceInterval uniformExpOnSymmetricUnitRealFunRaw a b stage) := by
  let h : Rat := b - a
  let stage : Nat := uniformExpSelfDerivativeEvalPrecision h n
  have hpos : 0 < h := by
    dsimp [h]
    exact (Rat.lt_iff_sub_pos a b).mp hab
  have hh : h ≠ 0 := Rat.ne_of_gt hpos
  have ha1 : a <= 1 := Rat.le_trans (Rat.le_of_lt hab) hb
  have hxh : -1 <= a + h ∧ a + h <= 1 := by
    have heq : a + h = b := by dsimp [h]; grind
    rw [heq]
    exact ⟨Rat.le_trans ha (Rat.le_of_lt hab), hb⟩
  have hclose := uniformExpOnSymmetricUnit_hasDerivativeOnInterval.close
    a h n ⟨ha, ha1⟩ hxh ⟨ha, ha1⟩ hh hsmall
  have heval :
      uniformExpOnSymmetricUnit_hasDerivativeOnInterval.evalPrecision a h n = stage := by
    rfl
  rw [heval] at hclose
  change QInterval.NearAt
    (QInterval.differenceQuotient
      (uniformExpBox (a + h) stage) (uniformExpBox a stage) h)
    (uniformExpBox a stage) (precisionAtStage n) at hclose
  have hscaledBox :=
    QInterval.scaleByRat_expand_contains_subInterval_of_differenceQuotient_near
      (A := uniformExpBox a stage) (B := uniformExpBox (a + h) stage)
      (D := uniformExpBox a stage) (h := h) (eps := precisionAtStage n)
      hpos hclose
  have hrange := uniformExpSymmetricCellRange_contains
    (a := a) (b := b) (x := a) stage ha hb hab Rat.le_refl (Rat.le_of_lt hab)
  have hrangeBox :
      (uniformExpSymmetricCellRange a b stage).ContainsInterval
        (uniformExpBox a stage) := by
    simpa [uniformExpBox, uniformExpRaw_compute] using hrange
  have hexpand :
      (QInterval.expand (uniformExpSymmetricCellRange a b stage)
        (2 * (precisionAtStage n).val)).ContainsInterval
        (QInterval.expand (uniformExpBox a stage)
          (2 * (precisionAtStage n).val)) := by
    unfold QInterval.ContainsInterval QInterval.expand at *
    grind
  have hscaledRange := QInterval.scaleByRat_contains_of_nonneg
    (Rat.le_of_lt hpos) hexpand
  have hcombined := hscaledRange.trans hscaledBox
  have heq : a + h = b := by dsimp [h]; grind
  rw [heq] at hcombined
  change QInterval.ContainsInterval
    (QInterval.scaleByRat h
      (QInterval.expand (uniformExpSymmetricCellRange a b stage)
        (2 * (precisionAtStage n).val)))
    (endpointDifferenceInterval uniformExpOnSymmetricUnitRealFunRaw a b stage)
  unfold endpointDifferenceInterval
  have hacompute := uniformExpOnSymmetricUnitRealFunRaw_compute a
    ⟨ha, ha1⟩ stage
  have hbcompute := uniformExpOnSymmetricUnitRealFunRaw_compute b
    ⟨Rat.le_trans ha (Rat.le_of_lt hab), hb⟩ stage
  dsimp
  rw [hacompute, hbcompute]
  simpa [h, uniformExpRaw_compute, QInterval.subInterval] using hcombined

def uniformExpSymmetricFTCInternalTolerance (eps : QPos) : QPos :=
  ⟨eps.val / 4, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property
      ((Rat.inv_pos).2 (by native_decide))⟩

def uniformExpSymmetricFTCScaledBound (eps : QPos) (k : Nat) : QInterval :=
  QInterval.expand
    (uniformExpSymmetricCellRange
      (leftPoint (-1) 1
        (uniformExpSymmetricFTCPieces (uniformExpSymmetricFTCInternalTolerance eps)) k)
      (leftPoint (-1) 1
        (uniformExpSymmetricFTCPieces (uniformExpSymmetricFTCInternalTolerance eps))
        (k + 1))
      (uniformExpFTCStage (uniformExpSymmetricFTCInternalTolerance eps)))
    (2 * (precisionAtStage
      (uniformExpFTCIndex (uniformExpSymmetricFTCInternalTolerance eps))).val)

theorem uniformExpSymmetricFTCScaledBound_width_le (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition
      (uniformExpSymmetricFTCInternalTolerance eps)).pieces) :
    (uniformExpSymmetricFTCScaledBound eps k).width <= eps.val / 2 := by
  let e := uniformExpSymmetricFTCInternalTolerance eps
  unfold uniformExpSymmetricFTCScaledBound
  rw [QInterval.expand_width]
  have hraw := uniformExpSymmetricCellRange_width_le_half_eps e k hk
  have hend := uniformExpSymmetricFTCPartition_cell_endpoints e k hk
  rw [hend.1, hend.2] at hraw
  have hprec := uniformExpFTCPrecision_le_input e
  have hinput : (uniformExpFTCInputPrecision e).val = e.val / 5 := rfl
  rw [hinput] at hprec
  have hq : (precisionAtStage (uniformExpFTCIndex e)).val <= eps.val / 20 := by
    dsimp [e, uniformExpSymmetricFTCInternalTolerance] at hprec ⊢
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  have hqnonneg : 0 <=
      2 * (precisionAtStage (uniformExpFTCIndex e)).val :=
    Rat.mul_nonneg (by native_decide)
      (Rat.le_of_lt (precisionAtStage (uniformExpFTCIndex e)).property)
  have heps : 0 <= eps.val := Rat.le_of_lt eps.property
  have he : e.val = eps.val / 4 := by
    rfl
  have hraw' :
      (uniformExpSymmetricCellRange
        (leftPoint (-1) 1 (uniformExpSymmetricFTCPieces e) k)
        (leftPoint (-1) 1 (uniformExpSymmetricFTCPieces e) (k + 1))
        (uniformExpFTCStage e)).width <= eps.val / 8 := by
    rw [he] at hraw
    grind [Rat.div_def]
  have hq' : 2 * (2 * (precisionAtStage (uniformExpFTCIndex e)).val) <=
      eps.val / 5 := by
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  have hmain :
      (uniformExpSymmetricCellRange
        (leftPoint (-1) 1 (uniformExpSymmetricFTCPieces e) k)
        (leftPoint (-1) 1 (uniformExpSymmetricFTCPieces e) (k + 1))
        (uniformExpFTCStage e)).width +
        2 * (2 * (precisionAtStage (uniformExpFTCIndex e)).val) <= eps.val / 2 := by
    calc
      _ <= eps.val / 8 + eps.val / 5 := rat_add_le_add hraw' hq'
      _ <= eps.val / 2 := by grind [Rat.div_def]
  simpa [e] using hmain

theorem uniformExpSymmetricFTCScaledBound_contains
    (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition
      (uniformExpSymmetricFTCInternalTolerance eps)).pieces)
    (x : Rat)
    (hx : ((uniformExpSymmetricFTCPartition
      (uniformExpSymmetricFTCInternalTolerance eps)).cell k hk).contains x) :
    QInterval.ContainsInterval (uniformExpSymmetricFTCScaledBound eps k)
      ((uniformExpRaw x).compute
        (uniformExpFTCStage (uniformExpSymmetricFTCInternalTolerance eps))) := by
  let e := uniformExpSymmetricFTCInternalTolerance eps
  have hraw := uniformExpSymmetricFTCIndexedBound_contains_raw e k hk x hx
  unfold uniformExpSymmetricFTCScaledBound
  unfold uniformExpSymmetricFTCIndexedBound at hraw
  dsimp [e] at hraw ⊢
  unfold QInterval.ContainsInterval QInterval.expand at *
  grind

theorem uniformExpSymmetricFTCScaledSum_width_le (eps : QPos) :
    ((uniformExpSymmetricFTCPartition
      (uniformExpSymmetricFTCInternalTolerance eps)).boundIntegralSum
      (fun k _ => uniformExpSymmetricFTCScaledBound eps k)).width <= eps.val := by
  let e := uniformExpSymmetricFTCInternalTolerance eps
  have hsum := RationalPartition.uniform_boundIntegralSum_width_le_indexed
    (a := (-1 : Rat)) (b := 1) (uniformExpSymmetricFTCPieces e)
    (uniformExpSymmetricFTCPieces_pos e) (by native_decide)
    (fun k => uniformExpSymmetricFTCScaledBound eps k) (eps.val / 2) (by
      intro k hk
      exact uniformExpSymmetricFTCScaledBound_width_le eps k hk)
  change ((RationalPartition.uniform (-1) 1
    (uniformExpSymmetricFTCPieces e)
    (uniformExpSymmetricFTCPieces_pos e) (by native_decide)).boundIntegralSum
    (fun k _ => uniformExpSymmetricFTCScaledBound eps k)).width <= eps.val
  exact Rat.le_trans hsum (by
    have heps : 0 <= eps.val := Rat.le_of_lt eps.property
    grind [Rat.div_def])

theorem uniformExpSymmetricFTCScaledBound_local_endpoint_contained
    (eps : QPos) (k : Nat)
    (hk : k < (uniformExpSymmetricFTCPartition
      (uniformExpSymmetricFTCInternalTolerance eps)).pieces) :
    QInterval.ContainsInterval
      (((uniformExpSymmetricFTCPartition
        (uniformExpSymmetricFTCInternalTolerance eps)).cell k hk).scaleBound
        (uniformExpSymmetricFTCScaledBound eps k))
      (endpointDifferenceInterval uniformExpOnSymmetricUnitRealFunRaw
        ((uniformExpSymmetricFTCPartition
          (uniformExpSymmetricFTCInternalTolerance eps)).cell k hk).lower
        ((uniformExpSymmetricFTCPartition
          (uniformExpSymmetricFTCInternalTolerance eps)).cell k hk).upper
        (uniformExpFTCStage (uniformExpSymmetricFTCInternalTolerance eps))) := by
  let e := uniformExpSymmetricFTCInternalTolerance eps
  let C := (uniformExpSymmetricFTCPartition e).cell k hk
  have hpos : 0 < C.width := by
    rw [show C.width = mesh 0 1 (uniformExpFTCPieces e) by
      dsimp [C]
      exact uniformExpSymmetricFTCPartition_cell_width e k hk]
    unfold mesh
    rw [if_neg (Nat.ne_of_gt (uniformExpFTCPieces_pos e))]
    rw [show (1 : Rat) - 0 = 1 by grind, Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (uniformExpFTCPieces_pos e)))
  have hab : C.lower < C.upper := by
    apply (Rat.lt_iff_sub_pos _ _).mpr
    simpa [RationalSubinterval.width] using hpos
  have hsmall : qabs (C.upper - C.lower) <=
      1 / ((uniformExpOnSymmetricUnit_hasDerivativeOnInterval.stepPrecision
        (uniformExpFTCIndex e) : Nat) : Rat) := by
    rw [qabs_eq_self_of_nonneg
      (Rat.le_of_lt ((Rat.lt_iff_sub_pos _ _).mp hab))]
    change C.width <= 1 /
      ((uniformExpOnSymmetricUnit_hasDerivativeOnInterval.stepPrecision
        (uniformExpFTCIndex e) : Nat) : Rat)
    rw [show C.width = mesh 0 1 (uniformExpFTCPieces e) by
      dsimp [C]
      exact uniformExpSymmetricFTCPartition_cell_width e k hk]
    exact uniformExpFTCPieces_step_le e
  have hlocal := uniformExpSymmetricCell_endpoint_contained_of_step
    (n := uniformExpFTCIndex e) C.lower_mem C.upper_mem hab hsmall
  have hstage : uniformExpSelfDerivativeEvalPrecision (C.upper - C.lower)
      (uniformExpFTCIndex e) = uniformExpFTCStage e := by
    have heq : C.upper - C.lower = mesh 0 1 (uniformExpFTCPieces e) := by
      dsimp [C, RationalSubinterval.width]
      exact uniformExpSymmetricFTCPartition_cell_width e k hk
    rw [heq, uniformExpSelfDerivativeEvalPrecision_eq_quotient]
    rw [uniformExpFTCStage_eq_quotient e]
  unfold uniformExpSymmetricFTCScaledBound
  change QInterval.ContainsInterval
    (C.scaleBound
      (QInterval.expand (uniformExpSymmetricCellRange C.lower C.upper
        (uniformExpFTCStage e))
        (2 * (precisionAtStage (uniformExpFTCIndex e)).val)))
    (endpointDifferenceInterval uniformExpOnSymmetricUnitRealFunRaw
      C.lower C.upper (uniformExpFTCStage e))
  unfold RationalSubinterval.scaleBound RationalSubinterval.width
  rw [← hstage]
  exact hlocal

def uniformExpOnSymmetricUnit_selectedStageFTCIndexed :
    SelectedStageCandidateDerivativeFTCIndexed
      uniformExpOnSymmetricUnitRealFunRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1 where
  primitive_valid := uniformExpOnSymmetricUnitRealFunRaw_valid
  choosePartition := fun eps =>
    uniformExpSymmetricFTCPartition (uniformExpSymmetricFTCInternalTolerance eps)
  chooseStage := fun eps =>
    uniformExpFTCStage (uniformExpSymmetricFTCInternalTolerance eps)
  derivativeBound := uniformExpSymmetricFTCScaledBound
  primitive_domain_on := by
    intro eps i hi
    exact (uniformExpSymmetricFTCPartition
      (uniformExpSymmetricFTCInternalTolerance eps)).point_in_bounds hi
  candidate_domain_on := by
    intro eps k hk x hx
    exact RationalSubinterval.contains_inDomain
      ((uniformExpSymmetricFTCPartition
        (uniformExpSymmetricFTCInternalTolerance eps)).cell k hk) hx
  candidate_contained := by
    intro eps k hk x hx
    change QInterval.ContainsInterval (uniformExpSymmetricFTCScaledBound eps k)
      ((uniformExpRaw x).compute
        (uniformExpFTCStage (uniformExpSymmetricFTCInternalTolerance eps)))
    exact uniformExpSymmetricFTCScaledBound_contains eps k hk x hx
  local_endpoint_contained := by
    intro eps k hk
    exact uniformExpSymmetricFTCScaledBound_local_endpoint_contained eps k hk
  riemann_width := uniformExpSymmetricFTCScaledSum_width_le
  endpoint_width := by
    intro eps
    let e := uniformExpSymmetricFTCInternalTolerance eps
    have hendpoint := uniformExpSymmetricFTC_endpoint_width_le e
    have he : e.val <= eps.val := by
      dsimp [e, uniformExpSymmetricFTCInternalTolerance]
      have heps : 0 <= eps.val := Rat.le_of_lt eps.property
      grind [Rat.div_def]
    exact Rat.le_trans hendpoint he

theorem uniformExpOnSymmetricUnit_effectiveFTC :
    (uniformExpOnSymmetricUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw).Equiv
      uniformExpOnSymmetricUnit_selectedStageFTCIndexed.toSelected.endpointRaw := by
  exact selectedStageCandidateDerivativeFTCIndexed
    uniformExpOnSymmetricUnit_selectedStageFTCIndexed

/-! The centered selected-stage schedule is not required to be nested.  Its
finite FTC sum is therefore stabilized against the canonical endpoint
difference, giving the public integral representative used by the ODE layer. -/

def uniformExpOnSymmetricUnit_endpointDifferenceValid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute uniformExpOnSymmetricUnitRealFunRaw (-1) 1) :=
  endpointDifference_valid_of_fun_valid uniformExpOnSymmetricUnitRealFunRaw_valid
    (by exact ⟨by native_decide, by native_decide⟩)
    (by exact ⟨by native_decide, by native_decide⟩)

set_option maxHeartbeats 1000000 in
theorem selectedStageCandidateDerivativeFTC_boundedIntegral_widthsShrink
    {F dF : RealFunRaw} {a b : Rat}
    (h : SelectedStageCandidateDerivativeFTC F dF a b) :
    RealRaw.WidthsShrinkToZero h.boundedIntegralRaw.compute := by
  intro eps
  refine ⟨eps.val.den + 1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hprec : (precisionAtStage n).val <= eps.val := by
    have hden : 0 < (eps.val.den + 1 : Nat) := by omega
    have hanti := FTC.one_div_nat_antitone
      (n := eps.val.den + 1) (m := n)
      (by exact hden) hnpos hn
    have hbase := FTC.one_div_den_succ_le_of_pos eps.property
    calc
      (precisionAtStage n).val = 1 / (n : Rat) := by
        simp [precisionAtStage, Nat.ne_of_gt hnpos]
      _ <= 1 / (((eps.val.den + 1 : Nat) : Rat)) := hanti
      _ <= eps.val := hbase
  change
    (SelectedStageCandidateDerivativeFTC.boundedIntegralInterval
      h (precisionAtStage n)).width <= eps.val
  exact Rat.le_trans
    (h.riemann_width (precisionAtStage n)) hprec

theorem uniformExpOnSymmetricUnit_boundedIntegral_widthsShrink :
    RealRaw.WidthsShrinkToZero
      uniformExpOnSymmetricUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw.compute := by
  exact selectedStageCandidateDerivativeFTC_boundedIntegral_widthsShrink
    uniformExpOnSymmetricUnit_selectedStageFTCIndexed.toSelected

def uniformExpOnSymmetricUnitStabilized : RealRaw :=
  RealRaw.prefixStabilize
    uniformExpOnSymmetricUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw
    (fun n =>
      (endpointDifferenceRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1
        uniformExpOnSymmetricUnit_endpointDifferenceValid).compute n |>.width)

theorem uniformExpOnSymmetricUnit_boundedIntegral_equiv_endpointDifference :
    uniformExpOnSymmetricUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw.Equiv
      (endpointDifferenceRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1
        uniformExpOnSymmetricUnit_endpointDifferenceValid) := by
  exact TwoStageCandidateDerivativeFTC.boundedIntegralRaw_equiv_endpointDifference
    uniformExpOnSymmetricUnit_selectedStageFTCIndexed.toSelected.toTwoStage
    uniformExpOnSymmetricUnit_endpointDifferenceValid

theorem uniformExpOnSymmetricUnitStabilized_valid :
    uniformExpOnSymmetricUnitStabilized.Valid := by
  unfold uniformExpOnSymmetricUnitStabilized
  apply RealRaw.prefixStabilize_valid
    (candidate := uniformExpOnSymmetricUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw)
    (anchor := endpointDifferenceRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1
      uniformExpOnSymmetricUnit_endpointDifferenceValid)
    (radius := fun n =>
      (endpointDifferenceRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1
        uniformExpOnSymmetricUnit_endpointDifferenceValid).compute n |>.width)
  · exact uniformExpOnSymmetricUnit_boundedIntegral_widthsShrink
  · simpa [endpointDifferenceRaw, RealRaw.Valid] using
      uniformExpOnSymmetricUnit_endpointDifferenceValid
  · exact uniformExpOnSymmetricUnit_boundedIntegral_equiv_endpointDifference
  · intro n
    exact Rat.le_refl
  · intro eps
    obtain ⟨N, hN⟩ := uniformExpOnSymmetricUnit_endpointDifferenceValid.2.2 eps
    exact ⟨N, fun n hn => hN n hn⟩

theorem uniformExpOnSymmetricUnitStabilized_equiv_endpointDifference :
    uniformExpOnSymmetricUnitStabilized.Equiv
      (endpointDifferenceRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1
        uniformExpOnSymmetricUnit_endpointDifferenceValid) := by
  unfold uniformExpOnSymmetricUnitStabilized
  apply RealRaw.prefixStabilize_equiv_anchor
    (candidate := uniformExpOnSymmetricUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw)
    (anchor := endpointDifferenceRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1
      uniformExpOnSymmetricUnit_endpointDifferenceValid)
    (radius := fun n =>
      (endpointDifferenceRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1
        uniformExpOnSymmetricUnit_endpointDifferenceValid).compute n |>.width)
  · simpa [endpointDifferenceRaw, RealRaw.Valid] using
      uniformExpOnSymmetricUnit_endpointDifferenceValid
  · exact uniformExpOnSymmetricUnit_boundedIntegral_equiv_endpointDifference
  · intro n
    exact Rat.le_refl

def uniformExpOnSymmetricUnitStabilizedConstruction :
    Integral.ConstructionFor uniformExpOnSymmetricUnit where
  compute := uniformExpOnSymmetricUnitStabilized.compute
  certificate := by
    simpa [RealRaw.Valid] using uniformExpOnSymmetricUnitStabilized_valid

theorem uniformExpOnSymmetricUnitStabilizedIntegral_equiv_endpointDifference :
    (Integral.integralFor uniformExpOnSymmetricUnit
      uniformExpOnSymmetricUnitStabilizedConstruction).Equiv
      (endpointDifferenceRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1
        uniformExpOnSymmetricUnit_endpointDifferenceValid) := by
  change uniformExpOnSymmetricUnitStabilized.Equiv
    (endpointDifferenceRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1
      uniformExpOnSymmetricUnit_endpointDifferenceValid)
  exact uniformExpOnSymmetricUnitStabilized_equiv_endpointDifference

/-! The one-sided unit chart can now be stabilized against its canonical
endpoint difference.  This is the standard \\([0,1]\\) effective-FTC
instance, while the centered chart below is the local ODE instance. -/
def uniformExpOnUnit_endpointDifferenceValid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute uniformExpOnUnitRealFunRaw 0 1) :=
  endpointDifference_valid_of_fun_valid uniformExpOnUnitRealFunRaw_valid
    (by exact ⟨by native_decide, by native_decide⟩)
    (by exact ⟨by native_decide, by native_decide⟩)

def uniformExpOnUnitStabilized : RealRaw :=
  RealRaw.prefixStabilize
    uniformExpOnUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw
    (fun n =>
      (endpointDifferenceRaw uniformExpOnUnitRealFunRaw 0 1
        uniformExpOnUnit_endpointDifferenceValid).compute n |>.width)

theorem uniformExpOnUnitStabilized_valid :
    uniformExpOnUnitStabilized.Valid := by
  unfold uniformExpOnUnitStabilized
  apply RealRaw.prefixStabilize_valid
    (candidate := uniformExpOnUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw)
    (anchor := endpointDifferenceRaw uniformExpOnUnitRealFunRaw 0 1
      uniformExpOnUnit_endpointDifferenceValid)
    (radius := fun n =>
      (endpointDifferenceRaw uniformExpOnUnitRealFunRaw 0 1
        uniformExpOnUnit_endpointDifferenceValid).compute n |>.width)
  · exact selectedStageCandidateDerivativeFTC_boundedIntegral_widthsShrink
      uniformExpOnUnit_selectedStageFTCIndexed.toSelected
  · simpa [endpointDifferenceRaw, RealRaw.Valid] using
      uniformExpOnUnit_endpointDifferenceValid
  · exact TwoStageCandidateDerivativeFTC.boundedIntegralRaw_equiv_endpointDifference
      uniformExpOnUnit_selectedStageFTCIndexed.toSelected.toTwoStage
      uniformExpOnUnit_endpointDifferenceValid
  · intro n
    exact Rat.le_refl
  · intro eps
    obtain ⟨N, hN⟩ := uniformExpOnUnit_endpointDifferenceValid.2.2 eps
    exact ⟨N, fun n hn => hN n hn⟩

theorem uniformExpOnUnitStabilized_equiv_endpointDifference :
    uniformExpOnUnitStabilized.Equiv
      (endpointDifferenceRaw uniformExpOnUnitRealFunRaw 0 1
        uniformExpOnUnit_endpointDifferenceValid) := by
  unfold uniformExpOnUnitStabilized
  apply RealRaw.prefixStabilize_equiv_anchor
    (candidate := uniformExpOnUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw)
    (anchor := endpointDifferenceRaw uniformExpOnUnitRealFunRaw 0 1
      uniformExpOnUnit_endpointDifferenceValid)
    (radius := fun n =>
      (endpointDifferenceRaw uniformExpOnUnitRealFunRaw 0 1
        uniformExpOnUnit_endpointDifferenceValid).compute n |>.width)
  · simpa [endpointDifferenceRaw, RealRaw.Valid] using
      uniformExpOnUnit_endpointDifferenceValid
  · exact TwoStageCandidateDerivativeFTC.boundedIntegralRaw_equiv_endpointDifference
      uniformExpOnUnit_selectedStageFTCIndexed.toSelected.toTwoStage
      uniformExpOnUnit_endpointDifferenceValid
  · intro n
    exact Rat.le_refl

def uniformExpOnUnitStabilizedConstruction :
    Integral.ConstructionFor uniformExpOnUnit where
  compute := uniformExpOnUnitStabilized.compute
  certificate := by
    simpa [RealRaw.Valid] using uniformExpOnUnitStabilized_valid

theorem uniformExpOnUnitStabilizedIntegral_equiv_endpointDifference :
    (Integral.integralFor uniformExpOnUnit
      uniformExpOnUnitStabilizedConstruction).Equiv
      (endpointDifferenceRaw uniformExpOnUnitRealFunRaw 0 1
        uniformExpOnUnit_endpointDifferenceValid) := by
  change uniformExpOnUnitStabilized.Equiv
    (endpointDifferenceRaw uniformExpOnUnitRealFunRaw 0 1
      uniformExpOnUnit_endpointDifferenceValid)
  exact uniformExpOnUnitStabilized_equiv_endpointDifference

theorem uniformExpOnUnitStabilizedIntegral_equiv_exp_endpoint_subtraction :
    (Integral.integralFor uniformExpOnUnit
      uniformExpOnUnitStabilizedConstruction).Equiv
      ((uniformExpOnUnitRealFunRaw.apply uniformExpOnUnitRealFunRaw_valid
          (1 : Rat) (by constructor <;> native_decide)) -
        (uniformExpOnUnitRealFunRaw.apply uniformExpOnUnitRealFunRaw_valid
          (0 : Rat) (by constructor <;> native_decide))) := by
  let hF := uniformExpOnUnitRealFunRaw_valid
  have hzero : uniformExpOnUnitRealFunRaw.domain (0 : Rat) := by
    constructor <;> native_decide
  have hone : uniformExpOnUnitRealFunRaw.domain (1 : Rat) := by
    constructor <;> native_decide
  have hdiff := endpointDifferenceRaw_equiv_sub_apply
    hF hzero hone uniformExpOnUnit_endpointDifferenceValid
  have hintegral :
      (Integral.integralFor uniformExpOnUnit
        uniformExpOnUnitStabilizedConstruction).Valid :=
    Integral.integralFor_valid uniformExpOnUnit
      uniformExpOnUnitStabilizedConstruction
  have hendpoint :
      (endpointDifferenceRaw uniformExpOnUnitRealFunRaw 0 1
        uniformExpOnUnit_endpointDifferenceValid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using
      uniformExpOnUnit_endpointDifferenceValid
  have hsub :
      ((uniformExpOnUnitRealFunRaw.apply hF (1 : Rat) hone) -
        (uniformExpOnUnitRealFunRaw.apply hF (0 : Rat) hzero)).Valid :=
    RealRaw.sub_valid
      (by simpa [RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
        hF (1 : Rat) hone)
      (by simpa [RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
        hF (0 : Rat) hzero)
  exact RealRaw.equiv_trans hintegral hendpoint hsub
    uniformExpOnUnitStabilizedIntegral_equiv_endpointDifference hdiff

/-! The one-sided endpoint subtraction is also independent of the evaluator:
the common-prefix endpoints can be replaced by the canonical factorial
series endpoints through the maintained equivalence chain. -/
theorem uniformExpOnUnitStabilizedIntegral_equiv_powerSeries_endpoint_subtraction :
    (Integral.integralFor uniformExpOnUnit
      uniformExpOnUnitStabilizedConstruction).Equiv
      ((expPowerSeries (1 : Rat)) - (expPowerSeries (0 : Rat))) := by
  let hF := uniformExpOnUnitRealFunRaw_valid
  have hzero : uniformExpOnUnitRealFunRaw.domain (0 : Rat) := by
    constructor <;> native_decide
  have hone : uniformExpOnUnitRealFunRaw.domain (1 : Rat) := by
    constructor <;> native_decide
  have huniformOne :
      (uniformExpOnUnitRealFunRaw.apply hF (1 : Rat) hone).Valid := by
    simpa [RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF (1 : Rat) hone
  have huniformZero :
      (uniformExpOnUnitRealFunRaw.apply hF (0 : Rat) hzero).Valid := by
    simpa [RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF (0 : Rat) hzero
  have hseriesOne : (expPowerSeries (1 : Rat)).Valid :=
    expPowerSeries_valid (1 : Rat)
  have hseriesZero : (expPowerSeries (0 : Rat)).Valid :=
    expPowerSeries_valid (0 : Rat)
  have honeEq :
      (uniformExpOnUnitRealFunRaw.apply hF (1 : Rat) hone).Equiv
        (expPowerSeries (1 : Rat)) := by
    change (uniformExpRaw (1 : Rat)).Equiv (expPowerSeries (1 : Rat))
    exact uniformExpRaw_equiv_expPowerSeries 1 (by native_decide)
  have hzeroEq :
      (uniformExpOnUnitRealFunRaw.apply hF (0 : Rat) hzero).Equiv
        (expPowerSeries (0 : Rat)) := by
    change (uniformExpRaw (0 : Rat)).Equiv (expPowerSeries (0 : Rat))
    exact uniformExpRaw_equiv_expPowerSeries 0 (by native_decide)
  have hsubEq :
      ((uniformExpOnUnitRealFunRaw.apply hF (1 : Rat) hone) -
        (uniformExpOnUnitRealFunRaw.apply hF (0 : Rat) hzero)).Equiv
        ((expPowerSeries (1 : Rat)) - (expPowerSeries (0 : Rat))) :=
    RealRaw.sub_equiv huniformOne hseriesOne huniformZero hseriesZero
      honeEq hzeroEq
  have hintegralSub :=
    uniformExpOnUnitStabilizedIntegral_equiv_exp_endpoint_subtraction
  have hintegral :
      (Integral.integralFor uniformExpOnUnit
        uniformExpOnUnitStabilizedConstruction).Valid :=
    Integral.integralFor_valid uniformExpOnUnit
      uniformExpOnUnitStabilizedConstruction
  have huniformSub := RealRaw.sub_valid huniformOne huniformZero
  have hseriesSub := RealRaw.sub_valid hseriesOne hseriesZero
  exact RealRaw.equiv_trans hintegral huniformSub hseriesSub
    hintegralSub hsubEq

/-! The endpoint subtraction can be normalized at the public raw level.  This
is the user-facing unit exponential FTC statement: the rectangle integral of
the certified exponential evaluator is `exp(1) - 1`, where both terms are
still computable interval representations. -/

theorem uniformExpOnUnitStabilizedIntegral_equiv_powerSeries_one_sub_one :
    (Integral.integralFor uniformExpOnUnit
      uniformExpOnUnitStabilizedConstruction).Equiv
      ((expPowerSeries (1 : Rat)) - RealRaw.ofRat 1) := by
  have hseriesOne : (expPowerSeries (1 : Rat)).Valid :=
    expPowerSeries_valid (1 : Rat)
  have hseriesZero : (expPowerSeries (0 : Rat)).Valid :=
    expPowerSeries_valid (0 : Rat)
  have hone : (RealRaw.ofRat (1 : Rat)).Valid :=
    RealRaw.ofRat_valid (1 : Rat)
  have hsubEq :
      ((expPowerSeries (1 : Rat)) - (expPowerSeries (0 : Rat))).Equiv
        ((expPowerSeries (1 : Rat)) - RealRaw.ofRat 1) := by
    apply RealRaw.sub_equiv
    · exact hseriesOne
    · exact hseriesOne
    · exact hseriesZero
    · exact hone
    · exact RealRaw.equiv_refl _ hseriesOne
    · exact expPowerSeries_zero_equiv_one
  have hsubValid :
      ((expPowerSeries (1 : Rat)) - (expPowerSeries (0 : Rat))).Valid :=
    RealRaw.sub_valid hseriesOne hseriesZero
  have hnormalizedValid :
      ((expPowerSeries (1 : Rat)) - RealRaw.ofRat 1).Valid :=
    RealRaw.sub_valid hseriesOne hone
  exact RealRaw.equiv_trans
    (Integral.integralFor_valid uniformExpOnUnit
      uniformExpOnUnitStabilizedConstruction)
    hsubValid hnormalizedValid
    uniformExpOnUnitStabilizedIntegral_equiv_powerSeries_endpoint_subtraction
    hsubEq

/-! The endpoint-difference spelling can be transported to the ordinary
subtraction of the two certified exponential endpoint evaluations.  This is
the first user-facing non-polynomial integral identity in the ODE route:
the integral is still a `RealRaw`, and the familiar notation is only a proved
representation edge. -/
theorem uniformExpOnSymmetricUnitStabilizedIntegral_equiv_exp_endpoint_subtraction :
    (Integral.integralFor uniformExpOnSymmetricUnit
      uniformExpOnSymmetricUnitStabilizedConstruction).Equiv
      ((uniformExpOnSymmetricUnitRealFunRaw.apply
          uniformExpOnSymmetricUnitRealFunRaw_valid (1 : Rat)
          (by constructor <;> native_decide)) -
        (uniformExpOnSymmetricUnitRealFunRaw.apply
          uniformExpOnSymmetricUnitRealFunRaw_valid (-1 : Rat)
          (by constructor <;> native_decide))) := by
  let hF := uniformExpOnSymmetricUnitRealFunRaw_valid
  have hminus : uniformExpOnSymmetricUnitRealFunRaw.domain (-1 : Rat) := by
    constructor <;> native_decide
  have hplus : uniformExpOnSymmetricUnitRealFunRaw.domain (1 : Rat) := by
    constructor <;> native_decide
  have hendpoint :=
    uniformExpOnSymmetricUnit_endpointDifferenceValid
  have hdiff := endpointDifferenceRaw_equiv_sub_apply
    hF hminus hplus hendpoint
  have hintegral :
      (Integral.integralFor uniformExpOnSymmetricUnit
        uniformExpOnSymmetricUnitStabilizedConstruction).Valid :=
    Integral.integralFor_valid uniformExpOnSymmetricUnit
      uniformExpOnSymmetricUnitStabilizedConstruction
  have hendpoint :
      (endpointDifferenceRaw uniformExpOnSymmetricUnitRealFunRaw (-1) 1
        hendpoint).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using hendpoint
  have hsub :
      ((uniformExpOnSymmetricUnitRealFunRaw.apply hF (1 : Rat) hplus) -
        (uniformExpOnSymmetricUnitRealFunRaw.apply hF (-1 : Rat) hminus)).Valid :=
    RealRaw.sub_valid
      (by
        simpa [RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
          hF (1 : Rat) hplus)
      (by
        simpa [RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
          hF (-1 : Rat) hminus)
  exact RealRaw.equiv_trans hintegral hendpoint hsub
    uniformExpOnSymmetricUnitStabilizedIntegral_equiv_endpointDifference hdiff

/-! The same identity can be transported to the canonical factorial-series
representation.  This is the representation-chain step needed by later ODE
and logarithm arguments: the integral theorem is independent of which
certified exponential evaluator is preferred. -/
theorem uniformExpOnSymmetricUnitStabilizedIntegral_equiv_powerSeries_endpoint_subtraction :
    (Integral.integralFor uniformExpOnSymmetricUnit
      uniformExpOnSymmetricUnitStabilizedConstruction).Equiv
      ((expPowerSeries (1 : Rat)) - (expPowerSeries (-1 : Rat))) := by
  let hF := uniformExpOnSymmetricUnitRealFunRaw_valid
  have hminus : uniformExpOnSymmetricUnitRealFunRaw.domain (-1 : Rat) := by
    constructor <;> native_decide
  have hplus : uniformExpOnSymmetricUnitRealFunRaw.domain (1 : Rat) := by
    constructor <;> native_decide
  have huniformPlus :
      (uniformExpOnSymmetricUnitRealFunRaw.apply hF (1 : Rat) hplus).Valid := by
    simpa [RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF (1 : Rat) hplus
  have huniformMinus :
      (uniformExpOnSymmetricUnitRealFunRaw.apply hF (-1 : Rat) hminus).Valid := by
    simpa [RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF (-1 : Rat) hminus
  have hseriesPlus : (expPowerSeries (1 : Rat)).Valid :=
    expPowerSeries_valid (1 : Rat)
  have hseriesMinus : (expPowerSeries (-1 : Rat)).Valid :=
    expPowerSeries_valid (-1 : Rat)
  have hplusEq :
      (uniformExpOnSymmetricUnitRealFunRaw.apply hF (1 : Rat) hplus).Equiv
        (expPowerSeries (1 : Rat)) := by
    change (uniformExpRaw (1 : Rat)).Equiv (expPowerSeries (1 : Rat))
    exact uniformExpRaw_equiv_expPowerSeries 1 (by native_decide)
  have hminusEq :
      (uniformExpOnSymmetricUnitRealFunRaw.apply hF (-1 : Rat) hminus).Equiv
        (expPowerSeries (-1 : Rat)) := by
    change (uniformExpRaw (-1 : Rat)).Equiv (expPowerSeries (-1 : Rat))
    exact uniformExpRaw_equiv_expPowerSeries (-1) (by native_decide)
  have hsubEq :
      ((uniformExpOnSymmetricUnitRealFunRaw.apply hF (1 : Rat) hplus) -
        (uniformExpOnSymmetricUnitRealFunRaw.apply hF (-1 : Rat) hminus)).Equiv
        ((expPowerSeries (1 : Rat)) - (expPowerSeries (-1 : Rat))) :=
    RealRaw.sub_equiv huniformPlus hseriesPlus huniformMinus hseriesMinus
      hplusEq hminusEq
  have hintegralSub :=
    uniformExpOnSymmetricUnitStabilizedIntegral_equiv_exp_endpoint_subtraction
  have hintegral :
      (Integral.integralFor uniformExpOnSymmetricUnit
        uniformExpOnSymmetricUnitStabilizedConstruction).Valid :=
    Integral.integralFor_valid uniformExpOnSymmetricUnit
      uniformExpOnSymmetricUnitStabilizedConstruction
  have huniformSub := RealRaw.sub_valid huniformPlus huniformMinus
  have hseriesSub := RealRaw.sub_valid hseriesPlus hseriesMinus
  exact RealRaw.equiv_trans hintegral huniformSub hseriesSub
    hintegralSub hsubEq

/-- The centered exponential chart has the exact initial value one at zero. -/
theorem uniformExpOnSymmetricUnit_zero_equiv_one :
    (PartialRealFunRaw.apply uniformExpOnSymmetricUnit.raw
      uniformExpOnSymmetricUnit.valid_on (0 : Rat)
      (uniformExpOnSymmetricUnit.defined_on 0 (by
        constructor <;> native_decide))).Equiv (RealRaw.ofRat 1) := by
  change (uniformExpRaw (0 : Rat)).Equiv (RealRaw.ofRat 1)
  exact uniformExpOnUnit_zero_equiv_one

/-- A centered constructive initial-value solution of `f' = f`. -/
def uniformExpOnSymmetricUnit_solvesSelfDerivative :
    SolvesSelfDerivativeOnInterval uniformExpOnSymmetricUnit where
  derivative_self := uniformExpOnSymmetricUnit_hasDerivativeOnInterval
  initial := 0
  initial_mem := by
    constructor <;> native_decide
  initial_value := RealRaw.ofRat 1
  initial_value_valid := by
    change RealRaw.ValidCompute (fun _ => { lo := 1, hi := 1 })
    exact RealRaw.ofRat_valid (1 : Rat)
  initial_value_equiv := by
    exact uniformExpOnSymmetricUnit_zero_equiv_one

/-- The total series-function wrapper inherits the exact power-series initial
value at zero. -/
theorem expPowerSeriesFunction_zero_equiv_one :
    (expPowerSeriesFunction.evalRaw (0 : Rat) trivial).Equiv
      (RealRaw.ofRat 1) := by
  change (expPowerSeries (0 : Rat)).Equiv (RealRaw.ofRat 1)
  exact expPowerSeries_zero_equiv_one

/-- On every rational interval that contains zero, the packaged series
function supplies the initial-value field required by a future
`SolvesSelfDerivativeOnInterval` certificate.  The remaining field is the
global analytic self-derivative proof; the local forward derivative at zero is
constructed below. -/
theorem expPowerSeriesOnInterval_zero_initial_value
    {a b : Rat} (hzero : inDomainInterval a b 0) :
    (PartialRealFunRaw.apply (expPowerSeriesOnInterval a b).raw
      (expPowerSeriesOnInterval a b).valid_on 0
      ((expPowerSeriesOnInterval a b).defined_on 0 hzero)).Equiv
      (RealRaw.ofRat 1) := by
  change (expPowerSeries (0 : Rat)).Equiv (RealRaw.ofRat 1)
  exact expPowerSeries_zero_equiv_one

/-- The exact zero-input series computation is therefore a valid raw real,
in addition to being stagewise equal to the rational constant one. -/
theorem expPowerSeries_zero_valid : (expPowerSeries (0 : Rat)).Valid := by
  simpa [PowerSeriesValid] using expPowerSeries_valid (0 : Rat)

private theorem powerSeriesState_two (x : Rat) :
    powerSeriesState x 2 = (1 + x, x * x / 2) := by
  unfold powerSeriesState
  change powerSeriesLoopStep x (powerSeriesLoopStep x (0, 1) 0) 1 = _
  simp [powerSeriesLoopStep]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

private theorem powerSeriesState_term_nonneg (x : Rat) (hx : 0 <= x) :
    forall N, 0 <= (powerSeriesState x N).2
  | 0 => by
      change 0 <= (1 : Rat)
      native_decide
  | N + 1 => by
      rw [powerSeriesState_succ]
      simp only [powerSeriesLoopStep]
      rw [Rat.div_def]
      have hden : 0 < (N : Rat) + 1 := by
        exact_mod_cast Nat.succ_pos N
      exact Rat.mul_nonneg
        (Rat.mul_nonneg (powerSeriesState_term_nonneg x hx N) hx)
        (Rat.le_of_lt ((Rat.inv_pos).2 hden))

private theorem rat_div_le_self_of_one_le {a d : Rat}
    (ha : 0 <= a) (hd : 1 <= d) :
    a / d <= a := by
  have hdpos : 0 < d := by grind
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      (a / d) * d = a := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
      _ <= a * d := by
        calc
          a = a * 1 := by rw [Rat.mul_one]
          _ <= a * d := Rat.mul_le_mul_of_nonneg_left hd ha
  · exact hdpos

/-- A finite positive-tail budget for the factorial series.  After the
constant and linear terms, the accumulated remainder plus twice the next
term never exceeds the square of the input on the unit half interval. -/
private theorem powerSeriesState_linear_tail_budget (x : Rat)
    (hx : 0 <= x) (hxhalf : x <= (1 : Rat) / 2) :
    forall k : Nat,
      0 <= (powerSeriesState x (2 + k)).1 - (1 + x) /\
      (powerSeriesState x (2 + k)).1 - (1 + x) +
          2 * (powerSeriesState x (2 + k)).2 <= x * x
  | 0 => by
      rw [powerSeriesState_two]
      constructor
      · grind [Rat.sub_eq_add_neg]
      · grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  | k + 1 => by
      have ih := powerSeriesState_linear_tail_budget x hx hxhalf k
      let N : Nat := 2 + k
      have hterm0 : 0 <= (powerSeriesState x N).2 :=
        powerSeriesState_term_nonneg x hx N
      have hdenone : (1 : Rat) <= (N : Rat) + 1 := by
        exact_mod_cast (show 1 <= N + 1 by omega)
      have hratio_le_x : x / ((N : Rat) + 1) <= x :=
        rat_div_le_self_of_one_le hx hdenone
      have hratio : x / ((N : Rat) + 1) <= (1 : Rat) / 2 :=
        Rat.le_trans hratio_le_x hxhalf
      have hnext_le :
          (powerSeriesState x N).2 * x / ((N : Rat) + 1) <=
            (powerSeriesState x N).2 * ((1 : Rat) / 2) := by
        calc
          (powerSeriesState x N).2 * x / ((N : Rat) + 1) =
              (powerSeriesState x N).2 * (x / ((N : Rat) + 1)) := by
            rw [Rat.div_def]
            grind [Rat.mul_assoc]
          _ <= (powerSeriesState x N).2 * ((1 : Rat) / 2) :=
            Rat.mul_le_mul_of_nonneg_left hratio hterm0
      have htwo_next :
          2 * ((powerSeriesState x N).2 * x / ((N : Rat) + 1)) <=
            (powerSeriesState x N).2 := by
        calc
          2 * ((powerSeriesState x N).2 * x / ((N : Rat) + 1)) <=
              2 * ((powerSeriesState x N).2 * ((1 : Rat) / 2)) :=
            Rat.mul_le_mul_of_nonneg_left hnext_le (by native_decide)
          _ = (powerSeriesState x N).2 := by
            rw [Rat.div_def]
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      have hstate : powerSeriesState x (N + 1) =
          powerSeriesLoopStep x (powerSeriesState x N) N :=
        powerSeriesState_succ x N
      have hsum :
          (powerSeriesState x (N + 1)).1 =
            (powerSeriesState x N).1 + (powerSeriesState x N).2 := by
        rw [hstate]
        rfl
      have hterm :
          (powerSeriesState x (N + 1)).2 =
            (powerSeriesState x N).2 * x / ((N : Rat) + 1) := by
        rw [hstate]
        rfl
      have hN : N + 1 = 2 + (k + 1) := by
        dsimp [N]
        omega
      rw [← hN, hsum, hterm]
      constructor
      · have htail0 : 0 <= (powerSeriesState x N).1 - (1 + x) := by
          simpa [N] using ih.1
        grind [Rat.sub_eq_add_neg]
      · have hbudget := ih.2
        grind [Rat.sub_eq_add_neg]

/-- The evaluator's initial public stage already includes enough positive
Taylor terms for a quadratic forward-error budget on the half unit interval.
This is a finite fact about the particular rational loop, not a limit or an
appeal to completeness. -/
private theorem expPowerSeries_stage_zero_linear_tail_bounds (x : Rat)
    (hx : 0 <= x) (hxhalf : x <= (1 : Rat) / 2) :
    0 <= powerSeriesCenter x 0 - (1 + x) /\
      powerSeriesCenter x 0 - (1 + x) <= x * x /\
      0 <= powerSeriesTailRadius x 0 /\
      powerSeriesTailRadius x 0 <= x * x := by
  let k : Nat := 6 + 2 * x.num.natAbs
  have hterms : expPowerSeriesTerms x 0 = 2 + k := by
    dsimp [k]
    unfold expPowerSeriesTerms
    omega
  have hbudget := powerSeriesState_linear_tail_budget x hx hxhalf k
  have hterm0 : 0 <= (powerSeriesState x (2 + k)).2 :=
    powerSeriesState_term_nonneg x hx (2 + k)
  have hrem0 : 0 <= powerSeriesCenter x 0 - (1 + x) := by
    rw [expPowerSeries_center_eq_state, hterms]
    exact hbudget.1
  have hremle : powerSeriesCenter x 0 - (1 + x) <= x * x := by
    rw [expPowerSeries_center_eq_state, hterms]
    have htwoterm : 0 <= 2 * (powerSeriesState x (2 + k)).2 := by
      exact Rat.mul_nonneg (by native_decide) hterm0
    grind [Rat.sub_eq_add_neg]
  have hr0 : 0 <= powerSeriesTailRadius x 0 :=
    powerSeriesTailRadius_nonneg_of_ratioBound x
      (expPowerSeries_ratio_bound x) 0
  have htermle : 2 * (powerSeriesState x (2 + k)).2 <= x * x := by
    have hrem := hbudget.1
    have hbudget' := hbudget.2
    grind [Rat.sub_eq_add_neg]
  have htail := powerSeriesTailRadius_stage_le_two_mul_absTerm x 0
  rw [hterms] at htail
  unfold powerSeriesTermAtTerms at htail
  rw [qabs_eq_self_of_nonneg hterm0] at htail
  exact ⟨hrem0, hremle, hr0, Rat.le_trans htail htermle⟩

/-- The forward derivative certificate asks for a factor-two smaller step
than its output precision.  This elementary schedule both keeps the input in
the half unit interval and leaves two copies of the step inside the requested
precision. -/
private theorem expPowerSeries_forward_step_bounds (h : Rat) (n : Nat)
    (hsmall : h <=
      1 / ((2 * (if n = 0 then 1 else n) : Nat) : Rat)) :
    h <= (1 : Rat) / 2 /\ 2 * h <= (precisionAtStage n).val := by
  by_cases hn : n = 0
  · subst n
    have hhalf : h <= (1 : Rat) / 2 := by
      simpa using hsmall
    constructor
    · exact hhalf
    · calc
        2 * h <= 2 * ((1 : Rat) / 2) :=
          Rat.mul_le_mul_of_nonneg_left hhalf (by native_decide)
        _ = 1 := by native_decide
        _ = (precisionAtStage 0).val := by native_decide
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hsmall' : h <= 1 / (2 * (n : Rat)) := by
      simpa [hn, Rat.natCast_mul] using hsmall
    have htwo_n : (2 : Rat) <= 2 * (n : Rat) := by
      have hnat : (1 : Rat) <= (n : Rat) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hnpos)
      simpa using Rat.mul_le_mul_of_nonneg_left hnat
        (by native_decide : (0 : Rat) <= 2)
    have hhalfbound : 1 / (2 * (n : Rat)) <= (1 : Rat) / 2 :=
      rat_div_den_antitone (a := 1) (d := 2) (e := 2 * (n : Rat))
        (by native_decide) (by native_decide) htwo_n
    constructor
    · exact Rat.le_trans hsmall' hhalfbound
    · have htwice := Rat.mul_le_mul_of_nonneg_left hsmall'
        (by native_decide : (0 : Rat) <= 2)
      calc
        2 * h <= 2 * (1 / (2 * (n : Rat))) := htwice
        _ = 1 / (n : Rat) := by
          rw [Rat.div_def, Rat.div_def]
          have hnrat : (n : Rat) ≠ 0 :=
            Rat.ne_of_gt ((Rat.natCast_pos).2 hnpos)
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ = (precisionAtStage n).val := by
          simp [precisionAtStage, hn]

/-- A positive interval enclosure whose center and radius have quadratic
forward error yields a first-order difference quotient enclosure.  The two
copies of the step in the precision budget pay separately for the center
remainder and the interval radius. -/
private theorem intervalAround_forward_quotient_near_one
    (c r h : Rat) (eps : QPos)
    (hpos : 0 < h)
    (hrem0 : 0 <= c - (1 + h))
    (hremle : c - (1 + h) <= h * h)
    (hr0 : 0 <= r) (hrle : r <= h * h)
    (hprec : 2 * h <= eps.val) :
    QInterval.NearAt
      (QInterval.differenceQuotient (intervalAround c r)
        { lo := 1, hi := 1 } h)
      { lo := 1, hi := 1 } eps := by
  have hhne : h ≠ 0 := Rat.ne_of_gt hpos
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hprecmul : 2 * h * h <= eps.val * h :=
    Rat.mul_le_mul_of_nonneg_right hprec (Rat.le_of_lt hpos)
  have hupper : c - r - 1 <= (1 + eps.val) * h := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  have hlower : h <= c + r - 1 := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  have hwidth : 2 * r <= eps.val * h := by
    calc
      2 * r <= 2 * (h * h) :=
        Rat.mul_le_mul_of_nonneg_left hrle (by native_decide)
      _ = 2 * h * h := by grind [Rat.mul_assoc]
      _ <= eps.val * h := hprecmul
  unfold QInterval.NearAt QInterval.differenceQuotient QInterval.divRat
    QInterval.sub QInterval.scaleRat intervalAround QInterval.width
  rw [if_pos hinv]
  dsimp
  change
    (1 / h) * (c - r - 1) <= 1 + eps.val /\
      1 <= (1 / h) * (c + r - 1) + eps.val /\
      (1 / h) * (c + r - 1) - (1 / h) * (c - r - 1) <= eps.val /\
      1 - 1 <= eps.val
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := h)
    · rw [Rat.div_def, Rat.one_mul]
      calc
        (h⁻¹ * (c - r - 1)) * h = c - r - 1 := by
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
        _ <= (1 + eps.val) * h := hupper
    · exact hpos
  constructor
  · have hquot : (1 : Rat) <= (1 / h) * (c + r - 1) := by
      apply Rat.le_of_mul_le_mul_right (c := h)
      · calc
          (1 : Rat) * h = h := by rw [Rat.one_mul]
          _ <= c + r - 1 := hlower
          _ = ((1 / h) * (c + r - 1)) * h := by
            rw [Rat.div_def, Rat.one_mul]
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      · exact hpos
    calc
      (1 : Rat) <= (1 / h) * (c + r - 1) := hquot
      _ <= (1 / h) * (c + r - 1) + eps.val := by
        grind
  constructor
  · have hwidthdiv : (2 * r) * h⁻¹ <= eps.val := by
      apply Rat.le_of_mul_le_mul_right (c := h)
      · calc
          (2 * r) * h⁻¹ * h = 2 * r := by
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
          _ <= eps.val * h := hwidth
      · exact hpos
    calc
      (1 / h) * (c + r - 1) - (1 / h) * (c - r - 1) =
          (2 * r) * h⁻¹ := by
        rw [Rat.div_def, Rat.one_mul]
        grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]
      _ <= eps.val := hwidthdiv
  · grind

/-- A direct finite difference-quotient certificate for the existing
power-series evaluator.  For a positive rational step in the bounded domain
`0 < h <= 1/2`, its public stage-zero interval, divided by the exact value at
zero, is within the requested rational precision of the derivative box
`[1,1]`.  The hypotheses are only the explicit quadratic remainder and
precision budgets; this is not a completed-limit or general derivative
statement. -/
theorem expPowerSeries_stage_zero_differenceQuotient_near_one
    {h : Rat} (hpos : 0 < h) (hhalf : h <= (1 : Rat) / 2)
    (n : Nat) (hprecision : 2 * h <= (precisionAtStage n).val) :
    QInterval.NearAt
      (QInterval.differenceQuotient
        (intervalAround (powerSeriesCenter h 0) (powerSeriesTailRadius h 0))
        { lo := 1, hi := 1 } h)
      { lo := 1, hi := 1 } (precisionAtStage n) := by
  have htail := expPowerSeries_stage_zero_linear_tail_bounds h
    (Rat.le_of_lt hpos) hhalf
  exact intervalAround_forward_quotient_near_one
    (powerSeriesCenter h 0) (powerSeriesTailRadius h 0) h
    (precisionAtStage n) hpos htail.1 htail.2.1 htail.2.2.1 htail.2.2.2
    hprecision

/-- The exact degree-two Taylor prefix has forward derivative one at zero.

This is a finite-difference certificate for the literal rational polynomial,
not yet the analytic derivative certificate for the full series evaluator. -/
def expTaylorQuadraticOnUnit : FunctionOnInterval :=
  FunctionOnInterval.exactRat expTaylorQuadratic 0 1

def expTaylorQuadratic_forwardDerivativeAtZero :
    HasForwardDerivativeAt expTaylorQuadraticOnUnit 0 RealRaw.one := by
  refine
    { x_mem := by
        constructor <;> native_decide
      derivative_valid := by
        change RealRaw.ValidCompute (fun _ : Nat => { lo := 1, hi := 1 })
        exact RealRaw.ofRat_valid (1 : Rat)
      stepPrecision := fun n => if n = 0 then 1 else n
      evalPrecision := fun _h _n => 0
      close := ?_ }
  intro h n hmem hpos hsmall
  have hprecision : h <= (precisionAtStage n).val := by
    change h <= 1 / (((if n = 0 then 1 else n : Nat) : Rat)) at hsmall
    by_cases hn : n = 0
    · subst n
      calc
        h <= 1 / (1 : Rat) := by
          change h <= 1 / (1 : Rat) at hsmall
          exact hsmall
        _ = (precisionAtStage 0).val := by native_decide
    · simpa [precisionAtStage, hn] using hsmall
  have hhalf_le_h : h / 2 <= h := by
    have hscale := Rat.mul_le_mul_of_nonneg_right
      (show (1 : Rat) / 2 <= 1 by native_decide) (Rat.le_of_lt hpos)
    simpa [Rat.div_def, Rat.mul_comm] using hscale
  have hhalf : h / 2 <= (precisionAtStage n).val :=
    Rat.le_trans hhalf_le_h hprecision
  have hgoal : intervalNearAtPrecision
      (QInterval.differenceQuotient
        { lo := expTaylorQuadratic h, hi := expTaylorQuadratic h }
        { lo := expTaylorQuadratic 0, hi := expTaylorQuadratic 0 } h)
      { lo := 1, hi := 1 } n := by
    rw [QInterval.differenceQuotient_singleton]
    have hhne : h ≠ 0 := Rat.ne_of_gt hpos
    have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hhne
    have hquotient :
        (expTaylorQuadratic h - expTaylorQuadratic 0) / h = 1 + h / 2 := by
      unfold expTaylorQuadratic
      rw [Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.mul_comm]
    rw [hquotient]
    unfold intervalNearAtPrecision QInterval.NearAt QInterval.width
    have heps : 0 <= (precisionAtStage n).val :=
      Rat.le_of_lt (precisionAtStage n).property
    constructor
    · exact (Rat.add_le_add_left).2 hhalf
    constructor
    · grind [Rat.sub_eq_add_neg]
    constructor <;> grind [Rat.sub_eq_add_neg]
  simpa only [expTaylorQuadraticOnUnit, FunctionOnInterval.compute,
    FunctionOnInterval.exactRat, Rat.zero_add, RealRaw.one,
    RealRaw.ofRat_compute] using hgoal

/-- The tail-enclosed exponential evaluator itself has forward derivative
one at zero on `[0, 1]`.

For every requested rational precision, the certificate evaluates the full
series algorithm at its public stage zero.  Its finite loop has already
consumed enough positive terms that both the remaining Taylor sum and the
certified geometric radius are quadratic in the positive step; interval
division then produces the required first-order quotient enclosure. -/
def expPowerSeriesOnUnit_forwardDerivativeAtZero :
    HasForwardDerivativeAt (expPowerSeriesOnInterval 0 1) 0 RealRaw.one := by
  refine
    { x_mem := by
        constructor <;> native_decide
      derivative_valid := by
        change RealRaw.ValidCompute (fun _ : Nat => { lo := 1, hi := 1 })
        exact RealRaw.ofRat_valid (1 : Rat)
      stepPrecision := fun n => 2 * (if n = 0 then 1 else n)
      evalPrecision := fun _h _n => 0
      close := ?_ }
  intro h n hmem hpos hsmall
  have hstep := expPowerSeries_forward_step_bounds h n hsmall
  have hhalf : h <= (1 : Rat) / 2 := hstep.1
  have hprecision : 2 * h <= (precisionAtStage n).val := hstep.2
  have htail := expPowerSeries_stage_zero_linear_tail_bounds h
    (Rat.le_of_lt hpos) hhalf
  have hgoal : QInterval.NearAt
      (QInterval.differenceQuotient
        (intervalAround (powerSeriesCenter h 0) (powerSeriesTailRadius h 0))
        { lo := 1, hi := 1 } h)
      { lo := 1, hi := 1 } (precisionAtStage n) :=
    intervalAround_forward_quotient_near_one
      (powerSeriesCenter h 0) (powerSeriesTailRadius h 0) h
      (precisionAtStage n) hpos htail.1 htail.2.1 htail.2.2.1 htail.2.2.2
      hprecision
  simp only [Rat.zero_add] at hmem
  have hvalue : (expPowerSeriesOnInterval 0 1).compute h hmem 0 =
      intervalAround (powerSeriesCenter h 0) (powerSeriesTailRadius h 0) := by
    change (expPowerSeries h).compute 0 = _
    exact expPowerSeries_compute_eq h 0
  have hzero (hz : inDomainInterval (0 : Rat) 1 0) :
      (expPowerSeriesOnInterval 0 1).compute 0 hz 0 = { lo := 1, hi := 1 } := by
    change (expPowerSeries (0 : Rat)).compute 0 = _
    rw [expPowerSeries_zero_compute_eq, RealRaw.ofRat_compute]
  simp only [Rat.zero_add]
  rw [hvalue]
  change intervalNearAtPrecision
    (QInterval.differenceQuotient
      (intervalAround (powerSeriesCenter h 0) (powerSeriesTailRadius h 0))
      ((expPowerSeries (0 : Rat)).compute 0) h)
    (RealRaw.one.compute 0) n
  rw [expPowerSeries_zero_compute_eq, RealRaw.ofRat_compute]
  simpa only [intervalNearAtPrecision, RealRaw.one, RealRaw.ofRat_compute]
    using hgoal

/-- The preceding basepoint derivative is genuinely a self-derivative
statement: its derivative representative is the full power-series evaluator
at zero, rather than an externally substituted constant.  The exact
stagewise computation `expPowerSeries 0 = 1` makes the two presentations
coincide without an appeal to real-number completeness. -/
def expPowerSeriesOnUnit_forwardSelfDerivativeAtZero :
    HasForwardDerivativeAt (expPowerSeriesOnInterval 0 1) 0
      (expPowerSeries 0) := by
  refine
    { x_mem := by
        constructor <;> native_decide
      derivative_valid := by
        exact expPowerSeries_valid 0
      stepPrecision := fun n => 2 * (if n = 0 then 1 else n)
      evalPrecision := fun _h _n => 0
      close := ?_ }
  intro h n hmem hpos hsmall
  have hstep := expPowerSeries_forward_step_bounds h n hsmall
  have hhalf : h <= (1 : Rat) / 2 := hstep.1
  have hprecision : 2 * h <= (precisionAtStage n).val := hstep.2
  have htail := expPowerSeries_stage_zero_linear_tail_bounds h
    (Rat.le_of_lt hpos) hhalf
  have hgoal : QInterval.NearAt
      (QInterval.differenceQuotient
        (intervalAround (powerSeriesCenter h 0) (powerSeriesTailRadius h 0))
        { lo := 1, hi := 1 } h)
      { lo := 1, hi := 1 } (precisionAtStage n) :=
    intervalAround_forward_quotient_near_one
      (powerSeriesCenter h 0) (powerSeriesTailRadius h 0) h
      (precisionAtStage n) hpos htail.1 htail.2.1 htail.2.2.1 htail.2.2.2
      hprecision
  simp only [Rat.zero_add] at hmem
  have hvalue : (expPowerSeriesOnInterval 0 1).compute h hmem 0 =
      intervalAround (powerSeriesCenter h 0) (powerSeriesTailRadius h 0) := by
    change (expPowerSeries h).compute 0 = _
    exact expPowerSeries_compute_eq h 0
  have hzero (hz : inDomainInterval (0 : Rat) 1 0) :
      (expPowerSeriesOnInterval 0 1).compute 0 hz 0 = { lo := 1, hi := 1 } := by
    change (expPowerSeries (0 : Rat)).compute 0 = _
    rw [expPowerSeries_zero_compute_eq, RealRaw.ofRat_compute]
  simp only [Rat.zero_add]
  rw [hvalue]
  change intervalNearAtPrecision
    (QInterval.differenceQuotient
      (intervalAround (powerSeriesCenter h 0) (powerSeriesTailRadius h 0))
      ((expPowerSeries (0 : Rat)).compute 0) h)
    ((expPowerSeries 0).compute 0) n
  rw [expPowerSeries_zero_compute_eq, RealRaw.ofRat_compute]
  simpa only [intervalNearAtPrecision] using hgoal

theorem ePowerSeries_valid_of_nested
    (hnested : EPowerSeriesNested)
    (hshrink : EPowerSeriesWidthsShrink) : EPowerSeriesValid := by
  change PowerSeriesValid 1
  exact expPowerSeries_valid_of_nested_and_shrinking_autoRatio
    (1 : Rat) hnested hshrink

theorem eEuler_valid_of_nested
    (hnested : EEulerNested) : EEulerValid := by
  change EulerValid 1
  exact expEuler_valid_of_nested 1 hnested

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
  simp [Real.alternatives, eCertified, Real.withAlternative]

theorem eEulerStabilized_mem_eCertified_alternatives :
    eEulerStabilized ∈ eCertified.alternatives := by
  simp [Real.alternatives, eCertified, Real.withAlternative]

theorem ePowerSeries_mem_eCertified_alternatives :
    ePowerSeries ∈ eCertified.alternatives := by
  simp [Real.alternatives, eCertified, Real.withAlternative]

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
