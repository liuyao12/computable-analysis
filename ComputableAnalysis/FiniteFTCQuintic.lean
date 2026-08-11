import ComputableAnalysis.FiniteFTCIntervalRegular
import ComputableAnalysis.Series

set_option maxHeartbeats 1000000

/-!
# A finite quintic FTC certificate

This file gives a rational, finite certificate for the integral of `x ^ 5` on
`[0, 1]`.  The image intervals, endpoint sums, and the enclosure of `1 / 6`
are all explicit; no completed real or general Cauchy construction is used.
-/

namespace ComputableAnalysis
namespace Integral

private theorem rat_pow_le_one {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    ∀ k : Nat, x ^ k <= 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have h := Rat.mul_le_mul_of_nonneg_left ih hx0
      calc
        x ^ (k + 1) = x * x ^ k := by grind [Rat.pow_succ]
        _ <= x * 1 := h
        _ = x := by simp
        _ <= 1 := hx1

def exactQuinticInterval (I : QInterval) : QInterval :=
  { lo := I.lo ^ 5, hi := I.hi ^ 5 }

private theorem five_width_le_one_div_succ_of_width_le
    {w : Rat} (n : Nat)
    (hw : w <= 1 / ((5 * (n + 1) : Nat) : Rat)) :
    5 * w <= 1 / ((n + 1 : Nat) : Rat) := by
  calc
    5 * w <= 5 * (1 / ((5 * (n + 1) : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hw (by native_decide)
    _ = 1 / ((n + 1 : Nat) : Rat) := by
      rw [Rat.div_def]
      have hnrat : ((n + 1 : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
      rw [show ((5 * (n + 1) : Nat) : Rat) =
        (5 : Rat) * ((n + 1 : Nat) : Rat) by
          exact_mod_cast (by omega : 5 * (n + 1) = 5 * (n + 1))]
      rw [Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

def exactRat_quintic_intervalRegularOn_unit :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 5) 0 1) where
  evalInterval := fun I _hI _n => exactQuinticInterval I
  inputPrecision := fun n => 5 * (n + 1)
  inputPrecision_pos := by intro n; omega
  output_width := by
    intro I hI n hsmall
    unfold subintervalOf at hI
    have hw : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hlo : 0 <= I.lo := by simpa using hI.1
    have hhi : I.hi <= 1 := by simpa using hI.2.2
    have hwidth : (exactQuinticInterval I).width = I.width *
        (I.hi ^ 4 + I.hi ^ 3 * I.lo + I.hi ^ 2 * I.lo ^ 2 +
          I.hi * I.lo ^ 3 + I.lo ^ 4) := by
      unfold exactQuinticInterval QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul]
    rw [hwidth]
    constructor
    · exact Rat.mul_nonneg hw (by
        exact Rat.add_nonneg (Rat.add_nonneg
          (Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg (by grind))
            (Rat.mul_nonneg (Rat.pow_nonneg (by grind)) hlo))
            (Rat.mul_nonneg (Rat.pow_nonneg (by grind)) (Rat.pow_nonneg hlo)))
          (Rat.mul_nonneg (by grind) (Rat.pow_nonneg hlo)))
          (Rat.pow_nonneg hlo))
    · have hhi0 : 0 <= I.hi := by grind
      have hlo1 : I.lo <= 1 := by grind
      have hhi4 : I.hi ^ 4 <= 1 := rat_pow_le_one hhi0 hhi 4
      have hlo4 : I.lo ^ 4 <= 1 := rat_pow_le_one hlo hlo1 4
      have h1 : I.hi ^ 3 * I.lo <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_right
          (rat_pow_le_one hhi0 hhi 3) hlo
        exact Rat.le_trans h (by grind)
      have h2 : I.hi ^ 2 * I.lo ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_right
          (rat_pow_le_one hhi0 hhi 2) (Rat.pow_nonneg (n := 2) hlo)
        have hb := rat_pow_le_one hlo hlo1 2
        have h' := Rat.mul_le_mul_of_nonneg_left hb
          (by native_decide : (0 : Rat) <= 1)
        calc
          I.hi ^ 2 * I.lo ^ 2 <= 1 * I.lo ^ 2 := h
          _ <= 1 * 1 := h'
          _ = 1 := by simp
      have h3 : I.hi * I.lo ^ 3 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left
          (rat_pow_le_one hlo hlo1 3) hhi0
        exact Rat.le_trans h (by grind)
      have hsum : I.hi ^ 4 + I.hi ^ 3 * I.lo + I.hi ^ 2 * I.lo ^ 2 +
          I.hi * I.lo ^ 3 + I.lo ^ 4 <= 5 := by grind
      have hp := Rat.mul_le_mul_of_nonneg_left hsum hw
      calc
        I.width * (I.hi ^ 4 + I.hi ^ 3 * I.lo + I.hi ^ 2 * I.lo ^ 2 +
            I.hi * I.lo ^ 3 + I.lo ^ 4) <= I.width * 5 := hp
        _ = 5 * I.width := by rw [Rat.mul_comm]
        _ <= 1 / ((n + 1 : Nat) : Rat) :=
          five_width_le_one_div_succ_of_width_le n hsmall
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    unfold subintervalOf at hI
    unfold exactQuinticInterval QInterval.ContainsInterval
    rw [FunctionOnInterval.exactRat_compute]
    have hx' : 0 <= x ∧ x <= 1 := by
      simpa [FunctionOnInterval.exactRat, inDomainInterval] using hx
    have hx0 : 0 <= x := hx'.1
    have hlo : 0 <= I.lo := by simpa using hI.1
    have hhi0 : 0 <= I.hi := by grind
    have hl : 0 <= (x - I.lo) *
        (x ^ 4 + x ^ 3 * I.lo + x ^ 2 * I.lo ^ 2 +
          x * I.lo ^ 3 + I.lo ^ 4) := by
      exact Rat.mul_nonneg (by grind)
        (Rat.add_nonneg (Rat.add_nonneg
          (Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg hx0)
            (Rat.mul_nonneg (Rat.pow_nonneg hx0) hlo))
            (Rat.mul_nonneg (Rat.pow_nonneg hx0) (Rat.pow_nonneg hlo)))
          (Rat.mul_nonneg hx0 (Rat.pow_nonneg hlo))) (Rat.pow_nonneg hlo))
    have hr : 0 <= (I.hi - x) *
        (I.hi ^ 4 + I.hi ^ 3 * x + I.hi ^ 2 * x ^ 2 +
          I.hi * x ^ 3 + x ^ 4) := by
      exact Rat.mul_nonneg (by grind)
        (Rat.add_nonneg (Rat.add_nonneg
          (Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg hhi0)
            (Rat.mul_nonneg (Rat.pow_nonneg hhi0) hx0))
            (Rat.mul_nonneg (Rat.pow_nonneg hhi0) (Rat.pow_nonneg hx0)))
          (Rat.mul_nonneg hhi0 (Rat.pow_nonneg hx0))) (Rat.pow_nonneg hx0))
    constructor <;> grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]

def exactRat_quintic_lipschitz_on_unit :
    Integral.LipschitzOnUnit (fun x : Rat => x ^ 5) 5 := by
  constructor
  · native_decide
  · intro s t hs hs1 ht ht1
    have hsum : 0 <= s ^ 4 + s ^ 3 * t + s ^ 2 * t ^ 2 +
        s * t ^ 3 + t ^ 4 := by
      exact Rat.add_nonneg (Rat.add_nonneg
        (Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg (by grind))
          (Rat.mul_nonneg (Rat.pow_nonneg (by grind)) (by grind)))
          (Rat.mul_nonneg (Rat.pow_nonneg (by grind)) (Rat.pow_nonneg (by grind))))
        (Rat.mul_nonneg (by grind) (Rat.pow_nonneg (by grind))))
        (Rat.pow_nonneg (by grind))
    have hsum5 : s ^ 4 + s ^ 3 * t + s ^ 2 * t ^ 2 +
        s * t ^ 3 + t ^ 4 <= 5 := by
      have hs0 : 0 <= s := by grind
      have ht0 : 0 <= t := by grind
      have hs4 : s ^ 4 <= 1 := rat_pow_le_one hs0 hs1 4
      have ht4 : t ^ 4 <= 1 := rat_pow_le_one ht0 ht1 4
      have hst1 : s ^ 3 * t <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_right (rat_pow_le_one hs0 hs1 3) ht0
        exact Rat.le_trans h (by grind)
      have hst2 : s ^ 2 * t ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_right
          (rat_pow_le_one hs0 hs1 2) (Rat.pow_nonneg (n := 2) ht0)
        have h' := Rat.mul_le_mul_of_nonneg_left
          (rat_pow_le_one ht0 ht1 2) (by native_decide : (0 : Rat) <= 1)
        calc
          s ^ 2 * t ^ 2 <= 1 * t ^ 2 := h
          _ <= 1 * 1 := h'
          _ = 1 := by simp
      have hst3 : s * t ^ 3 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left (rat_pow_le_one ht0 ht1 3) hs0
        exact Rat.le_trans h (by grind)
      grind
    have hf : s ^ 5 - t ^ 5 = (s - t) *
        (s ^ 4 + s ^ 3 * t + s ^ 2 * t ^ 2 + s * t ^ 3 + t ^ 4) := by
      grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul]
    rw [hf, qabs_mul]
    calc
      qabs (s - t) * qabs (s ^ 4 + s ^ 3 * t + s ^ 2 * t ^ 2 + s * t ^ 3 + t ^ 4) <=
          qabs (s - t) * 5 :=
        Rat.mul_le_mul_of_nonneg_left
          (by simpa [qabs_eq_self_of_nonneg hsum] using hsum5) (qabs_nonneg _)
      _ = 5 * qabs (t - s) := by
        rw [show qabs (s - t) = qabs (t - s) by
          rw [show s - t = -(t - s) by grind [Rat.sub_eq_add_neg], qabs_neg]]
        grind [Rat.mul_comm]

def exactRat_quintic_integral_certificate :
    Integral.IntervalRegularIntegralCertificate
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 5) 0 1) where
  regular := exactRat_quintic_intervalRegularOn_unit
  construction :=
    IntegralIdentities.LipschitzDyadic.construction (fun x : Rat => x ^ 5) 5
      exactRat_quintic_lipschitz_on_unit

theorem exactRat_quintic_integral_raw_valid :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 5) 0 1)
      exactRat_quintic_integral_certificate).Valid := by
  exact Integral.raw_valid _ exactRat_quintic_integral_certificate

theorem exactQuintic_uniformLeftSum_eq {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ 5) n =
      Series.fifthPowerSum n / (n : Rat) ^ 6 := by
  have hnrat : (n : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : ∀ k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) => total + (1 / (n : Rat)) *
            (((j : Rat) / (n : Rat)) ^ 5)) 0 =
        Series.fifthPowerSum k / (n : Rat) ^ 6 := by
    intro k; induction k with
    | zero => simp [Series.fifthPowerSum, Rat.div_def]
    | succ k ih =>
        simp at ih ⊢
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih, Series.fifthPowerSum_succ]
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
          Rat.add_mul, Rat.pow_succ, Rat.mul_inv_cancel]
  unfold IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
  exact haux n

theorem exactQuintic_uniformRightSum_eq {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ 5) n =
      Series.fifthPowerSum (n + 1) / (n : Rat) ^ 6 := by
  have hnrat : (n : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : ∀ k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) => total + (1 / (n : Rat)) *
            ((((j + 1 : Nat) : Rat) / (n : Rat)) ^ 5)) 0 =
        Series.fifthPowerSum (k + 1) / (n : Rat) ^ 6 := by
    intro k; induction k with
    | zero => simp [Series.fifthPowerSum, Rat.div_def]; grind
    | succ k ih =>
        simp at ih ⊢
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih]
        have hterm : (1 / (n : Rat)) *
            (((k : Rat) + 1) / (n : Rat)) ^ 5 =
              ((k : Rat) + 1) ^ 5 / (n : Rat) ^ 6 := by
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        change Series.fifthPowerSum (k + 1) / (n : Rat) ^ 6 + _ =
          Series.fifthPowerSum (k + 1 + 1) / (n : Rat) ^ 6
        rw [hterm]
        rw [show k + 1 + 1 = (k + 1) + 1 by omega,
          Series.fifthPowerSum_succ, Series.fifthPowerSum_succ]
        have hs : Series.fifthPowerSum (k + 1) =
            Series.fifthPowerSum k + (k : Rat) ^ 5 := by
          rw [Series.fifthPowerSum_succ]
        rw [hs]
        grind [Rat.natCast_add, Rat.add_assoc]
  unfold IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
  exact haux n

theorem exactQuintic_uniformLeftSum_le_one_sixth :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ 5) 10 <= 1 / 6 := by
  native_decide

theorem exactQuintic_uniformRightSum_ge_one_sixth :
    1 / 6 <= IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ 5) 10 := by
  native_decide

theorem exactQuintic_compute_contains_one_sixth :
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 5) 5 10).ContainsInterval
      { lo := 1 / 6, hi := 1 / 6 } := by
  have hl := IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
    exactRat_quintic_lipschitz_on_unit 10
  have hr := IntegralIdentities.LipschitzDyadic.compute_contains_uniformRightEndpointSum
    exactRat_quintic_lipschitz_on_unit 10
  unfold QInterval.ContainsInterval
  constructor
  · exact Rat.le_trans hl.1 (by native_decide)
  · exact Rat.le_trans (by native_decide) hr.2

theorem exactQuintic_compute_contains_one_sixth_stage20 :
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 5) 5 20).ContainsInterval
      { lo := 1 / 6, hi := 1 / 6 } := by
  unfold QInterval.ContainsInterval
  native_decide

end Integral
end ComputableAnalysis
