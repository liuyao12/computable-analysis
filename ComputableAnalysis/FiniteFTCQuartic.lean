import ComputableAnalysis.FiniteFTCIntervalRegular
import ComputableAnalysis.Series

/-!
# A finite quartic FTC certificate

This file records an executable rational certificate for the integral of
`x ^ 4` on `[0, 1]`.  The interval modulus, endpoint sums, and enclosure are
all finite rational data; no completeness or general Cauchy construction is
used here.
-/

namespace ComputableAnalysis

namespace Integral

def exactQuarticInterval (I : QInterval) : QInterval :=
  { lo := I.lo ^ 4, hi := I.hi ^ 4 }

private theorem four_width_le_one_div_succ_of_width_le
    {w : Rat} (n : Nat)
    (hw : w <= 1 / ((4 * (n + 1) : Nat) : Rat)) :
    4 * w <= 1 / ((n + 1 : Nat) : Rat) := by
  calc
    4 * w <= 4 * (1 / ((4 * (n + 1) : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hw (by native_decide)
    _ = 1 / ((n + 1 : Nat) : Rat) := by
      rw [Rat.div_def]
      have hnrat : ((n + 1 : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
      rw [show ((4 * (n + 1) : Nat) : Rat) =
        (4 : Rat) * ((n + 1 : Nat) : Rat) by
          exact_mod_cast (by omega : 4 * (n + 1) = 4 * (n + 1))]
      rw [Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

def exactRat_quartic_intervalRegularOn_unit :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1) where
  evalInterval := fun I _hI _n => exactQuarticInterval I
  inputPrecision := fun n => 4 * (n + 1)
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    unfold subintervalOf at hI
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hlo_nonneg : 0 <= I.lo := by
      have h := hI.1
      change (0 : Rat) <= I.lo at h
      exact h
    have hhi_le_one : I.hi <= 1 := by
      have h := hI.2.2
      change I.hi <= (1 : Rat) at h
      exact h
    have hwidth : (exactQuarticInterval I).width =
        I.width * (I.hi ^ 3 + I.hi ^ 2 * I.lo +
          I.hi * I.lo ^ 2 + I.lo ^ 3) := by
      unfold exactQuarticInterval QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul]
    rw [hwidth]
    constructor
    · have hsum_nonneg : 0 <= I.hi ^ 3 + I.hi ^ 2 * I.lo +
          I.hi * I.lo ^ 2 + I.lo ^ 3 := by
        exact Rat.add_nonneg (Rat.add_nonneg
          (Rat.add_nonneg (Rat.pow_nonneg (by grind))
            (Rat.mul_nonneg (Rat.pow_nonneg (by grind)) hlo_nonneg))
          (Rat.mul_nonneg (by grind) (Rat.pow_nonneg hlo_nonneg)))
          (Rat.pow_nonneg hlo_nonneg)
      exact Rat.mul_nonneg hwidth_nonneg hsum_nonneg
    · have hhi_nonneg : 0 <= I.hi := by grind
      have hhi2 : I.hi ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left hhi_le_one hhi_nonneg
        calc
          I.hi ^ 2 = I.hi * I.hi := by grind [Rat.pow_succ, Rat.mul_assoc]
          _ <= I.hi * 1 := h
          _ = I.hi := by simp
          _ <= 1 := hhi_le_one
      have hhi3 : I.hi ^ 3 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left hhi2 hhi_nonneg
        calc
          I.hi ^ 3 = I.hi * I.hi ^ 2 := by grind [Rat.pow_succ, Rat.mul_assoc]
          _ <= I.hi * 1 := h
          _ = I.hi := by simp
          _ <= 1 := hhi_le_one
      have hlo_le_one : I.lo <= 1 := by grind
      have hlo2 : I.lo ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left hlo_le_one hlo_nonneg
        calc
          I.lo ^ 2 = I.lo * I.lo := by grind [Rat.pow_succ, Rat.mul_assoc]
          _ <= I.lo * 1 := h
          _ = I.lo := by simp
          _ <= 1 := hlo_le_one
      have hlo3 : I.lo ^ 3 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left hlo2 hlo_nonneg
        calc
          I.lo ^ 3 = I.lo * I.lo ^ 2 := by grind [Rat.pow_succ, Rat.mul_assoc]
          _ <= I.lo * 1 := h
          _ = I.lo := by simp
          _ <= 1 := hlo_le_one
      have hterm2 : I.hi ^ 2 * I.lo <= 1 := by
        exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hhi2 hlo_nonneg)
          (by grind)
      have hterm3 : I.hi * I.lo ^ 2 <= 1 := by
        exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hlo2 hhi_nonneg)
          (by grind)
      have hsum_le_four : I.hi ^ 3 + I.hi ^ 2 * I.lo +
          I.hi * I.lo ^ 2 + I.lo ^ 3 <= 4 := by grind
      have hprod := Rat.mul_le_mul_of_nonneg_left hsum_le_four hwidth_nonneg
      calc
        I.width * (I.hi ^ 3 + I.hi ^ 2 * I.lo +
            I.hi * I.lo ^ 2 + I.lo ^ 3) <= I.width * 4 := hprod
        _ = 4 * I.width := by rw [Rat.mul_comm]
        _ <= 1 / ((n + 1 : Nat) : Rat) :=
          four_width_le_one_div_succ_of_width_le n hsmall
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    unfold subintervalOf at hI
    unfold exactQuarticInterval QInterval.ContainsInterval
    change I.lo ^ 4 <= x ^ 4 ∧ x ^ 4 <= I.hi ^ 4
    have hx' : 0 <= x ∧ x <= 1 := by
      simpa [FunctionOnInterval.exactRat, inDomainInterval] using hx
    have hx_nonneg : 0 <= x := hx'.1
    have hlo_nonneg : 0 <= I.lo := by
      have h := hI.1
      change (0 : Rat) <= I.lo at h
      exact h
    have hhi_nonneg : 0 <= I.hi := by grind
    have hsum_lo : 0 <= x ^ 3 + x ^ 2 * I.lo +
        x * I.lo ^ 2 + I.lo ^ 3 := by
      exact Rat.add_nonneg (Rat.add_nonneg
        (Rat.add_nonneg (Rat.pow_nonneg hx_nonneg)
          (Rat.mul_nonneg (Rat.pow_nonneg hx_nonneg) hlo_nonneg))
        (Rat.mul_nonneg hx_nonneg (Rat.pow_nonneg hlo_nonneg)))
        (Rat.pow_nonneg hlo_nonneg)
    have hsum_hi : 0 <= I.hi ^ 3 + I.hi ^ 2 * x +
        I.hi * x ^ 2 + x ^ 3 := by
      exact Rat.add_nonneg (Rat.add_nonneg
        (Rat.add_nonneg (Rat.pow_nonneg hhi_nonneg)
          (Rat.mul_nonneg (Rat.pow_nonneg hhi_nonneg) hx_nonneg))
        (Rat.mul_nonneg hhi_nonneg (Rat.pow_nonneg hx_nonneg)))
        (Rat.pow_nonneg hx_nonneg)
    have hlow : 0 <= (x - I.lo) * (x ^ 3 + x ^ 2 * I.lo +
        x * I.lo ^ 2 + I.lo ^ 3) := by
      exact Rat.mul_nonneg (by grind) hsum_lo
    have hhigh : 0 <= (I.hi - x) * (I.hi ^ 3 + I.hi ^ 2 * x +
        I.hi * x ^ 2 + x ^ 3) := by
      exact Rat.mul_nonneg (by grind) hsum_hi
    constructor <;> grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]

def exactRat_quartic_lipschitz_on_unit :
    Integral.LipschitzOnUnit (fun x : Rat => x ^ 4) 4 := by
  constructor
  · native_decide
  · intro s t hs hs1 ht ht1
    have hsum_nonneg : 0 <= s ^ 3 + s ^ 2 * t + s * t ^ 2 + t ^ 3 := by
      exact Rat.add_nonneg (Rat.add_nonneg
        (Rat.add_nonneg (Rat.pow_nonneg hs) (Rat.mul_nonneg (Rat.pow_nonneg hs) ht))
        (Rat.mul_nonneg hs (Rat.pow_nonneg ht))) (Rat.pow_nonneg ht)
    have hsum_le_four : s ^ 3 + s ^ 2 * t + s * t ^ 2 + t ^ 3 <= 4 := by
      have hs0 : 0 <= s := by grind
      have ht0 : 0 <= t := by grind
      have hs2 : s ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left hs1 hs0
        calc
          s ^ 2 = s * s := by grind [Rat.pow_succ, Rat.mul_assoc]
          _ <= s * 1 := h
          _ = s := by simp
          _ <= 1 := hs1
      have ht2 : t ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left ht1 ht0
        calc
          t ^ 2 = t * t := by grind [Rat.pow_succ, Rat.mul_assoc]
          _ <= t * 1 := h
          _ = t := by simp
          _ <= 1 := ht1
      have hs3 : s ^ 3 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left hs2 hs0
        calc
          s ^ 3 = s * s ^ 2 := by grind [Rat.pow_succ, Rat.mul_assoc]
          _ <= s * 1 := h
          _ = s := by simp
          _ <= 1 := hs1
      have ht3 : t ^ 3 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left ht2 ht0
        calc
          t ^ 3 = t * t ^ 2 := by grind [Rat.pow_succ, Rat.mul_assoc]
          _ <= t * 1 := h
          _ = t := by simp
          _ <= 1 := ht1
      have hst2 : s ^ 2 * t <= 1 := by
        exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hs2 ht0) (by grind)
      have hst3 : s * t ^ 2 <= 1 := by
        exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left ht2 hs0) (by grind)
      grind
    have hfactor : s ^ 4 - t ^ 4 = (s - t) *
        (s ^ 3 + s ^ 2 * t + s * t ^ 2 + t ^ 3) := by
      grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul]
    rw [hfactor, qabs_mul]
    calc
      qabs (s - t) * qabs (s ^ 3 + s ^ 2 * t + s * t ^ 2 + t ^ 3) <=
          qabs (s - t) * 4 :=
        Rat.mul_le_mul_of_nonneg_left
          (by simpa [qabs_eq_self_of_nonneg hsum_nonneg] using hsum_le_four)
          (qabs_nonneg _)
      _ = 4 * qabs (t - s) := by
        rw [show qabs (s - t) = qabs (t - s) by
          rw [show s - t = -(t - s) by grind [Rat.sub_eq_add_neg], qabs_neg]]
        grind [Rat.mul_comm]

def exactRat_quartic_integral_certificate :
    Integral.IntervalRegularIntegralCertificate
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1) where
  regular := exactRat_quartic_intervalRegularOn_unit
  construction :=
    IntegralIdentities.LipschitzDyadic.construction (fun x : Rat => x ^ 4) 4
      exactRat_quartic_lipschitz_on_unit

theorem exactRat_quartic_integral_raw_valid :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1)
      exactRat_quartic_integral_certificate).Valid := by
  exact Integral.raw_valid _ exactRat_quartic_integral_certificate

theorem exactQuartic_uniformLeftSum_eq
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ 4) n =
      Series.fourthPowerSum n / (n : Rat) ^ 5 := by
  have hnrat : (n : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) => total + (1 / (n : Rat)) *
            (((j : Rat) / (n : Rat)) ^ 4)) 0 =
        Series.fourthPowerSum k / (n : Rat) ^ 5 := by
    intro k
    induction k with
    | zero => simp [Series.fourthPowerSum, Rat.div_def]
    | succ k ih =>
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih, Series.fourthPowerSum_succ]
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
          Rat.add_mul, Rat.pow_succ, Rat.mul_inv_cancel]
  unfold IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
  exact haux n

theorem exactQuartic_uniformRightSum_eq
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ 4) n =
      Series.fourthPowerSum (n + 1) / (n : Rat) ^ 5 := by
  have hnrat : (n : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) => total + (1 / (n : Rat)) *
            ((((j + 1 : Nat) : Rat) / (n : Rat)) ^ 4)) 0 =
        Series.fourthPowerSum (k + 1) / (n : Rat) ^ 5 := by
    intro k
    induction k with
    | zero => simp [Series.fourthPowerSum, Rat.div_def]; grind
    | succ k ih =>
        simp at ih ⊢
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih]
        have hterm :
            (1 / (n : Rat)) * ((((k : Rat) + 1) / (n : Rat)) ^ 4) =
              ((k : Rat) + 1) ^ 4 / (n : Rat) ^ 5 := by
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel]
        change Series.fourthPowerSum (k + 1) / (n : Rat) ^ 5 +
          (1 / (n : Rat)) * (((k : Rat) + 1) / (n : Rat)) ^ 4 =
          Series.fourthPowerSum (k + 1 + 1) / (n : Rat) ^ 5
        rw [hterm]
        have hs : Series.fourthPowerSum (k + 1 + 1) =
            Series.fourthPowerSum (k + 1) + ((k + 1 : Nat) : Rat) ^ 4 := by
          rw [show k + 1 + 1 = (k + 1) + 1 by omega,
            Series.fourthPowerSum_succ]
        rw [hs]
        have hfrac (a b : Rat) :
            a / (n : Rat) ^ 5 + b / (n : Rat) ^ 5 =
              (a + b) / (n : Rat) ^ 5 := by
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
            Rat.pow_succ, Rat.mul_inv_cancel]
        simpa [Rat.natCast_add] using hfrac _ _
  unfold IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
  exact haux n

theorem exactQuartic_uniformLeftSum_le_one_fifth
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ 4) n <= 1 / 5 := by
  rw [exactQuartic_uniformLeftSum_eq hn, Series.fourthPowerSum_eq]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < (n : Rat) ^ 5 := Rat.pow_pos hnrat
  have hn1 : 1 <= (n : Rat) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) ^ 5)
  · rw [Rat.div_def, Rat.div_def]
    have hn1 : 1 <= (n : Rat) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
    have hpoly : (n : Rat) * ((n : Rat) - 1) *
        (2 * (n : Rat) - 1) * (3 * (n : Rat) ^ 2 - 3 * (n : Rat) - 1) <=
        6 * (n : Rat) ^ 5 := by
      have hcore : 0 <= 15 * (n : Rat) ^ 3 - 10 * (n : Rat) ^ 2 + 1 := by
        have hthree : 0 <= 3 * (n : Rat) - 2 := by grind
        have hterm : 0 <= 5 * (n : Rat) ^ 2 * (3 * (n : Rat) - 2) := by
          exact Rat.mul_nonneg
            (Rat.mul_nonneg (by native_decide) (Rat.pow_nonneg (by grind))) hthree
        grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_add, Rat.add_mul]
      have hdiff : 0 <= 6 * (n : Rat) ^ 5 -
          (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
            (3 * (n : Rat) ^ 2 - 3 * (n : Rat) - 1) := by
        have hfactor : 6 * (n : Rat) ^ 5 -
            (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
              (3 * (n : Rat) ^ 2 - 3 * (n : Rat) - 1) =
            (n : Rat) * (15 * (n : Rat) ^ 3 - 10 * (n : Rat) ^ 2 + 1) := by
          grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_add, Rat.add_mul,
            Rat.sub_eq_add_neg]
        rw [hfactor]
        exact Rat.mul_nonneg (Rat.le_of_lt hnrat) hcore
      grind
    have hscaled := Rat.mul_le_mul_of_nonneg_right hpoly
      (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 30)))
    have hcancel : ((n : Rat) ^ 5)⁻¹ * (n : Rat) ^ 5 = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
    calc
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
          (3 * (n : Rat) ^ 2 - 3 * (n : Rat) - 1) * 30⁻¹ *
          ((n : Rat) ^ 5)⁻¹ * (n : Rat) ^ 5 =
        (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
          (3 * (n : Rat) ^ 2 - 3 * (n : Rat) - 1) * 30⁻¹ := by
            grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= 6 * (n : Rat) ^ 5 * 30⁻¹ := hscaled
      _ = (1 / 5) * (n : Rat) ^ 5 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hden

theorem exactQuartic_uniformRightSum_ge_one_fifth
    {n : Nat} (hn : 0 < n) :
    1 / 5 <= IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ 4) n := by
  rw [exactQuartic_uniformRightSum_eq hn, Series.fourthPowerSum_eq]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < (n : Rat) ^ 5 := Rat.pow_pos hnrat
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) ^ 5)
  · rw [Rat.div_def, Rat.div_def]
    have hnp1 : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
      simp [Rat.natCast_add]
    rw [hnp1]
    have hminus : (n : Rat) + 1 - 1 = (n : Rat) := by grind
    rw [hminus]
    have hn1 : 1 <= (n : Rat) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
    have hpoly : 6 * (n : Rat) ^ 5 <=
        ((n : Rat) + 1) * (n : Rat) * (2 * ((n : Rat) + 1) - 1) *
          (3 * ((n : Rat) + 1) ^ 2 - 3 * ((n : Rat) + 1) - 1) := by
      have hcore : 0 <= 15 * (n : Rat) ^ 3 + 10 * (n : Rat) ^ 2 - 1 := by
        have hn2 : 1 <= (n : Rat) ^ 2 := by
          have h := Rat.mul_le_mul_of_nonneg_right hn1
            (by grind : (0 : Rat) <= n)
          have hleft : (1 : Rat) * 1 <= 1 * (n : Rat) :=
            Rat.mul_le_mul_of_nonneg_left hn1 (by native_decide)
          calc
            1 = (1 : Rat) * 1 := by native_decide
            _ <= 1 * (n : Rat) := hleft
            _ <= (n : Rat) * (n : Rat) := h
            _ = (n : Rat) ^ 2 := by grind [Rat.pow_succ, Rat.mul_assoc]
        have hn3 : 1 <= (n : Rat) ^ 3 := by
          have h := Rat.mul_le_mul_of_nonneg_right hn2
            (by grind : (0 : Rat) <= n)
          calc
            1 = (1 : Rat) * 1 := by native_decide
            _ <= 1 * (n : Rat) := by simpa using hn1
            _ <= (n : Rat) ^ 2 * (n : Rat) := h
            _ = (n : Rat) * (n : Rat) ^ 2 := by rw [Rat.mul_comm]
            _ = (n : Rat) ^ 3 := by grind [Rat.pow_succ, Rat.mul_assoc]
        have hterm : 0 <= 15 * (n : Rat) ^ 3 - 1 := by grind
        have hnon : 0 <= 10 * (n : Rat) ^ 2 :=
          Rat.mul_nonneg (by native_decide) (Rat.pow_nonneg (by grind))
        simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
          using Rat.add_nonneg hterm hnon
      have hdiff : 0 <=
          ((n : Rat) + 1) * (n : Rat) * (2 * ((n : Rat) + 1) - 1) *
            (3 * ((n : Rat) + 1) ^ 2 - 3 * ((n : Rat) + 1) - 1) -
            6 * (n : Rat) ^ 5 := by
        have hfactor :
            ((n : Rat) + 1) * (n : Rat) * (2 * ((n : Rat) + 1) - 1) *
              (3 * ((n : Rat) + 1) ^ 2 - 3 * ((n : Rat) + 1) - 1) -
              6 * (n : Rat) ^ 5 =
            (n : Rat) * (15 * (n : Rat) ^ 3 + 10 * (n : Rat) ^ 2 - 1) := by
          grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_add, Rat.add_mul,
            Rat.sub_eq_add_neg]
        rw [hfactor]
        exact Rat.mul_nonneg (Rat.le_of_lt hnrat) hcore
      grind
    have hscaled := Rat.mul_le_mul_of_nonneg_right hpoly
      (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 30)))
    have hcancel : ((n : Rat) ^ 5)⁻¹ * (n : Rat) ^ 5 = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
    calc
      (1 / 5) * (n : Rat) ^ 5 = 6 * (n : Rat) ^ 5 * 30⁻¹ := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= ((n : Rat) + 1) * (n : Rat) * (2 * ((n : Rat) + 1) - 1) *
          (3 * ((n : Rat) + 1) ^ 2 - 3 * ((n : Rat) + 1) - 1) * 30⁻¹ := hscaled
      _ = ((n : Rat) + 1) * (n : Rat) *
          (2 * ((n : Rat) + 1) - 1) *
          (3 * ((n : Rat) + 1) ^ 2 - 3 * ((n : Rat) + 1) - 1) * 30⁻¹ *
          ((n : Rat) ^ 5)⁻¹ * (n : Rat) ^ 5 := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hden

theorem exactQuartic_compute_contains_one_fifth (stage : Nat) :
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 4) 4 stage).ContainsInterval
      { lo := 1 / 5, hi := 1 / 5 } := by
  let n : Nat := 2 ^ stage
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.pow_pos (by omega : 0 < 2)
  have hl := IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
    exactRat_quartic_lipschitz_on_unit stage
  have hr := IntegralIdentities.LipschitzDyadic.compute_contains_uniformRightEndpointSum
    exactRat_quartic_lipschitz_on_unit stage
  have hleft := exactQuartic_uniformLeftSum_le_one_fifth hn
  have hright := exactQuartic_uniformRightSum_ge_one_fifth hn
  unfold QInterval.ContainsInterval
  constructor
  · exact Rat.le_trans hl.1 hleft
  · exact Rat.le_trans hright hr.2

theorem exactRat_quartic_integral_raw_equiv_one_fifth :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1)
      exactRat_quartic_integral_certificate).Equiv
      (RealRaw.ofRat (1 / 5)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 4) 4 n)
    { lo := 1 / 5, hi := 1 / 5 }
  unfold QInterval.Overlaps
  exact exactQuartic_compute_contains_one_fifth n

/-! The quartic certificate is also exposed through the domain-aware definite
integral interface, with the rational primitive `x^5 / 5`. -/

def quarticPrimitiveOnUnit : FunctionOnInterval :=
  FunctionOnInterval.exactRat (fun x : Rat => x ^ 5 / 5) 0 1

theorem quarticPrimitiveOnUnit_compute_zero (n : Nat) :
    quarticPrimitiveOnUnit.toRealFunRaw.compute 0 n =
      { lo := (0 : Rat), hi := 0 } := by
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    quarticPrimitiveOnUnit (x := 0)
      (hx := ⟨by native_decide, by native_decide⟩) n]
  change ({ lo := (0 : Rat) ^ 5 / 5, hi := 0 ^ 5 / 5 } : QInterval) = _
  native_decide

theorem quarticPrimitiveOnUnit_compute_one (n : Nat) :
    quarticPrimitiveOnUnit.toRealFunRaw.compute 1 n =
      { lo := (1 / 5 : Rat), hi := 1 / 5 } := by
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    quarticPrimitiveOnUnit (x := 1)
      (hx := ⟨by native_decide, by native_decide⟩) n]
  change ({ lo := (1 : Rat) ^ 5 / 5, hi := 1 ^ 5 / 5 } : QInterval) = _
  native_decide

theorem quarticPrimitiveOnUnit_endpoint_compute (n : Nat) :
    endpointDifferenceCompute quarticPrimitiveOnUnit.toRealFunRaw 0 1 n =
      { lo := (1 / 5 : Rat), hi := 1 / 5 } := by
  simp [endpointDifferenceCompute, endpointDifferenceInterval,
    quarticPrimitiveOnUnit_compute_one, quarticPrimitiveOnUnit_compute_zero]
  native_decide

theorem quarticPrimitiveOnUnit_endpoint_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute quarticPrimitiveOnUnit.toRealFunRaw 0 1) := by
  have hcompute :
      endpointDifferenceCompute quarticPrimitiveOnUnit.toRealFunRaw 0 1 =
        fun _ : Nat => ({ lo := (1 / 5 : Rat), hi := 1 / 5 } : QInterval) := by
    funext n
    exact quarticPrimitiveOnUnit_endpoint_compute n
  rw [hcompute]
  exact RealRaw.ofRat_valid _

theorem exactRat_quartic_integral_raw_equiv_quartic_endpoint :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1)
      exactRat_quartic_integral_certificate).Equiv
      (endpointDifferenceRaw quarticPrimitiveOnUnit.toRealFunRaw 0 1
        quarticPrimitiveOnUnit_endpoint_valid) := by
  have hendpoint :
      (endpointDifferenceRaw quarticPrimitiveOnUnit.toRealFunRaw 0 1
        quarticPrimitiveOnUnit_endpoint_valid).Equiv
        (RealRaw.ofRat (1 / 5)) := by
    apply RealRaw.sameStageOverlap_equiv
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    change QInterval.Overlaps
      (endpointDifferenceCompute quarticPrimitiveOnUnit.toRealFunRaw 0 1 n)
      { lo := (1 / 5 : Rat), hi := 1 / 5 }
    rw [quarticPrimitiveOnUnit_endpoint_compute]
    exact ⟨by native_decide, by native_decide⟩
  have hmid : (RealRaw.ofRat (1 / 5)).Valid := by
    change RealRaw.ValidCompute
      (fun _ : Nat => ({ lo := (1 / 5 : Rat), hi := 1 / 5 } : QInterval))
    exact RealRaw.ofRat_valid _
  have hend :
      (endpointDifferenceRaw quarticPrimitiveOnUnit.toRealFunRaw 0 1
        quarticPrimitiveOnUnit_endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using
      quarticPrimitiveOnUnit_endpoint_valid
  exact RealRaw.equiv_trans
    (Integral.raw_valid _ exactRat_quartic_integral_certificate)
    hmid
    hend
    exactRat_quartic_integral_raw_equiv_one_fifth
    (RealRaw.equiv_symm hendpoint)

def exactRat_quartic_definiteIdentity :
    Integral.DefiniteIdentityFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1)
      quarticPrimitiveOnUnit :=
  Integral.DefiniteIdentityFor.ofConstruction rfl rfl
    exactRat_quartic_integral_certificate.construction
    quarticPrimitiveOnUnit_endpoint_valid (by
      change (Integral.raw
        (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1)
        exactRat_quartic_integral_certificate).Equiv
        (endpointDifferenceRaw quarticPrimitiveOnUnit.toRealFunRaw 0 1
          quarticPrimitiveOnUnit_endpoint_valid)
      exact exactRat_quartic_integral_raw_equiv_quartic_endpoint)


end Integral

end ComputableAnalysis
