import ComputableAnalysis.RiemannHilbert.CoefficientSeries
import ComputableAnalysis.RiemannHilbert.LocalSeriesHolomorphic

/-! Executable values and derivative candidates for supplied complex series. -/
namespace ComputableAnalysis.RiemannHilbert.BoundedSeries
open ComplexRaw FunctionTheory LocalODE

def valueBlock (c : Nat → ComplexRaw) (z : ComplexRaw) (N : Nat) : Nat → ComplexRaw
  | 0 => zero
  | k+1 => add (valueBlock c z N k) (mul (c (N+k)) (power z (N+k)))

theorem valueBlock_valid (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (N k : Nat) : (valueBlock c z N k).Valid := by
  induction k with
  | zero => exact ofQComplex_valid _
  | succ k ih => exact add_valid ih (mul_valid (hc _) (power_valid z hz _))

theorem valueBlock_as_terms (c : Nat → ComplexRaw) (z : ComplexRaw) (N k : Nat) :
    valueBlock c z N k = ScalarSeries.block (seriesTerm c z) N k := by
  induction k with
  | zero => rfl
  | succ k ih => change add (valueBlock c z N k) _ = add (ScalarSeries.block (seriesTerm c z) N k) _
                 rw [ih]; rfl

def sumValue (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (C K R : Rat) : ComplexRaw :=
  coefficientSum c z hc hz C K R

theorem sumValue_valid (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hzB : Small z R) (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    (sumValue c z hc hz C K R).Valid := coefficientSum_valid c z hc hz C K R hC hK hR hcB hzB hlocal

theorem sumValue_close_prefix (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hzB : Small z R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) (N : Nat) :
    Small (sub (sumValue c z hc hz C K R) (valueBlock c z 0 N)) (valueTail C K R N) := by
  rw [valueBlock_as_terms]
  exact coefficientSum_close c z hc hz C K R hC hK hR hcB hzB hlocal N

def derivativeTerm (c : Nat → ComplexRaw) (z : ComplexRaw) (k : Nat) : ComplexRaw :=
  scaleRat ((k+1 : Nat) : Rat) (mul (c (k+1)) (power z k))

theorem derivativeTerm_valid (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (k : Nat) :
    (derivativeTerm c z k).Valid :=
  scaleRat_valid (mul_valid (hc _) (power_valid z hz _))

private theorem succ_le_two_pow (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      calc
        n+1+1 ≤ 2*(n+1) := by omega
        _ ≤ 2*(2^n) := Nat.mul_le_mul_left 2 ih
        _ = 2^(n+1) := by rw [Nat.pow_succ]; omega

private theorem cast_two_pow (n : Nat) : ((2^n : Nat) : Rat) = (2 : Rat)^n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [Nat.pow_succ, Rat.natCast_mul, Rat.pow_succ, ih]
      rfl

theorem derivativeTerm_majorant (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid)
    (C K R : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hpoint : Small z R) (k : Nat) :
    Small (derivativeTerm c z k) (2*C*K*(4*K*R)^k) := by
  have hq : 0 ≤ 2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have hcoef := hcB (k+1)
  have hp := power_small z hz R hR hpoint k
  have hm := Small.mul (hc (k+1)) (power_valid z hz k)
    (Rat.mul_nonneg hC (Rat.pow_nonneg hK))
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 2) hR)) hcoef hp
  have he : 2*(C*K^(k+1))*(2*R)^k = 2*C*K*(2*K*R)^k := by
    rw [Rat.pow_succ]
    have hp : K^k*(2*R)^k = (2*K*R)^k := by
      rw [← rational_mul_pow]
      congr 1
      grind [Rat.mul_assoc, Rat.mul_comm]
    calc
      _ = (2*C*K)*(K^k*(2*R)^k) := by grind [Rat.mul_assoc, Rat.mul_comm]
      _ = _ := by rw [hp]
  rw [he] at hm
  have hn0 : 0 ≤ ((k+1 : Nat) : Rat) :=
    Rat.le_of_lt ((Rat.natCast_pos).2 (Nat.succ_pos k))
  have hs := small_scale hn0 hm
  apply hs.mono
  have hn : ((k+1 : Nat) : Rat) ≤ (2 : Rat)^k := by
    rw [← cast_two_pow]
    exact_mod_cast succ_le_two_pow k
  have hmain := Rat.mul_le_mul_of_nonneg_right hn (Rat.pow_nonneg (n := k) hq)
  have hconstant : 0 ≤ 2*C*K := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) hK
  have hle := Rat.mul_le_mul_of_nonneg_left hmain hconstant
  have hpow : (2 : Rat)^k*(2*K*R)^k = (4*K*R)^k := by
    rw [← rational_mul_pow]
    congr 1
    grind [Rat.mul_assoc]
  rw [hpow] at hle
  grind [Rat.mul_assoc, Rat.mul_comm]


def derivativeBlock (c : Nat → ComplexRaw) (z : ComplexRaw) (N : Nat) : Nat → ComplexRaw
  | 0 => zero
  | k+1 => add (derivativeBlock c z N k) (derivativeTerm c z (N+k))

theorem derivativeBlock_valid (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (N k : Nat) : (derivativeBlock c z N k).Valid := by
  induction k with
  | zero => exact ofQComplex_valid _
  | succ k ih => exact add_valid ih (derivativeTerm_valid c z hc hz _)

theorem derivativeBlock_as_terms (c : Nat → ComplexRaw) (z : ComplexRaw) (N k : Nat) :
    derivativeBlock c z N k = ScalarSeries.block (derivativeTerm c z) N k := by
  induction k with
  | zero => rfl
  | succ k ih => change add (derivativeBlock c z N k) _ = add (ScalarSeries.block (derivativeTerm c z) N k) _
                 rw [ih]

def sumDerivative (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (C K R : Rat) : ComplexRaw :=
  ScalarSeries.value (derivativeTerm c z) (derivativeTerm_valid c z hc hz) (C*K) (4*K*R)

theorem sumDerivative_valid (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hzB : Small z R) (hlocal : 4*K*R ≤ (1 : Rat)/2) :
    (sumDerivative c z hc hz C K R).Valid := by
  apply ScalarSeries.value_valid _ _ (C*K) (4*K*R) (Rat.mul_nonneg hC hK)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
  intro k
  simpa only [Rat.mul_assoc] using derivativeTerm_majorant c z hc hz C K R hC hK hR hcB hzB k

theorem sumDerivative_close_prefix (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hzB : Small z R)
    (hlocal : 4*K*R ≤ (1 : Rat)/2) (N : Nat) :
    Small (sub (sumDerivative c z hc hz C K R) (derivativeBlock c z 0 N)) (derivativeTail C K R N) := by
  rw [derivativeBlock_as_terms]
  have hs := ScalarSeries.value_close _ (derivativeTerm_valid c z hc hz) (C*K) (4*K*R)
    (Rat.mul_nonneg hC hK) (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
    (fun k => by simpa only [Rat.mul_assoc] using derivativeTerm_majorant c z hc hz C K R hC hK hR hcB hzB k) N
  simpa only [sumDerivative, derivativeTail, Rat.mul_assoc] using hs


theorem sumDerivative_congr (c : Nat → ComplexRaw) (z w : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (hw : w.Valid) (hzw : z.Equiv w)
    (C K R : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hzB : Small z R) (hlocal : 4*K*R ≤ (1 : Rat)/2) :
    (sumDerivative c z hc hz C K R).Equiv (sumDerivative c w hc hw C K R) := by
  have hq : 0 ≤ 4*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have hCK := Rat.mul_nonneg hC hK
  have hwB := Small.congr hz hw hzw hzB
  exact ScalarSeries.value_congr _ _ (derivativeTerm_valid c z hc hz) (derivativeTerm_valid c w hc hw)
    (C*K) (4*K*R) (C*K) (4*K*R) hCK hq hCK hq hlocal hlocal
    (fun k => by simpa only [Rat.mul_assoc] using derivativeTerm_majorant c z hc hz C K R hC hK hR hcB hzB k)
    (fun k => by simpa only [Rat.mul_assoc] using derivativeTerm_majorant c w hc hw C K R hC hK hR hcB hwB k)
    (fun k => scaleRat_equiv (mul_equiv (hc _) (hc _) (power_valid z hz k) (power_valid w hw k)
      (equiv_refl _ (hc _)) (power_congr z w hz hw hzw k)))


theorem sumDerivative_congr_of_bounds (c d : Nat → ComplexRaw) (z w : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hd : ∀ i, (d i).Valid) (hz : z.Valid) (hw : w.Valid)
    (hcd : ∀ i, (c i).Equiv (d i)) (hzw : z.Equiv w) (C K R D L S : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hD : 0 ≤ D) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hdB : ∀ i, Small (d i) (D*L^i))
    (hzB : Small z R) (hwB : Small w S)
    (hq : 4*K*R ≤ (1 : Rat)/2) (hr : 4*L*S ≤ (1 : Rat)/2) :
    (sumDerivative c z hc hz C K R).Equiv (sumDerivative d w hd hw D L S) :=
  ScalarSeries.value_congr _ _ (derivativeTerm_valid c z hc hz) (derivativeTerm_valid d w hd hw)
    (C*K) (4*K*R) (D*L) (4*L*S) (Rat.mul_nonneg hC hK)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) (Rat.mul_nonneg hD hL)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hL) hS) hq hr
    (fun k => by simpa only [Rat.mul_assoc] using derivativeTerm_majorant c z hc hz C K R hC hK hR hcB hzB k)
    (fun k => by simpa only [Rat.mul_assoc] using derivativeTerm_majorant d w hd hw D L S hD hL hS hdB hwB k)
    (fun k => scaleRat_equiv (mul_equiv (hc _) (hd _) (power_valid z hz k) (power_valid w hw k)
      (hcd _) (power_congr z w hz hw hzw k)))

end ComputableAnalysis.RiemannHilbert.BoundedSeries
