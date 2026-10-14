import ComputableAnalysis.RiemannHilbert.ExponentialMajorant

/-! Executable integer exponents convert a fixed factor per radial step
into polynomial puncture growth. All estimates use finite rational powers;
neither logarithms of bounds nor a completed real norm are needed. -/
namespace ComputableAnalysis.RiemannHilbert.RadialGrowthArithmetic
open ComplexRaw FunctionTheory LocalODE
set_option autoImplicit false
set_option maxHeartbeats 1000000

def ratio : Rat := 63/64
def inverseRatio : Rat := 64/63
theorem ratio_positive : 0 < ratio := by decide +kernel
theorem inverseRatio_positive : 0 < inverseRatio := by decide +kernel
theorem ratio_inverse : ratio*inverseRatio=1 := by decide +kernel

theorem power_product (a b : Rat) (k : Nat) : (a*b)^k=a^k*b^k := by
  induction k with
  | zero => simp only [Rat.pow_zero,Rat.one_mul]
  | succ k ih => rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_succ,ih]; grind only

theorem power_add (a : Rat) (j k : Nat) : a^(j+k)=a^j*a^k := by
  induction k with
  | zero => simp only [Nat.add_zero,Rat.pow_zero,Rat.mul_one]
  | succ k ih => rw [Nat.add_succ,Rat.pow_succ,Rat.pow_succ,ih]; grind only

theorem power_multiple (a : Rat) (j k : Nat) : a^(j*k)=(a^j)^k := by
  induction k with
  | zero => simp only [Nat.mul_zero,Rat.pow_zero]
  | succ k ih => rw [Nat.mul_succ,power_add,ih,Rat.pow_succ]

theorem power_commute (a : Rat) (j k : Nat) : (a^j)^k=(a^k)^j := by
  rw [← power_multiple,← power_multiple,Nat.mul_comm]

theorem power_mono (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) (k : Nat) : a^k ≤ b^k := by
  induction k with
  | zero => rw [Rat.pow_zero,Rat.pow_zero]; exact Rat.le_refl
  | succ k ih =>
      rw [Rat.pow_succ,Rat.pow_succ]
      exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ha)
        (Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (Rat.le_trans ha hab)))

theorem inverse_power_cancel (k : Nat) : ratio^k*inverseRatio^k=1 := by
  rw [← power_product,ratio_inverse]
  induction k with
  | zero => rfl
  | succ k ih => rw [Rat.pow_succ,ih,Rat.one_mul]

theorem inverse_power (k : Nat) : (ratio^k)⁻¹=inverseRatio^k := by
  have h1 := inverse_power_cancel k
  have h2 := Rat.mul_inv_cancel (ratio^k) (Rat.ne_of_gt (Rat.pow_pos ratio_positive))
  grind only

theorem bernoulli (k : Nat) : 1+(k : Rat)/63 ≤ inverseRatio^k := by
  induction k with
  | zero => change 1+0/63 ≤ inverseRatio^0; rw [Rat.pow_zero]; decide +kernel
  | succ k ih =>
      have hm := Rat.mul_le_mul_of_nonneg_right ih (Rat.le_of_lt inverseRatio_positive)
      rw [Rat.pow_succ]
      have hn : 0 ≤ (k : Rat) := Rat.natCast_nonneg
      have hstep : 1+((k+1 : Nat) : Rat)/63 ≤ (1+(k : Rat)/63)*inverseRatio := by
        rw [Rat.natCast_add]
        dsimp [inverseRatio]
        grind only
      exact Rat.le_trans hstep hm

def ceiling (P : Rat) : Nat := P.ceil.natAbs+1
theorem ceiling_bound (P : Rat) : P ≤ (ceiling P : Rat) := by
  have hi : P.ceil ≤ (P.ceil.natAbs : Int)+1 := by have h := Int.le_natAbs (a := P.ceil); omega
  have hc : (P.ceil : Rat) ≤ (ceiling P : Rat) := by exact_mod_cast hi
  exact Rat.le_trans Rat.le_ceil hc

def degree (P : Rat) : Nat := 63*ceiling (P+1)

theorem degree_bound (P : Rat) : P ≤ inverseRatio^(degree P) := by
  have hc := ceiling_bound (P+1)
  have hb := bernoulli (degree P)
  have he : ((degree P : Nat) : Rat)=63*(ceiling (P+1) : Rat) := by
    simp only [degree,Rat.natCast_mul]
    rfl
  rw [he] at hb
  grind only

theorem growth_power (P : Rat) (hP : 0 ≤ P) (k : Nat) : P^k ≤ ((ratio^k)⁻¹)^(degree P) := by
  have hb := power_mono P (inverseRatio^(degree P)) hP (degree_bound P) k
  rw [inverse_power,power_commute inverseRatio k (degree P)]
  exact hb

theorem inverse_scale_comparison (k : Nat) (r : Rat) (hr : 0 < r) (hscale : r ≤ (33/32)*ratio^k) :
    (ratio^k)⁻¹ ≤ (33/32)/r := by
  have hm := Rat.mul_le_mul_of_nonneg_right hscale (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.pow_pos (n := k) ratio_positive)))
  have hi := Rat.mul_inv_cancel (ratio^k) (Rat.ne_of_gt (Rat.pow_pos ratio_positive))
  have hs := Rat.mul_le_mul_of_nonneg_left hm (Rat.le_of_lt ((Rat.inv_pos).2 hr))
  have hrI := Rat.inv_mul_cancel r (Rat.ne_of_gt hr)
  have hl : r⁻¹*(r*(ratio^k)⁻¹)=(ratio^k)⁻¹ := by rw [← Rat.mul_assoc,hrI,Rat.one_mul]
  have hright : r⁻¹*((33/32)*ratio^k*(ratio^k)⁻¹)=(33/32)/r := by
    rw [Rat.mul_assoc (33/32) (ratio^k) ((ratio^k)⁻¹),hi,Rat.mul_one,Rat.div_def]
    exact Rat.mul_comm _ _
  rw [hl,hright] at hs
  exact hs

theorem physical_growth (P : Rat) (hP : 0 ≤ P) (k : Nat) (r : Rat) (hr : 0 < r)
    (hscale : r ≤ (33/32)*ratio^k) : P^k ≤ ((33/32)/r)^(degree P) :=
  Rat.le_trans (growth_power P hP k)
    (power_mono ((ratio^k)⁻¹) ((33/32)/r)
      (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.pow_pos ratio_positive))) (inverse_scale_comparison k r hr hscale) (degree P))

theorem scaleOverSucc (k : Nat) : ratio^k ≤ 64/((k+1 : Nat) : Rat) := by
  have hb := bernoulli k
  have hm := Rat.mul_le_mul_of_nonneg_left hb (Rat.pow_nonneg (n := k) (Rat.le_of_lt ratio_positive))
  rw [inverse_power_cancel] at hm
  have hn : 0 ≤ (k : Rat) := Rat.natCast_nonneg
  have ht : ((k+1 : Nat) : Rat)/64 ≤ 1+(k : Rat)/63 := by rw [Rat.natCast_add]; grind only
  have hs := Rat.mul_le_mul_of_nonneg_left ht (Rat.pow_nonneg (n := k) (Rat.le_of_lt ratio_positive))
  apply Rat.le_of_mul_le_mul_right (c := ((k+1 : Nat) : Rat)) ?_ ((Rat.natCast_pos).2 (Nat.succ_pos k))
  rw [Rat.div_mul_cancel (Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos k)))]
  grind only

theorem scales_shrink : ShrinksToZero (fun k => ratio^k) :=
  shrinksToZero_of_natOverSuccBound (C := 64) scaleOverSucc

end ComputableAnalysis.RiemannHilbert.RadialGrowthArithmetic
