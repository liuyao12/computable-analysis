import ComputableAnalysis.HolomorphicJet
import ComputableAnalysis.Series

/-!
# The finite Cauchy kernel expansion on a Euclidean disk

Only rational complex arithmetic is used. `InDisk z r` uses squared Euclidean
modulus, so the radius is not silently reduced to an inscribed coordinate
diamond. The expansion is finite; its error estimate is the input needed by
a certified Cauchy integral formula, not a replacement for that formula.
-/

namespace ComputableAnalysis.CauchyTaylor

open QComplex

def InDisk (z : QComplex) (r : Rat) : Prop := normSq z ≤ r * r

theorem normSq_nonneg (z : QComplex) : 0 ≤ normSq z := by
  exact Rat.add_nonneg (rat_square_nonneg_basic _) (rat_square_nonneg_basic _)

theorem disk_coordinates {z : QComplex} {r : Rat} (hr : 0 ≤ r)
    (hz : InDisk z r) : -r ≤ z.re ∧ z.re ≤ r ∧ -r ≤ z.im ∧ z.im ≤ r := by
  have hre := rat_square_nonneg_basic z.re
  have him := rat_square_nonneg_basic z.im
  unfold InDisk normSq at hz
  constructor
  · by_cases h : -r ≤ z.re
    · exact h
    have hp := Rat.mul_pos (show 0 < -z.re - r by grind)
      (show 0 < -z.re + r by grind); grind
  constructor
  · by_cases h : z.re ≤ r
    · exact h
    have hp := Rat.mul_pos (show 0 < z.re - r by grind)
      (show 0 < z.re + r by grind); grind
  constructor
  · by_cases h : -r ≤ z.im
    · exact h
    have hp := Rat.mul_pos (show 0 < -z.im - r by grind)
      (show 0 < -z.im + r by grind); grind
  · by_cases h : z.im ≤ r
    · exact h
    have hp := Rat.mul_pos (show 0 < z.im - r by grind)
      (show 0 < z.im + r by grind); grind

theorem disk_mul {z w : QComplex} {r s : Rat}
    (hz : InDisk z r) (hw : InDisk w s) : InDisk (mul z w) (r * s) := by
  have h1 := Rat.mul_le_mul_of_nonneg_right hz (normSq_nonneg w)
  have h2 := Rat.mul_le_mul_of_nonneg_left hw (rat_square_nonneg_basic r)
  unfold InDisk at *
  rw [normSq_mul]
  grind

theorem disk_power {z : QComplex} {r : Rat} (hz : InDisk z r) (n : Nat) :
    InDisk (natPow z n) (r ^ n) := by
  induction n with
  | zero => simp [InDisk, natPow, normSq, one, Rat.add_zero]
  | succ n ih => simpa only [natPow, Rat.pow_succ] using disk_mul ih hz

theorem denominator_separated {z : QComplex} {r : Rat}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hz : InDisk z r) :
    (1 - r) * (1 - r) ≤ normSq (sub one z) := by
  have hc := disk_coordinates hr hz
  have hp := Rat.mul_nonneg (show 0 ≤ r - z.re by grind)
    (show 0 ≤ 2 - r - z.re by grind)
  have hi := rat_square_nonneg_basic z.im
  simp only [normSq, sub, one, add, neg]
  grind

theorem denominator_ne_zero {z : QComplex} {r : Rat}
    (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) : normSq (sub one z) ≠ 0 := by
  have h := denominator_separated hr (Rat.le_of_lt hr1) hz
  have hp := Rat.mul_pos (show 0 < 1-r by grind) (show 0 < 1-r by grind)
  grind

def kernel (z : QComplex) : QComplex := inverse (sub one z)

theorem kernel_disk {z : QComplex} {r : Rat}
    (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) :
    InDisk (kernel z) (1-r)⁻¹ := by
  have hs := denominator_separated hr (Rat.le_of_lt hr1) hz
  have hn := denominator_ne_zero hr hr1 hz
  have he := congrArg normSq (mul_inverse_of_normSq_ne_zero (sub one z) hn)
  rw [normSq_mul] at he
  have hi := Rat.mul_inv_cancel (1-r) (show 1-r ≠ 0 by grind)
  have hp := Rat.mul_pos (show 0 < 1-r by grind) (show 0 < 1-r by grind)
  have hm := Rat.mul_le_mul_of_nonneg_right hs (normSq_nonneg (kernel z))
  apply Rat.le_of_mul_le_mul_right (c := (1-r)*(1-r)) ?_ hp
  change normSq (kernel z) * ((1-r)*(1-r)) ≤ ((1-r)⁻¹*(1-r)⁻¹)*((1-r)*(1-r))
  have he' : normSq (sub one z) * normSq (kernel z) = 1 := by
    simpa only [kernel, normSq, one, Rat.one_mul, Rat.zero_mul, Rat.add_zero] using he
  have hi2 : ((1-r)⁻¹*(1-r)⁻¹)*((1-r)*(1-r)) = 1 := by
    calc
      _ = ((1-r)*(1-r)⁻¹)*((1-r)*(1-r)⁻¹) := by grind only
      _ = 1 := by rw [hi, Rat.one_mul]
  rw [hi2]
  grind only

/-- `N` terms, with the empty sum at `N = 0`. -/
def geometric (z : QComplex) : Nat → QComplex
  | 0 => zero
  | n+1 => add one (mul z (geometric z n))

theorem kernel_unfold (z : QComplex) (hz : normSq (sub one z) ≠ 0) :
    kernel z = add one (mul z (kernel z)) := by
  have h := mul_inverse_of_normSq_ne_zero (sub one z) hz
  change mul (sub one z) (kernel z) = one at h
  apply QComplex.le_antisymm <;>
    simp only [QComplex.le_def, add, one, mul] <;>
    simp only [sub, add, neg, one, mul, QComplex.mk.injEq] at h
  all_goals constructor <;> grind

/-- Exact finite geometric identity; no convergence premise. -/
theorem kernel_remainder (z : QComplex) (hz : normSq (sub one z) ≠ 0) (N : Nat) :
    sub (kernel z) (geometric z N) = mul (natPow z N) (kernel z) := by
  induction N with
  | zero =>
      simp only [geometric, natPow, one_mul_cert, sub, add, neg, zero]
      cases kernel z
      simp [Rat.add_zero]
  | succ N ih =>
      have hk := kernel_unfold z hz
      rw [geometric, natPow]
      simp only [sub, add, neg, mul, one, QComplex.mk.injEq] at ih hk ⊢
      constructor <;> grind

/-- Euclidean disk bound for the actual kernel remainder. -/
theorem kernel_remainder_disk {z : QComplex} {r : Rat}
    (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) (N : Nat) :
    InDisk (sub (kernel z) (geometric z N)) (r ^ N * (1-r)⁻¹) := by
  rw [kernel_remainder z (denominator_ne_zero hr hr1 hz)]
  exact disk_mul (disk_power hz N) (kernel_disk hr hr1 hz)

theorem kernel_remainder_coordinates {z : QComplex} {r : Rat}
    (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) (N : Nat) :
    let error := sub (kernel z) (geometric z N);
    let bound := r ^ N * (1-r)⁻¹;
    -bound ≤ error.re ∧ error.re ≤ bound ∧ -bound ≤ error.im ∧ error.im ≤ bound := by
  exact disk_coordinates
    (Rat.mul_nonneg (Rat.pow_nonneg hr)
      (Rat.le_of_lt ((Rat.inv_pos).2 (by grind))))
    (kernel_remainder_disk hr hr1 hz N)

/-- A rate valid for every rational ratio below one, not only `r ≤ 1/2`. -/
theorem power_budget {r : Rat} (hr : 0 ≤ r) (_hr1 : r < 1) (n : Nat) :
    (1 + (n : Rat) * (1-r)) * r ^ n ≤ 1 := by
  induction n with
  | zero => simp [Rat.pow_zero, Rat.zero_mul, Rat.add_zero, Rat.mul_one]
  | succ n ih =>
      have hn : 0 ≤ (n : Rat) := Rat.natCast_nonneg
      have hd : 0 ≤ (1-r)*(1-r) := rat_square_nonneg_basic _
      have hnd := Rat.mul_nonneg (show 0 ≤ (n : Rat)+1 by grind) hd
      have ha : (1 + ((n : Rat)+1)*(1-r))*r ≤ 1+(n : Rat)*(1-r) := by grind
      have hm := Rat.mul_le_mul_of_nonneg_right ha (Rat.pow_nonneg hr (n := n))
      simp only [Rat.pow_succ, Rat.natCast_add] at *
      grind only

theorem power_nat_bound {r : Rat} (hr : 0 ≤ r) (hr1 : r < 1) (n : Nat) :
    r ^ n ≤ (1-r)⁻¹ / ((n+1 : Nat) : Rat) := by
  have hp := power_budget hr hr1 n
  have hn : (0 : Rat) < ((n+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
  have hd : 0 < 1-r := by grind
  have hb : (((n+1 : Nat) : Rat)*(1-r)) * r^n ≤ 1 := by
    have h := Rat.mul_nonneg (show 0 ≤ r by grind) (Rat.pow_nonneg hr (n := n))
    simp only [Rat.natCast_add] at *
    grind only
  have hi := Rat.mul_inv_cancel (1-r) (Rat.ne_of_gt hd)
  have hj := Rat.mul_inv_cancel (((n+1 : Nat) : Rat)) (Rat.ne_of_gt hn)
  apply Rat.le_of_mul_le_mul_right (c := (1-r)*((n+1 : Nat) : Rat)) ?_
    (Rat.mul_pos hd hn)
  have he : ((1-r)⁻¹ / ((n+1 : Nat) : Rat))*((1-r)*((n+1 : Nat) : Rat)) = 1 := by
    rw [Rat.div_def]
    calc
      _ = ((1-r)*(1-r)⁻¹)*(((n+1 : Nat) : Rat)*(((n+1 : Nat) : Rat))⁻¹) := by grind only
      _ = 1 := by rw [hi, hj, Rat.one_mul]
  rw [he]
  grind only

theorem power_antitone {r : Rat} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {n m : Nat} (hnm : n ≤ m) : r^m ≤ r^n := by
  induction hnm with
  | refl => exact Rat.le_refl
  | @step m hnm ih =>
      have h := Rat.mul_le_mul_of_nonneg_left hr1 (Rat.pow_nonneg hr (n := m))
      rw [Rat.pow_succ]
      have hm : r^m*r ≤ r^m := by simpa only [Rat.mul_one] using h
      exact Rat.le_trans hm ih

end ComputableAnalysis.CauchyTaylor
