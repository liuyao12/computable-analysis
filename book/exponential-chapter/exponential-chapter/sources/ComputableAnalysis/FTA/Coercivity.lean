import ComputableAnalysis.ComplexReciprocalCalculus

/-! Explicit bounds for sublevel sets of monic rational-complex polynomials.
These finite inequalities supply the boundedness needed by the minimum-modulus
argument, uniformly over bounded coefficient samples. -/
namespace ComputableAnalysis.PolynomialCoercivity
open QComplex

def coefficientBound : CPoly.Coeffs → Rat
  | [] => 0
  | a :: p => normBound a + coefficientBound p

theorem coefficientBound_nonneg (p : CPoly.Coeffs) : 0 ≤ coefficientBound p := by
  induction p with
  | nil => exact Rat.le_refl
  | cons a p ih => exact Rat.add_nonneg (normBound_nonneg a) ih

private theorem pow_norm_le_one {w : QComplex} (hw : normBound w ≤ 1) (n : Nat) :
    normBound (pow w n) ≤ 1 := by
  have hn := normBound_pow_le (by decide +kernel : (0 : Rat) ≤ 1) hw n
  have hone : (1 : Rat)^n = 1 := by
    clear hn
    induction n with
    | zero => rw [Rat.pow_zero]
    | succ n ih => rw [Rat.pow_succ, ih, Rat.one_mul]
  rwa [hone] at hn

private theorem pow_succ_norm_le {w : QComplex} (hw : normBound w ≤ 1) (n : Nat) :
    normBound (pow w (n+1)) ≤ normBound w := by
  have h := normBound_mul_le w (pow w n)
  have hm := Rat.mul_le_mul_of_nonneg_left (pow_norm_le_one hw n) (normBound_nonneg w)
  change normBound (mul w (pow w n)) ≤ normBound w
  grind

private theorem normalized_step (a e z w v : QComplex) (hzw : mul z w = one) :
    sub (mul (add a (mul z e)) (mul w v)) one =
      add (mul a (mul w v)) (sub (mul e v) one) := by
  have hm : mul (mul z e) (mul w v) = mul e v := by
    calc
      mul (mul z e) (mul w v) = mul z (mul e (mul w v)) := mul_assoc_cert _ _ _
      _ = mul z (mul w (mul e v)) := by
        rw [← mul_assoc_cert e w v, mul_comm_cert e w, mul_assoc_cert w e v]
      _ = mul (mul z w) (mul e v) := (mul_assoc_cert _ _ _).symm
      _ = mul e v := by rw [hzw, one_mul_cert]
  rw [add_mul_cert, hm]
  exact add_assoc_cert _ _ _

private theorem normalized_error_bound (q : CPoly.Coeffs) (z w : QComplex)
    (hzw : mul z w = one) (hw : normBound w ≤ 1) :
    normBound (sub (mul (CPoly.eval (q ++ [one]) z) (pow w q.length)) one) ≤
      coefficientBound q * normBound w := by
  induction q with
  | nil =>
      simp [CPoly.eval, pow, add, mul, one, zero,
        sub, neg, normBound, coefficientBound, qabs]
      grind
  | cons a q ih =>
      change normBound (sub
        (mul (add a (mul z (CPoly.eval (q ++ [one]) z))) (mul w (pow w q.length))) one) ≤ _
      rw [normalized_step a _ z w _ hzw]
      have ha := normBound_mul_le a (pow w (q.length+1))
      have hp := Rat.mul_le_mul_of_nonneg_left (pow_succ_norm_le hw q.length) (normBound_nonneg a)
      have ht := normBound_add_le (mul a (pow w (q.length+1)))
        (sub (mul (CPoly.eval (q ++ [one]) z) (pow w q.length)) one)
      change normBound (add (mul a (pow w (q.length+1)))
        (sub (mul (CPoly.eval (q ++ [one]) z) (pow w q.length)) one)) ≤
          (normBound a + coefficientBound q) * normBound w
      grind

private theorem one_le_norm_plus_difference (a : QComplex) :
    1 ≤ normBound a + normBound (sub a one) := by
  have h : one = add a (neg (sub a one)) := by
    cases a
    simp [add, neg, sub, one]
    constructor <;> grind
  have hn := normBound_add_le a (neg (sub a one))
  rw [← h, normBound_neg] at hn
  have ho : normBound one = 1 := by decide +kernel
  rwa [ho] at hn

/-- The normalized polynomial stays close to one when the reciprocal input
is small. This proves the key finite inequality used by the root bound. -/
theorem normalized_sublevel_bound (q : CPoly.Coeffs) (hq : 0 < q.length)
    (z w : QComplex) (hzw : mul z w = one) (hw : normBound w ≤ 1)
    (M : Rat) (hM : 0 ≤ M) (heval : normBound (CPoly.eval (q ++ [one]) z) ≤ M) :
    1 ≤ (M + coefficientBound q) * normBound w := by
  have herror := normalized_error_bound q z w hzw hw
  have hpow : normBound (pow w q.length) ≤ normBound w := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    rw [hn]
    exact pow_succ_norm_le hw n
  have hmul := normBound_mul_le (CPoly.eval (q ++ [one]) z) (pow w q.length)
  have h1 := Rat.mul_le_mul_of_nonneg_right heval (normBound_nonneg (pow w q.length))
  have h2 := Rat.mul_le_mul_of_nonneg_left hpow hM
  have hone := one_le_norm_plus_difference (mul (CPoly.eval (q ++ [one]) z) (pow w q.length))
  grind

private theorem qabs_square (a : Rat) : qabs a * qabs a = a*a := by
  by_cases h : 0 ≤ a
  · rw [qabs_eq_self_of_nonneg h]
  · rw [qabs_eq_neg_of_nonpos (by grind)]
    grind

theorem normBound_square_le (z : QComplex) : normBound z * normBound z ≤ 2 * normSq z := by
  have h := rat_square_nonneg_basic (qabs z.re - qabs z.im)
  have hr := qabs_square z.re
  have hi := qabs_square z.im
  unfold normBound normSq
  grind

/-- Explicit coefficient-dependent bound for every monic polynomial sublevel
set. No root, completion, or compactness hypothesis is used. -/
theorem monic_sublevel_bound (q : CPoly.Coeffs) (hq : 0 < q.length)
    (z : QComplex) (M : Rat) (hM : 0 ≤ M)
    (heval : normBound (CPoly.eval (q ++ [one]) z) ≤ M) :
    normBound z ≤ 2 * (M + coefficientBound q + 1) := by
  by_cases h : normBound z ≤ 2 * (M + coefficientBound q + 1)
  · exact h
  have hC := coefficientBound_nonneg q
  have hz : 0 < normBound z := by grind
  have hs := normBound_square_le z
  have hsq := Rat.mul_pos hz hz
  have hnorm : 0 < normSq z := by grind
  have hbig : 2 * (M + coefficientBound q + 1) < normBound z := by grind
  have hb := Rat.mul_lt_mul_of_pos_right hbig hz
  have hmargin : (M + coefficientBound q + 1) * normBound z < normSq z := by grind
  have hi := Rat.inv_pos.mpr hnorm
  have hmul := Rat.mul_lt_mul_of_pos_right hmargin hi
  have hcancel := Rat.mul_inv_cancel (normSq z) (Rat.ne_of_gt hnorm)
  let w := inverse z
  have hw : normBound w = normBound z * (normSq z)⁻¹ := normBound_inverse_eq z hnorm
  have hw0 : 0 ≤ normBound w := normBound_nonneg w
  have hbound : (M + coefficientBound q + 1) * normBound w < 1 := by rw [hw]; grind
  have hmw := Rat.mul_nonneg (show 0 ≤ M + coefficientBound q by grind) hw0
  have hw1 : normBound w ≤ 1 := by grind
  have hone := normalized_sublevel_bound q hq z w
    (mul_inverse_of_normSq_ne_zero z (Rat.ne_of_gt hnorm)) hw1 M hM heval
  grind

theorem normSq_le_normBound_square (z : QComplex) : normSq z ≤ normBound z * normBound z := by
  have hr := qabs_square z.re
  have hi := qabs_square z.im
  have hp := Rat.mul_nonneg (qabs_nonneg z.re) (qabs_nonneg z.im)
  unfold normBound normSq
  grind

theorem normBound_le_normSq_add_one (z : QComplex) : normBound z ≤ normSq z + 1 := by
  have hr := qabs_square z.re
  have hi := qabs_square z.im
  have h1 := rat_square_nonneg_basic (qabs z.re - 1)
  have h2 := rat_square_nonneg_basic (qabs z.im - 1)
  have h3 := rat_square_nonneg_basic z.re
  have h4 := rat_square_nonneg_basic z.im
  unfold normBound normSq
  grind

theorem eval_normBound_on_unit (p : CPoly.Coeffs) (z : QComplex) (hz : normBound z ≤ 1) :
    normBound (CPoly.eval p z) ≤ coefficientBound p := by
  induction p with
  | nil => change normBound zero ≤ 0; decide +kernel
  | cons a p ih =>
      have hmul := normBound_mul_le z (CPoly.eval p z)
      have hb := Rat.mul_le_mul_of_nonneg_right hz (normBound_nonneg (CPoly.eval p z))
      have hsum := normBound_add_le a (mul z (CPoly.eval p z))
      change normBound (add a (mul z (CPoly.eval p z))) ≤ normBound a + coefficientBound p
      grind

theorem coefficientBound_append (p q : CPoly.Coeffs) :
    coefficientBound (p++q) = coefficientBound p + coefficientBound q := by
  induction p with
  | nil => simp [coefficientBound, Rat.zero_add]
  | cons a p ih => simp [coefficientBound, ih, Rat.add_assoc]

end ComputableAnalysis.PolynomialCoercivity
