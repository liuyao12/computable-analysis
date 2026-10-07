import ComputableAnalysis.Polynomial

/-! An explicit finite descent step for the minimum-modulus route to FTA.
A negative first nonconstant coefficient dominates all higher terms at the
computed rational step. This is a local estimate, not root existence. -/
namespace ComputableAnalysis.PolynomialDescent

def tailBound : List Rat → Rat
  | [] => 0
  | c :: cs => qabs c + tailBound cs

theorem tailBound_nonneg (p : List Rat) : 0 ≤ tailBound p := by
  induction p with
  | nil => exact Rat.le_refl
  | cons c cs ih =>
      have hc := qabs_nonneg c
      dsimp [tailBound]
      grind

theorem eval_abs_bound (p : List Rat) {t : Rat} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    qabs (Polynomial.eval p t) ≤ tailBound p := by
  induction p with
  | nil => simp [Polynomial.eval, tailBound, qabs]
  | cons c cs ih =>
      have h := qabs_add_le c (t * Polynomial.eval cs t)
      rw [qabs_mul, qabs_eq_self_of_nonneg ht] at h
      have hmul := Rat.mul_le_mul_of_nonneg_left ih ht
      have hunit := Rat.mul_le_mul_of_nonneg_right ht1 (tailBound_nonneg cs)
      change qabs (c + t * Polynomial.eval cs t) ≤ qabs c + tailBound cs
      grind

/-- A strictly positive rational step below one whenever the leading
nonconstant coefficient is negative. The denominator also controls the tail. -/
def step (b : Rat) (p : List Rat) : Rat := -b / (2 * (tailBound p + 1) - b)

theorem step_spec (b : Rat) (p : List Rat) (hb : b < 0) :
    0 < step b p ∧ step b p < 1 ∧
      b + step b p * Polynomial.eval p (step b p) ≤ b / 2 := by
  let B := tailBound p
  let d := 2 * (B + 1) - b
  have hB : 0 ≤ B := tailBound_nonneg p
  have hd : 0 < d := by dsimp [d]; grind
  have hdne : d ≠ 0 := Rat.ne_of_gt hd
  have hdinv := Rat.inv_pos.mpr hd
  have ht : 0 < step b p := by
    change 0 < -b * d⁻¹
    exact Rat.mul_pos (by grind) hdinv
  have hcancel : step b p * d = -b := by
    change (-b * d⁻¹) * d = -b
    have hc := Rat.mul_inv_cancel d hdne
    grind
  have ht1 : step b p < 1 := by
    have hnum : -b < d := by dsimp [d]; grind
    have hm := Rat.mul_lt_mul_of_pos_right hnum hdinv
    change step b p < 1
    dsimp [step, B, d] at *
    rw [Rat.div_def]
    have hc := Rat.mul_inv_cancel (2 * (tailBound p + 1) - b) hdne
    grind
  have heval : Polynomial.eval p (step b p) ≤ B :=
    Rat.le_trans (self_le_qabs _) (eval_abs_bound p (Rat.le_of_lt ht) (Rat.le_of_lt ht1))
  have he := Rat.mul_le_mul_of_nonneg_left heval (Rat.le_of_lt ht)
  have htail : step b p * (2 * B) ≤ step b p * d :=
    Rat.mul_le_mul_of_nonneg_left (by dsimp [d]; grind) (Rat.le_of_lt ht)
  rw [hcancel] at htail
  refine ⟨ht, ht1, ?_⟩
  have hhalf : b / 2 + b / 2 = b := by
    rw [Rat.div_def]
    have hc : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
    grind
  grind

/-- The computed step strictly decreases a polynomial with a negative first
nonconstant coefficient, at any positive order of vanishing. -/
theorem strict_descent (a b : Rat) (p : List Rat) (k : Nat)
    (hb : b < 0) (_hk : 0 < k) :
    a + (step b p)^k * (b + step b p * Polynomial.eval p (step b p)) < a := by
  have hs := step_spec b p hb
  have hp : 0 < (step b p)^k := by
    clear _hk
    induction k with
    | zero => rw [Rat.pow_zero]; decide +kernel
    | succ k ih => rw [Rat.pow_succ]; exact Rat.mul_pos ih hs.1
  have hhalf : b / 2 < 0 := by
    rw [Rat.div_def]
    have hi : (0 : Rat) < (2 : Rat)⁻¹ := by decide +kernel
    have := Rat.mul_lt_mul_of_pos_right hb hi
    grind
  have hnegative : b + step b p * Polynomial.eval p (step b p) < 0 := by grind
  have hprod := Rat.mul_lt_mul_of_pos_left hnegative hp
  grind

end ComputableAnalysis.PolynomialDescent
