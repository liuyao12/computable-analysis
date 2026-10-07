import ComputableAnalysis.ComplexSecantCalculus

/-! Rational descent directions for complex powers. All estimates and witnesses
use finite rational arithmetic; no trigonometric or complex-root theorem enters.
-/
namespace ComputableAnalysis.PolynomialDirection
open QComplex ComplexSecantCalculus

private theorem qext {a b : QComplex} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

private theorem pow_one (n : Nat) : pow one n = one := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow, ih, one_mul_cert]

private theorem majorant_scale (C t : Rat) (n : Nat) :
    powerLinearRemainderMajorant C t n = powerLinearRemainderMajorant C 1 n * t * t := by
  induction n with
  | zero => simp [powerLinearRemainderMajorant]
  | succ n ih =>
      rw [powerLinearRemainderMajorant, powerLinearRemainderMajorant, ih]
      cases n <;> simp only [powerSecondOrderMajorant] <;> grind

/-- A computable positive rational increment whose positive-degree power
has strictly positive imaginary part. -/
def smallStep (k : Nat) : Rat :=
  1 / (2 * (powerLinearRemainderMajorant 2 1 k + 1))

theorem smallStep_power_im_pos (k : Nat) (hk : 0 < k) :
    0 < (pow { re := 1, im := smallStep k } k).im := by
  let M := powerLinearRemainderMajorant 2 1 k
  let t := smallStep k
  have hM : 0 ≤ M := powerLinearRemainderMajorant_nonneg (by decide +kernel) (by decide +kernel) k
  have hd : 0 < 2 * (M + 1) := by grind
  have ht : 0 < t := by
    change 0 < 1 / (2 * (M + 1))
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.inv_pos.mpr hd
  have hcancel : t * (2 * (M + 1)) = 1 := by
    change (1 / (2 * (M + 1))) * (2 * (M + 1)) = 1
    rw [Rat.div_def, Rat.one_mul, Rat.mul_comm]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hd)
  have hMt0 := Rat.mul_nonneg hM (Rat.le_of_lt ht)
  have ht1 : t ≤ 1 := by grind
  have h2 : (0 : Rat) ≤ 2 := by decide +kernel
  have hz : normBound one ≤ (2 : Rat) := by decide +kernel
  have hinc : normBound ({ re := 0, im := t } : QComplex) = t := by
    change qabs 0 + qabs t = t
    rw [qabs_eq_self_of_nonneg (Rat.le_refl), qabs_eq_self_of_nonneg (Rat.le_of_lt ht), Rat.zero_add]
  have hsum : add one { re := 0, im := t } = { re := 1, im := t } := by
    simp [add, one, Rat.add_zero, Rat.zero_add]
  have hnorm : normBound (add one { re := 0, im := t }) ≤ 2 := by
    rw [hsum]
    simp only [normBound]
    rw [qabs_eq_self_of_nonneg (by decide +kernel : (0 : Rat) ≤ 1),
      qabs_eq_self_of_nonneg (Rat.le_of_lt ht)]
    grind
  have hr := powerLinearRemainder_normBound_le h2 hz hnorm (Rat.le_of_lt ht)
    (show normBound ({ re := 0, im := t } : QComplex) ≤ t by rw [hinc]; exact Rat.le_refl) k
  rw [majorant_scale] at hr
  have him : (powerLinearRemainder one { re := 0, im := t } k).im =
      (pow { re := 1, im := t } k).im - (k : Rat) * t := by
    cases k with
    | zero => omega
    | succ n =>
        unfold powerLinearRemainder
        rw [hsum, pow_one]
        simp only [powerDirectionalTerm]
        rw [pow_one, one_mul_cert]
        simp only [sub, add, neg, scaleRat, one]
        grind
  have habs : qabs ((pow { re := 1, im := t } k).im - (k : Rat) * t) ≤ M * t * t := by
    have hre := qabs_nonneg (powerLinearRemainder one { re := 0, im := t } k).re
    change qabs (powerLinearRemainder one { re := 0, im := t } k).re +
      qabs (powerLinearRemainder one { re := 0, im := t } k).im ≤ M * t * t at hr
    rw [him] at hr
    grind
  have hlow := neg_qabs_le_self ((pow { re := 1, im := t } k).im - (k : Rat) * t)
  have hk1 : (1 : Rat) ≤ (k : Rat) := by exact_mod_cast hk
  have hkt := Rat.mul_le_mul_of_nonneg_right hk1 (Rat.le_of_lt ht)
  have hMt : 2 * M * t < 1 := by grind
  have hMt2 := Rat.mul_lt_mul_of_pos_right hMt ht
  change 0 < (pow { re := 1, im := t } k).im
  grind

/-- An explicit upper bound for the first crossing of the left half-plane. -/
def crossingBound (t : Rat) : Nat := (t * t / 2).den + 2

theorem exists_negative_real_power_unit (t : Rat) (ht : 0 < t) :
    ∃ n, n ≤ crossingBound t ∧ (pow { re := 1, im := t } n).re < 0 := by
  classical
  apply Classical.byContradiction
  intro hnone
  let N := (t * t / 2).den + 1
  let u : QComplex := { re := 1, im := t }
  have hpos : ∀ n, n ≤ N + 1 → 0 ≤ (pow u n).re := by
    intro n hn
    by_cases h : (pow u n).re < 0
    · exact False.elim (hnone ⟨n, hn, h⟩)
    · grind
  have hrec : ∀ n, n ≤ N → t ≤ (pow u (n+1)).im ∧
      (pow u (n+1)).re ≤ 1 - (n : Rat) * t * t := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [pow, mul_one_cert, u]
        grind
    | succ n ih =>
        intro hn
        have hi := ih (by omega)
        have hp := hpos (n+1) (by omega)
        have him := Rat.mul_le_mul_of_nonneg_left hi.1 (Rat.le_of_lt ht)
        have hre := Rat.mul_nonneg (Rat.le_of_lt ht) hp
        change t ≤ (mul u (pow u (n+1))).im ∧
          (mul u (pow u (n+1))).re ≤ 1 - ((n+1 : Nat) : Rat) * t * t
        simp only [mul, u, Rat.one_mul, Rat.natCast_add]
        constructor <;> grind
  have hsq : 0 < t * t / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_pos (Rat.mul_pos ht ht) (by decide +kernel)
  have hden := one_div_den_succ_le_of_pos hsq
  have hN : 0 < (N : Rat) := Rat.natCast_pos.mpr (by dsimp [N]; omega)
  have hmul := Rat.mul_le_mul_of_nonneg_right hden (Rat.le_of_lt hN)
  have hcancel : (1 / (N : Rat)) * (N : Rat) = 1 := by
    rw [Rat.div_def, Rat.one_mul, Rat.mul_comm]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hN)
  change (1 / (N : Rat)) * (N : Rat) ≤ (t * t / 2) * (N : Rat) at hmul
  rw [hcancel] at hmul
  have hh : t*t/2+t*t/2=t*t := by
    rw [Rat.div_def]
    have : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
    grind
  have hn := (hrec N (Nat.le_refl _)).2
  have hp := hpos (N+1) (Nat.le_refl _)
  grind

private theorem pow_scale (a : Rat) (z : QComplex) (n : Nat) :
    pow (scaleRat a z) n = scaleRat (a^n) (pow z n) := by
  induction n with
  | zero => simp [pow, Rat.pow_zero, scaleRat, Rat.one_mul]
  | succ n ih =>
      rw [pow, ih, pow, Rat.pow_succ]
      apply qext <;> simp only [mul, scaleRat] <;> grind

private theorem pow_pos {a : Rat} (ha : 0 < a) (n : Nat) : 0 < a^n := by
  induction n with
  | zero => rw [Rat.pow_zero]; decide +kernel
  | succ n ih => rw [Rat.pow_succ]; exact Rat.mul_pos ih ha

/-- Any rational complex point strictly above the real axis has a power
strictly to the left of the imaginary axis. -/
theorem exists_negative_real_power (a : QComplex) (ha : 0 < a.im) :
    ∃ n, (pow a n).re < 0 := by
  by_cases hre : a.re < 0
  · exact ⟨1, by simpa only [pow, mul_one_cert] using hre⟩
  by_cases hz : a.re = 0
  · refine ⟨2, ?_⟩
    have hsq := Rat.mul_pos ha ha
    simp only [pow, mul, one, hz]
    grind
  have hre : 0 < a.re := by grind
  let t := a.im / a.re
  have ht : 0 < t := Rat.mul_pos ha (Rat.inv_pos.mpr hre)
  obtain ⟨n, _, hn⟩ := exists_negative_real_power_unit t ht
  have heq : a = scaleRat a.re { re := 1, im := t } := by
    apply qext
    · simp [scaleRat]
    · change a.im = a.re * (a.im / a.re)
      have hi := Rat.mul_inv_cancel a.re (Rat.ne_of_gt hre)
      rw [Rat.div_def]
      grind
  refine ⟨n, ?_⟩
  have hp : pow a n = scaleRat (a.re^n) (pow { re := 1, im := t } n) := by
    calc
      pow a n = pow (scaleRat a.re { re := 1, im := t }) n := congrArg (fun z => pow z n) heq
      _ = _ := pow_scale _ _ _
  rw [hp]
  change a.re^n * (pow { re := 1, im := t } n).re < 0
  have hprod := Rat.mul_lt_mul_of_pos_left hn (pow_pos hre n)
  grind

private theorem pow_add (z : QComplex) (m n : Nat) :
    pow z (m+n) = mul (pow z m) (pow z n) := by
  induction m with
  | zero => simp only [Nat.zero_add, pow, one_mul_cert]
  | succ m ih =>
      rw [show m+1+n=(m+n)+1 by omega, pow, ih, pow, mul_assoc_cert]

private theorem pow_pow (z : QComplex) (m n : Nat) :
    pow (pow z m) n = pow z (m*n) := by
  induction n with
  | zero => simp only [Nat.mul_zero, pow]
  | succ n ih =>
      rw [pow, ih, Nat.mul_succ, Nat.add_comm, pow_add]

private theorem pow_conj (z : QComplex) (n : Nat) :
    pow (conj z) n = conj (pow z n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow, ih, pow, QComplex.conj_mul]

/-- Every positive power takes a rational argument into the left half-plane.
The proof constructs the argument using a small rational rotation and finite
powers, avoiding roots of unity or trigonometry. -/
theorem exists_power_negative_real (k : Nat) (hk : 0 < k) :
    ∃ d : QComplex, (pow d k).re < 0 := by
  let w : QComplex := { re := 1, im := smallStep k }
  have hw : 0 < (pow w k).im := smallStep_power_im_pos k hk
  obtain ⟨n, hn⟩ := exists_negative_real_power (pow w k) hw
  refine ⟨pow w n, ?_⟩
  rw [pow_pow] at hn ⊢
  simpa only [Nat.mul_comm] using hn

/-- Rational directional negativity for every nonzero complex coefficient
and every positive exponent. This is the algebraic direction step in the
minimum-modulus proof of FTA. -/
theorem exists_negative_direction (c : QComplex) (hc : c ≠ zero)
    (k : Nat) (hk : 0 < k) : ∃ d : QComplex, (mul c (pow d k)).re < 0 := by
  by_cases hre : c.re < 0
  · exact ⟨one, by rw [pow_one, mul_one_cert]; exact hre⟩
  by_cases hpos : 0 < c.re
  · obtain ⟨d, hd⟩ := exists_power_negative_real k hk
    have hprod := Rat.mul_lt_mul_of_pos_left hd hpos
    by_cases him : 0 ≤ c.im * (pow d k).im
    · refine ⟨d, ?_⟩
      change c.re * (pow d k).re - c.im * (pow d k).im < 0
      grind
    · refine ⟨conj d, ?_⟩
      rw [pow_conj]
      change c.re * (pow d k).re - c.im * (-(pow d k).im) < 0
      grind
  have hre0 : c.re = 0 := by grind
  have himne : c.im ≠ 0 := by
    intro h
    apply hc
    apply qext <;> assumption
  let d : QComplex := { re := 1, im := smallStep k }
  have hd : 0 < (pow d k).im := smallStep_power_im_pos k hk
  by_cases him : 0 < c.im
  · refine ⟨d, ?_⟩
    have hp := Rat.mul_pos him hd
    change c.re * (pow d k).re - c.im * (pow d k).im < 0
    rw [hre0]
    grind
  · refine ⟨conj d, ?_⟩
    rw [pow_conj]
    have hn : c.im < 0 := by grind
    have hp := Rat.mul_lt_mul_of_pos_right hn hd
    change c.re * (pow d k).re - c.im * (-(pow d k).im) < 0
    rw [hre0]
    grind

end ComputableAnalysis.PolynomialDirection
