import ComputableAnalysis.FormalPowerSeriesAlgebra
import ComputableAnalysis.GeometricPowerSeries

/-! Local Laurent data for Painlevé I. The differential residual is specified
independently of the coefficient algorithm. Convergence and differential
semantics are separate obligations. No ambient completed number type is used. -/
namespace ComputableAnalysis.AlgebraicODE.Painleve.Laurent
open FormalPowerSeries

/-- `s^4 (y''-6y²-f(s))` for `y=s⁻² Σ cₙsⁿ`. -/
def residual (f c : Coeffs) (n : Nat) : Rat :=
  shiftedSecondEuler (-2) c n - 6*cauchyProduct c c n -
    (if 4 ≤ n then f (n-4) else 0)

def IsSolution (f c : Coeffs) : Prop := ∀ n, residual f c n = 0

def inner (c : Coeffs) (n : Nat) : Rat :=
  sumBelow (fun k => c (k+1)*c (n-1-k)) (n-1)

def divisor (n : Nat) : Rat := ((n : Rat)-6)*((n : Rat)+1)

theorem sumBelow_head (f : Nat → Rat) (n : Nat) :
    sumBelow f (n+1) = f 0 + sumBelow (fun k => f (k+1)) n := by
  induction n with
  | zero => rw [show 1 = 0+1 by rfl, sumBelow_succ]; simp; grind
  | succ n ih => rw [sumBelow_succ, ih, sumBelow_succ]; grind

theorem cauchy_square_split {c : Coeffs} (hc : c 0 = 1) {n : Nat} (hn : 0 < n) :
    cauchyProduct c c n = 2*c n+inner c n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [cauchyProduct_split, sumBelow_head]
  simp only [Nat.sub_zero, hc, Rat.mul_one, Rat.one_mul, inner]
  have he : (fun k => c (m+1-(k+1))*c (k+1)) =
      (fun k => c (k+1)*c (m-k)) := by
    funext k
    rw [show m+1-(k+1) = m-k by omega]
    grind
  rw [he]
  grind

theorem residual_split {f c : Coeffs} (hc : c 0 = 1) {n : Nat} (hn : 0 < n) :
    residual f c n = divisor n*c n-6*inner c n-
      (if 4 ≤ n then f (n-4) else 0) := by
  unfold residual
  rw [cauchy_square_split hc hn]
  unfold shiftedSecondEuler divisor
  grind

/-- Any nonzero double-pole leading coefficient is forced to be one. -/
theorem leading_coefficient {f c : Coeffs} (h : IsSolution f c) (hc : c 0 ≠ 0) :
    c 0 = 1 := by
  have h0 := h 0
  simp [residual, shiftedSecondEuler, cauchyProduct, sumBelow_succ] at h0
  grind

/-- The resonance obstruction is derived from the differential equation,
not inserted into the recurrence. At every double pole, `f₂` must vanish. -/
theorem resonance_obstruction {f c : Coeffs} (h : IsSolution f c) (hc : c 0 = 1) :
    c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0 ∧ c 4 = -f 0/10 ∧ c 5 = -f 1/6 ∧ f 2 = 0 := by
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  rw [residual_split hc (by decide)] at h1 h2 h3 h4 h5 h6
  simp [divisor, inner, sumBelow_succ, hc] at h1 h2 h3 h4 h5 h6
  grind

/-- Painlevé I in local coordinate `s=x-p`: the forcing is `p+s`. -/
def forcing (p : Rat) : Coeffs := ofPolynomial [p, 1]

/-- Pole position `p` and coefficient `c₆=q` are free parameters. -/
def coeff (p q : Rat) : Nat → Rat
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => -p/10
  | 5 => -1/6
  | 6 => q
  | n+7 => 6 * sumBelow (fun k =>
      if _hk : k < n+6 then coeff p q (k+1) * coeff p q (n+6-k) else 0) (n+6) /
        divisor (n+7)
termination_by n => n

theorem coeff_recurrence (p q : Rat) {n : Nat} (hn : 7 ≤ n) :
    divisor n*coeff p q n = 6*inner (coeff p q) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hdiv : divisor (7+m) ≠ 0 := by
    have hm : (0 : Rat) ≤ (m : Rat) := Rat.natCast_nonneg
    unfold divisor
    simp only [Rat.natCast_add]
    exact Rat.ne_of_gt (Rat.mul_pos (by grind) (by grind))
  rw [show 7+m=m+7 by omega, coeff]
  rw [mul_div_cancel_left (by simpa [Nat.add_comm] using hdiv)]
  congr 1
  apply sumBelow_congr
  intro k hk
  rw [dif_pos hk, show m+7-1 = m+6 by omega]

theorem coeff_isSolution (p q : Rat) : IsSolution (forcing p) (coeff p q) := by
  intro n
  by_cases hn : n < 7
  · have hn' : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
    rcases hn' with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [residual, shiftedSecondEuler, cauchyProduct, sumBelow_succ,
        coeff, forcing, ofPolynomial] <;> grind
  · rw [residual_split (by rw [coeff]) (by omega), coeff_recurrence p q (by omega)]
    have hf : forcing p (n-4) = 0 := by
      unfold forcing ofPolynomial
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [if_pos (by omega), hf]
    grind

private theorem rat_pow_add (r : Rat) (m n : Nat) : r^(m+n)=r^m*r^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [show m+(n+1)=(m+n)+1 by omega, Rat.pow_succ, ih, Rat.pow_succ]; grind

/-- An explicit majorant, uniform in the two supplied rational parameters. -/
def growthBound (p q : Rat) : Rat := 1+6*qabs p+6*qabs q

theorem growthBound_ge_one (p q : Rat) : 1 ≤ growthBound p q := by
  have := qabs_nonneg p
  have := qabs_nonneg q
  unfold growthBound
  grind

theorem divisor_lower {n : Nat} (hn : 7 ≤ n) : (n : Rat)-1 ≤ divisor n := by
  have hn' : (7 : Rat) ≤ (n : Rat) := by exact_mod_cast hn
  have hp := Rat.mul_nonneg (show 0 ≤ (n : Rat)-7 by grind)
    (show 0 ≤ (n : Rat)+1 by grind)
  unfold divisor
  grind

/-- The nonlinear convolution is controlled by a geometric majorant.
The stronger bound on positive coefficients closes the quadratic induction. -/
theorem coeff_growth_positive (p q : Rat) {n : Nat} (hn : 0 < n) :
    6*qabs (coeff p q n) ≤ growthBound p q ^ n := by
  let R := growthBound p q
  have hR : 1 ≤ R := growthBound_ge_one p q
  change 6*qabs (coeff p q n) ≤ R^n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn7 : n < 7
    · have hc : 6*qabs (coeff p q n) ≤ R := by
        have hp := qabs_nonneg p
        have hq := qabs_nonneg q
        have casesN : n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
        rcases casesN with rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [coeff, Rat.div_def, qabs, R, growthBound] <;> grind
      exact Rat.le_trans hc (by simpa using pow_mono_exponent hR (show 1 ≤ n by omega))
    · have hdiv := divisor_lower (show 7 ≤ n by omega)
      have hn' : (7 : Rat) ≤ (n : Rat) := by exact_mod_cast (show 7 ≤ n by omega)
      have hdpos : 0 < divisor n := by grind
      have hterm (k : Nat) (hk : k < n-1) :
          qabs (36*(coeff p q (k+1)*coeff p q (n-1-k))) ≤ R^n := by
        have h1 := ih (k+1) (by omega) (by omega)
        have h2 := ih (n-1-k) (by omega) (by omega)
        have hm1 := Rat.mul_le_mul_of_nonneg_right h1
          (Rat.mul_nonneg (show (0 : Rat) ≤ 6 by decide) (qabs_nonneg (coeff p q (n-1-k))))
        have hm2 := Rat.mul_le_mul_of_nonneg_left h2
          (Rat.pow_nonneg (n := k+1) (show 0 ≤ R by grind))
        have he : R^(k+1)*R^(n-1-k) = R^n := by
          rw [← rat_pow_add, show k+1+(n-1-k)=n by omega]
        rw [qabs_mul, qabs_mul, show qabs (36 : Rat)=36 by decide +kernel]
        rw [he] at hm2
        grind
      have hsum := sumBelow_abs_le hterm
      rw [sumBelow_mul, qabs_mul, show qabs (36 : Rat)=36 by decide +kernel] at hsum
      change 36*qabs (inner (coeff p q) n) ≤ ((n-1 : Nat) : Rat)*R^n at hsum
      have he : ((n-1 : Nat) : Rat) = (n : Rat)-1 := by
        have : n-1+1=n := by omega
        have h := congrArg (fun k : Nat => (k : Rat)) this
        simp only [Rat.natCast_add] at h
        grind
      rw [he] at hsum
      have hr := congrArg qabs (coeff_recurrence p q (show 7 ≤ n by omega))
      rw [qabs_mul, qabs_mul, qabs_eq_self_of_nonneg (Rat.le_of_lt hdpos),
        show qabs (6 : Rat)=6 by decide +kernel] at hr
      have hm := Rat.mul_le_mul_of_nonneg_right hdiv (Rat.pow_nonneg (n := n) (by grind : 0 ≤ R))
      apply Rat.le_of_mul_le_mul_right (c := divisor n)
      · grind
      · exact hdpos

theorem coeff_growth (p q : Rat) (n : Nat) :
    qabs (coeff p q n) ≤ growthBound p q ^ n := by
  cases n with
  | zero => simp [coeff, qabs]; grind
  | succ n =>
      have := coeff_growth_positive p q (n := n+1) (by omega)
      have := qabs_nonneg (coeff p q (n+1))
      grind

/-- The regular factor of the Laurent expansion, evaluated by finite boxes. -/
def factorRaw (p q s : Rat) : RealRaw := geometricRaw (coeff p q) 1 s

theorem factorRaw_valid (p q s : Rat) (hs : growthBound p q*qabs s ≤ 1/2) :
    (factorRaw p q s).Valid :=
  geometricRaw_valid (by decide) (Rat.le_trans (by decide) (growthBound_ge_one p q))
    (by intro n; simpa using coeff_growth p q n) hs

theorem factorRaw_precision (p q s : Rat) (eps : QPos) :
    ((factorRaw p q s).compute (RationalMajorant.halfDecayShift 4 eps)).width ≤ eps.val := by
  unfold factorRaw
  simpa only [Rat.mul_one] using geometricRaw_precision (coeff p q) (M := 1) (by decide) s eps

/-- The independent Laurent equation fixes every coefficient after the
pole position and resonant coefficient have been supplied. -/
theorem solution_unique (p q : Rat) {c : Coeffs} (h : IsSolution (forcing p) c)
    (h0 : c 0 = 1) (h6 : c 6 = q) : ∀ n, c n = coeff p q n := by
  have hl := resonance_obstruction h h0
  simp only [forcing, ofPolynomial, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none] at hl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 7
    · have hc : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rw [coeff] <;> grind only
    · have he := h n
      have he' := coeff_isSolution p q n
      rw [residual_split h0 (by omega)] at he
      rw [residual_split (by rw [coeff]) (by omega)] at he'
      have hi : inner c n = inner (coeff p q) n := by
        apply sumBelow_congr
        intro k hk
        rw [ih (k+1) (by omega), ih (n-1-k) (by omega)]
      have hd := divisor_lower (show 7 ≤ n by omega)
      have hnq : (7 : Rat) ≤ (n : Rat) := (Rat.natCast_le_natCast (a := 7) (b := n)).2 (by omega)
      have hd0 : divisor n ≠ 0 := by grind only
      have hc := Rat.mul_inv_cancel (divisor n) hd0
      rw [hi] at he
      grind only

end ComputableAnalysis.AlgebraicODE.Painleve.Laurent
