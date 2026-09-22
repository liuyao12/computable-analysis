import ComputableAnalysis.FormalPowerSeriesAlgebra

/-! Rational boxes for power series with an explicit geometric coefficient
bound. No completed real, limit selection, or analytic derivative is used. -/
namespace ComputableAnalysis.FormalPowerSeries

theorem sumBelow_abs_le {f : Nat → Rat} {B : Rat} {n : Nat}
    (h : ∀ k, k < n → qabs (f k) ≤ B) :
    qabs (sumBelow f n) ≤ (n : Rat) * B := by
  induction n with
  | zero => simp [qabs]
  | succ n ih =>
      rw [sumBelow_succ]
      have hi := ih (fun k hk => h k (by omega))
      have hs := qabs_add_le (sumBelow f n) (f n)
      have hn := h n (by omega)
      simp only [Rat.natCast_add] at *
      grind

theorem pow_mono_exponent {R : Rat} (hR : 1 ≤ R) {k n : Nat} (hkn : k ≤ n) :
    R ^ k ≤ R ^ n := by
  induction hkn with
  | refl => exact Rat.le_refl
  | @step n _ ih =>
      have hn : 0 ≤ R ^ n := Rat.pow_nonneg (by grind)
      rw [Rat.pow_succ]
      have hm := Rat.mul_le_mul_of_nonneg_left hR hn
      grind

theorem half_pow_antitone {k n : Nat} (hkn : k ≤ n) :
    ((1 : Rat) / 2) ^ n ≤ ((1 : Rat) / 2) ^ k := by
  induction hkn with
  | refl => exact Rat.le_refl
  | @step n _ ih =>
      have hn : 0 ≤ ((1 : Rat) / 2) ^ n := Rat.pow_nonneg (by decide +kernel)
      rw [Rat.pow_succ]
      grind

/-- The literal finite prefix, together with a symmetric geometric tail. -/
def geometricRaw (c : Coeffs) (M x : Rat) : RealRaw where
  compute n :=
    let s := sumBelow (fun k => c k * x ^ k) n
    let e := 2 * M * ((1 : Rat) / 2) ^ n
    ⟨s - e, s + e⟩
  rate := .geometric 0 (4 * M) (1 / 2) (by decide +kernel) (by decide +kernel) (by
    intro n _
    simp only [QInterval.width]
    grind)

theorem geometricRaw_width (c : Coeffs) (M x : Rat) (n : Nat) :
    ((geometricRaw c M x).compute n).width = 4 * M * ((1 : Rat) / 2) ^ n := by
  simp only [geometricRaw, QInterval.width]
  grind

/-- Absolute terms, not just their signed sums, decay geometrically. -/
theorem term_bound {c : Coeffs} {M R x : Rat}
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hc : ∀ n, qabs (c n) ≤ M * R ^ n)
    (hx : R * qabs x ≤ 1 / 2) (n : Nat) :
    qabs (c n * x ^ n) ≤ M * ((1 : Rat) / 2) ^ n := by
  have hp : R ^ n * qabs (x ^ n) ≤ ((1 : Rat) / 2) ^ n := by
    induction n with
    | zero => simp only [Rat.pow_zero, Rat.one_mul]; decide +kernel
    | succ n ih =>
        rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_succ, qabs_mul]
        have hnon : 0 ≤ R ^ n * qabs (x ^ n) :=
          Rat.mul_nonneg (Rat.pow_nonneg hR) (qabs_nonneg _)
        have hhalf := Rat.pow_nonneg (n := n) (a := (1 : Rat) / 2) (by decide +kernel)
        have hm := Rat.mul_le_mul_of_nonneg_left hx hnon
        have hi := Rat.mul_le_mul_of_nonneg_right ih (show (0 : Rat) ≤ 1/2 by decide +kernel)
        grind
  rw [qabs_mul]
  have hm := Rat.mul_le_mul_of_nonneg_right (hc n) (qabs_nonneg (x ^ n))
  have hh := Rat.mul_le_mul_of_nonneg_left hp hM
  grind

theorem geometricRaw_valid {c : Coeffs} {M R x : Rat}
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hc : ∀ n, qabs (c n) ≤ M * R ^ n)
    (hx : R * qabs x ≤ 1 / 2) : (geometricRaw c M x).Valid := by
  have hp (n : Nat) : 0 ≤ M * ((1 : Rat) / 2) ^ n :=
    Rat.mul_nonneg hM (Rat.pow_nonneg (by decide +kernel))
  have hord (n : Nat) :
      ((geometricRaw c M x).compute n).lo ≤ ((geometricRaw c M x).compute n).hi := by
    dsimp [geometricRaw]
    have := hp n
    grind
  have hstep (n : Nat) :
      ((geometricRaw c M x).compute n).lo ≤ ((geometricRaw c M x).compute (n+1)).lo ∧
      ((geometricRaw c M x).compute (n+1)).hi ≤ ((geometricRaw c M x).compute n).hi := by
    have ht := term_bound hM hR hc hx n
    have hlo := neg_qabs_le_self (c n * x ^ n)
    have hhi := self_le_qabs (c n * x ^ n)
    dsimp [geometricRaw]
    rw [sumBelow_succ, Rat.pow_succ]
    grind
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [geometricRaw_width]
    have := hp n
    grind
  · intro n m hnm
    induction hnm with
    | refl => exact ⟨Rat.le_refl, hord n, Rat.le_refl⟩
    | @step m _ ih =>
        exact ⟨Rat.le_trans ih.1 (hstep m).1, hord (m+1),
          Rat.le_trans (hstep m).2 ih.2.2⟩
  · intro eps
    refine ⟨RationalMajorant.halfDecayShift (4 * M) eps, ?_⟩
    intro n hn
    rw [geometricRaw_width]
    exact Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_left (half_pow_antitone hn) (by grind))
      (RationalMajorant.halfDecayShift_spec (by grind) eps)

/-- A computable stage meeting any positive rational width request. -/
theorem geometricRaw_precision (c : Coeffs) {M : Rat} (hM : 0 ≤ M)
    (x : Rat) (eps : QPos) :
    ((geometricRaw c M x).compute (RationalMajorant.halfDecayShift (4*M) eps)).width
      ≤ eps.val := by
  rw [geometricRaw_width]
  exact RationalMajorant.halfDecayShift_spec (by grind) eps

/-- Every later finite partial sum lies in the current box. This ties the
valid interval algorithm to its series, without introducing an ambient limit. -/
theorem geometricRaw_contains_prefix {c : Coeffs} {M R x : Rat}
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hc : ∀ n, qabs (c n) ≤ M * R ^ n)
    (hx : R * qabs x ≤ 1 / 2) {n m : Nat} (hnm : n ≤ m) :
    ((geometricRaw c M x).compute n).lo ≤ sumBelow (fun k => c k * x ^ k) m ∧
    sumBelow (fun k => c k * x ^ k) m ≤ ((geometricRaw c M x).compute n).hi := by
  have hn := (geometricRaw_valid hM hR hc hx).2.1 n m hnm
  have hp := Rat.mul_nonneg hM
    (Rat.pow_nonneg (n := m) (a := (1 : Rat)/2) (by decide +kernel))
  dsimp [geometricRaw] at *
  grind

/-- Nonnegative radii about the same prefix give same-stage overlap. When
both majorants certify validity, the evaluators represent the same value. -/
theorem geometricRaw_equiv (c : Coeffs) (x : Rat) {M N : Rat}
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    (geometricRaw c M x).Equiv (geometricRaw c N x) := by
  intro n
  have hm := Rat.mul_nonneg hM
    (Rat.pow_nonneg (n := n) (a := (1 : Rat)/2) (by decide +kernel))
  have hn := Rat.mul_nonneg hN
    (Rat.pow_nonneg (n := n) (a := (1 : Rat)/2) (by decide +kernel))
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  dsimp [geometricRaw, QInterval.Overlaps]
  grind

end ComputableAnalysis.FormalPowerSeries
