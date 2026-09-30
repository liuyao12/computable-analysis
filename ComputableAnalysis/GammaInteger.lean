import ComputableAnalysis.PowerSeries

/-! Positive-integer Gamma values from the actual Gauss finite products.
The computation uses the cancelled short product; its equivalence with the
original product and its convergence to factorial are proved. This is not
an arbitrary-real or complex Gamma evaluator or an Euler-integral bridge. -/
namespace ComputableAnalysis
namespace GammaInteger

/-- The finite rising product, including the empty product. -/
def rising (x : Rat) : Nat → Rat
  | 0 => 1
  | k+1 => rising x k * (x+(k : Rat))

/-- Gauss's original finite approximation at the positive integer `m+1`. -/
def gauss (m n : Nat) : Rat :=
  (factorial n : Rat)*(n : Rat)^(m+1)/rising ((m : Rat)+1) (n+1)

/-- The cancelled finite product, whose length depends on the input integer. -/
def ratioProduct (n : Nat) : Nat → Rat
  | 0 => 1
  | k+1 => ratioProduct n k*((n : Rat)/((n : Rat)+(k : Rat)+1))

def approx (m n : Nat) : Rat := (factorial m : Rat)*ratioProduct n (m+1)

theorem rising_pos (m k : Nat) : 0 < rising ((m : Rat)+1) k := by
  induction k with
  | zero => change (0 : Rat)<1; decide
  | succ k ih =>
    have hm := Rat.natCast_nonneg (a := m)
    have hk := Rat.natCast_nonneg (a := k)
    exact Rat.mul_pos ih (by grind)

theorem rising_factorial (m k : Nat) :
    rising ((m : Rat)+1) k*(factorial m : Rat)=(factorial (m+k) : Rat) := by
  induction k with
  | zero => simp [rising]
  | succ k ih =>
    rw [show m+(k+1)=(m+k)+1 by omega, factorial]
    simp only [Rat.natCast_mul,Rat.natCast_add]
    change (rising ((m : Rat)+1) k*((m : Rat)+1+(k : Rat)))*(factorial m : Rat)=_
    grind only

theorem ratioProduct_cancel (n k : Nat) :
    rising ((n : Rat)+1) k*ratioProduct n k=(n : Rat)^k := by
  induction k with
  | zero => simp [rising,ratioProduct]
  | succ k ih =>
    have hn := Rat.natCast_nonneg (a := n)
    have hk := Rat.natCast_nonneg (a := k)
    have hd : (n : Rat)+(k : Rat)+1 ≠ 0 := by grind
    have hc := Rat.mul_inv_cancel ((n : Rat)+(k : Rat)+1) hd
    simp only [rising,ratioProduct,Rat.pow_succ,Rat.div_def]
    grind only

/-- The efficient evaluator is exactly the original Gauss finite approximation. -/
theorem gauss_eq_approx (m n : Nat) : gauss m n=approx m n := by
  have h1 := rising_factorial m (n+1)
  have h2 := rising_factorial n (m+1)
  have hc := ratioProduct_cancel n (m+1)
  have he : m+(n+1)=n+(m+1) := by omega
  rw [he] at h1
  have hd := Rat.ne_of_gt (rising_pos m (n+1))
  have hi := Rat.mul_inv_cancel (rising ((m : Rat)+1) (n+1)) hd
  unfold gauss approx
  rw [Rat.div_def]
  grind only

theorem ratioProduct_bounds (n k : Nat) : 0 ≤ ratioProduct n k ∧ ratioProduct n k ≤ 1 := by
  induction k with
  | zero => change (0 : Rat) ≤ 1 ∧ 1 ≤ 1; constructor <;> decide
  | succ k ih =>
    have hn := Rat.natCast_nonneg (a := n)
    have hk := Rat.natCast_nonneg (a := k)
    have hd : 0 < (n : Rat)+(k : Rat)+1 := by grind
    have hnn : 0 ≤ (n : Rat)/((n : Rat)+(k : Rat)+1) :=
      Rat.mul_nonneg hn (Rat.le_of_lt (Rat.inv_pos.mpr hd))
    have hle : (n : Rat)/((n : Rat)+(k : Rat)+1) ≤ 1 := by
      apply Rat.le_of_mul_le_mul_right (c := (n : Rat)+(k : Rat)+1) ?_ hd
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hd),Rat.one_mul]
      grind
    exact ⟨Rat.mul_nonneg ih.1 hnn,
      Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hle ih.1) (by simpa using ih.2)⟩

/-- A finite product estimate; no infinite Gamma law is assumed. -/
theorem ratioProduct_gap (n k : Nat) :
    1-ratioProduct n k ≤ (k : Rat)^2/((n : Rat)+1) := by
  induction k with
  | zero => change (1 : Rat)-1 ≤ 0^2/((n : Rat)+1); simp only [Rat.pow_succ,Rat.pow_zero,Rat.mul_zero,Rat.zero_mul,Rat.div_def,Rat.sub_self]; exact Rat.le_refl
  | succ k ih =>
    have hn := Rat.natCast_nonneg (a := n)
    have hk := Rat.natCast_nonneg (a := k)
    have hN : 0 < (n : Rat)+1 := by grind
    have hD : 0 < (n : Rat)+(k : Rat)+1 := by grind
    have hninv := Rat.inv_pos.mpr hN
    have hDinv := Rat.inv_pos.mpr hD
    have hcN := Rat.mul_inv_cancel ((n : Rat)+1) (Rat.ne_of_gt hN)
    have hcD := Rat.mul_inv_cancel ((n : Rat)+(k : Rat)+1) (Rat.ne_of_gt hD)
    have hp := ratioProduct_bounds n k
    have hinv : ((n : Rat)+(k : Rat)+1)⁻¹ ≤ ((n : Rat)+1)⁻¹ := by
      apply Rat.le_of_mul_le_mul_right (c := (n : Rat)+(k : Rat)+1) ?_ hD
      have hnon := Rat.mul_nonneg hk (Rat.le_of_lt hninv)
      have he : ((n : Rat)+1)⁻¹*((n : Rat)+(k : Rat)+1) =
          1+(k : Rat)*((n : Rat)+1)⁻¹ := by grind only
      rw [Rat.inv_mul_cancel ((n : Rat)+(k : Rat)+1) (Rat.ne_of_gt hD),he]
      grind only
    have hratio := Rat.mul_le_mul_of_nonneg_left hinv
      (by grind : 0 ≤ (k : Rat)+1)
    have hb := Rat.mul_le_mul_of_nonneg_right hp.2
      (Rat.mul_nonneg (by grind : 0 ≤ (k : Rat)+1) (Rat.le_of_lt hDinv))
    have he : 1-ratioProduct n (k+1) =
        (1-ratioProduct n k)+ratioProduct n k*((k : Rat)+1)*((n : Rat)+(k : Rat)+1)⁻¹ := by
      simp only [ratioProduct,Rat.div_def]
      grind only
    rw [he]
    have hs : (1-ratioProduct n k)+ratioProduct n k*((k : Rat)+1)*((n : Rat)+(k : Rat)+1)⁻¹ ≤
        (k : Rat)^2/((n : Rat)+1)+((k : Rat)+1)*((n : Rat)+1)⁻¹ := by
      have hb' : ratioProduct n k*((k : Rat)+1)*((n : Rat)+(k : Rat)+1)⁻¹ ≤
          ((k : Rat)+1)*((n : Rat)+(k : Rat)+1)⁻¹ := by simpa only [Rat.one_mul,Rat.mul_assoc] using hb
      have ht := Rat.le_trans hb' hratio
      grind only
    have hk2 : (k : Rat)^2+((k : Rat)+1) ≤ ((k : Rat)+1)^2 := by
      simp only [Rat.pow_succ,Rat.pow_zero]
      grind only
    have ht := Rat.mul_le_mul_of_nonneg_right hk2 (Rat.le_of_lt hninv)
    simp only [Rat.div_def,Rat.natCast_add] at *
    have hre : (k : Rat)^2*((n : Rat)+1)⁻¹+((k : Rat)+1)*((n : Rat)+1)⁻¹ =
        ((k : Rat)^2+((k : Rat)+1))*((n : Rat)+1)⁻¹ := by grind only
    rw [hre] at hs
    exact Rat.le_trans hs ht

def errorNumerator (m : Nat) : Nat := factorial m*(m+1)^2

def error (m n : Nat) : Rat := (errorNumerator m : Rat)/((n+1 : Nat) : Rat)

/-- Explicit lower and upper estimates for the limit of the Gauss products. -/
theorem approx_bounds (m n : Nat) :
    approx m n ≤ (factorial m : Rat) ∧ (factorial m : Rat) ≤ approx m n+error m n := by
  have hp := ratioProduct_bounds n (m+1)
  have hg := ratioProduct_gap n (m+1)
  have hf := Rat.natCast_nonneg (a := factorial m)
  have hmul := Rat.mul_le_mul_of_nonneg_left hg hf
  have hupper := Rat.mul_le_mul_of_nonneg_left hp.2 hf
  unfold approx error errorNumerator
  simp only [Rat.natCast_mul,Rat.natCast_pow,Rat.natCast_add] at *
  rw [Rat.div_def] at *
  constructor <;> grind only

def candidate (m : Nat) : RealRaw where
  compute n := ⟨approx m n,approx m n+error m n⟩

private theorem candidate_equiv_factorial (m : Nat) :
    (candidate m).Equiv (RealRaw.ofRat (factorial m : Rat)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  exact ⟨(approx_bounds m n).1,(approx_bounds m n).2⟩

private theorem candidate_shrinks (m : Nat) : RealRaw.WidthsShrinkToZero (candidate m).compute := by
  apply shrinksToZero_of_natOverSuccBound (C := errorNumerator m)
  intro n
  change approx m n+error m n-approx m n ≤ _
  unfold error
  grind only

/-- A nested interval computation of Gamma at `m+1`, reading finite Gauss
products and their explicit errors; the factorial anchor is not read at runtime. -/
def raw (m : Nat) : RealRaw := RealRaw.prefixStabilize (candidate m) (fun _ => 0)

theorem raw_valid (m : Nat) : (raw m).Valid := by
  have hcontains := RealRaw.prefixStabilize_contains_anchor
    (candidate := candidate m) (anchor := RealRaw.ofRat (factorial m : Rat))
    (RealRaw.ofRat_valid _) (candidate_equiv_factorial m)
    (by intro n; change (factorial m : Rat)-(factorial m : Rat) ≤ 0; grind only)
  have hcurrent := RealRaw.prefixStabilize_contained_in_current_expand
    (candidate m) (fun _ => 0)
  have hstep : ∀ n, ((raw m).compute n).lo ≤ ((raw m).compute (n+1)).lo ∧
      ((raw m).compute (n+1)).hi ≤ ((raw m).compute n).hi := by
    intro n
    exact QInterval.intersection_contained_left
      ((raw m).compute n) (QInterval.expand ((candidate m).compute (n+1)) 0)
  have hordered : ∀ n, ((raw m).compute n).lo ≤ ((raw m).compute n).hi := by
    intro n
    have h := hcontains n
    change ((raw m).compute n).lo ≤ (factorial m : Rat) ∧
      (factorial m : Rat) ≤ ((raw m).compute n).hi at h
    exact Rat.le_trans h.1 h.2
  constructor
  · intro n; have h := hordered n; unfold QInterval.width; grind only
  · constructor
    · intro n k hnk
      induction hnk with
      | refl => exact ⟨Rat.le_refl,hordered n,Rat.le_refl⟩
      | @step k hnk ih =>
        have hs := hstep k
        exact ⟨Rat.le_trans ih.1 hs.1,hordered (k+1),Rat.le_trans hs.2 ih.2.2⟩
    · intro eps
      obtain ⟨N,hN⟩ := candidate_shrinks m eps
      refine ⟨N,fun n hn => ?_⟩
      have hc := hcurrent n
      have hw := hN n hn
      change (approx m n+error m n)-(approx m n) ≤ eps.val at hw
      change approx m n-0 ≤ ((raw m).compute n).lo ∧
        ((raw m).compute n).hi ≤ approx m n+error m n+0 at hc
      unfold QInterval.width
      grind only

/-- Exact identification of the actual limit computation. -/
theorem raw_equiv_factorial (m : Nat) :
    (raw m).Equiv (RealRaw.ofRat (factorial m : Rat)) :=
  RealRaw.prefixStabilize_equiv_anchor (RealRaw.ofRat_valid _) (candidate_equiv_factorial m)
    (by intro n; change (factorial m : Rat)-(factorial m : Rat) ≤ 0; grind only)

/-- The finite Gauss products converge with a rational error schedule. -/
theorem gauss_converges (m : Nat) (eps : QPos) : ∃ N, ∀ n, N ≤ n →
    qabs (gauss m n-(factorial m : Rat)) ≤ eps.val := by
  obtain ⟨N,hN⟩ := shrinksToZero_of_natOverSuccBound (C := errorNumerator m)
    (fun _ => Rat.le_refl) eps
  refine ⟨N,fun n hn => ?_⟩
  rw [gauss_eq_approx]
  have h := approx_bounds m n
  have he := hN n hn
  change error m n ≤ eps.val at he
  apply qabs_le_of_neg_le_le <;> grind only

end GammaInteger
end ComputableAnalysis
