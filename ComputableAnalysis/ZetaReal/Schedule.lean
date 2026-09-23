import ComputableAnalysis.ZetaReal.Rectangles

namespace ComputableAnalysis.ZetaReal
open FormalPowerSeries

/-- The lower exponent of a chart; positive `q` keeps it strictly below two. -/
def lower (q : Nat) : Rat := 1+1/((q : Rat)+1)

theorem lower_chart (q m : Nat) : InChart q m (lower q) := by
  have hr := reciprocal_bounds q
  have hm := Rat.natCast_nonneg (a := m)
  constructor
  · exact Rat.le_refl
  · unfold lower reciprocal at *; grind

theorem lower_lt_two {q : Nat} (hq : 0 < q) : lower q < 2 := by
  have hq' : 0 < (q : Rat) := (Rat.natCast_pos).mpr hq
  have hp := Rat.inv_pos.mpr (by grind : 0 < (q : Rat)+1)
  have hi := Rat.mul_inv_cancel ((q : Rat)+1) (by grind)
  have hh := Rat.mul_pos hq' hp
  unfold lower
  rw [Rat.div_def]
  grind only

theorem lower_coefficient_pos {q : Nat} (hq : 0 < q) (k : Nat) : 0 < coefficient (lower q) k := by
  induction k with
  | zero => exact (by decide : (0 : Rat) < 1)
  | succ k ih =>
    have hk := Rat.natCast_nonneg (a := k)
    have ha := lower_lt_two hq
    rw [coefficient, Rat.div_def]
    exact Rat.mul_pos (Rat.mul_pos ih (by grind)) (Rat.inv_pos.mpr (by grind))

theorem bound_pos (m : Nat) : 0 < bound m :=
  Rat.pow_pos (by have := Rat.natCast_nonneg (a := m); grind)

/-- Comparison with one positive binomial sequence bounds every exponent in the chart. -/
theorem coefficient_comparison {q m : Nat} {s : Rat} (hq : 0 < q) (hs : InChart q m s)
    (k : Nat) (hk : m+1 ≤ k) :
    magnitude s k*coefficient (lower q) (m+1) ≤ bound m*coefficient (lower q) k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction i with
  | zero =>
    have h := Rat.mul_le_mul_of_nonneg_right (magnitude_bound hs (m+1))
      (Rat.le_of_lt (lower_coefficient_pos hq (m+1)))
    simpa only [Nat.add_zero] using h
  | succ i ih =>
    let k := m+1+i
    have hn : 0 < (k : Rat)+1 := by have := Rat.natCast_nonneg (a := k); grind
    have hn0 : 0 ≤ (k : Rat)+2-s := by
      have hkm : (m : Rat)+1 ≤ (k : Rat) := by dsimp [k]; simp only [Rat.natCast_add]; have := Rat.natCast_nonneg (a := i); grind
      have := hs.2; grind
    have h1 := magnitude_step hs.2 (show m+1 ≤ k by dsimp [k]; omega)
    have h2 := coefficient_step (lower q) k
    have hi := Rat.mul_le_mul_of_nonneg_left ih hn0
    have hparam := Rat.mul_le_mul_of_nonneg_right hs.1
      (Rat.mul_nonneg (Rat.le_of_lt (bound_pos m)) (Rat.le_of_lt (lower_coefficient_pos hq k)))
    have he1 := congrArg (fun z : Rat => z*coefficient (lower q) (m+1)) h1
    have he2 := congrArg (fun z : Rat => z*bound m) h2
    change magnitude s (k+1)*coefficient (lower q) (m+1) ≤ bound m*coefficient (lower q) (k+1)
    apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) ?_ hn
    change magnitude s k*coefficient (lower q) (m+1) ≤ _ at ih
    change ((k : Rat)+2-s)*(magnitude s k*coefficient (lower q) (m+1)) ≤ _ at hi
    change lower q*(bound m*coefficient (lower q) k) ≤ s*(bound m*coefficient (lower q) k) at hparam
    grind only

/-- Computed uniform outer-tail budget, sharper than its geometric termination bound. -/
def outerBudget (q m K : Nat) : Rat :=
  (2*((q : Rat)+1)*bound m/coefficient (lower q) (m+1))*coefficient (lower q) K

theorem outerBudget_nonneg {q : Nat} (hq : 0 < q) (m K : Nat) : 0 ≤ outerBudget q m K := by
  unfold outerBudget
  rw [Rat.div_def]
  exact Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (by have := Rat.natCast_nonneg (a := q); grind) (Rat.le_of_lt (bound_pos m)))
    (Rat.le_of_lt (Rat.inv_pos.mpr (lower_coefficient_pos hq (m+1)))))
    (Rat.le_of_lt (lower_coefficient_pos hq K))

theorem outerBudget_covers {q m : Nat} {s : Rat} (hq : 0 < q) (hs : InChart q m s)
    {K : Nat} (hK : m+1 ≤ K) : 2*((q : Rat)+1)*magnitude s K ≤ outerBudget q m K := by
  have h := coefficient_comparison hq hs K hK
  have hp := lower_coefficient_pos hq (m+1)
  have hi := Rat.mul_inv_cancel (coefficient (lower q) (m+1)) (Rat.ne_of_gt hp)
  have hm := Rat.mul_le_mul_of_nonneg_left h
    (Rat.mul_nonneg (by have := Rat.natCast_nonneg (a := q); grind : 0 ≤ 2*((q : Rat)+1))
      (Rat.le_of_lt (Rat.inv_pos.mpr hp)))
  unfold outerBudget
  rw [Rat.div_def]
  have he : 2*((q : Rat)+1)*(coefficient (lower q) (m+1))⁻¹ *
      (magnitude s K*coefficient (lower q) (m+1)) = 2*((q : Rat)+1)*magnitude s K := by
    calc
      _ = (2*((q : Rat)+1)*magnitude s K) *
          (coefficient (lower q) (m+1)*(coefficient (lower q) (m+1))⁻¹) := by grind only
      _ = _ := by rw [hi, Rat.mul_one]
  rw [he] at hm
  calc
    _ ≤ _ := hm
    _ = _ := by grind only

private theorem ratio_decay_weighted (q j : Nat) :
    ratio q^j*(2*(q : Rat)+3+(j : Rat)) ≤ 2*(q : Rat)+3 := by
  have hq := Rat.natCast_nonneg (a := q)
  have hr := (ratio_bounds q).1
  have he : ratio q*(2*(q : Rat)+3)=2*(q : Rat)+2 := by
    have hi := Rat.mul_inv_cancel (2*(q : Rat)+3) (by grind)
    unfold ratio; rw [Rat.div_def]; grind only
  induction j with
  | zero => simp only [Rat.pow_zero]; grind
  | succ j ih =>
    have hj := Rat.natCast_nonneg (a := j)
    have hsmall : ratio q*(2*(q : Rat)+3+((j : Rat)+1)) ≤ 2*(q : Rat)+3+(j : Rat) := by
      have ht := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt (ratio_bounds q).2) (by grind : 0 ≤ (j : Rat)+1)
      grind only
    have h := Rat.mul_le_mul_of_nonneg_left hsmall (Rat.pow_nonneg (n := j) hr)
    simp only [Rat.pow_succ, Rat.natCast_add]
    grind only

theorem ratio_shrinks (q : Nat) (C : Rat) (hC : 0 ≤ C) : ShrinksToZero (fun j => C*ratio q^j) := by
  let D := 2*(q : Rat)+3
  let A := RationalMajorant.factorialTailStart (C*D)+1
  have hA : C*D ≤ (A : Rat) := by
    have h := RationalMajorant.factorialTailStart_satisfies (C*D)
    have ha := Rat.natCast_nonneg (a := A)
    change C*D ≤ (A : Rat)/2 at h
    grind
  apply shrinksToZero_of_natOverSuccBound (C := A)
  intro j
  have hj := Rat.natCast_nonneg (a := j)
  have hq := Rat.natCast_nonneg (a := q)
  have hb := ratio_decay_weighted q j
  have hp := Rat.pow_nonneg (n := j) (ratio_bounds q).1
  have hsmall : ratio q^j*((j : Rat)+1) ≤ D := by
    have hle : (j : Rat)+1 ≤ 2*(q : Rat)+3+(j : Rat) := by grind
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hle hp) hb
  have hh := Rat.mul_le_mul_of_nonneg_left hsmall hC
  have hi := Rat.mul_inv_cancel ((j : Rat)+1) (by grind)
  apply Rat.le_of_mul_le_mul_right (c := (j : Rat)+1) ?_ (by grind)
  simp only [Rat.natCast_add]
  change C*ratio q^j*((j : Rat)+1) ≤ (A : Rat)/((j : Rat)+1)*((j : Rat)+1)
  simp only [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel ((j : Rat)+1) (by grind : (j : Rat)+1 ≠ 0), Rat.mul_one]
  exact Rat.le_trans hh hA

theorem outerBudget_dyadic_shrinks {q : Nat} (hq : 0 < q) (m : Nat) :
    ShrinksToZero (fun j => outerBudget q m (cutoff m j)) := by
  let C := 2*((q : Rat)+1)*bound m/coefficient (lower q) (m+1)
  have hC : 0 ≤ C := by
    dsimp [C]; rw [Rat.div_def]
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by have := Rat.natCast_nonneg (a := q); grind) (Rat.le_of_lt (bound_pos m)))
      (Rat.le_of_lt (Rat.inv_pos.mpr (lower_coefficient_pos hq (m+1))))
  have decay (j : Nat) : outerBudget q m (cutoff m j) ≤ (C*bound m)*ratio q^j := by
    have h := magnitude_decay (lower_chart q m) j
    rw [magnitude, qabs_eq_self_of_nonneg (Rat.le_of_lt (lower_coefficient_pos hq _))] at h
    have hh := Rat.mul_le_mul_of_nonneg_left h hC
    change C*coefficient (lower q) (cutoff m j) ≤ _
    grind only
  intro eps
  obtain ⟨N,hN⟩ := ratio_shrinks q (C*bound m) (Rat.mul_nonneg hC (Rat.le_of_lt (bound_pos m))) eps
  exact ⟨N, fun j hj => Rat.le_trans (decay j) (hN j hj)⟩

/-- A terminating search whose proof affects termination only, not its rational tests. -/
def firstWitness (p : Nat → Prop) [DecidablePred p] (hex : ∃ N, ∀ n, N ≤ n → p n) (n : Nat := 0) : Subtype p :=
  if h : p n then ⟨n,h⟩ else firstWitness p hex (n+1)
termination_by (Classical.choose hex)-n
decreasing_by
  have hspec := Classical.choose_spec hex
  have hn : n < Classical.choose hex := by
    by_cases hn : n < Classical.choose hex
    · exact hn
    · have hle : Classical.choose hex ≤ n := by omega
      exact False.elim (h (hspec n hle))
  omega

/-- Each of the two truncations receives this budget. -/
def budget (n : Nat) : QPos := ⟨1/(32*((n : Rat)+1)), by
  have h := Rat.natCast_nonneg (a := n)
  rw [Rat.div_def]
  exact Rat.mul_pos (by decide) (Rat.inv_pos.mpr (by grind))⟩

def outerCutoff (q m : Nat) (hq : 0 < q) (n : Nat) : Nat :=
  cutoff m (firstWitness (fun j => outerBudget q m (cutoff m j) ≤ (budget n).val)
    (outerBudget_dyadic_shrinks hq m (budget n))).val

theorem outerCutoff_ge (q m : Nat) (hq : 0 < q) (n : Nat) : m+1 ≤ outerCutoff q m hq n := cutoff_ge _ _

theorem outerCutoff_budget (q m : Nat) (hq : 0 < q) (n : Nat) :
    outerBudget q m (outerCutoff q m hq n) ≤ (budget n).val :=
  (firstWitness (fun j => outerBudget q m (cutoff m j) ≤ (budget n).val)
    (outerBudget_dyadic_shrinks hq m (budget n))).property

/-- Search the second cutoff too; the bound proves termination independently of execution. -/
def innerCutoff (m K n : Nat) : Nat :=
  (firstWitness (fun j => (K : Rat)*bound m/((j+1 : Nat) : Rat) ≤ (budget n).val)
    (shrinksToZero_of_natOverSuccBound (C := K*(m+3)^(m+1)) (fun j => by
      simp only [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_add]
      exact Rat.le_refl) (budget n))).val+1

theorem innerCutoff_pos (m K n : Nat) : 0 < innerCutoff m K n := Nat.zero_lt_succ _

theorem innerCutoff_budget (m K n : Nat) :
    (K : Rat)*bound m/(innerCutoff m K n : Rat) ≤ (budget n).val :=
  (firstWitness (fun j => (K : Rat)*bound m/((j+1 : Nat) : Rat) ≤ (budget n).val)
    (shrinksToZero_of_natOverSuccBound (C := K*(m+3)^(m+1)) (fun j => by
      simp only [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_add]
      exact Rat.le_refl) (budget n))).property

theorem budget_antitone {k n : Nat} (hkn : k ≤ n) : (budget n).val ≤ (budget k).val := by
  have hcast := Rat.natCast_le_natCast.mpr hkn
  have hk := Rat.natCast_nonneg (a := k)
  have hn := Rat.natCast_nonneg (a := n)
  have ha : 0 < 32*((k : Rat)+1) := by grind
  have hb : 0 < 32*((n : Rat)+1) := by grind
  have hia := Rat.mul_inv_cancel (32*((k : Rat)+1)) (Rat.ne_of_gt ha)
  have hib := Rat.mul_inv_cancel (32*((n : Rat)+1)) (Rat.ne_of_gt hb)
  apply Rat.le_of_mul_le_mul_right (c := (32*((k : Rat)+1))*(32*((n : Rat)+1))) ?_ (Rat.mul_pos ha hb)
  dsimp [budget]
  simp only [Rat.div_def, Rat.one_mul]
  calc
    _ = 32*((k : Rat)+1) := by
      calc
        _ = (32*((k : Rat)+1))*((32*((n : Rat)+1))*(32*((n : Rat)+1))⁻¹) := by grind only
        _ = _ := by rw [hib, Rat.mul_one]
    _ ≤ 32*((n : Rat)+1) := by grind
    _ = _ := by
      calc
        _ = (32*((n : Rat)+1))*((32*((k : Rat)+1))*(32*((k : Rat)+1))⁻¹) := by rw [hia, Rat.mul_one]
        _ = _ := by grind only

end ComputableAnalysis.ZetaReal
