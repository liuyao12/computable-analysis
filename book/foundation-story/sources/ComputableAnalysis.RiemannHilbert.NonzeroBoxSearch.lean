import ComputableAnalysis.RiemannHilbert.BoxApproximation

/-! Executable search for a separated box at every nonzero represented
complex value. Separation and a positive squared-coordinate lower bound
are derived from nonzero value equality and rational interval nesting. -/
namespace ComputableAnalysis.RiemannHilbert.NonzeroBoxSearch
open ComplexRaw FunctionTheory

def Nonzero (z : Scalar) : Prop := ¬ z.val.Equiv zero

theorem nonzero_congr (z w : Scalar) (hzw : z.val.Equiv w.val) : Nonzero z ↔ Nonzero w := by
  constructor
  · intro hz hw
    exact hz (equiv_trans z.property w.property (ofQComplex_valid _) hzw hw)
  · intro hw hz
    exact hw (equiv_trans w.property z.property (ofQComplex_valid _) (equiv_symm hzw) hz)

def separated (B : QBox) : Prop := 0 < B.lo.re ∨ B.hi.re < 0 ∨ 0 < B.lo.im ∨ B.hi.im < 0
instance (B : QBox) : Decidable (separated B) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem exists_separated (z : Scalar) (hz : Nonzero z) : ∃ k, separated (z.val.compute k) := by
  classical
  apply Classical.byContradiction
  intro hnone
  apply hz
  intro k
  apply (compareAt_overlap_iff z.val zero k k).2
  have hk : ¬ separated (z.val.compute k) := fun h => hnone ⟨k,h⟩
  change ((z.val.compute k).lo.re ≤ 0 ∧ (z.val.compute k).lo.im ≤ 0) ∧
    (0 ≤ (z.val.compute k).hi.re ∧ 0 ≤ (z.val.compute k).hi.im)
  unfold separated at hk
  grind

theorem separated_later (z : Scalar) (k n : Nat) (hkn : k ≤ n) (hk : separated (z.val.compute k)) :
    separated (z.val.compute n) := by
  rcases valid_nestedIn z.property hkn with ⟨hnl,hnh⟩
  change (z.val.compute k).lo.re ≤ (z.val.compute n).lo.re ∧
    (z.val.compute k).lo.im ≤ (z.val.compute n).lo.im at hnl
  change (z.val.compute n).hi.re ≤ (z.val.compute k).hi.re ∧
    (z.val.compute n).hi.im ≤ (z.val.compute k).hi.im at hnh
  unfold separated at hk ⊢
  grind

def good (z : Scalar) (k : Nat) : Bool := decide (separated (z.val.compute k))

theorem eventually_good (z : Scalar) (hz : Nonzero z) : ∃ k, ∀ n, k ≤ n → good z n = true := by
  obtain ⟨k,hk⟩ := exists_separated z hz
  exact ⟨k, fun n hkn => by simp only [good, decide_eq_true_eq]; exact separated_later z k n hkn hk⟩

def stage (z : Scalar) (hz : Nonzero z) : Nat :=
  PrecisionSearch.firstFrom (good z) (eventually_good z hz) 0

theorem stage_spec (z : Scalar) (hz : Nonzero z) : separated (z.val.compute (stage z hz)) := by
  have h := (PrecisionSearch.firstFrom_spec (good z) (eventually_good z hz) 0).2
  simpa only [stage, good, decide_eq_true_eq] using h

def margin (B : QBox) : Rat :=
  if 0 < B.lo.re then B.lo.re
  else if B.hi.re < 0 then -B.hi.re
  else if 0 < B.lo.im then B.lo.im
  else -B.hi.im

theorem margin_pos (B : QBox) (hB : separated B) : 0 < margin B := by
  unfold margin
  split
  · assumption
  · split
    · grind
    · split
      · assumption
      · unfold separated at hB
        grind

private theorem square_mono {s t : Rat} (hs : 0 ≤ s) (hst : s ≤ t) : s*s ≤ t*t := by
  have ht := Rat.le_trans hs hst
  have h1 := Rat.mul_le_mul_of_nonneg_left hst hs
  have h2 := Rat.mul_le_mul_of_nonneg_right hst ht
  grind

theorem normSq_lower (B : QBox) (hB : separated B) (c : QComplex)
    (hc : B.lo ≤ c ∧ c ≤ B.hi) : margin B * margin B ≤ QComplex.normSq c := by
  have hre := rat_square_nonneg_basic c.re
  have him := rat_square_nonneg_basic c.im
  change (B.lo.re ≤ c.re ∧ B.lo.im ≤ c.im) ∧ (c.re ≤ B.hi.re ∧ c.im ≤ B.hi.im) at hc
  unfold margin
  split
  · have h := square_mono (Rat.le_of_lt ‹0 < B.lo.re›) hc.1.1
    unfold QComplex.normSq
    grind
  · split
    · have h := square_mono (s := -B.hi.re) (t := -c.re) (by grind) (Rat.neg_le_neg hc.2.1)
      unfold QComplex.normSq
      grind
    · split
      · have h := square_mono (Rat.le_of_lt ‹0 < B.lo.im›) hc.1.2
        unfold QComplex.normSq
        grind
      · have hneg : B.hi.im < 0 := by unfold separated at hB; grind
        have h := square_mono (s := -B.hi.im) (t := -c.im) (by grind) (Rat.neg_le_neg hc.2.2)
        unfold QComplex.normSq
        grind

theorem center_normSq_lower (z : Scalar) (k n : Nat) (hkn : k ≤ n) (hk : separated (z.val.compute k)) :
    margin (z.val.compute k) * margin (z.val.compute k) ≤ QComplex.normSq (z.val.compute n).center := by
  have hc := QBox.center_mem (valid_ordered z.property n)
  have hn := valid_nestedIn z.property hkn
  exact normSq_lower (z.val.compute k) hk (z.val.compute n).center
    ⟨QComplex.le_trans hn.1 hc.1, QComplex.le_trans hc.2 hn.2⟩

end ComputableAnalysis.RiemannHilbert.NonzeroBoxSearch
