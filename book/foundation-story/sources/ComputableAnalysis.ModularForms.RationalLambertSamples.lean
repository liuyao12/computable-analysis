import ComputableAnalysis.ModularForms.RationalLambertArithmetic
import ComputableAnalysis.ModularForms.RationalLambertBounds

/-! Primary rational Lambert-series samplers. Their runtime sees only one
rational chart point and exact finite rational sums with certified tails. -/
namespace ComputableAnalysis.ModularForms.RationalLambert
open ComplexRaw FunctionTheory RiemannHilbert

private def rationalTail (n : Nat) : Rat := 8*((1:Rat)/2)^n

private theorem rationalTail_shrinks : ShrinksToZero rationalTail := by
  change ShrinksToZero (fun n => 8*((1:Rat)/2)^n)
  simpa only [show (4:Rat)*2=8 by decide +kernel] using
    LocalODE.tail_bound_shrinks 2 (1/2) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem rationalTail_antitone (m n : Nat) (hmn : m≤n) : rationalTail n≤rationalTail m := by
  have hp : ∀ d : Nat, ((1:Rat)/2)^(m+d)≤((1:Rat)/2)^m := by
    intro d
    induction d with
    | zero => simp only [Nat.add_zero]; exact Rat.le_refl
    | succ d ih =>
      rw [Nat.add_succ,Rat.pow_succ]
      exact Rat.le_trans (by
        have h := Rat.mul_le_mul_of_nonneg_left (by decide +kernel : (1/2:Rat)≤1)
          (Rat.pow_nonneg (n := m+d) (by decide +kernel : (0:Rat)≤1/2))
        simpa only [Rat.mul_one] using h) ih
  have h := hp (n-m)
  rw [Nat.add_sub_cancel' hmn] at h
  exact Rat.mul_le_mul_of_nonneg_left h (by decide +kernel)

private theorem rational_close (q : QComplex) (hq : Small (ofQComplex q) ((1:Rat)/64))
    (k : Nat) (hk : k=1 ∨ k=3 ∨ k=5) (n : Nat) :
    Small (sub (comparison (point q) hq k).val (ofQComplex (finitePrefix q k n))) (rationalTail n) :=
  Small.congr (sub_valid (comparison (point q) hq k).property
    (ScalarSeries.block_valid _ (weightedLambertTerm_valid (point q) (1/64) k (by decide +kernel) (by decide +kernel) hq) 0 n))
    (sub_valid (comparison (point q) hq k).property (ofQComplex_valid _))
    (FunctionTheory.sub_congr (equiv_refl _ (comparison (point q) hq k).property) (prefix_agrees q hq k n))
    (comparison_tail (point q) hq k hk n)

private theorem rational_cauchy (q : QComplex) (hq : Small (ofQComplex q) ((1:Rat)/64))
    (k : Nat) (hk : k=1 ∨ k=3 ∨ k=5) (m n : Nat) (hmn : m≤n) :
    Small (sub (ofQComplex (finitePrefix q k n)) (ofQComplex (finitePrefix q k m))) (2*rationalTail m) := by
  have h := triangle _ _ _ (ofQComplex_valid _) (comparison (point q) hq k).property (ofQComplex_valid _)
    _ _ (RepresentedCauchySum.small_sub_symm _ _ _ (rational_close q hq k hk n)) (rational_close q hq k hk m)
  exact h.mono (by have := rationalTail_antitone m n hmn; grind only)

def rationalValue (q : QComplex) : Nat → ComplexRaw := fun k =>
  RepresentedCauchySum.value (fun n => ofQComplex (finitePrefix q k n)) (fun _ => ofQComplex_valid _)
    (fun n => 2*rationalTail n)

theorem rationalValue_valid (q : QComplex) (hq : Small (ofQComplex q) ((1:Rat)/64))
    (k : Nat) (hk : k=1 ∨ k=3 ∨ k=5) : (rationalValue q k).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (RepresentedCauchySum.twice_shrinks _ rationalTail_shrinks)
    (rational_cauchy q hq k hk)

theorem rationalValue_agrees (q : QComplex) (hq : Small (ofQComplex q) ((1:Rat)/64))
    (k : Nat) (hk : k=1 ∨ k=3 ∨ k=5) : (rationalValue q k).Equiv (comparison (point q) hq k).val := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun n => 3*rationalTail n)
    (SeriesLimitLaws.shrinks_scale _ rationalTail_shrinks 3 (by decide +kernel))
  intro n
  have hv := RepresentedCauchySum.value_close_prefix (fun n => ofQComplex (finitePrefix q k n))
    (fun _ => ofQComplex_valid _) (fun n => 2*rationalTail n) (rational_cauchy q hq k hk) n
  have hb := triangle _ _ _ (rationalValue_valid q hq k hk) (ofQComplex_valid _) (comparison (point q) hq k).property
    _ _ hv (RepresentedCauchySum.small_sub_symm _ _ _ (rational_close q hq k hk n))
  exact hb.mono (by grind only)

end ComputableAnalysis.ModularForms.RationalLambert
