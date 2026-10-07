import ComputableAnalysis.RepresentedPolynomial
import ComputableAnalysis.FiniteFTASubdivision

/-! From rational dyadic enclosures to an exact represented root.
The subdivision law proves nesting, validity, and an explicit geometric width
bound. Existence of a branch retaining zero is a separate FTA obligation. -/
namespace ComputableAnalysis.RepresentedPolynomial

open FiniteFTASubdivision

theorem dyadic_ordered (boxes : Nat → QBox) (h0 : (boxes 0).Ordered)
    (hstep : ∀ n, boxes (n+1) ∈ dyadicChildren (boxes n)) :
    ∀ n, (boxes n).Ordered := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact dyadicChildren_ordered ih _ (hstep n)

theorem dyadic_nested (boxes : Nat → QBox) (h0 : (boxes 0).Ordered)
    (hstep : ∀ n, boxes (n+1) ∈ dyadicChildren (boxes n))
    (n m : Nat) (hnm : n ≤ m) : (boxes m).NestedIn (boxes n) := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | succ m ih =>
      by_cases h : n ≤ m
      · have hprev := ih h
        have hnext := dyadicChildren_nested (dyadic_ordered boxes h0 hstep m) _ (hstep m)
        exact ⟨QComplex.le_trans hprev.1 hnext.1,
          QComplex.le_trans hnext.2 hprev.2⟩
      · have hn : n = m+1 := by omega
        subst n
        exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩

theorem dyadic_size (boxes : Nat → QBox) (h0 : (boxes 0).Ordered)
    (hstep : ∀ n, boxes (n+1) ∈ dyadicChildren (boxes n)) (n : Nat) :
    (boxes n).width = (boxes 0).width / ((2^n : Nat) : Rat) ∧
      (boxes n).height = (boxes 0).height / ((2^n : Nat) : Rat) := by
  induction n with
  | zero => simp [Nat.pow_zero, Rat.div_def, show (1 : Rat)⁻¹ = 1 by decide +kernel] <;> grind
  | succ n ih =>
      have hn := dyadicChildren_width_height (dyadic_ordered boxes h0 hstep n) _ (hstep n)
      rw [hn.1, hn.2, ih.1, ih.2]
      have hpow : ((2^(n+1) : Nat) : Rat) = ((2^n : Nat) : Rat) * 2 := by
        exact_mod_cast (Nat.pow_succ 2 n)
      rw [hpow]
      constructor <;> simp only [Rat.div_def, Rat.inv_mul_rev] <;> grind

theorem dyadic_scale_shrinks (a : Rat) (ha : 0 ≤ a) :
    ShrinksToZero (fun n => a / ((2^n : Nat) : Rat)) := by
  apply shrinksToZero_of_natOverSuccBound (C := a.num.natAbs + 1)
  intro n
  have hapos : a ≤ ((a.num.natAbs + 1 : Nat) : Rat) := by
    have hden : (0 : Rat) < (a.den : Rat) :=
      Rat.natCast_pos.mpr (Nat.pos_of_ne_zero a.den_nz)
    apply Rat.le_of_mul_le_mul_right (c := (a.den : Rat))
    · rw [Rat.mul_comm a _, rat_den_mul_self]
      have hnum : (a.num : Rat) ≤ ((a.num.natAbs : Nat) : Rat) := by
        exact_mod_cast (show a.num ≤ (a.num.natAbs : Int) from Int.le_natAbs)
      have hnat : a.num.natAbs ≤ (a.num.natAbs + 1) * a.den := by
        have hd := Nat.pos_of_ne_zero a.den_nz
        have hm := Nat.le_mul_of_pos_right (a.num.natAbs + 1) hd
        omega
      exact Rat.le_trans hnum (by exact_mod_cast hnat)
    · exact hden
  have hpower : (((n+1 : Nat) : Rat)) ≤ ((2^n : Nat) : Rat) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n))
  have hnp : (0 : Rat) < ((n+1 : Nat) : Rat) :=
    Rat.natCast_pos.mpr (by omega)
  have hinv := QInterval.one_div_le_one_div_of_pos hnp hpower
  calc
    a / ((2^n : Nat) : Rat) ≤ a / ((n+1 : Nat) : Rat) := by
      simpa only [Rat.div_def, Rat.one_mul] using Rat.mul_le_mul_of_nonneg_left hinv ha
    _ ≤ ((a.num.natAbs + 1 : Nat) : Rat) / ((n+1 : Nat) : Rat) := by
      exact Rat.mul_le_mul_of_nonneg_right hapos (Rat.le_of_lt (Rat.inv_pos.mpr hnp))

theorem dyadic_valid (boxes : Nat → QBox) (h0 : (boxes 0).Ordered)
    (hstep : ∀ n, boxes (n+1) ∈ dyadicChildren (boxes n)) :
    ComplexRaw.ValidCompute boxes := by
  constructor
  · intro n
    exact (QBox.ordered_iff_width_height_nonneg _).1 (dyadic_ordered boxes h0 hstep n)
  · constructor
    · intro n m hnm
      have h := dyadic_nested boxes h0 hstep n m hnm
      exact ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩
    · intro eps
      have hnonneg := (QBox.ordered_iff_width_height_nonneg _).1 h0
      obtain ⟨N, hN⟩ := dyadic_scale_shrinks _ hnonneg.1 eps
      obtain ⟨M, hM⟩ := dyadic_scale_shrinks _ hnonneg.2 eps
      refine ⟨max N M, fun n hn => ?_⟩
      rw [(dyadic_size boxes h0 hstep n).1, (dyadic_size boxes h0 hstep n).2]
      exact ⟨hN n (by omega), hM n (by omega)⟩

/-- A branch of shrinking rational boxes defines the represented number
itself. Validity and the convergence rate are derived, not supplied. -/
def dyadicValue (boxes : Nat → QBox) (h0 : (boxes 0).Ordered)
    (hstep : ∀ n, boxes (n+1) ∈ dyadicChildren (boxes n)) : ComplexCert :=
  ⟨{ compute := boxes }, dyadic_valid boxes h0 hstep⟩

theorem root_of_dyadic_enclosures (p : Coefficients) (boxes : Nat → QBox)
    (h0 : (boxes 0).Ordered)
    (hstep : ∀ n, boxes (n+1) ∈ dyadicChildren (boxes n))
    (hzero : ∀ n, QBox.Overlaps
      (evalBox (p.map (fun a => a.raw.compute n)) (boxes n)) QBox.zero) :
    Root p (dyadicValue boxes h0 hstep) :=
  root_of_enclosures p boxes (dyadic_valid boxes h0 hstep) hzero

end ComputableAnalysis.RepresentedPolynomial
