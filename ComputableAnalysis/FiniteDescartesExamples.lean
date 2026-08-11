import ComputableAnalysis.PolynomialDescartes

/-!
# Finite Descartes examples

This module records an exact two-variation polynomial example.  It is a
finite root-set certificate, not the general real-root-counting theorem.
-/

namespace ComputableAnalysis

namespace Polynomial

def twoVariationQuadratic : List Rat := [2, -3, 1]

theorem twoVariationQuadratic_eval (x : Rat) :
    eval twoVariationQuadratic x = (x - 1) * (x - 2) := by
  simp [twoVariationQuadratic, eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem twoVariationQuadratic_sign_count :
    signChangeCountIgnoringZeros twoVariationQuadratic = 2 := by
  native_decide

theorem twoVariationQuadratic_positive_root_iff (x : Rat) :
    0 < x -> (eval twoVariationQuadratic x = 0 ↔ x = 1 ∨ x = 2) := by
  intro hx
  rw [twoVariationQuadratic_eval]
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with hleft | hright
    · left
      grind
    · right
      grind
  · intro h
    rcases h with rfl | rfl <;> native_decide

theorem twoVariationQuadratic_certificate :
    signChangeCountIgnoringZeros twoVariationQuadratic = 2 /\
      (forall x : Rat, 0 < x ->
        (eval twoVariationQuadratic x = 0 ↔ x = 1 ∨ x = 2)) := by
  constructor
  · exact twoVariationQuadratic_sign_count
  · intro x hx
    exact twoVariationQuadratic_positive_root_iff x hx

def threeVariationCubic : List Rat := [-6, 11, -6, 1]

theorem threeVariationCubic_eval (x : Rat) :
    eval threeVariationCubic x = (x - 1) * (x - 2) * (x - 3) := by
  simp [threeVariationCubic, eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem threeVariationCubic_sign_count :
    signChangeCountIgnoringZeros threeVariationCubic = 3 := by
  native_decide

theorem threeVariationCubic_positive_root_iff (x : Rat) :
    0 < x -> (eval threeVariationCubic x = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3) := by
  intro hx
  rw [threeVariationCubic_eval]
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h12 | h3
    · rcases Rat.mul_eq_zero.mp h12 with h1 | h2
      · left
        grind
      · right
        left
        grind
    · right
      right
      grind
  · intro h
    rcases h with rfl | rfl | rfl <;> native_decide

theorem threeVariationCubic_certificate :
    signChangeCountIgnoringZeros threeVariationCubic = 3 /\
      (forall x : Rat, 0 < x ->
        (eval threeVariationCubic x = 0 ↔
          x = 1 ∨ x = 2 ∨ x = 3)) := by
  constructor
  · exact threeVariationCubic_sign_count
  · intro x hx
    exact threeVariationCubic_positive_root_iff x hx

end Polynomial

end ComputableAnalysis
