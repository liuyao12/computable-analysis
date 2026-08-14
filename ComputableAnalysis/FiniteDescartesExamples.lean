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

def fourVariationQuartic : List Rat := [24, -50, 35, -10, 1]

theorem fourVariationQuartic_eval (x : Rat) :
    eval fourVariationQuartic x =
      (x - 1) * (x - 2) * (x - 3) * (x - 4) := by
  simp [fourVariationQuartic, eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem fourVariationQuartic_sign_count :
    signChangeCountIgnoringZeros fourVariationQuartic = 4 := by
  native_decide

theorem fourVariationQuartic_positive_root_iff (x : Rat) :
    0 < x -> (eval fourVariationQuartic x = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4) := by
  intro hx
  rw [fourVariationQuartic_eval]
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h123 | h4
    · rcases Rat.mul_eq_zero.mp h123 with h12 | h3
      · rcases Rat.mul_eq_zero.mp h12 with h1 | h2
        · left
          grind
        · right
          left
          grind
      · right
        right
        left
        grind
    · right
      right
      right
      grind
  · intro h
    rcases h with rfl | rfl | rfl | rfl <;> native_decide

theorem fourVariationQuartic_certificate :
    signChangeCountIgnoringZeros fourVariationQuartic = 4 /\
      (forall x : Rat, 0 < x ->
        (eval fourVariationQuartic x = 0 ↔
          x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4)) := by
  constructor
  · exact fourVariationQuartic_sign_count
  · intro x hx
    exact fourVariationQuartic_positive_root_iff x hx

def fiveVariationQuintic : List Rat := [-120, 274, -225, 85, -15, 1]

theorem fiveVariationQuintic_eval (x : Rat) :
    eval fiveVariationQuintic x =
      (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5) := by
  simp [fiveVariationQuintic, eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem fiveVariationQuintic_sign_count :
    signChangeCountIgnoringZeros fiveVariationQuintic = 5 := by
  native_decide

theorem fiveVariationQuintic_positive_root_iff (x : Rat) :
    0 < x -> (eval fiveVariationQuintic x = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5) := by
  intro hx
  rw [fiveVariationQuintic_eval]
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h1234 | h5
    · rcases Rat.mul_eq_zero.mp h1234 with h123 | h4
      · rcases Rat.mul_eq_zero.mp h123 with h12 | h3
        · rcases Rat.mul_eq_zero.mp h12 with h1 | h2
          · left
            grind
          · right
            left
            grind
        · right
          right
          left
          grind
      · right
        right
        right
        left
        grind
    · right
      right
      right
      right
      grind
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem fiveVariationQuintic_certificate :
    signChangeCountIgnoringZeros fiveVariationQuintic = 5 /\
      (forall x : Rat, 0 < x ->
        (eval fiveVariationQuintic x = 0 ↔
          x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5)) := by
  constructor
  · exact fiveVariationQuintic_sign_count
  · intro x hx
    exact fiveVariationQuintic_positive_root_iff x hx

def sixVariationSextic : List Rat := [720, -1764, 1624, -735, 175, -21, 1]

theorem sixVariationSextic_eval (x : Rat) :
    eval sixVariationSextic x =
      (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5) * (x - 6) := by
  simp [sixVariationSextic, eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem sixVariationSextic_sign_count :
    signChangeCountIgnoringZeros sixVariationSextic = 6 := by
  native_decide

theorem sixVariationSextic_positive_root_iff (x : Rat) :
    0 < x -> (eval sixVariationSextic x = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6) := by
  intro hx
  rw [sixVariationSextic_eval]
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h12345 | h6
    · rcases Rat.mul_eq_zero.mp h12345 with h1234 | h5
      · rcases Rat.mul_eq_zero.mp h1234 with h123 | h4
        · rcases Rat.mul_eq_zero.mp h123 with h12 | h3
          · rcases Rat.mul_eq_zero.mp h12 with h1 | h2
            · left
              grind
            · right
              left
              grind
          · right
            right
            left
            grind
        · right
          right
          right
          left
          grind
      · right
        right
        right
        right
        left
        grind
    · right
      right
      right
      right
      right
      grind
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem sixVariationSextic_certificate :
    signChangeCountIgnoringZeros sixVariationSextic = 6 /\
      (forall x : Rat, 0 < x ->
        (eval sixVariationSextic x = 0 ↔
          x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6)) := by
  constructor
  · exact sixVariationSextic_sign_count
  · intro x hx
    exact sixVariationSextic_positive_root_iff x hx

def oneVariationQuadratic : List Rat := [1, -2, -1]

theorem oneVariationQuadratic_sign_count :
    signChangeCountIgnoringZeros oneVariationQuadratic = 1 := by
  native_decide

theorem oneVariationQuadratic_endpoint_bracket :
    0 < eval oneVariationQuadratic (3 / 8) /\
      eval oneVariationQuadratic (1 / 2) < 0 := by
  native_decide

theorem oneVariationQuadratic_unique_positive_root
    {x y : Rat} (hx : 0 < x) (hy : 0 < y)
    (hxroot : eval oneVariationQuadratic x = 0)
    (hyroot : eval oneVariationQuadratic y = 0) :
    x = y := by
  have hcert := one_positive_variation_certificate
    (a := 1) (tail := [-2, -1]) (by native_decide)
    (by
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · native_decide
      · native_decide
      · simp at hc)
    (by exact ⟨-2, by simp, by native_decide⟩)
  apply hcert.2 x y hx hy
  · simpa [oneVariationQuadratic] using hxroot
  · simpa [oneVariationQuadratic] using hyroot

def sevenVariationSeptic : List Rat :=
  [-5040, 13068, -13132, 6769, -1960, 322, -28, 1]

theorem sevenVariationSeptic_eval (x : Rat) :
    eval sevenVariationSeptic x =
      (x - 1) * (x - 2) * (x - 3) * (x - 4) *
        (x - 5) * (x - 6) * (x - 7) := by
  simp [sevenVariationSeptic, eval]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem sevenVariationSeptic_sign_count :
    signChangeCountIgnoringZeros sevenVariationSeptic = 7 := by
  native_decide

theorem sevenVariationSeptic_positive_root_iff (x : Rat) :
    0 < x -> (eval sevenVariationSeptic x = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7) := by
  intro hx
  rw [sevenVariationSeptic_eval]
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h123456 | h7
    · rcases Rat.mul_eq_zero.mp h123456 with h12345 | h6
      · rcases Rat.mul_eq_zero.mp h12345 with h1234 | h5
        · rcases Rat.mul_eq_zero.mp h1234 with h123 | h4
          · rcases Rat.mul_eq_zero.mp h123 with h12 | h3
            · rcases Rat.mul_eq_zero.mp h12 with h1 | h2
              all_goals grind [Rat.sub_eq_add_neg]
            · right
              right
              left
              grind [Rat.sub_eq_add_neg]
          all_goals grind [Rat.sub_eq_add_neg]
        all_goals grind [Rat.sub_eq_add_neg]
      all_goals grind [Rat.sub_eq_add_neg]
    all_goals grind [Rat.sub_eq_add_neg]
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem sevenVariationSeptic_certificate :
    signChangeCountIgnoringZeros sevenVariationSeptic = 7 /\
      (forall x : Rat, 0 < x ->
        (eval sevenVariationSeptic x = 0 ↔
          x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7)) := by
  constructor
  · exact sevenVariationSeptic_sign_count
  · intro x hx
    exact sevenVariationSeptic_positive_root_iff x hx

end Polynomial

end ComputableAnalysis
