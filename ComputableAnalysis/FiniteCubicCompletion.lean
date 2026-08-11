import ComputableAnalysis.Polynomial

/-!
# Finite completion of a cubic from one supplied root

This is the project-facing boundary of the cubic formula.  A rational root
is supplied to the finite synthetic factorization, and a rational square
witness for the quotient discriminant supplies the remaining two roots.  No
real-root existence or completed-real construction is used.
-/

namespace ComputableAnalysis

namespace Polynomial

theorem quadratic_eval_root_of_discriminant
    (a b c d : Rat) (ha : a ≠ 0)
    (hd : d ^ 2 = b ^ 2 - 4 * a * c) :
    a * ((-b + d) / (2 * a)) ^ 2 +
        b * ((-b + d) / (2 * a)) + c = 0 := by
  rw [Rat.div_def]
  have hden : 2 * a ≠ 0 := by
    intro hzero
    have htwo : (2 : Rat) ≠ 0 := by native_decide
    rcases Rat.mul_eq_zero.mp hzero with htwozero | hazero
    · exact htwo htwozero
    · exact ha hazero
  have hcancel : (2 * a) * (2 * a)⁻¹ = 1 :=
    Rat.mul_inv_cancel (2 * a) hden
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem cubic_completion_roots_of_discriminant
    (c₀ c₁ c₂ c₃ r d : Rat)
    (hcubic : c₃ ≠ 0)
    (hroot : eval [c₀, c₁, c₂, c₃] r = 0)
    (hd : d ^ 2 =
      (c₂ + c₃ * r) ^ 2 -
        4 * c₃ * (c₁ + c₂ * r + c₃ * r ^ 2)) :
    eval [c₀, c₁, c₂, c₃] ((-((c₂ + c₃ * r)) + d) / (2 * c₃)) = 0 ∧
      eval [c₀, c₁, c₂, c₃] ((-((c₂ + c₃ * r)) - d) / (2 * c₃)) = 0 := by
  have hplus :
      c₃ * ((-((c₂ + c₃ * r)) + d) / (2 * c₃)) ^ 2 +
          (c₂ + c₃ * r) *
            ((-((c₂ + c₃ * r)) + d) / (2 * c₃)) +
          (c₁ + c₂ * r + c₃ * r ^ 2) = 0 := by
    exact quadratic_eval_root_of_discriminant c₃
      (c₂ + c₃ * r) (c₁ + c₂ * r + c₃ * r ^ 2) d hcubic hd
  have hminus :
      c₃ * ((-((c₂ + c₃ * r)) - d) / (2 * c₃)) ^ 2 +
          (c₂ + c₃ * r) *
            ((-((c₂ + c₃ * r)) - d) / (2 * c₃)) +
          (c₁ + c₂ * r + c₃ * r ^ 2) = 0 := by
    have hdneg : (-d) ^ 2 =
        (c₂ + c₃ * r) ^ 2 -
          4 * c₃ * (c₁ + c₂ * r + c₃ * r ^ 2) := by
      rw [show (-d) ^ 2 = d ^ 2 by
        grind [Rat.pow_succ, Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]]
      exact hd
    have h := quadratic_eval_root_of_discriminant c₃
      (c₂ + c₃ * r) (c₁ + c₂ * r + c₃ * r ^ 2) (-d) hcubic hdneg
    simpa [Rat.sub_eq_add_neg, Rat.neg_neg] using h
  constructor
  · rw [cubic_factor_of_root hroot]
    rw [show c₃ * ((-((c₂ + c₃ * r)) + d) / (2 * c₃)) ^ 2 +
        (c₂ + c₃ * r) *
          ((-((c₂ + c₃ * r)) + d) / (2 * c₃)) +
        (c₁ + c₂ * r + c₃ * r ^ 2) = 0 from hplus]
    simp
  · rw [cubic_factor_of_root hroot]
    rw [show c₃ * ((-((c₂ + c₃ * r)) - d) / (2 * c₃)) ^ 2 +
        (c₂ + c₃ * r) *
          ((-((c₂ + c₃ * r)) - d) / (2 * c₃)) +
        (c₁ + c₂ * r + c₃ * r ^ 2) = 0 from hminus]
    simp

end Polynomial

end ComputableAnalysis
