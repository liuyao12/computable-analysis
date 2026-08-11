import ComputableAnalysis.Series

/-!
# A worked induction certificate

This module uses the project's public induction schema to re-prove the
arithmetic-series closed form and then evaluates it at a concrete stage.
It is a finite proof/programming witness for benchmark item 74.
-/

namespace ComputableAnalysis

theorem induction_arithmeticSum_eq (n : Nat) :
    Series.arithmeticSum n = (n : Rat) * ((n : Rat) - 1) / 2 := by
  have h : ∀ k : Nat,
      Series.arithmeticSum k = (k : Rat) * ((k : Rat) - 1) / 2 := by
    apply nat_induction_schema
    · simp [Series.arithmeticSum, Rat.div_def]
    · intro k ih
      rw [Series.arithmeticSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]
  exact h n

theorem induction_arithmeticSum_stage5 :
    Series.arithmeticSum 5 = 10 := by
  rw [induction_arithmeticSum_eq]
  native_decide

end ComputableAnalysis
