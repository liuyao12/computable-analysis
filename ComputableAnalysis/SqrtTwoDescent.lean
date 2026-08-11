import ComputableAnalysis.IrrationalSqrt

namespace ComputableAnalysis

/-! A deliberately low-level Diophantine descent kernel.

This file does not provide the public square-root irrationality API.  For the
general rational criterion used by comparison projects, use
`ComputableAnalysis.IrrationalSqrt.irrational_sqrt_rat_iff_not_square`.
This module remains as a pedagogical elementary-descent example: it proves
the Diophantine kernel `a² = 2b² → b = 0` without real numbers, rationals,
factorisation, or library irrationality theorems.
-/

private theorem odd_square_mod_two (k : Nat) :
    ((2 * k + 1) ^ 2) % 2 = 1 := by
  simp [Nat.pow_two, Nat.add_mod, Nat.mul_mod]

private theorem even_square_even_root {a : Nat} (h : a ^ 2 % 2 = 0) :
    ∃ c, a = 2 * c := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · have hdvd : 2 ∣ a := (Nat.dvd_iff_mod_eq_zero).2 ha
    rcases hdvd with ⟨c, hc⟩
    exact ⟨c, hc⟩
  · have hdecomp := Nat.mod_add_div a 2
    have hac : a = 2 * (a / 2) + 1 := by omega
    rw [hac] at h
    simp [odd_square_mod_two] at h

theorem sqrtTwo_descent_core :
    ∀ a b : Nat, a ^ 2 = 2 * b ^ 2 → b = 0 := by
  intro a b
  revert a
  refine Nat.strongRecOn b ?_
  intro b ih a hsq
  by_cases hb : b = 0
  · exact hb
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have haeven : a ^ 2 % 2 = 0 := by
    rw [hsq]
    simp
  obtain ⟨c, hac⟩ := even_square_even_root haeven
  have hsq' : b ^ 2 = 2 * c ^ 2 := by
    have hsq'' : (2 * c) ^ 2 = 2 * b ^ 2 := by simpa [hac] using hsq
    have hcancel : 2 * (2 * c ^ 2) = 2 * b ^ 2 := by
      calc
        2 * (2 * c ^ 2) = (2 * c) ^ 2 := by
          simp [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = 2 * b ^ 2 := hsq''
    exact Nat.mul_left_cancel (n := 2) (by omega) hcancel.symm
  have hcb : c < b := by
    have hb2pos : 0 < b ^ 2 := Nat.pow_pos hbpos
    have hc2pos : 0 < c ^ 2 := by omega
    have hlt : c ^ 2 < b ^ 2 := by rw [hsq']; omega
    exact (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp hlt
  have hc : c = 0 := ih c hcb b hsq'
  simpa [hc] using hsq'

private theorem nat_square_two_impossible_via_descent {k : Nat}
    (hk : k * k = 2) : False := by
  have hsq : k ^ 2 = 2 * 1 ^ 2 := by
    simpa [Nat.pow_two] using hk
  have hzero : (1 : Nat) = 0 := sqrtTwo_descent_core k 1 hsq
  omega

/-- The rational-square obstruction for `2`, now explicitly routed through
the classical infinite-descent kernel above. -/
theorem two_not_rat_square_via_descent : ¬ Rat.IsSquare (2 : Rat) := by
  intro hsquare
  have hlowest := Rat.isSquareInLowestTerms_of_isSquare hsquare
  rcases hlowest.1 with ⟨_, hnum⟩
  rcases hnum with ⟨k, hk⟩
  have hnumabs : ((2 : Rat).num).natAbs = 2 := by native_decide
  rw [hnumabs] at hk
  apply nat_square_two_impossible_via_descent
  simpa using hk

/-- Benchmark item 1, with the computable square-root representation and the
infinite-descent proof of the nonsquare input. -/
theorem sqrt_two_irrational_via_descent :
    RealRaw.Irrational (sqrtRat (2 : Rat) (by native_decide)) := by
  apply (irrational_sqrt_ratCast_iff_of_nonneg (by native_decide)).2
  exact two_not_rat_square_via_descent

end ComputableAnalysis
