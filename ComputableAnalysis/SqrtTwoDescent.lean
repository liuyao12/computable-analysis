import ComputableAnalysis.Basic

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

end ComputableAnalysis
