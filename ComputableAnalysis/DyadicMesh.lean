import ComputableAnalysis.Basic

/-!
# Finite dyadic mesh arithmetic

Shared interval/mesh facts, extracted from the arctangent application.
The historical namespace is retained to preserve existing public names.
There are no circle, inverse-function, calculus, or Mathlib dependencies.
-/
namespace ComputableAnalysis.ClosedArctanInverse

abbrev Unit (x : Rat) : Prop := 0 ≤ x ∧ x ≤ 1

theorem one_div_le_one_div_of_pos_of_le {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : Not (a = 0) := Rat.ne_of_gt ha
  have hbne : Not (b = 0) := Rat.ne_of_gt hb
  have habpos : 0 < a * b := Rat.mul_pos ha hb
  refine Rat.le_of_mul_le_mul_right (c := a * b) ?_ habpos
  calc
    (1 / b) * (a * b) = a := by
      rw [Rat.div_def]
      have hcancel : b * Inv.inv b = 1 := Rat.mul_inv_cancel b hbne
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= b := hab
    _ = (1 / a) * (a * b) := by
      rw [Rat.div_def]
      have hcancel : a * Inv.inv a = 1 := Rat.mul_inv_cancel a hane
      grind [Rat.mul_assoc, Rat.mul_comm]


def meshRadius (n : Nat) : Rat := 1 / (2 ^ n : Rat)

theorem meshRadius_pos (n : Nat) : 0 < meshRadius n := by
  simp only [meshRadius, Rat.div_def, Rat.one_mul]
  exact (Rat.inv_pos).2 (Rat.pow_pos (by decide))

theorem meshRadius_antitone {n m : Nat} (hnm : n <= m) : meshRadius m <= meshRadius n := by
  have hp : (2 ^ n : Rat) <= 2 ^ m := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hnm
  exact one_div_le_one_div_of_pos_of_le (Rat.pow_pos (by decide)) hp

theorem meshRadius_le (n : Nat) : meshRadius n <= 1 / ((n+1 : Nat) : Rat) := by
  have hp : (n+1 : Nat) ≤ 2^n := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Nat.pow_succ]
      omega
  have hr : ((n+1:Nat):Rat) ≤ (2:Rat)^n := by exact_mod_cast hp
  exact one_div_le_one_div_of_pos_of_le
    ((Rat.natCast_pos).2 (by omega)) hr

end ComputableAnalysis.ClosedArctanInverse
