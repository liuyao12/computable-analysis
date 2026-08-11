import ComputableAnalysis.Basic

/-!
# Finite positional digit-sum divisibility

This file records the finite, list-based form of the usual digit-sum
argument.  Digits are stored least significant first, so the definition is
an executable positional evaluation using only `Nat` arithmetic.
-/

namespace ComputableAnalysis

/-- Evaluate a finite list of base-`b` digits, least significant first. -/
def basePositionalValue (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + b * basePositionalValue b ds

private theorem base_mul_mod_sub_one (b x : Nat) (hb : 2 ≤ b) :
    (b * x) % (b - 1) = x % (b - 1) := by
  have hsub : b = (b - 1) + 1 := by omega
  rw [hsub, Nat.add_mul, Nat.add_mod]
  simp

/--
For every finite list of base-`b` digits, positional evaluation and the digit
sum have the same residue modulo `b - 1`.  No digit-range or infinite
representation assumption is needed: this is a literal finite theorem.
-/
theorem basePositionalValue_mod_sub_one (b : Nat) (hb : 2 ≤ b)
    (digits : List Nat) :
    basePositionalValue b digits % (b - 1) = digits.sum % (b - 1) := by
  induction digits with
  | nil => simp [basePositionalValue]
  | cons d ds ih =>
      simp only [basePositionalValue, List.sum_cons]
      rw [Nat.add_mod, base_mul_mod_sub_one b
        (basePositionalValue b ds) hb, ih, Nat.add_mod]
      simp

/-- The decimal case, stated directly for a finite list of decimal digits. -/
theorem decimalPositionalValue_mod_nine (digits : List Nat) :
    basePositionalValue 10 digits % 9 = digits.sum % 9 := by
  simpa using basePositionalValue_mod_sub_one 10 (by omega) digits

end ComputableAnalysis
