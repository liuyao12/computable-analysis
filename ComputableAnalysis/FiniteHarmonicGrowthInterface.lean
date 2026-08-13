import ComputableAnalysis.Basic

/-!
# Independent finite harmonic-growth certificate

This is the computable core of harmonic-series divergence.  A requested
natural target is exceeded at an explicit dyadic finite stage; no logarithm,
integral, infinite sum, or completed real is involved.
-/

namespace ComputableAnalysis

namespace FiniteHarmonic

def harmonicSum : Nat -> Rat
  | 0 => 0
  | n + 1 => harmonicSum n + 1 / ((n + 1 : Nat) : Rat)

theorem harmonicSum_succ (n : Nat) :
    harmonicSum (n + 1) = harmonicSum n + 1 / ((n + 1 : Nat) : Rat) :=
  rfl

private theorem reciprocal_pair_lower (n : Nat) :
    1 / ((n + 1 : Nat) : Rat) <=
      1 / ((2 * n + 1 : Nat) : Rat) +
        1 / ((2 * n + 2 : Nat) : Rat) := by
  have hb : 0 < ((2 * n + 1 : Nat) : Rat) := by
    exact_mod_cast (by omega : 0 < 2 * n + 1)
  have hc : 0 < ((2 * n + 2 : Nat) : Rat) := by
    exact_mod_cast (by omega : 0 < 2 * n + 2)
  have horder : ((2 * n + 1 : Nat) : Rat) <=
      ((2 * n + 2 : Nat) : Rat) := by
    exact_mod_cast (by omega)
  have hmono :
      1 / ((2 * n + 2 : Nat) : Rat) <=
        1 / ((2 * n + 1 : Nat) : Rat) := by
    have hprod : 0 <
        ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) :=
      Rat.mul_pos hb hc
    apply Rat.le_of_mul_le_mul_right
      (c := ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat))
    · rw [Rat.div_def, Rat.div_def]
      have hleft :
          ((2 * n + 1 : Nat) : Rat) *
              ((2 * n + 1 : Nat) : Rat)⁻¹ = 1 :=
        Rat.mul_inv_cancel _ (Rat.ne_of_gt hb)
      have hright :
          ((2 * n + 2 : Nat) : Rat) *
              ((2 * n + 2 : Nat) : Rat)⁻¹ = 1 :=
        Rat.mul_inv_cancel _ (Rat.ne_of_gt hc)
      grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hprod
  have hsplit : 1 / ((n + 1 : Nat) : Rat) / 2 =
      1 / ((2 * n + 2 : Nat) : Rat) := by
    have hden : ((2 * n + 2 : Nat) : Rat) =
        2 * ((n + 1 : Nat) : Rat) := by
      exact_mod_cast (by omega : 2 * n + 2 = 2 * (n + 1))
    rw [hden, Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]
  rw [← hsplit] at hmono
  grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem harmonicSum_double_succ (n : Nat) :
    harmonicSum (2 * (n + 1)) =
      harmonicSum (2 * n) + 1 / ((2 * n + 1 : Nat) : Rat) +
        1 / ((2 * n + 2 : Nat) : Rat) := by
  have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  rw [hindex, harmonicSum_succ, harmonicSum_succ]

theorem harmonicSum_double_lower (n : Nat) (hn : 0 < n) :
    harmonicSum n + 1 / 2 <= harmonicSum (2 * n) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hnzero : n = 0
      · subst n
        native_decide
      · have hprev := ih (by omega)
        rw [harmonicSum_double_succ, harmonicSum_succ]
        have hpair := reciprocal_pair_lower n
        grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem harmonicSum_two_pow_lower (k : Nat) :
    (k : Rat) / 2 <= harmonicSum (2 ^ k) := by
  induction k with
  | zero => native_decide
  | succ k ih =>
      rw [Nat.pow_succ]
      have hdouble := harmonicSum_double_lower (2 ^ k)
        (Nat.two_pow_pos k)
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem harmonicSum_two_pow_reaches (target : Nat) :
    (target : Rat) <= harmonicSum (2 ^ (2 * target)) := by
  have h := harmonicSum_two_pow_lower (2 * target)
  calc
    (target : Rat) = ((2 * target : Nat) : Rat) / 2 := by
      rw [Rat.div_def]
      push_cast
      grind [Rat.mul_assoc]
    _ <= harmonicSum (2 ^ (2 * target)) := h

structure Certificate where
  target : Nat
  stage : Nat
  stage_eq : stage = 2 ^ (2 * target)
  target_reached : (target : Rat) <= harmonicSum stage

theorem Certificate.explicit_stage (certificate : Certificate) :
    (certificate.target : Rat) <=
      harmonicSum (2 ^ (2 * certificate.target)) := by
  rw [← certificate.stage_eq]
  exact certificate.target_reached

def certificate (target : Nat) : Certificate where
  target := target
  stage := 2 ^ (2 * target)
  stage_eq := rfl
  target_reached := harmonicSum_two_pow_reaches target

end FiniteHarmonic

end ComputableAnalysis
