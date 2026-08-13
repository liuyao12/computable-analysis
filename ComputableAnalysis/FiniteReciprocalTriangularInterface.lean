import ComputableAnalysis.Series

/-!
# Reusable finite reciprocal-triangular interface

The infinite-looking identity is represented by a finite prefix, an exact
rational value for that prefix, and an explicit remaining tail.
-/

namespace ComputableAnalysis
namespace Series

structure ReciprocalTriangularCertificate where
  stage : Nat
  prefixValue : Rat
  prefix_eq : prefixValue = triangularTelescopingSum stage
  targetValue : Rat
  tail : Rat
  target_eq : targetValue - prefixValue = tail
  tail_nonneg : 0 <= tail

theorem ReciprocalTriangularCertificate.prefix_mem_target
    (certificate : ReciprocalTriangularCertificate) :
    certificate.prefixValue <= certificate.targetValue := by
  have h := certificate.target_eq
  have hdiff : 0 ≤ certificate.targetValue - certificate.prefixValue := by
    rw [h]
    exact certificate.tail_nonneg
  grind

theorem ReciprocalTriangularCertificate.exact_prefix
    (certificate : ReciprocalTriangularCertificate) :
    certificate.prefixValue = 2 - 2 / (certificate.stage + 1) := by
  rw [certificate.prefix_eq]
  exact triangularTelescopingSum_eq certificate.stage

theorem ReciprocalTriangularCertificate.tail_formula
    (certificate : ReciprocalTriangularCertificate)
    (htarget : certificate.targetValue = 2) :
    certificate.tail = 2 / (certificate.stage + 1) := by
  rw [← certificate.target_eq, htarget, certificate.prefix_eq]
  exact triangularTelescopingSum_tail_eq certificate.stage

def reciprocalTriangularCertificate (stage : Nat) :
    ReciprocalTriangularCertificate where
  stage := stage
  prefixValue := triangularTelescopingSum stage
  prefix_eq := rfl
  targetValue := 2
  tail := 2 / (stage + 1)
  target_eq := by
    exact triangularTelescopingSum_tail_eq stage
  tail_nonneg := by
    rw [Rat.div_def]
    have hden : ((stage : Rat) + 1) = ((stage + 1 : Nat) : Rat) := by
      exact_mod_cast (by omega : stage + 1 = stage + 1)
    have hinv : 0 ≤ ((stage : Rat) + 1)⁻¹ := by
      apply Rat.le_of_lt
      apply (Rat.inv_pos).2
      have : (0 : Rat) < (stage : Rat) + 1 := by
        have hs : (0 : Rat) ≤ (stage : Rat) := Rat.natCast_nonneg
        grind
      exact this
    exact Rat.mul_nonneg (by native_decide) hinv

theorem reciprocalTriangularCertificate_tail_formula (stage : Nat) :
    (reciprocalTriangularCertificate stage).tail = 2 / (stage + 1) := by
  rfl

end Series
end ComputableAnalysis
