import ComputableAnalysis.PowerSeries

/-!
# Reusable finite factorial interface

Factorials are terminating natural recursion transported to rational values.
This interface exposes the finite recurrence and positivity used by Stirling
ratios and factorial-tail bounds.
-/

namespace ComputableAnalysis

structure FiniteFactorialCertificate where
  stage : Nat
  value : Rat
  value_eq : value = factorialRat stage

theorem FiniteFactorialCertificate.succ_step
    (certificate : FiniteFactorialCertificate) :
    factorialRat (certificate.stage + 1) =
      ((certificate.stage + 1 : Nat) : Rat) * certificate.value := by
  rw [FormalPowerSeries.factorialRat_succ, ← certificate.value_eq]

theorem FiniteFactorialCertificate.positive
    (certificate : FiniteFactorialCertificate) :
    0 < certificate.value := by
  rw [certificate.value_eq]
  exact RationalMajorant.factorialRat_pos certificate.stage

def finiteFactorialCertificate (stage : Nat) : FiniteFactorialCertificate where
  stage := stage
  value := factorialRat stage
  value_eq := rfl

theorem finiteFactorialCertificate_value (stage : Nat) :
    (finiteFactorialCertificate stage).value = factorialRat stage := by
  rfl

end ComputableAnalysis
