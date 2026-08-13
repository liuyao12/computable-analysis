import ComputableAnalysis.Series

/-!
# Reusable finite arithmetic-series interface

An arithmetic series is represented by its finite prefix.  The certificate
keeps the recursive computation and its closed form together; no completed
infinite sum is introduced.
-/

namespace ComputableAnalysis
namespace Series

structure FiniteArithmeticSeriesCertificate where
  initialValue : Rat
  difference : Rat
  stage : Nat
  prefixValue : Rat
  prefix_eq : prefixValue = arithmeticProgressionSum initialValue difference stage

theorem FiniteArithmeticSeriesCertificate.closed_form
    (certificate : FiniteArithmeticSeriesCertificate) :
    certificate.prefixValue =
      (certificate.stage : Rat) *
        (2 * certificate.initialValue +
          ((certificate.stage : Rat) - 1) * certificate.difference) / 2 := by
  rw [certificate.prefix_eq]
  exact arithmeticProgressionSum_eq _ _ _

theorem FiniteArithmeticSeriesCertificate.succ_step
    (certificate : FiniteArithmeticSeriesCertificate) :
    arithmeticProgressionSum certificate.initialValue certificate.difference
        (certificate.stage + 1) =
      certificate.prefixValue +
        (certificate.initialValue + (certificate.stage : Rat) * certificate.difference) := by
  rw [arithmeticProgressionSum_succ, ← certificate.prefix_eq]

def finiteArithmeticSeriesCertificate
    (initialValue difference : Rat) (stage : Nat) :
    FiniteArithmeticSeriesCertificate where
  initialValue := initialValue
  difference := difference
  stage := stage
  prefixValue := arithmeticProgressionSum initialValue difference stage
  prefix_eq := rfl

end Series
end ComputableAnalysis
