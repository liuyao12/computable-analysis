import ComputableAnalysis.Series

/-!
# Reusable finite power-sum interface

Power sums are finite rational folds indexed by an exponent and a stage.  This
interface packages the recurrence, a shifted-block extension, and a growth
bound; closed forms for low exponents are refinements of the same object.
-/

namespace ComputableAnalysis
namespace Series

structure FinitePowerSumCertificate where
  exponent : Nat
  stage : Nat
  value : Rat
  value_eq : value = powerSum exponent stage

theorem FinitePowerSumCertificate.succ_step
    (certificate : FinitePowerSumCertificate) :
    powerSum certificate.exponent (certificate.stage + 1) =
      certificate.value + (certificate.stage : Rat) ^ certificate.exponent := by
  rw [powerSum_succ, ← certificate.value_eq]

theorem FinitePowerSumCertificate.growth_bound
    (certificate : FinitePowerSumCertificate) :
    certificate.value <=
      (certificate.stage : Rat) * (certificate.stage : Rat) ^ certificate.exponent := by
  rw [certificate.value_eq]
  exact powerSum_le_mul_pow certificate.exponent certificate.stage

theorem powerSum_add_block_certificate (exponent stage block : Nat) :
    powerSum exponent (stage + block) =
      powerSum exponent stage + powerSumBlock exponent stage block := by
  exact powerSum_add_block exponent stage block

def finitePowerSumCertificate (exponent stage : Nat) :
    FinitePowerSumCertificate where
  exponent := exponent
  stage := stage
  value := powerSum exponent stage
  value_eq := rfl

theorem finitePowerSumCertificate_value (exponent stage : Nat) :
    (finitePowerSumCertificate exponent stage).value =
      powerSum exponent stage := by
  rfl

end Series
end ComputableAnalysis
