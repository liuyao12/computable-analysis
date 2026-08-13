import ComputableAnalysis.Series

/-!
# Reusable finite binomial-series interface

The binomial theorem is represented as a finite row computation.  The
certificate records the exact rational fold and its power interpretation.
-/

namespace ComputableAnalysis
namespace Series

structure FiniteBinomialSeriesCertificate where
  exponent : Nat
  leftValue : Rat
  rightValue : Rat
  stage : Nat
  prefixValue : Rat
  stage_reached : exponent + 1 <= stage
  prefix_eq : prefixValue = binomialSum exponent leftValue rightValue stage

theorem FiniteBinomialSeriesCertificate.power_identity
    (certificate : FiniteBinomialSeriesCertificate) :
    certificate.prefixValue =
      (certificate.leftValue + certificate.rightValue) ^ certificate.exponent := by
  rw [certificate.prefix_eq]
  exact binomialSum_eq_pow_of_reached certificate.stage_reached _ _

def finiteBinomialSeriesCertificate
    (exponent : Nat) (leftValue rightValue : Rat) (stage : Nat)
    (stage_reached : exponent + 1 <= stage) :
    FiniteBinomialSeriesCertificate where
  exponent := exponent
  leftValue := leftValue
  rightValue := rightValue
  stage := stage
  prefixValue := binomialSum exponent leftValue rightValue stage
  stage_reached := stage_reached
  prefix_eq := rfl

end Series
end ComputableAnalysis
