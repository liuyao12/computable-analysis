import ComputableAnalysis.RotationDerivative

/-!
# Stable rotation derivatives

The rotation derivative proofs are first established for the ordinary
interval-function façade.  This file exposes the same results through the
proof-independent stable evaluators used by the public calculus interface.
-/

namespace ComputableAnalysis

namespace RotationSeries

def stableUniformRotationSinFunction_hasDerivativeOnInterval :
    HasDerivativeOnInterval stableUniformRotationSinFunction
      stableUniformRotationCosFunction where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := uniformRotationSinOnTwo_hasDerivativeOnInterval.stepPrecision
  evalPrecision := uniformRotationSinOnTwo_hasDerivativeOnInterval.evalPrecision
  close := by
    intro x h n hx hxh hdx hh hsmall
    have hcert := uniformRotationSinOnTwo_hasDerivativeOnInterval.close x h n
      (by simpa [stableUniformRotationSinFunction, uniformRotationSinOnTwo,
        FunctionOnInterval.ofStable, inDomainInterval] using hx)
      (by simpa [stableUniformRotationSinFunction, uniformRotationSinOnTwo,
        FunctionOnInterval.ofStable, inDomainInterval] using hxh)
      (by simpa [stableUniformRotationCosFunction, uniformRotationCosOnTwo,
        FunctionOnInterval.ofStable, inDomainInterval] using hdx)
      hh hsmall
    change intervalNearAtPrecision
      (((ComplexRaw.imagPart (uniformRotationExpRaw (x + h))).compute
        (uniformRotationSinOnTwo_hasDerivativeOnInterval.evalPrecision x h n)).differenceQuotient
        ((ComplexRaw.imagPart (uniformRotationExpRaw x)).compute
          (uniformRotationSinOnTwo_hasDerivativeOnInterval.evalPrecision x h n)) h)
      ((ComplexRaw.realPart (uniformRotationExpRaw x)).compute
        (uniformRotationSinOnTwo_hasDerivativeOnInterval.evalPrecision x h n)) n
    exact hcert

def stableUniformRotationCosFunction_hasDerivativeOnInterval :
    HasDerivativeOnInterval stableUniformRotationCosFunction
      stableUniformRotationNegSinFunction where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := uniformRotationCosOnTwo_hasDerivativeOnInterval.stepPrecision
  evalPrecision := uniformRotationCosOnTwo_hasDerivativeOnInterval.evalPrecision
  close := by
    intro x h n hx hxh hdx hh hsmall
    have hcert := uniformRotationCosOnTwo_hasDerivativeOnInterval.close x h n
      (by simpa [stableUniformRotationCosFunction, uniformRotationCosOnTwo,
        FunctionOnInterval.ofStable, inDomainInterval] using hx)
      (by simpa [stableUniformRotationCosFunction, uniformRotationCosOnTwo,
        FunctionOnInterval.ofStable, inDomainInterval] using hxh)
      (by simpa [stableUniformRotationNegSinFunction, uniformRotationNegSinOnTwo,
        FunctionOnInterval.ofStable, inDomainInterval] using hdx)
      hh hsmall
    change intervalNearAtPrecision
      (((ComplexRaw.realPart (uniformRotationExpRaw (x + h))).compute
        (uniformRotationCosOnTwo_hasDerivativeOnInterval.evalPrecision x h n)).differenceQuotient
        ((ComplexRaw.realPart (uniformRotationExpRaw x)).compute
          (uniformRotationCosOnTwo_hasDerivativeOnInterval.evalPrecision x h n)) h)
      ((RealRaw.neg (ComplexRaw.imagPart (uniformRotationExpRaw x))).compute
        (uniformRotationCosOnTwo_hasDerivativeOnInterval.evalPrecision x h n)) n
    exact hcert

end RotationSeries

end ComputableAnalysis
