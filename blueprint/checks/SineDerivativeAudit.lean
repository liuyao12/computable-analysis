import ComputableAnalysis.SineDerivative

open ComputableAnalysis FixedSchedule

-- These examples also check that the public conclusions have no missing
-- analytic certificate argument.
example : HasEndpointDerivativeOn sine cosine 2 := sine_derivative_cosine
example : HasEndpointDerivativeOn sine sineDerivative 1 := sin'_eq_cos.1
example (x : Rat) (hx : qabs x <= 1) :
    (sineDerivative x).Valid ∧ (sineDerivative x).Equiv (cosine x) :=
  sin'_eq_cos.2 x hx
example (x : Rat) (hx : qabs x <= 1) (n m : Nat) :
    QInterval.Overlaps ((sineDerivative x).compute n) ((cosine x).compute m) :=
  sineDerivative_output_overlap hx n m

#print axioms sine_derivative_cosine
#print axioms sin'_eq_cos
#print axioms RotationSeries.uniformRotationSinOnTwo_hasDerivativeOnInterval
#print axioms RotationSeries.uniformRotationCosOnTwo_hasDerivativeOnInterval
