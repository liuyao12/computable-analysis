import ComputableAnalysis.ExponentialComputations.API
open ComputableAnalysis ComputableAnalysis.ExponentialComputations

/- Quadrature encloses zero at the normalization point. -/
#eval let I := (integralLog oneInput).val.compute 0
  decide (I.lo ≤ 0 ∧ 0 ≤ I.hi ∧ I.width ≤ 1)

/- Reversed orientation produces a negative interval at the endpoint one half. -/
#eval let x : PositiveInput :=
    ⟨⟨RealRaw.ofRat (1/2),RealRaw.ofRat_valid _⟩,⟨0,by decide +kernel⟩⟩
  let I := (integralLog x).val.compute 0
  decide (-1 < I.lo ∧ I.hi < -(1/2:Rat) ∧ I.width ≤ 1)
