import ComputableAnalysis.CauchyPi

/-!
# A reciprocal-quartic quadrature computation of pi

The compact rational kernel
`(1 + x^2) / (x^4 - x^2 + 1)` on `[-1,1]` has a literal dyadic rectangle
algorithm.  Its finite projective comparison is already proved in
`IntegralIdentities`; this module exposes the resulting pi bridge without
depending on the large pi-presentation registry.
-/

namespace ComputableAnalysis

namespace ReciprocalQuarticPi

/-- The dyadic compact quadrature of the reciprocal-quartic kernel on
`[-1,1]`. -/
def raw : RealRaw :=
  IntegralIdentities.reciprocalQuarticMinusOneCompactDyadicIntegral

theorem raw_valid : raw.Valid :=
  IntegralIdentities.reciprocalQuarticMinusOneCompactDyadicIntegral_valid

/-- The literal public quadrature rate. -/
theorem raw_width (n : Nat) :
    (raw.compute n).width = 64 * (1 / (((2 ^ n : Nat) : Rat)) ) := by
  exact IntegralIdentities.reciprocalQuarticMinusOneCompactDyadicIntegral_width n

/-- The finite projective envelope connects the compact quartic computation
to the independently defined full-line Cauchy raw. -/
theorem raw_equiv_cauchyRaw : raw.Equiv CauchyPi.raw := by
  exact IntegralIdentities.reciprocalQuarticMinusOneCompactDyadicIntegral_equiv_cauchyFullLine

/-- The reciprocal-quartic quadrature computes the geometric circle-area
representative of pi. -/
theorem raw_equiv_piCircleArea : raw.Equiv piCircleArea := by
  exact RealRaw.equiv_trans raw_valid CauchyPi.raw_valid
    CauchyPi.piCircleArea_valid raw_equiv_cauchyRaw
    CauchyPi.raw_equiv_piCircleArea

end ReciprocalQuarticPi

end ComputableAnalysis
