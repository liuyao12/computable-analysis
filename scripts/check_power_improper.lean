import ComputableAnalysis.HarmonicImproperBounds

open ComputableAnalysis IntegerPowerIntegral

#print axioms Integral.HasIntegral.unique
#print axioms Integral.HasIntegralLimit.unique
#print axioms compact_hasIntegral
#print axioms compact_exact
#print axioms infinity_exhausts
#print axioms zero_cutoff_shrinks
#print axioms dyadic_ge_stage
#print axioms dyadic_cutoff_shrinks
#print axioms infinity_valid
#print axioms infinity_contains_compact
#print axioms infinity_hasIntegralLimit
#print axioms infinity_exact_of_hasIntegralLimit
#print axioms monomial_hasIntegral
#print axioms zero_hasIntegralLimit
#print axioms zero_exact_of_hasIntegralLimit
#print axioms zero_reciprocal_not_hasIntegralLimit
#print axioms monomial_infinity_diverges
#print axioms harmonic_bounds_sums
#print axioms harmonic_infinity_diverges
#print axioms harmonic_zero_diverges
#print axioms finite_integral_comparison
#print axioms series_valid
#print axioms series_sumsTo
#print axioms SumsTo.unique
#print axioms SumsTo.congr
#print axioms natural_series_converges_iff
#print axioms harmonic_diverges
#print axioms integrand_eq_one_div

-- Executable regression checks are supplementary to the theorem audits above.
#eval do
  let mut checked := 0
  for k in [0,1,2,4,8] do
    for n in [0,1,2,5,12,25] do
      let I := (infinity k).compute n
      let target : Rat := 1/((k : Rat)+1)
      unless I.lo ≤ target && target ≤ I.hi && I.width == tail k ((n+1 : Nat) : Rat) do
        throw (IO.userError "improper interval regression")
      let J := (series k).compute n
      for extra in [1,3,7] do
        let s := partialSum (k+2) (n+1+extra)
        unless J.lo ≤ s && s ≤ J.hi do
          throw (IO.userError "integral-to-series tail regression")
      let a : Rat := 1/((n+1 : Nat) : Rat)
      unless monomialCompact k a 1 == I.lo do
        throw (IO.userError "zero endpoint regression")
      for t in [0,1,3] do
        let z : Rat := 1/(((k+1)*t+1 : Nat) : Rat)
        unless ((t : Nat) : Rat) ≤ compact k z 1 do
          throw (IO.userError "zero divergence regression")
      checked := checked+1
  for t in ([0,1,2,3] : List Nat) do
    unless ((t : Nat) : Rat) ≤ partialSum 1 (2^(2*t)) do
      throw (IO.userError "harmonic divergence regression")
    checked := checked+1
  IO.println s!"POWER_TESTS|{checked}|passed"
