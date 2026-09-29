import ComputableAnalysis.RealPowerIntegralTest
import ComputableAnalysis.AlgebraicFunctions

open ComputableAnalysis

#print axioms ComputableAnalysis.PowerIntegral.compact_hasIntegral
#print axioms ComputableAnalysis.PowerIntegral.compact_closedForm
#print axioms ComputableAnalysis.PowerIntegral.compact_equiv
#print axioms ComputableAnalysis.PowerIntegral.zero_hasIntegralLimit
#print axioms ComputableAnalysis.PowerIntegral.zero_closedForm
#print axioms ComputableAnalysis.PowerIntegral.zero_equiv
#print axioms ComputableAnalysis.PowerIntegral.infinityCompact_hasIntegral
#print axioms ComputableAnalysis.PowerIntegral.infinityCompact_closedForm
#print axioms ComputableAnalysis.PowerIntegral.infinity_hasIntegralLimit
#print axioms ComputableAnalysis.PowerIntegral.infinityIntegral_equiv
#print axioms ComputableAnalysis.PowerIntegral.infinity_antitone
#print axioms ComputableAnalysis.PowerIntegral.finite_integral_comparison
#print axioms ComputableAnalysis.PowerIntegral.series_valid
#print axioms ComputableAnalysis.PowerIntegral.series_sumsTo
#print axioms ComputableAnalysis.PowerIntegral.series_stage_bounds
#print axioms ComputableAnalysis.PowerIntegral.series_equiv
#print axioms ComputableAnalysis.PowerIntegral.series_diverges
#print axioms ComputableAnalysis.PowerIntegral.series_converges_iff
#print axioms ComputableAnalysis.PowerIntegral.zero_diverges
#print axioms ComputableAnalysis.PowerIntegral.infinity_diverges
#print axioms ComputableAnalysis.PowerIntegral.zero_converges_iff
#print axioms ComputableAnalysis.PowerIntegral.infinity_converges_iff
#print axioms ComputableAnalysis.PowerIntegral.zero_supplied_exact
#print axioms ComputableAnalysis.PowerIntegral.infinity_supplied_exact
#print axioms ComputableAnalysis.PowerIntegral.series_integral_test
#print axioms ComputableAnalysis.BinomialPower.integrated_endpoint_error_le_cutoff
#print axioms ComputableAnalysis.BinomialPower.Global.canonical_nonneg
#print axioms ComputableAnalysis.FormalPowerSeries.reciprocal_polynomial_hasIntegral

private def halfExponent : Real := Real.ofRat (1/2)
private theorem halfBelow : PowerIntegral.BelowOne halfExponent := ⟨0,by decide +kernel⟩
private def threeHalfExponent : Real := Real.ofRat (3/2)
private theorem threeHalfAbove : BinomialPower.AboveOne threeHalfExponent := ⟨0,by decide +kernel⟩
private def sqrtExponent : Real := sqrtReal 2 (by change ¬(2 : Rat)<0; decide) (sqrtRaw_valid 2 (by change ¬(2 : Rat)<0; decide))
private theorem sqrtAbove : BinomialPower.AboveOne sqrtExponent := ⟨0,by decide +kernel⟩
private def complementaryExponent : Real := PowerIntegral.parameter sqrtExponent
private theorem complementaryBelow : PowerIntegral.BelowOne complementaryExponent := ⟨0,by decide +kernel⟩

-- Numerical tests supplement the universally quantified proofs above.
-- The general series constructor is a conservative reference algorithm;
-- these regressions exercise its finite ingredients, not huge truncations.
#eval do
  let mut checked := 0
  for n in [0,1,3,8] do
    let I := (PowerIntegral.zeroIntegral halfExponent halfBelow).compute n
    let J := (PowerIntegral.infinityIntegral threeHalfExponent threeHalfAbove).compute n
    unless I.lo ≤ 2 && 2 ≤ I.hi && J.lo ≤ 2 && 2 ≤ J.hi do
      throw (IO.userError "noninteger improper formula")
    let A := (PowerIntegral.infinityIntegral sqrtExponent sqrtAbove).compute n
    let B := (PowerIntegral.zeroIntegral complementaryExponent complementaryBelow).compute n
    unless 2 < A.lo && A.hi < 3 && A.lo ≤ B.hi && B.lo ≤ A.hi do
      throw (IO.userError "irrational exponent reciprocal enclosures")
    checked := checked+1
  for s in ([3/2,5/3,2,7/2] : List Rat) do
    for j in [0,1,2] do
      let m := 2
      let q := 1
      let K := ZetaReal.cutoff m j
      let a := BinomialPower.endpointCutoff m j
      let err := BinomialPower.endpointError q m j
      let v := ZetaReal.integratedPowerPolynomial s (K+3) (1-a)
      unless qabs (v-1/(s-1)) ≤ err && 0 < a && a ≤ 1 do
        throw (IO.userError "finite endpoint error")
      checked := checked+1
  for n in [0,1,2] do
    let I := (PowerIntegral.compact halfExponent (1/2) 1 (by decide +kernel) (by decide +kernel) (Rat.le_refl)).compute n
    unless I.lo ≤ 586/1000 && 585/1000 ≤ I.hi && 0 ≤ I.width && I.width ≤ 4*((1 : Rat)/2)^n do
      throw (IO.userError "independent compact noninteger integral")
    checked := checked+1
  IO.println s!"REAL_POWER_TESTS|{checked}|passed"
