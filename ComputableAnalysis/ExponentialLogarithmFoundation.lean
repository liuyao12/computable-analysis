import ComputableAnalysis.ExpProofs
import ComputableAnalysis.FiniteExponentialTaylor
import ComputableAnalysis.RotationSeries
import ComputableAnalysis.FiniteGapAwareInverseSearch
import ComputableAnalysis.IdentityInverse
import ComputableAnalysis.Logarithm

/-!
# Computable exponential and logarithm foundation

This scoped entry point collects rational Taylor-prefix evaluators, finite
tail certificates, rotation coordinates, and gap-aware inverse-search data for
the logarithm.  It exposes the computational contracts needed by later
calculus and ODE developments without postulating a completed real or complex
function space.

One representative evaluator is formalized for each pattern.  Scalar,
signed, and routine compositional variants are transported from these
certificates.
-/

namespace ComputableAnalysis

/-! Small public names for the completed exp/log results in this chapter.
The detailed proofs remain in their focused modules. -/

/-- The certified dyadic integral of the unit exponential is its endpoint
difference: the chapter's first non-polynomial effective FTC. -/
theorem effectiveFTC_exp_on_unit :
    (ExpProofs.uniformExpOnUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw).Equiv
      ExpProofs.uniformExpOnUnit_selectedStageFTCIndexed.toSelected.endpointRaw :=
  ExpProofs.uniformExpOnUnit_effectiveFTC

/-- The stabilized unit-exponential integral is the power-series value at one
minus the rational value at zero. -/
theorem integral_exp_on_unit_eq_exp_one_sub_one :
    (Integral.integralFor ExpProofs.uniformExpOnUnit
      ExpProofs.uniformExpOnUnitStabilizedConstruction).Equiv
      ((expPowerSeries (1 : Rat)) - RealRaw.ofRat 1) :=
  ExpProofs.uniformExpOnUnitStabilizedIntegral_equiv_powerSeries_one_sub_one

/-- The alternating logarithm computation is equivalent to the finite
reciprocal-integral computation on `[1,2]`. -/
theorem log_two_series_eq_reciprocal_integral :
    Logarithm.logTwoSeries.Equiv Logarithm.logTwoReciprocalIntegral :=
  Logarithm.logTwoSeries_equiv_logTwoReciprocalIntegral

end ComputableAnalysis
