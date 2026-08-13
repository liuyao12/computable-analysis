import ComputableAnalysis.Series

/-!
# Reusable finite geometric-series interface

This packages the finite prefix and its rational upper endpoint together with
an explicit power budget for the remaining gap.  It is a finite certificate:
no infinite sum or completed limit is part of the object.
-/

namespace ComputableAnalysis
namespace Series

structure FiniteGeometricSeriesCertificate where
  ratioValue : Rat
  stage : Nat
  tolerance : Rat
  prefixValue : Rat
  endpointValue : Rat
  ratio_nonneg : 0 <= ratioValue
  ratio_lt_one : ratioValue < 1
  tolerance_nonneg : 0 <= tolerance
  prefix_eq : prefixValue = geometricSum ratioValue stage
  endpoint_eq : endpointValue = 1 / (1 - ratioValue)
  power_budget : ratioValue ^ stage <= tolerance * (1 - ratioValue)

theorem FiniteGeometricSeriesCertificate.prefix_le_endpoint
    (certificate : FiniteGeometricSeriesCertificate) :
    certificate.prefixValue <= certificate.endpointValue := by
  rw [certificate.prefix_eq, certificate.endpoint_eq]
  exact geometricSum_le_inv_one_sub certificate.ratio_nonneg
    certificate.ratio_lt_one certificate.stage

theorem FiniteGeometricSeriesCertificate.gap_le_tolerance
    (certificate : FiniteGeometricSeriesCertificate) :
    certificate.endpointValue - certificate.prefixValue <= certificate.tolerance := by
  rw [certificate.prefix_eq, certificate.endpoint_eq]
  exact geometricSum_gap_le_of_power_budget certificate.ratio_lt_one
    certificate.power_budget

def finiteGeometricSeriesCertificate
    (ratioValue tolerance : Rat) (stage : Nat)
    (ratio_nonneg : 0 <= ratioValue) (ratio_lt_one : ratioValue < 1)
    (tolerance_nonneg : 0 <= tolerance)
    (power_budget : ratioValue ^ stage <= tolerance * (1 - ratioValue)) :
    FiniteGeometricSeriesCertificate where
  ratioValue := ratioValue
  stage := stage
  tolerance := tolerance
  prefixValue := geometricSum ratioValue stage
  endpointValue := 1 / (1 - ratioValue)
  ratio_nonneg := ratio_nonneg
  ratio_lt_one := ratio_lt_one
  tolerance_nonneg := tolerance_nonneg
  prefix_eq := rfl
  endpoint_eq := rfl
  power_budget := power_budget

end Series
end ComputableAnalysis
