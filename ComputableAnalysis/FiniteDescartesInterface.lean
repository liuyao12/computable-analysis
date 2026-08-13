import ComputableAnalysis.PolynomialDescartes

/-!
# A finite Descartes sign-count certificate

This packages the degree-free finite part of Descartes' rule: a supplied
coefficient list has a checked sign-change count after zero removal, and that
count is bounded by the length of the surviving list.  Root-count statements
remain separate certificates; no completed real root space is introduced.
-/

namespace ComputableAnalysis

namespace Polynomial

structure FiniteDescartesSignCertificate where
  coefficients : List Rat
  variationCount : Nat
  filteredLength : Nat
  variation_eq :
    signChangeCountIgnoringZeros coefficients = variationCount
  filteredLength_eq :
    (coefficients.filter (fun c => c != 0)).length = filteredLength
  variation_lt_length : variationCount + 1 ≤ filteredLength

theorem FiniteDescartesSignCertificate.variation_eq_count
    (certificate : FiniteDescartesSignCertificate) :
    signChangeCountIgnoringZeros certificate.coefficients =
      certificate.variationCount :=
  certificate.variation_eq

theorem FiniteDescartesSignCertificate.variation_bound
    (certificate : FiniteDescartesSignCertificate) :
    certificate.variationCount + 1 ≤ certificate.filteredLength :=
  certificate.variation_lt_length

def finiteDescartesSignCertificate
    (coefficients : List Rat)
    (hne : (coefficients.filter (fun c => c != 0)).length > 0) :
    FiniteDescartesSignCertificate := by
  let filteredLength := (coefficients.filter (fun c => c != 0)).length
  let variationCount := signChangeCountIgnoringZeros coefficients
  have hbound :=
    signChangeCountIgnoringZeros_add_one_le_filter_length (coeffs := coefficients) hne
  exact
    { coefficients := coefficients
      variationCount := variationCount
      filteredLength := filteredLength
      variation_eq := rfl
      filteredLength_eq := rfl
      variation_lt_length := hbound }

end Polynomial

end ComputableAnalysis
