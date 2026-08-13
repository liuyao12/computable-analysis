import ComputableAnalysis.FiniteTaylorFTCInterface

/-!
# Reusable finite Taylor certificate

This is the project-scoped Taylor theorem: a finite integrated polynomial
prefix, its exact endpoint increment, and the explicit finite fold of its
monomial contributions.  Any omitted remainder is a separate rational bound.
-/

namespace ComputableAnalysis

structure FiniteTaylorCertificate where
  coefficients : Nat → Rat
  terms : Nat
  leftEndpoint : Rat
  rightEndpoint : Rat
  prefixIncrement : Rat
  prefix_eq : prefixIncrement =
    FinitePolynomial.integratedTaylorPrefix coefficients terms rightEndpoint -
      FinitePolynomial.integratedTaylorPrefix coefficients terms leftEndpoint

theorem FiniteTaylorCertificate.fold_identity
    (certificate : FiniteTaylorCertificate) :
    certificate.prefixIncrement =
      (List.range certificate.terms).foldl
        (fun acc k => acc + certificate.coefficients k *
          (certificate.rightEndpoint ^ (k + 1) /
              ((k + 1 : Nat) : Rat) -
            certificate.leftEndpoint ^ (k + 1) /
              ((k + 1 : Nat) : Rat))) 0 := by
  rw [certificate.prefix_eq]
  exact FinitePolynomial.finiteTaylorFTC_prefix
    certificate.coefficients certificate.terms
    certificate.leftEndpoint certificate.rightEndpoint

def finiteTaylorCertificate
    (coefficients : Nat → Rat) (terms : Nat)
    (leftEndpoint rightEndpoint : Rat) : FiniteTaylorCertificate where
  coefficients := coefficients
  terms := terms
  leftEndpoint := leftEndpoint
  rightEndpoint := rightEndpoint
  prefixIncrement :=
    FinitePolynomial.integratedTaylorPrefix coefficients terms rightEndpoint -
      FinitePolynomial.integratedTaylorPrefix coefficients terms leftEndpoint
  prefix_eq := rfl

end ComputableAnalysis
