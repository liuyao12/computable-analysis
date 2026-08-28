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

namespace FiniteTaylorCertificate

/-! A finite Taylor certificate can be exposed as an ordinary project-native
    raw endpoint computation.  This is an exact finite object; no tail or
    completed-real passage is included. -/

noncomputable def endpointRaw (certificate : FiniteTaylorCertificate) : RealRaw :=
  endpointDifferenceRaw
    (RealFunRaw.exact
      (FinitePolynomial.integratedTaylorPrefix certificate.coefficients
        certificate.terms))
    certificate.leftEndpoint certificate.rightEndpoint
    (endpointDifference_valid_of_fun_valid (RealFunRaw.exact_valid _) trivial trivial)

theorem endpointRaw_valid (certificate : FiniteTaylorCertificate) :
    certificate.endpointRaw.Valid := by
  change RealRaw.ValidCompute
    (endpointDifferenceCompute
      (RealFunRaw.exact
        (FinitePolynomial.integratedTaylorPrefix certificate.coefficients
          certificate.terms))
      certificate.leftEndpoint certificate.rightEndpoint)
  exact endpointDifference_valid_of_fun_valid
    (F := RealFunRaw.exact
      (FinitePolynomial.integratedTaylorPrefix certificate.coefficients
        certificate.terms))
    (a := certificate.leftEndpoint) (b := certificate.rightEndpoint)
    (RealFunRaw.exact_valid _) trivial trivial

theorem endpointRaw_equiv_prefixIncrement
    (certificate : FiniteTaylorCertificate) :
    certificate.endpointRaw.Equiv
      (RealRaw.ofRat certificate.prefixIncrement) := by
  intro stage
  apply (RealRaw.compareAt_overlap_iff _ _ stage stage).2
  change QInterval.Overlaps
    (endpointDifferenceCompute
      (RealFunRaw.exact
        (FinitePolynomial.integratedTaylorPrefix certificate.coefficients
          certificate.terms))
      certificate.leftEndpoint certificate.rightEndpoint stage)
    { lo := certificate.prefixIncrement, hi := certificate.prefixIncrement }
  unfold endpointDifferenceCompute endpointDifferenceInterval
  simp [RealFunRaw.exact]
  rw [certificate.prefix_eq]
  exact ⟨Rat.le_refl, Rat.le_refl⟩

end FiniteTaylorCertificate

end ComputableAnalysis
