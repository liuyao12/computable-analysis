import ComputableAnalysis.FiniteDeflationChain

/-!
# Reusable finite cubic-root witness interface

The cubic theorem is represented here by supplied exact roots and a finite
synthetic-deflation chain.  This yields computable root certificates and a
Horner factorization, without claiming a general cubic formula or root
existence for arbitrary coefficients.
-/

namespace ComputableAnalysis

namespace FiniteDeflationChain

structure CubicRootWitnessCertificate where
  coeffs : CPoly.Coeffs
  root₁ root₂ root₃ : QComplex
  root₁_exact : CPoly.hasExactRoot coeffs root₁
  root₂_exact : CPoly.hasExactRoot coeffs root₂
  root₃_exact : CPoly.hasExactRoot coeffs root₃
  chain : IsDeflationChain coeffs [root₁, root₂, root₃]

theorem CubicRootWitnessCertificate.computable_roots_and_factorization
    (certificate : CubicRootWitnessCertificate) (x : QComplex) :
    (IsComputableRoot certificate.coeffs (exactComplexCert certificate.root₁)) /\
      (IsComputableRoot certificate.coeffs (exactComplexCert certificate.root₂)) /\
      (IsComputableRoot certificate.coeffs (exactComplexCert certificate.root₃)) /\
      CPoly.eval certificate.coeffs x =
        QComplex.mul
          (rootFactorProduct
            [certificate.root₁, certificate.root₂, certificate.root₃] x)
          (CPoly.eval
            (deflatedCoeffs certificate.coeffs
              [certificate.root₁, certificate.root₂, certificate.root₃]) x) := by
  refine ⟨exactRoot_is_computable certificate.root₁_exact,
    exactRoot_is_computable certificate.root₂_exact,
    exactRoot_is_computable certificate.root₃_exact, ?_⟩
  exact horner_factorization certificate.coeffs
    [certificate.root₁, certificate.root₂, certificate.root₃] x
    certificate.chain

end FiniteDeflationChain

end ComputableAnalysis
