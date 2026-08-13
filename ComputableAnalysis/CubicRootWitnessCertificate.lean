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
  root1 : QComplex
  root2 : QComplex
  root3 : QComplex
  root1_exact : CPoly.hasExactRoot coeffs root1
  root2_exact : CPoly.hasExactRoot coeffs root2
  root3_exact : CPoly.hasExactRoot coeffs root3
  chain : IsDeflationChain coeffs [root1, root2, root3]

theorem CubicRootWitnessCertificate.computable_roots_and_factorization
    (certificate : CubicRootWitnessCertificate) (x : QComplex) :
    (IsComputableRoot certificate.coeffs (exactComplexCert certificate.root1)) /\
      (IsComputableRoot certificate.coeffs (exactComplexCert certificate.root2)) /\
      (IsComputableRoot certificate.coeffs (exactComplexCert certificate.root3)) /\
      CPoly.eval certificate.coeffs x =
        QComplex.mul
          (rootFactorProduct
            [certificate.root1, certificate.root2, certificate.root3] x)
          (CPoly.eval
            (deflatedCoeffs certificate.coeffs
              [certificate.root1, certificate.root2, certificate.root3]) x) := by
  refine ⟨exactRoot_is_computable certificate.root1_exact,
    exactRoot_is_computable certificate.root2_exact,
    exactRoot_is_computable certificate.root3_exact, ?_⟩
  exact FiniteDeflationChain.horner_factorization certificate.coeffs
    [certificate.root1, certificate.root2, certificate.root3] x
    certificate.chain

end FiniteDeflationChain

end ComputableAnalysis
