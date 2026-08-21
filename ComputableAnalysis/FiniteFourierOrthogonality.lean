import ComputableAnalysis.FiniteFourierFoundation

/-!
# Certified finite Fourier orthogonality

The finite Fourier transform is driven by rational-complex arithmetic.  This
file isolates the one algebraic fact that an arbitrary finite transform needs:
the inner products of its certified mode vectors.  Root-of-unity identities
are supplied as finite certificates, so no completed `Real`, topology, or
classical infinite sum is hidden in the interface.
-/

namespace ComputableAnalysis

def finiteFourierModeVector (root : QComplex) (mode length : Nat) : List QComplex :=
  (List.range length).map (fun k =>
    QComplex.natPow root (mode * k))

def finiteFourierModeInnerProduct
    (root : QComplex) (length mode₁ mode₂ : Nat) : QComplex :=
  qcomplexListSum ((List.range length).map (fun k =>
    QComplex.mul
      (QComplex.conj (QComplex.natPow root (mode₁ * k)))
      (QComplex.natPow root (mode₂ * k))))

structure FiniteFourierOrthogonalityCertificate where
  root : QComplex
  length : Nat
  positive_length : 0 < length
  modes : List Nat
  mode_bounded : ∀ mode, mode ∈ modes → mode < length
  inner_product : ∀ mode₁ mode₂,
    mode₁ ∈ modes → mode₂ ∈ modes →
      finiteFourierModeInnerProduct root length mode₁ mode₂ =
        if mode₁ = mode₂ then
          QComplex.ofRat (length : Rat)
        else QComplex.zero

theorem FiniteFourierOrthogonalityCertificate.mode_vector_length
    (certificate : FiniteFourierOrthogonalityCertificate)
    (mode : Nat) :
    (finiteFourierModeVector certificate.root mode certificate.length).length =
      certificate.length := by
  simp [finiteFourierModeVector]

theorem FiniteFourierOrthogonalityCertificate.diagonal_inner_product
    (certificate : FiniteFourierOrthogonalityCertificate)
    {mode : Nat} (hmode : mode ∈ certificate.modes) :
    finiteFourierModeInnerProduct certificate.root certificate.length mode mode =
      QComplex.ofRat (certificate.length : Rat) := by
  simpa using certificate.inner_product mode mode hmode hmode

theorem FiniteFourierOrthogonalityCertificate.off_diagonal_inner_product
    (certificate : FiniteFourierOrthogonalityCertificate)
    {mode₁ mode₂ : Nat}
    (h₁ : mode₁ ∈ certificate.modes)
    (h₂ : mode₂ ∈ certificate.modes)
    (hne : mode₁ ≠ mode₂) :
    finiteFourierModeInnerProduct certificate.root certificate.length mode₁ mode₂ =
      QComplex.zero := by
  simpa [hne] using certificate.inner_product mode₁ mode₂ h₁ h₂

theorem FiniteFourierOrthogonalityCertificate.modes_bounded
    (certificate : FiniteFourierOrthogonalityCertificate)
    {mode : Nat} (hmode : mode ∈ certificate.modes) :
    mode < certificate.length := by
  exact certificate.mode_bounded mode hmode

/-! The certificate is also an executable finite check: every asserted inner
product is a sum over `List.range length`, hence can be instantiated by a
finite rational-complex computation. -/
theorem finiteFourierModeVector_eq_range_map
    (root : QComplex) (mode length : Nat) :
    finiteFourierModeVector root mode length =
      (List.range length).map (fun k =>
        QComplex.natPow root (mode * k)) := by
  rfl

end ComputableAnalysis
