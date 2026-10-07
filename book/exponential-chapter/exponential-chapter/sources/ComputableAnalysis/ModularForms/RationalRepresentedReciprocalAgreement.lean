import ComputableAnalysis.ModularForms.PairedRiccatiCauchyIntegrand

/-! Exact agreement between rational inverse arithmetic and represented inversion. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem rationalConstant_inverse_identity (q : QComplex) (hq : QComplex.normSq q≠0) :
    (mul (ofQComplex q) (ofQComplex (RationalReciprocal.inverse q))).Equiv one := by
  have h := RationalReciprocal.raw_mul_constants q (RationalReciprocal.inverse q)
  rw [RationalReciprocal.mul_inverse q hq] at h
  exact h

theorem rationalConstant_nonzero (q : QComplex) (hq : QComplex.normSq q≠0) :
    NonzeroBoxSearch.Nonzero (⟨ofQComplex q,ofQComplex_valid _⟩ : Scalar) :=
  RepresentedReciprocal.nonzero_of_inverse _
    ⟨ofQComplex (RationalReciprocal.inverse q),ofQComplex_valid _⟩
    (rationalConstant_inverse_identity q hq)

theorem representedInverse_rational_agreement (q : QComplex) (hq : QComplex.normSq q≠0)
    (hz : NonzeroBoxSearch.Nonzero (⟨ofQComplex q,ofQComplex_valid _⟩ : Scalar)) :
    (RepresentedReciprocal.inverse ⟨ofQComplex q,ofQComplex_valid _⟩ hz).val.Equiv
      (ofQComplex (RationalReciprocal.inverse q)) :=
  RepresentedReciprocal.inverse_unique _ hz
    ⟨ofQComplex (RationalReciprocal.inverse q),ofQComplex_valid _⟩
    (rationalConstant_inverse_identity q hq)

theorem scaledSquarePoint_normSq_nonzero (edge : PDE.CauchyContour.HalfEdge)
    (u R : Rat) (hR : 0<R) :
    QComplex.normSq (QComplex.scaleRat R (PDE.CauchyContour.point edge u))≠0 := by
  intro h
  have hz := QComplex.normSq_eq_zero_iff.mp h
  have hs := scaledSquarePoint_coordinate_separated edge u R
  rw [hz] at hs
  change R≤0 ∨ 0≤ -R ∨ R≤0 ∨ 0≤ -R at hs
  grind only

end ComputableAnalysis.ModularForms
