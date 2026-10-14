import ComputableAnalysis.ModularForms.ScalarNonvanishingAlgebra
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- A represented product is nonzero exactly when both of its factors are nonzero. -/
theorem scalar_mul_nonzero_iff (x y : Scalar) :
    NonzeroBoxSearch.Nonzero ⟨mul x.val y.val,mul_valid x.property y.property⟩ ↔
      NonzeroBoxSearch.Nonzero x ∧ NonzeroBoxSearch.Nonzero y := by
  constructor
  · intro hp
    constructor
    · intro hx
      apply hp
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := mul_valid x.property y.property) (hright := ofQComplex_valid _)
      have he := ComplexRawQuotient.ofRaw_eq_ofRaw
        (hleft := x.property) (hright := ofQComplex_valid _) hx
      change ComplexRawQuotient.ofRaw x.val x.property * ComplexRawQuotient.ofRaw y.val y.property = 0
      change ComplexRawQuotient.ofRaw x.val x.property = 0 at he
      rw [he]
      grind only
    · intro hy
      apply hp
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := mul_valid x.property y.property) (hright := ofQComplex_valid _)
      have he := ComplexRawQuotient.ofRaw_eq_ofRaw
        (hleft := y.property) (hright := ofQComplex_valid _) hy
      change ComplexRawQuotient.ofRaw x.val x.property * ComplexRawQuotient.ofRaw y.val y.property = 0
      change ComplexRawQuotient.ofRaw y.val y.property = 0 at he
      rw [he]
      grind only
  · rintro ⟨hx,hy⟩
    exact scalar_mul_nonzero x y hx hy
end ComputableAnalysis.ModularForms
