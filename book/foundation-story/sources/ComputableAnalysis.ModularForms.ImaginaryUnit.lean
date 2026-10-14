import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal

/-! The rational imaginary unit, independently of lattice constructions. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

/-- The existing imaginary-unit API, now with only rational-box dependencies. -/
def latticeImaginaryUnit : Scalar := ⟨ofQComplex ⟨0,1⟩,ofQComplex_valid _⟩

end ComputableAnalysis.ModularForms
