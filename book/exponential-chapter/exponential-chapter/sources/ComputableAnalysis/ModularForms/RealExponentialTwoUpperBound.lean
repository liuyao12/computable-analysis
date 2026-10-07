import ComputableAnalysis.ModularForms.RealExponentialQuadraticPrefixes

/-! A checked finite factorial-series enclosure for the actual exponential at two. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory ComplexExponentialApproximation

/-- The actual represented exponential at two is bounded by eight,
using a kernel-checked rational-series box and proved representation agreement. -/
theorem entireExponential_rational_two_upper_eight :
    (entireExponentialValue ⟨ofQComplex ⟨2,0⟩,ofQComplex_valid _⟩).val.realPart.Le (RealRaw.ofRat 8) := by
  let f := exponentialRawAt ⟨2,0⟩ 2
  have hz : QComplex.normBound (⟨2,0⟩ : QComplex)≤(2:Rat) := by decide +kernel
  have hf : f.Valid := exponentialRawAt_valid (by decide +kernel) hz
  have hbox : (f.compute 2).hi.re≤(8:Rat) := by decide +kernel
  have hl : f.realPart.Le (RealRaw.ofRat 8) := by
    intro n m
    have h := RealRaw.le_refl f.realPart (realPart_valid hf) n 2
    change (f.compute n).lo.re≤8
    exact Rat.le_trans h hbox
  have he := ComplexRaw.realPart_equiv (entireExponential_legacy_rational ⟨2,0⟩ 2 (by decide +kernel) hz)
  exact RealRaw.le_trans (realPart_valid hf)
    (RealRaw.le_of_equiv (realPart_valid (entireExponentialValue _).property) (realPart_valid hf) he) hl

end ComputableAnalysis.ModularForms
