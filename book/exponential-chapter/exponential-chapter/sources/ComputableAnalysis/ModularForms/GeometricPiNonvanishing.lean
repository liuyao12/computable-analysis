import ComputableAnalysis.ModularForms.CMGrowthSharperBounds163
import ComputableAnalysis.ModularForms.NomeRiccatiConstant

/-! Nonvanishing of the actual geometric pi scalar from a checked angle bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The geometric pi scalar is a justified nonzero represented value. -/
theorem geometricPiScalar_nonzero : NonzeroBoxSearch.Nonzero geometricPiScalar := by
  have hl : (RealRaw.ofRat 3).Le geometricPiScalar.val.realPart := by
    intro n m
    have h := halfPi_lower_three_halves 0 m
    change (3/2:Rat)≤(GeometricPiRotation.halfPi.compute m).hi at h
    change (3:Rat)≤2*(GeometricPiRotation.halfPi.compute m).hi
    grind only
  intro he
  have hu := RealRaw.le_of_equiv (realPart_valid geometricPiScalar.property)
    (realPart_valid (ofQComplex_valid QComplex.zero)) (realPart_equiv he)
  have ht := RealRaw.le_trans (realPart_valid geometricPiScalar.property) hl hu
  have h := ht 0 0
  change (3:Rat)≤0 at h
  contradiction

end ComputableAnalysis.ModularForms
