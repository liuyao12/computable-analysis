import ComputableAnalysis.ModularForms.NomeDenominator
import ComputableAnalysis.ModularForms.PairedPartialFractionQuotient

/-! Quantitative square normalization for paired partial-fraction denominators. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedNormalizedSquare (z : Scalar) (c : Rat) : Scalar :=
  ⟨scaleRat c (mul z.val z.val),scaleRat_valid (mul_valid z.property z.property)⟩

theorem pairedNormalizedSquare_small (z : Scalar) (R c : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R) :
    Small (pairedNormalizedSquare z c).val (c*(2*R*R)) :=
  LocalODE.small_scale hc (Small.mul z.property z.property hR hR hz hz)

theorem pairedNormalizedSquare_eighth (z : Scalar) (R c : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R) (hsmall : c*(2*R*R)≤(1:Rat)/8) :
    Small (pairedNormalizedSquare z c).val ((1:Rat)/8) :=
  (pairedNormalizedSquare_small z R c hR hc hz).mono hsmall

theorem pairedNormalizedDenominator_nonzero (z : Scalar) (R c : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R) (hsmall : c*(2*R*R)≤(1:Rat)/8) :
    NonzeroBoxSearch.Nonzero (nomeDenominator (pairedNormalizedSquare z c)) :=
  nomeDenominator_nonzero (pairedNormalizedSquare z c) (1/8) (by decide +kernel)
    (by decide +kernel) (pairedNormalizedSquare_eighth z R c hR hc hz hsmall)

theorem pairedNormalizedGeometric_bound (z : Scalar) (R c : Rat)
    (hR : 0≤R) (hc : 0≤c) (hz : Small z.val R) (hsmall : c*(2*R*R)≤(1:Rat)/8) :
    Small (nomeGeometricSum (pairedNormalizedSquare z c) (1/8)) 4 := by
  exact nomeGeometricSum_bound (pairedNormalizedSquare z c) (1/8) (by decide +kernel)
    (by decide +kernel) (pairedNormalizedSquare_eighth z R c hR hc hz hsmall)

end ComputableAnalysis.ModularForms
