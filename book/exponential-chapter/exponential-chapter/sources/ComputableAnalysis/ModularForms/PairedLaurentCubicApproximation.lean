import ComputableAnalysis.ModularForms.PairedRegularPartCubicCenter

/-! Quantitative pole and first regular coefficient of the actual lattice chart. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedLaurentFirstApproximation (z : Scalar) (hn : NonzeroBoxSearch.Nonzero z) : Scalar :=
  ⟨add (RepresentedReciprocal.inverse z hn).val (mul z.val pairedZeroSquareSum),
    add_valid (RepresentedReciprocal.inverse z hn).property (mul_valid z.property pairedZeroSquareSum_valid)⟩

theorem pairedLaurent_cubic_approximation (z : Scalar) (hz : pairedZeroLaurentMap.domain z)
    (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (pairedZeroLaurentMap.eval z hz).val (pairedLaurentFirstApproximation z hz.2).val)
      (9216*R*R*R) := by
  have he : (sub (pairedRegularPartMap.eval z hz.1).val (mul z.val pairedZeroSquareSum)).Equiv
      (sub (pairedZeroLaurentMap.eval z hz).val (pairedLaurentFirstApproximation z hz.2).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedRegularPartMap.eval z hz.1).property (mul_valid z.property pairedZeroSquareSum_valid))
      (hright := sub_valid (pairedZeroLaurentMap.eval z hz).property (pairedLaurentFirstApproximation z hz.2).property)
    let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz.1).val (pairedRegularPartMap.eval z hz.1).property
    let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz.2).val (RepresentedReciprocal.inverse z hz.2).property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let C := ComplexRawQuotient.ofRaw pairedZeroSquareSum pairedZeroSquareSum_valid
    change S-Z*C=(I+S)-(I+Z*C)
    grind only
  exact Small.congr
    (sub_valid (pairedRegularPartMap.eval z hz.1).property (mul_valid z.property pairedZeroSquareSum_valid))
    (sub_valid (pairedZeroLaurentMap.eval z hz).property (pairedLaurentFirstApproximation z hz.2).property) he
    (pairedRegularPart_cubic_center_bound z hz.1 R hR hs)

theorem pairedUpper_cubic_approximation (z : Scalar) (hz : pairedZeroLaurentMap.domain z)
    (hu : InUpperHalfPlane z.val) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (upperPairedPartialFractionValue z hu) (pairedLaurentFirstApproximation z hz.2).val)
      (9216*R*R*R) :=
  Small.congr (sub_valid (pairedZeroLaurentMap.eval z hz).property (pairedLaurentFirstApproximation z hz.2).property)
    (sub_valid (upperPairedPartialFractionValue_valid z hu) (pairedLaurentFirstApproximation z hz.2).property)
    (FunctionTheory.sub_congr (pairedZeroLaurentMap_upper z hz hu)
      (equiv_refl _ (pairedLaurentFirstApproximation z hz.2).property))
    (pairedLaurent_cubic_approximation z hz R hR hs)

end ComputableAnalysis.ModularForms
