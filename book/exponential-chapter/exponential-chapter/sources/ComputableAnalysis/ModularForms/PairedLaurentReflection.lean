import ComputableAnalysis.ModularForms.PairedRegularDivisionEven
import ComputableAnalysis.ModularForms.PairedRiccatiLaurentNormalization

/-! Exact odd reflection symmetry of the constructed lattice Laurent function. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedRegularPart_odd (z w : Scalar) (hz : Small z.val (1/4))
    (hw : Small w.val (1/4)) (he : w.val.Equiv (neg z.val)) :
    (pairedRegularPart w hw).Equiv (neg (pairedRegularPart z hz)) := by
  have ht := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := pairedRegularDivisionValue_valid w hw)
    (hright := pairedRegularDivisionValue_valid z hz)
    (pairedRegularDivisionValue_even z w hz hw he)
  have hpz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (pairedRegularDivisionValue_valid z hz))
    (hright := pairedRegularPart_valid z hz) (pairedRegularDivisionValue_product z hz)
  have hpw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid w.property (pairedRegularDivisionValue_valid w hw))
    (hright := pairedRegularPart_valid w hw) (pairedRegularDivisionValue_product w hw)
  have hzw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := w.property) (hright := neg_valid z.property) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := pairedRegularPart_valid w hw)
    (hright := neg_valid (pairedRegularPart_valid z hz))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionValue z hz) (pairedRegularDivisionValue_valid z hz)
  let U := ComplexRawQuotient.ofRaw (pairedRegularDivisionValue w hw) (pairedRegularDivisionValue_valid w hw)
  let S := ComplexRawQuotient.ofRaw (pairedRegularPart z hz) (pairedRegularPart_valid z hz)
  let V := ComplexRawQuotient.ofRaw (pairedRegularPart w hw) (pairedRegularPart_valid w hw)
  change U=T at ht
  change Z*T=S at hpz
  change W*U=V at hpw
  change W= -Z at hzw
  change V= -S
  grind only

theorem pairedZeroLaurent_odd (z w : Scalar)
    (hz : pairedZeroLaurentMap.domain z) (hw : pairedZeroLaurentMap.domain w)
    (he : w.val.Equiv (neg z.val)) :
    (pairedZeroLaurentMap.eval w hw).val.Equiv
      (neg (pairedZeroLaurentMap.eval z hz).val) := by
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := pairedRegularPart_valid w (LocalODE.interior_bound _ w hw.1))
    (hright := neg_valid (pairedRegularPart_valid z (LocalODE.interior_bound _ z hz.1)))
    (pairedRegularPart_odd z w (LocalODE.interior_bound _ z hz.1)
      (LocalODE.interior_bound _ w hw.1) he)
  have hzw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := w.property) (hright := neg_valid z.property) he
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (RepresentedReciprocal.inverse z hz.2).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse z hz.2)
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid w.property (RepresentedReciprocal.inverse w hw.2).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse w hw.2)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedZeroLaurentMap.eval w hw).property)
    (hright := neg_valid (pairedZeroLaurentMap.eval z hz).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz.2).val (RepresentedReciprocal.inverse z hz.2).property
  let J := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse w hw.2).val (RepresentedReciprocal.inverse w hw.2).property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPart z (LocalODE.interior_bound _ z hz.1))
    (pairedRegularPart_valid z (LocalODE.interior_bound _ z hz.1))
  let T := ComplexRawQuotient.ofRaw (pairedRegularPart w (LocalODE.interior_bound _ w hw.1))
    (pairedRegularPart_valid w (LocalODE.interior_bound _ w hw.1))
  change T= -S at hs
  change W= -Z at hzw
  change Z*I=1 at hi
  change W*J=1 at hj
  change J+T= -(I+S)
  grind only

end ComputableAnalysis.ModularForms
