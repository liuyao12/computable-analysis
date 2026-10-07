import ComputableAnalysis.ModularForms.PairedRiccatiPoleCancellation
import ComputableAnalysis.ModularForms.PairedRegularDivisionAgreement

/-! A represented extension of the unweighted lattice Riccati expression. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedRiccatiExtension (z : Scalar) (hz : LocalODE.interior (1/4) z) : Scalar :=
  let hq := LocalODE.interior_bound _ z hz
  let t : Scalar := ⟨pairedRegularDivisionValue z hq,pairedRegularDivisionValue_valid z hq⟩
  let s := pairedRegularPartMap.eval z hz
  DomainFunctions.scalarSum (pairedRegularPartDerivative z hz)
    (DomainFunctions.scalarSum (DomainFunctions.scalarSum t t) (DomainFunctions.scalarProduct s s))

theorem pairedLaurent_riccati_extension (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    (add (pairedZeroLaurentMap_holomorphic.derivative z hz).val
      (mul (pairedZeroLaurentMap.eval z hz).val (pairedZeroLaurentMap.eval z hz).val)).Equiv
      (pairedRiccatiExtension z hz.1).val := by
  let hq := LocalODE.interior_bound _ z hz.1
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (RepresentedReciprocal.inverse z hz.2).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse z hz.2)
  have ht := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (pairedRegularDivisionValue_valid z hq))
    (hright := pairedRegularPart_valid z hq) (pairedRegularDivisionValue_product z hq)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (pairedZeroLaurentMap_holomorphic.derivative z hz).property
      (mul_valid (pairedZeroLaurentMap.eval z hz).property (pairedZeroLaurentMap.eval z hz).property))
    (hright := (pairedRiccatiExtension z hz.1).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz.2).val (RepresentedReciprocal.inverse z hz.2).property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPart z hq) (pairedRegularPart_valid z hq)
  let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionValue z hq) (pairedRegularDivisionValue_valid z hq)
  let D := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz.1).val (pairedRegularPartDerivative z hz.1).property
  change Z*I=1 at hi
  change Z*T=S at ht
  change (-(I*I)+D)+(I+S)*(I+S)=D+((T+T)+S*S)
  grind only

theorem pairedRiccatiExtension_congr (z w : Scalar)
    (hz : LocalODE.interior (1/4) z) (hw : LocalODE.interior (1/4) w)
    (he : z.val.Equiv w.val) :
    (pairedRiccatiExtension z hz).val.Equiv (pairedRiccatiExtension w hw).val := by
  have ht := pairedRegularDivisionValue_congr z w
    (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ w hw) he
  have hs := pairedRegularPartMap.eval_congr z w hz hw he
  exact add_equiv (pairedRegularPartDerivative_congr z w hz hw he)
    (add_equiv (add_equiv ht ht)
      (mul_equiv (pairedRegularPartMap.eval z hz).property (pairedRegularPartMap.eval w hw).property
        (pairedRegularPartMap.eval z hz).property (pairedRegularPartMap.eval w hw).property hs hs))

end ComputableAnalysis.ModularForms
