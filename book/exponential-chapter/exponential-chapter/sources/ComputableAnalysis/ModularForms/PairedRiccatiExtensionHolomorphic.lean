import ComputableAnalysis.ModularForms.PairedDivisionFirstDerivativeHolomorphic
import ComputableAnalysis.ModularForms.PairedRegularDivisionProductDerivative

/-! Holomorphic extension of the actual lattice Riccati expression through its pole. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedRiccatiExtensionMap : DomainFunctions.Map where
  domain := LocalODE.interior (1/4)
  eval := pairedRiccatiExtension
  domain_congr := pairedRegularDivisionMap.domain_congr
  eval_congr := pairedRiccatiExtension_congr

def pairedRiccatiExtensionMap_holomorphic : Holomorphic pairedRiccatiExtensionMap := by
  let hid := affine_holomorphic ⟨zero,ofQComplex_valid _⟩
    ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
  let hzd := pairedDivisionFirstDerivativeMap_holomorphic.productOn hid (fun _ _ => trivial)
  let hss := pairedRegularPartMap_holomorphic.productOn pairedRegularPartMap_holomorphic (fun _ hz => hz)
  let hrest := hzd.sumOn hss (fun _ hz => hz)
  let ht := pairedRegularDivisionMap_holomorphic
  let id := affine ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
  let rest := sumOn (productOn pairedDivisionFirstDerivativeMap id (fun _ _ => trivial))
    (productOn pairedRegularPartMap pairedRegularPartMap (fun _ hz => hz)) (fun _ hz => hz)
  let f := sumOn pairedRegularDivisionMap (sumOn pairedRegularDivisionMap
    (sumOn pairedRegularDivisionMap rest (fun _ hz => hz)) (fun _ hz => hz)) (fun _ hz => hz)
  let hf : Holomorphic f := ht.sumOn (ht.sumOn (ht.sumOn hrest (fun _ hz => hz)) (fun _ hz => hz)) (fun _ hz => hz)
  apply hf.transfer pairedRiccatiExtensionMap (fun _ hz => hz)
    ⟨LocalODE.interiorRadius (1/4),LocalODE.interiorRadius_inside (1/4)⟩
  intro z hz
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularPartDerivative z hz).property)
    (hright := add_valid (pairedRegularDivisionMap.eval z hz).property
      (mul_valid z.property (pairedRegularDivisionDerivative z hz).property))
    (pairedRegularPartDerivative_division z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (f.eval z hz).property)
    (hright := (pairedRiccatiExtension z hz).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).property
  let D := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative z hz).val (pairedRegularDivisionDerivative z hz).property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz).val (pairedRegularPartMap.eval z hz).property
  let SD := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz).val (pairedRegularPartDerivative z hz).property
  change SD=T+Z*D at hd
  change T+(T+(T+(D*(0+1*Z)+S*S)))=SD+((T+T)+S*S)
  grind only

end ComputableAnalysis.ModularForms
