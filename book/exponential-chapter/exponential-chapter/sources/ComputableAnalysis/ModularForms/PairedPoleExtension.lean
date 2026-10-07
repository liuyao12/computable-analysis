import ComputableAnalysis.ModularForms.PairedRegularPartHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicAlgebra

/-! Holomorphic pole normalization of the actual reciprocal series through zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedPoleExtensionMap : DomainFunctions.Map where
  domain := pairedRegularPartMap.domain
  eval z hz := ⟨add (ofQComplex QComplex.one)
    (mul z.val (pairedRegularPartMap.eval z hz).val),
    add_valid (ofQComplex_valid _) (mul_valid z.property (pairedRegularPartMap.eval z hz).property)⟩
  domain_congr := pairedRegularPartMap.domain_congr
  eval_congr z w hz hw he := add_equiv (equiv_refl _ (ofQComplex_valid _))
    (mul_equiv z.property w.property (pairedRegularPartMap.eval z hz).property
      (pairedRegularPartMap.eval w hw).property he (pairedRegularPartMap.eval_congr z w hz hw he))

def pairedPoleExtensionMap_holomorphic : DomainFunctions.Holomorphic pairedPoleExtensionMap := by
  let f := affine ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
  let hf := affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
  let hfg := fun (z : Scalar) (hz : pairedRegularPartMap.domain z) => (show f.domain z from trivial)
  let openData : ScalarTopology.OpenData pairedRegularPartMap.domain :=
    ⟨pairedRegularPartMap.domain_congr,LocalODE.interiorRadius (1/4),LocalODE.interiorRadius_inside (1/4)⟩
  have h := (constantOn_holomorphic openData ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩).sumOn
    (pairedRegularPartMap_holomorphic.productOn hf hfg)
    (fun (z : Scalar) (hz : pairedRegularPartMap.domain z) => hz)
  apply h.transfer pairedPoleExtensionMap
    (fun (z : Scalar) (hz : pairedPoleExtensionMap.domain z) => hz)
    ⟨LocalODE.interiorRadius (1/4),LocalODE.interiorRadius_inside (1/4)⟩
  intro z hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((sumOn (constantOn pairedRegularPartMap.domain openData.invariant
      ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩)
      (productOn pairedRegularPartMap f hfg)
      (fun (z : Scalar) (hz : pairedRegularPartMap.domain z) => hz)).eval z hz).property)
    (hright := (pairedPoleExtensionMap.eval z hz).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz).val (pairedRegularPartMap.eval z hz).property
  change 1+S*(0+1*Z)=1+Z*S
  grind only

theorem pairedPoleExtensionMap_upper (z : Scalar) (hz : pairedPoleExtensionMap.domain z)
    (hupper : InUpperHalfPlane z.val) :
    (pairedPoleExtensionMap.eval z hz).val.Equiv (mul z.val (upperPairedPartialFractionValue z hupper)) := by
  have vP := mul_valid z.property (upperPairedPartialFractionValue_valid z hupper)
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := sub_valid vP (ofQComplex_valid _))
    (hright := mul_valid z.property (pairedRegularPart_valid z (LocalODE.interior_bound _ z hz)))
    (pairedZeroPole_normalization z hupper (LocalODE.interior_bound _ z hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedPoleExtensionMap.eval z hz).property) (hright := vP)
  let P := ComplexRawQuotient.ofRaw (mul z.val (upperPairedPartialFractionValue z hupper)) vP
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz).val (pairedRegularPartMap.eval z hz).property
  change P-1=Z*S at h
  change 1+Z*S=P
  grind only

theorem pairedPoleExtensionMap_zero (z : Scalar) (hz : pairedPoleExtensionMap.domain z)
    (hzero : z.val.Equiv zero) :
    (pairedPoleExtensionMap.eval z hz).val.Equiv (ofQComplex QComplex.one) := by
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := ofQComplex_valid _) hzero
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedPoleExtensionMap.eval z hz).property) (hright := ofQComplex_valid _)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz).val (pairedRegularPartMap.eval z hz).property
  change Z=0 at h
  change 1+Z*S=1
  grind only

end ComputableAnalysis.ModularForms
