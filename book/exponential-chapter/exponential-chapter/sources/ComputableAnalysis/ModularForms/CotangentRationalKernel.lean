import ComputableAnalysis.ModularForms.CotangentNomeHolomorphic
import ComputableAnalysis.ModularForms.NomeDenominator
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicAlgebra
import ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic

/-! The actual rational nome kernel on every nonzero-denominator input. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def nomeDenominatorMap : DomainFunctions.Map where
  domain _ := True
  eval z _ := nomeDenominator z
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ he := FunctionTheory.sub_congr (equiv_refl _ (ofQComplex_valid _)) he

def nomeDenominatorMap_holomorphic : DomainFunctions.Holomorphic nomeDenominatorMap := by
  let hf := DomainFunctions.affine_holomorphic ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
    ⟨ofQComplex ⟨-1,0⟩,ofQComplex_valid _⟩
  apply hf.transfer nomeDenominatorMap (fun _ _ => trivial)
    ⟨(fun _ _ => unitError),(fun _ _ _ _ => trivial)⟩
  intro z hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((DomainFunctions.affine ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
      ⟨ofQComplex ⟨-1,0⟩,ofQComplex_valid _⟩).eval z trivial).property)
    (hright := (nomeDenominator z).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change 1+(-1)*Z=1-Z
  grind only

def nomeRationalInverseMap : DomainFunctions.Map := compose ReciprocalHolomorphic.function nomeDenominatorMap

def nomeRationalInverseMap_holomorphic : Holomorphic nomeRationalInverseMap :=
  ReciprocalHolomorphic.holomorphic.compose nomeDenominatorMap_holomorphic

def nomeNumeratorMap : DomainFunctions.Map :=
  DomainFunctions.affine ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩

def cotangentRationalMap : DomainFunctions.Map :=
  productOn nomeRationalInverseMap nomeNumeratorMap (fun _ _ => trivial)

def cotangentRationalMap_holomorphic : Holomorphic cotangentRationalMap :=
  nomeRationalInverseMap_holomorphic.productOn
    (DomainFunctions.affine_holomorphic ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
      ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩) (fun _ _ => trivial)

theorem cotangentRationalMap_domain (z : Scalar) :
    cotangentRationalMap.domain z ↔ NonzeroBoxSearch.Nonzero (nomeDenominator z) := by
  constructor
  · intro hz; exact compose_outer_mem hz
  · intro hz; exact ⟨trivial,hz⟩

theorem cotangentRationalMap_identity (z : Scalar) (hz : cotangentRationalMap.domain z) :
    (mul (nomeDenominator z).val (cotangentRationalMap.eval z hz).val).Equiv
      (add (ofQComplex QComplex.one) z.val) := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property (nomeRationalInverseMap.eval z hz).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse _ (compose_outer_mem hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (nomeDenominator z).property (cotangentRationalMap.eval z hz).property)
    (hright := add_valid (ofQComplex_valid _) z.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (nomeRationalInverseMap.eval z hz).val (nomeRationalInverseMap.eval z hz).property
  change (1-Z)*I=1 at hi
  change (1-Z)*(I*(1+1*Z))=1+Z
  grind only

theorem cotangentRationalMap_series_agreement (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hs : Small z.val r) (hz : cotangentRationalMap.domain z) :
    (cotangentRationalMap.eval z hz).val.Equiv (cotangentNomeKernel z r) := by
  have h1 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property (cotangentRationalMap.eval z hz).property)
    (hright := add_valid (ofQComplex_valid _) z.property) (cotangentRationalMap_identity z hz)
  have h2 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property (cotangentNomeKernel_valid z r hr hlocal hs))
    (hright := add_valid (ofQComplex_valid _) z.property) (cotangentNomeKernel_identity z r hr hlocal hs)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property (nomeRationalInverseMap.eval z hz).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse _ (compose_outer_mem hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (cotangentRationalMap.eval z hz).property) (hright := cotangentNomeKernel_valid z r hr hlocal hs)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (nomeRationalInverseMap.eval z hz).val (nomeRationalInverseMap.eval z hz).property
  let C := ComplexRawQuotient.ofRaw (cotangentRationalMap.eval z hz).val (cotangentRationalMap.eval z hz).property
  let K := ComplexRawQuotient.ofRaw (cotangentNomeKernel z r) (cotangentNomeKernel_valid z r hr hlocal hs)
  change (1-Z)*C=1+Z at h1
  change (1-Z)*K=1+Z at h2
  change (1-Z)*I=1 at hi
  change C=K
  grind only

end ComputableAnalysis.ModularForms
