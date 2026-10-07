import ComputableAnalysis.ModularForms.LatticeDiscriminant
import ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic

/-! The actual lattice j evaluator on its justified nonzero-discriminant domain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def latticeDiscriminantReciprocalMap : DomainFunctions.Map :=
  compose ReciprocalHolomorphic.function latticeDiscriminantMap

def latticeDiscriminantReciprocalMap_holomorphic : Holomorphic latticeDiscriminantReciprocalMap :=
  ReciprocalHolomorphic.holomorphic.compose latticeDiscriminantMap_holomorphic

private def latticeJNumeratorMap : DomainFunctions.Map :=
  productOn (constantOn (fun z => InUpperHalfPlane z.val) upperOpenData.invariant
    ⟨ofQComplex ⟨1728,0⟩,ofQComplex_valid _⟩) latticeG2CubeMap (fun _ hz => hz)

private def latticeJNumeratorMap_holomorphic : Holomorphic latticeJNumeratorMap :=
  (constantOn_holomorphic upperOpenData ⟨ofQComplex ⟨1728,0⟩,ofQComplex_valid _⟩).productOn
    latticeG2CubeMap_holomorphic (fun _ hz => hz)

def latticeJMap : DomainFunctions.Map :=
  productOn latticeDiscriminantReciprocalMap latticeJNumeratorMap (fun _ hz => hz.1)

def latticeJMap_holomorphic : Holomorphic latticeJMap :=
  latticeDiscriminantReciprocalMap_holomorphic.productOn latticeJNumeratorMap_holomorphic
    (fun _ hz => hz.1)

theorem latticeJMap_domain (z : Scalar) : latticeJMap.domain z ↔
    ∃ hz : InUpperHalfPlane z.val, NonzeroBoxSearch.Nonzero (latticeDiscriminantMap.eval z hz) := by
  constructor
  · intro hz; exact ⟨hz.1,hz.2⟩
  · rintro ⟨hz,hn⟩; exact ⟨hz,hn⟩

theorem latticeJMap_discriminant_product (z : Scalar) (hz : latticeJMap.domain z) :
    (mul (latticeJMap.eval z hz).val (latticeDiscriminantMap.eval z hz.1).val).Equiv
      (mul (ofQComplex ⟨1728,0⟩) (latticeG2CubeMap.eval z hz.1).val) := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (latticeDiscriminantMap.eval z hz.1).property
      (RepresentedReciprocal.inverse (latticeDiscriminantMap.eval z hz.1) hz.2).property)
    (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (latticeDiscriminantMap.eval z hz.1) hz.2)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (latticeJMap.eval z hz).property (latticeDiscriminantMap.eval z hz.1).property)
    (hright := mul_valid (ofQComplex_valid _) (latticeG2CubeMap.eval z hz.1).property)
  let D := ComplexRawQuotient.ofRaw (latticeDiscriminantMap.eval z hz.1).val
    (latticeDiscriminantMap.eval z hz.1).property
  let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse (latticeDiscriminantMap.eval z hz.1) hz.2).val
    (RepresentedReciprocal.inverse (latticeDiscriminantMap.eval z hz.1) hz.2).property
  let N := ComplexRawQuotient.ofRaw (latticeG2CubeMap.eval z hz.1).val
    (latticeG2CubeMap.eval z hz.1).property
  let C := ComplexRawQuotient.ofQComplex ⟨1728,0⟩
  change D*R=1 at hi
  change (R*(C*N))*D=C*N
  grind only

end ComputableAnalysis.ModularForms
