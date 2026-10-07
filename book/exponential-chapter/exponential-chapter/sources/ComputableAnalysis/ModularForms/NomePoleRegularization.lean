import ComputableAnalysis.ModularForms.RegularizedReciprocalSecondDerivative

/-! A holomorphic nome quotient through the cotangent pole. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def entireNomeMap : DomainFunctions.Map :=
  compose entireExponential (affine ⟨zero,ofQComplex_valid _⟩ nomeSlope)

def entireNomeMap_holomorphic : Holomorphic entireNomeMap :=
  entireExponential_holomorphic.compose (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ nomeSlope)

theorem entireNomeMap_mem (z : Scalar) : entireNomeMap.domain z := ⟨trivial,trivial⟩

theorem entireNomeMap_upper_agreement (z : Scalar) (hu : InUpperHalfPlane z.val) :
    (entireNomeMap.eval z (entireNomeMap_mem z)).val.Equiv (nome.eval z hu).val :=
  entireExponentialValue_congr _ _ (zero_add_equiv _ (mul_valid nomeSlope.property z.property))

theorem entireNomeMap_center (z : Scalar) (he : z.val.Equiv zero) :
    (entireNomeMap.eval z (entireNomeMap_mem z)).val.Equiv (ofQComplex QComplex.one) := by
  have ha : ((affine ⟨zero,ofQComplex_valid _⟩ nomeSlope).eval z trivial).val.Equiv zero := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((affine ⟨zero,ofQComplex_valid _⟩ nomeSlope).eval z trivial).property)
      (hright := ofQComplex_valid _)
    have hz := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := ofQComplex_valid _) he
    let Z := gridScalarValue z
    let A := gridScalarValue nomeSlope
    change Z=0 at hz
    change 0+A*Z=0
    rw [hz]
    grind only
  exact equiv_trans (entireNomeMap.eval z (entireNomeMap_mem z)).property
    (entireExponentialValue ⟨zero,ofQComplex_valid _⟩).property (ofQComplex_valid _)
    (entireExponentialValue_congr _ _ ha) entireExponential_zero

def nomePlusDenominatorMap : DomainFunctions.Map :=
  affine ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩

def nomePlusDenominatorMap_holomorphic : Holomorphic nomePlusDenominatorMap :=
  affine_holomorphic ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩

def nomePlusInverseMap : DomainFunctions.Map := compose ReciprocalHolomorphic.function nomePlusDenominatorMap

def nomePlusInverseMap_holomorphic : Holomorphic nomePlusInverseMap :=
  ReciprocalHolomorphic.holomorphic.compose nomePlusDenominatorMap_holomorphic

def nomeReciprocalQuotientMap : DomainFunctions.Map :=
  productOn nomePlusInverseMap nomeDenominatorMap (fun _ _ => trivial)

def nomeReciprocalQuotientMap_holomorphic : Holomorphic nomeReciprocalQuotientMap :=
  nomePlusInverseMap_holomorphic.productOn nomeDenominatorMap_holomorphic (fun _ _ => trivial)

theorem nomeReciprocalQuotient_at_one_mem (q : Scalar) (he : q.val.Equiv (ofQComplex QComplex.one)) :
    nomeReciprocalQuotientMap.domain q := by
  refine ⟨trivial,?_⟩
  intro hn
  have hz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (nomePlusDenominatorMap.eval q trivial).property) (hright := ofQComplex_valid _) hn
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property) (hright := ofQComplex_valid _) he
  have hbad : (2:Int)=(0:ScalarAlgebra.Value) := by
    let Q := gridScalarValue q
    change 1+1*Q=0 at hz
    change Q=1 at hq
    rw [hq] at hz
    grind only
  have hzero : (ofQComplex ⟨2,0⟩).Equiv zero := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := ofQComplex_valid _) (hright := ofQComplex_valid _)
    change ComplexRawQuotient.ofQComplex ⟨2,0⟩=(0:ScalarAlgebra.Value)
    have hi := integer_constant (2:Int)
    change ComplexRawQuotient.ofQComplex ⟨2,0⟩=(2:Int) at hi
    rw [hi]
    exact hbad
  have hh := (compareAt_overlap_iff _ _ 0 0).1 (hzero 0)
  have ht := hh.1.1
  change (2:Rat)≤0 at ht
  grind only

def entireNomeReciprocalQuotientMap : DomainFunctions.Map :=
  compose nomeReciprocalQuotientMap entireNomeMap

def entireNomeReciprocalQuotientMap_holomorphic : Holomorphic entireNomeReciprocalQuotientMap :=
  nomeReciprocalQuotientMap_holomorphic.compose entireNomeMap_holomorphic

theorem entireNomeReciprocalQuotient_center_mem (z : Scalar) (he : z.val.Equiv zero) :
    entireNomeReciprocalQuotientMap.domain z :=
  ⟨entireNomeMap_mem z,nomeReciprocalQuotient_at_one_mem _ (entireNomeMap_center z he)⟩

theorem entireNomeReciprocalQuotient_center (z : Scalar) (he : z.val.Equiv zero) :
    (entireNomeReciprocalQuotientMap.eval z (entireNomeReciprocalQuotient_center_mem z he)).val.Equiv zero := by
  let hz := entireNomeReciprocalQuotient_center_mem z he
  let q := entireNomeMap.eval z (compose_inner_mem hz)
  let hq := compose_outer_mem hz
  have h1 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property) (hright := ofQComplex_valid _)
    (entireNomeMap_center z he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (entireNomeReciprocalQuotientMap.eval z hz).property) (hright := ofQComplex_valid _)
  let Q := gridScalarValue q
  let I := gridScalarValue (nomePlusInverseMap.eval q hq)
  change Q=1 at h1
  change I*(1-Q)=0
  rw [h1]
  grind only

theorem entireNomeReciprocalQuotient_center_derivative_twice (z : Scalar) (he : z.val.Equiv zero) :
    (add
      (entireNomeReciprocalQuotientMap_holomorphic.derivative z (entireNomeReciprocalQuotient_center_mem z he)).val
      (entireNomeReciprocalQuotientMap_holomorphic.derivative z (entireNomeReciprocalQuotient_center_mem z he)).val).Equiv
      (neg nomeSlope.val) := by
  let hz := entireNomeReciprocalQuotient_center_mem z he
  let q := entireNomeMap.eval z (compose_inner_mem hz)
  let hq := compose_outer_mem hz
  let i := nomePlusInverseMap.eval q hq
  let a := (affine ⟨zero,ofQComplex_valid _⟩ nomeSlope).eval z trivial
  have h1 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property) (hright := ofQComplex_valid _)
    (entireNomeMap_center z he)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomePlusDenominatorMap.eval q trivial).property i.property)
    (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomePlusDenominatorMap.eval q trivial) (compose_outer_mem hq))
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponential_holomorphic.derivative a trivial).property) (hright := q.property)
    (entireExponential_derivative_value a)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (entireNomeReciprocalQuotientMap_holomorphic.derivative z hz).property
      (entireNomeReciprocalQuotientMap_holomorphic.derivative z hz).property)
    (hright := neg_valid nomeSlope.property)
  let Q := gridScalarValue q
  let I := gridScalarValue i
  let E := gridScalarValue (entireExponential_holomorphic.derivative a trivial)
  let A := gridScalarValue nomeSlope
  change Q=1 at h1
  change (1+1*Q)*I=1 at hi
  change E=Q at hd
  change (((-(I*I)*1)*(1-Q)+I*(-1))*(E*A))+
    (((-(I*I)*1)*(1-Q)+I*(-1))*(E*A))= -A
  rw [h1] at hi hd ⊢
  rw [hd]
  grind only

end ComputableAnalysis.ModularForms
