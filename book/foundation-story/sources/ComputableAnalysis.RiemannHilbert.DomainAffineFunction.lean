import ComputableAnalysis.RiemannHilbert.DomainHolomorphicAlgebra

/-! Actual entire affine scalar functions at arbitrary represented
coefficients, with exact zero remainder and executable derivative data. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def affine (a b : Scalar) : Map where
  domain _ := True
  eval z _ := scalarSum a (scalarProduct b z)
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ hzw := add_equiv (equiv_refl _ a.property)
    (mul_equiv b.property b.property z.property w.property (equiv_refl _ b.property) hzw)

theorem affine_remainder (a b p z : Scalar) : (remainder (affine a b) p trivial b z trivial).Equiv zero := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := remainder_valid _ _ _ _ _ _) (hright := ofQComplex_valid _)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let P := ComplexRawQuotient.ofRaw p.val p.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change ((A+B*Z) + -(A+B*P)) + -(B*(Z + -P)) = 0
  grind

def affine_holomorphic (a b : Scalar) : Holomorphic (affine a b) where
  openDomain := { radius := fun _ _ => unitError, inside := fun _ _ _ _ => trivial }
  derivative _ _ := b
  atPoint p _ := {
    delta := fun _ => unitError
    estimate eps H z _ _ _ := Small.congr (ofQComplex_valid _) (remainder_valid _ _ _ _ _ _)
      (equiv_symm (affine_remainder a b p z))
      (Small.zero (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property))) }
  derivative_congr _ _ _ _ _ := equiv_refl _ b.property
  continuousDerivative := {
    delta := fun _ _ _ => unitError
    estimate _ _ eps _ _ _ := Small.congr (ofQComplex_valid _) (sub_valid b.property b.property)
      (equiv_symm (add_neg_equiv b.val b.property)) (Small.zero (Rat.le_of_lt eps.property)) }

def oneScalar : Scalar := ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩

def shift (a : Scalar) : Map := affine (scalarNeg a) oneScalar

def residual (a : Scalar) : Map := affine oneScalar (scalarNeg a)

theorem shift_zero_iff (a z : Scalar) : ((shift a).eval z trivial).val.Equiv zero ↔ z.val.Equiv a.val := by
  constructor
  · intro h
    have he := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ((shift a).eval z trivial).property) (hright := ofQComplex_valid _) h
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := z.property) (hright := a.property)
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change -A+1*Z=0 at he
    change Z=A
    grind
  · intro h
    have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := a.property) h
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((shift a).eval z trivial).property) (hright := ofQComplex_valid _)
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change Z=A at he
    change -A+1*Z=0
    grind

end ComputableAnalysis.RiemannHilbert.DomainFunctions
