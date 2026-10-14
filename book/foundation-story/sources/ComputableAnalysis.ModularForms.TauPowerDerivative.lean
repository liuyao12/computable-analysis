import ComputableAnalysis.ModularForms.TauFiniteProductHolomorphic

/-! Exact derivatives of the actual represented map powers used in Euler factors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem power_derivative_step (f : DomainFunctions.Map) (hf : Holomorphic f)
    (q : Scalar) (hq : f.domain q) (n : Nat) :
    ComplexRawQuotient.ofRaw ((tauMapPower_holomorphic f hf (n+1)).derivative q hq).val
      ((tauMapPower_holomorphic f hf (n+1)).derivative q hq).property =
      ComplexRawQuotient.ofRaw ((tauMapPower_holomorphic f hf n).derivative q hq).val
        ((tauMapPower_holomorphic f hf n).derivative q hq).property *
        ComplexRawQuotient.ofRaw (f.eval q hq).val (f.eval q hq).property +
      (ComplexRawQuotient.ofRaw (f.eval q hq).val (f.eval q hq).property)^n *
        ComplexRawQuotient.ofRaw (hf.derivative q hq).val (hf.derivative q hq).property := by
  change ComplexRawQuotient.ofRaw ((tauMapPower_holomorphic f hf n).derivative q hq).val
      ((tauMapPower_holomorphic f hf n).derivative q hq).property *
      ComplexRawQuotient.ofRaw (f.eval q hq).val (f.eval q hq).property +
    ComplexRawQuotient.ofRaw (LocalODE.power (f.eval q hq).val n)
      (LocalODE.power_valid _ (f.eval q hq).property n) *
      ComplexRawQuotient.ofRaw (hf.derivative q hq).val (hf.derivative q hq).property = _
  rw [ScalarAlgebra.ofRaw_power]

private theorem power_derivative_class (f : DomainFunctions.Map) (hf : Holomorphic f)
    (q : Scalar) (hq : f.domain q) (n : Nat) :
    ComplexRawQuotient.ofRaw ((tauMapPower_holomorphic f hf (n+1)).derivative q hq).val
      ((tauMapPower_holomorphic f hf (n+1)).derivative q hq).property =
      ComplexRawQuotient.scaleRat ((n+1:Nat):Rat)
        ((ComplexRawQuotient.ofRaw (f.eval q hq).val (f.eval q hq).property)^n *
          ComplexRawQuotient.ofRaw (hf.derivative q hq).val (hf.derivative q hq).property) := by
  let F := ComplexRawQuotient.ofRaw (f.eval q hq).val (f.eval q hq).property
  let D := ComplexRawQuotient.ofRaw (hf.derivative q hq).val (hf.derivative q hq).property
  induction n with
  | zero =>
    rw [power_derivative_step]
    change 0*F+F^0*D=ComplexRawQuotient.scaleRat 1 (F^0*D)
    rw [ComplexRawQuotient.scaleRat_one]
    grind only
  | succ n ih =>
    rw [power_derivative_step,ih]
    change ComplexRawQuotient.scaleRat ((n+1:Nat):Rat) (F^n*D)*F+F^(n+1)*D =
      ComplexRawQuotient.scaleRat ((n+1+1:Nat):Rat) (F^(n+1)*D)
    rw [←ComplexRawQuotient.scaleRat_mul ((n+1:Nat):Rat) (F^n*D) F]
    have hid : (F^n*D)*F=F^(n+1)*D := by grind only
    change ComplexRawQuotient.scaleRat ((n+1:Nat):Rat) ((F^n*D)*F)+F^(n+1)*D =
      ComplexRawQuotient.scaleRat ((n+1+1:Nat):Rat) (F^(n+1)*D)
    rw [hid]
    have he := ComplexRawQuotient.add_scaleRat ((n+1:Nat):Rat) 1 (F^(n+1)*D)
    rw [ComplexRawQuotient.scaleRat_one] at he
    rw [he]
    simp only [Rat.natCast_add,show ((1:Nat):Rat)=1 by rfl]

/-- Exact represented power rule for arbitrary actual holomorphic map values. -/
theorem tauMapPower_derivative (f : DomainFunctions.Map) (hf : Holomorphic f)
    (q : Scalar) (hq : f.domain q) (n : Nat) :
    ((tauMapPower_holomorphic f hf (n+1)).derivative q hq).val.Equiv
      (scaleRat ((n+1:Nat):Rat)
        (mul (LocalODE.power (f.eval q hq).val n) (hf.derivative q hq).val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((tauMapPower_holomorphic f hf (n+1)).derivative q hq).property)
    (hright := scaleRat_valid (mul_valid (LocalODE.power_valid _ (f.eval q hq).property n)
      (hf.derivative q hq).property))
  rw [ComplexRawQuotient.ofRaw_scaleRat _ _
      (mul_valid (LocalODE.power_valid _ (f.eval q hq).property n) (hf.derivative q hq).property),
    ComplexRawQuotient.ofRaw_mul _ _ (LocalODE.power_valid _ (f.eval q hq).property n)
      (hf.derivative q hq).property,ScalarAlgebra.ofRaw_power,power_derivative_class]

/-- Exact derivative of a literal coordinate monomial. -/
theorem tauCoordinatePower_derivative (q : Scalar) (N : Nat) :
    ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial).val.Equiv
      (scaleRat ((N+1:Nat):Rat) (LocalODE.power q.val N)) := by
  have h := tauMapPower_derivative tauCoordinateMap tauCoordinateMap_holomorphic q trivial N
  have he : (scaleRat ((N+1:Nat):Rat)
      (mul (LocalODE.power q.val N) (tauCoordinateMap_holomorphic.derivative q trivial).val)).Equiv
      (scaleRat ((N+1:Nat):Rat) (LocalODE.power q.val N)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (mul_valid (LocalODE.power_valid _ q.property N)
        (tauCoordinateMap_holomorphic.derivative q trivial).property))
      (hright := scaleRat_valid (LocalODE.power_valid _ q.property N))
    let P := ComplexRawQuotient.ofRaw (LocalODE.power q.val N) (LocalODE.power_valid _ q.property N)
    change ComplexRawQuotient.scaleRat ((N+1:Nat):Rat) (P*1)=
      ComplexRawQuotient.scaleRat ((N+1:Nat):Rat) P
    congr 1
    grind only
  exact equiv_trans
    ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial).property
    (scaleRat_valid (mul_valid (LocalODE.power_valid _ q.property N)
      (tauCoordinateMap_holomorphic.derivative q trivial).property))
    (scaleRat_valid (LocalODE.power_valid _ q.property N)) h he

end ComputableAnalysis.ModularForms
