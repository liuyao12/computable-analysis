import ComputableAnalysis.ModularForms.UpperReciprocalDerivative

/-! Exact algebra of the derivatives supplied by the inverse-power holomorphic maps. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert ComplexRaw

theorem latticePower_derivative_value (u : QuadraticOrder163)
    (hu : u≠QuadraticOrder163.zero) (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) :
    ComplexRawQuotient.ofRaw ((latticePowerMap_holomorphic u hu k).derivative z hz).val
      ((latticePowerMap_holomorphic u hu k).derivative z hz).property =
      -((k:Nat):ScalarAlgebra.Value)*(u.y:ScalarAlgebra.Value)*
        (ComplexRawQuotient.ofRaw (latticeInverse z hz u hu).val
          (latticeInverse z hz u hu).property)^(k+1) := by
  let R := ComplexRawQuotient.ofRaw (latticeInverse z hz u hu).val
    (latticeInverse z hz u hu).property
  have hd : ComplexRawQuotient.ofRaw
      ((latticeReciprocalMap_holomorphic u hu).derivative z hz).val
      ((latticeReciprocalMap_holomorphic u hu).derivative z hz).property =
      -(R*R)*(u.y:ScalarAlgebra.Value) := by
    change -(R*R)*ComplexRawQuotient.ofQComplex ⟨(u.y:Rat),0⟩ = _
    rw [integer_constant]
  induction k with
  | zero =>
    change (0:ScalarAlgebra.Value)= -(0:ScalarAlgebra.Value)*(u.y:ScalarAlgebra.Value)*R^(0+1)
    grind only
  | succ k ih =>
    change ComplexRawQuotient.ofRaw
      ((latticePowerMap_holomorphic u hu k).derivative z hz).val
      ((latticePowerMap_holomorphic u hu k).derivative z hz).property*R+
      ComplexRawQuotient.ofRaw (LocalODE.power (latticeInverse z hz u hu).val k)
        (LocalODE.power_valid _ (latticeInverse z hz u hu).property k)*
      ComplexRawQuotient.ofRaw ((latticeReciprocalMap_holomorphic u hu).derivative z hz).val
        ((latticeReciprocalMap_holomorphic u hu).derivative z hz).property = _
    rw [ih,hd,ScalarAlgebra.ofRaw_power _ (latticeInverse z hz u hu).property k]
    change -((k:Nat):ScalarAlgebra.Value)*(u.y:ScalarAlgebra.Value)*R^(k+1)*R+
      R^k*(-(R*R)*(u.y:ScalarAlgebra.Value)) =
      -((k+1:Nat):ScalarAlgebra.Value)*(u.y:ScalarAlgebra.Value)*R^(k+1+1)
    grind only

theorem latticePower_derivative (u : QuadraticOrder163)
    (hu : u≠QuadraticOrder163.zero) (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) :
    ((latticePowerMap_holomorphic u hu k).derivative z hz).val.Equiv
      (mul (ofQComplex ⟨((- (k:Int)*u.y):Rat),0⟩)
        (LocalODE.power (latticeInverse z hz u hu).val (k+1))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((latticePowerMap_holomorphic u hu k).derivative z hz).property)
    (hright := mul_valid (ofQComplex_valid _)
      (LocalODE.power_valid _ (latticeInverse z hz u hu).property (k+1)))
  rw [latticePower_derivative_value,ComplexRawQuotient.ofRaw_mul _ _ (ofQComplex_valid _)
    (LocalODE.power_valid _ (latticeInverse z hz u hu).property (k+1)),
    ScalarAlgebra.ofRaw_power _ (latticeInverse z hz u hu).property (k+1)]
  change _ = ComplexRawQuotient.ofQComplex ⟨((- (k:Int)*u.y):Rat),0⟩*_
  have hi := integer_constant (- (k:Int)*u.y)
  simp only [Rat.intCast_mul,Rat.intCast_neg] at hi
  have hk : ((k:Int):ScalarAlgebra.Value)=(k:ScalarAlgebra.Value) := by
    change ComplexRawQuotient.scaleRat ((k:Int):Rat) 1 = _
    rw [Rat.intCast_natCast,ScalarAlgebra.scale_natural]
    exact ComplexRawQuotient.mul_one _
  rw [hi]
  grind only

end ComputableAnalysis.ModularForms
