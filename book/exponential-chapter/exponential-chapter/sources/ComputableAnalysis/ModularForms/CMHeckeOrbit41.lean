import ComputableAnalysis.ModularForms.CMCyclicQuotient41
import ComputableAnalysis.ModularForms.LatticeJTransformation
import ComputableAnalysis.ModularForms.CMJDomain163

/-! A concrete degree-41 Hecke representative lies in the actual CM modular orbit. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The determinant-one transformation T S. -/
def cmHeckeOrbitMatrix163 : SL2Z := ⟨1,-1,1,0,by decide +kernel⟩

/-- The fortieth affine representative of the degree-41 Hecke correspondence. -/
def cmHeckePointForty163 : Scalar :=
  ⟨scaleRat (1/41) (translate 40 cmScalar163.val),scaleRat_valid (translate_valid _ cmScalar163.property)⟩

private theorem quadratic_quotient (Z : ScalarAlgebra.Value) (hZ : Z*Z=Z-41) :
    Z*ComplexRawQuotient.scaleRat (1/41) (Z+40)=Z-1 := by
  have hp : Z*(Z+40)=ComplexRawQuotient.scaleRat 41 (Z-1) := by
    rw [←show ((41:Nat):Rat)=(41:Rat) by decide +kernel,ScalarAlgebra.scale_natural 41]
    grind only
  rw [ComplexRawQuotient.mul_scaleRat,hp,ComplexRawQuotient.scaleRat_scaleRat,
    show (1/41:Rat)*41=1 by decide +kernel,ComplexRawQuotient.scaleRat_one]

/-- The actual affine degree-41 representative equals the actual T S image of the CM point. -/
theorem cmHeckePointForty163_action_agreement :
    (fractionalLinear cmHeckeOrbitMatrix163 cmScalar163 cmPoint163_upper).val.Equiv
      cmHeckePointForty163.val := by
  apply fractionalLinear_unique cmHeckeOrbitMatrix163 cmScalar163 cmPoint163_upper cmHeckePointForty163
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (integerAffine_valid _ _ cmScalar163.property) cmHeckePointForty163.property)
    (hright := integerAffine_valid _ _ cmScalar163.property)
  change ComplexRawQuotient.ofRaw (integerAffine 1 0 cmScalar163.val) (integerAffine_valid _ _ cmScalar163.property)*
    ComplexRawQuotient.ofRaw cmHeckePointForty163.val cmHeckePointForty163.property=
    ComplexRawQuotient.ofRaw (integerAffine 1 (-1) cmScalar163.val) (integerAffine_valid _ _ cmScalar163.property)
  rw [integerAffine_class,integerAffine_class]
  have hc : ComplexRawQuotient.ofQComplex ⟨40,0⟩=(40:ScalarAlgebra.Value) := by
    have h := integer_constant 40
    rw [show ((40:Int):Rat)=(40:Rat) by decide +kernel] at h
    grind
  have hp := quadratic_quotient cmPoint163Value cmPoint163Value_quadratic
  change (((1:Int):ScalarAlgebra.Value)*cmPoint163Value+((0:Int):ScalarAlgebra.Value))*
    ComplexRawQuotient.scaleRat (1/41) (cmPoint163Value+ComplexRawQuotient.ofQComplex ⟨40,0⟩)=
    ((1:Int):ScalarAlgebra.Value)*cmPoint163Value+((-1:Int):ScalarAlgebra.Value)
  rw [hc]
  grind

/-- The concrete affine degree-41 representative lies in the upper half-plane. -/
theorem cmHeckePointForty163_upper : InUpperHalfPlane cmHeckePointForty163.val :=
  (upperHalfPlane_congr (fractionalLinear cmHeckeOrbitMatrix163 cmScalar163 cmPoint163_upper).property
    cmHeckePointForty163.property cmHeckePointForty163_action_agreement).mp
    (fractionalLinear_mem cmHeckeOrbitMatrix163 cmScalar163 cmPoint163_upper)

/-- The actual lattice j evaluator is defined at the affine degree-41 representative. -/
theorem cmHeckePointForty163_j_domain : latticeJMap.domain cmHeckePointForty163 :=
  (latticeJMap.domain_congr
    (fractionalLinear cmHeckeOrbitMatrix163 cmScalar163 cmPoint163_upper) cmHeckePointForty163
    cmHeckePointForty163_action_agreement).mp
    (latticeJMap_action_mem cmHeckeOrbitMatrix163 cmScalar163 latticeJMap_cm_domain)

/-- The actual lattice j value at the concrete degree-41 representative equals the CM j value. -/
theorem cmHeckePointForty163_j_agreement :
    (latticeJMap.eval cmHeckePointForty163 cmHeckePointForty163_j_domain).val.Equiv cmJValue163.val := by
  have he := latticeJMap.eval_congr
    (fractionalLinear cmHeckeOrbitMatrix163 cmScalar163 cmPoint163_upper) cmHeckePointForty163
    (latticeJMap_action_mem cmHeckeOrbitMatrix163 cmScalar163 latticeJMap_cm_domain)
    cmHeckePointForty163_j_domain cmHeckePointForty163_action_agreement
  exact equiv_trans (latticeJMap.eval cmHeckePointForty163 cmHeckePointForty163_j_domain).property
    (latticeJMap.eval (fractionalLinear cmHeckeOrbitMatrix163 cmScalar163 cmPoint163_upper)
      (latticeJMap_action_mem cmHeckeOrbitMatrix163 cmScalar163 latticeJMap_cm_domain)).property
    cmJValue163.property (equiv_symm he)
    (latticeJMap_invariant cmHeckeOrbitMatrix163 cmScalar163 latticeJMap_cm_domain)

end ComputableAnalysis.ModularForms
