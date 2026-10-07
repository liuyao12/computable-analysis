import ComputableAnalysis.ModularForms.NomeEisensteinLeadingTerms

/-! Quantitative polynomial difference laws for supplied represented values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

/-- Supplied coordinate bounds transport through the difference of squares. -/
theorem represented_square_difference_bound (x y : Scalar) (M E : Rat)
    (hM : 0≤M) (hE : 0≤E) (hx : Small x.val M) (hy : Small y.val M)
    (hd : Small (sub x.val y.val) E) :
    Small (sub (LocalODE.power x.val 2) (LocalODE.power y.val 2)) (4*E*M) := by
  have h := Small.mul (sub_valid x.property y.property) (add_valid x.property y.property)
    hE (Rat.add_nonneg hM hM) hd (LocalODE.small_add hx hy)
  have he : (mul (sub x.val y.val) (add x.val y.val)).Equiv
      (sub (LocalODE.power x.val 2) (LocalODE.power y.val 2)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid (sub_valid x.property y.property) (add_valid x.property y.property))
      (hright := sub_valid (LocalODE.power_valid _ x.property 2) (LocalODE.power_valid _ y.property 2))
    let X := ComplexRawQuotient.ofRaw x.val x.property
    let Y := ComplexRawQuotient.ofRaw y.val y.property
    change (X-Y)*(X+Y)=ComplexRawQuotient.ofRaw (LocalODE.power x.val 2) (LocalODE.power_valid _ x.property 2)-
      ComplexRawQuotient.ofRaw (LocalODE.power y.val 2) (LocalODE.power_valid _ y.property 2)
    rw [ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power]
    change (X-Y)*(X+Y)=X^2-Y^2
    grind only
  have hb := Small.congr
    (mul_valid (sub_valid x.property y.property) (add_valid x.property y.property))
    (sub_valid (LocalODE.power_valid _ x.property 2) (LocalODE.power_valid _ y.property 2)) he h
  rw [show 2*E*(M+M)=4*E*M by grind only] at hb
  exact hb

/-- Supplied coordinate bounds transport through the difference of cubes. -/
theorem represented_cube_difference_bound (x y : Scalar) (M E : Rat)
    (hM : 0≤M) (hE : 0≤E) (hx : Small x.val M) (hy : Small y.val M)
    (hd : Small (sub x.val y.val) E) :
    Small (sub (LocalODE.power x.val 3) (LocalODE.power y.val 3)) (12*E*M*M) := by
  let f := scalarSum (scalarSum (scalarProduct x x) (scalarProduct x y)) (scalarProduct y y)
  have hxx := Small.mul x.property x.property hM hM hx hx
  have hxy := Small.mul x.property y.property hM hM hx hy
  have hyy := Small.mul y.property y.property hM hM hy hy
  have hf : Small f.val ((2*M*M+2*M*M)+2*M*M) := LocalODE.small_add (LocalODE.small_add hxx hxy) hyy
  have hM2 : 0≤2*M*M := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hM) hM
  have h := Small.mul (sub_valid x.property y.property) f.property hE
    (Rat.add_nonneg (Rat.add_nonneg hM2 hM2) hM2) hd hf
  have he : (mul (sub x.val y.val) f.val).Equiv
      (sub (LocalODE.power x.val 3) (LocalODE.power y.val 3)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid (sub_valid x.property y.property) f.property)
      (hright := sub_valid (LocalODE.power_valid _ x.property 3) (LocalODE.power_valid _ y.property 3))
    let X := ComplexRawQuotient.ofRaw x.val x.property
    let Y := ComplexRawQuotient.ofRaw y.val y.property
    change (X-Y)*((X*X+X*Y)+Y*Y)=ComplexRawQuotient.ofRaw (LocalODE.power x.val 3) (LocalODE.power_valid _ x.property 3)-
      ComplexRawQuotient.ofRaw (LocalODE.power y.val 3) (LocalODE.power_valid _ y.property 3)
    rw [ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power]
    change (X-Y)*((X*X+X*Y)+Y*Y)=X^3-Y^3
    grind only
  have hb := Small.congr (mul_valid (sub_valid x.property y.property) f.property)
    (sub_valid (LocalODE.power_valid _ x.property 3) (LocalODE.power_valid _ y.property 3)) he h
  rw [show 2*E*((2*M*M+2*M*M)+2*M*M)=12*E*M*M by grind only] at hb
  exact hb

end ComputableAnalysis.ModularForms
