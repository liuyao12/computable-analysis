import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal

/-! Nonvanishing laws for actual represented products, powers, and rational scales. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- Products of justified nonzero represented values are nonzero. -/
theorem scalar_mul_nonzero (x y : Scalar) (hx : NonzeroBoxSearch.Nonzero x)
    (hy : NonzeroBoxSearch.Nonzero y) :
    NonzeroBoxSearch.Nonzero ⟨mul x.val y.val,mul_valid x.property y.property⟩ := by
  intro hz
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid x.property (RepresentedReciprocal.inverse x hx).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse x hx)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid x.property y.property) (hright := ofQComplex_valid _) hz
  apply hy
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := y.property) (hright := ofQComplex_valid _)
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let Y := ComplexRawQuotient.ofRaw y.val y.property
  let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse x hx).val
    (RepresentedReciprocal.inverse x hx).property
  change X*R=1 at hi
  change X*Y=0 at he
  change Y=0
  grind only

/-- Every natural power of a justified nonzero value is nonzero. -/
theorem scalar_power_nonzero (x : Scalar) (hx : NonzeroBoxSearch.Nonzero x) (n : Nat) :
    NonzeroBoxSearch.Nonzero ⟨LocalODE.power x.val n,LocalODE.power_valid _ x.property n⟩ := by
  induction n with
  | zero =>
    intro h
    exact RepresentedReciprocal.zero_ne_one (equiv_symm h)
  | succ n ih =>
    exact scalar_mul_nonzero ⟨LocalODE.power x.val n,LocalODE.power_valid _ x.property n⟩ x ih hx

/-- Scaling by a nonzero rational preserves nonvanishing. -/
theorem scalar_scale_nonzero (x : Scalar) (hx : NonzeroBoxSearch.Nonzero x)
    (r : Rat) (hr : r≠0) :
    NonzeroBoxSearch.Nonzero ⟨scaleRat r x.val,scaleRat_valid x.property⟩ := by
  intro hz
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := scaleRat_valid x.property) (hright := ofQComplex_valid _) hz
  have ht := congrArg (ComplexRawQuotient.scaleRat r⁻¹) he
  change ComplexRawQuotient.scaleRat r⁻¹
    (ComplexRawQuotient.scaleRat r (ComplexRawQuotient.ofRaw x.val x.property)) =
    ComplexRawQuotient.scaleRat r⁻¹ 0 at ht
  rw [ComplexRawQuotient.scaleRat_scaleRat, Rat.inv_mul_cancel r hr,
    ComplexRawQuotient.scaleRat_one] at ht
  exact hx (ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := x.property) (hright := ofQComplex_valid _) (ht.trans (ComplexRawQuotient.scaleRat_zero r⁻¹)))

end ComputableAnalysis.ModularForms
