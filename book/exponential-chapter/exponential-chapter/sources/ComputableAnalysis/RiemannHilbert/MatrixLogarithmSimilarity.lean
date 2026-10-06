import ComputableAnalysis.RiemannHilbert.MatrixLogarithmFiniteNilpotence
import ComputableAnalysis.RiemannHilbert.MatrixLogarithmExponential

/-! Logarithm construction in a quantitatively small basis, followed by an
actual represented change of basis. Finite nilpotence removes the choice of
basis from the resulting logarithm by comparison with its finite formula. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n m : Nat}
set_option maxHeartbeats 1000000

def conjugated (c : LinearIso n m) (E : ValueMap (Fiber n) (Fiber n)) :
    ValueMap (Fiber m) (Fiber m) :=
  (c.toValueIso.backward.followedBy E).followedBy c.toValueIso.forward

theorem conjugated_linear (c : LinearIso n m) (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) :
    IsLinear (conjugated c E) :=
  IsLinear.followedBy (IsLinear.followedBy (IsLinear.inverse c.toValueIso c.linear) hE) c.linear

theorem conjugated_congr (c : LinearIso n m) (E F : ValueMap (Fiber n) (Fiber n)) (hEF : E.Equiv F) :
    (conjugated c E).Equiv (conjugated c F) :=
  ValueMap.followedBy_congr (ValueMap.followedBy_congr (ValueMap.equiv_refl _) hEF) (ValueMap.equiv_refl _)

theorem conjugated_basis_congr (c d : LinearIso n m) (E F : ValueMap (Fiber n) (Fiber n))
    (hcd : c.toValueIso.forward.Equiv d.toValueIso.forward) (hEF : E.Equiv F) :
    (conjugated c E).Equiv (conjugated d F) :=
  ValueMap.followedBy_congr
    (ValueMap.followedBy_congr (ValueIso.inverse_congr c.toValueIso d.toValueIso hcd) hEF) hcd

theorem conjugated_intertwines (c : LinearIso n m) (E : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) :
    c.toValueIso.forward.eval (E.eval x) ≈ (conjugated c E).eval (c.toValueIso.forward.eval x) :=
  c.toValueIso.forward.congr (E.congr (Setoid.symm (c.toValueIso.backward_forward x)))

theorem exponential_conjugated (c : LinearIso n m) (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (z : Scalar) :
    (conjugated c (MatrixExponential.value E hE z)).Equiv
      (MatrixExponential.value (conjugated c E) (conjugated_linear c E hE) z) := by
  intro x
  exact Setoid.trans (MatrixExponential.value_intertwines E hE (conjugated c E) (conjugated_linear c E hE)
    c.toValueIso.forward c.linear (conjugated_intertwines c E) z (c.toValueIso.backward.eval x))
    ((MatrixExponential.value (conjugated c E) (conjugated_linear c E hE) z).congr
      (c.toValueIso.forward_backward x))

theorem identityPlus_conjugated (c : LinearIso n m) (E : ValueMap (Fiber n) (Fiber n)) (z : Scalar) :
    (conjugated c (identityPlus E z)).Equiv (identityPlus (conjugated c E) z) := by
  intro x
  exact Setoid.trans (identityPlus_intertwines E (conjugated c E) c.toValueIso.forward c.linear
    (conjugated_intertwines c E) z (c.toValueIso.backward.eval x))
    ((identityPlus (conjugated c E) z).congr (c.toValueIso.forward_backward x))

def transportedValue (c : LinearIso n m) (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E) :=
  conjugated c (value E hsmall)

theorem transportedValue_linear (c : LinearIso n m) (E : ValueMap (Fiber n) (Fiber n))
    (hE : IsLinear E) (hsmall : SmallOperator E) : IsLinear (transportedValue c E hsmall) :=
  conjugated_linear c (value E hsmall) (value_linear E hE hsmall)

/-- The Taylor logarithm in a supplied small basis exponentiates to the
original represented map after changing coordinates. -/
theorem exponential_transportedValue (c : LinearIso n m) (E : ValueMap (Fiber n) (Fiber n))
    (hE : IsLinear E) (hsmall : SmallOperator E) :
    (MatrixExponential.value (transportedValue c E hsmall) (transportedValue_linear c E hE hsmall) unit).Equiv
      (identityPlus (conjugated c E) unit) :=
  ValueMap.equiv_trans (ValueMap.equiv_symm (exponential_conjugated c (value E hsmall) (value_linear E hE hsmall) unit))
    (ValueMap.equiv_trans (conjugated_congr c _ _ (exponential_value E hE hsmall)) (identityPlus_conjugated c E unit))

theorem transportedValue_finite (c : LinearIso n m) (F : ValueMap (Fiber n) (Fiber n)) (hF : IsLinear F)
    (hsmall : SmallOperator F) (s : Nat) (hNil : NilpotentAt F s)
    (E : ValueMap (Fiber m) (Fiber m))
    (hFE : ∀ x, c.toValueIso.forward.eval (F.eval x) ≈ E.eval (c.toValueIso.forward.eval x)) :
    (transportedValue c F hsmall).Equiv (finitePrefix E unit s) := by
  intro x
  exact Setoid.trans (c.toValueIso.forward.congr (value_finite_nilpotent F hF hsmall s hNil _))
    (Setoid.trans (prefix_intertwines F E c.toValueIso.forward c.linear hFE _ unit s)
      ((finitePrefix E unit s).congr (c.toValueIso.forward_backward x)))

/-- A finite nilpotent logarithm needs no smallness in the original basis.
The supplied basis change must establish smallness; the conclusion is proved
for the independent finite logarithm and independent entire exponential. -/
theorem exponential_finite_of_small_basis (c : LinearIso n m) (F : ValueMap (Fiber n) (Fiber n)) (hF : IsLinear F)
    (hsmall : SmallOperator F) (s : Nat) (hNil : NilpotentAt F s)
    (E : ValueMap (Fiber m) (Fiber m)) (hE : IsLinear E)
    (hFE : ∀ x, c.toValueIso.forward.eval (F.eval x) ≈ E.eval (c.toValueIso.forward.eval x)) :
    (MatrixExponential.value (finitePrefix E unit s) (prefix_linear E hE unit s) unit).Equiv (identityPlus E unit) := by
  have he : (conjugated c F).Equiv E := fun x =>
    Setoid.trans (hFE (c.toValueIso.backward.eval x)) (E.congr (c.toValueIso.forward_backward x))
  intro x
  exact Setoid.trans (MatrixExponential.value_congr (finitePrefix E unit s) (transportedValue c F hsmall)
    (prefix_linear E hE unit s) (transportedValue_linear c F hF hsmall)
    (ValueMap.equiv_symm (transportedValue_finite c F hF hsmall s hNil E hFE))
    unit unit (equiv_refl _ unit.property) x x (Setoid.refl _))
    (Setoid.trans (exponential_transportedValue c F hF hsmall x)
      (Fiber.add_congr (Setoid.refl x) (Fiber.scale_congr (equiv_refl _ unit.property) (he x))))

end ComputableAnalysis.RiemannHilbert.MatrixLogarithm
