import ComputableAnalysis.RiemannHilbert.OperatorPowerAlgebra

/-! An executable complex diagonal basis from supplied reciprocal values.
The inverse laws follow from finite power algebra over represented scalars. -/
namespace ComputableAnalysis.RiemannHilbert.ComplexDiagonalBasis
open ComplexRaw FunctionTheory LocalSystem LocalODE
set_option maxHeartbeats 1000000

theorem reciprocal_power (c d : Scalar) (hcd : (mul c.val d.val).Equiv one) (k : Nat) :
    (mul (power c.val k) (power d.val k)).Equiv one := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (power_valid c.val c.property k) (power_valid d.val d.property k))
    (hright := ofQComplex_valid _)
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid c.property d.property) (hright := ofQComplex_valid _) hcd
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  change C*D=1 at hq
  change ComplexRawQuotient.ofRaw (power c.val k) (power_valid c.val c.property k) *
    ComplexRawQuotient.ofRaw (power d.val k) (power_valid d.val d.property k) = 1
  rw [ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power]
  change C^k*D^k=1
  induction k with
  | zero => change (1 : ScalarAlgebra.Value)*1=1; grind only
  | succ k ih =>
    change (C^k*C)*(D^k*D)=1
    grind only

def diagonal (n : Nat) (c : Scalar) : ValueMap (Fiber n) (Fiber n) where
  eval x := ⟨fun i => mul (power c.val i.val) (x.val i),
    fun i => mul_valid (power_valid c.val c.property i.val) (x.property i)⟩
  congr {x y} h i := mul_equiv (power_valid c.val c.property i.val) (power_valid c.val c.property i.val)
    (x.property i) (y.property i) (equiv_refl _ (power_valid c.val c.property i.val)) (h i)

theorem diagonal_linear (n : Nat) (c : Scalar) : IsLinear (diagonal n c) := by
  constructor
  · intro x y i
    exact mul_add_equiv _ _ _ (power_valid c.val c.property i.val) (x.property i) (y.property i)
  · intro a x i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((diagonal n c).eval (Fiber.scale a x)).property i)
      (hright := (Fiber.scale a ((diagonal n c).eval x)).property i)
    let C := ComplexRawQuotient.ofRaw (power c.val i.val) (power_valid c.val c.property i.val)
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let X := ComplexRawQuotient.ofRaw (x.val i) (x.property i)
    change C*(A*X)=A*(C*X)
    grind only

theorem diagonal_cancel (n : Nat) (c d : Scalar) (hcd : (mul c.val d.val).Equiv one) (x : Fiber n) :
    (diagonal n c).eval ((diagonal n d).eval x) ≈ x := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((diagonal n c).eval ((diagonal n d).eval x)).property i) (hright := x.property i)
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (power_valid c.val c.property i.val) (power_valid d.val d.property i.val))
    (hright := ofQComplex_valid _) (reciprocal_power c d hcd i.val)
  let C := ComplexRawQuotient.ofRaw (power c.val i.val) (power_valid c.val c.property i.val)
  let D := ComplexRawQuotient.ofRaw (power d.val i.val) (power_valid d.val d.property i.val)
  let X := ComplexRawQuotient.ofRaw (x.val i) (x.property i)
  change C*D=1 at hq
  change C*(D*X)=X
  grind only

def basis (n : Nat) (c d : Scalar) (hcd : (mul c.val d.val).Equiv one) : LinearIso n n where
  toValueIso := {
    forward := diagonal n c
    backward := diagonal n d
    backward_forward x := diagonal_cancel n d c
      (equiv_trans (mul_valid d.property c.property) (mul_valid c.property d.property) (ofQComplex_valid _)
        (mul_comm_equiv _ _ d.property c.property) hcd) x
    forward_backward := diagonal_cancel n c d hcd }
  linear := diagonal_linear n c

theorem diagonal_congr (n : Nat) (c d : Scalar) (hcd : c.val.Equiv d.val) :
    (diagonal n c).Equiv (diagonal n d) :=
  fun x i => mul_equiv (power_valid c.val c.property i.val) (power_valid d.val d.property i.val)
    (x.property i) (x.property i) (power_congr c.val d.val c.property d.property hcd i.val) (equiv_refl _ (x.property i))

end ComputableAnalysis.RiemannHilbert.ComplexDiagonalBasis
