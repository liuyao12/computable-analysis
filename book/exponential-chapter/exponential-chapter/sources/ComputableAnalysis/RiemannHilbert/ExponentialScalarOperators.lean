import ComputableAnalysis.RiemannHilbert.ExponentialIntertwiners
import ComputableAnalysis.RiemannHilbert.MatrixLogarithmSeries
import ComputableAnalysis.RiemannHilbert.ScalarNeumannInverse
import ComputableAnalysis.RiemannHilbert.ExponentialNilpotent
import ComputableAnalysis.RiemannHilbert.ExponentialInverse

/-! Scalar operators at every finite rank have the same actual scalar
exponential. The comparison is proved by represented linear intertwiners,
not by identifying raw scalar and matrix evaluators. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}
set_option maxHeartbeats 1000000

def scalarExponential (a : Scalar) : Scalar :=
  Fiber.coordinate ((value (Fiber.scaleMap a) (Fiber.scaleMap_linear a) MatrixLogarithm.unit).eval
    ScalarNeumannInverse.unit) 0

def spread (x : Fiber n) : ValueMap (Fiber 1) (Fiber n) where
  eval y := Fiber.scale (Fiber.coordinate y 0) x
  congr h := Fiber.scale_congr (h 0) (Setoid.refl x)

theorem spread_linear (x : Fiber n) : IsLinear (spread x) := by
  constructor
  · intro y z i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((spread x).eval (Fiber.add y z)).property i)
      (hright := (Fiber.add ((spread x).eval y) ((spread x).eval z)).property i)
    let Y := ComplexRawQuotient.ofRaw (y.val 0) (y.property 0)
    let Z := ComplexRawQuotient.ofRaw (z.val 0) (z.property 0)
    let X := ComplexRawQuotient.ofRaw (x.val i) (x.property i)
    change (Y+Z)*X=Y*X+Z*X
    grind only
  · intro a y i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((spread x).eval (Fiber.scale a y)).property i)
      (hright := (Fiber.scale a ((spread x).eval y)).property i)
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let Y := ComplexRawQuotient.ofRaw (y.val 0) (y.property 0)
    let X := ComplexRawQuotient.ofRaw (x.val i) (x.property i)
    change (A*Y)*X=A*(Y*X)
    grind only

theorem spread_unit (x : Fiber n) : (spread x).eval ScalarNeumannInverse.unit ≈ x :=
  fun i => one_mul_equiv _ (x.property i)

theorem spread_intertwines (a : Scalar) (x : Fiber n) (y : Fiber 1) :
    (spread x).eval ((Fiber.scaleMap a).eval y) ≈ (Fiber.scaleMap a).eval ((spread x).eval y) :=
  (spread_linear x).2 a y

theorem rank_one_coordinate (x : Fiber 1) (i : Fin 1) : x.val i=x.val 0 := by
  have hi : i=0 := Fin.ext (by omega)
  rw [hi]

/-- Every represented complex-linear map in rank one is its scalar value
on the unit vector. This connects independent matrix and scalar programs. -/
theorem rank_one_operator (A : ValueMap (Fiber 1) (Fiber 1)) (hA : IsLinear A) :
    A.Equiv (Fiber.scaleMap (Fiber.coordinate (A.eval ScalarNeumannInverse.unit) 0)) := by
  intro x
  have hx : x ≈ Fiber.scale (Fiber.coordinate x 0) ScalarNeumannInverse.unit := by
    intro i
    rw [rank_one_coordinate x i]
    exact equiv_symm (mul_one_equiv _ (x.property 0))
  have hs : Fiber.scale (Fiber.coordinate x 0) (A.eval ScalarNeumannInverse.unit) ≈
      Fiber.scale (Fiber.coordinate (A.eval ScalarNeumannInverse.unit) 0) x := by
    intro i
    change (mul (x.val 0) ((A.eval ScalarNeumannInverse.unit).val i)).Equiv
      (mul ((A.eval ScalarNeumannInverse.unit).val 0) (x.val i))
    rw [rank_one_coordinate x i,rank_one_coordinate (A.eval ScalarNeumannInverse.unit) i]
    exact mul_comm_equiv _ _ (x.property 0) ((A.eval ScalarNeumannInverse.unit).property 0)
  exact Setoid.trans (A.congr hx) (Setoid.trans (hA.2 _ _) hs)

/-- Exponentiating a scalar operator equals coordinatewise scaling by the
rank-one exponential, for every valid represented coefficient and vector. -/
theorem value_scalar_operator (a : Scalar) :
    (value (Fiber.scaleMap (n := n) a) (Fiber.scaleMap_linear a) MatrixLogarithm.unit).Equiv
      (Fiber.scaleMap (scalarExponential a)) := by
  intro x
  exact Setoid.symm (Setoid.trans (value_intertwines (Fiber.scaleMap (n := 1) a) (Fiber.scaleMap_linear a)
    (Fiber.scaleMap (n := n) a) (Fiber.scaleMap_linear a) (spread x) (spread_linear x)
    (spread_intertwines a x) MatrixLogarithm.unit ScalarNeumannInverse.unit)
    ((value (Fiber.scaleMap (n := n) a) (Fiber.scaleMap_linear a) MatrixLogarithm.unit).congr (spread_unit x)))

theorem scalarExponential_congr (a b : Scalar) (hab : a.val.Equiv b.val) :
    (scalarExponential a).val.Equiv (scalarExponential b).val :=
  value_congr (Fiber.scaleMap a) (Fiber.scaleMap b) (Fiber.scaleMap_linear a) (Fiber.scaleMap_linear b)
    (fun x => Fiber.scale_congr hab (Setoid.refl x)) MatrixLogarithm.unit MatrixLogarithm.unit
    (equiv_refl _ MatrixLogarithm.unit.property) ScalarNeumannInverse.unit ScalarNeumannInverse.unit (Setoid.refl _) 0

def scalarInverse (a : Scalar) : Scalar :=
  Fiber.coordinate ((frame (Fiber.scaleMap a) (Fiber.scaleMap_linear a) MatrixLogarithm.unit).toValueIso.backward.eval
    ScalarNeumannInverse.unit) 0

/-- The scalar exponential has a constructed reciprocal, obtained from the
proved inverse exponential frame rather than an assumed nonzero field. -/
theorem scalarInverse_law (a : Scalar) :
    (mul (scalarExponential a).val (scalarInverse a).val).Equiv one := by
  let F := frame (Fiber.scaleMap (n := 1) a) (Fiber.scaleMap_linear a) MatrixLogarithm.unit
  have he : Fiber.scale (scalarExponential a) (F.toValueIso.backward.eval ScalarNeumannInverse.unit) ≈
      ScalarNeumannInverse.unit :=
    Setoid.trans (Setoid.symm (value_scalar_operator a (F.toValueIso.backward.eval ScalarNeumannInverse.unit)))
      (F.toValueIso.forward_backward ScalarNeumannInverse.unit)
  exact he 0

theorem scalarBranch_inverse (a c : Scalar) (hbranch : (scalarExponential a).val.Equiv c.val) :
    (mul c.val (scalarInverse a).val).Equiv one :=
  equiv_trans (mul_valid c.property (scalarInverse a).property)
    (mul_valid (scalarExponential a).property (scalarInverse a).property) (ofQComplex_valid _)
    (mul_equiv c.property (scalarExponential a).property (scalarInverse a).property (scalarInverse a).property
      (equiv_symm hbranch) (equiv_refl _ (scalarInverse a).property)) (scalarInverse_law a)

theorem scalarExponential_zero : (scalarExponential ⟨zero,ofQComplex_valid _⟩).val.Equiv one := by
  let a : Scalar := ⟨zero,ofQComplex_valid _⟩
  let A := Fiber.scaleMap (n := 1) a
  have hzero : ∀ x, A.eval x ≈ Fiber.zero 1 := fun x i => zero_mul_equiv _ (x.property i)
  have he : (value A (Fiber.scaleMap_linear a) MatrixLogarithm.unit).eval ScalarNeumannInverse.unit ≈
      ScalarNeumannInverse.unit :=
    Setoid.trans (value_nilpotent A (Fiber.scaleMap_linear a) (fun x => hzero (A.eval x)) MatrixLogarithm.unit _)
      (Setoid.trans (Fiber.add_congr (Setoid.refl _)
        (Setoid.trans (Fiber.scale_congr (equiv_refl _ MatrixLogarithm.unit.property) (hzero _)) (Fiber.scale_zero _)))
        (Fiber.add_zero _))
  exact he 0

end ComputableAnalysis.RiemannHilbert.MatrixExponential
