import ComputableAnalysis.RiemannHilbert.ExponentialParameterScaling
import ComputableAnalysis.RiemannHilbert.ExponentialScalarOperators
import ComputableAnalysis.RiemannHilbert.DomainAffineFunction

/-! The actual scalar-operator exponential at every represented parameter.
The operator/parameter scaling theorem supplies the analytic comparison;
finite represented algebra identifies the two scalar products. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE DomainFunctions
set_option maxHeartbeats 1000000
set_option autoImplicit false
variable {n : Nat}

theorem scaled_scalar_operator (a z : Scalar) :
    (OperatorPower.scaled (Fiber.scaleMap (n := n) a) z).Equiv (Fiber.scaleMap (parameterProduct a z)) := by
  intro x
  exact Setoid.trans (Fiber.scale_scale z a x)
    (Fiber.scale_congr (mul_comm_equiv z.val a.val z.property a.property) (Setoid.refl x))

theorem value_scalar_parameter (a z : Scalar) :
    (value (Fiber.scaleMap (n := n) a) (Fiber.scaleMap_linear a) z).Equiv
      (Fiber.scaleMap (scalarExponential (parameterProduct a z))) := by
  let A : ValueMap (Fiber n) (Fiber n) := Fiber.scaleMap a
  let hA : IsLinear A := Fiber.scaleMap_linear a
  let B : ValueMap (Fiber n) (Fiber n) := OperatorPower.scaled A z
  let hB : IsLinear B := OperatorPower.scaled_linear A hA z
  have hscale : (value B hB MatrixLogarithm.unit).Equiv (value A hA z) :=
    ValueMap.equiv_trans (value_scaled_operator A hA z MatrixLogarithm.unit)
      (fun x => value_congr A A hA hA (ValueMap.equiv_refl A) (parameterProduct z MatrixLogarithm.unit) z
        (mul_one_equiv z.val z.property) x x (Setoid.refl x))
  have hoperator : (value B hB MatrixLogarithm.unit).Equiv
      (value (Fiber.scaleMap (parameterProduct a z)) (Fiber.scaleMap_linear _) MatrixLogarithm.unit) :=
    fun x => value_congr B (Fiber.scaleMap (parameterProduct a z)) hB (Fiber.scaleMap_linear _)
      (scaled_scalar_operator a z) MatrixLogarithm.unit MatrixLogarithm.unit
      (equiv_refl _ MatrixLogarithm.unit.property) x x (Setoid.refl x)
  exact ValueMap.equiv_trans (ValueMap.equiv_symm hscale)
    (ValueMap.equiv_trans hoperator (value_scalar_operator (parameterProduct a z)))

theorem value_unit_operator (z : Scalar) :
    (value (Fiber.scaleMap (n := n) oneScalar) (Fiber.scaleMap_linear oneScalar) z).Equiv
      (Fiber.scaleMap (scalarExponential z)) :=
  ValueMap.equiv_trans (value_scalar_parameter oneScalar z)
    (fun x => Fiber.scale_congr (scalarExponential_congr _ z (one_mul_equiv z.val z.property)) (Setoid.refl x))

end ComputableAnalysis.RiemannHilbert.MatrixExponential
