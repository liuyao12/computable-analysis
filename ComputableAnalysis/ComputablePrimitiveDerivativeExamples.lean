import ComputableAnalysis.ComputableArctangentSeries
import ComputableAnalysis.ComputableQuadraticPrimitives
import ComputableAnalysis.ComputablePrimitiveExamples

/-! Actual derivative certificates with irrational coefficients and poles. -/
namespace ComputableAnalysis
namespace ComputablePrimitiveDerivativeExamples
open ComputableCoefficient ComputableLogarithmChart

def pole : Value := .parameter ComputablePrimitiveExamples.rootTwo

def inverse? := (Value.sub (.rational 0) pole).inv? 4

theorem inverse_computes : inverse?.isSome = true := by decide +kernel

def inverse : Value := inverse?.get inverse_computes

def reciprocal? := (Value.sub (.rational (1/16)) pole).inv? 4

theorem reciprocal_computes : reciprocal?.isSome = true := by decide +kernel

def reciprocal : Value := reciprocal?.get reciprocal_computes

theorem pole_point_in_chart : qabs ((1:Rat)/16-0) ≤ (simplePoleChart inverse).radius := by decide +kernel

def irrationalPole_hasDerivative :
    HasDerivativeOnInterval (simplePolePrimitive inverse 0) (simplePoleDerivative inverse 0) :=
  simplePole_hasDerivative inverse 0

theorem irrationalPole_derivative_is_reciprocal :
    (rawCoordinate false ((simplePoleChart inverse).derivative (1/16-0))).Equiv reciprocal.real.preferred := by
  exact simplePole_derivative_equiv pole inverse reciprocal 0 (1/16) 4 4
    (Option.some_get inverse_computes).symm (Option.some_get reciprocal_computes).symm pole_point_in_chart

private def r : Expr := .parameter ComputablePrimitiveExamples.rootTwo
private def t : Expr := .rational (1/16)

def arctanKernelExpr : Expr := r.div (.add (.rational 1) (.mul (.mul r t) (.mul r t)))

def arctanKernel? := arctanKernelExpr.realize 4

theorem arctanKernel_computes : arctanKernel?.isSome = true := by decide +kernel

def arctanKernel : Value := arctanKernel?.get arctanKernel_computes

theorem arctan_point_in_chart : qabs ((1:Rat)/16-0) ≤ (arctanChart pole).radius := by decide +kernel

def irrationalArctan_hasDerivative :
    HasDerivativeOnInterval (arctanPrimitive pole 0) (arctanDerivative pole 0) :=
  arctan_hasDerivative pole 0

theorem irrationalArctan_derivative_is_kernel :
    (rawCoordinate true ((arctanChart pole).derivative (1/16-0))).Equiv arctanKernel.real.preferred := by
  apply arctan_derivative_equiv pole arctanKernel 0 (1/16) arctan_point_in_chart
  intro s
  have he := Expr.realize_sample arctanKernelExpr 4 arctanKernel
    (Option.some_get arctanKernel_computes).symm s
  simpa only [arctanKernelExpr, Expr.sample_div, Expr.sample, pole, Value.parameter, r, t,
    Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero] using he

/-- Regression against accidentally replacing the primitive by a kernel or
an unspecified value: its candidates are the actual arctangent Taylor sums. -/
theorem irrationalArctan_series (n : Nat) :
    ((arctanChart pole).valueSample (1/16) (2*n)).im =
      atanPartial ((1/16) * pole.sample ((arctanChart pole).samples (2*n))) n :=
  arctan_valueSample pole (1/16) n

def widthInverse? := pole.inv? 4

theorem widthInverse_computes : widthInverse?.isSome = true := by decide +kernel

def widthInverse : Value := widthInverse?.get widthInverse_computes

def quadraticInverse? := (quadraticValue pole pole 0).inv? 4

theorem quadraticInverse_computes : quadraticInverse?.isSome = true := by decide +kernel

def quadraticInverse : Value := quadraticInverse?.get quadraticInverse_computes

def quadraticTarget? := (quadraticValue pole pole (1/16)).inv? 4

theorem quadraticTarget_computes : quadraticTarget?.isSome = true := by decide +kernel

def quadraticTarget : Value := quadraticTarget?.get quadraticTarget_computes

def quadraticAtanChart := quadraticChart pole pole quadraticInverse (Value.neg widthInverse) 0

def irrationalQuadratic_hasDerivative :
    HasDerivativeOnInterval (quadraticAtanChart.weightedValueOn true 0) (quadraticAtanChart.weightedDerivativeOn true 0) :=
  quadraticArctan_hasDerivative pole pole quadraticInverse widthInverse 0

theorem quadratic_point_in_chart : qabs ((1:Rat)/16-0) ≤ quadraticAtanChart.radius := by decide +kernel

theorem irrationalQuadratic_derivative_is_reciprocal :
    (rawCoordinate true (quadraticAtanChart.weightedDerivative (1/16-0))).Equiv quadraticTarget.real.preferred := by
  exact quadraticArctan_derivative_equiv pole pole quadraticInverse widthInverse quadraticTarget 0 (1/16) 4 4 4
    (Option.some_get quadraticInverse_computes).symm (Option.some_get widthInverse_computes).symm
    (Option.some_get quadraticTarget_computes).symm quadratic_point_in_chart

end ComputablePrimitiveDerivativeExamples
end ComputableAnalysis
