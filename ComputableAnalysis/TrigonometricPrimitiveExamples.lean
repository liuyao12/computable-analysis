import ComputableAnalysis.TrigonometricRepresentedFactorization
import ComputableAnalysis.ComputablePrimitiveExamples
import ComputableAnalysis.PrimitiveChangeOfVariables

namespace ComputableAnalysis
namespace TrigonometricPrimitiveExamples
open ComputableCoefficient ComputableFactoredAlgebra ComputableTrigonometricRationalization

/-- A genuinely irrational coefficient in the original trigonometric input. -/
def coefficient : ComputableCoefficient.Expr := .parameter ComputablePrimitiveExamples.rootTwo

def integrand : ComputableTrigonometricRationalization.Expr :=
  .mul (.const coefficient) (.inv (.add (.const (.rational 1)) .cosine))

def factors : List ComputableFactoredAlgebra.Factor := [.quadratic (.rational 0) (.rational 1) 1]

def checked? := certifyFactors 4 factors

theorem factors_checked : checked?.isSome = true := by decide +kernel

def factorization : ComputableTrigonometricRationalization.Factorization integrand where
  factors := factors
  leading := .rational 2
  checked := checked?.get factors_checked
  leadingApart := ⟨0, by intros; exact (by decide +kernel : (2 : Rat) ≠ 0)⟩
  identity := ⟨0, by
    intro n hn s hs t
    rw [ComputableTrigonometricRationalization.Expr.shadow_pullback]
    simp only [integrand, ComputableTrigonometricRationalization.Expr.shadow,
      TrigonometricRationalization.Expr.pullback, TrigonometricRationalization.Expr.substitute,
      TrigonometricRationalization.cosineExpr, TrigonometricRationalization.circleDenominator,
      TrigonometricRationalization.jacobianExpr, RatExpr.div, RatExpr.sub,
      RationalExpressionNormalization.compile, RationalExpressionNormalization.mulFun,
      RationalExpressionNormalization.addFun, RationalExpressionNormalization.negFun,
      RationalExpressionNormalization.invFun, RatFun.denominator,
      RationalExpressionNormalization.mul, RationalExpressionNormalization.add,
      RationalExpressionNormalization.scale, List.map, List.foldr, Polynomial.eval,
      factors, denominator, Factor.polynomial, Factor.multiplicity,
      ComputableFactoredAlgebra.power, ComputableFactoredAlgebra.mul,
      ComputableFactoredAlgebra.add, ComputableFactoredAlgebra.scale,
      sampled, ComputableCoefficient.Expr.sample]
    grind⟩

def coordinate : ComputableCoefficient.Expr := .rational (1/16)

def domain : SampleCertificate (fun s =>
    (integrand.shadow s).eval (TrigonometricRationalization.sineCoordinate (coordinate.sample s))
      (TrigonometricRationalization.cosineCoordinate (coordinate.sample s)) ≠ none) :=
  ⟨0, by
    intro n hn s hs
    have hj := Rat.ne_of_gt (TrigonometricRationalization.jacobian_pos (coordinate.sample s))
    simp only [integrand, ComputableTrigonometricRationalization.Expr.shadow,
      TrigonometricRationalization.Expr.eval, ComputableCoefficient.Expr.sample]
    rw [TrigonometricRationalization.one_add_cosine]
    simp [hj]⟩

def derivative? := (factorization.angleDerivative coordinate).realize 4

def value? := (integrand.value (ComputableTrigonometricRationalization.sineCoordinate coordinate)
  (ComputableTrigonometricRationalization.cosineCoordinate coordinate)).realize 4

theorem derivative_computes : derivative?.isSome = true := by decide +kernel

theorem value_computes : value?.isSome = true := by decide +kernel

/-- The coefficient is the existing square-root computation, not a rational
stand-in; both derivative and original expression use that same parameter. -/
theorem irrational_primitive_correct :
    (derivative?.get derivative_computes).real.preferred.Equiv
      (value?.get value_computes).real.preferred :=
  factorization.primitive_correct coordinate domain 4 4 _ _
    (Option.some_get derivative_computes).symm (Option.some_get value_computes).symm

def expected : Value := Value.mul (.parameter ComputablePrimitiveExamples.rootTwo) (.rational (257/512))

/-- At the chosen point the answer is exactly the represented square root
multiplied by the rational inverse Jacobian. -/
theorem derivative_is_expected :
    (derivative?.get derivative_computes).real.preferred.Equiv expected.real.preferred := by
  have hv : (value?.get value_computes).real.preferred.Equiv expected.real.preferred := by
    apply Value.equiv_of_samples _ _ 0
    intro n hn s hs
    rw [ComputableCoefficient.Expr.realize_sample _ 4 _ (Option.some_get value_computes).symm]
    simp only [integrand, ComputableTrigonometricRationalization.Expr.value,
      coefficient, coordinate, ComputableTrigonometricRationalization.cosineCoordinate,
      ComputableTrigonometricRationalization.circleDenominator,
      ComputableCoefficient.Expr.sample_div, ComputableCoefficient.Expr.sample_sub,
      ComputableCoefficient.Expr.sample, expected, Value.mul, Value.parameter, Value.rational]
    change s ComputablePrimitiveExamples.rootTwo * (1 + (1-(1/16:Rat)*(1/16))/(1+(1/16:Rat)*(1/16)))⁻¹ =
      s ComputablePrimitiveExamples.rootTwo * (257/512)
    congr 1
    decide +kernel
  exact RealRaw.equiv_trans
    (derivative?.get derivative_computes).real.valid
    (value?.get value_computes).real.valid expected.real.valid irrational_primitive_correct hv

/-- Forgetting the reciprocal Jacobian would leave an erroneous factor. -/
theorem inverse_jacobian_at_one : inverseJacobian 1 = 1 := by decide +kernel

theorem inverse_jacobian_at_zero : inverseJacobian 0 = 1/2 := by decide +kernel

/-- A zero numerator does not erase a pole in the original expression. -/
theorem zero_times_cosecant_stays_undefined (s : Real → Rat) :
    ((ComputableTrigonometricRationalization.Expr.mul (.const (.rational 0)) (.inv .sine)).pullback.shadow s).eval? 0 = none := by
  rw [ComputableTrigonometricRationalization.Expr.pullback_correct]
  simp only [ComputableTrigonometricRationalization.Expr.shadow, ComputableCoefficient.Expr.sample]
  decide +kernel

/-- The antipodal chart does not hide an actual pole of the integrand. -/
theorem antipodal_pole_retained (s : Real → Rat) :
    (integrand.antipodal.pullback.shadow s).eval? 0 = none := by
  rw [ComputableTrigonometricRationalization.Expr.antipodal_pullback_correct]
  have hc : TrigonometricRationalization.cosineCoordinate 0 = 1 := by decide +kernel
  simp only [integrand, ComputableTrigonometricRationalization.Expr.shadow,
    TrigonometricRationalization.Expr.eval, ComputableCoefficient.Expr.sample, hc,
    show (1 : Rat) + -1 = 0 by decide +kernel, if_true, Option.map_none]

/-- A stationary finite inner sample is allowed by the transport rule. -/
theorem zero_inner_increment (f g df dg h eps B : Rat)
    (hh : h ≠ 0) (hB : 0 < B) (hdf : qabs df ≤ B) (heps : 0 ≤ eps)
    (hdg : qabs dg ≤ eps / (2*B)) :
    qabs ((f-f)/h-df*dg) ≤ eps := by
  apply PrimitiveChangeOfVariables.rationalCompositionSecant_error_le f f df g g dg h eps B hh hB hdf
  · have hh0 := qabs_nonneg h
    have hp : 0 ≤ eps * qabs h / 2 := Rat.mul_nonneg (Rat.mul_nonneg heps hh0) (by decide +kernel)
    simpa only [show (f-f)-(df*(g-g)) = 0 by grind, show qabs (0:Rat) = 0 by decide +kernel] using hp
  · simpa only [show (g-g)/h-dg = -dg by simp [Rat.div_def]; grind, qabs_neg] using hdg

end TrigonometricPrimitiveExamples
end ComputableAnalysis
