import ComputableAnalysis.DifferentialSynchronizedSum
import ComputableAnalysis.RationalPrimitivePolynomial
import ComputableAnalysis.RationalPrimitiveLogarithm
import ComputableAnalysis.RationalPrimitiveFormula
import ComputableAnalysis.TrigonometricRationalization

/-! Regression examples for the finite integration layer. These verify domain
preservation, repeated poles, and an actual partial-fraction identity, rather
than merely checking that the new declarations exist. -/

namespace ComputableAnalysis
namespace RationalPrimitiveExamples

open RationalPrimitiveFormula

def unitRadius : QPos := ⟨1, by decide⟩

/-- The repeated quadratic algorithm produces the familiar two-term formula. -/
theorem repeatedQuadratic_formula :
    quadraticPrimitive 0 unitRadius 1 =
      .add (.scale (1 / 2) (.quadraticRatio 0 unitRadius 0))
        (.scale (1 / 2) (.atanQuadratic 0 unitRadius)) := by
  simp only [quadraticPrimitive, unitRadius]
  congr 2 <;> congr 1 <;> grind

/-- An independently displayed derivative of that formula. -/
theorem repeatedQuadratic_derivative (x : Rat) :
    (1 / 2 : Rat) * ((1 - x * x) / (1 + x * x) ^ 2) +
      (1 / 2 : Rat) * (1 / (1 + x * x)) = 1 / (1 + x * x) ^ 2 := by
  have hi := Rat.mul_inv_cancel (1 + x * x)
    (Rat.ne_of_gt (TrigonometricRationalization.denominator_pos x))
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul,
    Rat.div_def, Rat.inv_mul_rev]
  grind

def twoPoles : RatFun := ⟨[1], [0, -1, 1]⟩

def twoPolesNormal : NormalForm :=
  ⟨[], [.linear (-1) 0 0, .linear 1 1 0]⟩

private theorem twoPoles_denominator (x : Rat) :
    twoPoles.denominator x = x * (x - 1) := by
  simp only [twoPoles, RatFun.denominator, Polynomial.eval, List.foldr]
  grind

def twoPolesDecomposition : Decomposition twoPoles where
  normalForm := twoPolesNormal
  regular := by
    intro x hx t ht
    have hd : x * (x - 1) ≠ 0 := by
      change (twoPoles.denominator x != 0) = true at hx
      rw [twoPoles_denominator] at hx
      simpa using hx
    simp only [twoPolesNormal, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp only [Term.RegularAt] <;> grind
  identity := by
    intro x hx
    have hd : x * (x - 1) ≠ 0 := by
      change (twoPoles.denominator x != 0) = true at hx
      rw [twoPoles_denominator] at hx
      simpa using hx
    have hx0 : x ≠ 0 := by grind
    have hx1 : x - 1 ≠ 0 := by grind
    have hi := Rat.mul_inv_cancel x hx0
    have hj := Rat.mul_inv_cancel (x - 1) hx1
    simp only [NormalForm.eval, twoPolesNormal, sumTerms, Term.eval, RatFun.evalOnDomain]
    rw [twoPoles_denominator]
    simp only [Polynomial.eval, List.foldr, RatFun.numerator, twoPoles,
      Nat.zero_add, Rat.pow_one, Rat.div_def, Rat.inv_mul_rev]
    grind

theorem twoPoles_primitive (x : Rat) (hx : twoPoles.DefinedAt x) :
    twoPolesNormal.primitive.formalDerivative x = twoPoles.evalOnDomain x hx :=
  twoPolesDecomposition.primitive_correct x hx

/-- Guard regression: double inverse must not fill the original hole. -/
theorem doubleInverse_undefined :
    (RationalExpressionNormalization.compile (.inv (.inv .var))).eval? 0 = none := by
  rw [RationalExpressionNormalization.compile_correct]
  simp [RatExpr.eval]

theorem zeroTimesPole_undefined :
    (RationalExpressionNormalization.compile (.mul (.const 0) (.inv .var))).eval? 0 = none := by
  rw [RationalExpressionNormalization.compile_correct]
  simp [RatExpr.eval]

open TrigonometricRationalization

/-- Reciprocal sine has a genuine pole at the chart origin. -/
theorem cosecant_pullback_pole : (Expr.inv .sine).pullback.eval? 0 = none := by
  rw [Expr.pullback_correct]
  simp [Expr.eval, sineCoordinate, Rat.div_def]

/-- The identically zero denominator stays undefined on the entire chart. -/
theorem zeroDenominator_pullback (t : Rat) : (Expr.inv (.const 0)).pullback.eval? t = none := by
  rw [Expr.pullback_correct]
  simp [Expr.eval]

/-- The half-angle pullback of the reciprocal of one plus cosine is one.
Its omitted antipode is a chart issue and has not been assigned a value. -/
theorem onePlusCosine_pullback (t : Rat) :
    (Expr.inv (.add (.const 1) .cosine)).pullback.eval? t = some 1 := by
  rw [Expr.pullback_correct]
  have hj := Rat.ne_of_gt (jacobian_pos t)
  have hi := Rat.inv_mul_cancel (jacobian t) hj
  simp only [Expr.eval, one_add_cosine, if_neg hj, Option.map_some,
    Rat.div_def, Rat.one_mul]
  rw [hi]


/-- The logarithm chart is analytic on the negative side of its pole too. -/
def negativePole_hasDerivative :
    HasDerivativeOnInterval (RationalPrimitiveLogarithm.simplePolePrimitive 0 (-1) (by decide))
      (FunctionOnInterval.exactRat (fun x => 1 / (x - 0))
        (-1 - RationalPrimitiveLogarithm.poleRadius 0 (-1))
        (-1 + RationalPrimitiveLogarithm.poleRadius 0 (-1))) :=
  RationalPrimitiveLogarithm.simplePole_hasDerivative 0 (-1) (by decide)

/-- The compiler's coefficient primitive now has an analytic certificate. -/
def polynomial_hasDerivative :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (Polynomial.eval (polynomialPrimitive [1, -2, 3])) (-2) 3)
      (FunctionOnInterval.exactRat (Polynomial.eval [1, -2, 3]) (-2) 3) :=
  RationalPrimitivePolynomial.hasDerivative [1, -2, 3] (-2) 3


/-- A polynomial and a logarithm use different runtime schedules. The
unconditional sum rule synchronizes them, with no schedule hypotheses. -/
def polynomialPlusLog_hasDerivative :=
  (RationalPrimitivePolynomial.hasDerivative [1] (-(1 / 2)) (1 / 2)).add
    RationalPrimitiveLogarithm.hasDerivative rfl rfl

end RationalPrimitiveExamples
end ComputableAnalysis
