import ComputableAnalysis.ComputablePrimitiveDerivativeExamples
import ComputableAnalysis.ComputablePrimitiveExamples
import ComputableAnalysis.RationalFactoredPrimitives
import ComputableAnalysis.RationalPrimitiveAssembly
import ComputableAnalysis.RationalPrimitivePowers
import ComputableAnalysis.RationalPartialFractions
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


/-- Pole blocks with both nontrivial multiplicities and different centers. -/
def mixedRepeatedPoles : List RationalPartialFractions.Pole := [⟨0, 1⟩, ⟨1, 2⟩]

theorem mixedRepeatedPoles_admissible : RationalPartialFractions.Admissible mixedRepeatedPoles := by
  decide +kernel

def automaticMixedDecomposition :=
  RationalPartialFractions.decomposition mixedRepeatedPoles [1, 2] mixedRepeatedPoles_admissible

/-- Independently specified coefficients for `(1+2*x)/(x^2*(x-1)^3)`. -/
theorem automaticMixed_coefficients :
    (automaticMixedDecomposition.normalForm.terms.map fun t => match t with
      | .linear c a n => some (c, a, n)
      | .quadratic _ _ _ _ _ => none) =
    [some ((-1 : Rat), (0 : Rat), 1), some (-5, 0, 0),
      some (3, 1, 2), some (-4, 1, 1), some (5, 1, 0)] := by
  decide +kernel

/-- Negative coefficients and a negative-side denominator are both supported. -/
def negativeTriplePole_hasDerivative :=
  RationalPrimitivePowers.weighted_hasDerivative (-3) 0 (-2) (-1) unitRadius
    (by
      intro x hx
      change (-2 : Rat) <= x ∧ x <= -1 at hx
      change (1 : Rat) <= qabs (x - 0)
      have hn : x - 0 <= 0 := by grind
      rw [qabs_eq_neg_of_nonpos hn]
      grind) 1

/-- All coefficients, all elementary evaluators, and the analytic derivative
are constructed by the algorithm on the interval around the center two. -/
def automaticMixedPrimitive := RationalPrimitiveAssembly.splitPrimitive
  mixedRepeatedPoles [1, 2] mixedRepeatedPoles_admissible 2 (by decide +kernel)

def automaticMixed_hasDerivative := automaticMixedPrimitive.derivative

theorem automaticMixed_elementary : RationalPrimitiveAssembly.Elementary
    automaticMixedPrimitive.function := automaticMixedPrimitive.elementary

theorem automaticMixed_radius : RationalPrimitiveAssembly.radius 2 mixedRepeatedPoles = 1 / 2 := by
  decide +kernel

/-- A repeated quadratic, a simple linear pole, and a distinct shifted
quadratic exercise inversion of a nonconstant residual denominator. -/
def mixedQuadraticFactors : List RationalFactoredPrimitives.Factor :=
  [.quadratic 0 ⟨2, by decide⟩ 1, .linear 0 0, .quadratic 1 ⟨3, by decide⟩ 0]

theorem mixedQuadratic_admissible : RationalFactoredPrimitives.Admissible mixedQuadraticFactors := by
  decide +kernel

def mixedQuadraticDecomposition := RationalFactoredPrimitives.decomposition
  mixedQuadraticFactors [1, 2, 3] mixedQuadratic_admissible

/-- The independently specified exact coefficients are checked by the kernel. -/
theorem mixedQuadratic_coefficients :
    (mixedQuadraticDecomposition.normalForm.terms.map fun t => match t with
      | .linear c a n => (false, c, (0 : Rat), a, (0 : Rat), n)
      | .quadratic A B a b n => (true, A, B, a, b.val, n)) =
    [(true, (3/4 : Rat), (-1/2 : Rat), (0 : Rat), (2 : Rat), 1),
      (true, 1/6, 2/3, 0, 2, 0), (false, 1/16, 0, 0, 0, 0),
      (true, -11/48, -7/16, 1, 3, 0)] := by
  decide +kernel

/-- Duplicate blocks must be merged into a single multiplicity. This is a
checked algebraic condition, not a hidden division by zero. -/
theorem duplicateQuadratic_rejected :
    ¬RationalFactoredPrimitives.Admissible
      [.quadratic 0 unitRadius 0, .quadratic 0 unitRadius 1] := by
  decide +kernel

/-- The public factorization interface handles a nonunit leading coefficient. -/
def factoredQuadraticExample : RatFun := ⟨[1, 2, 3], [-12, 12, -12, 12, -3, 3]⟩

def factoredQuadraticExample_factorization :
    RationalFactoredPrimitives.Factorization factoredQuadraticExample where
  factors := [.linear 1 0, .quadratic 0 ⟨2, by decide⟩ 1]
  leading := 3
  leading_ne_zero := by decide
  admissible := by decide +kernel
  identity := by
    intro x
    change Polynomial.eval [-12, 12, -12, 12, -3, 3] x =
      3 * Polynomial.eval (RationalFactoredPrimitives.denominator
        [.linear 1 0, .quadratic 0 ⟨2, by decide⟩ 1]) x
    rw [RationalFactoredPrimitives.denominator_cons_eval,
      RationalFactoredPrimitives.denominator_cons_eval]
    simp only [RationalFactoredPrimitives.denominator,
      RationalFactoredPrimitives.Factor.value,
      RationalFactoredPrimitives.Factor.multiplicity,
      Polynomial.eval, List.foldr, quadratic, Rat.pow_succ, Rat.pow_zero]
    grind

theorem factoredQuadraticExample_primitive (x : Rat) (hx : factoredQuadraticExample.DefinedAt x) :
    factoredQuadraticExample_factorization.decomposition.normalForm.primitive.formalDerivative x =
      factoredQuadraticExample.evalOnDomain x hx :=
  factoredQuadraticExample_factorization.primitive_correct x hx

end RationalPrimitiveExamples
end ComputableAnalysis
