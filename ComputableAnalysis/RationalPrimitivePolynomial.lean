import ComputableAnalysis.RationalPrimitiveFormula
import ComputableAnalysis.FinitePolynomialCalculus

/-!
# Analytic polynomial primitives

A finite list of rational coefficients yields an executable polynomial
primitive and a two-sided interval derivative certificate on every rational
interval. The proof uses finite monomial secants, with no assumed derivative
or coefficient decomposition.
-/

namespace ComputableAnalysis
namespace RationalPrimitivePolynomial

open FinitePolynomial

/-- A finite coefficient list interpreted starting at the specified degree. -/
def monomialSum : List Rat → Nat → Rat → Rat
  | [], _, _ => 0
  | c :: cs, degree, x => c * x ^ degree + monomialSum cs (degree + 1) x

/-- Literal termwise integration, using only rational arithmetic. -/
def primitiveSum : List Rat → Nat → Rat → Rat
  | [], _, _ => 0
  | c :: cs, degree, x =>
      c * (x ^ (degree + 1) / ((degree + 1 : Nat) : Rat)) +
        primitiveSum cs (degree + 1) x

theorem monomialSum_eq (cs : List Rat) (degree : Nat) (x : Rat) :
    monomialSum cs degree x = x ^ degree * Polynomial.eval cs x := by
  induction cs generalizing degree with
  | nil => simp [monomialSum, Polynomial.eval]
  | cons c cs ih =>
      simp only [monomialSum, Polynomial.eval, List.foldr_cons]
      rw [ih, Rat.pow_succ]
      grind [Polynomial.eval, Rat.pow_succ]

theorem monomialSum_zero (cs : List Rat) (x : Rat) :
    monomialSum cs 0 x = Polynomial.eval cs x := by
  rw [monomialSum_eq, Rat.pow_zero, Rat.one_mul]

/-- The returned expression is exactly the polynomial coefficient primitive
used by the formal partial-fraction compiler. -/
theorem primitiveSum_eq (cs : List Rat) (degree : Nat) (x : Rat) :
    primitiveSum cs degree x = x ^ (degree + 1) *
      Polynomial.eval ((cs.zipIdx degree).map
        (fun (c, i) => c / ((i + 1 : Nat) : Rat))) x := by
  induction cs generalizing degree with
  | nil => simp [primitiveSum, Polynomial.eval]
  | cons c cs ih =>
      simp only [primitiveSum, List.zipIdx, List.map_cons,
        Polynomial.eval, List.foldr_cons]
      rw [ih]
      rw [show degree + 1 + 1 = (degree + 1) + 1 by rfl, Rat.pow_succ]
      simp only [Rat.div_def]
      grind [Polynomial.eval, Rat.pow_succ]

theorem primitiveSum_zero (cs : List Rat) (x : Rat) :
    primitiveSum cs 0 x = Polynomial.eval
      (RationalPrimitiveFormula.polynomialPrimitive cs) x := by
  rw [primitiveSum_eq]
  simp only [RationalPrimitiveFormula.polynomialPrimitive, Polynomial.eval,
    List.foldr_cons, Nat.zero_add, Rat.pow_one, Rat.zero_add]

/-- Uniform quantitative secant bounds are constructed recursively, one
normalized monomial at a time. -/
def secantBound (C : Rat) (hC : 1 <= C) : (cs : List Rat) → (degree : Nat) →
    SecantDerivativeBound C (primitiveSum cs degree) (monomialSum cs degree)
  | [], _ => SecantDerivativeBound.constant C 0
  | c :: cs, degree =>
      (SecantDerivativeBound.scaleRat c (normalizedMonomialSecantBound C degree hC)).add
        (secantBound C hC cs (degree + 1))

/-- Every rational polynomial has a polynomial primitive, with an actual
finite-difference certificate on any rational interval. -/
def hasDerivative (cs : List Rat) (a b : Rat) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat
        (Polynomial.eval (RationalPrimitiveFormula.polynomialPrimitive cs)) a b)
      (FunctionOnInterval.exactRat (Polynomial.eval cs) a b) := by
  let C := 1 + qabs a + qabs b
  have hC : 1 <= C := by
    have ha := qabs_nonneg a
    have hb := qabs_nonneg b
    dsimp [C]
    grind
  have hleft : -C <= a := by
    have ha := neg_qabs_le_self a
    have hb := qabs_nonneg b
    dsimp [C]
    grind
  have hright : b <= C := by
    have hb := self_le_qabs b
    have ha := qabs_nonneg a
    dsimp [C]
    grind
  have H := (secantBound C hC cs 0).toHasDerivativeOnInterval a b hleft hright
  have hp : primitiveSum cs 0 = Polynomial.eval (RationalPrimitiveFormula.polynomialPrimitive cs) :=
    funext (primitiveSum_zero cs)
  have hd : monomialSum cs 0 = Polynomial.eval cs := funext (monomialSum_zero cs)
  rw [hp, hd] at H
  exact H

end RationalPrimitivePolynomial
end ComputableAnalysis
