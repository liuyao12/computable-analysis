import ComputableAnalysis.Polynomial

/-!
# Elementary primitive formulas for supplied partial fractions

An executable finite integration algorithm for a polynomial plus real linear
and positive quadratic partial fractions, of arbitrary multiplicity. Its
correctness theorem is a *formal derivative identity*. This file neither
constructs partial fractions for an arbitrary denominator nor realizes the
formulas as interval-valued functions with analytic derivative certificates.

All coefficients here are rational. Algebraic centers and quadratic constants
are needed for general rational input, and require a further represented
algebraic-number layer. No completed real numbers are used.
-/

namespace ComputableAnalysis
namespace RationalPrimitiveFormula

def quadratic (a b x : Rat) : Rat := (x - a) * (x - a) + b

theorem quadratic_pos (a x : Rat) (b : QPos) : 0 < quadratic a b.val x := by
  have hs : 0 ≤ (x - a) * (x - a) := by
    by_cases h : 0 ≤ x - a
    · exact Rat.mul_nonneg h h
    · have hh : 0 ≤ -(x - a) := by grind
      have := Rat.mul_nonneg hh hh
      grind
  have := b.property
  unfold quadratic
  grind

/-- Elementary syntax in integration normal form. `atanQuadratic a b` denotes
the normalized arctangent with center `a` and positive squared radius `b`.
The power constructors use exponent `n+1`, so none has a zero exponent. -/
inductive Formula where
  | polynomial (coeffs : List Rat)
  | logLinear (a : Rat)
  | linearPower (a : Rat) (n : Nat)
  | logQuadratic (a : Rat) (b : QPos)
  | atanQuadratic (a : Rat) (b : QPos)
  | quadraticPower (a : Rat) (b : QPos) (n : Nat)
  | quadraticRatio (a : Rat) (b : QPos) (n : Nat)
  | add (f g : Formula)
  | scale (c : Rat) (f : Formula)

/-- Pointwise domain of the displayed elementary formula. Positive quadratic
parameters exclude real quadratic poles; linear logarithms mean log-absolute
value and therefore require only nonvanishing. Interval calculus will need
uniform apartness, a stronger property than this pointwise predicate. -/
def Formula.RegularAt (x : Rat) : Formula → Prop
  | .polynomial _ => True
  | .logLinear a => x ≠ a
  | .linearPower a _ => x ≠ a
  | .logQuadratic _ _ => True
  | .atanQuadratic _ _ => True
  | .quadraticPower _ _ _ => True
  | .quadraticRatio _ _ _ => True
  | .add f g => f.RegularAt x ∧ g.RegularAt x
  | .scale _ f => f.RegularAt x

/-- Evaluate the usual symbolic differentiation rules in rational arithmetic.
This is deliberately not named `HasDerivativeOnInterval`. -/
def Formula.formalDerivative (x : Rat) : Formula → Rat
  | .polynomial p => Polynomial.eval (Polynomial.derivative p) x
  | .logLinear a => 1 / (x - a)
  | .linearPower a n => -((n + 1 : Nat) : Rat) / (x - a) ^ (n + 2)
  | .logQuadratic a b => 2 * (x - a) / quadratic a b.val x
  | .atanQuadratic a b => 1 / quadratic a b.val x
  | .quadraticPower a b n =>
      -(2 * ((n + 1 : Nat) : Rat) * (x - a)) / quadratic a b.val x ^ (n + 2)
  | .quadraticRatio a b n =>
      (b.val - (2 * ((n + 1 : Nat) : Rat) - 1) * (x - a) * (x - a)) /
        quadratic a b.val x ^ (n + 2)
  | .add f g => f.formalDerivative x + g.formalDerivative x
  | .scale c f => c * f.formalDerivative x

/-- Primitive of the reciprocal of a positive quadratic to power `n+1`.
Repeated powers reduce to one arctangent and finitely many rational terms. -/
def quadraticPrimitive (a : Rat) (b : QPos) : Nat → Formula
  | 0 => .atanQuadratic a b
  | n + 1 =>
      .add (.scale (1 / (2 * ((n + 1 : Nat) : Rat) * b.val))
          (.quadraticRatio a b n))
        (.scale ((2 * ((n + 1 : Nat) : Rat) - 1) /
            (2 * ((n + 1 : Nat) : Rat) * b.val)) (quadraticPrimitive a b n))

theorem quadraticPrimitive_regular (a x : Rat) (b : QPos) (n : Nat) :
    (quadraticPrimitive a b n).RegularAt x := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨True.intro, ih⟩

private theorem quadratic_reduction (u b m : Rat) (n : Nat)
    (hb : b ≠ 0) (hm : m ≠ 0) (hq : u * u + b ≠ 0) :
    1 / (2 * m * b) * ((b - (2 * m - 1) * u * u) / (u * u + b) ^ (n + 2)) +
      ((2 * m - 1) / (2 * m * b)) * (1 / (u * u + b) ^ (n + 1)) =
        1 / (u * u + b) ^ (n + 2) := by
  have hi := Rat.mul_inv_cancel b hb
  have hj := Rat.mul_inv_cancel m hm
  have hk := Rat.mul_inv_cancel (u * u + b) hq
  simp only [Rat.pow_succ, Rat.div_def, Rat.inv_mul_rev, Rat.one_mul]
  grind

theorem quadraticPrimitive_correct (a x : Rat) (b : QPos) (n : Nat) :
    (quadraticPrimitive a b n).formalDerivative x = 1 / quadratic a b.val x ^ (n + 1) := by
  induction n with
  | zero => simp [quadraticPrimitive, Formula.formalDerivative, Rat.pow_one]
  | succ n ih =>
      change 1 / (2 * ((n + 1 : Nat) : Rat) * b.val) *
          ((b.val - (2 * ((n + 1 : Nat) : Rat) - 1) * (x - a) * (x - a)) /
            quadratic a b.val x ^ (n + 2)) +
        ((2 * ((n + 1 : Nat) : Rat) - 1) / (2 * ((n + 1 : Nat) : Rat) * b.val)) *
          (quadraticPrimitive a b n).formalDerivative x = _
      rw [ih]
      exact quadratic_reduction (x - a) b.val ((n + 1 : Nat) : Rat) n
        (Rat.ne_of_gt b.property)
        (Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n)))
        (Rat.ne_of_gt (quadratic_pos a x b))

/-- A linear or quadratic partial fraction; the numerator of the quadratic
term is centered at `a`. The pole order is `n+1`. -/
inductive Term where
  | linear (c a : Rat) (n : Nat)
  | quadratic (A B a : Rat) (b : QPos) (n : Nat)

def Term.eval (x : Rat) : Term → Rat
  | .linear c a n => c / (x - a) ^ (n + 1)
  | .quadratic A B a b n => (A * (x - a) + B) / RationalPrimitiveFormula.quadratic a b.val x ^ (n + 1)

def Term.RegularAt (x : Rat) : Term → Prop
  | .linear _ a _ => x ≠ a
  | .quadratic _ _ _ _ _ => True

def Term.primitive : Term → Formula
  | .linear c a 0 => .scale c (.logLinear a)
  | .linear c a (n + 1) => .scale (-c / ((n + 1 : Nat) : Rat)) (.linearPower a n)
  | .quadratic A B a b 0 =>
      .add (.scale (A / 2) (.logQuadratic a b))
        (.scale B (quadraticPrimitive a b 0))
  | .quadratic A B a b (n + 1) =>
      .add (.scale (-A / (2 * ((n + 1 : Nat) : Rat))) (.quadraticPower a b n))
        (.scale B (quadraticPrimitive a b (n + 1)))

theorem Term.primitive_regular (term : Term) (x : Rat) (hx : term.RegularAt x) :
    term.primitive.RegularAt x := by
  cases term with
  | linear c a n => cases n <;> exact hx
  | quadratic A B a b n =>
      cases n <;> exact ⟨True.intro, quadraticPrimitive_regular _ _ _ _⟩

theorem Term.primitive_correct (term : Term) (x : Rat) (_hx : term.RegularAt x) :
    term.primitive.formalDerivative x = term.eval x := by
  cases term with
  | linear c a n =>
      cases n with
      | zero =>
          simp only [primitive, Formula.formalDerivative, eval, Nat.zero_add, Rat.pow_one,
            Rat.div_def, Rat.one_mul]
      | succ n =>
          have hn := Rat.mul_inv_cancel ((n + 1 : Nat) : Rat)
            (Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n)))
          simp only [primitive, Formula.formalDerivative, eval, Rat.div_def]
          grind
  | quadratic A B a b n =>
      cases n with
      | zero =>
          simp only [primitive, Formula.formalDerivative, eval, quadraticPrimitive_correct,
            Nat.zero_add, Rat.pow_one, Rat.div_def]
          grind
      | succ n =>
          have hn := Rat.mul_inv_cancel ((n + 1 : Nat) : Rat)
            (Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n)))
          simp only [primitive, Formula.formalDerivative, eval, quadraticPrimitive_correct,
            Rat.div_def, Rat.inv_mul_rev]
          grind

def sumTerms (x : Rat) : List Term → Rat
  | [] => 0
  | t :: ts => t.eval x + sumTerms x ts

def primitiveTerms : List Term → Formula
  | [] => .polynomial []
  | t :: ts => .add t.primitive (primitiveTerms ts)

theorem primitiveTerms_correct (terms : List Term) (x : Rat)
    (hx : ∀ t ∈ terms, t.RegularAt x) :
    (primitiveTerms terms).formalDerivative x = sumTerms x terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
      change t.primitive.formalDerivative x + (primitiveTerms ts).formalDerivative x = _
      rw [t.primitive_correct x (hx t (by simp)), ih (by
        intro u hu
        exact hx u (by simp [hu]))]
      rfl

structure NormalForm where
  polynomial : List Rat
  terms : List Term

def NormalForm.eval (f : NormalForm) (x : Rat) : Rat :=
  Polynomial.eval f.polynomial x + sumTerms x f.terms

def NormalForm.primitive (f : NormalForm) : Formula :=
  .add (.polynomial (Polynomial.primitive f.polynomial)) (primitiveTerms f.terms)

theorem NormalForm.primitive_regular (f : NormalForm) (x : Rat)
    (hx : ∀ t ∈ f.terms, t.RegularAt x) : f.primitive.RegularAt x := by
  refine ⟨True.intro, ?_⟩
  change (primitiveTerms f.terms).RegularAt x
  generalize f.terms = ts at hx ⊢
  induction ts with
  | nil => trivial
  | cons t ts ih =>
      refine ⟨t.primitive_regular x (hx t (by simp)), ?_⟩
      exact ih (by intro u hu; exact hx u (by simp [hu]))

theorem NormalForm.primitive_correct (f : NormalForm) (x : Rat)
    (hx : ∀ t ∈ f.terms, t.RegularAt x) :
    f.primitive.formalDerivative x = f.eval x := by
  change Polynomial.eval (Polynomial.derivative (Polynomial.primitive f.polynomial)) x +
    (primitiveTerms f.terms).formalDerivative x = _
  rw [Polynomial.derivative_primitive, primitiveTerms_correct f.terms x hx]
  rfl

/-- A supplied decomposition, not an assertion that all rational functions
admit such a decomposition with rational centers and coefficients. -/
structure Decomposition (f : RatFun) where
  normalForm : NormalForm
  regular : ∀ x, f.DefinedAt x → ∀ t ∈ normalForm.terms, t.RegularAt x
  identity : ∀ x (hx : f.DefinedAt x), normalForm.eval x = f.evalOnDomain x hx

/-- Soundness of the computed formula, conditional only at the finite
decomposition layer. Analytic realization remains a separate theorem. -/
theorem Decomposition.primitive_correct {f : RatFun} (d : Decomposition f)
    (x : Rat) (hx : f.DefinedAt x) :
    d.normalForm.primitive.formalDerivative x = f.evalOnDomain x hx := by
  rw [d.normalForm.primitive_correct x (d.regular x hx)]
  exact d.identity x hx

theorem Decomposition.primitive_regular {f : RatFun} (d : Decomposition f)
    (x : Rat) (hx : f.DefinedAt x) : d.normalForm.primitive.RegularAt x :=
  d.normalForm.primitive_regular x (d.regular x hx)

end RationalPrimitiveFormula
end ComputableAnalysis
