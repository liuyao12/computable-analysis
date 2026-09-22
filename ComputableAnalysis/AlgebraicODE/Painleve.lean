import ComputableAnalysis.AlgebraicODE.Expressions
import ComputableAnalysis.DifferentialReciprocal

/-! Painlevé I and II in the DLMF convention. Exact rational residual
theorems are separated from two-sided finite-difference certificates. -/
namespace ComputableAnalysis.AlgebraicODE.Painleve

def first : Equation := .add ddy (.neg (.add
  (.mul (.const 6) (.mul y y)) x))
def second (alpha : Rat) : Equation := .add ddy (.neg (.add
  (.add (.mul (.const 2) (.mul y (.mul y y))) (.mul x y)) (.const alpha)))

def I (x y ddy : Rat) : Prop := ddy = 6 * y ^ 2 + x
def II (alpha x y ddy : Rat) : Prop := ddy = 2 * y ^ 3 + x * y + alpha

theorem first_eval (a b c d : Rat) :
    first.evalRat (fun i => if i.val = 0 then a else if i.val = 1 then b
      else if i.val = 2 then c else d) = d - (6 * b ^ 2 + a) := by
  simp [first, x, y, ddy, Expr.evalRat, Rat.pow_succ]
  grind

theorem second_eval (alpha a b c d : Rat) :
    (second alpha).evalRat (fun i => if i.val = 0 then a else if i.val = 1 then b
      else if i.val = 2 then c else d) = d - (2 * b ^ 3 + a * b + alpha) := by
  simp [second, x, y, ddy, Expr.evalRat, Rat.pow_succ]
  grind [Rat.mul_assoc]

theorem zero_solution (x : Rat) : II 0 x 0 0 := by simp [II, Rat.pow_succ]; grind

theorem sign_symmetry (alpha x y ddy : Rat) :
    II alpha x y ddy ↔ II (-alpha) x (-y) (-ddy) := by
  simp only [II, Rat.pow_succ]
  grind

/-- The only constant solution is zero, at parameter zero. -/
theorem constant_classification (alpha c : Rat) :
    (∀ x, II alpha x c 0) ↔ c = 0 ∧ alpha = 0 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [II] at h0 h1
    grind
  · rintro ⟨rfl, rfl⟩
    exact zero_solution

theorem first_no_constant (c : Rat) : ¬ (∀ x, I x c 0) := by
  intro h
  have h0 := h 0
  have h1 := h 1
  simp only [I] at h0 h1
  grind

/-- All affine candidates for PII are classified; this is not yet the
arbitrary-degree polynomial nonexistence theorem. -/
theorem affine_classification (alpha a b : Rat) :
    (∀ x, II alpha x (a * x + b) 0) ↔ a = 0 ∧ b = 0 ∧ alpha = 0 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have hm := h (-1)
    have h2 := h 2
    simp only [II, Rat.pow_succ] at h0 h1 hm h2
    grind
  · rintro ⟨rfl, rfl, rfl⟩ x
    simp [II, Rat.pow_succ]
    grind

/-- The Riccati reduction at alpha=1/2, as a second-jet identity.
An application must separately certify both differentiations. -/
theorem riccati_half (x y dy ddy : Rat)
    (hfirst : dy = y ^ 2 + x / 2)
    (hsecond : ddy = 2 * y * dy + 1 / 2) : II (1 / 2) x y ddy := by
  simp only [II, Rat.pow_succ] at *
  grind

/-- Classification of the simple-pole ansatz `c/x`, on the punctured line.
The derivatives are `-c/x²` and `2c/x³`; certificates follow below. -/
theorem simple_pole_classification (alpha c : Rat) :
    (∀ x : Rat, x ≠ 0 → II alpha x (c / x) (2 * c / x ^ 3)) ↔
      alpha = -c ∧ (c = 0 ∨ c = 1 ∨ c = -1) := by
  constructor
  · intro h
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    simp [II, Rat.pow_succ] at h1 h2
    grind
  · rintro ⟨rfl, hc⟩ x hx
    have hi := Rat.mul_inv_cancel x hx
    rcases hc with rfl | rfl | rfl <;>
      simp [II, Rat.div_def, Rat.pow_succ, Rat.inv_mul_rev] <;>
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Explicit nonzero algebraic relation for the pole family: `x*y-c=0`. -/
def poleRelation (c : Rat) : AlgebraicRelation where
  polynomial := .add (.mul (.var 0) (.var 1)) (.const (-c))
  witness := fun i => if i.val = 0 then 1 else c + 1
  nonzero := by simp [Expr.evalRat]; grind

theorem pole_algebraic (c x : Rat) (hx : x ≠ 0) :
    (poleRelation c).polynomial.evalRat
      (fun i => if i.val = 0 then x else c / x) = 0 := by
  have hi := Rat.mul_inv_cancel x hx
  simp [poleRelation, Expr.evalRat, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- A finite-difference certificate for the first derivative of `c/x`. -/
def poleFirstDerivative (c a b : Rat) (ha : 0 < a) (hab : a ≤ b) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (fun x => c * (1 / x)) a b)
      (FunctionOnInterval.exactRat (fun x => c * (-(1 / x ^ 2))) a b) := by
  let D := (FinitePolynomial.positiveReciprocalCenteredSecantBound a b ha hab).scaleRat c
  exact D.toHasDerivativeOnInterval a b (by grind) (by grind)

/-- The second derivative, via the existing inverse-square secant bound. -/
def poleSecondDerivative (c a b : Rat) (ha : 0 < a) (hab : a ≤ b) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (fun x => c * (-(1 / x ^ 2))) a b)
      (FunctionOnInterval.exactRat (fun x => 2 * c / x ^ 3) a b) := by
  let D := (FinitePolynomial.inverseSquareTimeCenteredSecantBound a b ha hab).scaleRat (-4 * c)
  have hf : (fun x : Rat => (-4 * c) * (1 / (4 * x ^ 2))) =
      (fun x => c * (-(1 / x ^ 2))) := by
    funext x
    simp [Rat.div_def, Rat.inv_mul_rev]
    grind
  have hd : (fun x : Rat => (-4 * c) * (-(1 / (2 * x ^ 3)))) =
      (fun x => 2 * c / x ^ 3) := by
    funext x
    simp [Rat.div_def, Rat.inv_mul_rev]
    grind
  rw [hf, hd] at D
  exact D.toHasDerivativeOnInterval a b (by grind) (by grind)

/-- An actual interval solution package: both derivative certificates,
the ODE, and a nonzero algebraic relation refer to the same evaluator. -/
structure AlgebraicSolutionOn (alpha a b : Rat) where
  value : Rat → Rat
  derivative : Rat → Rat
  secondDerivative : Rat → Rat
  first_certificate : HasDerivativeOnInterval
    (FunctionOnInterval.exactRat value a b)
    (FunctionOnInterval.exactRat derivative a b)
  second_certificate : HasDerivativeOnInterval
    (FunctionOnInterval.exactRat derivative a b)
    (FunctionOnInterval.exactRat secondDerivative a b)
  equation : ∀ x, inDomainInterval a b x → II alpha x (value x) (secondDerivative x)
  relation : AlgebraicRelation
  algebraic : ∀ x, inDomainInterval a b x →
    relation.polynomial.evalRat (fun i => if i.val = 0 then x else value x) = 0

/-- Construct the three simple-pole/zero algebraic solutions on every
positive rational interval, using genuine secant derivative certificates. -/
def poleSolution (c a b : Rat) (hc : c = 0 ∨ c = 1 ∨ c = -1)
    (ha : 0 < a) (hab : a ≤ b) : AlgebraicSolutionOn (-c) a b where
  value := fun x => c * (1 / x)
  derivative := fun x => c * (-(1 / x ^ 2))
  secondDerivative := fun x => 2 * c / x ^ 3
  first_certificate := poleFirstDerivative c a b ha hab
  second_certificate := poleSecondDerivative c a b ha hab
  equation := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have hax := hx.1
      grind
    simpa [Rat.div_def, Rat.one_mul] using
      (simple_pole_classification (-c) c).mpr ⟨rfl, hc⟩ x hx0
  relation := poleRelation c
  algebraic := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have hax := hx.1
      grind
    simpa [Rat.div_def, Rat.one_mul] using pole_algebraic c x hx0

end ComputableAnalysis.AlgebraicODE.Painleve
