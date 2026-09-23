import ComputableAnalysis.RationalExpressionNormalization

/-!
# Rationalization on a stereographic circle chart

Every rational expression in two coordinates pulls back to a `RatFun` along
the tangent-half-angle chart, including its Jacobian. The theorem preserves
the exact domain of the expression. This finite result is the algebraic step
of the trigonometric integration corollary; identifying an angle evaluator
and applying an analytic chain rule are separate obligations.
-/

namespace ComputableAnalysis
namespace TrigonometricRationalization

/-- Syntax for a rational expression in sine and cosine, with partial inverse. -/
inductive Expr where
  | sine | cosine
  | const (q : Rat)
  | neg (e : Expr)
  | add (a b : Expr)
  | mul (a b : Expr)
  | inv (e : Expr)
deriving Repr, DecidableEq

def Expr.eval (s c : Rat) : Expr → Option Rat
  | .sine => some s
  | .cosine => some c
  | .const q => some q
  | .neg e => (e.eval s c).map (fun y => -y)
  | .add a b => match a.eval s c, b.eval s c with
    | some y, some z => some (y + z)
    | _, _ => none
  | .mul a b => match a.eval s c, b.eval s c with
    | some y, some z => some (y * z)
    | _, _ => none
  | .inv e => match e.eval s c with
    | some y => if y = 0 then none else some (1 / y)
    | none => none

def circleDenominator : RatExpr := .add (.const 1) (.mul .var .var)
def sineExpr : RatExpr := .div (.mul (.const 2) .var) circleDenominator
def cosineExpr : RatExpr :=
  .div (.sub (.const 1) (.mul .var .var)) circleDenominator
def jacobianExpr : RatExpr := .div (.const 2) circleDenominator

def sineCoordinate (t : Rat) : Rat := 2 * t / (1 + t * t)
def cosineCoordinate (t : Rat) : Rat := (1 - t * t) / (1 + t * t)
def jacobian (t : Rat) : Rat := 2 / (1 + t * t)

theorem denominator_pos (t : Rat) : 0 < 1 + t * t := by
  have hs : 0 ≤ t * t := by
    by_cases h : 0 ≤ t
    · exact Rat.mul_nonneg h h
    · have hn : 0 ≤ -t := by grind
      have hh := Rat.mul_nonneg hn hn
      grind
  grind

theorem sineExpr_eval (t : Rat) : sineExpr.eval t = some (sineCoordinate t) := by
  have hd := Rat.ne_of_gt (denominator_pos t)
  simp [sineExpr, circleDenominator, RatExpr.div, RatExpr.eval, hd, sineCoordinate,
    Rat.div_def]

theorem cosineExpr_eval (t : Rat) : cosineExpr.eval t = some (cosineCoordinate t) := by
  have hd := Rat.ne_of_gt (denominator_pos t)
  simp [cosineExpr, circleDenominator, RatExpr.div, RatExpr.sub, RatExpr.eval,
    hd, cosineCoordinate, Rat.div_def, Rat.sub_eq_add_neg]

theorem jacobianExpr_eval (t : Rat) : jacobianExpr.eval t = some (jacobian t) := by
  have hd := Rat.ne_of_gt (denominator_pos t)
  simp [jacobianExpr, circleDenominator, RatExpr.div, RatExpr.eval, hd, jacobian,
    Rat.div_def]

def Expr.substitute : Expr → RatExpr
  | .sine => sineExpr
  | .cosine => cosineExpr
  | .const q => .const q
  | .neg e => .neg e.substitute
  | .add a b => .add a.substitute b.substitute
  | .mul a b => .mul a.substitute b.substitute
  | .inv e => .inv e.substitute

theorem Expr.substitute_correct (e : Expr) (t : Rat) :
    e.substitute.eval t = e.eval (sineCoordinate t) (cosineCoordinate t) := by
  induction e with
  | sine => exact sineExpr_eval t
  | cosine => exact cosineExpr_eval t
  | const q => rfl
  | neg e ih => simp only [substitute, RatExpr.eval, Expr.eval, ih]
  | add a b ia ib =>
      simp only [substitute, RatExpr.eval, Expr.eval, ia, ib]
      cases a.eval (sineCoordinate t) (cosineCoordinate t) <;>
        cases b.eval (sineCoordinate t) (cosineCoordinate t) <;> rfl
  | mul a b ia ib =>
      simp only [substitute, RatExpr.eval, Expr.eval, ia, ib]
      cases a.eval (sineCoordinate t) (cosineCoordinate t) <;>
        cases b.eval (sineCoordinate t) (cosineCoordinate t) <;> rfl
  | inv e ih =>
      simp only [substitute, RatExpr.eval, Expr.eval, ih]
      cases e.eval (sineCoordinate t) (cosineCoordinate t) <;> rfl

/-- The rational integrand after including the change-of-variable factor. -/
def Expr.pullback (e : Expr) : RatFun :=
  RationalExpressionNormalization.compile (.mul e.substitute jacobianExpr)

/-- Universal finite rationalization, with poles retained. -/
theorem Expr.pullback_correct (e : Expr) (t : Rat) :
    e.pullback.eval? t =
      (e.eval (sineCoordinate t) (cosineCoordinate t)).map (fun v => v * jacobian t) := by
  rw [pullback, RationalExpressionNormalization.compile_correct]
  simp only [RatExpr.eval, substitute_correct, jacobianExpr_eval]
  cases e.eval (sineCoordinate t) (cosineCoordinate t) <;> rfl

theorem Expr.pullback_defined_iff (e : Expr) (t : Rat) :
    e.pullback.eval? t ≠ none ↔ e.eval (sineCoordinate t) (cosineCoordinate t) ≠ none := by
  rw [pullback_correct]
  cases e.eval (sineCoordinate t) (cosineCoordinate t) <;> simp

/-- The chart actually lies on the circle. -/
theorem circle_identity (t : Rat) :
    sineCoordinate t * sineCoordinate t + cosineCoordinate t * cosineCoordinate t = 1 := by
  have hd := Rat.ne_of_gt (denominator_pos t)
  have hi := Rat.mul_inv_cancel _ hd
  unfold sineCoordinate cosineCoordinate
  simp only [Rat.div_def]
  grind

/-- The missing point of this chart is the antipode, not an integrand pole. -/
theorem one_add_cosine (t : Rat) : 1 + cosineCoordinate t = jacobian t := by
  have hd := Rat.ne_of_gt (denominator_pos t)
  have hi := Rat.mul_inv_cancel _ hd
  unfold cosineCoordinate jacobian
  simp only [Rat.div_def]
  grind

theorem jacobian_pos (t : Rat) : 0 < jacobian t := by
  unfold jacobian
  rw [Rat.div_def]
  exact Rat.mul_pos (by decide) ((Rat.inv_pos).2 (denominator_pos t))

/-- Inverse stereographic coordinate on this chart. -/
theorem recover_parameter (t : Rat) : sineCoordinate t / (1 + cosineCoordinate t) = t := by
  rw [one_add_cosine]
  have hd := Rat.ne_of_gt (denominator_pos t)
  have hi := Rat.mul_inv_cancel _ hd
  unfold sineCoordinate jacobian
  simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv]
  grind

/-- Changing to the chart centered at the antipode changes both coordinates'
signs. This handles the point omitted by the first chart. -/
def Expr.antipodal : Expr → Expr
  | .sine => .neg .sine
  | .cosine => .neg .cosine
  | .const q => .const q
  | .neg e => .neg e.antipodal
  | .add a b => .add a.antipodal b.antipodal
  | .mul a b => .mul a.antipodal b.antipodal
  | .inv e => .inv e.antipodal

theorem Expr.antipodal_correct (e : Expr) (s c : Rat) :
    e.antipodal.eval s c = e.eval (-s) (-c) := by
  induction e with
  | sine => rfl
  | cosine => rfl
  | const q => rfl
  | neg e ih => simp only [antipodal, Expr.eval, ih]
  | add a b ia ib => simp only [antipodal, Expr.eval, ia, ib]
  | mul a b ia ib => simp only [antipodal, Expr.eval, ia, ib]
  | inv e ih => simp only [antipodal, Expr.eval, ih]

theorem Expr.antipodal_pullback_correct (e : Expr) (t : Rat) :
    e.antipodal.pullback.eval? t =
      (e.eval (-sineCoordinate t) (-cosineCoordinate t)).map
        (fun v => v * jacobian t) := by
  rw [pullback_correct, antipodal_correct]

/-- Inverse of the first chart for every rational point except the antipode. -/
theorem chart_inverse (s c : Rat) (hcirc : s * s + c * c = 1) (hc : 1 + c ≠ 0) :
    sineCoordinate (s / (1 + c)) = s ∧ cosineCoordinate (s / (1 + c)) = c := by
  have hi := Rat.mul_inv_cancel (1 + c) hc
  have hj := Rat.mul_inv_cancel (1 + s / (1 + c) * (s / (1 + c)))
    (Rat.ne_of_gt (denominator_pos (s / (1 + c))))
  unfold sineCoordinate cosineCoordinate
  simp only [Rat.div_def] at *
  constructor <;> grind

/-- Two rational charts cover the rational circle. This does not assert a
global tangent function or a global branch of the angle. -/
theorem rational_circle_chart_cover (s c : Rat) (hcirc : s * s + c * c = 1) :
    (∃ t, sineCoordinate t = s ∧ cosineCoordinate t = c) ∨
      (∃ t, -sineCoordinate t = s ∧ -cosineCoordinate t = c) := by
  by_cases hc : 1 + c = 0
  · right
    have hn : 1 + -c ≠ 0 := by grind
    have hcircle : (-s) * (-s) + (-c) * (-c) = 1 := by grind
    have h := chart_inverse (-s) (-c) hcircle hn
    refine ⟨(-s) / (1 + -c), ?_, ?_⟩ <;> grind
  · exact Or.inl ⟨s / (1 + c), chart_inverse s c hcirc hc⟩

end TrigonometricRationalization
end ComputableAnalysis
