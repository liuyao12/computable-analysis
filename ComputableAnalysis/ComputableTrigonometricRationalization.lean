import ComputableAnalysis.ComputableFactoredPrimitives
import ComputableAnalysis.TrigonometricRationalization

/-! Domain-preserving half-angle substitution with computable coefficients.
Sampling is only the proof device: the compiler retains the original real
parameters and its output is executable certified coefficient arithmetic. -/
namespace ComputableAnalysis
namespace ComputableTrigonometricRationalization
open ComputableCoefficient
abbrev C := ComputableCoefficient.Expr

inductive Expr where
  | sine | cosine
  | const (c : C)
  | neg (e : Expr)
  | add (e f : Expr)
  | mul (e f : Expr)
  | inv (e : Expr)

def Expr.shadow (s : Real → Rat) : Expr → TrigonometricRationalization.Expr
  | .sine => .sine
  | .cosine => .cosine
  | .const c => .const (c.sample s)
  | .neg e => .neg (e.shadow s)
  | .add e f => .add (e.shadow s) (f.shadow s)
  | .mul e f => .mul (e.shadow s) (f.shadow s)
  | .inv e => .inv (e.shadow s)

def Expr.value (sin cos : C) : Expr → C
  | .sine => sin
  | .cosine => cos
  | .const c => c
  | .neg e => .neg (e.value sin cos)
  | .add e f => .add (e.value sin cos) (f.value sin cos)
  | .mul e f => .mul (e.value sin cos) (f.value sin cos)
  | .inv e => .inv (e.value sin cos)

/-- Polynomial quotient with the original domain guard retained. -/
structure Rational where
  num : List C
  den : List C

def Rational.shadow (s : Real → Rat) (f : Rational) : RatFun :=
  ⟨ComputableFactoredAlgebra.sampled s f.num, ComputableFactoredAlgebra.sampled s f.den⟩

def Rational.value (f : Rational) (x : C) : C :=
  (ComputableFactoredAlgebra.eval f.num x).div (ComputableFactoredAlgebra.eval f.den x)

def Rational.neg (f : Rational) : Rational :=
  ⟨ComputableFactoredAlgebra.scale (.rational (-1)) f.num, f.den⟩
def Rational.add (f g : Rational) : Rational :=
  ⟨ComputableFactoredAlgebra.add (ComputableFactoredAlgebra.mul f.num g.den)
    (ComputableFactoredAlgebra.mul g.num f.den), ComputableFactoredAlgebra.mul f.den g.den⟩
def Rational.mul (f g : Rational) : Rational :=
  ⟨ComputableFactoredAlgebra.mul f.num g.num, ComputableFactoredAlgebra.mul f.den g.den⟩
def Rational.inv (f : Rational) : Rational :=
  ⟨ComputableFactoredAlgebra.mul f.den f.den, ComputableFactoredAlgebra.mul f.num f.den⟩

@[simp] theorem Rational.shadow_neg (s : Real → Rat) (f : Rational) :
    (f.neg).shadow s = RationalExpressionNormalization.negFun (f.shadow s) := by
  simp [neg, shadow, ComputableFactoredAlgebra.sample_scale, ComputableCoefficient.Expr.sample,
    RationalExpressionNormalization.negFun]
@[simp] theorem Rational.shadow_add (s : Real → Rat) (f g : Rational) :
    (f.add g).shadow s = RationalExpressionNormalization.addFun (f.shadow s) (g.shadow s) := by
  simp [add, shadow, ComputableFactoredAlgebra.sample_add, ComputableFactoredAlgebra.sample_mul,
    RationalExpressionNormalization.addFun]
@[simp] theorem Rational.shadow_mul (s : Real → Rat) (f g : Rational) :
    (f.mul g).shadow s = RationalExpressionNormalization.mulFun (f.shadow s) (g.shadow s) := by
  simp [mul, shadow, ComputableFactoredAlgebra.sample_mul, RationalExpressionNormalization.mulFun]
@[simp] theorem Rational.shadow_inv (s : Real → Rat) (f : Rational) :
    (f.inv).shadow s = RationalExpressionNormalization.invFun (f.shadow s) := by
  simp [inv, shadow, ComputableFactoredAlgebra.sample_mul, RationalExpressionNormalization.invFun]

def lift (f : RatFun) : Rational := ⟨f.num.map ComputableCoefficient.Expr.rational, f.den.map ComputableCoefficient.Expr.rational⟩
@[simp] theorem shadow_lift (s : Real → Rat) (f : RatFun) : (lift f).shadow s = f := by
  cases f
  simp [lift, Rational.shadow, ComputableFactoredAlgebra.sampled, List.map_map, Function.comp_def, C,
    ComputableCoefficient.Expr.sample]

def Expr.compile : Expr → Rational
  | .sine => lift (RationalExpressionNormalization.compile TrigonometricRationalization.sineExpr)
  | .cosine => lift (RationalExpressionNormalization.compile TrigonometricRationalization.cosineExpr)
  | .const c => ⟨[c], [.rational 1]⟩
  | .neg e => e.compile.neg
  | .add e f => e.compile.add f.compile
  | .mul e f => e.compile.mul f.compile
  | .inv e => e.compile.inv

@[simp] theorem Expr.shadow_compile (e : Expr) (s : Real → Rat) :
    e.compile.shadow s = RationalExpressionNormalization.compile (e.shadow s).substitute := by
  induction e with
  | sine => exact shadow_lift s _
  | cosine => exact shadow_lift s _
  | const c => rfl
  | neg e ih => simp only [compile, Rational.shadow_neg, ih, shadow,
      TrigonometricRationalization.Expr.substitute, RationalExpressionNormalization.compile]
  | add e f ie iff => simp only [compile, Rational.shadow_add, ie, iff, shadow,
      TrigonometricRationalization.Expr.substitute, RationalExpressionNormalization.compile]
  | mul e f ie iff => simp only [compile, Rational.shadow_mul, ie, iff, shadow,
      TrigonometricRationalization.Expr.substitute, RationalExpressionNormalization.compile]
  | inv e ih => simp only [compile, Rational.shadow_inv, ih, shadow,
      TrigonometricRationalization.Expr.substitute, RationalExpressionNormalization.compile]

def Expr.pullback (e : Expr) : Rational := e.compile.mul
  (lift (RationalExpressionNormalization.compile TrigonometricRationalization.jacobianExpr))

theorem Expr.shadow_pullback (e : Expr) (s : Real → Rat) :
    e.pullback.shadow s = (e.shadow s).pullback := by
  simp only [pullback, Rational.shadow_mul, shadow_lift, shadow_compile,
    TrigonometricRationalization.Expr.pullback, RationalExpressionNormalization.compile]

theorem Expr.pullback_correct (e : Expr) (s : Real → Rat) (t : Rat) :
    (e.pullback.shadow s).eval? t =
      ((e.shadow s).eval (TrigonometricRationalization.sineCoordinate t)
        (TrigonometricRationalization.cosineCoordinate t)).map
        (fun v => v * TrigonometricRationalization.jacobian t) := by
  rw [shadow_pullback, TrigonometricRationalization.Expr.pullback_correct]

theorem Expr.pullback_defined_iff (e : Expr) (s : Real → Rat) (t : Rat) :
    (e.pullback.shadow s).eval? t ≠ none ↔
      (e.shadow s).eval (TrigonometricRationalization.sineCoordinate t)
        (TrigonometricRationalization.cosineCoordinate t) ≠ none := by
  rw [shadow_pullback, TrigonometricRationalization.Expr.pullback_defined_iff]

/-- The inverse chart's derivative, for angle rather than parameter. -/
def inverseJacobian (t : Rat) : Rat := (1+t*t)/2

theorem jacobian_cancel (t : Rat) :
    TrigonometricRationalization.jacobian t * inverseJacobian t = 1 := by
  have hn := Rat.ne_of_gt (TrigonometricRationalization.denominator_pos t)
  have hc := Rat.mul_inv_cancel _ hn
  simp only [TrigonometricRationalization.jacobian, inverseJacobian, Rat.div_def]
  have ht := Rat.mul_inv_cancel (2 : Rat) (by decide +kernel)
  grind

/-- The chain factor follows from `sin' = cos`, `cos' = -sin`, and
`sin^2+cos^2=1`; it is not an assumed tangent derivative law. -/
theorem halfAngle_derivative (s c : Rat) (hcircle : s*s+c*c=1) (hc : 1+c ≠ 0) :
    (c*(1+c)+s*s)/((1+c)*(1+c)) = inverseJacobian (s/(1+c)) := by
  have hi := Rat.mul_inv_cancel (1+c) hc
  simp only [inverseJacobian, Rat.div_def, Rat.inv_mul_rev]
  have ht := Rat.mul_inv_cancel (2 : Rat) (by decide +kernel)
  grind

/-- The opposite chart retains the coefficient algorithms. -/
def Expr.antipodal : Expr → Expr
  | .sine => .neg .sine
  | .cosine => .neg .cosine
  | .const c => .const c
  | .neg e => .neg e.antipodal
  | .add e f => .add e.antipodal f.antipodal
  | .mul e f => .mul e.antipodal f.antipodal
  | .inv e => .inv e.antipodal

theorem Expr.shadow_antipodal (e : Expr) (s : Real → Rat) :
    e.antipodal.shadow s = (e.shadow s).antipodal := by
  induction e <;> simp_all [antipodal, shadow, TrigonometricRationalization.Expr.antipodal]

theorem Expr.antipodal_pullback_correct (e : Expr) (s : Real → Rat) (t : Rat) :
    (e.antipodal.pullback.shadow s).eval? t =
      ((e.shadow s).eval (-TrigonometricRationalization.sineCoordinate t)
        (-TrigonometricRationalization.cosineCoordinate t)).map
        (fun v => v * TrigonometricRationalization.jacobian t) := by
  rw [shadow_pullback, shadow_antipodal, TrigonometricRationalization.Expr.antipodal_pullback_correct]

end ComputableTrigonometricRationalization
end ComputableAnalysis
