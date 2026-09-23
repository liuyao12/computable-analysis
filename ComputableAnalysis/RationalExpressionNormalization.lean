import ComputableAnalysis.Polynomial

/-!
# Domain-preserving rational-expression normalization

Finite polynomial arithmetic and a compiler from `RatExpr` to `RatFun`.
The compiler preserves *undefinedness* as well as values. In particular,
inverting a quotient keeps its original denominator as a guard. No pole is
silently filled by cancellation. This is rational algebra, not calculus.
-/

namespace ComputableAnalysis
namespace RationalExpressionNormalization

def add : List Rat → List Rat → List Rat
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : Rat) (p : List Rat) : List Rat := p.map (a * ·)

def mul : List Rat → List Rat → List Rat
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

theorem eval_add (p q : List Rat) (x : Rat) :
    Polynomial.eval (add p q) x = Polynomial.eval p x + Polynomial.eval q x := by
  induction p generalizing q with
  | nil => simp [add, Polynomial.eval, Rat.zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp [add, Polynomial.eval, Rat.add_zero]
    | cons b q =>
      change a + b + x * Polynomial.eval (add p q) x =
        (a + x * Polynomial.eval p x) + (b + x * Polynomial.eval q x)
      rw [ih]
      grind

theorem eval_scale (a : Rat) (p : List Rat) (x : Rat) :
    Polynomial.eval (scale a p) x = a * Polynomial.eval p x := by
  induction p with
  | nil => simp [scale, Polynomial.eval]
  | cons b p ih =>
    change a * b + x * Polynomial.eval (scale a p) x =
      a * (b + x * Polynomial.eval p x)
    rw [ih]
    grind

theorem eval_mul (p q : List Rat) (x : Rat) :
    Polynomial.eval (mul p q) x = Polynomial.eval p x * Polynomial.eval q x := by
  induction p with
  | nil => simp [mul, Polynomial.eval]
  | cons a p ih =>
    rw [mul, eval_add, eval_scale]
    change a * Polynomial.eval q x + (0 + x * Polynomial.eval (mul p q) x) =
      (a + x * Polynomial.eval p x) * Polynomial.eval q x
    rw [ih]
    grind

def negFun (f : RatFun) : RatFun := ⟨scale (-1) f.num, f.den⟩
def addFun (f g : RatFun) : RatFun :=
  ⟨add (mul f.num g.den) (mul g.num f.den), mul f.den g.den⟩
def mulFun (f g : RatFun) : RatFun := ⟨mul f.num g.num, mul f.den g.den⟩

/-- The extra denominator factor retains the poles of the operand. -/
def invFun (f : RatFun) : RatFun := ⟨mul f.den f.den, mul f.num f.den⟩

private theorem div_add (a b c d : Rat) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a * d + c * b) / (b * d) = a / b + c / d := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have hbi := Rat.mul_inv_cancel _ hb
  have hdi := Rat.mul_inv_cancel _ hd
  grind

private theorem div_mul (a b c d : Rat) :
    (a * c) / (b * d) = (a / b) * (c / d) := by
  simp only [Rat.div_def, Rat.inv_mul_rev]
  grind

private theorem div_inv_guarded (a b : Rat) (_ha : a ≠ 0) (hb : b ≠ 0) :
    b * b / (a * b) = 1 / (a / b) := by
  simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv, Rat.one_mul]
  have hbi := Rat.mul_inv_cancel _ hb
  grind

theorem eval_negFun (f : RatFun) (x : Rat) :
    (negFun f).eval? x = (f.eval? x).map (fun y => -y) := by
  simp only [RatFun.eval?, RatFun.numerator, RatFun.denominator, negFun, eval_scale]
  split <;> simp_all [Rat.div_def, Rat.neg_mul]

theorem eval_addFun (f g : RatFun) (x : Rat) :
    (addFun f g).eval? x =
      match f.eval? x, g.eval? x with
      | some y, some z => some (y + z)
      | _, _ => none := by
  simp only [RatFun.eval?, RatFun.numerator, RatFun.denominator, addFun,
    eval_add, eval_mul]
  by_cases hf : Polynomial.eval f.den x = 0
  · simp [hf]
  · by_cases hg : Polynomial.eval g.den x = 0
    · simp [hg]
    · simp [hf, hg, (by grind [Rat.mul_eq_zero] : Polynomial.eval f.den x * Polynomial.eval g.den x ≠ 0), div_add _ _ _ _ hf hg]

theorem eval_mulFun (f g : RatFun) (x : Rat) :
    (mulFun f g).eval? x =
      match f.eval? x, g.eval? x with
      | some y, some z => some (y * z)
      | _, _ => none := by
  simp only [RatFun.eval?, RatFun.numerator, RatFun.denominator, mulFun, eval_mul]
  by_cases hf : Polynomial.eval f.den x = 0
  · simp [hf]
  · by_cases hg : Polynomial.eval g.den x = 0
    · simp [hg]
    · simp [hf, hg, (by grind [Rat.mul_eq_zero] : Polynomial.eval f.den x * Polynomial.eval g.den x ≠ 0), div_mul]

theorem eval_invFun (f : RatFun) (x : Rat) :
    (invFun f).eval? x =
      match f.eval? x with
      | some y => if y = 0 then none else some (1 / y)
      | none => none := by
  simp only [RatFun.eval?, RatFun.numerator, RatFun.denominator, invFun, eval_mul]
  by_cases hd : Polynomial.eval f.den x = 0
  · simp [hd]
  · by_cases hn : Polynomial.eval f.num x = 0
    · simp [hn, hd, Rat.div_def]
    · have hv : Polynomial.eval f.num x / Polynomial.eval f.den x ≠ 0 := by
        simp only [Rat.div_def]
        have hi := Rat.mul_inv_cancel _ hd
        grind [Rat.mul_eq_zero]
      simp [hd, hv, (by grind [Rat.mul_eq_zero] : Polynomial.eval f.num x * Polynomial.eval f.den x ≠ 0), div_inv_guarded _ _ hn hd]

/-- An executable compiler; no polynomial factoring or cancellation is used. -/
def compile : RatExpr → RatFun
  | .var => ⟨[0, 1], [1]⟩
  | .const q => ⟨[q], [1]⟩
  | .neg e => negFun (compile e)
  | .add a b => addFun (compile a) (compile b)
  | .mul a b => mulFun (compile a) (compile b)
  | .inv e => invFun (compile e)

/-- All expressions, all rational inputs, including every undefined case. -/
theorem compile_correct (e : RatExpr) (x : Rat) :
    (compile e).eval? x = e.eval x := by
  induction e with
  | var => simp [compile, RatExpr.eval, RatFun.eval?, RatFun.numerator,
      RatFun.denominator, Polynomial.eval, Rat.zero_add, Rat.add_zero, Rat.mul_one, Rat.div_def, (show (1 : Rat)⁻¹ = 1 by have h := Rat.mul_inv_cancel (1 : Rat) (by decide); grind), Rat.mul_one]
  | const q => simp [compile, RatExpr.eval, RatFun.eval?, RatFun.numerator,
      RatFun.denominator, Polynomial.eval, Rat.add_zero, Rat.div_def, (show (1 : Rat)⁻¹ = 1 by have h := Rat.mul_inv_cancel (1 : Rat) (by decide); grind), Rat.mul_one]
  | neg e ih => simp only [compile, RatExpr.eval, eval_negFun, ih]
  | add a b ia ib =>
      simp only [compile, RatExpr.eval, eval_addFun, ia, ib]
      cases a.eval x <;> cases b.eval x <;> rfl
  | mul a b ia ib =>
      simp only [compile, RatExpr.eval, eval_mulFun, ia, ib]
      cases a.eval x <;> cases b.eval x <;> rfl
  | inv e ih =>
      simp only [compile, RatExpr.eval, eval_invFun, ih]
      cases e.eval x <;> rfl

end RationalExpressionNormalization
end ComputableAnalysis
