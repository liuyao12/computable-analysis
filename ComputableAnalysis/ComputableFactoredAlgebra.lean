import ComputableAnalysis.ComputableCoefficient
import ComputableAnalysis.RationalFactoredPrimitives

/-!
# Factored rational algebra with computable-real coefficients

The executable coefficient expressions retain their certified real parameters.
Rational sampling verifies arithmetic identities; `Expr.realize_equiv` then
transports those identities to the interval evaluators.
-/
namespace ComputableAnalysis
namespace ComputableFactoredAlgebra
open ComputableCoefficient

abbrev C := Expr
local instance : OfNat C n := ⟨.rational n⟩
local instance : Add C := ⟨.add⟩
local instance : Mul C := ⟨.mul⟩
local instance : Neg C := ⟨.neg⟩
local instance : Sub C := ⟨.sub⟩
local instance : Div C := ⟨.div⟩
local instance : Pow C Nat := ⟨.pow⟩

@[simp] theorem sample_sub' (s : Real → Rat) (x y : C) :
    (x-y).sample s = x.sample s - y.sample s := Expr.sample_sub s x y
@[simp] theorem sample_div' (s : Real → Rat) (x y : C) :
    (x/y).sample s = x.sample s / y.sample s := rfl
@[simp] theorem sample_pow' (s : Real → Rat) (x : C) (n : Nat) :
    (x^n).sample s = x.sample s ^ n := Expr.sample_pow s x n

abbrev sampled (s : Real → Rat) (p : List C) := p.map (Expr.sample s)

def eval (p : List C) (x : C) : C := p.foldr (fun a y => a + x*y) 0

def add : List C → List C → List C
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a+b) :: add p q

def scale (a : C) (p : List C) : List C := p.map (a * ·)

def mul : List C → List C → List C
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

def power (p : List C) : Nat → List C
  | 0 => [1]
  | n+1 => mul (power p n) p

@[simp] theorem sample_eval (s : Real → Rat) (p : List C) (x : C) :
    (eval p x).sample s = Polynomial.eval (sampled s p) (x.sample s) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change a.sample s + x.sample s * (eval p x).sample s =
        a.sample s + x.sample s * Polynomial.eval (sampled s p) (x.sample s)
      rw [ih]

@[simp] theorem sample_add (s : Real → Rat) (p q : List C) :
    sampled s (add p q) = RationalExpressionNormalization.add (sampled s p) (sampled s q) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih => cases q <;> simp [add, sampled, Expr.sample, RationalExpressionNormalization.add, ih]

@[simp] theorem sample_scale (s : Real → Rat) (a : C) (p : List C) :
    sampled s (scale a p) = RationalExpressionNormalization.scale (a.sample s) (sampled s p) := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [scale, sampled, Expr.sample, RationalExpressionNormalization.scale] at ih ⊢

@[simp] theorem sample_mul (s : Real → Rat) (p q : List C) :
    sampled s (mul p q) = RationalExpressionNormalization.mul (sampled s p) (sampled s q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      rw [mul, sample_add, sample_scale]
      change _ = RationalExpressionNormalization.add _ _
      rw [show sampled s (0 :: mul p q) = 0 :: sampled s (mul p q) from rfl, ih]

@[simp] theorem sample_power (s : Real → Rat) (p : List C) (n : Nat) :
    sampled s (power p n) = RationalPartialFractions.polynomialPower (sampled s p) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [power, sample_mul, ih]; rfl

def syntheticDivide (a : C) : List C → List C × C
  | [] => ([], 0)
  | c :: p =>
      let d := syntheticDivide a p
      (d.2 :: d.1, c + a*d.2)

@[simp] theorem sample_syntheticDivide (s : Real → Rat) (a : C) (p : List C) :
    (sampled s (syntheticDivide a p).1, (syntheticDivide a p).2.sample s) =
      Polynomial.syntheticDivide (a.sample s) (sampled s p) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
      have h1 := congrArg Prod.fst ih
      have h2 := congrArg Prod.snd ih
      dsimp only at h1 h2
      change ((syntheticDivide a p).2.sample s :: sampled s (syntheticDivide a p).1,
        c.sample s + a.sample s * (syntheticDivide a p).2.sample s) = _
      rw [h1, h2]
      rfl

structure Division where
  quotient : List C
  slope : C
  constant : C

def divide (a b : C) : List C → Division
  | [] => ⟨[], 0, 0⟩
  | c :: p =>
      let d := divide a b p
      ⟨d.slope :: d.quotient, a*d.slope+d.constant, a*d.constant+c-b*d.slope⟩

def Division.sample (s : Real → Rat) (d : Division) : RationalQuadraticDivision.Division :=
  ⟨sampled s d.quotient, d.slope.sample s, d.constant.sample s⟩

@[simp] theorem sample_divide (s : Real → Rat) (a b : C) (p : List C) :
    (divide a b p).sample s = RationalQuadraticDivision.divide (a.sample s) (b.sample s) (sampled s p) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
      have h1 := congrArg RationalQuadraticDivision.Division.quotient ih
      have h2 := congrArg RationalQuadraticDivision.Division.slope ih
      have h3 := congrArg RationalQuadraticDivision.Division.constant ih
      dsimp only [Division.sample, sampled] at h1 h2 h3
      simp only [divide, Division.sample, sampled, List.map_cons, sample_sub', Expr.sample,
        RationalQuadraticDivision.divide]
      change RationalQuadraticDivision.Division.mk (_ :: _) (_ * _ + _) (_ * _ + _ - _ * _) = _
      rw [h1, h2, h3]

def norm (b : C) (d : Division) : C := d.constant*d.constant+b*d.slope*d.slope

@[simp] theorem sample_norm (s : Real → Rat) (b : C) (d : Division) :
    (norm b d).sample s = RationalQuadraticDivision.norm (b.sample s) (d.sample s) := rfl

structure Coefficients where
  slope : C
  constant : C

def coefficients (a b : C) (p q : List C) : Coefficients :=
  let u := divide a b p
  let v := divide a b q
  ⟨(u.slope*v.constant-u.constant*v.slope) / norm b v,
    (b*u.slope*v.slope+u.constant*v.constant) / norm b v⟩

def Coefficients.sample (s : Real → Rat) (d : Coefficients) : RationalQuadraticDivision.Coefficients :=
  ⟨d.slope.sample s, d.constant.sample s⟩

@[simp] theorem sample_coefficients (s : Real → Rat) (a b : C) (p q : List C) :
    (coefficients a b p q).sample s =
      RationalQuadraticDivision.coefficients (a.sample s) (b.sample s) (sampled s p) (sampled s q) := by
  have hp := sample_divide s a b p
  have hq := sample_divide s a b q
  have p1 := congrArg RationalQuadraticDivision.Division.slope hp
  have p2 := congrArg RationalQuadraticDivision.Division.constant hp
  have q1 := congrArg RationalQuadraticDivision.Division.slope hq
  have q2 := congrArg RationalQuadraticDivision.Division.constant hq
  dsimp only [Division.sample, sampled] at p1 p2 q1 q2
  simp only [coefficients, Coefficients.sample, sample_div', sample_sub', Expr.sample, sample_norm, hq]
  rw [p1, p2, q1, q2]
  rfl

def coefficientPolynomial (a : C) (d : Coefficients) : List C := [d.constant-d.slope*a, d.slope]

def nextQuadratic (a b : C) (p q : List C) : List C :=
  let u := divide a b p
  let v := divide a b q
  let d := coefficients a b p q
  add u.quotient (add (scale (-1) (mul (coefficientPolynomial a d) v.quotient)) [-d.slope*v.slope])

@[simp] theorem sample_nextQuadratic (s : Real → Rat) (a b : C) (p q : List C) :
    sampled s (nextQuadratic a b p q) =
      RationalQuadraticDivision.nextNumerator (a.sample s) (b.sample s) (sampled s p) (sampled s q) := by
  have hp := sample_divide s a b p
  have hq := sample_divide s a b q
  have hc := sample_coefficients s a b p q
  have p1 := congrArg RationalQuadraticDivision.Division.quotient hp
  have q1 := congrArg RationalQuadraticDivision.Division.quotient hq
  have q2 := congrArg RationalQuadraticDivision.Division.slope hq
  have c1 := congrArg RationalQuadraticDivision.Coefficients.slope hc
  have c2 := congrArg RationalQuadraticDivision.Coefficients.constant hc
  dsimp only [Division.sample, sampled] at p1 q1 q2
  dsimp only [Coefficients.sample] at c1 c2
  simp only [nextQuadratic, sample_add, sample_scale, sample_mul,
    coefficientPolynomial, sampled, List.map_cons, List.map_nil,
    sample_sub', Expr.sample]
  rw [p1, q1, q2, c1, c2]
  rfl

def linearCoefficient (p q : List C) (a : C) : C := eval p a / eval q a

def nextLinear (p q : List C) (a : C) : List C :=
  (syntheticDivide a (add p (scale (-(linearCoefficient p q a)) q))).1

@[simp] theorem sample_linearCoefficient (s : Real → Rat) (p q : List C) (a : C) :
    (linearCoefficient p q a).sample s = RationalPartialFractions.coefficient (sampled s p) (sampled s q) (a.sample s) := by
  simp only [linearCoefficient, sample_div', sample_eval, RationalPartialFractions.coefficient]

@[simp] theorem sample_nextLinear (s : Real → Rat) (p q : List C) (a : C) :
    sampled s (nextLinear p q a) = RationalPartialFractions.nextNumerator (sampled s p) (sampled s q) (a.sample s) := by
  have h := congrArg Prod.fst (sample_syntheticDivide s a (add p (scale (-(linearCoefficient p q a)) q)))
  simpa only [nextLinear, sample_add, sample_scale, Expr.sample, sample_linearCoefficient,
    RationalPartialFractions.nextNumerator] using h


/-- Used only to state the rational sampling theorems. Successful certificates
ensure the positive branch is taken; the fallback is never a real evaluator. -/
def positiveSample (s : Real → Rat) (b : C) : QPos :=
  if h : 0 < b.sample s then ⟨b.sample s, h⟩ else ⟨1, by decide +kernel⟩

theorem positiveSample_val (s : Real → Rat) (b : C) (h : 0 < b.sample s) :
    (positiveSample s b).val = b.sample s := by simp [positiveSample, h]

inductive Term where
  | linear (c a : C) (order : Nat)
  | quadratic (A B a b : C) (order : Nat)

def Term.shadow (s : Real → Rat) : Term → RationalPrimitiveFormula.Term
  | .linear c a n => .linear (c.sample s) (a.sample s) n
  | .quadratic A B a b n => .quadratic (A.sample s) (B.sample s) (a.sample s) (positiveSample s b) n

structure Reduction where
  terms : List Term
  remainder : List C

def Reduction.shadow (s : Real → Rat) (d : Reduction) : RationalPartialFractions.Reduction :=
  ⟨d.terms.map (Term.shadow s), sampled s d.remainder⟩

def removeLinear (p q : List C) (a : C) : Nat → Reduction
  | 0 => ⟨[], p⟩
  | n+1 =>
      let later := removeLinear (nextLinear p q a) q a n
      ⟨.linear (linearCoefficient p q a) a n :: later.terms, later.remainder⟩

def removeQuadratic (a b : C) (p q : List C) : Nat → Reduction
  | 0 => ⟨[], p⟩
  | n+1 =>
      let d := coefficients a b p q
      let later := removeQuadratic a b (nextQuadratic a b p q) q n
      ⟨.quadratic d.slope d.constant a b n :: later.terms, later.remainder⟩

@[simp] theorem shadow_removeLinear (s : Real → Rat) (p q : List C) (a : C) (n : Nat) :
    (removeLinear p q a n).shadow s =
      RationalPartialFractions.removePole (sampled s p) (sampled s q) (a.sample s) n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      have ht := congrArg RationalPartialFractions.Reduction.terms (ih (nextLinear p q a))
      have hr := congrArg RationalPartialFractions.Reduction.remainder (ih (nextLinear p q a))
      dsimp only [Reduction.shadow] at ht hr
      simp only [sample_nextLinear] at ht hr
      simp only [Reduction.shadow, removeLinear, List.map_cons, Term.shadow, sample_linearCoefficient]
      rw [ht, hr]
      rfl

@[simp] theorem shadow_removeQuadratic (s : Real → Rat) (a b : C) (p q : List C)
    (hb : 0 < b.sample s) (n : Nat) :
    (removeQuadratic a b p q n).shadow s =
      RationalQuadraticDivision.remove (a.sample s) (positiveSample s b) (sampled s p) (sampled s q) n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      have ht := congrArg RationalPartialFractions.Reduction.terms (ih (nextQuadratic a b p q))
      have hr := congrArg RationalPartialFractions.Reduction.remainder (ih (nextQuadratic a b p q))
      have hc := sample_coefficients s a b p q
      have c1 := congrArg RationalQuadraticDivision.Coefficients.slope hc
      have c2 := congrArg RationalQuadraticDivision.Coefficients.constant hc
      dsimp only [Reduction.shadow] at ht hr
      dsimp only [Coefficients.sample] at c1 c2
      simp only [sample_nextQuadratic] at ht hr
      simp only [Reduction.shadow, removeQuadratic, List.map_cons, Term.shadow]
      rw [ht, hr, c1, c2]
      simp only [RationalQuadraticDivision.remove, positiveSample_val s b hb]

inductive Factor where
  | linear (center : C) (order : Nat)
  | quadratic (center constant : C) (order : Nat)

def Factor.shadow (s : Real → Rat) : Factor → RationalFactoredPrimitives.Factor
  | .linear a n => .linear (a.sample s) n
  | .quadratic a b n => .quadratic (a.sample s) (positiveSample s b) n

def Factor.Positive (s : Real → Rat) : Factor → Prop
  | .linear _ _ => True
  | .quadratic _ b _ => 0 < b.sample s

def Factor.polynomial : Factor → List C
  | .linear a _ => [-a, 1]
  | .quadratic a b _ => [a*a+b, -(2*a), 1]

def Factor.multiplicity : Factor → Nat
  | .linear _ n | .quadratic _ _ n => n+1

def Factor.remove (f : Factor) (p q : List C) : Reduction :=
  match f with
  | .linear a n => removeLinear p q a (n+1)
  | .quadratic a b n => removeQuadratic a b p q (n+1)

@[simp] theorem Factor.shadow_remove (s : Real → Rat) (f : Factor) (p q : List C)
    (h : f.Positive s) :
    (f.remove p q).shadow s = (f.shadow s).remove (sampled s p) (sampled s q) := by
  cases f with
  | linear a n => exact shadow_removeLinear s p q a (n+1)
  | quadratic a b n => exact shadow_removeQuadratic s a b p q h (n+1)

@[simp] theorem Factor.sample_polynomial (s : Real → Rat) (f : Factor) (h : f.Positive s) :
    sampled s f.polynomial = (f.shadow s).polynomial := by
  cases f with
  | linear a n => rfl
  | quadratic a b n =>
      simp only [polynomial, shadow, RationalFactoredPrimitives.Factor.polynomial,
        sampled, List.map_cons, List.map_nil, Expr.sample, positiveSample_val s b h]
      congr 2
      grind

@[simp] theorem Factor.shadow_multiplicity (s : Real → Rat) (f : Factor) :
    (f.shadow s).multiplicity = f.multiplicity := by cases f <;> rfl

def denominator : List Factor → List C
  | [] => [1]
  | f :: fs => mul (power f.polynomial f.multiplicity) (denominator fs)

def Positive (s : Real → Rat) (fs : List Factor) : Prop := ∀ f ∈ fs, f.Positive s

@[simp] theorem sample_denominator (s : Real → Rat) (fs : List Factor) (h : Positive s fs) :
    sampled s (denominator fs) = RationalFactoredPrimitives.denominator (fs.map (Factor.shadow s)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      have hf := h f (by simp)
      have ht : Positive s fs := by intro g hg; exact h g (by simp [hg])
      rw [denominator, sample_mul, sample_power, f.sample_polynomial s hf, ih ht]
      simp only [List.map_cons, RationalFactoredPrimitives.denominator, Factor.shadow_multiplicity]

structure NormalForm where
  polynomial : List C
  terms : List Term

def NormalForm.shadow (s : Real → Rat) (d : NormalForm) : RationalPrimitiveFormula.NormalForm :=
  ⟨sampled s d.polynomial, d.terms.map (Term.shadow s)⟩

def normalForm : List Factor → List C → NormalForm
  | [], p => ⟨p, []⟩
  | f :: fs, p =>
      let block := f.remove p (denominator fs)
      let later := normalForm fs block.remainder
      ⟨later.polynomial, block.terms ++ later.terms⟩

/-- The complete expression compiler commutes with rational sampling. The
coefficients in its output still contain the original computable parameters. -/
theorem shadow_normalForm (s : Real → Rat) (fs : List Factor) (p : List C)
    (h : Positive s fs) :
    (normalForm fs p).shadow s = RationalFactoredPrimitives.normalForm (fs.map (Factor.shadow s)) (sampled s p) := by
  induction fs generalizing p with
  | nil => rfl
  | cons f fs ih =>
      have hf := h f (by simp)
      have ht : Positive s fs := by intro g hg; exact h g (by simp [hg])
      have hb := f.shadow_remove s p (denominator fs) hf
      rw [sample_denominator s fs ht] at hb
      have hb1 := congrArg RationalPartialFractions.Reduction.terms hb
      have hb2 := congrArg RationalPartialFractions.Reduction.remainder hb
      dsimp only [Reduction.shadow] at hb1 hb2
      have hl := ih (f.remove p (denominator fs)).remainder ht
      rw [hb2] at hl
      have hl1 := congrArg RationalPrimitiveFormula.NormalForm.polynomial hl
      have hl2 := congrArg RationalPrimitiveFormula.NormalForm.terms hl
      dsimp only [NormalForm.shadow] at hl1 hl2
      simp only [NormalForm.shadow, normalForm, List.map_append]
      rw [hb1, hl1, hl2]
      rfl

end ComputableFactoredAlgebra
end ComputableAnalysis
