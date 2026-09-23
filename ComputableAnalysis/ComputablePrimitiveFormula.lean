import ComputableAnalysis.ComputableFactoredAlgebra

/-!
# Elementary formulas with computable-real coefficients

This is the formula and coefficient-evaluation layer. `formalDerivative` is
an arithmetic expression, not an analytic differentiation certificate.
-/
namespace ComputableAnalysis
namespace ComputableFactoredAlgebra
open ComputableCoefficient
local instance : OfNat C n := ⟨.rational n⟩
local instance : Add C := ⟨.add⟩
local instance : Mul C := ⟨.mul⟩
local instance : Neg C := ⟨.neg⟩
local instance : Sub C := ⟨.sub⟩
local instance : Div C := ⟨.div⟩
local instance : Pow C Nat := ⟨.pow⟩

abbrev natCoefficient (n : Nat) : C := .rational (n : Rat)

def polynomialPrimitive (p : List C) : List C :=
  0 :: p.zipIdx.map (fun (c,i) => c / natCoefficient (i+1))

def polynomialDerivative : List C → List C
  | [] => []
  | _ :: p => p.zipIdx.map (fun (c,i) => natCoefficient (i+1) * c)

private theorem sample_zip (s : Real → Rat) (p : List C) (i : Nat)
    (f : C → Nat → C) (g : Rat → Nat → Rat)
    (h : ∀ c i, (f c i).sample s = g (c.sample s) i) :
    sampled s (p.zipIdx i |>.map (fun (c,j) => f c j)) =
      ((sampled s p).zipIdx i).map (fun (c,j) => g c j) := by
  induction p generalizing i with
  | nil => rfl
  | cons c p ih =>
      simp only [List.zipIdx, List.map_cons, sampled, h]
      exact congrArg (List.cons _) (ih (i+1))

@[simp] theorem sample_polynomialPrimitive (s : Real → Rat) (p : List C) :
    sampled s (polynomialPrimitive p) = RationalPrimitiveFormula.polynomialPrimitive (sampled s p) := by
  change 0 :: _ = 0 :: _
  exact congrArg (List.cons 0) (sample_zip s p 0 (fun c i => c / natCoefficient (i+1)) (fun c i => c / ((i+1 : Nat) : Rat)) (by intro c i; rfl))

@[simp] theorem sample_polynomialDerivative (s : Real → Rat) (p : List C) :
    sampled s (polynomialDerivative p) = Polynomial.derivative (sampled s p) := by
  cases p with
  | nil => rfl
  | cons c p => exact sample_zip s p 0 (fun c i => natCoefficient (i+1) * c) (fun c i => ((i+1 : Nat) : Rat) * c) (by intro c i; rfl)

def quadratic (a b x : C) : C := (x-a)*(x-a)+b

inductive Formula where
  | polynomial (p : List C)
  | logLinear (a : C)
  | linearPower (a : C) (n : Nat)
  | logQuadratic (a b : C)
  | atanQuadratic (a b : C)
  | quadraticPower (a b : C) (n : Nat)
  | quadraticRatio (a b : C) (n : Nat)
  | add (f g : Formula)
  | scale (c : C) (f : Formula)

def Formula.shadow (s : Real → Rat) : Formula → RationalPrimitiveFormula.Formula
  | .polynomial p => .polynomial (sampled s p)
  | .logLinear a => .logLinear (a.sample s)
  | .linearPower a n => .linearPower (a.sample s) n
  | .logQuadratic a b => .logQuadratic (a.sample s) (positiveSample s b)
  | .atanQuadratic a b => .atanQuadratic (a.sample s) (positiveSample s b)
  | .quadraticPower a b n => .quadraticPower (a.sample s) (positiveSample s b) n
  | .quadraticRatio a b n => .quadraticRatio (a.sample s) (positiveSample s b) n
  | .add f g => .add (f.shadow s) (g.shadow s)
  | .scale c f => .scale (c.sample s) (f.shadow s)

def Formula.Positive (s : Real → Rat) : Formula → Prop
  | .polynomial _ | .logLinear _ | .linearPower _ _ => True
  | .logQuadratic _ b | .atanQuadratic _ b | .quadraticPower _ b _ | .quadraticRatio _ b _ => 0 < b.sample s
  | .add f g => f.Positive s ∧ g.Positive s
  | .scale _ f => f.Positive s

def Formula.formalDerivative (x : C) : Formula → C
  | .polynomial p => eval (polynomialDerivative p) x
  | .logLinear a => 1 / (x-a)
  | .linearPower a n => -(natCoefficient (n+1)) / (x-a)^(n+2)
  | .logQuadratic a b => 2*(x-a) / quadratic a b x
  | .atanQuadratic a b => 1 / quadratic a b x
  | .quadraticPower a b n => -(2*natCoefficient (n+1)*(x-a)) / (quadratic a b x)^(n+2)
  | .quadraticRatio a b n => (b-(2*natCoefficient (n+1)-1)*(x-a)*(x-a)) / (quadratic a b x)^(n+2)
  | .add f g => f.formalDerivative x + g.formalDerivative x
  | .scale c f => c * f.formalDerivative x

@[simp] theorem sample_quadratic (s : Real → Rat) (a b x : C) :
    (quadratic a b x).sample s = RationalPrimitiveFormula.quadratic (a.sample s) (b.sample s) (x.sample s) := by
  simp only [quadratic, Expr.sample, sample_sub', RationalPrimitiveFormula.quadratic]

theorem Formula.sample_formalDerivative (s : Real → Rat) (f : Formula) (x : C)
    (hp : f.Positive s) :
    (f.formalDerivative x).sample s = (f.shadow s).formalDerivative (x.sample s) := by
  induction f with
  | polynomial p => simp [formalDerivative, shadow, RationalPrimitiveFormula.Formula.formalDerivative]
  | logLinear a => simp [formalDerivative, shadow, sample_div', sample_sub', Expr.sample, RationalPrimitiveFormula.Formula.formalDerivative]
  | linearPower a n => simp [formalDerivative, shadow, sample_div', sample_pow', sample_sub', Expr.sample, RationalPrimitiveFormula.Formula.formalDerivative]
  | logQuadratic a b | atanQuadratic a b | quadraticPower a b n | quadraticRatio a b n =>
      simp only [formalDerivative, shadow, sample_div', sample_pow', sample_sub', Expr.sample,
        sample_quadratic, RationalPrimitiveFormula.Formula.formalDerivative, positiveSample_val s b hp] <;> rfl
  | add f g ihf ihg =>
      change (f.formalDerivative x).sample s + (g.formalDerivative x).sample s = _
      rw [ihf hp.1, ihg hp.2]
      rfl
  | scale c f ih => exact congrArg (fun r => c.sample s * r) (ih hp)

def quadraticPrimitive (a b : C) : Nat → Formula
  | 0 => .atanQuadratic a b
  | n+1 => .add (.scale (1/(2*natCoefficient (n+1)*b)) (.quadraticRatio a b n))
      (.scale ((2*natCoefficient (n+1)-1)/(2*natCoefficient (n+1)*b)) (quadraticPrimitive a b n))

theorem shadow_quadraticPrimitive (s : Real → Rat) (a b : C) (n : Nat) (hb : 0 < b.sample s) :
    (quadraticPrimitive a b n).shadow s =
      RationalPrimitiveFormula.quadraticPrimitive (a.sample s) (positiveSample s b) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [quadraticPrimitive, Formula.shadow, sample_div', sample_sub', Expr.sample, ih,
        RationalPrimitiveFormula.quadraticPrimitive, positiveSample_val s b hb] <;> rfl

theorem quadraticPrimitive_positive (s : Real → Rat) (a b : C) (n : Nat) (hb : 0 < b.sample s) :
    (quadraticPrimitive a b n).Positive s := by
  induction n with
  | zero => exact hb
  | succ n ih => exact ⟨hb, ih⟩

def Term.Positive (s : Real → Rat) : Term → Prop
  | .linear _ _ _ => True
  | .quadratic _ _ _ b _ => 0 < b.sample s

def Term.primitive : Term → Formula
  | .linear c a 0 => .scale c (.logLinear a)
  | .linear c a (n+1) => .scale (-c / natCoefficient (n+1)) (.linearPower a n)
  | .quadratic A B a b 0 => .add (.scale (A/2) (.logQuadratic a b)) (.scale B (quadraticPrimitive a b 0))
  | .quadratic A B a b (n+1) => .add (.scale (-A/(2*natCoefficient (n+1))) (.quadraticPower a b n))
      (.scale B (quadraticPrimitive a b (n+1)))

theorem Term.shadow_primitive (s : Real → Rat) (t : Term) (h : t.Positive s) :
    t.primitive.shadow s = (t.shadow s).primitive := by
  cases t with
  | linear c a n => cases n <;> rfl
  | quadratic A B a b n =>
      cases n <;> simp only [primitive, shadow, Formula.shadow, sample_div', Expr.sample,
        shadow_quadraticPrimitive s a b _ h, RationalPrimitiveFormula.Term.primitive] <;> rfl

theorem Term.primitive_positive (s : Real → Rat) (t : Term) (h : t.Positive s) :
    t.primitive.Positive s := by
  cases t with
  | linear c a n => cases n <;> trivial
  | quadratic A B a b n => cases n <;> exact ⟨h, quadraticPrimitive_positive s a b _ h⟩

def primitiveTerms : List Term → Formula
  | [] => .polynomial []
  | t :: ts => .add t.primitive (primitiveTerms ts)

def NormalForm.primitive (d : NormalForm) : Formula :=
  .add (.polynomial (polynomialPrimitive d.polynomial)) (primitiveTerms d.terms)

theorem shadow_primitiveTerms (s : Real → Rat) (ts : List Term) (h : ∀ t ∈ ts, t.Positive s) :
    (primitiveTerms ts).shadow s = RationalPrimitiveFormula.primitiveTerms (ts.map (Term.shadow s)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      change RationalPrimitiveFormula.Formula.add _ _ = RationalPrimitiveFormula.Formula.add _ _
      rw [t.shadow_primitive s (h t (by simp)), ih (by intro u hu; exact h u (by simp [hu]))]

theorem primitiveTerms_positive (s : Real → Rat) (ts : List Term) (h : ∀ t ∈ ts, t.Positive s) :
    (primitiveTerms ts).Positive s := by
  induction ts with
  | nil => trivial
  | cons t ts ih => exact ⟨t.primitive_positive s (h t (by simp)), ih (by intro u hu; exact h u (by simp [hu]))⟩

theorem NormalForm.shadow_primitive (s : Real → Rat) (d : NormalForm) (h : ∀ t ∈ d.terms, t.Positive s) :
    d.primitive.shadow s = (d.shadow s).primitive := by
  simp only [primitive, Formula.shadow, sample_polynomialPrimitive, shadow_primitiveTerms s d.terms h]
  rfl

theorem NormalForm.primitive_positive (s : Real → Rat) (d : NormalForm) (h : ∀ t ∈ d.terms, t.Positive s) :
    d.primitive.Positive s := ⟨True.intro, primitiveTerms_positive s d.terms h⟩

end ComputableFactoredAlgebra
end ComputableAnalysis
