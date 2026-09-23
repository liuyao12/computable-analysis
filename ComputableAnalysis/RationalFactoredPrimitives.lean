import ComputableAnalysis.RationalQuadraticDivision

/-!
# Elementary integration from a checked linear/quadratic factorization

Factorization is input data, not a new axiom or a partial-fraction assumption.
The partial fractions and formal elementary primitive are computed. Factors
currently have rational coefficients; a general real algebraic factorization
needs the represented algebraic-coefficient extension.
-/

namespace ComputableAnalysis
namespace RationalFactoredPrimitives

open RationalPrimitiveFormula

/-- Multiplicity is `order+1`; quadratic factors are irreducible because their
centered constant is positive. Equal factors should be grouped into one block. -/
inductive Factor where
  | linear (center : Rat) (order : Nat)
  | quadratic (center : Rat) (constant : QPos) (order : Nat)

def Factor.polynomial : Factor → List Rat
  | .linear a _ => [-a, 1]
  | .quadratic a b _ => [a*a+b.val, -2*a, 1]

def Factor.value (x : Rat) : Factor → Rat
  | .linear a _ => x-a
  | .quadratic a b _ => RationalPrimitiveFormula.quadratic a b.val x

def Factor.multiplicity : Factor → Nat
  | .linear _ n | .quadratic _ _ n => n+1

theorem Factor.polynomial_eval (f : Factor) (x : Rat) :
    Polynomial.eval f.polynomial x = f.value x := by
  cases f <;> simp only [polynomial, value, Polynomial.eval, List.foldr,
    Rat.mul_zero, Rat.add_zero, Rat.mul_one, RationalPrimitiveFormula.quadratic] <;> grind

/-- Completing the square converts any rational quadratic with negative
 discriminant into the positive centered form accepted by the factor list. -/
def quadraticConstant (A B C : Rat) (hA : A ≠ 0) (hdisc : B*B < 4*A*C) : QPos :=
  ⟨(4*A*C-B*B)/(4*A*A), by
    have hs : 0 < A*A := by
      by_cases ha : 0 < A
      · exact Rat.mul_pos ha ha
      · have hn : 0 < -A := by grind
        have hh := Rat.mul_pos hn hn
        grind
    have hd : 0 < 4*A*A := by
      have hh := Rat.mul_pos (show (0 : Rat) < 4 by decide) hs
      grind
    rw [Rat.div_def]
    exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 hd)⟩

def generalQuadratic (A B C : Rat) (hA : A ≠ 0) (hdisc : B*B < 4*A*C)
    (order : Nat) : Factor :=
  .quadratic (-B/(2*A)) (quadraticConstant A B C hA hdisc) order

theorem generalQuadratic_value (A B C : Rat) (hA : A ≠ 0)
    (hdisc : B*B < 4*A*C) (order : Nat) (x : Rat) :
    A*(generalQuadratic A B C hA hdisc order).value x = A*x*x+B*x+C := by
  have ha := Rat.mul_inv_cancel A hA
  change A*((x-(-B/(2*A)))*(x-(-B/(2*A)))+(4*A*C-B*B)/(4*A*A)) = _
  simp only [Rat.div_def, Rat.inv_mul_rev]
  have h2 : (2 : Rat)⁻¹ = 1/2 := by decide +kernel
  have h4 : (4 : Rat)⁻¹ = 1/4 := by decide +kernel
  rw [h2, h4]
  grind

/-- A decidable noncollision check on the residual denominator. For a
quadratic, it is nonvanishing in the rational quadratic quotient field. -/
def Factor.Compatible (f : Factor) (q : List Rat) : Prop :=
  match f with
  | .linear a _ => Polynomial.eval q a ≠ 0
  | .quadratic a b _ => (RationalQuadraticDivision.divide a b.val q).slope ≠ 0 ∨
      (RationalQuadraticDivision.divide a b.val q).constant ≠ 0

instance (f : Factor) (q : List Rat) : Decidable (f.Compatible q) := by
  cases f <;> unfold Factor.Compatible <;> infer_instance

def Factor.remove (f : Factor) (p q : List Rat) : RationalPartialFractions.Reduction :=
  match f with
  | .linear a n => RationalPartialFractions.removePole p q a (n+1)
  | .quadratic a b n => RationalQuadraticDivision.remove a b p q (n+1)

theorem Factor.remove_identity (f : Factor) (p q : List Rat) (hq : f.Compatible q)
    (x : Rat) (hfx : f.value x ≠ 0) (hqx : Polynomial.eval q x ≠ 0) :
    Polynomial.eval p x / (f.value x ^ f.multiplicity * Polynomial.eval q x) =
      sumTerms x (f.remove p q).terms + Polynomial.eval (f.remove p q).remainder x / Polynomial.eval q x := by
  cases f with
  | linear a n =>
      exact RationalPartialFractions.removePole_identity p q a x hq hqx (by
        change x-a ≠ 0 at hfx
        grind) (n+1)
  | quadratic a b n => exact RationalQuadraticDivision.remove_identity a b p q hq x hqx (n+1)

theorem Factor.remove_regular (f : Factor) (p q : List Rat) (x : Rat)
    (hfx : f.value x ≠ 0) : ∀ t ∈ (f.remove p q).terms, t.RegularAt x := by
  cases f with
  | linear a n =>
      exact RationalPartialFractions.removePole_regular p q a x (by
        change x-a ≠ 0 at hfx
        grind) (n+1)
  | quadratic a b n => exact RationalQuadraticDivision.remove_regular a b p q x (n+1)

def denominator : List Factor → List Rat
  | [] => [1]
  | f :: fs => RationalExpressionNormalization.mul
      (RationalPartialFractions.polynomialPower f.polynomial f.multiplicity) (denominator fs)

theorem denominator_cons_eval (f : Factor) (fs : List Factor) (x : Rat) :
    Polynomial.eval (denominator (f::fs)) x =
      f.value x ^ f.multiplicity * Polynomial.eval (denominator fs) x := by
  rw [denominator, RationalExpressionNormalization.eval_mul,
    RationalPartialFractions.polynomialPower_eval, Factor.polynomial_eval]

def Admissible : List Factor → Prop
  | [] => True
  | f :: fs => f.Compatible (denominator fs) ∧ Admissible fs

instance decidableAdmissible : (fs : List Factor) → Decidable (Admissible fs)
  | [] => isTrue trivial
  | f :: fs => by
      haveI := decidableAdmissible fs
      change Decidable (f.Compatible (denominator fs) ∧ Admissible fs)
      infer_instance

def normalForm : List Factor → List Rat → NormalForm
  | [], p => ⟨p, []⟩
  | f :: fs, p =>
      let block := f.remove p (denominator fs)
      let later := normalForm fs block.remainder
      ⟨later.polynomial, block.terms ++ later.terms⟩

private theorem sumTerms_append (x : Rat) (ts us : List Term) :
    sumTerms x (ts++us) = sumTerms x ts + sumTerms x us := by
  induction ts with
  | nil => simp only [List.nil_append, sumTerms, Rat.zero_add]
  | cons t ts ih => simp only [List.cons_append, sumTerms, ih, Rat.add_assoc]

private theorem denominator_nonzero_tail (f : Factor) (fs : List Factor) (x : Rat)
    (hx : Polynomial.eval (denominator (f::fs)) x ≠ 0) :
    f.value x ≠ 0 ∧ Polynomial.eval (denominator fs) x ≠ 0 := by
  rw [denominator_cons_eval] at hx
  constructor
  · intro he
    have hn : f.multiplicity ≠ 0 := by cases f <;> simp [Factor.multiplicity]
    cases hn' : f.multiplicity with
    | zero => exact hn hn'
    | succ n => rw [hn', Rat.pow_succ, he, Rat.mul_zero, Rat.zero_mul] at hx; exact hx rfl
  · intro he
    rw [he, Rat.mul_zero] at hx
    exact hx rfl

theorem normalForm_identity (fs : List Factor) (p : List Rat) (hf : Admissible fs)
    (x : Rat) (hx : Polynomial.eval (denominator fs) x ≠ 0) :
    (normalForm fs p).eval x = Polynomial.eval p x / Polynomial.eval (denominator fs) x := by
  induction fs generalizing p with
  | nil =>
      simp only [normalForm, NormalForm.eval, sumTerms, Rat.add_zero, denominator,
        Polynomial.eval, List.foldr, Rat.mul_zero, Rat.add_zero, Rat.div_def,
        show (1 : Rat)⁻¹ = 1 by decide +kernel, Rat.mul_one]
  | cons f fs ih =>
      have hxrest := denominator_nonzero_tail f fs x hx
      let block := f.remove p (denominator fs)
      have hb := f.remove_identity p (denominator fs) hf.1 x hxrest.1 hxrest.2
      have ht := ih block.remainder hf.2 hxrest.2
      change Polynomial.eval (normalForm fs block.remainder).polynomial x +
        sumTerms x (block.terms ++ (normalForm fs block.remainder).terms) = _
      rw [sumTerms_append, denominator_cons_eval]
      change Polynomial.eval (normalForm fs block.remainder).polynomial x +
        sumTerms x (normalForm fs block.remainder).terms = _ at ht
      change _ = sumTerms x block.terms + Polynomial.eval block.remainder x / Polynomial.eval (denominator fs) x at hb
      grind

theorem normalForm_regular (fs : List Factor) (p : List Rat) (x : Rat)
    (hx : Polynomial.eval (denominator fs) x ≠ 0) :
    ∀ t ∈ (normalForm fs p).terms, t.RegularAt x := by
  induction fs generalizing p with
  | nil => simp [normalForm]
  | cons f fs ih =>
      have hxrest := denominator_nonzero_tail f fs x hx
      intro t ht
      change t ∈ (f.remove p (denominator fs)).terms ++
        (normalForm fs (f.remove p (denominator fs)).remainder).terms at ht
      rcases List.mem_append.mp ht with hb | hr
      · exact f.remove_regular p (denominator fs) x hxrest.1 t hb
      · exact ih _ hxrest.2 t hr

/-- Partial fractions are derived from the factor list. Neither a primitive
nor a partial-fraction identity is an input. -/
def decomposition (fs : List Factor) (p : List Rat) (hf : Admissible fs) :
    Decomposition (⟨p, denominator fs⟩ : RatFun) where
  normalForm := normalForm fs p
  regular := by
    intro x hx
    have hn : Polynomial.eval (denominator fs) x ≠ 0 := by
      change (Polynomial.eval (denominator fs) x != 0) = true at hx
      simpa using hx
    exact normalForm_regular fs p x hn
  identity := by
    intro x hx
    have hn : Polynomial.eval (denominator fs) x ≠ 0 := by
      change (Polynomial.eval (denominator fs) x != 0) = true at hx
      simpa using hx
    exact normalForm_identity fs p hf x hn

/-- The factorization interface: exact rational data plus its checked identity.
FTA can eventually provide this interface over represented algebraic coefficients;
no FTA axiom is introduced by accepting factorization as an explicit input. -/
structure Factorization (f : RatFun) where
  factors : List Factor
  leading : Rat
  leading_ne_zero : leading ≠ 0
  admissible : Admissible factors
  identity : ∀ x, f.denominator x = leading * Polynomial.eval (denominator factors) x

def Factorization.decomposition {f : RatFun} (F : Factorization f) : Decomposition f where
  normalForm := normalForm F.factors (RationalExpressionNormalization.scale F.leading⁻¹ f.num)
  regular := by
    intro x hx
    have hx0 : f.denominator x ≠ 0 := by change (f.denominator x != 0) = true at hx; simpa using hx
    have hq : Polynomial.eval (denominator F.factors) x ≠ 0 := by
      intro hz
      rw [F.identity, hz, Rat.mul_zero] at hx0
      exact hx0 rfl
    exact normalForm_regular F.factors _ x hq
  identity := by
    intro x hx
    have hx0 : f.denominator x ≠ 0 := by change (f.denominator x != 0) = true at hx; simpa using hx
    have hq : Polynomial.eval (denominator F.factors) x ≠ 0 := by
      intro hz
      rw [F.identity, hz, Rat.mul_zero] at hx0
      exact hx0 rfl
    rw [normalForm_identity F.factors _ F.admissible x hq, RationalExpressionNormalization.eval_scale]
    change F.leading⁻¹ * Polynomial.eval f.num x / Polynomial.eval (denominator F.factors) x =
      f.numerator x / f.denominator x
    rw [F.identity]
    simp only [RatFun.numerator, Rat.div_def, Rat.inv_mul_rev]
    grind

/-- From a checked factorization, compute a logarithm/arctangent/rational
formula and prove its formal derivative. Analytic realization of the quadratic
atoms is a separate obligation, not an assumed field of the factorization. -/
theorem Factorization.primitive_correct {f : RatFun} (F : Factorization f)
    (x : Rat) (hx : f.DefinedAt x) :
    F.decomposition.normalForm.primitive.formalDerivative x = f.evalOnDomain x hx :=
  F.decomposition.primitive_correct x hx

end RationalFactoredPrimitives
end ComputableAnalysis
