import ComputableAnalysis.RationalExpressionNormalization
import ComputableAnalysis.RationalPrimitiveFormula

/-!
# Executable partial fractions for split rational denominators

Synthetic division computes every coefficient, including repeated poles.
The input is a finite list of distinct rational pole blocks, rather than a
supplied partial-fraction identity. This does not assert that every rational
polynomial splits into rational linear factors.
-/

namespace ComputableAnalysis
namespace RationalPartialFractions

open RationalPrimitiveFormula

/-- Remove the value of the numerator at a selected pole, divided by the
nonvanishing residual denominator at that pole. -/
def coefficient (p q : List Rat) (a : Rat) : Rat :=
  Polynomial.eval p a / Polynomial.eval q a

def nextNumerator (p q : List Rat) (a : Rat) : List Rat :=
  (Polynomial.syntheticDivide a
    (RationalExpressionNormalization.add p (RationalExpressionNormalization.scale (-(coefficient p q a)) q))).1

theorem nextNumerator_identity (p q : List Rat) (a x : Rat)
    (hq : Polynomial.eval q a ≠ 0) :
    Polynomial.eval p x = coefficient p q a * Polynomial.eval q x +
      (x - a) * Polynomial.eval (nextNumerator p q a) x := by
  have hc := Rat.mul_inv_cancel (Polynomial.eval q a) hq
  have hzero : Polynomial.eval (RationalExpressionNormalization.add p (RationalExpressionNormalization.scale (-(coefficient p q a)) q)) a = 0 := by
    rw [RationalExpressionNormalization.eval_add, RationalExpressionNormalization.eval_scale]
    unfold coefficient
    rw [Rat.div_def]
    grind
  have H := Polynomial.syntheticDivide_factor_of_root (x := x) hzero
  rw [RationalExpressionNormalization.eval_add, RationalExpressionNormalization.eval_scale] at H
  change _ = (x - a) * Polynomial.eval (nextNumerator p q a) x at H
  grind

structure Reduction where
  terms : List Term
  remainder : List Rat

/-- Remove a whole pole block by finite repeated synthetic division. -/
def removePole (p q : List Rat) (a : Rat) : Nat → Reduction
  | 0 => ⟨[], p⟩
  | n + 1 =>
      let later := removePole (nextNumerator p q a) q a n
      ⟨Term.linear (coefficient p q a) a n :: later.terms, later.remainder⟩

/-- Every coefficient in a repeated block is computed, with no supplied
partial-fraction identity. -/
theorem removePole_identity (p q : List Rat) (a x : Rat)
    (hqa : Polynomial.eval q a ≠ 0) (hqx : Polynomial.eval q x ≠ 0)
    (hxa : x ≠ a) (n : Nat) :
    Polynomial.eval p x / ((x - a) ^ n * Polynomial.eval q x) =
      sumTerms x (removePole p q a n).terms +
        Polynomial.eval (removePole p q a n).remainder x / Polynomial.eval q x := by
  induction n generalizing p with
  | zero =>
      simp only [removePole, sumTerms, Rat.pow_zero, Rat.one_mul, Rat.zero_add]
  | succ n ih =>
      have hnext := nextNumerator_identity p q a x hqa
      have htail := ih (nextNumerator p q a)
      have hxc := Rat.mul_inv_cancel (x - a) (by grind)
      have hqc := Rat.mul_inv_cancel (Polynomial.eval q x) hqx
      simp only [removePole, sumTerms, Term.eval]
      rw [Rat.add_assoc, ← htail]
      simp only [Rat.pow_succ, Rat.div_def, Rat.inv_mul_rev]
      grind

theorem removePole_regular (p q : List Rat) (a x : Rat) (hxa : x ≠ a) (n : Nat) :
    ∀ t ∈ (removePole p q a n).terms, t.RegularAt x := by
  induction n generalizing p with
  | zero => simp [removePole]
  | succ n ih =>
      intro t ht
      change t ∈ Term.linear (coefficient p q a) a n ::
        (removePole (nextNumerator p q a) q a n).terms at ht
      rcases List.mem_cons.mp ht with h | h
      · subst t
        exact hxa
      · exact ih (nextNumerator p q a) t h

def polynomialPower (p : List Rat) : Nat → List Rat
  | 0 => [1]
  | n + 1 => RationalExpressionNormalization.mul (polynomialPower p n) p

theorem polynomialPower_eval (p : List Rat) (x : Rat) (n : Nat) :
    Polynomial.eval (polynomialPower p n) x = (Polynomial.eval p x) ^ n := by
  induction n with
  | zero => simp [polynomialPower, Polynomial.eval, Rat.add_zero]
  | succ n ih => rw [polynomialPower, RationalExpressionNormalization.eval_mul, ih, Rat.pow_succ]

/-- Pole order is `order + 1`, so every listed block has positive degree. -/
structure Pole where
  center : Rat
  order : Nat

def denominator : List Pole → List Rat
  | [] => [1]
  | a :: rest => RationalExpressionNormalization.mul (polynomialPower [-a.center, 1] (a.order + 1)) (denominator rest)

theorem denominator_cons_eval (a : Pole) (rest : List Pole) (x : Rat) :
    Polynomial.eval (denominator (a :: rest)) x =
      (x - a.center) ^ (a.order + 1) * Polynomial.eval (denominator rest) x := by
  rw [denominator, RationalExpressionNormalization.eval_mul, polynomialPower_eval]
  have hlinear : Polynomial.eval [-a.center, 1] x = x - a.center := by
    simp only [Polynomial.eval, List.foldr, Rat.mul_zero, Rat.add_zero, Rat.mul_one]
    grind
  rw [hlinear]

/-- The residual denominator must not contain another copy of a pole block.
This condition is decidable by finite rational evaluation. -/
def Admissible : List Pole → Prop
  | [] => True
  | a :: rest => Polynomial.eval (denominator rest) a.center ≠ 0 ∧ Admissible rest

instance decidableAdmissible : (poles : List Pole) → Decidable (Admissible poles)
  | [] => isTrue True.intro
  | a :: rest => by
      haveI := decidableAdmissible rest
      change Decidable (Polynomial.eval (denominator rest) a.center ≠ 0 ∧ Admissible rest)
      infer_instance

/-- Partial fractions are computed for arbitrary numerators and every
admissible list of rational pole blocks. -/
def normalForm : List Pole → List Rat → NormalForm
  | [], p => ⟨p, []⟩
  | a :: rest, p =>
      let block := removePole p (denominator rest) a.center (a.order + 1)
      let later := normalForm rest block.remainder
      ⟨later.polynomial, block.terms ++ later.terms⟩

private theorem sumTerms_append (x : Rat) (as bs : List Term) :
    sumTerms x (as ++ bs) = sumTerms x as + sumTerms x bs := by
  induction as with
  | nil => simp only [List.nil_append, sumTerms, Rat.zero_add]
  | cons a as ih => simp only [List.cons_append, sumTerms, ih, Rat.add_assoc]

private theorem denominator_nonzero_tail (a : Pole) (rest : List Pole) (x : Rat)
    (hx : Polynomial.eval (denominator (a :: rest)) x ≠ 0) :
    x ≠ a.center ∧ Polynomial.eval (denominator rest) x ≠ 0 := by
  rw [denominator_cons_eval] at hx
  constructor
  · intro h
    rw [h, Rat.sub_self, Rat.pow_succ, Rat.mul_zero, Rat.zero_mul] at hx
    exact hx rfl
  · intro h
    rw [h, Rat.mul_zero] at hx
    exact hx rfl

theorem normalForm_identity (poles : List Pole) (p : List Rat)
    (hpoles : Admissible poles) (x : Rat)
    (hx : Polynomial.eval (denominator poles) x ≠ 0) :
    (normalForm poles p).eval x = Polynomial.eval p x / Polynomial.eval (denominator poles) x := by
  induction poles generalizing p with
  | nil =>
      simp only [normalForm, NormalForm.eval, sumTerms, Rat.add_zero, denominator,
        Polynomial.eval, List.foldr, Rat.mul_zero, Rat.add_zero, Rat.div_def]
      have h1 : (1 : Rat)⁻¹ = 1 := by decide +kernel
      rw [h1, Rat.mul_one]
  | cons a rest ih =>
      have hxrest := denominator_nonzero_tail a rest x hx
      let block := removePole p (denominator rest) a.center (a.order + 1)
      have H := removePole_identity p (denominator rest) a.center x
        hpoles.1 hxrest.2 hxrest.1 (a.order + 1)
      have htail := ih block.remainder hpoles.2 hxrest.2
      change Polynomial.eval (normalForm rest block.remainder).polynomial x +
        sumTerms x (block.terms ++ (normalForm rest block.remainder).terms) = _
      rw [sumTerms_append, denominator_cons_eval]
      change Polynomial.eval (normalForm rest block.remainder).polynomial x +
        sumTerms x (normalForm rest block.remainder).terms = _ at htail
      change _ = sumTerms x block.terms + Polynomial.eval block.remainder x /
        Polynomial.eval (denominator rest) x at H
      grind

theorem normalForm_regular (poles : List Pole) (p : List Rat) (x : Rat)
    (hx : Polynomial.eval (denominator poles) x ≠ 0) :
    ∀ t ∈ (normalForm poles p).terms, t.RegularAt x := by
  induction poles generalizing p with
  | nil => simp [normalForm]
  | cons a rest ih =>
      have hxrest := denominator_nonzero_tail a rest x hx
      intro t ht
      change t ∈ (removePole p (denominator rest) a.center (a.order + 1)).terms ++
        (normalForm rest (removePole p (denominator rest) a.center (a.order + 1)).remainder).terms at ht
      rcases List.mem_append.mp ht with hb | hr
      · exact removePole_regular p (denominator rest) a.center x hxrest.1 (a.order + 1) t hb
      · exact ih _ hxrest.2 t hr

/-- A fully constructed decomposition for split rational denominators. The
input is factor data and its noncollision check, not a partial-fraction witness. -/
def decomposition (poles : List Pole) (p : List Rat) (hpoles : Admissible poles) :
    Decomposition (⟨p, denominator poles⟩ : RatFun) where
  normalForm := normalForm poles p
  regular := by
    intro x hx
    have hxn : Polynomial.eval (denominator poles) x ≠ 0 := by
      change (Polynomial.eval (denominator poles) x != 0) = true at hx
      simpa using hx
    exact normalForm_regular poles p x hxn
  identity := by
    intro x hx
    have hxn : Polynomial.eval (denominator poles) x ≠ 0 := by
      change (Polynomial.eval (denominator poles) x != 0) = true at hx
      simpa using hx
    exact normalForm_identity poles p hpoles x hxn


/-- Transfer a computed split decomposition to any rational function whose
denominator is given by the corresponding factorization, including a nonunit
leading coefficient. No partial-fraction identity is supplied. -/
def ofFactorization (f : RatFun) (poles : List Pole) (leading : Rat)
    (_hleading : leading ≠ 0) (hpoles : Admissible poles)
    (hfactor : ∀ x, f.denominator x = leading * Polynomial.eval (denominator poles) x) :
    Decomposition f where
  normalForm := normalForm poles (RationalExpressionNormalization.scale leading⁻¹ f.num)
  regular := by
    intro x hx
    have hx0 : f.denominator x ≠ 0 := by
      change (f.denominator x != 0) = true at hx
      simpa using hx
    have hq : Polynomial.eval (denominator poles) x ≠ 0 := by
      intro hz
      rw [hfactor, hz, Rat.mul_zero] at hx0
      exact hx0 rfl
    exact normalForm_regular poles _ x hq
  identity := by
    intro x hx
    have hx0 : f.denominator x ≠ 0 := by
      change (f.denominator x != 0) = true at hx
      simpa using hx
    have hq : Polynomial.eval (denominator poles) x ≠ 0 := by
      intro hz
      rw [hfactor, hz, Rat.mul_zero] at hx0
      exact hx0 rfl
    rw [normalForm_identity poles _ hpoles x hq, RationalExpressionNormalization.eval_scale]
    change leading⁻¹ * Polynomial.eval f.num x / Polynomial.eval (denominator poles) x =
      f.numerator x / f.denominator x
    rw [hfactor]
    simp only [RatFun.numerator, Rat.div_def, Rat.inv_mul_rev]
    grind

end RationalPartialFractions
end ComputableAnalysis
