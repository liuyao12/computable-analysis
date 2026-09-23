import ComputableAnalysis.RationalPartialFractions

/-!
# Exact division and partial fractions at an irreducible quadratic

All computations use rational coefficients. The positive parameter is the
constant term in the centered quadratic, not a supplied square root.
-/

namespace ComputableAnalysis
namespace RationalQuadraticDivision

open RationalPrimitiveFormula

/-- The remainder is `slope * (x-center) + constant`. -/
structure Division where
  quotient : List Rat
  slope : Rat
  constant : Rat

def divide (a b : Rat) : List Rat → Division
  | [] => ⟨[], 0, 0⟩
  | c :: p =>
      let d := divide a b p
      ⟨d.slope :: d.quotient, a * d.slope + d.constant,
        a * d.constant + c - b * d.slope⟩

theorem divide_identity (a b : Rat) (p : List Rat) (x : Rat) :
    Polynomial.eval p x = quadratic a b x * Polynomial.eval (divide a b p).quotient x +
      (divide a b p).slope * (x-a) + (divide a b p).constant := by
  induction p with
  | nil => simp [divide, Polynomial.eval, Rat.add_zero]
  | cons c p ih =>
      change c + x * Polynomial.eval p x =
        quadratic a b x * ((divide a b p).slope + x * Polynomial.eval (divide a b p).quotient x) +
        (a * (divide a b p).slope + (divide a b p).constant) * (x-a) +
        (a * (divide a b p).constant + c - b * (divide a b p).slope)
      rw [ih]
      unfold quadratic
      grind

/-- The norm of the residual denominator in the quadratic quotient field. -/
def norm (b : Rat) (d : Division) : Rat := d.constant*d.constant + b*d.slope*d.slope

theorem norm_pos (b : QPos) (d : Division) (hd : d.slope ≠ 0 ∨ d.constant ≠ 0) :
    0 < norm b.val d := by
  have sq_nonneg : ∀ x : Rat, 0 <= x*x := by
    intro x
    by_cases hx : 0 <= x
    · exact Rat.mul_nonneg hx hx
    · have hn : 0 <= -x := by grind
      have := Rat.mul_nonneg hn hn
      grind
  have sq_pos : ∀ x : Rat, x ≠ 0 → 0 < x*x := by
    intro x hx
    have hn := sq_nonneg x
    have hne : x*x ≠ 0 := by intro hz; exact (Rat.mul_eq_zero.mp hz).elim hx hx
    grind
  have hs := sq_nonneg d.slope
  have ht := sq_nonneg d.constant
  have hb := b.property
  have hmul := Rat.mul_nonneg (Rat.le_of_lt hb) hs
  unfold norm
  rcases hd with hd | hd
  · have hp := Rat.mul_pos hb (sq_pos d.slope hd)
    grind
  · have hp := sq_pos d.constant hd
    grind

structure Coefficients where
  slope : Rat
  constant : Rat

def coefficients (a b : Rat) (p q : List Rat) : Coefficients :=
  let u := divide a b p
  let v := divide a b q
  ⟨(u.slope*v.constant-u.constant*v.slope) / norm b v,
    (b*u.slope*v.slope+u.constant*v.constant) / norm b v⟩

def coefficientPolynomial (a : Rat) (d : Coefficients) : List Rat :=
  [d.constant-d.slope*a, d.slope]

theorem coefficientPolynomial_eval (a x : Rat) (d : Coefficients) :
    Polynomial.eval (coefficientPolynomial a d) x = d.slope*(x-a)+d.constant := by
  simp only [coefficientPolynomial, Polynomial.eval, List.foldr, Rat.mul_zero, Rat.add_zero]
  grind

/-- Compute the next numerator without polynomial division by a variable
leading coefficient: only division by a positive rational norm is needed. -/
def nextNumerator (a b : Rat) (p q : List Rat) : List Rat :=
  let u := divide a b p
  let v := divide a b q
  let d := coefficients a b p q
  RationalExpressionNormalization.add u.quotient
    (RationalExpressionNormalization.add
      (RationalExpressionNormalization.scale (-1)
        (RationalExpressionNormalization.mul (coefficientPolynomial a d) v.quotient))
      [-d.slope*v.slope])

/-- A local partial-fraction step, with its coefficient computed by inversion
in the rational quadratic quotient field. -/
theorem nextNumerator_identity (a : Rat) (b : QPos) (p q : List Rat)
    (hq : (divide a b.val q).slope ≠ 0 ∨ (divide a b.val q).constant ≠ 0) (x : Rat) :
    Polynomial.eval p x =
      ((coefficients a b.val p q).slope*(x-a)+(coefficients a b.val p q).constant) *
        Polynomial.eval q x + quadratic a b.val x * Polynomial.eval (nextNumerator a b.val p q) x := by
  let u := divide a b.val p
  let v := divide a b.val q
  let d := coefficients a b.val p q
  have hn : norm b.val v ≠ 0 := Rat.ne_of_gt (norm_pos b v hq)
  have hc := Rat.mul_inv_cancel (norm b.val v) hn
  have hs : d.slope*v.constant+d.constant*v.slope = u.slope := by
    dsimp [d, coefficients]
    simp only [Rat.div_def]
    change (u.slope*v.constant-u.constant*v.slope)*(norm b.val v)⁻¹*v.constant +
      (b.val*u.slope*v.slope+u.constant*v.constant)*(norm b.val v)⁻¹*v.slope = _
    unfold norm at hc ⊢
    grind
  have ht : d.constant*v.constant-b.val*d.slope*v.slope = u.constant := by
    dsimp [d, coefficients]
    simp only [Rat.div_def]
    change (b.val*u.slope*v.slope+u.constant*v.constant)*(norm b.val v)⁻¹*v.constant -
      b.val*((u.slope*v.constant-u.constant*v.slope)*(norm b.val v)⁻¹)*v.slope = _
    unfold norm at hc ⊢
    grind
  have hp := divide_identity a b.val p x
  have hq' := divide_identity a b.val q x
  change Polynomial.eval p x = quadratic a b.val x * Polynomial.eval u.quotient x + u.slope*(x-a)+u.constant at hp
  change Polynomial.eval q x = quadratic a b.val x * Polynomial.eval v.quotient x + v.slope*(x-a)+v.constant at hq'
  change Polynomial.eval p x = (d.slope*(x-a)+d.constant)*Polynomial.eval q x + _
  rw [nextNumerator, RationalExpressionNormalization.eval_add,
    RationalExpressionNormalization.eval_add, RationalExpressionNormalization.eval_scale,
    RationalExpressionNormalization.eval_mul, coefficientPolynomial_eval]
  simp only [Polynomial.eval, List.foldr_cons, List.foldr_nil, Rat.mul_zero, Rat.add_zero]
  change Polynomial.eval p x = (d.slope*(x-a)+d.constant)*Polynomial.eval q x +
    quadratic a b.val x * (Polynomial.eval u.quotient x +
      ((-1)*((d.slope*(x-a)+d.constant)*Polynomial.eval v.quotient x) + -d.slope*v.slope))
  rw [hp, hq']
  unfold quadratic
  grind

/-- Remove a whole repeated quadratic block. -/
def remove (a : Rat) (b : QPos) (p q : List Rat) : Nat → RationalPartialFractions.Reduction
  | 0 => ⟨[], p⟩
  | n+1 =>
      let d := coefficients a b.val p q
      let later := remove a b (nextNumerator a b.val p q) q n
      ⟨.quadratic d.slope d.constant a b n :: later.terms, later.remainder⟩

theorem remove_identity (a : Rat) (b : QPos) (p q : List Rat)
    (hq : (divide a b.val q).slope ≠ 0 ∨ (divide a b.val q).constant ≠ 0)
    (x : Rat) (hqx : Polynomial.eval q x ≠ 0) (n : Nat) :
    Polynomial.eval p x / (quadratic a b.val x ^ n * Polynomial.eval q x) =
      sumTerms x (remove a b p q n).terms +
        Polynomial.eval (remove a b p q n).remainder x / Polynomial.eval q x := by
  induction n generalizing p with
  | zero => simp only [remove, sumTerms, Rat.pow_zero, Rat.one_mul, Rat.zero_add]
  | succ n ih =>
      have hn := nextNumerator_identity a b p q hq x
      have ht := ih (nextNumerator a b.val p q)
      have hc := Rat.mul_inv_cancel (quadratic a b.val x) (Rat.ne_of_gt (quadratic_pos a x b))
      have hqc := Rat.mul_inv_cancel (Polynomial.eval q x) hqx
      simp only [remove, sumTerms, Term.eval]
      rw [Rat.add_assoc, ← ht]
      simp only [Rat.pow_succ, Rat.div_def, Rat.inv_mul_rev]
      grind

theorem remove_regular (a : Rat) (b : QPos) (p q : List Rat) (x : Rat) (n : Nat) :
    ∀ t ∈ (remove a b p q n).terms, t.RegularAt x := by
  induction n generalizing p with
  | zero => simp [remove]
  | succ n ih =>
      intro t ht
      change t ∈ Term.quadratic _ _ a b n :: (remove a b (nextNumerator a b.val p q) q n).terms at ht
      rcases List.mem_cons.mp ht with he | hm
      · subst t; trivial
      · exact ih _ t hm

end RationalQuadraticDivision
end ComputableAnalysis
