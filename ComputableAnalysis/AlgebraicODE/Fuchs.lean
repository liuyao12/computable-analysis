import ComputableAnalysis.Polynomial

/-! The rank-one Euler--Fuchs equation `x y' = r y`.
The coefficient theorem is a classification of finite polynomial solutions,
not the general Fuchs regular-singular or algebraic-solution theorem. -/
namespace ComputableAnalysis.AlgebraicODE.Fuchs

def weighted (r : Rat) (p : List Rat) (start : Nat := 0) : List Rat :=
  (p.zipIdx start).map (fun (c, k) => ((k : Rat) - r) * c)

theorem eval_weighted (r x : Rat) (p : List Rat) (start : Nat) :
    Polynomial.eval (weighted r p start) x =
      Polynomial.eval (weighted 0 p start) x - r * Polynomial.eval p x := by
  induction p generalizing start with
  | nil => simp [weighted, Polynomial.eval]; grind
  | cons c cs ih =>
      simp only [weighted, List.zipIdx, List.map_cons, Polynomial.eval,
        List.foldr_cons] at *
      rw [ih]
      grind [Rat.mul_add, Rat.add_mul]

theorem eval_weighted_zero (p : List Rat) (x : Rat) :
    Polynomial.eval (weighted 0 p) x =
      x * Polynomial.eval (Polynomial.derivative p) x := by
  cases p with
  | nil => simp [weighted, Polynomial.eval, Polynomial.derivative]
  | cons c cs =>
      have hm (cs : List Rat) (k : Nat) :
          (cs.zipIdx (k + 1)).map (fun (c, i) => ((i : Rat) - 0) * c) =
          (cs.zipIdx k).map (fun (c, i) => ((i + 1 : Nat) : Rat) * c) := by
        induction cs generalizing k with
        | nil => rfl
        | cons a as ih =>
            simp only [List.zipIdx, List.map_cons]
            congr 1
            · grind
            · exact ih (k + 1)
      simp only [weighted, Polynomial.eval, Polynomial.derivative,
        List.zipIdx, List.map_cons, List.foldr_cons]
      rw [hm cs 0]
      grind

/-- Every coefficient of the Euler residual vanishes. -/
def PolynomialSolution (r : Rat) (p : List Rat) : Prop :=
  ∀ k : Nat, ((k : Rat) - r) * p[k]?.getD 0 = 0

private theorem eval_weighted_vanishes (r x : Rat) (p : List Rat) (start : Nat)
    (h : ∀ k : Nat, (((start + k : Nat) : Rat) - r) * p[k]?.getD 0 = 0) :
    Polynomial.eval (weighted r p start) x = 0 := by
  induction p generalizing start with
  | nil => rfl
  | cons c cs ih =>
      have h0 := h 0
      simp only [Nat.add_zero, List.getElem?_cons_zero, Option.getD_some] at h0
      have ht : ∀ k : Nat,
          (((start + 1 + k : Nat) : Rat) - r) * cs[k]?.getD 0 = 0 := by
        intro k
        have hk := h (k + 1)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
      simp only [weighted, List.zipIdx, List.map_cons, Polynomial.eval,
        List.foldr_cons]
      change ((start : Rat) - r) * c + x *
        Polynomial.eval (weighted r cs (start + 1)) x = 0
      rw [h0, ih (start + 1) ht]
      grind

/-- The coefficient certificate really implies the differential polynomial
identity, using the existing executable formal derivative. -/
theorem polynomial_equation (r : Rat) (p : List Rat)
    (h : PolynomialSolution r p) (x : Rat) :
    x * Polynomial.eval (Polynomial.derivative p) x = r * Polynomial.eval p x := by
  have hz := eval_weighted_vanishes r x p 0 (by simpa [PolynomialSolution] using h)
  rw [eval_weighted, eval_weighted_zero] at hz
  grind

theorem polynomial_classification (r : Rat) (p : List Rat) :
    PolynomialSolution r p ↔
      ∀ k : Nat, p[k]?.getD 0 ≠ 0 → (k : Rat) = r := by
  constructor
  · intro h k hk
    have he := h k
    grind
  · intro h k
    by_cases hk : p[k]?.getD 0 = 0
    · simp [hk]
    · rw [h k hk]
      grind

/-- A nonzero polynomial solution forces a nonnegative integral exponent. -/
theorem exponent_of_nonzero_polynomial (r : Rat) (p : List Rat)
    (h : PolynomialSolution r p) (hne : ∃ k : Nat, p[k]?.getD 0 ≠ 0) :
    ∃ k : Nat, r = (k : Rat) := by
  obtain ⟨k, hk⟩ := hne
  exact ⟨k, ((polynomial_classification r p).mp h k hk).symm⟩

theorem nonintegral_polynomial_zero (r : Rat) (p : List Rat)
    (hr : ∀ k : Nat, (k : Rat) ≠ r) (h : PolynomialSolution r p) :
    ∀ k : Nat, p[k]?.getD 0 = 0 := by
  intro k
  by_cases hk : p[k]?.getD 0 = 0
  · exact hk
  · exact False.elim (hr k ((polynomial_classification r p).mp h k hk))

/-- Implicit differentiation of `y^n = x^m` at a nonzero branch gives
the Euler equation once the differentiated relation is certified.
This algebraic elimination does not choose or differentiate a branch. -/
theorem radical_euler (m n : Nat) (x y dy : Rat)
    (hy : y ≠ 0) (hn : n ≠ 0)
    (curve : y ^ n = x ^ m)
    (tangent : (n : Rat) * y ^ (n - 1) * (x * dy) =
      (m : Rat) * x ^ m) :
    (n : Rat) * x * dy = (m : Rat) * y := by
  have hpall (k : Nat) : y ^ k ≠ 0 := by
    induction k with
    | zero => simp [Rat.pow_zero]
    | succ k ih => rw [Rat.pow_succ]; grind
  have hp := hpall (n - 1)
  have hn' : n = (n - 1) + 1 := by omega
  have hpow : y ^ n = y ^ (n - 1) * y := by
    calc
      y ^ n = y ^ ((n - 1) + 1) := congrArg (fun k => y ^ k) hn'
      _ = y ^ (n - 1) * y := Rat.pow_succ y (n - 1)
  rw [← curve, hpow] at tangent
  grind [Rat.mul_assoc, Rat.mul_comm]

end ComputableAnalysis.AlgebraicODE.Fuchs
