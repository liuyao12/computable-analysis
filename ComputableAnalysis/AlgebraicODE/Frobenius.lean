import ComputableAnalysis.FormalPowerSeriesAlgebra

/-! Constructive formal Frobenius theory for
`x² y'' + x p(x) y' + q(x) y = 0`, with rational polynomial `p,q`.
The origin is at most regular singular. Exponents are rational and formal:
no value of `x^r`, convergence, or analytic branch is asserted here. -/
namespace ComputableAnalysis.AlgebraicODE.Fuchs.Frobenius
open FormalPowerSeries

structure Equation where
  p : List Rat
  q : List Rat

def Equation.indicial (E : Equation) (s : Rat) : Rat :=
  s * (s - 1) + ofPolynomial E.p 0 * s + ofPolynomial E.q 0

/-- The coefficient of the shifted formal differential expression, defined
from the Euler operators and Cauchy products, independently of the solver. -/
def Equation.residual (E : Equation) (r : Rat) (c : Coeffs) : Coeffs :=
  fun n => shiftedSecondEuler r c n +
    cauchyProduct (ofPolynomial E.p) (shiftedEuler r c) n +
    cauchyProduct (ofPolynomial E.q) c n

/-- The strictly lower-triangular contribution at degree `n`. -/
def Equation.lower (E : Equation) (r : Rat) (c : Coeffs) (n : Nat) : Rat :=
  sumBelow (fun k =>
    ((r + (k : Rat)) * ofPolynomial E.p (n - k) + ofPolynomial E.q (n - k)) * c k) n

/-- Coefficient extraction derives the Frobenius recurrence from the
formal differential operator; it is not its definition. -/
theorem Equation.residual_split (E : Equation) (r : Rat) (c : Coeffs) (n : Nat) :
    E.residual r c n = E.indicial (r + (n : Rat)) * c n + E.lower r c n := by
  unfold Equation.residual
  rw [cauchyProduct_split, cauchyProduct_split]
  have hs : E.lower r c n =
      sumBelow (fun k => ofPolynomial E.p (n - k) * shiftedEuler r c k) n +
      sumBelow (fun k => ofPolynomial E.q (n - k) * c k) n := by
    rw [← sumBelow_add]
    apply sumBelow_congr
    intro k _
    simp only [shiftedEuler]
    grind
  rw [hs]
  simp only [Equation.indicial, shiftedSecondEuler, shiftedEuler]
  grind

def Equation.IsSolution (E : Equation) (r : Rat) (c : Coeffs) : Prop :=
  ∀ n, E.residual r c n = 0

/-- Every positive recurrence denominator must be nonzero. Resonances are
not silently handled by the totalized rational division operation. -/
def Equation.Nonresonant (E : Equation) (r : Rat) : Prop :=
  ∀ n : Nat, E.indicial (r + ((n + 1 : Nat) : Rat)) ≠ 0

theorem Equation.indicial_obstruction (E : Equation) (r : Rat) (c : Coeffs)
    (hc : E.IsSolution r c) (h0 : c 0 ≠ 0) : E.indicial r = 0 := by
  have h := hc 0
  rw [E.residual_split] at h
  simp only [Equation.lower, sumBelow_zero] at h
  have hr : r + ((0 : Nat) : Rat) = r := by grind
  rw [hr] at h
  grind

theorem Equation.lower_congr (E : Equation) (r : Rat) {c d : Coeffs} {n : Nat}
    (h : ∀ k, k < n → c k = d k) : E.lower r c n = E.lower r d n := by
  apply sumBelow_congr
  intro k hk
  rw [h k hk]

/-- A terminating rational coefficient algorithm. Each call uses only
strictly smaller indices. Correctness requires nonresonance below. -/
def Equation.coeff (E : Equation) (r c0 : Rat) : Nat → Rat
  | 0 => c0
  | n + 1 =>
      -sumBelow (fun k => if _h : k < n + 1 then
        ((r + (k : Rat)) * ofPolynomial E.p (n + 1 - k) +
          ofPolynomial E.q (n + 1 - k)) * E.coeff r c0 k else 0) (n + 1) /
        E.indicial (r + ((n + 1 : Nat) : Rat))
termination_by n => n

@[simp] theorem Equation.coeff_zero (E : Equation) (r c0 : Rat) :
    E.coeff r c0 0 = c0 := by rw [Equation.coeff]

theorem Equation.coeff_succ (E : Equation) (r c0 : Rat) (n : Nat) :
    E.coeff r c0 (n + 1) =
      -E.lower r (E.coeff r c0) (n + 1) / E.indicial (r + ((n + 1 : Nat) : Rat)) := by
  rw [Equation.coeff]
  congr 2
  apply sumBelow_congr
  intro k hk
  simp only [dif_pos hk]

/-- Every supplied leading coefficient produces a formal solution when the
indicial root and nonresonance conditions hold. -/
theorem Equation.coeff_isSolution (E : Equation) (r c0 : Rat)
    (hroot : E.indicial r = 0) (hnr : E.Nonresonant r) :
    E.IsSolution r (E.coeff r c0) := by
  intro n
  rw [E.residual_split]
  cases n with
  | zero =>
      have hr : r + ((0 : Nat) : Rat) = r := by grind
      rw [hr, hroot]
      simp [Equation.lower]
      grind
  | succ n =>
      rw [E.coeff_succ]
      have hi := mul_div_cancel_left (a := E.indicial (r + ((n + 1 : Nat) : Rat)))
        (b := -E.lower r (E.coeff r c0) (n + 1)) (hnr n)
      rw [hi]
      grind

/-- Uniqueness holds coefficient by coefficient and uses no choice of a
limit or analytic function. -/
theorem Equation.solution_unique (E : Equation) (r : Rat) (hnr : E.Nonresonant r)
    {c d : Coeffs} (hc : E.IsSolution r c) (hd : E.IsSolution r d)
    (h0 : c 0 = d 0) : c = d := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      cases n with
      | zero => exact h0
      | succ n =>
          have hlow := E.lower_congr r ih
          have hcn := hc (n + 1)
          have hdn := hd (n + 1)
          rw [E.residual_split] at hcn hdn
          rw [hlow] at hcn
          have hne := hnr n
          grind

/-- Necessary and sufficient coefficient description of every solution
with the specified initial coefficient. -/
theorem Equation.solution_iff_coeff (E : Equation) (r c0 : Rat)
    (hroot : E.indicial r = 0) (hnr : E.Nonresonant r) (c : Coeffs) :
    (E.IsSolution r c ∧ c 0 = c0) ↔ c = E.coeff r c0 := by
  constructor
  · rintro ⟨hc, h0⟩
    exact E.solution_unique r hnr hc (E.coeff_isSolution r c0 hroot hnr)
      (by simpa using h0)
  · intro h
    subst c
    exact ⟨E.coeff_isSolution r c0 hroot hnr, E.coeff_zero r c0⟩

/-- At a resonant index the lower terms must vanish. A nonzero lower term
is an obstruction, regardless of the proposed next coefficient. -/
theorem Equation.resonance_compatibility (E : Equation) (r : Rat) (c : Coeffs)
    (n : Nat) (hz : E.indicial (r + (n : Rat)) = 0) :
    E.residual r c n = 0 ↔ E.lower r c n = 0 := by
  rw [E.residual_split, hz]
  grind

theorem Equation.residual_congr_below (E : Equation) (r : Rat) {c d : Coeffs}
    {n : Nat} (h : ∀ k, k ≤ n → c k = d k) :
    E.residual r c n = E.residual r d n := by
  rw [E.residual_split, E.residual_split, h n (by omega),
    E.lower_congr r (fun k hk => h k (by omega))]

/-- Each literal finite polynomial prefix has zero shifted residual at
all degrees below its cutoff. This does not say the truncated polynomial
solves the ODE at its higher degrees. -/
theorem Equation.truncation_residual (E : Equation) (r c0 : Rat)
    (hroot : E.indicial r = 0) (hnr : E.Nonresonant r) {N n : Nat} (hn : n < N) :
    E.residual r (ofPolynomial (truncation (E.coeff r c0) N)) n = 0 := by
  rw [E.residual_congr_below r (fun k hk => truncation_coeff _ (by omega))]
  exact E.coeff_isSolution r c0 hroot hnr n

end ComputableAnalysis.AlgebraicODE.Fuchs.Frobenius
