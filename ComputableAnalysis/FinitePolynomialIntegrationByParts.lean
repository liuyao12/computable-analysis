import ComputableAnalysis.FiniteFTCPolynomial
import ComputableAnalysis.Polynomial

/-!
# A finite polynomial integration-by-parts certificate

This file records the finite, rational version of integration by parts for
the explicit polynomials `x^2` and `x^3` on `[0,1]`. The sums use only the
successive polynomial increments on a finite rational grid. Thus the proof
is a telescoping product-rule calculation: it does not invoke a completed
integral, a limit, or a completeness theorem.
-/

namespace ComputableAnalysis

namespace FinitePolynomialIntegrationByParts

/-- The sum of the first `n` terms of a rational sequence. -/
def finiteRatSum (term : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => finiteRatSum term n + term n

theorem finiteRatSum_succ (term : Nat → Rat) (n : Nat) :
    finiteRatSum term (n + 1) = finiteRatSum term n + term n := by
  rfl

theorem finiteRatSum_add (left right : Nat → Rat) (n : Nat) :
    finiteRatSum (fun k => left k + right k) n =
      finiteRatSum left n + finiteRatSum right n := by
  induction n with
  | zero =>
      simp [finiteRatSum]
      grind
  | succ n ih =>
      rw [finiteRatSum_succ, finiteRatSum_succ, finiteRatSum_succ, ih]
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem finiteRatSum_telescope (value : Nat → Rat) (n : Nat) :
    finiteRatSum (fun k => value (k + 1) - value k) n =
      value n - value 0 := by
  induction n with
  | zero =>
      simp [finiteRatSum]
      grind
  | succ n ih =>
      rw [finiteRatSum_succ, ih]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-! ## The finite product-rule telescope -/

/-- First orientation of the finite product rule. The first sum uses the
left endpoint for `g`, and the second uses the right endpoint for `f`. -/
theorem finiteRatSum_ibp_left_right
    (f g : Rat → Rat) (x : Nat → Rat) (n : Nat) :
    finiteRatSum
        (fun k => (f (x (k + 1)) - f (x k)) * g (x k)) n +
      finiteRatSum
        (fun k => f (x (k + 1)) * (g (x (k + 1)) - g (x k))) n =
      f (x n) * g (x n) - f (x 0) * g (x 0) := by
  induction n with
  | zero =>
      simp [finiteRatSum]
      grind
  | succ n ih =>
      calc
        finiteRatSum
              (fun k => (f (x (k + 1)) - f (x k)) * g (x k)) (n + 1) +
            finiteRatSum
              (fun k => f (x (k + 1)) *
                (g (x (k + 1)) - g (x k))) (n + 1) =
            finiteRatSum
              (fun k => (f (x (k + 1)) - f (x k)) * g (x k)) n +
            finiteRatSum
              (fun k => f (x (k + 1)) *
                (g (x (k + 1)) - g (x k))) n +
              (f (x (n + 1)) - f (x n)) * g (x n) +
              f (x (n + 1)) * (g (x (n + 1)) - g (x n)) := by
                rw [finiteRatSum_succ, finiteRatSum_succ]
                grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
        _ = (f (x n) * g (x n) - f (x 0) * g (x 0)) +
              (f (x (n + 1)) - f (x n)) * g (x n) +
              f (x (n + 1)) * (g (x (n + 1)) - g (x n)) := by
                rw [ih]
        _ = f (x (n + 1)) * g (x (n + 1)) -
              f (x 0) * g (x 0) := by
                grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                  Rat.mul_assoc, Rat.add_assoc, Rat.add_comm,
                  Rat.add_left_comm]

/-- Second orientation of the finite product rule. The first sum uses the
left endpoint for `f`, and the second uses the right endpoint for `g`. -/
theorem finiteRatSum_ibp_right_left
    (f g : Rat → Rat) (x : Nat → Rat) (n : Nat) :
    finiteRatSum
        (fun k => f (x k) * (g (x (k + 1)) - g (x k))) n +
      finiteRatSum
        (fun k => (f (x (k + 1)) - f (x k)) * g (x (k + 1))) n =
      f (x n) * g (x n) - f (x 0) * g (x 0) := by
  induction n with
  | zero =>
      simp [finiteRatSum]
      grind
  | succ n ih =>
      calc
        finiteRatSum
              (fun k => f (x k) * (g (x (k + 1)) - g (x k))) (n + 1) +
            finiteRatSum
              (fun k => (f (x (k + 1)) - f (x k)) * g (x (k + 1))) (n + 1) =
            finiteRatSum
              (fun k => f (x k) * (g (x (k + 1)) - g (x k))) n +
            finiteRatSum
              (fun k => (f (x (k + 1)) - f (x k)) * g (x (k + 1))) n +
              f (x n) * (g (x (n + 1)) - g (x n)) +
              (f (x (n + 1)) - f (x n)) * g (x (n + 1)) := by
                rw [finiteRatSum_succ, finiteRatSum_succ]
                grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
        _ = (f (x n) * g (x n) - f (x 0) * g (x 0)) +
              f (x n) * (g (x (n + 1)) - g (x n)) +
              (f (x (n + 1)) - f (x n)) * g (x (n + 1)) := by
                rw [ih]
        _ = f (x (n + 1)) * g (x (n + 1)) -
              f (x 0) * g (x 0) := by
                grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                  Rat.mul_assoc, Rat.add_assoc, Rat.add_comm,
                  Rat.add_left_comm]

/-! ## Explicit rational polynomials and their unit grid -/

def unitGridPoint (n k : Nat) : Rat :=
  if n = 0 then 0 else (k : Rat) / (n : Rat)

def quadraticCoefficients : List Rat := [0, 0, 1]

def cubicCoefficients : List Rat := [0, 0, 0, 1]

def quadratic (x : Rat) : Rat :=
  Polynomial.eval quadraticCoefficients x

def cubic (x : Rat) : Rat :=
  Polynomial.eval cubicCoefficients x

theorem quadratic_eq (x : Rat) : quadratic x = x ^ 2 := by
  simp [quadratic, quadraticCoefficients, Polynomial.eval]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem cubic_eq (x : Rat) : cubic x = x ^ 3 := by
  simp [cubic, cubicCoefficients, Polynomial.eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem quadratic_derivative_eq (x : Rat) :
    Polynomial.eval (Polynomial.derivative quadraticCoefficients) x = 2 * x := by
  have h := Polynomial.eval_derivative_quadratic 0 0 1 x
  simp [quadraticCoefficients] at h ⊢
  grind

theorem cubic_derivative_eq (x : Rat) :
    Polynomial.eval (Polynomial.derivative cubicCoefficients) x = 3 * x ^ 2 := by
  have h := Polynomial.eval_derivative_cubic 0 0 0 1 x
  simp [cubicCoefficients] at h ⊢
  grind

theorem unitGridPoint_zero (n : Nat) : unitGridPoint n 0 = 0 := by
  unfold unitGridPoint
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, Rat.div_def]

theorem unitGridPoint_self {n : Nat} (hn : 0 < n) :
    unitGridPoint n n = 1 := by
  unfold unitGridPoint
  simp only [if_neg (Nat.ne_of_gt hn)]
  rw [Rat.div_def]
  have hnr : (n : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  grind [Rat.mul_inv_cancel]

/-! ## The two finite integration-by-parts sums -/

/-- The left-`g`, right-`f` finite integration-by-parts sum for `x^2` and
`x^3`. -/
def quadraticCubicLeftRightSum (n : Nat) : Rat :=
  finiteRatSum
    (fun k =>
      (quadratic (unitGridPoint n (k + 1)) - quadratic (unitGridPoint n k)) *
          cubic (unitGridPoint n k) +
        quadratic (unitGridPoint n (k + 1)) *
          (cubic (unitGridPoint n (k + 1)) - cubic (unitGridPoint n k))) n

/-- The left-`f`, right-`g` finite integration-by-parts sum for `x^2` and
`x^3`. -/
def quadraticCubicRightLeftSum (n : Nat) : Rat :=
  finiteRatSum
    (fun k =>
      quadratic (unitGridPoint n k) *
          (cubic (unitGridPoint n (k + 1)) - cubic (unitGridPoint n k)) +
        (quadratic (unitGridPoint n (k + 1)) - quadratic (unitGridPoint n k)) *
          cubic (unitGridPoint n (k + 1))) n

theorem quadraticCubicLeftRightSum_eq_endpoint_difference (n : Nat) :
    quadraticCubicLeftRightSum n =
      quadratic (unitGridPoint n n) * cubic (unitGridPoint n n) -
        quadratic (unitGridPoint n 0) * cubic (unitGridPoint n 0) := by
  unfold quadraticCubicLeftRightSum
  calc
    finiteRatSum
        (fun k =>
          (quadratic (unitGridPoint n (k + 1)) -
              quadratic (unitGridPoint n k)) * cubic (unitGridPoint n k) +
            quadratic (unitGridPoint n (k + 1)) *
              (cubic (unitGridPoint n (k + 1)) - cubic (unitGridPoint n k))) n =
      finiteRatSum
          (fun k => (quadratic (unitGridPoint n (k + 1)) -
            quadratic (unitGridPoint n k)) * cubic (unitGridPoint n k)) n +
        finiteRatSum
          (fun k => quadratic (unitGridPoint n (k + 1)) *
            (cubic (unitGridPoint n (k + 1)) - cubic (unitGridPoint n k))) n :=
      finiteRatSum_add _ _ _
    _ = quadratic (unitGridPoint n n) * cubic (unitGridPoint n n) -
        quadratic (unitGridPoint n 0) * cubic (unitGridPoint n 0) :=
      finiteRatSum_ibp_left_right quadratic cubic (unitGridPoint n) n

theorem quadraticCubicRightLeftSum_eq_endpoint_difference (n : Nat) :
    quadraticCubicRightLeftSum n =
      quadratic (unitGridPoint n n) * cubic (unitGridPoint n n) -
        quadratic (unitGridPoint n 0) * cubic (unitGridPoint n 0) := by
  unfold quadraticCubicRightLeftSum
  calc
    finiteRatSum
        (fun k =>
          quadratic (unitGridPoint n k) *
              (cubic (unitGridPoint n (k + 1)) - cubic (unitGridPoint n k)) +
            (quadratic (unitGridPoint n (k + 1)) -
              quadratic (unitGridPoint n k)) * cubic (unitGridPoint n (k + 1))) n =
      finiteRatSum
          (fun k => quadratic (unitGridPoint n k) *
            (cubic (unitGridPoint n (k + 1)) - cubic (unitGridPoint n k))) n +
        finiteRatSum
          (fun k => (quadratic (unitGridPoint n (k + 1)) -
            quadratic (unitGridPoint n k)) * cubic (unitGridPoint n (k + 1))) n :=
      finiteRatSum_add _ _ _
    _ = quadratic (unitGridPoint n n) * cubic (unitGridPoint n n) -
        quadratic (unitGridPoint n 0) * cubic (unitGridPoint n 0) :=
      finiteRatSum_ibp_right_left quadratic cubic (unitGridPoint n) n

theorem quadraticCubicLeftRightSum_eq_one {n : Nat} (hn : 0 < n) :
    quadraticCubicLeftRightSum n = 1 := by
  rw [quadraticCubicLeftRightSum_eq_endpoint_difference n]
  rw [unitGridPoint_self hn, unitGridPoint_zero]
  rw [quadratic_eq, cubic_eq, quadratic_eq, cubic_eq]
  native_decide

theorem quadraticCubicRightLeftSum_eq_one {n : Nat} (hn : 0 < n) :
    quadraticCubicRightLeftSum n = 1 := by
  rw [quadraticCubicRightLeftSum_eq_endpoint_difference n]
  rw [unitGridPoint_self hn, unitGridPoint_zero]
  rw [quadratic_eq, cubic_eq, quadratic_eq, cubic_eq]
  native_decide

end FinitePolynomialIntegrationByParts

end ComputableAnalysis
