import ComputableAnalysis.PowerSeries
import ComputableAnalysis.Polynomial

/-! Finite coefficient algebra for rational formal series. All sums are
finite; this module makes no convergence or analytic derivative claim. -/
namespace ComputableAnalysis.FormalPowerSeries

/-- Sum the first `n` rational values using the foundation's list sum. -/
def sumBelow (f : Nat → Rat) (n : Nat) : Rat :=
  ratListSum ((List.range n).map f)

@[simp] theorem sumBelow_zero (f : Nat → Rat) : sumBelow f 0 = 0 := rfl

theorem sumBelow_succ (f : Nat → Rat) (n : Nat) :
    sumBelow f (n + 1) = sumBelow f n + f n := by
  simp [sumBelow, List.range_succ, List.map_append, ratListSum_append, ratListSum]
  grind

theorem sumBelow_congr {f g : Nat → Rat} {n : Nat}
    (h : ∀ k, k < n → f k = g k) : sumBelow f n = sumBelow g n := by
  unfold sumBelow
  congr 1
  apply List.map_congr_left
  intro k hk
  exact h k (List.mem_range.mp hk)

theorem sumBelow_add (f g : Nat → Rat) (n : Nat) :
    sumBelow (fun k => f k + g k) n = sumBelow f n + sumBelow g n := by
  induction n with
  | zero => simp; grind
  | succ n ih => simp only [sumBelow_succ, ih]; grind

theorem sumBelow_mul (a : Rat) (f : Nat → Rat) (n : Nat) :
    sumBelow (fun k => a * f k) n = a * sumBelow f n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [sumBelow_succ, ih]; grind

/-- The coefficient of a Cauchy product, with a finite convolution. -/
def cauchyProduct (a b : Coeffs) : Coeffs :=
  fun n => sumBelow (fun k => a (n - k) * b k) (n + 1)

theorem cauchyProduct_split (a b : Coeffs) (n : Nat) :
    cauchyProduct a b n =
      sumBelow (fun k => a (n - k) * b k) n + a 0 * b n := by
  simp [cauchyProduct, sumBelow_succ]

theorem cauchyProduct_congr_below {a b c : Coeffs} {n : Nat}
    (h : ∀ k, k ≤ n → b k = c k) :
    cauchyProduct a b n = cauchyProduct a c n := by
  apply sumBelow_congr
  intro k hk
  rw [h k (by omega)]

/-- Multiplication by the formal variable. -/
def mulX (c : Coeffs) : Coeffs
  | 0 => 0
  | n + 1 => c n

/-- The Euler operator after a formal exponent shift `y = x^r c`. -/
def shiftedEuler (r : Rat) (c : Coeffs) : Coeffs :=
  fun n => (r + (n : Rat)) * c n

theorem shiftedEuler_zero_eq_mulX_shift (c : Coeffs) :
    shiftedEuler 0 c = mulX (coefficientShift c) := by
  funext n
  cases n <;> simp [shiftedEuler, mulX, coefficientShift] <;> grind

/-- The shifted coefficient for `x² y''`, without choosing `x^r`. -/
def shiftedSecondEuler (r : Rat) (c : Coeffs) : Coeffs :=
  fun n => (r + (n : Rat)) * (r + (n : Rat) - 1) * c n

theorem shiftedSecondEuler_eq (r : Rat) (c : Coeffs) (n : Nat) :
    shiftedSecondEuler r c n =
      shiftedEuler r (shiftedEuler r c) n - shiftedEuler r c n := by
  simp only [shiftedSecondEuler, shiftedEuler]
  grind

theorem shiftedSecondEuler_zero_eq_mulX_shift (c : Coeffs) :
    shiftedSecondEuler 0 c = mulX (mulX (coefficientShift (coefficientShift c))) := by
  funext n
  cases n with
  | zero => simp [shiftedSecondEuler, mulX]; grind
  | succ n =>
      cases n with
      | zero => simp [shiftedSecondEuler, mulX]; grind
      | succ n =>
          simp only [shiftedSecondEuler, mulX, coefficientShift]
          simp only [Rat.natCast_add]
          change ((0 : Rat) + ((n : Rat) + 1 + 1)) *
            (0 + ((n : Rat) + 1 + 1) - 1) * c (n + 1 + 1) =
            ((n : Rat) + 1) * (((n : Rat) + 1 + 1) * c (n + 1 + 1))
          grind

/-- Finite polynomial data embedded as a coefficient stream. -/
def ofPolynomial (p : List Rat) : Coeffs := fun n => p[n]?.getD 0

/-- Executable polynomial truncation, retaining precisely degrees below `N`. -/
def truncation (c : Coeffs) (N : Nat) : List Rat := (List.range N).map c

theorem truncation_coeff (c : Coeffs) {N n : Nat} (hn : n < N) :
    ofPolynomial (truncation c N) n = c n := by
  simp [ofPolynomial, truncation, hn]

theorem truncation_coeff_zero (c : Coeffs) {N n : Nat} (hn : N ≤ n) :
    ofPolynomial (truncation c N) n = 0 := by
  unfold ofPolynomial
  rw [List.getElem?_eq_none (by simpa [truncation] using hn)]
  rfl

end ComputableAnalysis.FormalPowerSeries
