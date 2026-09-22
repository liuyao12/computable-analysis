import ComputableAnalysis.AlgebraicODE.Frobenius
import ComputableAnalysis.FormalPowerSeriesPolynomial
import ComputableAnalysis.AlgebraicODE.PolynomialRelation

/-! An all-degree family of terminating Frobenius series for
`x y'' + (b-x)y' + m y = 0`, with natural `m` and rational `b > 0`.
The normalization is `y(0)=c0`. No classical real-number library is used. -/
namespace ComputableAnalysis.AlgebraicODE.Fuchs.Laguerre
open FormalPowerSeries Frobenius

def equation (m : Nat) (b : Rat) : Frobenius.Equation := ⟨[b, -1], [0, (m : Rat)]⟩

theorem indicial (m : Nat) (b s : Rat) :
    (equation m b).indicial s = s * (s + b - 1) := by
  simp [equation, Frobenius.Equation.indicial, ofPolynomial]
  grind

theorem root (m : Nat) (b : Rat) : (equation m b).indicial 0 = 0 := by
  rw [indicial]
  grind

theorem nonresonant (m : Nat) {b : Rat} (hb : 0 < b) :
    (equation m b).Nonresonant 0 := by
  intro n
  rw [indicial]
  have hn : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
  have hn1 := (Rat.natCast_pos (a := n + 1)).mpr (by omega)
  simp only [Rat.natCast_add] at *
  apply Rat.ne_of_gt
  apply Rat.mul_pos
  · grind
  · grind

private theorem sumBelow_vanishes (f : Nat → Rat) (n : Nat)
    (h : ∀ k, k < n → f k = 0) : sumBelow f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumBelow_succ, ih (fun k hk => h k (by omega)), h n (by omega)]
      grind

theorem lower_succ (m n : Nat) (b r : Rat) (c : Coeffs) :
    (equation m b).lower r c (n + 1) = ((m : Rat) - (r + (n : Rat))) * c n := by
  unfold Frobenius.Equation.lower
  rw [sumBelow_succ]
  have hz : sumBelow (fun k =>
      ((r + (k : Rat)) * ofPolynomial (equation m b).p (n + 1 - k) +
        ofPolynomial (equation m b).q (n + 1 - k)) * c k) n = 0 := by
    apply sumBelow_vanishes
    intro k hk
    have hd : 2 ≤ n + 1 - k := by omega
    have hp : ofPolynomial (equation m b).p (n + 1 - k) = 0 := by
      unfold ofPolynomial
      rw [List.getElem?_eq_none (by simpa [equation] using hd)]
      rfl
    have hq : ofPolynomial (equation m b).q (n + 1 - k) = 0 := by
      unfold ofPolynomial
      rw [List.getElem?_eq_none (by simpa [equation] using hd)]
      rfl
    rw [hp, hq]
    grind
  rw [hz]
  have hs : n + 1 - n = 1 := by omega
  rw [hs]
  simp [equation, ofPolynomial]
  grind

/-- The executable rational coefficients, constructed by the general solver. -/
def coeff (m : Nat) (b c0 : Rat) : Coeffs := (equation m b).coeff 0 c0

theorem coeff_recurrence (m n : Nat) (b c0 : Rat) :
    coeff m b c0 (n + 1) =
      (((n : Rat) - (m : Rat)) * coeff m b c0 n) /
        (((n + 1 : Nat) : Rat) * ((n : Rat) + b)) := by
  unfold coeff
  rw [Frobenius.Equation.coeff_succ, lower_succ, indicial]
  have hd : ((0 : Rat) + ((n + 1 : Nat) : Rat)) *
      (0 + ((n + 1 : Nat) : Rat) + b - 1) =
      ((n + 1 : Nat) : Rat) * ((n : Rat) + b) := by
    simp only [Rat.natCast_add]
    grind
  rw [hd]
  congr 1
  grind

/-- Termination is proved for every degree, not checked at finitely many examples. -/
theorem coeff_vanishes (m : Nat) (b c0 : Rat) {n : Nat} (hn : m < n) :
    coeff m b c0 n = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      cases n with
      | zero => omega
      | succ n =>
          rw [coeff_recurrence]
          by_cases heq : n = m
          · subst n
            have hz : ((m : Rat) - (m : Rat)) * coeff m b c0 m = 0 := by grind
            rw [hz]
            simp [Rat.div_def]
          · rw [ih n (by omega) (by omega)]
            simp [Rat.div_def]

/-- The actual finite coefficient list of the polynomial solution. -/
def polynomial (m : Nat) (b c0 : Rat) : List Rat := truncation (coeff m b c0) (m + 1)

theorem polynomial_coeff (m : Nat) (b c0 : Rat) :
    ofPolynomial (polynomial m b c0) = coeff m b c0 := by
  funext n
  by_cases hn : n < m + 1
  · exact truncation_coeff _ hn
  · rw [coeff_vanishes m b c0 (by omega)]
    exact truncation_coeff_zero _ (by omega)

theorem polynomial_isSolution (m : Nat) {b : Rat} (hb : 0 < b) (c0 : Rat) :
    (equation m b).IsSolution 0 (ofPolynomial (polynomial m b c0)) := by
  rw [polynomial_coeff]
  exact (equation m b).coeff_isSolution 0 c0 (root m b) (nonresonant m hb)

theorem coeff_nonzero (m : Nat) {b c0 : Rat} (hb : 0 < b) (hc0 : c0 ≠ 0)
    {n : Nat} (hn : n ≤ m) : coeff m b c0 n ≠ 0 := by
  induction n with
  | zero => simpa [coeff] using hc0
  | succ n ih =>
      have hp := ih (by omega)
      have hsol := (equation m b).coeff_isSolution 0 c0 (root m b) (nonresonant m hb) (n + 1)
      rw [Frobenius.Equation.residual_split, lower_succ] at hsol
      change (equation m b).indicial (0 + ((n + 1 : Nat) : Rat)) * coeff m b c0 (n + 1) +
        ((m : Rat) - (0 + (n : Rat))) * coeff m b c0 n = 0 at hsol
      have hlt : (n : Rat) < (m : Rat) := Rat.natCast_lt_natCast.mpr (by omega)
      intro hz
      rw [hz] at hsol
      grind

/-- Exact degree `m` is expressed without a normalized-polynomial quotient:
coefficient `m` is nonzero and every higher coefficient is zero. -/
theorem polynomial_exact_degree (m : Nat) {b c0 : Rat} (hb : 0 < b) (hc0 : c0 ≠ 0) :
    ofPolynomial (polynomial m b c0) m ≠ 0 ∧
      ∀ n, m < n → ofPolynomial (polynomial m b c0) n = 0 := by
  rw [polynomial_coeff]
  exact ⟨coeff_nonzero m hb hc0 (by omega), fun n hn => coeff_vanishes m b c0 hn⟩

/-- The unmultiplied Laguerre differential equation at coefficient level,
including the ordinary interpretation at `x=0`. -/
theorem differential_coefficients (m : Nat) {b : Rat} (hb : 0 < b) (c0 : Rat) (n : Nat) :
    let c := coeff m b c0
    mulX (coefficientShift (coefficientShift c)) n + b * coefficientShift c n -
      mulX (coefficientShift c) n + (m : Rat) * c n = 0 := by
  have hs := (equation m b).coeff_isSolution 0 c0 (root m b) (nonresonant m hb) (n + 1)
  rw [Frobenius.Equation.residual_split, lower_succ, indicial] at hs
  change (0 + ((n + 1 : Nat) : Rat)) * (0 + ((n + 1 : Nat) : Rat) + b - 1) *
      coeff m b c0 (n + 1) + ((m : Rat) - (0 + (n : Rat))) * coeff m b c0 n = 0 at hs
  dsimp
  cases n with
  | zero => simp only [mulX, coefficientShift] at *; grind
  | succ n =>
      simp only [mulX, coefficientShift, Rat.natCast_add] at *
      grind

/-- The polynomial value and its two actual derivative polynomials. -/
def value (m : Nat) (b c0 : Rat) : Rat → Rat :=
  FinitePolynomial.taylorPrefix (coeff m b c0) (m + 1)
def firstDerivative (m : Nat) (b c0 : Rat) : Rat → Rat :=
  FinitePolynomial.taylorPrefix (coefficientShift (coeff m b c0)) (m + 1)
def secondDerivative (m : Nat) (b c0 : Rat) : Rat → Rat :=
  FinitePolynomial.taylorPrefix (coefficientShift (coefficientShift (coeff m b c0))) (m + 1)

/-- Pointwise ODE identity for the terminating Frobenius polynomial. -/
theorem differential_equation (m : Nat) {b : Rat} (hb : 0 < b) (c0 x : Rat) :
    x * secondDerivative m b c0 x + (b - x) * firstDerivative m b c0 x +
      (m : Rat) * value m b c0 x = 0 := by
  let c := coeff m b c0
  let d := coefficientShift c
  let dd := coefficientShift d
  have hd : d ((m + 1) - 1) = 0 := by
    dsimp [d, c, coefficientShift]
    rw [coeff_vanishes m b c0 (by omega)]
    grind
  have hdd : dd ((m + 1) - 1) = 0 := by
    dsimp [dd, d, c, coefficientShift]
    rw [coeff_vanishes m b c0 (by omega)]
    grind
  have hz : (fun n => (mulX dd n + b * d n) + ((-1 : Rat) * mulX d n + (m : Rat) * c n)) =
      (fun _ => 0) := by
    funext n
    have h := differential_coefficients m hb c0 n
    change mulX dd n + b * d n - mulX d n + (m : Rat) * c n = 0 at h
    grind
  have he := congrArg (fun f => FinitePolynomial.taylorPrefix f (m + 1) x) hz
  rw [taylorPrefix_add, taylorPrefix_add, taylorPrefix_add,
    taylorPrefix_scale, taylorPrefix_scale, taylorPrefix_scale,
    taylorPrefix_mulX dd (m + 1) x hdd, taylorPrefix_mulX d (m + 1) x hd,
    taylorPrefix_zero] at he
  change x * FinitePolynomial.taylorPrefix dd (m + 1) x +
    (b - x) * FinitePolynomial.taylorPrefix d (m + 1) x +
    (m : Rat) * FinitePolynomial.taylorPrefix c (m + 1) x = 0
  grind

def firstDerivativeCertificate (m : Nat) (b c0 a z C : Rat)
    (hleft : -C ≤ a) (hright : z ≤ C) (hC : 1 ≤ C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (value m b c0) a z)
      (FunctionOnInterval.exactRat (firstDerivative m b c0) a z) :=
  polynomialDerivativeCertificate (coeff m b c0) (m + 1)
    (coeff_vanishes m b c0 (by omega)) a z C hleft hright hC

def secondDerivativeCertificate (m : Nat) (b c0 a z C : Rat)
    (hleft : -C ≤ a) (hright : z ≤ C) (hC : 1 ≤ C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (firstDerivative m b c0) a z)
      (FunctionOnInterval.exactRat (secondDerivative m b c0) a z) := by
  apply polynomialDerivativeCertificate (coefficientShift (coeff m b c0)) (m + 1)
    ?_ a z C hleft hright hC
  simp only [coefficientShift, coeff_vanishes m b c0 (by omega : m < m + 1 + 1)]
  grind

theorem algebraic_relation (m : Nat) (b c0 x : Rat) :
    (polynomialGraph (polynomial m b c0)).polynomial.evalRat
      (fun i => if i.val = 0 then x else value m b c0 x) = 0 := by
  have hv : Polynomial.eval (polynomial m b c0) x = value m b c0 x :=
    eval_truncation _ _ _
  rw [← hv]
  exact polynomialGraph_holds _ x

end ComputableAnalysis.AlgebraicODE.Fuchs.Laguerre
