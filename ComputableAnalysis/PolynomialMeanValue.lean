import ComputableAnalysis.Differential
import ComputableAnalysis.Polynomial

/-!
# A finite polynomial mean-value certificate

This file gives an endpoint certificate for finite rational polynomials.  The
coefficient list uses the Horner convention from `Polynomial.eval`: the head
is the constant coefficient.  The derivative evaluator below is defined by
the corresponding finite Horner recurrence.  Thus the result uses only
rational arithmetic and finite induction; it introduces no intermediate
point and no completeness or limiting argument.
-/

namespace ComputableAnalysis

namespace Polynomial

/-- The derivative evaluator for the Horner representation of a polynomial.

For `c :: cs`, the represented polynomial is `c + x * P`, so its derivative
evaluator is `P + x * P'`.  This local evaluator avoids depending on the
implementation details of `Polynomial.derivative` while retaining an
executable finite algorithm. -/
def finiteDerivativeEval : List Rat -> Rat -> Rat
  | [], _ => 0
  | _ :: cs, x => eval cs x + x * finiteDerivativeEval cs x

theorem finiteDerivativeEval_cons (c : Rat) (cs : List Rat) (x : Rat) :
    finiteDerivativeEval (c :: cs) x =
      eval cs x + x * finiteDerivativeEval cs x := by
  rfl

theorem finiteDerivativeEval_linear (c₀ c₁ x : Rat) :
    finiteDerivativeEval [c₀, c₁] x = c₁ := by
  simp [finiteDerivativeEval, eval]
  grind

theorem finiteDerivativeEval_quadratic (c₀ c₁ c₂ x : Rat) :
    finiteDerivativeEval [c₀, c₁, c₂] x = c₁ + 2 * c₂ * x := by
  simp [finiteDerivativeEval, eval]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem finiteDerivativeEval_cubic (c₀ c₁ c₂ c₃ x : Rat) :
    finiteDerivativeEval [c₀, c₁, c₂, c₃] x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 := by
  simp [finiteDerivativeEval, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ]

theorem finiteDerivativeEval_quartic (c₀ c₁ c₂ c₃ c₄ x : Rat) :
    finiteDerivativeEval [c₀, c₁, c₂, c₃, c₄] x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 + 4 * c₄ * x ^ 3 := by
  simp [finiteDerivativeEval, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ]

theorem finiteDerivativeEval_quintic
    (c₀ c₁ c₂ c₃ c₄ c₅ x : Rat) :
    finiteDerivativeEval [c₀, c₁, c₂, c₃, c₄, c₅] x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 +
        4 * c₄ * x ^ 3 + 5 * c₅ * x ^ 4 := by
  simp [finiteDerivativeEval, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ]

theorem finiteDerivativeEval_sextic
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ x : Rat) :
    finiteDerivativeEval [c₀, c₁, c₂, c₃, c₄, c₅, c₆] x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 +
        4 * c₄ * x ^ 3 + 5 * c₅ * x ^ 4 + 6 * c₆ * x ^ 5 := by
  simp [finiteDerivativeEval, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ]

theorem finiteDerivativeEval_septic
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ x : Rat) :
    finiteDerivativeEval [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇] x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 +
        4 * c₄ * x ^ 3 + 5 * c₅ * x ^ 4 + 6 * c₆ * x ^ 5 +
        7 * c₇ * x ^ 6 := by
  simp [finiteDerivativeEval, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ]

theorem finiteDerivativeEval_octic
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ x : Rat) :
    finiteDerivativeEval [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈] x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 +
        4 * c₄ * x ^ 3 + 5 * c₅ * x ^ 4 + 6 * c₆ * x ^ 5 +
        7 * c₇ * x ^ 6 + 8 * c₈ * x ^ 7 := by
  simp [finiteDerivativeEval, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ]

theorem finiteDerivativeEval_nonic
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ x : Rat) :
    finiteDerivativeEval
        [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉] x =
      c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 +
        4 * c₄ * x ^ 3 + 5 * c₅ * x ^ 4 + 6 * c₆ * x ^ 5 +
        7 * c₇ * x ^ 6 + 8 * c₈ * x ^ 7 + 9 * c₉ * x ^ 8 := by
  simp [finiteDerivativeEval, eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ]

private theorem eval_mono_of_nonneg_coeffs
    {coeffs : List Rat} {a b : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) :
    eval coeffs a <= eval coeffs b := by
  induction coeffs with
  | nil => simp [eval]
  | cons c cs ih =>
      simp only [eval, List.foldr]
      have hc : 0 <= c := hcoeffs c (by simp)
      have hcs : forall d, d ∈ cs -> 0 <= d := by
        intro d hd
        exact hcoeffs d (by simp [hd])
      have htail : eval cs a <= eval cs b := ih hcs
      have htail_nonneg : 0 <= eval cs a :=
        eval_nonneg_of_nonneg_coeffs hcs ha
      have hba : 0 <= b - a := by grind
      have hprod : a * eval cs a <= b * eval cs b := by
        calc
          a * eval cs a <= b * eval cs a :=
            Rat.mul_le_mul_of_nonneg_right hab htail_nonneg
          _ <= b * eval cs b :=
            Rat.mul_le_mul_of_nonneg_left htail (by
              have hb : 0 <= b := by grind
              exact hb)
      change c + a * eval cs a <= c + b * eval cs b
      exact (Rat.add_le_add_left).2 hprod

private theorem finiteDerivativeEval_nonneg_of_nonneg_coeffs
    {coeffs : List Rat} {x : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c) (hx : 0 <= x) :
    0 <= finiteDerivativeEval coeffs x := by
  induction coeffs with
  | nil => simp [finiteDerivativeEval]
  | cons c cs ih =>
      have hcs : forall d, d ∈ cs -> 0 <= d := by
        intro d hd
        exact hcoeffs d (by simp [hd])
      have hvalue : 0 <= eval cs x :=
        eval_nonneg_of_nonneg_coeffs hcs hx
      have hderiv : 0 <= finiteDerivativeEval cs x := ih hcs
      simp only [finiteDerivativeEval]
      exact Rat.add_nonneg hvalue (Rat.mul_nonneg hx hderiv)

private theorem eval_secant_horner
    {c : Rat} {cs : List Rat} {a b : Rat}
    (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient (fun z => eval (c :: cs) z) a (b - a) =
      eval cs b + a * ExactFunction.differenceQuotient
        (fun z => eval cs z) a (b - a) := by
  unfold ExactFunction.differenceQuotient
  simp only [eval, List.foldr]
  have hab : a + (b - a) = b := by grind
  rw [hab]
  rw [Rat.div_def]
  have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
    Rat.mul_inv_cancel (b - a) hne
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.mul_comm]

/-! The endpoint bound for finite Horner polynomials. -/
theorem finitePolynomial_secant_derivative_bracket
    {coeffs : List Rat} {a b : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    finiteDerivativeEval coeffs a <=
        ExactFunction.differenceQuotient (fun z => eval coeffs z) a (b - a) /\
      ExactFunction.differenceQuotient (fun z => eval coeffs z) a (b - a) <=
        finiteDerivativeEval coeffs b := by
  induction coeffs with
  | nil =>
      simp only [finiteDerivativeEval, eval]
      unfold ExactFunction.differenceQuotient
      simp only [List.foldr]
      have hz : (0 - 0 : Rat) = 0 := by grind
      rw [hz]
      constructor <;> rw [Rat.div_def, Rat.zero_mul] <;> grind
  | cons c cs ih =>
      have hcs : forall d, d ∈ cs -> 0 <= d := by
        intro d hd
        exact hcoeffs d (by simp [hd])
      have htail := ih hcs
      have hmono := eval_mono_of_nonneg_coeffs hcs ha hab
      have htail_nonneg : 0 <= eval cs a :=
        eval_nonneg_of_nonneg_coeffs hcs ha
      have hsecant := eval_secant_horner (c := c) (cs := cs)
        (a := a) (b := b) hne
      rw [hsecant]
      constructor
      · dsimp [finiteDerivativeEval]
        have hscaled := Rat.mul_le_mul_of_nonneg_left htail.1 ha
        grind
      · dsimp [finiteDerivativeEval]
        have hscaled := Rat.mul_le_mul_of_nonneg_left htail.2 ha
        have hba : 0 <= b - a := by grind
        have hterm := Rat.mul_le_mul_of_nonneg_right hmono hba
        have hb : 0 <= b := by grind
        have hderiv_nonneg : 0 <= finiteDerivativeEval cs b :=
          finiteDerivativeEval_nonneg_of_nonneg_coeffs hcs hb
        have hscaled' := Rat.mul_le_mul_of_nonneg_right hab hderiv_nonneg
        grind

/-- A generic finite Mean Value error bound: the secant's distance from the
left endpoint derivative is no larger than the derivative bracket width. -/
theorem finitePolynomial_secant_qabs_error_le_derivative_gap
    {coeffs : List Rat} {a b : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    qabs (ExactFunction.differenceQuotient
      (fun z => eval coeffs z) a (b - a) - finiteDerivativeEval coeffs a) ≤
      finiteDerivativeEval coeffs b - finiteDerivativeEval coeffs a := by
  have hbracket := finitePolynomial_secant_derivative_bracket
    (coeffs := coeffs) (a := a) (b := b) hcoeffs ha hab hne
  have hderiv_order : finiteDerivativeEval coeffs a ≤
      finiteDerivativeEval coeffs b :=
    Rat.le_trans hbracket.1 hbracket.2
  exact qabs_sub_le_of_common_bounds
    hbracket.1 hbracket.2 Rat.le_refl hderiv_order

theorem finiteCubic_secant_derivative_bracket
    {c₀ c₁ c₂ c₃ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 <=
        ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃] z) a (b - a) /\
      ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃] z) a (b - a) <=
        c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 := by
  have hbracket := finitePolynomial_secant_derivative_bracket
    (coeffs := [c₀, c₁, c₂, c₃]) (a := a) (b := b)
    hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_cubic] using hbracket

theorem finiteQuartic_secant_derivative_bracket
    {c₀ c₁ c₂ c₃ c₄ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 <=
        ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄] z) a (b - a) /\
      ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄] z) a (b - a) <=
        c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 := by
  have hbracket := finitePolynomial_secant_derivative_bracket
    (coeffs := [c₀, c₁, c₂, c₃, c₄]) (a := a) (b := b)
    hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_quartic] using hbracket

theorem finiteQuintic_secant_derivative_bracket
    {c₀ c₁ c₂ c₃ c₄ c₅ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄, c₅] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 +
          4 * c₄ * a ^ 3 + 5 * c₅ * a ^ 4 <=
        ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅] z) a (b - a) /\
      ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅] z) a (b - a) <=
        c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 +
          4 * c₄ * b ^ 3 + 5 * c₅ * b ^ 4 := by
  have hbracket := finitePolynomial_secant_derivative_bracket
    (coeffs := [c₀, c₁, c₂, c₃, c₄, c₅]) (a := a) (b := b)
    hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_quintic] using hbracket

theorem finiteSextic_secant_derivative_bracket
    {c₀ c₁ c₂ c₃ c₄ c₅ c₆ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄, c₅, c₆] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5 <=
        ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅, c₆] z) a (b - a) /\
      ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅, c₆] z) a (b - a) <=
        c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4 + 6 * c₆ * b ^ 5 := by
  have hbracket := finitePolynomial_secant_derivative_bracket
    (coeffs := [c₀, c₁, c₂, c₃, c₄, c₅, c₆]) (a := a) (b := b)
    hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_sextic] using hbracket

/-- The finite bracket has an explicit rational width budget.  This is the
quantitative form used by a stagewise Mean Value computation: the secant
quotient cannot lie farther from the lower endpoint derivative than the
endpoint derivative gap. -/
theorem finitePolynomial_secant_derivative_gap
    {coeffs : List Rat} {a b : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient (fun z => eval coeffs z) a (b - a) -
        finiteDerivativeEval coeffs a <=
      finiteDerivativeEval coeffs b - finiteDerivativeEval coeffs a := by
  have hbracket := finitePolynomial_secant_derivative_bracket
    (coeffs := coeffs) (a := a) (b := b) hcoeffs ha hab hne
  grind [Rat.sub_eq_add_neg]

theorem finiteCubic_secant_derivative_gap
    {c₀ c₁ c₂ c₃ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃] z) a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2) <=
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2) := by
  have hgap := finitePolynomial_secant_derivative_gap
    (coeffs := [c₀, c₁, c₂, c₃]) (a := a) (b := b)
    hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_cubic] using hgap

/-- The cubic secant gap has an explicit linear mesh-width budget.  This is
the quantitative form used when a finite Mean Value certificate must choose
the mesh from a requested rational tolerance. -/
theorem finiteCubic_secant_derivative_gap_le
    {c₀ c₁ c₂ c₃ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃] z) a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2) <=
      (2 * c₂ + 6 * c₃ * b) * (b - a) := by
  have hgap := finiteCubic_secant_derivative_gap
    (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃)
    (a := a) (b := b) hcoeffs ha hab hne
  have hc₂ : 0 <= c₂ := hcoeffs c₂ (by simp)
  have hc₃ : 0 <= c₃ := hcoeffs c₃ (by simp)
  have hba : 0 <= b - a := by grind
  have habsum : a + b <= 2 * b := by grind
  have hscaled : 3 * c₃ * (a + b) <= 3 * c₃ * (2 * b) := by
    exact Rat.mul_le_mul_of_nonneg_left habsum
      (Rat.mul_nonneg (by native_decide) hc₃)
  have hcoef :
      2 * c₂ + 3 * c₃ * (a + b) <= 2 * c₂ + 6 * c₃ * b := by
    calc
      2 * c₂ + 3 * c₃ * (a + b) <=
          2 * c₂ + 3 * c₃ * (2 * b) :=
        (Rat.add_le_add_left).2 hscaled
      _ = 2 * c₂ + 6 * c₃ * b := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hderivgap :
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2) -
          (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2) =
        (2 * c₂ + 3 * c₃ * (a + b)) * (b - a) := by
    grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.sub_eq_add_neg]
  have hbudget :
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2) -
          (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2) <=
        (2 * c₂ + 6 * c₃ * b) * (b - a) := by
    rw [hderivgap]
    exact Rat.mul_le_mul_of_nonneg_right hcoef hba
  calc
    _ <= (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2) := hgap
    _ <= _ := hbudget

/- A finite rational enclosure for the cubic secant derivative.  Once the
mesh budget is below `ε`, the secant quotient is a certified witness lying
between the endpoint derivative and its `ε`-neighbourhood. -/
theorem finiteCubic_secant_derivative_enclosure_of_budget
    {c₀ c₁ c₂ c₃ a b ε : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0)
    (hε : (2 * c₂ + 6 * c₃ * b) * (b - a) <= ε) :
    c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 <=
        ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃] z) a (b - a) ∧
      ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃] z) a (b - a) <=
        c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + ε := by
  have hbracket := finiteCubic_secant_derivative_bracket
    (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃)
    (a := a) (b := b) hcoeffs ha hab hne
  have hgap := finiteCubic_secant_derivative_gap_le
    (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃)
    (a := a) (b := b) hcoeffs ha hab hne
  constructor
  · exact hbracket.1
  · have hsecant_gap :
        ExactFunction.differenceQuotient
            (fun z => eval [c₀, c₁, c₂, c₃] z) a (b - a) -
          (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2) <= ε :=
      Rat.le_trans hgap hε
    grind [Rat.sub_eq_add_neg]

theorem finiteQuartic_secant_derivative_gap
    {c₀ c₁ c₂ c₃ c₄ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄] z) a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3) <=
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3) := by
  have hgap := finitePolynomial_secant_derivative_gap
    (coeffs := [c₀, c₁, c₂, c₃, c₄]) (a := a) (b := b)
    hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_quartic] using hgap

/-- The quartic secant gap has an explicit linear mesh-width budget. -/
theorem finiteQuartic_secant_derivative_gap_le
    {c₀ c₁ c₂ c₃ c₄ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄] z) a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3) <=
      (2 * c₂ + 6 * c₃ * b + 12 * c₄ * b ^ 2) * (b - a) := by
  have hgap := finiteQuartic_secant_derivative_gap
    (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (c₄ := c₄)
    (a := a) (b := b) hcoeffs ha hab hne
  have hc₂ : 0 <= c₂ := hcoeffs c₂ (by simp)
  have hc₃ : 0 <= c₃ := hcoeffs c₃ (by simp)
  have hc₄ : 0 <= c₄ := hcoeffs c₄ (by simp)
  have hb : 0 <= b := by grind
  have hba : 0 <= b - a := by grind
  have habsum : a + b <= 2 * b := by grind
  have hsq_a : a ^ 2 <= a * b := by
    rw [show a ^ 2 = a * a by grind]
    exact Rat.mul_le_mul_of_nonneg_left hab ha
  have hsq_b : a * b <= b ^ 2 := by
    rw [show b ^ 2 = b * b by grind]
    exact Rat.mul_le_mul_of_nonneg_right hab hb
  have hsq_b_mul : a * b <= b * b := by
    rw [← show b ^ 2 = b * b by grind]
    exact hsq_b
  have hsq : a ^ 2 + a * b + b ^ 2 <= 3 * b ^ 2 := by
    calc
      a ^ 2 + a * b + b ^ 2 <= a * b + a * b + b ^ 2 := by
        simpa [Rat.add_assoc] using
          (Rat.add_le_add_right (c := a * b + b ^ 2)).2 hsq_a
      _ = a * b + (a * b + b ^ 2) := by grind
      _ <= b ^ 2 + (a * b + b ^ 2) := by
        exact (Rat.add_le_add_right (c := a * b + b ^ 2)).2 hsq_b
      _ <= b ^ 2 + (b ^ 2 + b ^ 2) := by
        exact (Rat.add_le_add_left (c := b ^ 2)).2
          ((Rat.add_le_add_right (c := b ^ 2)).2 hsq_b)
      _ = 3 * b ^ 2 := by grind
      _ = 3 * b ^ 2 := by grind
  have hscaled₃ : 3 * c₃ * (a + b) <= 3 * c₃ * (2 * b) := by
    exact Rat.mul_le_mul_of_nonneg_left habsum
      (Rat.mul_nonneg (by native_decide) hc₃)
  have hscaled₄ : 4 * c₄ * (a ^ 2 + a * b + b ^ 2) <=
      4 * c₄ * (3 * b ^ 2) := by
    exact Rat.mul_le_mul_of_nonneg_left hsq
      (Rat.mul_nonneg (by native_decide) hc₄)
  have hcoef :
      2 * c₂ + 3 * c₃ * (a + b) +
          4 * c₄ * (a ^ 2 + a * b + b ^ 2) <=
        2 * c₂ + 6 * c₃ * b + 12 * c₄ * b ^ 2 := by
    calc
      2 * c₂ + 3 * c₃ * (a + b) +
          4 * c₄ * (a ^ 2 + a * b + b ^ 2) <=
          2 * c₂ + 3 * c₃ * (2 * b) +
            4 * c₄ * (3 * b ^ 2) := by
        have hinner :
            3 * c₃ * (a + b) +
                4 * c₄ * (a ^ 2 + a * b + b ^ 2) <=
              3 * c₃ * (2 * b) + 4 * c₄ * (3 * b ^ 2) := by
          calc
            3 * c₃ * (a + b) +
                4 * c₄ * (a ^ 2 + a * b + b ^ 2) <=
                3 * c₃ * (2 * b) +
                  4 * c₄ * (a ^ 2 + a * b + b ^ 2) :=
              (Rat.add_le_add_right
                (c := 4 * c₄ * (a ^ 2 + a * b + b ^ 2))).2 hscaled₃
            _ <= 3 * c₃ * (2 * b) + 4 * c₄ * (3 * b ^ 2) :=
              (Rat.add_le_add_left
                (c := 3 * c₃ * (2 * b))).2 hscaled₄
        simpa [Rat.add_assoc] using (Rat.add_le_add_left (c := 2 * c₂)).2 hinner
      _ = 2 * c₂ + 6 * c₃ * b + 12 * c₄ * b ^ 2 := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hderivgap :
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3) -
          (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3) =
        (2 * c₂ + 3 * c₃ * (a + b) +
          4 * c₄ * (a ^ 2 + a * b + b ^ 2)) * (b - a) := by
    grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.sub_eq_add_neg]
  have hbudget :
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3) -
          (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3) <=
        (2 * c₂ + 6 * c₃ * b + 12 * c₄ * b ^ 2) * (b - a) := by
    rw [hderivgap]
    exact Rat.mul_le_mul_of_nonneg_right hcoef hba
  calc
    _ <= (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3) := hgap
    _ <= _ := hbudget

theorem finiteQuintic_secant_derivative_gap
    {c₀ c₁ c₂ c₃ c₄ c₅ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄, c₅] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅] z) a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4) <=
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4) := by
  have hgap := finitePolynomial_secant_derivative_gap
    (coeffs := [c₀, c₁, c₂, c₃, c₄, c₅]) (a := a) (b := b)
    hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_quintic] using hgap

/-- The quintic secant gap has an explicit linear mesh-width budget. -/
theorem finiteQuintic_secant_derivative_gap_le
    {c₀ c₁ c₂ c₃ c₄ c₅ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄, c₅] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅] z) a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4) <=
      (2 * c₂ + 6 * c₃ * b + 12 * c₄ * b ^ 2 +
        20 * c₅ * b ^ 3) * (b - a) := by
  have hgap := finiteQuintic_secant_derivative_gap
    (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (c₄ := c₄) (c₅ := c₅)
    (a := a) (b := b) hcoeffs ha hab hne
  have hc₂ : 0 <= c₂ := hcoeffs c₂ (by simp)
  have hc₃ : 0 <= c₃ := hcoeffs c₃ (by simp)
  have hc₄ : 0 <= c₄ := hcoeffs c₄ (by simp)
  have hc₅ : 0 <= c₅ := hcoeffs c₅ (by simp)
  have hb : 0 <= b := by grind
  have hba : 0 <= b - a := by grind
  have habsum : a + b <= 2 * b := by grind
  have hsq_a : a ^ 2 <= a * b := by
    rw [show a ^ 2 = a * a by grind]
    exact Rat.mul_le_mul_of_nonneg_left hab ha
  have hsq_b : a * b <= b ^ 2 := by
    rw [show b ^ 2 = b * b by grind]
    exact Rat.mul_le_mul_of_nonneg_right hab hb
  have hcube_a : a ^ 3 <= a ^ 2 * b := by
    calc
      a ^ 3 = a ^ 2 * a := by grind [Rat.pow_succ]
      _ <= a ^ 2 * b := Rat.mul_le_mul_of_nonneg_left hab
        (Rat.pow_nonneg ha)
  have hcube_b : a ^ 2 * b <= a * b ^ 2 := by
    calc
      a ^ 2 * b = a * (a * b) := by grind [Rat.pow_succ, Rat.mul_assoc]
      _ <= b * (a * b) := Rat.mul_le_mul_of_nonneg_right hab
        (Rat.mul_nonneg ha hb)
      _ = a * b ^ 2 := by grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm]
  have hcube_c : a * b ^ 2 <= b ^ 3 := by
    calc
      a * b ^ 2 <= b * b ^ 2 := Rat.mul_le_mul_of_nonneg_right hab
        (Rat.pow_nonneg hb)
      _ = b ^ 3 := by grind [Rat.pow_succ]
  have hsq : a ^ 2 + a * b + b ^ 2 <= 3 * b ^ 2 := by
    calc
      a ^ 2 + a * b + b ^ 2 <= a * b + a * b + b ^ 2 := by
        simpa [Rat.add_assoc] using
          (Rat.add_le_add_right (c := a * b + b ^ 2)).2 hsq_a
      _ = a * b + (a * b + b ^ 2) := by grind
      _ <= b ^ 2 + (a * b + b ^ 2) := by
        exact (Rat.add_le_add_right (c := a * b + b ^ 2)).2 hsq_b
      _ <= b ^ 2 + (b ^ 2 + b ^ 2) := by
        exact (Rat.add_le_add_left (c := b ^ 2)).2
          ((Rat.add_le_add_right (c := b ^ 2)).2 hsq_b)
      _ = 3 * b ^ 2 := by grind
  have hcube : a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 <=
      4 * b ^ 3 := by
    grind [Rat.add_assoc]
  have hscaled₃ : 3 * c₃ * (a + b) <= 3 * c₃ * (2 * b) := by
    exact Rat.mul_le_mul_of_nonneg_left habsum
      (Rat.mul_nonneg (by native_decide) hc₃)
  have hscaled₄ : 4 * c₄ * (a ^ 2 + a * b + b ^ 2) <=
      4 * c₄ * (3 * b ^ 2) := by
    exact Rat.mul_le_mul_of_nonneg_left hsq
      (Rat.mul_nonneg (by native_decide) hc₄)
  have hscaled₅ : 5 * c₅ * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) <=
      5 * c₅ * (4 * b ^ 3) := by
    exact Rat.mul_le_mul_of_nonneg_left hcube
      (Rat.mul_nonneg (by native_decide) hc₅)
  have hcoef :
      2 * c₂ + 3 * c₃ * (a + b) +
          4 * c₄ * (a ^ 2 + a * b + b ^ 2) +
          5 * c₅ * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) <=
        2 * c₂ + 6 * c₃ * b + 12 * c₄ * b ^ 2 + 20 * c₅ * b ^ 3 := by
    grind [Rat.add_assoc, Rat.mul_assoc, Rat.mul_comm]
  have hderivgap :
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4) -
          (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
            5 * c₅ * a ^ 4) =
        (2 * c₂ + 3 * c₃ * (a + b) +
          4 * c₄ * (a ^ 2 + a * b + b ^ 2) +
          5 * c₅ * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3)) * (b - a) := by
    grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.sub_eq_add_neg]
  have hbudget :
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4) -
          (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
            5 * c₅ * a ^ 4) <=
        (2 * c₂ + 6 * c₃ * b + 12 * c₄ * b ^ 2 +
          20 * c₅ * b ^ 3) * (b - a) := by
    rw [hderivgap]
    exact Rat.mul_le_mul_of_nonneg_right hcoef hba
  calc
    _ <= (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
        5 * c₅ * b ^ 4) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4) := hgap
    _ <= _ := hbudget

theorem finiteSextic_secant_derivative_gap
    {c₀ c₁ c₂ c₃ c₄ c₅ c₆ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄, c₅, c₆] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅, c₆] z) a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5) <=
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4 + 6 * c₆ * b ^ 5) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5) := by
  have hgap := finitePolynomial_secant_derivative_gap
    (coeffs := [c₀, c₁, c₂, c₃, c₄, c₅, c₆]) (a := a) (b := b)
    hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_sextic] using hgap

/-- The sextic secant gap has an explicit linear mesh-width budget. -/
theorem finiteSextic_secant_derivative_gap_le
    {c₀ c₁ c₂ c₃ c₄ c₅ c₆ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄, c₅, c₆] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅, c₆] z) a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5) <=
      (2 * c₂ + 6 * c₃ * b + 12 * c₄ * b ^ 2 +
        20 * c₅ * b ^ 3 + 30 * c₆ * b ^ 4) * (b - a) := by
  have hgap := finiteSextic_secant_derivative_gap
    (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (c₄ := c₄)
    (c₅ := c₅) (c₆ := c₆) (a := a) (b := b) hcoeffs ha hab hne
  have hc₂ : 0 <= c₂ := hcoeffs c₂ (by simp)
  have hc₃ : 0 <= c₃ := hcoeffs c₃ (by simp)
  have hc₄ : 0 <= c₄ := hcoeffs c₄ (by simp)
  have hc₅ : 0 <= c₅ := hcoeffs c₅ (by simp)
  have hc₆ : 0 <= c₆ := hcoeffs c₆ (by simp)
  have hb : 0 <= b := by grind
  have hba : 0 <= b - a := by grind
  have habsum : a + b <= 2 * b := by grind
  have hsq_a : a ^ 2 <= a * b := by
    rw [show a ^ 2 = a * a by grind]
    exact Rat.mul_le_mul_of_nonneg_left hab ha
  have hsq_b : a * b <= b ^ 2 := by
    rw [show b ^ 2 = b * b by grind]
    exact Rat.mul_le_mul_of_nonneg_right hab hb
  have hsq_b_mul : a * b <= b * b := by
    rw [← show b ^ 2 = b * b by grind]
    exact hsq_b
  have hcube_a : a ^ 3 <= a ^ 2 * b := by
    calc
      a ^ 3 = a ^ 2 * a := by grind [Rat.pow_succ]
      _ <= a ^ 2 * b := Rat.mul_le_mul_of_nonneg_left hab
        (Rat.pow_nonneg ha)
  have hcube_b : a ^ 2 * b <= a * b ^ 2 := by
    calc
      a ^ 2 * b = a * (a * b) := by grind [Rat.pow_succ, Rat.mul_assoc]
      _ <= b * (a * b) := Rat.mul_le_mul_of_nonneg_right hab
        (Rat.mul_nonneg ha hb)
      _ = a * b ^ 2 := by grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm]
  have hcube_c : a * b ^ 2 <= b ^ 3 := by
    calc
      a * b ^ 2 <= b * b ^ 2 := Rat.mul_le_mul_of_nonneg_right hab
        (Rat.pow_nonneg hb)
      _ = b ^ 3 := by grind [Rat.pow_succ]
  have hfour_a : a ^ 4 <= a ^ 3 * b := by
    calc
      a ^ 4 = a ^ 3 * a := by grind [Rat.pow_succ]
      _ <= a ^ 3 * b := Rat.mul_le_mul_of_nonneg_left hab
        (Rat.pow_nonneg ha)
  have hfour_b : a ^ 3 * b <= a ^ 2 * b ^ 2 := by
    calc
      a ^ 3 * b = a ^ 2 * (a * b) := by grind [Rat.pow_succ, Rat.mul_assoc]
      _ <= a ^ 2 * (b * b) := Rat.mul_le_mul_of_nonneg_left hsq_b_mul
        (Rat.pow_nonneg ha)
      _ = a ^ 2 * b ^ 2 := by grind [Rat.pow_succ]
  have hfour_c : a ^ 2 * b ^ 2 <= a * b ^ 3 := by
    calc
      a ^ 2 * b ^ 2 = a * (a * b ^ 2) := by grind [Rat.pow_succ, Rat.mul_assoc]
      _ <= b * (a * b ^ 2) := Rat.mul_le_mul_of_nonneg_right hab
        (Rat.mul_nonneg ha (Rat.pow_nonneg hb))
      _ = a * b ^ 3 := by grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm]
  have hfour_d : a * b ^ 3 <= b ^ 4 := by
    calc
      a * b ^ 3 <= b * b ^ 3 := Rat.mul_le_mul_of_nonneg_right hab
        (Rat.pow_nonneg hb)
      _ = b ^ 4 := by grind [Rat.pow_succ]
  have hsq : a ^ 2 + a * b + b ^ 2 <= 3 * b ^ 2 := by grind
  have hcube : a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 <=
      4 * b ^ 3 := by grind [Rat.add_assoc]
  have hfour : a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4 <=
      5 * b ^ 4 := by grind [Rat.add_assoc]
  have hscaled₃ : 3 * c₃ * (a + b) <= 3 * c₃ * (2 * b) := by
    exact Rat.mul_le_mul_of_nonneg_left habsum
      (Rat.mul_nonneg (by native_decide) hc₃)
  have hscaled₄ : 4 * c₄ * (a ^ 2 + a * b + b ^ 2) <=
      4 * c₄ * (3 * b ^ 2) := by
    exact Rat.mul_le_mul_of_nonneg_left hsq
      (Rat.mul_nonneg (by native_decide) hc₄)
  have hscaled₅ : 5 * c₅ * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) <=
      5 * c₅ * (4 * b ^ 3) := by
    exact Rat.mul_le_mul_of_nonneg_left hcube
      (Rat.mul_nonneg (by native_decide) hc₅)
  have hscaled₆ : 6 * c₆ * (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 +
      a * b ^ 3 + b ^ 4) <= 6 * c₆ * (5 * b ^ 4) := by
    exact Rat.mul_le_mul_of_nonneg_left hfour
      (Rat.mul_nonneg (by native_decide) hc₆)
  have hcoef :
      2 * c₂ + 3 * c₃ * (a + b) +
          4 * c₄ * (a ^ 2 + a * b + b ^ 2) +
          5 * c₅ * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) +
          6 * c₆ * (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) <=
        2 * c₂ + 6 * c₃ * b + 12 * c₄ * b ^ 2 +
          20 * c₅ * b ^ 3 + 30 * c₆ * b ^ 4 := by
    grind [Rat.add_assoc, Rat.mul_assoc, Rat.mul_comm]
  have hderivgap :
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4 + 6 * c₆ * b ^ 5) -
          (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
            5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5) =
        (2 * c₂ + 3 * c₃ * (a + b) +
          4 * c₄ * (a ^ 2 + a * b + b ^ 2) +
          5 * c₅ * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) +
          6 * c₆ * (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4)) *
          (b - a) := by
    grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.sub_eq_add_neg]
  have hbudget :
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4 + 6 * c₆ * b ^ 5) -
          (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
            5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5) <=
        (2 * c₂ + 6 * c₃ * b + 12 * c₄ * b ^ 2 +
          20 * c₅ * b ^ 3 + 30 * c₆ * b ^ 4) * (b - a) := by
    rw [hderivgap]
    exact Rat.mul_le_mul_of_nonneg_right hcoef hba
  calc
    _ <= (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
        5 * c₅ * b ^ 4 + 6 * c₆ * b ^ 5) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5) := hgap
    _ <= _ := hbudget

theorem finiteSeptic_secant_derivative_bracket
    {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇] z) a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5 + 7 * c₇ * a ^ 6) <=
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4 + 6 * c₆ * b ^ 5 + 7 * c₇ * b ^ 6) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5 + 7 * c₇ * a ^ 6) := by
  have hgap := finitePolynomial_secant_derivative_gap
    (coeffs := [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇]) (a := a) (b := b)
    hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_septic] using hgap

theorem finiteOctic_secant_derivative_bracket
    {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ a b : Rat}
    (hcoeffs : forall c,
      c ∈ [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈] z)
          a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5 + 7 * c₇ * a ^ 6 +
          8 * c₈ * a ^ 7) <=
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4 + 6 * c₆ * b ^ 5 + 7 * c₇ * b ^ 6 +
          8 * c₈ * b ^ 7) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5 + 7 * c₇ * a ^ 6 +
          8 * c₈ * a ^ 7) := by
  have hgap := finitePolynomial_secant_derivative_gap
    (coeffs := [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈])
    (a := a) (b := b) hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_octic] using hgap

theorem finiteNonic_secant_derivative_bracket
    {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ a b : Rat}
    (hcoeffs : forall c,
      c ∈ [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉] z)
          a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5 + 7 * c₇ * a ^ 6 +
          8 * c₈ * a ^ 7 + 9 * c₉ * a ^ 8) <=
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4 + 6 * c₆ * b ^ 5 + 7 * c₇ * b ^ 6 +
          8 * c₈ * b ^ 7 + 9 * c₉ * b ^ 8) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5 + 7 * c₇ * a ^ 6 +
          8 * c₈ * a ^ 7 + 9 * c₉ * a ^ 8) := by
  have hgap := finitePolynomial_secant_derivative_gap
    (coeffs := [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉])
    (a := a) (b := b) hcoeffs ha hab hne
  simpa only [finiteDerivativeEval_nonic] using hgap

theorem finiteSeptic_secant_derivative_gap
    {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    ExactFunction.differenceQuotient
          (fun z => eval [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇] z) a (b - a) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5 + 7 * c₇ * a ^ 6) <=
      (c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
          5 * c₅ * b ^ 4 + 6 * c₆ * b ^ 5 + 7 * c₇ * b ^ 6) -
        (c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
          5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5 + 7 * c₇ * a ^ 6) := by
  exact finiteSeptic_secant_derivative_bracket hcoeffs ha hab hne

private theorem finite_power_mono_nonneg {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (n : Nat) :
    a ^ n <= b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      have hleft := Rat.mul_le_mul_of_nonneg_right ih ha
      have hb : 0 <= b := by grind
      have hright := Rat.mul_le_mul_of_nonneg_left hab
        (Rat.pow_nonneg hb : 0 <= b ^ n)
      exact Rat.le_trans hleft hright

/- A monotonicity companion for the finite Mean Value interface.  With
nonnegative coefficients, the septic derivative evaluator is itself
monotone on every nonnegative rational interval. -/
theorem finiteSeptic_derivative_mono
    {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ a b : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃, c₄, c₅, c₆, c₇] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) :
    c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3 +
        5 * c₅ * a ^ 4 + 6 * c₆ * a ^ 5 + 7 * c₇ * a ^ 6 <=
      c₁ + 2 * c₂ * b + 3 * c₃ * b ^ 2 + 4 * c₄ * b ^ 3 +
        5 * c₅ * b ^ 4 + 6 * c₆ * b ^ 5 + 7 * c₇ * b ^ 6 := by
  have hc₂ : 0 <= c₂ := hcoeffs c₂ (by simp)
  have hc₃ : 0 <= c₃ := hcoeffs c₃ (by simp)
  have hc₄ : 0 <= c₄ := hcoeffs c₄ (by simp)
  have hc₅ : 0 <= c₅ := hcoeffs c₅ (by simp)
  have hc₆ : 0 <= c₆ := hcoeffs c₆ (by simp)
  have hc₇ : 0 <= c₇ := hcoeffs c₇ (by simp)
  have h2 := finite_power_mono_nonneg ha hab 2
  have h3 := finite_power_mono_nonneg ha hab 3
  have h4 := finite_power_mono_nonneg ha hab 4
  have h5 := finite_power_mono_nonneg ha hab 5
  have h6 := finite_power_mono_nonneg ha hab 6
  have hterm1 : 2 * c₂ * a <= 2 * c₂ * b := by
    exact Rat.mul_le_mul_of_nonneg_left hab
      (Rat.mul_nonneg (by native_decide) hc₂)
  have hterm2 : 3 * c₃ * a ^ 2 <= 3 * c₃ * b ^ 2 := by
    exact Rat.mul_le_mul_of_nonneg_left h2
      (Rat.mul_nonneg (by native_decide) hc₃)
  have hterm3 : 4 * c₄ * a ^ 3 <= 4 * c₄ * b ^ 3 := by
    exact Rat.mul_le_mul_of_nonneg_left h3
      (Rat.mul_nonneg (by native_decide) hc₄)
  have hterm4 : 5 * c₅ * a ^ 4 <= 5 * c₅ * b ^ 4 := by
    exact Rat.mul_le_mul_of_nonneg_left h4
      (Rat.mul_nonneg (by native_decide) hc₅)
  have hterm5 : 6 * c₆ * a ^ 5 <= 6 * c₆ * b ^ 5 := by
    exact Rat.mul_le_mul_of_nonneg_left h5
      (Rat.mul_nonneg (by native_decide) hc₆)
  have hterm6 : 7 * c₇ * a ^ 6 <= 7 * c₇ * b ^ 6 := by
    exact Rat.mul_le_mul_of_nonneg_left h6
      (Rat.mul_nonneg (by native_decide) hc₇)
  grind [Rat.add_le_add_left, Rat.add_assoc]

end Polynomial

end ComputableAnalysis
