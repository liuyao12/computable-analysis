import ComputableAnalysis.Differential
import ComputableAnalysis.PowerSeries

/-!
# Quantitative derivatives of finite rational polynomials

This module packages the finite secant estimate from `PowerSeries.lean` into
the project’s two-sided interval derivative interface.  The input is a
rational interval together with a rational bounding box; the proof selects a
dyadic step schedule from the explicitly computed monomial error coefficient.
No mean-value theorem, topology API, or completed-real argument is used.
-/

namespace ComputableAnalysis

namespace FinitePolynomial

/-- The normalized monomial `x^(n+1)/(n+1)` as an exact rational interval
function. -/
def normalizedMonomialOnInterval (a b : Rat) (n : Nat) : FunctionOnInterval :=
  FunctionOnInterval.exactRat
    (fun x => x ^ (n + 1) / ((n + 1 : Nat) : Rat)) a b

/-- The derivative monomial `x^n` on the same interval. -/
def monomialOnInterval (a b : Rat) (n : Nat) : FunctionOnInterval :=
  FunctionOnInterval.exactRat (fun x => x ^ n) a b

/-- The executable dyadic step schedule for the normalized-monomial
derivative.  It converts the explicit finite secant coefficient into the
requested interval precision by the rational half-decay modulus. -/
def normalizedMonomialStepPrecision (C : Rat) (n stage : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift
    (powerSecantErrorBound C (n + 1)) (precisionAtStage stage)

private theorem qabs_le_of_neg_le_le {x C : Rat}
    (hleft : -C <= x) (hright : x <= C) :
    qabs x <= C := by
  unfold qabs
  by_cases hx : x < 0
  · rw [if_pos hx]
    grind [Rat.sub_eq_add_neg]
  · rw [if_neg hx]
    exact hright

private theorem normalizedMonomial_step_error_le_precision
    {C h : Rat} (hC0 : 0 <= C) (n stage : Nat)
    (hsmall : qabs h <=
      1 / ((normalizedMonomialStepPrecision C n stage : Nat) : Rat)) :
    qabs h * powerSecantErrorBound C (n + 1) <=
      (precisionAtStage stage).val := by
  let E : Rat := powerSecantErrorBound C (n + 1)
  let shift : Nat := RationalMajorant.halfDecayShift E (precisionAtStage stage)
  have hE0 : 0 <= E := by
    dsimp [E]
    exact powerSecantErrorBound_nonneg hC0 _
  have hsmall' : qabs h <= 1 / (((2 ^ shift : Nat) : Rat)) := by
    simpa [normalizedMonomialStepPrecision, E, shift] using hsmall
  have hscaled : qabs h * E <= (1 / (((2 ^ shift : Nat) : Rat)) * E) :=
    Rat.mul_le_mul_of_nonneg_right hsmall' hE0
  have hgeometric : E * ((1 : Rat) / 2) ^ shift <=
      (precisionAtStage stage).val := by
    simpa [shift] using
      RationalMajorant.halfDecayShift_spec hE0 (precisionAtStage stage)
  calc
    qabs h * powerSecantErrorBound C (n + 1) = qabs h * E := rfl
    _ <= 1 / (((2 ^ shift : Nat) : Rat)) * E := hscaled
    _ = E * ((1 : Rat) / 2) ^ shift := by
      rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
      grind [Rat.mul_comm]
    _ <= (precisionAtStage stage).val := hgeometric

/-- Every normalized monomial has a two-sided rational interval derivative on
any interval contained in `[-C,C]`, provided `C >= 1`.  The proof is the
literal finite quotient estimate with a dyadic schedule chosen from its
explicit error coefficient. -/
def normalizedMonomial_hasDerivativeOnInterval
    (a b C : Rat) (n : Nat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (normalizedMonomialOnInterval a b n)
      (monomialOnInterval a b n) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := normalizedMonomialStepPrecision C n
  evalPrecision := fun _x _h _stage => 0
  close := by
    intro x h stage hx hxh _hdx hh hsmall
    have hC0 : 0 <= C := Rat.le_trans (by native_decide) hC1
    have hxleft : -C <= x := Rat.le_trans hleft hx.1
    have hxright : x <= C := Rat.le_trans hx.2 hright
    have hxhleft : -C <= x + h := Rat.le_trans hleft hxh.1
    have hxhright : x + h <= C := Rat.le_trans hxh.2 hright
    have hxbound : qabs x <= C := qabs_le_of_neg_le_le hxleft hxright
    have hxhbound : qabs (x + h) <= C :=
      qabs_le_of_neg_le_le hxhleft hxhright
    have hfinite := qabs_normalized_power_differenceQuotient_sub_monomial_le
      (x := x) (h := h) (C := C) hh hC0 hC1 hxbound hxhbound n
    have hstep := normalizedMonomial_step_error_le_precision
      (C := C) (h := h) hC0 n stage hsmall
    have herror :
        qabs
            ((((x + h) ^ (n + 1) / ((n + 1 : Nat) : Rat)) -
              x ^ (n + 1) / ((n + 1 : Nat) : Rat)) / h - x ^ n) <=
          (precisionAtStage stage).val :=
      Rat.le_trans hfinite hstep
    let q : Rat :=
      (((x + h) ^ (n + 1) / ((n + 1 : Nat) : Rat) -
        x ^ (n + 1) / ((n + 1 : Nat) : Rat)) / h)
    have heps0 : 0 <= (precisionAtStage stage).val :=
      Rat.le_of_lt (precisionAtStage stage).property
    have hupper : q - x ^ n <= (precisionAtStage stage).val := by
      calc
        q - x ^ n <= qabs (q - x ^ n) := self_le_qabs _
        _ <= (precisionAtStage stage).val := by
          simpa [q] using herror
    have hlower : -(q - x ^ n) <= (precisionAtStage stage).val := by
      calc
        -(q - x ^ n) <= qabs (-(q - x ^ n)) := self_le_qabs _
        _ = qabs (q - x ^ n) := qabs_neg _
        _ <= (precisionAtStage stage).val := by
          simpa [q] using herror
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        { lo := (x + h) ^ (n + 1) / ((n + 1 : Nat) : Rat),
          hi := (x + h) ^ (n + 1) / ((n + 1 : Nat) : Rat) }
        { lo := x ^ (n + 1) / ((n + 1 : Nat) : Rat),
          hi := x ^ (n + 1) / ((n + 1 : Nat) : Rat) } h)
      { lo := x ^ n, hi := x ^ n } stage
    rw [QInterval.differenceQuotient_singleton]
    unfold intervalNearAtPrecision QInterval.NearAt QInterval.width
    constructor
    · change q <= x ^ n + (precisionAtStage stage).val
      grind [Rat.sub_eq_add_neg]
    constructor
    · change x ^ n <= q + (precisionAtStage stage).val
      grind [Rat.sub_eq_add_neg]
    constructor <;> grind [Rat.sub_eq_add_neg]

end FinitePolynomial

end ComputableAnalysis
