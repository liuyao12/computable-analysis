import ComputableAnalysis.Differential
import ComputableAnalysis.Exp
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

/-- A quantitative rational finite-difference certificate on the symmetric
box `[-C,C]`.

Unlike a bare derivative assertion, this records the explicit coefficient of
`|h|` in the secant error.  That is precisely the datum that survives finite
addition and rational scaling, and that later gives an executable dyadic
step schedule. -/
structure SecantDerivativeBound (C : Rat) (f df : Rat -> Rat) where
  errorCoefficient : Rat
  errorCoefficient_nonneg : 0 <= errorCoefficient
  error_bound : forall x h : Rat, h != 0 ->
    qabs x <= C -> qabs (x + h) <= C ->
    qabs (((f (x + h) - f x) / h) - df x) <=
      qabs h * errorCoefficient

namespace SecantDerivativeBound

/-- Constants have zero finite-difference error. -/
def constant (C c : Rat) : SecantDerivativeBound C (fun _x => c) (fun _x => 0) where
  errorCoefficient := 0
  errorCoefficient_nonneg := by native_decide
  error_bound := by
    intro x h _hh _hx _hxh
    have hzero : (((c - c) / h) - 0 : Rat) = 0 := by
      rw [Rat.sub_self, Rat.zero_div, Rat.zero_sub]
    rw [hzero, qabs_eq_self_of_nonneg (by native_decide)]
    exact Rat.le_refl

/-- Quantitative secant bounds are closed under finite addition. -/
def add {C : Rat} {f df g dg : Rat -> Rat}
    (F : SecantDerivativeBound C f df)
    (G : SecantDerivativeBound C g dg) :
    SecantDerivativeBound C
      (fun x => f x + g x)
      (fun x => df x + dg x) where
  errorCoefficient := F.errorCoefficient + G.errorCoefficient
  errorCoefficient_nonneg := Rat.add_nonneg F.errorCoefficient_nonneg
    G.errorCoefficient_nonneg
  error_bound := by
    intro x h hh hx hxh
    have hF := F.error_bound x h hh hx hxh
    have hG := G.error_bound x h hh hx hxh
    have hsplit :
        (((f (x + h) + g (x + h) - (f x + g x)) / h) -
            (df x + dg x)) =
          (((f (x + h) - f x) / h) - df x) +
            (((g (x + h) - g x) / h) - dg x) := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.add_assoc, Rat.add_comm, Rat.mul_comm]
    rw [hsplit]
    calc
      qabs
          ((((f (x + h) - f x) / h) - df x) +
            (((g (x + h) - g x) / h) - dg x)) <=
          qabs (((f (x + h) - f x) / h) - df x) +
            qabs (((g (x + h) - g x) / h) - dg x) :=
        qabs_add_le _ _
      _ <= qabs h * F.errorCoefficient + qabs h * G.errorCoefficient :=
        rat_add_le_add hF hG
      _ = qabs h * (F.errorCoefficient + G.errorCoefficient) := by
        grind [Rat.mul_add]

/-- Quantitative secant bounds are closed under rational scaling. -/
def scaleRat (r : Rat) {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df) :
    SecantDerivativeBound C
      (fun x => r * f x)
      (fun x => r * df x) where
  errorCoefficient := qabs r * F.errorCoefficient
  errorCoefficient_nonneg := Rat.mul_nonneg (qabs_nonneg _)
    F.errorCoefficient_nonneg
  error_bound := by
    intro x h hh hx hxh
    have hF := F.error_bound x h hh hx hxh
    have hsplit :
        (((r * f (x + h) - r * f x) / h) - r * df x) =
          r * (((f (x + h) - f x) / h) - df x) := by
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.add_assoc, Rat.add_comm, Rat.mul_comm]
    rw [hsplit, qabs_mul]
    exact Rat.mul_le_mul_of_nonneg_left hF (qabs_nonneg _)

/-- The dyadic schedule selected by a quantitative secant coefficient. -/
def stepPrecision {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df) (stage : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift F.errorCoefficient
    (precisionAtStage stage)

private theorem step_error_le_precision
    {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df) {h : Rat} (stage : Nat)
    (hsmall : qabs h <= 1 / ((F.stepPrecision stage : Nat) : Rat)) :
    qabs h * F.errorCoefficient <= (precisionAtStage stage).val := by
  let shift : Nat := RationalMajorant.halfDecayShift F.errorCoefficient
    (precisionAtStage stage)
  have hsmall' : qabs h <= 1 / (((2 ^ shift : Nat) : Rat)) := by
    simpa [stepPrecision, shift] using hsmall
  have hscaled : qabs h * F.errorCoefficient <=
      1 / (((2 ^ shift : Nat) : Rat)) * F.errorCoefficient :=
    Rat.mul_le_mul_of_nonneg_right hsmall' F.errorCoefficient_nonneg
  have hgeometric : F.errorCoefficient * ((1 : Rat) / 2) ^ shift <=
      (precisionAtStage stage).val := by
    simpa [shift] using RationalMajorant.halfDecayShift_spec
      F.errorCoefficient_nonneg (precisionAtStage stage)
  calc
    qabs h * F.errorCoefficient <=
        1 / (((2 ^ shift : Nat) : Rat)) * F.errorCoefficient := hscaled
    _ = F.errorCoefficient * ((1 : Rat) / 2) ^ shift := by
      rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
      grind [Rat.mul_comm]
    _ <= (precisionAtStage stage).val := hgeometric

/-- Package a quantitative rational secant bound as the project's two-sided
interval derivative certificate on any subinterval of its symmetric box. -/
def toHasDerivativeOnInterval {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df)
    (a b : Rat) (hleft : -C <= a) (hright : b <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat f a b)
      (FunctionOnInterval.exactRat df a b) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := F.stepPrecision
  evalPrecision := fun _x _h _stage => 0
  close := by
    intro x h stage hx hxh _hdx hh hsmall
    have hxleft : -C <= x := Rat.le_trans hleft hx.1
    have hxright : x <= C := Rat.le_trans hx.2 hright
    have hxhleft : -C <= x + h := Rat.le_trans hleft hxh.1
    have hxhright : x + h <= C := Rat.le_trans hxh.2 hright
    have hxbound : qabs x <= C := qabs_le_of_neg_le_le hxleft hxright
    have hxhbound : qabs (x + h) <= C :=
      qabs_le_of_neg_le_le hxhleft hxhright
    have hfinite := F.error_bound x h hh hxbound hxhbound
    have hstep := F.step_error_le_precision stage hsmall
    have herror : qabs (((f (x + h) - f x) / h) - df x) <=
        (precisionAtStage stage).val :=
      Rat.le_trans hfinite hstep
    let q : Rat := (f (x + h) - f x) / h
    have hupper : q - df x <= (precisionAtStage stage).val := by
      calc
        q - df x <= qabs (q - df x) := self_le_qabs _
        _ <= (precisionAtStage stage).val := by simpa [q] using herror
    have hlower : -(q - df x) <= (precisionAtStage stage).val := by
      calc
        -(q - df x) <= qabs (-(q - df x)) := self_le_qabs _
        _ = qabs (q - df x) := qabs_neg _
        _ <= (precisionAtStage stage).val := by simpa [q] using herror
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        { lo := f (x + h), hi := f (x + h) }
        { lo := f x, hi := f x } h)
      { lo := df x, hi := df x } stage
    rw [QInterval.differenceQuotient_singleton]
    unfold intervalNearAtPrecision QInterval.NearAt QInterval.width
    constructor
    · change q <= df x + (precisionAtStage stage).val
      grind [Rat.sub_eq_add_neg]
    constructor
    · change df x <= q + (precisionAtStage stage).val
      grind [Rat.sub_eq_add_neg]
    constructor <;> grind [Rat.sub_eq_add_neg]

end SecantDerivativeBound

/-- The monomial secant estimate as reusable quantitative data. -/
def normalizedMonomialSecantBound (C : Rat) (n : Nat) (hC1 : 1 <= C) :
    SecantDerivativeBound C
      (fun x => x ^ (n + 1) / ((n + 1 : Nat) : Rat))
      (fun x => x ^ n) where
  errorCoefficient := powerSecantErrorBound C (n + 1)
  errorCoefficient_nonneg :=
    powerSecantErrorBound_nonneg
      (Rat.le_trans (by native_decide) hC1) _
  error_bound := by
    intro x h hh hx hxh
    exact qabs_normalized_power_differenceQuotient_sub_monomial_le
      (x := x) (h := h) (C := C) hh
      (Rat.le_trans (by native_decide) hC1) hC1 hx hxh n

/-- Every normalized monomial has a two-sided rational interval derivative on
any interval contained in `[-C,C]`, provided `C >= 1`.  The proof is the
literal finite quotient estimate with a dyadic schedule chosen from its
explicit error coefficient. -/
def normalizedMonomial_hasDerivativeOnInterval
    (a b C : Rat) (n : Nat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (normalizedMonomialOnInterval a b n)
      (monomialOnInterval a b n) := by
  simpa [normalizedMonomialOnInterval, monomialOnInterval,
    normalizedMonomialStepPrecision, SecantDerivativeBound.stepPrecision]
    using (normalizedMonomialSecantBound C n hC1).toHasDerivativeOnInterval
      a b hleft hright

/-- The degree-two Taylor prefix of exponential has the expected derivative
on every rational interval inside a bounded symmetric box.  This is the first
nontrivial finite Taylor polynomial assembled through the quantitative linear
interface, rather than by a separate hand-written quotient calculation. -/
def expTaylorQuadraticSecantBound (C : Rat) (hC1 : 1 <= C) :
    SecantDerivativeBound C expTaylorQuadratic (fun x => 1 + x) := by
  simpa [expTaylorQuadratic, pow_two] using
    SecantDerivativeBound.add
      (SecantDerivativeBound.add
        (SecantDerivativeBound.constant C 1)
        (normalizedMonomialSecantBound C 0 hC1))
      (normalizedMonomialSecantBound C 1 hC1)

/-- The literal quadratic exponential prefix satisfies
`d/dx (1 + x + x^2/2) = 1 + x` in the project’s two-sided interval
finite-difference sense. -/
def expTaylorQuadratic_hasDerivativeOnInterval
    (a b C : Rat) (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat expTaylorQuadratic a b)
      (FunctionOnInterval.exactRat (fun x => 1 + x) a b) :=
  (expTaylorQuadraticSecantBound C hC1).toHasDerivativeOnInterval
    a b hleft hright

end FinitePolynomial

end ComputableAnalysis
