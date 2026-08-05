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
  error_bound : forall x h : Rat, h ≠ 0 ->
    qabs x <= C -> qabs (x + h) <= C ->
    qabs (((f (x + h) - f x) / h) - df x) <=
      qabs h * errorCoefficient

/-- A quantitative secant bound on a box centered at a rational expansion
point.  This is the translated form of `SecantDerivativeBound`; its local
coordinate is `x - basepoint`. -/
structure CenteredSecantDerivativeBound (basepoint C : Rat)
    (f df : Rat -> Rat) where
  errorCoefficient : Rat
  errorCoefficient_nonneg : 0 <= errorCoefficient
  error_bound : forall x h : Rat, h ≠ 0 ->
    qabs (x - basepoint) <= C -> qabs (x + h - basepoint) <= C ->
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
      rw [Rat.sub_self, Rat.div_def, Rat.zero_mul]
      grind [Rat.sub_eq_add_neg]
    rw [hzero, qabs_eq_self_of_nonneg (by native_decide), Rat.mul_zero]
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
    calc
      qabs r * qabs (((f (x + h) - f x) / h) - df x) <=
          qabs r * (qabs h * F.errorCoefficient) :=
        Rat.mul_le_mul_of_nonneg_left hF (qabs_nonneg _)
      _ = qabs h * (qabs r * F.errorCoefficient) := by
        grind [Rat.mul_assoc, Rat.mul_comm]

/-- Quantitative secant bounds are closed under products when rational local
majorants for each factor and its proposed derivative are supplied.

The final term of the coefficient is the finite ``corner rectangle'': the
two secant quotients are bounded using `|h| <= 2C` on the symmetric box. -/
def mul {C : Rat} {f df g dg : Rat -> Rat}
    (F : SecantDerivativeBound C f df)
    (G : SecantDerivativeBound C g dg)
    (fMajorant dfMajorant gMajorant dgMajorant : Rat)
    (hfMajorant : forall x, qabs x <= C -> qabs (f x) <= fMajorant)
    (hdfMajorant : forall x, qabs x <= C -> qabs (df x) <= dfMajorant)
    (hgMajorant : forall x, qabs x <= C -> qabs (g x) <= gMajorant)
    (hdgMajorant : forall x, qabs x <= C -> qabs (dg x) <= dgMajorant)
    (hC0 : 0 <= C) (hf0 : 0 <= fMajorant) (hdf0 : 0 <= dfMajorant)
    (hg0 : 0 <= gMajorant) (hdg0 : 0 <= dgMajorant) :
    SecantDerivativeBound C
      (fun x => f x * g x)
      (fun x => f x * dg x + g x * df x) where
  errorCoefficient :=
    fMajorant * G.errorCoefficient + gMajorant * F.errorCoefficient +
      (dfMajorant + 2 * C * F.errorCoefficient) *
        (dgMajorant + 2 * C * G.errorCoefficient)
  errorCoefficient_nonneg := by
    apply Rat.add_nonneg
    · apply Rat.add_nonneg
      · exact Rat.mul_nonneg hf0 G.errorCoefficient_nonneg
      · exact Rat.mul_nonneg hg0 F.errorCoefficient_nonneg
    · apply Rat.mul_nonneg
      · exact Rat.add_nonneg hdf0
          (Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) hC0)
            F.errorCoefficient_nonneg)
      · exact Rat.add_nonneg hdg0
          (Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) hC0)
            G.errorCoefficient_nonneg)
  error_bound := by
    intro x h hh hx hxh
    let qf : Rat := (f (x + h) - f x) / h
    let qg : Rat := (g (x + h) - g x) / h
    have hstep : qabs h <= 2 * C := by
      have hrewrite : h = (x + h) - x := by
        grind [Rat.sub_eq_add_neg]
      rw [hrewrite]
      calc
        qabs ((x + h) - x) <= qabs (x + h) + qabs x := qabs_sub_le _ _
        _ <= C + C := rat_add_le_add hxh hx
        _ = 2 * C := by grind
    have hF := F.error_bound x h hh hx hxh
    have hG := G.error_bound x h hh hx hxh
    have hqf : qabs qf <= dfMajorant + 2 * C * F.errorCoefficient := by
      have hq : qabs qf <= qabs (qf - df x) + qabs (df x) := by
        calc
          qabs qf = qabs ((qf - df x) + df x) := by
            congr 1
            grind [Rat.sub_eq_add_neg]
          _ <= qabs (qf - df x) + qabs (df x) := qabs_add_le _ _
      have hF' : qabs (qf - df x) <= qabs h * F.errorCoefficient := by
        simpa [qf] using hF
      have hstepF : qabs h * F.errorCoefficient <=
          2 * C * F.errorCoefficient :=
        Rat.mul_le_mul_of_nonneg_right hstep F.errorCoefficient_nonneg
      calc
        qabs qf <= qabs (qf - df x) + qabs (df x) := hq
        _ <= qabs h * F.errorCoefficient + dfMajorant :=
          rat_add_le_add hF' (hdfMajorant x hx)
        _ <= 2 * C * F.errorCoefficient + dfMajorant :=
          rat_add_le_add hstepF Rat.le_refl
        _ = dfMajorant + 2 * C * F.errorCoefficient := by
          grind [Rat.add_comm]
    have hqg : qabs qg <= dgMajorant + 2 * C * G.errorCoefficient := by
      have hq : qabs qg <= qabs (qg - dg x) + qabs (dg x) := by
        calc
          qabs qg = qabs ((qg - dg x) + dg x) := by
            congr 1
            grind [Rat.sub_eq_add_neg]
          _ <= qabs (qg - dg x) + qabs (dg x) := qabs_add_le _ _
      have hG' : qabs (qg - dg x) <= qabs h * G.errorCoefficient := by
        simpa [qg] using hG
      have hstepG : qabs h * G.errorCoefficient <=
          2 * C * G.errorCoefficient :=
        Rat.mul_le_mul_of_nonneg_right hstep G.errorCoefficient_nonneg
      calc
        qabs qg <= qabs (qg - dg x) + qabs (dg x) := hq
        _ <= qabs h * G.errorCoefficient + dgMajorant :=
          rat_add_le_add hG' (hdgMajorant x hx)
        _ <= 2 * C * G.errorCoefficient + dgMajorant :=
          rat_add_le_add hstepG Rat.le_refl
        _ = dgMajorant + 2 * C * G.errorCoefficient := by
          grind [Rat.add_comm]
    have htermF :
        qabs (f x) * qabs (qg - dg x) <=
          qabs h * (fMajorant * G.errorCoefficient) := by
      calc
        qabs (f x) * qabs (qg - dg x) <=
            fMajorant * qabs (qg - dg x) :=
          Rat.mul_le_mul_of_nonneg_right (hfMajorant x hx) (qabs_nonneg _)
        _ <= fMajorant * (qabs h * G.errorCoefficient) :=
          Rat.mul_le_mul_of_nonneg_left (by simpa [qg] using hG) hf0
        _ = qabs h * (fMajorant * G.errorCoefficient) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    have htermG :
        qabs (g x) * qabs (qf - df x) <=
          qabs h * (gMajorant * F.errorCoefficient) := by
      calc
        qabs (g x) * qabs (qf - df x) <=
            gMajorant * qabs (qf - df x) :=
          Rat.mul_le_mul_of_nonneg_right (hgMajorant x hx) (qabs_nonneg _)
        _ <= gMajorant * (qabs h * F.errorCoefficient) :=
          Rat.mul_le_mul_of_nonneg_left (by simpa [qf] using hF) hg0
        _ = qabs h * (gMajorant * F.errorCoefficient) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    have htermQ :
        qabs h * qabs qf * qabs qg <=
          qabs h * ((dfMajorant + 2 * C * F.errorCoefficient) *
            (dgMajorant + 2 * C * G.errorCoefficient)) := by
      have hproduct : qabs qf * qabs qg <=
          (dfMajorant + 2 * C * F.errorCoefficient) *
            (dgMajorant + 2 * C * G.errorCoefficient) := by
        calc
          qabs qf * qabs qg <=
              (dfMajorant + 2 * C * F.errorCoefficient) * qabs qg :=
            Rat.mul_le_mul_of_nonneg_right hqf (qabs_nonneg _)
          _ <= (dfMajorant + 2 * C * F.errorCoefficient) *
              (dgMajorant + 2 * C * G.errorCoefficient) :=
            Rat.mul_le_mul_of_nonneg_left hqg
              (Rat.add_nonneg hdf0
                (Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) hC0)
                  F.errorCoefficient_nonneg))
      calc
        qabs h * qabs qf * qabs qg = qabs h * (qabs qf * qabs qg) := by
          rw [Rat.mul_assoc]
        _ <= qabs h * ((dfMajorant + 2 * C * F.errorCoefficient) *
            (dgMajorant + 2 * C * G.errorCoefficient)) :=
          Rat.mul_le_mul_of_nonneg_left hproduct (qabs_nonneg _)
    have hproduct := ExactFunction.product_differenceQuotient_error_le_qabs
      f df g dg x h hh
    calc
      qabs (((f (x + h) * g (x + h) - f x * g x) / h) -
          (f x * dg x + g x * df x)) <=
          qabs (f x) * qabs (qg - dg x) +
            qabs (g x) * qabs (qf - df x) +
              qabs h * qabs qf * qabs qg := by
            simpa [qf, qg] using hproduct
      _ <= qabs h * (fMajorant * G.errorCoefficient) +
            qabs h * (gMajorant * F.errorCoefficient) +
              qabs h * ((dfMajorant + 2 * C * F.errorCoefficient) *
                (dgMajorant + 2 * C * G.errorCoefficient)) := by
            exact rat_add_le_add (rat_add_le_add htermF htermG) htermQ
      _ = qabs h *
          (fMajorant * G.errorCoefficient + gMajorant * F.errorCoefficient +
            (dfMajorant + 2 * C * F.errorCoefficient) *
              (dgMajorant + 2 * C * G.errorCoefficient)) := by
            grind [Rat.mul_add, Rat.mul_assoc, Rat.add_assoc]

/-- Translation of the input leaves a quantitative secant bound unchanged.
This is the finite algebra needed to use a Taylor polynomial at its declared
rational expansion point instead of only at zero. -/
def translate (a : Rat) {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df) :
    CenteredSecantDerivativeBound a C
      (fun x => f (x - a))
      (fun x => df (x - a)) where
  errorCoefficient := F.errorCoefficient
  errorCoefficient_nonneg := F.errorCoefficient_nonneg
  error_bound := by
    intro x h hh hx hxh
    have hshift : (x - a) + h = (x + h) - a := by
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    have hF := F.error_bound (x - a) h hh hx (by
      rw [hshift]
      exact hxh)
    simpa [hshift] using hF

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

namespace CenteredSecantDerivativeBound

/-- The same explicit dyadic schedule works on a translated box, because a
translation changes neither the step nor the quantitative error coefficient. -/
def stepPrecision {basepoint C : Rat} {f df : Rat -> Rat}
    (F : CenteredSecantDerivativeBound basepoint C f df) (stage : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift F.errorCoefficient
    (precisionAtStage stage)

private theorem step_error_le_precision
    {basepoint C : Rat} {f df : Rat -> Rat}
    (F : CenteredSecantDerivativeBound basepoint C f df) {h : Rat} (stage : Nat)
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

/-- A translated quantitative secant bound gives a two-sided interval
derivative certificate on any rational interval lying in its local box. -/
def toHasDerivativeOnInterval {basepoint C : Rat} {f df : Rat -> Rat}
    (F : CenteredSecantDerivativeBound basepoint C f df)
    (a b : Rat) (hleft : -C <= a - basepoint)
    (hright : b - basepoint <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat f a b)
      (FunctionOnInterval.exactRat df a b) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := F.stepPrecision
  evalPrecision := fun _x _h _stage => 0
  close := by
    intro x h stage hx hxh _hdx hh hsmall
    change a <= x /\ x <= b at hx
    change a <= x + h /\ x + h <= b at hxh
    have hxleft : -C <= x - basepoint := by
      calc
        -C <= a - basepoint := hleft
        _ <= x - basepoint := by grind [Rat.sub_eq_add_neg]
    have hxright : x - basepoint <= C := by
      calc
        x - basepoint <= b - basepoint := by grind [Rat.sub_eq_add_neg]
        _ <= C := hright
    have hxhleft : -C <= x + h - basepoint := by
      calc
        -C <= a - basepoint := hleft
        _ <= x + h - basepoint := by grind [Rat.sub_eq_add_neg]
    have hxhright : x + h - basepoint <= C := by
      calc
        x + h - basepoint <= b - basepoint := by grind [Rat.sub_eq_add_neg]
        _ <= C := hright
    have hxbound : qabs (x - basepoint) <= C :=
      qabs_le_of_neg_le_le hxleft hxright
    have hxhbound : qabs (x + h - basepoint) <= C :=
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

end CenteredSecantDerivativeBound

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
  change SecantDerivativeBound C (fun x => 1 + x + x * x / 2) (fun x => 1 + x)
  have hinvone : ((1 : Rat)⁻¹) = 1 := by native_decide
  simpa [Rat.pow_succ, Rat.div_def, Rat.zero_add, Rat.mul_assoc, hinvone] using
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

/-- The finite primitive prefix generated by rational derivative coefficients.
The `k`th coefficient contributes `c_k x^(k+1)/(k+1)`. -/
def integratedTaylorPrefix (coeffs : Nat -> Rat) : Nat -> Rat -> Rat
  | 0 => fun _x => 0
  | n + 1 => fun x =>
      integratedTaylorPrefix coeffs n x +
        coeffs n * (x ^ (n + 1) / ((n + 1 : Nat) : Rat))

/-- The corresponding finite derivative prefix `sum_{k<n} c_k x^k`. -/
def taylorDerivativePrefix (coeffs : Nat -> Rat) : Nat -> Rat -> Rat
  | 0 => fun _x => 0
  | n + 1 => fun x =>
      taylorDerivativePrefix coeffs n x + coeffs n * x ^ n

/-- The finite polynomial formed from the first `terms` coefficients of a
formal Taylor stream.

The constant coefficient is retained explicitly; all higher terms are the
finite primitive of the stream's algebraic coefficient shift.  Thus this is
only rational polynomial evaluation, even when `coeffs` later belongs to an
infinite series. -/
def taylorPrefix (coeffs : FormalPowerSeries.Coeffs) : Nat -> Rat -> Rat
  | 0 => fun _x => 0
  | terms + 1 => fun x =>
      coeffs 0 +
        integratedTaylorPrefix
          (FormalPowerSeries.coefficientShift coeffs) terms x

/-- The finite coefficient-shift polynomial paired with `taylorPrefix`.
For `terms + 1`, it is the literal derivative polynomial of the displayed
finite prefix; no statement about an infinite tail is made here. -/
def taylorPrefixShift (coeffs : FormalPowerSeries.Coeffs) : Nat -> Rat -> Rat
  | 0 => fun _x => 0
  | terms + 1 =>
      taylorDerivativePrefix (FormalPowerSeries.coefficientShift coeffs) terms

/-- A finite Taylor polynomial centered at the rational point `a`.

The coefficient stream remains the usual stream in powers of `(x - a)`, so
the linear coefficient has the same local meaning at every rational center. -/
def taylorPrefixAt (a : Rat) (coeffs : FormalPowerSeries.Coeffs)
    (terms : Nat) (x : Rat) : Rat :=
  taylorPrefix coeffs terms (x - a)

/-- The coefficient-shift polynomial paired with `taylorPrefixAt`. -/
def taylorPrefixShiftAt (a : Rat) (coeffs : FormalPowerSeries.Coeffs)
    (terms : Nat) (x : Rat) : Rat :=
  taylorPrefixShift coeffs terms (x - a)

/-- At the basepoint, every nonconstant finite derivative prefix is its
constant coefficient.  This elementary identity is the exact algebraic core
of reading the linear Taylor coefficient as the slope at zero. -/
theorem taylorDerivativePrefix_at_zero (coeffs : Nat -> Rat) (terms : Nat) :
    taylorDerivativePrefix coeffs (terms + 1) 0 = coeffs 0 := by
  induction terms with
  | zero =>
      change 0 + coeffs 0 * 0 ^ 0 = coeffs 0
      rw [Rat.pow_zero, Rat.mul_one]
      exact Rat.zero_add _
  | succ terms ih =>
      rw [taylorDerivativePrefix]
      change taylorDerivativePrefix coeffs (terms + 1) 0 +
          coeffs (terms + 1) * 0 ^ (terms + 1) = coeffs 0
      rw [ih, Rat.pow_succ, Rat.mul_zero, Rat.mul_zero]
      exact Rat.add_zero _

/-- For a finite Taylor prefix with at least a linear term, the certified
coefficient-shift derivative has value `c₁` at the basepoint.  The analytic
certificate itself is supplied below by `taylorPrefix_hasDerivativeOnInterval`;
this theorem records the value selected by the finite Lagrange remainder. -/
theorem taylorPrefixShift_at_zero (coeffs : FormalPowerSeries.Coeffs)
    (terms : Nat) :
    taylorPrefixShift coeffs (terms + 2) 0 = coeffs 1 := by
  rw [show terms + 2 = (terms + 1) + 1 by omega]
  rw [taylorPrefixShift, taylorDerivativePrefix_at_zero]
  simp [FormalPowerSeries.coefficientShift]

/-- The coefficient-shift polynomial of a finite Taylor expansion takes the
value `c₁` at its declared rational basepoint. -/
theorem taylorPrefixShiftAt_at_basepoint (a : Rat)
    (coeffs : FormalPowerSeries.Coeffs) (terms : Nat) :
    taylorPrefixShiftAt a coeffs (terms + 2) a = coeffs 1 := by
  unfold taylorPrefixShiftAt
  rw [Rat.sub_self]
  exact taylorPrefixShift_at_zero coeffs terms

/-- Every finite rational Taylor primitive carries an explicit secant bound.
The proof is structural: add the next normalized monomial, then scale it by
its rational coefficient. -/
def integratedTaylorPrefixSecantBound (C : Rat) (coeffs : Nat -> Rat)
    (hC1 : 1 <= C) : (n : Nat) ->
    SecantDerivativeBound C
      (integratedTaylorPrefix coeffs n)
      (taylorDerivativePrefix coeffs n)
  | 0 => SecantDerivativeBound.constant C 0
  | n + 1 => by
      simpa [integratedTaylorPrefix, taylorDerivativePrefix] using
        SecantDerivativeBound.add
          (integratedTaylorPrefixSecantBound C coeffs hC1 n)
          (SecantDerivativeBound.scaleRat (coeffs n)
            (normalizedMonomialSecantBound C n hC1))

/-- A finite rational Taylor primitive has its literal finite coefficient
prefix as a two-sided interval derivative on every subinterval of `[-C,C]`. -/
def integratedTaylorPrefix_hasDerivativeOnInterval
    (coeffs : Nat -> Rat) (n : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (integratedTaylorPrefix coeffs n) a b)
      (FunctionOnInterval.exactRat (taylorDerivativePrefix coeffs n) a b) :=
  (integratedTaylorPrefixSecantBound C coeffs hC1 n).toHasDerivativeOnInterval
    a b hleft hright

/-- Every finite Taylor prefix carries the explicit secant bound supplied by
its coefficient shift.  This is the reusable Taylor--Lagrange bridge for a
finite polynomial: the analytic-looking derivative claim is justified by a
rational `|h|` remainder coefficient. -/
def taylorPrefixSecantBound (C : Rat) (coeffs : FormalPowerSeries.Coeffs)
    (hC1 : 1 <= C) : (terms : Nat) ->
    SecantDerivativeBound C
      (taylorPrefix coeffs terms)
      (taylorPrefixShift coeffs terms)
  | 0 => SecantDerivativeBound.constant C 0
  | terms + 1 => by
      simpa [taylorPrefix, taylorPrefixShift, Rat.zero_add] using
        SecantDerivativeBound.add
          (SecantDerivativeBound.constant C (coeffs 0))
          (integratedTaylorPrefixSecantBound C
            (FormalPowerSeries.coefficientShift coeffs) hC1 terms)

/-- A finite Taylor coefficient prefix has its coefficient-shift polynomial
as a two-sided interval derivative on every rational subinterval of a
bounded symmetric box. -/
def taylorPrefix_hasDerivativeOnInterval
    (coeffs : FormalPowerSeries.Coeffs) (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (taylorPrefix coeffs terms) a b)
      (FunctionOnInterval.exactRat (taylorPrefixShift coeffs terms) a b) :=
  (taylorPrefixSecantBound C coeffs hC1 terms).toHasDerivativeOnInterval
    a b hleft hright

/-- The finite Taylor--Lagrange secant bound transports to any rational
expansion point.  The symmetric box is expressed in the local coordinate
`x - basepoint`. -/
def taylorPrefixAtSecantBound (C basepoint : Rat)
    (coeffs : FormalPowerSeries.Coeffs) (hC1 : 1 <= C) (terms : Nat) :
    CenteredSecantDerivativeBound basepoint C
      (taylorPrefixAt basepoint coeffs terms)
      (taylorPrefixShiftAt basepoint coeffs terms) := by
  simpa [taylorPrefixAt, taylorPrefixShiftAt] using
    SecantDerivativeBound.translate basepoint
      (taylorPrefixSecantBound C coeffs hC1 terms)

/-- A finite Taylor polynomial centered at any rational basepoint has the
coefficient-shift polynomial as its interval derivative.  Together with
`taylorPrefixShiftAt_at_basepoint`, this makes `c₁` an actual certified slope
at the point where the expansion is centered. -/
def taylorPrefixAt_hasDerivativeOnInterval
    (basepoint : Rat) (coeffs : FormalPowerSeries.Coeffs)
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a - basepoint) (hright : b - basepoint <= C)
    (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (taylorPrefixAt basepoint coeffs terms) a b)
      (FunctionOnInterval.exactRat (taylorPrefixShiftAt basepoint coeffs terms) a b) :=
  CenteredSecantDerivativeBound.toHasDerivativeOnInterval
    (taylorPrefixAtSecantBound C basepoint coeffs hC1 terms)
    a b hleft hright

/-- The ordinary finite factorial-series prefix for exponential. -/
def expTaylorPrefix (n : Nat) (x : Rat) : Rat :=
  1 + integratedTaylorPrefix FormalPowerSeries.expCoeff n x

/-- The factorial-series prefix one degree lower, the derivative of
`expTaylorPrefix n`. -/
def expTaylorDerivativePrefix (n : Nat) (x : Rat) : Rat :=
  taylorDerivativePrefix FormalPowerSeries.expCoeff n x

/-- A finite factorial Taylor prefix for exponential has the expected
one-degree-lower prefix as its derivative. -/
def expTaylorPrefixSecantBound (C : Rat) (n : Nat) (hC1 : 1 <= C) :
    SecantDerivativeBound C (expTaylorPrefix n) (expTaylorDerivativePrefix n) := by
  simpa [expTaylorPrefix, expTaylorDerivativePrefix, Rat.zero_add] using
    SecantDerivativeBound.add
      (SecantDerivativeBound.constant C 1)
      (integratedTaylorPrefixSecantBound C FormalPowerSeries.expCoeff hC1 n)

/-- The finite factorial Taylor prefixes used by exponential satisfy the
two-sided interval derivative interface before the separately certified
factorial tail is attached. -/
def expTaylorPrefix_hasDerivativeOnInterval
    (n : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (expTaylorPrefix n) a b)
      (FunctionOnInterval.exactRat (expTaylorDerivativePrefix n) a b) :=
  (expTaylorPrefixSecantBound C n hC1).toHasDerivativeOnInterval
    a b hleft hright

end FinitePolynomial

end ComputableAnalysis
