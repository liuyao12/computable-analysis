import ComputableAnalysis.FiniteDerivativeLimit

/-! Quantitative change of variables for primitive evaluators.
This is the focused composition core of the workspace's DifferentialComposition
module, with closed rational checks kernel-verified. The certificate records
executable witnesses and approximation budgets; it does not assume the
composite derivative conclusion. No nonzero inner increment is required.
-/
namespace ComputableAnalysis
namespace PrimitiveChangeOfVariables

theorem rationalCompositionSecant_error_identity
    (outerBase outerStep outerDerivative
      innerBase innerStep innerDerivative h : Rat) :
    (outerStep - outerBase) / h - outerDerivative * innerDerivative =
      ((outerStep - outerBase) -
          outerDerivative * (innerStep - innerBase)) / h +
        outerDerivative *
          (((innerStep - innerBase) / h) - innerDerivative) := by
  rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

/-- Convert an ordinary secant-error estimate into the division-free outer
linearization residual consumed by the composition rule. -/
theorem secantError_to_linearizationError
    (base step derivative increment eps : Rat) (hincrement : increment ≠ 0)
    (hsecant : qabs (((step - base) / increment) - derivative) <= eps) :
    qabs ((step - base) - derivative * increment) <=
      eps * qabs increment := by
  have hid :
      (step - base) - derivative * increment =
        (((step - base) / increment) - derivative) * increment := by
    rw [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel increment hincrement]
  rw [hid, qabs_mul]
  exact Rat.mul_le_mul_of_nonneg_right hsecant (qabs_nonneg increment)

/-- Quantitative chain-rule estimate.  Half of the requested error is paid by
the outer first-order residual and half by the inner secant error. -/
theorem rationalCompositionSecant_error_le
    (outerBase outerStep outerDerivative
      innerBase innerStep innerDerivative h eps bound : Rat)
    (hh : h ≠ 0) (hbound : 0 < bound)
    (houterDerivative : qabs outerDerivative <= bound)
    (houter :
      qabs ((outerStep - outerBase) -
        outerDerivative * (innerStep - innerBase)) <=
          eps * qabs h / 2)
    (hinner :
      qabs (((innerStep - innerBase) / h) - innerDerivative) <=
        eps / (2 * bound)) :
    qabs (((outerStep - outerBase) / h) -
      outerDerivative * innerDerivative) <= eps := by
  let residual := (outerStep - outerBase) -
    outerDerivative * (innerStep - innerBase)
  let innerError := ((innerStep - innerBase) / h) - innerDerivative
  have hhabs : qabs h ≠ 0 := by
    exact Rat.ne_of_gt (qabs_pos_of_ne hh)
  have habsCancel : qabs h * qabs (1 / h) = 1 := by
    rw [← qabs_mul]
    have hcancel : h * (1 / h) = 1 := by
      rw [Rat.div_def, Rat.one_mul]
      exact Rat.mul_inv_cancel h hh
    rw [hcancel]
    decide +kernel
  have hresidual : qabs residual <= eps * qabs h / 2 := by
    simpa [residual] using houter
  have hfirst : qabs (residual / h) <= eps / 2 := by
    rw [Rat.div_def, qabs_mul]
    calc
      qabs residual * qabs h⁻¹ <=
          (eps * qabs h / 2) * qabs h⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right hresidual (qabs_nonneg _)
      _ = eps / 2 := by
        rw [Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hbound0 : 0 <= bound := Rat.le_of_lt hbound
  have hinner' : qabs innerError <= eps / (2 * bound) := by
    simpa [innerError] using hinner
  have hsecond : qabs (outerDerivative * innerError) <= eps / 2 := by
    rw [qabs_mul]
    calc
      qabs outerDerivative * qabs innerError <=
          bound * qabs innerError :=
        Rat.mul_le_mul_of_nonneg_right houterDerivative (qabs_nonneg _)
      _ <= bound * (eps / (2 * bound)) :=
        Rat.mul_le_mul_of_nonneg_left hinner' hbound0
      _ = eps / 2 := by
        rw [Rat.div_def, Rat.div_def]
        have hBne : bound ≠ 0 := Rat.ne_of_gt hbound
        grind [Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel bound hBne]
  rw [rationalCompositionSecant_error_identity
    outerBase outerStep outerDerivative innerBase innerStep
      innerDerivative h]
  calc
    qabs (residual / h + outerDerivative * innerError) <=
        qabs (residual / h) + qabs (outerDerivative * innerError) :=
      qabs_add_le _ _
    _ <= eps / 2 + eps / 2 := rat_add_le_add hfirst hsecond
    _ = eps := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel 2 (by decide +kernel : (2 : Rat) ≠ 0)]

structure FiniteCompositionDerivativeOnInterval
    (composite compositeDerivative : FunctionOnInterval) where
  same_lower : compositeDerivative.lower = composite.lower
  same_upper : compositeDerivative.upper = composite.upper
  stepPrecision : Nat -> Nat
  evalPrecision : Rat -> Rat -> Nat -> Nat
  outerDerivativeBound : Rat
  outerDerivativeBound_pos : 0 < outerDerivativeBound
  innerBaseValue : Rat -> Rat -> Nat -> Rat
  innerStepValue : Rat -> Rat -> Nat -> Rat
  innerDerivativeValue : Rat -> Rat -> Nat -> Rat
  outerBaseValue : Rat -> Rat -> Nat -> Rat
  outerStepValue : Rat -> Rat -> Nat -> Rat
  outerDerivativeValue : Rat -> Rat -> Nat -> Rat
  base_mem :
    forall x h n
      (hx : inDomainInterval composite.lower composite.upper x)
      (_hxh : inDomainInterval composite.lower composite.upper (x + h)),
      let I := composite.compute x hx (evalPrecision x h n)
      I.lo <= outerBaseValue x h n /\ outerBaseValue x h n <= I.hi
  step_mem :
    forall x h n
      (_hx : inDomainInterval composite.lower composite.upper x)
      (hxh : inDomainInterval composite.lower composite.upper (x + h)),
      let I := composite.compute (x + h) hxh (evalPrecision x h n)
      I.lo <= outerStepValue x h n /\ outerStepValue x h n <= I.hi
  derivative_mem :
    forall x h n
      (hdx : inDomainInterval compositeDerivative.lower
        compositeDerivative.upper x),
      let I := compositeDerivative.compute x hdx (evalPrecision x h n)
      I.lo <= outerDerivativeValue x h n * innerDerivativeValue x h n /\
        outerDerivativeValue x h n * innerDerivativeValue x h n <= I.hi
  outerDerivative_bound :
    forall x h n,
      qabs (outerDerivativeValue x h n) <= outerDerivativeBound
  outer_linearization_error :
    forall x h n,
      inDomainInterval composite.lower composite.upper x ->
      inDomainInterval composite.lower composite.upper (x + h) ->
      h ≠ 0 ->
      qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
      qabs ((outerStepValue x h n - outerBaseValue x h n) -
        outerDerivativeValue x h n *
          (innerStepValue x h n - innerBaseValue x h n)) <=
        (precisionAtStage n).val * qabs h / 2
  inner_secant_error :
    forall x h n,
      inDomainInterval composite.lower composite.upper x ->
      inDomainInterval composite.lower composite.upper (x + h) ->
      h ≠ 0 ->
      qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
      qabs (((innerStepValue x h n - innerBaseValue x h n) / h) -
        innerDerivativeValue x h n) <=
          (precisionAtStage n).val / (2 * outerDerivativeBound)
  quotient_width :
    forall x h n
      (hx : inDomainInterval composite.lower composite.upper x)
      (hxh : inDomainInterval composite.lower composite.upper (x + h)),
      h ≠ 0 ->
      qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
      (QInterval.differenceQuotient
        (composite.compute (x + h) hxh (evalPrecision x h n))
        (composite.compute x hx (evalPrecision x h n)) h).width <=
          (precisionAtStage n).val
  derivative_width :
    forall x h n
      (hdx : inDomainInterval compositeDerivative.lower
        compositeDerivative.upper x),
      (compositeDerivative.compute x hdx (evalPrecision x h n)).width <=
        (precisionAtStage n).val

/-- Composition package driven by ordinary finite secant models.

Compared with `FiniteCompositionDerivativeOnInterval`, this interface asks
for an outer secant error rather than a division-free residual.  It includes
an explicit zero-inner-increment field and two rational budget fields; the
conversion theorem below derives the division-free certificate. -/
structure FiniteSecantCompositionDerivativeOnInterval
    (composite compositeDerivative : FunctionOnInterval) where
  same_lower : compositeDerivative.lower = composite.lower
  same_upper : compositeDerivative.upper = composite.upper
  stepPrecision : Nat -> Nat
  evalPrecision : Rat -> Rat -> Nat -> Nat
  outerDerivativeBound : Rat
  outerDerivativeBound_pos : 0 < outerDerivativeBound
  outerError : Nat -> Rat
  innerError : Nat -> Rat
  innerBaseValue : Rat -> Rat -> Nat -> Rat
  innerStepValue : Rat -> Rat -> Nat -> Rat
  innerDerivativeValue : Rat -> Rat -> Nat -> Rat
  outerBaseValue : Rat -> Rat -> Nat -> Rat
  outerStepValue : Rat -> Rat -> Nat -> Rat
  outerDerivativeValue : Rat -> Rat -> Nat -> Rat
  base_mem :
    forall x h n
      (hx : inDomainInterval composite.lower composite.upper x)
      (_hxh : inDomainInterval composite.lower composite.upper (x + h)),
      let I := composite.compute x hx (evalPrecision x h n)
      I.lo <= outerBaseValue x h n /\ outerBaseValue x h n <= I.hi
  step_mem :
    forall x h n
      (_hx : inDomainInterval composite.lower composite.upper x)
      (hxh : inDomainInterval composite.lower composite.upper (x + h)),
      let I := composite.compute (x + h) hxh (evalPrecision x h n)
      I.lo <= outerStepValue x h n /\ outerStepValue x h n <= I.hi
  derivative_mem :
    forall x h n
      (hdx : inDomainInterval compositeDerivative.lower
        compositeDerivative.upper x),
      let I := compositeDerivative.compute x hdx (evalPrecision x h n)
      I.lo <= outerDerivativeValue x h n * innerDerivativeValue x h n /\
        outerDerivativeValue x h n * innerDerivativeValue x h n <= I.hi
  outerDerivative_bound : forall x h n,
    qabs (outerDerivativeValue x h n) <= outerDerivativeBound
  outer_zero_increment : forall x h n,
    innerStepValue x h n - innerBaseValue x h n = 0 ->
      outerStepValue x h n = outerBaseValue x h n
  outer_secant_error : forall x h n,
    inDomainInterval composite.lower composite.upper x ->
    inDomainInterval composite.lower composite.upper (x + h) ->
    h ≠ 0 ->
    qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
    innerStepValue x h n - innerBaseValue x h n ≠ 0 ->
    qabs (((outerStepValue x h n - outerBaseValue x h n) /
      (innerStepValue x h n - innerBaseValue x h n)) -
        outerDerivativeValue x h n) <= outerError n
  outer_error_budget : forall x h n,
    inDomainInterval composite.lower composite.upper x ->
    inDomainInterval composite.lower composite.upper (x + h) ->
    h ≠ 0 ->
    qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
    outerError n *
        qabs (innerStepValue x h n - innerBaseValue x h n) <=
      (precisionAtStage n).val * qabs h / 2
  inner_secant_error : forall x h n,
    inDomainInterval composite.lower composite.upper x ->
    inDomainInterval composite.lower composite.upper (x + h) ->
    h ≠ 0 ->
    qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
    qabs (((innerStepValue x h n - innerBaseValue x h n) / h) -
      innerDerivativeValue x h n) <= innerError n
  inner_error_budget : forall n,
    innerError n <=
      (precisionAtStage n).val / (2 * outerDerivativeBound)
  quotient_width :
    forall x h n
      (hx : inDomainInterval composite.lower composite.upper x)
      (hxh : inDomainInterval composite.lower composite.upper (x + h)),
      h ≠ 0 ->
      qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
      (QInterval.differenceQuotient
        (composite.compute (x + h) hxh (evalPrecision x h n))
        (composite.compute x hx (evalPrecision x h n)) h).width <=
          (precisionAtStage n).val
  derivative_width :
    forall x h n
      (hdx : inDomainInterval compositeDerivative.lower
        compositeDerivative.upper x),
      (compositeDerivative.compute x hdx (evalPrecision x h n)).width <=
        (precisionAtStage n).val

namespace FiniteSecantCompositionDerivativeOnInterval

/-- Convert ordinary outer/inner secant models into the division-free
composition package, including the zero finite inner-increment branch. -/
def toFiniteComposition
    {composite compositeDerivative : FunctionOnInterval}
    (C : FiniteSecantCompositionDerivativeOnInterval
      composite compositeDerivative) :
    FiniteCompositionDerivativeOnInterval composite compositeDerivative where
  same_lower := C.same_lower
  same_upper := C.same_upper
  stepPrecision := C.stepPrecision
  evalPrecision := C.evalPrecision
  outerDerivativeBound := C.outerDerivativeBound
  outerDerivativeBound_pos := C.outerDerivativeBound_pos
  innerBaseValue := C.innerBaseValue
  innerStepValue := C.innerStepValue
  innerDerivativeValue := C.innerDerivativeValue
  outerBaseValue := C.outerBaseValue
  outerStepValue := C.outerStepValue
  outerDerivativeValue := C.outerDerivativeValue
  base_mem := C.base_mem
  step_mem := C.step_mem
  derivative_mem := C.derivative_mem
  outerDerivative_bound := C.outerDerivative_bound
  outer_linearization_error := by
    intro x h n hx hxh hh hsmall
    by_cases hincrement :
        C.innerStepValue x h n - C.innerBaseValue x h n = 0
    · rw [C.outer_zero_increment x h n hincrement, hincrement]
      have hnonneg :
          0 <= (precisionAtStage n).val * qabs h / 2 :=
        Rat.mul_nonneg
          (Rat.mul_nonneg
            (Rat.le_of_lt (precisionAtStage n).property) (qabs_nonneg h))
          (by decide +kernel)
      have hzero :
          (C.outerBaseValue x h n - C.outerBaseValue x h n) -
            C.outerDerivativeValue x h n * 0 = 0 := by grind
      rw [hzero]
      simpa [qabs] using hnonneg
    · exact Rat.le_trans
        (secantError_to_linearizationError
          (C.outerBaseValue x h n) (C.outerStepValue x h n)
          (C.outerDerivativeValue x h n)
          (C.innerStepValue x h n - C.innerBaseValue x h n)
          (C.outerError n) hincrement
          (C.outer_secant_error x h n hx hxh hh hsmall hincrement))
        (C.outer_error_budget x h n hx hxh hh hsmall)
  inner_secant_error := by
    intro x h n hx hxh hh hsmall
    exact Rat.le_trans
      (C.inner_secant_error x h n hx hxh hh hsmall)
      (C.inner_error_budget n)
  quotient_width := C.quotient_width
  derivative_width := C.derivative_width

end FiniteSecantCompositionDerivativeOnInterval

namespace FiniteCompositionDerivativeOnInterval

/-- Assemble a standard finite derivative model from the two explicit
chain-rule error budgets. -/
def toFiniteModel
    {composite compositeDerivative : FunctionOnInterval}
    (C : FiniteCompositionDerivativeOnInterval
      composite compositeDerivative) :
    FiniteModelDerivativeOnInterval composite compositeDerivative where
  same_lower := C.same_lower
  same_upper := C.same_upper
  stepPrecision := C.stepPrecision
  evalPrecision := C.evalPrecision
  baseValue := C.outerBaseValue
  stepValue := C.outerStepValue
  derivativeValue := fun x h n =>
    C.outerDerivativeValue x h n * C.innerDerivativeValue x h n
  base_mem := C.base_mem
  step_mem := C.step_mem
  derivative_mem := C.derivative_mem
  secant_error := by
    intro x h n hx hxh hh hsmall
    exact rationalCompositionSecant_error_le
      (C.outerBaseValue x h n) (C.outerStepValue x h n)
      (C.outerDerivativeValue x h n)
      (C.innerBaseValue x h n) (C.innerStepValue x h n)
      (C.innerDerivativeValue x h n) h (precisionAtStage n).val
      C.outerDerivativeBound hh C.outerDerivativeBound_pos
      (C.outerDerivative_bound x h n)
      (C.outer_linearization_error x h n hx hxh hh hsmall)
      (C.inner_secant_error x h n hx hxh hh hsmall)
  quotient_width := C.quotient_width
  derivative_width := C.derivative_width

/-- Publish the full two-sided represented derivative certificate. -/
def toHasDerivativeOnInterval
    {composite compositeDerivative : FunctionOnInterval}
    (C : FiniteCompositionDerivativeOnInterval
      composite compositeDerivative) :
    HasDerivativeOnInterval composite compositeDerivative :=
  C.toFiniteModel.toHasDerivativeOnInterval

end FiniteCompositionDerivativeOnInterval

namespace FiniteSecantCompositionDerivativeOnInterval

/-- Publish a full represented derivative from ordinary finite secant models. -/
def toHasDerivativeOnInterval
    {composite compositeDerivative : FunctionOnInterval}
    (C : FiniteSecantCompositionDerivativeOnInterval
      composite compositeDerivative) :
    HasDerivativeOnInterval composite compositeDerivative :=
  C.toFiniteComposition.toHasDerivativeOnInterval

end FiniteSecantCompositionDerivativeOnInterval


end PrimitiveChangeOfVariables
end ComputableAnalysis
