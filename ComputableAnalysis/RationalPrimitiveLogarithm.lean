import ComputableAnalysis.ComplexLogarithmCompletedSecant
import ComputableAnalysis.FiniteDerivativeLimit

/-!
# An analytic logarithm primitive

Restrict the certified logarithm series to the real half interval. The
finite quadratic remainder and geometric box widths give an actual two-sided
`HasDerivativeOnInterval` certificate with the exact rational reciprocal as
its derivative. No derivative law is assumed as an input.
-/

namespace ComputableAnalysis
namespace RationalPrimitiveLogarithm

open ComplexLogarithmApproximation ComplexLogarithmJet
  ComplexLogarithmCompletedSecant

/-- Half-budget used to separate finite secant error from evaluator error. -/
private def halfTolerance (eps : QPos) : QPos :=
  ⟨eps.val / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩

private def dyadicStepPrecision (bound : Rat) (eps : QPos) : Nat :=
  2 ^ RationalMajorant.halfDecayShift bound eps

private theorem dyadicStepPrecision_spec {bound : Rat} (hbound : 0 <= bound)
    (eps : QPos) {h : Rat}
    (hsmall : qabs h <= 1 / ((dyadicStepPrecision bound eps : Nat) : Rat)) :
    qabs h * bound <= eps.val := by
  have hs := Rat.mul_le_mul_of_nonneg_right hsmall hbound
  have hid : 1 / ((dyadicStepPrecision bound eps : Nat) : Rat) * bound =
      bound * (1 / 2 : Rat) ^ RationalMajorant.halfDecayShift bound eps := by
    rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
    exact Rat.mul_comm _ _
  rw [hid] at hs
  exact Rat.le_trans hs (RationalMajorant.halfDecayShift_spec hbound eps)

private theorem norm_ofRat (x : Rat) : QComplex.normBound (QComplex.ofRat x) = qabs x := by
  simp only [QComplex.normBound, QComplex.ofRat, show qabs (0 : Rat) = 0 by unfold qabs; decide, Rat.add_zero]

private theorem domain_bound {x : Rat}
    (hx : inDomainInterval (-(1 / 2)) (1 / 2) x) : qabs x <= 1 / 2 := by
  change -(1 / 2) <= x ∧ x <= 1 / 2 at hx
  unfold qabs
  split <;> grind

/-- The interval algorithm for the real series `log(1+x)`. -/
def logOnePlus (x : Rat) : RealRaw :=
  (logOnePlusRawAt (QComplex.ofRat x)).realPart

theorem logOnePlus_valid {x : Rat} (hx : qabs x <= 1 / 2) :
    (logOnePlus x).Valid :=
  ComplexRaw.realPart_valid (logOnePlusRawAt_valid (w := QComplex.ofRat x) (by change QComplex.normBound (QComplex.ofRat x) <= (1 / 2 : Rat); simpa only [norm_ofRat] using hx))

def logOnePlusOnHalf : FunctionOnInterval :=
  FunctionOnInterval.ofStable
    { definedAt := fun x => qabs x <= 1 / 2
      compute := fun x => (logOnePlus x).compute
      rate := fun _ => .unknown }
    (-(1 / 2)) (1 / 2) (fun _ hx => domain_bound hx)
    (fun _ hx => logOnePlus_valid hx)

def reciprocalOnePlusOnHalf : FunctionOnInterval :=
  FunctionOnInterval.exactRat (fun x => 1 / (1 + x)) (-(1 / 2)) (1 / 2)

private def valueCenter (x : Rat) (s : Nat) : Rat :=
  ((logOnePlusRawAt (QComplex.ofRat x)).compute s).center.re

private def derivativeCenter (x : Rat) (s : Nat) : Rat :=
  ((derivativeRawAt (QComplex.ofRat x)).compute s).center.re

private theorem inverse_real (x : Rat) (hx : qabs x <= 1 / 2) :
    (QComplex.inverse (QComplex.add QComplex.one (QComplex.ofRat x))).re =
      1 / (1 + x) := by
  have hleft : -x <= qabs x := by simpa only [qabs_neg] using self_le_qabs (-x)
  have hp : 0 < 1 + x := by grind
  have hc := Rat.mul_inv_cancel (1 + x) (Rat.ne_of_gt hp)
  simp only [QComplex.inverse, QComplex.normSq, QComplex.add, QComplex.one,
    QComplex.ofRat, Rat.mul_zero, Rat.add_zero, Rat.div_def,
    Rat.inv_mul_rev, Rat.one_mul]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- Each geometric derivative box contains the exact reciprocal, rather
than merely an unspecified derivative candidate. -/
theorem derivative_contains_reciprocal {x : Rat} (hx : qabs x <= 1 / 2) (s : Nat) :
    let D := (derivativeRawAt (QComplex.ofRat x)).compute s
    D.lo.re <= 1 / (1 + x) ∧ 1 / (1 + x) <= D.hi.re := by
  have he := derivativeRawAt_equiv_inverse (w := QComplex.ofRat x) (by change QComplex.normBound (QComplex.ofRat x) <= (1 / 2 : Rat); simpa only [norm_ofRat] using hx)
  have ho := (ComplexRaw.compareAt_overlap_iff _ _ s s).1 (he s)
  have hr := inverse_real x hx
  exact ⟨by simpa only [ComplexRaw.ofQComplex, QBox.point, hr] using ho.1.1,
    by simpa only [ComplexRaw.ofQComplex, QBox.point, hr] using ho.2.1⟩

private theorem derivativeCenter_error {x : Rat} (hx : qabs x <= 1 / 2) (s : Nat) :
    qabs (derivativeCenter x s - 1 / (1 + x)) <= 4 * (1 / 2 : Rat) ^ s := by
  have hm := QBox.center_mem (ComplexRaw.valid_ordered
    (derivativeRawAt_valid (w := QComplex.ofRat x) (by change QComplex.normBound (QComplex.ofRat x) <= (1 / 2 : Rat); simpa only [norm_ofRat] using hx)) s)
  have hd := derivative_contains_reciprocal hx s
  exact Rat.le_trans (qabs_sub_le_of_common_bounds hm.1.1 hm.2.1 hd.1 hd.2)
    (derivativeRawAt_width_height_geometric (QComplex.ofRat x) s).1

private theorem valueCenter_mem {x : Rat} (hx : qabs x <= 1 / 2) (s : Nat) :
    ((logOnePlus x).compute s).lo <= valueCenter x s ∧
      valueCenter x s <= ((logOnePlus x).compute s).hi := by
  have hm := QBox.center_mem (ComplexRaw.valid_ordered
    (logOnePlusRawAt_valid (w := QComplex.ofRat x) (by change QComplex.normBound (QComplex.ofRat x) <= (1 / 2 : Rat); simpa only [norm_ofRat] using hx)) s)
  exact ⟨hm.1.1, hm.2.1⟩

private theorem center_secant_error {x h : Rat}
    (hx : qabs x <= 1 / 2) (hxh : qabs (x + h) <= 1 / 2)
    (hh : h ≠ 0) (s : Nat) :
    qabs ((valueCenter (x + h) s - valueCenter x s) / h - 1 / (1 + x)) <=
      2 * qabs h +
        (8 * (1 + qabs h) * qabs h⁻¹ + 4) * (1 / 2 : Rat) ^ s := by
  have hadd : QComplex.add (QComplex.ofRat x) (QComplex.ofRat h) =
      QComplex.ofRat (x + h) := by
    simp [QComplex.add, QComplex.ofRat, Rat.zero_add]
  have hb := centerLinearRemainder_normBound_le
    (w := QComplex.ofRat x) (h := QComplex.ofRat h) (H := qabs h)
    (by change QComplex.normBound (QComplex.ofRat x) <= (1 / 2 : Rat); simpa only [norm_ofRat] using hx)
    (by change QComplex.normBound (QComplex.add (QComplex.ofRat x) (QComplex.ofRat h)) <= (1 / 2 : Rat); simpa only [hadd, norm_ofRat] using hxh)
    (qabs_nonneg h) (by rw [norm_ofRat]; exact Rat.le_refl) s
  change QComplex.normBound _ <= 2 * qabs h * qabs h + 8 * (1 + qabs h) * (1 / 2 : Rat) ^ s at hb
  have hre : qabs (valueCenter (x + h) s - valueCenter x s - derivativeCenter x s * h) <=
      2 * qabs h * qabs h + 8 * (1 + qabs h) * (1 / 2 : Rat) ^ s := by
    have him := qabs_nonneg (centerLinearRemainder (QComplex.ofRat x) (QComplex.ofRat h) s).im
    have hr : (centerLinearRemainder (QComplex.ofRat x) (QComplex.ofRat h) s).re =
        valueCenter (x + h) s - valueCenter x s - derivativeCenter x s * h := by
      simp only [centerLinearRemainder, QComplex.sub, QComplex.add,
        QComplex.neg, QComplex.mul, QComplex.ofRat, Rat.mul_zero, Rat.sub_eq_add_neg,
        Rat.neg_zero, Rat.add_zero, valueCenter, derivativeCenter]
    change qabs _ + qabs _ <= _ at hb
    rw [hr] at hb
    grind
  have hc : qabs h * qabs h⁻¹ = 1 := by
    rw [← qabs_mul, Rat.mul_inv_cancel h hh]
    exact qabs_eq_self_of_nonneg (by decide)
  have hid : (valueCenter (x + h) s - valueCenter x s) / h - 1 / (1 + x) =
      (valueCenter (x + h) s - valueCenter x s - derivativeCenter x s * h) * h⁻¹ +
        (derivativeCenter x s - 1 / (1 + x)) := by
    have hcancel := Rat.mul_inv_cancel h hh
    grind [Rat.div_def]
  rw [hid]
  apply Rat.le_trans (qabs_add_le _ _)
  rw [qabs_mul]
  have hm := Rat.mul_le_mul_of_nonneg_right hre (qabs_nonneg h⁻¹)
  have hd := derivativeCenter_error hx s
  have hs := rat_add_le_add hm hd
  apply Rat.le_trans hs
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- Runtime coefficient simultaneously paying for the value boxes and the
geometric derivative approximation. -/
def runtimeCoefficient (h : Rat) : Rat :=
  8 * (1 + qabs h) * qabs h⁻¹ + 4 + 4 * qabs h⁻¹

private theorem runtimeCoefficient_nonneg (h : Rat) : 0 <= runtimeCoefficient h := by
  have ha := qabs_nonneg h
  have hb := qabs_nonneg h⁻¹
  have hc := Rat.mul_nonneg (show 0 <= 8 * (1 + qabs h) by grind) hb
  unfold runtimeCoefficient
  grind

def evaluationStage (h : Rat) (n : Nat) : Nat :=
  RationalMajorant.halfDecayShift (runtimeCoefficient h)
    (halfTolerance (precisionAtStage n))

private theorem runtime_budget (h : Rat) (n : Nat) :
    runtimeCoefficient h * (1 / 2 : Rat) ^ evaluationStage h n <=
      (precisionAtStage n).val / 2 :=
  RationalMajorant.halfDecayShift_spec (runtimeCoefficient_nonneg h)
    (halfTolerance (precisionAtStage n))

/-- A fully constructed finite model for the logarithm derivative. -/
def finiteModel : FiniteModelDerivativeOnInterval logOnePlusOnHalf reciprocalOnePlusOnHalf where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := fun n => dyadicStepPrecision 2
    (halfTolerance (precisionAtStage n))
  evalPrecision := fun _ h n => evaluationStage h n
  baseValue := fun x h n => valueCenter x (evaluationStage h n)
  stepValue := fun x h n => valueCenter (x + h) (evaluationStage h n)
  derivativeValue := fun x _ _ => 1 / (1 + x)
  base_mem := fun _ _ _ hx _ => valueCenter_mem (domain_bound hx) _
  step_mem := fun _ _ _ _ hx => valueCenter_mem (domain_bound hx) _
  derivative_mem := fun _ _ _ _ => ⟨Rat.le_refl, Rat.le_refl⟩
  secant_error := by
    intro x h n hx hxh hh hsmall
    have hs := dyadicStepPrecision_spec (by decide : (0 : Rat) <= 2)
      (halfTolerance (precisionAtStage n)) hsmall
    have hr := runtime_budget h n
    have hpow : 0 <= (1 / 2 : Rat) ^ evaluationStage h n := Rat.pow_nonneg (by rw [Rat.div_def, Rat.one_mul]; exact Rat.le_of_lt ((Rat.inv_pos).2 (by decide)))
    have habs := qabs_nonneg h⁻¹
    have hc : 8 * (1 + qabs h) * qabs h⁻¹ + 4 <= runtimeCoefficient h := by
      unfold runtimeCoefficient
      grind
    have hb := Rat.mul_le_mul_of_nonneg_right hc hpow
    have he := center_secant_error (domain_bound hx) (domain_bound hxh) hh (evaluationStage h n)
    change qabs _ <= _
    change qabs h * 2 <= (precisionAtStage n).val / 2 at hs
    grind [Rat.mul_comm]
  quotient_width := by
    intro x h n hx hxh hh _
    rw [QInterval.differenceQuotient_width]
    have hxw := (logOnePlusRawAt_width_height_geometric (QComplex.ofRat x) (evaluationStage h n)).1
    have hyw := (logOnePlusRawAt_width_height_geometric (QComplex.ofRat (x + h)) (evaluationStage h n)).1
    change _ <= 2 * (1 / 2 : Rat) ^ evaluationStage h n at hxw hyw
    have hsum := rat_add_le_add hyw hxw
    have habs := qabs_nonneg h⁻¹
    have hm := Rat.mul_le_mul_of_nonneg_left hsum habs
    have hp : 0 <= (1 / 2 : Rat) ^ evaluationStage h n := Rat.pow_nonneg (by rw [Rat.div_def, Rat.one_mul]; exact Rat.le_of_lt ((Rat.inv_pos).2 (by decide)))
    have ha := qabs_nonneg h
    have ht := Rat.mul_nonneg (show 0 <= 8 * (1 + qabs h) by grind) habs
    have hc : 4 * qabs h⁻¹ <= runtimeCoefficient h := by
      unfold runtimeCoefficient
      grind
    have hb := Rat.mul_le_mul_of_nonneg_right hc hp
    have hr := runtime_budget h n
    have he := (precisionAtStage n).property
    change qabs (1 / h) *
      (((logOnePlusRawAt (QComplex.ofRat (x + h))).compute (evaluationStage h n)).width +
       ((logOnePlusRawAt (QComplex.ofRat x)).compute (evaluationStage h n)).width) <= _
    simp only [Rat.div_def, Rat.one_mul]
    grind [Rat.mul_assoc, Rat.mul_add]
  derivative_width := by
    intro x h n hx
    change 1 / (1 + x) - 1 / (1 + x) <= _
    rw [Rat.sub_self]
    exact Rat.le_of_lt (precisionAtStage n).property

/-- The actual represented logarithm has the exact reciprocal derivative on
both sides at every rational point of the closed half interval. -/
def hasDerivative : HasDerivativeOnInterval logOnePlusOnHalf reciprocalOnePlusOnHalf :=
  finiteModel.toHasDerivativeOnInterval


/-- The same logarithm series evaluated in a rational affine chart. -/
def logAffine (m c a b : Rat)
    (hmap : ∀ x, inDomainInterval a b x → qabs (m * x + c) <= 1 / 2) :
    FunctionOnInterval :=
  FunctionOnInterval.ofStable
    { definedAt := fun x => qabs (m * x + c) <= 1 / 2
      compute := fun x => (logOnePlus (m * x + c)).compute
      rate := fun _ => .unknown }
    a b hmap (fun _ hx => logOnePlus_valid hx)

private def affineRuntimeCoefficient (m h : Rat) : Rat :=
  qabs m * (8 * (1 + qabs (m * h)) * qabs (m * h)⁻¹ + 4) +
    4 * qabs h⁻¹

private theorem affineRuntimeCoefficient_nonneg (m h : Rat) :
    0 <= affineRuntimeCoefficient m h := by
  have ha := qabs_nonneg m
  have hb := qabs_nonneg (m * h)
  have hc := qabs_nonneg (m * h)⁻¹
  have hd := qabs_nonneg h⁻¹
  have he := Rat.mul_nonneg (show 0 <= 8 * (1 + qabs (m * h)) by grind) hc
  have hf := Rat.mul_nonneg ha (show 0 <= 8 * (1 + qabs (m * h)) * qabs (m * h)⁻¹ + 4 by grind)
  unfold affineRuntimeCoefficient
  grind

/-- Analytic chain rule for every nonconstant rational affine logarithm
chart, including negative slopes. -/
def affineFiniteModel (m c a b : Rat) (hm : m ≠ 0)
    (hmap : ∀ x, inDomainInterval a b x → qabs (m * x + c) <= 1 / 2) :
    FiniteModelDerivativeOnInterval (logAffine m c a b hmap)
      (FunctionOnInterval.exactRat (fun x => m / (1 + (m * x + c))) a b) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := fun n => dyadicStepPrecision (2 * qabs m * qabs m)
    (halfTolerance (precisionAtStage n))
  evalPrecision := fun _ h n => RationalMajorant.halfDecayShift (affineRuntimeCoefficient m h)
    (halfTolerance (precisionAtStage n))
  baseValue := fun x h n => valueCenter (m * x + c)
    (RationalMajorant.halfDecayShift (affineRuntimeCoefficient m h)
      (halfTolerance (precisionAtStage n)))
  stepValue := fun x h n => valueCenter (m * (x + h) + c)
    (RationalMajorant.halfDecayShift (affineRuntimeCoefficient m h)
      (halfTolerance (precisionAtStage n)))
  derivativeValue := fun x _ _ => m / (1 + (m * x + c))
  base_mem := fun _ _ _ hx _ => valueCenter_mem (hmap _ hx) _
  step_mem := fun _ _ _ _ hx => valueCenter_mem (hmap _ hx) _
  derivative_mem := fun _ _ _ _ => ⟨Rat.le_refl, Rat.le_refl⟩
  secant_error := by
    intro x h n hx hxh hh hsmall
    let s := RationalMajorant.halfDecayShift (affineRuntimeCoefficient m h)
      (halfTolerance (precisionAtStage n))
    have hmh : m * h ≠ 0 := by grind [Rat.mul_eq_zero]
    have he := center_secant_error (hmap x hx)
      (show qabs (m * x + c + m * h) <= 1 / 2 by
        have h := hmap (x + h) hxh
        simpa only [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm] using h)
      hmh s
    have hcancel := Rat.mul_inv_cancel m hm
    have hid :
        (valueCenter (m * (x + h) + c) s - valueCenter (m * x + c) s) / h -
          m / (1 + (m * x + c)) =
        m * ((valueCenter (m * x + c + m * h) s - valueCenter (m * x + c) s) /
          (m * h) - 1 / (1 + (m * x + c))) := by
      have hp : m * (x + h) + c = m * x + c + m * h := by grind
      rw [hp]
      simp only [Rat.div_def, Rat.inv_mul_rev, Rat.one_mul]
      grind
    change qabs ((valueCenter (m * (x + h) + c) s - valueCenter (m * x + c) s) / h -
      m / (1 + (m * x + c))) <= _
    rw [hid, qabs_mul]
    have hb := Rat.mul_le_mul_of_nonneg_left he (qabs_nonneg m)
    have hc0 : 0 <= 2 * qabs m * qabs m := by
      have h := Rat.mul_nonneg (qabs_nonneg m) (qabs_nonneg m)
      grind
    have hs := dyadicStepPrecision_spec hc0
      (halfTolerance (precisionAtStage n)) hsmall
    change qabs h * (2 * qabs m * qabs m) <= (precisionAtStage n).val / 2 at hs
    have hr := RationalMajorant.halfDecayShift_spec (affineRuntimeCoefficient_nonneg m h)
      (halfTolerance (precisionAtStage n))
    change affineRuntimeCoefficient m h * (1 / 2 : Rat) ^ s <= (precisionAtStage n).val / 2 at hr
    have htail := Rat.mul_nonneg (qabs_nonneg h⁻¹)
      (Rat.pow_nonneg (show (0 : Rat) <= 1 / 2 by grind) (n := s))
    rw [qabs_mul] at hb
    unfold affineRuntimeCoefficient at hr
    rw [qabs_mul] at hr
    grind
  quotient_width := by
    intro x h n hx hxh hh _
    let s := RationalMajorant.halfDecayShift (affineRuntimeCoefficient m h)
      (halfTolerance (precisionAtStage n))
    rw [QInterval.differenceQuotient_width]
    have hxw := (logOnePlusRawAt_width_height_geometric (QComplex.ofRat (m * x + c)) s).1
    have hyw := (logOnePlusRawAt_width_height_geometric (QComplex.ofRat (m * (x + h) + c)) s).1
    change _ <= 2 * (1 / 2 : Rat) ^ s at hxw hyw
    have hb := Rat.mul_le_mul_of_nonneg_left (rat_add_le_add hyw hxw) (qabs_nonneg h⁻¹)
    have hr := RationalMajorant.halfDecayShift_spec (affineRuntimeCoefficient_nonneg m h)
      (halfTolerance (precisionAtStage n))
    change affineRuntimeCoefficient m h * (1 / 2 : Rat) ^ s <= (precisionAtStage n).val / 2 at hr
    have hcoeff : 0 <= qabs m * (8 * (1 + qabs (m * h)) * qabs (m * h)⁻¹ + 4) := by
      have ht := Rat.mul_nonneg (show 0 <= 8 * (1 + qabs (m * h)) by have := qabs_nonneg (m * h); grind)
        (qabs_nonneg (m * h)⁻¹)
      exact Rat.mul_nonneg (qabs_nonneg m) (by grind)
    have hp := Rat.mul_nonneg hcoeff
      (Rat.pow_nonneg (show (0 : Rat) <= 1 / 2 by grind) (n := s))
    have he := (precisionAtStage n).property
    change qabs (1 / h) *
      (((logOnePlusRawAt (QComplex.ofRat (m * (x + h) + c))).compute s).width +
       ((logOnePlusRawAt (QComplex.ofRat (m * x + c))).compute s).width) <= _
    simp only [Rat.div_def, Rat.one_mul]
    unfold affineRuntimeCoefficient at hr
    grind
  derivative_width := by
    intro x h n hx
    change m / (1 + (m * x + c)) - m / (1 + (m * x + c)) <= _
    rw [Rat.sub_self]
    exact Rat.le_of_lt (precisionAtStage n).property

def affineHasDerivative (m c a b : Rat) (hm : m ≠ 0)
    (hmap : ∀ x, inDomainInterval a b x → qabs (m * x + c) <= 1 / 2) :
    HasDerivativeOnInterval (logAffine m c a b hmap)
      (FunctionOnInterval.exactRat (fun x => m / (1 + (m * x + c))) a b) :=
  (affineFiniteModel m c a b hm hmap).toHasDerivativeOnInterval


/-- A rational neighborhood avoiding a specified linear pole. -/
def poleRadius (pole center : Rat) : Rat := qabs (center - pole) / 2

theorem poleRadius_pos {pole center : Rat} (hc : center ≠ pole) :
    0 < poleRadius pole center := by
  have hd : center - pole ≠ 0 := by grind
  unfold poleRadius
  rw [Rat.div_def]
  exact Rat.mul_pos (qabs_pos_of_ne hd) ((Rat.inv_pos).2 (by decide))

private theorem poleChart_map (pole center : Rat) (hc : center ≠ pole) :
    ∀ x, inDomainInterval (center - poleRadius pole center)
      (center + poleRadius pole center) x →
      qabs ((center - pole)⁻¹ * x + (-(center - pole)⁻¹ * center)) <= 1 / 2 := by
  intro x hx
  have hd : center - pole ≠ 0 := by grind
  have ha : qabs (x - center) <= poleRadius pole center := by
    change center - poleRadius pole center <= x ∧ x <= center + poleRadius pole center at hx
    unfold qabs
    split <;> grind
  have hid : (center - pole)⁻¹ * x + (-(center - pole)⁻¹ * center) =
      (center - pole)⁻¹ * (x - center) := by grind
  rw [hid, qabs_mul]
  have hmul := Rat.mul_le_mul_of_nonneg_left ha (qabs_nonneg (center - pole)⁻¹)
  have hcanc : qabs (center - pole)⁻¹ * qabs (center - pole) = 1 := by
    rw [← qabs_mul, Rat.inv_mul_cancel _ hd]
    exact qabs_eq_self_of_nonneg (by decide)
  unfold poleRadius at hmul
  grind

/-- The normalized elementary logarithm of `(x-pole)/(center-pole)`.
Both sides of the pole are supported; the argument stays positive. -/
def simplePolePrimitive (pole center : Rat) (hc : center ≠ pole) : FunctionOnInterval :=
  logAffine (center - pole)⁻¹ (-(center - pole)⁻¹ * center)
    (center - poleRadius pole center) (center + poleRadius pole center)
    (poleChart_map pole center hc)

/-- Every rational point away from a linear pole has an explicitly computed
nondegenerate neighborhood on which the elementary logarithm is a primitive
of the reciprocal. There is no supplied analytic certificate among the inputs. -/
def simplePole_hasDerivative (pole center : Rat) (hc : center ≠ pole) :
    HasDerivativeOnInterval (simplePolePrimitive pole center hc)
      (FunctionOnInterval.exactRat (fun x => 1 / (x - pole))
        (center - poleRadius pole center) (center + poleRadius pole center)) := by
  have hd : center - pole ≠ 0 := by grind
  have hm : (center - pole)⁻¹ ≠ 0 := by
    have hh := Rat.mul_inv_cancel (center - pole) hd
    grind
  have H := affineHasDerivative (center - pole)⁻¹ (-(center - pole)⁻¹ * center)
    (center - poleRadius pole center) (center + poleRadius pole center) hm
    (poleChart_map pole center hc)
  have hf : (fun x => (center - pole)⁻¹ /
      (1 + ((center - pole)⁻¹ * x + (-(center - pole)⁻¹ * center)))) =
      (fun x => 1 / (x - pole)) := by
    funext x
    have hcanc := Rat.inv_mul_cancel (center - pole) hd
    have hid : 1 + ((center - pole)⁻¹ * x + (-(center - pole)⁻¹ * center)) =
        (center - pole)⁻¹ * (x - pole) := by grind
    rw [hid, Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv, Rat.div_def, Rat.one_mul]
    grind
  rw [hf] at H
  exact H

end RationalPrimitiveLogarithm
end ComputableAnalysis
