import ComputableAnalysis.RationalCircle
import ComputableAnalysis.ArctanGeometry
import ComputableAnalysis.ArctanPresentations
import ComputableAnalysis.Basic
import ComputableAnalysis.DirichletSeries
import ComputableAnalysis.IntegralIdentities
import ComputableAnalysis.Logarithm
import ComputableAnalysis.Nilakantha
import ComputableAnalysis.Taylor

/-!
# Proof targets for the four pi algorithms

`Pi.lean` is intentionally computational: it exposes four `RealRaw`
algorithms for pi.  This file is the companion proof layer.  It names the
validity checks and equivalence theorems for those public algorithms, and keeps
the proof statements phrased directly in terms of the new definitions.
-/

namespace ComputableAnalysis

namespace PiProofs

/-- Small rational-order compatibility layer.  These are direct finite-field
lemmas, stated here so the pi proofs do not depend on a particular Lean
prelude spelling for additive and multiplicative order transport. -/
theorem Rat.add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) : a + c <= b + d := by
  calc
    a + c <= b + c := (Rat.add_le_add_right).2 hab
    _ <= b + d := (Rat.add_le_add_left).2 hcd

theorem Rat.mul_left_comm (a b c : Rat) : a * b * c = a * c * b := by
  calc
    a * b * c = a * (b * c) := Rat.mul_assoc _ _ _
    _ = a * (c * b) := by rw [Rat.mul_comm b c]
    _ = a * c * b := (Rat.mul_assoc _ _ _).symm

theorem Rat.div_le_div_of_nonneg_right {a b c : Rat}
    (hab : a <= b) (hc : 0 < c) : a / c <= b / c := by
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right hab
    (Rat.le_of_lt ((Rat.inv_pos).2 hc))

def LeibnizValid : Prop :=
  RealRaw.ValidCompute piLeibniz.compute

def MachinValid : Prop :=
  RealRaw.ValidCompute piMachin.compute

def AreaValid : Prop :=
  RealRaw.ValidCompute piCircleArea.compute

def AreaPolygonValid : Prop :=
  RealRaw.ValidCompute piCircleAreaPolygon.compute

def PiCircleAreaPolygonAgreement : Prop :=
  forall n, piCircleArea.compute n = piCircleAreaPolygon.compute n

/-- The public increment/decrement area loop and the polygon-stage
computation agree exactly at every dyadic stage. -/
theorem piCircleAreaPolygonAgreement : PiCircleAreaPolygonAgreement :=
  ArctanGeometry.piCircleArea_compute_eq_piCircleAreaPolygon_compute

def CircumferenceValid : Prop :=
  RealRaw.ValidCompute piCircumference.compute

def LeibnizEqMachin : Prop :=
  piLeibniz.Equiv piMachin

def LeibnizEqArea : Prop :=
  piLeibniz.Equiv piCircleArea

def AreaEqCircumference : Prop :=
  piCircleArea.Equiv piCircumference

/-- The power-series arctangent algorithm is intended on `[-1, 1]`. -/
def arctanDomain (x : Rat) : Prop :=
  -1 <= x /\ x <= 1

/-- Arctangent as a domain-aware raw function.

The public `Pi.lean` definition remains the readable evaluator
`arctan : Rat -> RealRaw`; this wrapper is the proof-facing statement that its
validity is a theorem about a function on a domain. -/
def arctanFunction : RealFunRaw where
  domain := arctanDomain
  compute := fun x => (arctan x).compute

def ArctanValid : Prop :=
  arctanFunction.Valid

theorem arctan_valid_at
    (h : ArctanValid) {x : Rat} (hx : arctanDomain x) :
    (arctan x).Valid := by
  simpa [RealRaw.Valid, RealFunRaw.applyCompute, arctanFunction]
    using RealFunRaw.validAt h hx

theorem arctan_one_fifth_mem_domain :
    arctanDomain ((1 : Rat) / 5) := by
  unfold arctanDomain
  constructor <;> native_decide

theorem arctan_one_239_mem_domain :
    arctanDomain ((1 : Rat) / 239) := by
  unfold arctanDomain
  constructor <;> native_decide

theorem arctan_one_mem_domain :
    arctanDomain (1 : Rat) := by
  unfold arctanDomain
  constructor <;> native_decide

theorem arctanKernel_one_fifth_mem_unitDomain :
    Taylor.ArctanComparison.unitDomain ((1 : Rat) / 5) := by
  unfold Taylor.ArctanComparison.unitDomain
  unfold Elementary.Arctan.powerSeriesDomain qabs
  native_decide

theorem arctanKernel_one_239_mem_unitDomain :
    Taylor.ArctanComparison.unitDomain ((1 : Rat) / 239) := by
  unfold Taylor.ArctanComparison.unitDomain
  unfold Elementary.Arctan.powerSeriesDomain qabs
  native_decide

theorem arctanKernel_one_mem_unitDomain :
    Taylor.ArctanComparison.unitDomain (1 : Rat) := by
  unfold Taylor.ArctanComparison.unitDomain
  unfold Elementary.Arctan.powerSeriesDomain qabs
  native_decide

/-- The rectangle-sum construction, viewed as the Taylor comparison kernel
integral on a nonnegative unit-branch input.  The construction is intentionally
kept in `PiProofs`: it uses the already verified rectangle schedule from
`ArctanGeometry` while targeting the oriented-kernel interface from `Taylor`. -/
def rectangleKernelIntegralAtNonnegativeUnit
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    Taylor.ArctanComparison.KernelIntegralAt x where
  construction :=
    { compute := ArctanGeometry.arctanIntegralRectangleCompute x
      certificate := by
        simpa [ArctanGeometry.arctanIntegralRectangleRaw] using
          ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1 }

theorem rectangleKernelIntegralRaw_equiv_rectangleRaw_nonnegativeUnit
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (ArctanGeometry.arctanIntegralRectangleRaw x).Equiv
      (Taylor.ArctanComparison.kernelIntegralRaw x
        (rectangleKernelIntegralAtNonnegativeUnit x hx0 hx1)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (ArctanGeometry.arctanIntegralRectangleRaw x)
    (Taylor.ArctanComparison.kernelIntegralRaw x
      (rectangleKernelIntegralAtNonnegativeUnit x hx0 hx1)) n n).2
  have hordered :=
    ArctanGeometry.arctanIntegralRectangleCompute_ordered hx0 n
  have hle :
      (ArctanGeometry.arctanIntegralRectangleCompute x n).lo <=
        (ArctanGeometry.arctanIntegralRectangleCompute x n).hi := by
    unfold QInterval.width at hordered
    grind [Rat.sub_eq_add_neg]
  change QInterval.Overlaps
    (ArctanGeometry.arctanIntegralRectangleCompute x n)
    ((Taylor.ArctanComparison.kernelIntegralRaw x
      (rectangleKernelIntegralAtNonnegativeUnit x hx0 hx1)).compute n)
  simp [Taylor.ArctanComparison.kernelIntegralRaw,
    Taylor.ArctanComparison.positiveKernelIntegralRaw,
    rectangleKernelIntegralAtNonnegativeUnit, Integral.integralFor, hx0]
  exact ⟨hle, hle⟩

theorem arctanGeom_equiv_rectangleKernelIntegral_nonnegativeUnit
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) :
    (ArctanGeometry.arctanGeom x).Equiv
      (Taylor.ArctanComparison.kernelIntegralRaw x
        (rectangleKernelIntegralAtNonnegativeUnit x hx0 hx1)) := by
  have hgeomValid : (ArctanGeometry.arctanGeom x).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit hx0 hx1
  have hrectValid : (ArctanGeometry.arctanIntegralRectangleRaw x).Valid :=
    ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1
  have hkValid :
      (Taylor.ArctanComparison.kernelIntegralRaw x
        (rectangleKernelIntegralAtNonnegativeUnit x hx0 hx1)).Valid :=
    Taylor.ArctanComparison.kernelIntegralRaw_valid x
      (rectangleKernelIntegralAtNonnegativeUnit x hx0 hx1)
  exact RealRaw.equiv_trans
    hgeomValid hrectValid hkValid
    (RealRaw.equiv_symm
      (ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom hx0))
    (rectangleKernelIntegralRaw_equiv_rectangleRaw_nonnegativeUnit
      x hx0 hx1)

theorem arctanGeom_one_equiv_rectangleKernelIntegral :
    (ArctanGeometry.arctanGeom (1 : Rat)).Equiv
      (Taylor.ArctanComparison.kernelIntegralRaw (1 : Rat)
        (rectangleKernelIntegralAtNonnegativeUnit
          (1 : Rat) (by native_decide) (by native_decide))) :=
  arctanGeom_equiv_rectangleKernelIntegral_nonnegativeUnit
    (1 : Rat) (by native_decide) (by native_decide)

theorem arctanDomain_of_nonnegativeUnit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) : arctanDomain x := by
  unfold arctanDomain
  constructor
  · grind
  · exact hx1

theorem arctanKernel_unitDomain_of_nonnegativeUnit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    Taylor.ArctanComparison.unitDomain x := by
  unfold Taylor.ArctanComparison.unitDomain
  unfold Elementary.Arctan.powerSeriesDomain qabs
  have hnot : ¬x < 0 := by grind
  simp [hnot]
  exact hx1

/-- The remaining analytic equality at a nonnegative unit-branch input, after
the rectangle construction and the geometric-kernel comparison have been
filled in. -/
def PowerSeriesEqualsRectangleKernelAt
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) : Prop :=
  (arctan x).Equiv
    (Taylor.ArctanComparison.kernelIntegralRaw x
      (rectangleKernelIntegralAtNonnegativeUnit x hx0 hx1))

abbrev PowerSeriesEqualsRectangleKernelAtOne : Prop :=
  PowerSeriesEqualsRectangleKernelAt
    (1 : Rat) (by native_decide) (by native_decide)

theorem machinValid_of_arctanValid
    (hArctan : ArctanValid) : MachinValid := by
  have h15 : (arctan ((1 : Rat) / 5)).Valid :=
    arctan_valid_at hArctan arctan_one_fifth_mem_domain
  have h239 : (arctan ((1 : Rat) / 239)).Valid :=
    arctan_valid_at hArctan arctan_one_239_mem_domain
  change piMachin.Valid
  unfold piMachin
  exact RealRaw.natScale_valid 4
    (RealRaw.sub_valid
      (RealRaw.natScale_valid 4 h15)
      h239)

namespace ArctanValidity

abbrev State := Prod Rat (Prod Rat Rat)

def state (y : Rat) (n : Nat) : State := Id.run do
  let mut lo : Rat := 0
  let mut hi : Rat := y
  let mut yPow : Rat := y * y * y
  for i in List.range n do
    let term1 : Rat := yPow / (4 * i + 3)
    yPow := yPow * y * y
    let term2 : Rat := yPow / (4 * i + 5)
    yPow := yPow * y * y
    lo := hi - term1
    hi := lo + term2
  return (lo, hi, yPow)

def lo (y : Rat) (n : Nat) : Rat := (state y n).1
def hi (y : Rat) (n : Nat) : Rat := (state y n).2.1
def powState (y : Rat) (n : Nat) : Rat := (state y n).2.2

def positiveRaw (y : Rat) : RealRaw where
  compute := fun n => { lo := lo y n, hi := hi y n }

theorem state_zero (y : Rat) :
    state y 0 = (0, y, y * y * y) := by
  unfold state
  simp

theorem state_succ (y : Rat) (n : Nat) :
    state y (n + 1) =
      let s := state y n
      let term1 : Rat := s.2.2 / (4 * (n : Rat) + 3)
      let yPow := s.2.2 * y * y
      let term2 : Rat := yPow / (4 * (n : Rat) + 5)
      let lo := s.2.1 - term1
      let hi := lo + term2
      (lo, hi, yPow * y * y) := by
  unfold state
  rw [List.range_succ]
  simp

theorem powState_eq (y : Rat) (n : Nat) :
    powState y n = y ^ (4 * n + 3) := by
  induction n with
  | zero =>
      unfold powState
      rw [state_zero]
      rw [show 4 * 0 + 3 = 1 + 1 + 1 by omega]
      repeat rw [Rat.pow_succ]
      simp [Rat.pow_zero]
  | succ n ih =>
      unfold powState
      rw [state_succ]
      change (state y n).2.2 * y * y * y * y =
        y ^ (4 * (n + 1) + 3)
      rw [show (state y n).2.2 = powState y n by rfl, ih]
      rw [show 4 * (n + 1) + 3 =
        (((4 * n + 3) + 1) + 1) + 1 + 1 by omega]
      repeat rw [Rat.pow_succ]

/-- The alternating power-series endpoints are finite integrals of the
corresponding odd and even arctangent-kernel polynomials over `[0,y]`.
This is a finite rational identity, before any limiting argument. -/
theorem endpoints_eq_kernelPartialIntegralBetween (y : Rat) (n : Nat) :
    hi y n = Taylor.ArctanKernel.kernelPartialIntegralBetween 0 y (2 * n) /\
      lo y (n + 1) =
        Taylor.ArctanKernel.kernelPartialIntegralBetween 0 y (2 * n + 1) := by
  induction n with
  | zero =>
      constructor
      · simp [hi, state, Taylor.ArctanKernel.kernelPartialIntegralBetween]
        grind [Rat.sub_eq_add_neg]
      · rw [lo, state_succ]
        simp [state, Taylor.ArctanKernel.kernelPartialIntegralBetween,
          Taylor.ArctanKernel.kernelTermIntegralBetween]
        grind [Rat.sub_eq_add_neg]
  | succ n ih =>
      have hloAsStep :
          hi y n - y ^ (4 * n + 3) / (4 * (n : Rat) + 3) =
            Taylor.ArctanKernel.kernelPartialIntegralBetween 0 y
              (2 * n + 1) := by
        rw [← ih.2]
        rw [lo, state_succ]
        simp
        rw [show (state y n).2.1 = hi y n by rfl]
        rw [show (state y n).2.2 = powState y n by rfl, powState_eq]
      have hhiSucc : hi y (n + 1) =
          Taylor.ArctanKernel.kernelPartialIntegralBetween 0 y
            (2 * (n + 1)) := by
        rw [hi, state_succ]
        simp
        rw [show (state y n).2.1 = hi y n by rfl]
        rw [show (state y n).2.2 = powState y n by rfl, powState_eq]
        rw [hloAsStep]
        have hpow : y ^ (4 * n + 3) * y * y = y ^ (4 * n + 5) := by
          rw [show 4 * n + 5 = ((4 * n + 3) + 1) + 1 by omega]
          repeat rw [Rat.pow_succ]
        rw [hpow]
        rw [show 2 * (n + 1) = 2 * n + 2 by omega]
        rw [Taylor.ArctanKernel.kernelPartialIntegralBetween_zero_even_succ]
      constructor
      · exact hhiSucc
      · rw [lo, state_succ]
        simp
        rw [show (state y (n + 1)).2.1 = hi y (n + 1) by rfl]
        rw [show (state y (n + 1)).2.2 = powState y (n + 1) by rfl,
          powState_eq]
        have hpow : y ^ (4 * (n + 1) + 3) = y ^ (4 * n + 7) := by
          congr 1 <;> omega
        rw [hpow]
        rw [hhiSucc]
        rw [Taylor.ArctanKernel.kernelPartialIntegralBetween_zero_odd_succ]
        grind

/-- The lower finite kernel primitive represented by a power-series stage. -/
def lowerKernelPartialAtStage (y : Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 =>
      Taylor.ArctanKernel.kernelPartialIntegralBetween 0 y (2 * n + 1)

/-- The upper finite kernel primitive represented by a power-series stage. -/
def upperKernelPartialAtStage (y : Rat) (n : Nat) : Rat :=
  Taylor.ArctanKernel.kernelPartialIntegralBetween 0 y (2 * n)

theorem lo_eq_lowerKernelPartialAtStage (y : Rat) (n : Nat) :
    lo y n = lowerKernelPartialAtStage y n := by
  cases n with
  | zero =>
      simp [lo, state, lowerKernelPartialAtStage]
  | succ n =>
      simp [lowerKernelPartialAtStage,
        (endpoints_eq_kernelPartialIntegralBetween y n).2]

theorem hi_eq_upperKernelPartialAtStage (y : Rat) (n : Nat) :
    hi y n = upperKernelPartialAtStage y n := by
  simp [upperKernelPartialAtStage,
    (endpoints_eq_kernelPartialIntegralBetween y n).1]

theorem positiveRaw_compute_eq_kernelPartialIntegralInterval
    (y : Rat) (n : Nat) :
    (positiveRaw y).compute n =
      { lo := lowerKernelPartialAtStage y n,
        hi := upperKernelPartialAtStage y n } := by
  unfold positiveRaw
  simp [lo_eq_lowerKernelPartialAtStage,
    hi_eq_upperKernelPartialAtStage]

theorem width_eq (y : Rat) (n : Nat) :
    hi y n - lo y n = y ^ (4 * n + 1) / (4 * (n : Rat) + 1) := by
  induction n with
  | zero =>
      unfold hi lo
      rw [state_zero]
      rw [show 4 * 0 + 1 = 1 by omega]
      rw [Rat.pow_succ]
      simp [Rat.pow_zero, Rat.div_def]
      have hone : Inv.inv ((0 : Rat) + 1) = 1 := by native_decide
      rw [hone, Rat.mul_one]
      grind
  | succ n ih =>
      unfold hi lo
      rw [state_succ]
      change
        ((state y n).2.1 - (state y n).2.2 / (4 * (n : Rat) + 3) +
            (state y n).2.2 * y * y / (4 * (n : Rat) + 5)) -
          ((state y n).2.1 - (state y n).2.2 / (4 * (n : Rat) + 3)) =
            y ^ (4 * (n + 1) + 1) /
              (4 * ((n + 1 : Nat) : Rat) + 1)
      rw [show (state y n).2.2 = powState y n by rfl, powState_eq]
      have hpow :
          y ^ (4 * n + 3) * y * y = y ^ (4 * (n + 1) + 1) := by
        rw [show 4 * (n + 1) + 1 = ((4 * n + 3) + 1) + 1 by omega]
        repeat rw [Rat.pow_succ]
      have hden :
          4 * ((n + 1 : Nat) : Rat) + 1 = 4 * (n : Rat) + 5 := by
        grind
      rw [Eq.symm hpow, hden]
      grind [Rat.sub_eq_add_neg]

private theorem pow_add_le_pow_of_unit {y : Rat}
    (hy0 : 0 <= y) (hy1 : y <= 1) (m k : Nat) :
    y ^ (m + k) <= y ^ m := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [show m + (k + 1) = (m + k) + 1 by omega]
      rw [Rat.pow_succ]
      calc
        y ^ (m + k) * y <= y ^ (m + k) * 1 :=
          Rat.mul_le_mul_of_nonneg_left hy1 (Rat.pow_nonneg hy0)
        _ = y ^ (m + k) := by rw [Rat.mul_one]
        _ <= y ^ m := ih

private theorem one_div_le_one_div_of_pos_of_le {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : Not (a = 0) := Rat.ne_of_gt ha
  have hbne : Not (b = 0) := Rat.ne_of_gt hb
  have habpos : 0 < a * b := Rat.mul_pos ha hb
  refine Rat.le_of_mul_le_mul_right (c := a * b) ?_ habpos
  calc
    (1 / b) * (a * b) = a := by
      rw [Rat.div_def]
      have hcancel : b * Inv.inv b = 1 := Rat.mul_inv_cancel b hbne
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= b := hab
    _ = (1 / a) * (a * b) := by
      rw [Rat.div_def]
      have hcancel : a * Inv.inv a = 1 := Rat.mul_inv_cancel a hane
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem div_le_div_of_nonneg_of_le_of_den_le {a b c d : Rat}
    (ha : 0 <= a) (hab : a <= b) (hc : 0 < c) (hcd : c <= d) :
    a / d <= b / c := by
  have hd : 0 < d := by grind
  have hinv_nonneg : 0 <= Inv.inv d := Rat.le_of_lt ((Rat.inv_pos).2 hd)
  have hinv_le : 1 / d <= 1 / c :=
    one_div_le_one_div_of_pos_of_le hc hcd
  rw [Rat.div_def, Rat.div_def]
  calc
    a * Inv.inv d <= b * Inv.inv d :=
      Rat.mul_le_mul_of_nonneg_right hab hinv_nonneg
    _ <= b * Inv.inv c := by
      rw [show Inv.inv d = 1 * Inv.inv d by simp]
      rw [show Inv.inv c = 1 * Inv.inv c by simp]
      exact Rat.mul_le_mul_of_nonneg_left
        (by simpa [Rat.div_def] using hinv_le)
        (Rat.le_trans ha hab)

theorem term1_le_width {y : Rat}
    (hy0 : 0 <= y) (hy1 : y <= 1) (n : Nat) :
    y ^ (4 * n + 3) / (4 * (n : Rat) + 3) <=
      y ^ (4 * n + 1) / (4 * (n : Rat) + 1) := by
  have hpow : y ^ (4 * n + 3) <= y ^ (4 * n + 1) := by
    have h := pow_add_le_pow_of_unit hy0 hy1 (4 * n + 1) 2
    simpa [show 4 * n + 1 + 2 = 4 * n + 3 by omega] using h
  exact div_le_div_of_nonneg_of_le_of_den_le
    (Rat.pow_nonneg hy0) hpow (by grind) (by grind)

theorem term2_le_term1 {y : Rat}
    (hy0 : 0 <= y) (hy1 : y <= 1) (n : Nat) :
    y ^ (4 * n + 5) / (4 * (n : Rat) + 5) <=
      y ^ (4 * n + 3) / (4 * (n : Rat) + 3) := by
  have hpow : y ^ (4 * n + 5) <= y ^ (4 * n + 3) := by
    have h := pow_add_le_pow_of_unit hy0 hy1 (4 * n + 3) 2
    simpa [show 4 * n + 3 + 2 = 4 * n + 5 by omega] using h
  exact div_le_div_of_nonneg_of_le_of_den_le
    (Rat.pow_nonneg hy0) hpow (by grind) (by grind)

theorem lo_mono_succ {y : Rat}
    (hy0 : 0 <= y) (hy1 : y <= 1) (n : Nat) :
    lo y n <= lo y (n + 1) := by
  unfold lo
  rw [state_succ]
  change (state y n).1 <=
    (state y n).2.1 - (state y n).2.2 / (4 * (n : Rat) + 3)
  have hterm :
      (state y n).2.2 / (4 * (n : Rat) + 3) <=
        (state y n).2.1 - (state y n).1 := by
    rw [show (state y n).2.2 = powState y n by rfl, powState_eq]
    rw [show (state y n).2.1 = hi y n by rfl]
    rw [show (state y n).1 = lo y n by rfl]
    rw [width_eq]
    exact term1_le_width hy0 hy1 n
  grind [Rat.sub_eq_add_neg]

theorem hi_anti_succ {y : Rat}
    (hy0 : 0 <= y) (hy1 : y <= 1) (n : Nat) :
    hi y (n + 1) <= hi y n := by
  unfold hi
  rw [state_succ]
  change
    (state y n).2.1 - (state y n).2.2 / (4 * (n : Rat) + 3) +
        (state y n).2.2 * y * y / (4 * (n : Rat) + 5) <=
      (state y n).2.1
  have hterm :
      (state y n).2.2 * y * y / (4 * (n : Rat) + 5) <=
        (state y n).2.2 / (4 * (n : Rat) + 3) := by
    rw [show (state y n).2.2 = powState y n by rfl, powState_eq]
    have hpow :
        y ^ (4 * n + 3) * y * y = y ^ (4 * n + 5) := by
      rw [show 4 * n + 5 = ((4 * n + 3) + 1) + 1 by omega]
      repeat rw [Rat.pow_succ]
    rw [hpow]
    exact term2_le_term1 hy0 hy1 n
  grind [Rat.sub_eq_add_neg]

theorem lo_mono {y : Rat}
    (hy0 : 0 <= y) (hy1 : y <= 1) {n m : Nat} (hnm : n <= m) :
    lo y n <= lo y m := by
  induction hnm with
  | refl =>
      exact Rat.le_refl
  | step hnm ih =>
      exact Rat.le_trans ih (lo_mono_succ hy0 hy1 _)

theorem hi_anti {y : Rat}
    (hy0 : 0 <= y) (hy1 : y <= 1) {n m : Nat} (hnm : n <= m) :
    hi y m <= hi y n := by
  induction hnm with
  | refl =>
      exact Rat.le_refl
  | step hnm ih =>
      exact Rat.le_trans (hi_anti_succ hy0 hy1 _) ih

theorem interval_ordered {y : Rat} (hy0 : 0 <= y) (n : Nat) :
    lo y n <= hi y n := by
  have hwidth := width_eq y n
  have hnonneg :
      0 <= y ^ (4 * n + 1) / (4 * (n : Rat) + 1) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.pow_nonneg hy0)
      (Rat.le_of_lt ((Rat.inv_pos).2 (by grind)))
  grind [Rat.sub_eq_add_neg]

theorem width_le_one_div {y : Rat}
    (hy0 : 0 <= y) (hy1 : y <= 1) (n : Nat) :
    ((positiveRaw y).compute n).width <=
      1 / (((4 * n + 1 : Nat) : Rat)) := by
  unfold positiveRaw QInterval.width
  rw [width_eq]
  have hden :
      4 * (n : Rat) + 1 = (((4 * n + 1 : Nat) : Rat)) := by
    exact_mod_cast (by rfl : 4 * n + 1 = 4 * n + 1)
  rw [hden]
  rw [Rat.div_def]
  have hpow : y ^ (4 * n + 1) <= 1 := by
    have hpowAll : forall k : Nat, y ^ k <= 1 := by
      intro k
      induction k with
      | zero =>
          simp
      | succ k ih =>
          rw [Rat.pow_succ]
          calc
            y ^ k * y <= y ^ k * 1 :=
              Rat.mul_le_mul_of_nonneg_left hy1 (Rat.pow_nonneg hy0)
            _ = y ^ k := by rw [Rat.mul_one]
            _ <= 1 := ih
    exact hpowAll _
  exact Rat.mul_le_mul_of_nonneg_right hpow
    (Rat.le_of_lt ((Rat.inv_pos).2
      ((Rat.natCast_pos).2 (by omega : 0 < 4 * n + 1))))

theorem widths_shrink {y : Rat}
    (hy0 : 0 <= y) (hy1 : y <= 1) :
    RealRaw.WidthsShrinkToZero (positiveRaw y).compute := by
  intro eps
  refine ⟨eps.val.den + 1, ?_⟩
  intro n hn
  have hwidth := width_le_one_div hy0 hy1 n
  have hone :
      1 / (((4 * n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    exact one_div_le_one_div_of_pos_of_le
      ((Rat.natCast_pos).2 (Nat.succ_pos eps.val.den))
      (by
        exact_mod_cast (by omega :
          eps.val.den + 1 <= 4 * n + 1))
  exact Rat.le_trans (Rat.le_trans hwidth hone)
    (FTC.one_div_den_succ_le_of_pos eps.property)

theorem positive_valid {y : Rat}
    (hy0 : 0 <= y) (hy1 : y <= 1) :
    (positiveRaw y).Valid := by
  constructor
  · intro n
    unfold positiveRaw QInterval.width
    have hordered := interval_ordered hy0 n
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      unfold positiveRaw
      constructor
      · exact lo_mono hy0 hy1 hnm
      · constructor
        · exact interval_ordered hy0 m
        · exact hi_anti hy0 hy1 hnm
    · exact widths_shrink hy0 hy1

theorem arctan_compute_nonneg (x : Rat) (hx : 0 <= x) (n : Nat) :
    (arctan x).compute n = (positiveRaw (qabs x)).compute n := by
  unfold arctan positiveRaw lo hi state
  simp [hx]

theorem arctan_compute_nonnegative_eq_kernelPartialIntegralInterval
    (x : Rat) (hx : 0 <= x) (n : Nat) :
    (arctan x).compute n =
      { lo := lowerKernelPartialAtStage x n,
        hi := upperKernelPartialAtStage x n } := by
  rw [arctan_compute_nonneg x hx n]
  have habs : qabs x = x := by
    unfold qabs
    have hnot : ¬x < 0 := by grind
    simp [hnot]
  rw [habs]
  exact positiveRaw_compute_eq_kernelPartialIntegralInterval x n

theorem arctan_compute_neg (x : Rat) (hx : Not (0 <= x)) (n : Nat) :
    (arctan x).compute n =
      RealRaw.negCompute (positiveRaw (qabs x)) n := by
  unfold arctan positiveRaw RealRaw.negCompute lo hi state
  simp [hx]

theorem validAt (x : Rat) (hx : arctanDomain x) :
    (arctan x).Valid := by
  let y := qabs x
  have hy0 : 0 <= y := by
    dsimp [y]
    exact qabs_nonneg x
  have hy1 : y <= 1 := by
    dsimp [y]
    unfold qabs
    by_cases hxneg : x < 0
    · simp [hxneg]
      have hlo : -1 <= x := hx.1
      grind
    · simp [hxneg]
      exact hx.2
  have hpos : (positiveRaw y).Valid := positive_valid hy0 hy1
  by_cases hx0 : 0 <= x
  · have hcompute :
        (arctan x).compute = (positiveRaw y).compute := by
      funext n
      dsimp [y]
      exact arctan_compute_nonneg x hx0 n
    simpa [RealRaw.Valid, hcompute] using hpos
  · have hneg :
        RealRaw.ValidCompute (RealRaw.negCompute (positiveRaw y)) :=
      RealRaw.negCompute_valid hpos
    have hcompute :
        (arctan x).compute = RealRaw.negCompute (positiveRaw y) := by
      funext n
      dsimp [y]
      exact arctan_compute_neg x hx0 n
    simpa [RealRaw.Valid, hcompute] using hneg

theorem valid : ArctanValid := by
  intro x hx
  simpa [RealFunRaw.applyCompute, arctanFunction] using validAt x hx

end ArctanValidity

theorem arctanValid : ArctanValid :=
  ArctanValidity.valid

def kernelComparisonAt_of_powerSeriesEqualsRectangleKernelAt
    {x : Rat} {hx0 : 0 <= x} {hx1 : x <= 1}
    (hps : PowerSeriesEqualsRectangleKernelAt x hx0 hx1) :
    Taylor.ArctanComparison.KernelComparisonAt x where
  domain := arctanKernel_unitDomain_of_nonnegativeUnit hx0 hx1
  integral := rectangleKernelIntegralAtNonnegativeUnit x hx0 hx1
  powerSeries_valid :=
    arctan_valid_at arctanValid
      (arctanDomain_of_nonnegativeUnit hx0 hx1)
  powerSeries_eq_kernel := hps
  geometric_eq_kernel :=
    arctanGeom_equiv_rectangleKernelIntegral_nonnegativeUnit x hx0 hx1

def kernelComparisonAtOne_of_powerSeriesEqualsRectangleKernelAtOne
    (hps : PowerSeriesEqualsRectangleKernelAtOne) :
    Taylor.ArctanComparison.KernelComparisonAt (1 : Rat) :=
  kernelComparisonAt_of_powerSeriesEqualsRectangleKernelAt hps

theorem machinValid : MachinValid :=
  machinValid_of_arctanValid arctanValid

/-- At a nonnegative series input, the literal arctangent evaluator has the
expected alternating-series width.  This makes convergence-rate statements
for concrete combinations such as Machin refer to their actual runtime boxes,
not to a transported equivalence. -/
theorem arctan_compute_width_eq_of_nonnegative
    (x : Rat) (hx : 0 <= x) (n : Nat) :
    ((arctan x).compute n).width =
      x ^ (4 * n + 1) / (4 * (n : Rat) + 1) := by
  rw [ArctanValidity.arctan_compute_nonneg x hx]
  rw [qabs_eq_self_of_nonneg hx]
  simpa [ArctanValidity.positiveRaw, QInterval.width] using
    ArctanValidity.width_eq x n

private theorem arctan_width_le_geometric_half
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) (hx4 : x ^ 4 <= (1 : Rat) / 2)
    (n : Nat) :
    ((arctan x).compute n).width <= ((1 : Rat) / 2) ^ n := by
  rw [arctan_compute_width_eq_of_nonnegative x hx0]
  have hpower : x ^ (4 * n + 1) <= ((1 : Rat) / 2) ^ n := by
    induction n with
    | zero =>
        simpa using hx1
    | succ n ih =>
        have hpow4_nonneg : 0 <= x ^ 4 := Rat.pow_nonneg hx0
        have hhalf_pow_nonneg : 0 <= ((1 : Rat) / 2) ^ n :=
          Rat.pow_nonneg (by native_decide)
        have hmul_left :
            x ^ (4 * n + 1) * x ^ 4 <=
              ((1 : Rat) / 2) ^ n * x ^ 4 :=
          Rat.mul_le_mul_of_nonneg_right ih hpow4_nonneg
        have hmul_right :
            ((1 : Rat) / 2) ^ n * x ^ 4 <=
              ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) :=
          Rat.mul_le_mul_of_nonneg_left hx4 hhalf_pow_nonneg
        have hmul := Rat.le_trans hmul_left hmul_right
        have hleft : x ^ (4 * (n + 1) + 1) =
            x ^ (4 * n + 1) * x ^ 4 := by
          rw [show 4 * (n + 1) + 1 =
            (((4 * n + 1) + 1) + 1) + 1 + 1 by omega]
          repeat rw [Rat.pow_succ]
          simp [Rat.pow_zero]
          grind [Rat.mul_assoc]
        have hright : ((1 : Rat) / 2) ^ (n + 1) =
            ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) := by
          rw [Rat.pow_succ]
        rw [hleft, hright]
        exact hmul
  have hdenpos : 0 < 4 * (n : Rat) + 1 := by
    have : (0 : Rat) <= 4 * (n : Rat) := by
      exact Rat.mul_nonneg (by native_decide) Rat.natCast_nonneg
    grind
  have hden_ge_one : (1 : Rat) <= 4 * (n : Rat) + 1 := by
    have hfour_n : (0 : Rat) <= 4 * (n : Rat) :=
      Rat.mul_nonneg (by native_decide) Rat.natCast_nonneg
    grind
  apply Rat.le_of_mul_le_mul_right (c := 4 * (n : Rat) + 1)
  · calc
      (x ^ (4 * n + 1) / (4 * (n : Rat) + 1)) *
          (4 * (n : Rat) + 1) =
          x ^ (4 * n + 1) := by
            rw [Rat.div_def]
            have hne : 4 * (n : Rat) + 1 ≠ 0 := Rat.ne_of_gt hdenpos
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= ((1 : Rat) / 2) ^ n := hpower
      _ <= ((1 : Rat) / 2) ^ n * (4 * (n : Rat) + 1) := by
        rw [show ((1 : Rat) / 2) ^ n =
          ((1 : Rat) / 2) ^ n * 1 by simp]
        have hhalf_pow_nonneg : 0 <= ((1 : Rat) / 2) ^ n :=
          Rat.pow_nonneg (by native_decide)
        simpa [Rat.mul_assoc] using
          (Rat.mul_le_mul_of_nonneg_left hden_ge_one hhalf_pow_nonneg)
  · exact hdenpos

private theorem arctan_one_fifth_width_le_geometric_half (n : Nat) :
    ((arctan ((1 : Rat) / 5)).compute n).width <= ((1 : Rat) / 2) ^ n := by
  apply arctan_width_le_geometric_half
  · native_decide
  · native_decide
  · native_decide

private theorem arctan_one_239_width_le_geometric_half (n : Nat) :
    ((arctan ((1 : Rat) / 239)).compute n).width <= ((1 : Rat) / 2) ^ n := by
  apply arctan_width_le_geometric_half
  · native_decide
  · native_decide
  · native_decide

/-- Exact width formula for the single Machin power-series computation. -/
theorem piMachin_compute_width_eq (n : Nat) :
    (piMachin.compute n).width =
      (16 : Rat) *
          (((1 : Rat) / 5) ^ (4 * n + 1) / (4 * (n : Rat) + 1)) +
        4 * (((1 : Rat) / 239) ^ (4 * n + 1) / (4 * (n : Rat) + 1)) := by
  unfold piMachin
  rw [RealRaw.natScale_width, RealRaw.sub_width, RealRaw.natScale_width,
    arctan_compute_width_eq_of_nonnegative ((1 : Rat) / 5) (by native_decide),
    arctan_compute_width_eq_of_nonnegative ((1 : Rat) / 239) (by native_decide)]
  have hfour : ((4 : Nat) : Rat) = 4 := by native_decide
  rw [hfour]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- The literal Machin power-series boxes contract geometrically.  The
constant is deliberately simple; the preceding exact formula is available
when a sharper cost estimate is useful. -/
theorem piMachin_compute_width_le_geometric_half (n : Nat) :
    (piMachin.compute n).width <= 20 * ((1 : Rat) / 2) ^ n := by
  rw [piMachin_compute_width_eq]
  have h15 := arctan_one_fifth_width_le_geometric_half n
  have h239 := arctan_one_239_width_le_geometric_half n
  rw [arctan_compute_width_eq_of_nonnegative ((1 : Rat) / 5)
    (by native_decide)] at h15
  rw [arctan_compute_width_eq_of_nonnegative ((1 : Rat) / 239)
    (by native_decide)] at h239
  have h16 : (16 : Rat) *
      (((1 : Rat) / 5) ^ (4 * n + 1) / (4 * (n : Rat) + 1)) <=
      16 * ((1 : Rat) / 2) ^ n :=
    Rat.mul_le_mul_of_nonneg_left h15 (by native_decide)
  have h4 : (4 : Rat) *
      (((1 : Rat) / 239) ^ (4 * n + 1) / (4 * (n : Rat) + 1)) <=
      4 * ((1 : Rat) / 2) ^ n :=
    Rat.mul_le_mul_of_nonneg_left h239 (by native_decide)
  calc
    (16 : Rat) *
          (((1 : Rat) / 5) ^ (4 * n + 1) / (4 * (n : Rat) + 1)) +
        4 * (((1 : Rat) / 239) ^ (4 * n + 1) / (4 * (n : Rat) + 1)) <=
      16 * ((1 : Rat) / 2) ^ n + 4 * ((1 : Rat) / 2) ^ n :=
        Rat.add_le_add h16 h4
    _ = 20 * ((1 : Rat) / 2) ^ n := by
      grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.mul_assoc]

/-- Public rate metadata for the one Machin formula. -/
def piMachinRate : RealRaw.Rate piMachin.compute :=
  .geometric 0 20 ((1 : Rat) / 2) (by native_decide) (by native_decide)
    (fun n _ => piMachin_compute_width_le_geometric_half n)

namespace LeibnizValidity

def step (state : Rat × Rat) (i : Nat) : Rat × Rat :=
  ⟨state.1 - 1 / (4 * (i : Rat) + 3) +
      1 / (4 * (i : Rat) + 5),
    state.1 - 1 / (4 * (i : Rat) + 3)⟩

def state (n : Nat) : Rat × Rat :=
  (List.range n).foldl
    (fun state (i : Nat) =>
      ⟨state.1 - 1 / (4 * (i : Rat) + 3) +
          1 / (4 * (i : Rat) + 5),
        state.1 - 1 / (4 * (i : Rat) + 3)⟩)
    ⟨1, 0⟩

def lo (n : Nat) : Rat :=
  (state n).2

def hi (n : Nat) : Rat :=
  (state n).1

theorem leibnizSeries_compute_eq (n : Nat) :
    leibnizSeries.compute n = { lo := lo n, hi := hi n } := by
  unfold leibnizSeries lo hi state
  simp

theorem compute_eq (n : Nat) :
    piLeibniz.compute n = { lo := 4 * lo n, hi := 4 * hi n } := by
  change (RealRaw.scaleRat (4 : Rat) leibnizSeries).compute n =
    { lo := 4 * lo n, hi := 4 * hi n }
  have h4 : (0 : Rat) <= 4 := by native_decide
  simp [RealRaw.scaleRat, RealRaw.scaleRatCompute, h4,
    leibnizSeries_compute_eq n]

theorem state_succ (n : Nat) :
    state (n + 1) = step (state n) n := by
  unfold state
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The Leibniz loop endpoints are the finite integrals of the odd/even
arctangent-kernel truncations over `[0,1]`.  This is the algebraic bridge that
turns the endpoint series into a finite polynomial-integral comparison. -/
theorem endpoints_eq_kernelPartialIntegral (n : Nat) :
    hi n = Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n) /\
      lo (n + 1) =
        Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n + 1) := by
  induction n with
  | zero =>
      constructor
      · simp [hi, state, Taylor.ArctanKernel.kernelPartialIntegralAtOne]
      · rw [lo, state_succ, step]
        simp [state, Taylor.ArctanKernel.kernelPartialIntegralAtOne,
          Taylor.ArctanKernel.kernelTermIntegralAtOne]
        native_decide
  | succ n ih =>
      have hloAsStep :
          hi n - 1 / (4 * (n : Rat) + 3) =
            Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n + 1) := by
        rw [←ih.2]
        rw [lo, state_succ, step]
        simp
        rw [show (state n).1 = hi n by rfl]
      have hhiSucc : hi (n + 1) =
          Taylor.ArctanKernel.kernelPartialIntegralAtOne
            (2 * (n + 1)) := by
        rw [hi, state_succ, step]
        simp
        rw [show (state n).1 = hi n by rfl]
        rw [hloAsStep]
        rw [show 2 * (n + 1) = 2 * n + 2 by omega]
        rw [Taylor.ArctanKernel.kernelPartialIntegralAtOne_even_succ]
      constructor
      · exact hhiSucc
      · rw [lo, state_succ, step]
        simp
        rw [show (state (n + 1)).1 = hi (n + 1) by rfl]
        rw [hhiSucc]
        rw [Taylor.ArctanKernel.kernelPartialIntegralAtOne_odd_succ]
        grind

theorem hi_eq_kernelPartialIntegral_even (n : Nat) :
    hi n = Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n) :=
  (endpoints_eq_kernelPartialIntegral n).1

theorem lo_eq_kernelPartialIntegral_odd_succ (n : Nat) :
    lo (n + 1) =
      Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n + 1) :=
  (endpoints_eq_kernelPartialIntegral n).2

def lowerKernelPartialAtStage : Nat -> Rat
  | 0 => 0
  | n + 1 => Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n + 1)

def upperKernelPartialAtStage (n : Nat) : Rat :=
  Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n)

theorem lo_eq_lowerKernelPartialAtStage (n : Nat) :
    lo n = lowerKernelPartialAtStage n := by
  cases n with
  | zero =>
      simp [lo, state, lowerKernelPartialAtStage]
  | succ n =>
      simp [lowerKernelPartialAtStage,
        lo_eq_kernelPartialIntegral_odd_succ n]

theorem hi_eq_upperKernelPartialAtStage (n : Nat) :
    hi n = upperKernelPartialAtStage n := by
  simp [upperKernelPartialAtStage, hi_eq_kernelPartialIntegral_even n]

theorem leibnizSeries_compute_eq_kernelPartialIntegralInterval (n : Nat) :
    leibnizSeries.compute n =
      { lo := lowerKernelPartialAtStage n,
        hi := upperKernelPartialAtStage n } := by
  rw [leibnizSeries_compute_eq n]
  simp [lo_eq_lowerKernelPartialAtStage, hi_eq_upperKernelPartialAtStage]

private theorem one_div_nat_le_one_div_nat_of_le
    {a b : Nat} (ha : 0 < a) (hab : a <= b) :
    1 / (b : Rat) <= 1 / (a : Rat) := by
  let A : Rat := (a : Rat)
  let B : Rat := (b : Rat)
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 ha
  have hBpos : 0 < B := by
    dsimp [B]
    exact (Rat.natCast_pos).2 (Nat.lt_of_lt_of_le ha hab)
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
  have hAcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
  have hABne : A * B ≠ 0 := by
    intro hzero
    rcases (Rat.mul_eq_zero).1 hzero with hzero | hzero
    · exact hAne hzero
    · exact hBne hzero
  have hABcancel : (A * B) * (A * B)⁻¹ = 1 :=
    Rat.mul_inv_cancel (A * B) hABne
  have hsixtyfourCancel : (64 : Rat) * (64 : Rat)⁻¹ = 1 := by
    native_decide
  have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
  have hAleB : A <= B := by
    dsimp [A, B]
    exact_mod_cast hab
  apply Rat.le_of_mul_le_mul_right (c := A * B)
  · calc
      (1 / B) * (A * B) = A := by
        rw [Rat.div_def]
        have hcancel : B * B⁻¹ = 1 := Rat.mul_inv_cancel B hBne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= B := hAleB
      _ = (1 / A) * (A * B) := by
        rw [Rat.div_def]
        have hcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hABpos

theorem width_eq (n : Nat) :
    hi n - lo n = 1 / ((4 * n + 1 : Nat) : Rat) := by
  induction n with
  | zero =>
      native_decide
  | succ n ih =>
      rw [hi, lo, state_succ, step]
      simp
      have hden :
          4 * ((n : Rat) + 1) + 1 = 4 * (n : Rat) + 5 := by
        grind
      rw [hden]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem lo_mono_succ (n : Nat) :
    lo n <= lo (n + 1) := by
  rw [lo, lo, state_succ, step]
  simp
  have hterm :
      1 / (4 * (n : Rat) + 3) <= (state n).1 - (state n).2 := by
    rw [show (state n).1 = hi n by rfl]
    rw [show (state n).2 = lo n by rfl]
    rw [width_eq n]
    have hden :
        (((4 * n + 3 : Nat) : Rat)) = 4 * (n : Rat) + 3 := by
      exact_mod_cast (by rfl : 4 * n + 3 = 4 * n + 3)
    rw [←hden]
    exact one_div_nat_le_one_div_nat_of_le
      (by omega : 0 < 4 * n + 1)
      (by omega : 4 * n + 1 <= 4 * n + 3)
  grind [Rat.sub_eq_add_neg]

theorem hi_anti_succ (n : Nat) :
    hi (n + 1) <= hi n := by
  rw [hi, hi, state_succ, step]
  simp
  have hterm :
      1 / (4 * (n : Rat) + 5) <=
        1 / (4 * (n : Rat) + 3) := by
    have hden5 :
        (((4 * n + 5 : Nat) : Rat)) = 4 * (n : Rat) + 5 := by
      exact_mod_cast (by rfl : 4 * n + 5 = 4 * n + 5)
    have hden3 :
        (((4 * n + 3 : Nat) : Rat)) = 4 * (n : Rat) + 3 := by
      exact_mod_cast (by rfl : 4 * n + 3 = 4 * n + 3)
    rw [←hden5, ←hden3]
    exact one_div_nat_le_one_div_nat_of_le
      (by omega : 0 < 4 * n + 3)
      (by omega : 4 * n + 3 <= 4 * n + 5)
  grind [Rat.sub_eq_add_neg]

theorem lo_mono {n m : Nat} (hnm : n <= m) :
    lo n <= lo m := by
  induction hnm with
  | refl =>
      exact Rat.le_refl
  | step hnm ih =>
      exact Rat.le_trans ih (lo_mono_succ _)

theorem hi_anti {n m : Nat} (hnm : n <= m) :
    hi m <= hi n := by
  induction hnm with
  | refl =>
      exact Rat.le_refl
  | step hnm ih =>
      exact Rat.le_trans (hi_anti_succ _) ih

theorem interval_ordered (n : Nat) :
    lo n <= hi n := by
  have hwidth := width_eq n
  have hpos : 0 < 1 / ((4 * n + 1 : Nat) : Rat) :=
    one_div_nat_pos (by omega : 0 < 4 * n + 1)
  grind [Rat.sub_eq_add_neg]

theorem compute_width_eq (n : Nat) :
    (piLeibniz.compute n).width =
      4 / ((4 * n + 1 : Nat) : Rat) := by
  rw [compute_eq]
  unfold QInterval.width
  have hwidth := width_eq n
  rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem widths_shrink : RealRaw.WidthsShrinkToZero piLeibniz.compute := by
  intro eps
  refine ⟨eps.val.den + 1, ?_⟩
  intro n hn
  rw [compute_width_eq n]
  have hfour :
      4 / ((4 * n + 1 : Nat) : Rat) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((4 * n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (by omega : 0 < 4 * n + 1)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : (4 : Rat) * B <= A := by
      dsimp [A, B]
      exact_mod_cast (by omega :
        4 * (eps.val.den + 1) <= 4 * n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (4 / A) * (A * B) = 4 * B := by
          rw [Rat.div_def]
          have hcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          have hcancel : B * B⁻¹ = 1 := Rat.mul_inv_cancel B hBne
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hABpos
  exact Rat.le_trans hfour (FTC.one_div_den_succ_le_of_pos eps.property)

theorem valid : LeibnizValid := by
  constructor
  · intro n
    rw [compute_width_eq n]
    rw [Rat.div_def]
    exact Rat.mul_nonneg
      (by native_decide : (0 : Rat) <= 4)
      (Rat.le_of_lt ((Rat.inv_pos).2
        ((Rat.natCast_pos).2 (by omega : 0 < 4 * n + 1))))
  · constructor
    · intro n m hnm
      rw [compute_eq n, compute_eq m]
      constructor
      · exact Rat.mul_le_mul_of_nonneg_left
          (lo_mono hnm) (by native_decide : (0 : Rat) <= 4)
      · constructor
        · exact Rat.mul_le_mul_of_nonneg_left
            (interval_ordered m) (by native_decide : (0 : Rat) <= 4)
        · exact Rat.mul_le_mul_of_nonneg_left
            (hi_anti hnm) (by native_decide : (0 : Rat) <= 4)
    · exact widths_shrink

end LeibnizValidity

theorem leibnizValid : LeibnizValid :=
  LeibnizValidity.valid

/-- A simple public rate bound for the literal Leibniz pi boxes. -/
theorem piLeibniz_compute_width_le_four_div (n : Nat) (hn : 0 < n) :
    (piLeibniz.compute n).width <= 4 / (n : Rat) := by
  rw [LeibnizValidity.compute_width_eq]
  have hdenpos : 0 < 4 * n + 1 := by omega
  have hreciprocal :
      1 / (((4 * n + 1 : Nat) : Rat)) <= 1 / (n : Rat) :=
    FTC.one_div_nat_antitone (Nat.pos_of_ne_zero (by omega)) hdenpos
      (by omega : n <= 4 * n + 1)
  have hscaled := Rat.mul_le_mul_of_nonneg_left hreciprocal
    (by native_decide : (0 : Rat) <= 4)
  calc
    4 / ((4 * n + 1 : Nat) : Rat) =
        (4 : Rat) * (1 / ((4 * n + 1 : Nat) : Rat)) := by
          rw [Rat.div_def]
          grind
    _ <= 4 * (1 / (n : Rat)) := hscaled
    _ = 4 / (n : Rat) := by simpa [Rat.div_def]

/-- Public rate metadata for the literal Leibniz series. -/
def piLeibnizRate : RealRaw.Rate piLeibniz.compute :=
  .power 1 4 1 (by omega)
    (fun n hn => by
      simpa using piLeibniz_compute_width_le_four_div n (by omega))

theorem leibnizSeriesValid : leibnizSeries.Valid := by
  exact RealRaw.valid_of_natScale_valid (by omega : 0 < (4 : Nat))
    (by simpa [piLeibniz] using leibnizValid)

theorem arctan_one_state_eq_leibniz_state (n : Nat) :
    ArctanValidity.state 1 n =
      (LeibnizValidity.lo n, LeibnizValidity.hi n, (1 : Rat)) := by
  induction n with
  | zero =>
      simp [ArctanValidity.state_zero, LeibnizValidity.lo, LeibnizValidity.hi,
        LeibnizValidity.state]
  | succ n ih =>
      rw [ArctanValidity.state_succ, ih]
      simp [LeibnizValidity.lo, LeibnizValidity.hi, LeibnizValidity.state_succ,
        LeibnizValidity.step]

/-- Stagewise equality between the Leibniz interval and the power-series
arctangent interval at `1`. -/
theorem leibnizSeries_compute_eq_arctan_one (n : Nat) :
    leibnizSeries.compute n = (arctan (1 : Rat)).compute n := by
  have hnonneg : (0 : Rat) <= 1 := by native_decide
  have hqabs : qabs (1 : Rat) = 1 := by native_decide
  rw [LeibnizValidity.leibnizSeries_compute_eq n]
  rw [ArctanValidity.arctan_compute_nonneg (1 : Rat) hnonneg n]
  rw [hqabs]
  simp [ArctanValidity.positiveRaw, ArctanValidity.lo,
    ArctanValidity.hi, arctan_one_state_eq_leibniz_state n]

/-- The Leibniz series is equivalent to the power-series arctangent at `1`.

The proof is by stagewise equality of the two algorithms, but the public
mathematical statement is equivalence of raw reals. -/
theorem leibnizSeries_equiv_arctan_one :
    leibnizSeries.Equiv (arctan (1 : Rat)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff leibnizSeries (arctan (1 : Rat)) n n).2
  rw [leibnizSeries_compute_eq_arctan_one n]
  have hx : (arctan (1 : Rat)).Valid :=
    arctan_valid_at arctanValid arctan_one_mem_domain
  have hnest := hx.2.1 n n (Nat.le_refl n)
  exact ⟨hnest.2.1, hnest.2.1⟩

/-- Stagewise equality between the Leibniz interval and the table-facing
`arctanSeries(1)` interval. -/
theorem leibnizSeries_compute_eq_arctanSeries_one (n : Nat) :
    leibnizSeries.compute n = (arctanSeries (1 : Rat)).compute n := by
  simpa [arctanSeries] using leibnizSeries_compute_eq_arctan_one n

/-- The Leibniz series is equivalent to the table-facing power-series
arctangent at `1`. -/
theorem leibnizSeries_equiv_arctanSeries_one :
    leibnizSeries.Equiv (arctanSeries (1 : Rat)) := by
  simpa [arctanSeries] using leibnizSeries_equiv_arctan_one

theorem arctanIntegralRectangleRawAtOne_compute_eq_raw_one (n : Nat) :
    ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n =
      (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)).compute n := rfl

theorem arctanIntegralRectangleRawAtOne_equiv_raw_one :
    ArctanGeometry.arctanIntegralRectangleRawAtOne.Equiv
      (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    ArctanGeometry.arctanIntegralRectangleRawAtOne
    (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)) n n).2
  change QInterval.Overlaps
    (ArctanGeometry.arctanIntegralRectangleCompute (1 : Rat) n)
    (ArctanGeometry.arctanIntegralRectangleCompute (1 : Rat) n)
  have hordered :=
    ArctanGeometry.arctanIntegralRectangleCompute_ordered
      (x := (1 : Rat)) (by native_decide) n
  unfold QInterval.Overlaps QInterval.width at *
  constructor <;> grind [Rat.sub_eq_add_neg]

def LeibnizEqualsRectangleRawAtOne : Prop :=
  leibnizSeries.Equiv (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat))

def LeibnizEqualsRectangleRawAtOneSpecial : Prop :=
  leibnizSeries.Equiv ArctanGeometry.arctanIntegralRectangleRawAtOne

/-- The finite rational inequalities that remain for comparing the Leibniz
endpoint truncations with the rectangle-sum integral at `1`.

At stage `n`, the Leibniz interval is already identified with the integrated
odd/even kernel truncations.  Thus the remaining proof can be stated without
completed reals: rectangle lower bound below the even truncation, and odd
truncation below rectangle upper bound. -/
def LeibnizRectangleKernelBoundsAtOne : Prop :=
  forall n,
    (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).lo <=
      LeibnizValidity.upperKernelPartialAtStage n /\
    LeibnizValidity.lowerKernelPartialAtStage n <=
      (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).hi

namespace LeibnizRectangleBridge

private theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) : a + c <= b + d := by
  grind

def kernelPartialIntegralSum (m : Nat) : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r m +
        kernelPartialIntegralSum m rest

/-- Right-endpoint sum for the finite arctangent-kernel polynomial on a
rational partition.  It is paired with `kernelPartialIntegralSum` below to
turn the cellwise Taylor estimate into a mesh-wide estimate. -/
def kernelPartialRightRectangleSum (m : Nat) : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      (r - p) * Taylor.ArctanKernel.kernelPartial r m +
        kernelPartialRightRectangleSum m rest

/-- Summing the finite polynomial cell estimates gives an explicit error bound
for any unit-interval mesh.  No limiting integral is used: both sides are
finite rational sums, and the error is controlled by the sum of squared cell
lengths. -/
theorem kernelPartialRightRectangleSum_error_bound
    {m : Nat} {intervals : List (Rat × Rat)}
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    -((m : Rat) * ((m + 1 : Nat) : Rat) *
        ArctanGeometry.intervalSquareSum intervals) <=
        kernelPartialRightRectangleSum m intervals -
          kernelPartialIntegralSum m intervals /\
      kernelPartialRightRectangleSum m intervals -
          kernelPartialIntegralSum m intervals <=
        (m : Rat) * ((m + 1 : Nat) : Rat) *
          ArctanGeometry.intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      constructor <;>
        simp [kernelPartialRightRectangleSum, kernelPartialIntegralSum,
          ArctanGeometry.intervalSquareSum] <;>
        grind [Rat.sub_eq_add_neg]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, hr1, hrest⟩
      have hp1 : p <= 1 := Rat.le_trans hpr hr1
      have hcell := Taylor.ArctanKernel.kernelPartial_rightRectangle_error_bound
        hp0 hp1 hpr hr1 m
      have htail := ih hrest
      let C : Rat := (m : Rat) * ((m + 1 : Nat) : Rat)
      have hrec :
          kernelPartialRightRectangleSum m ((p, r) :: rest) -
              kernelPartialIntegralSum m ((p, r) :: rest) =
            ((r - p) * Taylor.ArctanKernel.kernelPartial r m -
              Taylor.ArctanKernel.kernelPartialIntegralBetween p r m) +
            (kernelPartialRightRectangleSum m rest -
              kernelPartialIntegralSum m rest) := by
        simp only [kernelPartialRightRectangleSum, kernelPartialIntegralSum]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      rw [hrec]
      constructor
      · calc
          -((m : Rat) * ((m + 1 : Nat) : Rat) *
              ArctanGeometry.intervalSquareSum ((p, r) :: rest)) =
              -(C * (r - p) * (r - p)) +
                -(C * ArctanGeometry.intervalSquareSum rest) := by
                  simp only [ArctanGeometry.intervalSquareSum]
                  dsimp [C]
                  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
          _ <= ((r - p) * Taylor.ArctanKernel.kernelPartial r m -
              Taylor.ArctanKernel.kernelPartialIntegralBetween p r m) +
              (kernelPartialRightRectangleSum m rest -
                kernelPartialIntegralSum m rest) := by
                  exact rat_add_le_add hcell.1 htail.1
      · calc
          ((r - p) * Taylor.ArctanKernel.kernelPartial r m -
              Taylor.ArctanKernel.kernelPartialIntegralBetween p r m) +
              (kernelPartialRightRectangleSum m rest -
                kernelPartialIntegralSum m rest) <=
              C * (r - p) * (r - p) +
                C * ArctanGeometry.intervalSquareSum rest := by
                  exact rat_add_le_add hcell.2 htail.2
          _ = (m : Rat) * ((m + 1 : Nat) : Rat) *
              ArctanGeometry.intervalSquareSum ((p, r) :: rest) := by
                simp only [ArctanGeometry.intervalSquareSum]
                dsimp [C]
                grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                  Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

def EvenKernelCellBounds (m : Nat) : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest =>
      ArctanGeometry.integralLowerStep p r <=
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r m /\
      EvenKernelCellBounds m rest

def OddKernelCellBounds (m : Nat) : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest =>
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r m <=
        ArctanGeometry.integralUpperStep p r /\
      OddKernelCellBounds m rest

def EvenKernelCellBound (m : Nat) : Prop :=
  forall {p r : Rat}, 0 <= p -> p <= r -> r <= 1 ->
    ArctanGeometry.integralLowerStep p r <=
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r m

def OddKernelCellBound (m : Nat) : Prop :=
  forall {p r : Rat}, 0 <= p -> p <= r ->
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r m <=
      ArctanGeometry.integralUpperStep p r

def OddKernelUnitCellBound (m : Nat) : Prop :=
  forall {p r : Rat}, 0 <= p -> p <= r -> r <= 1 ->
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r m <=
      ArctanGeometry.integralUpperStep p r

def EvenKernelPointwiseCellBound (m : Nat) : Prop :=
  forall {p x r : Rat}, 0 <= p -> p <= x -> x <= r ->
    ArctanGeometry.integralKernel r <=
      Taylor.ArctanKernel.kernelPartial x m

def OddKernelPointwiseCellBound (m : Nat) : Prop :=
  forall {p x r : Rat}, 0 <= p -> p <= x -> x <= r ->
    Taylor.ArctanKernel.kernelPartial x m <=
      ArctanGeometry.integralKernel p

private instance evenKernelCellBoundsDecidable (m : Nat) :
    (intervals : List (Rat × Rat)) -> Decidable (EvenKernelCellBounds m intervals)
  | [] => isTrue trivial
  | (p, r) :: rest => by
      dsimp [EvenKernelCellBounds]
      exact @instDecidableAnd
        (ArctanGeometry.integralLowerStep p r <=
          Taylor.ArctanKernel.kernelPartialIntegralBetween p r m)
        (EvenKernelCellBounds m rest)
        inferInstance
        (evenKernelCellBoundsDecidable m rest)

private instance oddKernelCellBoundsDecidable (m : Nat) :
    (intervals : List (Rat × Rat)) -> Decidable (OddKernelCellBounds m intervals)
  | [] => isTrue trivial
  | (p, r) :: rest => by
      dsimp [OddKernelCellBounds]
      exact @instDecidableAnd
        (Taylor.ArctanKernel.kernelPartialIntegralBetween p r m <=
          ArctanGeometry.integralUpperStep p r)
        (OddKernelCellBounds m rest)
        inferInstance
        (oddKernelCellBoundsDecidable m rest)

def LeibnizRectangleUniformCellBoundsAtOne : Prop :=
  (forall n, EvenKernelCellBound (2 * n)) /\
  (forall n, OddKernelCellBound (2 * n + 1))

def LeibnizRectangleUniformUnitCellBoundsAtOne : Prop :=
  (forall n, EvenKernelCellBound (2 * n)) /\
  (forall n, OddKernelUnitCellBound (2 * n + 1))

def LeibnizRectangleUniformUnitCellBoundsAtOneUpTo (N : Nat) : Prop :=
  (forall n, n <= N -> EvenKernelCellBound (2 * n)) /\
  (forall n, n <= N -> OddKernelUnitCellBound (2 * n + 1))

def LeibnizRectangleUniformUnitCellBoundsAtOneUpToAll : Prop :=
  forall N, LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N

def LeibnizRectanglePointwiseCellBoundsAtOne : Prop :=
  (forall n, EvenKernelPointwiseCellBound (2 * n)) /\
  (forall n, OddKernelPointwiseCellBound (2 * n + 1))

def LeibnizRectanglePointwiseIntegralBridgeAtOne : Prop :=
  LeibnizRectanglePointwiseCellBoundsAtOne ->
    LeibnizRectangleUniformCellBoundsAtOne

def LeibnizRectanglePointwiseUnitIntegralBridgeAtOne : Prop :=
  LeibnizRectanglePointwiseCellBoundsAtOne ->
    LeibnizRectangleUniformUnitCellBoundsAtOne

/-- Calculus-facing order target for the Leibniz/rectangle comparison.

The pointwise kernel inequalities are already proved below.  What remains is
the integral order theorem on each rational unit cell: integrating a pointwise
lower bound gives a lower bound for the exact partial-kernel integral, and
integrating a pointwise upper bound gives the corresponding upper rectangle
bound. -/
def LeibnizRectangleUnitCellOrderPreservation : Prop :=
  (forall m, EvenKernelPointwiseCellBound m -> EvenKernelCellBound m) /\
  (forall m, OddKernelPointwiseCellBound m -> OddKernelUnitCellBound m)

/-- Exact cell-order preservation specialized to the arctangent-kernel
polynomial partial integrals on `[0,1]`.

This is the compact calculus target behind the Leibniz/rectangle comparison:
pointwise lower and upper bounds for a finite kernel partial may be integrated
over any rational unit cell. -/
def KernelPartialExactCellOrderPreservationOnUnit : Prop :=
  forall m,
    Integral.ExactCellOrderPreservation
      (fun x => Taylor.ArctanKernel.kernelPartial x m)
      (fun p r => Taylor.ArctanKernel.kernelPartialIntegralBetween p r m)
      0 1

/-- The constant zeroth kernel partial already has exact cell-order
preservation.  This is the base case of the all-partials calculus target. -/
theorem kernelPartialExactCellOrderPreservation_zero :
    Integral.ExactCellOrderPreservation
      (fun x => Taylor.ArctanKernel.kernelPartial x 0)
      (fun p r => Taylor.ArctanKernel.kernelPartialIntegralBetween p r 0)
      0 1 := by
  simpa [Taylor.ArctanKernel.kernelPartial,
    Taylor.ArctanKernel.altGeomPartial,
    Taylor.ArctanKernel.kernelPartialIntegralBetween] using
    (Integral.exactCellOrderPreservation_constant
      (0 : Rat) (1 : Rat) (1 : Rat))

/-- The first nonconstant kernel partial has exact cell-order preservation on
`[0,1]`.  Its gap from each endpoint rectangle factors into nonnegative
rational terms. -/
theorem kernelPartialExactCellOrderPreservation_one :
    Integral.ExactCellOrderPreservation
      (fun x => Taylor.ArctanKernel.kernelPartial x 1)
      (fun p r => Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1)
      0 1 := by
  have hkernel_one (x : Rat) :
      Taylor.ArctanKernel.kernelPartial x 1 = 1 - x * x := by
    simp [Taylor.ArctanKernel.kernelPartial,
      Taylor.ArctanKernel.altGeomPartial]
    grind [Rat.sub_eq_add_neg]
  constructor
  · intro p r c hp0 hpr _hr1 hbound
    let L : Rat := r - p
    let S : Rat := r * r + r * p + p * p
    have hr0 : 0 <= r := Rat.le_trans hp0 hpr
    have hL0 : 0 <= L := by
      dsimp [L]
      grind [Rat.sub_eq_add_neg]
    have hformula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcube : r ^ 3 - p ^ 3 = L * S := by
      dsimp [L, S]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hmul :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 * 3 =
          L * (3 - S) := by
      rw [hformula, hcube, Rat.div_def]
      dsimp [L, S]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel]
    have hfactor : 0 <= (r - p) * (2 * r + p) := by
      exact Rat.mul_nonneg
        (by grind [Rat.sub_eq_add_neg])
        (Rat.add_nonneg
          (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hr0) hp0)
    have hinner : 3 * (1 - r * r) <= 3 - S := by
      have hidentity :
          (3 - S) - 3 * (1 - r * r) = (r - p) * (2 * r + p) := by
        dsimp [S]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      grind [Rat.sub_eq_add_neg]
    have hrectangle :
        L * (1 - r * r) <=
          Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 := by
      apply Rat.le_of_mul_le_mul_right (c := 3)
      · calc
          L * (1 - r * r) * 3 = L * (3 * (1 - r * r)) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
          _ <= L * (3 - S) := Rat.mul_le_mul_of_nonneg_left hinner hL0
          _ = Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 * 3 :=
            hmul.symm
      · native_decide
    have hc : c <= 1 - r * r := by
      simpa [hkernel_one] using hbound hpr (Rat.le_refl : r <= r)
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hc hL0) hrectangle
  · intro p r c hp0 hpr _hr1 hbound
    let L : Rat := r - p
    let S : Rat := r * r + r * p + p * p
    have hr0 : 0 <= r := Rat.le_trans hp0 hpr
    have hL0 : 0 <= L := by
      dsimp [L]
      grind [Rat.sub_eq_add_neg]
    have hformula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcube : r ^ 3 - p ^ 3 = L * S := by
      dsimp [L, S]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hmul :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 * 3 =
          L * (3 - S) := by
      rw [hformula, hcube, Rat.div_def]
      dsimp [L, S]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel]
    have hfactor : 0 <= (r - p) * (r + 2 * p) := by
      exact Rat.mul_nonneg
        (by grind [Rat.sub_eq_add_neg])
        (Rat.add_nonneg hr0
          (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hp0))
    have hinner : 3 - S <= 3 * (1 - p * p) := by
      have hidentity :
          3 * (1 - p * p) - (3 - S) = (r - p) * (r + 2 * p) := by
        dsimp [S]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      grind [Rat.sub_eq_add_neg]
    have hrectangle :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 <=
          L * (1 - p * p) := by
      apply Rat.le_of_mul_le_mul_right (c := 3)
      · calc
          Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 * 3 =
              L * (3 - S) := hmul
          _ <= L * (3 * (1 - p * p)) :=
            Rat.mul_le_mul_of_nonneg_left hinner hL0
          _ = L * (1 - p * p) * 3 := by
            grind [Rat.mul_assoc, Rat.mul_comm]
      · native_decide
    have hc : 1 - p * p <= c := by
      simpa [hkernel_one] using hbound (Rat.le_refl : p <= p) hpr
    exact Rat.le_trans hrectangle (Rat.mul_le_mul_of_nonneg_left hc hL0)

private theorem kernelPartialIntegralBetween_two_boole
    (p r : Rat) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 2 =
      ((r - p) / 90) *
        (7 * Taylor.ArctanKernel.kernelPartial p 2 +
          32 * Taylor.ArctanKernel.kernelPartial (p + (r - p) / 4) 2 +
          12 * Taylor.ArctanKernel.kernelPartial (p + (r - p) / 2) 2 +
          32 * Taylor.ArctanKernel.kernelPartial
            (p + 3 * (r - p) / 4) 2 +
          7 * Taylor.ArctanKernel.kernelPartial r 2) := by
  simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
    Taylor.ArctanKernel.kernelTermIntegralBetween,
    Taylor.ArctanKernel.kernelPartial,
    Taylor.ArctanKernel.altGeomPartial]
  grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ, Rat.mul_inv_cancel]

/-- The degree-four kernel partial has exact cell-order preservation on `[0,1]`.
This instance is obtained from its positive rational Boole quadrature identity. -/
theorem kernelPartialExactCellOrderPreservation_two :
    Integral.ExactCellOrderPreservation
      (fun x => Taylor.ArctanKernel.kernelPartial x 2)
      (fun p r => Taylor.ArctanKernel.kernelPartialIntegralBetween p r 2)
      0 1 := by
  apply Integral.exactCellOrderPreservation_of_boole (a := (0 : Rat)) (b := 1)
  intro p r
  exact kernelPartialIntegralBetween_two_boole p r

private theorem affine_pow_two (p t L : Rat) :
    (p + t * L) ^ 2 =
      p ^ 2 + 2 * p * t * L + t ^ 2 * L ^ 2 := by
  repeat rw [Rat.pow_succ]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

private theorem affine_pow_four (p t L : Rat) :
    (p + t * L) ^ 4 =
      p ^ 4 + 4 * p ^ 3 * t * L + 6 * p ^ 2 * t ^ 2 * L ^ 2 +
        4 * p * t ^ 3 * L ^ 3 + t ^ 4 * L ^ 4 := by
  repeat rw [Rat.pow_succ]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

private theorem affine_pow_six (p t L : Rat) :
    (p + t * L) ^ 6 =
      p ^ 6 + 6 * p ^ 5 * t * L + 15 * p ^ 4 * t ^ 2 * L ^ 2 +
        20 * p ^ 3 * t ^ 3 * L ^ 3 + 15 * p ^ 2 * t ^ 4 * L ^ 4 +
          6 * p * t ^ 5 * L ^ 5 + t ^ 6 * L ^ 6 := by
  repeat rw [Rat.pow_succ]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

private def affineMoment : List (Rat × Rat) -> Nat -> Rat
  | [], _ => 0
  | (node, weight) :: rest, k => weight * node ^ k + affineMoment rest k

private def affinePowerSum (p L : Rat) (k : Nat) : List (Rat × Rat) -> Rat
  | [] => 0
  | (node, weight) :: rest =>
      weight * (p + node * L) ^ k + affinePowerSum p L k rest

private theorem affinePowerSum_two_eq_moments (p L : Rat) :
    forall nodes : List (Rat × Rat),
      affinePowerSum p L 2 nodes =
        affineMoment nodes 0 * p ^ 2 +
          2 * affineMoment nodes 1 * p * L +
          affineMoment nodes 2 * L ^ 2
  | [] => by
      simp [affinePowerSum, affineMoment]
      grind
  | (node, weight) :: rest => by
      simp only [affinePowerSum, affineMoment]
      rw [affine_pow_two p node L]
      rw [affinePowerSum_two_eq_moments p L rest]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]

private theorem affinePowerSum_four_eq_moments (p L : Rat) :
    forall nodes : List (Rat × Rat),
      affinePowerSum p L 4 nodes =
        affineMoment nodes 0 * p ^ 4 +
          4 * affineMoment nodes 1 * p ^ 3 * L +
          6 * affineMoment nodes 2 * p ^ 2 * L ^ 2 +
          4 * affineMoment nodes 3 * p * L ^ 3 +
          affineMoment nodes 4 * L ^ 4
  | [] => by
      simp [affinePowerSum, affineMoment]
      grind
  | (node, weight) :: rest => by
      simp only [affinePowerSum, affineMoment]
      rw [affine_pow_four p node L]
      rw [affinePowerSum_four_eq_moments p L rest]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]

private theorem affinePowerSum_six_eq_moments (p L : Rat) :
    forall nodes : List (Rat × Rat),
      affinePowerSum p L 6 nodes =
        affineMoment nodes 0 * p ^ 6 +
          6 * affineMoment nodes 1 * p ^ 5 * L +
          15 * affineMoment nodes 2 * p ^ 4 * L ^ 2 +
          20 * affineMoment nodes 3 * p ^ 3 * L ^ 3 +
          15 * affineMoment nodes 4 * p ^ 2 * L ^ 4 +
          6 * affineMoment nodes 5 * p * L ^ 5 +
          affineMoment nodes 6 * L ^ 6
  | [] => by
      simp [affinePowerSum, affineMoment]
      grind
  | (node, weight) :: rest => by
      simp only [affinePowerSum, affineMoment]
      rw [affine_pow_six p node L]
      rw [affinePowerSum_six_eq_moments p L rest]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]

private def sevenPointNewtonCotesNodes : List (Rat × Rat) :=
  [(0, 41 / 840), (1 / 6, 9 / 35), (1 / 3, 9 / 280),
    (1 / 2, 34 / 105), (2 / 3, 9 / 280), (5 / 6, 9 / 35),
    (1, 41 / 840)]

private theorem sevenPointNewtonCotes_moment_zero :
    affineMoment sevenPointNewtonCotesNodes 0 = 1 := by native_decide

private theorem sevenPointNewtonCotes_moment_one :
    affineMoment sevenPointNewtonCotesNodes 1 = 1 / 2 := by native_decide

private theorem sevenPointNewtonCotes_moment_two :
    affineMoment sevenPointNewtonCotesNodes 2 = 1 / 3 := by native_decide

private theorem sevenPointNewtonCotes_moment_three :
    affineMoment sevenPointNewtonCotesNodes 3 = 1 / 4 := by native_decide

private theorem sevenPointNewtonCotes_moment_four :
    affineMoment sevenPointNewtonCotesNodes 4 = 1 / 5 := by native_decide

private theorem sevenPointNewtonCotes_moment_five :
    affineMoment sevenPointNewtonCotesNodes 5 = 1 / 6 := by native_decide

private theorem sevenPointNewtonCotes_moment_six :
    affineMoment sevenPointNewtonCotesNodes 6 = 1 / 7 := by native_decide

private theorem sevenPointNewtonCotes_zero_expansion (p L : Rat) :
    affinePowerSum p L 0 sevenPointNewtonCotesNodes = 1 := by
  simp [affinePowerSum, sevenPointNewtonCotesNodes]
  native_decide

private theorem sevenPointNewtonCotes_two_expansion (p L : Rat) :
    affinePowerSum p L 2 sevenPointNewtonCotesNodes =
      p ^ 2 + p * L + (1 / 3) * L ^ 2 := by
  rw [affinePowerSum_two_eq_moments,
    sevenPointNewtonCotes_moment_zero,
    sevenPointNewtonCotes_moment_one,
    sevenPointNewtonCotes_moment_two]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem sevenPointNewtonCotes_four_expansion (p L : Rat) :
    affinePowerSum p L 4 sevenPointNewtonCotesNodes =
      p ^ 4 + 2 * p ^ 3 * L + 2 * p ^ 2 * L ^ 2 +
        p * L ^ 3 + (1 / 5) * L ^ 4 := by
  rw [affinePowerSum_four_eq_moments,
    sevenPointNewtonCotes_moment_zero,
    sevenPointNewtonCotes_moment_one,
    sevenPointNewtonCotes_moment_two,
    sevenPointNewtonCotes_moment_three,
    sevenPointNewtonCotes_moment_four]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem sevenPointNewtonCotes_six_expansion (p L : Rat) :
    affinePowerSum p L 6 sevenPointNewtonCotesNodes =
      p ^ 6 + 3 * p ^ 5 * L + 5 * p ^ 4 * L ^ 2 +
        5 * p ^ 3 * L ^ 3 + 3 * p ^ 2 * L ^ 4 +
          p * L ^ 5 + (1 / 7) * L ^ 6 := by
  rw [affinePowerSum_six_eq_moments,
    sevenPointNewtonCotes_moment_zero,
    sevenPointNewtonCotes_moment_one,
    sevenPointNewtonCotes_moment_two,
    sevenPointNewtonCotes_moment_three,
    sevenPointNewtonCotes_moment_four,
    sevenPointNewtonCotes_moment_five,
    sevenPointNewtonCotes_moment_six]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private def kernelThreeAverage (p L : Rat) : Rat :=
  1 - (p ^ 2 + p * L + (1 / 3) * L ^ 2) +
    (p ^ 4 + 2 * p ^ 3 * L + 2 * p ^ 2 * L ^ 2 +
      p * L ^ 3 + (1 / 5) * L ^ 4) -
      (p ^ 6 + 3 * p ^ 5 * L + 5 * p ^ 4 * L ^ 2 +
        5 * p ^ 3 * L ^ 3 + 3 * p ^ 2 * L ^ 4 +
          p * L ^ 5 + (1 / 7) * L ^ 6)

private theorem sevenPointNewtonCotes_kernel_three_expansion (p L : Rat) :
    affinePowerSum p L 0 sevenPointNewtonCotesNodes -
      affinePowerSum p L 2 sevenPointNewtonCotesNodes +
        affinePowerSum p L 4 sevenPointNewtonCotesNodes -
          affinePowerSum p L 6 sevenPointNewtonCotesNodes =
      kernelThreeAverage p L := by
  rw [sevenPointNewtonCotes_zero_expansion,
    sevenPointNewtonCotes_two_expansion,
    sevenPointNewtonCotes_four_expansion,
    sevenPointNewtonCotes_six_expansion]
  rfl

private theorem monomialIntegralTwo (p r : Rat) :
    (r ^ 3 - p ^ 3) / 3 =
      (r - p) * (p ^ 2 + p * (r - p) + (1 / 3) * (r - p) ^ 2) := by
  let L : Rat := r - p
  have hr : r = p + L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  rw [hr]
  dsimp [L]
  repeat rw [Rat.pow_succ]
  rw [Rat.div_def]
  have h3 : (3 : Rat) ≠ 0 := by native_decide
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

private theorem monomialIntegralFour (p r : Rat) :
    (r ^ 5 - p ^ 5) / 5 =
      (r - p) * (p ^ 4 + 2 * p ^ 3 * (r - p) +
        2 * p ^ 2 * (r - p) ^ 2 + p * (r - p) ^ 3 +
          (1 / 5) * (r - p) ^ 4) := by
  let L : Rat := r - p
  have hr : r = p + L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  rw [hr]
  dsimp [L]
  repeat rw [Rat.pow_succ]
  rw [Rat.div_def]
  have h5 : (5 : Rat) ≠ 0 := by native_decide
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

private theorem monomialIntegralSix (p r : Rat) :
    (r ^ 7 - p ^ 7) / 7 =
      (r - p) * (p ^ 6 + 3 * p ^ 5 * (r - p) +
        5 * p ^ 4 * (r - p) ^ 2 + 5 * p ^ 3 * (r - p) ^ 3 +
          3 * p ^ 2 * (r - p) ^ 4 + p * (r - p) ^ 5 +
            (1 / 7) * (r - p) ^ 6) := by
  let L : Rat := r - p
  have hr : r = p + L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  rw [hr]
  dsimp [L]
  repeat rw [Rat.pow_succ]
  rw [Rat.div_def]
  have h7 : (7 : Rat) ≠ 0 := by native_decide
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

private theorem kernelPartialIntegralThree_eq_average (p r : Rat) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 3 =
      (r - p) * kernelThreeAverage p (r - p) := by
  have h2 := monomialIntegralTwo p r
  have h4 := monomialIntegralFour p r
  have h6 := monomialIntegralSix p r
  simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
    Taylor.ArctanKernel.kernelTermIntegralBetween]
  have hden1 : (2 : Rat) + 1 = 3 := by native_decide
  have hden2 : (2 : Rat) * 2 + 1 = 5 := by native_decide
  have hden3 : (2 : Rat) * 3 + 1 = 7 := by native_decide
  have hneg2 : (-1 : Rat) ^ 2 = 1 := by native_decide
  have hneg3 : (-1 : Rat) ^ 3 = -1 := by native_decide
  have hnegmul (x : Rat) : (-1 : Rat) * x = -x := by
    change -(1 : Rat) * x = -x
    rw [Rat.neg_mul, Rat.one_mul]
  have hnegdiv (x d : Rat) : -x / d = -(x / d) := by
    rw [Rat.div_def, Rat.div_def, Rat.neg_mul]
  rw [hden1, hden2, hden3, hneg2, hneg3]
  rw [hnegmul, Rat.one_mul, hnegmul]
  rw [hnegdiv, hnegdiv]
  rw [h2, h4, h6]
  unfold kernelThreeAverage
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem kernelPartial_three_formula (x : Rat) :
    Taylor.ArctanKernel.kernelPartial x 3 = 1 - x ^ 2 + x ^ 4 - x ^ 6 := by
  simp [Taylor.ArctanKernel.kernelPartial,
    Taylor.ArctanKernel.altGeomPartial]
  grind [Rat.sub_eq_add_neg]

private theorem quadratureEvalSum_kernelPartial_three_eq_affine
    (p r : Rat) :
    forall nodes : List (Rat × Rat),
      Integral.quadratureEvalSum
          (fun x => Taylor.ArctanKernel.kernelPartial x 3) p r nodes =
        affinePowerSum p (r - p) 0 nodes -
          affinePowerSum p (r - p) 2 nodes +
            affinePowerSum p (r - p) 4 nodes -
              affinePowerSum p (r - p) 6 nodes
  | [] => by
      simp [Integral.quadratureEvalSum, affinePowerSum]
      grind
  | (node, weight) :: rest => by
      simp only [Integral.quadratureEvalSum, affinePowerSum]
      rw [kernelPartial_three_formula]
      rw [quadratureEvalSum_kernelPartial_three_eq_affine p r rest]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem kernelPartialIntegralThree_newtonCotes (p r : Rat) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 3 =
      (r - p) * Integral.quadratureEvalSum
        (fun x => Taylor.ArctanKernel.kernelPartial x 3) p r
        sevenPointNewtonCotesNodes := by
  rw [kernelPartialIntegralThree_eq_average]
  rw [← sevenPointNewtonCotes_kernel_three_expansion]
  rw [← quadratureEvalSum_kernelPartial_three_eq_affine]

/-- The degree-six kernel partial has exact cell-order preservation on `[0,1]`.
This instance is obtained from a positive seven-point rational Newton--Cotes
quadrature identity. -/
theorem kernelPartialExactCellOrderPreservation_three :
    Integral.ExactCellOrderPreservation
      (fun x => Taylor.ArctanKernel.kernelPartial x 3)
      (fun p r => Taylor.ArctanKernel.kernelPartialIntegralBetween p r 3)
      0 1 := by
  apply Integral.exactCellOrderPreservation_of_positive_quadrature
    (a := (0 : Rat)) (b := 1) sevenPointNewtonCotesNodes
  · intro pair hmem
    simp only [sevenPointNewtonCotesNodes, List.mem_cons, List.not_mem_nil] at hmem
    rcases hmem with h | h | h | h | h | h | h | h
    all_goals try contradiction
    all_goals subst pair <;> constructor <;> native_decide
  · intro pair hmem
    simp only [sevenPointNewtonCotesNodes, List.mem_cons, List.not_mem_nil] at hmem
    rcases hmem with h | h | h | h | h | h | h | h
    all_goals try contradiction
    all_goals subst pair <;> native_decide
  · native_decide
  · intro p r
    exact kernelPartialIntegralThree_newtonCotes p r

private theorem affine_pow_eight (p t L : Rat) :
    (p + t * L) ^ 8 =
      p ^ 8 + 8 * p ^ 7 * t * L + 28 * p ^ 6 * t ^ 2 * L ^ 2 +
        56 * p ^ 5 * t ^ 3 * L ^ 3 + 70 * p ^ 4 * t ^ 4 * L ^ 4 +
          56 * p ^ 3 * t ^ 5 * L ^ 5 + 28 * p ^ 2 * t ^ 6 * L ^ 6 +
            8 * p * t ^ 7 * L ^ 7 + t ^ 8 * L ^ 8 := by
  repeat rw [Rat.pow_succ]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

private theorem affinePowerSum_eight_eq_moments (p L : Rat) :
    forall nodes : List (Rat × Rat),
      affinePowerSum p L 8 nodes =
        affineMoment nodes 0 * p ^ 8 +
          8 * affineMoment nodes 1 * p ^ 7 * L +
          28 * affineMoment nodes 2 * p ^ 6 * L ^ 2 +
          56 * affineMoment nodes 3 * p ^ 5 * L ^ 3 +
          70 * affineMoment nodes 4 * p ^ 4 * L ^ 4 +
          56 * affineMoment nodes 5 * p ^ 3 * L ^ 5 +
          28 * affineMoment nodes 6 * p ^ 2 * L ^ 6 +
          8 * affineMoment nodes 7 * p * L ^ 7 +
          affineMoment nodes 8 * L ^ 8
  | [] => by
      simp [affinePowerSum, affineMoment]
      grind
  | (node, weight) :: rest => by
      simp only [affinePowerSum, affineMoment]
      rw [affine_pow_eight p node L]
      rw [affinePowerSum_eight_eq_moments p L rest]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]

private def elevenPointNewtonCotesNodes : List (Rat × Rat) :=
  [(0, 167287 / 5715360), (1 / 10, 21887 / 142884),
    (1 / 5, 403 / 14112), (3 / 10, 1937 / 11907),
    (2 / 5, 2077 / 27216), (1 / 2, 1 / 10),
    (3 / 5, 2077 / 27216), (7 / 10, 1937 / 11907),
    (4 / 5, 403 / 14112), (9 / 10, 21887 / 142884),
    (1, 167287 / 5715360)]

private theorem elevenPointNewtonCotes_moment_zero :
    affineMoment elevenPointNewtonCotesNodes 0 = 1 := by native_decide

private theorem elevenPointNewtonCotes_moment_one :
    affineMoment elevenPointNewtonCotesNodes 1 = 1 / 2 := by native_decide

private theorem elevenPointNewtonCotes_moment_two :
    affineMoment elevenPointNewtonCotesNodes 2 = 1 / 3 := by native_decide

private theorem elevenPointNewtonCotes_moment_three :
    affineMoment elevenPointNewtonCotesNodes 3 = 1 / 4 := by native_decide

private theorem elevenPointNewtonCotes_moment_four :
    affineMoment elevenPointNewtonCotesNodes 4 = 1 / 5 := by native_decide

private theorem elevenPointNewtonCotes_moment_five :
    affineMoment elevenPointNewtonCotesNodes 5 = 1 / 6 := by native_decide

private theorem elevenPointNewtonCotes_moment_six :
    affineMoment elevenPointNewtonCotesNodes 6 = 1 / 7 := by native_decide

private theorem elevenPointNewtonCotes_moment_seven :
    affineMoment elevenPointNewtonCotesNodes 7 = 1 / 8 := by native_decide

private theorem elevenPointNewtonCotes_moment_eight :
    affineMoment elevenPointNewtonCotesNodes 8 = 1 / 9 := by native_decide

private theorem elevenPointNewtonCotes_zero_expansion (p L : Rat) :
    affinePowerSum p L 0 elevenPointNewtonCotesNodes = 1 := by
  simp [affinePowerSum, elevenPointNewtonCotesNodes]
  native_decide

private theorem elevenPointNewtonCotes_two_expansion (p L : Rat) :
    affinePowerSum p L 2 elevenPointNewtonCotesNodes =
      p ^ 2 + p * L + (1 / 3) * L ^ 2 := by
  rw [affinePowerSum_two_eq_moments,
    elevenPointNewtonCotes_moment_zero,
    elevenPointNewtonCotes_moment_one,
    elevenPointNewtonCotes_moment_two]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem elevenPointNewtonCotes_four_expansion (p L : Rat) :
    affinePowerSum p L 4 elevenPointNewtonCotesNodes =
      p ^ 4 + 2 * p ^ 3 * L + 2 * p ^ 2 * L ^ 2 +
        p * L ^ 3 + (1 / 5) * L ^ 4 := by
  rw [affinePowerSum_four_eq_moments,
    elevenPointNewtonCotes_moment_zero,
    elevenPointNewtonCotes_moment_one,
    elevenPointNewtonCotes_moment_two,
    elevenPointNewtonCotes_moment_three,
    elevenPointNewtonCotes_moment_four]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem elevenPointNewtonCotes_six_expansion (p L : Rat) :
    affinePowerSum p L 6 elevenPointNewtonCotesNodes =
      p ^ 6 + 3 * p ^ 5 * L + 5 * p ^ 4 * L ^ 2 +
        5 * p ^ 3 * L ^ 3 + 3 * p ^ 2 * L ^ 4 +
          p * L ^ 5 + (1 / 7) * L ^ 6 := by
  rw [affinePowerSum_six_eq_moments,
    elevenPointNewtonCotes_moment_zero,
    elevenPointNewtonCotes_moment_one,
    elevenPointNewtonCotes_moment_two,
    elevenPointNewtonCotes_moment_three,
    elevenPointNewtonCotes_moment_four,
    elevenPointNewtonCotes_moment_five,
    elevenPointNewtonCotes_moment_six]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private def eighthAverage (p L : Rat) : Rat :=
  p ^ 8 + 4 * p ^ 7 * L + (28 / 3) * p ^ 6 * L ^ 2 +
    14 * p ^ 5 * L ^ 3 + 14 * p ^ 4 * L ^ 4 +
      (28 / 3) * p ^ 3 * L ^ 5 + 4 * p ^ 2 * L ^ 6 +
        p * L ^ 7 + (1 / 9) * L ^ 8

private theorem elevenPointNewtonCotes_eight_expansion (p L : Rat) :
    affinePowerSum p L 8 elevenPointNewtonCotesNodes = eighthAverage p L := by
  rw [affinePowerSum_eight_eq_moments,
    elevenPointNewtonCotes_moment_zero,
    elevenPointNewtonCotes_moment_one,
    elevenPointNewtonCotes_moment_two,
    elevenPointNewtonCotes_moment_three,
    elevenPointNewtonCotes_moment_four,
    elevenPointNewtonCotes_moment_five,
    elevenPointNewtonCotes_moment_six,
    elevenPointNewtonCotes_moment_seven,
    elevenPointNewtonCotes_moment_eight]
  unfold eighthAverage
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private def kernelFourAverage (p L : Rat) : Rat :=
  kernelThreeAverage p L + eighthAverage p L

private theorem elevenPointNewtonCotes_kernel_four_expansion (p L : Rat) :
    affinePowerSum p L 0 elevenPointNewtonCotesNodes -
      affinePowerSum p L 2 elevenPointNewtonCotesNodes +
        affinePowerSum p L 4 elevenPointNewtonCotesNodes -
          affinePowerSum p L 6 elevenPointNewtonCotesNodes +
            affinePowerSum p L 8 elevenPointNewtonCotesNodes =
      kernelFourAverage p L := by
  rw [elevenPointNewtonCotes_zero_expansion,
    elevenPointNewtonCotes_two_expansion,
    elevenPointNewtonCotes_four_expansion,
    elevenPointNewtonCotes_six_expansion,
    elevenPointNewtonCotes_eight_expansion]
  rfl

private theorem monomialIntegralEight (p r : Rat) :
    (r ^ 9 - p ^ 9) / 9 = (r - p) * eighthAverage p (r - p) := by
  let L : Rat := r - p
  have hr : r = p + L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  rw [hr]
  dsimp [L]
  repeat rw [Rat.pow_succ]
  rw [Rat.div_def]
  have h3 : (3 : Rat) ≠ 0 := by native_decide
  have h9 : (9 : Rat) ≠ 0 := by native_decide
  unfold eighthAverage
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

private theorem kernelPartialIntegralFour_eq_average (p r : Rat) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 4 =
      (r - p) * kernelFourAverage p (r - p) := by
  have h2 := monomialIntegralTwo p r
  have h4 := monomialIntegralFour p r
  have h6 := monomialIntegralSix p r
  have height := monomialIntegralEight p r
  simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
    Taylor.ArctanKernel.kernelTermIntegralBetween]
  have hden1 : (2 : Rat) + 1 = 3 := by native_decide
  have hden2 : (2 : Rat) * 2 + 1 = 5 := by native_decide
  have hden3 : (2 : Rat) * 3 + 1 = 7 := by native_decide
  have hden4 : (2 : Rat) * 4 + 1 = 9 := by native_decide
  have hneg2 : (-1 : Rat) ^ 2 = 1 := by native_decide
  have hneg3 : (-1 : Rat) ^ 3 = -1 := by native_decide
  have hneg4 : (-1 : Rat) ^ 4 = 1 := by native_decide
  have hnegmul (x : Rat) : (-1 : Rat) * x = -x := by
    change -(1 : Rat) * x = -x
    rw [Rat.neg_mul, Rat.one_mul]
  have hnegdiv (x d : Rat) : -x / d = -(x / d) := by
    rw [Rat.div_def, Rat.div_def, Rat.neg_mul]
  rw [hden1, hden2, hden3, hden4, hneg2, hneg3, hneg4]
  rw [hnegmul, Rat.one_mul, hnegmul, Rat.one_mul]
  rw [hnegdiv, hnegdiv]
  rw [h2, h4, h6, height]
  unfold kernelFourAverage kernelThreeAverage
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem kernelPartial_four_formula (x : Rat) :
    Taylor.ArctanKernel.kernelPartial x 4 =
      1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 := by
  simp [Taylor.ArctanKernel.kernelPartial,
    Taylor.ArctanKernel.altGeomPartial]
  grind [Rat.sub_eq_add_neg]

private theorem quadratureEvalSum_kernelPartial_four_eq_affine
    (p r : Rat) :
    forall nodes : List (Rat × Rat),
      Integral.quadratureEvalSum
          (fun x => Taylor.ArctanKernel.kernelPartial x 4) p r nodes =
        affinePowerSum p (r - p) 0 nodes -
          affinePowerSum p (r - p) 2 nodes +
            affinePowerSum p (r - p) 4 nodes -
              affinePowerSum p (r - p) 6 nodes +
                affinePowerSum p (r - p) 8 nodes
  | [] => by
      simp [Integral.quadratureEvalSum, affinePowerSum]
      grind
  | (node, weight) :: rest => by
      simp only [Integral.quadratureEvalSum, affinePowerSum]
      rw [kernelPartial_four_formula]
      rw [quadratureEvalSum_kernelPartial_four_eq_affine p r rest]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem kernelPartialIntegralFour_newtonCotes (p r : Rat) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 4 =
      (r - p) * Integral.quadratureEvalSum
        (fun x => Taylor.ArctanKernel.kernelPartial x 4) p r
        elevenPointNewtonCotesNodes := by
  rw [kernelPartialIntegralFour_eq_average]
  rw [← elevenPointNewtonCotes_kernel_four_expansion]
  rw [← quadratureEvalSum_kernelPartial_four_eq_affine]

/-- The degree-eight kernel partial has exact cell-order preservation on
`[0,1]`, via a positive eleven-point rational quadrature identity. -/
theorem kernelPartialExactCellOrderPreservation_four :
    Integral.ExactCellOrderPreservation
      (fun x => Taylor.ArctanKernel.kernelPartial x 4)
      (fun p r => Taylor.ArctanKernel.kernelPartialIntegralBetween p r 4)
      0 1 := by
  apply Integral.exactCellOrderPreservation_of_positive_quadrature
    (a := (0 : Rat)) (b := 1) elevenPointNewtonCotesNodes
  · intro pair hmem
    simp only [elevenPointNewtonCotesNodes, List.mem_cons, List.not_mem_nil] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals try contradiction
    all_goals subst pair <;> constructor <;> native_decide
  · intro pair hmem
    simp only [elevenPointNewtonCotesNodes, List.mem_cons, List.not_mem_nil] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals try contradiction
    all_goals subst pair <;> native_decide
  · native_decide
  · intro p r
    exact kernelPartialIntegralFour_newtonCotes p r

theorem evenKernelCellBound_of_exactCellOrderPreservation
    {m : Nat}
    (horder :
      Integral.ExactCellOrderPreservation
        (fun x => Taylor.ArctanKernel.kernelPartial x m)
        (fun p r => Taylor.ArctanKernel.kernelPartialIntegralBetween p r m)
        0 1)
    (hpointwise : EvenKernelPointwiseCellBound m) :
    EvenKernelCellBound m := by
  intro p r hp0 hpr hr1
  unfold ArctanGeometry.integralLowerStep
  exact horder.lower_const hp0 hpr hr1 (by
    intro x hpx hxr
    exact hpointwise hp0 hpx hxr)

theorem oddKernelUnitCellBound_of_exactCellOrderPreservation
    {m : Nat}
    (horder :
      Integral.ExactCellOrderPreservation
        (fun x => Taylor.ArctanKernel.kernelPartial x m)
        (fun p r => Taylor.ArctanKernel.kernelPartialIntegralBetween p r m)
        0 1)
    (hpointwise : OddKernelPointwiseCellBound m) :
    OddKernelUnitCellBound m := by
  intro p r hp0 hpr hr1
  unfold ArctanGeometry.integralUpperStep
  exact horder.upper_const hp0 hpr hr1 (by
    intro x hpx hxr
    exact hpointwise hp0 hpx hxr)

theorem unitCellOrderPreservation_of_kernelPartialExactCellOrderPreservation
    (h : KernelPartialExactCellOrderPreservationOnUnit) :
    LeibnizRectangleUnitCellOrderPreservation := by
  constructor
  · intro m hpointwise
    exact evenKernelCellBound_of_exactCellOrderPreservation
      (h m) hpointwise
  · intro m hpointwise
    exact oddKernelUnitCellBound_of_exactCellOrderPreservation
      (h m) hpointwise

theorem evenKernelCellBounds_of_cellBound
    {m : Nat} {intervals : List (Rat × Rat)}
    (hcell : EvenKernelCellBound m)
    (h : ArctanGeometry.UnitIntervals intervals) :
    EvenKernelCellBounds m intervals := by
  induction intervals with
  | nil =>
      simp [EvenKernelCellBounds]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp0, hpr, hr1, hrest⟩
      simp [EvenKernelCellBounds]
      exact ⟨hcell hp0 hpr hr1, ih hrest⟩

theorem oddKernelCellBounds_of_cellBound
    {m : Nat} {intervals : List (Rat × Rat)}
    (hcell : OddKernelCellBound m)
    (h : ArctanGeometry.NonnegativeIntervals intervals) :
    OddKernelCellBounds m intervals := by
  induction intervals with
  | nil =>
      simp [OddKernelCellBounds]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp0, hpr, hrest⟩
      simp [OddKernelCellBounds]
      exact ⟨hcell hp0 hpr, ih hrest⟩

theorem oddKernelCellBounds_of_unitCellBound
    {m : Nat} {intervals : List (Rat × Rat)}
    (hcell : OddKernelUnitCellBound m)
    (h : ArctanGeometry.UnitIntervals intervals) :
    OddKernelCellBounds m intervals := by
  induction intervals with
  | nil =>
      simp [OddKernelCellBounds]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp0, hpr, hr1, hrest⟩
      simp [OddKernelCellBounds]
      exact ⟨hcell hp0 hpr hr1, ih hrest⟩

theorem evenKernelPointwiseCellBound_even (n : Nat) :
    EvenKernelPointwiseCellBound (2 * n) := by
  intro p x r hp0 hpx hxr
  have hx0 : 0 <= x := Rat.le_trans hp0 hpx
  have hkernel :
      ArctanGeometry.integralKernel r <=
        ArctanGeometry.integralKernel x :=
    ArctanGeometry.integralKernel_antitone_nonneg hx0 hxr
  have hpartial :
      ArctanGeometry.integralKernel x <=
        Taylor.ArctanKernel.kernelPartial x (2 * n) := by
    exact Taylor.ArctanKernel.kernel_le_kernelPartial_even x n
  exact Rat.le_trans hkernel hpartial

theorem oddKernelPointwiseCellBound_odd (n : Nat) :
    OddKernelPointwiseCellBound (2 * n + 1) := by
  intro p x r hp0 hpx _hxr
  have hpartial :
      Taylor.ArctanKernel.kernelPartial x (2 * n + 1) <=
        ArctanGeometry.integralKernel x := by
    exact Taylor.ArctanKernel.kernelPartial_odd_le_kernel x n
  have hkernel :
      ArctanGeometry.integralKernel x <=
        ArctanGeometry.integralKernel p :=
    ArctanGeometry.integralKernel_antitone_nonneg hp0 hpx
  exact Rat.le_trans hpartial hkernel

theorem leibnizRectanglePointwiseCellBoundsAtOne :
    LeibnizRectanglePointwiseCellBoundsAtOne :=
  ⟨evenKernelPointwiseCellBound_even, oddKernelPointwiseCellBound_odd⟩

theorem uniformCellBounds_of_pointwiseIntegralBridge
    (h : LeibnizRectanglePointwiseIntegralBridgeAtOne) :
    LeibnizRectangleUniformCellBoundsAtOne :=
  h leibnizRectanglePointwiseCellBoundsAtOne

theorem unitUniformCellBounds_of_pointwiseUnitIntegralBridge
    (h : LeibnizRectanglePointwiseUnitIntegralBridgeAtOne) :
    LeibnizRectangleUniformUnitCellBoundsAtOne :=
  h leibnizRectanglePointwiseCellBoundsAtOne

theorem integralKernel_le_one (r : Rat) :
    ArctanGeometry.integralKernel r <= 1 := by
  unfold ArctanGeometry.integralKernel
  let d : Rat := 1 + r * r
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos r
  have hdge : 1 <= d := by
    dsimp [d]
    have hsq := RationalCircle.Stage.ratSquare_nonneg r
    grind
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      (1 / d) * d = 1 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= d := hdge
      _ = 1 * d := by grind
  · exact hdpos

theorem integralLowerStep_le_kernelPartialIntegralBetween_zero
    {p r : Rat} (hpr : p <= r) :
    ArctanGeometry.integralLowerStep p r <=
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 0 := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hk := integralKernel_le_one r
  unfold ArctanGeometry.integralLowerStep
  simp [Taylor.ArctanKernel.kernelPartialIntegralBetween]
  calc
    (r - p) * ArctanGeometry.integralKernel r <= (r - p) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hk hlen
    _ = r - p := by rw [Rat.mul_one]

theorem evenKernelCellBound_zero : EvenKernelCellBound 0 := by
  apply evenKernelCellBound_of_exactCellOrderPreservation
    (m := 0) kernelPartialExactCellOrderPreservation_zero
  intro p x r hp0 hpx hxr
  simpa using evenKernelPointwiseCellBound_even 0 hp0 hpx hxr

theorem kernelPartialIntegralBetween_two_lowerStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    ArctanGeometry.integralLowerStep p r <=
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 2 := by
  let L : Rat := r - p
  let D : Rat := 1 + r * r
  let S3 : Rat := r * r + r * p + p * p
  let S5 : Rat :=
    r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos r
  have h15Dpos : 0 < 15 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 15) hDpos
  have hrr_le_one : r * r <= 1 := by
    calc
      r * r <= 1 * r := Rat.mul_le_mul_of_nonneg_right hr1 hr0
      _ = r := by grind
      _ <= 1 := hr1
  have hone_sub_rr : 0 <= 1 - r * r := by
    grind [Rat.sub_eq_add_neg]
  have htwor_add_p : 0 <= 2 * r + p := by grind
  have hs5_nonneg : 0 <= S5 := by
    dsimp [S5]
    have hr2 : 0 <= r ^ 2 := Rat.pow_nonneg hr0
    have hr3 : 0 <= r ^ 3 := Rat.pow_nonneg hr0
    have hr4 : 0 <= r ^ 4 := Rat.pow_nonneg hr0
    have hp2 : 0 <= p ^ 2 := Rat.pow_nonneg hp0
    have hp3 : 0 <= p ^ 3 := Rat.pow_nonneg hp0
    have hp4 : 0 <= p ^ 4 := Rat.pow_nonneg hp0
    exact Rat.add_nonneg
      (Rat.add_nonneg
        (Rat.add_nonneg
          (Rat.add_nonneg hr4 (Rat.mul_nonneg hr3 hp0))
          (Rat.mul_nonneg hr2 hp2))
        (Rat.mul_nonneg hr0 hp3))
      hp4
  have hquad_nonneg : 0 <= 3 * p * p + 9 * p * r + 8 * r * r := by
    have hpp : 0 <= p * p := Rat.mul_nonneg hp0 hp0
    have hpr0 : 0 <= p * r := Rat.mul_nonneg hp0 hr0
    have hrr : 0 <= r * r := Rat.mul_nonneg hr0 hr0
    grind
  have hfactor :
      D * (15 - 5 * S3 + 3 * S5) - 15 =
        5 * (1 - r * r) * (r - p) * (2 * r + p) +
          (r - p) * (r - p) *
            (3 * p * p + 9 * p * r + 8 * r * r) +
            3 * (r * r) * S5 := by
    dsimp [D, S3, S5]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.pow_succ]
  have hgap_nonneg : 0 <= D * (15 - 5 * S3 + 3 * S5) - 15 := by
    rw [hfactor]
    have hterm1 : 0 <= 5 * (1 - r * r) * (r - p) * (2 * r + p) := by
      have h5 : 0 <= (5 : Rat) := by native_decide
      have hrp : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
      exact Rat.mul_nonneg
        (Rat.mul_nonneg (Rat.mul_nonneg h5 hone_sub_rr) hrp) htwor_add_p
    have hterm2 :
        0 <= (r - p) * (r - p) *
          (3 * p * p + 9 * p * r + 8 * r * r) := by
      have hrp : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
      exact Rat.mul_nonneg (Rat.mul_nonneg hrp hrp) hquad_nonneg
    have hterm3 : 0 <= 3 * (r * r) * S5 := by
      have h3 : 0 <= (3 : Rat) := by native_decide
      have hrr : 0 <= r * r := Rat.mul_nonneg hr0 hr0
      exact Rat.mul_nonneg (Rat.mul_nonneg h3 hrr) hs5_nonneg
    exact Rat.add_nonneg (Rat.add_nonneg hterm1 hterm2) hterm3
  have hscalar : 15 <= D * (15 - 5 * S3 + 3 * S5) := by
    grind [Rat.sub_eq_add_neg]
  have hlower_mul :
      ArctanGeometry.integralLowerStep p r * (15 * D) = L * 15 := by
    unfold ArctanGeometry.integralLowerStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 2 * (15 * D) =
        L * (D * (15 - 5 * S3 + 3 * S5)) := by
    have hkernel_formula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 2 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 +
            (r ^ 5 - p ^ 5) / 5 := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcube : r ^ 3 - p ^ 3 = L * S3 := by
      dsimp [L, S3]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifth : r ^ 5 - p ^ 5 = L * S5 := by
      dsimp [L, S5]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hkernel_formula, hcube, hfifth]
    dsimp [L, D, S3, S5]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 15 * D)
  · rw [hlower_mul, hkernel_mul]
    exact Rat.mul_le_mul_of_nonneg_left hscalar hL0
  · exact h15Dpos

theorem evenKernelCellBound_two : EvenKernelCellBound 2 := by
  apply evenKernelCellBound_of_exactCellOrderPreservation
    (m := 2) kernelPartialExactCellOrderPreservation_two
  intro p x r hp0 hpx hxr
  simpa using evenKernelPointwiseCellBound_even 1 hp0 hpx hxr

theorem kernelPartialIntegralBetween_one_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 <=
      ArctanGeometry.integralUpperStep p r := by
  let L : Rat := r - p
  let S : Rat := r * r + r * p + p * p
  let D : Rat := 1 + p * p
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos p
  have h3Dpos : 0 < 3 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 3) hDpos
  have hD1 : 1 <= D := by
    dsimp [D]
    have hsq := RationalCircle.Stage.ratSquare_nonneg p
    grind
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hpp_le_rp : p * p <= r * p :=
    Rat.mul_le_mul_of_nonneg_right hpr hp0
  have hrp_le_rr : r * p <= r * r :=
    Rat.mul_le_mul_of_nonneg_left hpr hr0
  have hpp_le_rr : p * p <= r * r :=
    Rat.le_trans hpp_le_rp hrp_le_rr
  have hthree : 3 * (p * p) <= S := by
    dsimp [S]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm]
  have hS0 : 0 <= S := by
    dsimp [S]
    exact Rat.add_nonneg
      (Rat.add_nonneg (Rat.mul_nonneg hr0 hr0) (Rat.mul_nonneg hr0 hp0))
      (Rat.mul_nonneg hp0 hp0)
  have hS_le_SD : S <= S * D := by
    calc
      S = S * 1 := by grind
      _ <= S * D := Rat.mul_le_mul_of_nonneg_left hD1 hS0
  have hthreeSD : 3 * (p * p) <= S * D :=
    Rat.le_trans hthree hS_le_SD
  have hbig0 : L * (3 * (p * p)) <= L * (S * D) :=
    Rat.mul_le_mul_of_nonneg_left hthreeSD hL0
  have hcube : r ^ 3 - p ^ 3 = L * S := by
    dsimp [L, S]
    repeat rw [Rat.pow_succ]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hbig : L * (3 * (p * p)) <= (r ^ 3 - p ^ 3) * D := by
    rw [hcube]
    dsimp [D] at hbig0 ⊢
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hkernel_formula :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 =
        (r - p) - (r ^ 3 - p ^ 3) / 3 := by
    simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
      Taylor.ArctanKernel.kernelTermIntegralBetween]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  have hupper_mul :
      ArctanGeometry.integralUpperStep p r * (3 * D) = L * 3 := by
    unfold ArctanGeometry.integralUpperStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 1 * (3 * D) =
        L * 3 * D - (r ^ 3 - p ^ 3) * D := by
    rw [hkernel_formula]
    rw [Rat.div_def]
    dsimp [L, D]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 3 * D)
  · rw [hkernel_mul, hupper_mul]
    have hrew : L * 3 * D = L * 3 + L * (3 * (p * p)) := by
      dsimp [D]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
        Rat.add_assoc, Rat.add_comm]
    calc
      L * 3 * D - (r ^ 3 - p ^ 3) * D =
          L * 3 + L * (3 * (p * p)) -
            (r ^ 3 - p ^ 3) * D := by
        rw [hrew]
      _ <= L * 3 + (r ^ 3 - p ^ 3) * D -
            (r ^ 3 - p ^ 3) * D := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      _ = L * 3 := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  · exact h3Dpos

theorem oddKernelCellBound_one : OddKernelCellBound 1 := by
  intro p r hp0 hpr
  exact kernelPartialIntegralBetween_one_le_integralUpperStep hp0 hpr

theorem oddKernelUnitCellBound_one : OddKernelUnitCellBound 1 := by
  apply oddKernelUnitCellBound_of_exactCellOrderPreservation
    (m := 1) kernelPartialExactCellOrderPreservation_one
  intro p x r hp0 hpx hxr
  simpa using oddKernelPointwiseCellBound_odd 0 hp0 hpx hxr

private structure SimplexCertTerm where
  c : Rat
  i : Nat
  j : Nat
  k : Nat

private def simplexCertTermEval (p q s : Rat) (t : SimplexCertTerm) : Rat :=
  t.c * p ^ t.i * q ^ t.j * s ^ t.k

private def simplexCertEval (terms : List SimplexCertTerm) (p q s : Rat) : Rat :=
  match terms with
  | [] => 0
  | t :: rest => simplexCertTermEval p q s t + simplexCertEval rest p q s

private def simplexCertCoeffsNonneg : List SimplexCertTerm -> Prop
  | [] => True
  | t :: rest => 0 <= t.c /\ simplexCertCoeffsNonneg rest

private instance simplexCertCoeffsNonnegDecidable :
    (terms : List SimplexCertTerm) -> Decidable (simplexCertCoeffsNonneg terms)
  | [] => isTrue trivial
  | t :: rest => by
      dsimp [simplexCertCoeffsNonneg]
      exact @instDecidableAnd (0 <= t.c) (simplexCertCoeffsNonneg rest)
        inferInstance (simplexCertCoeffsNonnegDecidable rest)

private theorem simplexCertTermEval_nonneg
    {p q s : Rat} (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s)
    {t : SimplexCertTerm} (hc : 0 <= t.c) :
    0 <= simplexCertTermEval p q s t := by
  unfold simplexCertTermEval
  exact Rat.mul_nonneg
    (Rat.mul_nonneg
      (Rat.mul_nonneg hc (Rat.pow_nonneg hp))
      (Rat.pow_nonneg hq))
    (Rat.pow_nonneg hs)

private theorem simplexCertEval_nonneg
    {terms : List SimplexCertTerm} {p q s : Rat}
    (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s)
    (hterms : simplexCertCoeffsNonneg terms) :
    0 <= simplexCertEval terms p q s := by
  induction terms with
  | nil =>
      simp [simplexCertEval]
  | cons t rest ih =>
      rcases hterms with ⟨hc, hrest⟩
      simp [simplexCertEval]
      exact Rat.add_nonneg
        (simplexCertTermEval_nonneg hp hq hs hc)
        (ih hrest)

private def oddKernelThreeUnitGapTerms : List SimplexCertTerm := [
  ⟨105, 8, 0, 0⟩,
  ⟨420, 7, 1, 0⟩,
  ⟨1120, 6, 2, 0⟩,
  ⟨2030, 5, 3, 0⟩,
  ⟨2478, 4, 4, 0⟩,
  ⟨1974, 3, 5, 0⟩,
  ⟨968, 2, 6, 0⟩,
  ⟨261, 1, 7, 0⟩,
  ⟨29, 0, 8, 0⟩,
  ⟨420, 6, 1, 1⟩,
  ⟨2240, 5, 2, 1⟩,
  ⟨5040, 4, 3, 1⟩,
  ⟨5964, 3, 4, 1⟩,
  ⟨3836, 2, 5, 1⟩,
  ⟨1248, 1, 6, 1⟩,
  ⟨156, 0, 7, 1⟩,
  ⟨1050, 5, 1, 2⟩,
  ⟨4830, 4, 2, 2⟩,
  ⟨8610, 3, 3, 2⟩,
  ⟨7308, 2, 4, 2⟩,
  ⟨2898, 1, 5, 2⟩,
  ⟨414, 0, 6, 2⟩,
  ⟨1680, 4, 1, 3⟩,
  ⟨5880, 3, 2, 3⟩,
  ⟨7280, 2, 3, 3⟩,
  ⟨3696, 1, 4, 3⟩,
  ⟨616, 0, 5, 3⟩,
  ⟨1470, 3, 1, 4⟩,
  ⟨3500, 2, 2, 4⟩,
  ⟨2520, 1, 3, 4⟩,
  ⟨504, 0, 4, 4⟩,
  ⟨630, 2, 1, 5⟩,
  ⟨840, 1, 2, 5⟩,
  ⟨210, 0, 3, 5⟩,
  ⟨105, 1, 1, 6⟩,
  ⟨35, 0, 2, 6⟩]

private def oddKernelThreeUnitGapCertificate (p q s : Rat) : Rat :=
  simplexCertEval oddKernelThreeUnitGapTerms p q s

private theorem oddKernelThreeUnitGapTerms_nonneg :
    simplexCertCoeffsNonneg oddKernelThreeUnitGapTerms := by
  native_decide

private theorem oddKernelThreeUnitGapCertificate_nonneg
    {p q s : Rat} (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s) :
    0 <= oddKernelThreeUnitGapCertificate p q s :=
  simplexCertEval_nonneg hp hq hs oddKernelThreeUnitGapTerms_nonneg

private theorem oddKernelThreeUnitGap_eq_certificate (p r : Rat) :
    let q : Rat := r - p
    let s : Rat := 1 - r
    105 - (1 + p * p) *
        (105 - 35 * (r * r + r * p + p * p) +
          21 * (r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4) -
          15 * (r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 +
            r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6)) =
      oddKernelThreeUnitGapCertificate p q s := by
  intro q s
  unfold oddKernelThreeUnitGapCertificate oddKernelThreeUnitGapTerms
  simp [simplexCertEval, simplexCertTermEval]
  dsimp [q, s]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem kernelPartialIntegralBetween_three_le_integralUpperStep_on_unit
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 3 <=
      ArctanGeometry.integralUpperStep p r := by
  let L : Rat := r - p
  let D : Rat := 1 + p * p
  let S3 : Rat := r * r + r * p + p * p
  let S5 : Rat :=
    r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4
  let S7 : Rat :=
    r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 +
      r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos p
  have h105Dpos : 0 < 105 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 105) hDpos
  let q : Rat := r - p
  let s : Rat := 1 - r
  have hq0 : 0 <= q := by
    dsimp [q]
    grind [Rat.sub_eq_add_neg]
  have hs0 : 0 <= s := by
    dsimp [s]
    grind [Rat.sub_eq_add_neg]
  have hgap_cert := oddKernelThreeUnitGap_eq_certificate p r
  have hgap_nonneg :
      0 <= 105 - D * (105 - 35 * S3 + 21 * S5 - 15 * S7) := by
    dsimp [D, S3, S5, S7]
    rw [hgap_cert]
    exact oddKernelThreeUnitGapCertificate_nonneg hp0 hq0 hs0
  have hscalar : D * (105 - 35 * S3 + 21 * S5 - 15 * S7) <= 105 := by
    grind [Rat.sub_eq_add_neg]
  have hupper_mul :
      ArctanGeometry.integralUpperStep p r * (105 * D) = L * 105 := by
    unfold ArctanGeometry.integralUpperStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 3 * (105 * D) =
        L * (D * (105 - 35 * S3 + 21 * S5 - 15 * S7)) := by
    have hkernel_formula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 3 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 +
            (r ^ 5 - p ^ 5) / 5 - (r ^ 7 - p ^ 7) / 7 := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcube : r ^ 3 - p ^ 3 = L * S3 := by
      dsimp [L, S3]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifth : r ^ 5 - p ^ 5 = L * S5 := by
      dsimp [L, S5]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hseventh : r ^ 7 - p ^ 7 = L * S7 := by
      dsimp [L, S7]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hkernel_formula, hcube, hfifth, hseventh]
    dsimp [L, D, S3, S5, S7]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 105 * D)
  · rw [hkernel_mul, hupper_mul]
    exact Rat.mul_le_mul_of_nonneg_left hscalar hL0
  · exact h105Dpos

theorem oddKernelUnitCellBound_three : OddKernelUnitCellBound 3 := by
  apply oddKernelUnitCellBound_of_exactCellOrderPreservation
    (m := 3) kernelPartialExactCellOrderPreservation_three
  intro p x r hp0 hpx hxr
  simpa using oddKernelPointwiseCellBound_odd 1 hp0 hpx hxr

private def evenKernelFourUnitGapTerms : List SimplexCertTerm := [
  ⟨945, 10, 0, 0⟩,
  ⟨5670, 9, 1, 0⟩,
  ⟨19845, 8, 2, 0⟩,
  ⟨49140, 7, 3, 0⟩,
  ⟨87318, 6, 4, 0⟩,
  ⟨111258, 5, 5, 0⟩,
  ⟨100530, 4, 6, 0⟩,
  ⟨62550, 3, 7, 0⟩,
  ⟨25365, 2, 8, 0⟩,
  ⟨6018, 1, 9, 0⟩,
  ⟨633, 0, 10, 0⟩,
  ⟨3780, 8, 1, 1⟩,
  ⟨34020, 7, 2, 1⟩,
  ⟨124740, 6, 3, 1⟩,
  ⟨257040, 5, 4, 1⟩,
  ⟨328230, 4, 5, 1⟩,
  ⟨265050, 3, 6, 1⟩,
  ⟨131760, 2, 7, 1⟩,
  ⟨36840, 1, 8, 1⟩,
  ⟨4440, 0, 9, 1⟩,
  ⟨17010, 7, 1, 2⟩,
  ⟨120960, 6, 2, 2⟩,
  ⟨368550, 5, 3, 2⟩,
  ⟨621054, 4, 4, 2⟩,
  ⟨620361, 3, 5, 2⟩,
  ⟨365904, 2, 6, 2⟩,
  ⟨117936, 1, 7, 2⟩,
  ⟨16044, 0, 8, 2⟩,
  ⟨37800, 6, 1, 3⟩,
  ⟨229320, 5, 2, 3⟩,
  ⟨575820, 4, 3, 3⟩,
  ⟨759276, 3, 4, 3⟩,
  ⟨552888, 2, 5, 3⟩,
  ⟨210888, 1, 6, 3⟩,
  ⟨32976, 0, 7, 3⟩,
  ⟨52920, 5, 1, 4⟩,
  ⟨263340, 4, 2, 4⟩,
  ⟨513765, 3, 3, 4⟩,
  ⟨490644, 2, 4, 4⟩,
  ⟨229698, 1, 5, 4⟩,
  ⟨42264, 0, 6, 4⟩,
  ⟨47250, 4, 1, 5⟩,
  ⟨180810, 3, 2, 5⟩,
  ⟨253260, 2, 3, 5⟩,
  ⟨154224, 1, 4, 5⟩,
  ⟨34524, 0, 5, 5⟩,
  ⟨25515, 3, 1, 6⟩,
  ⟨69300, 2, 2, 6⟩,
  ⟨61110, 1, 3, 6⟩,
  ⟨17514, 0, 4, 6⟩,
  ⟨7560, 2, 1, 7⟩,
  ⟨12600, 1, 2, 7⟩,
  ⟨5040, 0, 3, 7⟩,
  ⟨945, 1, 1, 8⟩,
  ⟨630, 0, 2, 8⟩]

private def evenKernelFourUnitGapCertificate (p q s : Rat) : Rat :=
  simplexCertEval evenKernelFourUnitGapTerms p q s

private theorem evenKernelFourUnitGapTerms_nonneg :
    simplexCertCoeffsNonneg evenKernelFourUnitGapTerms := by
  native_decide

private theorem evenKernelFourUnitGapCertificate_nonneg
    {p q s : Rat} (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s) :
    0 <= evenKernelFourUnitGapCertificate p q s :=
  simplexCertEval_nonneg hp hq hs evenKernelFourUnitGapTerms_nonneg

private theorem evenKernelFourUnitGap_eq_certificate (p r : Rat) :
    let q : Rat := r - p
    let s : Rat := 1 - r
    (1 + r * r) *
        (945 - 315 * (r * r + r * p + p * p) +
          189 * (r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4) -
          135 * (r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 +
            r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6) +
          105 * (r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 +
            r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 +
            r * p ^ 7 + p ^ 8)) - 945 =
      evenKernelFourUnitGapCertificate p q s := by
  intro q s
  unfold evenKernelFourUnitGapCertificate evenKernelFourUnitGapTerms
  simp [simplexCertEval, simplexCertTermEval]
  dsimp [q, s]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem kernelPartialIntegralBetween_four_lowerStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    ArctanGeometry.integralLowerStep p r <=
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 4 := by
  let L : Rat := r - p
  let D : Rat := 1 + r * r
  let S3 : Rat := r * r + r * p + p * p
  let S5 : Rat :=
    r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4
  let S7 : Rat :=
    r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 +
      r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6
  let S9 : Rat :=
    r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 +
      r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 +
      r * p ^ 7 + p ^ 8
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos r
  have h945Dpos : 0 < 945 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 945) hDpos
  let q : Rat := r - p
  let s : Rat := 1 - r
  have hq0 : 0 <= q := by
    dsimp [q]
    grind [Rat.sub_eq_add_neg]
  have hs0 : 0 <= s := by
    dsimp [s]
    grind [Rat.sub_eq_add_neg]
  have hgap_cert := evenKernelFourUnitGap_eq_certificate p r
  have hgap_nonneg :
      0 <= D * (945 - 315 * S3 + 189 * S5 - 135 * S7 + 105 * S9) - 945 := by
    dsimp [D, S3, S5, S7, S9]
    rw [hgap_cert]
    exact evenKernelFourUnitGapCertificate_nonneg hp0 hq0 hs0
  have hscalar : 945 <= D * (945 - 315 * S3 + 189 * S5 - 135 * S7 + 105 * S9) := by
    grind [Rat.sub_eq_add_neg]
  have hlower_mul :
      ArctanGeometry.integralLowerStep p r * (945 * D) = L * 945 := by
    unfold ArctanGeometry.integralLowerStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 4 * (945 * D) =
        L * (D * (945 - 315 * S3 + 189 * S5 - 135 * S7 + 105 * S9)) := by
    have hkernel_formula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 4 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 +
            (r ^ 5 - p ^ 5) / 5 - (r ^ 7 - p ^ 7) / 7 +
            (r ^ 9 - p ^ 9) / 9 := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcube : r ^ 3 - p ^ 3 = L * S3 := by
      dsimp [L, S3]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifth : r ^ 5 - p ^ 5 = L * S5 := by
      dsimp [L, S5]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hseventh : r ^ 7 - p ^ 7 = L * S7 := by
      dsimp [L, S7]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hninth : r ^ 9 - p ^ 9 = L * S9 := by
      dsimp [L, S9]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hkernel_formula, hcube, hfifth, hseventh, hninth]
    dsimp [L, D, S3, S5, S7, S9]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 945 * D)
  · rw [hlower_mul, hkernel_mul]
    exact Rat.mul_le_mul_of_nonneg_left hscalar hL0
  · exact h945Dpos

theorem evenKernelCellBound_four : EvenKernelCellBound 4 := by
  apply evenKernelCellBound_of_exactCellOrderPreservation
    (m := 4) kernelPartialExactCellOrderPreservation_four
  intro p x r hp0 hpx hxr
  simpa using evenKernelPointwiseCellBound_even 2 hp0 hpx hxr

private def oddKernelFiveUnitGapTerms : List SimplexCertTerm := [
  ⟨10395, 12, 0, 0⟩,
  ⟨62370, 11, 1, 0⟩,
  ⟨249480, 10, 2, 0⟩,
  ⟨717255, 9, 3, 0⟩,
  ⟨1523907, 8, 4, 0⟩,
  ⟨2410254, 7, 5, 0⟩,
  ⟨2834568, 6, 6, 0⟩,
  ⟨2459061, 5, 7, 0⟩,
  ⟨1546545, 4, 8, 0⟩,
  ⟨682902, 3, 9, 0⟩,
  ⟨199824, 2, 10, 0⟩,
  ⟨34593, 1, 11, 0⟩,
  ⟨2661, 0, 12, 0⟩,
  ⟨62370, 10, 1, 1⟩,
  ⟨582120, 9, 2, 1⟩,
  ⟨2474010, 8, 3, 1⟩,
  ⟨6228684, 7, 4, 1⟩,
  ⟨10236996, 6, 5, 1⟩,
  ⟨11439648, 5, 6, 1⟩,
  ⟨8773380, 4, 7, 1⟩,
  ⟨4542120, 3, 8, 1⟩,
  ⟨1511994, 2, 9, 1⟩,
  ⟨290376, 1, 10, 1⟩,
  ⟨24198, 0, 11, 1⟩,
  ⟨280665, 9, 1, 2⟩,
  ⟨2422035, 8, 2, 2⟩,
  ⟨9209970, 7, 3, 2⟩,
  ⟨20232828, 6, 4, 2⟩,
  ⟨28250838, 5, 5, 2⟩,
  ⟨25925130, 4, 6, 2⟩,
  ⟨15574680, 3, 7, 2⟩,
  ⟨5875980, 2, 8, 2⟩,
  ⟨1254033, 1, 9, 2⟩,
  ⟨114003, 0, 10, 2⟩,
  ⟨831600, 8, 1, 3⟩,
  ⟨6292440, 7, 2, 3⟩,
  ⟨20623680, 6, 3, 3⟩,
  ⟨38164896, 5, 4, 3⟩,
  ⟨43464960, 4, 5, 3⟩,
  ⟨31054320, 3, 6, 3⟩,
  ⟨13511520, 2, 7, 3⟩,
  ⟨3244560, 1, 8, 3⟩,
  ⟨324456, 0, 9, 3⟩,
  ⟨1600830, 7, 1, 4⟩,
  ⟨10436580, 6, 2, 4⟩,
  ⟨28787220, 5, 3, 4⟩,
  ⟨43367940, 4, 4, 4⟩,
  ⟨38336760, 3, 5, 4⟩,
  ⟨19746540, 2, 6, 4⟩,
  ⟨5429160, 1, 7, 4⟩,
  ⟨603240, 0, 8, 4⟩,
  ⟨2099790, 6, 1, 5⟩,
  ⟨11503800, 5, 2, 5⟩,
  ⟨25758810, 4, 3, 5⟩,
  ⟨29995812, 3, 4, 5⟩,
  ⟨19000674, 2, 5, 5⟩,
  ⟨6125328, 1, 6, 5⟩,
  ⟨765666, 0, 7, 5⟩,
  ⟨1902285, 5, 1, 6⟩,
  ⟨8423415, 4, 2, 6⟩,
  ⟨14497560, 3, 3, 6⟩,
  ⟨12001374, 2, 4, 6⟩,
  ⟨4696461, 1, 5, 6⟩,
  ⟨670923, 0, 6, 6⟩,
  ⟨1164240, 4, 1, 7⟩,
  ⟨3936240, 3, 2, 7⟩,
  ⟨4767840, 2, 3, 7⟩,
  ⟨2395008, 1, 4, 7⟩,
  ⟨399168, 0, 5, 7⟩,
  ⟨457380, 3, 1, 8⟩,
  ⟨1074150, 2, 2, 8⟩,
  ⟨769230, 1, 3, 8⟩,
  ⟨153846, 0, 4, 8⟩,
  ⟨103950, 2, 1, 9⟩,
  ⟨138600, 1, 2, 9⟩,
  ⟨34650, 0, 3, 9⟩,
  ⟨10395, 1, 1, 10⟩,
  ⟨3465, 0, 2, 10⟩]

private def oddKernelFiveUnitGapCertificate (p q s : Rat) : Rat :=
  simplexCertEval oddKernelFiveUnitGapTerms p q s

private theorem oddKernelFiveUnitGapTerms_nonneg :
    simplexCertCoeffsNonneg oddKernelFiveUnitGapTerms := by
  native_decide

private theorem oddKernelFiveUnitGapCertificate_nonneg
    {p q s : Rat} (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s) :
    0 <= oddKernelFiveUnitGapCertificate p q s :=
  simplexCertEval_nonneg hp hq hs oddKernelFiveUnitGapTerms_nonneg

private theorem oddKernelFiveUnitGap_eq_certificate (p r : Rat) :
    let q : Rat := r - p
    let s : Rat := 1 - r
    10395 - (1 + p * p) *
        (10395 - 3465 * (r * r + r * p + p * p) +
          2079 * (r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4) -
          1485 * (r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 +
            r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6) +
          1155 * (r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 +
            r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 +
            r * p ^ 7 + p ^ 8) -
          945 * (r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 +
            r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 +
            r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10)) =
      oddKernelFiveUnitGapCertificate p q s := by
  intro q s
  unfold oddKernelFiveUnitGapCertificate oddKernelFiveUnitGapTerms
  simp [simplexCertEval, simplexCertTermEval]
  dsimp [q, s]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem kernelPartialIntegralBetween_five_le_integralUpperStep_on_unit
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 5 <=
      ArctanGeometry.integralUpperStep p r := by
  let L : Rat := r - p
  let D : Rat := 1 + p * p
  let S3 : Rat := r * r + r * p + p * p
  let S5 : Rat :=
    r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4
  let S7 : Rat :=
    r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 +
      r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6
  let S9 : Rat :=
    r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 +
      r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 +
      r * p ^ 7 + p ^ 8
  let S11 : Rat :=
    r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 +
      r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 +
      r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos p
  have h10395Dpos : 0 < 10395 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 10395) hDpos
  let q : Rat := r - p
  let s : Rat := 1 - r
  have hq0 : 0 <= q := by
    dsimp [q]
    grind [Rat.sub_eq_add_neg]
  have hs0 : 0 <= s := by
    dsimp [s]
    grind [Rat.sub_eq_add_neg]
  have hgap_cert := oddKernelFiveUnitGap_eq_certificate p r
  have hgap_nonneg :
      0 <=
        10395 - D * (10395 - 3465 * S3 + 2079 * S5 -
          1485 * S7 + 1155 * S9 - 945 * S11) := by
    dsimp [D, S3, S5, S7, S9, S11]
    rw [hgap_cert]
    exact oddKernelFiveUnitGapCertificate_nonneg hp0 hq0 hs0
  have hscalar :
      D * (10395 - 3465 * S3 + 2079 * S5 -
          1485 * S7 + 1155 * S9 - 945 * S11) <= 10395 := by
    grind [Rat.sub_eq_add_neg]
  have hupper_mul :
      ArctanGeometry.integralUpperStep p r * (10395 * D) = L * 10395 := by
    unfold ArctanGeometry.integralUpperStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 5 * (10395 * D) =
        L * (D * (10395 - 3465 * S3 + 2079 * S5 -
          1485 * S7 + 1155 * S9 - 945 * S11)) := by
    have hkernel_formula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 5 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 +
            (r ^ 5 - p ^ 5) / 5 - (r ^ 7 - p ^ 7) / 7 +
            (r ^ 9 - p ^ 9) / 9 - (r ^ 11 - p ^ 11) / 11 := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcube : r ^ 3 - p ^ 3 = L * S3 := by
      dsimp [L, S3]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifth : r ^ 5 - p ^ 5 = L * S5 := by
      dsimp [L, S5]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hseventh : r ^ 7 - p ^ 7 = L * S7 := by
      dsimp [L, S7]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hninth : r ^ 9 - p ^ 9 = L * S9 := by
      dsimp [L, S9]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have heleventh : r ^ 11 - p ^ 11 = L * S11 := by
      dsimp [L, S11]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hkernel_formula, hcube, hfifth, hseventh, hninth, heleventh]
    dsimp [L, D, S3, S5, S7, S9, S11]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 10395 * D)
  · rw [hkernel_mul, hupper_mul]
    exact Rat.mul_le_mul_of_nonneg_left hscalar hL0
  · exact h10395Dpos

theorem oddKernelUnitCellBound_five : OddKernelUnitCellBound 5 := by
  intro p r hp0 hpr hr1
  exact kernelPartialIntegralBetween_five_le_integralUpperStep_on_unit hp0 hpr hr1

private def evenKernelSixUnitGapTerms : List SimplexCertTerm := [
  ⟨45045, 14, 0, 0⟩,
  ⟨360360, 13, 1, 0⟩,
  ⟨1756755, 12, 2, 0⟩,
  ⟨6216210, 11, 3, 0⟩,
  ⟨16549533, 10, 4, 0⟩,
  ⟨33753720, 9, 5, 0⟩,
  ⟨53185275, 8, 6, 0⟩,
  ⟨64851930, 7, 7, 0⟩,
  ⟨60955895, 6, 8, 0⟩,
  ⟨43699656, 5, 9, 0⟩,
  ⟨23430225, 4, 10, 0⟩,
  ⟨9086350, 3, 11, 0⟩,
  ⟨2405235, 2, 12, 0⟩,
  ⟨388650, 1, 13, 0⟩,
  ⟨28913, 0, 14, 0⟩,
  ⟨270270, 12, 1, 1⟩,
  ⟨3513510, 11, 2, 1⟩,
  ⟨19999980, 10, 3, 1⟩,
  ⟨68360292, 9, 4, 1⟩,
  ⟨157074918, 8, 5, 1⟩,
  ⟨255717462, 7, 6, 1⟩,
  ⟨302390088, 6, 7, 1⟩,
  ⟨261533272, 5, 8, 1⟩,
  ⟨164045882, 4, 9, 1⟩,
  ⟨72716098, 3, 10, 1⟩,
  ⟨21609952, 2, 11, 1⟩,
  ⟨3865148, 1, 12, 1⟩,
  ⟨314692, 0, 13, 1⟩,
  ⟨1756755, 11, 1, 2⟩,
  ⟨19639620, 10, 2, 2⟩,
  ⟨99909810, 9, 3, 2⟩,
  ⟨304576272, 8, 4, 2⟩,
  ⟨617287671, 7, 5, 2⟩,
  ⟨872596296, 6, 6, 2⟩,
  ⟨877059612, 5, 7, 2⟩,
  ⟨626134080, 4, 8, 2⟩,
  ⟨310858977, 3, 9, 2⟩,
  ⟨102162996, 2, 10, 2⟩,
  ⟨20000136, 1, 11, 2⟩,
  ⟨1767162, 0, 12, 2⟩,
  ⟨6306300, 10, 1, 3⟩,
  ⟨64084020, 9, 2, 3⟩,
  ⟨292432140, 8, 3, 3⟩,
  ⟨788071284, 7, 4, 3⟩,
  ⟨1388034648, 6, 5, 3⟩,
  ⟨1667941704, 5, 6, 3⟩,
  ⟨1383319080, 4, 7, 3⟩,
  ⟨781174680, 3, 8, 3⟩,
  ⟨287325324, 2, 9, 3⟩,
  ⟨62150868, 1, 10, 3⟩,
  ⟨6005064, 0, 11, 3⟩,
  ⟨15360345, 9, 1, 4⟩,
  ⟨139789650, 8, 2, 4⟩,
  ⟨563137575, 7, 3, 4⟩,
  ⟨1317356040, 6, 4, 4⟩,
  ⟨1970058090, 5, 5, 4⟩,
  ⟨1950877500, 4, 6, 4⟩,
  ⟨1278141150, 3, 7, 4⟩,
  ⟨534004900, 2, 8, 4⟩,
  ⟨129098255, 1, 9, 4⟩,
  ⟨13763230, 0, 10, 4⟩,
  ⟨26576550, 8, 1, 5⟩,
  ⟨213243030, 7, 2, 5⟩,
  ⟨744864120, 6, 3, 5⟩,
  ⟨1477548072, 5, 4, 5⟩,
  ⟨1818196380, 4, 5, 5⟩,
  ⟨1420050060, 3, 6, 5⟩,
  ⟨687180780, 2, 7, 5⟩,
  ⟨188382480, 1, 8, 5⟩,
  ⟨22405812, 0, 9, 5⟩,
  ⟨33378345, 7, 1, 6⟩,
  ⟨231951720, 6, 2, 6⟩,
  ⟨685945260, 5, 3, 6⟩,
  ⟨1117548432, 4, 4, 6⟩,
  ⟨1082419338, 3, 5, 6⟩,
  ⟨623083032, 2, 6, 6⟩,
  ⟨197392338, 1, 7, 6⟩,
  ⟨26557102, 0, 8, 6⟩,
  ⟨30630600, 6, 1, 7⟩,
  ⟨179819640, 5, 2, 7⟩,
  ⟨435675240, 4, 3, 7⟩,
  ⟨557188632, 3, 4, 7⟩,
  ⟨396612216, 2, 5, 7⟩,
  ⟨148993416, 1, 6, 7⟩,
  ⟨23083632, 0, 7, 7⟩,
  ⟨20315295, 5, 1, 8⟩,
  ⟨97387290, 4, 2, 8⟩,
  ⟨184549365, 3, 3, 8⟩,
  ⟨172756584, 2, 4, 8⟩,
  ⟨79882803, 1, 5, 8⟩,
  ⟨14597154, 0, 6, 8⟩,
  ⟨9459450, 4, 1, 9⟩,
  ⟨35285250, 3, 2, 9⟩,
  ⟨48648600, 2, 3, 9⟩,
  ⟨29369340, 1, 4, 9⟩,
  ⟨6546540, 0, 5, 9⟩,
  ⟨2927925, 3, 1, 10⟩,
  ⟨7867860, 2, 2, 10⟩,
  ⟨6906900, 1, 3, 10⟩,
  ⟨1975974, 0, 4, 10⟩,
  ⟨540540, 2, 1, 11⟩,
  ⟨900900, 1, 2, 11⟩,
  ⟨360360, 0, 3, 11⟩,
  ⟨45045, 1, 1, 12⟩,
  ⟨30030, 0, 2, 12⟩]

private def evenKernelSixUnitGapCertificate (p q s : Rat) : Rat :=
  simplexCertEval evenKernelSixUnitGapTerms p q s

private theorem evenKernelSixUnitGapTerms_nonneg :
    simplexCertCoeffsNonneg evenKernelSixUnitGapTerms := by
  native_decide

private theorem evenKernelSixUnitGapCertificate_nonneg
    {p q s : Rat} (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s) :
    0 <= evenKernelSixUnitGapCertificate p q s :=
  simplexCertEval_nonneg hp hq hs evenKernelSixUnitGapTerms_nonneg

private theorem evenKernelSixUnitGap_eq_certificate (p r : Rat) :
    let q : Rat := r - p
    let s : Rat := 1 - r
    (1 + r * r) *
        (45045 - 15015 * (r * r + r * p + p * p) +
          9009 * (r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4) -
          6435 * (r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 +
            r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6) +
          5005 * (r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 +
            r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 +
            r * p ^ 7 + p ^ 8) -
          4095 * (r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 +
            r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 +
            r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10) +
          3465 * (r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 +
            r ^ 8 * p ^ 4 + r ^ 7 * p ^ 5 + r ^ 6 * p ^ 6 +
            r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8 + r ^ 3 * p ^ 9 +
            r ^ 2 * p ^ 10 + r * p ^ 11 + p ^ 12)) - 45045 =
      evenKernelSixUnitGapCertificate p q s := by
  intro q s
  unfold evenKernelSixUnitGapCertificate evenKernelSixUnitGapTerms
  simp [simplexCertEval, simplexCertTermEval]
  dsimp [q, s]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem kernelPartialIntegralBetween_six_lowerStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    ArctanGeometry.integralLowerStep p r <=
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 6 := by
  let L : Rat := r - p
  let D : Rat := 1 + r * r
  let S3 : Rat := r * r + r * p + p * p
  let S5 : Rat :=
    r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4
  let S7 : Rat :=
    r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 +
      r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6
  let S9 : Rat :=
    r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 +
      r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 +
      r * p ^ 7 + p ^ 8
  let S11 : Rat :=
    r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 +
      r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 +
      r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10
  let S13 : Rat :=
    r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 +
      r ^ 8 * p ^ 4 + r ^ 7 * p ^ 5 + r ^ 6 * p ^ 6 +
      r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8 + r ^ 3 * p ^ 9 +
      r ^ 2 * p ^ 10 + r * p ^ 11 + p ^ 12
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos r
  have h45045Dpos : 0 < 45045 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 45045) hDpos
  let q : Rat := r - p
  let s : Rat := 1 - r
  have hq0 : 0 <= q := by
    dsimp [q]
    grind [Rat.sub_eq_add_neg]
  have hs0 : 0 <= s := by
    dsimp [s]
    grind [Rat.sub_eq_add_neg]
  have hgap_cert := evenKernelSixUnitGap_eq_certificate p r
  have hgap_nonneg :
      0 <=
        D * (45045 - 15015 * S3 + 9009 * S5 -
          6435 * S7 + 5005 * S9 - 4095 * S11 + 3465 * S13) -
          45045 := by
    dsimp [D, S3, S5, S7, S9, S11, S13]
    rw [hgap_cert]
    exact evenKernelSixUnitGapCertificate_nonneg hp0 hq0 hs0
  have hscalar :
      45045 <=
        D * (45045 - 15015 * S3 + 9009 * S5 -
          6435 * S7 + 5005 * S9 - 4095 * S11 + 3465 * S13) := by
    grind [Rat.sub_eq_add_neg]
  have hlower_mul :
      ArctanGeometry.integralLowerStep p r * (45045 * D) = L * 45045 := by
    unfold ArctanGeometry.integralLowerStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 6 * (45045 * D) =
        L * (D * (45045 - 15015 * S3 + 9009 * S5 -
          6435 * S7 + 5005 * S9 - 4095 * S11 + 3465 * S13)) := by
    have hkernel_formula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 6 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 +
            (r ^ 5 - p ^ 5) / 5 - (r ^ 7 - p ^ 7) / 7 +
            (r ^ 9 - p ^ 9) / 9 - (r ^ 11 - p ^ 11) / 11 +
            (r ^ 13 - p ^ 13) / 13 := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcube : r ^ 3 - p ^ 3 = L * S3 := by
      dsimp [L, S3]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifth : r ^ 5 - p ^ 5 = L * S5 := by
      dsimp [L, S5]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hseventh : r ^ 7 - p ^ 7 = L * S7 := by
      dsimp [L, S7]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hninth : r ^ 9 - p ^ 9 = L * S9 := by
      dsimp [L, S9]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have heleventh : r ^ 11 - p ^ 11 = L * S11 := by
      dsimp [L, S11]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hthirteenth : r ^ 13 - p ^ 13 = L * S13 := by
      dsimp [L, S13]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hkernel_formula, hcube, hfifth, hseventh, hninth, heleventh,
      hthirteenth]
    dsimp [L, D, S3, S5, S7, S9, S11, S13]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 45045 * D)
  · rw [hlower_mul, hkernel_mul]
    exact Rat.mul_le_mul_of_nonneg_left hscalar hL0
  · exact h45045Dpos

theorem evenKernelCellBound_six : EvenKernelCellBound 6 := by
  intro p r hp0 hpr hr1
  exact kernelPartialIntegralBetween_six_lowerStep hp0 hpr hr1

private def oddKernelSevenUnitGapTerms : List SimplexCertTerm := [
  ⟨45045, 16, 0, 0⟩,
  ⟨360360, 15, 1, 0⟩,
  ⟨1921920, 14, 2, 0⟩,
  ⟨7507500, 13, 3, 0⟩,
  ⟨22402380, 12, 4, 0⟩,
  ⟨52072020, 11, 5, 0⟩,
  ⟨95238000, 10, 6, 0⟩,
  ⟨137773350, 9, 7, 0⟩,
  ⟨157861990, 8, 8, 0⟩,
  ⟨142906192, 7, 9, 0⟩,
  ⟨101471552, 6, 10, 0⟩,
  ⟨55762616, 5, 11, 0⟩,
  ⟨23197160, 4, 12, 0⟩,
  ⟨7047310, 3, 13, 0⟩,
  ⟨1471408, 2, 14, 0⟩,
  ⟨188173, 1, 15, 0⟩,
  ⟨11069, 0, 16, 0⟩,
  ⟨360360, 14, 1, 1⟩,
  ⟨4804800, 13, 2, 1⟩,
  ⟨30030000, 12, 3, 1⟩,
  ⟨115675560, 11, 4, 1⟩,
  ⟨305945640, 10, 5, 1⟩,
  ⟨586872000, 9, 6, 1⟩,
  ⟨841028760, 8, 7, 1⟩,
  ⟨913747120, 7, 8, 1⟩,
  ⟨755466712, 6, 9, 1⟩,
  ⟨472394832, 5, 10, 1⟩,
  ⟨219581180, 4, 11, 1⟩,
  ⟨73437140, 3, 12, 1⟩,
  ⟨16665720, 2, 13, 1⟩,
  ⟨2290048, 1, 14, 1⟩,
  ⟨143128, 0, 15, 1⟩,
  ⟨2342340, 13, 1, 2⟩,
  ⟨29609580, 12, 2, 2⟩,
  ⟨172071900, 11, 3, 2⟩,
  ⟨608648040, 10, 4, 2⟩,
  ⟨1461439980, 9, 5, 2⟩,
  ⟨2513845620, 8, 6, 2⟩,
  ⟨3184295400, 7, 7, 2⟩,
  ⟨3004361360, 6, 8, 2⟩,
  ⟨2108622516, 5, 9, 2⟩,
  ⟨1085595420, 4, 10, 2⟩,
  ⟨397701850, 3, 11, 2⟩,
  ⟨97921320, 2, 12, 2⟩,
  ⟨14472660, 1, 13, 2⟩,
  ⟨964844, 0, 14, 2⟩,
  ⟨10090080, 12, 1, 3⟩,
  ⟨116996880, 11, 2, 3⟩,
  ⟨619338720, 10, 3, 3⟩,
  ⟨1978136160, 9, 4, 3⟩,
  ⟨4242398160, 8, 5, 3⟩,
  ⟨6430195200, 7, 6, 3⟩,
  ⟨7054887840, 6, 7, 3⟩,
  ⟨5637391760, 5, 8, 3⟩,
  ⟨3250487240, 4, 9, 3⟩,
  ⟨1315972840, 3, 10, 3⟩,
  ⟨354055520, 2, 11, 3⟩,
  ⟨56608160, 1, 12, 3⟩,
  ⟨4043440, 0, 13, 3⟩,
  ⟨29729700, 11, 1, 4⟩,
  ⟨314113800, 10, 2, 4⟩,
  ⟨1501500000, 9, 3, 4⟩,
  ⟨4282518240, 8, 4, 4⟩,
  ⟨8089601520, 7, 5, 4⟩,
  ⟨10613562960, 6, 6, 4⟩,
  ⟨9853864020, 5, 7, 4⟩,
  ⟨6461354900, 4, 8, 4⟩,
  ⟨2925232310, 3, 9, 4⟩,
  ⟨867932520, 2, 10, 4⟩,
  ⟨151183760, 1, 11, 4⟩,
  ⟨11629520, 0, 12, 4⟩,
  ⟨63603540, 10, 1, 5⟩,
  ⟨606606000, 9, 2, 5⟩,
  ⟨2587925340, 8, 3, 5⟩,
  ⟨6496714224, 7, 4, 5⟩,
  ⟨10613586984, 6, 5, 5⟩,
  ⟨11770510752, 5, 6, 5⟩,
  ⟨8954765820, 4, 7, 5⟩,
  ⟨4601817220, 3, 8, 5⟩,
  ⟨1522965444, 2, 9, 5⟩,
  ⟨291489744, 1, 10, 5⟩,
  ⟨24290812, 0, 11, 5⟩,
  ⟨101891790, 9, 1, 6⟩,
  ⟨866635770, 8, 2, 6⟩,
  ⟨3251408160, 7, 3, 6⟩,
  ⟨7051788744, 6, 4, 6⟩,
  ⟨9725239524, 5, 5, 6⟩,
  ⟨8823114300, 4, 6, 6⟩,
  ⟨5249033790, 3, 7, 6⟩,
  ⟨1965843880, 2, 8, 6⟩,
  ⟨417791374, 1, 9, 6⟩,
  ⟨37981034, 0, 10, 6⟩,
  ⟨123963840, 8, 1, 7⟩,
  ⟨926365440, 7, 2, 7⟩,
  ⟨2999156160, 6, 3, 7⟩,
  ⟨5482949472, 5, 4, 7⟩,
  ⟨6173927760, 4, 5, 7⟩,
  ⟨4368627120, 3, 6, 7⟩,
  ⟨1887050880, 2, 7, 7⟩,
  ⟨451285120, 1, 8, 7⟩,
  ⟨45128512, 0, 9, 7⟩,
  ⟨114954840, 7, 1, 8⟩,
  ⟨740299560, 6, 2, 8⟩,
  ⟨2016754740, 5, 3, 8⟩,
  ⟨3003420420, 4, 4, 8⟩,
  ⟨2629396770, 3, 5, 8⟩,
  ⟨1344709080, 2, 6, 8⟩,
  ⟨368236440, 1, 7, 8⟩,
  ⟨40915160, 0, 8, 8⟩,
  ⟨80720640, 6, 1, 9⟩,
  ⟨436516080, 5, 2, 9⟩,
  ⟨966065100, 4, 3, 9⟩,
  ⟨1114293180, 3, 4, 9⟩,
  ⟨701020320, 2, 5, 9⟩,
  ⟨225139200, 1, 6, 9⟩,
  ⟨28142400, 0, 7, 9⟩,
  ⟨42162120, 5, 1, 10⟩,
  ⟨184624440, 4, 2, 10⟩,
  ⟨314984670, 3, 3, 10⟩,
  ⟨259170912, 2, 4, 10⟩,
  ⟨101092992, 1, 5, 10⟩,
  ⟨14441856, 0, 6, 10⟩,
  ⟨15855840, 4, 1, 11⟩,
  ⟨53213160, 3, 2, 11⟩,
  ⟨64144080, 2, 3, 11⟩,
  ⟨32144112, 1, 4, 11⟩,
  ⟨5357352, 0, 5, 11⟩,
  ⟨4054050, 3, 1, 12⟩,
  ⟨9489480, 2, 2, 12⟩,
  ⟨6786780, 1, 3, 12⟩,
  ⟨1357356, 0, 4, 12⟩,
  ⟨630630, 2, 1, 13⟩,
  ⟨840840, 1, 2, 13⟩,
  ⟨210210, 0, 3, 13⟩,
  ⟨45045, 1, 1, 14⟩,
  ⟨15015, 0, 2, 14⟩]

private def oddKernelSevenUnitGapCertificate (p q s : Rat) : Rat :=
  simplexCertEval oddKernelSevenUnitGapTerms p q s

private theorem oddKernelSevenUnitGapTerms_nonneg :
    simplexCertCoeffsNonneg oddKernelSevenUnitGapTerms := by
  native_decide

private theorem oddKernelSevenUnitGapCertificate_nonneg
    {p q s : Rat} (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s) :
    0 <= oddKernelSevenUnitGapCertificate p q s :=
  simplexCertEval_nonneg hp hq hs oddKernelSevenUnitGapTerms_nonneg

private theorem oddKernelSevenUnitGap_eq_certificate (p r : Rat) :
    let q : Rat := r - p
    let s : Rat := 1 - r
    45045 - (1 + p * p) *
        (45045 - 15015 * (r * r + r * p + p * p) +
          9009 * (r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4) -
          6435 * (r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 +
            r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6) +
          5005 * (r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 +
            r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 +
            r * p ^ 7 + p ^ 8) -
          4095 * (r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 +
            r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 +
            r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10) +
          3465 * (r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 +
            r ^ 8 * p ^ 4 + r ^ 7 * p ^ 5 + r ^ 6 * p ^ 6 +
            r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8 + r ^ 3 * p ^ 9 +
            r ^ 2 * p ^ 10 + r * p ^ 11 + p ^ 12) -
          3003 * (r ^ 14 + r ^ 13 * p + r ^ 12 * p ^ 2 + r ^ 11 * p ^ 3 +
            r ^ 10 * p ^ 4 + r ^ 9 * p ^ 5 + r ^ 8 * p ^ 6 +
            r ^ 7 * p ^ 7 + r ^ 6 * p ^ 8 + r ^ 5 * p ^ 9 +
            r ^ 4 * p ^ 10 + r ^ 3 * p ^ 11 + r ^ 2 * p ^ 12 +
            r * p ^ 13 + p ^ 14)) =
      oddKernelSevenUnitGapCertificate p q s := by
  intro q s
  unfold oddKernelSevenUnitGapCertificate oddKernelSevenUnitGapTerms
  simp [simplexCertEval, simplexCertTermEval]
  dsimp [q, s]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem kernelPartialIntegralBetween_seven_le_integralUpperStep_on_unit
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 7 <=
      ArctanGeometry.integralUpperStep p r := by
  let L : Rat := r - p
  let D : Rat := 1 + p * p
  let S3 : Rat := r * r + r * p + p * p
  let S5 : Rat :=
    r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4
  let S7 : Rat :=
    r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 +
      r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6
  let S9 : Rat :=
    r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 +
      r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 +
      r * p ^ 7 + p ^ 8
  let S11 : Rat :=
    r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 +
      r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 +
      r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10
  let S13 : Rat :=
    r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 +
      r ^ 8 * p ^ 4 + r ^ 7 * p ^ 5 + r ^ 6 * p ^ 6 +
      r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8 + r ^ 3 * p ^ 9 +
      r ^ 2 * p ^ 10 + r * p ^ 11 + p ^ 12
  let S15 : Rat :=
    r ^ 14 + r ^ 13 * p + r ^ 12 * p ^ 2 + r ^ 11 * p ^ 3 +
      r ^ 10 * p ^ 4 + r ^ 9 * p ^ 5 + r ^ 8 * p ^ 6 +
      r ^ 7 * p ^ 7 + r ^ 6 * p ^ 8 + r ^ 5 * p ^ 9 +
      r ^ 4 * p ^ 10 + r ^ 3 * p ^ 11 + r ^ 2 * p ^ 12 +
      r * p ^ 13 + p ^ 14
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos p
  have h45045Dpos : 0 < 45045 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 45045) hDpos
  let q : Rat := r - p
  let s : Rat := 1 - r
  have hq0 : 0 <= q := by
    dsimp [q]
    grind [Rat.sub_eq_add_neg]
  have hs0 : 0 <= s := by
    dsimp [s]
    grind [Rat.sub_eq_add_neg]
  have hgap_cert := oddKernelSevenUnitGap_eq_certificate p r
  have hgap_nonneg :
      0 <=
        45045 - D * (45045 - 15015 * S3 + 9009 * S5 -
          6435 * S7 + 5005 * S9 - 4095 * S11 + 3465 * S13 -
          3003 * S15) := by
    dsimp [D, S3, S5, S7, S9, S11, S13, S15]
    rw [hgap_cert]
    exact oddKernelSevenUnitGapCertificate_nonneg hp0 hq0 hs0
  have hscalar :
      D * (45045 - 15015 * S3 + 9009 * S5 -
          6435 * S7 + 5005 * S9 - 4095 * S11 + 3465 * S13 -
          3003 * S15) <= 45045 := by
    grind [Rat.sub_eq_add_neg]
  have hupper_mul :
      ArctanGeometry.integralUpperStep p r * (45045 * D) = L * 45045 := by
    unfold ArctanGeometry.integralUpperStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 7 * (45045 * D) =
        L * (D * (45045 - 15015 * S3 + 9009 * S5 -
          6435 * S7 + 5005 * S9 - 4095 * S11 + 3465 * S13 -
          3003 * S15)) := by
    have hkernel_formula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 7 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 +
            (r ^ 5 - p ^ 5) / 5 - (r ^ 7 - p ^ 7) / 7 +
            (r ^ 9 - p ^ 9) / 9 - (r ^ 11 - p ^ 11) / 11 +
            (r ^ 13 - p ^ 13) / 13 - (r ^ 15 - p ^ 15) / 15 := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcube : r ^ 3 - p ^ 3 = L * S3 := by
      dsimp [L, S3]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifth : r ^ 5 - p ^ 5 = L * S5 := by
      dsimp [L, S5]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hseventh : r ^ 7 - p ^ 7 = L * S7 := by
      dsimp [L, S7]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hninth : r ^ 9 - p ^ 9 = L * S9 := by
      dsimp [L, S9]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have heleventh : r ^ 11 - p ^ 11 = L * S11 := by
      dsimp [L, S11]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hthirteenth : r ^ 13 - p ^ 13 = L * S13 := by
      dsimp [L, S13]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifteenth : r ^ 15 - p ^ 15 = L * S15 := by
      dsimp [L, S15]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hkernel_formula, hcube, hfifth, hseventh, hninth, heleventh,
      hthirteenth, hfifteenth]
    dsimp [L, D, S3, S5, S7, S9, S11, S13, S15]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 45045 * D)
  · rw [hkernel_mul, hupper_mul]
    exact Rat.mul_le_mul_of_nonneg_left hscalar hL0
  · exact h45045Dpos

theorem oddKernelUnitCellBound_seven : OddKernelUnitCellBound 7 := by
  intro p r hp0 hpr hr1
  exact kernelPartialIntegralBetween_seven_le_integralUpperStep_on_unit hp0 hpr hr1

private def evenKernelEightUnitGapTerms : List SimplexCertTerm := [
  ⟨765765, 18, 0, 0⟩,
  ⟨7657650, 17, 1, 0⟩,
  ⟨47732685, 16, 2, 0⟩,
  ⟨218498280, 15, 3, 0⟩,
  ⟨768828060, 14, 4, 0⟩,
  ⟨2132910780, 13, 5, 0⟩,
  ⟨4734761460, 12, 6, 0⟩,
  ⟨8485113780, 11, 7, 0⟩,
  ⟨12338029990, 10, 8, 0⟩,
  ⟨14583559276, 9, 9, 0⟩,
  ⟨13993581654, 8, 10, 0⟩,
  ⟨10847311176, 7, 11, 0⟩,
  ⟨6730560984, 6, 12, 0⟩,
  ⟨3293444646, 5, 13, 0⟩,
  ⟨1241880804, 4, 14, 0⟩,
  ⟨347992686, 3, 15, 0⟩,
  ⟨68212269, 2, 16, 0⟩,
  ⟨8344906, 1, 17, 0⟩,
  ⟨479509, 0, 18, 0⟩,
  ⟨6126120, 16, 1, 1⟩,
  ⟨104144040, 15, 2, 1⟩,
  ⟨802521720, 14, 3, 1⟩,
  ⟨3822698880, 13, 4, 1⟩,
  ⟨12647374740, 12, 5, 1⟩,
  ⟨30841075980, 11, 6, 1⟩,
  ⟨57349234800, 10, 7, 1⟩,
  ⟨82942413840, 9, 8, 1⟩,
  ⟨94267684368, 8, 9, 1⟩,
  ⟨84449471184, 7, 10, 1⟩,
  ⟨59413172364, 6, 11, 1⟩,
  ⟨32469387048, 5, 12, 1⟩,
  ⟨13508215470, 4, 13, 1⟩,
  ⟨4134652722, 3, 14, 1⟩,
  ⟨877955616, 2, 15, 1⟩,
  ⟨115541136, 1, 16, 1⟩,
  ⟨7099632, 0, 17, 1⟩,
  ⟨52072020, 15, 1, 2⟩,
  ⟨792311520, 14, 2, 2⟩,
  ⟨5630925300, 13, 3, 2⟩,
  ⟨24760756020, 12, 4, 2⟩,
  ⟨75294609390, 11, 5, 2⟩,
  ⟨167666653440, 10, 6, 2⟩,
  ⟨282355496280, 9, 7, 2⟩,
  ⟨366041698880, 8, 8, 2⟩,
  ⟨368169932416, 7, 9, 2⟩,
  ⟨287197356992, 6, 10, 2⟩,
  ⟨172266367546, 5, 11, 2⟩,
  ⟨77999360390, 4, 12, 2⟩,
  ⟨25799627125, 3, 13, 2⟩,
  ⟨5884288064, 2, 14, 2⟩,
  ⟨827427808, 1, 15, 2⟩,
  ⟨54077624, 0, 16, 2⟩,
  ⟨257297040, 14, 1, 3⟩,
  ⟨3655251600, 13, 2, 3⟩,
  ⟨24085861800, 12, 3, 3⟩,
  ⟨97533956520, 11, 4, 3⟩,
  ⟨271097146320, 10, 5, 3⟩,
  ⟨546965081520, 9, 6, 3⟩,
  ⟨825793974720, 8, 7, 3⟩,
  ⟨947407764160, 7, 8, 3⟩,
  ⟨829656619792, 6, 9, 3⟩,
  ⟨551660596032, 5, 10, 3⟩,
  ⟨274075894820, 4, 11, 3⟩,
  ⟨98632471700, 3, 12, 3⟩,
  ⟨24301202160, 2, 13, 3⟩,
  ⟨3668988688, 1, 14, 3⟩,
  ⟨256113568, 0, 15, 3⟩,
  ⟨888287400, 13, 1, 4⟩,
  ⟨11690679000, 12, 2, 4⟩,
  ⟨70902181350, 11, 3, 4⟩,
  ⟨262326584520, 10, 4, 4⟩,
  ⟨660380420700, 9, 5, 4⟩,
  ⟨1194043799520, 8, 6, 4⟩,
  ⟨1594719615060, 7, 7, 4⟩,
  ⟨1592221811180, 6, 8, 4⟩,
  ⟨1187970962178, 5, 9, 4⟩,
  ⟨653955605940, 4, 10, 4⟩,
  ⟨258100312015, 3, 11, 4⟩,
  ⟨69151285560, 2, 12, 4⟩,
  ⟨11272447380, 1, 13, 4⟩,
  ⟨844409312, 0, 14, 4⟩,
  ⟨2263601340, 12, 1, 5⟩,
  ⟨27409281900, 11, 2, 5⟩,
  ⟨151831800120, 10, 3, 5⟩,
  ⟨508592116032, 9, 4, 5⟩,
  ⟨1146932594808, 8, 5, 5⟩,
  ⟨1833681207072, 7, 6, 5⟩,
  ⟨2130257557428, 6, 7, 5⟩,
  ⟨1811197860472, 5, 8, 5⟩,
  ⟨1118141906882, 4, 9, 5⟩,
  ⟨488685533518, 3, 10, 5⟩,
  ⟨143506489672, 2, 11, 5⟩,
  ⟨25422783008, 1, 12, 5⟩,
  ⟨2054831752, 0, 13, 5⟩,
  ⟨4400085690, 11, 1, 6⟩,
  ⟨48647518920, 10, 2, 6⟩,
  ⟨243877774140, 9, 3, 6⟩,
  ⟨731466691956, 8, 4, 6⟩,
  ⟨1457806638288, 7, 5, 6⟩,
  ⟨2026212556368, 6, 6, 6⟩,
  ⟨2003281366086, 5, 7, 6⟩,
  ⟨1408382565590, 4, 8, 6⟩,
  ⟨689830602461, 3, 9, 6⟩,
  ⟨224162564808, 2, 10, 6⟩,
  ⟨43492673588, 1, 11, 6⟩,
  ⟨3817301516, 0, 12, 6⟩,
  ⟨6652966320, 10, 1, 7⟩,
  ⟨66533747280, 9, 2, 7⟩,
  ⟨298489070880, 8, 3, 7⟩,
  ⟨790720362432, 7, 4, 7⟩,
  ⟨1369101237504, 6, 5, 7⟩,
  ⟨1618271658432, 5, 6, 7⟩,
  ⟨1321940557080, 4, 7, 7⟩,
  ⟨736747125400, 3, 8, 7⟩,
  ⟨268067225712, 2, 9, 7⟩,
  ⟨57499847184, 1, 10, 7⟩,
  ⟨5521683232, 0, 11, 7⟩,
  ⟨7901163270, 9, 1, 8⟩,
  ⟨70665815220, 8, 2, 8⟩,
  ⟨279803383860, 7, 3, 8⟩,
  ⟨643434755964, 6, 4, 8⟩,
  ⟨946593461814, 5, 5, 8⟩,
  ⟨923562765840, 4, 6, 8⟩,
  ⟨597457328325, 3, 7, 8⟩,
  ⟨247078866320, 2, 8, 8⟩,
  ⟨59271168814, 1, 9, 8⟩,
  ⟨6284233124, 0, 10, 8⟩,
  ⟨7388100720, 8, 1, 9⟩,
  ⟨58267569360, 7, 2, 9⟩,
  ⟨200078058180, 6, 3, 9⟩,
  ⟨390502168056, 5, 4, 9⟩,
  ⟨473642499330, 4, 5, 9⟩,
  ⟨365483662830, 3, 6, 9⟩,
  ⟨175191279120, 2, 7, 9⟩,
  ⟨47691746960, 1, 8, 9⟩,
  ⟨5645209856, 0, 9, 9⟩,
  ⟨5415490080, 7, 1, 10⟩,
  ⟨36993596640, 6, 2, 10⟩,
  ⟨107665027470, 5, 3, 10⟩,
  ⟨172983556746, 4, 4, 10⟩,
  ⟨165657891399, 3, 5, 10⟩,
  ⟨94539684096, 2, 6, 10⟩,
  ⟨29767167144, 1, 7, 10⟩,
  ⟨3988823696, 0, 8, 10⟩,
  ⟨3075312240, 6, 1, 11⟩,
  ⟨17773916160, 5, 2, 11⟩,
  ⟨42497915460, 4, 3, 11⟩,
  ⟨53788763028, 3, 4, 11⟩,
  ⟨37997463504, 2, 5, 11⟩,
  ⟨14201279664, 1, 6, 11⟩,
  ⟨2193267648, 0, 7, 11⟩,
  ⟨1324773450, 5, 1, 12⟩,
  ⟨6273146880, 4, 2, 12⟩,
  ⟨11778231465, 3, 3, 12⟩,
  ⟨10955340396, 2, 4, 12⟩,
  ⟨5045472432, 1, 5, 12⟩,
  ⟨919880676, 0, 6, 12⟩,
  ⟨418107690, 4, 1, 13⟩,
  ⟨1547355810, 3, 2, 13⟩,
  ⟨2122700580, 2, 3, 13⟩,
  ⟨1277908632, 1, 4, 13⟩,
  ⟨284456172, 0, 5, 13⟩,
  ⟨91126035, 3, 1, 14⟩,
  ⟨244023780, 2, 2, 14⟩,
  ⟨213903690, 1, 3, 14⟩,
  ⟨61159098, 0, 4, 14⟩,
  ⟨12252240, 2, 1, 15⟩,
  ⟨20420400, 1, 2, 15⟩,
  ⟨8168160, 0, 3, 15⟩,
  ⟨765765, 1, 1, 16⟩,
  ⟨510510, 0, 2, 16⟩]

private def evenKernelEightUnitGapCertificate (p q s : Rat) : Rat :=
  simplexCertEval evenKernelEightUnitGapTerms p q s

private theorem evenKernelEightUnitGapTerms_nonneg :
    simplexCertCoeffsNonneg evenKernelEightUnitGapTerms := by
  native_decide

private theorem evenKernelEightUnitGapCertificate_nonneg
    {p q s : Rat} (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s) :
    0 <= evenKernelEightUnitGapCertificate p q s :=
  simplexCertEval_nonneg hp hq hs evenKernelEightUnitGapTerms_nonneg

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem evenKernelEightUnitGap_eq_certificate (p r : Rat) :
    let q : Rat := r - p
    let s : Rat := 1 - r
    (1 + r * r) *
      (765765 - 255255 * (r ^ 2 + r * p + p ^ 2)
        + 153153 * (r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4)
        - 109395 * (r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 + r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6)
        + 85085 * (r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 + r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 + r * p ^ 7 + p ^ 8)
        - 69615 * (r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 + r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 + r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10)
        + 58905 * (r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 + r ^ 8 * p ^ 4 + r ^ 7 * p ^ 5 + r ^ 6 * p ^ 6 + r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8 + r ^ 3 * p ^ 9 + r ^ 2 * p ^ 10 + r * p ^ 11 + p ^ 12)
        - 51051 * (r ^ 14 + r ^ 13 * p + r ^ 12 * p ^ 2 + r ^ 11 * p ^ 3 + r ^ 10 * p ^ 4 + r ^ 9 * p ^ 5 + r ^ 8 * p ^ 6 + r ^ 7 * p ^ 7 + r ^ 6 * p ^ 8 + r ^ 5 * p ^ 9 + r ^ 4 * p ^ 10 + r ^ 3 * p ^ 11 + r ^ 2 * p ^ 12 + r * p ^ 13 + p ^ 14)
        + 45045 * (r ^ 16 + r ^ 15 * p + r ^ 14 * p ^ 2 + r ^ 13 * p ^ 3 + r ^ 12 * p ^ 4 + r ^ 11 * p ^ 5 + r ^ 10 * p ^ 6 + r ^ 9 * p ^ 7 + r ^ 8 * p ^ 8 + r ^ 7 * p ^ 9 + r ^ 6 * p ^ 10 + r ^ 5 * p ^ 11 + r ^ 4 * p ^ 12 + r ^ 3 * p ^ 13 + r ^ 2 * p ^ 14 + r * p ^ 15 + p ^ 16)
          ) - 765765 =
      evenKernelEightUnitGapCertificate p q s := by
  intro q s
  unfold evenKernelEightUnitGapCertificate evenKernelEightUnitGapTerms
  simp [simplexCertEval, simplexCertTermEval]
  dsimp [q, s]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem kernelPartialIntegralBetween_eight_lowerStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    ArctanGeometry.integralLowerStep p r <=
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 8 := by
  let L : Rat := r - p
  let D : Rat := 1 + r * r
  let S3 : Rat :=
    r ^ 2 + r * p + p ^ 2
  let S5 : Rat :=
    r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4
  let S7 : Rat :=
    r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 + r ^ 2 * p ^ 4
      + r * p ^ 5 + p ^ 6
  let S9 : Rat :=
    r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 + r ^ 4 * p ^ 4
      + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 + r * p ^ 7 + p ^ 8
  let S11 : Rat :=
    r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 + r ^ 6 * p ^ 4
      + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 + r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8
      + r * p ^ 9 + p ^ 10
  let S13 : Rat :=
    r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 + r ^ 8 * p ^ 4
      + r ^ 7 * p ^ 5 + r ^ 6 * p ^ 6 + r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8
      + r ^ 3 * p ^ 9 + r ^ 2 * p ^ 10 + r * p ^ 11 + p ^ 12
  let S15 : Rat :=
    r ^ 14 + r ^ 13 * p + r ^ 12 * p ^ 2 + r ^ 11 * p ^ 3 + r ^ 10 * p ^ 4
      + r ^ 9 * p ^ 5 + r ^ 8 * p ^ 6 + r ^ 7 * p ^ 7 + r ^ 6 * p ^ 8
      + r ^ 5 * p ^ 9 + r ^ 4 * p ^ 10 + r ^ 3 * p ^ 11 + r ^ 2 * p ^ 12
      + r * p ^ 13 + p ^ 14
  let S17 : Rat :=
    r ^ 16 + r ^ 15 * p + r ^ 14 * p ^ 2 + r ^ 13 * p ^ 3 + r ^ 12 * p ^ 4
      + r ^ 11 * p ^ 5 + r ^ 10 * p ^ 6 + r ^ 9 * p ^ 7 + r ^ 8 * p ^ 8
      + r ^ 7 * p ^ 9 + r ^ 6 * p ^ 10 + r ^ 5 * p ^ 11 + r ^ 4 * p ^ 12
      + r ^ 3 * p ^ 13 + r ^ 2 * p ^ 14 + r * p ^ 15 + p ^ 16
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos r
  have h765765Dpos : 0 < 765765 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 765765) hDpos
  let q : Rat := r - p
  let s : Rat := 1 - r
  have hq0 : 0 <= q := by
    dsimp [q]
    grind [Rat.sub_eq_add_neg]
  have hs0 : 0 <= s := by
    dsimp [s]
    grind [Rat.sub_eq_add_neg]
  have hgap_cert := evenKernelEightUnitGap_eq_certificate p r
  have hgap_nonneg :
      0 <=
        D * (765765 - 255255 * S3 + 153153 * S5 - 109395 * S7 + 85085 * S9 - 69615 * S11 + 58905 * S13
          - 51051 * S15 + 45045 * S17
          ) - 765765 := by
    dsimp [D, S3, S5, S7, S9, S11, S13, S15, S17]
    rw [hgap_cert]
    exact evenKernelEightUnitGapCertificate_nonneg hp0 hq0 hs0
  have hscalar :
      765765 <=
        D * (765765 - 255255 * S3 + 153153 * S5 - 109395 * S7 + 85085 * S9 - 69615 * S11 + 58905 * S13
          - 51051 * S15 + 45045 * S17
          ) := by
    grind [Rat.sub_eq_add_neg]
  have hlower_mul :
      ArctanGeometry.integralLowerStep p r * (765765 * D) = L * 765765 := by
    unfold ArctanGeometry.integralLowerStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 8 * (765765 * D) =
        L * (D * (765765 - 255255 * S3 + 153153 * S5 - 109395 * S7 + 85085 * S9 - 69615 * S11 + 58905 * S13
          - 51051 * S15 + 45045 * S17
          )) := by
    have hkernel_formula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 8 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 + (r ^ 5 - p ^ 5) / 5 - (r ^ 7 - p ^ 7) / 7
          + (r ^ 9 - p ^ 9) / 9 - (r ^ 11 - p ^ 11) / 11 + (r ^ 13 - p ^ 13) / 13
          - (r ^ 15 - p ^ 15) / 15 + (r ^ 17 - p ^ 17) / 17 := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcube : r ^ 3 - p ^ 3 = L * S3 := by
      dsimp [L, S3]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifth : r ^ 5 - p ^ 5 = L * S5 := by
      dsimp [L, S5]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hseventh : r ^ 7 - p ^ 7 = L * S7 := by
      dsimp [L, S7]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hninth : r ^ 9 - p ^ 9 = L * S9 := by
      dsimp [L, S9]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have heleventh : r ^ 11 - p ^ 11 = L * S11 := by
      dsimp [L, S11]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hthirteenth : r ^ 13 - p ^ 13 = L * S13 := by
      dsimp [L, S13]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifteenth : r ^ 15 - p ^ 15 = L * S15 := by
      dsimp [L, S15]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hseventeenth : r ^ 17 - p ^ 17 = L * S17 := by
      dsimp [L, S17]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hkernel_formula, hcube, hfifth, hseventh, hninth,
      heleventh, hthirteenth, hfifteenth, hseventeenth]
    dsimp [L, D, S3, S5, S7, S9, S11, S13, S15, S17]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 765765 * D)
  · rw [hlower_mul, hkernel_mul]
    exact Rat.mul_le_mul_of_nonneg_left hscalar hL0
  · exact h765765Dpos

theorem evenKernelCellBound_eight : EvenKernelCellBound 8 := by
  intro p r hp0 hpr hr1
  exact kernelPartialIntegralBetween_eight_lowerStep hp0 hpr hr1

private def oddKernelNineUnitGapTerms : List SimplexCertTerm := [
  ⟨14549535, 20, 0, 0⟩,
  ⟨145495350, 19, 1, 0⟩,
  ⟨969969000, 18, 2, 0⟩,
  ⟨4777097325, 17, 3, 0⟩,
  ⟨18259666425, 16, 4, 0⟩,
  ⟨55579223700, 15, 5, 0⟩,
  ⟨136760086320, 14, 6, 0⟩,
  ⟨274691063790, 13, 7, 0⟩,
  ⟨453274365830, 12, 8, 0⟩,
  ⟨616889383396, 11, 9, 0⟩,
  ⟨693526323360, 10, 10, 0⟩,
  ⟨643503644758, 9, 11, 0⟩,
  ⟨491037337182, 8, 12, 0⟩,
  ⟨306051675138, 7, 13, 0⟩,
  ⟨154119263952, 6, 14, 0⟩,
  ⟨61681042863, 5, 15, 0⟩,
  ⟨19141496667, 4, 16, 0⟩,
  ⟨4434789278, 3, 17, 0⟩,
  ⟨720827032, 2, 18, 0⟩,
  ⟨73189137, 1, 19, 0⟩,
  ⟨3485197, 0, 20, 0⟩,
  ⟨145495350, 18, 1, 1⟩,
  ⟨2521919400, 17, 2, 1⟩,
  ⟨20805835050, 16, 3, 1⟩,
  ⟨107899351560, 15, 4, 1⟩,
  ⟨393380627640, 14, 5, 1⟩,
  ⟨1069648557120, 13, 6, 1⟩,
  ⟨2246664368520, 12, 7, 1⟩,
  ⟨3725153935360, 11, 8, 1⟩,
  ⟨4940675668500, 10, 9, 1⟩,
  ⟨5278303838496, 9, 10, 1⟩,
  ⟨4550680459416, 8, 11, 1⟩,
  ⟨3156843498732, 7, 12, 1⟩,
  ⟨1747848982680, 6, 13, 1⟩,
  ⟨761320695168, 5, 14, 1⟩,
  ⟨254912946264, 4, 15, 1⟩,
  ⟨63239737104, 3, 16, 1⟩,
  ⟨10931301958, 2, 17, 1⟩,
  ⟨1172792040, 1, 18, 1⟩,
  ⟨58639602, 0, 19, 1⟩,
  ⟨1236710475, 17, 1, 2⟩,
  ⟨20587592025, 16, 2, 2⟩,
  ⟨160917857100, 15, 3, 2⟩,
  ⟨784394530920, 14, 4, 2⟩,
  ⟨2670305257620, 13, 5, 2⟩,
  ⟨6735844409580, 12, 6, 2⟩,
  ⟨13033273916520, 11, 7, 2⟩,
  ⟨19751589600600, 10, 8, 2⟩,
  ⟨23725183173978, 9, 9, 2⟩,
  ⟨22705993210446, 8, 10, 2⟩,
  ⟨17304035506758, 7, 11, 2⟩,
  ⟨10434292427160, 6, 12, 2⟩,
  ⟨4913463667860, 5, 13, 2⟩,
  ⟨1767227265612, 4, 14, 2⟩,
  ⟨468281978784, 3, 15, 2⟩,
  ⟨86014612872, 2, 16, 2⟩,
  ⟨9759318555, 1, 17, 2⟩,
  ⟨513648345, 0, 18, 2⟩,
  ⟨6983776800, 16, 1, 3⟩,
  ⟨109024515600, 15, 2, 3⟩,
  ⟨796150555200, 14, 3, 3⟩,
  ⟨3609215850240, 13, 4, 3⟩,
  ⟨11365398364320, 12, 5, 3⟩,
  ⟨26352361669920, 11, 6, 3⟩,
  ⟨46521597751200, 10, 7, 3⟩,
  ⟨63756978759760, 9, 8, 3⟩,
  ⟨68517841944552, 8, 9, 3⟩,
  ⟨57897767759832, 7, 10, 3⟩,
  ⟨38312773786560, 6, 11, 3⟩,
  ⟨19628304622080, 5, 12, 3⟩,
  ⟨7624160062560, 4, 13, 3⟩,
  ⟨2167714426848, 3, 14, 3⟩,
  ⟨424756142208, 2, 15, 3⟩,
  ⟨51135648480, 1, 16, 3⟩,
  ⟨2840869360, 0, 17, 3⟩,
  ⟨27644116500, 15, 1, 4⟩,
  ⟨403313110200, 14, 2, 4⟩,
  ⟨2739386449800, 13, 3, 4⟩,
  ⟨11487265269480, 12, 4, 4⟩,
  ⟨33247278224160, 11, 5, 4⟩,
  ⟨70323223627800, 10, 6, 4⟩,
  ⟨112244449634460, 9, 7, 4⟩,
  ⟨137589152080380, 8, 8, 4⟩,
  ⟨130506808970538, 7, 9, 4⟩,
  ⟨95713729773480, 6, 10, 4⟩,
  ⟨53782491923160, 5, 11, 4⟩,
  ⟨22712537163960, 4, 12, 4⟩,
  ⟨6967876207680, 3, 13, 4⟩,
  ⟨1463322101832, 2, 14, 4⟩,
  ⟨187645454640, 1, 15, 4⟩,
  ⟨11037967920, 0, 16, 4⟩,
  ⟨81651990420, 14, 1, 5⟩,
  ⟨1107859793040, 13, 2, 5⟩,
  ⟨6959158986780, 12, 3, 5⟩,
  ⟨26815537941192, 11, 4, 5⟩,
  ⟨70780752462420, 10, 5, 5⟩,
  ⟨135316302428736, 9, 6, 5⟩,
  ⟨193107574243584, 8, 7, 5⟩,
  ⟨208832583635676, 7, 8, 5⟩,
  ⟨171829740638556, 6, 9, 5⟩,
  ⟨106940572122384, 5, 10, 5⟩,
  ⟨49493261140596, 4, 11, 5⟩,
  ⟨16491315859704, 3, 12, 5⟩,
  ⟨3732036332796, 2, 13, 5⟩,
  ⟨512004282048, 1, 14, 5⟩,
  ⟨32000267628, 0, 15, 5⟩,
  ⟨186495939630, 13, 1, 6⟩,
  ⟨2339574927690, 12, 2, 6⟩,
  ⟨13500649322160, 11, 3, 6⟩,
  ⟨47428283202300, 10, 4, 6⟩,
  ⟨113110120084962, 9, 5, 6⟩,
  ⟨193257475192782, 8, 6, 6⟩,
  ⟨243191467673154, 7, 7, 6⟩,
  ⟨228001727913960, 6, 8, 6⟩,
  ⟨159082972562514, 5, 9, 6⟩,
  ⟨81472170336102, 4, 10, 6⟩,
  ⟨29716154401752, 3, 11, 6⟩,
  ⟨7292783609244, 2, 12, 6⟩,
  ⟨1075880729070, 1, 13, 6⟩,
  ⟨71725381938, 0, 14, 6⟩,
  ⟨336618041760, 12, 1, 7⟩,
  ⟨3878168854560, 11, 2, 7⟩,
  ⟨20396352936960, 10, 3, 7⟩,
  ⟨64714376222496, 9, 4, 7⟩,
  ⟨137868181122672, 8, 5, 7⟩,
  ⟨207597494394576, 7, 6, 7⟩,
  ⟨226326247804800, 6, 7, 7⟩,
  ⟨179784851600640, 5, 8, 7⟩,
  ⟨103117167163296, 4, 9, 7⟩,
  ⟨41563897438752, 3, 10, 7⟩,
  ⟨11145936050496, 2, 11, 7⟩,
  ⟨1778769578880, 1, 12, 7⟩,
  ⟨127054969920, 0, 13, 7⟩,
  ⟨486536450400, 11, 1, 8⟩,
  ⟨5106828586860, 10, 2, 8⟩,
  ⟨24246741879360, 9, 3, 8⟩,
  ⟨68687400285504, 8, 4, 8⟩,
  ⟨128882929549374, 7, 5, 8⟩,
  ⟨168007172069880, 6, 6, 8⟩,
  ⟨155047277693880, 5, 7, 8⟩,
  ⟨101125470508920, 4, 8, 8⟩,
  ⟨45579113792784, 3, 9, 8⟩,
  ⟨13478955423804, 2, 10, 8⟩,
  ⟨2343496247820, 1, 11, 8⟩,
  ⟨180268942140, 0, 12, 8⟩,
  ⟨567024478020, 10, 1, 9⟩,
  ⟨5370369164160, 9, 2, 9⟩,
  ⟨22752679229280, 8, 3, 9⟩,
  ⟨56729766008916, 7, 4, 9⟩,
  ⟨92073686544840, 6, 5, 9⟩,
  ⟨101491747431360, 5, 6, 9⟩,
  ⟨76798647988920, 4, 7, 9⟩,
  ⟨39290942593760, 3, 8, 9⟩,
  ⟨12960404487316, 2, 9, 9⟩,
  ⟨2475946396560, 1, 10, 9⟩,
  ⟨206328866380, 0, 11, 9⟩,
  ⟨533764241010, 9, 1, 10⟩,
  ⟨4508173419750, 8, 2, 10⟩,
  ⟨16797583652850, 7, 3, 10⟩,
  ⟨36192189465432, 6, 4, 10⟩,
  ⟨49610697932796, 5, 5, 10⟩,
  ⟨44768398737348, 4, 6, 10⟩,
  ⟨26516266477272, 3, 7, 10⟩,
  ⟨9898472306008, 2, 8, 10⟩,
  ⟨2099814110394, 1, 9, 10⟩,
  ⟨190892191854, 0, 10, 10⟩,
  ⟨404593469280, 8, 1, 11⟩,
  ⟨3002674835160, 7, 2, 11⟩,
  ⟨9657632144160, 6, 3, 11⟩,
  ⟨17549672396256, 5, 4, 11⟩,
  ⟨19657609027056, 4, 5, 11⟩,
  ⟨13849866984096, 3, 6, 11⟩,
  ⟨5963693104512, 2, 7, 11⟩,
  ⟨1423681699440, 1, 8, 11⟩,
  ⟨142368169944, 0, 9, 11⟩,
  ⟨244926872190, 7, 1, 12⟩,
  ⟨1567120715160, 6, 2, 12⟩,
  ⟨4244196356400, 5, 3, 12⟩,
  ⟨6288611657328, 4, 4, 12⟩,
  ⟨5482947646176, 3, 5, 12⟩,
  ⟨2795731117608, 2, 6, 12⟩,
  ⟨764316172620, 1, 7, 12⟩,
  ⟨84924019180, 0, 8, 12⟩,
  ⟨116716369770, 6, 1, 13⟩,
  ⟨627647540520, 5, 2, 13⟩,
  ⟨1382467716630, 4, 3, 13⟩,
  ⟨1588564789812, 3, 4, 13⟩,
  ⟨996699405702, 2, 5, 13⟩,
  ⟨319624184880, 1, 6, 13⟩,
  ⟨39953023110, 0, 7, 13⟩,
  ⟨42790182435, 5, 1, 14⟩,
  ⟨186568687305, 4, 2, 14⟩,
  ⟨317238061140, 3, 3, 14⟩,
  ⟨260419217058, 2, 4, 14⟩,
  ⟨101453907555, 1, 5, 14⟩,
  ⟨14493415365, 0, 6, 14⟩,
  ⟨11639628000, 4, 1, 15⟩,
  ⟨38953955040, 3, 2, 15⟩,
  ⟨46868902080, 2, 3, 15⟩,
  ⟨23465490048, 1, 4, 15⟩,
  ⟨3910915008, 0, 5, 15⟩,
  ⟨2211529320, 3, 1, 16⟩,
  ⟨5169934770, 2, 2, 16⟩,
  ⟨3695581890, 1, 3, 16⟩,
  ⟨739116378, 0, 4, 16⟩,
  ⟨261891630, 2, 1, 17⟩,
  ⟨349188840, 1, 2, 17⟩,
  ⟨87297210, 0, 3, 17⟩,
  ⟨14549535, 1, 1, 18⟩,
  ⟨4849845, 0, 2, 18⟩]

private def oddKernelNineUnitGapCertificate (p q s : Rat) : Rat :=
  simplexCertEval oddKernelNineUnitGapTerms p q s

private theorem oddKernelNineUnitGapTerms_nonneg :
    simplexCertCoeffsNonneg oddKernelNineUnitGapTerms := by
  native_decide

private theorem oddKernelNineUnitGapCertificate_nonneg
    {p q s : Rat} (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s) :
    0 <= oddKernelNineUnitGapCertificate p q s :=
  simplexCertEval_nonneg hp hq hs oddKernelNineUnitGapTerms_nonneg

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem oddKernelNineUnitGap_eq_certificate (p r : Rat) :
    let q : Rat := r - p
    let s : Rat := 1 - r
    14549535 - (1 + p * p) *
      (14549535 - 4849845 * (r ^ 2 + r * p + p ^ 2)
        + 2909907 * (r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4)
        - 2078505 * (r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 + r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6)
        + 1616615 * (r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 + r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 + r * p ^ 7 + p ^ 8)
        - 1322685 * (r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 + r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 + r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10)
        + 1119195 * (r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 + r ^ 8 * p ^ 4 + r ^ 7 * p ^ 5 + r ^ 6 * p ^ 6 + r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8 + r ^ 3 * p ^ 9 + r ^ 2 * p ^ 10 + r * p ^ 11 + p ^ 12)
        - 969969 * (r ^ 14 + r ^ 13 * p + r ^ 12 * p ^ 2 + r ^ 11 * p ^ 3 + r ^ 10 * p ^ 4 + r ^ 9 * p ^ 5 + r ^ 8 * p ^ 6 + r ^ 7 * p ^ 7 + r ^ 6 * p ^ 8 + r ^ 5 * p ^ 9 + r ^ 4 * p ^ 10 + r ^ 3 * p ^ 11 + r ^ 2 * p ^ 12 + r * p ^ 13 + p ^ 14)
        + 855855 * (r ^ 16 + r ^ 15 * p + r ^ 14 * p ^ 2 + r ^ 13 * p ^ 3 + r ^ 12 * p ^ 4 + r ^ 11 * p ^ 5 + r ^ 10 * p ^ 6 + r ^ 9 * p ^ 7 + r ^ 8 * p ^ 8 + r ^ 7 * p ^ 9 + r ^ 6 * p ^ 10 + r ^ 5 * p ^ 11 + r ^ 4 * p ^ 12 + r ^ 3 * p ^ 13 + r ^ 2 * p ^ 14 + r * p ^ 15 + p ^ 16)
        - 765765 * (r ^ 18 + r ^ 17 * p + r ^ 16 * p ^ 2 + r ^ 15 * p ^ 3 + r ^ 14 * p ^ 4 + r ^ 13 * p ^ 5 + r ^ 12 * p ^ 6 + r ^ 11 * p ^ 7 + r ^ 10 * p ^ 8 + r ^ 9 * p ^ 9 + r ^ 8 * p ^ 10 + r ^ 7 * p ^ 11 + r ^ 6 * p ^ 12 + r ^ 5 * p ^ 13 + r ^ 4 * p ^ 14 + r ^ 3 * p ^ 15 + r ^ 2 * p ^ 16 + r * p ^ 17 + p ^ 18)
          ) =
      oddKernelNineUnitGapCertificate p q s := by
  intro q s
  unfold oddKernelNineUnitGapCertificate oddKernelNineUnitGapTerms
  simp [simplexCertEval, simplexCertTermEval]
  dsimp [q, s]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem kernelPartialIntegralBetween_nine_le_integralUpperStep_on_unit
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 9 <=
      ArctanGeometry.integralUpperStep p r := by
  let L : Rat := r - p
  let D : Rat := 1 + p * p
  let S3 : Rat :=
    r ^ 2 + r * p + p ^ 2
  let S5 : Rat :=
    r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4
  let S7 : Rat :=
    r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 + r ^ 2 * p ^ 4
      + r * p ^ 5 + p ^ 6
  let S9 : Rat :=
    r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 + r ^ 4 * p ^ 4
      + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 + r * p ^ 7 + p ^ 8
  let S11 : Rat :=
    r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 + r ^ 6 * p ^ 4
      + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 + r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8
      + r * p ^ 9 + p ^ 10
  let S13 : Rat :=
    r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 + r ^ 8 * p ^ 4
      + r ^ 7 * p ^ 5 + r ^ 6 * p ^ 6 + r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8
      + r ^ 3 * p ^ 9 + r ^ 2 * p ^ 10 + r * p ^ 11 + p ^ 12
  let S15 : Rat :=
    r ^ 14 + r ^ 13 * p + r ^ 12 * p ^ 2 + r ^ 11 * p ^ 3 + r ^ 10 * p ^ 4
      + r ^ 9 * p ^ 5 + r ^ 8 * p ^ 6 + r ^ 7 * p ^ 7 + r ^ 6 * p ^ 8
      + r ^ 5 * p ^ 9 + r ^ 4 * p ^ 10 + r ^ 3 * p ^ 11 + r ^ 2 * p ^ 12
      + r * p ^ 13 + p ^ 14
  let S17 : Rat :=
    r ^ 16 + r ^ 15 * p + r ^ 14 * p ^ 2 + r ^ 13 * p ^ 3 + r ^ 12 * p ^ 4
      + r ^ 11 * p ^ 5 + r ^ 10 * p ^ 6 + r ^ 9 * p ^ 7 + r ^ 8 * p ^ 8
      + r ^ 7 * p ^ 9 + r ^ 6 * p ^ 10 + r ^ 5 * p ^ 11 + r ^ 4 * p ^ 12
      + r ^ 3 * p ^ 13 + r ^ 2 * p ^ 14 + r * p ^ 15 + p ^ 16
  let S19 : Rat :=
    r ^ 18 + r ^ 17 * p + r ^ 16 * p ^ 2 + r ^ 15 * p ^ 3 + r ^ 14 * p ^ 4
      + r ^ 13 * p ^ 5 + r ^ 12 * p ^ 6 + r ^ 11 * p ^ 7 + r ^ 10 * p ^ 8
      + r ^ 9 * p ^ 9 + r ^ 8 * p ^ 10 + r ^ 7 * p ^ 11 + r ^ 6 * p ^ 12
      + r ^ 5 * p ^ 13 + r ^ 4 * p ^ 14 + r ^ 3 * p ^ 15 + r ^ 2 * p ^ 16
      + r * p ^ 17 + p ^ 18
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos p
  have h14549535Dpos : 0 < 14549535 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 14549535) hDpos
  let q : Rat := r - p
  let s : Rat := 1 - r
  have hq0 : 0 <= q := by
    dsimp [q]
    grind [Rat.sub_eq_add_neg]
  have hs0 : 0 <= s := by
    dsimp [s]
    grind [Rat.sub_eq_add_neg]
  have hgap_cert := oddKernelNineUnitGap_eq_certificate p r
  have hgap_nonneg :
      0 <=
        14549535 - D * (14549535 - 4849845 * S3 + 2909907 * S5 - 2078505 * S7 + 1616615 * S9 - 1322685 * S11
          + 1119195 * S13 - 969969 * S15 + 855855 * S17 - 765765 * S19
          ) := by
    dsimp [D, S3, S5, S7, S9, S11, S13, S15, S17, S19]
    rw [hgap_cert]
    exact oddKernelNineUnitGapCertificate_nonneg hp0 hq0 hs0
  have hscalar :
      D * (14549535 - 4849845 * S3 + 2909907 * S5 - 2078505 * S7 + 1616615 * S9 - 1322685 * S11
          + 1119195 * S13 - 969969 * S15 + 855855 * S17 - 765765 * S19
          ) <= 14549535 := by
    grind [Rat.sub_eq_add_neg]
  have hupper_mul :
      ArctanGeometry.integralUpperStep p r * (14549535 * D) = L * 14549535 := by
    unfold ArctanGeometry.integralUpperStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 9 * (14549535 * D) =
        L * (D * (14549535 - 4849845 * S3 + 2909907 * S5 - 2078505 * S7 + 1616615 * S9 - 1322685 * S11
          + 1119195 * S13 - 969969 * S15 + 855855 * S17 - 765765 * S19
          )) := by
    have hkernel_formula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 9 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 + (r ^ 5 - p ^ 5) / 5 - (r ^ 7 - p ^ 7) / 7
          + (r ^ 9 - p ^ 9) / 9 - (r ^ 11 - p ^ 11) / 11 + (r ^ 13 - p ^ 13) / 13
          - (r ^ 15 - p ^ 15) / 15 + (r ^ 17 - p ^ 17) / 17 - (r ^ 19 - p ^ 19) / 19 := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcube : r ^ 3 - p ^ 3 = L * S3 := by
      dsimp [L, S3]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifth : r ^ 5 - p ^ 5 = L * S5 := by
      dsimp [L, S5]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hseventh : r ^ 7 - p ^ 7 = L * S7 := by
      dsimp [L, S7]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hninth : r ^ 9 - p ^ 9 = L * S9 := by
      dsimp [L, S9]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have heleventh : r ^ 11 - p ^ 11 = L * S11 := by
      dsimp [L, S11]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hthirteenth : r ^ 13 - p ^ 13 = L * S13 := by
      dsimp [L, S13]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hfifteenth : r ^ 15 - p ^ 15 = L * S15 := by
      dsimp [L, S15]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hseventeenth : r ^ 17 - p ^ 17 = L * S17 := by
      dsimp [L, S17]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hnineteenth : r ^ 19 - p ^ 19 = L * S19 := by
      dsimp [L, S19]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hkernel_formula, hcube, hfifth, hseventh, hninth,
      heleventh, hthirteenth, hfifteenth, hseventeenth, hnineteenth]
    dsimp [L, D, S3, S5, S7, S9, S11, S13, S15, S17, S19]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 14549535 * D)
  · rw [hkernel_mul, hupper_mul]
    exact Rat.mul_le_mul_of_nonneg_left hscalar hL0
  · exact h14549535Dpos

theorem oddKernelUnitCellBound_nine : OddKernelUnitCellBound 9 := by
  intro p r hp0 hpr hr1
  exact kernelPartialIntegralBetween_nine_le_integralUpperStep_on_unit hp0 hpr hr1

private def evenKernelTenUnitGapTerms : List SimplexCertTerm := [
  ⟨14549535, 22, 0, 0⟩,
  ⟨174594420, 21, 1, 0⟩,
  ⟨1324007685, 20, 2, 0⟩,
  ⟨7420262850, 19, 3, 0⟩,
  ⟨32343616305, 18, 4, 0⟩,
  ⟨112914091290, 17, 5, 0⟩,
  ⟨321462276135, 16, 6, 0⟩,
  ⟨755276061540, 15, 7, 0⟩,
  ⟨1476567642550, 14, 8, 0⟩,
  ⟨2415574585424, 13, 9, 0⟩,
  ⟨3318378993202, 12, 10, 0⟩,
  ⟨3833830219492, 11, 11, 0⟩,
  ⟨3723444224654, 10, 12, 0⟩,
  ⟨3032096055670, 9, 13, 0⟩,
  ⟨2059937981310, 8, 14, 0⟩,
  ⟨1158310438890, 7, 15, 0⟩,
  ⟨532776211275, 6, 16, 0⟩,
  ⟨197064198100, 5, 17, 0⟩,
  ⟨57171111305, 4, 18, 0⟩,
  ⟨12525437386, 3, 19, 0⟩,
  ⟨1948007413, 2, 20, 0⟩,
  ⟨191641118, 1, 21, 0⟩,
  ⟨8964811, 0, 22, 0⟩,
  ⟨145495350, 20, 1, 1⟩,
  ⟨3055402350, 19, 2, 1⟩,
  ⟨29681051400, 18, 3, 1⟩,
  ⟨181170809820, 17, 4, 1⟩,
  ⟨781756215240, 16, 5, 1⟩,
  ⟨2536721126940, 15, 6, 1⟩,
  ⟨6424143485760, 14, 7, 1⟩,
  ⟨13001904195280, 13, 8, 1⟩,
  ⟨21357577989748, 12, 9, 1⟩,
  ⟨28751669782836, 11, 10, 1⟩,
  ⟨31889423794228, 10, 11, 1⟩,
  ⟨29187224762080, 9, 12, 1⟩,
  ⟨22002129474930, 8, 13, 1⟩,
  ⟨13583623774710, 7, 14, 1⟩,
  ⟨6799972151280, 6, 15, 1⟩,
  ⟨2717286430320, 5, 16, 1⟩,
  ⟨846331294270, 4, 17, 1⟩,
  ⟨197991475990, 3, 18, 1⟩,
  ⟨32726479632, 2, 19, 1⟩,
  ⟨3407798284, 1, 20, 1⟩,
  ⟨168126772, 0, 21, 1⟩,
  ⟨1527701175, 19, 1, 2⟩,
  ⟨29390060700, 18, 2, 2⟩,
  ⟨268002434700, 17, 3, 2⟩,
  ⟨1538322335550, 16, 4, 2⟩,
  ⟨6229286413350, 15, 5, 2⟩,
  ⟨18904851005040, 14, 6, 2⟩,
  ⟨44584431091200, 13, 7, 2⟩,
  ⟨83601847969640, 12, 8, 2⟩,
  ⟨126467539904706, 11, 9, 2⟩,
  ⟨155672252755656, 10, 10, 2⟩,
  ⟨156539623666790, 9, 11, 2⟩,
  ⟨128569083340950, 8, 12, 2⟩,
  ⟨85876620626655, 7, 13, 2⟩,
  ⟨46232507454000, 6, 14, 2⟩,
  ⟨19765362191400, 5, 15, 2⟩,
  ⟨6556518375120, 4, 16, 2⟩,
  ⟨1627092997355, 3, 17, 2⟩,
  ⟨284290879740, 2, 18, 2⟩,
  ⟨31193499624, 1, 19, 2⟩,
  ⟨1617043394, 0, 20, 2⟩,
  ⟨9602693100, 18, 1, 3⟩,
  ⟨175079404500, 17, 2, 3⟩,
  ⟨1506555850800, 16, 3, 3⟩,
  ⟨8128379018760, 15, 4, 3⟩,
  ⟨30810483303600, 14, 5, 3⟩,
  ⟨87117571741200, 13, 6, 3⟩,
  ⟨190400957226480, 12, 7, 3⟩,
  ⟨328833277492720, 11, 8, 3⟩,
  ⟨454860633178952, 10, 9, 3⟩,
  ⟨507611985036520, 9, 10, 3⟩,
  ⟨458018883869820, 8, 11, 3⟩,
  ⟨333287761997820, 7, 12, 3⟩,
  ⟨194099639218800, 6, 13, 3⟩,
  ⟨89227570946640, 5, 14, 3⟩,
  ⟨31661038945200, 4, 15, 3⟩,
  ⟨8366626116240, 3, 16, 3⟩,
  ⟨1550428100620, 2, 17, 3⟩,
  ⟨179789427860, 1, 18, 3⟩,
  ⟨9818794888, 0, 19, 3⟩,
  ⟨42848380575, 17, 1, 4⟩,
  ⟨736836950850, 16, 2, 4⟩,
  ⟨5958083080950, 15, 3, 4⟩,
  ⟨30084248113920, 14, 4, 4⟩,
  ⟨106225204465380, 13, 5, 4⟩,
  ⟨278299819597800, 12, 6, 4⟩,
  ⟨560111353761960, 11, 7, 4⟩,
  ⟨884386106744140, 10, 8, 4⟩,
  ⟨1108877866035940, 9, 9, 4⟩,
  ⟨1110169486749960, 8, 10, 4⟩,
  ⟨887306645339205, 7, 11, 4⟩,
  ⟨562835671641600, 6, 12, 4⟩,
  ⟨279827134820100, 5, 13, 4⟩,
  ⟨106740801865320, 4, 14, 4⟩,
  ⟨30165303742980, 3, 15, 4⟩,
  ⟨5950955835720, 2, 16, 4⟩,
  ⟨731709812155, 1, 17, 4⟩,
  ⟨42221174170, 0, 18, 4⟩,
  ⟨143924000220, 16, 1, 5⟩,
  ⟨2325345482460, 15, 2, 5⟩,
  ⟨17594461684800, 14, 3, 5⟩,
  ⟨82744206553008, 13, 4, 5⟩,
  ⟨270666334282344, 12, 5, 5⟩,
  ⟨652893482385144, 11, 6, 5⟩,
  ⟨1201111964760708, 10, 7, 5⟩,
  ⟨1718711570215640, 9, 8, 5⟩,
  ⟨1932873861268350, 8, 9, 5⟩,
  ⟨1713731108896170, 7, 10, 5⟩,
  ⟨1193696787017280, 6, 11, 5⟩,
  ⟨646241088724560, 5, 12, 5⟩,
  ⟨266534977960440, 4, 13, 5⟩,
  ⟨80951869291944, 3, 14, 5⟩,
  ⟨17073981637272, 2, 15, 5⟩,
  ⟨2234279712672, 1, 16, 5⟩,
  ⟨136658650184, 0, 17, 5⟩,
  ⟨377444036970, 15, 1, 6⟩,
  ⟨5705590450560, 14, 2, 6⟩,
  ⟨40202033551680, 13, 3, 6⟩,
  ⟨175122028817736, 12, 4, 6⟩,
  ⟨527322548845092, 11, 5, 6⟩,
  ⟨1162447537707456, 10, 6, 6⟩,
  ⟨1937619958384110, 9, 7, 6⟩,
  ⟨2486232484846110, 8, 8, 6⟩,
  ⟨2475504225168975, 7, 9, 6⟩,
  ⟨1912276854371520, 6, 10, 6⟩,
  ⟨1136500050067200, 5, 11, 6⟩,
  ⟨510258477035160, 4, 12, 6⟩,
  ⟨167511697815420, 3, 13, 6⟩,
  ⟨37958256872928, 2, 14, 6⟩,
  ⟨5308722085716, 1, 15, 6⟩,
  ⟨345450709548, 0, 16, 6⟩,
  ⟨791261911440, 14, 1, 7⟩,
  ⟨11136408082800, 13, 2, 7⟩,
  ⟨72666740786640, 12, 3, 7⟩,
  ⟨291321311993712, 11, 4, 7⟩,
  ⟨801482172162672, 10, 5, 7⟩,
  ⟨1600419839612880, 9, 6, 7⟩,
  ⟨2391461423980200, 8, 7, 7⟩,
  ⟨2716002254239560, 7, 8, 7⟩,
  ⟨2355396286042800, 6, 9, 7⟩,
  ⟨1551938795643600, 5, 10, 7⟩,
  ⟨764649087143760, 4, 11, 7⟩,
  ⟨273161536205040, 3, 12, 7⟩,
  ⟨66880078524720, 2, 13, 7⟩,
  ⟨10045223756496, 1, 14, 7⟩,
  ⟨698318981856, 0, 15, 7⟩,
  ⟨1346268473550, 13, 1, 8⟩,
  ⟨17542878733380, 12, 2, 8⟩,
  ⟨105324112964070, 11, 3, 8⟩,
  ⟨385685859683124, 10, 4, 8⟩,
  ⟨960886171485240, 9, 5, 8⟩,
  ⟨1719530034676740, 8, 6, 8⟩,
  ⟨2273454184130415, 7, 7, 8⟩,
  ⟨2248061456440800, 6, 8, 8⟩,
  ⟨1662260134224690, 5, 9, 8⟩,
  ⟨907616156510700, 4, 10, 8⟩,
  ⟨355664338053570, 3, 11, 8⟩,
  ⟨94716061443360, 2, 12, 8⟩,
  ⟨15363670844430, 1, 13, 8⟩,
  ⟨1146431717892, 0, 14, 8⟩,
  ⟨1876715420580, 12, 1, 9⟩,
  ⟨22494764472180, 11, 2, 9⟩,
  ⟨123323003223420, 10, 3, 9⟩,
  ⟨408809885724240, 9, 4, 9⟩,
  ⟨912431011201710, 8, 5, 9⟩,
  ⟨1444159118228970, 7, 6, 9⟩,
  ⟨1661744838193440, 6, 7, 9⟩,
  ⟨1400387674045360, 5, 8, 9⟩,
  ⟨857677363683140, 4, 9, 9⟩,
  ⟨372268776776260, 3, 10, 9⟩,
  ⟨108688908677440, 2, 11, 9⟩,
  ⟨19165110464360, 1, 12, 9⟩,
  ⟨1543489311640, 0, 13, 9⟩,
  ⟨2154349647450, 11, 1, 10⟩,
  ⟨23571139071480, 10, 2, 10⟩,
  ⟨116935476067410, 9, 3, 10⟩,
  ⟨347120961148962, 8, 4, 10⟩,
  ⟨684917060328501, 7, 5, 10⟩,
  ⟨942998880039216, 6, 6, 10⟩,
  ⟨924254019600912, 5, 7, 10⟩,
  ⟨644780542686280, 4, 8, 10⟩,
  ⟨313725950179642, 3, 9, 10⟩,
  ⟨101388054066936, 2, 10, 10⟩,
  ⟨19586122899616, 1, 11, 10⟩,
  ⟨1713402829852, 0, 12, 10⟩,
  ⟨2039146429320, 10, 1, 11⟩,
  ⟨20179894654920, 9, 2, 11⟩,
  ⟨89603776882620, 8, 3, 11⟩,
  ⟨235019604944124, 7, 4, 11⟩,
  ⟨403147004948688, 6, 5, 11⟩,
  ⟨472486814143344, 5, 6, 11⟩,
  ⟨383093912401200, 4, 7, 11⟩,
  ⟨212159094907760, 3, 8, 11⟩,
  ⟨76797621484584, 2, 9, 11⟩,
  ⟨16406943804888, 1, 10, 11⟩,
  ⟨1570890308624, 0, 11, 11⟩,
  ⟨1587878051760, 9, 1, 12⟩,
  ⟨14056344562260, 8, 2, 12⟩,
  ⟨55111286405175, 7, 3, 12⟩,
  ⟨125577145221528, 6, 4, 12⟩,
  ⟨183224439826428, 5, 5, 12⟩,
  ⟨177489505873680, 4, 6, 12⟩,
  ⟨114133924304400, 3, 7, 12⟩,
  ⟨46975010222140, 2, 8, 12⟩,
  ⟨11227806968378, 1, 9, 12⟩,
  ⟨1187328353848, 0, 10, 12⟩,
  ⟨1011163583430, 8, 1, 13⟩,
  ⟨7897555495830, 7, 2, 13⟩,
  ⟨26876405435880, 6, 3, 13⟩,
  ⟨52039286915616, 5, 4, 13⟩,
  ⟨62689794847680, 4, 5, 13⟩,
  ⟨48104758982280, 3, 6, 13⟩,
  ⟨22958176861620, 2, 7, 13⟩,
  ⟨6229697033560, 1, 8, 13⟩,
  ⟨735757698676, 0, 9, 13⟩,
  ⟨521149794165, 7, 1, 14⟩,
  ⟨3529096410840, 6, 2, 14⟩,
  ⟨10192764041460, 5, 3, 14⟩,
  ⟨16271792557020, 4, 4, 14⟩,
  ⟨15502839932580, 3, 5, 14⟩,
  ⟨8812911084120, 2, 6, 14⟩,
  ⟨2767167747630, 1, 7, 14⟩,
  ⟨370123080470, 0, 8, 14⟩,
  ⟨213936362640, 6, 1, 15⟩,
  ⟨1227515168880, 5, 2, 15⟩,
  ⟨2917589154480, 4, 3, 15⟩,
  ⟨3675654846864, 3, 4, 15⟩,
  ⟨2587768655472, 2, 5, 15⟩,
  ⟨964938463632, 1, 6, 15⟩,
  ⟨148814306784, 0, 7, 15⟩,
  ⟨68280967755, 5, 1, 16⟩,
  ⟨321573822570, 4, 2, 16⟩,
  ⟨601317732015, 3, 3, 16⟩,
  ⟨557724415248, 2, 4, 16⟩,
  ⟨256400635491, 1, 5, 16⟩,
  ⟨46699018938, 0, 6, 16⟩,
  ⟨16324578270, 4, 1, 17⟩,
  ⟨60205975830, 3, 2, 17⟩,
  ⟨82408566240, 2, 3, 17⟩,
  ⟨49549896396, 1, 4, 17⟩,
  ⟨11022727716, 0, 5, 17⟩,
  ⟨2749862115, 3, 1, 18⟩,
  ⟨7352365020, 2, 2, 18⟩,
  ⟨6440594160, 1, 3, 18⟩,
  ⟨1841001162, 0, 4, 18⟩,
  ⟨290990700, 2, 1, 19⟩,
  ⟨484984500, 1, 2, 19⟩,
  ⟨193993800, 0, 3, 19⟩,
  ⟨14549535, 1, 1, 20⟩,
  ⟨9699690, 0, 2, 20⟩]

private def evenKernelTenUnitGapCertificate (p q s : Rat) : Rat :=
  simplexCertEval evenKernelTenUnitGapTerms p q s

private theorem evenKernelTenUnitGapTerms_nonneg :
    simplexCertCoeffsNonneg evenKernelTenUnitGapTerms := by
  native_decide

private theorem evenKernelTenUnitGapCertificate_nonneg
    {p q s : Rat} (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s) :
    0 <= evenKernelTenUnitGapCertificate p q s :=
  simplexCertEval_nonneg hp hq hs evenKernelTenUnitGapTerms_nonneg

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem evenKernelTenUnitGap_eq_certificate (p r : Rat) :
    let q : Rat := r - p
    let s : Rat := 1 - r
    (1 + r * r) *
      (14549535 - 4849845 * (r ^ 2 + r * p + p ^ 2)
        + 2909907 * (r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4)
        - 2078505 * (r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 + r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6)
        + 1616615 * (r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 + r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 + r * p ^ 7 + p ^ 8)
        - 1322685 * (r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 + r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 + r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10)
        + 1119195 * (r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 + r ^ 8 * p ^ 4 + r ^ 7 * p ^ 5 + r ^ 6 * p ^ 6 + r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8 + r ^ 3 * p ^ 9 + r ^ 2 * p ^ 10 + r * p ^ 11 + p ^ 12)
        - 969969 * (r ^ 14 + r ^ 13 * p + r ^ 12 * p ^ 2 + r ^ 11 * p ^ 3 + r ^ 10 * p ^ 4 + r ^ 9 * p ^ 5 + r ^ 8 * p ^ 6 + r ^ 7 * p ^ 7 + r ^ 6 * p ^ 8 + r ^ 5 * p ^ 9 + r ^ 4 * p ^ 10 + r ^ 3 * p ^ 11 + r ^ 2 * p ^ 12 + r * p ^ 13 + p ^ 14)
        + 855855 * (r ^ 16 + r ^ 15 * p + r ^ 14 * p ^ 2 + r ^ 13 * p ^ 3 + r ^ 12 * p ^ 4 + r ^ 11 * p ^ 5 + r ^ 10 * p ^ 6 + r ^ 9 * p ^ 7 + r ^ 8 * p ^ 8 + r ^ 7 * p ^ 9 + r ^ 6 * p ^ 10 + r ^ 5 * p ^ 11 + r ^ 4 * p ^ 12 + r ^ 3 * p ^ 13 + r ^ 2 * p ^ 14 + r * p ^ 15 + p ^ 16)
        - 765765 * (r ^ 18 + r ^ 17 * p + r ^ 16 * p ^ 2 + r ^ 15 * p ^ 3 + r ^ 14 * p ^ 4 + r ^ 13 * p ^ 5 + r ^ 12 * p ^ 6 + r ^ 11 * p ^ 7 + r ^ 10 * p ^ 8 + r ^ 9 * p ^ 9 + r ^ 8 * p ^ 10 + r ^ 7 * p ^ 11 + r ^ 6 * p ^ 12 + r ^ 5 * p ^ 13 + r ^ 4 * p ^ 14 + r ^ 3 * p ^ 15 + r ^ 2 * p ^ 16 + r * p ^ 17 + p ^ 18)
        + 692835 * (r ^ 20 + r ^ 19 * p + r ^ 18 * p ^ 2 + r ^ 17 * p ^ 3 + r ^ 16 * p ^ 4 + r ^ 15 * p ^ 5 + r ^ 14 * p ^ 6 + r ^ 13 * p ^ 7 + r ^ 12 * p ^ 8 + r ^ 11 * p ^ 9 + r ^ 10 * p ^ 10 + r ^ 9 * p ^ 11 + r ^ 8 * p ^ 12 + r ^ 7 * p ^ 13 + r ^ 6 * p ^ 14 + r ^ 5 * p ^ 15 + r ^ 4 * p ^ 16 + r ^ 3 * p ^ 17 + r ^ 2 * p ^ 18 + r * p ^ 19 + p ^ 20)
          ) - 14549535 =
      evenKernelTenUnitGapCertificate p q s := by
  intro q s
  unfold evenKernelTenUnitGapCertificate evenKernelTenUnitGapTerms
  simp [simplexCertEval, simplexCertTermEval]
  dsimp [q, s]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem kernelPartialIntegralBetween_ten_lowerStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    ArctanGeometry.integralLowerStep p r <=
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 10 := by
  let L : Rat := r - p
  let D : Rat := 1 + r * r
  let S3 : Rat :=
    r ^ 2 + r * p + p ^ 2
  let S5 : Rat :=
    r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4
  let S7 : Rat :=
    r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 + r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6
  let S9 : Rat :=
    r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 + r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5
    + r ^ 2 * p ^ 6 + r * p ^ 7 + p ^ 8
  let S11 : Rat :=
    r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 + r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5
    + r ^ 4 * p ^ 6 + r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10
  let S13 : Rat :=
    r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 + r ^ 8 * p ^ 4 + r ^ 7 * p ^ 5
    + r ^ 6 * p ^ 6 + r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8 + r ^ 3 * p ^ 9 + r ^ 2 * p ^ 10
    + r * p ^ 11 + p ^ 12
  let S15 : Rat :=
    r ^ 14 + r ^ 13 * p + r ^ 12 * p ^ 2 + r ^ 11 * p ^ 3 + r ^ 10 * p ^ 4 + r ^ 9 * p ^ 5
    + r ^ 8 * p ^ 6 + r ^ 7 * p ^ 7 + r ^ 6 * p ^ 8 + r ^ 5 * p ^ 9 + r ^ 4 * p ^ 10
    + r ^ 3 * p ^ 11 + r ^ 2 * p ^ 12 + r * p ^ 13 + p ^ 14
  let S17 : Rat :=
    r ^ 16 + r ^ 15 * p + r ^ 14 * p ^ 2 + r ^ 13 * p ^ 3 + r ^ 12 * p ^ 4 + r ^ 11 * p ^ 5
    + r ^ 10 * p ^ 6 + r ^ 9 * p ^ 7 + r ^ 8 * p ^ 8 + r ^ 7 * p ^ 9 + r ^ 6 * p ^ 10
    + r ^ 5 * p ^ 11 + r ^ 4 * p ^ 12 + r ^ 3 * p ^ 13 + r ^ 2 * p ^ 14 + r * p ^ 15 + p ^ 16
  let S19 : Rat :=
    r ^ 18 + r ^ 17 * p + r ^ 16 * p ^ 2 + r ^ 15 * p ^ 3 + r ^ 14 * p ^ 4 + r ^ 13 * p ^ 5
    + r ^ 12 * p ^ 6 + r ^ 11 * p ^ 7 + r ^ 10 * p ^ 8 + r ^ 9 * p ^ 9 + r ^ 8 * p ^ 10
    + r ^ 7 * p ^ 11 + r ^ 6 * p ^ 12 + r ^ 5 * p ^ 13 + r ^ 4 * p ^ 14 + r ^ 3 * p ^ 15
    + r ^ 2 * p ^ 16 + r * p ^ 17 + p ^ 18
  let S21 : Rat :=
    r ^ 20 + r ^ 19 * p + r ^ 18 * p ^ 2 + r ^ 17 * p ^ 3 + r ^ 16 * p ^ 4 + r ^ 15 * p ^ 5
    + r ^ 14 * p ^ 6 + r ^ 13 * p ^ 7 + r ^ 12 * p ^ 8 + r ^ 11 * p ^ 9 + r ^ 10 * p ^ 10
    + r ^ 9 * p ^ 11 + r ^ 8 * p ^ 12 + r ^ 7 * p ^ 13 + r ^ 6 * p ^ 14 + r ^ 5 * p ^ 15
    + r ^ 4 * p ^ 16 + r ^ 3 * p ^ 17 + r ^ 2 * p ^ 18 + r * p ^ 19 + p ^ 20
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos r
  have h14549535Dpos : 0 < 14549535 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 14549535) hDpos
  let q : Rat := r - p
  let s : Rat := 1 - r
  have hq0 : 0 <= q := by
    dsimp [q]
    grind [Rat.sub_eq_add_neg]
  have hs0 : 0 <= s := by
    dsimp [s]
    grind [Rat.sub_eq_add_neg]
  have hgap_cert := evenKernelTenUnitGap_eq_certificate p r
  have hgap_nonneg :
      0 <=
        D * (14549535 - 4849845 * S3 + 2909907 * S5 - 2078505 * S7 + 1616615 * S9 - 1322685 * S11 + 1119195 * S13 - 969969 * S15 + 855855 * S17 - 765765 * S19 + 692835 * S21)
        - 14549535 := by
    dsimp [D, S3, S5, S7, S9, S11, S13, S15, S17, S19, S21]
    rw [hgap_cert]
    exact evenKernelTenUnitGapCertificate_nonneg hp0 hq0 hs0
  have hscalar :
      14549535 <=
        D * (14549535 - 4849845 * S3 + 2909907 * S5 - 2078505 * S7 + 1616615 * S9 - 1322685 * S11 + 1119195 * S13 - 969969 * S15 + 855855 * S17 - 765765 * S19 + 692835 * S21
          ) := by
    grind [Rat.sub_eq_add_neg]
  have hlower_mul :
      ArctanGeometry.integralLowerStep p r * (14549535 * D) = L * 14549535 := by
    unfold ArctanGeometry.integralLowerStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 10 * (14549535 * D) =
        L * (D * (14549535 - 4849845 * S3 + 2909907 * S5 - 2078505 * S7 + 1616615 * S9 - 1322685 * S11 + 1119195 * S13 - 969969 * S15 + 855855 * S17 - 765765 * S19 + 692835 * S21
          )) := by
    have hkernel_formula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 10 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 + (r ^ 5 - p ^ 5) / 5 - (r ^ 7 - p ^ 7) / 7
          + (r ^ 9 - p ^ 9) / 9 - (r ^ 11 - p ^ 11) / 11 + (r ^ 13 - p ^ 13) / 13
          - (r ^ 15 - p ^ 15) / 15 + (r ^ 17 - p ^ 17) / 17 - (r ^ 19 - p ^ 19) / 19
          + (r ^ 21 - p ^ 21) / 21
          := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hS3 : r ^ 3 - p ^ 3 = L * S3 := by
      dsimp [L, S3]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS5 : r ^ 5 - p ^ 5 = L * S5 := by
      dsimp [L, S5]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS7 : r ^ 7 - p ^ 7 = L * S7 := by
      dsimp [L, S7]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS9 : r ^ 9 - p ^ 9 = L * S9 := by
      dsimp [L, S9]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS11 : r ^ 11 - p ^ 11 = L * S11 := by
      dsimp [L, S11]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS13 : r ^ 13 - p ^ 13 = L * S13 := by
      dsimp [L, S13]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS15 : r ^ 15 - p ^ 15 = L * S15 := by
      dsimp [L, S15]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS17 : r ^ 17 - p ^ 17 = L * S17 := by
      dsimp [L, S17]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS19 : r ^ 19 - p ^ 19 = L * S19 := by
      dsimp [L, S19]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS21 : r ^ 21 - p ^ 21 = L * S21 := by
      dsimp [L, S21]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hkernel_formula, hS3, hS5, hS7, hS9, hS11, hS13, hS15, hS17, hS19, hS21]
    dsimp [D, S3, S5, S7, S9, S11, S13, S15, S17, S19, S21]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 14549535 * D)
  · rw [hlower_mul, hkernel_mul]
    exact Rat.mul_le_mul_of_nonneg_left hscalar hL0
  · exact h14549535Dpos

theorem evenKernelCellBound_ten : EvenKernelCellBound 10 := by
  intro p r hp0 hpr hr1
  exact kernelPartialIntegralBetween_ten_lowerStep hp0 hpr hr1

private def oddKernelElevenUnitGapTerms : List SimplexCertTerm := [
  ⟨334639305, 24, 0, 0⟩,
  ⟨4015671660, 23, 1, 0⟩,
  ⟨32125373280, 22, 2, 0⟩,
  ⟨190744403850, 21, 3, 0⟩,
  ⟨886794158250, 20, 4, 0⟩,
  ⟨3324753041610, 19, 5, 0⟩,
  ⟨10234608504120, 18, 6, 0⟩,
  ⟨26181398398155, 17, 7, 0⟩,
  ⟨56139796267555, 16, 8, 0⟩,
  ⟨101542593760608, 15, 9, 0⟩,
  ⟨155623831668032, 14, 10, 0⟩,
  ⟨202675442987472, 13, 11, 0⟩,
  ⟨224590762747904, 12, 12, 0⟩,
  ⟨211702162967450, 11, 13, 0⟩,
  ⟨169409254400144, 10, 14, 0⟩,
  ⟨114638190420215, 9, 15, 0⟩,
  ⟨65195396400255, 8, 16, 0⟩,
  ⟨30880444594780, 7, 17, 0⟩,
  ⟨12027832924800, 6, 18, 0⟩,
  ⟨3783607368002, 5, 19, 0⟩,
  ⟨936663427458, 4, 20, 0⟩,
  ⟨175518067958, 3, 21, 0⟩,
  ⟨23376292856, 2, 22, 0⟩,
  ⟨1969346525, 1, 23, 0⟩,
  ⟨78773861, 0, 24, 0⟩,
  ⟨4015671660, 22, 1, 1⟩,
  ⟨85667662080, 21, 2, 1⟩,
  ⟨878093536320, 20, 3, 1⟩,
  ⟨5725009229940, 19, 4, 1⟩,
  ⟨26601147633060, 18, 5, 1⟩,
  ⟨93631185167520, 17, 6, 1⟩,
  ⟨259140662120340, 16, 7, 1⟩,
  ⟨577883707761360, 15, 8, 1⟩,
  ⟨1055548803581272, 14, 9, 1⟩,
  ⟨1596797422509744, 13, 10, 1⟩,
  ⟨2014763031271172, 12, 11, 1⟩,
  ⟨2128522388204380, 11, 12, 1⟩,
  ⟨1884825471235080, 10, 13, 1⟩,
  ⟨1396668816878720, 9, 14, 1⟩,
  ⟨862204234516680, 8, 15, 1⟩,
  ⟨440028000688320, 7, 16, 1⟩,
  ⟨183487713675420, 6, 17, 1⟩,
  ⟨61448638340320, 5, 18, 1⟩,
  ⟨16114054721688, 4, 19, 1⟩,
  ⟨3184087541756, 3, 20, 1⟩,
  ⟨445294287508, 2, 21, 1⟩,
  ⟨39232973280, 1, 22, 1⟩,
  ⟨1634707220, 0, 23, 1⟩,
  ⟨42164552430, 21, 1, 2⟩,
  ⟨870731471610, 20, 2, 2⟩,
  ⟨8550034242750, 19, 3, 2⟩,
  ⟨53099226360180, 18, 4, 2⟩,
  ⟨233977348034430, 17, 5, 2⟩,
  ⟨777798790218450, 16, 6, 2⟩,
  ⟨2024581180822200, 15, 7, 2⟩,
  ⟨4227123841500560, 14, 8, 2⟩,
  ⟨7193484939733092, 13, 9, 2⟩,
  ⟨10082023356886572, 12, 10, 2⟩,
  ⟨11710808055485630, 11, 11, 2⟩,
  ⟨11305256105007480, 10, 12, 2⟩,
  ⟨9067703914985100, 9, 13, 2⟩,
  ⟨6022117062461940, 8, 14, 2⟩,
  ⟨3288860448580080, 7, 15, 2⟩,
  ⟨1460721316990320, 6, 16, 2⟩,
  ⟨518870818043270, 5, 17, 2⟩,
  ⟨143782806466530, 4, 18, 2⟩,
  ⟨29919206485938, 3, 19, 2⟩,
  ⟨4392262533428, 2, 20, 2⟩,
  ⟨404998968630, 1, 21, 2⟩,
  ⟨17608650810, 0, 22, 2⟩,
  ⟨294482588400, 20, 1, 3⟩,
  ⟨5778105333000, 19, 2, 3⟩,
  ⟨53783229099600, 18, 3, 3⟩,
  ⟨315740661796560, 17, 4, 3⟩,
  ⟨1310955277752120, 16, 5, 3⟩,
  ⟨4091444707109760, 15, 6, 3⟩,
  ⟨9957541437523680, 14, 7, 3⟩,
  ⟨19347771984581040, 13, 8, 3⟩,
  ⟨30475623934619864, 12, 9, 3⟩,
  ⟨39289143447390200, 11, 10, 3⟩,
  ⟨41671419621351520, 10, 11, 3⟩,
  ⟨36414319748144800, 9, 12, 3⟩,
  ⟨26161031686191600, 8, 13, 3⟩,
  ⟨15361524989511360, 7, 14, 3⟩,
  ⟨7296841964966400, 6, 15, 3⟩,
  ⟨2759126996952480, 5, 16, 3⟩,
  ⟨810483628933440, 4, 17, 3⟩,
  ⟨178098003341720, 3, 18, 3⟩,
  ⟨27513222047696, 2, 19, 3⟩,
  ⟨2660785718800, 1, 20, 3⟩,
  ⟨120944805400, 0, 21, 3⟩,
  ⟨1462373762850, 19, 1, 4⟩,
  ⟨27206175496500, 18, 2, 4⟩,
  ⟨239409882511800, 17, 3, 4⟩,
  ⟨1324387253269080, 16, 4, 4⟩,
  ⟨5162552840324880, 15, 5, 4⟩,
  ⟨15064071196334160, 14, 6, 4⟩,
  ⟨34115817236040540, 13, 7, 4⟩,
  ⟨61350671172250460, 12, 8, 4⟩,
  ⟨88878892455603250, 11, 9, 4⟩,
  ⟨104611474450643160, 10, 10, 4⟩,
  ⟨100416819545442400, 9, 11, 4⟩,
  ⟨78580020820408800, 8, 12, 4⟩,
  ⟨49901170750358400, 7, 13, 4⟩,
  ⟨25477770693790800, 6, 14, 4⟩,
  ⟨10299521596250040, 5, 15, 4⟩,
  ⟨3219145887961080, 4, 16, 4⟩,
  ⟨749448847525070, 3, 17, 4⟩,
  ⟨122179394994580, 2, 18, 4⟩,
  ⟨12423091434600, 1, 19, 4⟩,
  ⟨591575782600, 0, 20, 4⟩,
  ⟨5502139452810, 18, 1, 5⟩,
  ⟨96766086176760, 17, 2, 5⟩,
  ⟨802319819931630, 16, 3, 5⟩,
  ⟨4166458524564336, 15, 4, 5⟩,
  ⟨15182879571964104, 14, 5, 5⟩,
  ⟨41220381284226144, 13, 6, 5⟩,
  ⟨86386273751765988, 12, 7, 5⟩,
  ⟨142853847939502700, 11, 8, 5⟩,
  ⟨188906888628550092, 10, 9, 5⟩,
  ⟨201184023993192240, 9, 10, 5⟩,
  ⟨172894510858529460, 8, 11, 5⟩,
  ⟨119556558961796880, 7, 12, 5⟩,
  ⟨65991963414623400, 6, 13, 5⟩,
  ⟨28662599942251968, 5, 14, 5⟩,
  ⟨9572804480009232, 4, 15, 5⟩,
  ⟨2369859178706712, 3, 16, 5⟩,
  ⟨409003972743674, 2, 17, 5⟩,
  ⟨43842870687000, 1, 18, 5⟩,
  ⟨2192143534350, 0, 19, 5⟩,
  ⟨16287229613655, 17, 1, 6⟩,
  ⟨269860162977405, 16, 2, 6⟩,
  ⟨2100182000236320, 15, 3, 6⟩,
  ⟨10194273134749704, 14, 4, 6⟩,
  ⟨34558849870653108, 13, 5, 6⟩,
  ⟨86808999224031084, 12, 6, 6⟩,
  ⟨167263156238508330, 11, 7, 6⟩,
  ⟨252424876335271640, 10, 8, 6⟩,
  ⟨301958872271946890, 9, 9, 6⟩,
  ⟨287827650674674110, 8, 10, 6⟩,
  ⟨218506783781526240, 7, 11, 6⟩,
  ⟨131283088678129080, 6, 12, 6⟩,
  ⟨61616929400735940, 5, 13, 6⟩,
  ⟨22097811687773052, 4, 14, 6⟩,
  ⟨5841594879823164, 3, 15, 6⟩,
  ⟨1071117967068072, 2, 16, 6⟩,
  ⟨121412315574935, 1, 17, 6⟩,
  ⟨6390121872365, 0, 18, 6⟩,
  ⟨38871701668800, 16, 1, 7⟩,
  ⟨604456745692800, 15, 2, 7⟩,
  ⟨4396457278973760, 14, 3, 7⟩,
  ⟨19849533549509664, 13, 4, 7⟩,
  ⟨62247856966639344, 12, 5, 7⟩,
  ⟨143729480209046160, 11, 6, 7⟩,
  ⟨252677705530124160, 10, 7, 7⟩,
  ⟨344861360811968000, 9, 8, 7⟩,
  ⟨369119385533321280, 8, 9, 7⟩,
  ⟨310699889872257600, 7, 10, 7⟩,
  ⟨204852397166376960, 6, 11, 7⟩,
  ⟨104601268123450560, 5, 12, 7⟩,
  ⟨40511817178921440, 4, 13, 7⟩,
  ⟨11490819198035232, 3, 14, 7⟩,
  ⟨2247620934125952, 2, 15, 7⟩,
  ⟨270321649614720, 1, 16, 7⟩,
  ⟨15017869423040, 0, 17, 7⟩,
  ⟨76043435668200, 15, 1, 8⟩,
  ⟨1104962030051880, 14, 2, 8⟩,
  ⟨7474111319214540, 13, 3, 8⟩,
  ⟨31210096498088508, 12, 4, 8⟩,
  ⟨89947881057824790, 11, 5, 8⟩,
  ⟨189448023803112360, 10, 6, 8⟩,
  ⟨301115072497239000, 9, 7, 8⟩,
  ⟨367596956827128600, 8, 8, 8⟩,
  ⟨347306706831427200, 7, 9, 8⟩,
  ⟨253776557365170840, 6, 10, 8⟩,
  ⟨142120627492203360, 5, 11, 8⟩,
  ⟨59841539901047520, 4, 12, 8⟩,
  ⟨18314075795097060, 3, 13, 8⟩,
  ⟨3839281902590904, 2, 14, 8⟩,
  ⟨491831139385080, 1, 15, 8⟩,
  ⟨28931243493240, 0, 16, 8⟩,
  ⟨123291828419760, 14, 1, 9⟩,
  ⟨1665770209543440, 13, 2, 9⟩,
  ⟨10418989853131860, 12, 3, 9⟩,
  ⟨39974279728443060, 11, 4, 9⟩,
  ⟨105059863455827280, 10, 5, 9⟩,
  ⟨199996083016329600, 9, 6, 9⟩,
  ⟨284228003522892000, 8, 7, 9⟩,
  ⟨306152124719755600, 7, 8, 9⟩,
  ⟨250967308587755760, 6, 9, 9⟩,
  ⟨155663290387885280, 5, 10, 9⟩,
  ⟨71828990938144440, 4, 11, 9⟩,
  ⟨23875260584057960, 3, 12, 9⟩,
  ⟨5393339966038640, 2, 13, 9⟩,
  ⟨739178139941120, 1, 14, 9⟩,
  ⟨46198633746320, 0, 15, 9⟩,
  ⟨166843126129680, 13, 1, 10⟩,
  ⟨2083964040958800, 12, 2, 10⟩,
  ⟨11973171016937130, 11, 3, 10⟩,
  ⟨41879040316665552, 10, 4, 10⟩,
  ⟨99446575744171656, 9, 5, 10⟩,
  ⟨169200988987028856, 8, 6, 10⟩,
  ⟨212066278977287592, 7, 7, 10⟩,
  ⟨198075114195678720, 6, 8, 10⟩,
  ⟨137731229645025016, 5, 9, 10⟩,
  ⟨70327130808150216, 4, 10, 10⟩,
  ⟨25588339943121956, 3, 11, 10⟩,
  ⟨6268440936888592, 2, 12, 10⟩,
  ⟨923829467282040, 1, 13, 10⟩,
  ⟨61588631152136, 0, 14, 10⟩,
  ⟨189164906330400, 12, 1, 11⟩,
  ⟨2169752173188600, 11, 2, 11⟩,
  ⟨11361143614700880, 10, 3, 11⟩,
  ⟨35890842895283376, 9, 4, 11⟩,
  ⟨76140005789599752, 8, 5, 11⟩,
  ⟨114187670803267776, 7, 6, 11⟩,
  ⟨124021224311624640, 6, 7, 11⟩,
  ⟨98181622335196400, 5, 8, 11⟩,
  ⟨56145465087127416, 4, 9, 11⟩,
  ⟨22575572629074192, 3, 10, 11⟩,
  ⟨6043077347989136, 2, 11, 11⟩,
  ⟨963437161466640, 1, 12, 11⟩,
  ⟨68816940104760, 0, 13, 11⟩,
  ⟨179871972830550, 11, 1, 12⟩,
  ⟨1879635066068760, 10, 2, 12⟩,
  ⟨8885477128267740, 9, 3, 12⟩,
  ⟨25064915584584876, 8, 4, 12⟩,
  ⟨46841741923712736, 7, 5, 12⟩,
  ⟨60832269526588560, 6, 6, 12⟩,
  ⟨55949298009504900, 5, 7, 12⟩,
  ⟨36383817724434180, 4, 8, 12⟩,
  ⟨16359245806579676, 3, 9, 12⟩,
  ⟨4829269199035736, 2, 10, 12⟩,
  ⟨838794943064260, 1, 11, 12⟩,
  ⟨64522687928020, 0, 12, 12⟩,
  ⟨143199520674210, 10, 1, 13⟩,
  ⟨1350362402308920, 9, 2, 13⟩,
  ⟨5697005051247510, 8, 3, 13⟩,
  ⟨14147660477983032, 7, 4, 13⟩,
  ⟨22876715237315940, 6, 5, 13⟩,
  ⟨25132339871839200, 5, 6, 13⟩,
  ⟨18962459365089240, 4, 7, 13⟩,
  ⟨9678411059337020, 3, 8, 13⟩,
  ⟨3186944842723642, 2, 9, 13⟩,
  ⟨608236587908040, 1, 10, 13⟩,
  ⟨50686382325670, 0, 11, 13⟩,
  ⟨95021165294055, 9, 1, 14⟩,
  ⟨799204216455645, 8, 2, 14⟩,
  ⟨2966114298026880, 7, 3, 14⟩,
  ⟨6367518034097220, 6, 4, 14⟩,
  ⟨8699782877715930, 5, 5, 14⟩,
  ⟨7828501131606870, 4, 6, 14⟩,
  ⟨4626183879204030, 3, 7, 14⟩,
  ⟨1724048165059220, 2, 8, 14⟩,
  ⟨365386267112295, 1, 9, 14⟩,
  ⟨33216933373845, 0, 10, 14⟩,
  ⟨52150189291200, 8, 1, 15⟩,
  ⟨385540174219200, 7, 2, 15⟩,
  ⟨1235641801954560, 6, 3, 15⟩,
  ⟨2238303257910720, 5, 4, 15⟩,
  ⟨2500377055848672, 4, 5, 15⟩,
  ⟨1757806701379872, 3, 6, 15⟩,
  ⟨755700147506304, 2, 7, 15⟩,
  ⟨180243401212160, 1, 8, 15⟩,
  ⟨18024340121216, 0, 9, 15⟩,
  ⟨23397980205600, 7, 1, 16⟩,
  ⟨149200495784340, 6, 2, 16⟩,
  ⟨402865566503400, 5, 3, 16⟩,
  ⟨595405778719752, 4, 4, 16⟩,
  ⟨518067645889794, 3, 5, 16⟩,
  ⟨263771534678652, 2, 6, 16⟩,
  ⟨72052431705540, 1, 7, 16⟩,
  ⟨8005825745060, 0, 8, 16⟩,
  ⟨8436926157660, 6, 1, 17⟩,
  ⟨45243234036000, 5, 2, 17⟩,
  ⟨99419998958280, 4, 3, 17⟩,
  ⟨114029815591692, 3, 4, 17⟩,
  ⟨71450310423492, 2, 5, 17⟩,
  ⟨22896212470560, 1, 6, 17⟩,
  ⟨2862026558820, 0, 7, 17⟩,
  ⟨2384639687430, 5, 1, 18⟩,
  ⟨10375380105090, 4, 2, 18⟩,
  ⟨17613405179370, 3, 3, 18⟩,
  ⟨14442407743764, 2, 4, 18⟩,
  ⟨5623055788350, 1, 5, 18⟩,
  ⟨803293684050, 0, 6, 18⟩,
  ⟨508651743600, 4, 1, 19⟩,
  ⟨1699967669400, 3, 2, 19⟩,
  ⟨2043530689200, 2, 3, 19⟩,
  ⟨1022657716080, 1, 4, 19⟩,
  ⟨170442952680, 0, 5, 19⟩,
  ⟨76967040150, 3, 1, 20⟩,
  ⟨179812853220, 2, 2, 20⟩,
  ⟨128501493120, 1, 3, 20⟩,
  ⟨25700298624, 0, 4, 20⟩,
  ⟨7362064710, 2, 1, 21⟩,
  ⟨9816086280, 1, 2, 21⟩,
  ⟨2454021570, 0, 3, 21⟩,
  ⟨334639305, 1, 1, 22⟩,
  ⟨111546435, 0, 2, 22⟩]

private def oddKernelElevenUnitGapCertificate (p q s : Rat) : Rat :=
  simplexCertEval oddKernelElevenUnitGapTerms p q s

private theorem oddKernelElevenUnitGapTerms_nonneg :
    simplexCertCoeffsNonneg oddKernelElevenUnitGapTerms := by
  native_decide

private theorem oddKernelElevenUnitGapCertificate_nonneg
    {p q s : Rat} (hp : 0 <= p) (hq : 0 <= q) (hs : 0 <= s) :
    0 <= oddKernelElevenUnitGapCertificate p q s :=
  simplexCertEval_nonneg hp hq hs oddKernelElevenUnitGapTerms_nonneg

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem oddKernelElevenUnitGap_eq_certificate (p r : Rat) :
    let q : Rat := r - p
    let s : Rat := 1 - r
    334639305 - (1 + p * p) *
      (334639305 - 111546435 * (r ^ 2 + r * p + p ^ 2)
        + 66927861 * (r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4)
        - 47805615 * (r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 + r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6)
        + 37182145 * (r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 + r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5 + r ^ 2 * p ^ 6 + r * p ^ 7 + p ^ 8)
        - 30421755 * (r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 + r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5 + r ^ 4 * p ^ 6 + r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10)
        + 25741485 * (r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 + r ^ 8 * p ^ 4 + r ^ 7 * p ^ 5 + r ^ 6 * p ^ 6 + r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8 + r ^ 3 * p ^ 9 + r ^ 2 * p ^ 10 + r * p ^ 11 + p ^ 12)
        - 22309287 * (r ^ 14 + r ^ 13 * p + r ^ 12 * p ^ 2 + r ^ 11 * p ^ 3 + r ^ 10 * p ^ 4 + r ^ 9 * p ^ 5 + r ^ 8 * p ^ 6 + r ^ 7 * p ^ 7 + r ^ 6 * p ^ 8 + r ^ 5 * p ^ 9 + r ^ 4 * p ^ 10 + r ^ 3 * p ^ 11 + r ^ 2 * p ^ 12 + r * p ^ 13 + p ^ 14)
        + 19684665 * (r ^ 16 + r ^ 15 * p + r ^ 14 * p ^ 2 + r ^ 13 * p ^ 3 + r ^ 12 * p ^ 4 + r ^ 11 * p ^ 5 + r ^ 10 * p ^ 6 + r ^ 9 * p ^ 7 + r ^ 8 * p ^ 8 + r ^ 7 * p ^ 9 + r ^ 6 * p ^ 10 + r ^ 5 * p ^ 11 + r ^ 4 * p ^ 12 + r ^ 3 * p ^ 13 + r ^ 2 * p ^ 14 + r * p ^ 15 + p ^ 16)
        - 17612595 * (r ^ 18 + r ^ 17 * p + r ^ 16 * p ^ 2 + r ^ 15 * p ^ 3 + r ^ 14 * p ^ 4 + r ^ 13 * p ^ 5 + r ^ 12 * p ^ 6 + r ^ 11 * p ^ 7 + r ^ 10 * p ^ 8 + r ^ 9 * p ^ 9 + r ^ 8 * p ^ 10 + r ^ 7 * p ^ 11 + r ^ 6 * p ^ 12 + r ^ 5 * p ^ 13 + r ^ 4 * p ^ 14 + r ^ 3 * p ^ 15 + r ^ 2 * p ^ 16 + r * p ^ 17 + p ^ 18)
        + 15935205 * (r ^ 20 + r ^ 19 * p + r ^ 18 * p ^ 2 + r ^ 17 * p ^ 3 + r ^ 16 * p ^ 4 + r ^ 15 * p ^ 5 + r ^ 14 * p ^ 6 + r ^ 13 * p ^ 7 + r ^ 12 * p ^ 8 + r ^ 11 * p ^ 9 + r ^ 10 * p ^ 10 + r ^ 9 * p ^ 11 + r ^ 8 * p ^ 12 + r ^ 7 * p ^ 13 + r ^ 6 * p ^ 14 + r ^ 5 * p ^ 15 + r ^ 4 * p ^ 16 + r ^ 3 * p ^ 17 + r ^ 2 * p ^ 18 + r * p ^ 19 + p ^ 20)
        - 14549535 * (r ^ 22 + r ^ 21 * p + r ^ 20 * p ^ 2 + r ^ 19 * p ^ 3 + r ^ 18 * p ^ 4 + r ^ 17 * p ^ 5 + r ^ 16 * p ^ 6 + r ^ 15 * p ^ 7 + r ^ 14 * p ^ 8 + r ^ 13 * p ^ 9 + r ^ 12 * p ^ 10 + r ^ 11 * p ^ 11 + r ^ 10 * p ^ 12 + r ^ 9 * p ^ 13 + r ^ 8 * p ^ 14 + r ^ 7 * p ^ 15 + r ^ 6 * p ^ 16 + r ^ 5 * p ^ 17 + r ^ 4 * p ^ 18 + r ^ 3 * p ^ 19 + r ^ 2 * p ^ 20 + r * p ^ 21 + p ^ 22)
          ) =
      oddKernelElevenUnitGapCertificate p q s := by
  intro q s
  unfold oddKernelElevenUnitGapCertificate oddKernelElevenUnitGapTerms
  simp [simplexCertEval, simplexCertTermEval]
  dsimp [q, s]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem kernelPartialIntegralBetween_eleven_le_integralUpperStep_on_unit
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    Taylor.ArctanKernel.kernelPartialIntegralBetween p r 11 <=
      ArctanGeometry.integralUpperStep p r := by
  let L : Rat := r - p
  let D : Rat := 1 + p * p
  let S3 : Rat :=
    r ^ 2 + r * p + p ^ 2
  let S5 : Rat :=
    r ^ 4 + r ^ 3 * p + r ^ 2 * p ^ 2 + r * p ^ 3 + p ^ 4
  let S7 : Rat :=
    r ^ 6 + r ^ 5 * p + r ^ 4 * p ^ 2 + r ^ 3 * p ^ 3 + r ^ 2 * p ^ 4 + r * p ^ 5 + p ^ 6
  let S9 : Rat :=
    r ^ 8 + r ^ 7 * p + r ^ 6 * p ^ 2 + r ^ 5 * p ^ 3 + r ^ 4 * p ^ 4 + r ^ 3 * p ^ 5
    + r ^ 2 * p ^ 6 + r * p ^ 7 + p ^ 8
  let S11 : Rat :=
    r ^ 10 + r ^ 9 * p + r ^ 8 * p ^ 2 + r ^ 7 * p ^ 3 + r ^ 6 * p ^ 4 + r ^ 5 * p ^ 5
    + r ^ 4 * p ^ 6 + r ^ 3 * p ^ 7 + r ^ 2 * p ^ 8 + r * p ^ 9 + p ^ 10
  let S13 : Rat :=
    r ^ 12 + r ^ 11 * p + r ^ 10 * p ^ 2 + r ^ 9 * p ^ 3 + r ^ 8 * p ^ 4 + r ^ 7 * p ^ 5
    + r ^ 6 * p ^ 6 + r ^ 5 * p ^ 7 + r ^ 4 * p ^ 8 + r ^ 3 * p ^ 9 + r ^ 2 * p ^ 10
    + r * p ^ 11 + p ^ 12
  let S15 : Rat :=
    r ^ 14 + r ^ 13 * p + r ^ 12 * p ^ 2 + r ^ 11 * p ^ 3 + r ^ 10 * p ^ 4 + r ^ 9 * p ^ 5
    + r ^ 8 * p ^ 6 + r ^ 7 * p ^ 7 + r ^ 6 * p ^ 8 + r ^ 5 * p ^ 9 + r ^ 4 * p ^ 10
    + r ^ 3 * p ^ 11 + r ^ 2 * p ^ 12 + r * p ^ 13 + p ^ 14
  let S17 : Rat :=
    r ^ 16 + r ^ 15 * p + r ^ 14 * p ^ 2 + r ^ 13 * p ^ 3 + r ^ 12 * p ^ 4 + r ^ 11 * p ^ 5
    + r ^ 10 * p ^ 6 + r ^ 9 * p ^ 7 + r ^ 8 * p ^ 8 + r ^ 7 * p ^ 9 + r ^ 6 * p ^ 10
    + r ^ 5 * p ^ 11 + r ^ 4 * p ^ 12 + r ^ 3 * p ^ 13 + r ^ 2 * p ^ 14 + r * p ^ 15 + p ^ 16
  let S19 : Rat :=
    r ^ 18 + r ^ 17 * p + r ^ 16 * p ^ 2 + r ^ 15 * p ^ 3 + r ^ 14 * p ^ 4 + r ^ 13 * p ^ 5
    + r ^ 12 * p ^ 6 + r ^ 11 * p ^ 7 + r ^ 10 * p ^ 8 + r ^ 9 * p ^ 9 + r ^ 8 * p ^ 10
    + r ^ 7 * p ^ 11 + r ^ 6 * p ^ 12 + r ^ 5 * p ^ 13 + r ^ 4 * p ^ 14 + r ^ 3 * p ^ 15
    + r ^ 2 * p ^ 16 + r * p ^ 17 + p ^ 18
  let S21 : Rat :=
    r ^ 20 + r ^ 19 * p + r ^ 18 * p ^ 2 + r ^ 17 * p ^ 3 + r ^ 16 * p ^ 4 + r ^ 15 * p ^ 5
    + r ^ 14 * p ^ 6 + r ^ 13 * p ^ 7 + r ^ 12 * p ^ 8 + r ^ 11 * p ^ 9 + r ^ 10 * p ^ 10
    + r ^ 9 * p ^ 11 + r ^ 8 * p ^ 12 + r ^ 7 * p ^ 13 + r ^ 6 * p ^ 14 + r ^ 5 * p ^ 15
    + r ^ 4 * p ^ 16 + r ^ 3 * p ^ 17 + r ^ 2 * p ^ 18 + r * p ^ 19 + p ^ 20
  let S23 : Rat :=
    r ^ 22 + r ^ 21 * p + r ^ 20 * p ^ 2 + r ^ 19 * p ^ 3 + r ^ 18 * p ^ 4 + r ^ 17 * p ^ 5
    + r ^ 16 * p ^ 6 + r ^ 15 * p ^ 7 + r ^ 14 * p ^ 8 + r ^ 13 * p ^ 9 + r ^ 12 * p ^ 10
    + r ^ 11 * p ^ 11 + r ^ 10 * p ^ 12 + r ^ 9 * p ^ 13 + r ^ 8 * p ^ 14 + r ^ 7 * p ^ 15
    + r ^ 6 * p ^ 16 + r ^ 5 * p ^ 17 + r ^ 4 * p ^ 18 + r ^ 3 * p ^ 19 + r ^ 2 * p ^ 20
    + r * p ^ 21 + p ^ 22
  have hL0 : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hDpos : 0 < D := by
    dsimp [D]
    exact RationalCircle.Stage.one_add_square_pos p
  have h334639305Dpos : 0 < 334639305 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 334639305) hDpos
  let q : Rat := r - p
  let s : Rat := 1 - r
  have hq0 : 0 <= q := by
    dsimp [q]
    grind [Rat.sub_eq_add_neg]
  have hs0 : 0 <= s := by
    dsimp [s]
    grind [Rat.sub_eq_add_neg]
  have hgap_cert := oddKernelElevenUnitGap_eq_certificate p r
  have hgap_nonneg :
      0 <=
        334639305
        - D * (334639305 - 111546435 * S3 + 66927861 * S5 - 47805615 * S7 + 37182145 * S9 - 30421755 * S11 + 25741485 * S13 - 22309287 * S15 + 19684665 * S17 - 17612595 * S19 + 15935205 * S21 - 14549535 * S23
          ) := by
    dsimp [D, S3, S5, S7, S9, S11, S13, S15, S17, S19, S21, S23]
    rw [hgap_cert]
    exact oddKernelElevenUnitGapCertificate_nonneg hp0 hq0 hs0
  have hscalar :
      D * (334639305 - 111546435 * S3 + 66927861 * S5 - 47805615 * S7 + 37182145 * S9 - 30421755 * S11 + 25741485 * S13 - 22309287 * S15 + 19684665 * S17 - 17612595 * S19 + 15935205 * S21 - 14549535 * S23
          ) <= 334639305 := by
    grind [Rat.sub_eq_add_neg]
  have hupper_mul :
      ArctanGeometry.integralUpperStep p r * (334639305 * D) = L * 334639305 := by
    unfold ArctanGeometry.integralUpperStep ArctanGeometry.integralKernel
    rw [Rat.div_def]
    have hne : D ≠ 0 := Rat.ne_of_gt hDpos
    dsimp [L, D] at hne ⊢
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hkernel_mul :
      Taylor.ArctanKernel.kernelPartialIntegralBetween p r 11 * (334639305 * D) =
        L * (D * (334639305 - 111546435 * S3 + 66927861 * S5 - 47805615 * S7 + 37182145 * S9 - 30421755 * S11 + 25741485 * S13 - 22309287 * S15 + 19684665 * S17 - 17612595 * S19 + 15935205 * S21 - 14549535 * S23
          )) := by
    have hkernel_formula :
        Taylor.ArctanKernel.kernelPartialIntegralBetween p r 11 =
          (r - p) - (r ^ 3 - p ^ 3) / 3 + (r ^ 5 - p ^ 5) / 5 - (r ^ 7 - p ^ 7) / 7
          + (r ^ 9 - p ^ 9) / 9 - (r ^ 11 - p ^ 11) / 11 + (r ^ 13 - p ^ 13) / 13
          - (r ^ 15 - p ^ 15) / 15 + (r ^ 17 - p ^ 17) / 17 - (r ^ 19 - p ^ 19) / 19
          + (r ^ 21 - p ^ 21) / 21 - (r ^ 23 - p ^ 23) / 23
          := by
      simp [Taylor.ArctanKernel.kernelPartialIntegralBetween,
        Taylor.ArctanKernel.kernelTermIntegralBetween]
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hS3 : r ^ 3 - p ^ 3 = L * S3 := by
      dsimp [L, S3]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS5 : r ^ 5 - p ^ 5 = L * S5 := by
      dsimp [L, S5]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS7 : r ^ 7 - p ^ 7 = L * S7 := by
      dsimp [L, S7]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS9 : r ^ 9 - p ^ 9 = L * S9 := by
      dsimp [L, S9]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS11 : r ^ 11 - p ^ 11 = L * S11 := by
      dsimp [L, S11]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS13 : r ^ 13 - p ^ 13 = L * S13 := by
      dsimp [L, S13]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS15 : r ^ 15 - p ^ 15 = L * S15 := by
      dsimp [L, S15]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS17 : r ^ 17 - p ^ 17 = L * S17 := by
      dsimp [L, S17]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS19 : r ^ 19 - p ^ 19 = L * S19 := by
      dsimp [L, S19]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS21 : r ^ 21 - p ^ 21 = L * S21 := by
      dsimp [L, S21]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    have hS23 : r ^ 23 - p ^ 23 = L * S23 := by
      dsimp [L, S23]
      repeat rw [Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hkernel_formula, hS3, hS5, hS7, hS9, hS11, hS13, hS15, hS17, hS19, hS21, hS23]
    dsimp [D, S3, S5, S7, S9, S11, S13, S15, S17, S19, S21, S23]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  apply Rat.le_of_mul_le_mul_right (c := 334639305 * D)
  · rw [hkernel_mul, hupper_mul]
    exact Rat.mul_le_mul_of_nonneg_left hscalar hL0
  · exact h334639305Dpos

theorem oddKernelUnitCellBound_eleven : OddKernelUnitCellBound 11 := by
  intro p r hp0 hpr hr1
  exact kernelPartialIntegralBetween_eleven_le_integralUpperStep_on_unit hp0 hpr hr1

theorem unitUniformCellBoundsAtOneUpTo_of_le
    {M N : Nat} (hMN : M <= N)
    (h : LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N) :
    LeibnizRectangleUniformUnitCellBoundsAtOneUpTo M := by
  constructor
  · intro n hn
    exact h.1 n (Nat.le_trans hn hMN)
  · intro n hn
    exact h.2 n (Nat.le_trans hn hMN)

theorem unitUniformCellBoundsAtOneUpTo_of_unitUniformCellBounds
    (h : LeibnizRectangleUniformUnitCellBoundsAtOne) (N : Nat) :
    LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N := by
  constructor
  · intro n _hn
    exact h.1 n
  · intro n _hn
    exact h.2 n

theorem unitUniformCellBoundsAtOneUpToAll_of_unitUniformCellBounds
    (h : LeibnizRectangleUniformUnitCellBoundsAtOne) :
    LeibnizRectangleUniformUnitCellBoundsAtOneUpToAll := by
  intro N
  exact unitUniformCellBoundsAtOneUpTo_of_unitUniformCellBounds h N

theorem unitUniformCellBoundsAtOne_iff_upToAll :
    LeibnizRectangleUniformUnitCellBoundsAtOne ↔
      LeibnizRectangleUniformUnitCellBoundsAtOneUpToAll := by
  constructor
  · exact unitUniformCellBoundsAtOneUpToAll_of_unitUniformCellBounds
  · intro h
    constructor
    · intro n
      exact (h n).1 n (Nat.le_refl n)
    · intro n
      exact (h n).2 n (Nat.le_refl n)

theorem evenKernelCellBound_le_five
    (n : Nat) (hn : n <= 5) :
    EvenKernelCellBound (2 * n) := by
  intro p r hp0 hpr hr1
  cases n with
  | zero =>
      simpa using evenKernelCellBound_zero hp0 hpr hr1
  | succ n =>
      cases n with
      | zero =>
          simpa using evenKernelCellBound_two hp0 hpr hr1
      | succ n =>
          cases n with
          | zero =>
              simpa using evenKernelCellBound_four hp0 hpr hr1
          | succ n =>
              cases n with
              | zero =>
                  simpa using evenKernelCellBound_six hp0 hpr hr1
              | succ n =>
                  cases n with
                  | zero =>
                      simpa using evenKernelCellBound_eight hp0 hpr hr1
                  | succ n =>
                      cases n with
                      | zero =>
                          simpa using evenKernelCellBound_ten hp0 hpr hr1
                      | succ n => omega

theorem oddKernelUnitCellBound_le_five
    (n : Nat) (hn : n <= 5) :
    OddKernelUnitCellBound (2 * n + 1) := by
  intro p r hp0 hpr hr1
  cases n with
  | zero =>
      simpa using oddKernelUnitCellBound_one hp0 hpr hr1
  | succ n =>
      cases n with
      | zero =>
          simpa using oddKernelUnitCellBound_three hp0 hpr hr1
      | succ n =>
          cases n with
          | zero =>
              simpa using oddKernelUnitCellBound_five hp0 hpr hr1
          | succ n =>
              cases n with
              | zero =>
                  simpa using oddKernelUnitCellBound_seven hp0 hpr hr1
              | succ n =>
                  cases n with
                  | zero =>
                      simpa using oddKernelUnitCellBound_nine hp0 hpr hr1
                  | succ n =>
                      cases n with
                      | zero =>
                          simpa using oddKernelUnitCellBound_eleven hp0 hpr hr1
                      | succ n => omega

theorem leibnizRectangleUniformUnitCellBoundsAtOneUpToFive :
    LeibnizRectangleUniformUnitCellBoundsAtOneUpTo 5 :=
  ⟨evenKernelCellBound_le_five, oddKernelUnitCellBound_le_five⟩

theorem evenKernelCellBounds_zero_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    EvenKernelCellBounds 0 intervals :=
  evenKernelCellBounds_of_cellBound evenKernelCellBound_zero h

theorem oddKernelCellBounds_one_of_nonnegative
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.NonnegativeIntervals intervals) :
    OddKernelCellBounds 1 intervals :=
  oddKernelCellBounds_of_cellBound oddKernelCellBound_one h

theorem oddKernelCellBounds_three_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    OddKernelCellBounds 3 intervals := by
  induction intervals with
  | nil =>
      simp [OddKernelCellBounds]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp0, hpr, hr1, hrest⟩
      simp [OddKernelCellBounds]
      exact ⟨oddKernelUnitCellBound_three hp0 hpr hr1, ih hrest⟩

theorem oddKernelCellBounds_five_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    OddKernelCellBounds 5 intervals := by
  induction intervals with
  | nil =>
      simp [OddKernelCellBounds]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp0, hpr, hr1, hrest⟩
      simp [OddKernelCellBounds]
      exact ⟨oddKernelUnitCellBound_five hp0 hpr hr1, ih hrest⟩

theorem oddKernelCellBounds_seven_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    OddKernelCellBounds 7 intervals := by
  induction intervals with
  | nil =>
      simp [OddKernelCellBounds]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp0, hpr, hr1, hrest⟩
      simp [OddKernelCellBounds]
      exact ⟨oddKernelUnitCellBound_seven hp0 hpr hr1, ih hrest⟩

theorem oddKernelCellBounds_nine_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    OddKernelCellBounds 9 intervals := by
  induction intervals with
  | nil =>
      simp [OddKernelCellBounds]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp0, hpr, hr1, hrest⟩
      simp [OddKernelCellBounds]
      exact ⟨oddKernelUnitCellBound_nine hp0 hpr hr1, ih hrest⟩

theorem oddKernelCellBounds_eleven_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    OddKernelCellBounds 11 intervals := by
  induction intervals with
  | nil =>
      simp [OddKernelCellBounds]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp0, hpr, hr1, hrest⟩
      simp [OddKernelCellBounds]
      exact ⟨oddKernelUnitCellBound_eleven hp0 hpr hr1, ih hrest⟩

theorem evenKernelCellBounds_two_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    EvenKernelCellBounds 2 intervals :=
  evenKernelCellBounds_of_cellBound evenKernelCellBound_two h

theorem evenKernelCellBounds_four_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    EvenKernelCellBounds 4 intervals :=
  evenKernelCellBounds_of_cellBound evenKernelCellBound_four h

theorem evenKernelCellBounds_six_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    EvenKernelCellBounds 6 intervals :=
  evenKernelCellBounds_of_cellBound evenKernelCellBound_six h

theorem evenKernelCellBounds_eight_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    EvenKernelCellBounds 8 intervals :=
  evenKernelCellBounds_of_cellBound evenKernelCellBound_eight h

theorem evenKernelCellBounds_ten_of_unit
    {intervals : List (Rat × Rat)}
    (h : ArctanGeometry.UnitIntervals intervals) :
    EvenKernelCellBounds 10 intervals :=
  evenKernelCellBounds_of_cellBound evenKernelCellBound_ten h

theorem evenKernelCellBoundsAtOne_zero :
    EvenKernelCellBounds 0
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 0).intervals :=
  evenKernelCellBounds_zero_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 0)

theorem oddKernelCellBoundsAtOne_zero :
    OddKernelCellBounds 1
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 1).intervals :=
  oddKernelCellBounds_one_of_nonnegative
    (ArctanGeometry.arctanAreaLoopState_intervals_nonnegative
      (x := (1 : Rat)) (by native_decide) 1)

theorem evenKernelCellBoundsAtOne_one :
    EvenKernelCellBounds 2
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 1).intervals :=
  evenKernelCellBounds_two_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 1)

theorem oddKernelCellBoundsAtOne_one :
    OddKernelCellBounds 3
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 2).intervals :=
  oddKernelCellBounds_three_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 2)

theorem evenKernelCellBoundsAtOne_two :
    EvenKernelCellBounds 4
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 2).intervals :=
  evenKernelCellBounds_four_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 2)

theorem oddKernelCellBoundsAtOne_two :
    OddKernelCellBounds 5
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 3).intervals :=
  oddKernelCellBounds_five_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 3)

theorem evenKernelCellBoundsAtOne_three :
    EvenKernelCellBounds 6
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 3).intervals :=
  evenKernelCellBounds_six_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 3)

theorem oddKernelCellBoundsAtOne_three :
    OddKernelCellBounds 7
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 4).intervals :=
  oddKernelCellBounds_seven_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 4)

theorem evenKernelCellBoundsAtOne_four :
    EvenKernelCellBounds 8
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 4).intervals :=
  evenKernelCellBounds_eight_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 4)

theorem oddKernelCellBoundsAtOne_four :
    OddKernelCellBounds 9
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 5).intervals :=
  oddKernelCellBounds_nine_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 5)

theorem evenKernelCellBoundsAtOne_five :
    EvenKernelCellBounds 10
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 5).intervals :=
  evenKernelCellBounds_ten_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 5)

theorem oddKernelCellBoundsAtOne_five :
    OddKernelCellBounds 11
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 6).intervals :=
  oddKernelCellBounds_eleven_of_unit
    (ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) 6)

def LeibnizRectangleKernelCellBoundsAtOneBase : Prop :=
  EvenKernelCellBounds 0
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 0).intervals /\
    OddKernelCellBounds 1
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) 1).intervals

theorem leibnizRectangleKernelCellBoundsAtOneBase :
    LeibnizRectangleKernelCellBoundsAtOneBase :=
  ⟨evenKernelCellBoundsAtOne_zero, oddKernelCellBoundsAtOne_zero⟩

def LeibnizRectangleKernelCellBoundsAtOneUpTo (N : Nat) : Prop :=
  (forall n, n <= N ->
    EvenKernelCellBounds (2 * n)
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals) /\
  (forall n, n <= N ->
    OddKernelCellBounds (2 * n + 1)
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) (n + 1)).intervals)

def LeibnizRectangleKernelCellBoundsAtOneUpToAll : Prop :=
  forall N, LeibnizRectangleKernelCellBoundsAtOneUpTo N

theorem leibnizRectangleKernelCellBoundsAtOneUpTo_of_le
    {M N : Nat} (hMN : M <= N)
    (h : LeibnizRectangleKernelCellBoundsAtOneUpTo N) :
    LeibnizRectangleKernelCellBoundsAtOneUpTo M := by
  constructor
  · intro n hn
    exact h.1 n (Nat.le_trans hn hMN)
  · intro n hn
    exact h.2 n (Nat.le_trans hn hMN)

theorem cellBoundsUpTo_of_unitUniformCellBoundsUpTo
    {N : Nat} (h : LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N) :
    LeibnizRectangleKernelCellBoundsAtOneUpTo N := by
  constructor
  · intro n hn
    exact evenKernelCellBounds_of_cellBound (h.1 n hn)
      (ArctanGeometry.arctanAreaLoopState_intervals_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide) n)
  · intro n hn
    exact oddKernelCellBounds_of_unitCellBound (h.2 n hn)
      (ArctanGeometry.arctanAreaLoopState_intervals_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide) (n + 1))

theorem leibnizRectangleKernelCellBoundsAtOneUpToFive_of_unitUniform :
    LeibnizRectangleKernelCellBoundsAtOneUpTo 5 :=
  cellBoundsUpTo_of_unitUniformCellBoundsUpTo
    leibnizRectangleUniformUnitCellBoundsAtOneUpToFive

theorem leibnizRectangleKernelCellBoundsAtOneUpToOne :
    LeibnizRectangleKernelCellBoundsAtOneUpTo 1 := by
  unfold LeibnizRectangleKernelCellBoundsAtOneUpTo
  constructor
  · intro n hn
    cases n with
    | zero =>
        simpa using evenKernelCellBoundsAtOne_zero
    | succ n =>
        cases n with
        | zero =>
            simpa using evenKernelCellBoundsAtOne_one
        | succ n =>
            omega
  · intro n hn
    cases n with
    | zero =>
        simpa using oddKernelCellBoundsAtOne_zero
    | succ n =>
        cases n with
        | zero =>
            simpa using oddKernelCellBoundsAtOne_one
        | succ n =>
            omega

theorem leibnizRectangleKernelCellBoundsAtOneUpToTwo :
    LeibnizRectangleKernelCellBoundsAtOneUpTo 2 := by
  unfold LeibnizRectangleKernelCellBoundsAtOneUpTo
  constructor
  · intro n hn
    cases n with
    | zero =>
        simpa using evenKernelCellBoundsAtOne_zero
    | succ n =>
        cases n with
        | zero =>
            simpa using evenKernelCellBoundsAtOne_one
        | succ n =>
            cases n with
            | zero =>
                simpa using evenKernelCellBoundsAtOne_two
            | succ n =>
                omega
  · intro n hn
    cases n with
    | zero =>
        simpa using oddKernelCellBoundsAtOne_zero
    | succ n =>
        cases n with
        | zero =>
            simpa using oddKernelCellBoundsAtOne_one
        | succ n =>
            cases n with
            | zero =>
                simpa using oddKernelCellBoundsAtOne_two
            | succ n =>
                omega

theorem leibnizRectangleKernelCellBoundsAtOneUpToThree :
    LeibnizRectangleKernelCellBoundsAtOneUpTo 3 := by
  unfold LeibnizRectangleKernelCellBoundsAtOneUpTo
  constructor
  · intro n hn
    cases n with
    | zero =>
        simpa using evenKernelCellBoundsAtOne_zero
    | succ n =>
        cases n with
        | zero =>
            simpa using evenKernelCellBoundsAtOne_one
        | succ n =>
            cases n with
            | zero =>
                simpa using evenKernelCellBoundsAtOne_two
            | succ n =>
                cases n with
                | zero =>
                    simpa using evenKernelCellBoundsAtOne_three
                | succ n =>
                    omega
  · intro n hn
    cases n with
    | zero =>
        simpa using oddKernelCellBoundsAtOne_zero
    | succ n =>
        cases n with
        | zero =>
            simpa using oddKernelCellBoundsAtOne_one
        | succ n =>
            cases n with
            | zero =>
                simpa using oddKernelCellBoundsAtOne_two
            | succ n =>
                cases n with
                | zero =>
                    simpa using oddKernelCellBoundsAtOne_three
                | succ n =>
                    omega

theorem evenKernelCellBoundsAtOne_le_four
    (n : Nat) (hn : n <= 4) :
    EvenKernelCellBounds (2 * n)
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals := by
  cases n with
  | zero =>
      simpa using evenKernelCellBoundsAtOne_zero
  | succ n =>
      cases n with
      | zero =>
          simpa using evenKernelCellBoundsAtOne_one
      | succ n =>
          cases n with
          | zero =>
              simpa using evenKernelCellBoundsAtOne_two
          | succ n =>
              cases n with
              | zero =>
                  simpa using evenKernelCellBoundsAtOne_three
              | succ n =>
                  cases n with
                  | zero =>
                      simpa using evenKernelCellBoundsAtOne_four
                  | succ n => omega

theorem oddKernelCellBoundsAtOne_le_four
    (n : Nat) (hn : n <= 4) :
    OddKernelCellBounds (2 * n + 1)
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) (n + 1)).intervals := by
  cases n with
  | zero =>
      simpa using oddKernelCellBoundsAtOne_zero
  | succ n =>
      cases n with
      | zero =>
          simpa using oddKernelCellBoundsAtOne_one
      | succ n =>
          cases n with
          | zero =>
              simpa using oddKernelCellBoundsAtOne_two
          | succ n =>
              cases n with
              | zero =>
                  simpa using oddKernelCellBoundsAtOne_three
              | succ n =>
                  cases n with
                  | zero =>
                      simpa using oddKernelCellBoundsAtOne_four
                  | succ n => omega

theorem leibnizRectangleKernelCellBoundsAtOneUpToFour :
    LeibnizRectangleKernelCellBoundsAtOneUpTo 4 :=
  ⟨evenKernelCellBoundsAtOne_le_four, oddKernelCellBoundsAtOne_le_four⟩

theorem evenKernelCellBoundsAtOne_le_five
    (n : Nat) (hn : n <= 5) :
    EvenKernelCellBounds (2 * n)
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals := by
  cases n with
  | zero =>
      simpa using evenKernelCellBoundsAtOne_zero
  | succ n =>
      cases n with
      | zero =>
          simpa using evenKernelCellBoundsAtOne_one
      | succ n =>
          cases n with
          | zero =>
              simpa using evenKernelCellBoundsAtOne_two
          | succ n =>
              cases n with
              | zero =>
                  simpa using evenKernelCellBoundsAtOne_three
              | succ n =>
                  cases n with
                  | zero =>
                      simpa using evenKernelCellBoundsAtOne_four
                  | succ n =>
                      cases n with
                      | zero =>
                          simpa using evenKernelCellBoundsAtOne_five
                      | succ n => omega

theorem oddKernelCellBoundsAtOne_le_five
    (n : Nat) (hn : n <= 5) :
    OddKernelCellBounds (2 * n + 1)
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) (n + 1)).intervals := by
  cases n with
  | zero =>
      simpa using oddKernelCellBoundsAtOne_zero
  | succ n =>
      cases n with
      | zero =>
          simpa using oddKernelCellBoundsAtOne_one
      | succ n =>
          cases n with
          | zero =>
              simpa using oddKernelCellBoundsAtOne_two
          | succ n =>
              cases n with
              | zero =>
                  simpa using oddKernelCellBoundsAtOne_three
              | succ n =>
                  cases n with
                  | zero =>
                      simpa using oddKernelCellBoundsAtOne_four
                  | succ n =>
                      cases n with
                      | zero =>
                          simpa using oddKernelCellBoundsAtOne_five
                      | succ n => omega

theorem leibnizRectangleKernelCellBoundsAtOneUpToFive :
    LeibnizRectangleKernelCellBoundsAtOneUpTo 5 :=
  ⟨evenKernelCellBoundsAtOne_le_five, oddKernelCellBoundsAtOne_le_five⟩

theorem leibnizRectangleKernelCellBoundsAtOneUpToTwelve :
    LeibnizRectangleKernelCellBoundsAtOneUpTo 12 := by
  constructor <;> native_decide

theorem leibnizRectangleKernelCellBoundsAtOneUpToFifteen :
    LeibnizRectangleKernelCellBoundsAtOneUpTo 15 := by
  constructor <;> native_decide

theorem leibnizRectangleKernelCellBoundsAtOneUpToFourteen :
    LeibnizRectangleKernelCellBoundsAtOneUpTo 14 :=
  leibnizRectangleKernelCellBoundsAtOneUpTo_of_le
    (by native_decide : 14 <= 15)
    leibnizRectangleKernelCellBoundsAtOneUpToFifteen

theorem integralLowerSum_le_kernelPartialIntegralSum
    {m : Nat} {intervals : List (Rat × Rat)}
    (h : EvenKernelCellBounds m intervals) :
    ArctanGeometry.integralLowerSum intervals <=
      kernelPartialIntegralSum m intervals := by
  induction intervals with
  | nil => simp [ArctanGeometry.integralLowerSum, kernelPartialIntegralSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hhead, htail⟩
      simp [ArctanGeometry.integralLowerSum, kernelPartialIntegralSum]
      exact rat_add_le_add hhead (ih htail)

theorem kernelPartialIntegralSum_le_integralUpperSum
    {m : Nat} {intervals : List (Rat × Rat)}
    (h : OddKernelCellBounds m intervals) :
    kernelPartialIntegralSum m intervals <=
      ArctanGeometry.integralUpperSum intervals := by
  induction intervals with
  | nil => simp [ArctanGeometry.integralUpperSum, kernelPartialIntegralSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hhead, htail⟩
      simp [ArctanGeometry.integralUpperSum, kernelPartialIntegralSum]
      exact rat_add_le_add hhead (ih htail)

theorem refineAux_kernelPartialIntegralSum
    (m : Nat) (lo hi : Rat) (intervals : List (Rat × Rat)) :
    kernelPartialIntegralSum m
      (ArctanGeometry.AreaLoopState.refineAux lo hi intervals).intervals =
        kernelPartialIntegralSum m intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [ArctanGeometry.AreaLoopState.refineAux, kernelPartialIntegralSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      let q : Rat := (p + r) / 2
      simp [ArctanGeometry.AreaLoopState.refineAux, kernelPartialIntegralSum]
      rw [ih]
      have hsplit :=
        Taylor.ArctanKernel.kernelPartialIntegralBetween_split p q r m
      calc
        Taylor.ArctanKernel.kernelPartialIntegralBetween p q m +
              (Taylor.ArctanKernel.kernelPartialIntegralBetween q r m +
                kernelPartialIntegralSum m rest)
            = (Taylor.ArctanKernel.kernelPartialIntegralBetween p q m +
                Taylor.ArctanKernel.kernelPartialIntegralBetween q r m) +
                kernelPartialIntegralSum m rest := by
              grind [Rat.add_assoc, Rat.add_comm]
        _ = Taylor.ArctanKernel.kernelPartialIntegralBetween p r m +
              kernelPartialIntegralSum m rest := by
              rw [←hsplit]

theorem refineAreaLoopState_kernelPartialIntegralSum
    (m : Nat) (state : ArctanGeometry.AreaLoopState) :
    kernelPartialIntegralSum m
      (ArctanGeometry.refineAreaLoopState state).intervals =
        kernelPartialIntegralSum m state.intervals := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_kernelPartialIntegralSum m lo hi intervals

theorem iterateAreaLoopState_kernelPartialIntegralSum
    (m n : Nat) (state : ArctanGeometry.AreaLoopState) :
    kernelPartialIntegralSum m
      (ArctanGeometry.iterateAreaLoopState n state).intervals =
        kernelPartialIntegralSum m state.intervals := by
  induction n generalizing state with
  | zero =>
      simp [ArctanGeometry.iterateAreaLoopState]
  | succ n ih =>
      simp [ArctanGeometry.iterateAreaLoopState]
      calc
        kernelPartialIntegralSum m
            (ArctanGeometry.iterateAreaLoopState n
              (ArctanGeometry.refineAreaLoopState state)).intervals =
            kernelPartialIntegralSum m
              (ArctanGeometry.refineAreaLoopState state).intervals :=
          ih (ArctanGeometry.refineAreaLoopState state)
        _ = kernelPartialIntegralSum m state.intervals :=
          refineAreaLoopState_kernelPartialIntegralSum m state

theorem arctanAreaLoopState_one_kernelPartialIntegralSum
    (m n : Nat) :
    kernelPartialIntegralSum m
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals =
        Taylor.ArctanKernel.kernelPartialIntegralAtOne m := by
  unfold ArctanGeometry.arctanAreaLoopState
  rw [iterateAreaLoopState_kernelPartialIntegralSum]
  simp [ArctanGeometry.arctanAreaLoopInitial, kernelPartialIntegralSum]
  rw [Taylor.ArctanKernel.kernelPartialIntegralBetween_zero_one]
  grind

/-- On the midpoint partition of `[0,x]`, finite kernel-polynomial integrals
add exactly to the corresponding rational primitive over the whole interval. -/
theorem arctanAreaLoopState_kernelPartialIntegralSum
    (x : Rat) (m n : Nat) :
    kernelPartialIntegralSum m
      (ArctanGeometry.arctanAreaLoopState x n).intervals =
        Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x m := by
  unfold ArctanGeometry.arctanAreaLoopState
  rw [iterateAreaLoopState_kernelPartialIntegralSum]
  simp [ArctanGeometry.arctanAreaLoopInitial, kernelPartialIntegralSum]
  grind

/-- On the project’s dyadic mesh at `1`, the finite kernel polynomial differs
from its exact rational primitive by at most `m(m+1) / 2^n`.  The denominator
comes from the already verified sum of squared dyadic cell lengths. -/
theorem arctanAreaLoopState_one_kernelPartialRightRectangle_error_bound
    (m n : Nat) :
    -((m : Rat) * ((m + 1 : Nat) : Rat) *
        (1 / (((2 ^ n : Nat) : Rat)))) <=
        kernelPartialRightRectangleSum m
          (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals -
          Taylor.ArctanKernel.kernelPartialIntegralAtOne m /\
      kernelPartialRightRectangleSum m
          (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals -
          Taylor.ArctanKernel.kernelPartialIntegralAtOne m <=
        (m : Rat) * ((m + 1 : Nat) : Rat) *
          (1 / (((2 ^ n : Nat) : Rat))) := by
  have hunit : ArctanGeometry.UnitIntervals
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals :=
    ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) n
  have hsum := kernelPartialRightRectangleSum_error_bound (m := m) hunit
  rw [arctanAreaLoopState_one_kernelPartialIntegralSum] at hsum
  rw [ArctanGeometry.arctanAreaLoopState_one_squareSum] at hsum
  exact hsum

/-- Finite quadrature error for a kernel polynomial on the midpoint mesh of
`[0,x]`.  The exact squared-mesh budget is `x^2 / 2^n`. -/
theorem arctanAreaLoopState_kernelPartialRightRectangle_error_bound
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (m n : Nat) :
    -((m : Rat) * ((m + 1 : Nat) : Rat) *
        ((x * x) / (((2 ^ n : Nat) : Rat)))) <=
        kernelPartialRightRectangleSum m
          (ArctanGeometry.arctanAreaLoopState x n).intervals -
          Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x m /\
      kernelPartialRightRectangleSum m
          (ArctanGeometry.arctanAreaLoopState x n).intervals -
          Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x m <=
        (m : Rat) * ((m + 1 : Nat) : Rat) *
          ((x * x) / (((2 ^ n : Nat) : Rat))) := by
  have hunit : ArctanGeometry.UnitIntervals
      (ArctanGeometry.arctanAreaLoopState x n).intervals :=
    ArctanGeometry.arctanAreaLoopState_intervals_unit hx0 hx1 n
  have hsum := kernelPartialRightRectangleSum_error_bound (m := m) hunit
  rw [arctanAreaLoopState_kernelPartialIntegralSum] at hsum
  rw [ArctanGeometry.arctanAreaLoopState_squareSum] at hsum
  exact hsum

/-- The even Taylor kernel polynomial dominates the lower geometric rectangle
sum at its right endpoints. -/
theorem integralLowerSum_le_kernelPartialRightRectangleSum_even
    (n : Nat) {intervals : List (Rat × Rat)}
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    ArctanGeometry.integralLowerSum intervals <=
      kernelPartialRightRectangleSum (2 * n) intervals := by
  induction intervals with
  | nil =>
      simp [ArctanGeometry.integralLowerSum, kernelPartialRightRectangleSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, _hr1, hrest⟩
      have hlength : 0 <= r - p := by
        grind [Rat.sub_eq_add_neg]
      have hpoint : ArctanGeometry.integralKernel r <=
          Taylor.ArctanKernel.kernelPartial r (2 * n) :=
        Taylor.ArctanKernel.kernel_le_kernelPartial_even r n
      have hhead := Rat.mul_le_mul_of_nonneg_left hpoint hlength
      simp only [ArctanGeometry.integralLowerSum,
        kernelPartialRightRectangleSum, ArctanGeometry.integralLowerStep]
      exact rat_add_le_add hhead (ih hrest)

/-- The odd Taylor kernel polynomial at each right endpoint lies below the
corresponding upper geometric rectangle. -/
theorem kernelPartialRightRectangleSum_odd_le_integralUpperSum
    (n : Nat) {intervals : List (Rat × Rat)}
    (hunit : ArctanGeometry.UnitIntervals intervals) :
    kernelPartialRightRectangleSum (2 * n + 1) intervals <=
      ArctanGeometry.integralUpperSum intervals := by
  induction intervals with
  | nil =>
      simp [ArctanGeometry.integralUpperSum, kernelPartialRightRectangleSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hunit with ⟨hp0, hpr, _hr1, hrest⟩
      have hlength : 0 <= r - p := by
        grind [Rat.sub_eq_add_neg]
      have hpartial : Taylor.ArctanKernel.kernelPartial r (2 * n + 1) <=
          ArctanGeometry.integralKernel r :=
        Taylor.ArctanKernel.kernelPartial_odd_le_kernel r n
      have hkernel : ArctanGeometry.integralKernel r <=
          ArctanGeometry.integralKernel p :=
        ArctanGeometry.integralKernel_antitone_nonneg hp0 hpr
      have hhead := Rat.mul_le_mul_of_nonneg_left
        (Rat.le_trans hpartial hkernel) hlength
      simp only [ArctanGeometry.integralUpperSum,
        kernelPartialRightRectangleSum, ArctanGeometry.integralUpperStep]
      exact rat_add_le_add hhead (ih hrest)

/-- Cellwise finite inequalities on the actual midpoint partitions.

This is now the concrete finite target behind the rectangle comparison: even
kernel truncation integrals dominate lower rectangles on stage `n`, and odd
kernel truncation integrals are dominated by upper rectangles on stage
`n + 1`. -/
def LeibnizRectangleKernelCellBoundsAtOne : Prop :=
  (forall n,
    EvenKernelCellBounds (2 * n)
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals) /\
  (forall n,
    OddKernelCellBounds (2 * n + 1)
      (ArctanGeometry.arctanAreaLoopState (1 : Rat) (n + 1)).intervals)

theorem cellBounds_of_uniformCellBounds
    (h : LeibnizRectangleUniformCellBoundsAtOne) :
    LeibnizRectangleKernelCellBoundsAtOne := by
  unfold LeibnizRectangleKernelCellBoundsAtOne
  constructor
  · intro n
    exact evenKernelCellBounds_of_cellBound (h.1 n)
      (ArctanGeometry.arctanAreaLoopState_intervals_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide) n)
  · intro n
    exact oddKernelCellBounds_of_cellBound (h.2 n)
      (ArctanGeometry.arctanAreaLoopState_intervals_nonnegative
        (x := (1 : Rat)) (by native_decide) (n + 1))

theorem cellBounds_of_unitUniformCellBounds
    (h : LeibnizRectangleUniformUnitCellBoundsAtOne) :
    LeibnizRectangleKernelCellBoundsAtOne := by
  unfold LeibnizRectangleKernelCellBoundsAtOne
  constructor
  · intro n
    exact evenKernelCellBounds_of_cellBound (h.1 n)
      (ArctanGeometry.arctanAreaLoopState_intervals_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide) n)
  · intro n
    exact oddKernelCellBounds_of_unitCellBound (h.2 n)
      (ArctanGeometry.arctanAreaLoopState_intervals_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide) (n + 1))

theorem cellBoundsUpTo_of_cellBounds
    (h : LeibnizRectangleKernelCellBoundsAtOne) (N : Nat) :
    LeibnizRectangleKernelCellBoundsAtOneUpTo N := by
  unfold LeibnizRectangleKernelCellBoundsAtOne at h
  unfold LeibnizRectangleKernelCellBoundsAtOneUpTo
  exact ⟨fun n _hn => h.1 n, fun n _hn => h.2 n⟩

theorem cellBoundsUpToAll_of_cellBounds
    (h : LeibnizRectangleKernelCellBoundsAtOne) :
    LeibnizRectangleKernelCellBoundsAtOneUpToAll := by
  intro N
  exact cellBoundsUpTo_of_cellBounds h N

theorem cellBounds_of_cellBoundsUpToAll
    (h : LeibnizRectangleKernelCellBoundsAtOneUpToAll) :
    LeibnizRectangleKernelCellBoundsAtOne := by
  unfold LeibnizRectangleKernelCellBoundsAtOne
  constructor
  · intro n
    exact (h n).1 n (Nat.le_refl n)
  · intro n
    exact (h n).2 n (Nat.le_refl n)

theorem cellBoundsAtOne_iff_upToAll :
    LeibnizRectangleKernelCellBoundsAtOne ↔
      LeibnizRectangleKernelCellBoundsAtOneUpToAll := by
  constructor
  · exact cellBoundsUpToAll_of_cellBounds
  · exact cellBounds_of_cellBoundsUpToAll

theorem unitUniformCellBounds_of_unitUniformCellBoundsUpToAll
    (h : forall N, LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N) :
    LeibnizRectangleUniformUnitCellBoundsAtOne := by
  constructor
  · intro n
    exact (h n).1 n (Nat.le_refl n)
  · intro n
    exact (h n).2 n (Nat.le_refl n)

theorem cellBounds_of_unitUniformCellBoundsUpToAll
    (h : forall N, LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N) :
    LeibnizRectangleKernelCellBoundsAtOne :=
  cellBounds_of_unitUniformCellBounds
    (unitUniformCellBounds_of_unitUniformCellBoundsUpToAll h)

theorem pointwiseIntegralBridgeAtOne_iff_uniformCellBounds :
    LeibnizRectanglePointwiseIntegralBridgeAtOne ↔
      LeibnizRectangleUniformCellBoundsAtOne := by
  constructor
  · exact uniformCellBounds_of_pointwiseIntegralBridge
  · intro h _hpointwise
    exact h

theorem pointwiseUnitIntegralBridgeAtOne_iff_unitUniformCellBounds :
    LeibnizRectanglePointwiseUnitIntegralBridgeAtOne ↔
      LeibnizRectangleUniformUnitCellBoundsAtOne := by
  constructor
  · exact unitUniformCellBounds_of_pointwiseUnitIntegralBridge
  · intro h _hpointwise
    exact h

theorem pointwiseUnitIntegralBridgeAtOne_of_unitCellOrderPreservation
    (h : LeibnizRectangleUnitCellOrderPreservation) :
    LeibnizRectanglePointwiseUnitIntegralBridgeAtOne := by
  intro hpointwise
  constructor
  · intro n
    exact h.1 (2 * n) (hpointwise.1 n)
  · intro n
    exact h.2 (2 * n + 1) (hpointwise.2 n)

theorem unitUniformCellBounds_of_unitCellOrderPreservation
    (h : LeibnizRectangleUnitCellOrderPreservation) :
    LeibnizRectangleUniformUnitCellBoundsAtOne :=
  unitUniformCellBounds_of_pointwiseUnitIntegralBridge
    (pointwiseUnitIntegralBridgeAtOne_of_unitCellOrderPreservation h)

theorem cellBounds_of_pointwiseIntegralBridge
    (h : LeibnizRectanglePointwiseIntegralBridgeAtOne) :
    LeibnizRectangleKernelCellBoundsAtOne :=
  cellBounds_of_uniformCellBounds
    (uniformCellBounds_of_pointwiseIntegralBridge h)

theorem cellBounds_of_pointwiseUnitIntegralBridge
    (h : LeibnizRectanglePointwiseUnitIntegralBridgeAtOne) :
    LeibnizRectangleKernelCellBoundsAtOne :=
  cellBounds_of_unitUniformCellBounds
    (unitUniformCellBounds_of_pointwiseUnitIntegralBridge h)

theorem kernelBounds_of_cellBounds
    (h : LeibnizRectangleKernelCellBoundsAtOne) :
    LeibnizRectangleKernelBoundsAtOne := by
  intro n
  constructor
  · have hcell := h.1 n
    have hsum := integralLowerSum_le_kernelPartialIntegralSum hcell
    unfold ArctanGeometry.arctanIntegralRectangleComputeAtOne
    unfold ArctanGeometry.integralSumInterval
    dsimp
    calc
      ArctanGeometry.integralLowerSum
          (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals <=
          kernelPartialIntegralSum (2 * n)
            (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals := hsum
      _ = Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n) :=
          arctanAreaLoopState_one_kernelPartialIntegralSum (2 * n) n
      _ = LeibnizValidity.upperKernelPartialAtStage n := by
          simp [LeibnizValidity.upperKernelPartialAtStage]
  · cases n with
    | zero =>
        native_decide
    | succ n =>
        have hcell := h.2 n
        have hsum := kernelPartialIntegralSum_le_integralUpperSum hcell
        unfold ArctanGeometry.arctanIntegralRectangleComputeAtOne
        unfold ArctanGeometry.integralSumInterval
        dsimp
        calc
          LeibnizValidity.lowerKernelPartialAtStage (n + 1) =
              Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n + 1) := by
                simp [LeibnizValidity.lowerKernelPartialAtStage]
          _ = kernelPartialIntegralSum (2 * n + 1)
              (ArctanGeometry.arctanAreaLoopState (1 : Rat)
                (n + 1)).intervals := by
                rw [arctanAreaLoopState_one_kernelPartialIntegralSum]
          _ <= ArctanGeometry.integralUpperSum
              (ArctanGeometry.arctanAreaLoopState (1 : Rat)
                (n + 1)).intervals := hsum

def LeibnizRectangleKernelBoundsAtOneUpTo (N : Nat) : Prop :=
  forall n, n <= N ->
    (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).lo <=
      LeibnizValidity.upperKernelPartialAtStage n /\
    LeibnizValidity.lowerKernelPartialAtStage n <=
      (ArctanGeometry.arctanIntegralRectangleComputeAtOne n).hi

def LeibnizRectangleKernelBoundsAtOneUpToAll : Prop :=
  forall N, LeibnizRectangleKernelBoundsAtOneUpTo N

theorem kernelBoundsAtOneUpTo_of_le
    {M N : Nat} (hMN : M <= N)
    (h : LeibnizRectangleKernelBoundsAtOneUpTo N) :
    LeibnizRectangleKernelBoundsAtOneUpTo M := by
  intro n hn
  exact h n (Nat.le_trans hn hMN)

theorem kernelBoundsUpTo_of_cellBoundsUpTo
    {N : Nat} (h : LeibnizRectangleKernelCellBoundsAtOneUpTo N) :
    LeibnizRectangleKernelBoundsAtOneUpTo N := by
  intro n hn
  constructor
  · have hcell := h.1 n hn
    have hsum := integralLowerSum_le_kernelPartialIntegralSum hcell
    unfold ArctanGeometry.arctanIntegralRectangleComputeAtOne
    unfold ArctanGeometry.integralSumInterval
    dsimp
    calc
      ArctanGeometry.integralLowerSum
          (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals <=
          kernelPartialIntegralSum (2 * n)
            (ArctanGeometry.arctanAreaLoopState (1 : Rat) n).intervals := hsum
      _ = Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n) :=
          arctanAreaLoopState_one_kernelPartialIntegralSum (2 * n) n
      _ = LeibnizValidity.upperKernelPartialAtStage n := by
          simp [LeibnizValidity.upperKernelPartialAtStage]
  · cases n with
    | zero =>
        native_decide
    | succ n =>
        have hn' : n <= N := by omega
        have hcell := h.2 n hn'
        have hsum := kernelPartialIntegralSum_le_integralUpperSum hcell
        unfold ArctanGeometry.arctanIntegralRectangleComputeAtOne
        unfold ArctanGeometry.integralSumInterval
        dsimp
        calc
          LeibnizValidity.lowerKernelPartialAtStage (n + 1) =
              Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n + 1) := by
                simp [LeibnizValidity.lowerKernelPartialAtStage]
          _ = kernelPartialIntegralSum (2 * n + 1)
              (ArctanGeometry.arctanAreaLoopState (1 : Rat)
                (n + 1)).intervals := by
                rw [arctanAreaLoopState_one_kernelPartialIntegralSum]
          _ <= ArctanGeometry.integralUpperSum
              (ArctanGeometry.arctanAreaLoopState (1 : Rat)
                (n + 1)).intervals := hsum

theorem kernelBoundsUpTo_of_unitUniformCellBoundsUpTo
    {N : Nat} (h : LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N) :
    LeibnizRectangleKernelBoundsAtOneUpTo N :=
  kernelBoundsUpTo_of_cellBoundsUpTo
    (cellBoundsUpTo_of_unitUniformCellBoundsUpTo h)

theorem leibnizRectangleKernelBoundsAtOneUpToFifteen :
    LeibnizRectangleKernelBoundsAtOneUpTo 15 :=
  kernelBoundsUpTo_of_cellBoundsUpTo
    leibnizRectangleKernelCellBoundsAtOneUpToFifteen

theorem leibnizRectangleKernelBoundsAtOneUpToFourteen :
    LeibnizRectangleKernelBoundsAtOneUpTo 14 :=
  kernelBoundsAtOneUpTo_of_le
    (by native_decide : 14 <= 15)
    leibnizRectangleKernelBoundsAtOneUpToFifteen

theorem leibnizRectangleKernelBoundsAtOneUpToTwo :
    LeibnizRectangleKernelBoundsAtOneUpTo 2 :=
  kernelBoundsUpTo_of_cellBoundsUpTo
    leibnizRectangleKernelCellBoundsAtOneUpToTwo

theorem leibnizRectangleKernelBoundsAtOneUpToThree :
    LeibnizRectangleKernelBoundsAtOneUpTo 3 :=
  kernelBoundsUpTo_of_cellBoundsUpTo
    leibnizRectangleKernelCellBoundsAtOneUpToThree

theorem leibnizRectangleKernelBoundsAtOneUpToFour :
    LeibnizRectangleKernelBoundsAtOneUpTo 4 :=
  kernelBoundsUpTo_of_cellBoundsUpTo
    leibnizRectangleKernelCellBoundsAtOneUpToFour

theorem leibnizRectangleKernelBoundsAtOneUpToFive :
    LeibnizRectangleKernelBoundsAtOneUpTo 5 :=
  kernelBoundsUpTo_of_cellBoundsUpTo
    leibnizRectangleKernelCellBoundsAtOneUpToFive

theorem kernelBounds_of_cellBoundsUpToAll
    (h : LeibnizRectangleKernelCellBoundsAtOneUpToAll) :
    LeibnizRectangleKernelBoundsAtOne :=
  kernelBounds_of_cellBounds (cellBounds_of_cellBoundsUpToAll h)

theorem kernelBounds_of_unitUniformCellBoundsUpToAll
    (h : forall N, LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N) :
    LeibnizRectangleKernelBoundsAtOne :=
  kernelBounds_of_cellBounds (cellBounds_of_unitUniformCellBoundsUpToAll h)

theorem kernelBounds_of_kernelBoundsUpToAll
    (h : LeibnizRectangleKernelBoundsAtOneUpToAll) :
    LeibnizRectangleKernelBoundsAtOne := by
  intro n
  exact h n n (Nat.le_refl n)

theorem kernelBoundsUpToAll_of_kernelBounds
    (h : LeibnizRectangleKernelBoundsAtOne) :
    LeibnizRectangleKernelBoundsAtOneUpToAll := by
  intro N n _hn
  exact h n

theorem kernelBoundsAtOne_iff_upToAll :
    LeibnizRectangleKernelBoundsAtOne ↔
      LeibnizRectangleKernelBoundsAtOneUpToAll := by
  constructor
  · exact kernelBoundsUpToAll_of_kernelBounds
  · exact kernelBounds_of_kernelBoundsUpToAll

theorem kernelBoundsUpToAll_of_cellBoundsUpToAll
    (h : LeibnizRectangleKernelCellBoundsAtOneUpToAll) :
    LeibnizRectangleKernelBoundsAtOneUpToAll := by
  intro N
  exact kernelBoundsUpTo_of_cellBoundsUpTo (h N)

theorem kernelBoundsUpToAll_of_unitUniformCellBoundsUpToAll
    (h : LeibnizRectangleUniformUnitCellBoundsAtOneUpToAll) :
    LeibnizRectangleKernelBoundsAtOneUpToAll := by
  intro N
  exact kernelBoundsUpTo_of_unitUniformCellBoundsUpTo (h N)

theorem kernelBounds_of_pointwiseIntegralBridge
    (h : LeibnizRectanglePointwiseIntegralBridgeAtOne) :
    LeibnizRectangleKernelBoundsAtOne :=
  kernelBounds_of_cellBounds (cellBounds_of_pointwiseIntegralBridge h)

theorem kernelBounds_of_pointwiseUnitIntegralBridge
    (h : LeibnizRectanglePointwiseUnitIntegralBridgeAtOne) :
    LeibnizRectangleKernelBoundsAtOne :=
  kernelBounds_of_cellBounds (cellBounds_of_pointwiseUnitIntegralBridge h)

end LeibnizRectangleBridge

def LeibnizRectangleRawAtOneOverlapsUpTo (N : Nat) : Prop :=
  forall n, n <= N ->
    QInterval.Overlaps
      (leibnizSeries.compute n)
      (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute n)

def LeibnizRectangleRawAtOneOverlapsUpToAll : Prop :=
  forall N, LeibnizRectangleRawAtOneOverlapsUpTo N

theorem leibnizRectangleRawAtOneOverlapsUpTo_of_le
    {M N : Nat} (hMN : M <= N)
    (h : LeibnizRectangleRawAtOneOverlapsUpTo N) :
    LeibnizRectangleRawAtOneOverlapsUpTo M := by
  intro n hn
  exact h n (Nat.le_trans hn hMN)

theorem leibnizRectangleRawAtOneOverlapsUpTo_of_kernelBoundsUpTo
    {N : Nat}
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelBoundsAtOneUpTo N) :
    LeibnizRectangleRawAtOneOverlapsUpTo N := by
  intro n hn
  rw [LeibnizValidity.leibnizSeries_compute_eq_kernelPartialIntegralInterval n]
  change QInterval.Overlaps
    { lo := LeibnizValidity.lowerKernelPartialAtStage n,
      hi := LeibnizValidity.upperKernelPartialAtStage n }
    (ArctanGeometry.arctanIntegralRectangleComputeAtOne n)
  exact ⟨(h n hn).2, (h n hn).1⟩

theorem leibnizRectangleRawAtOneOverlapsUpTo_of_cellBoundsUpTo
    {N : Nat}
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelCellBoundsAtOneUpTo N) :
    LeibnizRectangleRawAtOneOverlapsUpTo N :=
  leibnizRectangleRawAtOneOverlapsUpTo_of_kernelBoundsUpTo
    (LeibnizRectangleBridge.kernelBoundsUpTo_of_cellBoundsUpTo h)

theorem leibnizRectangleRawAtOneOverlapsUpTo_of_unitUniformCellBoundsUpTo
    {N : Nat}
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N) :
    LeibnizRectangleRawAtOneOverlapsUpTo N :=
  leibnizRectangleRawAtOneOverlapsUpTo_of_kernelBoundsUpTo
    (LeibnizRectangleBridge.kernelBoundsUpTo_of_unitUniformCellBoundsUpTo h)

theorem leibnizRectangleRawAtOneOverlapsUpToAll_of_kernelBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelBoundsAtOneUpToAll) :
    LeibnizRectangleRawAtOneOverlapsUpToAll := by
  intro N
  exact leibnizRectangleRawAtOneOverlapsUpTo_of_kernelBoundsUpTo (h N)

theorem leibnizRectangleRawAtOneOverlapsUpToAll_of_cellBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelCellBoundsAtOneUpToAll) :
    LeibnizRectangleRawAtOneOverlapsUpToAll :=
  leibnizRectangleRawAtOneOverlapsUpToAll_of_kernelBoundsUpToAll
    (LeibnizRectangleBridge.kernelBoundsUpToAll_of_cellBoundsUpToAll h)

theorem leibnizRectangleRawAtOneOverlapsUpToAll_of_unitUniformCellBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOneUpToAll) :
    LeibnizRectangleRawAtOneOverlapsUpToAll :=
  leibnizRectangleRawAtOneOverlapsUpToAll_of_kernelBoundsUpToAll
    (LeibnizRectangleBridge.kernelBoundsUpToAll_of_unitUniformCellBoundsUpToAll h)

theorem leibnizEqualsRectangleRawAtOneSpecial_of_rawOverlapsUpToAll
    (h : LeibnizRectangleRawAtOneOverlapsUpToAll) :
    LeibnizEqualsRectangleRawAtOneSpecial := by
  unfold LeibnizEqualsRectangleRawAtOneSpecial
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    leibnizSeries ArctanGeometry.arctanIntegralRectangleRawAtOne n n).2
  exact h n n (Nat.le_refl n)

theorem rawOverlapsUpToAll_of_leibnizEqualsRectangleRawAtOneSpecial
    (h : LeibnizEqualsRectangleRawAtOneSpecial) :
    LeibnizRectangleRawAtOneOverlapsUpToAll := by
  intro N n _hn
  exact (RealRaw.compareAt_overlap_iff
    leibnizSeries ArctanGeometry.arctanIntegralRectangleRawAtOne n n).1
      (h n)

theorem leibnizEqualsRectangleRawAtOneSpecial_iff_rawOverlapsUpToAll :
    LeibnizEqualsRectangleRawAtOneSpecial ↔
      LeibnizRectangleRawAtOneOverlapsUpToAll := by
  constructor
  · exact rawOverlapsUpToAll_of_leibnizEqualsRectangleRawAtOneSpecial
  · exact leibnizEqualsRectangleRawAtOneSpecial_of_rawOverlapsUpToAll

theorem leibnizRectangleRawAtOneOverlapsUpToFifteen :
    LeibnizRectangleRawAtOneOverlapsUpTo 15 :=
  leibnizRectangleRawAtOneOverlapsUpTo_of_kernelBoundsUpTo
    LeibnizRectangleBridge.leibnizRectangleKernelBoundsAtOneUpToFifteen

theorem leibnizRectangleRawAtOneOverlapsUpToFourteen :
    LeibnizRectangleRawAtOneOverlapsUpTo 14 :=
  leibnizRectangleRawAtOneOverlapsUpTo_of_le
    (by native_decide : 14 <= 15)
    leibnizRectangleRawAtOneOverlapsUpToFifteen

theorem leibnizRectangleRawAtOneOverlapsUpToTwo :
    LeibnizRectangleRawAtOneOverlapsUpTo 2 :=
  leibnizRectangleRawAtOneOverlapsUpTo_of_kernelBoundsUpTo
    LeibnizRectangleBridge.leibnizRectangleKernelBoundsAtOneUpToTwo

theorem leibnizRectangleRawAtOneOverlapsUpToThree :
    LeibnizRectangleRawAtOneOverlapsUpTo 3 :=
  leibnizRectangleRawAtOneOverlapsUpTo_of_kernelBoundsUpTo
    LeibnizRectangleBridge.leibnizRectangleKernelBoundsAtOneUpToThree

theorem leibnizRectangleRawAtOneOverlapsUpToFour :
    LeibnizRectangleRawAtOneOverlapsUpTo 4 :=
  leibnizRectangleRawAtOneOverlapsUpTo_of_kernelBoundsUpTo
    LeibnizRectangleBridge.leibnizRectangleKernelBoundsAtOneUpToFour

theorem leibnizRectangleRawAtOneOverlapsUpToFive :
    LeibnizRectangleRawAtOneOverlapsUpTo 5 :=
  leibnizRectangleRawAtOneOverlapsUpTo_of_kernelBoundsUpTo
    LeibnizRectangleBridge.leibnizRectangleKernelBoundsAtOneUpToFive

theorem leibnizEqualsRectangleRawAtOneSpecial_of_kernelBounds
    (h : LeibnizRectangleKernelBoundsAtOne) :
    LeibnizEqualsRectangleRawAtOneSpecial := by
  unfold LeibnizEqualsRectangleRawAtOneSpecial
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    leibnizSeries ArctanGeometry.arctanIntegralRectangleRawAtOne n n).2
  rw [LeibnizValidity.leibnizSeries_compute_eq_kernelPartialIntegralInterval n]
  change QInterval.Overlaps
    { lo := LeibnizValidity.lowerKernelPartialAtStage n,
      hi := LeibnizValidity.upperKernelPartialAtStage n }
    (ArctanGeometry.arctanIntegralRectangleComputeAtOne n)
  exact ⟨(h n).2, (h n).1⟩

theorem leibnizEqualsRectangleRawAtOne_of_special
    (h : LeibnizEqualsRectangleRawAtOneSpecial) :
    LeibnizEqualsRectangleRawAtOne := by
  unfold LeibnizEqualsRectangleRawAtOne
  exact RealRaw.equiv_trans
    leibnizSeriesValid
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
    (ArctanGeometry.arctanIntegralRectangleRaw_valid
      (x := (1 : Rat)) (by native_decide) (by native_decide))
    h
    arctanIntegralRectangleRawAtOne_equiv_raw_one

theorem leibnizEqualsRectangleRawAtOne_of_rawOverlapsUpToAll
    (h : LeibnizRectangleRawAtOneOverlapsUpToAll) :
    LeibnizEqualsRectangleRawAtOne :=
  leibnizEqualsRectangleRawAtOne_of_special
    (leibnizEqualsRectangleRawAtOneSpecial_of_rawOverlapsUpToAll h)

theorem leibnizEqualsRectangleRawAtOne_of_kernelBounds
    (h : LeibnizRectangleKernelBoundsAtOne) :
    LeibnizEqualsRectangleRawAtOne :=
  leibnizEqualsRectangleRawAtOne_of_special
    (leibnizEqualsRectangleRawAtOneSpecial_of_kernelBounds h)

theorem leibnizEqualsRectangleRawAtOne_of_kernelBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelBoundsAtOneUpToAll) :
    LeibnizEqualsRectangleRawAtOne :=
  leibnizEqualsRectangleRawAtOne_of_kernelBounds
    (LeibnizRectangleBridge.kernelBounds_of_kernelBoundsUpToAll h)

theorem leibnizEqualsRectangleRawAtOne_of_cellBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelCellBoundsAtOneUpToAll) :
    LeibnizEqualsRectangleRawAtOne :=
  leibnizEqualsRectangleRawAtOne_of_kernelBounds
    (LeibnizRectangleBridge.kernelBounds_of_cellBoundsUpToAll h)

theorem leibnizEqualsRectangleRawAtOne_of_unitUniformCellBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOneUpToAll) :
    LeibnizEqualsRectangleRawAtOne :=
  leibnizEqualsRectangleRawAtOne_of_kernelBounds
    (LeibnizRectangleBridge.kernelBounds_of_unitUniformCellBoundsUpToAll h)

theorem leibnizEqualsRectangleRawAtOne_of_uniformCellBounds
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformCellBoundsAtOne) :
    LeibnizEqualsRectangleRawAtOne :=
  leibnizEqualsRectangleRawAtOne_of_kernelBounds
    (LeibnizRectangleBridge.kernelBounds_of_cellBounds
      (LeibnizRectangleBridge.cellBounds_of_uniformCellBounds h))

theorem leibnizEqualsRectangleRawAtOne_of_unitUniformCellBounds
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOne) :
    LeibnizEqualsRectangleRawAtOne :=
  leibnizEqualsRectangleRawAtOne_of_kernelBounds
    (LeibnizRectangleBridge.kernelBounds_of_cellBounds
      (LeibnizRectangleBridge.cellBounds_of_unitUniformCellBounds h))

theorem leibnizEqualsRectangleRawAtOne_of_pointwiseIntegralBridge
    (h : LeibnizRectangleBridge.LeibnizRectanglePointwiseIntegralBridgeAtOne) :
    LeibnizEqualsRectangleRawAtOne :=
  leibnizEqualsRectangleRawAtOne_of_kernelBounds
    (LeibnizRectangleBridge.kernelBounds_of_pointwiseIntegralBridge h)

theorem leibnizEqualsRectangleRawAtOne_of_pointwiseUnitIntegralBridge
    (h : LeibnizRectangleBridge.LeibnizRectanglePointwiseUnitIntegralBridgeAtOne) :
    LeibnizEqualsRectangleRawAtOne :=
  leibnizEqualsRectangleRawAtOne_of_kernelBounds
    (LeibnizRectangleBridge.kernelBounds_of_pointwiseUnitIntegralBridge h)

theorem leibnizEqualsRectangleRawAtOne_of_unitCellOrderPreservation
    (h : LeibnizRectangleBridge.LeibnizRectangleUnitCellOrderPreservation) :
    LeibnizEqualsRectangleRawAtOne :=
  leibnizEqualsRectangleRawAtOne_of_pointwiseUnitIntegralBridge
    (LeibnizRectangleBridge.pointwiseUnitIntegralBridgeAtOne_of_unitCellOrderPreservation
      h)

theorem special_of_leibnizEqualsRectangleRawAtOne
    (h : LeibnizEqualsRectangleRawAtOne) :
    LeibnizEqualsRectangleRawAtOneSpecial := by
  unfold LeibnizEqualsRectangleRawAtOneSpecial
  exact RealRaw.equiv_trans
    leibnizSeriesValid
    (ArctanGeometry.arctanIntegralRectangleRaw_valid
      (x := (1 : Rat)) (by native_decide) (by native_decide))
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
    h
    (RealRaw.equiv_symm arctanIntegralRectangleRawAtOne_equiv_raw_one)

theorem powerSeriesEqualsRectangleKernelAtOne_of_leibnizEqualsRectangleRawAtOne
    (h : LeibnizEqualsRectangleRawAtOne) :
    PowerSeriesEqualsRectangleKernelAtOne := by
  unfold PowerSeriesEqualsRectangleKernelAtOne
  unfold PowerSeriesEqualsRectangleKernelAt
  have hArctanValid : (arctan (1 : Rat)).Valid :=
    arctan_valid_at arctanValid arctan_one_mem_domain
  have hRectValid :
      (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)).Valid :=
    ArctanGeometry.arctanIntegralRectangleRaw_valid
      (x := (1 : Rat)) (by native_decide) (by native_decide)
  have hKernelValid :
      (Taylor.ArctanComparison.kernelIntegralRaw (1 : Rat)
        (rectangleKernelIntegralAtNonnegativeUnit
          (1 : Rat) (by native_decide) (by native_decide))).Valid :=
    Taylor.ArctanComparison.kernelIntegralRaw_valid (1 : Rat)
      (rectangleKernelIntegralAtNonnegativeUnit
        (1 : Rat) (by native_decide) (by native_decide))
  have hArctanLeibniz : (arctan (1 : Rat)).Equiv leibnizSeries :=
    RealRaw.equiv_symm leibnizSeries_equiv_arctan_one
  have hRectKernel :
      (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)).Equiv
        (Taylor.ArctanComparison.kernelIntegralRaw (1 : Rat)
          (rectangleKernelIntegralAtNonnegativeUnit
            (1 : Rat) (by native_decide) (by native_decide))) :=
    rectangleKernelIntegralRaw_equiv_rectangleRaw_nonnegativeUnit
      (1 : Rat) (by native_decide) (by native_decide)
  exact RealRaw.equiv_trans
    hArctanValid
    leibnizSeriesValid
    hKernelValid
    hArctanLeibniz
    (RealRaw.equiv_trans
      leibnizSeriesValid hRectValid hKernelValid h hRectKernel)

theorem leibnizEqualsRectangleRawAtOne_of_powerSeriesEqualsRectangleKernelAtOne
    (h : PowerSeriesEqualsRectangleKernelAtOne) :
    LeibnizEqualsRectangleRawAtOne := by
  unfold LeibnizEqualsRectangleRawAtOne
  unfold PowerSeriesEqualsRectangleKernelAtOne at h
  unfold PowerSeriesEqualsRectangleKernelAt at h
  have hArctanValid : (arctan (1 : Rat)).Valid :=
    arctan_valid_at arctanValid arctan_one_mem_domain
  have hKernelValid :
      (Taylor.ArctanComparison.kernelIntegralRaw (1 : Rat)
        (rectangleKernelIntegralAtNonnegativeUnit
          (1 : Rat) (by native_decide) (by native_decide))).Valid :=
    Taylor.ArctanComparison.kernelIntegralRaw_valid (1 : Rat)
      (rectangleKernelIntegralAtNonnegativeUnit
        (1 : Rat) (by native_decide) (by native_decide))
  have hRectValid :
      (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)).Valid :=
    ArctanGeometry.arctanIntegralRectangleRaw_valid
      (x := (1 : Rat)) (by native_decide) (by native_decide)
  have hLeibnizArctan : leibnizSeries.Equiv (arctan (1 : Rat)) :=
    leibnizSeries_equiv_arctan_one
  have hKernelRect :
      (Taylor.ArctanComparison.kernelIntegralRaw (1 : Rat)
        (rectangleKernelIntegralAtNonnegativeUnit
          (1 : Rat) (by native_decide) (by native_decide))).Equiv
        (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)) :=
    RealRaw.equiv_symm
      (rectangleKernelIntegralRaw_equiv_rectangleRaw_nonnegativeUnit
        (1 : Rat) (by native_decide) (by native_decide))
  exact RealRaw.equiv_trans
    leibnizSeriesValid
    hArctanValid
    hRectValid
    hLeibnizArctan
    (RealRaw.equiv_trans hArctanValid hKernelValid hRectValid h hKernelRect)

/-- The Leibniz series is equivalent to the Dirichlet L-value `L(1, chi4)`.

Here too the algorithms are stagewise equal, so equivalence is immediate. -/
theorem leibnizSeries_equiv_dirichletLChi4AtOne :
    leibnizSeries.Equiv DirichletSeries.dirichletLChi4AtOne := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hcompute :
      leibnizSeries.compute n =
        DirichletSeries.dirichletLChi4AtOne.compute n := by
    unfold leibnizSeries DirichletSeries.dirichletLChi4AtOne
    simp
  apply (RealRaw.compareAt_overlap_iff leibnizSeries
    DirichletSeries.dirichletLChi4AtOne n n).2
  rw [← hcompute]
  have hordered := LeibnizValidity.interval_ordered n
  rw [LeibnizValidity.leibnizSeries_compute_eq n]
  exact ⟨hordered, hordered⟩

theorem fourArctanOneValid :
    ((4 : Nat) * arctan (1 : Rat) : RealRaw).Valid :=
  RealRaw.natScale_valid 4
    (arctan_valid_at arctanValid arctan_one_mem_domain)

/-- Scoreboard-facing validity theorem for `4 * arctanSeries(1)`.

The implementation is the same power-series evaluator as `arctan`; the separate
name keeps it visually distinct from geometric and integral arctangent routes. -/
theorem fourArctanSeriesOneValid :
    ((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Valid := by
  simpa [arctanSeries] using fourArctanOneValid

/-- The Leibniz definition of pi is equivalent to `4 * arctan 1`. -/
theorem piLeibniz_equiv_four_arctan_one :
    piLeibniz.Equiv ((4 : Nat) * arctan (1 : Rat) : RealRaw) := by
  unfold piLeibniz
  exact RealRaw.natScale_equiv 4 leibnizSeries_equiv_arctan_one

/-- The legacy `piLeibniz` raw real is the scoreboard row
`4 * arctanSeries(1)`. -/
theorem piLeibniz_equiv_four_arctanSeries_one :
    piLeibniz.Equiv ((4 : Nat) * arctanSeries (1 : Rat) : RealRaw) := by
  simpa [arctanSeries] using piLeibniz_equiv_four_arctan_one

/-- Stagewise equality between the Leibniz pi computation and
`4 * arctan(1)`. -/
theorem piLeibniz_compute_eq_four_arctan_one (n : Nat) :
    piLeibniz.compute n =
      (((4 : Nat) * arctan (1 : Rat) : RealRaw).compute n) := by
  unfold piLeibniz
  change
    (RealRaw.scaleRat (4 : Rat) leibnizSeries).compute n =
      (RealRaw.scaleRat (4 : Rat) (arctan (1 : Rat))).compute n
  simp [RealRaw.scaleRat, RealRaw.scaleRatCompute,
    (by native_decide : (0 : Rat) <= 4),
    leibnizSeries_compute_eq_arctan_one n]

/-- Stagewise equality between the legacy Leibniz pi computation and the
scoreboard expression `4 * arctanSeries(1)`. -/
theorem piLeibniz_compute_eq_four_arctanSeries_one (n : Nat) :
    piLeibniz.compute n =
      (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).compute n) := by
  simpa [arctanSeries] using piLeibniz_compute_eq_four_arctan_one n

def FourArctanSeriesRectangleRouteOverlapsUpTo (N : Nat) : Prop :=
  forall n, n <= N ->
    QInterval.Overlaps
      (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).compute n)
      (((4 : Nat) *
        ArctanGeometry.arctanIntegralRectangleRawAtOne : RealRaw).compute n)

def FourArctanSeriesRectangleRouteOverlapsUpToAll : Prop :=
  forall N, FourArctanSeriesRectangleRouteOverlapsUpTo N

theorem fourArctanSeriesRectangleRouteOverlapsUpTo_of_le
    {M N : Nat} (hMN : M <= N)
    (h : FourArctanSeriesRectangleRouteOverlapsUpTo N) :
    FourArctanSeriesRectangleRouteOverlapsUpTo M := by
  intro n hn
  exact h n (Nat.le_trans hn hMN)

theorem fourArctanSeriesRectangleRouteOverlapsUpTo_of_leibnizRectangleRaw
    {N : Nat} (h : LeibnizRectangleRawAtOneOverlapsUpTo N) :
    FourArctanSeriesRectangleRouteOverlapsUpTo N := by
  intro n hn
  have hraw := h n hn
  rw [← piLeibniz_compute_eq_four_arctanSeries_one n]
  change QInterval.Overlaps
    ((RealRaw.scaleRat (4 : Rat) leibnizSeries).compute n)
    ((RealRaw.scaleRat (4 : Rat)
      ArctanGeometry.arctanIntegralRectangleRawAtOne).compute n)
  unfold RealRaw.scaleRat RealRaw.scaleRatCompute
  simp [(by native_decide : (0 : Rat) <= 4), QInterval.Overlaps]
  exact
    ⟨Rat.mul_le_mul_of_nonneg_left hraw.1
        (by native_decide : (0 : Rat) <= 4),
      Rat.mul_le_mul_of_nonneg_left hraw.2
        (by native_decide : (0 : Rat) <= 4)⟩

theorem fourArctanSeriesRectangleRouteOverlapsUpTo_of_kernelBoundsUpTo
    {N : Nat}
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelBoundsAtOneUpTo N) :
    FourArctanSeriesRectangleRouteOverlapsUpTo N :=
  fourArctanSeriesRectangleRouteOverlapsUpTo_of_leibnizRectangleRaw
    (leibnizRectangleRawAtOneOverlapsUpTo_of_kernelBoundsUpTo h)

theorem fourArctanSeriesRectangleRouteOverlapsUpTo_of_cellBoundsUpTo
    {N : Nat}
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelCellBoundsAtOneUpTo N) :
    FourArctanSeriesRectangleRouteOverlapsUpTo N :=
  fourArctanSeriesRectangleRouteOverlapsUpTo_of_kernelBoundsUpTo
    (LeibnizRectangleBridge.kernelBoundsUpTo_of_cellBoundsUpTo h)

theorem fourArctanSeriesRectangleRouteOverlapsUpTo_of_unitUniformCellBoundsUpTo
    {N : Nat}
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N) :
    FourArctanSeriesRectangleRouteOverlapsUpTo N :=
  fourArctanSeriesRectangleRouteOverlapsUpTo_of_leibnizRectangleRaw
    (leibnizRectangleRawAtOneOverlapsUpTo_of_unitUniformCellBoundsUpTo h)

theorem fourArctanSeriesRectangleRouteOverlapsUpToAll_of_leibnizRectangleRaw
    (h : LeibnizRectangleRawAtOneOverlapsUpToAll) :
    FourArctanSeriesRectangleRouteOverlapsUpToAll := by
  intro N
  exact fourArctanSeriesRectangleRouteOverlapsUpTo_of_leibnizRectangleRaw
    (h N)

theorem fourArctanSeriesRectangleRouteOverlapsUpToAll_of_kernelBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelBoundsAtOneUpToAll) :
    FourArctanSeriesRectangleRouteOverlapsUpToAll :=
  fourArctanSeriesRectangleRouteOverlapsUpToAll_of_leibnizRectangleRaw
    (leibnizRectangleRawAtOneOverlapsUpToAll_of_kernelBoundsUpToAll h)

theorem fourArctanSeriesRectangleRouteOverlapsUpToAll_of_cellBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelCellBoundsAtOneUpToAll) :
    FourArctanSeriesRectangleRouteOverlapsUpToAll :=
  fourArctanSeriesRectangleRouteOverlapsUpToAll_of_leibnizRectangleRaw
    (leibnizRectangleRawAtOneOverlapsUpToAll_of_cellBoundsUpToAll h)

theorem fourArctanSeriesRectangleRouteOverlapsUpToAll_of_unitUniformCellBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOneUpToAll) :
    FourArctanSeriesRectangleRouteOverlapsUpToAll :=
  fourArctanSeriesRectangleRouteOverlapsUpToAll_of_leibnizRectangleRaw
    (leibnizRectangleRawAtOneOverlapsUpToAll_of_unitUniformCellBoundsUpToAll h)

theorem fourArctanSeriesRectangleRouteOverlapsUpToFive_of_unitUniform :
    FourArctanSeriesRectangleRouteOverlapsUpTo 5 :=
  fourArctanSeriesRectangleRouteOverlapsUpTo_of_unitUniformCellBoundsUpTo
    LeibnizRectangleBridge.leibnizRectangleUniformUnitCellBoundsAtOneUpToFive

theorem fourArctanSeriesRectangleRouteOverlapsUpToFifteen :
    FourArctanSeriesRectangleRouteOverlapsUpTo 15 :=
  fourArctanSeriesRectangleRouteOverlapsUpTo_of_leibnizRectangleRaw
    leibnizRectangleRawAtOneOverlapsUpToFifteen

theorem fourArctanSeriesRectangleRouteOverlapsUpToFourteen :
    FourArctanSeriesRectangleRouteOverlapsUpTo 14 :=
  fourArctanSeriesRectangleRouteOverlapsUpTo_of_le
    (by native_decide : 14 <= 15)
    fourArctanSeriesRectangleRouteOverlapsUpToFifteen

namespace MachinIdentity

def gaussian (re im : Rat) : QComplex :=
  { re := re, im := im }

def gaussianPow : QComplex -> Nat -> QComplex
  | _, 0 => QComplex.one
  | z, n + 1 => QComplex.mul (gaussianPow z n) z

def addDen (x y : Rat) : Rat := 1 - x * y
def addSlope (x y : Rat) : Rat := (x + y) / addDen x y

def subDen (x y : Rat) : Rat := 1 + x * y
def subSlope (x y : Rat) : Rat := (x - y) / subDen x y

def tanDoubleDen (x : Rat) : Rat := addDen x x
def tanDouble (x : Rat) : Rat := addSlope x x

def tanSubDen (x y : Rat) : Rat := subDen x y
def tanSub (x y : Rat) : Rat := subSlope x y

def tanFour (x : Rat) : Rat := tanDouble (tanDouble x)

def HasSlope (z : QComplex) (x : Rat) : Prop :=
  0 < z.re /\ z.im = x * z.re

def conj (z : QComplex) : QComplex :=
  { re := z.re, im := -z.im }

/-- Exact Gaussian-rational identity behind Machin's formula:
`(5 + i)^4 = (2 + 2i) * (239 + i)`. -/
theorem gaussian_identity :
    gaussianPow (gaussian 5 1) 4 =
      QComplex.mul (gaussian 2 2) (gaussian 239 1) := by
  native_decide

/-- If `tan a = 1/5`, the rational tangent-doubling formula gives
`tan (4a) = 120/119`. -/
theorem tanFour_one_fifth :
    tanFour (1 / 5) = 120 / 119 := by
  native_decide

theorem tanDoubleDen_one_fifth_positive :
    0 < tanDoubleDen (1 / 5) := by
  native_decide

theorem tanDoubleDen_five_twelfths_positive :
    0 < tanDoubleDen (5 / 12) := by
  native_decide

theorem tanSubDen_machin_positive :
    0 < tanSubDen (120 / 119) (1 / 239) := by
  native_decide

/-- The Gaussian identity, after subtracting the argument of `239 + i`, says
that the resulting rational complex vector has slope `1`. -/
theorem gaussian_identity_subtract_slope :
    HasSlope
      (QComplex.mul (gaussianPow (gaussian 5 1) 4)
        (conj (gaussian 239 1))) 1 := by
  rw [gaussian_identity]
  change 0 <
      (QComplex.mul (QComplex.mul (gaussian 2 2) (gaussian 239 1))
        (conj (gaussian 239 1))).re /\
    (QComplex.mul (QComplex.mul (gaussian 2 2) (gaussian 239 1))
        (conj (gaussian 239 1))).im =
      1 * (QComplex.mul (QComplex.mul (gaussian 2 2) (gaussian 239 1))
        (conj (gaussian 239 1))).re
  native_decide

/-- Exact rational tangent identity behind Machin's formula:
`tan (4 atan(1/5) - atan(1/239)) = 1`.

The concrete raw-arctangent branch identity is now supplied below by bounded
rational chart transport; this tangent calculation remains its independent
algebraic certificate. -/
theorem quarter_tangent_identity :
    tanSub (tanFour (1 / 5)) (1 / 239) = 1 := by
  native_decide

theorem projective_tanFour_one_fifth :
    RationalCircle.ProjectiveRat.tanDouble
      (RationalCircle.ProjectiveRat.tanDouble
        (RationalCircle.ProjectiveRat.finite ((1 : Rat) / 5))) =
      RationalCircle.ProjectiveRat.finite ((120 : Rat) / 119) := by
  native_decide

theorem projective_quarter_tangent_identity :
    RationalCircle.ProjectiveRat.tanSub
      (RationalCircle.ProjectiveRat.tanDouble
        (RationalCircle.ProjectiveRat.tanDouble
          (RationalCircle.ProjectiveRat.finite ((1 : Rat) / 5))))
      (RationalCircle.ProjectiveRat.finite ((1 : Rat) / 239)) =
      RationalCircle.ProjectiveRat.finite 1 := by
  native_decide

def BranchIdentity : Prop :=
  ((4 : Nat) * arctan ((1 : Rat) / 5) - arctan ((1 : Rat) / 239)).Equiv
    (arctan (1 : Rat))

def GeometricBranchIdentity : Prop :=
  ((4 : Nat) * ArctanGeometry.arctanGeom ((1 : Rat) / 5) -
      ArctanGeometry.arctanGeom ((1 : Rat) / 239)).Equiv
    (ArctanGeometry.arctanGeom (1 : Rat))

/-- Generic principal-branch API for a tangent proof.

The concrete Machin instance is later proved without assuming this universal
law, by decomposing it into three bounded chart additions. -/
def BranchLaw : Prop :=
  tanSub (tanFour (1 / 5)) (1 / 239) = 1 -> BranchIdentity

/-- The geometric branch theorem has the same tangent premise, but concludes
the identity for sector-area arctangent instead of the power-series
arctangent. -/
def GeometricBranchLaw : Prop :=
  tanSub (tanFour (1 / 5)) (1 / 239) = 1 -> GeometricBranchIdentity

/-- Principal-branch addition for the geometric arctangent, restricted to
rational unit-chart inputs whose rational tangent sum stays in that chart.

This is the exact analytic input needed by the bounded Machin decomposition
below; it is deliberately stated without any completed-real trigonometry. -/
def GeometricUnitAdditionLaw : Prop :=
  forall x y z : Rat,
    0 <= x -> x <= 1 ->
    0 <= y -> y <= 1 ->
    0 <= z -> z <= 1 ->
    z = addSlope x y ->
    (ArctanGeometry.arctanGeom x + ArctanGeometry.arctanGeom y).Equiv
      (ArctanGeometry.arctanGeom z)

/-- The three bounded principal-branch additions that are exactly sufficient
for Machin's formula. -/
structure GeometricMachinUnitAdditions where
  double_one_fifth :
    (ArctanGeometry.arctanGeom ((1 : Rat) / 5) +
      ArctanGeometry.arctanGeom ((1 : Rat) / 5)).Equiv
      (ArctanGeometry.arctanGeom ((5 : Rat) / 12))
  seven_seventeenths_add_one_239 :
    (ArctanGeometry.arctanGeom ((7 : Rat) / 17) +
      ArctanGeometry.arctanGeom ((1 : Rat) / 239)).Equiv
      (ArctanGeometry.arctanGeom ((5 : Rat) / 12))
  five_twelfths_add_seven_seventeenths :
    (ArctanGeometry.arctanGeom ((5 : Rat) / 12) +
      ArctanGeometry.arctanGeom ((7 : Rat) / 17)).Equiv
      (ArctanGeometry.arctanGeom (1 : Rat))

/-- A universal bounded addition law supplies the three Machin instances. -/
def geometricMachinUnitAdditions_of_unitAdditionLaw
    (hadd : GeometricUnitAdditionLaw) : GeometricMachinUnitAdditions where
  double_one_fifth :=
    hadd ((1 : Rat) / 5) ((1 : Rat) / 5) ((5 : Rat) / 12)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide)
  seven_seventeenths_add_one_239 :=
    hadd ((7 : Rat) / 17) ((1 : Rat) / 239) ((5 : Rat) / 12)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide)
  five_twelfths_add_seven_seventeenths :=
    hadd ((5 : Rat) / 12) ((7 : Rat) / 17) (1 : Rat)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide)

/-- The three bounded additions needed by Machin follow directly from the
verified rational chart transport for geometric arctangent. -/
theorem geometricMachinUnitAdditions_of_chartTransport :
    GeometricMachinUnitAdditions where
  double_one_fifth := by
    have h := ArctanGeometry.arctanGeom_chartAdd_add_of_half
      (u := (1 : Rat) / 5) (x := (1 : Rat) / 5)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    have hparam :
        RationalCircle.Trigonometry.chartAddParameter
          ((1 : Rat) / 5) ((1 : Rat) / 5) = (5 : Rat) / 12 := by
      native_decide
    rw [hparam] at h
    exact h
  seven_seventeenths_add_one_239 := by
    have h := ArctanGeometry.arctanGeom_chartAdd_add_of_half
      (u := (7 : Rat) / 17) (x := (1 : Rat) / 239)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    have hparam :
        RationalCircle.Trigonometry.chartAddParameter
          ((7 : Rat) / 17) ((1 : Rat) / 239) = (5 : Rat) / 12 := by
      native_decide
    rw [hparam] at h
    exact h
  five_twelfths_add_seven_seventeenths := by
    have h := ArctanGeometry.arctanGeom_chartAdd_add_of_half
      (u := (5 : Rat) / 12) (x := (7 : Rat) / 17)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    have hparam :
        RationalCircle.Trigonometry.chartAddParameter
          ((5 : Rat) / 12) ((7 : Rat) / 17) = (1 : Rat) := by
      native_decide
    rw [hparam] at h
    exact h

structure PowerSeriesGeometryAtMachinInputs where
  one_fifth :
    (arctan ((1 : Rat) / 5)).Equiv
      (ArctanGeometry.arctanGeom ((1 : Rat) / 5))
  one_239 :
    (arctan ((1 : Rat) / 239)).Equiv
      (ArctanGeometry.arctanGeom ((1 : Rat) / 239))
  one :
    (arctan (1 : Rat)).Equiv (ArctanGeometry.arctanGeom (1 : Rat))

/-- The two power-series/geometric agreements used by the Machin evaluator
itself.  Unlike the separate Leibniz route, this data does not mention the
endpoint input `1`. -/
structure PowerSeriesGeometryAtMachinSmallInputs where
  one_fifth :
    (arctan ((1 : Rat) / 5)).Equiv
      (ArctanGeometry.arctanGeom ((1 : Rat) / 5))
  one_239 :
    (arctan ((1 : Rat) / 239)).Equiv
      (ArctanGeometry.arctanGeom ((1 : Rat) / 239))

structure KernelComparisonAtMachinInputs where
  one_fifth : Taylor.ArctanComparison.KernelComparisonAt ((1 : Rat) / 5)
  one_239 : Taylor.ArctanComparison.KernelComparisonAt ((1 : Rat) / 239)
  one : Taylor.ArctanComparison.KernelComparisonAt (1 : Rat)

/-- The two kernel comparisons needed by the direct Machin-to-area route.
The endpoint comparison at `1` is deliberately excluded: it is only needed
when routing Machin through Leibniz. -/
structure KernelComparisonAtMachinSmallInputs where
  one_fifth : Taylor.ArctanComparison.KernelComparisonAt ((1 : Rat) / 5)
  one_239 : Taylor.ArctanComparison.KernelComparisonAt ((1 : Rat) / 239)

structure PowerSeriesEqualsRectangleKernelAtMachinInputs where
  one_fifth :
    PowerSeriesEqualsRectangleKernelAt
      ((1 : Rat) / 5) (by native_decide) (by native_decide)
  one_239 :
    PowerSeriesEqualsRectangleKernelAt
      ((1 : Rat) / 239) (by native_decide) (by native_decide)
  one : PowerSeriesEqualsRectangleKernelAtOne

def kernelComparisonAtMachinInputs_of_powerSeriesEqualsRectangleKernelAtMachinInputs
    (hps : PowerSeriesEqualsRectangleKernelAtMachinInputs) :
    KernelComparisonAtMachinInputs where
  one_fifth :=
    kernelComparisonAt_of_powerSeriesEqualsRectangleKernelAt hps.one_fifth
  one_239 :=
    kernelComparisonAt_of_powerSeriesEqualsRectangleKernelAt hps.one_239
  one :=
    kernelComparisonAtOne_of_powerSeriesEqualsRectangleKernelAtOne hps.one

theorem branchIdentity_of_branchLaw (h : BranchLaw) : BranchIdentity :=
  h quarter_tangent_identity

theorem geometricBranchIdentity_of_geometricBranchLaw
    (h : GeometricBranchLaw) : GeometricBranchIdentity :=
  h quarter_tangent_identity

/-- Three rational unit-chart additions suffice for Machin's principal branch.

The potentially awkward intermediate slope `120/119` never appears as an
argument of the geometric arctangent.  Instead, the proof factors the identity
through the unit-chart values `5/12` and `7/17`:
`2 atan(1/5) = atan(5/12)`,
`atan(7/17) + atan(1/239) = atan(5/12)`, and
`atan(5/12) + atan(7/17) = atan(1)`.
All of these are bounded rational addition instances. -/
theorem geometricBranchIdentity_of_machinUnitAdditions
    (hadd : GeometricMachinUnitAdditions) : GeometricBranchIdentity := by
  let A : RealRaw := ArctanGeometry.arctanGeom ((1 : Rat) / 5)
  let B : RealRaw := ArctanGeometry.arctanGeom ((5 : Rat) / 12)
  let C : RealRaw := ArctanGeometry.arctanGeom ((7 : Rat) / 17)
  let D : RealRaw := ArctanGeometry.arctanGeom ((1 : Rat) / 239)
  let E : RealRaw := ArctanGeometry.arctanGeom (1 : Rat)
  have hA : A.Valid := by
    dsimp [A]
    exact ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hB : B.Valid := by
    dsimp [B]
    exact ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hC : C.Valid := by
    dsimp [C]
    exact ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hD : D.Valid := by
    dsimp [D]
    exact ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hE : E.Valid := by
    dsimp [E]
    exact ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hAA : (A + A).Equiv B := by
    simpa [A, B] using hadd.double_one_fifth
  have hCD : (C + D).Equiv B := by
    simpa [B, C, D] using hadd.seven_seventeenths_add_one_239
  have hBC : (B + C).Equiv E := by
    simpa [B, C, E] using hadd.five_twelfths_add_seven_seventeenths
  have hAAvalid : (A + A).Valid := RealRaw.add_valid hA hA
  have hCDvalid : (C + D).Valid := RealRaw.add_valid hC hD
  have hBBvalid : (B + B).Valid := RealRaw.add_valid hB hB
  have hB_CDvalid : (B + (C + D)).Valid := RealRaw.add_valid hB hCDvalid
  have hBCvalid : (B + C).Valid := RealRaw.add_valid hB hC
  have hBC_Dvalid : ((B + C) + D).Valid := RealRaw.add_valid hBCvalid hD
  have htwoA : ((2 : Nat) * A).Equiv (A + A) :=
    RealRaw.two_natscale_equiv_add_self A hA
  have htwoAvalid : ((2 : Nat) * A).Valid :=
    RealRaw.natScale_valid 2 hA
  have htwoAs :
      (((2 : Nat) * A) + ((2 : Nat) * A)).Equiv ((A + A) + (A + A)) :=
    RealRaw.add_equiv htwoAvalid hAAvalid htwoAvalid hAAvalid htwoA htwoA
  have hfourA_split :
      ((4 : Nat) * A).Equiv ((A + A) + (A + A)) :=
    RealRaw.equiv_trans
      (RealRaw.natScale_valid 4 hA)
      (RealRaw.add_valid htwoAvalid htwoAvalid)
      (RealRaw.add_valid hAAvalid hAAvalid)
      (RealRaw.four_natscale_equiv_add_two_natscale A hA)
      htwoAs
  have hfourA_BB : ((4 : Nat) * A).Equiv (B + B) :=
    RealRaw.equiv_trans
      (RealRaw.natScale_valid 4 hA)
      (RealRaw.add_valid hAAvalid hAAvalid) hBBvalid
      hfourA_split
      (RealRaw.add_equiv hAAvalid hB hAAvalid hB hAA hAA)
  have hBB_BCD : (B + B).Equiv (B + (C + D)) :=
    RealRaw.add_equiv hB hB hB hCDvalid
      (RealRaw.equiv_refl B hB) (RealRaw.equiv_symm hCD)
  have hBCD_assoc : (B + (C + D)).Equiv ((B + C) + D) :=
    RealRaw.equiv_symm (RealRaw.add_assoc_equiv B C D hB hC hD)
  have hDrefl : D.Equiv D := RealRaw.equiv_refl D hD
  have hBBminus_BCDminus :
      (B + B - D).Equiv (B + (C + D) - D) :=
    RealRaw.sub_equiv hBBvalid hB_CDvalid hD hD hBB_BCD hDrefl
  have hBCDminus_assocminus :
      (B + (C + D) - D).Equiv ((B + C) + D - D) :=
    RealRaw.sub_equiv hB_CDvalid hBC_Dvalid hD hD hBCD_assoc hDrefl
  have hBBminus_E : (B + B - D).Equiv E :=
    RealRaw.equiv_trans
      (RealRaw.sub_valid hBBvalid hD)
      (RealRaw.sub_valid hB_CDvalid hD)
      hE hBBminus_BCDminus
      (RealRaw.equiv_trans
        (RealRaw.sub_valid hB_CDvalid hD)
        (RealRaw.sub_valid hBC_Dvalid hD)
        hE hBCDminus_assocminus
        (RealRaw.equiv_trans
          (RealRaw.sub_valid hBC_Dvalid hD) hBCvalid hE
          (RealRaw.add_sub_cancel_right_equiv hBCvalid hD) hBC))
  have hfinal :
      ((4 : Nat) * A - D).Equiv E :=
    RealRaw.equiv_trans
      (RealRaw.sub_valid (RealRaw.natScale_valid 4 hA) hD)
      (RealRaw.sub_valid hBBvalid hD) hE
      (RealRaw.sub_equiv
        (RealRaw.natScale_valid 4 hA) hBBvalid hD hD hfourA_BB hDrefl)
      hBBminus_E
  simpa [A, D, E] using hfinal

/-- The universal unit-addition law proves Machin's three exact bounded
addition instances, hence its geometric branch identity. -/
theorem geometricBranchIdentity_of_unitAdditionLaw
    (hadd : GeometricUnitAdditionLaw) : GeometricBranchIdentity :=
  geometricBranchIdentity_of_machinUnitAdditions
    (geometricMachinUnitAdditions_of_unitAdditionLaw hadd)

/-- The exact three Machin unit additions imply the geometric branch law. -/
theorem geometricBranchLaw_of_machinUnitAdditions
    (hadd : GeometricMachinUnitAdditions) : GeometricBranchLaw :=
  fun _ => geometricBranchIdentity_of_machinUnitAdditions hadd

/-- Machin's geometric branch identity, with its three bounded additions
discharged by the certified tangent-chart transport. -/
theorem geometricBranchIdentity_of_chartTransport : GeometricBranchIdentity :=
  geometricBranchIdentity_of_machinUnitAdditions
    geometricMachinUnitAdditions_of_chartTransport

theorem geometricBranchLaw_of_chartTransport : GeometricBranchLaw :=
  geometricBranchLaw_of_machinUnitAdditions
    geometricMachinUnitAdditions_of_chartTransport

/-- The bounded unit-addition law implies the existing geometric Machin branch
law, with the rational tangent premise discharged separately. -/
theorem geometricBranchLaw_of_unitAdditionLaw
    (hadd : GeometricUnitAdditionLaw) : GeometricBranchLaw :=
  geometricBranchLaw_of_machinUnitAdditions
    (geometricMachinUnitAdditions_of_unitAdditionLaw hadd)

theorem powerSeriesGeometryAtMachinInputs_of_agreement
    (h : ArctanGeometry.PowerSeriesAgreesOnUnit) :
    PowerSeriesGeometryAtMachinInputs where
  one_fifth :=
    ArctanGeometry.powerSeries_equiv_geometric_of_agreement h
      (by unfold Elementary.Arctan.powerSeriesDomain qabs; native_decide)
  one_239 :=
    ArctanGeometry.powerSeries_equiv_geometric_of_agreement h
      (by unfold Elementary.Arctan.powerSeriesDomain qabs; native_decide)
  one :=
    ArctanGeometry.powerSeries_equiv_geometric_of_agreement h
      (by unfold Elementary.Arctan.powerSeriesDomain qabs; native_decide)

theorem powerSeriesGeometryAtMachinInputs_of_kernelComparisonAtMachinInputs
    (route : KernelComparisonAtMachinInputs) :
    PowerSeriesGeometryAtMachinInputs where
  one_fifth :=
    Taylor.ArctanComparison.powerSeriesAgreesAt_of_kernelComparisonAt
      route.one_fifth
  one_239 :=
    Taylor.ArctanComparison.powerSeriesAgreesAt_of_kernelComparisonAt
      route.one_239
  one :=
    Taylor.ArctanComparison.powerSeriesAgreesAt_of_kernelComparisonAt
      route.one

theorem powerSeriesGeometryAtMachinSmallInputs_of_kernelComparisonAtMachinSmallInputs
    (route : KernelComparisonAtMachinSmallInputs) :
    PowerSeriesGeometryAtMachinSmallInputs where
  one_fifth :=
    Taylor.ArctanComparison.powerSeriesAgreesAt_of_kernelComparisonAt
      route.one_fifth
  one_239 :=
    Taylor.ArctanComparison.powerSeriesAgreesAt_of_kernelComparisonAt
      route.one_239

theorem branchIdentity_of_geometricBranchIdentity_at_inputs
    (hg15 : (ArctanGeometry.arctanGeom ((1 : Rat) / 5)).Valid)
    (hg239 : (ArctanGeometry.arctanGeom ((1 : Rat) / 239)).Valid)
    (hg1 : (ArctanGeometry.arctanGeom (1 : Rat)).Valid)
    (hagree : PowerSeriesGeometryAtMachinInputs)
    (hgeom : GeometricBranchIdentity) : BranchIdentity := by
  have hps15 : (arctan ((1 : Rat) / 5)).Valid :=
    arctan_valid_at arctanValid arctan_one_fifth_mem_domain
  have hps239 : (arctan ((1 : Rat) / 239)).Valid :=
    arctan_valid_at arctanValid arctan_one_239_mem_domain
  have hps1 : (arctan (1 : Rat)).Valid :=
    arctan_valid_at arctanValid arctan_one_mem_domain
  have hps4_15 :
      ((4 : Nat) * arctan ((1 : Rat) / 5) : RealRaw).Valid :=
    RealRaw.natScale_valid 4 hps15
  have hg4_15 :
      ((4 : Nat) * ArctanGeometry.arctanGeom ((1 : Rat) / 5) : RealRaw).Valid :=
    RealRaw.natScale_valid 4 hg15
  have hpsExpr :
      ((4 : Nat) * arctan ((1 : Rat) / 5) -
        arctan ((1 : Rat) / 239) : RealRaw).Valid :=
    RealRaw.sub_valid hps4_15 hps239
  have hgExpr :
      ((4 : Nat) * ArctanGeometry.arctanGeom ((1 : Rat) / 5) -
        ArctanGeometry.arctanGeom ((1 : Rat) / 239) : RealRaw).Valid :=
    RealRaw.sub_valid hg4_15 hg239
  have hleft :
      ((4 : Nat) * arctan ((1 : Rat) / 5) -
        arctan ((1 : Rat) / 239) : RealRaw).Equiv
      ((4 : Nat) * ArctanGeometry.arctanGeom ((1 : Rat) / 5) -
        ArctanGeometry.arctanGeom ((1 : Rat) / 239) : RealRaw) :=
    RealRaw.sub_equiv
      hps4_15 hg4_15 hps239 hg239
      (RealRaw.natScale_equiv 4 hagree.one_fifth)
      hagree.one_239
  have htoGeomOne :
      ((4 : Nat) * arctan ((1 : Rat) / 5) -
        arctan ((1 : Rat) / 239) : RealRaw).Equiv
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
    RealRaw.equiv_trans
      hpsExpr hgExpr hg1 hleft hgeom
  exact RealRaw.equiv_trans
    hpsExpr hg1 hps1
    htoGeomOne
    (RealRaw.equiv_symm hagree.one)

theorem branchIdentity_of_geometricBranchIdentity
    (hGeomValid : ArctanGeometry.Valid)
    (hagree : PowerSeriesGeometryAtMachinInputs)
    (hgeom : GeometricBranchIdentity) : BranchIdentity := by
  have hg15 : (ArctanGeometry.arctanGeom ((1 : Rat) / 5)).Valid := by
    simpa [RealRaw.Valid, ArctanGeometry.functionRaw] using
      hGeomValid ((1 : Rat) / 5) (by trivial)
  have hg239 : (ArctanGeometry.arctanGeom ((1 : Rat) / 239)).Valid := by
    simpa [RealRaw.Valid, ArctanGeometry.functionRaw] using
      hGeomValid ((1 : Rat) / 239) (by trivial)
  have hg1 : (ArctanGeometry.arctanGeom (1 : Rat)).Valid := by
    simpa [RealRaw.Valid, ArctanGeometry.functionRaw] using
      hGeomValid (1 : Rat) (by trivial)
  exact branchIdentity_of_geometricBranchIdentity_at_inputs
    hg15 hg239 hg1 hagree hgeom

theorem branchIdentity_of_geometricBranchIdentity_on_unit
    (hagree : PowerSeriesGeometryAtMachinInputs)
    (hgeom : GeometricBranchIdentity) : BranchIdentity :=
  branchIdentity_of_geometricBranchIdentity_at_inputs
    (ArctanGeometry.arctanGeom_valid_on_unit
      (x := (1 : Rat) / 5) (by native_decide) (by native_decide))
    (ArctanGeometry.arctanGeom_valid_on_unit
      (x := (1 : Rat) / 239) (by native_decide) (by native_decide))
    (ArctanGeometry.arctanGeom_valid_on_unit
      (x := 1) (by native_decide) (by native_decide))
    hagree hgeom

theorem branchLaw_of_geometricBranchLaw
    (hGeomValid : ArctanGeometry.Valid)
    (hagree : PowerSeriesGeometryAtMachinInputs)
    (h : GeometricBranchLaw) : BranchLaw :=
  fun htangent =>
    branchIdentity_of_geometricBranchIdentity
      hGeomValid hagree (h htangent)

theorem branchLaw_of_geometricBranchLaw_on_unit
    (hagree : PowerSeriesGeometryAtMachinInputs)
    (h : GeometricBranchLaw) : BranchLaw :=
  fun htangent =>
    branchIdentity_of_geometricBranchIdentity_on_unit
      hagree (h htangent)

theorem piMachin_eq_four_arctan_one_of_branchIdentity
    (h : BranchIdentity) :
    piMachin.Equiv ((4 : Nat) * arctan (1 : Rat) : RealRaw) := by
  unfold piMachin
  exact RealRaw.natScale_equiv 4 h

theorem branchIdentity_of_piMachin_eq_four_arctan_one
    (h : piMachin.Equiv ((4 : Nat) * arctan (1 : Rat) : RealRaw)) :
    BranchIdentity := by
  unfold piMachin at h
  exact RealRaw.equiv_of_natScale_equiv
    (by omega : 0 < (4 : Nat)) h

theorem branchIdentity_iff_piMachin_eq_four_arctan_one :
    BranchIdentity ↔
      piMachin.Equiv ((4 : Nat) * arctan (1 : Rat) : RealRaw) :=
  ⟨piMachin_eq_four_arctan_one_of_branchIdentity,
    branchIdentity_of_piMachin_eq_four_arctan_one⟩

theorem piMachin_eq_four_arctanSeries_one_of_branchIdentity
    (h : BranchIdentity) :
    piMachin.Equiv ((4 : Nat) * arctanSeries (1 : Rat) : RealRaw) := by
  simpa [arctanSeries] using piMachin_eq_four_arctan_one_of_branchIdentity h

theorem branchIdentity_of_piMachin_eq_four_arctanSeries_one
    (h : piMachin.Equiv ((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :
    BranchIdentity :=
  branchIdentity_of_piMachin_eq_four_arctan_one (by
    simpa [arctanSeries] using h)

theorem branchIdentity_iff_piMachin_eq_four_arctanSeries_one :
    BranchIdentity ↔
      piMachin.Equiv ((4 : Nat) * arctanSeries (1 : Rat) : RealRaw) :=
  ⟨piMachin_eq_four_arctanSeries_one_of_branchIdentity,
    branchIdentity_of_piMachin_eq_four_arctanSeries_one⟩

end MachinIdentity

theorem leibnizEqMachin_of_machinBranchIdentity
    (h : MachinIdentity.BranchIdentity) : LeibnizEqMachin := by
  have hmachin :
      piMachin.Equiv ((4 : Nat) * arctan (1 : Rat) : RealRaw) :=
    MachinIdentity.piMachin_eq_four_arctan_one_of_branchIdentity h
  exact RealRaw.equiv_trans
    (x := piLeibniz) (y := ((4 : Nat) * arctan (1 : Rat) : RealRaw))
    (z := piMachin)
    leibnizValid fourArctanOneValid machinValid
    piLeibniz_equiv_four_arctan_one
    (RealRaw.equiv_symm hmachin)

theorem machinBranchIdentity_of_leibnizEqMachin
    (h : LeibnizEqMachin) : MachinIdentity.BranchIdentity := by
  have hmachin :
      piMachin.Equiv ((4 : Nat) * arctan (1 : Rat) : RealRaw) :=
    RealRaw.equiv_trans
      machinValid leibnizValid fourArctanOneValid
      (RealRaw.equiv_symm h)
      piLeibniz_equiv_four_arctan_one
  exact MachinIdentity.branchIdentity_of_piMachin_eq_four_arctan_one hmachin

theorem leibnizEqMachin_iff_machinBranchIdentity :
    LeibnizEqMachin ↔ MachinIdentity.BranchIdentity :=
  ⟨machinBranchIdentity_of_leibnizEqMachin,
    leibnizEqMachin_of_machinBranchIdentity⟩

theorem leibnizEqMachin_of_machinBranchLaw
    (h : MachinIdentity.BranchLaw) : LeibnizEqMachin :=
  leibnizEqMachin_of_machinBranchIdentity
    (MachinIdentity.branchIdentity_of_branchLaw h)

theorem leibnizEqMachin_of_geometricRoute
    (hGeomValid : ArctanGeometry.Valid)
    (hagree : MachinIdentity.PowerSeriesGeometryAtMachinInputs)
    (hgeom : MachinIdentity.GeometricBranchLaw) : LeibnizEqMachin :=
  leibnizEqMachin_of_machinBranchLaw
    (MachinIdentity.branchLaw_of_geometricBranchLaw
      hGeomValid hagree hgeom)

theorem leibnizEqMachin_of_geometricRoute_on_unit
    (hagree : MachinIdentity.PowerSeriesGeometryAtMachinInputs)
    (hgeom : MachinIdentity.GeometricBranchLaw) : LeibnizEqMachin :=
  leibnizEqMachin_of_machinBranchLaw
    (MachinIdentity.branchLaw_of_geometricBranchLaw_on_unit
      hagree hgeom)

/-- The bounded unit-addition formulation is sufficient for the geometric
Machin route; no out-of-chart arctangent value is required. -/
theorem leibnizEqMachin_of_machinUnitAdditions
    (hagree : MachinIdentity.PowerSeriesGeometryAtMachinInputs)
    (hadd : MachinIdentity.GeometricMachinUnitAdditions) : LeibnizEqMachin :=
  leibnizEqMachin_of_geometricRoute_on_unit hagree
    (MachinIdentity.geometricBranchLaw_of_machinUnitAdditions hadd)

theorem leibnizEqMachin_of_unitAdditionLaw
    (hagree : MachinIdentity.PowerSeriesGeometryAtMachinInputs)
    (hadd : MachinIdentity.GeometricUnitAdditionLaw) : LeibnizEqMachin :=
  leibnizEqMachin_of_machinUnitAdditions hagree
    (MachinIdentity.geometricMachinUnitAdditions_of_unitAdditionLaw hadd)

theorem leibnizEqMachin_of_kernelComparisonAtMachinInputs
    (route : MachinIdentity.KernelComparisonAtMachinInputs)
    (hgeom : MachinIdentity.GeometricBranchLaw) : LeibnizEqMachin :=
  leibnizEqMachin_of_geometricRoute_on_unit
    (MachinIdentity.powerSeriesGeometryAtMachinInputs_of_kernelComparisonAtMachinInputs
      route)
    hgeom

theorem leibnizEqMachin_of_powerSeriesRectangleKernelAtMachinInputs
    (hps : MachinIdentity.PowerSeriesEqualsRectangleKernelAtMachinInputs)
    (hgeom : MachinIdentity.GeometricBranchLaw) : LeibnizEqMachin :=
  leibnizEqMachin_of_kernelComparisonAtMachinInputs
    (MachinIdentity.kernelComparisonAtMachinInputs_of_powerSeriesEqualsRectangleKernelAtMachinInputs
      hps)
    hgeom

def MachinIdentity.KernelComparisonAtMachinInputs.ofKernelComparisonRoute
    (route : Taylor.ArctanComparison.KernelComparisonRoute) :
    MachinIdentity.KernelComparisonAtMachinInputs where
  one_fifth :=
    { domain := arctanKernel_one_fifth_mem_unitDomain
      integral := route.data.integralAt ((1 : Rat) / 5)
        arctanKernel_one_fifth_mem_unitDomain
      powerSeries_valid := route.powerSeries_valid ((1 : Rat) / 5)
        arctanKernel_one_fifth_mem_unitDomain
      powerSeries_eq_kernel := route.powerSeries_eq_kernel ((1 : Rat) / 5)
        arctanKernel_one_fifth_mem_unitDomain
      geometric_eq_kernel := route.geometric_eq_kernel ((1 : Rat) / 5)
        arctanKernel_one_fifth_mem_unitDomain }
  one_239 :=
    { domain := arctanKernel_one_239_mem_unitDomain
      integral := route.data.integralAt ((1 : Rat) / 239)
        arctanKernel_one_239_mem_unitDomain
      powerSeries_valid := route.powerSeries_valid ((1 : Rat) / 239)
        arctanKernel_one_239_mem_unitDomain
      powerSeries_eq_kernel := route.powerSeries_eq_kernel ((1 : Rat) / 239)
        arctanKernel_one_239_mem_unitDomain
      geometric_eq_kernel := route.geometric_eq_kernel ((1 : Rat) / 239)
        arctanKernel_one_239_mem_unitDomain }
  one :=
    { domain := arctanKernel_one_mem_unitDomain
      integral := route.data.integralAt (1 : Rat)
        arctanKernel_one_mem_unitDomain
      powerSeries_valid := route.powerSeries_valid (1 : Rat)
        arctanKernel_one_mem_unitDomain
      powerSeries_eq_kernel := route.powerSeries_eq_kernel (1 : Rat)
        arctanKernel_one_mem_unitDomain
      geometric_eq_kernel := route.geometric_eq_kernel (1 : Rat)
        arctanKernel_one_mem_unitDomain }

theorem leibnizEqMachin_of_kernelComparisonRoute
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) : LeibnizEqMachin :=
  leibnizEqMachin_of_kernelComparisonAtMachinInputs
    (MachinIdentity.KernelComparisonAtMachinInputs.ofKernelComparisonRoute
      route)
    hgeom

def piStage (n : Nat) : Nat :=
  2 ^ n

theorem piStage_pos (n : Nat) : 0 < piStage n := by
  unfold piStage
  exact Nat.pow_pos (by omega : 0 < 2)

def originPoint : PiCirclePoint :=
  { x := 0, y := 0 }

def circleParameter (stage k : Nat) : Rat :=
  (k : Rat) / (stage : Rat)

/-- The quarter-circle chart point for the vertical-radius coordinate `t`. -/
def circlePoint (t : Rat) : PiCirclePoint :=
  let d := 1 + t * t
  { x := (1 - t * t) / d,
    y := (2 * t) / d }

def circleSamplePoint (stage k : Nat) : PiCirclePoint :=
  circlePoint (circleParameter stage k)

def pointCross (p q : PiCirclePoint) : Rat :=
  p.x * q.y - p.y * q.x

theorem circlePoint_zero :
    circlePoint 0 = ({ x := 1, y := 0 } : PiCirclePoint) := by
  native_decide

theorem circlePoint_one :
    circlePoint 1 = ({ x := 0, y := 1 } : PiCirclePoint) := by
  native_decide

theorem circleParameter_zero (stage : Nat) :
    circleParameter stage 0 = 0 := by
  grind [circleParameter, Rat.div_def]

theorem circleParameter_self
    (stage : Nat) (hstage : 0 < stage) :
    circleParameter stage stage = 1 := by
  rw [circleParameter, Rat.div_def]
  have hne : (stage : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hstage
  exact Rat.mul_inv_cancel (stage : Rat) hne

theorem circleSamplePoint_zero (stage : Nat) :
    circleSamplePoint stage 0 = ({ x := 1, y := 0 } : PiCirclePoint) := by
  rw [circleSamplePoint, circleParameter_zero, circlePoint_zero]

theorem circleSamplePoint_self
    (stage : Nat) (hstage : 0 < stage) :
    circleSamplePoint stage stage = ({ x := 0, y := 1 } : PiCirclePoint) := by
  rw [circleSamplePoint, circleParameter_self stage hstage, circlePoint_one]

theorem pointCross_origin_left (p : PiCirclePoint) :
    pointCross originPoint p = 0 := by
  grind [pointCross, originPoint, Rat.sub_eq_add_neg]

theorem pointCross_origin_right (p : PiCirclePoint) :
    pointCross p originPoint = 0 := by
  grind [pointCross, originPoint, Rat.sub_eq_add_neg]

def tangentIntersection (p q : PiCirclePoint) : PiCirclePoint :=
  let det := pointCross p q
  { x := (q.y - p.y) / det,
    y := (p.x - q.x) / det }

def innerBoundaryFrom (stage k count : Nat) : List PiCirclePoint :=
  piCircleAreaPolygon.innerBoundaryFrom (circleSamplePoint stage) k count

def innerBoundary (stage : Nat) : List PiCirclePoint :=
  innerBoundaryFrom stage 0 (stage + 1)

def outerTangentPoint (stage k : Nat) : PiCirclePoint :=
  tangentIntersection
    (circleSamplePoint stage k) (circleSamplePoint stage (k + 1))

def outerTangentCrossSum (stage k : Nat) : Rat :=
  pointCross (circleSamplePoint stage k) (outerTangentPoint stage k) +
    pointCross (outerTangentPoint stage k) (circleSamplePoint stage (k + 1))

def rationalCircleStage (stage : Nat) : RationalCircle.Stage :=
  { subdivisions := stage }

theorem circleParameter_double_index
    (stage k : Nat) :
    circleParameter (2 * stage) (2 * k) = circleParameter stage k := by
  have href :
      RationalCircle.Stage.RefinesByDoubling
        (rationalCircleStage stage) (rationalCircleStage (2 * stage)) := by
    rfl
  simpa [rationalCircleStage, circleParameter,
    RationalCircle.Stage.parameter, RationalCircle.Stage.refineIndex] using
    RationalCircle.Stage.parameter_refineIndex_of_refinement href k

theorem circleSamplePoint_double_index
    (stage k : Nat) :
    circleSamplePoint (2 * stage) (2 * k) =
      circleSamplePoint stage k := by
  rw [circleSamplePoint, circleSamplePoint,
    circleParameter_double_index stage k]

theorem circleSamplePoint_double_index_succ
    (stage k : Nat) :
    circleSamplePoint (2 * stage) (2 * k + 2) =
      circleSamplePoint stage (k + 1) := by
  have h := circleSamplePoint_double_index stage (k + 1)
  rw [show 2 * (k + 1) = 2 * k + 2 by omega] at h
  exact h

theorem circleSamplePoint_eq_rationalCircleStage
    (stage k : Nat) :
    circleSamplePoint stage k =
      (rationalCircleStage stage).samplePoint k := by
  rfl

theorem pointCross_eq_rationalCircleCross
    (p q : PiCirclePoint) :
    pointCross p q = RationalCircle.Stage.cross p q := by
  rfl

theorem outerTangentPoint_eq_rationalCircleStage
    (stage k : Nat) :
    outerTangentPoint stage k =
      (rationalCircleStage stage).tangentPoint k := by
  rfl

theorem chordCross_le_outerTangentCrossSum
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    pointCross (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) <=
      outerTangentCrossSum stage k := by
  simpa [rationalCircleStage, circleSamplePoint, circleParameter,
    circlePoint, pointCross, outerTangentCrossSum, outerTangentPoint,
    tangentIntersection, RationalCircle.Stage.samplePoint,
    RationalCircle.Stage.parameter, RationalCircle.Stage.point,
    RationalCircle.Stage.cross, RationalCircle.Stage.tangentPoint,
    RationalCircle.Stage.tangentIntersection] using
    RationalCircle.Stage.adjacentChordCross_le_tangentCrossSum
      (rationalCircleStage stage) hstage k

def outerBoundaryFrom (stage k count : Nat) : List PiCirclePoint :=
  piCircleAreaPolygon.outerBoundaryFrom
    (circleSamplePoint stage) (outerTangentPoint stage) k count

def outerBoundary (stage : Nat) : List PiCirclePoint :=
  circleSamplePoint stage 0 :: outerBoundaryFrom stage 0 stage

def twiceSignedAreaAux
    (first prev : PiCirclePoint) : List PiCirclePoint -> Rat
  | vertices => piCircleAreaPolygon.twiceSignedAreaAux pointCross first prev vertices

def twiceSignedArea : List PiCirclePoint -> Rat
  | [] => 0
  | first :: rest => twiceSignedAreaAux first first rest

def polygonArea (vertices : List PiCirclePoint) : Rat :=
  qabs (twiceSignedArea vertices / 2)

def innerQuarterArea (stage : Nat) : Rat :=
  polygonArea (originPoint :: innerBoundary stage)

def outerQuarterArea (stage : Nat) : Rat :=
  polygonArea (originPoint :: outerBoundary stage)

def piCircleAreaPolygonComputeAtStage (stage : Nat) : QInterval :=
  { lo := 4 * innerQuarterArea stage,
    hi := 4 * outerQuarterArea stage }

def piCircumferenceComputeAtStage (stage : Nat) : QInterval :=
  let innerQuarter := rationalPointPathLength
    (piCircumference.innerBoundaryFrom (circleSamplePoint stage)
      0 (stage + 1)) stage
  let outerQuarter := rationalPointPathLength
    (circleSamplePoint stage 0 ::
      piCircumference.outerBoundaryFrom
        (circleSamplePoint stage) (outerTangentPoint stage) 0 stage) stage
  { lo := (4 * innerQuarter.lo) / 2,
    hi := (4 * outerQuarter.hi) / 2 }

def piCircumferenceCommonComputeAtStage (stage : Nat) : QInterval :=
  let innerQuarter := rationalPointPathLength (innerBoundary stage) stage
  let outerQuarter := rationalPointPathLength (outerBoundary stage) stage
  { lo := (4 * innerQuarter.lo) / 2,
    hi := (4 * outerQuarter.hi) / 2 }

def innerQuarterLength (stage : Nat) : QInterval :=
  rationalPointPathLength (innerBoundary stage) stage

def outerQuarterLength (stage : Nat) : QInterval :=
  rationalPointPathLength (outerBoundary stage) stage

def pointSegmentNormSq (p q : PiCirclePoint) : Rat :=
  let dx := q.x - p.x
  let dy := q.y - p.y
  dx * dx + dy * dy

theorem pointSegmentNormSq_eq_rationalCircleSegmentNormSq
    (p q : PiCirclePoint) :
    pointSegmentNormSq p q =
      RationalCircle.Stage.segmentNormSq p q := by
  rfl

/-- The rational Pythagorean decomposition of a unit-circle chord.

This rewrites the squared chord length as an exact cross-product term plus a
dot-deficit term, so the remaining direct-circumference refinement obligation
can be reduced to finite rational inequalities rather than an appeal to real
square roots. -/
theorem pointSegmentNormSq_eq_cross_sq_add_dot_deficit_sq_of_unit
    {p q : PiCirclePoint}
    (hp : RationalCircle.Stage.normSq p = 1)
    (hq : RationalCircle.Stage.normSq q = 1) :
    pointSegmentNormSq p q =
      sq (pointCross p q) + sq (1 - RationalCircle.Stage.dot p q) := by
  simpa [pointSegmentNormSq_eq_rationalCircleSegmentNormSq,
    pointCross_eq_rationalCircleCross] using
    RationalCircle.Stage.segmentNormSq_eq_cross_sq_add_dot_deficit_sq_of_unit
      hp hq

/-- A rational lower certificate for a positively oriented unit-circle chord.

The correction is second order in the dot-product deficit.  It is a finite
rational expression, kept separate from π itself so it can be used to close
the original chord-path enclosure-refinement proof. -/
def curvatureChordLower (p q : PiCirclePoint) : Rat :=
  pointCross p q +
    sq (1 - RationalCircle.Stage.dot p q) / 4

/-- The curvature chord certificate is below the exact chord length whenever
the two rational endpoints lie on the positively oriented first-quadrant arc.
The conclusion is stated on squared lengths, so no completed real-number
square root is used. -/
theorem curvatureChordLower_sq_le_segmentNormSq_of_unit
    {p q : PiCirclePoint}
    (hp : RationalCircle.Stage.normSq p = 1)
    (hq : RationalCircle.Stage.normSq q = 1)
    (hcross : 0 <= pointCross p q)
    (hdot : 0 <= RationalCircle.Stage.dot p q)
    (hdeficit : 0 <= 1 - RationalCircle.Stage.dot p q) :
    sq (curvatureChordLower p q) <= pointSegmentNormSq p q := by
  let c := pointCross p q
  let d := 1 - RationalCircle.Stage.dot p q
  have hunit : sq c + sq (RationalCircle.Stage.dot p q) = 1 := by
    dsimp [c]
    unfold pointCross RationalCircle.Stage.dot
      RationalCircle.Stage.normSq sq at *
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  have hdot_sq : 0 <= sq (RationalCircle.Stage.dot p q) := by
    unfold sq
    exact Rat.mul_nonneg hdot hdot
  have hc_sq_le_one : sq c <= 1 := by
    grind
  have hc_nonneg : 0 <= c := by
    simpa [c] using hcross
  have hc_le_one : c <= 1 := by
    apply le_of_sq_le_sq_of_nonneg_right (by native_decide : (0 : Rat) <= 1)
    simpa [sq] using hc_sq_le_one
  have hd_nonneg : 0 <= d := by
    simpa [d] using hdeficit
  have hd_le_one : d <= 1 := by
    dsimp [d]
    grind [Rat.sub_eq_add_neg]
  have hd_sq_le_one : sq d <= 1 := by
    have hs := sq_le_sq_of_nonneg_le hd_nonneg hd_le_one
    simpa [sq] using hs
  have hfactor : 0 <= 1 - c / 2 - sq d / 16 := by
    have hc_half : c / 2 <= (1 : Rat) / 2 := by
      exact Rat.div_le_div_of_nonneg_right hc_le_one
        (by native_decide : (0 : Rat) < 2)
    have hd_sixteenth : sq d / 16 <= (1 : Rat) / 16 := by
      exact Rat.div_le_div_of_nonneg_right hd_sq_le_one
        (by native_decide : (0 : Rat) < 16)
    have hnum : (1 : Rat) / 2 + 1 / 16 <= 1 := by
      native_decide
    grind [Rat.sub_eq_add_neg]
  have hdiff :
      (sq c + sq d) - sq (c + sq d / 4) =
        sq d * (1 - c / 2 - sq d / 16) := by
    unfold sq
    grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hdiff_nonneg : 0 <= (sq c + sq d) - sq (c + sq d / 4) := by
    rw [hdiff]
    exact Rat.mul_nonneg
      (by
        unfold sq
        exact Rat.mul_nonneg hd_nonneg hd_nonneg)
      hfactor
  have hbound : sq (c + sq d / 4) <= sq c + sq d := by
    grind [Rat.sub_eq_add_neg]
  rw [pointSegmentNormSq_eq_cross_sq_add_dot_deficit_sq_of_unit hp hq]
  change sq (c + sq d / 4) <= sq c + sq d
  exact hbound

theorem pointSegmentNormSq_self (p : PiCirclePoint) :
    pointSegmentNormSq p p = 0 := by
  grind [pointSegmentNormSq, Rat.sub_eq_add_neg]

theorem piCircleArea_innerBoundaryFrom_eq
    (stage k count : Nat) :
    piCircleAreaPolygon.innerBoundaryFrom (circleSamplePoint stage) k count =
      innerBoundaryFrom stage k count := by
  rfl

theorem piCircumference_innerBoundaryFrom_eq
    (stage k count : Nat) :
    piCircumference.innerBoundaryFrom (circleSamplePoint stage) k count =
      innerBoundaryFrom stage k count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      simp [piCircumference.innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
        innerBoundaryFrom, ih]

theorem piCircleArea_outerBoundaryFrom_eq
    (stage k count : Nat) :
    piCircleAreaPolygon.outerBoundaryFrom
        (circleSamplePoint stage) (outerTangentPoint stage) k count =
      outerBoundaryFrom stage k count := by
  rfl

theorem piCircumference_outerBoundaryFrom_eq
    (stage k count : Nat) :
    piCircumference.outerBoundaryFrom
        (circleSamplePoint stage) (outerTangentPoint stage) k count =
      outerBoundaryFrom stage k count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      simp [piCircumference.outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        outerBoundaryFrom, ih]

theorem piCircleArea_twiceSignedAreaAux_eq
    (first prev : PiCirclePoint) (vertices : List PiCirclePoint) :
    piCircleAreaPolygon.twiceSignedAreaAux pointCross first prev vertices =
      twiceSignedAreaAux first prev vertices := by
  rfl

theorem innerBoundaryFrom_length (stage k count : Nat) :
    (innerBoundaryFrom stage k count).length = count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      unfold innerBoundaryFrom
      simp [piCircleAreaPolygon.innerBoundaryFrom]
      exact ih (k + 1)

theorem innerBoundary_length (stage : Nat) :
    (innerBoundary stage).length = stage + 1 := by
  simp [innerBoundary, innerBoundaryFrom_length]

theorem outerBoundaryFrom_length (stage k count : Nat) :
    (outerBoundaryFrom stage k count).length = 2 * count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      unfold outerBoundaryFrom
      simp [piCircleAreaPolygon.outerBoundaryFrom]
      change (outerBoundaryFrom stage (k + 1) count).length + 1 + 1 =
        2 * (count + 1)
      rw [ih (k + 1)]
      omega

theorem outerBoundary_length (stage : Nat) :
    (outerBoundary stage).length = 2 * stage + 1 := by
  simp [outerBoundary, outerBoundaryFrom_length]

theorem piCircleAreaPolygon_compute_eq (n : Nat) :
    piCircleAreaPolygon.compute n =
      piCircleAreaPolygonComputeAtStage (piStage n) := by
  rfl

theorem piCircumference_compute_eq (n : Nat) :
    piCircumference.compute n = piCircumferenceComputeAtStage (piStage n) := by
  rfl

theorem piCircumferenceComputeAtStage_eq_common (stage : Nat) :
    piCircumferenceComputeAtStage stage =
      piCircumferenceCommonComputeAtStage stage := by
  simp [piCircumferenceComputeAtStage, piCircumferenceCommonComputeAtStage,
    innerBoundary, outerBoundary, piCircumference_innerBoundaryFrom_eq,
    piCircumference_outerBoundaryFrom_eq]

theorem four_arctanGeom_one_compute_eq_piCircleArea_compute
    (n : Nat) :
    (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).compute n) =
      piCircleArea.compute n :=
  ArctanGeometry.piAreaCompatibility n

theorem piLeibniz_equiv_piCircleArea_of_powerSeriesGeometryAgreement
    (hagree : ArctanGeometry.PowerSeriesAgreesOnUnit) :
    LeibnizEqArea := by
  have hpowGeom :
      (arctan (1 : Rat)).Equiv (ArctanGeometry.arctanGeom (1 : Rat)) :=
    ArctanGeometry.powerSeries_equiv_geometric_of_agreement
      hagree (by unfold Elementary.Arctan.powerSeriesDomain qabs; native_decide)
  have hscaled :
      (((4 : Nat) * arctan (1 : Rat) : RealRaw).Equiv
        ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw)) :=
    RealRaw.natScale_equiv 4 hpowGeom
  intro n
  have hover := (RealRaw.compareAt_overlap_iff
      ((4 : Nat) * arctan (1 : Rat) : RealRaw)
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) n n).1
    (hscaled n)
  apply (RealRaw.compareAt_overlap_iff piLeibniz piCircleArea n n).2
  rw [piLeibniz_compute_eq_four_arctan_one n]
  rw [← four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  exact hover

theorem leibnizEqArea_of_powerSeriesGeometryAgreement
    (_hGeomValid : ArctanGeometry.Valid)
    (hagree : ArctanGeometry.PowerSeriesAgreesOnUnit) :
    LeibnizEqArea :=
  piLeibniz_equiv_piCircleArea_of_powerSeriesGeometryAgreement hagree

theorem leibnizEqArea_of_powerSeriesGeometryAgreement_on_unit
    (hagree : ArctanGeometry.PowerSeriesAgreesOnUnit) :
    LeibnizEqArea :=
  piLeibniz_equiv_piCircleArea_of_powerSeriesGeometryAgreement hagree

theorem leibnizEqArea_of_kernelComparisonRoute
    (route : Taylor.ArctanComparison.KernelComparisonRoute) :
    LeibnizEqArea :=
  leibnizEqArea_of_powerSeriesGeometryAgreement_on_unit
    (Taylor.ArctanComparison.powerSeriesAgreesOnUnit_of_kernelComparisonRoute
      route)

theorem pointSegmentNormSq_nonneg (p q : PiCirclePoint) :
    0 <= pointSegmentNormSq p q := by
  unfold pointSegmentNormSq
  have hx := RationalCircle.Stage.ratSquare_nonneg (q.x - p.x)
  have hy := RationalCircle.Stage.ratSquare_nonneg (q.y - p.y)
  grind

theorem pointSegmentNormSq_sqrtDomain (p q : PiCirclePoint) :
    sqrtDomain (pointSegmentNormSq p q) := by
  change ¬pointSegmentNormSq p q < 0
  have h := pointSegmentNormSq_nonneg p q
  grind

def pointSegmentLengthInterval
    (p q : PiCirclePoint) (n : Nat) : QInterval :=
  sqrtPartialRaw.compute (pointSegmentNormSq p q)
    (pointSegmentNormSq_sqrtDomain p q) n

theorem pointSegmentLengthInterval_spec
    (p q : PiCirclePoint) (n : Nat) :
    SqrtIntervalSpec (pointSegmentNormSq p q)
      (pointSegmentLengthInterval p q n) := by
  unfold pointSegmentLengthInterval
  simpa [sqrtPartialRaw] using
    sqrtApproxOnDomain_spec (pointSegmentNormSq p q)
      (pointSegmentNormSq_sqrtDomain p q) n

theorem pointSegmentLengthInterval_lo_nonneg
    (p q : PiCirclePoint) (n : Nat) :
    0 <= (pointSegmentLengthInterval p q n).lo :=
  (pointSegmentLengthInterval_spec p q n).1

theorem pointSegmentLengthInterval_lo_le_hi
    (p q : PiCirclePoint) (n : Nat) :
    (pointSegmentLengthInterval p q n).lo <=
      (pointSegmentLengthInterval p q n).hi :=
  (pointSegmentLengthInterval_spec p q n).2.1

theorem pointSegmentLengthInterval_width_nonneg
    (p q : PiCirclePoint) (n : Nat) :
    0 <= (pointSegmentLengthInterval p q n).width := by
  have h := pointSegmentLengthInterval_lo_le_hi p q n
  grind [QInterval.width, Rat.sub_eq_add_neg]

theorem pointSegmentLengthInterval_width_eq
    (p q : PiCirclePoint) (n : Nat) :
    (pointSegmentLengthInterval p q n).width =
      sqrtUpperBound (pointSegmentNormSq p q) /
        (((2 ^ sqrtFuel (pointSegmentNormSq p q) (sqrtStageEps n) : Nat) :
          Rat)) := by
  unfold pointSegmentLengthInterval
  simpa [sqrtPartialRaw] using
    sqrtApproxOnDomain_width_eq (pointSegmentNormSq p q)
      (pointSegmentNormSq_sqrtDomain p q) n

/-- For an adjacent chord in a stage with at least two cells, the concrete
square-root interval used by the original circumference algorithm has an exact
dyadic width. This exposes the literal error term that must be paid in the
remaining local refinement margin. -/
theorem adjacentPointSegmentLengthInterval_width_eq_unit
    (stage : Nat) (hstage : 2 <= stage) (k n : Nat) (hn : n ≠ 0) :
    (pointSegmentLengthInterval
      (circleSamplePoint stage k)
      (circleSamplePoint stage (k + 1)) n).width =
      1 / (((2 ^ (n + 9) : Nat) : Rat)) := by
  have hunit :
      pointSegmentNormSq
          (circleSamplePoint stage k)
          (circleSamplePoint stage (k + 1)) <= 1 := by
    simpa [circleSamplePoint_eq_rationalCircleStage,
      pointSegmentNormSq_eq_rationalCircleSegmentNormSq] using
      RationalCircle.Stage.samplePoint_segmentNormSq_le_one_of_two_le_subdivisions
        (rationalCircleStage stage) hstage k
  simpa [pointSegmentLengthInterval, sqrtPartialRaw] using
    (sqrtApproxOnDomain_width_eq_unit
      (pointSegmentNormSq_sqrtDomain
        (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1))) hunit n hn)

theorem pointSegmentLengthInterval_contains_of_le_precision
    (p q : PiCirclePoint) {n m : Nat} (hnm : n <= m) :
    (pointSegmentLengthInterval p q n).ContainsInterval
      (pointSegmentLengthInterval p q m) := by
  unfold pointSegmentLengthInterval
  simpa [sqrtPartialRaw] using
    sqrtApproxOnDomain_contains_of_le (pointSegmentNormSq p q)
      (pointSegmentNormSq_sqrtDomain p q) hnm

theorem pointSegmentLengthInterval_lo_mono_precision
    (p q : PiCirclePoint) {n m : Nat} (hnm : n <= m) :
    (pointSegmentLengthInterval p q n).lo <=
      (pointSegmentLengthInterval p q m).lo :=
  (pointSegmentLengthInterval_contains_of_le_precision p q hnm).1

theorem pointSegmentLengthInterval_hi_anti_precision
    (p q : PiCirclePoint) {n m : Nat} (hnm : n <= m) :
    (pointSegmentLengthInterval p q m).hi <=
      (pointSegmentLengthInterval p q n).hi :=
  (pointSegmentLengthInterval_contains_of_le_precision p q hnm).2

theorem pointSegmentLengthInterval_le_hi_of_sq_le
    (p q : PiCirclePoint) (n : Nat) {r : Rat}
    (hrsq : sq r <= pointSegmentNormSq p q) :
    r <= (pointSegmentLengthInterval p q n).hi :=
  SqrtIntervalSpec.le_hi_of_sq_le
    (pointSegmentLengthInterval_spec p q n) hrsq

theorem pointSegmentLengthInterval_lo_le_of_sq_le
    (p q : PiCirclePoint) (n : Nat) {r : Rat}
    (hr : 0 <= r) (hsq : pointSegmentNormSq p q <= sq r) :
    (pointSegmentLengthInterval p q n).lo <= r :=
  SqrtIntervalSpec.lo_le_of_sq_le
    (pointSegmentLengthInterval_spec p q n) hr hsq

theorem pointSegmentLengthInterval_hi_nonneg
    (p q : PiCirclePoint) (n : Nat) :
    0 <= (pointSegmentLengthInterval p q n).hi :=
  Rat.le_trans
    (pointSegmentLengthInterval_lo_nonneg p q n)
    (pointSegmentLengthInterval_lo_le_hi p q n)

/-- Convert the exact rational curvature certificate into a lower bound for a
finite bisection enclosure.  The only loss is the explicitly computed width
of that enclosure. -/
theorem curvatureChordLower_sub_width_le_segment_lo_of_unit
    {p q : PiCirclePoint}
    (hp : RationalCircle.Stage.normSq p = 1)
    (hq : RationalCircle.Stage.normSq q = 1)
    (hcross : 0 <= pointCross p q)
    (hdot : 0 <= RationalCircle.Stage.dot p q)
    (hdeficit : 0 <= 1 - RationalCircle.Stage.dot p q)
    (precision : Nat) :
    curvatureChordLower p q -
        (pointSegmentLengthInterval p q precision).width <=
      (pointSegmentLengthInterval p q precision).lo := by
  have hhi : curvatureChordLower p q <=
      (pointSegmentLengthInterval p q precision).hi :=
    pointSegmentLengthInterval_le_hi_of_sq_le p q precision
      (curvatureChordLower_sq_le_segmentNormSq_of_unit hp hq hcross hdot
        hdeficit)
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- The sharper rational secant certificate also survives a finite square-root
bisection with only its displayed width lost.  In contrast to the older
curvature certificate, its correction is cubic at short chord scale. -/
theorem secantChordLower_sub_width_le_segment_lo_of_unit
    {p q : PiCirclePoint}
    (hp : RationalCircle.Stage.normSq p = 1)
    (hq : RationalCircle.Stage.normSq q = 1)
    (hcross : 0 < pointCross p q)
    (hdeficit : 0 <= 1 - RationalCircle.Stage.dot p q)
    (precision : Nat) :
    RationalCircle.Stage.secantChordLower p q -
        (pointSegmentLengthInterval p q precision).width <=
      (pointSegmentLengthInterval p q precision).lo := by
  have hhi : RationalCircle.Stage.secantChordLower p q <=
      (pointSegmentLengthInterval p q precision).hi :=
    pointSegmentLengthInterval_le_hi_of_sq_le p q precision (by
      simpa [pointSegmentNormSq, RationalCircle.Stage.segmentNormSq,
        pointCross, RationalCircle.Stage.cross] using
        RationalCircle.Stage.secantChordLower_sq_le_segmentNormSq_of_unit
          hp hq (by simpa [pointCross, RationalCircle.Stage.cross] using hcross)
          hdeficit)
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- Specialize the sharper secant certificate to consecutive rational-circle
samples.  This is the bisection-ready local ingredient for the remaining
direct circumference refinement problem. -/
theorem adjacentSecantChordLower_sub_width_le_segment_lo
    (stage : Nat) (hstage : 0 < stage) (k precision : Nat) :
    RationalCircle.Stage.secantChordLower
        (circleSamplePoint stage k) (circleSamplePoint stage (k + 1)) -
      (pointSegmentLengthInterval
        (circleSamplePoint stage k) (circleSamplePoint stage (k + 1))
        precision).width <=
      (pointSegmentLengthInterval
        (circleSamplePoint stage k) (circleSamplePoint stage (k + 1))
        precision).lo := by
  apply secantChordLower_sub_width_le_segment_lo_of_unit
  · change RationalCircle.Stage.normSq
      ((rationalCircleStage stage).samplePoint k) = 1
    exact RationalCircle.Stage.samplePoint_normSq_unit
      (rationalCircleStage stage) k
  · change RationalCircle.Stage.normSq
      ((rationalCircleStage stage).samplePoint (k + 1)) = 1
    exact RationalCircle.Stage.samplePoint_normSq_unit
      (rationalCircleStage stage) (k + 1)
  · change 0 < RationalCircle.Stage.cross
      ((rationalCircleStage stage).samplePoint k)
      ((rationalCircleStage stage).samplePoint (k + 1))
    exact RationalCircle.Stage.samplePoint_cross_pos_adjacent
      (rationalCircleStage stage) hstage k
  · change 0 <= 1 - RationalCircle.Stage.dot
      (RationalCircle.Stage.point (circleParameter stage k))
      (RationalCircle.Stage.point (circleParameter stage (k + 1)))
    exact RationalCircle.Stage.one_sub_point_dot_nonneg
      (circleParameter stage k) (circleParameter stage (k + 1))

theorem chordLengthLo_le_outerTangentCrossSum
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    (pointSegmentLengthInterval
      (circleSamplePoint stage k)
      (circleSamplePoint stage (k + 1)) stage).lo <=
      outerTangentCrossSum stage k := by
  have hnonneg :
      0 <= outerTangentCrossSum stage k := by
    simpa [rationalCircleStage, circleSamplePoint, circleParameter,
      circlePoint, pointCross, outerTangentCrossSum, outerTangentPoint,
      tangentIntersection, RationalCircle.Stage.samplePoint,
      RationalCircle.Stage.parameter, RationalCircle.Stage.point,
      RationalCircle.Stage.cross, RationalCircle.Stage.tangentPoint,
      RationalCircle.Stage.tangentIntersection] using
      RationalCircle.Stage.adjacentTangentCrossSum_nonneg
        (rationalCircleStage stage) hstage k
  have hsq :
      pointSegmentNormSq
        (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) <=
        sq (outerTangentCrossSum stage k) := by
    simpa [rationalCircleStage, circleSamplePoint, circleParameter,
      circlePoint, pointCross, outerTangentCrossSum, outerTangentPoint,
      tangentIntersection, pointSegmentNormSq,
      RationalCircle.Stage.samplePoint,
      RationalCircle.Stage.parameter, RationalCircle.Stage.point,
      RationalCircle.Stage.cross, RationalCircle.Stage.tangentPoint,
      RationalCircle.Stage.tangentIntersection,
      RationalCircle.Stage.segmentNormSq] using
      RationalCircle.Stage.adjacentChordSegmentNormSq_le_tangentCrossSum_sq
        (rationalCircleStage stage) hstage k
  exact pointSegmentLengthInterval_lo_le_of_sq_le
    (circleSamplePoint stage k)
    (circleSamplePoint stage (k + 1)) stage hnonneg hsq

def ConsecutiveCrossNonneg : List PiCirclePoint -> Prop
  | [] => True
  | [_] => True
  | p :: q :: rest =>
      0 <= pointCross p q /\ ConsecutiveCrossNonneg (q :: rest)

def ConsecutiveCrossLe (precision : Nat) : List PiCirclePoint -> Prop
  | [] => True
  | [_] => True
  | p :: q :: rest =>
      pointCross p q <= (pointSegmentLengthInterval p q precision).hi /\
        ConsecutiveCrossLe precision (q :: rest)

def ConsecutiveLengthLoLeCross (precision : Nat) : List PiCirclePoint -> Prop
  | [] => True
  | [_] => True
  | p :: q :: rest =>
      (pointSegmentLengthInterval p q precision).lo <= pointCross p q /\
        ConsecutiveLengthLoLeCross precision (q :: rest)

theorem circleSamplePoint_cross_nonneg_of_order
    (stage : Nat) (hstage : 0 < stage)
    {i j : Nat} (hij : i <= j) :
    0 <= pointCross (circleSamplePoint stage i)
      (circleSamplePoint stage j) := by
  simpa [circleSamplePoint_eq_rationalCircleStage,
    pointCross_eq_rationalCircleCross] using
    RationalCircle.Stage.samplePoint_cross_nonneg_of_order
      (rationalCircleStage stage) hstage hij

theorem circleSamplePoint_cross_le_segment_hi
    (stage precision i j : Nat) :
    pointCross (circleSamplePoint stage i) (circleSamplePoint stage j) <=
      (pointSegmentLengthInterval
        (circleSamplePoint stage i)
        (circleSamplePoint stage j) precision).hi := by
  have hsq :
      sq (pointCross (circleSamplePoint stage i)
          (circleSamplePoint stage j)) <=
        pointSegmentNormSq
          (circleSamplePoint stage i) (circleSamplePoint stage j) := by
    simpa [circleSamplePoint_eq_rationalCircleStage,
      pointCross_eq_rationalCircleCross,
      pointSegmentNormSq_eq_rationalCircleSegmentNormSq] using
      RationalCircle.Stage.cross_sq_le_segmentNormSq_of_unit
        (RationalCircle.Stage.samplePoint_normSq_unit
          (rationalCircleStage stage) i)
        (RationalCircle.Stage.samplePoint_normSq_unit
          (rationalCircleStage stage) j)
  exact pointSegmentLengthInterval_le_hi_of_sq_le
    (circleSamplePoint stage i) (circleSamplePoint stage j) precision hsq

theorem entryTangentCross_nonneg
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    0 <= pointCross (circleSamplePoint stage k)
      (outerTangentPoint stage k) := by
  simpa [circleSamplePoint_eq_rationalCircleStage,
    outerTangentPoint_eq_rationalCircleStage,
    pointCross_eq_rationalCircleCross] using
    RationalCircle.Stage.adjacentEntryTangentCross_nonneg
      (rationalCircleStage stage) hstage k

theorem exitTangentCross_nonneg
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    0 <= pointCross (outerTangentPoint stage k)
      (circleSamplePoint stage (k + 1)) := by
  simpa [circleSamplePoint_eq_rationalCircleStage,
    outerTangentPoint_eq_rationalCircleStage,
    pointCross_eq_rationalCircleCross] using
    RationalCircle.Stage.adjacentExitTangentCross_nonneg
      (rationalCircleStage stage) hstage k

theorem entryTangentSegmentNormSq_eq_cross_sq
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    pointSegmentNormSq
        (circleSamplePoint stage k) (outerTangentPoint stage k) =
      sq (pointCross (circleSamplePoint stage k)
        (outerTangentPoint stage k)) := by
  simpa [circleSamplePoint_eq_rationalCircleStage,
    outerTangentPoint_eq_rationalCircleStage,
    pointCross_eq_rationalCircleCross,
    pointSegmentNormSq_eq_rationalCircleSegmentNormSq] using
    RationalCircle.Stage.adjacentEntryTangentSegmentNormSq_eq_cross_sq
      (rationalCircleStage stage) hstage k

theorem exitTangentSegmentNormSq_eq_cross_sq
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    pointSegmentNormSq
        (outerTangentPoint stage k)
        (circleSamplePoint stage (k + 1)) =
      sq (pointCross (outerTangentPoint stage k)
        (circleSamplePoint stage (k + 1))) := by
  simpa [circleSamplePoint_eq_rationalCircleStage,
    outerTangentPoint_eq_rationalCircleStage,
    pointCross_eq_rationalCircleCross,
    pointSegmentNormSq_eq_rationalCircleSegmentNormSq] using
    RationalCircle.Stage.adjacentExitTangentSegmentNormSq_eq_cross_sq
      (rationalCircleStage stage) hstage k

theorem entryTangentCross_le_segment_hi
    (stage : Nat) (hstage : 0 < stage) (precision k : Nat) :
    pointCross (circleSamplePoint stage k) (outerTangentPoint stage k) <=
      (pointSegmentLengthInterval
        (circleSamplePoint stage k)
        (outerTangentPoint stage k) precision).hi :=
  pointSegmentLengthInterval_le_hi_of_sq_le
    (circleSamplePoint stage k) (outerTangentPoint stage k) precision
    (by
      rw [entryTangentSegmentNormSq_eq_cross_sq stage hstage k]
      exact Rat.le_refl)

theorem exitTangentCross_le_segment_hi
    (stage : Nat) (hstage : 0 < stage) (precision k : Nat) :
    pointCross (outerTangentPoint stage k)
        (circleSamplePoint stage (k + 1)) <=
      (pointSegmentLengthInterval
        (outerTangentPoint stage k)
        (circleSamplePoint stage (k + 1)) precision).hi :=
  pointSegmentLengthInterval_le_hi_of_sq_le
    (outerTangentPoint stage k)
    (circleSamplePoint stage (k + 1)) precision
    (by
      rw [exitTangentSegmentNormSq_eq_cross_sq stage hstage k]
      exact Rat.le_refl)

theorem entryTangentSegment_lo_le_cross
    (stage : Nat) (hstage : 0 < stage) (precision k : Nat) :
    (pointSegmentLengthInterval
      (circleSamplePoint stage k)
      (outerTangentPoint stage k) precision).lo <=
      pointCross (circleSamplePoint stage k)
        (outerTangentPoint stage k) :=
  pointSegmentLengthInterval_lo_le_of_sq_le
    (circleSamplePoint stage k) (outerTangentPoint stage k) precision
    (entryTangentCross_nonneg stage hstage k)
    (by
      rw [entryTangentSegmentNormSq_eq_cross_sq stage hstage k]
      exact Rat.le_refl)

theorem exitTangentSegment_lo_le_cross
    (stage : Nat) (hstage : 0 < stage) (precision k : Nat) :
    (pointSegmentLengthInterval
      (outerTangentPoint stage k)
      (circleSamplePoint stage (k + 1)) precision).lo <=
      pointCross (outerTangentPoint stage k)
        (circleSamplePoint stage (k + 1)) :=
  pointSegmentLengthInterval_lo_le_of_sq_le
    (outerTangentPoint stage k)
    (circleSamplePoint stage (k + 1)) precision
    (exitTangentCross_nonneg stage hstage k)
    (by
      rw [exitTangentSegmentNormSq_eq_cross_sq stage hstage k]
      exact Rat.le_refl)

theorem innerBoundaryFrom_consecutiveCrossNonneg
    (stage : Nat) (hstage : 0 < stage) (count k : Nat) :
    ConsecutiveCrossNonneg (innerBoundaryFrom stage k count) := by
  induction count generalizing k with
  | zero =>
      simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
        ConsecutiveCrossNonneg]
  | succ count ih =>
      cases count with
      | zero =>
          simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
            ConsecutiveCrossNonneg]
      | succ count =>
          simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
            ConsecutiveCrossNonneg]
          exact ⟨circleSamplePoint_cross_nonneg_of_order
              stage hstage (Nat.le_succ k),
            ih (k + 1)⟩

theorem innerBoundary_consecutiveCrossNonneg
    (stage : Nat) (hstage : 0 < stage) :
    ConsecutiveCrossNonneg (innerBoundary stage) := by
  unfold innerBoundary
  exact innerBoundaryFrom_consecutiveCrossNonneg
    stage hstage (stage + 1) 0

theorem innerBoundaryFrom_consecutiveCrossLe
    (stage precision count k : Nat) :
    ConsecutiveCrossLe precision (innerBoundaryFrom stage k count) := by
  induction count generalizing k with
  | zero =>
      simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
        ConsecutiveCrossLe]
  | succ count ih =>
      cases count with
      | zero =>
          simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
            ConsecutiveCrossLe]
      | succ count =>
          simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
            ConsecutiveCrossLe]
          exact ⟨circleSamplePoint_cross_le_segment_hi
              stage precision k (k + 1),
            ih (k + 1)⟩

theorem innerBoundary_consecutiveCrossLe
    (stage precision : Nat) :
    ConsecutiveCrossLe precision (innerBoundary stage) := by
  unfold innerBoundary
  exact innerBoundaryFrom_consecutiveCrossLe
    stage precision (stage + 1) 0

theorem outerBoundaryFrom_consecutiveCrossNonneg
    (stage : Nat) (hstage : 0 < stage) (count k : Nat) :
    ConsecutiveCrossNonneg
      (circleSamplePoint stage k :: outerBoundaryFrom stage k count) := by
  induction count generalizing k with
  | zero =>
      simp [outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        ConsecutiveCrossNonneg]
  | succ count ih =>
      simp [outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        ConsecutiveCrossNonneg]
      exact ⟨entryTangentCross_nonneg stage hstage k,
        ⟨exitTangentCross_nonneg stage hstage k, ih (k + 1)⟩⟩

theorem outerBoundary_consecutiveCrossNonneg
    (stage : Nat) (hstage : 0 < stage) :
    ConsecutiveCrossNonneg (outerBoundary stage) := by
  unfold outerBoundary
  exact outerBoundaryFrom_consecutiveCrossNonneg
    stage hstage stage 0

theorem outerBoundaryFrom_consecutiveCrossLe
    (stage : Nat) (hstage : 0 < stage) (precision count k : Nat) :
    ConsecutiveCrossLe precision
      (circleSamplePoint stage k :: outerBoundaryFrom stage k count) := by
  induction count generalizing k with
  | zero =>
      simp [outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        ConsecutiveCrossLe]
  | succ count ih =>
      simp [outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        ConsecutiveCrossLe]
      exact ⟨entryTangentCross_le_segment_hi stage hstage precision k,
        ⟨exitTangentCross_le_segment_hi stage hstage precision k,
          ih (k + 1)⟩⟩

theorem outerBoundary_consecutiveCrossLe
    (stage : Nat) (hstage : 0 < stage) (precision : Nat) :
    ConsecutiveCrossLe precision (outerBoundary stage) := by
  unfold outerBoundary
  exact outerBoundaryFrom_consecutiveCrossLe
    stage hstage precision stage 0

theorem outerBoundaryFrom_consecutiveLengthLoLeCross
    (stage : Nat) (hstage : 0 < stage) (precision count k : Nat) :
    ConsecutiveLengthLoLeCross precision
      (circleSamplePoint stage k :: outerBoundaryFrom stage k count) := by
  induction count generalizing k with
  | zero =>
      simp [outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        ConsecutiveLengthLoLeCross]
  | succ count ih =>
      simp [outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        ConsecutiveLengthLoLeCross]
      exact ⟨entryTangentSegment_lo_le_cross stage hstage precision k,
        ⟨exitTangentSegment_lo_le_cross stage hstage precision k,
          ih (k + 1)⟩⟩

theorem outerBoundary_consecutiveLengthLoLeCross
    (stage : Nat) (hstage : 0 < stage) (precision : Nat) :
    ConsecutiveLengthLoLeCross precision (outerBoundary stage) := by
  unfold outerBoundary
  exact outerBoundaryFrom_consecutiveLengthLoLeCross
    stage hstage precision stage 0

theorem circlePoint_normSq (u : Rat) :
    (circlePoint u).x * (circlePoint u).x +
      (circlePoint u).y * (circlePoint u).y = 1 := by
  unfold circlePoint
  simp
  have hdpos : 0 < 1 + u * u := by
    have hs : 0 <= u * u := RationalCircle.Stage.ratSquare_nonneg u
    grind
  have hdne : 1 + u * u ≠ 0 := Rat.ne_of_gt hdpos
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem circleSamplePoint_normSq (stage k : Nat) :
    (circleSamplePoint stage k).x * (circleSamplePoint stage k).x +
      (circleSamplePoint stage k).y * (circleSamplePoint stage k).y = 1 := by
  unfold circleSamplePoint
  exact circlePoint_normSq (circleParameter stage k)

theorem rationalPointPathLength_lo_nonneg
    (points : List PiCirclePoint) (n : Nat) :
    0 <= (rationalPointPathLength points n).lo := by
  induction points with
  | nil =>
      simp [rationalPointPathLength, rationalPointPathLength.totalLength]
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp [rationalPointPathLength, rationalPointPathLength.totalLength]
      | cons q qs =>
          unfold rationalPointPathLength at ih
          have hseg_nonneg :
              0 <=
                (sqrtPartialRaw.compute
                  ((q.x - p.x) * (q.x - p.x) +
                    (q.y - p.y) * (q.y - p.y))
                  (pointSegmentNormSq_sqrtDomain p q) n).lo := by
            simpa [pointSegmentNormSq] using
              pointSegmentLengthInterval_lo_nonneg p q n
          simp [rationalPointPathLength,
            rationalPointPathLength.totalLength]
          exact Rat.add_nonneg hseg_nonneg ih

theorem rationalPointPathLength_lo_le_hi
    (points : List PiCirclePoint) (n : Nat) :
    (rationalPointPathLength points n).lo <=
      (rationalPointPathLength points n).hi := by
  induction points with
  | nil =>
      simp [rationalPointPathLength, rationalPointPathLength.totalLength]
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp [rationalPointPathLength, rationalPointPathLength.totalLength]
      | cons q qs =>
          unfold rationalPointPathLength at ih
          have hseg_order :
              (sqrtPartialRaw.compute
                ((q.x - p.x) * (q.x - p.x) +
                  (q.y - p.y) * (q.y - p.y))
                (pointSegmentNormSq_sqrtDomain p q) n).lo <=
              (sqrtPartialRaw.compute
                ((q.x - p.x) * (q.x - p.x) +
                  (q.y - p.y) * (q.y - p.y))
                (pointSegmentNormSq_sqrtDomain p q) n).hi := by
            simpa [pointSegmentNormSq] using
              pointSegmentLengthInterval_lo_le_hi p q n
          simp [rationalPointPathLength,
            rationalPointPathLength.totalLength]
          grind

theorem rationalPointPathLength_width_nonneg
    (points : List PiCirclePoint) (n : Nat) :
    0 <= (rationalPointPathLength points n).width := by
  have h := rationalPointPathLength_lo_le_hi points n
  grind [QInterval.width, Rat.sub_eq_add_neg]

theorem rationalPointPathLength_contains_of_le_precision
    (points : List PiCirclePoint) {n m : Nat} (hnm : n <= m) :
    (rationalPointPathLength points n).ContainsInterval
      (rationalPointPathLength points m) := by
  induction points with
  | nil =>
      simp [rationalPointPathLength, rationalPointPathLength.totalLength,
        QInterval.ContainsInterval]
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp [rationalPointPathLength, rationalPointPathLength.totalLength,
            QInterval.ContainsInterval]
      | cons q qs =>
          have hseg :=
            pointSegmentLengthInterval_contains_of_le_precision p q hnm
          have htail := ih
          unfold QInterval.ContainsInterval at hseg htail ⊢
          simp [rationalPointPathLength, rationalPointPathLength.totalLength,
            pointSegmentLengthInterval, pointSegmentNormSq] at *
          constructor <;> grind

theorem rationalPointPathLength_lo_mono_precision
    (points : List PiCirclePoint) {n m : Nat} (hnm : n <= m) :
    (rationalPointPathLength points n).lo <=
      (rationalPointPathLength points m).lo :=
  (rationalPointPathLength_contains_of_le_precision points hnm).1

theorem rationalPointPathLength_hi_anti_precision
    (points : List PiCirclePoint) {n m : Nat} (hnm : n <= m) :
    (rationalPointPathLength points m).hi <=
      (rationalPointPathLength points n).hi :=
  (rationalPointPathLength_contains_of_le_precision points hnm).2

theorem innerBoundaryPathLength_contains_of_le_precision
    (stage : Nat) {n m : Nat} (hnm : n <= m) :
    (rationalPointPathLength (innerBoundary stage) n).ContainsInterval
      (rationalPointPathLength (innerBoundary stage) m) :=
  rationalPointPathLength_contains_of_le_precision (innerBoundary stage) hnm

theorem outerBoundaryPathLength_contains_of_le_precision
    (stage : Nat) {n m : Nat} (hnm : n <= m) :
    (rationalPointPathLength (outerBoundary stage) n).ContainsInterval
      (rationalPointPathLength (outerBoundary stage) m) :=
  rationalPointPathLength_contains_of_le_precision (outerBoundary stage) hnm

def pathSegmentWidthSum : List PiCirclePoint -> Nat -> Rat
  | [], _ => 0
  | [_], _ => 0
  | p :: q :: rest, n =>
      (pointSegmentLengthInterval p q n).width +
        pathSegmentWidthSum (q :: rest) n

def pathSegmentWidthBudget : List PiCirclePoint -> Nat -> Rat
  | [], _ => 0
  | [_], _ => 0
  | p :: q :: rest, n =>
      sqrtUpperBound (pointSegmentNormSq p q) /
          (((2 ^ sqrtFuel (pointSegmentNormSq p q) (sqrtStageEps n) : Nat) :
            Rat)) +
        pathSegmentWidthBudget (q :: rest) n

def pathSegmentCount : List PiCirclePoint -> Nat
  | [] => 0
  | [_] => 0
  | _p :: q :: rest => 1 + pathSegmentCount (q :: rest)

def ConsecutiveBudgetLe (precision : Nat) (B : Rat) :
    List PiCirclePoint -> Prop
  | [] => True
  | [_] => True
  | p :: q :: rest =>
      sqrtUpperBound (pointSegmentNormSq p q) /
          (((2 ^ sqrtFuel (pointSegmentNormSq p q) (sqrtStageEps precision) :
            Nat) : Rat)) <= B /\
        ConsecutiveBudgetLe precision B (q :: rest)

def SegmentBudgetLeAt
    (precision : Nat) (B : Rat) (p q : PiCirclePoint) : Prop :=
  sqrtUpperBound (pointSegmentNormSq p q) /
      (((2 ^ sqrtFuel (pointSegmentNormSq p q) (sqrtStageEps precision) :
        Nat) : Rat)) <= B

theorem circleParameter_succ_sub (stage k : Nat) :
    circleParameter stage (k + 1) - circleParameter stage k =
      1 / (stage : Rat) := by
  simpa [rationalCircleStage, circleParameter,
    RationalCircle.Stage.parameter] using
    RationalCircle.Stage.parameter_succ_sub (rationalCircleStage stage) k

theorem circleParameter_nonneg
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    0 <= circleParameter stage k := by
  simpa [rationalCircleStage, circleParameter,
    RationalCircle.Stage.parameter] using
    RationalCircle.Stage.parameter_nonneg (rationalCircleStage stage) hstage k

theorem circleParameter_lt_succ
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    circleParameter stage k < circleParameter stage (k + 1) := by
  have hdiff := circleParameter_succ_sub stage k
  have hpos : 0 < (1 : Rat) / (stage : Rat) := by
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hstage)
  grind [Rat.sub_eq_add_neg]

def adjacentChordNormSqFormula (stage k : Nat) : Rat :=
  let u := circleParameter stage k
  let v := circleParameter stage (k + 1)
  let d := (1 : Rat) / (stage : Rat)
  (4 * d * d) / ((1 + u * u) * (1 + v * v))

def adjacentTangentCrossFormula (stage k : Nat) : Rat :=
  let u := circleParameter stage k
  let v := circleParameter stage (k + 1)
  let d := (1 : Rat) / (stage : Rat)
  d / (1 + u * v)

def entryTangentNormSqFormula (stage k : Nat) : Rat :=
  sq (adjacentTangentCrossFormula stage k)

def exitTangentNormSqFormula (stage k : Nat) : Rat :=
  sq (adjacentTangentCrossFormula stage k)

theorem adjacentChordSegmentNormSq_eq_formula
    (stage k : Nat) :
    pointSegmentNormSq
        (circleSamplePoint stage k) (circleSamplePoint stage (k + 1)) =
      adjacentChordNormSqFormula stage k := by
  have hbase :
      pointSegmentNormSq
          (circleSamplePoint stage k) (circleSamplePoint stage (k + 1)) =
        (4 * (circleParameter stage (k + 1) - circleParameter stage k) *
            (circleParameter stage (k + 1) - circleParameter stage k)) /
          ((1 + circleParameter stage k * circleParameter stage k) *
            (1 + circleParameter stage (k + 1) *
              circleParameter stage (k + 1))) := by
    simpa [circleSamplePoint, circlePoint, pointSegmentNormSq,
      RationalCircle.Stage.point, RationalCircle.Stage.segmentNormSq] using
      RationalCircle.Stage.point_segmentNormSq_formula
        (circleParameter stage k) (circleParameter stage (k + 1))
  rw [hbase]
  unfold adjacentChordNormSqFormula
  rw [circleParameter_succ_sub]

theorem entryTangentCross_eq_formula
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    pointCross (circleSamplePoint stage k) (outerTangentPoint stage k) =
      adjacentTangentCrossFormula stage k := by
  have hu0 := circleParameter_nonneg stage hstage k
  have hv0 := circleParameter_nonneg stage hstage (k + 1)
  have huv := circleParameter_lt_succ stage hstage k
  have hbase :
      pointCross (circleSamplePoint stage k) (outerTangentPoint stage k) =
        (circleParameter stage (k + 1) - circleParameter stage k) /
          (1 + circleParameter stage k * circleParameter stage (k + 1)) := by
    simpa [circleSamplePoint, circlePoint, pointCross, outerTangentPoint,
      tangentIntersection, RationalCircle.Stage.point,
      RationalCircle.Stage.cross,
      RationalCircle.Stage.tangentIntersection] using
      RationalCircle.Stage.point_entry_tangent_cross_formula hu0 hv0 huv
  rw [hbase]
  unfold adjacentTangentCrossFormula
  rw [circleParameter_succ_sub]

theorem exitTangentCross_eq_formula
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    pointCross (outerTangentPoint stage k)
        (circleSamplePoint stage (k + 1)) =
      adjacentTangentCrossFormula stage k := by
  have hu0 := circleParameter_nonneg stage hstage k
  have hv0 := circleParameter_nonneg stage hstage (k + 1)
  have huv := circleParameter_lt_succ stage hstage k
  have hbase :
      pointCross (outerTangentPoint stage k)
          (circleSamplePoint stage (k + 1)) =
        (circleParameter stage (k + 1) - circleParameter stage k) /
          (1 + circleParameter stage k * circleParameter stage (k + 1)) := by
    simpa [circleSamplePoint, circlePoint, pointCross, outerTangentPoint,
      tangentIntersection, RationalCircle.Stage.point,
      RationalCircle.Stage.cross,
      RationalCircle.Stage.tangentIntersection] using
      RationalCircle.Stage.point_exit_tangent_cross_formula hu0 hv0 huv
  rw [hbase]
  unfold adjacentTangentCrossFormula
  rw [circleParameter_succ_sub]

/-- The two tangent edges in one outer-polygon cell have the same exact
rational length. -/
theorem outerTangentCrossSum_eq_two_adjacentTangentCrossFormula
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    outerTangentCrossSum stage k =
      2 * adjacentTangentCrossFormula stage k := by
  unfold outerTangentCrossSum
  rw [entryTangentCross_eq_formula stage hstage k,
    exitTangentCross_eq_formula stage hstage k]
  grind

/-- The tangent-edge length for the adjacent parameters `k/stage` and
`(k+1)/stage`, in a denominator-cleared rational form. -/
def adjacentTangentCrossClosedForm (stage k : Nat) : Rat :=
  (stage : Rat) /
    ((stage : Rat) * (stage : Rat) + (k : Rat) * ((k + 1 : Nat) : Rat))

private theorem tangentRefinement_cancel_mul_right {a b c : Rat} (hc : c ≠ 0) :
    a * c = b * c -> a = b := by
  intro h
  have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
  calc
    a = a * 1 := by grind
    _ = a * (c * c⁻¹) := by rw [hcancel]
    _ = (a * c) * c⁻¹ := by grind [Rat.mul_assoc]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b * (c * c⁻¹) := by grind [Rat.mul_assoc]
    _ = b * 1 := by rw [hcancel]
    _ = b := by grind

private theorem tangentRefinement_div_two_cancel (a b : Rat) :
    (2 * a) / (2 * b) = a / b := by
  rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by native_decide
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem adjacentTangentCrossFormula_eq_closedForm
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    adjacentTangentCrossFormula stage k =
      adjacentTangentCrossClosedForm stage k := by
  unfold adjacentTangentCrossFormula adjacentTangentCrossClosedForm
  simp only
  rw [show circleParameter stage k = (k : Rat) / (stage : Rat) by rfl]
  rw [show circleParameter stage (k + 1) =
    ((k + 1 : Nat) : Rat) / (stage : Rat) by rfl]
  have hs : (stage : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hstage)
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have hsq : (stage : Rat) * (stage : Rat) ≠ 0 := by
    exact Rat.ne_of_gt (Rat.mul_pos ((Rat.natCast_pos).2 hstage)
      ((Rat.natCast_pos).2 hstage))
  apply tangentRefinement_cancel_mul_right hsq
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem adjacentTangentCrossClosedForm_double_left
    (stage k : Nat) :
    adjacentTangentCrossClosedForm (2 * stage) (2 * k) =
      (stage : Rat) /
        (2 * (stage : Rat) * (stage : Rat) +
          2 * (k : Rat) * (k : Rat) + (k : Rat)) := by
  unfold adjacentTangentCrossClosedForm
  simp only [Rat.natCast_mul, Rat.natCast_add]
  change (2 * (stage : Rat)) /
      ((2 * (stage : Rat)) * (2 * (stage : Rat)) +
        (2 * (k : Rat)) * (2 * (k : Rat) + 1)) =
    (stage : Rat) /
      (2 * (stage : Rat) * (stage : Rat) +
        2 * (k : Rat) * (k : Rat) + (k : Rat))
  have hden :
      (2 * (stage : Rat)) * (2 * (stage : Rat)) +
          (2 * (k : Rat)) * (2 * (k : Rat) + 1) =
        2 * (2 * (stage : Rat) * (stage : Rat) +
          2 * (k : Rat) * (k : Rat) + (k : Rat)) := by
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hden]
  exact tangentRefinement_div_two_cancel _ _

private theorem adjacentTangentCrossClosedForm_double_right
    (stage k : Nat) :
    adjacentTangentCrossClosedForm (2 * stage) (2 * k + 1) =
      (stage : Rat) /
        (2 * (stage : Rat) * (stage : Rat) +
          2 * (k : Rat) * (k : Rat) + 3 * (k : Rat) + 1) := by
  unfold adjacentTangentCrossClosedForm
  simp only [Rat.natCast_mul, Rat.natCast_add]
  change (2 * (stage : Rat)) /
      ((2 * (stage : Rat)) * (2 * (stage : Rat)) +
        (2 * (k : Rat) + 1) * (2 * (k : Rat) + 1 + 1)) =
    (stage : Rat) /
      (2 * (stage : Rat) * (stage : Rat) +
        2 * (k : Rat) * (k : Rat) + 3 * (k : Rat) + 1)
  have hden :
      (2 * (stage : Rat)) * (2 * (stage : Rat)) +
          (2 * (k : Rat) + 1) * (2 * (k : Rat) + 1 + 1) =
        2 * (2 * (stage : Rat) * (stage : Rat) +
          2 * (k : Rat) * (k : Rat) + 3 * (k : Rat) + 1) := by
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hden]
  exact tangentRefinement_div_two_cancel _ _

private theorem tangentCrossClosedForm_refinement_algebra
    (N K : Rat) (hN : 0 < N) (hK : 0 <= K) :
    let A := N * N + K * K + K
    let B := 2 * N * N + 2 * K * K + K
    let D := 2 * N * N + 2 * K * K + 3 * K + 1
    N / B + N / D <= N / A := by
  dsimp
  let A : Rat := N * N + K * K + K
  let B : Rat := 2 * N * N + 2 * K * K + K
  let D : Rat := 2 * N * N + 2 * K * K + 3 * K + 1
  have hN0 : 0 <= N := Rat.le_of_lt hN
  have hNN : 0 < N * N := Rat.mul_pos hN hN
  have hK2 : 0 <= K * K := Rat.mul_nonneg hK hK
  have hApos : 0 < A := by
    dsimp [A]
    have hrest : 0 <= K * K + K := Rat.add_nonneg hK2 hK
    grind
  have hBpos : 0 < B := by
    dsimp [B]
    have htwoNN : 0 < 2 * N * N := by
      exact Rat.mul_pos (Rat.mul_pos (by native_decide) hN) hN
    have htwoK2 : 0 <= 2 * K * K := by
      calc
        0 <= 2 * (K * K) := Rat.mul_nonneg (by native_decide) hK2
        _ = 2 * K * K := by grind [Rat.mul_assoc]
    have hrest : 0 <= 2 * K * K + K := Rat.add_nonneg htwoK2 hK
    grind
  have hDpos : 0 < D := by
    dsimp [D]
    have htwoNN : 0 < 2 * N * N := by
      exact Rat.mul_pos (Rat.mul_pos (by native_decide) hN) hN
    have hrest : 0 <= 2 * K * K + 3 * K + 1 := by
      have hfirst : 0 <= 2 * K * K := by
        calc
          0 <= 2 * (K * K) := Rat.mul_nonneg (by native_decide) hK2
          _ = 2 * K * K := by grind [Rat.mul_assoc]
      have hsecond : 0 <= 3 * K :=
        Rat.mul_nonneg (by native_decide) hK
      grind
    grind
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
  have hDne : D ≠ 0 := Rat.ne_of_gt hDpos
  have hidentity : B * D - A * (B + D) = N * N := by
    dsimp [A, B, D]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hcore : A * (B + D) <= B * D := by
    have hnonneg : 0 <= N * N := Rat.mul_nonneg hN0 hN0
    rw [show A * (B + D) = B * D - (N * N) by
      rw [← hidentity]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]]
    grind [Rat.sub_eq_add_neg]
  have hscaled : N * (A * (B + D)) <= N * (B * D) :=
    Rat.mul_le_mul_of_nonneg_left hcore hN0
  have hprodpos : 0 < A * B * D :=
    Rat.mul_pos (Rat.mul_pos hApos hBpos) hDpos
  apply Rat.le_of_mul_le_mul_right (c := A * B * D)
  · rw [Rat.div_def, Rat.div_def, Rat.div_def]
    have hAcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
    have hBcancel : B * B⁻¹ = 1 := Rat.mul_inv_cancel B hBne
    have hDcancel : D * D⁻¹ = 1 := Rat.mul_inv_cancel D hDne
    calc
      (N * B⁻¹ + N * D⁻¹) * (A * B * D) =
          N * (A * (B + D)) := by
            grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
              Rat.mul_assoc, Rat.mul_comm]
      _ <= N * (B * D) := hscaled
      _ = (N * A⁻¹) * (A * B * D) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hprodpos

/-- Splitting an adjacent tangent edge at the dyadic midpoint lowers its
exact rational tangent-length bound.  This is the symbolic geometric half of
the upper-endpoint refinement for the direct circumference algorithm. -/
theorem adjacentTangentCrossClosedForm_refinesByDoubling
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    adjacentTangentCrossClosedForm (2 * stage) (2 * k) +
      adjacentTangentCrossClosedForm (2 * stage) (2 * k + 1) <=
      adjacentTangentCrossClosedForm stage k := by
  have h := tangentCrossClosedForm_refinement_algebra (stage : Rat) (k : Rat)
    ((Rat.natCast_pos).2 hstage) Rat.natCast_nonneg
  rw [adjacentTangentCrossClosedForm_double_left,
    adjacentTangentCrossClosedForm_double_right]
  unfold adjacentTangentCrossClosedForm
  have hksucc : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
    rw [Rat.natCast_add]
    rfl
  calc
    (stage : Rat) /
          (2 * (stage : Rat) * (stage : Rat) +
            2 * (k : Rat) * (k : Rat) + (k : Rat)) +
        (stage : Rat) /
          (2 * (stage : Rat) * (stage : Rat) +
            2 * (k : Rat) * (k : Rat) + 3 * (k : Rat) + 1) <=
      (stage : Rat) /
        ((stage : Rat) * (stage : Rat) + (k : Rat) * (k : Rat) + (k : Rat)) := h
    _ = (stage : Rat) /
        ((stage : Rat) * (stage : Rat) + (k : Rat) * ((k + 1 : Nat) : Rat)) := by
      rw [hksucc]
      congr 1
      grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

theorem outerTangentCrossSum_refinesByDoubling
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    outerTangentCrossSum (2 * stage) (2 * k) +
      outerTangentCrossSum (2 * stage) (2 * k + 1) <=
      outerTangentCrossSum stage k := by
  have hfine : 0 < 2 * stage := by omega
  rw [outerTangentCrossSum_eq_two_adjacentTangentCrossFormula (2 * stage)
      hfine (2 * k),
    outerTangentCrossSum_eq_two_adjacentTangentCrossFormula (2 * stage)
      hfine (2 * k + 1),
    outerTangentCrossSum_eq_two_adjacentTangentCrossFormula stage hstage k,
    adjacentTangentCrossFormula_eq_closedForm (2 * stage) hfine (2 * k),
    adjacentTangentCrossFormula_eq_closedForm (2 * stage) hfine (2 * k + 1),
    adjacentTangentCrossFormula_eq_closedForm stage hstage k]
  have h := adjacentTangentCrossClosedForm_refinesByDoubling stage hstage k
  calc
    2 * adjacentTangentCrossClosedForm (2 * stage) (2 * k) +
          2 * adjacentTangentCrossClosedForm (2 * stage) (2 * k + 1) =
        2 * (adjacentTangentCrossClosedForm (2 * stage) (2 * k) +
          adjacentTangentCrossClosedForm (2 * stage) (2 * k + 1)) := by
          grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]
    _ <= 2 * adjacentTangentCrossClosedForm stage k :=
      Rat.mul_le_mul_of_nonneg_left h (by native_decide)

/-- The exact rational perimeter of a consecutive block of outer tangent
cells.  Unlike the square-root path evaluator, this records the tangent
segment lengths directly through their rational cross-product formulas. -/
def outerTangentCrossSumFrom (stage k : Nat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      outerTangentCrossSum stage k +
        outerTangentCrossSumFrom stage (k + 1) count

private theorem outerTangentCrossSumFrom_refinesByDoubling_aux
    (stage : Nat) (hstage : 0 < stage) (count k : Nat) :
    outerTangentCrossSumFrom (2 * stage) (2 * k) (2 * count) <=
      outerTangentCrossSumFrom stage k count := by
  induction count generalizing k with
  | zero =>
      simp [outerTangentCrossSumFrom]
  | succ count ih =>
      have hlocal := outerTangentCrossSum_refinesByDoubling stage hstage k
      have htail := ih (k + 1)
      rw [show 2 * (count + 1) = 2 * count + 2 by omega]
      simp only [outerTangentCrossSumFrom]
      have htail' :
          outerTangentCrossSumFrom (2 * stage) (2 * k + 1 + 1)
              (2 * count) <=
            outerTangentCrossSumFrom stage (k + 1) count := by
        have hindex : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
        rw [hindex] at htail
        exact htail
      calc
        outerTangentCrossSum (2 * stage) (2 * k) +
              (outerTangentCrossSum (2 * stage) (2 * k + 1) +
                outerTangentCrossSumFrom (2 * stage) (2 * k + 2)
                  (2 * count)) =
            (outerTangentCrossSum (2 * stage) (2 * k) +
              outerTangentCrossSum (2 * stage) (2 * k + 1)) +
                outerTangentCrossSumFrom (2 * stage) (2 * k + 2)
                  (2 * count) := by
              grind [Rat.add_assoc, Rat.add_comm]
        _ <= outerTangentCrossSum stage k +
              outerTangentCrossSumFrom stage (k + 1) count := by
              calc
                (outerTangentCrossSum (2 * stage) (2 * k) +
                    outerTangentCrossSum (2 * stage) (2 * k + 1)) +
                    outerTangentCrossSumFrom (2 * stage) (2 * k + 1 + 1)
                      (2 * count) <=
                  outerTangentCrossSum stage k +
                    outerTangentCrossSumFrom (2 * stage) (2 * k + 1 + 1)
                      (2 * count) :=
                    Rat.add_le_add_right.mpr hlocal
                _ <= outerTangentCrossSum stage k +
                    outerTangentCrossSumFrom stage (k + 1) count :=
                    by
                      rw [Rat.add_le_add_left]
                      exact htail'

/-- Exact rational tangent perimeter decreases under dyadic subdivision. -/
theorem outerTangentCrossSumFrom_refinesByDoubling
    (stage : Nat) (hstage : 0 < stage) (count k : Nat) :
    outerTangentCrossSumFrom (2 * stage) (2 * k) (2 * count) <=
      outerTangentCrossSumFrom stage k count :=
  outerTangentCrossSumFrom_refinesByDoubling_aux stage hstage count k

theorem adjacentChordCross_eq_formula
    (stage : Nat) (k : Nat) :
    pointCross (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) =
      let u := circleParameter stage k
      let v := circleParameter stage (k + 1)
      let d : Rat := 1 / (stage : Rat)
      (2 * d * (1 + u * v)) /
        ((1 + u * u) * (1 + v * v)) := by
  let u := circleParameter stage k
  let v := circleParameter stage (k + 1)
  have hbase :
      pointCross (circleSamplePoint stage k)
          (circleSamplePoint stage (k + 1)) =
        (2 * (v - u) * (1 + u * v)) /
          ((1 + u * u) * (1 + v * v)) := by
    simpa [circleSamplePoint, circlePoint, pointCross, u, v,
      RationalCircle.Stage.point, RationalCircle.Stage.cross] using
      RationalCircle.Stage.point_cross_formula u v
  rw [hbase]
  dsimp [u, v]
  rw [circleParameter_succ_sub]

theorem entryTangentSegmentNormSq_eq_formula
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    pointSegmentNormSq
        (circleSamplePoint stage k) (outerTangentPoint stage k) =
      entryTangentNormSqFormula stage k := by
  rw [entryTangentSegmentNormSq_eq_cross_sq stage hstage k]
  rw [entryTangentCross_eq_formula stage hstage k]
  rfl

theorem exitTangentSegmentNormSq_eq_formula
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    pointSegmentNormSq
        (outerTangentPoint stage k) (circleSamplePoint stage (k + 1)) =
      exitTangentNormSqFormula stage k := by
  rw [exitTangentSegmentNormSq_eq_cross_sq stage hstage k]
  rw [exitTangentCross_eq_formula stage hstage k]
  rfl

theorem adjacentChordNormSqFormula_nonneg
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    0 <= adjacentChordNormSqFormula stage k := by
  unfold adjacentChordNormSqFormula
  let u := circleParameter stage k
  let v := circleParameter stage (k + 1)
  let d : Rat := 1 / (stage : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hstage)
  have hnum : 0 <= 4 * d * d := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 4)
        (Rat.le_of_lt hdpos))
      (Rat.le_of_lt hdpos)
  have hdenpos : 0 < (1 + u * u) * (1 + v * v) :=
    Rat.mul_pos (RationalCircle.Stage.one_add_square_pos u)
      (RationalCircle.Stage.one_add_square_pos v)
  rw [Rat.div_def]
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))

theorem adjacentTangentCrossFormula_pos
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    0 < adjacentTangentCrossFormula stage k := by
  unfold adjacentTangentCrossFormula
  let u := circleParameter stage k
  let v := circleParameter stage (k + 1)
  let d : Rat := 1 / (stage : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hstage)
  have hu0 : 0 <= u := by
    dsimp [u]
    exact circleParameter_nonneg stage hstage k
  have hv0 : 0 <= v := by
    dsimp [v]
    exact circleParameter_nonneg stage hstage (k + 1)
  have hdenpos : 0 < 1 + u * v :=
    RationalCircle.Stage.one_add_mul_pos_of_nonneg hu0 hv0
  rw [Rat.div_def]
  exact Rat.mul_pos hdpos ((Rat.inv_pos).2 hdenpos)

theorem entryTangentNormSqFormula_nonneg
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    0 <= entryTangentNormSqFormula stage k := by
  unfold entryTangentNormSqFormula sq
  have h := adjacentTangentCrossFormula_pos stage hstage k
  exact Rat.mul_nonneg (Rat.le_of_lt h) (Rat.le_of_lt h)

theorem exitTangentNormSqFormula_nonneg
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    0 <= exitTangentNormSqFormula stage k := by
  unfold exitTangentNormSqFormula sq
  have h := adjacentTangentCrossFormula_pos stage hstage k
  exact Rat.mul_nonneg (Rat.le_of_lt h) (Rat.le_of_lt h)

def FormulaBudgetLeAt (precision : Nat) (B q : Rat) : Prop :=
  sqrtUpperBound q /
      (((2 ^ sqrtFuel q (sqrtStageEps precision) : Nat) : Rat)) <= B

def InnerAdjacentChordFormulaBudgetLe (stage : Nat) (B : Rat) : Prop :=
  forall k,
    FormulaBudgetLeAt stage B (adjacentChordNormSqFormula stage k)

def OuterAdjacentTangentFormulaBudgetLe (stage : Nat) (B : Rat) : Prop :=
  forall k,
    FormulaBudgetLeAt stage B (entryTangentNormSqFormula stage k) /\
      FormulaBudgetLeAt stage B (exitTangentNormSqFormula stage k)

def InnerAdjacentChordFormulaBudgetLeUpTo (stage : Nat) (B : Rat) : Prop :=
  forall k, k < stage ->
    FormulaBudgetLeAt stage B (adjacentChordNormSqFormula stage k)

def OuterAdjacentTangentFormulaBudgetLeUpTo (stage : Nat) (B : Rat) : Prop :=
  forall k, k < stage ->
    FormulaBudgetLeAt stage B (entryTangentNormSqFormula stage k) /\
      FormulaBudgetLeAt stage B (exitTangentNormSqFormula stage k)

private theorem sqrtUpperBound_le_two_of_le_two {q : Rat}
    (hq : q <= 2) :
    sqrtUpperBound q <= 2 := by
  unfold sqrtUpperBound maxRat
  split <;> grind

private theorem one_le_one_add_square (u : Rat) :
    (1 : Rat) <= 1 + u * u := by
  have hs := RationalCircle.Stage.ratSquare_nonneg u
  grind

private theorem one_le_one_add_mul_of_nonneg
    {u v : Rat} (hu : 0 <= u) (hv : 0 <= v) :
    (1 : Rat) <= 1 + u * v := by
  have huv : 0 <= u * v := Rat.mul_nonneg hu hv
  grind

private theorem one_le_mul_three_of_one_le
    {A B C : Rat} (hA : (1 : Rat) <= A)
    (hB : (1 : Rat) <= B) (hC : (1 : Rat) <= C) :
    (1 : Rat) <= A * B * C := by
  have hB0 : 0 <= B := by grind
  have hC0 : 0 <= C := by grind
  have hAB : (1 : Rat) <= A * B := by
    calc
      (1 : Rat) = 1 * 1 := by grind
      _ <= A * 1 := Rat.mul_le_mul_of_nonneg_right hA
        (by native_decide)
      _ <= A * B := Rat.mul_le_mul_of_nonneg_left hB (by grind)
  calc
    (1 : Rat) = 1 * 1 := by grind
    _ <= (A * B) * 1 := Rat.mul_le_mul_of_nonneg_right hAB
      (by native_decide)
    _ <= (A * B) * C := Rat.mul_le_mul_of_nonneg_left hC (by grind)

private theorem tangent_chord_gap_le_two_cube
    {u v d : Rat} (hdpos : 0 < d) (hd : d = v - u)
    (hu0 : 0 <= u) (hv0 : 0 <= v) :
    2 * (d / (1 + u * v)) -
        (2 * d * (1 + u * v)) /
          ((1 + u * u) * (1 + v * v)) <=
      2 * d * d * d := by
  let A : Rat := 1 + u * v
  let B : Rat := 1 + u * u
  let C : Rat := 1 + v * v
  let D : Rat := A * B * C
  have hApos : 0 < A := by
    dsimp [A]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hu0 hv0
  have hBpos : 0 < B := by
    dsimp [B]
    exact RationalCircle.Stage.one_add_square_pos u
  have hCpos : 0 < C := by
    dsimp [C]
    exact RationalCircle.Stage.one_add_square_pos v
  have hDpos : 0 < D := by
    dsimp [D]
    exact Rat.mul_pos (Rat.mul_pos hApos hBpos) hCpos
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have hBCne : B * C ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hBpos hCpos)
  have hDge : (1 : Rat) <= D := by
    dsimp [D, A, B, C]
    exact one_le_mul_three_of_one_le
      (one_le_one_add_mul_of_nonneg hu0 hv0)
      (one_le_one_add_square u)
      (one_le_one_add_square v)
  have hcube_nonneg : 0 <= 2 * d * d * d := by
    have hd0 : 0 <= d := Rat.le_of_lt hdpos
    exact Rat.mul_nonneg
      (Rat.mul_nonneg
        (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hd0)
        hd0)
      hd0
  have hleft :
      (2 * (d / A) - (2 * d * A) / (B * C)) * D =
        2 * d * (B * C - A * A) := by
    dsimp [D]
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  have hdiff : B * C - A * A = (v - u) * (v - u) := by
    dsimp [A, B, C]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hleft_le :
      2 * d * (B * C - A * A) <= (2 * d * d * d) * D := by
    rw [hdiff, ← hd]
    calc
      2 * d * (d * d) = 2 * d * d * d := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ = (2 * d * d * d) * 1 := by grind
      _ <= (2 * d * d * d) * D :=
        Rat.mul_le_mul_of_nonneg_left hDge hcube_nonneg
  apply Rat.le_of_mul_le_mul_right (c := D)
  · dsimp [A, B, C] at hleft hleft_le
    rw [hleft]
    simpa [D] using hleft_le
  · exact hDpos

private theorem adjacentFanGap_le_two_step_cube
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    2 * adjacentTangentCrossFormula stage k -
        pointCross (circleSamplePoint stage k)
          (circleSamplePoint stage (k + 1)) <=
      2 * (1 / (stage : Rat)) *
        (1 / (stage : Rat)) * (1 / (stage : Rat)) := by
  let u := circleParameter stage k
  let v := circleParameter stage (k + 1)
  let d : Rat := 1 / (stage : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hstage)
  have hd : d = v - u := by
    dsimp [d, u, v]
    rw [circleParameter_succ_sub]
  have hu0 : 0 <= u := by
    dsimp [u]
    exact circleParameter_nonneg stage hstage k
  have hv0 : 0 <= v := by
    dsimp [v]
    exact circleParameter_nonneg stage hstage (k + 1)
  rw [adjacentChordCross_eq_formula stage k]
  unfold adjacentTangentCrossFormula
  dsimp [u, v, d]
  exact tangent_chord_gap_le_two_cube hdpos hd hu0 hv0

private theorem adjacentTangentCrossFormula_le_one
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    adjacentTangentCrossFormula stage k <= 1 := by
  unfold adjacentTangentCrossFormula
  let u := circleParameter stage k
  let v := circleParameter stage (k + 1)
  let d : Rat := 1 / (stage : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hstage)
  have hdle1 : d <= 1 := by
    dsimp [d]
    have hone : (1 / (1 : Rat)) = 1 := by native_decide
    simpa [hone] using
      (FTC.one_div_nat_antitone (n := 1) (m := stage)
        (by omega) hstage (by omega : 1 <= stage))
  have hu0 : 0 <= u := by
    dsimp [u]
    exact circleParameter_nonneg stage hstage k
  have hv0 : 0 <= v := by
    dsimp [v]
    exact circleParameter_nonneg stage hstage (k + 1)
  have hden_ge_one : (1 : Rat) <= 1 + u * v :=
    one_le_one_add_mul_of_nonneg hu0 hv0
  have hden_pos : 0 < 1 + u * v :=
    RationalCircle.Stage.one_add_mul_pos_of_nonneg hu0 hv0
  have hd_le_den : d <= 1 + u * v := Rat.le_trans hdle1 hden_ge_one
  rw [Rat.div_def]
  calc
    d * (1 + u * v)⁻¹ <= (1 + u * v) * (1 + u * v)⁻¹ := by
      exact Rat.mul_le_mul_of_nonneg_right hd_le_den
        (Rat.le_of_lt ((Rat.inv_pos).2 hden_pos))
    _ = 1 := by
      exact Rat.mul_inv_cancel (1 + u * v) (Rat.ne_of_gt hden_pos)

private theorem entryTangentNormSqFormula_le_two
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    entryTangentNormSqFormula stage k <= 2 := by
  unfold entryTangentNormSqFormula
  have hpos := adjacentTangentCrossFormula_pos stage hstage k
  have hle := adjacentTangentCrossFormula_le_one stage hstage k
  have hsquare :
      sq (adjacentTangentCrossFormula stage k) <= sq (1 : Rat) :=
    sq_le_sq_of_nonneg_le (Rat.le_of_lt hpos) hle
  unfold sq at hsquare
  calc
    adjacentTangentCrossFormula stage k *
        adjacentTangentCrossFormula stage k <= 1 := by
      simpa using hsquare
    _ <= 2 := by native_decide

private theorem exitTangentNormSqFormula_le_two
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    exitTangentNormSqFormula stage k <= 2 := by
  simpa [exitTangentNormSqFormula, entryTangentNormSqFormula] using
    entryTangentNormSqFormula_le_two stage hstage k

private theorem adjacentChordNormSqFormula_le_two
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    adjacentChordNormSqFormula stage k <= 2 := by
  unfold adjacentChordNormSqFormula
  let u := circleParameter stage k
  let v := circleParameter stage (k + 1)
  let d : Rat := 1 / (stage : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hstage)
  have hd0 : 0 <= d := Rat.le_of_lt hdpos
  have hdle1 : d <= 1 := by
    dsimp [d]
    have hone : (1 / (1 : Rat)) = 1 := by native_decide
    simpa [hone] using
      (FTC.one_div_nat_antitone (n := 1) (m := stage)
        (by omega) hstage (by omega : 1 <= stage))
  have hu0 : 0 <= u := by
    dsimp [u]
    exact circleParameter_nonneg stage hstage k
  have hv0 : 0 <= v := by
    dsimp [v]
    exact circleParameter_nonneg stage hstage (k + 1)
  have hd_eq : d = v - u := by
    dsimp [d, u, v]
    rw [circleParameter_succ_sub]
  have hd_le_v : d <= v := by
    rw [hd_eq]
    grind [Rat.sub_eq_add_neg]
  have hd_sq_le_v_sq : d * d <= v * v := by
    have hs := sq_le_sq_of_nonneg_le hd0 hd_le_v
    simpa [sq] using hs
  have hden_pos :
      0 < (1 + u * u) * (1 + v * v) := by
    exact Rat.mul_pos
      (RationalCircle.Stage.one_add_square_pos u)
      (RationalCircle.Stage.one_add_square_pos v)
  have hden_ge :
      1 + d * d <= (1 + u * u) * (1 + v * v) := by
    have hleft : 1 + d * d <= 1 + v * v := by
      grind
    have hright : 1 + v * v <= (1 + u * u) * (1 + v * v) := by
      have honeu : 1 <= 1 + u * u := one_le_one_add_square u
      have hvpos : 0 <= 1 + v * v :=
        Rat.le_of_lt (RationalCircle.Stage.one_add_square_pos v)
      calc
        1 + v * v = 1 * (1 + v * v) := by grind
        _ <= (1 + u * u) * (1 + v * v) :=
          Rat.mul_le_mul_of_nonneg_right honeu hvpos
    exact Rat.le_trans hleft hright
  have hd_sq_le_one : d * d <= 1 := by
    have hs := sq_le_sq_of_nonneg_le hd0 hdle1
    simpa [sq] using hs
  have hnum_le : 4 * d * d <= 2 * (1 + d * d) := by
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
      Rat.add_assoc, Rat.add_comm]
  have hscaled :
      4 * d * d <= 2 * ((1 + u * u) * (1 + v * v)) := by
    exact Rat.le_trans hnum_le
      (Rat.mul_le_mul_of_nonneg_left hden_ge
        (by native_decide : (0 : Rat) <= 2))
  apply Rat.le_of_mul_le_mul_right
    (c := (1 + u * u) * (1 + v * v))
  · rw [Rat.div_def]
    have hden_ne :
        (1 + u * u) * (1 + v * v) ≠ 0 := Rat.ne_of_gt hden_pos
    calc
      (4 * d * d * ((1 + u * u) * (1 + v * v))⁻¹) *
          ((1 + u * u) * (1 + v * v)) =
          4 * d * d := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= 2 * ((1 + u * u) * (1 + v * v)) := hscaled
      _ = 2 * ((1 + u * u) * (1 + v * v)) := rfl
  · exact hden_pos

private theorem formulaBudgetLeAt_of_sqrtUpperBound_le_two
    {precision : Nat} (hprecision : precision ≠ 0)
    {B q : Rat}
    (hub : sqrtUpperBound q <= 2)
    (hbudget :
      2 / (((2 ^ (precision + 9) : Nat) : Rat)) <= B) :
    FormulaBudgetLeAt precision B q := by
  unfold FormulaBudgetLeAt
  let fuel : Nat := sqrtFuel q (sqrtStageEps precision)
  have hfuel_ge : precision + 9 <= fuel := by
    dsimp [fuel]
    rw [sqrtFuel_sqrtStageEps_eq q precision hprecision]
    have hden_pos : 0 < (sqrtUpperBound q).den :=
      Nat.pos_of_ne_zero (sqrtUpperBound q).den_nz
    omega
  have hpow_ge : 2 ^ (precision + 9) <= 2 ^ fuel :=
    Nat.pow_le_pow_right (by omega : 0 < 2) hfuel_ge
  have hfuel_pos : 0 < 2 ^ fuel :=
    Nat.pow_pos (by omega : 0 < 2)
  have hsmall :
      1 / (((2 ^ fuel : Nat) : Rat)) <=
        1 / (((2 ^ (precision + 9) : Nat) : Rat)) :=
    FTC.one_div_nat_antitone
      (Nat.pow_pos (by omega : 0 < 2)) hfuel_pos hpow_ge
  have hfuel_nonneg :
      0 <= 1 / (((2 ^ fuel : Nat) : Rat)) := by
    exact Rat.le_of_lt
      (one_div_nat_pos (Nat.pow_pos (by omega : 0 < 2)))
  calc
    sqrtUpperBound q /
        (((2 ^ sqrtFuel q (sqrtStageEps precision) : Nat) : Rat)) =
        sqrtUpperBound q * (1 / (((2 ^ fuel : Nat) : Rat))) := by
      dsimp [fuel]
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= 2 * (1 / (((2 ^ fuel : Nat) : Rat))) := by
      exact Rat.mul_le_mul_of_nonneg_right hub hfuel_nonneg
    _ <= 2 * (1 / (((2 ^ (precision + 9) : Nat) : Rat))) := by
      exact Rat.mul_le_mul_of_nonneg_left hsmall
        (by native_decide : (0 : Rat) <= 2)
    _ = 2 / (((2 ^ (precision + 9) : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= B := hbudget

private theorem succ_le_two_pow_local (n : Nat) : n + 1 <= 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 2 * (n + 1) := by omega
        _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by
          rw [Nat.pow_succ]
          omega

private theorem two_mul_le_two_pow_of_four_le
    (n : Nat) (h4 : 4 <= n) :
    n + n <= 2 ^ n := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      by_cases h4n : 4 <= n
      · have hih := ih h4n
        calc
          n + 1 + (n + 1) = n + n + 2 := by omega
          _ <= 2 ^ n + 2 := Nat.add_le_add_right hih 2
          _ <= 2 ^ n + 2 ^ n := by
            exact Nat.add_le_add_left
              (Nat.le_trans (by native_decide : 2 <= 2 ^ 1)
                (Nat.pow_le_pow_right (by omega : 0 < 2)
                  (by omega : 1 <= n)))
              (2 ^ n)
          _ = 2 ^ (n + 1) := by
            rw [Nat.pow_succ]
            omega
      · have hn3 : n = 3 := by omega
        subst n
        native_decide

private theorem two_mul_le_two_pow_add_eight (n : Nat) :
    n + n <= 2 ^ n + 8 := by
  by_cases h4 : 4 <= n
  · exact Nat.le_trans (two_mul_le_two_pow_of_four_le n h4)
      (by omega)
  · cases n with
    | zero => native_decide
    | succ n =>
        cases n with
        | zero => native_decide
        | succ n =>
            cases n with
            | zero => native_decide
            | succ n =>
                cases n with
                | zero => native_decide
                | succ n => omega

private theorem piStage_mul_succ_le_two_pow_stage_add_eight
    (n : Nat) :
    piStage n * (n + 1) <= 2 ^ (piStage n + 8) := by
  have hsucc : n + 1 <= piStage n := by
    simpa [piStage] using succ_le_two_pow_local n
  have hsquare :
      piStage n * piStage n = 2 ^ (n + n) := by
    unfold piStage
    rw [← Nat.pow_add]
  have hexp :
      2 ^ (n + n) <= 2 ^ (piStage n + 8) :=
    Nat.pow_le_pow_right (by omega : 0 < 2)
      (by
        simpa [piStage] using two_mul_le_two_pow_add_eight n)
  calc
    piStage n * (n + 1) <= piStage n * piStage n :=
      Nat.mul_le_mul_left (piStage n) hsucc
    _ = 2 ^ (n + n) := hsquare
    _ <= 2 ^ (piStage n + 8) := hexp

private theorem two_mul_piStage_mul_succ_le_two_pow_stage_add_nine
    (n : Nat) :
    2 * (piStage n * (n + 1)) <= 2 ^ (piStage n + 9) := by
  calc
    2 * (piStage n * (n + 1)) <=
        2 * 2 ^ (piStage n + 8) :=
      Nat.mul_le_mul_left 2
        (piStage_mul_succ_le_two_pow_stage_add_eight n)
    _ = 2 ^ (piStage n + 8) * 2 := by
      rw [Nat.mul_comm]
    _ = 2 ^ (piStage n + 8 + 1) := by
      exact (Nat.pow_succ 2 (piStage n + 8)).symm
    _ = 2 ^ (piStage n + 9) := by
      congr 1 <;> omega

/-- The polynomial numerator needed for the scheduled Leibniz/rectangle
comparison is absorbed by the exponentially finer dyadic mesh. -/
private theorem leibniz_bridge_numerator_le_mesh_power (n : Nat) :
    2 * n * (2 * n + 1) <= 2 ^ (piStage n + 10) := by
  have hn_stage : n <= piStage n := by
    exact Nat.le_trans (Nat.le_succ n)
      (by simpa [piStage] using succ_le_two_pow_local n)
  have hleft : 2 * n <= 2 * piStage n :=
    Nat.mul_le_mul_left 2 hn_stage
  have hright : 2 * n + 1 <= 2 * (n + 1) := by omega
  have hproduct : 2 * n * (2 * n + 1) <=
      (2 * piStage n) * (2 * (n + 1)) :=
    Nat.mul_le_mul hleft hright
  calc
    2 * n * (2 * n + 1) <= (2 * piStage n) * (2 * (n + 1)) := hproduct
    _ = 2 * (2 * (piStage n * (n + 1))) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ <= 2 * 2 ^ (piStage n + 9) :=
      Nat.mul_le_mul_left 2
        (two_mul_piStage_mul_succ_le_two_pow_stage_add_nine n)
    _ = 2 ^ (piStage n + 10) := by
      rw [Nat.mul_comm]
      rw [← Nat.pow_succ]

/-- The mesh used to compare a Leibniz stage with the geometric rectangle
construction.  Its rapidly increasing refinement makes the finite polynomial
quadrature error smaller than the dyadic zero enclosure at the same stage. -/
def leibnizRectangleBridgeMeshStage (n : Nat) : Nat :=
  piStage n + n + 10

private theorem leibnizBridgeMeshStage_monotone {i j : Nat} (hij : i <= j) :
    leibnizRectangleBridgeMeshStage i <= leibnizRectangleBridgeMeshStage j := by
  unfold leibnizRectangleBridgeMeshStage piStage
  have hpow : 2 ^ i <= 2 ^ j :=
    Nat.pow_le_pow_right (by omega : 0 < 2) hij
  omega

def leibnizRectangleBridgeMeshSchedule : RealRaw.StageSchedule where
  stage := leibnizRectangleBridgeMeshStage
  monotone := fun _ _ hij => leibnizBridgeMeshStage_monotone hij
  cofinal := by
    intro target
    refine ⟨target, ?_⟩
    unfold leibnizRectangleBridgeMeshStage
    have hpos := piStage_pos target
    omega

/-- A nested interval representation of zero with radius `1 / 2^n`.  It is
used only to widen a scheduled geometric bracket by a certified vanishing
rational error, then cancelled again by raw-real algebra. -/
def leibnizBridgeDyadicZero : RealRaw where
  compute := fun n => { lo := 0, hi := 1 / (((2 ^ n : Nat) : Rat)) }

private theorem leibnizBridgeDyadicZero_valid :
    leibnizBridgeDyadicZero.Valid := by
  constructor
  · intro n
    change 0 <= 1 / (((2 ^ n : Nat) : Rat)) - 0
    have hpos : 0 < 1 / (((2 ^ n : Nat) : Rat)) :=
      one_div_nat_pos (Nat.pow_pos (by omega : 0 < 2))
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      change 0 <= 0 /\ 0 <= 1 / (((2 ^ m : Nat) : Rat)) /\
        1 / (((2 ^ m : Nat) : Rat)) <= 1 / (((2 ^ n : Nat) : Rat))
      have hpow : 2 ^ n <= 2 ^ m :=
        Nat.pow_le_pow_right (by omega : 0 < 2) hnm
      have hnpos : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
      have hmpos : 0 < 2 ^ m := Nat.pow_pos (by omega : 0 < 2)
      constructor
      · exact Rat.le_refl
      constructor
      · exact Rat.le_of_lt
          (one_div_nat_pos hmpos)
      · exact FTC.one_div_nat_antitone hnpos hmpos hpow
    · intro eps
      refine ⟨eps.val.den, ?_⟩
      intro n hn
      change 1 / (((2 ^ n : Nat) : Rat)) - 0 <= eps.val
      have hpow : n + 1 <= 2 ^ n := succ_le_two_pow_local n
      have hpowpos : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
      have hsmall :
          1 / (((2 ^ n : Nat) : Rat)) <=
            1 / (((n + 1 : Nat) : Rat)) :=
        FTC.one_div_nat_antitone (Nat.succ_pos n) hpowpos hpow
      have hstage : eps.val.den + 1 <= n + 1 := by omega
      have hdenpos : 0 < eps.val.den + 1 := Nat.succ_pos _
      have hnatpos : 0 < n + 1 := Nat.succ_pos _
      have hbound :
          1 / (((n + 1 : Nat) : Rat)) <=
            1 / (((eps.val.den + 1 : Nat) : Rat)) :=
        FTC.one_div_nat_antitone hdenpos hnatpos hstage
      calc
        1 / (((2 ^ n : Nat) : Rat)) - 0 =
            1 / (((2 ^ n : Nat) : Rat)) := by grind [Rat.sub_eq_add_neg]
        _ <= 1 / (((n + 1 : Nat) : Rat)) := hsmall
        _ <= 1 / (((eps.val.den + 1 : Nat) : Rat)) := hbound
        _ <= eps.val := FTC.one_div_den_succ_le_of_pos eps.property

private theorem leibniz_bridge_error_le_dyadic (n : Nat) :
    ((2 * n * (2 * n + 1) : Nat) : Rat) *
        (1 / (((2 ^ leibnizRectangleBridgeMeshStage n : Nat) : Rat))) <=
      1 / (((2 ^ n : Nat) : Rat)) := by
  let C : Nat := 2 * n * (2 * n + 1)
  let A : Nat := 2 ^ (piStage n + 10)
  let B : Nat := 2 ^ n
  have hC : C <= A := by
    dsimp [C, A]
    exact leibniz_bridge_numerator_le_mesh_power n
  have hApos : 0 < A := by
    dsimp [A]
    exact Nat.pow_pos (by omega : 0 < 2)
  have hBpos : 0 < B := by
    dsimp [B]
    exact Nat.pow_pos (by omega : 0 < 2)
  have hmesh : 2 ^ leibnizRectangleBridgeMeshStage n = A * B := by
    unfold leibnizRectangleBridgeMeshStage
    dsimp [A, B]
    rw [show piStage n + n + 10 = (piStage n + 10) + n by omega]
    exact Nat.pow_add 2 (piStage n + 10) n
  change (C : Rat) *
      (1 / (((2 ^ leibnizRectangleBridgeMeshStage n : Nat) : Rat)) ) <=
        1 / (B : Rat)
  rw [hmesh]
  apply Rat.le_of_mul_le_mul_right (c := (A : Rat) * (B : Rat))
  · calc
      ((C : Rat) * (1 / ((A * B : Nat) : Rat))) *
          ((A : Rat) * (B : Rat)) = (C : Rat) := by
            rw [Rat.div_def]
            have hAne : (A : Rat) ≠ 0 :=
              Rat.ne_of_gt ((Rat.natCast_pos).2 hApos)
            have hBne : (B : Rat) ≠ 0 :=
              Rat.ne_of_gt ((Rat.natCast_pos).2 hBpos)
            push_cast
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (A : Rat) := by exact_mod_cast hC
      _ = (1 / (B : Rat)) * ((A : Rat) * (B : Rat)) := by
            rw [Rat.div_def]
            have hBne : (B : Rat) ≠ 0 :=
              Rat.ne_of_gt ((Rat.natCast_pos).2 hBpos)
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos ((Rat.natCast_pos).2 hApos)
      ((Rat.natCast_pos).2 hBpos)

private theorem leibniz_bridge_even_error_le_radius (n : Nat) :
    (2 * (n : Rat)) * ((2 * n + 1 : Nat) : Rat) *
        (1 / (((2 ^ leibnizRectangleBridgeMeshStage n : Nat) : Rat))) <=
      1 / (((2 ^ n : Nat) : Rat)) := by
  have hcast :
      (2 * (n : Rat)) * ((2 * n + 1 : Nat) : Rat) =
        ((2 * n * (2 * n + 1) : Nat) : Rat) := by
    exact_mod_cast (by rfl : 2 * n * (2 * n + 1) = 2 * n * (2 * n + 1))
  rw [hcast]
  exact leibniz_bridge_error_le_dyadic n

private theorem leibniz_bridge_odd_error_le_radius (n : Nat) :
    ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) *
        (1 / (((2 ^ leibnizRectangleBridgeMeshStage (n + 1) : Nat) : Rat))) <=
      1 / (((2 ^ (n + 1) : Nat) : Rat)) := by
  have hinv : 0 <=
      1 / (((2 ^ leibnizRectangleBridgeMeshStage (n + 1) : Nat) : Rat)) :=
    Rat.le_of_lt (one_div_nat_pos
      (Nat.pow_pos (by omega : 0 < 2)))
  have hcoeff : ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) <=
      (2 * ((n + 1 : Nat) : Rat)) * ((2 * (n + 1) + 1 : Nat) : Rat) := by
    have hleft : ((2 * n + 1 : Nat) : Rat) <=
        ((2 * (n + 1) + 1 : Nat) : Rat) := by
      exact_mod_cast (by omega : 2 * n + 1 <= 2 * (n + 1) + 1)
    have hright : 0 <= ((2 * n + 2 : Nat) : Rat) := Rat.natCast_nonneg
    calc
      ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) <=
          ((2 * (n + 1) + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) :=
            Rat.mul_le_mul_of_nonneg_right hleft hright
      _ = (2 * ((n + 1 : Nat) : Rat)) *
          ((2 * (n + 1) + 1 : Nat) : Rat) := by
            have hnat : 2 * n + 2 = 2 * (n + 1) := by omega
            rw [hnat]
            grind [Rat.mul_assoc, Rat.mul_comm]
  calc
    ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) *
        (1 / (((2 ^ leibnizRectangleBridgeMeshStage (n + 1) : Nat) : Rat))) <=
        (2 * ((n + 1 : Nat) : Rat)) *
          ((2 * (n + 1) + 1 : Nat) : Rat) *
          (1 / (((2 ^ leibnizRectangleBridgeMeshStage (n + 1) : Nat) : Rat))) :=
            Rat.mul_le_mul_of_nonneg_right hcoeff hinv
    _ <= 1 / (((2 ^ (n + 1) : Nat) : Rat)) :=
      leibniz_bridge_even_error_le_radius (n + 1)

private theorem arctan_square_le_one
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    x * x <= 1 := by
  calc
    x * x <= 1 * x := Rat.mul_le_mul_of_nonneg_right hx1 hx0
    _ = x := by rw [Rat.one_mul]
    _ <= 1 := hx1

private theorem arctan_bridge_mesh_factor_le_one
    {x C : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (hC : 0 <= C)
    (stage : Nat) :
    C * (x * x / (((2 ^ stage : Nat) : Rat))) <=
      C * (1 / (((2 ^ stage : Nat) : Rat))) := by
  have hxx := arctan_square_le_one hx0 hx1
  have hdenpos : 0 < ((2 ^ stage : Nat) : Rat) :=
    (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hinv : 0 <= (((2 ^ stage : Nat) : Rat))⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
  rw [Rat.div_def, Rat.div_def]
  calc
    C * (x * x * (((2 ^ stage : Nat) : Rat))⁻¹) =
        (x * x) * (C * (((2 ^ stage : Nat) : Rat))⁻¹) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= 1 * (C * (((2 ^ stage : Nat) : Rat))⁻¹) :=
      Rat.mul_le_mul_of_nonneg_right hxx (Rat.mul_nonneg hC hinv)
    _ = C * (1 * (((2 ^ stage : Nat) : Rat))⁻¹) := by
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem arctan_bridge_even_error_le_radius
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (2 * (n : Rat)) * ((2 * n + 1 : Nat) : Rat) *
        (x * x / (((2 ^ leibnizRectangleBridgeMeshStage n : Nat) : Rat))) <=
      1 / (((2 ^ n : Nat) : Rat)) := by
  have hC : 0 <= (2 * (n : Rat)) * ((2 * n + 1 : Nat) : Rat) :=
    Rat.mul_nonneg
      (Rat.mul_nonneg (by native_decide) Rat.natCast_nonneg)
      Rat.natCast_nonneg
  calc
    (2 * (n : Rat)) * ((2 * n + 1 : Nat) : Rat) *
        (x * x / (((2 ^ leibnizRectangleBridgeMeshStage n : Nat) : Rat))) <=
        (2 * (n : Rat)) * ((2 * n + 1 : Nat) : Rat) *
          (1 / (((2 ^ leibnizRectangleBridgeMeshStage n : Nat) : Rat))) :=
      arctan_bridge_mesh_factor_le_one hx0 hx1 hC
        (leibnizRectangleBridgeMeshStage n)
    _ <= 1 / (((2 ^ n : Nat) : Rat)) :=
      leibniz_bridge_even_error_le_radius n

private theorem arctan_bridge_odd_error_le_radius
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) *
        (x * x /
          (((2 ^ leibnizRectangleBridgeMeshStage (n + 1) : Nat) : Rat))) <=
      1 / (((2 ^ (n + 1) : Nat) : Rat)) := by
  have hC : 0 <= ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) :=
    Rat.mul_nonneg Rat.natCast_nonneg Rat.natCast_nonneg
  calc
    ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) *
        (x * x / (((2 ^ leibnizRectangleBridgeMeshStage (n + 1) : Nat) : Rat))) <=
        ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) *
          (1 / (((2 ^ leibnizRectangleBridgeMeshStage (n + 1) : Nat) : Rat))) :=
      arctan_bridge_mesh_factor_le_one hx0 hx1 hC
        (leibnizRectangleBridgeMeshStage (n + 1))
    _ <= 1 / (((2 ^ (n + 1) : Nat) : Rat)) :=
      leibniz_bridge_odd_error_le_radius n

private theorem scheduledRectangle_lower_le_leibniz_upper_plus_radius
    (n : Nat) :
    (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute
      (leibnizRectangleBridgeMeshStage n)).lo <=
      (leibnizSeries.compute n).hi + 1 / (((2 ^ n : Nat) : Rat)) := by
  let stage := leibnizRectangleBridgeMeshStage n
  let intervals := (ArctanGeometry.arctanAreaLoopState (1 : Rat) stage).intervals
  have hunit : ArctanGeometry.UnitIntervals intervals := by
    dsimp [intervals]
    exact ArctanGeometry.arctanAreaLoopState_intervals_unit
      (x := (1 : Rat)) (by native_decide) (by native_decide) stage
  have hlower :=
    LeibnizRectangleBridge.integralLowerSum_le_kernelPartialRightRectangleSum_even
      n hunit
  have herr :=
    LeibnizRectangleBridge.arctanAreaLoopState_one_kernelPartialRightRectangle_error_bound
      (2 * n) stage
  have hradius := leibniz_bridge_even_error_le_radius n
  rw [LeibnizValidity.leibnizSeries_compute_eq_kernelPartialIntegralInterval n]
  change (ArctanGeometry.arctanIntegralRectangleComputeAtOne stage).lo <=
    LeibnizValidity.upperKernelPartialAtStage n +
      1 / (((2 ^ n : Nat) : Rat))
  change ArctanGeometry.integralLowerSum intervals <=
    LeibnizValidity.upperKernelPartialAtStage n +
      1 / (((2 ^ n : Nat) : Rat))
  have herr' :
      LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n) intervals -
          Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n) <=
        ((2 * n : Nat) : Rat) * ((2 * n + 1 : Nat) : Rat) *
          (1 / (((2 ^ stage : Nat) : Rat))) := by
    simpa [intervals] using herr.2
  have hright : LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n)
      intervals <= Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n) +
        (2 * (n : Rat)) * ((2 * n + 1 : Nat) : Rat) *
          (1 / (((2 ^ stage : Nat) : Rat))) := by
    have hcast : ((2 * n : Nat) : Rat) = 2 * (n : Rat) := by
      exact_mod_cast (by rfl : 2 * n = 2 * n)
    rw [hcast] at herr'
    grind [Rat.sub_eq_add_neg]
  calc
    ArctanGeometry.integralLowerSum intervals <=
        LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n) intervals := hlower
    _ <= Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n) +
        (2 * (n : Rat)) * ((2 * n + 1 : Nat) : Rat) *
          (1 / (((2 ^ stage : Nat) : Rat))) := hright
    _ <= Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n) +
        1 / (((2 ^ n : Nat) : Rat)) :=
      (Rat.add_le_add_left).2 hradius
    _ = LeibnizValidity.upperKernelPartialAtStage n +
        1 / (((2 ^ n : Nat) : Rat)) := by
          simp [LeibnizValidity.upperKernelPartialAtStage]

private theorem leibniz_lower_le_scheduledRectangle_upper_plus_radius
    (n : Nat) :
    (leibnizSeries.compute n).lo <=
      (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute
        (leibnizRectangleBridgeMeshStage n)).hi +
        1 / (((2 ^ n : Nat) : Rat)) := by
  cases n with
  | zero =>
      let stage := leibnizRectangleBridgeMeshStage 0
      let intervals :=
        (ArctanGeometry.arctanAreaLoopState (1 : Rat) stage).intervals
      have hunit : ArctanGeometry.UnitIntervals intervals := by
        dsimp [intervals]
        exact ArctanGeometry.arctanAreaLoopState_intervals_unit
          (x := (1 : Rat)) (by native_decide) (by native_decide) stage
      have hnonneg := ArctanGeometry.integralUpperSum_nonneg intervals
        (ArctanGeometry.unitIntervals_nonnegative intervals hunit)
      change 0 <= ArctanGeometry.integralUpperSum intervals +
        1 / (((2 ^ 0 : Nat) : Rat))
      have hrad : 0 <= 1 / (((2 ^ 0 : Nat) : Rat)) := by native_decide
      grind
  | succ n =>
      let stage := leibnizRectangleBridgeMeshStage (n + 1)
      let intervals := (ArctanGeometry.arctanAreaLoopState (1 : Rat) stage).intervals
      have hunit : ArctanGeometry.UnitIntervals intervals := by
        dsimp [intervals]
        exact ArctanGeometry.arctanAreaLoopState_intervals_unit
          (x := (1 : Rat)) (by native_decide) (by native_decide) stage
      have hupper :=
        LeibnizRectangleBridge.kernelPartialRightRectangleSum_odd_le_integralUpperSum
          n hunit
      have herr :=
        LeibnizRectangleBridge.arctanAreaLoopState_one_kernelPartialRightRectangle_error_bound
          (2 * n + 1) stage
      have hradius := leibniz_bridge_odd_error_le_radius n
      rw [LeibnizValidity.leibnizSeries_compute_eq_kernelPartialIntegralInterval]
      change LeibnizValidity.lowerKernelPartialAtStage (n + 1) <=
        (ArctanGeometry.arctanIntegralRectangleComputeAtOne stage).hi +
          1 / (((2 ^ (n + 1) : Nat) : Rat))
      change LeibnizValidity.lowerKernelPartialAtStage (n + 1) <=
        ArctanGeometry.integralUpperSum intervals +
          1 / (((2 ^ (n + 1) : Nat) : Rat))
      have herr' :
          -(((2 * n + 1 : Nat) : Rat) * ((2 * n + 1 + 1 : Nat) : Rat) *
              (1 / (((2 ^ stage : Nat) : Rat))) ) <=
            LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n + 1)
              intervals -
              Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n + 1) := by
        simpa [intervals] using herr.1
      have hsucc : ((2 * n + 1 + 1 : Nat) : Rat) =
          ((2 * n + 2 : Nat) : Rat) := by
        exact_mod_cast (by omega : 2 * n + 1 + 1 = 2 * n + 2)
      rw [hsucc] at herr'
      have hleft : Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n + 1) <=
          LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n + 1)
            intervals + ((2 * n + 1 : Nat) : Rat) *
              ((2 * n + 2 : Nat) : Rat) *
              (1 / (((2 ^ stage : Nat) : Rat))) := by
        grind [Rat.sub_eq_add_neg]
      calc
        LeibnizValidity.lowerKernelPartialAtStage (n + 1) =
            Taylor.ArctanKernel.kernelPartialIntegralAtOne (2 * n + 1) := by
              simp [LeibnizValidity.lowerKernelPartialAtStage]
        _ <= LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n + 1)
            intervals + ((2 * n + 1 : Nat) : Rat) *
              ((2 * n + 2 : Nat) : Rat) *
              (1 / (((2 ^ stage : Nat) : Rat))) := hleft
        _ <= ArctanGeometry.integralUpperSum intervals +
            ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) *
              (1 / (((2 ^ stage : Nat) : Rat))) :=
          (Rat.add_le_add_right).2 hupper
        _ <= ArctanGeometry.integralUpperSum intervals +
            1 / (((2 ^ (n + 1) : Nat) : Rat)) :=
          (Rat.add_le_add_left).2 hradius

def leibnizRectangleBridgePaddedRaw : RealRaw :=
  (RealRaw.schedule leibnizRectangleBridgeMeshSchedule
    ArctanGeometry.arctanIntegralRectangleRawAtOne -
      leibnizBridgeDyadicZero) + leibnizBridgeDyadicZero

private theorem leibnizRectangleBridgePaddedRaw_valid :
    leibnizRectangleBridgePaddedRaw.Valid := by
  unfold leibnizRectangleBridgePaddedRaw
  exact RealRaw.add_valid
    (RealRaw.sub_valid
      (RealRaw.schedule_valid ArctanGeometry.arctanIntegralRectangleRawAtOne
        ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
        leibnizRectangleBridgeMeshSchedule)
      leibnizBridgeDyadicZero_valid)
    leibnizBridgeDyadicZero_valid

private theorem leibnizSeries_equiv_leibnizRectangleBridgePaddedRaw :
    leibnizSeries.Equiv leibnizRectangleBridgePaddedRaw := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff leibnizSeries
    leibnizRectangleBridgePaddedRaw n n).2
  rw [LeibnizValidity.leibnizSeries_compute_eq_kernelPartialIntegralInterval n]
  change QInterval.Overlaps
    { lo := LeibnizValidity.lowerKernelPartialAtStage n,
      hi := LeibnizValidity.upperKernelPartialAtStage n }
    { lo := (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute
          (leibnizRectangleBridgeMeshStage n)).lo -
          (1 / (((2 ^ n : Nat) : Rat))) + 0,
      hi := (ArctanGeometry.arctanIntegralRectangleRawAtOne.compute
          (leibnizRectangleBridgeMeshStage n)).hi - 0 +
          (1 / (((2 ^ n : Nat) : Rat))) }
  unfold QInterval.Overlaps
  have hlower := leibniz_lower_le_scheduledRectangle_upper_plus_radius n
  have hupper := scheduledRectangle_lower_le_leibniz_upper_plus_radius n
  rw [LeibnizValidity.leibnizSeries_compute_eq_kernelPartialIntegralInterval n] at hlower hupper
  generalize hradius : 1 / (((2 ^ n : Nat) : Rat)) = radius at hlower hupper ⊢
  constructor <;> grind [Rat.sub_eq_add_neg]

private theorem leibnizRectangleBridgePaddedRaw_equiv_scheduledRectangle :
    leibnizRectangleBridgePaddedRaw.Equiv
      (RealRaw.schedule leibnizRectangleBridgeMeshSchedule
        ArctanGeometry.arctanIntegralRectangleRawAtOne) := by
  unfold leibnizRectangleBridgePaddedRaw
  exact RealRaw.sub_add_cancel_equiv
    (RealRaw.schedule_valid ArctanGeometry.arctanIntegralRectangleRawAtOne
      ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
      leibnizRectangleBridgeMeshSchedule)
    leibnizBridgeDyadicZero_valid

/-- The Leibniz raw series and the geometric rectangle raw integral at one
are equivalent without any real-completeness axiom.  The proof schedules an
exponentially finer rational mesh, widens it by a vanishing dyadic zero
interval, and cancels that interval after the finite Taylor error bounds have
established overlap. -/
theorem leibnizEqualsRectangleRawAtOne_finiteRiemannBridge :
    LeibnizEqualsRectangleRawAtOne := by
  unfold LeibnizEqualsRectangleRawAtOne
  have hscheduleValid :
      (RealRaw.schedule leibnizRectangleBridgeMeshSchedule
        ArctanGeometry.arctanIntegralRectangleRawAtOne).Valid :=
    RealRaw.schedule_valid ArctanGeometry.arctanIntegralRectangleRawAtOne
      ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
      leibnizRectangleBridgeMeshSchedule
  have htoScheduled : leibnizSeries.Equiv
      (RealRaw.schedule leibnizRectangleBridgeMeshSchedule
        ArctanGeometry.arctanIntegralRectangleRawAtOne) :=
    RealRaw.equiv_trans leibnizSeriesValid
      leibnizRectangleBridgePaddedRaw_valid hscheduleValid
      leibnizSeries_equiv_leibnizRectangleBridgePaddedRaw
      leibnizRectangleBridgePaddedRaw_equiv_scheduledRectangle
  have hscheduled :
      (RealRaw.schedule leibnizRectangleBridgeMeshSchedule
        ArctanGeometry.arctanIntegralRectangleRawAtOne).Equiv
        ArctanGeometry.arctanIntegralRectangleRawAtOne :=
    RealRaw.equiv_symm
      (RealRaw.schedule_equiv ArctanGeometry.arctanIntegralRectangleRawAtOne
        ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
        leibnizRectangleBridgeMeshSchedule)
  exact RealRaw.equiv_trans leibnizSeriesValid hscheduleValid
    ArctanGeometry.arctanIntegralRectangleRawAtOne_valid
    htoScheduled hscheduled

private theorem scheduledRectangle_lower_le_arctan_upper_plus_radius
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    ((ArctanGeometry.arctanIntegralRectangleRaw x).compute
        (leibnizRectangleBridgeMeshStage n)).lo <=
      ((arctan x).compute n).hi + 1 / (((2 ^ n : Nat) : Rat)) := by
  let stage := leibnizRectangleBridgeMeshStage n
  let intervals := (ArctanGeometry.arctanAreaLoopState x stage).intervals
  have hunit : ArctanGeometry.UnitIntervals intervals := by
    dsimp [intervals]
    exact ArctanGeometry.arctanAreaLoopState_intervals_unit hx0 hx1 stage
  have hlower :=
    LeibnizRectangleBridge.integralLowerSum_le_kernelPartialRightRectangleSum_even
      n hunit
  have herr :=
    LeibnizRectangleBridge.arctanAreaLoopState_kernelPartialRightRectangle_error_bound
      hx0 hx1 (2 * n) stage
  have hradius := arctan_bridge_even_error_le_radius hx0 hx1 n
  rw [ArctanValidity.arctan_compute_nonnegative_eq_kernelPartialIntegralInterval
    x hx0 n]
  change (ArctanGeometry.arctanIntegralRectangleCompute x stage).lo <=
    ArctanValidity.upperKernelPartialAtStage x n +
      1 / (((2 ^ n : Nat) : Rat))
  change ArctanGeometry.integralLowerSum intervals <=
    ArctanValidity.upperKernelPartialAtStage x n +
      1 / (((2 ^ n : Nat) : Rat))
  have herr' :
      LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n) intervals -
          Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x (2 * n) <=
        ((2 * n : Nat) : Rat) * ((2 * n + 1 : Nat) : Rat) *
          (x * x / (((2 ^ stage : Nat) : Rat))) := by
    simpa [intervals] using herr.2
  have hright : LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n)
      intervals <= Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x (2 * n) +
        (2 * (n : Rat)) * ((2 * n + 1 : Nat) : Rat) *
          (x * x / (((2 ^ stage : Nat) : Rat))) := by
    have hcast : ((2 * n : Nat) : Rat) = 2 * (n : Rat) := by
      exact_mod_cast (by rfl : 2 * n = 2 * n)
    rw [hcast] at herr'
    grind [Rat.sub_eq_add_neg]
  calc
    ArctanGeometry.integralLowerSum intervals <=
        LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n) intervals := hlower
    _ <= Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x (2 * n) +
        (2 * (n : Rat)) * ((2 * n + 1 : Nat) : Rat) *
          (x * x / (((2 ^ stage : Nat) : Rat))) := hright
    _ <= Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x (2 * n) +
        1 / (((2 ^ n : Nat) : Rat)) :=
      (Rat.add_le_add_left).2 hradius
    _ = ArctanValidity.upperKernelPartialAtStage x n +
        1 / (((2 ^ n : Nat) : Rat)) := by
          simp [ArctanValidity.upperKernelPartialAtStage]

private theorem arctan_lower_le_scheduledRectangle_upper_plus_radius
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    ((arctan x).compute n).lo <=
      ((ArctanGeometry.arctanIntegralRectangleRaw x).compute
        (leibnizRectangleBridgeMeshStage n)).hi +
        1 / (((2 ^ n : Nat) : Rat)) := by
  cases n with
  | zero =>
      let stage := leibnizRectangleBridgeMeshStage 0
      let intervals := (ArctanGeometry.arctanAreaLoopState x stage).intervals
      have hunit : ArctanGeometry.UnitIntervals intervals := by
        dsimp [intervals]
        exact ArctanGeometry.arctanAreaLoopState_intervals_unit hx0 hx1 stage
      have hnonneg := ArctanGeometry.integralUpperSum_nonneg intervals
        (ArctanGeometry.unitIntervals_nonnegative intervals hunit)
      rw [ArctanValidity.arctan_compute_nonnegative_eq_kernelPartialIntegralInterval
        x hx0 0]
      change 0 <= ArctanGeometry.integralUpperSum intervals +
        1 / (((2 ^ 0 : Nat) : Rat))
      have hrad : 0 <= 1 / (((2 ^ 0 : Nat) : Rat)) := by native_decide
      grind
  | succ n =>
      let stage := leibnizRectangleBridgeMeshStage (n + 1)
      let intervals := (ArctanGeometry.arctanAreaLoopState x stage).intervals
      have hunit : ArctanGeometry.UnitIntervals intervals := by
        dsimp [intervals]
        exact ArctanGeometry.arctanAreaLoopState_intervals_unit hx0 hx1 stage
      have hupper :=
        LeibnizRectangleBridge.kernelPartialRightRectangleSum_odd_le_integralUpperSum
          n hunit
      have herr :=
        LeibnizRectangleBridge.arctanAreaLoopState_kernelPartialRightRectangle_error_bound
          hx0 hx1 (2 * n + 1) stage
      have hradius := arctan_bridge_odd_error_le_radius hx0 hx1 n
      rw [ArctanValidity.arctan_compute_nonnegative_eq_kernelPartialIntegralInterval
        x hx0 (n + 1)]
      change ArctanValidity.lowerKernelPartialAtStage x (n + 1) <=
        (ArctanGeometry.arctanIntegralRectangleCompute x stage).hi +
          1 / (((2 ^ (n + 1) : Nat) : Rat))
      change ArctanValidity.lowerKernelPartialAtStage x (n + 1) <=
        ArctanGeometry.integralUpperSum intervals +
          1 / (((2 ^ (n + 1) : Nat) : Rat))
      have herr' :
          -(((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) *
              (x * x / (((2 ^ stage : Nat) : Rat)))) <=
            LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n + 1)
              intervals -
              Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x (2 * n + 1) := by
        have hsucc : ((2 * n + 1 + 1 : Nat) : Rat) =
            ((2 * n + 2 : Nat) : Rat) := by
          exact_mod_cast (by omega : 2 * n + 1 + 1 = 2 * n + 2)
        rw [hsucc] at herr
        simpa [intervals] using herr.1
      have hleft : Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x
          (2 * n + 1) <=
          LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n + 1)
            intervals + ((2 * n + 1 : Nat) : Rat) *
              ((2 * n + 2 : Nat) : Rat) *
              (x * x / (((2 ^ stage : Nat) : Rat))) := by
        grind [Rat.sub_eq_add_neg]
      calc
        ArctanValidity.lowerKernelPartialAtStage x (n + 1) =
            Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x (2 * n + 1) := by
              simp [ArctanValidity.lowerKernelPartialAtStage]
        _ <= LeibnizRectangleBridge.kernelPartialRightRectangleSum (2 * n + 1)
            intervals + ((2 * n + 1 : Nat) : Rat) *
              ((2 * n + 2 : Nat) : Rat) *
              (x * x / (((2 ^ stage : Nat) : Rat))) := hleft
        _ <= ArctanGeometry.integralUpperSum intervals +
            ((2 * n + 1 : Nat) : Rat) * ((2 * n + 2 : Nat) : Rat) *
              (x * x / (((2 ^ stage : Nat) : Rat))) :=
          (Rat.add_le_add_right).2 hupper
        _ <= ArctanGeometry.integralUpperSum intervals +
            1 / (((2 ^ (n + 1) : Nat) : Rat)) :=
          (Rat.add_le_add_left).2 hradius

private def arctanRectangleBridgePaddedRaw (x : Rat) : RealRaw :=
  (RealRaw.schedule leibnizRectangleBridgeMeshSchedule
    (ArctanGeometry.arctanIntegralRectangleRaw x) -
      leibnizBridgeDyadicZero) + leibnizBridgeDyadicZero

private theorem arctanRectangleBridgePaddedRaw_valid
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanRectangleBridgePaddedRaw x).Valid := by
  unfold arctanRectangleBridgePaddedRaw
  exact RealRaw.add_valid
    (RealRaw.sub_valid
      (RealRaw.schedule_valid (ArctanGeometry.arctanIntegralRectangleRaw x)
        (ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1)
        leibnizRectangleBridgeMeshSchedule)
      leibnizBridgeDyadicZero_valid)
    leibnizBridgeDyadicZero_valid

private theorem arctan_equiv_arctanRectangleBridgePaddedRaw
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctan x).Equiv (arctanRectangleBridgePaddedRaw x) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff (arctan x)
    (arctanRectangleBridgePaddedRaw x) n n).2
  rw [ArctanValidity.arctan_compute_nonnegative_eq_kernelPartialIntegralInterval
    x hx0 n]
  change QInterval.Overlaps
    { lo := ArctanValidity.lowerKernelPartialAtStage x n,
      hi := ArctanValidity.upperKernelPartialAtStage x n }
    { lo := ((ArctanGeometry.arctanIntegralRectangleRaw x).compute
          (leibnizRectangleBridgeMeshStage n)).lo -
          (1 / (((2 ^ n : Nat) : Rat))) + 0,
      hi := ((ArctanGeometry.arctanIntegralRectangleRaw x).compute
          (leibnizRectangleBridgeMeshStage n)).hi - 0 +
          (1 / (((2 ^ n : Nat) : Rat))) }
  unfold QInterval.Overlaps
  have hlower := arctan_lower_le_scheduledRectangle_upper_plus_radius hx0 hx1 n
  have hupper := scheduledRectangle_lower_le_arctan_upper_plus_radius hx0 hx1 n
  rw [ArctanValidity.arctan_compute_nonnegative_eq_kernelPartialIntegralInterval
    x hx0 n] at hlower hupper
  generalize hradius : 1 / (((2 ^ n : Nat) : Rat)) = radius at hlower hupper ⊢
  constructor <;> grind [Rat.sub_eq_add_neg]

private theorem arctanRectangleBridgePaddedRaw_equiv_scheduledRectangle
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanRectangleBridgePaddedRaw x).Equiv
      (RealRaw.schedule leibnizRectangleBridgeMeshSchedule
        (ArctanGeometry.arctanIntegralRectangleRaw x)) := by
  unfold arctanRectangleBridgePaddedRaw
  exact RealRaw.sub_add_cancel_equiv
    (RealRaw.schedule_valid (ArctanGeometry.arctanIntegralRectangleRaw x)
      (ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1)
      leibnizRectangleBridgeMeshSchedule)
    leibnizBridgeDyadicZero_valid

/-- The alternating arctangent power series agrees with the geometric
rectangle construction on every nonnegative rational input in `[0,1]`.
The proof uses only finite rational kernel-polynomial estimates and a
scheduled vanishing dyadic enclosure; it assumes no completed-real axiom. -/
theorem arctanEqualsRectangleRaw_finiteRiemannBridge
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctan x).Equiv (ArctanGeometry.arctanIntegralRectangleRaw x) := by
  have hArctanValid : (arctan x).Valid :=
    arctan_valid_at arctanValid (arctanDomain_of_nonnegativeUnit hx0 hx1)
  have hScheduledValid :
      (RealRaw.schedule leibnizRectangleBridgeMeshSchedule
        (ArctanGeometry.arctanIntegralRectangleRaw x)).Valid :=
    RealRaw.schedule_valid (ArctanGeometry.arctanIntegralRectangleRaw x)
      (ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1)
      leibnizRectangleBridgeMeshSchedule
  have htoScheduled : (arctan x).Equiv
      (RealRaw.schedule leibnizRectangleBridgeMeshSchedule
        (ArctanGeometry.arctanIntegralRectangleRaw x)) :=
    RealRaw.equiv_trans hArctanValid
      (arctanRectangleBridgePaddedRaw_valid hx0 hx1) hScheduledValid
      (arctan_equiv_arctanRectangleBridgePaddedRaw hx0 hx1)
      (arctanRectangleBridgePaddedRaw_equiv_scheduledRectangle hx0 hx1)
  have hscheduled :
      (RealRaw.schedule leibnizRectangleBridgeMeshSchedule
        (ArctanGeometry.arctanIntegralRectangleRaw x)).Equiv
        (ArctanGeometry.arctanIntegralRectangleRaw x) :=
    RealRaw.equiv_symm
      (RealRaw.schedule_equiv (ArctanGeometry.arctanIntegralRectangleRaw x)
        (ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1)
        leibnizRectangleBridgeMeshSchedule)
  exact RealRaw.equiv_trans hArctanValid hScheduledValid
    (ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1)
    htoScheduled hscheduled

/-- The alternating arctangent power series agrees directly with the
geometric arctangent on every nonnegative rational input in `[0,1]`.
This packages the finite-Riemann series bridge with the finite rectangle-to-
geometry comparison, without invoking a completed-real limit theorem. -/
theorem arctanEqualsGeom_finiteRiemannBridge
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctan x).Equiv (ArctanGeometry.arctanGeom x) := by
  have hArctanValid : (arctan x).Valid :=
    arctan_valid_at arctanValid (arctanDomain_of_nonnegativeUnit hx0 hx1)
  have hRectValid : (ArctanGeometry.arctanIntegralRectangleRaw x).Valid :=
    ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1
  have hGeomValid : (ArctanGeometry.arctanGeom x).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit hx0 hx1
  exact RealRaw.equiv_trans hArctanValid hRectValid hGeomValid
    (arctanEqualsRectangleRaw_finiteRiemannBridge hx0 hx1)
    (ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom hx0)

/-- The named geometric and power-series arctangent presentations agree on
the nonnegative unit branch.  This is the reusable function-level form of the
finite-Riemann bridge: it compares the representations themselves, rather
than creating another special-purpose π formula. -/
theorem arctanGeomPresentation_equiv_arctanSeriesPresentation_on_nonnegativeUnit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctan.geom.raw.evalRaw x (by trivial)).Equiv
      (arctan.series.raw.evalRaw x
        (by
          change qabs x <= 1
          rw [qabs_eq_self_of_nonneg hx0]
          exact hx1)) := by
  simpa [arctan.geom, arctan.series, ArctanGeometry.representation,
    ArctanGeometry.functionRaw, Elementary.Arctan.powerSeries,
    Elementary.Arctan.powerSeriesFunctionRaw, PartialRealFunRaw.evalRaw] using
    (RealRaw.equiv_symm (arctanEqualsGeom_finiteRiemannBridge hx0 hx1))

/-- The series/kernal-integral comparison obtained from the finite Riemann
bridge.  This is the analytic input used at the two arguments in Machin's
single formula. -/
theorem powerSeriesEqualsRectangleKernelAt_finiteRiemannBridge
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    PowerSeriesEqualsRectangleKernelAt x hx0 hx1 := by
  unfold PowerSeriesEqualsRectangleKernelAt
  have hArctanValid : (arctan x).Valid :=
    arctan_valid_at arctanValid (arctanDomain_of_nonnegativeUnit hx0 hx1)
  have hRectValid : (ArctanGeometry.arctanIntegralRectangleRaw x).Valid :=
    ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1
  have hKernelValid :
      (Taylor.ArctanComparison.kernelIntegralRaw x
        (rectangleKernelIntegralAtNonnegativeUnit x hx0 hx1)).Valid :=
    Taylor.ArctanComparison.kernelIntegralRaw_valid x
      (rectangleKernelIntegralAtNonnegativeUnit x hx0 hx1)
  exact RealRaw.equiv_trans hArctanValid hRectValid hKernelValid
    (arctanEqualsRectangleRaw_finiteRiemannBridge hx0 hx1)
    (rectangleKernelIntegralRaw_equiv_rectangleRaw_nonnegativeUnit x hx0 hx1)

private theorem two_div_two_pow_stage_add_nine_le_budget
    (n : Nat) :
    2 / (((2 ^ (piStage n + 9) : Nat) : Rat)) <=
      6 / (6 * ((piStage n : Nat) : Rat) *
        (((n + 1 : Nat) : Rat))) := by
  let A : Nat := 2 ^ (piStage n + 9)
  let S : Nat := piStage n * (n + 1)
  have hSpos : 0 < S := Nat.mul_pos (piStage_pos n) (Nat.succ_pos n)
  have hApos : 0 < A := Nat.pow_pos (by omega : 0 < 2)
  have h2SA : 2 * S <= A := by
    dsimp [S, A]
    exact two_mul_piStage_mul_succ_le_two_pow_stage_add_nine n
  have hmain : 2 / (A : Rat) <= 1 / (S : Rat) := by
    apply Rat.le_of_mul_le_mul_right (c := (A : Rat) * (S : Rat))
    · calc
        (2 / (A : Rat)) * ((A : Rat) * (S : Rat)) =
            (2 : Rat) * (S : Rat) := by
          have hAne : (A : Rat) ≠ 0 :=
            Rat.ne_of_gt ((Rat.natCast_pos).2 hApos)
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= (A : Rat) := by exact_mod_cast h2SA
        _ = (1 / (S : Rat)) * ((A : Rat) * (S : Rat)) := by
          have hSne : (S : Rat) ≠ 0 :=
            Rat.ne_of_gt ((Rat.natCast_pos).2 hSpos)
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact Rat.mul_pos ((Rat.natCast_pos).2 hApos)
        ((Rat.natCast_pos).2 hSpos)
  calc
    2 / (A : Rat) <= 1 / (S : Rat) := hmain
    _ = 6 / (6 * ((piStage n : Nat) : Rat) *
        (((n + 1 : Nat) : Rat))) := by
      dsimp [S]
      rw [Rat.div_def, Rat.div_def]
      have h6 : (6 : Rat) ≠ 0 := by native_decide
      have hstage_ne : ((piStage n : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (piStage_pos n))
      have hN_ne : (((n + 1 : Nat) : Rat)) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

def InnerAdjacentSegmentBudgetLe (stage : Nat) (B : Rat) : Prop :=
  forall k,
    SegmentBudgetLeAt stage B
      (circleSamplePoint stage k) (circleSamplePoint stage (k + 1))

def OuterAdjacentSegmentBudgetLe (stage : Nat) (B : Rat) : Prop :=
  forall k,
    SegmentBudgetLeAt stage B
      (circleSamplePoint stage k) (outerTangentPoint stage k) /\
    SegmentBudgetLeAt stage B
      (outerTangentPoint stage k) (circleSamplePoint stage (k + 1))

def InnerBoundarySegmentBudgetLe (stage : Nat) (B : Rat) : Prop :=
  ConsecutiveBudgetLe stage B (innerBoundary stage)

def OuterBoundarySegmentBudgetLe (stage : Nat) (B : Rat) : Prop :=
  ConsecutiveBudgetLe stage B (outerBoundary stage)

theorem innerAdjacentSegmentBudgetLe_of_chordFormulaBudget
    {stage : Nat} {B : Rat}
    (h : InnerAdjacentChordFormulaBudgetLe stage B) :
    InnerAdjacentSegmentBudgetLe stage B := by
  intro k
  unfold SegmentBudgetLeAt
  rw [adjacentChordSegmentNormSq_eq_formula]
  simpa [FormulaBudgetLeAt] using h k

theorem outerAdjacentSegmentBudgetLe_of_tangentFormulaBudget
    {stage : Nat} {B : Rat} (hstage : 0 < stage)
    (h : OuterAdjacentTangentFormulaBudgetLe stage B) :
    OuterAdjacentSegmentBudgetLe stage B := by
  intro k
  constructor
  · unfold SegmentBudgetLeAt
    rw [entryTangentSegmentNormSq_eq_formula stage hstage k]
    simpa [FormulaBudgetLeAt] using (h k).1
  · unfold SegmentBudgetLeAt
    rw [exitTangentSegmentNormSq_eq_formula stage hstage k]
    simpa [FormulaBudgetLeAt] using (h k).2

theorem innerBoundaryFrom_consecutiveBudgetLe_of_chordFormulaBudgetUpTo
    (stage : Nat) (B : Rat) (count k : Nat)
    (h : forall j, k <= j -> j + 1 < k + count ->
      FormulaBudgetLeAt stage B (adjacentChordNormSqFormula stage j)) :
    ConsecutiveBudgetLe stage B (innerBoundaryFrom stage k count) := by
  induction count generalizing k with
  | zero =>
      simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
        ConsecutiveBudgetLe]
  | succ count ih =>
      cases count with
      | zero =>
          simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
            ConsecutiveBudgetLe]
      | succ count =>
          simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
            ConsecutiveBudgetLe]
          constructor
          · rw [adjacentChordSegmentNormSq_eq_formula]
            simpa [FormulaBudgetLeAt] using h k (by omega) (by omega)
          · exact ih (k + 1) (by
              intro j hj hupper
              exact h j (by omega) (by omega))

theorem outerBoundaryFrom_consecutiveBudgetLe_of_tangentFormulaBudgetUpTo
    (stage : Nat) (hstage : 0 < stage) (B : Rat) (count k : Nat)
    (h : forall j, k <= j -> j < k + count ->
      FormulaBudgetLeAt stage B (entryTangentNormSqFormula stage j) /\
        FormulaBudgetLeAt stage B (exitTangentNormSqFormula stage j)) :
    ConsecutiveBudgetLe stage B
      (circleSamplePoint stage k :: outerBoundaryFrom stage k count) := by
  induction count generalizing k with
  | zero =>
      simp [outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        ConsecutiveBudgetLe]
  | succ count ih =>
      simp [outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        ConsecutiveBudgetLe]
      constructor
      · rw [entryTangentSegmentNormSq_eq_formula stage hstage k]
        simpa [FormulaBudgetLeAt] using (h k (by omega) (by omega)).1
      · constructor
        · rw [exitTangentSegmentNormSq_eq_formula stage hstage k]
          simpa [FormulaBudgetLeAt] using (h k (by omega) (by omega)).2
        · exact ih (k + 1) (by
            intro j hj hupper
            exact h j (by omega) (by omega))

theorem innerBoundarySegmentBudgetLe_of_chordFormulaBudgetUpTo
    {stage : Nat} {B : Rat}
    (h : InnerAdjacentChordFormulaBudgetLeUpTo stage B) :
    InnerBoundarySegmentBudgetLe stage B := by
  unfold InnerBoundarySegmentBudgetLe innerBoundary
  exact innerBoundaryFrom_consecutiveBudgetLe_of_chordFormulaBudgetUpTo
    stage B (stage + 1) 0 (by
      intro j _ hupper
      exact h j (by omega))

theorem outerBoundarySegmentBudgetLe_of_tangentFormulaBudgetUpTo
    {stage : Nat} {B : Rat} (hstage : 0 < stage)
    (h : OuterAdjacentTangentFormulaBudgetLeUpTo stage B) :
    OuterBoundarySegmentBudgetLe stage B := by
  unfold OuterBoundarySegmentBudgetLe outerBoundary
  exact outerBoundaryFrom_consecutiveBudgetLe_of_tangentFormulaBudgetUpTo
    stage hstage B stage 0 (by
      intro j _ hupper
      exact h j (by omega))

theorem rationalPointPathLength_width_nil (n : Nat) :
    (rationalPointPathLength [] n).width = 0 := by
  simp [rationalPointPathLength, rationalPointPathLength.totalLength,
    QInterval.width]
  grind

theorem rationalPointPathLength_width_single
    (p : PiCirclePoint) (n : Nat) :
    (rationalPointPathLength [p] n).width = 0 := by
  simp [rationalPointPathLength, rationalPointPathLength.totalLength,
    QInterval.width]
  grind

theorem rationalPointPathLength_width_cons_cons
    (p q : PiCirclePoint) (rest : List PiCirclePoint) (n : Nat) :
    (rationalPointPathLength (p :: q :: rest) n).width =
      (pointSegmentLengthInterval p q n).width +
        (rationalPointPathLength (q :: rest) n).width := by
  unfold rationalPointPathLength pointSegmentLengthInterval
    pointSegmentNormSq QInterval.width
  simp [rationalPointPathLength.totalLength]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem rationalPointPathLength_width_eq_segmentWidthSum
    (points : List PiCirclePoint) (n : Nat) :
    (rationalPointPathLength points n).width =
      pathSegmentWidthSum points n := by
  induction points with
  | nil =>
      simp [pathSegmentWidthSum, rationalPointPathLength,
        rationalPointPathLength.totalLength, QInterval.width]
      grind
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp [pathSegmentWidthSum, rationalPointPathLength,
            rationalPointPathLength.totalLength, QInterval.width]
          grind
      | cons q qs =>
          rw [rationalPointPathLength_width_cons_cons]
          simp [pathSegmentWidthSum, ih]

theorem pathSegmentWidthSum_nonneg
    (points : List PiCirclePoint) (n : Nat) :
    0 <= pathSegmentWidthSum points n := by
  induction points with
  | nil => simp [pathSegmentWidthSum]
  | cons p ps ih =>
      cases ps with
      | nil => simp [pathSegmentWidthSum]
      | cons q qs =>
          simp [pathSegmentWidthSum]
          exact Rat.add_nonneg
            (pointSegmentLengthInterval_width_nonneg p q n) ih

theorem pathSegmentWidthSum_eq_budget
    (points : List PiCirclePoint) (n : Nat) :
    pathSegmentWidthSum points n = pathSegmentWidthBudget points n := by
  induction points with
  | nil => simp [pathSegmentWidthSum, pathSegmentWidthBudget]
  | cons p ps ih =>
      cases ps with
      | nil => simp [pathSegmentWidthSum, pathSegmentWidthBudget]
      | cons q qs =>
          simp [pathSegmentWidthSum, pathSegmentWidthBudget,
            pointSegmentLengthInterval_width_eq, ih]

theorem rationalPointPathLength_width_eq_segmentBudget
    (points : List PiCirclePoint) (n : Nat) :
    (rationalPointPathLength points n).width =
      pathSegmentWidthBudget points n := by
  rw [rationalPointPathLength_width_eq_segmentWidthSum,
    pathSegmentWidthSum_eq_budget]

theorem pathSegmentWidthBudget_nonneg
    (points : List PiCirclePoint) (n : Nat) :
    0 <= pathSegmentWidthBudget points n := by
  rw [← pathSegmentWidthSum_eq_budget]
  exact pathSegmentWidthSum_nonneg points n

theorem pathSegmentWidthBudget_le_count_mul
    (precision : Nat) (B : Rat) :
    forall points : List PiCirclePoint,
      ConsecutiveBudgetLe precision B points ->
      pathSegmentWidthBudget points precision <=
        (pathSegmentCount points : Rat) * B
  | [], _h => by
      simp [pathSegmentWidthBudget, pathSegmentCount]
  | [_p], _h => by
      simp [pathSegmentWidthBudget, pathSegmentCount]
  | p :: q :: rest, h => by
      have hhead := h.1
      have htail := h.2
      have ih :=
        pathSegmentWidthBudget_le_count_mul precision B (q :: rest) htail
      simp [pathSegmentWidthBudget, pathSegmentCount]
      calc
        sqrtUpperBound (pointSegmentNormSq p q) /
              ↑(2 ^ sqrtFuel (pointSegmentNormSq p q)
                (sqrtStageEps precision)) +
            pathSegmentWidthBudget (q :: rest) precision
            <= B + (pathSegmentCount (q :: rest) : Rat) * B := by
          grind
        _ = (1 + (pathSegmentCount (q :: rest) : Rat)) * B := by
          grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]

theorem pathSegmentCount_eq_length_pred (points : List PiCirclePoint) :
    pathSegmentCount points = points.length - 1 := by
  induction points with
  | nil => rfl
  | cons p ps ih =>
      cases ps with
      | nil => rfl
      | cons q qs =>
          change 1 + pathSegmentCount (q :: qs) = (q :: qs).length
          rw [ih]
          have hpos : 0 < (q :: qs).length := by simp
          omega

theorem pathSegmentCount_innerBoundary (stage : Nat) :
    pathSegmentCount (innerBoundary stage) = stage := by
  rw [pathSegmentCount_eq_length_pred, innerBoundary_length]
  omega

theorem pathSegmentCount_outerBoundary (stage : Nat) :
    pathSegmentCount (outerBoundary stage) = 2 * stage := by
  rw [pathSegmentCount_eq_length_pred, outerBoundary_length]
  omega

theorem innerBoundaryFrom_consecutiveBudgetLe
    (stage : Nat) (B : Rat)
    (h : InnerAdjacentSegmentBudgetLe stage B)
    (count k : Nat) :
    ConsecutiveBudgetLe stage B (innerBoundaryFrom stage k count) := by
  induction count generalizing k with
  | zero =>
      simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
        ConsecutiveBudgetLe]
  | succ count ih =>
      cases count with
      | zero =>
          simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
            ConsecutiveBudgetLe]
      | succ count =>
          simp [innerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
            ConsecutiveBudgetLe]
          exact ⟨by simpa [SegmentBudgetLeAt] using h k, ih (k + 1)⟩

theorem innerBoundarySegmentBudgetLe_of_adjacent
    {stage : Nat} {B : Rat}
    (h : InnerAdjacentSegmentBudgetLe stage B) :
    InnerBoundarySegmentBudgetLe stage B := by
  unfold InnerBoundarySegmentBudgetLe innerBoundary
  exact innerBoundaryFrom_consecutiveBudgetLe stage B h (stage + 1) 0

theorem outerBoundaryFrom_consecutiveBudgetLe
    (stage : Nat) (B : Rat)
    (h : OuterAdjacentSegmentBudgetLe stage B)
    (count k : Nat) :
    ConsecutiveBudgetLe stage B
      (circleSamplePoint stage k :: outerBoundaryFrom stage k count) := by
  induction count generalizing k with
  | zero =>
      simp [outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        ConsecutiveBudgetLe]
  | succ count ih =>
      simp [outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        ConsecutiveBudgetLe]
      exact ⟨by simpa [SegmentBudgetLeAt] using (h k).1,
        ⟨by simpa [SegmentBudgetLeAt] using (h k).2, ih (k + 1)⟩⟩

theorem outerBoundarySegmentBudgetLe_of_adjacent
    {stage : Nat} {B : Rat}
    (h : OuterAdjacentSegmentBudgetLe stage B) :
    OuterBoundarySegmentBudgetLe stage B := by
  unfold OuterBoundarySegmentBudgetLe outerBoundary
  exact outerBoundaryFrom_consecutiveBudgetLe stage B h stage 0

private theorem div_two_le_div_two {x y : Rat} (hxy : x <= y) :
    x / 2 <= y / 2 := by
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right hxy
    (Rat.le_of_lt ((Rat.inv_pos).2
      (by native_decide : (0 : Rat) < 2)))

namespace Fan

def sumRat : List Rat -> Rat
  | [] => 0
  | x :: xs => x + sumRat xs

def perimeter (widths : List Rat) : Rat :=
  sumRat widths

def triangleArea (height width : Rat) : Rat :=
  height * width / 2

def area (height : Rat) (widths : List Rat) : Rat :=
  sumRat (widths.map (triangleArea height))

def variableArea : List (Prod Rat Rat) -> Rat
  | [] => 0
  | piece :: rest => triangleArea piece.1 piece.2 + variableArea rest

def widths : List (Prod Rat Rat) -> List Rat
  | [] => []
  | piece :: rest => piece.2 :: widths rest

def unitPieces (widths : List Rat) : List (Prod Rat Rat) :=
  widths.map (fun width => (1, width))

theorem widths_unitPieces (widths : List Rat) :
    Fan.widths (unitPieces widths) = widths := by
  induction widths with
  | nil => rfl
  | cons width rest ih =>
      change width :: Fan.widths (unitPieces rest) =
        width :: rest
      rw [ih]

theorem area_eq_height_mul_half_perimeter
    (height : Rat) (widths : List Rat) :
    area height widths = height * perimeter widths / 2 := by
  induction widths with
  | nil =>
      simp [area, perimeter, sumRat]
      grind [Rat.div_def]
  | cons width widths ih =>
      simp [area, perimeter, sumRat, triangleArea] at *
      rw [ih]
      grind [Rat.div_def, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]

theorem area_le_half_perimeter
    {height : Rat} {widths : List Rat}
    (hheight : height <= 1)
    (hperim : 0 <= perimeter widths) :
    area height widths <= perimeter widths / 2 := by
  rw [area_eq_height_mul_half_perimeter]
  have hmul : height * perimeter widths <= 1 * perimeter widths :=
    Rat.mul_le_mul_of_nonneg_right hheight hperim
  have hdiv := div_two_le_div_two hmul
  simpa [Rat.one_mul] using hdiv

theorem area_one_eq_half_perimeter (widths : List Rat) :
    area 1 widths = perimeter widths / 2 := by
  rw [area_eq_height_mul_half_perimeter]
  grind

theorem variableArea_unitPieces_eq_area (widths : List Rat) :
    variableArea (unitPieces widths) = area 1 widths := by
  induction widths with
  | nil => rfl
  | cons width rest ih =>
      change triangleArea 1 width + variableArea (unitPieces rest) =
        triangleArea 1 width + area 1 rest
      rw [ih]

theorem sumRat_nonneg :
    forall widths : List Rat,
      (forall width : Rat, List.Mem width widths -> 0 <= width) ->
      0 <= sumRat widths
  | [], _hwidth => by
      simp [sumRat]
  | width :: rest, hwidth => by
      have h_head : 0 <= width :=
        hwidth width (List.Mem.head rest)
      have h_tail :
          forall tailWidth : Rat, List.Mem tailWidth rest ->
            0 <= tailWidth := by
        intro tailWidth hmem
        exact hwidth tailWidth (List.Mem.tail width hmem)
      have h_rest : 0 <= sumRat rest :=
        sumRat_nonneg rest h_tail
      simp [sumRat]
      exact Rat.add_nonneg h_head h_rest

private theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d := by
  grind

theorem variableArea_le_half_perimeter :
    forall pieces : List (Prod Rat Rat),
      (forall piece : Prod Rat Rat, List.Mem piece pieces -> piece.1 <= 1) ->
      (forall piece : Prod Rat Rat, List.Mem piece pieces -> 0 <= piece.2) ->
      variableArea pieces <= perimeter (widths pieces) / 2
  | [], _hheight, _hwidth => by
      simp [variableArea, widths, perimeter, sumRat, Rat.div_def]
  | piece :: rest, hheight, hwidth => by
      have h_height : piece.1 <= 1 :=
        hheight piece (List.Mem.head rest)
      have h_width : 0 <= piece.2 :=
        hwidth piece (List.Mem.head rest)
      have hrest_height :
          forall p : Prod Rat Rat, List.Mem p rest -> p.1 <= 1 := by
        intro p hp
        exact hheight p (List.Mem.tail piece hp)
      have hrest_width :
          forall p : Prod Rat Rat, List.Mem p rest -> 0 <= p.2 := by
        intro p hp
        exact hwidth p (List.Mem.tail piece hp)
      have ih :=
        variableArea_le_half_perimeter rest hrest_height hrest_width
      have htriangle : triangleArea piece.1 piece.2 <= piece.2 / 2 := by
        unfold triangleArea
        have hmul : piece.1 * piece.2 <= 1 * piece.2 :=
          Rat.mul_le_mul_of_nonneg_right h_height h_width
        have hmul' : piece.1 * piece.2 <= piece.2 := by
          simpa [Rat.one_mul] using hmul
        rw [Rat.div_def, Rat.div_def]
        exact Rat.mul_le_mul_of_nonneg_right hmul'
          (Rat.le_of_lt ((Rat.inv_pos).2
            (by native_decide : (0 : Rat) < 2)))
      simp [variableArea, widths, perimeter, sumRat]
      calc
        triangleArea piece.1 piece.2 + variableArea rest <=
            piece.2 / 2 + perimeter (widths rest) / 2 :=
          rat_add_le_add htriangle ih
        _ = (piece.2 + perimeter (widths rest)) / 2 := by
          grind [Rat.div_def, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]
        _ = (piece.2 + sumRat (widths rest)) / 2 := rfl

def edgeCrossesFrom (prev : PiCirclePoint) : List PiCirclePoint -> List Rat
  | [] => []
  | vertex :: rest =>
      pointCross prev vertex :: edgeCrossesFrom vertex rest

def sectorFanWidths (boundary : List PiCirclePoint) : List Rat :=
  edgeCrossesFrom originPoint boundary

theorem twiceSignedAreaAux_origin_eq_sum_edgeCrossesFrom
    (prev : PiCirclePoint) (vertices : List PiCirclePoint) :
    twiceSignedAreaAux originPoint prev vertices =
      sumRat (edgeCrossesFrom prev vertices) := by
  induction vertices generalizing prev with
  | nil =>
      change pointCross prev originPoint = 0
      exact pointCross_origin_right prev
  | cons vertex rest ih =>
      simp [twiceSignedAreaAux, edgeCrossesFrom, sumRat,
        piCircleAreaPolygon.twiceSignedAreaAux]
      change pointCross prev vertex + twiceSignedAreaAux originPoint vertex rest =
        pointCross prev vertex + sumRat (edgeCrossesFrom vertex rest)
      rw [ih vertex]

theorem twiceSignedArea_origin_cons
    (boundary : List PiCirclePoint) :
    twiceSignedArea (originPoint :: boundary) =
      sumRat (sectorFanWidths boundary) := by
  unfold twiceSignedArea sectorFanWidths
  exact twiceSignedAreaAux_origin_eq_sum_edgeCrossesFrom originPoint boundary

theorem sectorArea_eq_half_perimeter
    {boundary : List PiCirclePoint}
    (hnonneg : 0 <= sumRat (sectorFanWidths boundary)) :
    polygonArea (originPoint :: boundary) =
      perimeter (sectorFanWidths boundary) / 2 := by
  unfold polygonArea perimeter
  rw [twiceSignedArea_origin_cons]
  rw [show qabs (sumRat (sectorFanWidths boundary) / 2) =
      sumRat (sectorFanWidths boundary) / 2 by
    unfold qabs
    by_cases hlt : sumRat (sectorFanWidths boundary) / 2 < 0
    · have hnonnegHalf :
          0 <= sumRat (sectorFanWidths boundary) / 2 := by
        rw [Rat.div_def]
        exact Rat.mul_nonneg hnonneg
          (Rat.le_of_lt ((Rat.inv_pos).2
            (by native_decide : (0 : Rat) < 2)))
      have hfalse : False := by grind
      exact False.elim hfalse
    · simp [hlt]]

end Fan

namespace Fan

theorem edgeCrossesFrom_sum_nonneg :
    forall (prev : PiCirclePoint) (vertices : List PiCirclePoint),
      ConsecutiveCrossNonneg (prev :: vertices) ->
      0 <= sumRat (edgeCrossesFrom prev vertices)
  | _prev, [], _h => by
      simp [edgeCrossesFrom, sumRat]
  | prev, vertex :: rest, h => by
      have hhead : 0 <= pointCross prev vertex := h.1
      have htail : ConsecutiveCrossNonneg (vertex :: rest) := h.2
      have ih := edgeCrossesFrom_sum_nonneg vertex rest htail
      simp [edgeCrossesFrom, sumRat]
      exact Rat.add_nonneg hhead ih

theorem edgeCrossesFrom_mem_nonneg :
    forall (prev : PiCirclePoint) (vertices : List PiCirclePoint),
      ConsecutiveCrossNonneg (prev :: vertices) ->
      forall width : Rat,
        List.Mem width (edgeCrossesFrom prev vertices) -> 0 <= width
  | _prev, [], _h, width, hmem => by
      cases hmem
  | prev, vertex :: rest, h, width, hmem => by
      have hcases := hmem
      change List.Mem width
        (pointCross prev vertex :: edgeCrossesFrom vertex rest) at hcases
      cases hcases with
      | head =>
          exact h.1
      | tail _ htail =>
          exact edgeCrossesFrom_mem_nonneg vertex rest h.2 width htail

theorem sectorFanWidths_sum_nonneg :
    forall vertices : List PiCirclePoint,
      ConsecutiveCrossNonneg vertices ->
      0 <= sumRat (sectorFanWidths vertices)
  | [], _h => by
      simp [sectorFanWidths, edgeCrossesFrom, sumRat]
  | first :: rest, h => by
      have htail := edgeCrossesFrom_sum_nonneg first rest h
      have horigin : pointCross originPoint first = 0 :=
        pointCross_origin_left first
      unfold sectorFanWidths
      simp [edgeCrossesFrom, sumRat, horigin]
      exact Rat.add_nonneg (by native_decide : (0 : Rat) <= 0) htail

theorem sectorFanWidths_mem_nonneg :
    forall vertices : List PiCirclePoint,
      ConsecutiveCrossNonneg vertices ->
      forall width : Rat,
        List.Mem width (sectorFanWidths vertices) -> 0 <= width
  | [], _h, width, hmem => by
      cases hmem
  | first :: rest, h, width, hmem => by
      have hcases := hmem
      unfold sectorFanWidths at hcases
      change List.Mem width
        (pointCross originPoint first :: edgeCrossesFrom first rest) at hcases
      cases hcases with
      | head =>
          rw [pointCross_origin_left first]
          native_decide
      | tail _ htail =>
          exact edgeCrossesFrom_mem_nonneg first rest h width htail

theorem edgeCrossesFrom_le_pathLength_hi
    (precision : Nat) :
    forall (prev : PiCirclePoint) (vertices : List PiCirclePoint),
      ConsecutiveCrossLe precision (prev :: vertices) ->
      perimeter (edgeCrossesFrom prev vertices) <=
        (rationalPointPathLength (prev :: vertices) precision).hi
  | _prev, [], _h => by
      simp [edgeCrossesFrom, perimeter, sumRat,
        rationalPointPathLength, rationalPointPathLength.totalLength]
  | prev, vertex :: rest, h => by
      have hhead :
          pointCross prev vertex <=
            (pointSegmentLengthInterval prev vertex precision).hi := h.1
      have htail :
          ConsecutiveCrossLe precision (vertex :: rest) := h.2
      have ih :=
        edgeCrossesFrom_le_pathLength_hi precision vertex rest htail
      have hhead' :
          pointCross prev vertex <=
            (sqrtPartialRaw.compute
              ((vertex.x - prev.x) * (vertex.x - prev.x) +
                (vertex.y - prev.y) * (vertex.y - prev.y))
              (pointSegmentNormSq_sqrtDomain prev vertex) precision).hi := by
        simpa [pointSegmentLengthInterval, pointSegmentNormSq] using hhead
      simp [edgeCrossesFrom, perimeter, sumRat,
        rationalPointPathLength, rationalPointPathLength.totalLength]
      exact rat_add_le_add hhead' ih

theorem sectorFanPerimeter_le_pathLength_hi
    (precision : Nat) :
    forall vertices : List PiCirclePoint,
      ConsecutiveCrossLe precision vertices ->
      perimeter (sectorFanWidths vertices) <=
        (rationalPointPathLength vertices precision).hi
  | [], _h => by
      simp [sectorFanWidths, edgeCrossesFrom, perimeter, sumRat,
        rationalPointPathLength, rationalPointPathLength.totalLength]
  | first :: rest, h => by
      have htail :=
        edgeCrossesFrom_le_pathLength_hi precision first rest h
      have horigin : pointCross originPoint first = 0 :=
        pointCross_origin_left first
      unfold sectorFanWidths perimeter
      simp [edgeCrossesFrom, sumRat, horigin]
      calc
        0 + sumRat (edgeCrossesFrom first rest) =
            sumRat (edgeCrossesFrom first rest) := by grind
        _ <= (rationalPointPathLength (first :: rest) precision).hi :=
            htail

theorem pathLength_lo_le_edgeCrosses
    (precision : Nat) :
    forall (prev : PiCirclePoint) (vertices : List PiCirclePoint),
      ConsecutiveLengthLoLeCross precision (prev :: vertices) ->
      (rationalPointPathLength (prev :: vertices) precision).lo <=
        perimeter (edgeCrossesFrom prev vertices)
  | _prev, [], _h => by
      simp [edgeCrossesFrom, perimeter, sumRat,
        rationalPointPathLength, rationalPointPathLength.totalLength]
  | prev, vertex :: rest, h => by
      have hhead :
          (pointSegmentLengthInterval prev vertex precision).lo <=
            pointCross prev vertex := h.1
      have htail :
          ConsecutiveLengthLoLeCross precision (vertex :: rest) := h.2
      have ih :=
        pathLength_lo_le_edgeCrosses precision vertex rest htail
      have ih' :
          (rationalPointPathLength (vertex :: rest) precision).lo <=
            sumRat (edgeCrossesFrom vertex rest) := by
        simpa [perimeter] using ih
      have hhead' :
          (sqrtPartialRaw.compute
            ((vertex.x - prev.x) * (vertex.x - prev.x) +
              (vertex.y - prev.y) * (vertex.y - prev.y))
            (pointSegmentNormSq_sqrtDomain prev vertex) precision).lo <=
            pointCross prev vertex := by
        simpa [pointSegmentLengthInterval, pointSegmentNormSq] using hhead
      simp [edgeCrossesFrom, perimeter, sumRat,
        rationalPointPathLength, rationalPointPathLength.totalLength]
      exact rat_add_le_add hhead' ih'

theorem pathLength_lo_le_sectorFanPerimeter
    (precision : Nat) :
    forall vertices : List PiCirclePoint,
      ConsecutiveLengthLoLeCross precision vertices ->
      (rationalPointPathLength vertices precision).lo <=
        perimeter (sectorFanWidths vertices)
  | [], _h => by
      simp [sectorFanWidths, edgeCrossesFrom, perimeter, sumRat,
        rationalPointPathLength, rationalPointPathLength.totalLength]
  | first :: rest, h => by
      have htail :=
        pathLength_lo_le_edgeCrosses precision first rest h
      have horigin : pointCross originPoint first = 0 :=
        pointCross_origin_left first
      unfold sectorFanWidths perimeter
      simp [edgeCrossesFrom, sumRat, horigin]
      calc
        (rationalPointPathLength (first :: rest) precision).lo <=
            sumRat (edgeCrossesFrom first rest) := htail
        _ = 0 + sumRat (edgeCrossesFrom first rest) := by grind

end Fan

private theorem four_mul_le_four_mul {a b : Rat} (h : a <= b) :
    4 * a <= 4 * b :=
  Rat.mul_le_mul_of_nonneg_left h (by native_decide : (0 : Rat) <= 4)

/-- The exact finite Archimedes inequalities for one rational polygon stage.

The first field says the inscribed quarter-sector area is below half of the
computed outer tangent path length.  The second says the computed lower chord
path length is below twice the circumscribed quarter-sector area.  After
scaling by four and halving circumference, these are precisely the two
interval-overlap inequalities for `piCircleArea` and `piCircumference`. -/
structure FiniteArchimedesStage (stage : Nat) where
  innerArea_le_half_outerLength :
    innerQuarterArea stage <= (outerQuarterLength stage).hi / 2
  innerLength_le_twice_outerArea :
    (innerQuarterLength stage).lo <= 2 * outerQuarterArea stage

structure FiniteArchimedesBounds where
  atStage : forall stage : Nat, 0 < stage -> FiniteArchimedesStage stage

def innerFanWidths (stage : Nat) : List Rat :=
  Fan.sectorFanWidths (innerBoundary stage)

def outerFanWidths (stage : Nat) : List Rat :=
  Fan.sectorFanWidths (outerBoundary stage)

private theorem outerTangentCrossSumFrom_eq_edgeCrossPerimeter
    (stage count k : Nat) :
    outerTangentCrossSumFrom stage k count =
      Fan.perimeter
        (Fan.edgeCrossesFrom (circleSamplePoint stage k)
          (outerBoundaryFrom stage k count)) := by
  induction count generalizing k with
  | zero =>
      simp [outerTangentCrossSumFrom, outerBoundaryFrom,
        piCircleAreaPolygon.outerBoundaryFrom, Fan.perimeter,
        Fan.edgeCrossesFrom, Fan.sumRat]
  | succ count ih =>
      simp [outerTangentCrossSumFrom, outerTangentCrossSum,
        outerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        Fan.perimeter, Fan.edgeCrossesFrom, Fan.sumRat, ih, Rat.add_assoc]

/-- The rational tangent-cell sum is exactly the outer fan perimeter used by
the finite Archimedes comparison. -/
theorem outerFanPerimeter_eq_outerTangentCrossSumFrom (stage : Nat) :
    Fan.perimeter (outerFanWidths stage) =
      outerTangentCrossSumFrom stage 0 stage := by
  have h := outerTangentCrossSumFrom_eq_edgeCrossPerimeter stage stage 0
  symm
  simpa [outerFanWidths, outerBoundary, Fan.sectorFanWidths,
    Fan.perimeter, Fan.edgeCrossesFrom, Fan.sumRat, pointCross_origin_left,
    Rat.zero_add]
    using h

/-- The exact outer tangent fan is antitone under the dyadic refinement of
the rational-circle parameter mesh. -/
theorem outerFanPerimeter_refinesByDoubling
    (stage : Nat) (hstage : 0 < stage) :
    Fan.perimeter (outerFanWidths (2 * stage)) <=
      Fan.perimeter (outerFanWidths stage) := by
  rw [outerFanPerimeter_eq_outerTangentCrossSumFrom,
    outerFanPerimeter_eq_outerTangentCrossSumFrom]
  simpa using
    (outerTangentCrossSumFrom_refinesByDoubling stage hstage stage 0)

def innerFanPieces (stage : Nat) : List (Prod Rat Rat) :=
  Fan.unitPieces (innerFanWidths stage)

theorem innerFanPieces_heights_le_one (stage : Nat) :
    forall piece : Prod Rat Rat, List.Mem piece (innerFanPieces stage) ->
      piece.1 <= 1 := by
  intro piece hmem
  unfold innerFanPieces Fan.unitPieces at hmem
  cases List.mem_map.mp hmem with
  | intro width hw =>
      cases hw with
      | intro _hwidth hpiece =>
          rw [Eq.symm hpiece]
          change (1 : Rat) <= 1
          native_decide

theorem innerFanPieces_widths_nonneg
    (stage : Nat)
    (hwidth :
      forall width : Rat, List.Mem width (innerFanWidths stage) -> 0 <= width) :
    forall piece : Prod Rat Rat, List.Mem piece (innerFanPieces stage) ->
      0 <= piece.2 := by
  intro piece hmem
  unfold innerFanPieces Fan.unitPieces at hmem
  cases List.mem_map.mp hmem with
  | intro width hw =>
      cases hw with
      | intro hwidth_mem hpiece =>
          rw [Eq.symm hpiece]
          exact hwidth width hwidth_mem

theorem innerQuarterArea_eq_variable_unit_fan
    (stage : Nat)
    (hnonneg : 0 <= Fan.sumRat (innerFanWidths stage)) :
    innerQuarterArea stage = Fan.variableArea (innerFanPieces stage) := by
  unfold innerQuarterArea innerFanPieces innerFanWidths
  rw [Fan.sectorArea_eq_half_perimeter hnonneg]
  rw [Fan.variableArea_unitPieces_eq_area]
  rw [Fan.area_one_eq_half_perimeter]

theorem outerQuarterArea_eq_area_one
    (stage : Nat)
    (hnonneg : 0 <= Fan.sumRat (outerFanWidths stage)) :
    outerQuarterArea stage = Fan.area 1 (outerFanWidths stage) := by
  unfold outerQuarterArea outerFanWidths
  rw [Fan.sectorArea_eq_half_perimeter hnonneg]
  rw [Fan.area_one_eq_half_perimeter]

/-- A finite fan certificate for one stage.

This isolates the remaining geometric work.  To construct one of these for the
actual rational circle samples, we need rational inequalities saying:

* the inner sector area is the rearranged inner fan area;
* the inner fan base perimeter sits below the outer tangent fan perimeter;
* the computed lower chord length sits below that same outer fan perimeter;
* the outer sector area is exactly half the outer tangent fan perimeter;
* the outer fan perimeter sits below the computed upper tangent path length.
-/
structure VariableFanStage (stage : Nat) where
  innerPieces : List (Prod Rat Rat)
  outerWidths : List Rat
  innerHeights_le_one :
    forall piece : Prod Rat Rat, List.Mem piece innerPieces ->
      piece.1 <= 1
  innerWidths_nonneg :
    forall piece : Prod Rat Rat, List.Mem piece innerPieces ->
      0 <= piece.2
  innerArea_eq :
    innerQuarterArea stage = Fan.variableArea innerPieces
  innerBasePerimeter_le_outerPerimeter :
    Fan.perimeter (Fan.widths innerPieces) <= Fan.perimeter outerWidths
  innerComputedLo_le_outerPerimeter :
    (innerQuarterLength stage).lo <= Fan.perimeter outerWidths
  outerArea_eq :
    outerQuarterArea stage = Fan.area 1 outerWidths
  outerPerimeter_le_outerComputedHi :
    Fan.perimeter outerWidths <= (outerQuarterLength stage).hi

theorem finiteArchimedesStage_of_variableFanStage
    {stage : Nat} (S : VariableFanStage stage) :
    FiniteArchimedesStage stage where
  innerArea_le_half_outerLength := by
    have hinner :
        innerQuarterArea stage <=
          Fan.perimeter (Fan.widths S.innerPieces) / 2 := by
      rw [S.innerArea_eq]
      exact Fan.variableArea_le_half_perimeter
        S.innerPieces S.innerHeights_le_one S.innerWidths_nonneg
    have hperim :
        Fan.perimeter (Fan.widths S.innerPieces) / 2 <=
          Fan.perimeter S.outerWidths / 2 :=
      div_two_le_div_two S.innerBasePerimeter_le_outerPerimeter
    have houter :
        Fan.perimeter S.outerWidths / 2 <=
          (outerQuarterLength stage).hi / 2 :=
      div_two_le_div_two S.outerPerimeter_le_outerComputedHi
    exact Rat.le_trans hinner (Rat.le_trans hperim houter)
  innerLength_le_twice_outerArea := by
    rw [S.outerArea_eq, Fan.area_one_eq_half_perimeter]
    calc
      (innerQuarterLength stage).lo <= Fan.perimeter S.outerWidths :=
        S.innerComputedLo_le_outerPerimeter
      _ = 2 * (Fan.perimeter S.outerWidths / 2) := by
        rw [Rat.div_def]
        have hne : (2 : Rat) != 0 := by native_decide
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem finiteArchimedesBounds_of_variableFanStages
    (stageData : forall stage : Nat, 0 < stage -> VariableFanStage stage) :
    FiniteArchimedesBounds where
  atStage := fun stage hstage =>
    finiteArchimedesStage_of_variableFanStage (stageData stage hstage)

/-- Concrete rational fan inequalities for one stage.

These are now the real finite goals.  They talk only about rational cross
products, rational polygon areas, and rational intervals returned by the sqrt
path-length computation. -/
structure SectorFanBounds (stage : Nat) where
  innerWidths_nonneg :
    forall width : Rat, List.Mem width (innerFanWidths stage) -> 0 <= width
  outerWidths_sum_nonneg :
    0 <= Fan.sumRat (outerFanWidths stage)
  innerPerimeter_le_outerPerimeter :
    Fan.perimeter (innerFanWidths stage) <=
      Fan.perimeter (outerFanWidths stage)
  innerComputedLo_le_outerPerimeter :
    (innerQuarterLength stage).lo <=
      Fan.perimeter (outerFanWidths stage)
  outerPerimeter_le_outerComputedHi :
    Fan.perimeter (outerFanWidths stage) <=
      (outerQuarterLength stage).hi

def variableFanStageOfSectorBounds
    (stage : Nat) (bounds : SectorFanBounds stage) :
    VariableFanStage stage where
  innerPieces := innerFanPieces stage
  outerWidths := outerFanWidths stage
  innerHeights_le_one := innerFanPieces_heights_le_one stage
  innerWidths_nonneg :=
    innerFanPieces_widths_nonneg stage bounds.innerWidths_nonneg
  innerArea_eq :=
    innerQuarterArea_eq_variable_unit_fan stage
      (Fan.sumRat_nonneg
        (innerFanWidths stage) bounds.innerWidths_nonneg)
  innerBasePerimeter_le_outerPerimeter := by
    unfold innerFanPieces
    rw [Fan.widths_unitPieces]
    exact bounds.innerPerimeter_le_outerPerimeter
  innerComputedLo_le_outerPerimeter :=
    bounds.innerComputedLo_le_outerPerimeter
  outerArea_eq :=
    outerQuarterArea_eq_area_one stage bounds.outerWidths_sum_nonneg
  outerPerimeter_le_outerComputedHi :=
    bounds.outerPerimeter_le_outerComputedHi

theorem finiteArchimedesBounds_of_sectorFanBounds
    (bounds : forall stage : Nat, 0 < stage -> SectorFanBounds stage) :
    FiniteArchimedesBounds :=
  finiteArchimedesBounds_of_variableFanStages
    (fun stage hstage =>
      variableFanStageOfSectorBounds stage (bounds stage hstage))

/-- The remaining concrete cross-product bounds for one stage.

The first three fields are local path facts.  The last two are the classical
inner-vs-outer fan comparisons: chord-sector fan perimeter below tangent fan
perimeter, and the computed lower chord path below that same tangent fan
perimeter. -/
structure CrossFanBounds (stage : Nat) where
  innerCrossNonneg :
    ConsecutiveCrossNonneg (innerBoundary stage)
  outerCrossNonneg :
    ConsecutiveCrossNonneg (outerBoundary stage)
  outerCrossLeLength :
    ConsecutiveCrossLe stage (outerBoundary stage)
  innerPerimeter_le_outerPerimeter :
    Fan.perimeter (innerFanWidths stage) <=
      Fan.perimeter (outerFanWidths stage)
  innerComputedLo_le_outerPerimeter :
    (innerQuarterLength stage).lo <=
      Fan.perimeter (outerFanWidths stage)

def sectorFanBoundsOfCrossFanBounds
    (stage : Nat) (bounds : CrossFanBounds stage) :
    SectorFanBounds stage where
  innerWidths_nonneg :=
    Fan.sectorFanWidths_mem_nonneg
      (innerBoundary stage) bounds.innerCrossNonneg
  outerWidths_sum_nonneg :=
    Fan.sectorFanWidths_sum_nonneg
      (outerBoundary stage) bounds.outerCrossNonneg
  innerPerimeter_le_outerPerimeter :=
    bounds.innerPerimeter_le_outerPerimeter
  innerComputedLo_le_outerPerimeter :=
    bounds.innerComputedLo_le_outerPerimeter
  outerPerimeter_le_outerComputedHi :=
    Fan.sectorFanPerimeter_le_pathLength_hi
      stage (outerBoundary stage) bounds.outerCrossLeLength

theorem finiteArchimedesBounds_of_crossFanBounds
    (bounds : forall stage : Nat, 0 < stage -> CrossFanBounds stage) :
    FiniteArchimedesBounds :=
  finiteArchimedesBounds_of_sectorFanBounds
    (fun stage hstage =>
      sectorFanBoundsOfCrossFanBounds stage (bounds stage hstage))

/-- Local adjacent tangent bounds for one stage.

These are closer to the algebra one proves from the explicit rational
formulas for `circlePoint` and `tangentIntersection`. -/
structure LocalTangentBounds (stage : Nat) where
  innerCrossNonneg :
    ConsecutiveCrossNonneg (innerBoundary stage)
  outerCrossNonneg :
    ConsecutiveCrossNonneg (outerBoundary stage)
  outerCrossLeLength :
    ConsecutiveCrossLe stage (outerBoundary stage)
  chordCross_le_tangentCrossSum :
    forall k,
      pointCross (circleSamplePoint stage k)
          (circleSamplePoint stage (k + 1)) <=
        outerTangentCrossSum stage k
  chordLengthLo_le_tangentCrossSum :
    forall k,
      (pointSegmentLengthInterval
        (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) stage).lo <=
        outerTangentCrossSum stage k

theorem localTangentBounds
    (stage : Nat) (hstage : 0 < stage) :
    LocalTangentBounds stage where
  innerCrossNonneg :=
    innerBoundary_consecutiveCrossNonneg stage hstage
  outerCrossNonneg :=
    outerBoundary_consecutiveCrossNonneg stage hstage
  outerCrossLeLength :=
    outerBoundary_consecutiveCrossLe stage hstage stage
  chordCross_le_tangentCrossSum :=
    chordCross_le_outerTangentCrossSum stage hstage
  chordLengthLo_le_tangentCrossSum :=
    chordLengthLo_le_outerTangentCrossSum stage hstage

theorem innerEdgeCrosses_le_outerTangentEdgeCrosses
    (stage : Nat)
    (hlocal :
      forall k,
        pointCross (circleSamplePoint stage k)
            (circleSamplePoint stage (k + 1)) <=
          outerTangentCrossSum stage k) :
    forall count k,
      Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage k)
          (innerBoundaryFrom stage (k + 1) count)) <=
      Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage k)
          (outerBoundaryFrom stage k count))
  | 0, k => by
      simp [innerBoundaryFrom, outerBoundaryFrom,
        piCircleAreaPolygon.innerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
  | count + 1, k => by
      have hhead := hlocal k
      have htail :=
        innerEdgeCrosses_le_outerTangentEdgeCrosses
          stage hlocal count (k + 1)
      simp [innerBoundaryFrom, outerBoundaryFrom,
        piCircleAreaPolygon.innerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
      calc
        pointCross (circleSamplePoint stage k)
              (circleSamplePoint stage (k + 1)) +
            Fan.sumRat
              (Fan.edgeCrossesFrom
                (circleSamplePoint stage (k + 1))
                (innerBoundaryFrom stage (k + 2) count))
            <=
          outerTangentCrossSum stage k +
            Fan.sumRat
              (Fan.edgeCrossesFrom
                (circleSamplePoint stage (k + 1))
                (outerBoundaryFrom stage (k + 1) count)) := by
            exact Fan.rat_add_le_add hhead htail
        _ =
          pointCross (circleSamplePoint stage k)
              (outerTangentPoint stage k) +
            (pointCross (outerTangentPoint stage k)
              (circleSamplePoint stage (k + 1)) +
              Fan.sumRat
                (Fan.edgeCrossesFrom
                  (circleSamplePoint stage (k + 1))
                  (outerBoundaryFrom stage (k + 1) count))) := by
          grind [outerTangentCrossSum, Rat.add_assoc, Rat.add_comm]

theorem innerPathLo_le_outerTangentEdgeCrosses
    (stage precision : Nat)
    (hlocal :
      forall k,
        (pointSegmentLengthInterval
          (circleSamplePoint stage k)
          (circleSamplePoint stage (k + 1)) precision).lo <=
          outerTangentCrossSum stage k) :
    forall count k,
      (rationalPointPathLength
        (circleSamplePoint stage k ::
          innerBoundaryFrom stage (k + 1) count) precision).lo <=
      Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage k)
          (outerBoundaryFrom stage k count))
  | 0, k => by
      simp [innerBoundaryFrom, outerBoundaryFrom,
        piCircleAreaPolygon.innerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        rationalPointPathLength, rationalPointPathLength.totalLength,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
  | count + 1, k => by
      have hhead := hlocal k
      have htail :=
        innerPathLo_le_outerTangentEdgeCrosses
          stage precision hlocal count (k + 1)
      have hhead' :
          (sqrtPartialRaw.compute
            (pointSegmentNormSq
              (circleSamplePoint stage k)
              (circleSamplePoint stage (k + 1)))
            (pointSegmentNormSq_sqrtDomain
              (circleSamplePoint stage k)
              (circleSamplePoint stage (k + 1))) precision).lo <=
          outerTangentCrossSum stage k := by
        simpa [pointSegmentLengthInterval] using hhead
      simp [innerBoundaryFrom, outerBoundaryFrom,
        piCircleAreaPolygon.innerBoundaryFrom, piCircleAreaPolygon.outerBoundaryFrom,
        rationalPointPathLength, rationalPointPathLength.totalLength,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
      calc
        (sqrtPartialRaw.compute
              (pointSegmentNormSq
                (circleSamplePoint stage k)
                (circleSamplePoint stage (k + 1)))
              (pointSegmentNormSq_sqrtDomain
                (circleSamplePoint stage k)
                (circleSamplePoint stage (k + 1))) precision).lo +
            (rationalPointPathLength
              (circleSamplePoint stage (k + 1) ::
                innerBoundaryFrom stage (k + 2) count) precision).lo
            <=
          outerTangentCrossSum stage k +
            Fan.sumRat
              (Fan.edgeCrossesFrom
                (circleSamplePoint stage (k + 1))
                (outerBoundaryFrom stage (k + 1) count)) := by
            exact Fan.rat_add_le_add hhead' htail
        _ =
          pointCross (circleSamplePoint stage k)
              (outerTangentPoint stage k) +
            (pointCross (outerTangentPoint stage k)
              (circleSamplePoint stage (k + 1)) +
              Fan.sumRat
                (Fan.edgeCrossesFrom
                  (circleSamplePoint stage (k + 1))
                  (outerBoundaryFrom stage (k + 1) count))) := by
          grind [outerTangentCrossSum, Rat.add_assoc, Rat.add_comm]

theorem innerFanPerimeter_le_outerFanPerimeter_of_adjacent
    (stage : Nat)
    (hlocal :
      forall k,
        pointCross (circleSamplePoint stage k)
            (circleSamplePoint stage (k + 1)) <=
          outerTangentCrossSum stage k) :
    Fan.perimeter (innerFanWidths stage) <=
      Fan.perimeter (outerFanWidths stage) := by
  have h :=
    innerEdgeCrosses_le_outerTangentEdgeCrosses
      stage hlocal stage 0
  have h' :
      0 + Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage 0)
          (innerBoundaryFrom stage (0 + 1) stage)) <=
      0 + Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage 0)
          (outerBoundaryFrom stage 0 stage)) := by
    exact (Rat.add_le_add_left).2 h
  simpa [innerFanWidths, outerFanWidths, innerBoundary, outerBoundary,
    Fan.sectorFanWidths, Fan.perimeter, innerBoundaryFrom,
    outerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
    piCircleAreaPolygon.outerBoundaryFrom, Fan.edgeCrossesFrom, Fan.sumRat,
    pointCross_origin_left] using h'

theorem innerFanPerimeter_le_outerFanPerimeter
    (stage : Nat) (hstage : 0 < stage) :
    Fan.perimeter (innerFanWidths stage) <=
      Fan.perimeter (outerFanWidths stage) :=
  innerFanPerimeter_le_outerFanPerimeter_of_adjacent
    stage (chordCross_le_outerTangentCrossSum stage hstage)

theorem innerFanPerimeter_le_innerQuarterLength_hi
    (stage : Nat) :
    Fan.perimeter (innerFanWidths stage) <=
      (innerQuarterLength stage).hi := by
  simpa [innerQuarterLength, innerFanWidths] using
    Fan.sectorFanPerimeter_le_pathLength_hi
      stage (innerBoundary stage)
      (innerBoundary_consecutiveCrossLe stage stage)

theorem innerQuarterLength_lo_le_outerFanPerimeter_of_adjacent
    (stage : Nat)
    (hlocal :
      forall k,
        (pointSegmentLengthInterval
          (circleSamplePoint stage k)
          (circleSamplePoint stage (k + 1)) stage).lo <=
          outerTangentCrossSum stage k) :
    (innerQuarterLength stage).lo <=
      Fan.perimeter (outerFanWidths stage) := by
  have h :=
    innerPathLo_le_outerTangentEdgeCrosses
      stage stage hlocal stage 0
  have h' :
      (rationalPointPathLength
        (circleSamplePoint stage 0 ::
          innerBoundaryFrom stage (0 + 1) stage) stage).lo <=
      0 + Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage 0)
          (outerBoundaryFrom stage 0 stage)) := by
    grind [Fan.perimeter]
  simpa [innerQuarterLength, outerFanWidths, innerBoundary, outerBoundary,
    Fan.sectorFanWidths, Fan.perimeter, innerBoundaryFrom,
    outerBoundaryFrom, piCircleAreaPolygon.innerBoundaryFrom,
    piCircleAreaPolygon.outerBoundaryFrom, Fan.edgeCrossesFrom, Fan.sumRat,
    pointCross_origin_left] using h'

theorem innerQuarterLength_lo_le_outerFanPerimeter
    (stage : Nat) (hstage : 0 < stage) :
    (innerQuarterLength stage).lo <=
      Fan.perimeter (outerFanWidths stage) :=
  innerQuarterLength_lo_le_outerFanPerimeter_of_adjacent
    stage (chordLengthLo_le_outerTangentCrossSum stage hstage)

theorem outerQuarterLength_lo_le_outerFanPerimeter
    (stage : Nat) (hstage : 0 < stage) :
    (outerQuarterLength stage).lo <=
      Fan.perimeter (outerFanWidths stage) := by
  simpa [outerQuarterLength, outerFanWidths] using
    Fan.pathLength_lo_le_sectorFanPerimeter
      stage (outerBoundary stage)
      (outerBoundary_consecutiveLengthLoLeCross stage hstage stage)

theorem outerFanPerimeter_le_outerQuarterLength_hi
    (stage : Nat) (hstage : 0 < stage) :
    Fan.perimeter (outerFanWidths stage) <=
      (outerQuarterLength stage).hi :=
  Fan.sectorFanPerimeter_le_pathLength_hi
    stage (outerBoundary stage)
    (outerBoundary_consecutiveCrossLe stage hstage stage)

theorem outerFanPerimeter_mem_outerQuarterLength
    (stage : Nat) (hstage : 0 < stage) :
    (outerQuarterLength stage).lo <=
        Fan.perimeter (outerFanWidths stage) /\
      Fan.perimeter (outerFanWidths stage) <=
        (outerQuarterLength stage).hi :=
  ⟨outerQuarterLength_lo_le_outerFanPerimeter stage hstage,
    outerFanPerimeter_le_outerQuarterLength_hi stage hstage⟩

def crossFanBoundsOfLocalTangentBounds
    (stage : Nat) (bounds : LocalTangentBounds stage) :
    CrossFanBounds stage where
  innerCrossNonneg := bounds.innerCrossNonneg
  outerCrossNonneg := bounds.outerCrossNonneg
  outerCrossLeLength := bounds.outerCrossLeLength
  innerPerimeter_le_outerPerimeter :=
    innerFanPerimeter_le_outerFanPerimeter_of_adjacent
      stage bounds.chordCross_le_tangentCrossSum
  innerComputedLo_le_outerPerimeter :=
    innerQuarterLength_lo_le_outerFanPerimeter_of_adjacent
      stage bounds.chordLengthLo_le_tangentCrossSum

theorem finiteArchimedesBounds_of_localTangentBounds
    (bounds : forall stage : Nat, 0 < stage -> LocalTangentBounds stage) :
    FiniteArchimedesBounds :=
  finiteArchimedesBounds_of_crossFanBounds
    (fun stage hstage =>
      crossFanBoundsOfLocalTangentBounds stage (bounds stage hstage))

theorem finiteArchimedesBounds : FiniteArchimedesBounds :=
  finiteArchimedesBounds_of_localTangentBounds
    (fun stage hstage => localTangentBounds stage hstage)

theorem sectorFanBounds
    (stage : Nat) (hstage : 0 < stage) :
    SectorFanBounds stage :=
  sectorFanBoundsOfCrossFanBounds stage
    (crossFanBoundsOfLocalTangentBounds stage
      (localTangentBounds stage hstage))

theorem innerQuarterArea_le_outerQuarterArea_of_sectorFanBounds
    (stage : Nat) (bounds : SectorFanBounds stage) :
    innerQuarterArea stage <= outerQuarterArea stage := by
  have hinner :
      innerQuarterArea stage <= Fan.perimeter (innerFanWidths stage) / 2 := by
    rw [innerQuarterArea_eq_variable_unit_fan stage
      (Fan.sumRat_nonneg (innerFanWidths stage) bounds.innerWidths_nonneg)]
    have hvar :=
      Fan.variableArea_le_half_perimeter
        (innerFanPieces stage)
        (innerFanPieces_heights_le_one stage)
        (innerFanPieces_widths_nonneg stage bounds.innerWidths_nonneg)
    simpa [innerFanPieces, Fan.widths_unitPieces] using hvar
  have hperim :
      Fan.perimeter (innerFanWidths stage) / 2 <=
        Fan.perimeter (outerFanWidths stage) / 2 :=
    div_two_le_div_two bounds.innerPerimeter_le_outerPerimeter
  have houter :
      Fan.perimeter (outerFanWidths stage) / 2 =
        outerQuarterArea stage := by
    rw [outerQuarterArea_eq_area_one stage bounds.outerWidths_sum_nonneg]
    rw [Fan.area_one_eq_half_perimeter]
  calc
    innerQuarterArea stage <=
        Fan.perimeter (innerFanWidths stage) / 2 := hinner
    _ <= Fan.perimeter (outerFanWidths stage) / 2 := hperim
    _ = outerQuarterArea stage := houter

theorem innerQuarterArea_le_outerQuarterArea
    (stage : Nat) (hstage : 0 < stage) :
    innerQuarterArea stage <= outerQuarterArea stage :=
  innerQuarterArea_le_outerQuarterArea_of_sectorFanBounds
    stage (sectorFanBounds stage hstage)

theorem innerQuarterLength_lo_le_outerQuarterLength_hi_of_sectorFanBounds
    (stage : Nat) (bounds : SectorFanBounds stage) :
    (innerQuarterLength stage).lo <= (outerQuarterLength stage).hi :=
  Rat.le_trans bounds.innerComputedLo_le_outerPerimeter
    bounds.outerPerimeter_le_outerComputedHi

theorem innerQuarterLength_lo_le_outerQuarterLength_hi
    (stage : Nat) (hstage : 0 < stage) :
    (innerQuarterLength stage).lo <= (outerQuarterLength stage).hi :=
  innerQuarterLength_lo_le_outerQuarterLength_hi_of_sectorFanBounds
    stage (sectorFanBounds stage hstage)

theorem piCircleAreaPolygonComputeAtStage_ordered
    (stage : Nat) (hstage : 0 < stage) :
    0 <= (piCircleAreaPolygonComputeAtStage stage).width := by
  have h := innerQuarterArea_le_outerQuarterArea stage hstage
  have hscaled :
      4 * innerQuarterArea stage <= 4 * outerQuarterArea stage :=
    four_mul_le_four_mul h
  unfold piCircleAreaPolygonComputeAtStage QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem piCircumferenceCommonComputeAtStage_ordered
    (stage : Nat) (hstage : 0 < stage) :
    0 <= (piCircumferenceCommonComputeAtStage stage).width := by
  have h := innerQuarterLength_lo_le_outerQuarterLength_hi stage hstage
  have hscaled :
      (4 * (innerQuarterLength stage).lo) / 2 <=
        (4 * (outerQuarterLength stage).hi) / 2 :=
    div_two_le_div_two (four_mul_le_four_mul h)
  have hnonneg :
      0 <= (4 * (outerQuarterLength stage).hi) / 2 -
        (4 * (innerQuarterLength stage).lo) / 2 := by
    grind [Rat.sub_eq_add_neg]
  simpa [piCircumferenceCommonComputeAtStage, innerQuarterLength,
    outerQuarterLength, QInterval.width] using hnonneg

private theorem four_div_two_eq_two_mul (x : Rat) :
    (4 * x) / 2 = 2 * x := by
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

def circumferenceQuarterGap (stage : Nat) : Rat :=
  (outerQuarterLength stage).hi - (innerQuarterLength stage).lo

theorem piCircumferenceCommonComputeAtStage_width_eq
    (stage : Nat) :
    (piCircumferenceCommonComputeAtStage stage).width =
      2 * circumferenceQuarterGap stage := by
  simp [piCircumferenceCommonComputeAtStage, circumferenceQuarterGap,
    innerQuarterLength, outerQuarterLength, QInterval.width,
    four_div_two_eq_two_mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem piCircumference_compute_width_eq (n : Nat) :
    (piCircumference.compute n).width =
      2 * circumferenceQuarterGap (piStage n) := by
  rw [piCircumference_compute_eq, piCircumferenceComputeAtStage_eq_common]
  exact piCircumferenceCommonComputeAtStage_width_eq (piStage n)

def circumferenceFanGap (stage : Nat) : Rat :=
  Fan.perimeter (outerFanWidths stage) - Fan.perimeter (innerFanWidths stage)

def circumferencePathWidthBudget (stage : Nat) : Rat :=
  pathSegmentWidthBudget (innerBoundary stage) stage +
    pathSegmentWidthBudget (outerBoundary stage) stage

theorem circumferencePathWidthBudget_le_three_stage_mul
    (stage : Nat) (B : Rat)
    (hinner : InnerBoundarySegmentBudgetLe stage B)
    (houter : OuterBoundarySegmentBudgetLe stage B) :
    circumferencePathWidthBudget stage <= (3 * (stage : Rat)) * B := by
  have hi :=
    pathSegmentWidthBudget_le_count_mul
      stage B (innerBoundary stage) hinner
  have ho :=
    pathSegmentWidthBudget_le_count_mul
      stage B (outerBoundary stage) houter
  rw [pathSegmentCount_innerBoundary] at hi
  rw [pathSegmentCount_outerBoundary] at ho
  unfold circumferencePathWidthBudget
  calc
    pathSegmentWidthBudget (innerBoundary stage) stage +
        pathSegmentWidthBudget (outerBoundary stage) stage <=
      (stage : Rat) * B + (↑(2 * stage) : Rat) * B := by
        grind
    _ = (3 * (stage : Rat)) * B := by
        grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]

theorem circumferenceFanGap_nonneg
    (stage : Nat) (hstage : 0 < stage) :
    0 <= circumferenceFanGap stage := by
  have h := innerFanPerimeter_le_outerFanPerimeter stage hstage
  unfold circumferenceFanGap
  grind [Rat.sub_eq_add_neg]

theorem circumferencePathWidthBudget_nonneg (stage : Nat) :
    0 <= circumferencePathWidthBudget stage := by
  unfold circumferencePathWidthBudget
  exact Rat.add_nonneg
    (pathSegmentWidthBudget_nonneg (innerBoundary stage) stage)
    (pathSegmentWidthBudget_nonneg (outerBoundary stage) stage)

theorem circumferenceQuarterGap_le_fanGap_add_pathWidthBudget
    (stage : Nat) (hstage : 0 < stage) :
    circumferenceQuarterGap stage <=
      circumferenceFanGap stage + circumferencePathWidthBudget stage := by
  let I := innerQuarterLength stage
  let O := outerQuarterLength stage
  let Fi := Fan.perimeter (innerFanWidths stage)
  let Fo := Fan.perimeter (outerFanWidths stage)
  have hFo_lo : O.lo <= Fo := by
    dsimp [O, Fo]
    exact outerQuarterLength_lo_le_outerFanPerimeter stage hstage
  have hFi_hi : Fi <= I.hi := by
    dsimp [I, Fi]
    exact innerFanPerimeter_le_innerQuarterLength_hi stage
  have hOwidth : O.hi - Fo <= O.width := by
    dsimp [O]
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hIwidth : Fi - I.lo <= I.width := by
    dsimp [I]
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hsum :
      O.hi - I.lo = (O.hi - Fo) + (Fo - Fi) + (Fi - I.lo) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  have hparts :
      (O.hi - Fo) + (Fo - Fi) + (Fi - I.lo) <=
        O.width + (Fo - Fi) + I.width := by
    grind [Rat.add_assoc, Rat.add_comm]
  have hbudgetI :
      I.width = pathSegmentWidthBudget (innerBoundary stage) stage := by
    dsimp [I]
    exact rationalPointPathLength_width_eq_segmentBudget
      (innerBoundary stage) stage
  have hbudgetO :
      O.width = pathSegmentWidthBudget (outerBoundary stage) stage := by
    dsimp [O]
    exact rationalPointPathLength_width_eq_segmentBudget
      (outerBoundary stage) stage
  unfold circumferenceQuarterGap circumferenceFanGap
    circumferencePathWidthBudget
  dsimp [I, O, Fi, Fo] at hsum hparts hbudgetI hbudgetO
  rw [hsum]
  calc
    (outerQuarterLength stage).hi - Fan.perimeter (outerFanWidths stage) +
          (Fan.perimeter (outerFanWidths stage) -
            Fan.perimeter (innerFanWidths stage)) +
        (Fan.perimeter (innerFanWidths stage) - (innerQuarterLength stage).lo)
        <=
      (outerQuarterLength stage).width +
          (Fan.perimeter (outerFanWidths stage) -
            Fan.perimeter (innerFanWidths stage)) +
        (innerQuarterLength stage).width := hparts
    _ =
      (Fan.perimeter (outerFanWidths stage) -
          Fan.perimeter (innerFanWidths stage)) +
        (pathSegmentWidthBudget (innerBoundary stage) stage +
          pathSegmentWidthBudget (outerBoundary stage) stage) := by
        rw [hbudgetI, hbudgetO]
        grind [Rat.add_assoc, Rat.add_comm]

theorem piCircleAreaPolygon_ordered (n : Nat) :
    0 <= (piCircleAreaPolygon.compute n).width := by
  rw [piCircleAreaPolygon_compute_eq]
  exact piCircleAreaPolygonComputeAtStage_ordered
    (piStage n) (piStage_pos n)

theorem piCircleArea_equiv_self (hvalid : AreaValid) :
    piCircleArea.Equiv piCircleArea :=
  RealRaw.equiv_refl piCircleArea hvalid

theorem piCircleAreaPolygon_equiv_self :
    piCircleAreaPolygon.Equiv piCircleAreaPolygon := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    piCircleAreaPolygon piCircleAreaPolygon n n).2
  have hordered := piCircleAreaPolygon_ordered n
  unfold QInterval.width at hordered
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem four_arctan_one_equiv_piCircleArea_of_powerSeriesGeometryAtOne
    (hagree : ArctanGeometry.PowerSeriesAgreesAt (1 : Rat)) :
    (((4 : Nat) * arctan (1 : Rat) : RealRaw).Equiv piCircleArea) := by
  have hscaled :
      (((4 : Nat) * arctan (1 : Rat) : RealRaw).Equiv
        ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw)) :=
    RealRaw.natScale_equiv 4 hagree
  intro n
  have hover := (RealRaw.compareAt_overlap_iff
      ((4 : Nat) * arctan (1 : Rat) : RealRaw)
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) n n).1
    (hscaled n)
  apply (RealRaw.compareAt_overlap_iff
    ((4 : Nat) * arctan (1 : Rat) : RealRaw) piCircleArea n n).2
  rw [← four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  exact hover

theorem four_arctan_one_equiv_piCircleArea_of_powerSeriesGeometryAgreement
    (hagree : ArctanGeometry.PowerSeriesAgreesOnUnit) :
    (((4 : Nat) * arctan (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctan_one_equiv_piCircleArea_of_powerSeriesGeometryAtOne
    (ArctanGeometry.powerSeriesAgreesAt_of_agreement
      hagree (by unfold Elementary.Arctan.powerSeriesDomain qabs; native_decide))

theorem four_arctanSeries_one_equiv_piCircleArea_of_powerSeriesGeometryAtOne
    (hagree : ArctanGeometry.PowerSeriesAgreesAt (1 : Rat)) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) := by
  simpa [arctanSeries] using
    four_arctan_one_equiv_piCircleArea_of_powerSeriesGeometryAtOne hagree

theorem four_arctanSeries_one_equiv_piCircleArea_of_powerSeriesGeometryAgreement
    (hagree : ArctanGeometry.PowerSeriesAgreesOnUnit) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) := by
  simpa [arctanSeries] using
    four_arctan_one_equiv_piCircleArea_of_powerSeriesGeometryAgreement hagree

theorem four_arctanSeries_one_equiv_piCircleArea_of_kernelComparisonAtOne
    (route : Taylor.ArctanComparison.KernelComparisonAt (1 : Rat)) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_powerSeriesGeometryAtOne
    (Taylor.ArctanComparison.powerSeriesAgreesAt_of_kernelComparisonAt route)

theorem four_arctanSeries_one_equiv_piCircleArea_of_powerSeriesRectangleKernelAtOne
    (hps : PowerSeriesEqualsRectangleKernelAtOne) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_kernelComparisonAtOne
    (kernelComparisonAtOne_of_powerSeriesEqualsRectangleKernelAtOne hps)

theorem four_arctanSeries_one_equiv_piCircleArea_of_leibnizEqualsRectangleRawAtOne
    (h : LeibnizEqualsRectangleRawAtOne) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_powerSeriesRectangleKernelAtOne
    (powerSeriesEqualsRectangleKernelAtOne_of_leibnizEqualsRectangleRawAtOne h)

/-- The public Leibniz/area pi equivalence, discharged by the finite rational
Riemann bridge rather than a completeness theorem or a separate arctangent
integral definition. -/
theorem four_arctanSeries_one_equiv_piCircleArea :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_leibnizEqualsRectangleRawAtOne
    leibnizEqualsRectangleRawAtOne_finiteRiemannBridge

theorem four_arctanSeries_one_equiv_piCircleArea_of_rawOverlapsUpToAll
    (h : LeibnizRectangleRawAtOneOverlapsUpToAll) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_rawOverlapsUpToAll h)

theorem four_arctanSeries_one_equiv_piCircleArea_of_kernelBounds
    (h : LeibnizRectangleKernelBoundsAtOne) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_kernelBounds h)

theorem four_arctanSeries_one_equiv_piCircleArea_of_kernelBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelBoundsAtOneUpToAll) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_kernelBoundsUpToAll h)

theorem four_arctanSeries_one_equiv_piCircleArea_of_uniformCellBounds
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformCellBoundsAtOne) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_uniformCellBounds h)

theorem four_arctanSeries_one_equiv_piCircleArea_of_unitUniformCellBounds
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOne) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_unitUniformCellBounds h)

theorem four_arctanSeries_one_equiv_piCircleArea_of_cellBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleKernelCellBoundsAtOneUpToAll) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_cellBoundsUpToAll h)

theorem four_arctanSeries_one_equiv_piCircleArea_of_unitUniformCellBoundsUpToAll
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOneUpToAll) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_unitUniformCellBoundsUpToAll h)

theorem four_arctanSeries_one_equiv_piCircleArea_of_pointwiseIntegralBridge
    (h : LeibnizRectangleBridge.LeibnizRectanglePointwiseIntegralBridgeAtOne) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_uniformCellBounds
    (LeibnizRectangleBridge.uniformCellBounds_of_pointwiseIntegralBridge h)

theorem four_arctanSeries_one_equiv_piCircleArea_of_pointwiseUnitIntegralBridge
    (h : LeibnizRectangleBridge.LeibnizRectanglePointwiseUnitIntegralBridgeAtOne) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_unitUniformCellBounds
    (LeibnizRectangleBridge.unitUniformCellBounds_of_pointwiseUnitIntegralBridge h)

theorem four_arctanSeries_one_equiv_piCircleArea_of_unitCellOrderPreservation
    (h : LeibnizRectangleBridge.LeibnizRectangleUnitCellOrderPreservation) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_pointwiseUnitIntegralBridge
    (LeibnizRectangleBridge.pointwiseUnitIntegralBridgeAtOne_of_unitCellOrderPreservation
      h)

theorem four_arctanSeries_one_equiv_piCircleArea_of_kernelPartialExactCellOrderPreservation
    (h :
      LeibnizRectangleBridge.KernelPartialExactCellOrderPreservationOnUnit) :
    (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw).Equiv piCircleArea) :=
  four_arctanSeries_one_equiv_piCircleArea_of_unitCellOrderPreservation
    (LeibnizRectangleBridge.unitCellOrderPreservation_of_kernelPartialExactCellOrderPreservation
      h)

theorem piCircleArea_equiv_four_arctan_one_of_powerSeriesGeometryAgreement
    (hagree : ArctanGeometry.PowerSeriesAgreesOnUnit) :
    piCircleArea.Equiv (((4 : Nat) * arctan (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctan_one_equiv_piCircleArea_of_powerSeriesGeometryAgreement hagree)

theorem piCircleArea_equiv_four_arctan_one_of_powerSeriesGeometryAtOne
    (hagree : ArctanGeometry.PowerSeriesAgreesAt (1 : Rat)) :
    piCircleArea.Equiv (((4 : Nat) * arctan (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctan_one_equiv_piCircleArea_of_powerSeriesGeometryAtOne hagree)

theorem piCircleArea_equiv_four_arctanSeries_one_of_powerSeriesGeometryAtOne
    (hagree : ArctanGeometry.PowerSeriesAgreesAt (1 : Rat)) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_powerSeriesGeometryAtOne
      hagree)

theorem piCircleArea_equiv_four_arctanSeries_one_of_powerSeriesGeometryAgreement
    (hagree : ArctanGeometry.PowerSeriesAgreesOnUnit) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_powerSeriesGeometryAgreement
      hagree)

theorem piCircleArea_equiv_four_arctanSeries_one_of_kernelComparisonAtOne
    (route : Taylor.ArctanComparison.KernelComparisonAt (1 : Rat)) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_kernelComparisonAtOne
      route)

theorem piCircleArea_equiv_four_arctanSeries_one_of_powerSeriesRectangleKernelAtOne
    (hps : PowerSeriesEqualsRectangleKernelAtOne) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_powerSeriesRectangleKernelAtOne
      hps)

theorem piCircleArea_equiv_four_arctanSeries_one_of_leibnizEqualsRectangleRawAtOne
    (h : LeibnizEqualsRectangleRawAtOne) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_leibnizEqualsRectangleRawAtOne
      h)

theorem piCircleArea_equiv_four_arctanSeries_one_of_kernelBounds
    (h : LeibnizRectangleKernelBoundsAtOne) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_kernelBounds h)

theorem piCircleArea_equiv_four_arctanSeries_one_of_kernelBoundsUpToAll
    (h : forall N,
      LeibnizRectangleBridge.LeibnizRectangleKernelBoundsAtOneUpTo N) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_kernelBoundsUpToAll h)

theorem piCircleArea_equiv_four_arctanSeries_one_of_uniformCellBounds
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformCellBoundsAtOne) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_uniformCellBounds h)

theorem piCircleArea_equiv_four_arctanSeries_one_of_unitUniformCellBounds
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOne) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_unitUniformCellBounds h)

theorem piCircleArea_equiv_four_arctanSeries_one_of_cellBoundsUpToAll
    (h : forall N,
      LeibnizRectangleBridge.LeibnizRectangleKernelCellBoundsAtOneUpTo N) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_cellBoundsUpToAll h)

theorem piCircleArea_equiv_four_arctanSeries_one_of_unitUniformCellBoundsUpToAll
    (h : forall N,
      LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_unitUniformCellBoundsUpToAll h)

theorem piCircleArea_equiv_four_arctanSeries_one_of_pointwiseIntegralBridge
    (h : LeibnizRectangleBridge.LeibnizRectanglePointwiseIntegralBridgeAtOne) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_pointwiseIntegralBridge h)

theorem piCircleArea_equiv_four_arctanSeries_one_of_pointwiseUnitIntegralBridge
    (h : LeibnizRectangleBridge.LeibnizRectanglePointwiseUnitIntegralBridgeAtOne) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_pointwiseUnitIntegralBridge h)

theorem piCircleArea_equiv_four_arctanSeries_one_of_unitCellOrderPreservation
    (h : LeibnizRectangleBridge.LeibnizRectangleUnitCellOrderPreservation) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_unitCellOrderPreservation h)

theorem piCircleArea_equiv_four_arctanSeries_one_of_kernelPartialExactCellOrderPreservation
    (h :
      LeibnizRectangleBridge.KernelPartialExactCellOrderPreservationOnUnit) :
    piCircleArea.Equiv (((4 : Nat) * arctanSeries (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctanSeries_one_equiv_piCircleArea_of_kernelPartialExactCellOrderPreservation
      h)

theorem piFromArctanIntegral_equiv_piCircleArea_of_geom_agreement
    (c : IntegralIdentities.ArctanIntegralConstruction (1 : Rat))
    (hgeom :
      (IntegralIdentities.arctanIntegral (1 : Rat) c).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (IntegralIdentities.arctanIntegral (1 : Rat) c)).Equiv
        piCircleArea := by
  have hscaled :
      (IntegralIdentities.PiFromArctanIntegral
        (IntegralIdentities.arctanIntegral (1 : Rat) c)).Equiv
          ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) := by
    unfold IntegralIdentities.PiFromArctanIntegral
    exact RealRaw.natScale_equiv 4 hgeom
  intro n
  have hover := (RealRaw.compareAt_overlap_iff
      (IntegralIdentities.PiFromArctanIntegral
        (IntegralIdentities.arctanIntegral (1 : Rat) c))
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) n n).1
    (hscaled n)
  apply (RealRaw.compareAt_overlap_iff
    (IntegralIdentities.PiFromArctanIntegral
      (IntegralIdentities.arctanIntegral (1 : Rat) c))
    piCircleArea n n).2
  rw [← four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  exact hover

theorem piFromArctanIntegral_equiv_piCircleArea_of_definite_identity
    (primitive : RealFunRaw)
    (I : Integral.DefiniteIdentity
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      primitive 0 1)
    (hendpoint :
      (endpointDifferenceRaw primitive 0 1 I.endpoint_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (IntegralIdentities.arctanIntegral (1 : Rat) I.construction)).Equiv
        piCircleArea := by
  have hintegralEndpoint :
      (IntegralIdentities.arctanIntegral (1 : Rat) I.construction).Equiv
        (endpointDifferenceRaw primitive 0 1 I.endpoint_valid) := by
    simpa [IntegralIdentities.arctanIntegral] using I.equivalent
  have hendpointValid :
      (endpointDifferenceRaw primitive 0 1 I.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using I.endpoint_valid
  have hgeomValid :
      (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hgeom :
      (IntegralIdentities.arctanIntegral (1 : Rat) I.construction).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) :=
    RealRaw.equiv_trans
      (IntegralIdentities.arctanIntegral_valid (1 : Rat) I.construction)
      hendpointValid
      hgeomValid
      hintegralEndpoint
      hendpoint
  exact piFromArctanIntegral_equiv_piCircleArea_of_geom_agreement
    I.construction hgeom

theorem piFromArctanIntegralFor_equiv_piCircleArea_of_geom_agreement
    (c : Integral.ConstructionFor
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1))
    (hgeom :
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1) c).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1) c)).Equiv
        piCircleArea := by
  have hscaled :
      (IntegralIdentities.PiFromArctanIntegral
        (Integral.integralFor
          (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1) c)).Equiv
          ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) := by
    unfold IntegralIdentities.PiFromArctanIntegral
    exact RealRaw.natScale_equiv 4 hgeom
  intro n
  have hover := (RealRaw.compareAt_overlap_iff
      (IntegralIdentities.PiFromArctanIntegral
        (Integral.integralFor
          (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1) c))
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) n n).1
    (hscaled n)
  apply (RealRaw.compareAt_overlap_iff
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1) c))
    piCircleArea n n).2
  rw [← four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  exact hover

theorem piFromArctanIntegralFor_equiv_piCircleArea_of_definiteIdentityFor
    (primitive : FunctionOnInterval)
    (I : Integral.DefiniteIdentityFor
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1) primitive)
    (hendpoint :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 I.endpoint_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        I.construction)).Equiv piCircleArea := by
  have hintegralEndpoint :
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        I.construction).Equiv
        (endpointDifferenceRaw primitive.toRealFunRaw 0 1 I.endpoint_valid) := by
    simpa using I.equivalent
  have hendpointValid :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 I.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using I.endpoint_valid
  have hgeomValid :
      (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hgeom :
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        I.construction).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) :=
    RealRaw.equiv_trans
      (Integral.integralFor_valid
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        I.construction)
      hendpointValid
      hgeomValid
      hintegralEndpoint
      hendpoint
  exact piFromArctanIntegralFor_equiv_piCircleArea_of_geom_agreement
    I.construction hgeom

/-- Public-general-integral version of the arctangent-integral pi route.
This consumes an endpoint identity whose integral side is `generalIntegralFor`,
the finite sum over monotone pieces. -/
theorem piFromArctanGeneralIntegralFor_equiv_piCircleArea_of_generalDefiniteIdentityFor
    (primitive : FunctionOnInterval)
    (I : Integral.GeneralDefiniteIdentityFor
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1) primitive)
    (hendpoint :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 I.endpoint_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.generalIntegralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        I.construction)).Equiv piCircleArea := by
  have hintegralEndpoint :
      (Integral.generalIntegralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        I.construction).Equiv
        (endpointDifferenceRaw primitive.toRealFunRaw 0 1 I.endpoint_valid) := by
    simpa using I.equivalent
  have hendpointValid :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 I.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using I.endpoint_valid
  have hgeomValid :
      (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hgeom :
      (Integral.generalIntegralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        I.construction).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) :=
    RealRaw.equiv_trans
      (Integral.generalIntegralFor_valid
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        I.construction)
      hendpointValid
      hgeomValid
      hintegralEndpoint
      hendpoint
  have hscaled :
      (IntegralIdentities.PiFromArctanIntegral
        (Integral.generalIntegralFor
          (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
          I.construction)).Equiv
          ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) := by
    unfold IntegralIdentities.PiFromArctanIntegral
    exact RealRaw.natScale_equiv 4 hgeom
  intro n
  have hover := (RealRaw.compareAt_overlap_iff
      (IntegralIdentities.PiFromArctanIntegral
        (Integral.generalIntegralFor
          (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
          I.construction))
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) n n).1
    (hscaled n)
  apply (RealRaw.compareAt_overlap_iff
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.generalIntegralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        I.construction))
    piCircleArea n n).2
  rw [← four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  exact hover

/-- Public-general-integral pi route obtained from an ordinary
`DefiniteIdentityFor` plus an equivalent general construction.  This is the
adapter used when an FTC proof first produces a domain-aware endpoint identity
for a concrete construction, and a separate monotone-piece construction is
known to compute the same raw integral. -/
theorem piFromArctanGeneralIntegralFor_equiv_piCircleArea_of_definiteIdentityFor_generalConstruction
    (primitive : FunctionOnInterval)
    (I : Integral.DefiniteIdentityFor
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1) primitive)
    (construction :
      Integral.GeneralConstructionFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1))
    (hconstruction :
      (Integral.generalIntegralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        construction).Equiv
        (Integral.integralFor
          (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
          I.construction))
    (hendpoint :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 I.endpoint_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.generalIntegralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        construction)).Equiv piCircleArea :=
  piFromArctanGeneralIntegralFor_equiv_piCircleArea_of_generalDefiniteIdentityFor
    primitive
    (Integral.GeneralDefiniteIdentityFor.ofDefiniteIdentityFor
      I construction hconstruction)
    hendpoint

/-- Domain-aware monotone definite-integral route to the arctangent-integral
pi equivalence.  This consumes a monotone-integral endpoint identity directly,
then forgets the monotonicity certificate through
`MonotoneDefiniteIdentityFor.toDefiniteIdentityFor`. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_monotoneDefiniteIdentityFor
    (primitive : FunctionOnInterval)
    (I : Integral.MonotoneDefiniteIdentityFor
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1) primitive)
    (hendpoint :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 I.endpoint_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.monotoneIntegralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        I.construction)).Equiv piCircleArea := by
  simpa [Integral.MonotoneDefiniteIdentityFor.toDefiniteIdentityFor,
    Integral.monotoneIntegralFor] using
    (piFromArctanIntegralFor_equiv_piCircleArea_of_definiteIdentityFor
      primitive I.toDefiniteIdentityFor hendpoint)

/-- Domain-aware effective-FTC route to the arctangent-integral pi
equivalence.  The conclusion uses the `ConstructionFor` integral produced by
the FTC certificate, not the older point-Riemann wrapper. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_effectiveFTC
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : EffectiveFTC primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hscheduledEndpoint : (FTC.endpointRawOfEffectiveFTC h).Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (hendpoint_equiv :
      (FTC.endpointRawOfEffectiveFTC h).Equiv
        (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint))
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_effectiveFTC h hriemann))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_definiteIdentityFor
    primitive
    (Integral.definiteIdentityFor_of_effectiveFTC
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_lower)
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_upper)
      h hriemann hscheduledEndpoint hendpoint hendpoint_equiv)
    hgeom

/-- Domain-aware effective-FTC route using packaged endpoint-schedule
agreement. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_effectiveFTC_endpointAgreement
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : EffectiveFTC primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw 0 1
        (FTC.endpointRawOfEffectiveFTC h))
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1
        endpoint.endpoint_valid).Equiv
          (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_effectiveFTC h hriemann))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_effectiveFTC
    primitive same_lower same_upper h hriemann
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent hgeom

/-- Effective-FTC route where the endpoint schedule is supplied as a cofinal
monotone stage schedule. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_effectiveFTC_stageSchedule
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : EffectiveFTC primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h).Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (FTC.requestedPrecision n) =
        sigma.stage n)
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_effectiveFTC h hriemann))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_effectiveFTC_endpointAgreement
    primitive same_lower same_upper h hriemann
    (FTC.endpointScheduleAgreement_of_effectiveFTC_stageSchedule
      h hendpoint sigma hsigma)
    hgeom

/-- Static-dyadic specialization of the domain-aware effective-FTC route to
the arctangent-integral pi equivalence. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_staticDyadicEffectiveFTC
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hscheduledEndpoint :
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (hendpoint_equiv :
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Equiv
        (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint))
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_staticDyadicEffectiveFTC h hriemann))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_definiteIdentityFor
    primitive
    (Integral.definiteIdentityFor_of_staticDyadicEffectiveFTC
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_lower)
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_upper)
      h hriemann hscheduledEndpoint hendpoint hendpoint_equiv)
    hgeom

/-- Static-dyadic effective-FTC route using packaged endpoint-schedule
agreement. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_staticDyadicEffectiveFTC_endpointAgreement
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw 0 1
        (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC))
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1
        endpoint.endpoint_valid).Equiv
          (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_staticDyadicEffectiveFTC h hriemann))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_staticDyadicEffectiveFTC
    primitive same_lower same_upper h hriemann
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent hgeom

/-- Static-dyadic effective-FTC route where the endpoint schedule is supplied
as a cofinal monotone stage schedule. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_staticDyadicEffectiveFTC_stageSchedule
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : StaticDyadicEffectiveFTC primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hriemann : (FTC.riemannRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n, h.chooseEvalPrecision (FTC.requestedPrecision n) =
        sigma.stage n)
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_staticDyadicEffectiveFTC h hriemann))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_staticDyadicEffectiveFTC_endpointAgreement
    primitive same_lower same_upper h hriemann
    (FTC.endpointScheduleAgreement_of_staticDyadicEffectiveFTC_stageSchedule
      h hendpoint sigma hsigma)
    hgeom

/-- Candidate-derivative FTC route to the domain-aware arctangent-integral pi
equivalence. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_candidateDerivativeFTC
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint))
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_candidateDerivativeFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_definiteIdentityFor
    primitive
    (Integral.definiteIdentityFor_of_candidateDerivativeFTC
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_lower)
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_upper)
      h hbounded hscheduledEndpoint hendpoint hendpoint_equiv)
    hgeom

/-- Candidate-derivative FTC route using packaged endpoint-schedule
agreement. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_candidateDerivativeFTC_endpointAgreement
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw 0 1
        h.toDerivativeBoundFTC.endpointRaw)
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1
        endpoint.endpoint_valid).Equiv
          (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_candidateDerivativeFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_candidateDerivativeFTC
    primitive same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent hgeom

/-- Candidate-derivative FTC route where the endpoint schedule is supplied as
a cofinal monotone stage schedule. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_candidateDerivativeFTC_stageSchedule
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : CandidateDerivativeFTC primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_candidateDerivativeFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_candidateDerivativeFTC_endpointAgreement
    primitive same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_candidateDerivativeFTC_stageSchedule
      h hendpoint sigma hsigma)
    hgeom

/-- Curvature FTC route to the domain-aware arctangent-integral pi
equivalence.  Unlike the convex-only route, this also covers concave
primitives such as the arctangent branch on `[0,1]`. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_curvatureFTC
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint))
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_curvatureFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_definiteIdentityFor
    primitive
    (Integral.definiteIdentityFor_of_curvatureFTC
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_lower)
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_upper)
      h hbounded hscheduledEndpoint hendpoint hendpoint_equiv)
    hgeom

/-- Curvature FTC route using packaged endpoint-schedule agreement. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_curvatureFTC_endpointAgreement
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw 0 1
        h.toDerivativeBoundFTC.endpointRaw)
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1
        endpoint.endpoint_valid).Equiv
          (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_curvatureFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_curvatureFTC
    primitive same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent hgeom

/-- Curvature FTC route where the endpoint schedule is supplied as a cofinal
monotone stage schedule. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_curvatureFTC_stageSchedule
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : CurvatureFTCCertificate primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_curvatureFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_curvatureFTC_endpointAgreement
    primitive same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_curvatureFTC_stageSchedule
      h hendpoint sigma hsigma)
    hgeom

/-- Convex FTC route to the domain-aware arctangent-integral pi equivalence. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_convexFTC
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : ConvexFTCCertificate primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint))
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_convexFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_definiteIdentityFor
    primitive
    (Integral.definiteIdentityFor_of_convexFTC
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_lower)
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_upper)
      h hbounded hscheduledEndpoint hendpoint hendpoint_equiv)
    hgeom

/-- Convex FTC route using packaged endpoint-schedule agreement. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_convexFTC_endpointAgreement
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : ConvexFTCCertificate primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw 0 1
        h.toDerivativeBoundFTC.endpointRaw)
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1
        endpoint.endpoint_valid).Equiv
          (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_convexFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_convexFTC
    primitive same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent hgeom

/-- Convex FTC route where the endpoint schedule is supplied as a cofinal
monotone stage schedule. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_convexFTC_stageSchedule
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : ConvexFTCCertificate primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_convexFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_convexFTC_endpointAgreement
    primitive same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_convexFTC_stageSchedule
      h hendpoint sigma hsigma)
    hgeom

/-- Concave FTC route to the domain-aware arctangent-integral pi
equivalence.  This is the curvature specialization naturally matched to the
arctangent primitive on `[0,1]`. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_concaveFTC
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hscheduledEndpoint : h.toDerivativeBoundFTC.endpointRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (hendpoint_equiv :
      h.toDerivativeBoundFTC.endpointRaw.Equiv
        (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint))
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_concaveFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_definiteIdentityFor
    primitive
    (Integral.definiteIdentityFor_of_concaveFTC
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_lower)
      (by simpa [IntegralIdentities.oneOverOnePlusSquareOnInterval] using
        same_upper)
      h hbounded hscheduledEndpoint hendpoint hendpoint_equiv)
    hgeom

/-- Concave FTC route using packaged endpoint-schedule agreement. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_concaveFTC_endpointAgreement
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (endpoint :
      FTC.EndpointScheduleAgreement primitive.toRealFunRaw 0 1
        h.toDerivativeBoundFTC.endpointRaw)
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1
        endpoint.endpoint_valid).Equiv
          (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_concaveFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_concaveFTC
    primitive same_lower same_upper h hbounded
    endpoint.scheduled_valid endpoint.endpoint_valid endpoint.equivalent hgeom

/-- Concave FTC route where the endpoint schedule is supplied as a cofinal
monotone stage schedule.  This is the schedule-facing form of the route
naturally matched to the arctangent primitive on `[0,1]`. -/
theorem piFromArctanIntegralFor_equiv_piCircleArea_of_concaveFTC_stageSchedule
    (primitive : FunctionOnInterval)
    (same_lower : primitive.lower = 0)
    (same_upper : primitive.upper = 1)
    (h : ConcaveFTCCertificate primitive.toRealFunRaw
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (hbounded : h.toDerivativeBoundFTC.boundedIntegralRaw.Valid)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute primitive.toRealFunRaw 0 1))
    (sigma : RealRaw.StageSchedule)
    (hsigma :
      forall n,
        h.toDerivativeBoundFTC.chooseEndpointPrecision
            (precisionAtStage n) =
          sigma.stage n)
    (hgeom :
      (endpointDifferenceRaw primitive.toRealFunRaw 0 1 hendpoint).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
        (Integral.constructionFor_of_concaveFTC h hbounded))).Equiv
        piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_concaveFTC_endpointAgreement
    primitive same_lower same_upper h hbounded
    (FTC.endpointScheduleAgreement_of_concaveFTC_stageSchedule
      h hendpoint sigma hsigma)
    hgeom

theorem piFromArctanIntegralUnitAtOne_equiv_piCircleArea_of_geom_agreement
    (c : Integral.ConstructionFor
      (IntegralIdentities.arctanKernelInterval (1 : Rat)))
    (hgeom :
      (IntegralIdentities.arctanIntegralUnit (1 : Rat) c).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (IntegralIdentities.arctanIntegralUnit (1 : Rat) c)).Equiv
        piCircleArea := by
  have hgeom' :
      (Integral.integralFor
        (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1) c).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) := by
    simpa [IntegralIdentities.arctanIntegralUnit,
      IntegralIdentities.arctanKernelInterval] using hgeom
  simpa [IntegralIdentities.arctanIntegralUnit,
    IntegralIdentities.arctanKernelInterval] using
    piFromArctanIntegralFor_equiv_piCircleArea_of_geom_agreement
      c hgeom'

theorem piFromArctanIntegralUnitAtOne_equiv_piCircleArea_of_functionAgreement
    (data : IntegralIdentities.ArctanIntegralUnitData)
    (hgeom : IntegralIdentities.ArctanIntegralUnitGeomFunctionAgreement data) :
    (IntegralIdentities.PiFromArctanIntegral
      (IntegralIdentities.arctanIntegralUnit (1 : Rat)
        (data.constructionAt (1 : Rat)
          (by native_decide) (by native_decide)))).Equiv
        piCircleArea :=
  piFromArctanIntegralUnitAtOne_equiv_piCircleArea_of_geom_agreement
    (data.constructionAt (1 : Rat)
      (by native_decide) (by native_decide))
    (IntegralIdentities.arctanIntegralUnit_equiv_arctanGeom_of_functionAgreement
      data hgeom (by native_decide) (by native_decide))


theorem piFromArctanIntegral_equiv_piCircleArea_of_effectiveFTC
    (primitive : RealFunRaw)
    (h : EffectiveFTC primitive
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (c : IntegralIdentities.ArctanIntegralConstruction (1 : Rat))
    (hplan : c.plan = FTC.integralPlanOfEffectiveFTC h)
    (hscheduledEndpoint : (FTC.endpointRawOfEffectiveFTC h).Valid)
    (hendpoint :
      (FTC.endpointRawOfEffectiveFTC h).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (IntegralIdentities.arctanIntegral (1 : Rat) c)).Equiv
        piCircleArea := by
  have hintegralEndpoint :
      (IntegralIdentities.arctanIntegral (1 : Rat) c).Equiv
        (FTC.endpointRawOfEffectiveFTC h) := by
    simpa [IntegralIdentities.arctanIntegral] using
      FTC.effectiveFTC_integral_equiv_scheduledEndpoint h c hplan
  have hgeomValid :
      (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hgeom :
      (IntegralIdentities.arctanIntegral (1 : Rat) c).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) :=
    RealRaw.equiv_trans
      (IntegralIdentities.arctanIntegral_valid (1 : Rat) c)
      hscheduledEndpoint
      hgeomValid
      hintegralEndpoint
      hendpoint
  exact piFromArctanIntegral_equiv_piCircleArea_of_geom_agreement c hgeom

/-- Static-dyadic FTC route to the arctangent-integral pi equivalence.

This is the version aligned with the default bounded-integral mesh of
Chapter 3: the analytic input is a `StaticDyadicEffectiveFTC` certificate for
the arctangent kernel, plus the endpoint identification with the geometric
arctangent. -/
theorem piFromArctanIntegral_equiv_piCircleArea_of_staticDyadicEffectiveFTC
    (primitive : RealFunRaw)
    (h : StaticDyadicEffectiveFTC primitive
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1).toRealFunRaw
      0 1)
    (c : IntegralIdentities.ArctanIntegralConstruction (1 : Rat))
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (hscheduledEndpoint :
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Valid)
    (hendpoint :
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat))) :
    (IntegralIdentities.PiFromArctanIntegral
      (IntegralIdentities.arctanIntegral (1 : Rat) c)).Equiv
        piCircleArea := by
  have hintegralEndpoint :
      (IntegralIdentities.arctanIntegral (1 : Rat) c).Equiv
        (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC) := by
    simpa [IntegralIdentities.arctanIntegral] using
      FTC.staticDyadicEffectiveFTC_integral_equiv_scheduledEndpoint h c hplan
  have hgeomValid :
      (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hgeom :
      (IntegralIdentities.arctanIntegral (1 : Rat) c).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) :=
    RealRaw.equiv_trans
      (IntegralIdentities.arctanIntegral_valid (1 : Rat) c)
      hscheduledEndpoint
      hgeomValid
      hintegralEndpoint
      hendpoint
  exact piFromArctanIntegral_equiv_piCircleArea_of_geom_agreement c hgeom

theorem exists_piFromArctanIntegral_equiv_piCircleArea
    (hgeom : IntegralIdentities.ArctanIntegralGeomAgreement (1 : Rat)) :
    Exists fun c : IntegralIdentities.ArctanIntegralConstruction (1 : Rat) =>
      (IntegralIdentities.PiFromArctanIntegral
        (IntegralIdentities.arctanIntegral (1 : Rat) c)).Equiv
          piCircleArea := by
  rcases hgeom with ⟨c, hc⟩
  exact ⟨c, piFromArctanIntegral_equiv_piCircleArea_of_geom_agreement
    c hc⟩

theorem arctanIntegralPiRoute_of_geom_agreement
    (harea :
      IntegralIdentities.PiFromArctanIntegralAgrees
        (ArctanGeometry.arctanGeom (1 : Rat)))
    (hgeom : IntegralIdentities.ArctanIntegralGeomAgreement (1 : Rat)) :
    IntegralIdentities.ArctanIntegralPiRoute where
  integral_computes_geom_at_one := hgeom
  four_geom_arctan_one_eq_pi := harea

theorem piFromArctanIntegral_equiv_piCircleArea_of_function_agreement
    (data : IntegralIdentities.ArctanIntegralData)
    (hgeom : IntegralIdentities.ArctanIntegralGeomFunctionAgreement data) :
    (IntegralIdentities.PiFromArctanIntegral
      (IntegralIdentities.arctanIntegral (1 : Rat)
        (data.constructionAt (1 : Rat) (by native_decide)))).Equiv
        piCircleArea :=
  piFromArctanIntegral_equiv_piCircleArea_of_geom_agreement
    (data.constructionAt (1 : Rat) (by native_decide))
    (IntegralIdentities.arctanIntegral_equiv_arctanGeom_of_functionAgreement
      data hgeom (by native_decide))

theorem arctanIntegralPiRoute_of_function_agreement
    (harea :
      IntegralIdentities.PiFromArctanIntegralAgrees
        (ArctanGeometry.arctanGeom (1 : Rat)))
    (data : IntegralIdentities.ArctanIntegralData)
    (hgeom : IntegralIdentities.ArctanIntegralGeomFunctionAgreement data) :
    IntegralIdentities.ArctanIntegralPiRoute :=
  arctanIntegralPiRoute_of_geom_agreement harea
    (IntegralIdentities.arctanIntegralGeomAgreement_one_of_functionAgreement
      data hgeom)

theorem piCircumference_ordered (n : Nat) :
    0 <= (piCircumference.compute n).width := by
  rw [piCircumference_compute_eq,
    piCircumferenceComputeAtStage_eq_common]
  exact piCircumferenceCommonComputeAtStage_ordered
    (piStage n) (piStage_pos n)

theorem areaLower_le_circumferenceUpper_of_finite
    (bounds : FiniteArchimedesBounds) (stage : Nat) (hstage : 0 < stage) :
    (piCircleAreaPolygonComputeAtStage stage).lo <=
      (piCircumferenceCommonComputeAtStage stage).hi := by
  have h :=
    (bounds.atStage stage hstage).innerArea_le_half_outerLength
  have hscaled :
      4 * innerQuarterArea stage <=
        (4 * (outerQuarterLength stage).hi) / 2 := by
    calc
      4 * innerQuarterArea stage <=
          4 * ((outerQuarterLength stage).hi / 2) :=
        four_mul_le_four_mul h
      _ = (4 * (outerQuarterLength stage).hi) / 2 := by
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  simpa [piCircleAreaPolygonComputeAtStage, piCircumferenceCommonComputeAtStage,
    outerQuarterLength] using hscaled

theorem circumferenceLower_le_areaUpper_of_finite
    (bounds : FiniteArchimedesBounds) (stage : Nat) (hstage : 0 < stage) :
    (piCircumferenceCommonComputeAtStage stage).lo <=
      (piCircleAreaPolygonComputeAtStage stage).hi := by
  have h :=
    (bounds.atStage stage hstage).innerLength_le_twice_outerArea
  have hscaled :
      (4 * (innerQuarterLength stage).lo) / 2 <=
        4 * outerQuarterArea stage := by
    rw [show (4 * (innerQuarterLength stage).lo) / 2 =
        2 * (innerQuarterLength stage).lo by
      rw [Rat.div_def]
      have hne : (2 : Rat) != 0 := by native_decide
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]]
    have h2 := Rat.mul_le_mul_of_nonneg_left h
      (by native_decide : (0 : Rat) <= 2)
    calc
      2 * (innerQuarterLength stage).lo <=
          2 * (2 * outerQuarterArea stage) := h2
      _ = 4 * outerQuarterArea stage := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  simpa [piCircleAreaPolygonComputeAtStage, piCircumferenceCommonComputeAtStage,
    innerQuarterLength] using hscaled

/-- The direct finite Archimedes overlap needed for the two geometric
definitions in `Pi.lean`.

This is deliberately stated only with the public computations.  A proof should
come from the rational point geometry inside `piCircleArea` and
`piCircumference`: the area lower bound is below the circumference upper bound,
and the circumference lower bound is below the area upper bound, at every
stage. -/
structure AreaCircumferenceOverlapBounds where
  areaLower_le_circumferenceUpper :
    forall n, (piCircleArea.compute n).lo <= (piCircumference.compute n).hi
  circumferenceLower_le_areaUpper :
    forall n, (piCircumference.compute n).lo <= (piCircleArea.compute n).hi

theorem areaCircumference_sameStageOverlap_of_bounds
    (bounds : AreaCircumferenceOverlapBounds) :
    piCircleArea.SameStageOverlap piCircumference := by
  intro n
  exact (RealRaw.compareAt_overlap_iff piCircleArea piCircumference n n).2
    ⟨bounds.areaLower_le_circumferenceUpper n,
      bounds.circumferenceLower_le_areaUpper n⟩

theorem areaEqCircumference_of_bounds
    (bounds : AreaCircumferenceOverlapBounds) :
    AreaEqCircumference :=
  RealRaw.sameStageOverlap_equiv
    (areaCircumference_sameStageOverlap_of_bounds bounds)

theorem areaCircumferenceOverlapBounds_of_finite
    (hpoly : PiCircleAreaPolygonAgreement)
    (bounds : FiniteArchimedesBounds) :
    AreaCircumferenceOverlapBounds where
  areaLower_le_circumferenceUpper := by
    intro n
    rw [hpoly n]
    rw [piCircleAreaPolygon_compute_eq, piCircumference_compute_eq,
      piCircumferenceComputeAtStage_eq_common]
    exact areaLower_le_circumferenceUpper_of_finite
      bounds (piStage n) (piStage_pos n)
  circumferenceLower_le_areaUpper := by
    intro n
    rw [hpoly n]
    rw [piCircleAreaPolygon_compute_eq, piCircumference_compute_eq,
      piCircumferenceComputeAtStage_eq_common]
    exact circumferenceLower_le_areaUpper_of_finite
      bounds (piStage n) (piStage_pos n)

theorem areaEqCircumference_of_finite
    (hpoly : PiCircleAreaPolygonAgreement)
    (bounds : FiniteArchimedesBounds) :
    AreaEqCircumference :=
  areaEqCircumference_of_bounds
    (areaCircumferenceOverlapBounds_of_finite hpoly bounds)

/-- Archimedes' theorem: the polygonal area and circumference definitions of
pi determine the same computable real. -/
theorem archimedesTheorem
    (hpoly : PiCircleAreaPolygonAgreement) : AreaEqCircumference :=
  areaEqCircumference_of_finite hpoly finiteArchimedesBounds

theorem piCircumference_equiv_piCircleArea
    (hpoly : PiCircleAreaPolygonAgreement) :
    piCircumference.Equiv piCircleArea :=
  RealRaw.equiv_symm (archimedesTheorem hpoly)

/-- The finite Archimedes comparison is now connected to the public area loop.
The circumference computation still needs its separate validity proof before
this raw equivalence can close the scoreboard row. -/
theorem areaEqCircumference : AreaEqCircumference :=
  archimedesTheorem piCircleAreaPolygonAgreement

theorem piCircumference_equiv_piCircleArea_of_verified_area_polygon :
    piCircumference.Equiv piCircleArea :=
  RealRaw.equiv_symm areaEqCircumference

/-- The finite Archimedes comparison already gives same-stage overlap between
the polygon-area scaffolding computation and the circumference computation.

Unlike the public `piCircleArea` loop, the polygon computation need not first
be identified stagewise with another area representation for this finite
geometric equivalence. -/
theorem piCircleAreaPolygon_equiv_piCircumference :
    piCircleAreaPolygon.Equiv piCircumference := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    piCircleAreaPolygon piCircumference n n).2
  rw [piCircleAreaPolygon_compute_eq, piCircumference_compute_eq,
    piCircumferenceComputeAtStage_eq_common]
  exact ⟨
    areaLower_le_circumferenceUpper_of_finite finiteArchimedesBounds
      (piStage n) (piStage_pos n),
    circumferenceLower_le_areaUpper_of_finite finiteArchimedesBounds
      (piStage n) (piStage_pos n)⟩

theorem piCircumference_equiv_piCircleAreaPolygon :
    piCircumference.Equiv piCircleAreaPolygon :=
  RealRaw.equiv_symm piCircleAreaPolygon_equiv_piCircumference

/-- Validity certificates for the four public pi algorithms. -/
structure ValidityProofs where
  leibniz : LeibnizValid
  machin : MachinValid
  area : AreaValid
  circumference : CircumferenceValid

namespace AreaLoopValidity

def areaGap (p r : Rat) : Rat :=
  ((r - p) * (r - p) * (r - p)) /
    ((1 + p * r) * (1 + p * p) * (1 + r * r))

def areaGapSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => areaGap p r + areaGapSum rest

def areaCubeSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest =>
      (r - p) * (r - p) * (r - p) + areaCubeSum rest

def IntervalsWellFormed : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest =>
      0 <= p /\ p <= r /\ r <= 1 /\ IntervalsWellFormed rest

private theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d := by
  grind

private theorem half_square_div_eq (h d : Rat) :
    (2 * h * (h / 2) * (h / 2)) / d =
      (h * h * h) / (2 * d) := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem quarter_div_eq (h d : Rat) :
    (h * (h / 2) * (h / 2)) / d =
      (h * h * h) / (4 * d) := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem eighth_div_eq (h d : Rat) :
    ((h / 2) * (h / 2) * (h / 2)) / d =
      (h * h * h) / (8 * d) := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem midpoint_left_sub (p r : Rat) :
    (p + r) / 2 - p = (r - p) / 2 := by
  rw [Rat.div_def, Rat.div_def]
  have h2 : (2 : Rat) ≠ 0 := by native_decide
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem midpoint_right_sub (p r : Rat) :
    r - (p + r) / 2 = (r - p) / 2 := by
  rw [Rat.div_def, Rat.div_def]
  have h2 : (2 : Rat) ≠ 0 := by native_decide
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem areaGap_eq_factor (p r : Rat) :
    areaGap p r =
      ((r - p) * (r - p) * (r - p)) *
        (1 / ((1 + p * r) * (1 + p * p) * (1 + r * r))) := by
  unfold areaGap
  rw [Rat.div_def]
  grind [Rat.mul_assoc]

private theorem increment_mid_eq_factor (p r : Rat) :
    let q : Rat := (p + r) / 2
    circleAreaIncrement p q r =
      ((r - p) * (r - p) * (r - p)) *
        (1 / (2 * (1 + p * p) * (1 + q * q) * (1 + r * r))) := by
  intro q
  unfold circleAreaIncrement
  dsimp [q]
  rw [midpoint_left_sub, midpoint_right_sub]
  rw [half_square_div_eq]
  rw [Rat.div_def]
  grind [Rat.mul_assoc]

private theorem decrement_mid_eq_factor (p r : Rat) :
    let q : Rat := (p + r) / 2
    circleAreaDecrement p q r =
      ((r - p) * (r - p) * (r - p)) *
        (1 / (4 * (1 + p * r) * (1 + p * q) * (1 + q * r))) := by
  intro q
  unfold circleAreaDecrement
  dsimp [q]
  rw [midpoint_left_sub, midpoint_right_sub]
  rw [quarter_div_eq]
  rw [Rat.div_def]
  grind [Rat.mul_assoc]

private theorem areaGap_left_mid_eq_factor (p r : Rat) :
    let q : Rat := (p + r) / 2
    areaGap p q =
      ((r - p) * (r - p) * (r - p)) *
        (1 / (8 * (1 + p * q) * (1 + p * p) * (1 + q * q))) := by
  intro q
  unfold areaGap
  dsimp [q]
  rw [midpoint_left_sub]
  rw [eighth_div_eq]
  rw [Rat.div_def]
  grind [Rat.mul_assoc]

private theorem areaGap_right_mid_eq_factor (p r : Rat) :
    let q : Rat := (p + r) / 2
    areaGap q r =
      ((r - p) * (r - p) * (r - p)) *
        (1 / (8 * (1 + q * r) * (1 + q * q) * (1 + r * r))) := by
  intro q
  unfold areaGap
  dsimp [q]
  rw [midpoint_right_sub]
  rw [eighth_div_eq]
  rw [Rat.div_def]
  grind [Rat.mul_assoc]

private theorem rat_eq_of_mul_eq_mul_pos {a b c : Rat}
    (hc : 0 < c) (h : a * c = b * c) : a = b := by
  have hcne : c ≠ 0 := Rat.ne_of_gt hc
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem abstract_gap_den_identity {a b c x y z : Rat}
    (hx : x + c = 2 * a) (hz : z + c = 2 * b)
    (hy : a + b = 2 * y) :
    8 * a * b * y =
      4 * a * b * c + 2 * x * y * z + c * b * z + c * x * a := by
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

private theorem cancel_common {d t common : Rat}
    (hd : d ≠ 0) (hcommon : common = t * d) :
    (1 / d) * common = t := by
  rw [hcommon, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem abstract_gap_recip_identity {a b c x y z : Rat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z)
    (hx : x + c = 2 * a) (hz : z + c = 2 * b)
    (hy : a + b = 2 * y) :
    1 / (c * x * z) =
      1 / (2 * x * y * z) + 1 / (4 * c * a * b) +
        1 / (8 * a * x * y) + 1 / (8 * b * y * z) := by
  let D : Rat := a * b * c * x * y * z
  have hDpos : 0 < D := by
    dsimp [D]
    exact Rat.mul_pos
      (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos ha hb) hc) hxpos)
        hypos)
      hzpos
  have h8Dpos : 0 < 8 * D :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 8) hDpos
  have hcxz : c * x * z ≠ 0 :=
    Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hc hxpos) hzpos)
  have h2xyz : 2 * x * y * z ≠ 0 :=
    Rat.ne_of_gt
      (Rat.mul_pos
        (Rat.mul_pos
          (Rat.mul_pos (by native_decide : (0 : Rat) < 2) hxpos)
          hypos)
        hzpos)
  have h4cab : 4 * c * a * b ≠ 0 :=
    Rat.ne_of_gt
      (Rat.mul_pos
        (Rat.mul_pos (Rat.mul_pos (by native_decide : (0 : Rat) < 4) hc)
          ha)
        hb)
  have h8axy : 8 * a * x * y ≠ 0 :=
    Rat.ne_of_gt
      (Rat.mul_pos
        (Rat.mul_pos (Rat.mul_pos (by native_decide : (0 : Rat) < 8) ha)
          hxpos)
        hypos)
  have h8byz : 8 * b * y * z ≠ 0 :=
    Rat.ne_of_gt
      (Rat.mul_pos
        (Rat.mul_pos (Rat.mul_pos (by native_decide : (0 : Rat) < 8) hb)
          hypos)
        hzpos)
  apply rat_eq_of_mul_eq_mul_pos h8Dpos
  calc
    (1 / (c * x * z)) * (8 * D) = 8 * a * b * y := by
      dsimp [D]
      exact cancel_common
        (d := c * x * z) (t := 8 * a * b * y)
        (common := 8 * (a * b * c * x * y * z))
        hcxz (by grind [Rat.mul_assoc, Rat.mul_comm])
    _ = 4 * a * b * c + 2 * x * y * z + c * b * z + c * x * a :=
      abstract_gap_den_identity hx hz hy
    _ =
        (1 / (2 * x * y * z) + 1 / (4 * c * a * b) +
          1 / (8 * a * x * y) + 1 / (8 * b * y * z)) * (8 * D) := by
      dsimp [D]
      rw [Rat.add_mul, Rat.add_mul, Rat.add_mul]
      rw [cancel_common
          (d := 2 * x * y * z) (t := 4 * a * b * c)
          (common := 8 * (a * b * c * x * y * z))
          h2xyz (by grind [Rat.mul_assoc, Rat.mul_comm]),
        cancel_common
          (d := 4 * c * a * b) (t := 2 * x * y * z)
          (common := 8 * (a * b * c * x * y * z))
          h4cab (by grind [Rat.mul_assoc, Rat.mul_comm]),
        cancel_common
          (d := 8 * a * x * y) (t := c * b * z)
          (common := 8 * (a * b * c * x * y * z))
          h8axy (by grind [Rat.mul_assoc, Rat.mul_comm]),
        cancel_common
          (d := 8 * b * y * z) (t := c * x * a)
          (common := 8 * (a * b * c * x * y * z))
          h8byz (by grind [Rat.mul_assoc, Rat.mul_comm])]

private theorem local_gap_refine {p r : Rat}
    (hp0 : 0 <= p) (hpr : p <= r) :
    let q : Rat := (p + r) / 2
    areaGap p r =
      circleAreaIncrement p q r + circleAreaDecrement p q r +
        areaGap p q + areaGap q r := by
  intro q
  let a : Rat := 1 + p * q
  let b : Rat := 1 + q * r
  let c : Rat := 1 + p * r
  let x : Rat := 1 + p * p
  let y : Rat := 1 + q * q
  let z : Rat := 1 + r * r
  have hq0 : 0 <= q := by
    dsimp [q]
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind)
      (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2)))
  have hr0 : 0 <= r := by grind
  have ha : 0 < a := by
    dsimp [a]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hq0
  have hb : 0 < b := by
    dsimp [b]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hq0 hr0
  have hc : 0 < c := by
    dsimp [c]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0
  have hxpos : 0 < x := by
    dsimp [x]
    exact RationalCircle.Stage.one_add_square_pos p
  have hypos : 0 < y := by
    dsimp [y]
    exact RationalCircle.Stage.one_add_square_pos q
  have hzpos : 0 < z := by
    dsimp [z]
    exact RationalCircle.Stage.one_add_square_pos r
  have hxrel : x + c = 2 * a := by
    dsimp [x, c, a, q]
    rw [Rat.div_def]
    have h2 : (2 : Rat) ≠ 0 := by native_decide
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hzrel : z + c = 2 * b := by
    dsimp [z, c, b, q]
    rw [Rat.div_def]
    have h2 : (2 : Rat) ≠ 0 := by native_decide
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hyrel : a + b = 2 * y := by
    dsimp [a, b, y, q]
    rw [Rat.div_def]
    have h2 : (2 : Rat) ≠ 0 := by native_decide
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hrecip :=
    abstract_gap_recip_identity ha hb hc hxpos hypos hzpos hxrel hzrel hyrel
  rw [areaGap_eq_factor p r]
  rw [increment_mid_eq_factor p r]
  rw [decrement_mid_eq_factor p r]
  rw [areaGap_left_mid_eq_factor p r]
  rw [areaGap_right_mid_eq_factor p r]
  dsimp [q, a, b, c, x, y, z] at hrecip ⊢
  rw [hrecip]
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

private theorem midpoint_nonneg {p r : Rat}
    (hp0 : 0 <= p) (hr0 : 0 <= r) :
    0 <= (p + r) / 2 := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg (Rat.add_nonneg hp0 hr0)
    (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2)))

private theorem left_le_midpoint {p r : Rat} (hpr : p <= r) :
    p <= (p + r) / 2 := by
  apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
  · rw [Rat.div_def]
    have h2 : (2 : Rat) ≠ 0 := by native_decide
    calc
      p * 2 <= p + r := by grind
      _ = ((p + r) * (2 : Rat)⁻¹) * 2 := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · native_decide

private theorem midpoint_le_right {p r : Rat} (hpr : p <= r) :
    (p + r) / 2 <= r := by
  apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
  · rw [Rat.div_def]
    have h2 : (2 : Rat) ≠ 0 := by native_decide
    calc
      ((p + r) * (2 : Rat)⁻¹) * 2 = p + r := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= r * 2 := by grind
  · native_decide

private theorem increment_nonneg {p q r : Rat}
    (hpq : p <= q) (hqr : q <= r) :
    0 <= circleAreaIncrement p q r := by
  unfold circleAreaIncrement
  rw [Rat.div_def]
  have hpq' : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hqr' : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hrp' : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hnum : 0 <= 2 * (r - p) * (q - p) * (r - q) := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg
        (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hrp')
        hpq')
      hqr'
  have hden : 0 < (1 + p * p) * (1 + q * q) * (1 + r * r) := by
    exact Rat.mul_pos
      (Rat.mul_pos (RationalCircle.Stage.one_add_square_pos p)
        (RationalCircle.Stage.one_add_square_pos q))
      (RationalCircle.Stage.one_add_square_pos r)
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))

private theorem decrement_nonneg {p q r : Rat}
    (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    0 <= circleAreaDecrement p q r := by
  unfold circleAreaDecrement
  rw [Rat.div_def]
  have hq0 : 0 <= q := by grind
  have hr0 : 0 <= r := by grind
  have hpq' : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hqr' : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hrp' : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hnum : 0 <= (r - p) * (q - p) * (r - q) := by
    exact Rat.mul_nonneg (Rat.mul_nonneg hrp' hpq') hqr'
  have hden : 0 < (1 + p * r) * (1 + p * q) * (1 + q * r) := by
    exact Rat.mul_pos
      (Rat.mul_pos
        (RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0)
        (RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hq0))
      (RationalCircle.Stage.one_add_mul_pos_of_nonneg hq0 hr0)
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))

private theorem refineAux_wellFormed
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : IntervalsWellFormed intervals) :
    IntervalsWellFormed
      (AreaBoundsLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaBoundsLoopState.refineAux, IntervalsWellFormed]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hq0 : 0 <= q := by
        dsimp [q]
        exact midpoint_nonneg hp0 (by grind)
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have hq1 : q <= 1 := Rat.le_trans hqr hr1
      have htail :=
        ih (lo + circleAreaIncrement p q r)
          (hi - circleAreaDecrement p q r) hrest
      simp [AreaBoundsLoopState.refineAux, IntervalsWellFormed, q,
        hp0, hpq, hqr, hr1, hq0, hq1, htail]

theorem refineAreaBounds_wellFormed (state : AreaBoundsLoopState)
    (hwf : IntervalsWellFormed state.intervals) :
    IntervalsWellFormed (refineAreaBounds state).intervals := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_wellFormed lo hi intervals hwf

private theorem refineAux_endpoint_refines
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : IntervalsWellFormed intervals) :
    lo <= (AreaBoundsLoopState.refineAux lo hi intervals).lo /\
      (AreaBoundsLoopState.refineAux lo hi intervals).hi <= hi := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaBoundsLoopState.refineAux]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, _hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have hinc : 0 <= circleAreaIncrement p q r :=
        increment_nonneg hpq hqr
      have hdec : 0 <= circleAreaDecrement p q r :=
        decrement_nonneg hp0 hpq hqr
      have htail :=
        ih (lo + circleAreaIncrement p q r)
          (hi - circleAreaDecrement p q r) hrest
      simp [AreaBoundsLoopState.refineAux]
      exact ⟨Rat.le_trans (by grind) htail.1,
        Rat.le_trans htail.2 (by grind)⟩

theorem refineAreaBounds_lo_mono (state : AreaBoundsLoopState)
    (hwf : IntervalsWellFormed state.intervals) :
    state.lo <= (refineAreaBounds state).lo := by
  cases state with
  | mk lo hi intervals =>
      exact (refineAux_endpoint_refines lo hi intervals hwf).1

theorem refineAreaBounds_hi_anti (state : AreaBoundsLoopState)
    (hwf : IntervalsWellFormed state.intervals) :
    (refineAreaBounds state).hi <= state.hi := by
  cases state with
  | mk lo hi intervals =>
      exact (refineAux_endpoint_refines lo hi intervals hwf).2

private theorem refineAux_gapSum_extra
    (extra lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : IntervalsWellFormed intervals)
    (hgap : hi - lo = extra + areaGapSum intervals) :
    let next := AreaBoundsLoopState.refineAux lo hi intervals
    next.hi - next.lo = extra + areaGapSum next.intervals := by
  induction intervals generalizing extra lo hi with
  | nil =>
      intro next
      simp [areaGapSum] at hgap ⊢
      exact hgap
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, _hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hlocal := local_gap_refine hp0 hpr
      dsimp [q] at hlocal
      let extra' : Rat := extra + areaGap p q + areaGap q r
      have hstart :
          (hi - circleAreaDecrement p q r) -
              (lo + circleAreaIncrement p q r) =
            extra' + areaGapSum rest := by
        dsimp [extra']
        calc
          (hi - circleAreaDecrement p q r) -
              (lo + circleAreaIncrement p q r)
              = hi - lo -
                  (circleAreaIncrement p q r +
                    circleAreaDecrement p q r) := by
                grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
          _ = extra + areaGapSum ((p, r) :: rest) -
                  (circleAreaIncrement p q r +
                    circleAreaDecrement p q r) := by
                rw [hgap]
          _ = extra' + areaGapSum rest := by
                simp [areaGapSum]
                rw [hlocal]
                grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      have htail :=
        ih extra' (lo + circleAreaIncrement p q r)
          (hi - circleAreaDecrement p q r) hrest hstart
      simp [AreaBoundsLoopState.refineAux, areaGapSum]
      simpa [extra', areaGapSum, Rat.add_assoc, Rat.add_comm] using htail

theorem refineAreaBounds_gapSum (state : AreaBoundsLoopState)
    (hwf : IntervalsWellFormed state.intervals)
    (hgap : state.hi - state.lo = areaGapSum state.intervals) :
    let next := refineAreaBounds state
    next.hi - next.lo = areaGapSum next.intervals := by
  cases state with
  | mk lo hi intervals =>
      have hgap' : hi - lo = 0 + areaGapSum intervals := by
        grind
      have h := refineAux_gapSum_extra 0 lo hi intervals hwf hgap'
      have h' :
          (AreaBoundsLoopState.refineAux lo hi intervals).hi -
              (AreaBoundsLoopState.refineAux lo hi intervals).lo =
            areaGapSum
              (AreaBoundsLoopState.refineAux lo hi intervals).intervals := by
        grind
      simpa [refineAreaBounds] using h'

private theorem cube_midpoint_split (p r : Rat) :
    let q : Rat := (p + r) / 2
    (q - p) * (q - p) * (q - p) +
        (r - q) * (r - q) * (r - q) =
      ((r - p) * (r - p) * (r - p)) / 4 := by
  intro q
  dsimp [q]
  rw [midpoint_left_sub, midpoint_right_sub]
  have h2 : (2 : Rat) ≠ 0 := by native_decide
  have h4 : (4 : Rat) ≠ 0 := by native_decide
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem refineAux_cubeSum
    (lo hi : Rat) (intervals : List (Rat × Rat)) :
    areaCubeSum
        (AreaBoundsLoopState.refineAux lo hi intervals).intervals =
      areaCubeSum intervals / 4 := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaBoundsLoopState.refineAux, areaCubeSum, Rat.div_def]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      let q : Rat := (p + r) / 2
      have hsplit := cube_midpoint_split p r
      dsimp [q] at hsplit
      have htail :=
        ih (lo + circleAreaIncrement p q r)
          (hi - circleAreaDecrement p q r)
      simp [AreaBoundsLoopState.refineAux, areaCubeSum]
      rw [htail]
      have h4 : (4 : Rat) ≠ 0 := by native_decide
      calc
        ((p + r) / 2 - p) * ((p + r) / 2 - p) *
              ((p + r) / 2 - p) +
            ((r - (p + r) / 2) * (r - (p + r) / 2) *
                (r - (p + r) / 2) + areaCubeSum rest / 4)
            =
          (((p + r) / 2 - p) * ((p + r) / 2 - p) *
              ((p + r) / 2 - p) +
            (r - (p + r) / 2) * (r - (p + r) / 2) *
                (r - (p + r) / 2)) + areaCubeSum rest / 4 := by
            grind [Rat.add_assoc, Rat.add_comm]
        _ = (r - p) * (r - p) * (r - p) / 4 +
              areaCubeSum rest / 4 := by
            rw [hsplit]
        _ = ((r - p) * (r - p) * (r - p) +
              areaCubeSum rest) / 4 := by
            rw [Rat.div_def, Rat.div_def, Rat.div_def]
            grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
              Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem refineAreaBounds_cubeSum (state : AreaBoundsLoopState) :
    areaCubeSum (refineAreaBounds state).intervals =
      areaCubeSum state.intervals / 4 := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_cubeSum lo hi intervals

private theorem areaGap_nonneg {p r : Rat}
    (hp0 : 0 <= p) (hpr : p <= r) :
    0 <= areaGap p r := by
  rw [areaGap_eq_factor]
  have hr0 : 0 <= r := by grind
  have hdiff : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hcube : 0 <= (r - p) * (r - p) * (r - p) :=
    Rat.mul_nonneg (Rat.mul_nonneg hdiff hdiff) hdiff
  have hden : 0 < (1 + p * r) * (1 + p * p) * (1 + r * r) := by
    exact Rat.mul_pos
      (Rat.mul_pos
        (RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0)
        (RationalCircle.Stage.one_add_square_pos p))
      (RationalCircle.Stage.one_add_square_pos r)
  have hinv : 0 <= 1 / ((1 + p * r) * (1 + p * p) * (1 + r * r)) := by
    rw [Rat.div_def]
    have hpos := (Rat.inv_pos).2 hden
    grind
  exact Rat.mul_nonneg hcube hinv

private theorem one_div_le_one_of_one_le {d : Rat}
    (hd : 1 <= d) :
    1 / d <= 1 := by
  have hdpos : 0 < d := by grind
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      (1 / d) * d = 1 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= d := hd
      _ = 1 * d := by grind
  · exact hdpos

private theorem areaGap_le_cube {p r : Rat}
    (hp0 : 0 <= p) (hpr : p <= r) :
    areaGap p r <= (r - p) * (r - p) * (r - p) := by
  rw [areaGap_eq_factor]
  have hr0 : 0 <= r := by grind
  have hprmul : 0 <= p * r := Rat.mul_nonneg hp0 hr0
  have hpp : 0 <= p * p := RationalCircle.Stage.ratSquare_nonneg p
  have hrr : 0 <= r * r := RationalCircle.Stage.ratSquare_nonneg r
  let A : Rat := 1 + p * r
  let B : Rat := 1 + p * p
  let C : Rat := 1 + r * r
  have hA1 : 1 <= A := by dsimp [A]; grind
  have hB1 : 1 <= B := by dsimp [B]; grind
  have hC1 : 1 <= C := by dsimp [C]; grind
  have hB0 : 0 <= B := by grind
  have hC0 : 0 <= C := by grind
  have hAB : 1 <= A * B := by
    calc
      1 = 1 * 1 := by grind
      _ <= A * 1 := Rat.mul_le_mul_of_nonneg_right hA1 (by native_decide)
      _ <= A * B := Rat.mul_le_mul_of_nonneg_left hB1 (by grind)
  have hABC : 1 <= A * B * C := by
    calc
      1 = 1 * 1 := by grind
      _ <= (A * B) * 1 :=
        Rat.mul_le_mul_of_nonneg_right hAB (by native_decide)
      _ <= (A * B) * C :=
        Rat.mul_le_mul_of_nonneg_left hC1 (by grind)
  have hinv : 1 / (A * B * C) <= 1 :=
    one_div_le_one_of_one_le hABC
  have hdiff : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hcube : 0 <= (r - p) * (r - p) * (r - p) :=
    Rat.mul_nonneg (Rat.mul_nonneg hdiff hdiff) hdiff
  dsimp [A, B, C] at hinv
  calc
    (r - p) * (r - p) * (r - p) *
        (1 / ((1 + p * r) * (1 + p * p) * (1 + r * r)))
        <= (r - p) * (r - p) * (r - p) * 1 :=
          Rat.mul_le_mul_of_nonneg_left hinv hcube
    _ = (r - p) * (r - p) * (r - p) := by
          rw [Rat.mul_one]

private theorem areaGapSum_bounds
    (intervals : List (Rat × Rat))
    (hwf : IntervalsWellFormed intervals) :
    0 <= areaGapSum intervals /\
      areaGapSum intervals <= areaCubeSum intervals := by
  induction intervals with
  | nil =>
      simp [areaGapSum, areaCubeSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, _hr1, hrest⟩
      have hhead_nonneg := areaGap_nonneg hp0 hpr
      have hhead_le := areaGap_le_cube hp0 hpr
      have htail := ih hrest
      simp [areaGapSum, areaCubeSum]
      exact ⟨Rat.add_nonneg hhead_nonneg htail.1,
        rat_add_le_add hhead_le htail.2⟩

theorem areaGapSum_nonneg
    (intervals : List (Rat × Rat))
    (hwf : IntervalsWellFormed intervals) :
    0 <= areaGapSum intervals :=
  (areaGapSum_bounds intervals hwf).1

theorem areaGapSum_le_cubeSum
    (intervals : List (Rat × Rat))
    (hwf : IntervalsWellFormed intervals) :
    areaGapSum intervals <= areaCubeSum intervals :=
  (areaGapSum_bounds intervals hwf).2

end AreaLoopValidity

def AreaNested : Prop :=
  forall n m, n <= m ->
    (piCircleArea.compute n).lo <= (piCircleArea.compute m).lo /\
    (piCircleArea.compute m).lo <= (piCircleArea.compute m).hi /\
    (piCircleArea.compute m).hi <= (piCircleArea.compute n).hi

def AreaOrdered : Prop :=
  forall n, 0 <= (piCircleArea.compute n).width

def WidthBoundedByNatOverSucc
    (compute : Nat -> QInterval) (C : Nat) : Prop :=
  forall n,
    (compute n).width <= (C : Rat) / (((n + 1 : Nat) : Rat))

theorem widthsShrink_of_natOverSuccBound
    {compute : Nat -> QInterval} {C : Nat}
    (hbound : WidthBoundedByNatOverSucc compute C) :
    RealRaw.WidthsShrinkToZero compute := by
  intro eps
  refine ⟨C * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (C : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (C : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        C * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          have hcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          have hcancel : B * B⁻¹ = 1 := Rat.mul_inv_cancel B hBne
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hABpos
  exact Rat.le_trans (hbound n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

def AreaWidthsShrink : Prop :=
  RealRaw.WidthsShrinkToZero piCircleArea.compute

def AreaWidthLinearBound (C : Nat) : Prop :=
  WidthBoundedByNatOverSucc piCircleArea.compute C

theorem areaWidthsShrink_of_linearBound
    {C : Nat} (hbound : AreaWidthLinearBound C) :
    AreaWidthsShrink :=
  widthsShrink_of_natOverSuccBound hbound

def CircumferenceNested : Prop :=
  forall n m, n <= m ->
    (piCircumference.compute n).lo <= (piCircumference.compute m).lo /\
    (piCircumference.compute m).lo <= (piCircumference.compute m).hi /\
    (piCircumference.compute m).hi <= (piCircumference.compute n).hi

def CircumferenceWidthsShrink : Prop :=
  RealRaw.WidthsShrinkToZero piCircumference.compute

def CircumferenceWidthLinearBound (C : Nat) : Prop :=
  WidthBoundedByNatOverSucc piCircumference.compute C

def CircumferenceQuarterGapLinearBound (C : Nat) : Prop :=
  forall n,
    2 * circumferenceQuarterGap (piStage n) <=
      (C : Rat) / (((n + 1 : Nat) : Rat))

theorem circumferenceWidthLinearBound_of_quarterGapLinearBound
    {C : Nat} (hgap : CircumferenceQuarterGapLinearBound C) :
    CircumferenceWidthLinearBound C := by
  intro n
  rw [piCircumference_compute_width_eq]
  exact hgap n

def CircumferenceFanGapPathBudgetLinearBound (C : Nat) : Prop :=
  forall n,
    2 * (circumferenceFanGap (piStage n) +
      circumferencePathWidthBudget (piStage n)) <=
      (C : Rat) / (((n + 1 : Nat) : Rat))

def CircumferenceFanGapLinearBound (C : Nat) : Prop :=
  forall n,
    2 * circumferenceFanGap (piStage n) <=
      (C : Rat) / (((n + 1 : Nat) : Rat))

def CircumferencePathWidthBudgetLinearBound (C : Nat) : Prop :=
  forall n,
    2 * circumferencePathWidthBudget (piStage n) <=
      (C : Rat) / (((n + 1 : Nat) : Rat))

def CircumferencePathSegmentUniformLinearBound (C : Nat) : Prop :=
  forall n,
    let stage := piStage n
    let B : Rat :=
      (C : Rat) / (6 * (stage : Rat) * (((n + 1 : Nat) : Rat)))
    InnerBoundarySegmentBudgetLe stage B /\
      OuterBoundarySegmentBudgetLe stage B

def CircumferenceAdjacentSegmentUniformLinearBound (C : Nat) : Prop :=
  forall n,
    let stage := piStage n
    let B : Rat :=
      (C : Rat) / (6 * (stage : Rat) * (((n + 1 : Nat) : Rat)))
    InnerAdjacentSegmentBudgetLe stage B /\
      OuterAdjacentSegmentBudgetLe stage B

def CircumferenceFormulaSegmentUniformLinearBound (C : Nat) : Prop :=
  forall n,
    let stage := piStage n
    let B : Rat :=
      (C : Rat) / (6 * (stage : Rat) * (((n + 1 : Nat) : Rat)))
    InnerAdjacentChordFormulaBudgetLe stage B /\
      OuterAdjacentTangentFormulaBudgetLe stage B

def CircumferenceFiniteFormulaSegmentUniformLinearBound (C : Nat) : Prop :=
  forall n,
    let stage := piStage n
    let B : Rat :=
      (C : Rat) / (6 * (stage : Rat) * (((n + 1 : Nat) : Rat)))
    InnerAdjacentChordFormulaBudgetLeUpTo stage B /\
      OuterAdjacentTangentFormulaBudgetLeUpTo stage B

theorem adjacentSegmentUniformLinearBound_of_formulaSegmentUniformLinearBound
    {C : Nat}
    (hseg : CircumferenceFormulaSegmentUniformLinearBound C) :
    CircumferenceAdjacentSegmentUniformLinearBound C := by
  intro n
  have h := hseg n
  dsimp at h ⊢
  exact ⟨innerAdjacentSegmentBudgetLe_of_chordFormulaBudget h.1,
    outerAdjacentSegmentBudgetLe_of_tangentFormulaBudget (piStage_pos n) h.2⟩

theorem pathSegmentUniformLinearBound_of_adjacentSegmentUniformLinearBound
    {C : Nat}
    (hseg : CircumferenceAdjacentSegmentUniformLinearBound C) :
    CircumferencePathSegmentUniformLinearBound C := by
  intro n
  have h := hseg n
  dsimp at h ⊢
  exact ⟨innerBoundarySegmentBudgetLe_of_adjacent h.1,
    outerBoundarySegmentBudgetLe_of_adjacent h.2⟩

theorem pathSegmentUniformLinearBound_of_formulaSegmentUniformLinearBound
    {C : Nat}
    (hseg : CircumferenceFormulaSegmentUniformLinearBound C) :
    CircumferencePathSegmentUniformLinearBound C :=
  pathSegmentUniformLinearBound_of_adjacentSegmentUniformLinearBound
    (adjacentSegmentUniformLinearBound_of_formulaSegmentUniformLinearBound hseg)

theorem finiteFormulaSegmentUniformLinearBound_of_formulaSegmentUniformLinearBound
    {C : Nat}
    (hseg : CircumferenceFormulaSegmentUniformLinearBound C) :
    CircumferenceFiniteFormulaSegmentUniformLinearBound C := by
  intro n
  have h := hseg n
  dsimp at h ⊢
  exact ⟨fun k _ => h.1 k, fun k _ => h.2 k⟩

theorem pathSegmentUniformLinearBound_of_finiteFormulaSegmentUniformLinearBound
    {C : Nat}
    (hseg : CircumferenceFiniteFormulaSegmentUniformLinearBound C) :
    CircumferencePathSegmentUniformLinearBound C := by
  intro n
  have h := hseg n
  dsimp at h ⊢
  exact ⟨innerBoundarySegmentBudgetLe_of_chordFormulaBudgetUpTo h.1,
    outerBoundarySegmentBudgetLe_of_tangentFormulaBudgetUpTo (piStage_pos n) h.2⟩

theorem circumferencePathWidthBudgetLinearBound_of_segmentUniformLinearBound
    {C : Nat} (hseg : CircumferencePathSegmentUniformLinearBound C) :
    CircumferencePathWidthBudgetLinearBound C := by
  intro n
  let stage := piStage n
  let N : Rat := ((n + 1 : Nat) : Rat)
  let B : Rat := (C : Rat) / (6 * (stage : Rat) * N)
  have hstage_pos : 0 < (stage : Rat) := by
    dsimp [stage]
    exact (Rat.natCast_pos).2 (piStage_pos n)
  have hN_pos : 0 < N := by
    dsimp [N]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hden_ne : 6 * (stage : Rat) * N ≠ 0 := by
    exact Rat.ne_of_gt (Rat.mul_pos
      (Rat.mul_pos (by native_decide : (0 : Rat) < 6) hstage_pos)
      hN_pos)
  have hdata := hseg n
  dsimp [stage, B] at hdata
  have hbudget :=
    circumferencePathWidthBudget_le_three_stage_mul
      (piStage n)
      ((C : Rat) / (6 * ((piStage n) : Rat) * N))
      hdata.1 hdata.2
  calc
    2 * circumferencePathWidthBudget (piStage n) <=
        2 * ((3 * ((piStage n) : Rat)) *
          ((C : Rat) / (6 * ((piStage n) : Rat) * N))) := by
      exact Rat.mul_le_mul_of_nonneg_left hbudget
        (by native_decide : (0 : Rat) <= 2)
    _ = (C : Rat) / N := by
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem circumferencePathWidthBudgetLinearBound_of_formulaSegmentUniformLinearBound
    {C : Nat}
    (hseg : CircumferenceFormulaSegmentUniformLinearBound C) :
    CircumferencePathWidthBudgetLinearBound C :=
  circumferencePathWidthBudgetLinearBound_of_segmentUniformLinearBound
    (pathSegmentUniformLinearBound_of_formulaSegmentUniformLinearBound hseg)

theorem circumferencePathWidthBudgetLinearBound_of_finiteFormulaSegmentUniformLinearBound
    {C : Nat}
    (hseg : CircumferenceFiniteFormulaSegmentUniformLinearBound C) :
    CircumferencePathWidthBudgetLinearBound C :=
  circumferencePathWidthBudgetLinearBound_of_segmentUniformLinearBound
    (pathSegmentUniformLinearBound_of_finiteFormulaSegmentUniformLinearBound hseg)

theorem circumferenceFiniteFormulaSegmentUniformLinearBound_six :
    CircumferenceFiniteFormulaSegmentUniformLinearBound 6 := by
  intro n
  let stage := piStage n
  let B : Rat :=
    (6 : Rat) / (6 * (stage : Rat) * (((n + 1 : Nat) : Rat)))
  have hstage_pos : 0 < stage := piStage_pos n
  have hbudget :
      2 / (((2 ^ (stage + 9) : Nat) : Rat)) <= B := by
    dsimp [stage, B]
    exact two_div_two_pow_stage_add_nine_le_budget n
  dsimp [stage, B]
  constructor
  · intro k _hk
    exact formulaBudgetLeAt_of_sqrtUpperBound_le_two
      (Nat.ne_of_gt hstage_pos)
      (sqrtUpperBound_le_two_of_le_two
        (adjacentChordNormSqFormula_le_two stage hstage_pos k))
      hbudget
  · intro k _hk
    constructor
    · exact formulaBudgetLeAt_of_sqrtUpperBound_le_two
        (Nat.ne_of_gt hstage_pos)
        (sqrtUpperBound_le_two_of_le_two
          (entryTangentNormSqFormula_le_two stage hstage_pos k))
        hbudget
    · exact formulaBudgetLeAt_of_sqrtUpperBound_le_two
        (Nat.ne_of_gt hstage_pos)
        (sqrtUpperBound_le_two_of_le_two
          (exitTangentNormSqFormula_le_two stage hstage_pos k))
        hbudget

theorem circumferencePathWidthBudgetLinearBound_six :
    CircumferencePathWidthBudgetLinearBound 6 :=
  circumferencePathWidthBudgetLinearBound_of_finiteFormulaSegmentUniformLinearBound
    circumferenceFiniteFormulaSegmentUniformLinearBound_six

private theorem outerInnerEdgeCrosses_gap_le
    (stage : Nat) (hstage : 0 < stage) :
    forall count k,
      Fan.perimeter
          (Fan.edgeCrossesFrom
            (circleSamplePoint stage k)
            (outerBoundaryFrom stage k count)) -
        Fan.perimeter
          (Fan.edgeCrossesFrom
            (circleSamplePoint stage k)
            (innerBoundaryFrom stage (k + 1) count)) <=
        (count : Rat) *
          (2 * (1 / (stage : Rat)) *
            (1 / (stage : Rat)) * (1 / (stage : Rat)))
  | 0, k => by
      simp [innerBoundaryFrom, outerBoundaryFrom,
        piCircleAreaPolygon.innerBoundaryFrom,
        piCircleAreaPolygon.outerBoundaryFrom,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
      grind
  | count + 1, k => by
      let B : Rat :=
        2 * (1 / (stage : Rat)) *
          (1 / (stage : Rat)) * (1 / (stage : Rat))
      have hhead := adjacentFanGap_le_two_step_cube stage hstage k
      have htail :=
        outerInnerEdgeCrosses_gap_le stage hstage count (k + 1)
      have htail' :
          Fan.sumRat
              (Fan.edgeCrossesFrom
                (circleSamplePoint stage (k + 1))
                (outerBoundaryFrom stage (k + 1) count)) -
            Fan.sumRat
              (Fan.edgeCrossesFrom
                (circleSamplePoint stage (k + 1))
                (innerBoundaryFrom stage (k + 2) count)) <=
            (count : Rat) * B := by
        dsimp [B]
        simpa [Fan.perimeter] using htail
      have hsplit :
          pointCross (circleSamplePoint stage k)
              (outerTangentPoint stage k) +
              (pointCross (outerTangentPoint stage k)
                (circleSamplePoint stage (k + 1)) +
                Fan.sumRat
                  (Fan.edgeCrossesFrom
                    (circleSamplePoint stage (k + 1))
                    (outerBoundaryFrom stage (k + 1) count))) -
            (pointCross (circleSamplePoint stage k)
                (circleSamplePoint stage (k + 1)) +
              Fan.sumRat
                (Fan.edgeCrossesFrom
                  (circleSamplePoint stage (k + 1))
                  (innerBoundaryFrom stage (k + 2) count))) =
          (2 * adjacentTangentCrossFormula stage k -
              pointCross (circleSamplePoint stage k)
                (circleSamplePoint stage (k + 1))) +
            (Fan.sumRat
                (Fan.edgeCrossesFrom
                  (circleSamplePoint stage (k + 1))
                  (outerBoundaryFrom stage (k + 1) count)) -
              Fan.sumRat
                (Fan.edgeCrossesFrom
                  (circleSamplePoint stage (k + 1))
                  (innerBoundaryFrom stage (k + 2) count))) := by
        rw [entryTangentCross_eq_formula stage hstage k,
          exitTangentCross_eq_formula stage hstage k]
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]
      simp [innerBoundaryFrom, outerBoundaryFrom,
        piCircleAreaPolygon.innerBoundaryFrom,
        piCircleAreaPolygon.outerBoundaryFrom,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
      change
        pointCross (circleSamplePoint stage k)
            (outerTangentPoint stage k) +
            (pointCross (outerTangentPoint stage k)
              (circleSamplePoint stage (k + 1)) +
              Fan.sumRat
                (Fan.edgeCrossesFrom
                  (circleSamplePoint stage (k + 1))
                  (outerBoundaryFrom stage (k + 1) count))) -
          (pointCross (circleSamplePoint stage k)
              (circleSamplePoint stage (k + 1)) +
            Fan.sumRat
              (Fan.edgeCrossesFrom
                (circleSamplePoint stage (k + 1))
                (innerBoundaryFrom stage (k + 2) count))) <=
        ((count : Rat) + 1) * B
      rw [hsplit]
      calc
        (2 * adjacentTangentCrossFormula stage k -
              pointCross (circleSamplePoint stage k)
                (circleSamplePoint stage (k + 1))) +
            (Fan.sumRat
                (Fan.edgeCrossesFrom
                  (circleSamplePoint stage (k + 1))
                  (outerBoundaryFrom stage (k + 1) count)) -
              Fan.sumRat
                (Fan.edgeCrossesFrom
                  (circleSamplePoint stage (k + 1))
                  (innerBoundaryFrom stage (k + 2) count)))
            <= B + (count : Rat) * B := by
              have hhead' :
                  2 * adjacentTangentCrossFormula stage k -
                      pointCross (circleSamplePoint stage k)
                        (circleSamplePoint stage (k + 1)) <= B := by
                simpa [B] using hhead
              exact Fan.rat_add_le_add hhead' htail'
        _ = ((count : Rat) + 1) * B := by
              grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc,
                Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem circumferenceFanGap_stage_le_two_div_stage
    (stage : Nat) (hstage : 0 < stage) :
    circumferenceFanGap stage <= 2 / (stage : Rat) := by
  let d : Rat := 1 / (stage : Rat)
  let B : Rat := 2 * d * d * d
  have hgap :=
    outerInnerEdgeCrosses_gap_le stage hstage stage 0
  have hfan :
      circumferenceFanGap stage <= (stage : Rat) * B := by
    have hgap' :
        0 + Fan.sumRat
            (Fan.edgeCrossesFrom (circleSamplePoint stage 0)
              (outerBoundaryFrom stage 0 stage)) -
          (0 + Fan.sumRat
            (Fan.edgeCrossesFrom (circleSamplePoint stage 0)
              (innerBoundaryFrom stage 1 stage))) <=
          (stage : Rat) *
            (2 * (1 / (stage : Rat)) *
              (1 / (stage : Rat)) * (1 / (stage : Rat))) := by
      calc
        0 + Fan.sumRat
            (Fan.edgeCrossesFrom (circleSamplePoint stage 0)
              (outerBoundaryFrom stage 0 stage)) -
          (0 + Fan.sumRat
            (Fan.edgeCrossesFrom (circleSamplePoint stage 0)
              (innerBoundaryFrom stage 1 stage))) =
            Fan.perimeter
              (Fan.edgeCrossesFrom (circleSamplePoint stage 0)
                (outerBoundaryFrom stage 0 stage)) -
            Fan.perimeter
              (Fan.edgeCrossesFrom (circleSamplePoint stage 0)
                (innerBoundaryFrom stage 1 stage)) := by
              simp [Fan.perimeter]
              grind [Rat.sub_eq_add_neg]
        _ <=
          (stage : Rat) *
            (2 * (1 / (stage : Rat)) *
              (1 / (stage : Rat)) * (1 / (stage : Rat))) := hgap
    dsimp [B, d]
    simpa [circumferenceFanGap, innerFanWidths, outerFanWidths,
      innerBoundary, outerBoundary, Fan.sectorFanWidths, Fan.perimeter,
      innerBoundaryFrom, outerBoundaryFrom,
      piCircleAreaPolygon.innerBoundaryFrom,
      piCircleAreaPolygon.outerBoundaryFrom, Fan.edgeCrossesFrom,
      Fan.sumRat, pointCross_origin_left] using hgap'
  have hdpos : 0 < d := by
    dsimp [d]
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hstage)
  have hd0 : 0 <= d := Rat.le_of_lt hdpos
  have hdle1 : d <= 1 := by
    dsimp [d]
    have hone : (1 / (1 : Rat)) = 1 := by native_decide
    simpa [hone] using
      (FTC.one_div_nat_antitone (n := 1) (m := stage)
        (by omega) hstage (by omega : 1 <= stage))
  have hBbound : (stage : Rat) * B <= 2 * d := by
    have hstage_ne : (stage : Rat) ≠ 0 :=
      Rat.ne_of_gt ((Rat.natCast_pos).2 hstage)
    have hd_sq_le_d : d * d <= d := by
      calc
        d * d <= 1 * d := Rat.mul_le_mul_of_nonneg_right hdle1 hd0
        _ = d := by grind
    calc
      (stage : Rat) * B = 2 * d * d := by
        dsimp [B, d]
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= 2 * d := by
        simpa [Rat.mul_assoc] using
          Rat.mul_le_mul_of_nonneg_left hd_sq_le_d
            (by native_decide : (0 : Rat) <= 2)
      _ = 2 * d := rfl
  calc
    circumferenceFanGap stage <= (stage : Rat) * B := hfan
    _ <= 2 * d := hBbound
    _ = 2 / (stage : Rat) := by
      dsimp [d]
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem circumferenceFanGapLinearBound_four :
    CircumferenceFanGapLinearBound 4 := by
  intro n
  have hstage := circumferenceFanGap_stage_le_two_div_stage
    (piStage n) (piStage_pos n)
  have hscaled :
      2 * circumferenceFanGap (piStage n) <=
        2 * (2 / ((piStage n : Nat) : Rat)) :=
    Rat.mul_le_mul_of_nonneg_left hstage
      (by native_decide : (0 : Rat) <= 2)
  have hsucc : n + 1 <= piStage n := by
    simpa [piStage] using succ_le_two_pow_local n
  have hone :
      1 / (((piStage n : Nat) : Rat)) <=
        1 / (((n + 1 : Nat) : Rat)) :=
    FTC.one_div_nat_antitone
      (Nat.succ_pos n) (piStage_pos n) hsucc
  have hfour :
      4 / (((piStage n : Nat) : Rat)) <=
        4 / (((n + 1 : Nat) : Rat)) := by
    have hmul := Rat.mul_le_mul_of_nonneg_left hone
      (by native_decide : (0 : Rat) <= 4)
    simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using hmul
  calc
    2 * circumferenceFanGap (piStage n) <=
        2 * (2 / ((piStage n : Nat) : Rat)) := hscaled
    _ = 4 / (((piStage n : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= 4 / (((n + 1 : Nat) : Rat)) := hfour

theorem fanGapPathBudgetLinearBound_of_parts
    {Cfan Cpath : Nat}
    (hfan : CircumferenceFanGapLinearBound Cfan)
    (hpath : CircumferencePathWidthBudgetLinearBound Cpath) :
    CircumferenceFanGapPathBudgetLinearBound (Cfan + Cpath) := by
  intro n
  have hf := hfan n
  have hp := hpath n
  calc
    2 * (circumferenceFanGap (piStage n) +
        circumferencePathWidthBudget (piStage n)) =
      2 * circumferenceFanGap (piStage n) +
        2 * circumferencePathWidthBudget (piStage n) := by
        grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]
    _ <=
      (Cfan : Rat) / (((n + 1 : Nat) : Rat)) +
        (Cpath : Rat) / (((n + 1 : Nat) : Rat)) := by
        grind
    _ =
      ((Cfan + Cpath : Nat) : Rat) / (((n + 1 : Nat) : Rat)) := by
        rw [Rat.div_def, Rat.div_def, Rat.div_def]
        grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]

theorem circumferenceQuarterGapLinearBound_of_fanGapPathBudgetLinearBound
    {C : Nat} (hbound : CircumferenceFanGapPathBudgetLinearBound C) :
    CircumferenceQuarterGapLinearBound C := by
  intro n
  have hgap :=
    circumferenceQuarterGap_le_fanGap_add_pathWidthBudget
      (piStage n) (piStage_pos n)
  have hscaled :
      2 * circumferenceQuarterGap (piStage n) <=
        2 * (circumferenceFanGap (piStage n) +
          circumferencePathWidthBudget (piStage n)) :=
    Rat.mul_le_mul_of_nonneg_left hgap
      (by native_decide : (0 : Rat) <= 2)
  exact Rat.le_trans hscaled (hbound n)

theorem circumferenceWidthLinearBound_of_fanGapPathBudgetLinearBound
    {C : Nat} (hbound : CircumferenceFanGapPathBudgetLinearBound C) :
    CircumferenceWidthLinearBound C :=
  circumferenceWidthLinearBound_of_quarterGapLinearBound
    (circumferenceQuarterGapLinearBound_of_fanGapPathBudgetLinearBound hbound)

theorem circumferenceWidthsShrink_of_linearBound
    {C : Nat} (hbound : CircumferenceWidthLinearBound C) :
    CircumferenceWidthsShrink :=
  widthsShrink_of_natOverSuccBound hbound

theorem circumferenceFanGapPathBudgetLinearBound_ten :
    CircumferenceFanGapPathBudgetLinearBound 10 := by
  simpa using
    fanGapPathBudgetLinearBound_of_parts
      circumferenceFanGapLinearBound_four
      circumferencePathWidthBudgetLinearBound_six

theorem circumferenceWidthLinearBound_ten :
    CircumferenceWidthLinearBound 10 :=
  circumferenceWidthLinearBound_of_fanGapPathBudgetLinearBound
    circumferenceFanGapPathBudgetLinearBound_ten

theorem circumferenceWidthsShrink :
    CircumferenceWidthsShrink :=
  circumferenceWidthsShrink_of_linearBound circumferenceWidthLinearBound_ten

def EndpointStepRefines (compute : Nat -> QInterval) : Prop :=
  forall n,
    (compute n).lo <= (compute (n + 1)).lo /\
    (compute (n + 1)).hi <= (compute n).hi

def EndpointMonotone (compute : Nat -> QInterval) : Prop :=
  forall n m, n <= m ->
    (compute n).lo <= (compute m).lo /\
    (compute m).hi <= (compute n).hi

theorem endpointMonotone_of_stepRefines
    {compute : Nat -> QInterval}
    (hstep : EndpointStepRefines compute) :
    EndpointMonotone compute := by
  intro n m hnm
  induction hnm with
  | refl =>
      constructor <;> exact Rat.le_refl
  | step hnm ih =>
      rename_i k
      have hnext := hstep k
      constructor
      · exact Rat.le_trans ih.1 hnext.1
      · exact Rat.le_trans hnext.2 ih.2

theorem piCircleArea_equiv_piCircleAreaPolygon_of_polygonAgreement
    (hagree : PiCircleAreaPolygonAgreement) :
    piCircleArea.Equiv piCircleAreaPolygon := by
  intro n
  apply (RealRaw.compareAt_overlap_iff piCircleArea piCircleAreaPolygon n n).2
  rw [hagree n]
  have hordered := piCircleAreaPolygon_ordered n
  unfold QInterval.width at hordered
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem piCircleArea_equiv_piCircleAreaPolygon :
    piCircleArea.Equiv piCircleAreaPolygon :=
  piCircleArea_equiv_piCircleAreaPolygon_of_polygonAgreement
    piCircleAreaPolygonAgreement

theorem piCircleAreaPolygonValid_of_polygonAgreement_and_areaValid
    (hagree : PiCircleAreaPolygonAgreement)
    (hvalid : AreaValid) :
    AreaPolygonValid := by
  unfold AreaValid RealRaw.ValidCompute at hvalid
  unfold AreaPolygonValid RealRaw.ValidCompute
  constructor
  · intro n
    rw [← hagree n]
    exact hvalid.1 n
  · constructor
    · intro n m hnm
      rw [← hagree n, ← hagree m]
      exact hvalid.2.1 n m hnm
    · intro eps
      obtain ⟨N, hN⟩ := hvalid.2.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      rw [← hagree n]
      exact hN n hn

def AreaStepRefines : Prop :=
  EndpointStepRefines piCircleArea.compute

def CircumferenceStepRefines : Prop :=
  EndpointStepRefines piCircumference.compute

def CircumferenceQuarterLengthStepRefines : Prop :=
  forall n,
    (innerQuarterLength (piStage n)).lo <=
      (innerQuarterLength (piStage (n + 1))).lo /\
    (outerQuarterLength (piStage (n + 1))).hi <=
      (outerQuarterLength (piStage n)).hi

def CircumferenceQuarterLengthStepRefinesUpTo (N : Nat) : Prop :=
  forall n, n <= N ->
    (innerQuarterLength (piStage n)).lo <=
      (innerQuarterLength (piStage (n + 1))).lo /\
    (outerQuarterLength (piStage (n + 1))).hi <=
      (outerQuarterLength (piStage n)).hi

def CircumferenceQuarterLengthStepRefinesUpToAll : Prop :=
  forall N, CircumferenceQuarterLengthStepRefinesUpTo N

theorem circumferenceQuarterLengthStepRefinesUpTo_of_stepRefines
    (hrefine : CircumferenceQuarterLengthStepRefines) (N : Nat) :
    CircumferenceQuarterLengthStepRefinesUpTo N := by
  intro n _hn
  exact hrefine n

theorem circumferenceQuarterLengthStepRefinesUpToAll_of_stepRefines
    (hrefine : CircumferenceQuarterLengthStepRefines) :
    CircumferenceQuarterLengthStepRefinesUpToAll := by
  intro N
  exact circumferenceQuarterLengthStepRefinesUpTo_of_stepRefines hrefine N

theorem circumferenceQuarterLengthStepRefines_of_upToAll
    (hrefine : CircumferenceQuarterLengthStepRefinesUpToAll) :
    CircumferenceQuarterLengthStepRefines := by
  intro n
  exact hrefine n n (Nat.le_refl n)

theorem circumferenceQuarterLengthStepRefines_iff_upToAll :
    CircumferenceQuarterLengthStepRefines ↔
      CircumferenceQuarterLengthStepRefinesUpToAll := by
  constructor
  · exact circumferenceQuarterLengthStepRefinesUpToAll_of_stepRefines
  · exact circumferenceQuarterLengthStepRefines_of_upToAll

theorem circumferenceQuarterLengthStepRefinesUpToNine :
    CircumferenceQuarterLengthStepRefinesUpTo 9 := by
  unfold CircumferenceQuarterLengthStepRefinesUpTo
  native_decide

/-- Exhaustive rational regression of the two direct perimeter endpoint
inequalities through twelve dyadic refinement transitions.  This is evidence
for, but deliberately not a replacement for, the symbolic all-stage
refinement theorem needed to validate `piCircumference`. -/
theorem circumferenceQuarterLengthStepRefinesUpToTwelve :
    CircumferenceQuarterLengthStepRefinesUpTo 12 := by
  unfold CircumferenceQuarterLengthStepRefinesUpTo
  native_decide

theorem circumferenceQuarterLengthStepRefinesUpToEight :
    CircumferenceQuarterLengthStepRefinesUpTo 8 := by
  intro n hn
  exact circumferenceQuarterLengthStepRefinesUpToNine n (by omega)

theorem circumferenceStepRefines_of_quarterLengthStepRefines
    (hrefine : CircumferenceQuarterLengthStepRefines) :
    CircumferenceStepRefines := by
  intro n
  have h := hrefine n
  rw [piCircumference_compute_eq,
    piCircumference_compute_eq,
    piCircumferenceComputeAtStage_eq_common,
    piCircumferenceComputeAtStage_eq_common]
  simp [piCircumferenceCommonComputeAtStage, four_div_two_eq_two_mul]
  constructor
  · exact Rat.mul_le_mul_of_nonneg_left h.1
      (by native_decide : (0 : Rat) <= 2)
  · exact Rat.mul_le_mul_of_nonneg_left h.2
      (by native_decide : (0 : Rat) <= 2)

def CircumferenceStepRefinesUpTo (N : Nat) : Prop :=
  forall n, n <= N ->
    (piCircumference.compute n).lo <=
      (piCircumference.compute (n + 1)).lo /\
    (piCircumference.compute (n + 1)).hi <=
      (piCircumference.compute n).hi

def CircumferenceStepRefinesUpToAll : Prop :=
  forall N, CircumferenceStepRefinesUpTo N

theorem circumferenceStepRefinesUpTo_of_stepRefines
    (hrefine : CircumferenceStepRefines) (N : Nat) :
    CircumferenceStepRefinesUpTo N := by
  intro n _hn
  exact hrefine n

theorem circumferenceStepRefinesUpTo_of_quarterLengthStepRefinesUpTo
    {N : Nat} (hrefine : CircumferenceQuarterLengthStepRefinesUpTo N) :
    CircumferenceStepRefinesUpTo N := by
  intro n hn
  have h := hrefine n hn
  rw [piCircumference_compute_eq,
    piCircumference_compute_eq,
    piCircumferenceComputeAtStage_eq_common,
    piCircumferenceComputeAtStage_eq_common]
  simp [piCircumferenceCommonComputeAtStage, four_div_two_eq_two_mul]
  constructor
  · exact Rat.mul_le_mul_of_nonneg_left h.1
      (by native_decide : (0 : Rat) <= 2)
  · exact Rat.mul_le_mul_of_nonneg_left h.2
      (by native_decide : (0 : Rat) <= 2)

theorem circumferenceStepRefinesUpToAll_of_stepRefines
    (hrefine : CircumferenceStepRefines) :
    CircumferenceStepRefinesUpToAll := by
  intro N
  exact circumferenceStepRefinesUpTo_of_stepRefines hrefine N

theorem circumferenceStepRefinesUpToAll_of_quarterLengthStepRefinesUpToAll
    (hrefine : CircumferenceQuarterLengthStepRefinesUpToAll) :
    CircumferenceStepRefinesUpToAll := by
  intro N
  exact circumferenceStepRefinesUpTo_of_quarterLengthStepRefinesUpTo
    (hrefine N)

theorem circumferenceStepRefines_of_stepRefinesUpToAll
    (hrefine : CircumferenceStepRefinesUpToAll) :
    CircumferenceStepRefines := by
  intro n
  exact hrefine n n (Nat.le_refl n)

theorem circumferenceStepRefines_iff_upToAll :
    CircumferenceStepRefines ↔ CircumferenceStepRefinesUpToAll := by
  constructor
  · exact circumferenceStepRefinesUpToAll_of_stepRefines
  · exact circumferenceStepRefines_of_stepRefinesUpToAll

theorem circumferenceStepRefines_of_quarterLengthStepRefinesUpToAll
    (hrefine : CircumferenceQuarterLengthStepRefinesUpToAll) :
    CircumferenceStepRefines :=
  circumferenceStepRefines_of_quarterLengthStepRefines
    (circumferenceQuarterLengthStepRefines_of_upToAll hrefine)

theorem circumferenceStepRefinesUpToEight :
    CircumferenceStepRefinesUpTo 8 :=
  circumferenceStepRefinesUpTo_of_quarterLengthStepRefinesUpTo
    circumferenceQuarterLengthStepRefinesUpToEight

theorem circumferenceStepRefinesUpToNine :
    CircumferenceStepRefinesUpTo 9 :=
  circumferenceStepRefinesUpTo_of_quarterLengthStepRefinesUpTo
    circumferenceQuarterLengthStepRefinesUpToNine

/-- The public perimeter endpoint inequalities through twelve transitions,
promoted from the direct quarter-path regression above. -/
theorem circumferenceStepRefinesUpToTwelve :
    CircumferenceStepRefinesUpTo 12 :=
  circumferenceStepRefinesUpTo_of_quarterLengthStepRefinesUpTo
    circumferenceQuarterLengthStepRefinesUpToTwelve

theorem areaNested_of_endpointMonotone
    (hordered : AreaOrdered)
    (hmono : EndpointMonotone piCircleArea.compute) :
    AreaNested := by
  intro n m hnm
  have h := hmono n m hnm
  constructor
  case left =>
    exact h.1
  case right =>
    constructor
    case left =>
      have hwidth := hordered m
      grind [QInterval.width, Rat.sub_eq_add_neg]
    case right =>
      exact h.2

theorem circumferenceNested_of_endpointMonotone
    (hmono : EndpointMonotone piCircumference.compute) :
    CircumferenceNested := by
  intro n m hnm
  have h := hmono n m hnm
  constructor
  case left =>
    exact h.1
  case right =>
    constructor
    case left =>
      have hwidth := piCircumference_ordered m
      grind [QInterval.width, Rat.sub_eq_add_neg]
    case right =>
      exact h.2

theorem areaNested_of_stepRefines
    (hordered : AreaOrdered)
    (hstep : AreaStepRefines) : AreaNested :=
  areaNested_of_endpointMonotone hordered
    (endpointMonotone_of_stepRefines hstep)

theorem circumferenceNested_of_stepRefines
    (hstep : CircumferenceStepRefines) : CircumferenceNested :=
  circumferenceNested_of_endpointMonotone
    (endpointMonotone_of_stepRefines hstep)

theorem areaValid_of_nested_and_shrinking
    (hordered : AreaOrdered)
    (hnested : AreaNested) (hshrink : AreaWidthsShrink) :
    AreaValid := by
  unfold AreaValid RealRaw.ValidCompute
  constructor
  case left =>
    exact hordered
  case right =>
    constructor
    case left =>
      exact hnested
    case right =>
      exact hshrink

namespace AreaLoopValidity

theorem iterateAreaBounds_succ_refine
    (n : Nat) (state : AreaBoundsLoopState) :
    iterateAreaBounds (n + 1) state =
      refineAreaBounds (iterateAreaBounds n state) := by
  induction n generalizing state with
  | zero =>
      rfl
  | succ n ih =>
      simp [iterateAreaBounds]
      exact ih (refineAreaBounds state)

theorem piCircleAreaState_succ (n : Nat) :
    piCircleAreaState (n + 1) =
      refineAreaBounds (piCircleAreaState n) := by
  unfold piCircleAreaState
  exact iterateAreaBounds_succ_refine n piCircleAreaInitial

theorem state_wellFormed (n : Nat) :
    IntervalsWellFormed (piCircleAreaState n).intervals := by
  induction n with
  | zero =>
      change IntervalsWellFormed [(0, 1)]
      simp [IntervalsWellFormed]
      native_decide
  | succ n ih =>
      rw [piCircleAreaState_succ]
      exact refineAreaBounds_wellFormed (piCircleAreaState n) ih

theorem state_gapSum (n : Nat) :
    (piCircleAreaState n).hi - (piCircleAreaState n).lo =
      areaGapSum (piCircleAreaState n).intervals := by
  induction n with
  | zero =>
      native_decide
  | succ n ih =>
      rw [piCircleAreaState_succ]
      exact refineAreaBounds_gapSum
        (piCircleAreaState n) (state_wellFormed n) ih

private theorem one_div_four_pow_succ (n : Nat) :
    (1 / (((4 ^ n : Nat) : Rat))) / 4 =
      1 / (((4 ^ (n + 1) : Nat) : Rat)) := by
  let A : Rat := ((4 ^ n : Nat) : Rat)
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 4))
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have h4 : (4 : Rat) ≠ 0 := by native_decide
  have hA4 : A * 4 ≠ 0 := by
    intro hz
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hpow :
      (((4 ^ (n + 1) : Nat) : Rat)) = A * 4 := by
    dsimp [A]
    exact_mod_cast (by
      simpa using (Nat.pow_succ 4 n))
  rw [hpow]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem state_cubeSum (n : Nat) :
    areaCubeSum (piCircleAreaState n).intervals =
      1 / (((4 ^ n : Nat) : Rat)) := by
  induction n with
  | zero =>
      native_decide
  | succ n ih =>
      rw [piCircleAreaState_succ]
      rw [refineAreaBounds_cubeSum, ih]
      exact one_div_four_pow_succ n

theorem areaOrdered : AreaOrdered := by
  intro n
  let state := piCircleAreaState n
  have hgap : state.hi - state.lo = areaGapSum state.intervals := by
    dsimp [state]
    exact state_gapSum n
  have hnonneg : 0 <= areaGapSum state.intervals := by
    dsimp [state]
    exact areaGapSum_nonneg _ (state_wellFormed n)
  change 0 <= (piCircleAreaCompute n).width
  unfold piCircleAreaCompute QInterval.width
  dsimp [state] at hgap hnonneg
  change 0 <= 4 * (piCircleAreaState n).hi -
    4 * (piCircleAreaState n).lo
  have hwidth :
      4 * (piCircleAreaState n).hi -
          4 * (piCircleAreaState n).lo =
        4 * ((piCircleAreaState n).hi - (piCircleAreaState n).lo) := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add]
  rw [hwidth, hgap]
  exact Rat.mul_nonneg (by native_decide : (0 : Rat) <= 4) hnonneg

theorem areaStepRefines : AreaStepRefines := by
  intro n
  have hwf := state_wellFormed n
  have hsucc := piCircleAreaState_succ n
  constructor
  · change (piCircleAreaCompute n).lo <= (piCircleAreaCompute (n + 1)).lo
    unfold piCircleAreaCompute
    rw [hsucc]
    exact Rat.mul_le_mul_of_nonneg_left
      (refineAreaBounds_lo_mono (piCircleAreaState n) hwf)
      (by native_decide : (0 : Rat) <= 4)
  · change (piCircleAreaCompute (n + 1)).hi <= (piCircleAreaCompute n).hi
    unfold piCircleAreaCompute
    rw [hsucc]
    exact Rat.mul_le_mul_of_nonneg_left
      (refineAreaBounds_hi_anti (piCircleAreaState n) hwf)
      (by native_decide : (0 : Rat) <= 4)

private theorem succ_le_four_pow (n : Nat) :
    n + 1 <= 4 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 4 * (n + 1) := by omega
        _ <= 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (n + 1) := by
          rw [Nat.pow_succ]
          omega

private theorem four_mul_one_div_eq_div (N : Nat) :
    4 * (1 / (N : Rat)) = 4 / (N : Rat) := by
  rw [Rat.div_def]
  grind [Rat.mul_assoc]

theorem areaWidthLinearBound_four : AreaWidthLinearBound 4 := by
  intro n
  let state := piCircleAreaState n
  have hwf := state_wellFormed n
  have hgap := state_gapSum n
  have hgap_le_cube := areaGapSum_le_cubeSum _ hwf
  have hcube := state_cubeSum n
  change (piCircleAreaCompute n).width <=
    (4 : Rat) / (((n + 1 : Nat) : Rat))
  unfold piCircleAreaCompute QInterval.width
  have hwidth :
      4 * state.hi - 4 * state.lo =
        4 * (state.hi - state.lo) := by
    dsimp [state]
    grind [Rat.sub_eq_add_neg, Rat.mul_add]
  rw [hwidth]
  calc
    4 * ((piCircleAreaState n).hi - (piCircleAreaState n).lo)
        = 4 * areaGapSum (piCircleAreaState n).intervals := by
          rw [hgap]
    _ <= 4 * areaCubeSum (piCircleAreaState n).intervals :=
          Rat.mul_le_mul_of_nonneg_left hgap_le_cube
            (by native_decide : (0 : Rat) <= 4)
    _ = 4 * (1 / (((4 ^ n : Nat) : Rat))) := by
          rw [hcube]
    _ = 4 / (((4 ^ n : Nat) : Rat)) := by
          exact four_mul_one_div_eq_div (4 ^ n)
    _ <= 4 / (((n + 1 : Nat) : Rat)) := by
          have hone :
              1 / (((4 ^ n : Nat) : Rat)) <=
                1 / (((n + 1 : Nat) : Rat)) :=
            FTC.one_div_nat_antitone (Nat.succ_pos n)
              (Nat.pow_pos (by omega : 0 < 4)) (succ_le_four_pow n)
          rw [← four_mul_one_div_eq_div (4 ^ n),
            ← four_mul_one_div_eq_div (n + 1)]
          exact Rat.mul_le_mul_of_nonneg_left hone
            (by native_decide : (0 : Rat) <= 4)

theorem areaWidthsShrink : AreaWidthsShrink :=
  areaWidthsShrink_of_linearBound areaWidthLinearBound_four

theorem areaNested : AreaNested :=
  areaNested_of_stepRefines areaOrdered areaStepRefines

theorem areaValid : AreaValid :=
  areaValid_of_nested_and_shrinking areaOrdered areaNested areaWidthsShrink

end AreaLoopValidity

/-- The polygonal area computation is a valid raw real because its stages are
exactly those of the verified public area loop. -/
theorem areaPolygonValid : AreaPolygonValid :=
  piCircleAreaPolygonValid_of_polygonAgreement_and_areaValid
    piCircleAreaPolygonAgreement AreaLoopValidity.areaValid

theorem piCircleAreaPolygon_valid : piCircleAreaPolygon.Valid :=
  areaPolygonValid

/-- Nilakantha's cubically convergent rational series is the same pi
computation as the verified circle-area construction.  The only new series
step is the finite endpoint transformation in `Nilakantha.equiv_piLeibniz`. -/
theorem piNilakantha_equiv_piCircleArea :
    piNilakantha.Equiv piCircleArea :=
  RealRaw.equiv_trans
    Nilakantha.valid
    leibnizValid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    Nilakantha.equiv_piLeibniz
    (RealRaw.equiv_trans
      leibnizValid
      fourArctanSeriesOneValid
      (by simpa [AreaValid] using AreaLoopValidity.areaValid)
      piLeibniz_equiv_four_arctanSeries_one
      four_arctanSeries_one_equiv_piCircleArea)

/-- Public rational error radius for the direct Archimedean chord-path
schedule.  Its proof is supplied by the verified area-loop width modulus, but
evaluating this function uses no area intervals. -/
def circumferenceStabilizationRadius (n : Nat) : Rat :=
  4 / (((n + 1 : Nat) : Rat))

theorem circumferenceStabilizationRadius_covers_area (n : Nat) :
    (piCircleArea.compute n).width <= circumferenceStabilizationRadius n := by
  simpa [circumferenceStabilizationRadius] using
    AreaLoopValidity.areaWidthLinearBound_four n

theorem circumferenceStabilizationRadius_shrinks :
    ShrinksToZero circumferenceStabilizationRadius := by
  apply shrinksToZero_of_natOverSuccBound (C := 4)
  intro n
  exact Rat.le_refl

/-- A valid direct-only Archimedean perimeter representative.

At stage `n`, evaluation widens the first `n + 1` direct chord-path intervals
by the rational schedule `4 / (n + 1)` and intersects that finite prefix.  It
does not call the circle-area evaluator.  The latter occurs only in the proof
that this public radius encloses the common value. -/
def piCircumferenceStabilized : RealRaw :=
  RealRaw.prefixStabilize piCircumference circumferenceStabilizationRadius

theorem piCircumferenceStabilized_valid : piCircumferenceStabilized.Valid := by
  unfold piCircumferenceStabilized
  exact RealRaw.prefixStabilize_valid
    circumferenceWidthsShrink
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    piCircumference_equiv_piCircleArea_of_verified_area_polygon
    circumferenceStabilizationRadius_covers_area
    circumferenceStabilizationRadius_shrinks

/-- The original direct chord-path intervals remain equivalent to their
finite-prefix stabilized representative. -/
theorem piCircumference_equiv_piCircumferenceStabilized :
    piCircumference.Equiv piCircumferenceStabilized := by
  unfold piCircumferenceStabilized
  exact RealRaw.candidate_equiv_prefixStabilize
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    piCircumference_equiv_piCircleArea_of_verified_area_polygon
    circumferenceStabilizationRadius_covers_area

/-- The stabilized direct Archimedean chord-path computation agrees with the
baseline circle-area definition of pi. -/
theorem piCircumferenceStabilized_equiv_piCircleArea :
    piCircumferenceStabilized.Equiv piCircleArea := by
  unfold piCircumferenceStabilized
  exact RealRaw.prefixStabilize_equiv_anchor
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    piCircumference_equiv_piCircleArea_of_verified_area_polygon
    circumferenceStabilizationRadius_covers_area

/-- A certified representative of the Archimedean circumference computation.

At every stage it intersects the finite prefix of hulls formed by the raw
perimeter interval and the verified circle-area interval.  The construction
uses only rational endpoint `min`/`max` arithmetic.  It is deliberately kept
separate from `piCircumference`: the latter remains the direct polygonal
perimeter schedule whose all-stage endpoint-refinement theorem is still an
open geometric result. -/
def piCircumferenceReboxed : RealRaw :=
  RealRaw.anchorRebox piCircumference piCircleArea

/-- The reboxed Archimedean perimeter representative is a valid computable
real.  Its proof combines the existing perimeter width modulus and finite
Archimedes overlap with the verified nested area computation; it does not
assume a limit or completeness principle. -/
theorem piCircumferenceReboxed_valid : piCircumferenceReboxed.Valid := by
  unfold piCircumferenceReboxed
  exact RealRaw.anchorRebox_valid
    piCircumference_ordered
    circumferenceWidthsShrink
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    piCircumference_equiv_piCircleArea_of_verified_area_polygon

/-- The direct perimeter intervals overlap their certified reboxed
representative at every common stage. -/
theorem piCircumference_equiv_piCircumferenceReboxed :
    piCircumference.Equiv piCircumferenceReboxed := by
  unfold piCircumferenceReboxed
  exact RealRaw.candidate_equiv_anchorRebox
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    piCircumference_equiv_piCircleArea_of_verified_area_polygon

/-- The certified reboxed perimeter computation agrees with the baseline
circle-area definition of pi. -/
theorem piCircumferenceReboxed_equiv_piCircleArea :
    piCircumferenceReboxed.Equiv piCircleArea := by
  unfold piCircumferenceReboxed
  exact RealRaw.anchorRebox_equiv_anchor
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)

/-- The initial certified π handle, retaining the two perimeter
normalizations available before the remaining independent routes have been
assembled below.  `piCertified` is the full presentation registry declared at
the end of this file. -/
def piCertifiedPerimeter : Real :=
  { preferred := piCircleArea
    valid := by simpa [AreaValid] using AreaLoopValidity.areaValid
    alternatives := [piCircumferenceStabilized, piCircumferenceReboxed]
    alternative_valid := by
      intro rep hrep
      cases hrep with
      | head => exact piCircumferenceStabilized_valid
      | tail _ htail =>
          cases htail with
          | head => exact piCircumferenceReboxed_valid
          | tail _ htail => cases htail
    coherent := by
      intro rep hrep
      cases hrep with
      | head => exact piCircumferenceStabilized_equiv_piCircleArea
      | tail _ htail =>
          cases htail with
          | head => exact piCircumferenceReboxed_equiv_piCircleArea
          | tail _ htail => cases htail }

theorem piCertifiedPerimeter_preferred :
    piCertifiedPerimeter.preferred = piCircleArea :=
  rfl

theorem fourArctanGeomOneValid :
    (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).Valid) := by
  have hcompute :
      (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).compute) =
        piCircleArea.compute := by
    funext n
    exact four_arctanGeom_one_compute_eq_piCircleArea_compute n
  change RealRaw.ValidCompute
    (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).compute)
  rw [hcompute]
  simpa [AreaValid] using AreaLoopValidity.areaValid

theorem arctanGeomOneValid :
    (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
  RealRaw.valid_of_natScale_valid (by omega : 0 < (4 : Nat))
    fourArctanGeomOneValid

theorem four_arctanGeom_one_equiv_piCircleArea :
    (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).Equiv
      piCircleArea) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw)
    piCircleArea n n).2
  rw [four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  have hordered := AreaLoopValidity.areaOrdered n
  unfold QInterval.Overlaps QInterval.width at *
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem piCircleArea_equiv_four_arctanGeom_one :
    piCircleArea.Equiv
      (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm four_arctanGeom_one_equiv_piCircleArea

/-- The direct Machin evaluator reaches the certified circle-area definition
from comparisons at its two actual series inputs.  The endpoint comparison at
`1` is not an analytic dependency of this route: the verified tangent-chart
transport supplies the corresponding geometric value. -/
theorem piMachin_equiv_piCircleArea_of_powerSeriesGeometryAtMachinSmallInputs
    (hagree : MachinIdentity.PowerSeriesGeometryAtMachinSmallInputs) :
    piMachin.Equiv piCircleArea := by
  have hps15 : (arctan ((1 : Rat) / 5)).Valid :=
    arctan_valid_at arctanValid arctan_one_fifth_mem_domain
  have hps239 : (arctan ((1 : Rat) / 239)).Valid :=
    arctan_valid_at arctanValid arctan_one_239_mem_domain
  have hg15 : (ArctanGeometry.arctanGeom ((1 : Rat) / 5)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hg239 : (ArctanGeometry.arctanGeom ((1 : Rat) / 239)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hg1 : (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide)
  have hps4_15 :
      ((4 : Nat) * arctan ((1 : Rat) / 5) : RealRaw).Valid :=
    RealRaw.natScale_valid 4 hps15
  have hg4_15 :
      ((4 : Nat) * ArctanGeometry.arctanGeom ((1 : Rat) / 5) : RealRaw).Valid :=
    RealRaw.natScale_valid 4 hg15
  have hpsExpr :
      ((4 : Nat) * arctan ((1 : Rat) / 5) -
        arctan ((1 : Rat) / 239) : RealRaw).Valid :=
    RealRaw.sub_valid hps4_15 hps239
  have hgExpr :
      ((4 : Nat) * ArctanGeometry.arctanGeom ((1 : Rat) / 5) -
        ArctanGeometry.arctanGeom ((1 : Rat) / 239) : RealRaw).Valid :=
    RealRaw.sub_valid hg4_15 hg239
  have hseries_geom :
      ((4 : Nat) * arctan ((1 : Rat) / 5) -
        arctan ((1 : Rat) / 239) : RealRaw).Equiv
      ((4 : Nat) * ArctanGeometry.arctanGeom ((1 : Rat) / 5) -
        ArctanGeometry.arctanGeom ((1 : Rat) / 239) : RealRaw) :=
    RealRaw.sub_equiv
      hps4_15 hg4_15 hps239 hg239
      (RealRaw.natScale_equiv 4 hagree.one_fifth)
      hagree.one_239
  have htoGeomOne :
      ((4 : Nat) * arctan ((1 : Rat) / 5) -
        arctan ((1 : Rat) / 239) : RealRaw).Equiv
      (ArctanGeometry.arctanGeom (1 : Rat)) :=
    RealRaw.equiv_trans
      hpsExpr hgExpr hg1 hseries_geom
      MachinIdentity.geometricBranchIdentity_of_chartTransport
  have hscaled :
      piMachin.Equiv
        ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) := by
    simpa [piMachin] using RealRaw.natScale_equiv 4 htoGeomOne
  exact RealRaw.equiv_trans
    machinValid
    (RealRaw.natScale_valid 4 hg1)
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    hscaled
    four_arctanGeom_one_equiv_piCircleArea

/-- Machin's classical single formula is a verified pi computation using its
two alternating arctangent power series.  The only analytic comparison is the
finite-rational series/rectangle bridge at `1/5` and `1/239`; the bounded
tangent-chart additions provide the geometric identity. -/
theorem piMachin_equiv_piCircleArea_finiteRiemannBridge :
    piMachin.Equiv piCircleArea :=
  piMachin_equiv_piCircleArea_of_powerSeriesGeometryAtMachinSmallInputs
    (MachinIdentity.powerSeriesGeometryAtMachinSmallInputs_of_kernelComparisonAtMachinSmallInputs
      { one_fifth :=
          kernelComparisonAt_of_powerSeriesEqualsRectangleKernelAt
            (powerSeriesEqualsRectangleKernelAt_finiteRiemannBridge
              (x := (1 : Rat) / 5) (by native_decide) (by native_decide))
        one_239 :=
          kernelComparisonAt_of_powerSeriesEqualsRectangleKernelAt
            (powerSeriesEqualsRectangleKernelAt_finiteRiemannBridge
              (x := (1 : Rat) / 239) (by native_decide) (by native_decide)) })

theorem piMachin_equiv_piCircleArea_of_kernelComparisonAtMachinSmallInputs
    (route : MachinIdentity.KernelComparisonAtMachinSmallInputs) :
  piMachin.Equiv piCircleArea :=
  piMachin_equiv_piCircleArea_of_powerSeriesGeometryAtMachinSmallInputs
    (MachinIdentity.powerSeriesGeometryAtMachinSmallInputs_of_kernelComparisonAtMachinSmallInputs
      route)

theorem leibnizEqArea_of_kernelComparisonAtOne
    (route : Taylor.ArctanComparison.KernelComparisonAt (1 : Rat)) :
    LeibnizEqArea :=
  RealRaw.equiv_trans
    leibnizValid
    fourArctanSeriesOneValid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    piLeibniz_equiv_four_arctanSeries_one
    (four_arctanSeries_one_equiv_piCircleArea_of_kernelComparisonAtOne
      route)

theorem leibnizEqArea_of_powerSeriesRectangleKernelAtOne
    (hps : PowerSeriesEqualsRectangleKernelAtOne) :
    LeibnizEqArea :=
  leibnizEqArea_of_kernelComparisonAtOne
    (kernelComparisonAtOne_of_powerSeriesEqualsRectangleKernelAtOne hps)

theorem leibnizEqArea_of_leibnizEqualsRectangleRawAtOne
    (h : LeibnizEqualsRectangleRawAtOne) :
    LeibnizEqArea :=
  leibnizEqArea_of_powerSeriesRectangleKernelAtOne
    (powerSeriesEqualsRectangleKernelAtOne_of_leibnizEqualsRectangleRawAtOne h)

theorem leibnizEqArea_of_kernelBounds
    (h : LeibnizRectangleKernelBoundsAtOne) :
    LeibnizEqArea :=
  leibnizEqArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_kernelBounds h)

theorem leibnizEqArea_of_kernelBoundsUpToAll
    (h : forall N,
      LeibnizRectangleBridge.LeibnizRectangleKernelBoundsAtOneUpTo N) :
    LeibnizEqArea :=
  leibnizEqArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_kernelBoundsUpToAll h)

theorem leibnizEqArea_of_uniformCellBounds
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformCellBoundsAtOne) :
    LeibnizEqArea :=
  leibnizEqArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_uniformCellBounds h)

theorem leibnizEqArea_of_unitUniformCellBounds
    (h : LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOne) :
    LeibnizEqArea :=
  leibnizEqArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_unitUniformCellBounds h)

theorem leibnizEqArea_of_cellBoundsUpToAll
    (h : forall N,
      LeibnizRectangleBridge.LeibnizRectangleKernelCellBoundsAtOneUpTo N) :
    LeibnizEqArea :=
  leibnizEqArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_cellBoundsUpToAll h)

theorem leibnizEqArea_of_unitUniformCellBoundsUpToAll
    (h : forall N,
      LeibnizRectangleBridge.LeibnizRectangleUniformUnitCellBoundsAtOneUpTo N) :
    LeibnizEqArea :=
  leibnizEqArea_of_leibnizEqualsRectangleRawAtOne
    (leibnizEqualsRectangleRawAtOne_of_unitUniformCellBoundsUpToAll h)

theorem leibnizEqArea_of_pointwiseIntegralBridge
    (h : LeibnizRectangleBridge.LeibnizRectanglePointwiseIntegralBridgeAtOne) :
    LeibnizEqArea :=
  leibnizEqArea_of_uniformCellBounds
    (LeibnizRectangleBridge.uniformCellBounds_of_pointwiseIntegralBridge h)

theorem leibnizEqArea_of_pointwiseUnitIntegralBridge
    (h : LeibnizRectangleBridge.LeibnizRectanglePointwiseUnitIntegralBridgeAtOne) :
    LeibnizEqArea :=
  leibnizEqArea_of_unitUniformCellBounds
    (LeibnizRectangleBridge.unitUniformCellBounds_of_pointwiseUnitIntegralBridge h)

theorem leibnizEqArea_of_unitCellOrderPreservation
    (h : LeibnizRectangleBridge.LeibnizRectangleUnitCellOrderPreservation) :
    LeibnizEqArea :=
  leibnizEqArea_of_pointwiseUnitIntegralBridge
    (LeibnizRectangleBridge.pointwiseUnitIntegralBridgeAtOne_of_unitCellOrderPreservation
      h)

theorem leibnizEqArea_of_kernelPartialExactCellOrderPreservation
    (h :
      LeibnizRectangleBridge.KernelPartialExactCellOrderPreservationOnUnit) :
    LeibnizEqArea :=
  leibnizEqArea_of_unitCellOrderPreservation
    (LeibnizRectangleBridge.unitCellOrderPreservation_of_kernelPartialExactCellOrderPreservation
      h)

theorem piMachin_equiv_piCircleArea_of_kernelComparisonAtMachinInputs
    (route : MachinIdentity.KernelComparisonAtMachinInputs)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    piMachin.Equiv piCircleArea :=
  RealRaw.equiv_trans
    machinValid
    leibnizValid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    (RealRaw.equiv_symm
      (leibnizEqMachin_of_kernelComparisonAtMachinInputs route hgeom))
    (leibnizEqArea_of_kernelComparisonAtOne route.one)

/-- The remaining data for the canonical Machin pi equivalence are the three
pointwise power-series/kernel comparisons.  The bounded geometric additions
are now theorems. -/
theorem piMachin_equiv_piCircleArea_of_machinUnitAdditions
    (route : MachinIdentity.KernelComparisonAtMachinInputs)
    (hadd : MachinIdentity.GeometricMachinUnitAdditions) :
    piMachin.Equiv piCircleArea :=
  piMachin_equiv_piCircleArea_of_kernelComparisonAtMachinInputs route
    (MachinIdentity.geometricBranchLaw_of_machinUnitAdditions hadd)

/-- The bounded geometric Machin additions are now internal theorems; only
the three remaining power-series/kernel comparisons are parameters here. -/
theorem piMachin_equiv_piCircleArea_of_kernelComparisonAtMachinInputs_chartTransport
    (route : MachinIdentity.KernelComparisonAtMachinInputs) :
    piMachin.Equiv piCircleArea :=
  piMachin_equiv_piCircleArea_of_kernelComparisonAtMachinInputs route
    MachinIdentity.geometricBranchLaw_of_chartTransport

theorem piMachin_equiv_piCircleArea_of_unitAdditionLaw
    (route : MachinIdentity.KernelComparisonAtMachinInputs)
    (hadd : MachinIdentity.GeometricUnitAdditionLaw) :
    piMachin.Equiv piCircleArea :=
  piMachin_equiv_piCircleArea_of_machinUnitAdditions route
    (MachinIdentity.geometricMachinUnitAdditions_of_unitAdditionLaw hadd)

theorem piCircleArea_equiv_piMachin_of_kernelComparisonAtMachinInputs
    (route : MachinIdentity.KernelComparisonAtMachinInputs)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    piCircleArea.Equiv piMachin :=
  RealRaw.equiv_symm
    (piMachin_equiv_piCircleArea_of_kernelComparisonAtMachinInputs
      route hgeom)

theorem piMachin_equiv_piCircleArea_of_powerSeriesRectangleKernelAtMachinInputs
    (hps : MachinIdentity.PowerSeriesEqualsRectangleKernelAtMachinInputs)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    piMachin.Equiv piCircleArea :=
  piMachin_equiv_piCircleArea_of_kernelComparisonAtMachinInputs
    (MachinIdentity.kernelComparisonAtMachinInputs_of_powerSeriesEqualsRectangleKernelAtMachinInputs
      hps)
    hgeom

theorem piCircleArea_equiv_piMachin_of_powerSeriesRectangleKernelAtMachinInputs
    (hps : MachinIdentity.PowerSeriesEqualsRectangleKernelAtMachinInputs)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    piCircleArea.Equiv piMachin :=
  RealRaw.equiv_symm
    (piMachin_equiv_piCircleArea_of_powerSeriesRectangleKernelAtMachinInputs
      hps hgeom)

theorem four_arctanIntegralRectangleRawAtOne_equiv_piCircleArea :
    (((4 : Nat) *
        ArctanGeometry.arctanIntegralRectangleRawAtOne : RealRaw).Equiv
      piCircleArea) := by
  have hscale :
      (((4 : Nat) *
          ArctanGeometry.arctanIntegralRectangleRawAtOne : RealRaw).Equiv
        ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw)) :=
    RealRaw.natScale_equiv 4
      ArctanGeometry.arctanIntegralRectangleRawAtOne_equiv_arctanGeom_one
  exact RealRaw.equiv_trans
    (RealRaw.natScale_valid 4
      ArctanGeometry.arctanIntegralRectangleRawAtOne_valid)
    fourArctanGeomOneValid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    hscale
    four_arctanGeom_one_equiv_piCircleArea

/-- The direct finite integration-by-parts mesh computation is a valid
supplementary pi evaluator.  Its proof is intentionally separate from the
uncompleted arctangent--logarithm integral route: it uses only the finite mesh
identity, its explicit corner budget, and the verified arctangent rectangle
anchor. -/
theorem piFromArctanIntegrationByPartsMesh_equiv_piCircleArea :
    IntegralIdentities.piFromArctanIntegrationByPartsMesh.Equiv
      piCircleArea := by
  have hscale :
      IntegralIdentities.piFromArctanIntegrationByPartsMesh.Equiv
        ((4 : Nat) * ArctanGeometry.arctanIntegralRectangleRawAtOne : RealRaw) := by
    unfold IntegralIdentities.piFromArctanIntegrationByPartsMesh
    exact RealRaw.natScale_equiv 4
      IntegralIdentities.arctanIntegrationByPartsMesh_equiv_rectangleAtOne
  exact RealRaw.equiv_trans
    IntegralIdentities.piFromArctanIntegrationByPartsMesh_valid
    (RealRaw.natScale_valid 4
      ArctanGeometry.arctanIntegralRectangleRawAtOne_valid)
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    hscale
    four_arctanIntegralRectangleRawAtOne_equiv_piCircleArea

/-- The direct triangle-plus-alternating-logarithm formula is a valid
supplementary pi computation.  Its proof uses the finite triangle/strip
bridge and the independently checked logarithm series at two; it deliberately
does not assert the still-pending function-level integration-by-parts theorem.
-/
theorem piTriangleLogSeries_equiv_piCircleArea :
    Logarithm.piTriangleLogSeries.Equiv piCircleArea := by
  exact RealRaw.equiv_trans
    Logarithm.piTriangleLogSeries_valid
    fourArctanGeomOneValid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    Logarithm.piTriangleLogSeries_equiv_four_arctanGeom_one
    four_arctanGeom_one_equiv_piCircleArea

/-- The literal reciprocal-integral logarithm version of the supplied
arctangent integration-by-parts formula is also a certified pi presentation.
It is deliberately supplementary: it gives the natural calculus-side formula
before the still-open transport to the canonical inverse-exponential log. -/
theorem piTriangleLogReciprocalIntegral_equiv_piCircleArea :
    Logarithm.piTriangleLogReciprocalIntegral.Equiv piCircleArea := by
  exact RealRaw.equiv_trans
    Logarithm.piTriangleLogReciprocalIntegral_valid
    fourArctanGeomOneValid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    Logarithm.piTriangleLogReciprocalIntegral_equiv_four_arctanGeom_one
    four_arctanGeom_one_equiv_piCircleArea

/-- The square-substitution form of the supplied arctangent formula is a
certified pi presentation.  Its logarithmic endpoint is the literal integral
of `2*x/(1+x^2)` on the unit interval, kept separate from the reciprocal-log
form so the finite substitution certificate is exercised at pi level. -/
theorem piTriangleLogSquareSubstitutionIntegral_equiv_piCircleArea :
    Logarithm.piTriangleLogSquareSubstitutionIntegral.Equiv piCircleArea := by
  exact RealRaw.equiv_trans
    Logarithm.piTriangleLogSquareSubstitutionIntegral_valid
    fourArctanGeomOneValid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    Logarithm.piTriangleLogSquareSubstitutionIntegral_equiv_four_arctanGeom_one
    four_arctanGeom_one_equiv_piCircleArea

theorem four_arctanIntegralRectangleForAtOne_equiv_piCircleArea :
    (IntegralIdentities.PiFromArctanIntegral
      IntegralIdentities.arctanIntegralRectangleForAtOne).Equiv
        piCircleArea := by
  have hscaled :
      (IntegralIdentities.PiFromArctanIntegral
        IntegralIdentities.arctanIntegralRectangleForAtOne).Equiv
          ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) := by
    unfold IntegralIdentities.PiFromArctanIntegral
    exact RealRaw.natScale_equiv 4
      IntegralIdentities.arctanIntegralRectangleForAtOne_equiv_arctanGeom_one
  have hleft :
      (IntegralIdentities.PiFromArctanIntegral
        IntegralIdentities.arctanIntegralRectangleForAtOne).Valid := by
    unfold IntegralIdentities.PiFromArctanIntegral
    exact RealRaw.natScale_valid 4
      IntegralIdentities.arctanIntegralRectangleForAtOne_valid
  exact RealRaw.equiv_trans
    hleft
    fourArctanGeomOneValid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    hscaled
    four_arctanGeom_one_equiv_piCircleArea

/-- The reciprocal-tail compactification of the full-line Cauchy integral is
another completed pi computation.  Its construction is finite: evenness and
the reciprocal substitution turn the two tails into the compact density
`2 / (1+x^2)` on `[0,1]`, whose rectangle bracket is exactly twice the
verified arctangent rectangle bracket. -/
theorem cauchyFullLineIntegral_equiv_piCircleArea :
    IntegralIdentities.cauchyFullLineIntegral.Equiv piCircleArea := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    IntegralIdentities.cauchyFullLineIntegral piCircleArea n n).2
  rw [IntegralIdentities.cauchyFullLineIntegral_compute_eq_four_rectangle n]
  simpa [IntegralIdentities.PiFromArctanIntegral] using
    (RealRaw.compareAt_overlap_iff
      (IntegralIdentities.PiFromArctanIntegral
        IntegralIdentities.arctanIntegralRectangleForAtOne)
      piCircleArea n n).1
      (four_arctanIntegralRectangleForAtOne_equiv_piCircleArea n)

/-- The bounded symmetric Cauchy formula is a separate finite
piecewise-monotone computation: the kernel is assembled from an increasing
negative branch and a decreasing positive branch before being compared with
the unit-branch rectangle integral. -/
theorem piSymmetricCauchyPiecewiseIntegral_equiv_four_arctanIntegralRectangleForAtOne :
    IntegralIdentities.piSymmetricCauchyPiecewiseIntegral.Equiv
      ((4 : Nat) * IntegralIdentities.arctanIntegralRectangleForAtOne : RealRaw) := by
  have hA : IntegralIdentities.arctanIntegralRectangleForAtOne.Valid :=
    IntegralIdentities.arctanIntegralRectangleForAtOne_valid
  have hfirst : IntegralIdentities.piSymmetricCauchyPiecewiseIntegral.Equiv
      ((2 : Nat) * ((2 : Nat) *
        IntegralIdentities.arctanIntegralRectangleForAtOne : RealRaw) : RealRaw) := by
    unfold IntegralIdentities.piSymmetricCauchyPiecewiseIntegral
    exact RealRaw.natScale_equiv 2
      IntegralIdentities.symmetricCauchyPiecewiseIntegral_equiv_two_rectangle
  have hcompose :
      ((2 : Nat) * ((2 : Nat) *
        IntegralIdentities.arctanIntegralRectangleForAtOne : RealRaw) : RealRaw).Equiv
      ((4 : Nat) * IntegralIdentities.arctanIntegralRectangleForAtOne : RealRaw) := by
    have h := RealRaw.scaleRat_scaleRat_equiv_of_nonneg
      (2 : Rat) (2 : Rat) (by native_decide) (by native_decide)
      IntegralIdentities.arctanIntegralRectangleForAtOne hA
    simpa only [show (2 : Rat) * (2 : Rat) = 4 by native_decide] using h
  exact RealRaw.equiv_trans
    IntegralIdentities.piSymmetricCauchyPiecewiseIntegral_valid
    (RealRaw.natScale_valid 2 (RealRaw.natScale_valid 2 hA))
    (RealRaw.natScale_valid 4 hA)
    hfirst hcompose

/-- The bounded symmetric Cauchy formula evaluates to the preferred
circle-area representation of pi. -/
theorem piSymmetricCauchyPiecewiseIntegral_equiv_piCircleArea :
    IntegralIdentities.piSymmetricCauchyPiecewiseIntegral.Equiv piCircleArea := by
  exact RealRaw.equiv_trans
    IntegralIdentities.piSymmetricCauchyPiecewiseIntegral_valid
    (RealRaw.natScale_valid 4
      IntegralIdentities.arctanIntegralRectangleForAtOne_valid)
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    piSymmetricCauchyPiecewiseIntegral_equiv_four_arctanIntegralRectangleForAtOne
    four_arctanIntegralRectangleForAtOne_equiv_piCircleArea

/-- The same completed rectangle-integral pi route, viewed through the
monotone-integral interface for the decreasing kernel `1/(1+x^2)` on
`[0,1]`. -/
theorem four_arctanIntegralRectangleMonotoneForAtOne_equiv_piCircleArea :
    (IntegralIdentities.PiFromArctanIntegral
      IntegralIdentities.arctanIntegralRectangleMonotoneForAtOne).Equiv
        piCircleArea := by
  have hscaled :
      (IntegralIdentities.PiFromArctanIntegral
        IntegralIdentities.arctanIntegralRectangleMonotoneForAtOne).Equiv
          (IntegralIdentities.PiFromArctanIntegral
            IntegralIdentities.arctanIntegralRectangleForAtOne) := by
    unfold IntegralIdentities.PiFromArctanIntegral
    exact RealRaw.natScale_equiv 4
      IntegralIdentities.arctanIntegralRectangleMonotoneForAtOne_equiv_rectangleForAtOne
  have hleft :
      (IntegralIdentities.PiFromArctanIntegral
        IntegralIdentities.arctanIntegralRectangleMonotoneForAtOne).Valid := by
    unfold IntegralIdentities.PiFromArctanIntegral
    exact RealRaw.natScale_valid 4
      IntegralIdentities.arctanIntegralRectangleMonotoneForAtOne_valid
  have hrect :
      (IntegralIdentities.PiFromArctanIntegral
        IntegralIdentities.arctanIntegralRectangleForAtOne).Valid := by
    unfold IntegralIdentities.PiFromArctanIntegral
    exact RealRaw.natScale_valid 4
      IntegralIdentities.arctanIntegralRectangleForAtOne_valid
  exact RealRaw.equiv_trans
    hleft
    hrect
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    hscaled
    four_arctanIntegralRectangleForAtOne_equiv_piCircleArea

/-- The table-facing unit-branch rectangle integral computation of pi:
`4 * ∫_0^1 dt/(1+t^2)`, using the `arctanIntegralUnit` API. -/
def piFromArctanIntegralRectangleUnitAtOne : RealRaw :=
  IntegralIdentities.PiFromArctanIntegral
    (IntegralIdentities.arctanIntegralUnit (1 : Rat)
      (IntegralIdentities.arctanIntegralRectangleUnitData.constructionAt
        (1 : Rat) (by native_decide) (by native_decide)))

/-- At the raw-computation level, the public rectangle presentation of pi is
exactly four times the unit rectangle integral. -/
theorem piFromArctanIntegralRectangleUnitAtOne_compute_eq_four_rectangle
    (n : Nat) :
    piFromArctanIntegralRectangleUnitAtOne.compute n =
      ((4 : Nat) * IntegralIdentities.arctanIntegralRectangleForAtOne : RealRaw).compute n :=
  rfl

/-- Certified linear width bound for the public rectangle-integral
presentation of pi.  The unscaled integral has bound `4/(n+1)`; the displayed
pi evaluator includes its factor of four. -/
theorem piFromArctanIntegralRectangleUnitAtOne_width_le_sixteen_div_succ
    (n : Nat) :
    (piFromArctanIntegralRectangleUnitAtOne.compute n).width <=
      (16 : Rat) / (((n + 1 : Nat) : Rat)) := by
  rw [piFromArctanIntegralRectangleUnitAtOne_compute_eq_four_rectangle]
  rw [RealRaw.natScale_width]
  calc
    (4 : Rat) * (IntegralIdentities.arctanIntegralRectangleForAtOne.compute n).width <=
        4 * ((4 : Rat) / (((n + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left
        (IntegralIdentities.arctanIntegralRectangleForAtOne_width_le_four_div_succ n)
        (by native_decide)
    _ = (16 : Rat) / (((n + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc]

theorem piFromArctanIntegralRectangleUnitAtOne_valid :
    piFromArctanIntegralRectangleUnitAtOne.Valid := by
  unfold piFromArctanIntegralRectangleUnitAtOne
    IntegralIdentities.PiFromArctanIntegral
  apply RealRaw.natScale_valid
  exact Integral.integralFor_valid
    (IntegralIdentities.arctanKernelInterval (1 : Rat))
    (IntegralIdentities.arctanIntegralRectangleUnitData.constructionAt
      (1 : Rat) (by native_decide) (by native_decide))

theorem piFromArctanIntegralRectangleUnitAtOne_equiv_piCircleArea :
    piFromArctanIntegralRectangleUnitAtOne.Equiv piCircleArea := by
  have hscaled :
      piFromArctanIntegralRectangleUnitAtOne.Equiv
          ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) := by
    unfold piFromArctanIntegralRectangleUnitAtOne
      IntegralIdentities.PiFromArctanIntegral
    exact RealRaw.natScale_equiv 4
      (IntegralIdentities.arctanIntegralRectangleUnit_equiv_arctanGeom
        (1 : Rat) (by native_decide) (by native_decide))
  exact RealRaw.equiv_trans
    piFromArctanIntegralRectangleUnitAtOne_valid
    fourArctanGeomOneValid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    hscaled
    four_arctanGeom_one_equiv_piCircleArea

theorem piCircleArea_equiv_piFromArctanIntegralRectangleUnitAtOne :
    piCircleArea.Equiv piFromArctanIntegralRectangleUnitAtOne :=
  RealRaw.equiv_symm
    piFromArctanIntegralRectangleUnitAtOne_equiv_piCircleArea

def piFromArctanGeomUnitRectangleDefiniteIdentity : RealRaw :=
  IntegralIdentities.PiFromArctanIntegral
    (Integral.integralFor
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
      IntegralIdentities.arctanGeomUnitRectangleDefiniteIdentity.construction)

theorem piFromArctanGeomUnitRectangleDefiniteIdentity_valid :
    piFromArctanGeomUnitRectangleDefiniteIdentity.Valid := by
  unfold piFromArctanGeomUnitRectangleDefiniteIdentity
    IntegralIdentities.PiFromArctanIntegral
  exact RealRaw.scaleRat_valid_of_nonneg
    (by native_decide : (0 : Rat) <= 4)
    (Integral.integralFor_valid
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
      IntegralIdentities.arctanGeomUnitRectangleDefiniteIdentity.construction)

theorem piFromArctanGeomUnitRectangleDefiniteIdentity_equiv_piCircleArea :
    piFromArctanGeomUnitRectangleDefiniteIdentity.Equiv piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_definiteIdentityFor
    IntegralIdentities.arctanGeomOnUnit
    IntegralIdentities.arctanGeomUnitRectangleDefiniteIdentity
    IntegralIdentities.arctanGeomOnUnit_endpointDifference_equiv_arctanGeom_one

theorem piFromArctanGeomUnitRectangleDefiniteIdentity_compute_eq_rectangleUnit
    (n : Nat) :
    piFromArctanGeomUnitRectangleDefiniteIdentity.compute n =
      piFromArctanIntegralRectangleUnitAtOne.compute n := by
  rfl

theorem piFromArctanGeomUnitRectangleDefiniteIdentity_equiv_rectangleUnit :
    piFromArctanGeomUnitRectangleDefiniteIdentity.Equiv
      piFromArctanIntegralRectangleUnitAtOne := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    piFromArctanGeomUnitRectangleDefiniteIdentity
    piFromArctanIntegralRectangleUnitAtOne n n).2
  rw [piFromArctanGeomUnitRectangleDefiniteIdentity_compute_eq_rectangleUnit n]
  have horder := RealRaw.interval_order_of_valid
    piFromArctanIntegralRectangleUnitAtOne
    piFromArctanIntegralRectangleUnitAtOne_valid n
  exact ⟨horder, horder⟩

theorem piFromArctanIntegralRectangleUnitAtOne_equiv_geomUnitDefiniteIdentity :
    piFromArctanIntegralRectangleUnitAtOne.Equiv
      piFromArctanGeomUnitRectangleDefiniteIdentity :=
  RealRaw.equiv_symm
    piFromArctanGeomUnitRectangleDefiniteIdentity_equiv_rectangleUnit

/-- The pi raw real obtained from the monotone-definite endpoint identity for
the rectangle arctangent integral. -/
def piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity : RealRaw :=
  IntegralIdentities.PiFromArctanIntegral
    (Integral.monotoneIntegralFor
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
      IntegralIdentities.arctanGeomUnitRectangleMonotoneDefiniteIdentity.construction)

theorem piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity_valid :
    piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity.Valid := by
  unfold piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity
    IntegralIdentities.PiFromArctanIntegral
  exact RealRaw.scaleRat_valid_of_nonneg
    (by native_decide : (0 : Rat) <= 4)
    (Integral.monotoneIntegralFor_valid
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
      IntegralIdentities.arctanGeomUnitRectangleMonotoneDefiniteIdentity.construction)

theorem piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity_equiv_piCircleArea :
    piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity.Equiv piCircleArea :=
  piFromArctanIntegralFor_equiv_piCircleArea_of_monotoneDefiniteIdentityFor
    IntegralIdentities.arctanGeomOnUnit
    IntegralIdentities.arctanGeomUnitRectangleMonotoneDefiniteIdentity
    IntegralIdentities.arctanGeomOnUnit_endpointDifference_equiv_arctanGeom_one

theorem piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity_compute_eq_rectangle
    (n : Nat) :
    piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity.compute n =
      piFromArctanGeomUnitRectangleDefiniteIdentity.compute n := by
  rfl

theorem piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity_equiv_rectangle :
    piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity.Equiv
      piFromArctanGeomUnitRectangleDefiniteIdentity := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity
    piFromArctanGeomUnitRectangleDefiniteIdentity n n).2
  rw [piFromArctanGeomUnitRectangleMonotoneDefiniteIdentity_compute_eq_rectangle n]
  have horder := RealRaw.interval_order_of_valid
    piFromArctanGeomUnitRectangleDefiniteIdentity
    piFromArctanGeomUnitRectangleDefiniteIdentity_valid n
  exact ⟨horder, horder⟩

/-- The pi raw real obtained from the public general-integral endpoint
identity for the rectangle arctangent integral. -/
noncomputable def piFromArctanGeomUnitRectangleGeneralDefiniteIdentity :
    RealRaw :=
  IntegralIdentities.PiFromArctanIntegral
    (Integral.generalIntegralFor
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
      IntegralIdentities.arctanGeomUnitRectangleGeneralDefiniteIdentity.construction)

theorem piFromArctanGeomUnitRectangleGeneralDefiniteIdentity_valid :
    piFromArctanGeomUnitRectangleGeneralDefiniteIdentity.Valid := by
  unfold piFromArctanGeomUnitRectangleGeneralDefiniteIdentity
    IntegralIdentities.PiFromArctanIntegral
  exact RealRaw.scaleRat_valid_of_nonneg
    (by native_decide : (0 : Rat) <= 4)
    (Integral.generalIntegralFor_valid
      (IntegralIdentities.oneOverOnePlusSquareOnInterval 0 1)
      IntegralIdentities.arctanGeomUnitRectangleGeneralDefiniteIdentity.construction)

theorem piFromArctanGeomUnitRectangleGeneralDefiniteIdentity_equiv_piCircleArea :
    piFromArctanGeomUnitRectangleGeneralDefiniteIdentity.Equiv piCircleArea :=
  piFromArctanGeneralIntegralFor_equiv_piCircleArea_of_generalDefiniteIdentityFor
    IntegralIdentities.arctanGeomOnUnit
    IntegralIdentities.arctanGeomUnitRectangleGeneralDefiniteIdentity
    IntegralIdentities.arctanGeomOnUnit_endpointDifference_equiv_arctanGeom_one

/-- The finite compact reciprocal-quartic pi computation.  This is the
explicit dyadic integral of `(1 + x^2) / (x^4 - x^2 + 1)` on `[-1,1]`, not a
reboxing of an existing pi raw real.  Its equivalence to `piCircleArea` is
proved below through a finite projective/Cauchy bridge. -/
def piReciprocalQuarticCompact : RealRaw :=
  IntegralIdentities.reciprocalQuarticMinusOneCompactDyadicIntegral

/-- Exact dyadic width of the public compact reciprocal-quartic pi
presentation. -/
theorem piReciprocalQuarticCompact_width (n : Nat) :
    (piReciprocalQuarticCompact.compute n).width =
      64 * (1 / (((2 ^ n : Nat) : Rat))) := by
  exact IntegralIdentities.reciprocalQuarticMinusOneCompactDyadicIntegral_width n

theorem piReciprocalQuarticCompact_valid :
    piReciprocalQuarticCompact.Valid := by
  exact IntegralIdentities.reciprocalQuarticMinusOneCompactDyadicIntegral_valid

/-- The literal compact reciprocal-quartic dyadic integral is another
fully verified pi computation.  Its route passes through the independently
completed Cauchy full-line raw, using only the explicit shrinking rational
projective envelope proved in `IntegralIdentities`. -/
theorem piReciprocalQuarticCompact_equiv_piCircleArea :
    piReciprocalQuarticCompact.Equiv piCircleArea := by
  exact RealRaw.equiv_trans
    piReciprocalQuarticCompact_valid
    IntegralIdentities.cauchyFullLineIntegral_valid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    IntegralIdentities.reciprocalQuarticMinusOneCompactDyadicIntegral_equiv_cauchyFullLine
    cauchyFullLineIntegral_equiv_piCircleArea

/-- The expected value of the clean reciprocal quartic projective integral is a
valid raw real, because it is just the baseline area-pi raw real scaled by `1`. -/
theorem reciprocalQuarticMinusOneExpectedPi_valid :
    IntegralIdentities.reciprocalQuarticMinusOneExpectedPi.Valid := by
  unfold IntegralIdentities.reciprocalQuarticMinusOneExpectedPi
    IntegralIdentities.reciprocalQuarticExpectedPiMultiple
  exact RealRaw.scaleRat_valid_of_nonneg
    (by native_decide : (0 : Rat) <= 1 / 1)
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)

/-- The expected value of the clean reciprocal quartic projective integral is
equivalent to the baseline circle-area pi.  This is only the expected-value
comparison; constructing the improper/projective integral is the remaining
analytic work. -/
theorem reciprocalQuarticMinusOneExpectedPi_equiv_piCircleArea :
    IntegralIdentities.reciprocalQuarticMinusOneExpectedPi.Equiv
      piCircleArea := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    IntegralIdentities.reciprocalQuarticMinusOneExpectedPi piCircleArea n n).2
  have hordered :=
    RealRaw.interval_order_of_valid piCircleArea
      (by simpa [AreaValid] using AreaLoopValidity.areaValid) n
  unfold IntegralIdentities.reciprocalQuarticMinusOneExpectedPi
    IntegralIdentities.reciprocalQuarticExpectedPiMultiple
    RealRaw.scaleRat RealRaw.scaleRatCompute
  have hunit : (1 / (1 : Rat)) = 1 := by native_decide
  have hnonneg : (0 : Rat) <= 1 / (1 : Rat) := by native_decide
  simpa [hunit, hnonneg] using ⟨hordered, hordered⟩

/-- A verified projective-line construction for the clean reciprocal quartic test
would immediately give another formal pi computation once it is proved to agree
with the expected value isolated in `IntegralIdentities`. -/
theorem reciprocalQuarticMinusOneProjectiveRoute_equiv_piCircleArea
    (R : IntegralIdentities.ReciprocalQuarticMinusOneProjectiveRoute) :
    R.projectiveIntegral.Equiv piCircleArea :=
  RealRaw.equiv_trans
    R.projectiveIntegral_valid
    reciprocalQuarticMinusOneExpectedPi_valid
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)
    R.computes_expected
    reciprocalQuarticMinusOneExpectedPi_equiv_piCircleArea

theorem circumferenceValid_of_nested_and_shrinking
    (hnested : CircumferenceNested)
    (hshrink : CircumferenceWidthsShrink) :
    CircumferenceValid := by
  unfold CircumferenceValid RealRaw.ValidCompute
  constructor
  case left =>
    exact piCircumference_ordered
  case right =>
    constructor
    case left =>
      exact hnested
    case right =>
      exact hshrink

theorem circumferenceValid_of_stepRefines_and_linearBound
    (hstep : CircumferenceStepRefines)
    {C : Nat} (hbound : CircumferenceWidthLinearBound C) :
    CircumferenceValid :=
  circumferenceValid_of_nested_and_shrinking
    (circumferenceNested_of_stepRefines hstep)
    (circumferenceWidthsShrink_of_linearBound hbound)

theorem circumferenceValid_of_stepRefines
    (hstep : CircumferenceStepRefines) :
    CircumferenceValid :=
  circumferenceValid_of_nested_and_shrinking
    (circumferenceNested_of_stepRefines hstep)
    circumferenceWidthsShrink

theorem circumferenceValid_of_quarterLengthStepRefines
    (hrefine : CircumferenceQuarterLengthStepRefines) :
    CircumferenceValid :=
  circumferenceValid_of_stepRefines
    (circumferenceStepRefines_of_quarterLengthStepRefines hrefine)

theorem circumferenceValid_of_stepRefinesUpToAll
    (hrefine : forall N, CircumferenceStepRefinesUpTo N) :
    CircumferenceValid :=
  circumferenceValid_of_stepRefines
    (circumferenceStepRefines_of_stepRefinesUpToAll hrefine)

theorem circumferenceValid_of_quarterLengthStepRefinesUpToAll
    (hrefine : forall N, CircumferenceQuarterLengthStepRefinesUpTo N) :
    CircumferenceValid :=
  circumferenceValid_of_stepRefines
    (circumferenceStepRefines_of_quarterLengthStepRefinesUpToAll hrefine)

structure CircumferenceStepRemainders where
  step_refines : CircumferenceStepRefines

structure CircumferenceQuarterLengthRemainders where
  quarter_refines : CircumferenceQuarterLengthStepRefines

structure CircumferenceLinearRemainders where
  step_refines : CircumferenceStepRefines
  width_constant : Nat
  width_bound : CircumferenceWidthLinearBound width_constant

def circumferenceStepRemainders_of_stepRefinesUpToAll
    (hrefine : CircumferenceStepRefinesUpToAll) :
    CircumferenceStepRemainders where
  step_refines := circumferenceStepRefines_of_stepRefinesUpToAll hrefine

def circumferenceQuarterLengthRemainders_of_upToAll
    (hrefine : CircumferenceQuarterLengthStepRefinesUpToAll) :
    CircumferenceQuarterLengthRemainders where
  quarter_refines := circumferenceQuarterLengthStepRefines_of_upToAll hrefine

def circumferenceStepRemainders_of_quarterLengthStepRefinesUpToAll
    (hrefine : CircumferenceQuarterLengthStepRefinesUpToAll) :
    CircumferenceStepRemainders :=
  circumferenceStepRemainders_of_stepRefinesUpToAll
    (circumferenceStepRefinesUpToAll_of_quarterLengthStepRefinesUpToAll
      hrefine)

def CircumferenceQuarterLengthRemainders.toStepRemainders
    (remainders : CircumferenceQuarterLengthRemainders) :
    CircumferenceStepRemainders where
  step_refines :=
    circumferenceStepRefines_of_quarterLengthStepRefines
      remainders.quarter_refines

theorem circumferenceValid_of_quarterLengthRemainders
    (remainders : CircumferenceQuarterLengthRemainders) :
    CircumferenceValid :=
  circumferenceValid_of_quarterLengthStepRefines remainders.quarter_refines

theorem circumferenceValid_of_stepRemainders
    (remainders : CircumferenceStepRemainders) :
    CircumferenceValid :=
  circumferenceValid_of_stepRefines remainders.step_refines

theorem circumferenceValid_of_linearRemainders
    (remainders : CircumferenceLinearRemainders) :
    CircumferenceValid :=
  circumferenceValid_of_stepRefines remainders.step_refines

structure GeometricValidityRemainders where
  area_ordered : AreaOrdered
  area_nested : AreaNested
  area_widths_shrink : AreaWidthsShrink
  circumference_nested : CircumferenceNested
  circumference_widths_shrink : CircumferenceWidthsShrink

def CircumferenceStepRemainders.toGeometricValidityRemainders
    (remainders : CircumferenceStepRemainders) :
    GeometricValidityRemainders where
  area_ordered := AreaLoopValidity.areaOrdered
  area_nested := AreaLoopValidity.areaNested
  area_widths_shrink := AreaLoopValidity.areaWidthsShrink
  circumference_nested :=
    circumferenceNested_of_stepRefines remainders.step_refines
  circumference_widths_shrink := circumferenceWidthsShrink

def CircumferenceQuarterLengthRemainders.toGeometricValidityRemainders
    (remainders : CircumferenceQuarterLengthRemainders) :
    GeometricValidityRemainders :=
  remainders.toStepRemainders.toGeometricValidityRemainders

def CircumferenceLinearRemainders.toGeometricValidityRemainders
    (remainders : CircumferenceLinearRemainders) :
    GeometricValidityRemainders where
  area_ordered := AreaLoopValidity.areaOrdered
  area_nested := AreaLoopValidity.areaNested
  area_widths_shrink := AreaLoopValidity.areaWidthsShrink
  circumference_nested :=
    circumferenceNested_of_stepRefines remainders.step_refines
  circumference_widths_shrink := circumferenceWidthsShrink

structure GeometricStepRemainders where
  area_ordered : AreaOrdered
  area_step_refines : AreaStepRefines
  area_widths_shrink : AreaWidthsShrink
  circumference_step_refines : CircumferenceStepRefines
  circumference_widths_shrink : CircumferenceWidthsShrink

structure GeometricLinearStepRemainders where
  area_ordered : AreaOrdered
  area_step_refines : AreaStepRefines
  area_width_constant : Nat
  area_width_bound : AreaWidthLinearBound area_width_constant
  circumference_step_refines : CircumferenceStepRefines
  circumference_width_constant : Nat
  circumference_width_bound :
    CircumferenceWidthLinearBound circumference_width_constant

theorem geometricStepRemainders_of_linearStepRemainders
    (remainders : GeometricLinearStepRemainders) :
    GeometricStepRemainders where
  area_ordered := remainders.area_ordered
  area_step_refines := remainders.area_step_refines
  area_widths_shrink :=
    areaWidthsShrink_of_linearBound remainders.area_width_bound
  circumference_step_refines := remainders.circumference_step_refines
  circumference_widths_shrink :=
    circumferenceWidthsShrink_of_linearBound
      remainders.circumference_width_bound

theorem geometricValidityRemainders_of_stepRemainders
    (remainders : GeometricStepRemainders) :
    GeometricValidityRemainders where
  area_ordered := remainders.area_ordered
  area_nested :=
    areaNested_of_stepRefines
      remainders.area_ordered remainders.area_step_refines
  area_widths_shrink :=
    remainders.area_widths_shrink
  circumference_nested :=
    circumferenceNested_of_stepRefines
      remainders.circumference_step_refines
  circumference_widths_shrink :=
    remainders.circumference_widths_shrink

theorem validityProofs_of_geometric_remainders
    (remainders : GeometricValidityRemainders) :
    ValidityProofs where
  leibniz := leibnizValid
  machin := machinValid
  area :=
    areaValid_of_nested_and_shrinking
      remainders.area_ordered
      remainders.area_nested
      remainders.area_widths_shrink
  circumference :=
    circumferenceValid_of_nested_and_shrinking
      remainders.circumference_nested
      remainders.circumference_widths_shrink

theorem validityProofs_of_geometric_step_remainders
    (remainders : GeometricStepRemainders) :
    ValidityProofs :=
  validityProofs_of_geometric_remainders
    (geometricValidityRemainders_of_stepRemainders remainders)

theorem validityProofs_of_geometric_linear_step_remainders
    (remainders : GeometricLinearStepRemainders) :
    ValidityProofs :=
  validityProofs_of_geometric_step_remainders
    (geometricStepRemainders_of_linearStepRemainders remainders)

theorem validityProofs_of_circumference_step_remainders
    (remainders : CircumferenceStepRemainders) :
    ValidityProofs :=
  validityProofs_of_geometric_remainders
    remainders.toGeometricValidityRemainders

theorem validityProofs_of_circumference_quarter_length_remainders
    (remainders : CircumferenceQuarterLengthRemainders) :
    ValidityProofs :=
  validityProofs_of_geometric_remainders
    remainders.toGeometricValidityRemainders

theorem validityProofs_of_circumference_linear_remainders
    (remainders : CircumferenceLinearRemainders) :
    ValidityProofs :=
  validityProofs_of_geometric_remainders
    remainders.toGeometricValidityRemainders

/-- A small generating set of agreement proofs.

Once these three bridges are proved, the remaining pairwise equivalences follow
by transitivity, using the validity certificates above. -/
structure AgreementProofs where
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea
  area_eq_circumference : AreaEqCircumference

theorem leibnizEqCircumference_of_validity_and_agreement
    (validity : ValidityProofs) (agreement : AgreementProofs) :
    piLeibniz.Equiv piCircumference :=
  RealRaw.equiv_trans
    validity.leibniz validity.area validity.circumference
    agreement.leibniz_eq_area
    agreement.area_eq_circumference

theorem machinEqArea_of_validity_and_agreement
    (validity : ValidityProofs) (agreement : AgreementProofs) :
    piMachin.Equiv piCircleArea :=
  RealRaw.equiv_trans
    validity.machin validity.leibniz validity.area
    (RealRaw.equiv_symm agreement.leibniz_eq_machin)
    agreement.leibniz_eq_area

theorem machinEqCircumference_of_validity_and_agreement
    (validity : ValidityProofs) (agreement : AgreementProofs) :
    piMachin.Equiv piCircumference :=
  RealRaw.equiv_trans
    validity.machin validity.area validity.circumference
    (machinEqArea_of_validity_and_agreement validity agreement)
    agreement.area_eq_circumference

/-- All pairwise pi-algorithm equivalences derived from the small generating
set and validity certificates. -/
structure PairwiseAgreementProofs where
  leibniz_eq_machin : piLeibniz.Equiv piMachin
  machin_eq_leibniz : piMachin.Equiv piLeibniz
  leibniz_eq_area : piLeibniz.Equiv piCircleArea
  area_eq_leibniz : piCircleArea.Equiv piLeibniz
  area_eq_circumference : piCircleArea.Equiv piCircumference
  circumference_eq_area : piCircumference.Equiv piCircleArea
  leibniz_eq_circumference : piLeibniz.Equiv piCircumference
  circumference_eq_leibniz : piCircumference.Equiv piLeibniz
  machin_eq_area : piMachin.Equiv piCircleArea
  area_eq_machin : piCircleArea.Equiv piMachin
  machin_eq_circumference : piMachin.Equiv piCircumference
  circumference_eq_machin : piCircumference.Equiv piMachin

theorem pairwiseAgreementProofs_of_validity_and_agreement
    (validity : ValidityProofs) (agreement : AgreementProofs) :
    PairwiseAgreementProofs where
  leibniz_eq_machin := agreement.leibniz_eq_machin
  machin_eq_leibniz := RealRaw.equiv_symm agreement.leibniz_eq_machin
  leibniz_eq_area := agreement.leibniz_eq_area
  area_eq_leibniz := RealRaw.equiv_symm agreement.leibniz_eq_area
  area_eq_circumference := agreement.area_eq_circumference
  circumference_eq_area := RealRaw.equiv_symm agreement.area_eq_circumference
  leibniz_eq_circumference :=
    leibnizEqCircumference_of_validity_and_agreement validity agreement
  circumference_eq_leibniz :=
    RealRaw.equiv_symm
      (leibnizEqCircumference_of_validity_and_agreement validity agreement)
  machin_eq_area :=
    machinEqArea_of_validity_and_agreement validity agreement
  area_eq_machin :=
    RealRaw.equiv_symm
      (machinEqArea_of_validity_and_agreement validity agreement)
  machin_eq_circumference :=
    machinEqCircumference_of_validity_and_agreement validity agreement
  circumference_eq_machin :=
    RealRaw.equiv_symm
      (machinEqCircumference_of_validity_and_agreement validity agreement)

structure PiProofsComplete where
  validity : ValidityProofs
  agreement : AgreementProofs

theorem PiProofsComplete.pairwiseAgreement
    (proofs : PiProofsComplete) : PairwiseAgreementProofs :=
  pairwiseAgreementProofs_of_validity_and_agreement
    proofs.validity proofs.agreement

/-- The remaining mathematical obligations needed to close the pi proof layer.

The Archimedes bridge `piCircleArea = piCircumference` is already proved in
this file, the public area loop is already valid, and the Leibniz and Machin
algorithms are already valid.  This legacy package still accepts the full
geometric-validity record for compatibility with callers that already provide
that larger certificate. -/
structure CompletionRemainders where
  area_polygon_agreement : PiCircleAreaPolygonAgreement
  geometric_validity : GeometricValidityRemainders
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

theorem agreementProofs_of_completionRemainders
    (remainders : CompletionRemainders) :
    AgreementProofs where
  leibniz_eq_machin := remainders.leibniz_eq_machin
  leibniz_eq_area := remainders.leibniz_eq_area
  area_eq_circumference :=
    archimedesTheorem remainders.area_polygon_agreement

theorem piProofsComplete_of_completionRemainders
    (remainders : CompletionRemainders) :
    PiProofsComplete where
  validity :=
    validityProofs_of_geometric_remainders
      remainders.geometric_validity
  agreement :=
    agreementProofs_of_completionRemainders remainders

/-- A sharper completion route: prove single-step dyadic refinement plus
width-shrinking for the two geometric algorithms, instead of proving full
nesting directly. -/
structure CompletionStepRemainders where
  area_polygon_agreement : PiCircleAreaPolygonAgreement
  geometric_steps : GeometricStepRemainders
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

def CompletionStepRemainders.toCompletionRemainders
    (remainders : CompletionStepRemainders) : CompletionRemainders where
  geometric_validity :=
    geometricValidityRemainders_of_stepRemainders
      remainders.geometric_steps
  area_polygon_agreement := remainders.area_polygon_agreement
  leibniz_eq_machin := remainders.leibniz_eq_machin
  leibniz_eq_area := remainders.leibniz_eq_area

theorem piProofsComplete_of_stepRemainders
    (remainders : CompletionStepRemainders) :
    PiProofsComplete :=
  piProofsComplete_of_completionRemainders
    remainders.toCompletionRemainders

/-- Fully close the proof package from the finite dyadic refinement
inequalities and linear width estimates, together with the two analytic
bridges to the Leibniz definition. -/
structure CompletionLinearStepRemainders where
  area_polygon_agreement : PiCircleAreaPolygonAgreement
  geometric_linear_steps : GeometricLinearStepRemainders
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

def CompletionLinearStepRemainders.toCompletionStepRemainders
    (remainders : CompletionLinearStepRemainders) :
    CompletionStepRemainders where
  geometric_steps :=
    geometricStepRemainders_of_linearStepRemainders
      remainders.geometric_linear_steps
  area_polygon_agreement := remainders.area_polygon_agreement
  leibniz_eq_machin := remainders.leibniz_eq_machin
  leibniz_eq_area := remainders.leibniz_eq_area

theorem piProofsComplete_of_linearStepRemainders
    (remainders : CompletionLinearStepRemainders) :
    PiProofsComplete :=
  piProofsComplete_of_stepRemainders
    remainders.toCompletionStepRemainders

/-- Legacy circumference completion route.

The public `piCircleArea` validity is already discharged by the
increment/decrement loop.  The circumference width shrinkage is now proved
unconditionally, so the sharper public route below asks only for the
quarter-path endpoint refinement.  This package is retained for callers that
already formulate the target as step refinement plus an explicit width
bound. -/
structure CompletionCircumferenceRemainders where
  area_polygon_agreement : PiCircleAreaPolygonAgreement
  circumference : CircumferenceLinearRemainders
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

def CompletionCircumferenceRemainders.toCompletionRemainders
    (remainders : CompletionCircumferenceRemainders) :
    CompletionRemainders where
  area_polygon_agreement := remainders.area_polygon_agreement
  geometric_validity :=
    remainders.circumference.toGeometricValidityRemainders
  leibniz_eq_machin := remainders.leibniz_eq_machin
  leibniz_eq_area := remainders.leibniz_eq_area

theorem piProofsComplete_of_circumferenceRemainders
    (remainders : CompletionCircumferenceRemainders) :
    PiProofsComplete :=
  piProofsComplete_of_completionRemainders
    remainders.toCompletionRemainders

/-- Sharper public completion route: the area loop and both geometric
width estimates are already verified, so the remaining geometric validity
input is only the one-step dyadic refinement of `piCircumference`. -/
structure CompletionCircumferenceStepRemainders where
  area_polygon_agreement : PiCircleAreaPolygonAgreement
  circumference : CircumferenceStepRemainders
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

def CompletionCircumferenceStepRemainders.toCompletionRemainders
    (remainders : CompletionCircumferenceStepRemainders) :
    CompletionRemainders where
  area_polygon_agreement := remainders.area_polygon_agreement
  geometric_validity :=
    remainders.circumference.toGeometricValidityRemainders
  leibniz_eq_machin := remainders.leibniz_eq_machin
  leibniz_eq_area := remainders.leibniz_eq_area

theorem piProofsComplete_of_circumferenceStepRemainders
    (remainders : CompletionCircumferenceStepRemainders) :
    PiProofsComplete :=
  piProofsComplete_of_completionRemainders
    remainders.toCompletionRemainders

/-- Table-facing completion route, phrased in terms of the two quarter-path
endpoint inequalities that imply public circumference step refinement. -/
structure CompletionCircumferenceQuarterLengthRemainders where
  area_polygon_agreement : PiCircleAreaPolygonAgreement
  circumference : CircumferenceQuarterLengthRemainders
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

def CompletionCircumferenceQuarterLengthRemainders.toCompletionRemainders
    (remainders : CompletionCircumferenceQuarterLengthRemainders) :
    CompletionRemainders where
  area_polygon_agreement := remainders.area_polygon_agreement
  geometric_validity :=
    remainders.circumference.toGeometricValidityRemainders
  leibniz_eq_machin := remainders.leibniz_eq_machin
  leibniz_eq_area := remainders.leibniz_eq_area

theorem piProofsComplete_of_circumferenceQuarterLengthRemainders
    (remainders : CompletionCircumferenceQuarterLengthRemainders) :
    PiProofsComplete :=
  piProofsComplete_of_completionRemainders
    remainders.toCompletionRemainders

/-- Completion route whose only circumference input is the family of all finite
step-refinement prefixes. -/
structure CompletionCircumferenceStepRefinesUpToAllRemainders where
  area_polygon_agreement : PiCircleAreaPolygonAgreement
  circumference : CircumferenceStepRefinesUpToAll
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

def CompletionCircumferenceStepRefinesUpToAllRemainders.toCompletionRemainders
    (remainders : CompletionCircumferenceStepRefinesUpToAllRemainders) :
    CompletionRemainders where
  area_polygon_agreement := remainders.area_polygon_agreement
  geometric_validity :=
    (circumferenceStepRemainders_of_stepRefinesUpToAll
      remainders.circumference).toGeometricValidityRemainders
  leibniz_eq_machin := remainders.leibniz_eq_machin
  leibniz_eq_area := remainders.leibniz_eq_area

theorem piProofsComplete_of_circumferenceStepRefinesUpToAllRemainders
    (remainders : CompletionCircumferenceStepRefinesUpToAllRemainders) :
    PiProofsComplete :=
  piProofsComplete_of_completionRemainders
    remainders.toCompletionRemainders

/-- Completion route whose circumference input is the quarter-length version of
all finite step-refinement prefixes. -/
structure CompletionCircumferenceQuarterLengthUpToAllRemainders where
  area_polygon_agreement : PiCircleAreaPolygonAgreement
  circumference : CircumferenceQuarterLengthStepRefinesUpToAll
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

def CompletionCircumferenceQuarterLengthUpToAllRemainders.toCompletionRemainders
    (remainders : CompletionCircumferenceQuarterLengthUpToAllRemainders) :
    CompletionRemainders where
  area_polygon_agreement := remainders.area_polygon_agreement
  geometric_validity :=
    (circumferenceStepRemainders_of_quarterLengthStepRefinesUpToAll
      remainders.circumference).toGeometricValidityRemainders
  leibniz_eq_machin := remainders.leibniz_eq_machin
  leibniz_eq_area := remainders.leibniz_eq_area

theorem piProofsComplete_of_circumferenceQuarterLengthUpToAllRemainders
    (remainders : CompletionCircumferenceQuarterLengthUpToAllRemainders) :
    PiProofsComplete :=
  piProofsComplete_of_completionRemainders
    remainders.toCompletionRemainders

theorem piProofsComplete_of_kernelComparisonRoute
    (hpoly : PiCircleAreaPolygonAgreement)
    (geometric_validity : GeometricValidityRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PiProofsComplete :=
  piProofsComplete_of_completionRemainders
    { area_polygon_agreement := hpoly
      geometric_validity := geometric_validity
      leibniz_eq_machin :=
        leibnizEqMachin_of_kernelComparisonRoute route hgeom
      leibniz_eq_area :=
        leibnizEqArea_of_kernelComparisonRoute route }

theorem piProofsComplete_of_circumferenceRemainders_and_kernelComparisonRoute
    (hpoly : PiCircleAreaPolygonAgreement)
    (circumference : CircumferenceLinearRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PiProofsComplete :=
  piProofsComplete_of_circumferenceRemainders
    { area_polygon_agreement := hpoly
      circumference := circumference
      leibniz_eq_machin :=
        leibnizEqMachin_of_kernelComparisonRoute route hgeom
      leibniz_eq_area :=
        leibnizEqArea_of_kernelComparisonRoute route }

theorem piProofsComplete_of_circumferenceStepRemainders_and_kernelComparisonRoute
    (hpoly : PiCircleAreaPolygonAgreement)
    (circumference : CircumferenceStepRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PiProofsComplete :=
  piProofsComplete_of_circumferenceStepRemainders
    { area_polygon_agreement := hpoly
      circumference := circumference
      leibniz_eq_machin :=
        leibnizEqMachin_of_kernelComparisonRoute route hgeom
      leibniz_eq_area :=
        leibnizEqArea_of_kernelComparisonRoute route }

theorem piProofsComplete_of_circumferenceQuarterLengthRemainders_and_kernelComparisonRoute
    (hpoly : PiCircleAreaPolygonAgreement)
    (circumference : CircumferenceQuarterLengthRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PiProofsComplete :=
  piProofsComplete_of_circumferenceQuarterLengthRemainders
    { area_polygon_agreement := hpoly
      circumference := circumference
      leibniz_eq_machin :=
        leibnizEqMachin_of_kernelComparisonRoute route hgeom
      leibniz_eq_area :=
        leibnizEqArea_of_kernelComparisonRoute route }

theorem piProofsComplete_of_stepRemainders_and_kernelComparisonRoute
    (hpoly : PiCircleAreaPolygonAgreement)
    (geometric_steps : GeometricStepRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PiProofsComplete :=
  piProofsComplete_of_kernelComparisonRoute
    hpoly
    (geometricValidityRemainders_of_stepRemainders geometric_steps)
    route
    hgeom

theorem piProofsComplete_of_linearStepRemainders_and_kernelComparisonRoute
    (hpoly : PiCircleAreaPolygonAgreement)
    (geometric_linear_steps : GeometricLinearStepRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PiProofsComplete :=
  piProofsComplete_of_stepRemainders_and_kernelComparisonRoute
    hpoly
    (geometricStepRemainders_of_linearStepRemainders
      geometric_linear_steps)
    route
    hgeom

theorem pairwiseAgreementProofs_of_completionRemainders
    (remainders : CompletionRemainders) :
    PairwiseAgreementProofs :=
  PiProofsComplete.pairwiseAgreement
    (piProofsComplete_of_completionRemainders remainders)

theorem pairwiseAgreementProofs_of_stepRemainders
    (remainders : CompletionStepRemainders) :
    PairwiseAgreementProofs :=
  PiProofsComplete.pairwiseAgreement
    (piProofsComplete_of_stepRemainders remainders)

theorem pairwiseAgreementProofs_of_linearStepRemainders
    (remainders : CompletionLinearStepRemainders) :
    PairwiseAgreementProofs :=
  PiProofsComplete.pairwiseAgreement
    (piProofsComplete_of_linearStepRemainders remainders)

theorem pairwiseAgreementProofs_of_kernelComparisonRoute
    (hpoly : PiCircleAreaPolygonAgreement)
    (geometric_validity : GeometricValidityRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PairwiseAgreementProofs :=
  PiProofsComplete.pairwiseAgreement
    (piProofsComplete_of_kernelComparisonRoute
      hpoly geometric_validity route hgeom)

theorem pairwiseAgreementProofs_of_stepRemainders_and_kernelComparisonRoute
    (hpoly : PiCircleAreaPolygonAgreement)
    (geometric_steps : GeometricStepRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PairwiseAgreementProofs :=
  PiProofsComplete.pairwiseAgreement
    (piProofsComplete_of_stepRemainders_and_kernelComparisonRoute
      hpoly geometric_steps route hgeom)

theorem pairwiseAgreementProofs_of_linearStepRemainders_and_kernelComparisonRoute
    (hpoly : PiCircleAreaPolygonAgreement)
    (geometric_linear_steps : GeometricLinearStepRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PairwiseAgreementProofs :=
  PiProofsComplete.pairwiseAgreement
    (piProofsComplete_of_linearStepRemainders_and_kernelComparisonRoute
      hpoly geometric_linear_steps route hgeom)

/-- Each tangent edge at a positive stage has a bisection-width budget of
`2 / 2^(stage + 9)`.  This sharper local bound is used to compare the
square-root enclosure error with the strict dyadic decrease of the exact
outer tangent fan. -/
private theorem outerAdjacentTangentFormulaBudgetLe_sharp
    (stage : Nat) (hstage : 0 < stage) :
    OuterAdjacentTangentFormulaBudgetLe stage
      (2 / (((2 ^ (stage + 9) : Nat) : Rat)) ) := by
  intro k
  constructor
  · exact formulaBudgetLeAt_of_sqrtUpperBound_le_two
      (Nat.ne_of_gt hstage)
      (sqrtUpperBound_le_two_of_le_two
        (entryTangentNormSqFormula_le_two stage hstage k))
      Rat.le_refl
  · exact formulaBudgetLeAt_of_sqrtUpperBound_le_two
      (Nat.ne_of_gt hstage)
      (sqrtUpperBound_le_two_of_le_two
        (exitTangentNormSqFormula_le_two stage hstage k))
      Rat.le_refl

/-- The whole outer tangent path at stage `stage` has at most twice as many
segment-width budgets as tangent cells. -/
theorem outerQuarterLength_width_le_sharp
    (stage : Nat) (hstage : 0 < stage) :
    (outerQuarterLength stage).width <=
      ((2 * stage : Nat) : Rat) *
        (2 / (((2 ^ (stage + 9) : Nat) : Rat))) := by
  let B : Rat := 2 / (((2 ^ (stage + 9) : Nat) : Rat))
  have hadj : OuterAdjacentSegmentBudgetLe stage B :=
    outerAdjacentSegmentBudgetLe_of_tangentFormulaBudget hstage
      (outerAdjacentTangentFormulaBudgetLe_sharp stage hstage)
  have hboundary : OuterBoundarySegmentBudgetLe stage B :=
    outerBoundarySegmentBudgetLe_of_adjacent hadj
  have hbudget := pathSegmentWidthBudget_le_count_mul stage B
    (outerBoundary stage) hboundary
  rw [pathSegmentCount_outerBoundary] at hbudget
  change (rationalPointPathLength (outerBoundary stage) stage).width <= _
  rw [rationalPointPathLength_width_eq_segmentBudget]
  exact hbudget

private theorem outerTangentZeroGapAlgebra
    (N : Rat) (hN : 0 < N) :
    2 * (N / (2 * N * N)) +
        2 * (N / (2 * N * N + 1)) +
        1 / (N * (2 * N * N + 1)) =
      2 * (N / (N * N)) := by
  have hNne : N ≠ 0 := Rat.ne_of_gt hN
  have hfirst : 2 * (N / (2 * N * N)) = 1 / N := by
    rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev, Rat.inv_mul_rev]
    have hNcancel : N * N⁻¹ = 1 := Rat.mul_inv_cancel N hNne
    have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by native_decide
    grind [Rat.mul_assoc, Rat.mul_comm]
  let D : Rat := 2 * N * N + 1
  have hDpos : 0 < D := by
    dsimp [D]
    have hNN : 0 <= N * N :=
      Rat.mul_nonneg (Rat.le_of_lt hN) (Rat.le_of_lt hN)
    grind
  have hDne : D ≠ 0 := Rat.ne_of_gt hDpos
  rw [hfirst]
  change 1 / N + 2 * (N / D) + 1 / (N * D) =
    2 * (N / (N * N))
  apply tangentRefinement_cancel_mul_right
    (Rat.ne_of_gt (Rat.mul_pos hN hDpos))
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  rw [Rat.inv_mul_rev, Rat.inv_mul_rev]
  have hNcancel : N * N⁻¹ = 1 := Rat.mul_inv_cancel N hNne
  have hDcancel : D * D⁻¹ = 1 := Rat.mul_inv_cancel D hDne
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

/-- The first outer tangent cell decreases by an explicit positive rational
amount under dyadic subdivision. -/
theorem outerTangentCrossSum_zero_refinesByDoubling_withGap
    (stage : Nat) (hstage : 0 < stage) :
    outerTangentCrossSum (2 * stage) 0 +
        outerTangentCrossSum (2 * stage) 1 +
        1 / ((stage : Rat) *
          (2 * (stage : Rat) * (stage : Rat) + 1)) =
      outerTangentCrossSum stage 0 := by
  have hfine : 0 < 2 * stage := by omega
  rw [outerTangentCrossSum_eq_two_adjacentTangentCrossFormula (2 * stage)
      hfine 0,
    outerTangentCrossSum_eq_two_adjacentTangentCrossFormula (2 * stage)
      hfine 1,
    outerTangentCrossSum_eq_two_adjacentTangentCrossFormula stage hstage 0,
    adjacentTangentCrossFormula_eq_closedForm (2 * stage) hfine 0,
    adjacentTangentCrossFormula_eq_closedForm (2 * stage) hfine 1,
    adjacentTangentCrossFormula_eq_closedForm stage hstage 0,
    adjacentTangentCrossClosedForm_double_left stage 0,
    adjacentTangentCrossClosedForm_double_right stage 0]
  simpa [adjacentTangentCrossClosedForm, Rat.natCast_mul,
    Rat.natCast_add, Rat.add_zero, Rat.zero_add, Rat.mul_zero, Rat.zero_mul] using
    outerTangentZeroGapAlgebra (stage : Rat)
      ((Rat.natCast_pos).2 hstage)

private theorem outerTangentCrossSumFrom_refinesByDoubling_withZeroGap
    (stage : Nat) (hstage : 0 < stage) :
    outerTangentCrossSumFrom (2 * stage) 0 (2 * stage) +
        1 / ((stage : Rat) *
          (2 * (stage : Rat) * (stage : Rat) + 1)) <=
      outerTangentCrossSumFrom stage 0 stage := by
  have hfirst := outerTangentCrossSum_zero_refinesByDoubling_withGap
    stage hstage
  have htail := outerTangentCrossSumFrom_refinesByDoubling_aux
    stage hstage (stage - 1) 1
  have hfine :
      outerTangentCrossSumFrom (2 * stage) 0 (2 * stage) =
        outerTangentCrossSum (2 * stage) 0 +
          (outerTangentCrossSum (2 * stage) 1 +
            outerTangentCrossSumFrom (2 * stage) 2 (2 * (stage - 1))) := by
    calc
      outerTangentCrossSumFrom (2 * stage) 0 (2 * stage) =
          outerTangentCrossSumFrom (2 * stage) 0
            (Nat.succ (Nat.succ (2 * (stage - 1)))) := by
              exact congrArg
                (fun count => outerTangentCrossSumFrom (2 * stage) 0 count)
                (by omega)
      _ = outerTangentCrossSum (2 * stage) 0 +
            (outerTangentCrossSum (2 * stage) 1 +
              outerTangentCrossSumFrom (2 * stage) 2 (2 * (stage - 1))) := by
              simp [outerTangentCrossSumFrom]
  have hcoarse :
      outerTangentCrossSumFrom stage 0 stage =
        outerTangentCrossSum stage 0 +
          outerTangentCrossSumFrom stage 1 (stage - 1) := by
    calc
      outerTangentCrossSumFrom stage 0 stage =
          outerTangentCrossSumFrom stage 0 (Nat.succ (stage - 1)) := by
            exact congrArg (fun count => outerTangentCrossSumFrom stage 0 count)
              (by omega)
      _ = outerTangentCrossSum stage 0 +
            outerTangentCrossSumFrom stage 1 (stage - 1) := by
            simp [outerTangentCrossSumFrom]
  calc
    outerTangentCrossSumFrom (2 * stage) 0 (2 * stage) +
          1 / ((stage : Rat) *
            (2 * (stage : Rat) * (stage : Rat) + 1)) =
        (outerTangentCrossSum (2 * stage) 0 +
          outerTangentCrossSum (2 * stage) 1 +
          1 / ((stage : Rat) *
            (2 * (stage : Rat) * (stage : Rat) + 1))) +
          outerTangentCrossSumFrom (2 * stage) 2 (2 * (stage - 1)) := by
          rw [hfine]
          grind [Rat.add_assoc, Rat.add_comm]
    _ = outerTangentCrossSum stage 0 +
          outerTangentCrossSumFrom (2 * stage) 2 (2 * (stage - 1)) := by
          rw [hfirst]
    _ <= outerTangentCrossSum stage 0 +
          outerTangentCrossSumFrom stage 1 (stage - 1) := by
          rw [Rat.add_le_add_left]
          exact htail
    _ = outerTangentCrossSumFrom stage 0 stage := hcoarse.symm

/-- The exact outer tangent fan decreases by a positive, explicit first-cell
gap at every positive dyadic stage. -/
theorem outerFanPerimeter_refinesByDoubling_withZeroGap
    (stage : Nat) (hstage : 0 < stage) :
    Fan.perimeter (outerFanWidths (2 * stage)) +
        1 / ((stage : Rat) *
          (2 * (stage : Rat) * (stage : Rat) + 1)) <=
      Fan.perimeter (outerFanWidths stage) := by
  rw [outerFanPerimeter_eq_outerTangentCrossSumFrom,
    outerFanPerimeter_eq_outerTangentCrossSumFrom]
  exact outerTangentCrossSumFrom_refinesByDoubling_withZeroGap stage hstage

private theorem two_mul_le_piStage_add_two (n : Nat) :
    2 * n <= piStage n + 2 := by
  unfold piStage
  induction n with
  | zero => native_decide
  | succ n ih =>
      cases n with
      | zero => native_decide
      | succ n =>
          have hpow : 2 <= 2 ^ (n + 1) := by
            rw [Nat.pow_succ]
            have hpos : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
            omega
          calc
            2 * (n + 1 + 1) = 2 * (n + 1) + 2 := by omega
            _ <= (2 ^ (n + 1) + 2) + 2 := Nat.add_le_add_right ih 2
            _ <= 2 * (2 ^ (n + 1)) + 2 := by omega
            _ = 2 ^ (n + 1 + 1) + 2 := by
              rw [Nat.pow_succ]
              omega

private theorem outerWidthNumerator_le_dyadicMesh (n : Nat) :
    8 * piStage n * piStage n *
        (2 * piStage n * piStage n + 1) <=
      2 ^ (2 * piStage n + 9) := by
  let S := piStage n
  have hSpos : 0 < S := piStage_pos n
  have hSSpos : 0 < S * S := Nat.mul_pos hSpos hSpos
  have hone : 1 <= S * S := hSSpos
  have hfactor : 2 * S * S + 1 <= 3 * S * S := by
    calc
      2 * S * S + 1 <= 2 * S * S + S * S :=
        Nat.add_le_add_left hone _
      _ = 2 * (S * S) + S * S := by simp [Nat.mul_assoc]
      _ = 3 * (S * S) := by omega
      _ = 3 * S * S := by simp [Nat.mul_assoc]
  have hpoly :
      8 * S * S * (2 * S * S + 1) <= 24 * (S * S * S * S) := by
    calc
      8 * S * S * (2 * S * S + 1) <=
          8 * S * S * (3 * S * S) :=
        Nat.mul_le_mul_left (8 * S * S) hfactor
      _ = (8 * 3) * (S * S * S * S) := by ac_rfl
      _ = 24 * (S * S * S * S) := rfl
  have hSfour : S * S * S * S = 2 ^ (4 * n) := by
    dsimp [S, piStage]
    calc
      2 ^ n * 2 ^ n * 2 ^ n * 2 ^ n =
          (2 ^ n * 2 ^ n) * (2 ^ n * 2 ^ n) := by ac_rfl
      _ = 2 ^ (n + n) * 2 ^ (n + n) := by
            rw [Nat.pow_add]
      _ = 2 ^ ((n + n) + (n + n)) := by
            exact (Nat.pow_add 2 (n + n) (n + n)).symm
      _ = 2 ^ (4 * n) := by congr 1 <;> omega
  have hconst : 24 * (2 ^ (4 * n)) <= 2 ^ (4 * n + 5) := by
    calc
      24 * (2 ^ (4 * n)) <= 32 * (2 ^ (4 * n)) :=
        Nat.mul_le_mul_right _ (by native_decide)
      _ = 2 ^ (4 * n) * 2 ^ 5 := by
        have hfive : 2 ^ 5 = 32 := by native_decide
        rw [hfive]
        ac_rfl
      _ = 2 ^ (4 * n + 5) := by rw [← Nat.pow_add]
  have hexp : 4 * n + 5 <= 2 * S + 9 := by
    have htwo := two_mul_le_piStage_add_two n
    omega
  change 8 * S * S * (2 * S * S + 1) <= 2 ^ (2 * S + 9)
  calc
    8 * S * S * (2 * S * S + 1) <= 24 * (S * S * S * S) := hpoly
    _ = 24 * (2 ^ (4 * n)) := by rw [hSfour]
    _ <= 2 ^ (4 * n + 5) := hconst
    _ <= 2 ^ (2 * S + 9) :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hexp

private theorem outerWidthBudget_le_outerFanZeroGap (n : Nat) :
    (((4 * piStage n : Nat) : Rat) *
      (2 / (((2 ^ (2 * piStage n + 9) : Nat) : Rat)))) <=
      1 / (((piStage n : Nat) : Rat) *
        (2 * ((piStage n : Nat) : Rat) * ((piStage n : Nat) : Rat) + 1)) := by
  let S := piStage n
  let A : Nat := 2 ^ (2 * S + 9)
  let B : Rat := (S : Rat) *
    (2 * (S : Rat) * (S : Rat) + 1)
  have hSpos : 0 < S := piStage_pos n
  have hApos : 0 < A := Nat.pow_pos (by omega : 0 < 2)
  have hBpos : 0 < B := by
    dsimp [B]
    have hSnonneg : 0 <= (S : Rat) :=
      Rat.le_of_lt ((Rat.natCast_pos).2 hSpos)
    have hsq : 0 <= (S : Rat) * (S : Rat) :=
      Rat.mul_nonneg hSnonneg hSnonneg
    have hterm : 0 < 2 * (S : Rat) * (S : Rat) + 1 := by
      have hscaled : 0 <= 2 * ((S : Rat) * (S : Rat)) :=
        Rat.mul_nonneg (by native_decide) hsq
      have hnonneg : 0 <= 2 * (S : Rat) * (S : Rat) := by
        simpa [Rat.mul_assoc] using hscaled
      grind
    exact Rat.mul_pos ((Rat.natCast_pos).2 hSpos) hterm
  have hnum : 8 * S * S * (2 * S * S + 1) <= A := by
    dsimp [A]
    simpa [S] using outerWidthNumerator_le_dyadicMesh n
  change ((4 * S : Nat) : Rat) * (2 / (A : Rat)) <= 1 / B
  apply Rat.le_of_mul_le_mul_right (c := (A : Rat) * B)
  · rw [Rat.div_def, Rat.div_def]
    have hAne : (A : Rat) ≠ 0 :=
      Rat.ne_of_gt ((Rat.natCast_pos).2 hApos)
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    calc
      (((4 * S : Nat) : Rat) * (2 * (A : Rat)⁻¹)) *
          ((A : Rat) * B) =
        ((8 * S * S * (2 * S * S + 1) : Nat) : Rat) := by
          simp only [B, Rat.natCast_mul, Rat.natCast_add]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (A : Rat) := by exact_mod_cast hnum
      _ = (1 * B⁻¹) * ((A : Rat) * B) := by
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos ((Rat.natCast_pos).2 hApos) hBpos

private theorem piStage_succ_eq_two_mul (n : Nat) :
    piStage (n + 1) = 2 * piStage n := by
  unfold piStage
  rw [Nat.pow_succ]
  omega

private theorem outerQuarterLength_hi_le_outerFan_add_width
    (stage : Nat) (hstage : 0 < stage) :
    (outerQuarterLength stage).hi <=
      Fan.perimeter (outerFanWidths stage) +
        (outerQuarterLength stage).width := by
  have hlo := outerQuarterLength_lo_le_outerFanPerimeter stage hstage
  unfold QInterval.width
  change (outerQuarterLength stage).hi <=
    Fan.perimeter (outerFanWidths stage) +
      ((outerQuarterLength stage).hi - (outerQuarterLength stage).lo)
  grind [Rat.sub_eq_add_neg]

/-- The upper endpoint of the direct circumscribed perimeter path is antitone
at every public dyadic stage.  The proof combines the strict rational tangent
fan decrease with a certified exponential square-root enclosure budget. -/
theorem outerQuarterLength_hi_refinesByDyadicStage (n : Nat) :
    (outerQuarterLength (piStage (n + 1))).hi <=
      (outerQuarterLength (piStage n)).hi := by
  let stage := piStage n
  have hstage : 0 < stage := piStage_pos n
  have hstage_next : piStage (n + 1) = 2 * stage := by
    dsimp [stage]
    exact piStage_succ_eq_two_mul n
  rw [hstage_next]
  have hwidth := outerQuarterLength_width_le_sharp (2 * stage) (by omega)
  have hbudget := outerWidthBudget_le_outerFanZeroGap n
  have hwidth_gap :
      (outerQuarterLength (2 * stage)).width <=
        1 / ((stage : Rat) *
          (2 * (stage : Rat) * (stage : Rat) + 1)) := by
    calc
      (outerQuarterLength (2 * stage)).width <=
          ((2 * (2 * stage) : Nat) : Rat) *
            (2 / (((2 ^ (2 * stage + 9) : Nat) : Rat))) := hwidth
      _ = ((4 * stage : Nat) : Rat) *
            (2 / (((2 ^ (2 * stage + 9) : Nat) : Rat))) := by
            congr 2 <;> omega
      _ <= 1 / ((stage : Rat) *
          (2 * (stage : Rat) * (stage : Rat) + 1)) := by
            simpa [stage] using hbudget
  have hfan := outerFanPerimeter_refinesByDoubling_withZeroGap stage hstage
  calc
    (outerQuarterLength (2 * stage)).hi <=
        Fan.perimeter (outerFanWidths (2 * stage)) +
          (outerQuarterLength (2 * stage)).width :=
      outerQuarterLength_hi_le_outerFan_add_width (2 * stage) (by omega)
    _ <= Fan.perimeter (outerFanWidths (2 * stage)) +
        1 / ((stage : Rat) *
          (2 * (stage : Rat) * (stage : Rat) + 1)) :=
      (Rat.add_le_add_left).2 hwidth_gap
    _ <= Fan.perimeter (outerFanWidths stage) := hfan
    _ <= (outerQuarterLength stage).hi :=
      outerFanPerimeter_le_outerQuarterLength_hi stage hstage

/-- Splitting a directed chord through a unit point gives the usual
angle-addition identity for rational cross products. -/
private theorem pointCross_split_through_unit
    (p mid q : PiCirclePoint)
    (hmid : RationalCircle.Stage.normSq mid = 1) :
    pointCross p q =
      pointCross p mid * RationalCircle.Stage.dot mid q +
        RationalCircle.Stage.dot p mid * pointCross mid q := by
  unfold pointCross RationalCircle.Stage.dot
    RationalCircle.Stage.normSq at *
  grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

private theorem circleSamplePoint_dot_le_one
    (stage i j : Nat) :
    RationalCircle.Stage.dot (circleSamplePoint stage i)
      (circleSamplePoint stage j) <= 1 := by
  have h := RationalCircle.Stage.one_sub_point_dot_nonneg
    (circleParameter stage i) (circleParameter stage j)
  change RationalCircle.Stage.dot (RationalCircle.Stage.point
      (circleParameter stage i)) (RationalCircle.Stage.point
      (circleParameter stage j)) <= 1
  grind [Rat.sub_eq_add_neg]

/-- Consecutive samples of a positive rational-circle stage have nonnegative
dot product.  The proof is entirely in the rational chart: their parameter
increment is `1 / stage`, hence at most one. -/
theorem circleSamplePoint_dot_nonneg_adjacent
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    0 <= RationalCircle.Stage.dot
      (circleSamplePoint stage k) (circleSamplePoint stage (k + 1)) := by
  let u := circleParameter stage k
  let v := circleParameter stage (k + 1)
  have hu : 0 <= u := by
    dsimp [u]
    exact circleParameter_nonneg stage hstage k
  have hv : 0 <= v := by
    dsimp [v]
    exact circleParameter_nonneg stage hstage (k + 1)
  have hstep_eq : v - u = 1 / (stage : Rat) := by
    dsimp [u, v]
    exact circleParameter_succ_sub stage k
  have hstep : 0 <= v - u := by
    rw [hstep_eq, Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hstage))
  have hstep_one : v - u <= 1 := by
    rw [hstep_eq]
    have hone : (1 / (1 : Rat)) = 1 := by
      native_decide
    simpa [hone] using
      (FTC.one_div_nat_antitone (n := 1) (m := stage)
        (by omega) hstage (by omega : 1 <= stage))
  simpa [circleSamplePoint, circlePoint, u, v,
    RationalCircle.Stage.point] using
    RationalCircle.Stage.point_dot_nonneg_of_step_le_one hu hv hstep hstep_one

/-- The curvature lower certificate for any consecutive rational-circle chord
survives a finite square-root bisection with only its displayed width lost. -/
theorem adjacentCurvatureChordLower_sub_width_le_segment_lo
    (stage : Nat) (hstage : 0 < stage) (k precision : Nat) :
    curvatureChordLower (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) -
        (pointSegmentLengthInterval
          (circleSamplePoint stage k)
          (circleSamplePoint stage (k + 1)) precision).width <=
      (pointSegmentLengthInterval
        (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) precision).lo := by
  apply curvatureChordLower_sub_width_le_segment_lo_of_unit
  · exact RationalCircle.Stage.samplePoint_normSq_unit
      (rationalCircleStage stage) k
  · exact RationalCircle.Stage.samplePoint_normSq_unit
      (rationalCircleStage stage) (k + 1)
  · exact circleSamplePoint_cross_nonneg_of_order stage hstage (by omega)
  · exact circleSamplePoint_dot_nonneg_adjacent stage hstage k
  · have h := circleSamplePoint_dot_le_one stage k (k + 1)
    grind [Rat.sub_eq_add_neg]

/-- The rational cross-product fan of the inscribed chords increases when an
adjacent chord is split at the dyadic parameter midpoint. -/
theorem adjacentChordCross_refinesByDoubling
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    pointCross (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) <=
      pointCross (circleSamplePoint (2 * stage) (2 * k))
        (circleSamplePoint (2 * stage) (2 * k + 1)) +
      pointCross (circleSamplePoint (2 * stage) (2 * k + 1))
        (circleSamplePoint (2 * stage) (2 * k + 2)) := by
  let fine := 2 * stage
  let p := circleSamplePoint fine (2 * k)
  let mid := circleSamplePoint fine (2 * k + 1)
  let q := circleSamplePoint fine (2 * k + 2)
  have hfine : 0 < fine := by
    dsimp [fine]
    omega
  have hpm : 0 <= pointCross p mid := by
    dsimp [p, mid]
    exact circleSamplePoint_cross_nonneg_of_order fine hfine (by omega)
  have hmq : 0 <= pointCross mid q := by
    dsimp [mid, q]
    exact circleSamplePoint_cross_nonneg_of_order fine hfine (by omega)
  have hmid : RationalCircle.Stage.normSq mid = 1 := by
    dsimp [mid]
    exact RationalCircle.Stage.samplePoint_normSq_unit
      (rationalCircleStage fine) (2 * k + 1)
  have hdot_right : RationalCircle.Stage.dot mid q <= 1 := by
    dsimp [mid, q]
    exact circleSamplePoint_dot_le_one fine (2 * k + 1) (2 * k + 2)
  have hdot_left : RationalCircle.Stage.dot p mid <= 1 := by
    dsimp [p, mid]
    exact circleSamplePoint_dot_le_one fine (2 * k) (2 * k + 1)
  have hsplit := pointCross_split_through_unit p mid q hmid
  have hcoarse :
      pointCross (circleSamplePoint stage k)
          (circleSamplePoint stage (k + 1)) = pointCross p q := by
    dsimp [p, q, fine]
    rw [circleSamplePoint_double_index,
      circleSamplePoint_double_index_succ]
  rw [hcoarse, hsplit]
  calc
    pointCross p mid * RationalCircle.Stage.dot mid q +
        RationalCircle.Stage.dot p mid * pointCross mid q <=
      pointCross p mid * 1 + 1 * pointCross mid q := by
        calc
          pointCross p mid * RationalCircle.Stage.dot mid q +
              RationalCircle.Stage.dot p mid * pointCross mid q <=
            pointCross p mid * 1 +
              RationalCircle.Stage.dot p mid * pointCross mid q :=
              Rat.add_le_add_right.mpr
                (Rat.mul_le_mul_of_nonneg_left hdot_right hpm)
          _ <= pointCross p mid * 1 + 1 * pointCross mid q :=
              Rat.add_le_add_left.mpr
                (Rat.mul_le_mul_of_nonneg_right hdot_left hmq)
    _ = pointCross p mid + pointCross mid q := by grind

/-- The exact rational cross-product perimeter of a consecutive block of
inscribed chord cells. -/
def innerChordCrossSumFrom (stage k : Nat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      pointCross (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) +
      innerChordCrossSumFrom stage (k + 1) count

private theorem innerChordCrossSumFrom_refinesByDoubling_aux
    (stage : Nat) (hstage : 0 < stage) (count k : Nat) :
    innerChordCrossSumFrom stage k count <=
      innerChordCrossSumFrom (2 * stage) (2 * k) (2 * count) := by
  induction count generalizing k with
  | zero =>
      simp [innerChordCrossSumFrom]
  | succ count ih =>
      have hlocal := adjacentChordCross_refinesByDoubling stage hstage k
      have htail := ih (k + 1)
      rw [show 2 * (count + 1) = 2 * count + 2 by omega]
      simp only [innerChordCrossSumFrom]
      have htail' :
          innerChordCrossSumFrom stage (k + 1) count <=
            innerChordCrossSumFrom (2 * stage) (2 * k + 1 + 1)
              (2 * count) := by
        have hindex : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
        rw [hindex] at htail
        exact htail
      calc
        pointCross (circleSamplePoint stage k)
            (circleSamplePoint stage (k + 1)) +
            innerChordCrossSumFrom stage (k + 1) count <=
          (pointCross (circleSamplePoint (2 * stage) (2 * k))
              (circleSamplePoint (2 * stage) (2 * k + 1)) +
            pointCross (circleSamplePoint (2 * stage) (2 * k + 1))
              (circleSamplePoint (2 * stage) (2 * k + 2))) +
            innerChordCrossSumFrom stage (k + 1) count :=
          Rat.add_le_add_right.mpr hlocal
        _ <=
          (pointCross (circleSamplePoint (2 * stage) (2 * k))
              (circleSamplePoint (2 * stage) (2 * k + 1)) +
            pointCross (circleSamplePoint (2 * stage) (2 * k + 1))
              (circleSamplePoint (2 * stage) (2 * k + 2))) +
            innerChordCrossSumFrom (2 * stage) (2 * k + 1 + 1)
              (2 * count) :=
          Rat.add_le_add_left.mpr htail'
        _ =
          pointCross (circleSamplePoint (2 * stage) (2 * k))
              (circleSamplePoint (2 * stage) (2 * k + 1)) +
            (pointCross (circleSamplePoint (2 * stage) (2 * k + 1))
              (circleSamplePoint (2 * stage) (2 * k + 2)) +
              innerChordCrossSumFrom (2 * stage) (2 * k + 2)
                (2 * count)) := by
          rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega]
          grind [Rat.add_assoc, Rat.add_comm]

theorem innerChordCrossSumFrom_refinesByDoubling
    (stage : Nat) (hstage : 0 < stage) (count k : Nat) :
    innerChordCrossSumFrom stage k count <=
      innerChordCrossSumFrom (2 * stage) (2 * k) (2 * count) :=
  innerChordCrossSumFrom_refinesByDoubling_aux stage hstage count k

private theorem innerChordCrossSumFrom_eq_edgeCrossPerimeter
    (stage count k : Nat) :
    innerChordCrossSumFrom stage k count =
      Fan.perimeter
        (Fan.edgeCrossesFrom (circleSamplePoint stage k)
          (innerBoundaryFrom stage (k + 1) count)) := by
  induction count generalizing k with
  | zero =>
      simp [innerChordCrossSumFrom, innerBoundaryFrom,
        piCircleAreaPolygon.innerBoundaryFrom, Fan.perimeter,
        Fan.edgeCrossesFrom, Fan.sumRat]
  | succ count ih =>
      simp [innerChordCrossSumFrom, innerBoundaryFrom,
        piCircleAreaPolygon.innerBoundaryFrom, Fan.perimeter,
        Fan.edgeCrossesFrom, Fan.sumRat, ih]

/-- The rational inscribed chord fan is exactly the sum of its adjacent
cross-product cells. -/
theorem innerFanPerimeter_eq_innerChordCrossSumFrom (stage : Nat) :
    Fan.perimeter (innerFanWidths stage) =
      innerChordCrossSumFrom stage 0 stage := by
  have h := innerChordCrossSumFrom_eq_edgeCrossPerimeter stage stage 0
  symm
  simpa [innerFanWidths, innerBoundary, Fan.sectorFanWidths,
    Fan.perimeter, Fan.edgeCrossesFrom, Fan.sumRat, innerBoundaryFrom,
    piCircleAreaPolygon.innerBoundaryFrom, pointCross_origin_left,
    Rat.zero_add] using h

/-- Exact rational inscribed chord fan increases under dyadic subdivision. -/
theorem innerFanPerimeter_refinesByDoubling
    (stage : Nat) (hstage : 0 < stage) :
    Fan.perimeter (innerFanWidths stage) <=
      Fan.perimeter (innerFanWidths (2 * stage)) := by
  rw [innerFanPerimeter_eq_innerChordCrossSumFrom,
    innerFanPerimeter_eq_innerChordCrossSumFrom]
  simpa using
    (innerChordCrossSumFrom_refinesByDoubling stage hstage stage 0)

/-- A local, same-units refinement certificate for the inscribed path: the
certified lower bound for one chord is no greater than the sum of the lower
bounds for its two dyadic subchords. -/
def AdjacentChordLowerRefinesByDoubling (stage : Nat) : Prop :=
  forall k : Fin stage,
    (pointSegmentLengthInterval
      (circleSamplePoint stage k.1)
      (circleSamplePoint stage (k.1 + 1)) stage).lo <=
      (pointSegmentLengthInterval
        (circleSamplePoint (2 * stage) (2 * k.1))
        (circleSamplePoint (2 * stage) (2 * k.1 + 1)) (2 * stage)).lo +
        (pointSegmentLengthInterval
          (circleSamplePoint (2 * stage) (2 * k.1 + 1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 2)) (2 * stage)).lo

/-- The finite rational margin whose verification closes the remaining
lower-endpoint refinement of the original chord-path circumference algorithm.

For each coarse chord, the two curvature certificates for its fine chords,
minus the two explicit bisection widths, must dominate the coarse squared
chord.  This is a finite statement over rational coordinates; it has no
completeness or real-square-root premise. -/
def AdjacentChordCurvatureMarginCoversFineWidths (stage : Nat) : Prop :=
  forall k : Fin stage,
    let p := circleSamplePoint stage k.1
    let q := circleSamplePoint stage (k.1 + 1)
    let p' := circleSamplePoint (2 * stage) (2 * k.1)
    let m := circleSamplePoint (2 * stage) (2 * k.1 + 1)
    let q' := circleSamplePoint (2 * stage) (2 * k.1 + 2)
    let left := pointSegmentLengthInterval p' m (2 * stage)
    let right := pointSegmentLengthInterval m q' (2 * stage)
    let r := curvatureChordLower p' m + curvatureChordLower m q' -
      left.width - right.width
    0 <= r /\ pointSegmentNormSq p q <= sq r

/-- A verified curvature margin yields the local lower-chord refinement
needed by the original `piCircumference` computation. -/
theorem adjacentChordLowerRefinesByDoubling_of_curvatureMargin
    (stage : Nat) (hstage : 0 < stage)
    (hmargin : AdjacentChordCurvatureMarginCoversFineWidths stage) :
    AdjacentChordLowerRefinesByDoubling stage := by
  intro k
  have h := hmargin k
  dsimp at h
  let p := circleSamplePoint stage k.1
  let q := circleSamplePoint stage (k.1 + 1)
  let p' := circleSamplePoint (2 * stage) (2 * k.1)
  let m := circleSamplePoint (2 * stage) (2 * k.1 + 1)
  let q' := circleSamplePoint (2 * stage) (2 * k.1 + 2)
  let left := pointSegmentLengthInterval p' m (2 * stage)
  let right := pointSegmentLengthInterval m q' (2 * stage)
  let r := curvatureChordLower p' m + curvatureChordLower m q' -
    left.width - right.width
  have hcoarse :
      (pointSegmentLengthInterval p q stage).lo <= r :=
    pointSegmentLengthInterval_lo_le_of_sq_le p q stage h.1 h.2
  have hleft : curvatureChordLower p' m - left.width <= left.lo := by
    dsimp [p', m, left]
    exact adjacentCurvatureChordLower_sub_width_le_segment_lo
      (2 * stage) (by omega) (2 * k.1) (2 * stage)
  have hright : curvatureChordLower m q' - right.width <= right.lo := by
    dsimp [m, q', right]
    exact adjacentCurvatureChordLower_sub_width_le_segment_lo
      (2 * stage) (by omega) (2 * k.1 + 1) (2 * stage)
  dsimp [p, q, p', m, q', left, right, r] at hcoarse hleft hright ⊢
  calc
    (pointSegmentLengthInterval
        (circleSamplePoint stage k.1)
        (circleSamplePoint stage (k.1 + 1)) stage).lo <=
      curvatureChordLower (circleSamplePoint (2 * stage) (2 * k.1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 1)) +
        curvatureChordLower (circleSamplePoint (2 * stage) (2 * k.1 + 1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 2)) -
        (pointSegmentLengthInterval
          (circleSamplePoint (2 * stage) (2 * k.1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 1)) (2 * stage)).width -
        (pointSegmentLengthInterval
          (circleSamplePoint (2 * stage) (2 * k.1 + 1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 2)) (2 * stage)).width :=
      hcoarse
    _ <=
      (pointSegmentLengthInterval
        (circleSamplePoint (2 * stage) (2 * k.1))
        (circleSamplePoint (2 * stage) (2 * k.1 + 1)) (2 * stage)).lo +
      (pointSegmentLengthInterval
        (circleSamplePoint (2 * stage) (2 * k.1 + 1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 2)) (2 * stage)).lo := by
      grind [Rat.sub_eq_add_neg]

/-- The sharper finite rational margin for the direct chord-path
refinement.  It differs from the curvature margin only in replacing each
fine chord's lower certificate by the cubic-scale secant certificate. -/
def AdjacentChordSecantMarginCoversFineWidths (stage : Nat) : Prop :=
  forall k : Fin stage,
    let p := circleSamplePoint stage k.1
    let q := circleSamplePoint stage (k.1 + 1)
    let p' := circleSamplePoint (2 * stage) (2 * k.1)
    let m := circleSamplePoint (2 * stage) (2 * k.1 + 1)
    let q' := circleSamplePoint (2 * stage) (2 * k.1 + 2)
    let left := pointSegmentLengthInterval p' m (2 * stage)
    let right := pointSegmentLengthInterval m q' (2 * stage)
    let r := RationalCircle.Stage.secantChordLower p' m +
      RationalCircle.Stage.secantChordLower m q' - left.width - right.width
    0 <= r /\ pointSegmentNormSq p q <= sq r

/-- The literal bisection width for a unit-bounded chord at a nonzero
precision. This is the rational error budget used by the fine-cell secant
margin, separated from the square-root evaluator for arithmetic proofs. -/
def adjacentChordBisectionWidth (precision : Nat) : Rat :=
  1 / (((2 ^ (precision + 9) : Nat) : Rat))

/-- The direct secant-margin condition with its two fine square-root errors
already normalized to explicit dyadic rationals.  It is a finite rational
inequality; `adjacentChordSecantMargin_of_fineDyadicBudget` transports it to
the original interval-based condition. -/
def AdjacentChordSecantMarginCoversFineDyadicBudget (stage : Nat) : Prop :=
  forall k : Fin stage,
    let p := circleSamplePoint stage k.1
    let q := circleSamplePoint stage (k.1 + 1)
    let p' := circleSamplePoint (2 * stage) (2 * k.1)
    let m := circleSamplePoint (2 * stage) (2 * k.1 + 1)
    let q' := circleSamplePoint (2 * stage) (2 * k.1 + 2)
    let b := adjacentChordBisectionWidth (2 * stage)
    let r := RationalCircle.Stage.secantChordLower p' m +
      RationalCircle.Stage.secantChordLower m q' - b - b
    0 <= r /\ pointSegmentNormSq p q <= sq r

/-- Replacing the two fine interval widths by their exact dyadic value turns
the explicit budget margin into the original secant margin condition. -/
theorem adjacentChordSecantMargin_of_fineDyadicBudget
    (stage : Nat) (hstage : 0 < stage)
    (hbudget : AdjacentChordSecantMarginCoversFineDyadicBudget stage) :
    AdjacentChordSecantMarginCoversFineWidths stage := by
  intro k
  have h := hbudget k
  dsimp [AdjacentChordSecantMarginCoversFineDyadicBudget] at h
  dsimp [AdjacentChordSecantMarginCoversFineWidths]
  have hleft := adjacentPointSegmentLengthInterval_width_eq_unit
    (2 * stage) (by omega) (2 * k.1) (2 * stage) (by omega)
  have hright := adjacentPointSegmentLengthInterval_width_eq_unit
    (2 * stage) (by omega) (2 * k.1 + 1) (2 * stage) (by omega)
  rw [hleft, hright]
  simpa [adjacentChordBisectionWidth] using h

/-- A verified secant margin yields the original local lower-chord
refinement.  This packages the new rational chord certificate directly in
the criterion used by `piCircumference`. -/
theorem adjacentChordLowerRefinesByDoubling_of_secantMargin
    (stage : Nat) (hstage : 0 < stage)
    (hmargin : AdjacentChordSecantMarginCoversFineWidths stage) :
    AdjacentChordLowerRefinesByDoubling stage := by
  intro k
  have h := hmargin k
  dsimp at h
  let p := circleSamplePoint stage k.1
  let q := circleSamplePoint stage (k.1 + 1)
  let p' := circleSamplePoint (2 * stage) (2 * k.1)
  let m := circleSamplePoint (2 * stage) (2 * k.1 + 1)
  let q' := circleSamplePoint (2 * stage) (2 * k.1 + 2)
  let left := pointSegmentLengthInterval p' m (2 * stage)
  let right := pointSegmentLengthInterval m q' (2 * stage)
  let r := RationalCircle.Stage.secantChordLower p' m +
    RationalCircle.Stage.secantChordLower m q' - left.width - right.width
  have hcoarse :
      (pointSegmentLengthInterval p q stage).lo <= r :=
    pointSegmentLengthInterval_lo_le_of_sq_le p q stage h.1 h.2
  have hleft : RationalCircle.Stage.secantChordLower p' m - left.width <=
      left.lo := by
    dsimp [p', m, left]
    exact adjacentSecantChordLower_sub_width_le_segment_lo
      (2 * stage) (by omega) (2 * k.1) (2 * stage)
  have hright : RationalCircle.Stage.secantChordLower m q' - right.width <=
      right.lo := by
    dsimp [m, q', right]
    exact adjacentSecantChordLower_sub_width_le_segment_lo
      (2 * stage) (by omega) (2 * k.1 + 1) (2 * stage)
  dsimp [p, q, p', m, q', left, right, r] at hcoarse hleft hright ⊢
  calc
    (pointSegmentLengthInterval
        (circleSamplePoint stage k.1)
        (circleSamplePoint stage (k.1 + 1)) stage).lo <=
      RationalCircle.Stage.secantChordLower
          (circleSamplePoint (2 * stage) (2 * k.1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 1)) +
        RationalCircle.Stage.secantChordLower
          (circleSamplePoint (2 * stage) (2 * k.1 + 1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 2)) -
        (pointSegmentLengthInterval
          (circleSamplePoint (2 * stage) (2 * k.1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 1)) (2 * stage)).width -
        (pointSegmentLengthInterval
          (circleSamplePoint (2 * stage) (2 * k.1 + 1))
          (circleSamplePoint (2 * stage) (2 * k.1 + 2)) (2 * stage)).width :=
      hcoarse
    _ <=
      (pointSegmentLengthInterval
        (circleSamplePoint (2 * stage) (2 * k.1))
        (circleSamplePoint (2 * stage) (2 * k.1 + 1)) (2 * stage)).lo +
      (pointSegmentLengthInterval
        (circleSamplePoint (2 * stage) (2 * k.1 + 1))
        (circleSamplePoint (2 * stage) (2 * k.1 + 2)) (2 * stage)).lo := by
      grind [Rat.sub_eq_add_neg]

private def innerChordLowerSumFrom
    (stage precision k : Nat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      (pointSegmentLengthInterval
        (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) precision).lo +
        innerChordLowerSumFrom stage precision (k + 1) count

private theorem innerChordLowerSumFrom_eq_pathLo
    (stage precision count k : Nat) :
    innerChordLowerSumFrom stage precision k count =
      (rationalPointPathLength
        (circleSamplePoint stage k ::
          innerBoundaryFrom stage (k + 1) count) precision).lo := by
  induction count generalizing k with
  | zero =>
      rfl
  | succ count ih =>
      simp [innerChordLowerSumFrom, rationalPointPathLength,
        rationalPointPathLength.totalLength, innerBoundaryFrom,
        piCircleAreaPolygon.innerBoundaryFrom, pointSegmentLengthInterval,
        pointSegmentNormSq, ih]

private theorem innerChordLowerSumFrom_refinesByDoubling_aux
    (stage : Nat) (hlocal : AdjacentChordLowerRefinesByDoubling stage) :
    forall count k, k + count <= stage ->
      innerChordLowerSumFrom stage stage k count <=
        innerChordLowerSumFrom (2 * stage) (2 * stage) (2 * k) (2 * count)
  | 0, _k, _hbound => by
      simp [innerChordLowerSumFrom]
  | count + 1, k, hbound => by
      have hhead :
          (pointSegmentLengthInterval
            (circleSamplePoint stage k)
            (circleSamplePoint stage (k + 1)) stage).lo <=
            (pointSegmentLengthInterval
              (circleSamplePoint (2 * stage) (2 * k))
              (circleSamplePoint (2 * stage) (2 * k + 1)) (2 * stage)).lo +
              (pointSegmentLengthInterval
                (circleSamplePoint (2 * stage) (2 * k + 1))
                (circleSamplePoint (2 * stage) (2 * k + 2))
                (2 * stage)).lo :=
        hlocal ⟨k, by omega⟩
      have htail :=
        innerChordLowerSumFrom_refinesByDoubling_aux stage hlocal count
          (k + 1) (by omega)
      have htail' :
          innerChordLowerSumFrom stage stage (k + 1) count <=
            innerChordLowerSumFrom (2 * stage) (2 * stage)
              (2 * k + 1 + 1) (2 * count) := by
        have hindex : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
        rw [hindex] at htail
        exact htail
      rw [show 2 * (count + 1) = 2 * count + 2 by omega]
      simp only [innerChordLowerSumFrom]
      calc
        (pointSegmentLengthInterval
            (circleSamplePoint stage k)
            (circleSamplePoint stage (k + 1)) stage).lo +
            innerChordLowerSumFrom stage stage (k + 1) count <=
          ((pointSegmentLengthInterval
              (circleSamplePoint (2 * stage) (2 * k))
              (circleSamplePoint (2 * stage) (2 * k + 1))
              (2 * stage)).lo +
            (pointSegmentLengthInterval
              (circleSamplePoint (2 * stage) (2 * k + 1))
              (circleSamplePoint (2 * stage) (2 * k + 2))
              (2 * stage)).lo) +
            innerChordLowerSumFrom stage stage (k + 1) count :=
          Rat.add_le_add_right.mpr hhead
        _ <=
          ((pointSegmentLengthInterval
              (circleSamplePoint (2 * stage) (2 * k))
              (circleSamplePoint (2 * stage) (2 * k + 1))
              (2 * stage)).lo +
            (pointSegmentLengthInterval
              (circleSamplePoint (2 * stage) (2 * k + 1))
              (circleSamplePoint (2 * stage) (2 * k + 2))
              (2 * stage)).lo) +
            innerChordLowerSumFrom (2 * stage) (2 * stage)
              (2 * k + 1 + 1) (2 * count) :=
          Rat.add_le_add_left.mpr htail'
        _ =
          (pointSegmentLengthInterval
              (circleSamplePoint (2 * stage) (2 * k))
              (circleSamplePoint (2 * stage) (2 * k + 1))
              (2 * stage)).lo +
            ((pointSegmentLengthInterval
              (circleSamplePoint (2 * stage) (2 * k + 1))
              (circleSamplePoint (2 * stage) (2 * k + 2))
              (2 * stage)).lo +
              innerChordLowerSumFrom (2 * stage) (2 * stage)
                (2 * k + 1 + 1) (2 * count)) := by
          grind [Rat.add_assoc, Rat.add_comm]

/-- Local lower-chord refinement lifts by finite recursion to the full
inscribed quarter-path endpoint. -/
theorem innerQuarterLength_lo_refinesByDoubling_of_adjacentChordLowerRefines
    (stage : Nat) (hlocal : AdjacentChordLowerRefinesByDoubling stage) :
    (innerQuarterLength stage).lo <=
      (innerQuarterLength (2 * stage)).lo := by
  rw [show (innerQuarterLength stage).lo =
      innerChordLowerSumFrom stage stage 0 stage by
        simpa [innerQuarterLength, innerBoundary] using
          (innerChordLowerSumFrom_eq_pathLo stage stage stage 0).symm,
    show (innerQuarterLength (2 * stage)).lo =
      innerChordLowerSumFrom (2 * stage) (2 * stage) 0 (2 * stage) by
        simpa [innerQuarterLength, innerBoundary] using
          (innerChordLowerSumFrom_eq_pathLo (2 * stage) (2 * stage)
            (2 * stage) 0).symm]
  exact innerChordLowerSumFrom_refinesByDoubling_aux stage hlocal stage 0
    (by omega)

/-- The remaining direct lower-endpoint condition, expressed as finite local
rational comparisons at every public dyadic stage. -/
def InnerChordLowerRefinement : Prop :=
  forall n, AdjacentChordLowerRefinesByDoubling (piStage n)

theorem innerQuarterLength_lo_refinesByDyadicStage_of_adjacentChordLowerRefinement
    (hlocal : InnerChordLowerRefinement) (n : Nat) :
    (innerQuarterLength (piStage n)).lo <=
      (innerQuarterLength (piStage (n + 1))).lo := by
  have hstage : piStage (n + 1) = 2 * piStage n := by
    unfold piStage
    rw [Nat.pow_succ]
    omega
  rw [hstage]
  exact innerQuarterLength_lo_refinesByDoubling_of_adjacentChordLowerRefines
    (piStage n) (hlocal n)

/-- The local lower-chord refinement condition, together with the proved
outer endpoint inequality, suffices for direct circumference refinement. -/
theorem circumferenceQuarterLengthStepRefines_of_adjacentChordLowerRefinement
    (hlocal : InnerChordLowerRefinement) :
    CircumferenceQuarterLengthStepRefines := by
  intro n
  exact ⟨innerQuarterLength_lo_refinesByDyadicStage_of_adjacentChordLowerRefinement
      hlocal n,
    outerQuarterLength_hi_refinesByDyadicStage n⟩

/-- A direct Archimedean pi algorithm with an exact rational inscribed
cross-product lower endpoint and the original circumscribed polygonal
path-length upper endpoint.  The cross product is a certified lower bound for
each positive chord on the unit circle, so this remains a geometric
circumference enclosure; unlike `piCircumference`, its lower endpoint is
monotone under dyadic subdivision by finite rational algebra. -/
def piCircumferenceFanComputeAtStage (stage : Nat) : QInterval :=
  { lo := (4 * Fan.perimeter (innerFanWidths stage)) / 2,
    hi := (4 * (outerQuarterLength stage).hi) / 2 }

/-- The cross-fan Archimedean circumference pi computation.  This is not an
anchor reboxing: every endpoint is evaluated from the displayed finite
rational circle polygon at the requested dyadic stage. -/
def piCircumferenceFan : RealRaw where
  compute := fun n => piCircumferenceFanComputeAtStage (piStage n)

theorem piCircumferenceFan_compute_eq (n : Nat) :
    piCircumferenceFan.compute n =
      piCircumferenceFanComputeAtStage (piStage n) :=
  rfl

/-- The finite cross-fan circumference bracket is ordered at every positive
circle stage. -/
theorem piCircumferenceFanComputeAtStage_ordered
    (stage : Nat) (hstage : 0 < stage) :
    0 <= (piCircumferenceFanComputeAtStage stage).width := by
  have hfan :
      Fan.perimeter (innerFanWidths stage) <=
        Fan.perimeter (outerFanWidths stage) :=
    innerFanPerimeter_le_outerFanPerimeter stage hstage
  have houter :
      Fan.perimeter (outerFanWidths stage) <=
        (outerQuarterLength stage).hi :=
    outerFanPerimeter_le_outerQuarterLength_hi stage hstage
  have hscaled :
      (4 * Fan.perimeter (innerFanWidths stage)) / 2 <=
        (4 * (outerQuarterLength stage).hi) / 2 :=
    div_two_le_div_two
      (four_mul_le_four_mul (Rat.le_trans hfan houter))
  unfold piCircumferenceFanComputeAtStage QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem piCircumferenceFan_ordered (n : Nat) :
    0 <= (piCircumferenceFan.compute n).width := by
  rw [piCircumferenceFan_compute_eq]
  exact piCircumferenceFanComputeAtStage_ordered (piStage n) (piStage_pos n)

/-- The cross-fan lower endpoint and polygonal upper endpoint both refine
under each dyadic stage doubling. -/
theorem piCircumferenceFan_step_refines :
    EndpointStepRefines piCircumferenceFan.compute := by
  intro n
  have hstage : piStage (n + 1) = 2 * piStage n := by
    unfold piStage
    rw [Nat.pow_succ]
    omega
  have houter := outerQuarterLength_hi_refinesByDyadicStage n
  rw [hstage] at houter
  rw [piCircumferenceFan_compute_eq,
    piCircumferenceFan_compute_eq, hstage]
  unfold piCircumferenceFanComputeAtStage
  constructor
  · exact div_two_le_div_two
      (four_mul_le_four_mul
        (innerFanPerimeter_refinesByDoubling (piStage n) (piStage_pos n)))
  · exact div_two_le_div_two
      (four_mul_le_four_mul
        houter)

/-- The quarter-gap of the cross-fan circumference enclosure. -/
def circumferenceFanQuarterGap (stage : Nat) : Rat :=
  (outerQuarterLength stage).hi - Fan.perimeter (innerFanWidths stage)

/-- The remaining cross-fan gap is controlled by the already certified fan
gap plus the upper polygonal path's square-root enclosure budget. -/
theorem circumferenceFanQuarterGap_le_fanGap_add_pathWidthBudget
    (stage : Nat) (hstage : 0 < stage) :
    circumferenceFanQuarterGap stage <=
      circumferenceFanGap stage + circumferencePathWidthBudget stage := by
  let Fi := Fan.perimeter (innerFanWidths stage)
  let Fo := Fan.perimeter (outerFanWidths stage)
  let O := outerQuarterLength stage
  have houterLo : O.lo <= Fo := by
    dsimp [O, Fo]
    exact outerQuarterLength_lo_le_outerFanPerimeter stage hstage
  have houterWidth : O.hi - Fo <= O.width := by
    dsimp [O]
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hpath : O.width <= circumferencePathWidthBudget stage := by
    change (rationalPointPathLength (outerBoundary stage) stage).width <=
      circumferencePathWidthBudget stage
    rw [rationalPointPathLength_width_eq_segmentBudget]
    unfold circumferencePathWidthBudget
    have hinner := pathSegmentWidthBudget_nonneg (innerBoundary stage) stage
    grind
  unfold circumferenceFanQuarterGap circumferenceFanGap
  dsimp [Fi, Fo, O] at houterWidth hpath ⊢
  calc
    (outerQuarterLength stage).hi - Fan.perimeter (innerFanWidths stage) =
        ((outerQuarterLength stage).hi - Fan.perimeter (outerFanWidths stage)) +
          (Fan.perimeter (outerFanWidths stage) -
            Fan.perimeter (innerFanWidths stage)) := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    _ <= (outerQuarterLength stage).width +
          (Fan.perimeter (outerFanWidths stage) -
            Fan.perimeter (innerFanWidths stage)) :=
          Rat.add_le_add_right.mpr houterWidth
    _ <= circumferencePathWidthBudget stage +
          (Fan.perimeter (outerFanWidths stage) -
            Fan.perimeter (innerFanWidths stage)) :=
          Rat.add_le_add_right.mpr hpath
    _ = (Fan.perimeter (outerFanWidths stage) -
          Fan.perimeter (innerFanWidths stage)) +
          circumferencePathWidthBudget stage := by
          grind [Rat.add_comm]

theorem piCircumferenceFanComputeAtStage_width_eq (stage : Nat) :
    (piCircumferenceFanComputeAtStage stage).width =
      2 * circumferenceFanQuarterGap stage := by
  simp [piCircumferenceFanComputeAtStage, circumferenceFanQuarterGap,
    QInterval.width, four_div_two_eq_two_mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem piCircumferenceFan_compute_width_eq (n : Nat) :
    (piCircumferenceFan.compute n).width =
      2 * circumferenceFanQuarterGap (piStage n) := by
  rw [piCircumferenceFan_compute_eq]
  exact piCircumferenceFanComputeAtStage_width_eq (piStage n)

theorem piCircumferenceFan_width_linear_bound_ten :
    forall n,
      (piCircumferenceFan.compute n).width <=
        (10 : Rat) / (((n + 1 : Nat) : Rat)) := by
  intro n
  rw [piCircumferenceFan_compute_width_eq]
  have hgap := circumferenceFanQuarterGap_le_fanGap_add_pathWidthBudget
    (piStage n) (piStage_pos n)
  have hscaled :
      2 * circumferenceFanQuarterGap (piStage n) <=
        2 * (circumferenceFanGap (piStage n) +
          circumferencePathWidthBudget (piStage n)) :=
    Rat.mul_le_mul_of_nonneg_left hgap
      (by native_decide : (0 : Rat) <= 2)
  exact Rat.le_trans hscaled (circumferenceFanGapPathBudgetLinearBound_ten n)

theorem piCircumferenceFan_widthsShrink :
    RealRaw.WidthsShrinkToZero piCircumferenceFan.compute :=
  widthsShrink_of_natOverSuccBound piCircumferenceFan_width_linear_bound_ten

private theorem innerQuarterArea_eq_half_innerFanPerimeter
    (stage : Nat) (hstage : 0 < stage) :
    innerQuarterArea stage = Fan.perimeter (innerFanWidths stage) / 2 := by
  rw [innerQuarterArea_eq_variable_unit_fan stage]
  · unfold innerFanPieces
    rw [Fan.variableArea_unitPieces_eq_area, Fan.area_one_eq_half_perimeter]
  · exact Fan.sumRat_nonneg (innerFanWidths stage)
      (Fan.sectorFanWidths_mem_nonneg (innerBoundary stage)
        (innerBoundary_consecutiveCrossNonneg stage hstage))

/-- The cross-fan lower endpoint is exactly the inscribed polygon-area lower
endpoint for the baseline circle-area pi computation. -/
theorem piCircumferenceFan_compute_lo_eq_piCircleArea_compute_lo (n : Nat) :
    (piCircumferenceFan.compute n).lo = (piCircleArea.compute n).lo := by
  rw [piCircumferenceFan_compute_eq, piCircleAreaPolygonAgreement n,
    piCircleAreaPolygon_compute_eq]
  unfold piCircumferenceFanComputeAtStage piCircleAreaPolygonComputeAtStage
  rw [innerQuarterArea_eq_half_innerFanPerimeter
    (piStage n) (piStage_pos n)]
  rw [four_div_two_eq_two_mul]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

/-- The cross-fan circumference computation is a valid rational raw real:
ordered brackets, symbolic dyadic endpoint refinement, and an explicit
`10/(n+1)` width modulus. -/
theorem piCircumferenceFan_valid : piCircumferenceFan.Valid := by
  change RealRaw.ValidCompute piCircumferenceFan.compute
  refine ⟨piCircumferenceFan_ordered, ?_, piCircumferenceFan_widthsShrink⟩
  intro n m hnm
  have hmono := endpointMonotone_of_stepRefines piCircumferenceFan_step_refines
    n m hnm
  have hordered := piCircumferenceFan_ordered m
  unfold QInterval.width at hordered
  exact ⟨hmono.1, by grind [Rat.sub_eq_add_neg], hmono.2⟩

/-- The direct cross-fan circumference computation agrees with the baseline
circle-area pi at every stage.  The common lower endpoint is the inscribed
sector-polygon area, while both independently certified upper endpoints lie
above it. -/
theorem piCircumferenceFan_equiv_piCircleArea :
    piCircumferenceFan.Equiv piCircleArea := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff piCircumferenceFan piCircleArea n n).2
  have hsame := piCircumferenceFan_compute_lo_eq_piCircleArea_compute_lo n
  have hfan := piCircumferenceFan_ordered n
  have harea := AreaLoopValidity.areaOrdered n
  unfold QInterval.width at hfan harea
  constructor
  · rw [hsame]
    grind [Rat.sub_eq_add_neg]
  · rw [← hsame]
    grind [Rat.sub_eq_add_neg]

/-- The polygonal area presentation agrees directly with the increment and
decrement area loop.  The two computations have equal stage boxes, so this is
the representation-level bridge used by the certified π registry below. -/
theorem piCircleAreaPolygon_equiv_piCircleArea :
    piCircleAreaPolygon.Equiv piCircleArea := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    piCircleAreaPolygon piCircleArea n n).2
  rw [piCircleAreaPolygonAgreement n]
  have hordered := piCircleAreaPolygon_ordered n
  unfold QInterval.width at hordered
  have hlohi : (piCircleAreaPolygon.compute n).lo <=
      (piCircleAreaPolygon.compute n).hi := by
    grind [Rat.sub_eq_add_neg]
  exact ⟨hlohi, hlohi⟩

/-- Canonical checked presentations of π.

These constructors are deliberately presentations, rather than a second
scoreboard: each one is a completed finite rational computation, or an
essential certified normalization of one, with a validity proof and an
equivalence proof to the preferred area evaluator.  Several presentations
exercise the same underlying calculus capability; `PiIntegrationFamily` below
records that distinction so a count of constructors is never mistaken for a
measure of calculus readiness. -/
inductive PiPresentation where
  | area
  | areaPolygon
  | circumferenceStabilized
  | circumferenceReboxed
  | circumferenceFan
  | arctanGeometry
  | arctanRectangleIntegral
  | arctanIntegrationByParts
  | arctanSquareSubstitution
  | leibnizSeries
  | nilakanthaSeries
  | machinSeries
  | cauchyIntegral
  | symmetricCauchyPiecewiseIntegral
  | reciprocalQuarticIntegral
deriving DecidableEq, Repr

/-- The distinct constructive capabilities exercised by the checked π
presentations.

This is release-test metadata, not mathematical data about π.  In particular,
the three arctangent presentations and the accelerated series formulas are
kept as separate certified evaluators, while their shared dependencies are
recorded by one family.  The project measures readiness for calculus through
the calculus gates, not by counting values of this type. -/
inductive PiIntegrationFamily where
  | finiteGeometry
  | arctangentGeometry
  | finiteIntegral
  | finiteIntegrationByParts
  | finiteSubstitution
  | alternatingSeries
  | compactifiedImproperIntegral
  | piecewiseMonotoneIntegral
deriving DecidableEq, Repr

/-- The primary constructive capability exercised by a checked π
presentation.  This deliberately groups presentation variants that share the
same bridge, while retaining all variants as independently executable
regression tests. -/
def PiPresentation.integrationFamily : PiPresentation -> PiIntegrationFamily
  | .area | .areaPolygon | .circumferenceStabilized | .circumferenceReboxed |
      .circumferenceFan => .finiteGeometry
  | .arctanGeometry => .arctangentGeometry
  | .arctanRectangleIntegral | .reciprocalQuarticIntegral => .finiteIntegral
  | .arctanIntegrationByParts => .finiteIntegrationByParts
  | .arctanSquareSubstitution => .finiteSubstitution
  | .leibnizSeries | .nilakanthaSeries | .machinSeries => .alternatingSeries
  | .cauchyIntegral => .compactifiedImproperIntegral
  | .symmetricCauchyPiecewiseIntegral => .piecewiseMonotoneIntegral

/-- The raw interval algorithm behind each canonical checked presentation. -/
def piPresentationRaw : PiPresentation -> RealRaw
  | .area => piCircleArea
  | .areaPolygon => piCircleAreaPolygon
  | .circumferenceStabilized => piCircumferenceStabilized
  | .circumferenceReboxed => piCircumferenceReboxed
  | .circumferenceFan => piCircumferenceFan
  | .arctanGeometry => (4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat)
  | .arctanRectangleIntegral => piFromArctanIntegralRectangleUnitAtOne
  | .arctanIntegrationByParts => Logarithm.piTriangleLogReciprocalIntegral
  | .arctanSquareSubstitution =>
      Logarithm.piTriangleLogSquareSubstitutionIntegral
  | .leibnizSeries => piLeibniz
  | .nilakanthaSeries => piNilakantha
  | .machinSeries => piMachin
  | .cauchyIntegral => IntegralIdentities.cauchyFullLineIntegral
  | .symmetricCauchyPiecewiseIntegral =>
      IntegralIdentities.piSymmetricCauchyPiecewiseIntegral
  | .reciprocalQuarticIntegral => piReciprocalQuarticCompact

/-- Every canonical presentation has a checked nested, shrinking interval
algorithm. -/
theorem piPresentation_valid (presentation : PiPresentation) :
    (piPresentationRaw presentation).Valid := by
  cases presentation with
  | area => simpa [piPresentationRaw, AreaValid, RealRaw.Valid] using
      AreaLoopValidity.areaValid
  | areaPolygon => simpa [piPresentationRaw] using piCircleAreaPolygon_valid
  | circumferenceStabilized =>
      simpa [piPresentationRaw] using piCircumferenceStabilized_valid
  | circumferenceReboxed =>
      simpa [piPresentationRaw] using piCircumferenceReboxed_valid
  | circumferenceFan => simpa [piPresentationRaw] using piCircumferenceFan_valid
  | arctanGeometry => simpa [piPresentationRaw] using fourArctanGeomOneValid
  | arctanRectangleIntegral =>
      simpa [piPresentationRaw] using piFromArctanIntegralRectangleUnitAtOne_valid
  | arctanIntegrationByParts =>
      simpa [piPresentationRaw] using Logarithm.piTriangleLogReciprocalIntegral_valid
  | arctanSquareSubstitution =>
      simpa [piPresentationRaw] using
        Logarithm.piTriangleLogSquareSubstitutionIntegral_valid
  | leibnizSeries => simpa [piPresentationRaw, LeibnizValid, RealRaw.Valid] using
      leibnizValid
  | nilakanthaSeries => simpa [piPresentationRaw] using Nilakantha.valid
  | machinSeries => simpa [piPresentationRaw, MachinValid, RealRaw.Valid] using
      machinValid
  | cauchyIntegral =>
      simpa [piPresentationRaw] using IntegralIdentities.cauchyFullLineIntegral_valid
  | symmetricCauchyPiecewiseIntegral =>
      simpa [piPresentationRaw] using
        IntegralIdentities.piSymmetricCauchyPiecewiseIntegral_valid
  | reciprocalQuarticIntegral =>
      simpa [piPresentationRaw] using piReciprocalQuarticCompact_valid

/-- Every canonical presentation agrees with the preferred circle-area
evaluator.  This is the useful outcome of the Pi integration suite: a named
collection of interchangeable, certified rational algorithms. -/
theorem piPresentation_equiv_piCircleArea (presentation : PiPresentation) :
    (piPresentationRaw presentation).Equiv piCircleArea := by
  cases presentation with
  | area => exact RealRaw.equiv_refl piCircleArea (piPresentation_valid .area)
  | areaPolygon =>
      simpa [piPresentationRaw] using piCircleAreaPolygon_equiv_piCircleArea
  | circumferenceStabilized => simpa [piPresentationRaw] using
      piCircumferenceStabilized_equiv_piCircleArea
  | circumferenceReboxed => simpa [piPresentationRaw] using
      piCircumferenceReboxed_equiv_piCircleArea
  | circumferenceFan => simpa [piPresentationRaw] using
      piCircumferenceFan_equiv_piCircleArea
  | arctanGeometry => simpa [piPresentationRaw] using
      four_arctanGeom_one_equiv_piCircleArea
  | arctanRectangleIntegral => simpa [piPresentationRaw] using
      piFromArctanIntegralRectangleUnitAtOne_equiv_piCircleArea
  | arctanIntegrationByParts => simpa [piPresentationRaw] using
      piTriangleLogReciprocalIntegral_equiv_piCircleArea
  | arctanSquareSubstitution => simpa [piPresentationRaw] using
      piTriangleLogSquareSubstitutionIntegral_equiv_piCircleArea
  | leibnizSeries =>
      exact RealRaw.equiv_trans
        (piPresentation_valid .leibnizSeries)
        fourArctanSeriesOneValid
        (piPresentation_valid .area)
        piLeibniz_equiv_four_arctanSeries_one
        four_arctanSeries_one_equiv_piCircleArea
  | nilakanthaSeries => simpa [piPresentationRaw] using
      piNilakantha_equiv_piCircleArea
  | machinSeries => simpa [piPresentationRaw] using
      piMachin_equiv_piCircleArea_finiteRiemannBridge
  | cauchyIntegral => simpa [piPresentationRaw] using
      cauchyFullLineIntegral_equiv_piCircleArea
  | symmetricCauchyPiecewiseIntegral => simpa [piPresentationRaw] using
      piSymmetricCauchyPiecewiseIntegral_equiv_piCircleArea
  | reciprocalQuarticIntegral => simpa [piPresentationRaw] using
      piReciprocalQuarticCompact_equiv_piCircleArea

/-- Any two named, checked pi presentations are interchangeable.

This is an API-level interoperability theorem for the complete presentation
registry.  It intentionally does not add a `PiCoverageBridge` row: the latter
keeps only the independent calculus capabilities exercised by the compact
scoreboard. -/
theorem piPresentation_equiv (source target : PiPresentation) :
    (piPresentationRaw source).Equiv (piPresentationRaw target) := by
  exact RealRaw.equiv_trans
    (piPresentation_valid source)
    (piPresentation_valid .area)
    (piPresentation_valid target)
    (piPresentation_equiv_piCircleArea source)
    (RealRaw.equiv_symm (piPresentation_equiv_piCircleArea target))

/-- The small set of π equivalences that act as distinct end-to-end
calculus-regression bridges.

Unlike `PiPresentation`, this is deliberately not an inventory of every
certified evaluator.  Each constructor is one independent bridge from a
construction needed in effective calculus to a second checked construction.
For example, Machin and Nilakantha remain useful series regressions in
`PiPresentation`, but they do not add a second calculus-readiness cell beyond
the arctangent/power-series bridge. -/
inductive PiCoverageBridge where
  /-- Finite Archimedean geometry: polygonal area and circumference enclosures. -/
  | archimedeanGeometry
  /-- Circular arctangent geometry agrees with an alternating power series. -/
  | arctangentPowerSeries
  /-- A finite rectangle integral agrees with the arctangent series. -/
  | definiteIntegral
  /-- The supplied arctangent integration-by-parts formula with its literal
  reciprocal-integral logarithm agrees with area pi. -/
  | arctangentIntegrationByParts
  /-- The arctangent formula with its logarithmic endpoint evaluated by the
  checked finite square substitution agrees with the reciprocal-log form. -/
  | arctangentSquareSubstitution
  /-- Reciprocal-tail compactification agrees with the bounded geometry value. -/
  | compactifiedImproperIntegral
  /-- A nontrivial algebraic kernel agrees with the compactified Cauchy route. -/
  | algebraicKernelIntegral
  /-- The bounded symmetric Cauchy integral uses the public finite
  piecewise-monotone assembler, with an increasing and a decreasing branch. -/
  | piecewiseMonotoneCauchyIntegral
deriving DecidableEq, Repr

/-- The source implementation for a distinct π coverage bridge. -/
def PiCoverageBridge.sourcePresentation : PiCoverageBridge -> PiPresentation
  | .archimedeanGeometry => .circumferenceFan
  | .arctangentPowerSeries => .arctanGeometry
  | .definiteIntegral => .arctanRectangleIntegral
  | .arctangentIntegrationByParts => .arctanIntegrationByParts
  | .arctangentSquareSubstitution => .arctanSquareSubstitution
  | .compactifiedImproperIntegral => .cauchyIntegral
  | .algebraicKernelIntegral => .reciprocalQuarticIntegral
  | .piecewiseMonotoneCauchyIntegral => .symmetricCauchyPiecewiseIntegral

/-- The independently constructed target implementation for a distinct π
coverage bridge. -/
def PiCoverageBridge.targetPresentation : PiCoverageBridge -> PiPresentation
  | .archimedeanGeometry => .area
  | .arctangentPowerSeries => .leibnizSeries
  | .definiteIntegral => .leibnizSeries
  | .arctangentIntegrationByParts => .area
  | .arctangentSquareSubstitution => .arctanIntegrationByParts
  | .compactifiedImproperIntegral => .area
  | .algebraicKernelIntegral => .cauchyIntegral
  | .piecewiseMonotoneCauchyIntegral => .arctanRectangleIntegral

/-- The source raw computation for a coverage bridge. -/
def PiCoverageBridge.sourceRaw (bridge : PiCoverageBridge) : RealRaw :=
  piPresentationRaw bridge.sourcePresentation

/-- The target raw computation for a coverage bridge. -/
def PiCoverageBridge.targetRaw (bridge : PiCoverageBridge) : RealRaw :=
  piPresentationRaw bridge.targetPresentation

/-- Every source side of the compact coverage suite is a valid raw real. -/
theorem PiCoverageBridge.source_valid (bridge : PiCoverageBridge) :
    bridge.sourceRaw.Valid :=
  piPresentation_valid bridge.sourcePresentation

/-- Every target side of the compact coverage suite is a valid raw real. -/
theorem PiCoverageBridge.target_valid (bridge : PiCoverageBridge) :
    bridge.targetRaw.Valid :=
  piPresentation_valid bridge.targetPresentation

/-- The two independently constructed sides of every coverage bridge agree. -/
theorem PiCoverageBridge.equivalent (bridge : PiCoverageBridge) :
    bridge.sourceRaw.Equiv bridge.targetRaw := by
  exact RealRaw.equiv_trans
    (piPresentation_valid bridge.sourcePresentation)
    (piPresentation_valid .area)
    (piPresentation_valid bridge.targetPresentation)
    (piPresentation_equiv_piCircleArea bridge.sourcePresentation)
    (RealRaw.equiv_symm
      (piPresentation_equiv_piCircleArea bridge.targetPresentation))

/-- Every raw algorithm placed directly in the abstract π registry.  The
canonical family covers the scoreboard presentations; the two supplementary
entries are independently useful finite computations. -/
inductive PiView where
  | canonical (presentation : PiPresentation)
  | integrationByPartsMesh
  | triangleLogSeries
deriving DecidableEq, Repr

def PiView.raw : PiView -> RealRaw
  | .canonical presentation => piPresentationRaw presentation
  | .integrationByPartsMesh => IntegralIdentities.piFromArctanIntegrationByPartsMesh
  | .triangleLogSeries => Logarithm.piTriangleLogSeries

theorem PiView.valid (view : PiView) : view.raw.Valid := by
  cases view with
  | canonical presentation => exact piPresentation_valid presentation
  | integrationByPartsMesh =>
      exact IntegralIdentities.piFromArctanIntegrationByPartsMesh_valid
  | triangleLogSeries => exact Logarithm.piTriangleLogSeries_valid

theorem PiView.equiv_piCircleArea (view : PiView) :
    view.raw.Equiv piCircleArea := by
  cases view with
  | canonical presentation => exact piPresentation_equiv_piCircleArea presentation
  | integrationByPartsMesh =>
      exact piFromArctanIntegrationByPartsMesh_equiv_piCircleArea
  | triangleLogSeries => exact piTriangleLogSeries_equiv_piCircleArea

/-- The finite registry of non-preferred π computations.  'PiView.canonical'
keeps the table tied to the public coverage presentations rather than to
builder-chain order. -/
def piCertifiedViews : List PiView :=
  [ .canonical .areaPolygon,
    .canonical .circumferenceStabilized,
    .canonical .circumferenceReboxed,
    .canonical .circumferenceFan,
    .canonical .arctanGeometry,
    .canonical .arctanRectangleIntegral,
    .integrationByPartsMesh,
    .triangleLogSeries,
    .canonical .arctanIntegrationByParts,
    .canonical .arctanSquareSubstitution,
    .canonical .leibnizSeries,
    .canonical .nilakanthaSeries,
    .canonical .machinSeries,
    .canonical .cauchyIntegral,
    .canonical .symmetricCauchyPiecewiseIntegral,
    .canonical .reciprocalQuarticIntegral ]

/-- The project-facing certified π value.  It keeps the fast public area loop
as its preferred evaluator and points to every checked alternative through the
explicit finite registry above. -/
def piCertified : Real where
  preferred := piCircleArea
  valid := piPresentation_valid .area
  alternatives := piCertifiedViews.map PiView.raw
  alternative_valid := by
    intro rep hrep
    obtain ⟨view, _, rfl⟩ := List.mem_map.mp hrep
    exact view.valid
  coherent := by
    intro rep hrep
    obtain ⟨view, _, rfl⟩ := List.mem_map.mp hrep
    exact view.equiv_piCircleArea

theorem piCertified_preferred : piCertified.preferred = piCircleArea :=
  rfl


/-- Retrieve a named certified representation from the primary π registry
without depending on its position in the implementation list. -/
def piCertifiedPresentation (presentation : PiPresentation) :
    Real.Representation piCertified where
  raw := piPresentationRaw presentation
  valid := piPresentation_valid presentation
  agrees := piPresentation_equiv_piCircleArea presentation

namespace pi

/-- The abstract certified value of pi.  Its named views below assign stable
semantic names to the checked raw algorithms in its finite registry. -/
def value : Real := piCertified

def presentation (kind : PiPresentation) : Real.Representation value :=
  piCertifiedPresentation kind

/-- Every named certified view of the abstract pi handle is interchangeable
with every other one.  Unlike `PiPresentation`, this also covers supplementary
views whose role is regression or implementation provenance rather than a
new calculus-coverage bridge. -/
theorem representations_equiv
    (source target : Real.Representation value) :
    source.raw.Equiv target.raw :=
  Real.Representation.equiv source target

def circleArea : Real.Representation value := presentation .area
def circleAreaPolygon : Real.Representation value := presentation .areaPolygon
/-- The default circumference view: the fully direct cross-fan evaluator.
It is deliberately separate from the original chord-path raw algorithm
`piCircumference`; `CircumferenceBridge` certifies that direct view
downstream. -/
def circumference : Real.Representation value := presentation .circumferenceFan

/-- Explicit name for the same default direct cross-fan circumference view.
`pi.circumference` is retained as the convenient short name. -/
def circumferenceFan : Real.Representation value := circumference

/-- The prefix-stabilized view of the original direct chord-path computation.
Its evaluator reads only finite prefixes of `piCircumference`; the area loop
appears only in the proof that its rational stabilization radius is sound. -/
def circumferenceStabilized : Real.Representation value :=
  presentation .circumferenceStabilized

/-- The older anchor-reboxed view of the original direct chord-path
computation.  Unlike `pi.circumferenceStabilized`, its evaluator reads the
area anchor at run time. -/
def circumferenceReboxed : Real.Representation value :=
  presentation .circumferenceReboxed

def arctanGeom : Real.Representation value := presentation .arctanGeometry
def arctanIntegral : Real.Representation value := presentation .arctanRectangleIntegral

/-- The checked unit-branch integration-by-parts formula
`4 * ∫₀¹ arctan(x) dx + 2 * log_rec(2)`.  Its logarithm is the literal
reciprocal integral; transporting it to a canonical inverse-exponential log
is a separate later theorem. -/
def integrationByParts : Real.Representation value :=
  presentation .arctanIntegrationByParts

/-- The finite square-substitution view
`4 * ∫₀¹ arctan(x) dx + 4 * ∫₀¹ x/(1+x^2) dx`.  It is equivalent to the
literal reciprocal-log integration-by-parts view, but retains the pullback
integral as the executable substitution witness. -/
def squareSubstitution : Real.Representation value :=
  presentation .arctanSquareSubstitution

/-- The supplementary direct finite mesh behind integration by parts.  This
is deliberately distinct from the future arctangent--logarithm integral
theorem. -/
def integrationByPartsMesh : Real.Representation value where
  raw := IntegralIdentities.piFromArctanIntegrationByPartsMesh
  valid := IntegralIdentities.piFromArctanIntegrationByPartsMesh_valid
  agrees := piFromArctanIntegrationByPartsMesh_equiv_piCircleArea

/-- The direct triangle plus logarithm-series evaluator.  It is a named
supplementary view of pi, not an additional `PiCoverageBridge` constructor. -/
def triangleLogSeries : Real.Representation value where
  raw := Logarithm.piTriangleLogSeries
  valid := Logarithm.piTriangleLogSeries_valid
  agrees := piTriangleLogSeries_equiv_piCircleArea

/-- The same supplied arctangent integration-by-parts formula with its
logarithm retained as the literal reciprocal integral on `[1,2]`. -/
def triangleLogReciprocalIntegral : Real.Representation value := integrationByParts

def leibniz : Real.Representation value := presentation .leibnizSeries
def nilakantha : Real.Representation value := presentation .nilakanthaSeries
def machin : Real.Representation value := presentation .machinSeries
def cauchy : Real.Representation value := presentation .cauchyIntegral
/-- The bounded symmetric Cauchy computation, built by the public
piecewise-monotone integral assembler on `[-1,0,1]`. -/
def symmetricCauchy : Real.Representation value :=
  presentation .symmetricCauchyPiecewiseIntegral
def reciprocalQuartic : Real.Representation value := presentation .reciprocalQuarticIntegral

end pi


end PiProofs

end ComputableAnalysis
