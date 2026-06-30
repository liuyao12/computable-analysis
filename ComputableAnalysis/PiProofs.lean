import ComputableAnalysis.RationalCircle
import ComputableAnalysis.ArctanGeometry
import ComputableAnalysis.Basic
import ComputableAnalysis.DirichletSeries
import ComputableAnalysis.IntegralIdentities
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

theorem machinValid : MachinValid :=
  machinValid_of_arctanValid arctanValid

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

/-- The Leibniz definition of pi is equivalent to `4 * arctan 1`. -/
theorem piLeibniz_equiv_four_arctan_one :
    piLeibniz.Equiv ((4 : Nat) * arctan (1 : Rat) : RealRaw) := by
  unfold piLeibniz
  exact RealRaw.natScale_equiv 4 leibnizSeries_equiv_arctan_one

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

The remaining analytic step for `Leibniz = Machin` is the constructive branch
theorem turning this tangent identity into equivalence of the raw arctangent
algorithms. -/
theorem quarter_tangent_identity :
    tanSub (tanFour (1 / 5)) (1 / 239) = 1 := by
  native_decide

def BranchIdentity : Prop :=
  ((4 : Nat) * arctan ((1 : Rat) / 5) - arctan ((1 : Rat) / 239)).Equiv
    (arctan (1 : Rat))

def GeometricBranchIdentity : Prop :=
  ((4 : Nat) * ArctanGeometry.arctanGeom ((1 : Rat) / 5) -
      ArctanGeometry.arctanGeom ((1 : Rat) / 239)).Equiv
    (ArctanGeometry.arctanGeom (1 : Rat))

/-- The remaining analytic branch theorem for Machin's formula.

The Gaussian-integer computation above proves the rational tangent identity.
This is the constructive arctangent fact still needed: on the principal branch,
that tangent identity identifies the corresponding raw arctangent algorithms. -/
def BranchLaw : Prop :=
  tanSub (tanFour (1 / 5)) (1 / 239) = 1 -> BranchIdentity

/-- The geometric branch theorem has the same tangent premise, but concludes
the identity for sector-area arctangent instead of the power-series
arctangent. -/
def GeometricBranchLaw : Prop :=
  tanSub (tanFour (1 / 5)) (1 / 239) = 1 -> GeometricBranchIdentity

structure PowerSeriesGeometryAtMachinInputs where
  one_fifth :
    (arctan ((1 : Rat) / 5)).Equiv
      (ArctanGeometry.arctanGeom ((1 : Rat) / 5))
  one_239 :
    (arctan ((1 : Rat) / 239)).Equiv
      (ArctanGeometry.arctanGeom ((1 : Rat) / 239))
  one :
    (arctan (1 : Rat)).Equiv (ArctanGeometry.arctanGeom (1 : Rat))

theorem branchIdentity_of_branchLaw (h : BranchLaw) : BranchIdentity :=
  h quarter_tangent_identity

theorem geometricBranchIdentity_of_geometricBranchLaw
    (h : GeometricBranchLaw) : GeometricBranchIdentity :=
  h quarter_tangent_identity

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

theorem branchIdentity_of_geometricBranchIdentity
    (hGeomValid : ArctanGeometry.Valid)
    (hagree : PowerSeriesGeometryAtMachinInputs)
    (hgeom : GeometricBranchIdentity) : BranchIdentity := by
  have hps15 : (arctan ((1 : Rat) / 5)).Valid :=
    arctan_valid_at arctanValid arctan_one_fifth_mem_domain
  have hps239 : (arctan ((1 : Rat) / 239)).Valid :=
    arctan_valid_at arctanValid arctan_one_239_mem_domain
  have hps1 : (arctan (1 : Rat)).Valid :=
    arctan_valid_at arctanValid arctan_one_mem_domain
  have hg15 : (ArctanGeometry.arctanGeom ((1 : Rat) / 5)).Valid := by
    simpa [RealRaw.Valid, ArctanGeometry.functionRaw] using
      hGeomValid ((1 : Rat) / 5) (by trivial)
  have hg239 : (ArctanGeometry.arctanGeom ((1 : Rat) / 239)).Valid := by
    simpa [RealRaw.Valid, ArctanGeometry.functionRaw] using
      hGeomValid ((1 : Rat) / 239) (by trivial)
  have hg1 : (ArctanGeometry.arctanGeom (1 : Rat)).Valid := by
    simpa [RealRaw.Valid, ArctanGeometry.functionRaw] using
      hGeomValid (1 : Rat) (by trivial)
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

theorem branchLaw_of_geometricBranchLaw
    (hGeomValid : ArctanGeometry.Valid)
    (hagree : PowerSeriesGeometryAtMachinInputs)
    (h : GeometricBranchLaw) : BranchLaw :=
  fun htangent =>
    branchIdentity_of_geometricBranchIdentity
      hGeomValid hagree (h htangent)

theorem piMachin_eq_four_arctan_one_of_branchIdentity
    (h : BranchIdentity) :
    piMachin.Equiv ((4 : Nat) * arctan (1 : Rat) : RealRaw) := by
  unfold piMachin
  exact RealRaw.natScale_equiv 4 h

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

theorem leibnizEqMachin_of_kernelComparisonRoute
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) : LeibnizEqMachin :=
  leibnizEqMachin_of_geometricRoute
    route.geometric_valid
    (MachinIdentity.powerSeriesGeometryAtMachinInputs_of_agreement
      (Taylor.ArctanComparison.powerSeriesAgreesOnUnit_of_kernelComparisonRoute
        route))
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

def circlePoint (u : Rat) : PiCirclePoint :=
  let d := 1 + u * u
  { x := (1 - u * u) / d,
    y := (2 * u) / d }

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

theorem leibnizEqArea_of_kernelComparisonRoute
    (route : Taylor.ArctanComparison.KernelComparisonRoute) :
    LeibnizEqArea :=
  leibnizEqArea_of_powerSeriesGeometryAgreement
    route.geometric_valid
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

theorem circleSamplePoint_cross_nonneg_of_order
    (stage : Nat) (hstage : 0 < stage)
    {i j : Nat} (hij : i <= j) :
    0 <= pointCross (circleSamplePoint stage i)
      (circleSamplePoint stage j) := by
  simpa [circleSamplePoint_eq_rationalCircleStage,
    pointCross_eq_rationalCircleCross] using
    RationalCircle.Stage.samplePoint_cross_nonneg_of_order
      (rationalCircleStage stage) hstage hij

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

theorem four_arctan_one_equiv_piCircleArea_of_powerSeriesGeometryAgreement
    (hagree : ArctanGeometry.PowerSeriesAgreesOnUnit) :
    (((4 : Nat) * arctan (1 : Rat) : RealRaw).Equiv piCircleArea) := by
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
  apply (RealRaw.compareAt_overlap_iff
    ((4 : Nat) * arctan (1 : Rat) : RealRaw) piCircleArea n n).2
  rw [← four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  exact hover

theorem piCircleArea_equiv_four_arctan_one_of_powerSeriesGeometryAgreement
    (hagree : ArctanGeometry.PowerSeriesAgreesOnUnit) :
    piCircleArea.Equiv (((4 : Nat) * arctan (1 : Rat) : RealRaw)) :=
  RealRaw.equiv_symm
    (four_arctan_one_equiv_piCircleArea_of_powerSeriesGeometryAgreement hagree)

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

theorem circumferenceWidthsShrink_of_linearBound
    {C : Nat} (hbound : CircumferenceWidthLinearBound C) :
    CircumferenceWidthsShrink :=
  widthsShrink_of_natOverSuccBound hbound

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

structure GeometricValidityRemainders where
  area_ordered : AreaOrdered
  area_nested : AreaNested
  area_widths_shrink : AreaWidthsShrink
  circumference_nested : CircumferenceNested
  circumference_widths_shrink : CircumferenceWidthsShrink

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
this file, and the Leibniz and Machin algorithms are already valid.  What
remains is geometric validity for the two polygon algorithms, plus the two
bridges that connect the analytic definitions to the geometric one. -/
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

end PiProofs

end ComputableAnalysis
