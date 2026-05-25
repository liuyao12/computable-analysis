import ComputableAnalysis.RationalCircle
import ComputableAnalysis.ArctanGeometry
import ComputableAnalysis.Basic
import ComputableAnalysis.DirichletSeries
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
    piLeibniz.compute n =
      { lo := 4 * lo (RealRaw.scaleRatStage 4 n),
        hi := 4 * hi (RealRaw.scaleRatStage 4 n) } := by
  change (RealRaw.scaleRat (4 : Rat) leibnizSeries).compute n =
    { lo := 4 * lo (RealRaw.scaleRatStage 4 n),
      hi := 4 * hi (RealRaw.scaleRatStage 4 n) }
  have h4 : (0 : Rat) <= 4 := by native_decide
  simp [RealRaw.scaleRat, RealRaw.scaleRatCompute, h4,
    leibnizSeries_compute_eq (RealRaw.scaleRatStage 4 n)]

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
      4 / ((4 * RealRaw.scaleRatStage 4 n + 1 : Nat) : Rat) := by
  rw [compute_eq]
  unfold QInterval.width
  have hwidth := width_eq (RealRaw.scaleRatStage 4 n)
  rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem widths_shrink : RealRaw.WidthsShrinkToZero piLeibniz.compute := by
  intro eps
  refine ⟨eps.val.den + 1, ?_⟩
  intro n hn
  rw [compute_width_eq n]
  have hfour :
      4 / ((4 * RealRaw.scaleRatStage 4 n + 1 : Nat) : Rat) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((4 * RealRaw.scaleRatStage 4 n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2
        (by omega : 0 < 4 * RealRaw.scaleRatStage 4 n + 1)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : (4 : Rat) * B <= A := by
      dsimp [A, B]
      have hn_stage : n <= RealRaw.scaleRatStage 4 n :=
        RealRaw.le_scaleRatStage 4 n
      exact_mod_cast (by omega :
        4 * (eps.val.den + 1) <=
          4 * RealRaw.scaleRatStage 4 n + 1)
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
        ((Rat.natCast_pos).2
          (by omega : 0 < 4 * RealRaw.scaleRatStage 4 n + 1))))
  · constructor
    · intro n m hnm
      rw [compute_eq n, compute_eq m]
      have hstage :
          RealRaw.scaleRatStage 4 n <= RealRaw.scaleRatStage 4 m := by
        unfold RealRaw.scaleRatStage
        exact Nat.mul_le_mul_left (RealRaw.scaleRatPrecisionFactor 4) hnm
      constructor
      · exact Rat.mul_le_mul_of_nonneg_left
          (lo_mono hstage) (by native_decide : (0 : Rat) <= 4)
      · constructor
        · exact Rat.mul_le_mul_of_nonneg_left
            (interval_ordered (RealRaw.scaleRatStage 4 m))
            (by native_decide : (0 : Rat) <= 4)
        · exact Rat.mul_le_mul_of_nonneg_left
            (hi_anti hstage) (by native_decide : (0 : Rat) <= 4)
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

/-- The Leibniz series is equivalent to the power-series arctangent at `1`.

The proof is by stagewise equality of the two algorithms, but the public
mathematical statement is equivalence of raw reals. -/
theorem leibnizSeries_equiv_arctan_one :
    leibnizSeries.Equiv (arctan (1 : Rat)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hcompute :
      leibnizSeries.compute n = (arctan (1 : Rat)).compute n := by
    have hnonneg : (0 : Rat) <= 1 := by native_decide
    have hqabs : qabs (1 : Rat) = 1 := by native_decide
    rw [LeibnizValidity.leibnizSeries_compute_eq n]
    rw [ArctanValidity.arctan_compute_nonneg (1 : Rat) hnonneg n]
    rw [hqabs]
    simp [ArctanValidity.positiveRaw, ArctanValidity.lo,
      ArctanValidity.hi, arctan_one_state_eq_leibniz_state n]
  apply (RealRaw.compareAt_overlap_iff leibnizSeries (arctan (1 : Rat)) n n).2
  rw [hcompute]
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
  piCircleArea.innerBoundaryFrom (circleSamplePoint stage) k count

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
  piCircleArea.outerBoundaryFrom
    (circleSamplePoint stage) (outerTangentPoint stage) k count

def outerBoundary (stage : Nat) : List PiCirclePoint :=
  circleSamplePoint stage 0 :: outerBoundaryFrom stage 0 stage

def twiceSignedAreaAux
    (first prev : PiCirclePoint) : List PiCirclePoint -> Rat
  | vertices => piCircleArea.twiceSignedAreaAux pointCross first prev vertices

def twiceSignedArea : List PiCirclePoint -> Rat
  | [] => 0
  | first :: rest => twiceSignedAreaAux first first rest

def polygonArea (vertices : List PiCirclePoint) : Rat :=
  qabs (twiceSignedArea vertices / 2)

def innerQuarterArea (stage : Nat) : Rat :=
  polygonArea (originPoint :: innerBoundary stage)

def outerQuarterArea (stage : Nat) : Rat :=
  polygonArea (originPoint :: outerBoundary stage)

def piCircleAreaComputeAtStage (stage : Nat) : QInterval :=
  { lo := 4 * innerQuarterArea stage,
    hi := 4 * outerQuarterArea stage }

def piCircumferenceComputeAtStage (stage : Nat) : QInterval :=
  let precision := circumferenceSqrtPrecision stage
  let innerQuarter := rationalPointPathLength
    (piCircumference.innerBoundaryFrom (circleSamplePoint stage)
      0 (stage + 1)) precision
  let outerQuarter := rationalPointPathLength
    (circleSamplePoint stage 0 ::
      piCircumference.outerBoundaryFrom
        (circleSamplePoint stage) (outerTangentPoint stage) 0 stage) precision
  { lo := (4 * innerQuarter.lo) / 2,
    hi := (4 * outerQuarter.hi) / 2 }

def piCircumferenceCommonComputeAtStage (stage : Nat) : QInterval :=
  let precision := circumferenceSqrtPrecision stage
  let innerQuarter := rationalPointPathLength (innerBoundary stage) precision
  let outerQuarter := rationalPointPathLength (outerBoundary stage) precision
  { lo := (4 * innerQuarter.lo) / 2,
    hi := (4 * outerQuarter.hi) / 2 }

def innerQuarterLength (stage : Nat) : QInterval :=
  rationalPointPathLength (innerBoundary stage) (circumferenceSqrtPrecision stage)

def outerQuarterLength (stage : Nat) : QInterval :=
  rationalPointPathLength (outerBoundary stage) (circumferenceSqrtPrecision stage)

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
    piCircleArea.innerBoundaryFrom (circleSamplePoint stage) k count =
      innerBoundaryFrom stage k count := by
  rfl

theorem piCircumference_innerBoundaryFrom_eq
    (stage k count : Nat) :
    piCircumference.innerBoundaryFrom (circleSamplePoint stage) k count =
      innerBoundaryFrom stage k count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      simp [piCircumference.innerBoundaryFrom, piCircleArea.innerBoundaryFrom,
        innerBoundaryFrom, ih]

theorem piCircleArea_outerBoundaryFrom_eq
    (stage k count : Nat) :
    piCircleArea.outerBoundaryFrom
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
      simp [piCircumference.outerBoundaryFrom, piCircleArea.outerBoundaryFrom,
        outerBoundaryFrom, ih]

theorem piCircleArea_twiceSignedAreaAux_eq
    (first prev : PiCirclePoint) (vertices : List PiCirclePoint) :
    piCircleArea.twiceSignedAreaAux pointCross first prev vertices =
      twiceSignedAreaAux first prev vertices := by
  rfl

theorem innerBoundaryFrom_length (stage k count : Nat) :
    (innerBoundaryFrom stage k count).length = count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      unfold innerBoundaryFrom
      simp [piCircleArea.innerBoundaryFrom]
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
      simp [piCircleArea.outerBoundaryFrom]
      change (outerBoundaryFrom stage (k + 1) count).length + 1 + 1 =
        2 * (count + 1)
      rw [ih (k + 1)]
      omega

theorem outerBoundary_length (stage : Nat) :
    (outerBoundary stage).length = 2 * stage + 1 := by
  simp [outerBoundary, outerBoundaryFrom_length]

theorem piCircleArea_compute_eq (n : Nat) :
    piCircleArea.compute n = piCircleAreaComputeAtStage (piStage n) := by
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

theorem arctanGeometry_samplePoint_one_eq (stage k : Nat) :
    ArctanGeometry.samplePoint 1 stage k = circleSamplePoint stage k := by
  simp [ArctanGeometry.samplePoint, ArctanGeometry.parameter,
    ArctanGeometry.circlePoint, circleSamplePoint, circleParameter,
    circlePoint]

theorem arctanGeometry_tangentIntersection_eq
    (p q : PiCirclePoint) :
    ArctanGeometry.tangentIntersection p q = tangentIntersection p q := by
  simp [ArctanGeometry.tangentIntersection, tangentIntersection,
    ArctanGeometry.pointCross, pointCross]

theorem arctanGeometry_outerTangentPoint_one_eq (stage k : Nat) :
    ArctanGeometry.outerTangentPoint 1 stage k =
      outerTangentPoint stage k := by
  simp [ArctanGeometry.outerTangentPoint, outerTangentPoint,
    arctanGeometry_samplePoint_one_eq,
    arctanGeometry_tangentIntersection_eq]

theorem arctanGeometry_innerBoundaryFrom_one_eq
    (stage k count : Nat) :
    ArctanGeometry.innerBoundaryFrom 1 stage k count =
      innerBoundaryFrom stage k count := by
  unfold ArctanGeometry.innerBoundaryFrom innerBoundaryFrom
  induction count generalizing k with
  | zero =>
      simp [piCircleArea.innerBoundaryFrom]
  | succ count ih =>
      simp [piCircleArea.innerBoundaryFrom,
        arctanGeometry_samplePoint_one_eq, ih]

theorem arctanGeometry_innerBoundary_one_eq (stage : Nat) :
    ArctanGeometry.innerBoundary 1 stage = innerBoundary stage := by
  simp [ArctanGeometry.innerBoundary, innerBoundary,
    arctanGeometry_innerBoundaryFrom_one_eq]

theorem arctanGeometry_outerBoundaryFrom_one_eq
    (stage k count : Nat) :
    ArctanGeometry.outerBoundaryFrom 1 stage k count =
      outerBoundaryFrom stage k count := by
  unfold ArctanGeometry.outerBoundaryFrom outerBoundaryFrom
  induction count generalizing k with
  | zero =>
      simp [piCircleArea.outerBoundaryFrom]
  | succ count ih =>
      simp [piCircleArea.outerBoundaryFrom,
        arctanGeometry_samplePoint_one_eq,
        arctanGeometry_outerTangentPoint_one_eq, ih]

theorem arctanGeometry_outerBoundary_one_eq (stage : Nat) :
    ArctanGeometry.outerBoundary 1 stage = outerBoundary stage := by
  simp [ArctanGeometry.outerBoundary, outerBoundary,
    arctanGeometry_samplePoint_one_eq,
    arctanGeometry_outerBoundaryFrom_one_eq]

theorem arctanGeometry_twiceSignedAreaAux_eq
    (first prev : PiCirclePoint) (vertices : List PiCirclePoint) :
    ArctanGeometry.twiceSignedAreaAux first prev vertices =
      twiceSignedAreaAux first prev vertices := by
  rfl

theorem arctanGeometry_twiceSignedArea_eq
    (vertices : List PiCirclePoint) :
    ArctanGeometry.twiceSignedArea vertices = twiceSignedArea vertices := by
  cases vertices <;> rfl

theorem arctanGeometry_polygonArea_eq
    (vertices : List PiCirclePoint) :
    ArctanGeometry.polygonArea vertices = polygonArea vertices := by
  simp [ArctanGeometry.polygonArea, polygonArea,
    arctanGeometry_twiceSignedArea_eq]

theorem arctanGeometry_innerSectorArea_one_eq (stage : Nat) :
    ArctanGeometry.innerSectorArea 1 stage = innerQuarterArea stage := by
  simp [ArctanGeometry.innerSectorArea, innerQuarterArea,
    ArctanGeometry.originPoint, originPoint,
    arctanGeometry_innerBoundary_one_eq,
    arctanGeometry_polygonArea_eq]

theorem arctanGeometry_outerSectorArea_one_eq (stage : Nat) :
    ArctanGeometry.outerSectorArea 1 stage = outerQuarterArea stage := by
  simp [ArctanGeometry.outerSectorArea, outerQuarterArea,
    ArctanGeometry.originPoint, originPoint,
    arctanGeometry_outerBoundary_one_eq,
    arctanGeometry_polygonArea_eq]

theorem four_arctanGeom_one_compute_eq_piCircleArea_compute
    (n : Nat) :
    (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).compute n) =
      piCircleArea.compute (RealRaw.scaleRatStage 4 n) := by
  rw [piCircleArea_compute_eq (RealRaw.scaleRatStage 4 n)]
  change (RealRaw.scaleRat (4 : Rat)
      (ArctanGeometry.arctanGeom (1 : Rat))).compute n =
    piCircleAreaComputeAtStage (piStage (RealRaw.scaleRatStage 4 n))
  have hnonzero : ¬(1 : Rat) = 0 := by native_decide
  have hnonneg : (0 : Rat) <= 1 := by native_decide
  have hfour : (0 : Rat) <= 4 := by native_decide
  simp [ArctanGeometry.arctanGeom, hnonzero, hnonneg, hfour,
    ArctanGeometry.positiveRaw,
    ArctanGeometry.positiveComputeAtStage, ArctanGeometry.stage,
    piStage, piCircleAreaComputeAtStage, RealRaw.scaleRat,
    RealRaw.scaleRatCompute, arctanGeometry_innerSectorArea_one_eq,
    arctanGeometry_outerSectorArea_one_eq]

theorem fourArctanGeomOneValid_of_geometricValid
    (hGeomValid : ArctanGeometry.Valid) :
    (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).Valid) := by
  have hgeom : (ArctanGeometry.arctanGeom (1 : Rat)).Valid := by
    simpa [RealRaw.Valid, ArctanGeometry.functionRaw] using
      hGeomValid (1 : Rat) (by trivial)
  exact RealRaw.natScale_valid 4 hgeom

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
    (stage : Nat) (hstage : 0 < stage) (precision k : Nat) :
    (pointSegmentLengthInterval
      (circleSamplePoint stage k)
      (circleSamplePoint stage (k + 1)) precision).lo <=
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
    (circleSamplePoint stage (k + 1)) precision hnonneg hsq

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
      simp [innerBoundaryFrom, piCircleArea.innerBoundaryFrom,
        ConsecutiveCrossNonneg]
  | succ count ih =>
      cases count with
      | zero =>
          simp [innerBoundaryFrom, piCircleArea.innerBoundaryFrom,
            ConsecutiveCrossNonneg]
      | succ count =>
          simp [innerBoundaryFrom, piCircleArea.innerBoundaryFrom,
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
      simp [outerBoundaryFrom, piCircleArea.outerBoundaryFrom,
        ConsecutiveCrossNonneg]
  | succ count ih =>
      simp [outerBoundaryFrom, piCircleArea.outerBoundaryFrom,
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
      simp [outerBoundaryFrom, piCircleArea.outerBoundaryFrom,
        ConsecutiveCrossLe]
  | succ count ih =>
      simp [outerBoundaryFrom, piCircleArea.outerBoundaryFrom,
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
        piCircleArea.twiceSignedAreaAux]
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
    ConsecutiveCrossLe (circumferenceSqrtPrecision stage) (outerBoundary stage)
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
      (circumferenceSqrtPrecision stage)
      (outerBoundary stage) bounds.outerCrossLeLength

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
    ConsecutiveCrossLe (circumferenceSqrtPrecision stage) (outerBoundary stage)
  chordCross_le_tangentCrossSum :
    forall k,
      pointCross (circleSamplePoint stage k)
          (circleSamplePoint stage (k + 1)) <=
        outerTangentCrossSum stage k
  chordLengthLo_le_tangentCrossSum :
    forall k,
      (pointSegmentLengthInterval
        (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1))
        (circumferenceSqrtPrecision stage)).lo <=
        outerTangentCrossSum stage k

theorem localTangentBounds
    (stage : Nat) (hstage : 0 < stage) :
    LocalTangentBounds stage where
  innerCrossNonneg :=
    innerBoundary_consecutiveCrossNonneg stage hstage
  outerCrossNonneg :=
    outerBoundary_consecutiveCrossNonneg stage hstage
  outerCrossLeLength :=
    outerBoundary_consecutiveCrossLe stage hstage
      (circumferenceSqrtPrecision stage)
  chordCross_le_tangentCrossSum :=
    chordCross_le_outerTangentCrossSum stage hstage
  chordLengthLo_le_tangentCrossSum :=
    chordLengthLo_le_outerTangentCrossSum stage hstage
      (circumferenceSqrtPrecision stage)

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
        piCircleArea.innerBoundaryFrom, piCircleArea.outerBoundaryFrom,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
  | count + 1, k => by
      have hhead := hlocal k
      have htail :=
        innerEdgeCrosses_le_outerTangentEdgeCrosses
          stage hlocal count (k + 1)
      simp [innerBoundaryFrom, outerBoundaryFrom,
        piCircleArea.innerBoundaryFrom, piCircleArea.outerBoundaryFrom,
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
        piCircleArea.innerBoundaryFrom, piCircleArea.outerBoundaryFrom,
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
        piCircleArea.innerBoundaryFrom, piCircleArea.outerBoundaryFrom,
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
    outerBoundaryFrom, piCircleArea.innerBoundaryFrom,
    piCircleArea.outerBoundaryFrom, Fan.edgeCrossesFrom, Fan.sumRat,
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
          (circleSamplePoint stage (k + 1))
          (circumferenceSqrtPrecision stage)).lo <=
          outerTangentCrossSum stage k) :
    (innerQuarterLength stage).lo <=
      Fan.perimeter (outerFanWidths stage) := by
  let precision := circumferenceSqrtPrecision stage
  have h :=
    innerPathLo_le_outerTangentEdgeCrosses
      stage precision hlocal stage 0
  have h' :
      (rationalPointPathLength
        (circleSamplePoint stage 0 ::
          innerBoundaryFrom stage (0 + 1) stage) precision).lo <=
      0 + Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage 0)
          (outerBoundaryFrom stage 0 stage)) := by
    grind [Fan.perimeter]
  simpa [innerQuarterLength, outerFanWidths, innerBoundary, outerBoundary,
    Fan.sectorFanWidths, Fan.perimeter, innerBoundaryFrom,
    outerBoundaryFrom, piCircleArea.innerBoundaryFrom,
    piCircleArea.outerBoundaryFrom, Fan.edgeCrossesFrom, Fan.sumRat,
    pointCross_origin_left] using h'

theorem innerQuarterLength_lo_le_outerFanPerimeter
    (stage : Nat) (hstage : 0 < stage) :
    (innerQuarterLength stage).lo <=
      Fan.perimeter (outerFanWidths stage) :=
  innerQuarterLength_lo_le_outerFanPerimeter_of_adjacent
    stage (chordLengthLo_le_outerTangentCrossSum stage hstage
      (circumferenceSqrtPrecision stage))

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

theorem piCircleAreaComputeAtStage_ordered
    (stage : Nat) (hstage : 0 < stage) :
    0 <= (piCircleAreaComputeAtStage stage).width := by
  have h := innerQuarterArea_le_outerQuarterArea stage hstage
  have hscaled :
      4 * innerQuarterArea stage <= 4 * outerQuarterArea stage :=
    four_mul_le_four_mul h
  unfold piCircleAreaComputeAtStage QInterval.width
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

theorem piCircleArea_ordered (n : Nat) :
    0 <= (piCircleArea.compute n).width := by
  rw [piCircleArea_compute_eq]
  exact piCircleAreaComputeAtStage_ordered
    (piStage n) (piStage_pos n)

theorem piCircumference_ordered (n : Nat) :
    0 <= (piCircumference.compute n).width := by
  rw [piCircumference_compute_eq,
    piCircumferenceComputeAtStage_eq_common]
  exact piCircumferenceCommonComputeAtStage_ordered
    (piStage n) (piStage_pos n)

theorem areaLower_le_circumferenceUpper_of_finite
    (bounds : FiniteArchimedesBounds) (stage : Nat) (hstage : 0 < stage) :
    (piCircleAreaComputeAtStage stage).lo <=
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
  simpa [piCircleAreaComputeAtStage, piCircumferenceCommonComputeAtStage,
    outerQuarterLength] using hscaled

theorem circumferenceLower_le_areaUpper_of_finite
    (bounds : FiniteArchimedesBounds) (stage : Nat) (hstage : 0 < stage) :
    (piCircumferenceCommonComputeAtStage stage).lo <=
      (piCircleAreaComputeAtStage stage).hi := by
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
  simpa [piCircleAreaComputeAtStage, piCircumferenceCommonComputeAtStage,
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
    (bounds : FiniteArchimedesBounds) :
    AreaCircumferenceOverlapBounds where
  areaLower_le_circumferenceUpper := by
    intro n
    rw [piCircleArea_compute_eq, piCircumference_compute_eq,
      piCircumferenceComputeAtStage_eq_common]
    exact areaLower_le_circumferenceUpper_of_finite
      bounds (piStage n) (piStage_pos n)
  circumferenceLower_le_areaUpper := by
    intro n
    rw [piCircleArea_compute_eq, piCircumference_compute_eq,
      piCircumferenceComputeAtStage_eq_common]
    exact circumferenceLower_le_areaUpper_of_finite
      bounds (piStage n) (piStage_pos n)

theorem areaEqCircumference_of_finite
    (bounds : FiniteArchimedesBounds) :
    AreaEqCircumference :=
  areaEqCircumference_of_bounds
    (areaCircumferenceOverlapBounds_of_finite bounds)

/-- Archimedes' theorem: the polygonal area and circumference definitions of
pi determine the same computable real. -/
theorem archimedesTheorem : AreaEqCircumference :=
  areaEqCircumference_of_finite finiteArchimedesBounds

/-- Validity certificates for the four public pi algorithms. -/
structure ValidityProofs where
  leibniz : LeibnizValid
  machin : MachinValid
  area : AreaValid
  circumference : CircumferenceValid

def AreaNested : Prop :=
  forall n m, n <= m ->
    (piCircleArea.compute n).lo <= (piCircleArea.compute m).lo /\
    (piCircleArea.compute m).lo <= (piCircleArea.compute m).hi /\
    (piCircleArea.compute m).hi <= (piCircleArea.compute n).hi

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

def AreaPositivePrecision : Prop :=
  RealRaw.PositivePrecisionBound piCircleArea.compute

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

def CircumferencePositivePrecision : Prop :=
  RealRaw.PositivePrecisionBound piCircumference.compute

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

def AreaStepRefines : Prop :=
  EndpointStepRefines piCircleArea.compute

def CircumferenceStepRefines : Prop :=
  EndpointStepRefines piCircumference.compute

/-!
Dyadic refinement should not be proved by attacking the full interval
endpoint inequalities directly.  The geometric content is local: one coarse
arc is split into two fine arcs, and a small cell inequality says the
inscribed quantity improves while the circumscribed quantity shrinks.  The
definitions below isolate that local target and then provide the thin wrapper
that turns stage-to-stage refinement into the public `EndpointStepRefines`
obligations.
-/

theorem piStage_succ (n : Nat) :
    piStage (n + 1) = 2 * piStage n := by
  unfold piStage
  simpa [Nat.mul_comm] using (Nat.pow_succ 2 n)

theorem circleSamplePoint_refine_even (stage k : Nat) :
    circleSamplePoint (2 * stage) (2 * k) =
      circleSamplePoint stage k := by
  simpa [rationalCircleStage, RationalCircle.Stage.refineIndex]
    using RationalCircle.Stage.samplePoint_refineIndex_of_refinement
      (coarse := rationalCircleStage stage)
      (fine := rationalCircleStage (2 * stage))
      (by rfl)
      k

theorem circleSamplePoint_refine_succ_even (stage k : Nat) :
    circleSamplePoint (2 * stage) (2 * k + 2) =
      circleSamplePoint stage (k + 1) := by
  have h :=
    RationalCircle.Stage.samplePoint_refineIndex_of_refinement
      (coarse := rationalCircleStage stage)
      (fine := rationalCircleStage (2 * stage))
      (by rfl)
      (k + 1)
  simpa [rationalCircleStage, RationalCircle.Stage.refineIndex, Nat.mul_add,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def InnerAreaCellSplitBound (stage k : Nat) : Prop :=
  pointCross (circleSamplePoint stage k) (circleSamplePoint stage (k + 1)) <=
    pointCross
        (circleSamplePoint (2 * stage) (2 * k))
        (circleSamplePoint (2 * stage) (2 * k + 1)) +
      pointCross
        (circleSamplePoint (2 * stage) (2 * k + 1))
        (circleSamplePoint (2 * stage) (2 * k + 2))

def OuterAreaCellSplitBound (stage k : Nat) : Prop :=
  outerTangentCrossSum (2 * stage) (2 * k) +
      outerTangentCrossSum (2 * stage) (2 * k + 1) <=
    outerTangentCrossSum stage k

def InnerLengthCellSplitBound (stage k : Nat) : Prop :=
  (pointSegmentLengthInterval
      (circleSamplePoint stage k)
      (circleSamplePoint stage (k + 1))
      (circumferenceSqrtPrecision stage)).lo <=
    (pointSegmentLengthInterval
        (circleSamplePoint (2 * stage) (2 * k))
        (circleSamplePoint (2 * stage) (2 * k + 1))
        (circumferenceSqrtPrecision (2 * stage))).lo +
      (pointSegmentLengthInterval
        (circleSamplePoint (2 * stage) (2 * k + 1))
        (circleSamplePoint (2 * stage) (2 * k + 2))
        (circumferenceSqrtPrecision (2 * stage))).lo

def OuterLengthCellSplitBound (stage k : Nat) : Prop :=
  (pointSegmentLengthInterval
        (circleSamplePoint (2 * stage) (2 * k))
        (outerTangentPoint (2 * stage) (2 * k))
        (circumferenceSqrtPrecision (2 * stage))).hi +
      (pointSegmentLengthInterval
        (outerTangentPoint (2 * stage) (2 * k))
        (circleSamplePoint (2 * stage) (2 * k + 1))
        (circumferenceSqrtPrecision (2 * stage))).hi +
      ((pointSegmentLengthInterval
        (circleSamplePoint (2 * stage) (2 * k + 1))
        (outerTangentPoint (2 * stage) (2 * k + 1))
        (circumferenceSqrtPrecision (2 * stage))).hi +
      (pointSegmentLengthInterval
        (outerTangentPoint (2 * stage) (2 * k + 1))
        (circleSamplePoint (2 * stage) (2 * k + 2))
        (circumferenceSqrtPrecision (2 * stage))).hi) <=
    (pointSegmentLengthInterval
      (circleSamplePoint stage k)
      (outerTangentPoint stage k)
      (circumferenceSqrtPrecision stage)).hi +
      (pointSegmentLengthInterval
        (outerTangentPoint stage k)
        (circleSamplePoint stage (k + 1))
        (circumferenceSqrtPrecision stage)).hi

/-- Determinant identity behind the local inner-area split.  Multiplying by the
positive rational denominator keeps the algebra in polynomial form. -/
theorem pointCross_split_difference_mul_den
    (u v w : Rat) :
    let du := 1 + u * u
    let dv := 1 + v * v
    let dw := 1 + w * w
    (RationalCircle.Stage.cross
        (RationalCircle.Stage.point u)
        (RationalCircle.Stage.point v) +
      RationalCircle.Stage.cross
        (RationalCircle.Stage.point v)
        (RationalCircle.Stage.point w) -
      RationalCircle.Stage.cross
        (RationalCircle.Stage.point u)
        (RationalCircle.Stage.point w)) *
        (du * dv * dw) =
      4 * (v - u) * (w - u) * (w - v) := by
  dsimp
  rw [RationalCircle.Stage.point_cross_formula,
    RationalCircle.Stage.point_cross_formula,
    RationalCircle.Stage.point_cross_formula]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hdupos : 0 < 1 + u * u :=
    RationalCircle.Stage.one_add_square_pos u
  have hdvpos : 0 < 1 + v * v :=
    RationalCircle.Stage.one_add_square_pos v
  have hdwpos : 0 < 1 + w * w :=
    RationalCircle.Stage.one_add_square_pos w
  have hdune : 1 + u * u ≠ 0 := Rat.ne_of_gt hdupos
  have hdvne : 1 + v * v ≠ 0 := Rat.ne_of_gt hdvpos
  have hdwne : 1 + w * w ≠ 0 := Rat.ne_of_gt hdwpos
  have hduvne : (1 + u * u) * (1 + v * v) ≠ 0 :=
    Rat.ne_of_gt (Rat.mul_pos hdupos hdvpos)
  have hdvwne : (1 + v * v) * (1 + w * w) ≠ 0 :=
    Rat.ne_of_gt (Rat.mul_pos hdvpos hdwpos)
  have hduwne : (1 + u * u) * (1 + w * w) ≠ 0 :=
    Rat.ne_of_gt (Rat.mul_pos hdupos hdwpos)
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_rev,
    Rat.mul_inv_cancel]

theorem pointCross_split_le
    {u v w : Rat} (huv : u <= v) (hvw : v <= w) :
    RationalCircle.Stage.cross
        (RationalCircle.Stage.point u)
        (RationalCircle.Stage.point w) <=
      RationalCircle.Stage.cross
          (RationalCircle.Stage.point u)
          (RationalCircle.Stage.point v) +
        RationalCircle.Stage.cross
          (RationalCircle.Stage.point v)
          (RationalCircle.Stage.point w) := by
  let x :=
    RationalCircle.Stage.cross
        (RationalCircle.Stage.point u)
        (RationalCircle.Stage.point v) +
      RationalCircle.Stage.cross
        (RationalCircle.Stage.point v)
        (RationalCircle.Stage.point w) -
      RationalCircle.Stage.cross
        (RationalCircle.Stage.point u)
        (RationalCircle.Stage.point w)
  let den := (1 + u * u) * (1 + v * v) * (1 + w * w)
  have hdenpos : 0 < den := by
    dsimp [den]
    exact Rat.mul_pos
      (Rat.mul_pos
        (RationalCircle.Stage.one_add_square_pos u)
        (RationalCircle.Stage.one_add_square_pos v))
      (RationalCircle.Stage.one_add_square_pos w)
  have hdiff1 : 0 <= v - u := by
    grind [Rat.sub_eq_add_neg]
  have hdiff2 : 0 <= w - u := by
    grind [Rat.sub_eq_add_neg]
  have hdiff3 : 0 <= w - v := by
    grind [Rat.sub_eq_add_neg]
  have hnum : 0 <= 4 * (v - u) * (w - u) * (w - v) := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg
        (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 4) hdiff1)
        hdiff2)
      hdiff3
  have hmul : x * den = 4 * (v - u) * (w - u) * (w - v) := by
    dsimp [x, den]
    simpa using pointCross_split_difference_mul_den u v w
  have hx_nonneg : 0 <= x := by
    apply Rat.le_of_mul_le_mul_right (c := den)
    · simpa [hmul] using hnum
    · exact hdenpos
  dsimp [x] at hx_nonneg
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- Rational simplification for a tangent-width expression.  This is kept
separate from the circle formulas so the geometric step below reduces to a
small algebraic cancellation. -/
theorem tangentWidth_div_simplify
    {A B D : Rat} (hApos : 0 < A) (hB : B ≠ 0) (hD : D ≠ 0) :
    (2 * D * D / A) / (2 * D * B / A) +
      (2 * D * D / A) / (2 * D * B / A) =
      2 * D / B := by
  simp only [Rat.div_def]
  have hA : A ≠ 0 := Rat.ne_of_gt hApos
  have h2 : (2 : Rat) ≠ 0 := by native_decide
  have h2D : 2 * D ≠ 0 := by
    intro h
    have h' : (2 : Rat) = 0 ∨ D = 0 := Rat.mul_eq_zero.mp h
    cases h' with
    | inl htwo => exact h2 htwo
    | inr hD0 => exact hD hD0
  have h2DB : 2 * D * B ≠ 0 := by
    intro h
    have h' : 2 * D = 0 ∨ B = 0 := Rat.mul_eq_zero.mp h
    cases h' with
    | inl h2D0 => exact h2D h2D0
    | inr hB0 => exact hB hB0
  have hAinvpos : 0 < A⁻¹ := (Rat.inv_pos).2 hApos
  have hAinv : A⁻¹ ≠ 0 := Rat.ne_of_gt hAinvpos
  have _hden : 2 * D * B * A⁻¹ ≠ 0 := by
    intro h
    have h' : 2 * D * B = 0 ∨ A⁻¹ = 0 := Rat.mul_eq_zero.mp h
    cases h' with
    | inl h2DB0 => exact h2DB h2DB0
    | inr hA0 => exact hAinv hA0
  have hc1 : (2 * D * B * A⁻¹)⁻¹ = A * (2 * D * B)⁻¹ := by
    rw [Rat.inv_mul_rev]
    rw [Rat.inv_inv]
  have hc2 : (2 * D * B)⁻¹ = B⁻¹ * (2 * D)⁻¹ := by
    rw [Rat.inv_mul_rev]
  rw [hc1, hc2]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
    Rat.add_assoc, Rat.add_comm]

/-- Exact rational formula for the two tangent fan widths over the chord
between parameters `u` and `v`. -/
theorem pointTangentCrossSum_formula_of_lt
    {u v : Rat} (hu : 0 <= u) (hv : 0 <= v) (huv : u < v) :
    RationalCircle.Stage.cross (RationalCircle.Stage.point u)
        (RationalCircle.Stage.tangentIntersection
          (RationalCircle.Stage.point u) (RationalCircle.Stage.point v)) +
      RationalCircle.Stage.cross
        (RationalCircle.Stage.tangentIntersection
          (RationalCircle.Stage.point u) (RationalCircle.Stage.point v))
        (RationalCircle.Stage.point v) =
      2 * (v - u) / (1 + u * v) := by
  rw [RationalCircle.Stage.cross_left_tangentIntersection
    (RationalCircle.Stage.point_normSq_unit u)]
  rw [RationalCircle.Stage.cross_tangentIntersection_right
    (RationalCircle.Stage.point_normSq_unit v)]
  rw [RationalCircle.Stage.one_sub_point_dot_formula]
  rw [RationalCircle.Stage.point_cross_formula]
  let A := (1 + u * u) * (1 + v * v)
  let B := 1 + u * v
  let D := v - u
  have hApos : 0 < A := by
    dsimp [A]
    exact Rat.mul_pos (RationalCircle.Stage.one_add_square_pos u)
      (RationalCircle.Stage.one_add_square_pos v)
  have hBpos : 0 < B := by
    dsimp [B]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hu hv
  have hB : B ≠ 0 := Rat.ne_of_gt hBpos
  have hDpos : 0 < D := by
    dsimp [D]
    grind [Rat.sub_eq_add_neg]
  have hD : D ≠ 0 := Rat.ne_of_gt hDpos
  simpa [A, B, D] using
    tangentWidth_div_simplify (A := A) (B := B) (D := D)
      hApos hB hD

/-- Denominator-cleared identity for the tangent-width split. -/
theorem tangentWidth_split_difference_mul_den_of_nonneg
    {u v w : Rat} (hu : 0 <= u) (hv : 0 <= v) (hw : 0 <= w) :
    let A := 1 + u * v
    let B := 1 + v * w
    let C := 1 + u * w
    (2 * (w - u) / C -
        (2 * (v - u) / A + 2 * (w - v) / B)) * (A * B * C) =
      2 * (v - u) * (w - v) * (w - u) := by
  dsimp
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hApos : 0 < 1 + u * v :=
    RationalCircle.Stage.one_add_mul_pos_of_nonneg hu hv
  have hBpos : 0 < 1 + v * w :=
    RationalCircle.Stage.one_add_mul_pos_of_nonneg hv hw
  have hCpos : 0 < 1 + u * w :=
    RationalCircle.Stage.one_add_mul_pos_of_nonneg hu hw
  have hA : 1 + u * v ≠ 0 := Rat.ne_of_gt hApos
  have hB : 1 + v * w ≠ 0 := Rat.ne_of_gt hBpos
  have hC : 1 + u * w ≠ 0 := Rat.ne_of_gt hCpos
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_rev,
    Rat.mul_inv_cancel]

theorem tangentWidth_split_le
    {u v w : Rat} (hu : 0 <= u) (huv : u <= v) (hvw : v <= w) :
    2 * (v - u) / (1 + u * v) +
        2 * (w - v) / (1 + v * w) <=
      2 * (w - u) / (1 + u * w) := by
  have hv : 0 <= v := Rat.le_trans hu huv
  have hw : 0 <= w := Rat.le_trans hv hvw
  let A := 1 + u * v
  let B := 1 + v * w
  let C := 1 + u * w
  let den := A * B * C
  have hApos : 0 < A := by
    dsimp [A]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hu hv
  have hBpos : 0 < B := by
    dsimp [B]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hv hw
  have hCpos : 0 < C := by
    dsimp [C]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hu hw
  have hdenpos : 0 < den := by
    dsimp [den]
    exact Rat.mul_pos (Rat.mul_pos hApos hBpos) hCpos
  have hdiffmul :=
    tangentWidth_split_difference_mul_den_of_nonneg
      (u := u) (v := v) (w := w) hu hv hw
  have hnonnegRhs : 0 <= 2 * (v - u) * (w - v) * (w - u) := by
    have h1 : 0 <= v - u := by grind [Rat.sub_eq_add_neg]
    have h2 : 0 <= w - v := by grind [Rat.sub_eq_add_neg]
    have h3 : 0 <= w - u := by grind [Rat.sub_eq_add_neg]
    exact Rat.mul_nonneg
      (Rat.mul_nonneg
        (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) h1) h2)
      h3
  have hdiffmul_nonneg :
      0 <= (2 * (w - u) / C -
          (2 * (v - u) / A + 2 * (w - v) / B)) * den := by
    rw [show (2 * (w - u) / C -
          (2 * (v - u) / A + 2 * (w - v) / B)) * den =
        2 * (v - u) * (w - v) * (w - u) by
          simpa [A, B, C, den] using hdiffmul]
    exact hnonnegRhs
  have hdiff_nonneg :
      0 <= 2 * (w - u) / C -
        (2 * (v - u) / A + 2 * (w - v) / B) := by
    have hzero : (0 : Rat) * den <=
        (2 * (w - u) / C -
          (2 * (v - u) / A + 2 * (w - v) / B)) * den := by
      simpa using hdiffmul_nonneg
    exact Rat.le_of_mul_le_mul_right hzero hdenpos
  dsimp [A, B, C] at hdiff_nonneg
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem circleParameter_refine_even (stage k : Nat) :
    circleParameter (2 * stage) (2 * k) = circleParameter stage k := by
  simpa [rationalCircleStage, RationalCircle.Stage.refineIndex,
    RationalCircle.Stage.parameter, circleParameter]
    using RationalCircle.Stage.parameter_refineIndex_of_refinement
      (coarse := rationalCircleStage stage)
      (fine := rationalCircleStage (2 * stage))
      (by rfl)
      k

theorem circleParameter_refine_succ_even (stage k : Nat) :
    circleParameter (2 * stage) (2 * k + 2) =
      circleParameter stage (k + 1) := by
  have h :=
    RationalCircle.Stage.parameter_refineIndex_of_refinement
      (coarse := rationalCircleStage stage)
      (fine := rationalCircleStage (2 * stage))
      (by rfl)
      (k + 1)
  simpa [rationalCircleStage, RationalCircle.Stage.refineIndex,
    RationalCircle.Stage.parameter, circleParameter, Nat.mul_add,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem outerTangentCrossSum_eq_parameter_formula
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    outerTangentCrossSum stage k =
      2 * (circleParameter stage (k + 1) - circleParameter stage k) /
        (1 + circleParameter stage k * circleParameter stage (k + 1)) := by
  let S := rationalCircleStage stage
  let u := S.parameter k
  let v := S.parameter (k + 1)
  have hu : 0 <= u := by
    dsimp [u, S, rationalCircleStage]
    exact RationalCircle.Stage.parameter_nonneg
      (rationalCircleStage stage) hstage k
  have huvle : u <= v := by
    dsimp [u, v, S]
    exact RationalCircle.Stage.parameter_mono
      (rationalCircleStage stage) hstage (Nat.le_succ k)
  have hv : 0 <= v := Rat.le_trans hu huvle
  have huv : u < v := by
    have hgap : v - u = 1 / (stage : Rat) := by
      dsimp [u, v, S, rationalCircleStage]
      simpa using
        RationalCircle.Stage.parameter_succ_sub
          (rationalCircleStage stage) k
    have hgap_pos : 0 < v - u := by
      rw [hgap, Rat.div_def, Rat.one_mul]
      exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hstage)
    grind [Rat.sub_eq_add_neg]
  have hformula := pointTangentCrossSum_formula_of_lt hu hv huv
  simpa [S, u, v, rationalCircleStage, outerTangentCrossSum,
    outerTangentPoint, circleSamplePoint, circleParameter, circlePoint,
    pointCross, tangentIntersection, RationalCircle.Stage.samplePoint,
    RationalCircle.Stage.parameter, RationalCircle.Stage.point,
    RationalCircle.Stage.cross, RationalCircle.Stage.tangentIntersection]
    using hformula

theorem outerAreaCellSplitBound
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    OuterAreaCellSplitBound stage k := by
  unfold OuterAreaCellSplitBound
  have hfine : 0 < 2 * stage := by omega
  rw [outerTangentCrossSum_eq_parameter_formula (2 * stage) hfine (2 * k)]
  rw [outerTangentCrossSum_eq_parameter_formula (2 * stage) hfine (2 * k + 1)]
  rw [outerTangentCrossSum_eq_parameter_formula stage hstage k]
  let u := circleParameter (2 * stage) (2 * k)
  let v := circleParameter (2 * stage) (2 * k + 1)
  let w := circleParameter (2 * stage) (2 * k + 1 + 1)
  have hu : 0 <= u := by
    dsimp [u, circleParameter]
    exact RationalCircle.Stage.parameter_nonneg
      (rationalCircleStage (2 * stage)) hfine (2 * k)
  have huv : u <= v := by
    dsimp [u, v, circleParameter]
    exact RationalCircle.Stage.parameter_mono
      (rationalCircleStage (2 * stage)) hfine (by omega)
  have hvw : v <= w := by
    dsimp [v, w, circleParameter]
    exact RationalCircle.Stage.parameter_mono
      (rationalCircleStage (2 * stage)) hfine (by omega)
  have hsplit := tangentWidth_split_le hu huv hvw
  have hlast :
      circleParameter (2 * stage) (2 * k + 1 + 1) =
        circleParameter stage (k + 1) :=
    by
      have hidx : 2 * k + 1 + 1 = 2 + 2 * k := by omega
      rw [hidx]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using circleParameter_refine_succ_even stage k
  have hfirst :
      circleParameter (2 * stage) (2 * k) =
        circleParameter stage k :=
    circleParameter_refine_even stage k
  have hlastNorm :
      circleParameter (2 * stage) (1 + (1 + 2 * k)) =
        circleParameter stage (k + 1) := by
    have hidx : 1 + (1 + 2 * k) = 2 * k + 1 + 1 := by omega
    rw [hidx]
    exact hlast
  simpa [u, v, w, hfirst, hlast, hlastNorm, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hsplit

theorem innerAreaCellSplitBound
    (stage : Nat) (hstage : 0 < stage) (k : Nat) :
    InnerAreaCellSplitBound stage k := by
  unfold InnerAreaCellSplitBound
  rw [← circleSamplePoint_refine_even stage k,
    ← circleSamplePoint_refine_succ_even stage k]
  let S := rationalCircleStage (2 * stage)
  have hS : 0 < S.subdivisions := by
    dsimp [S, rationalCircleStage]
    omega
  have h01 : S.parameter (2 * k) <= S.parameter (2 * k + 1) :=
    RationalCircle.Stage.parameter_mono S hS (by omega)
  have h12 : S.parameter (2 * k + 1) <= S.parameter (2 * k + 2) :=
    RationalCircle.Stage.parameter_mono S hS (by omega)
  have hsplit := pointCross_split_le h01 h12
  simpa [S, rationalCircleStage, circleSamplePoint, circlePoint,
    circleParameter, pointCross, RationalCircle.Stage.samplePoint,
    RationalCircle.Stage.parameter, RationalCircle.Stage.point,
    RationalCircle.Stage.cross] using hsplit

structure DyadicCellRefinementBounds (stage : Nat) where
  inner_area :
    forall k, k < stage -> InnerAreaCellSplitBound stage k
  outer_area :
    forall k, k < stage -> OuterAreaCellSplitBound stage k
  inner_length :
    forall k, k < stage -> InnerLengthCellSplitBound stage k
  outer_length :
    forall k, k < stage -> OuterLengthCellSplitBound stage k

theorem innerEdgeCrosses_le_refinedInnerEdgeCrosses
    (stage : Nat)
    (hlocal : forall k, k < stage -> InnerAreaCellSplitBound stage k) :
    forall count k, k + count <= stage ->
      Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage k)
          (innerBoundaryFrom stage (k + 1) count)) <=
      Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint (2 * stage) (2 * k))
          (innerBoundaryFrom (2 * stage) (2 * k + 1) (2 * count)))
  | 0, k, _hbound => by
      simp [innerBoundaryFrom, piCircleArea.innerBoundaryFrom,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
  | count + 1, k, hbound => by
      have hk : k < stage := by omega
      have htailBound : k + 1 + count <= stage := by omega
      have hhead := hlocal k hk
      have htail :=
        innerEdgeCrosses_le_refinedInnerEdgeCrosses
          stage hlocal count (k + 1) htailBound
      simp [innerBoundaryFrom, piCircleArea.innerBoundaryFrom,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
      calc
        pointCross (circleSamplePoint stage k)
            (circleSamplePoint stage (k + 1)) +
          Fan.sumRat
            (Fan.edgeCrossesFrom
              (circleSamplePoint stage (k + 1))
              (innerBoundaryFrom stage (k + 2) count)) <=
          (pointCross (circleSamplePoint (2 * stage) (2 * k))
              (circleSamplePoint (2 * stage) (2 * k + 1)) +
            pointCross (circleSamplePoint (2 * stage) (2 * k + 1))
              (circleSamplePoint (2 * stage) (2 * k + 2))) +
          Fan.sumRat
            (Fan.edgeCrossesFrom
              (circleSamplePoint (2 * stage) (2 * (k + 1)))
              (innerBoundaryFrom (2 * stage) (2 * (k + 1) + 1)
                (2 * count))) := by
            exact Fan.rat_add_le_add hhead htail
        _ =
          pointCross (circleSamplePoint (2 * stage) (2 * k))
              (circleSamplePoint (2 * stage) (2 * k + 1)) +
          (pointCross (circleSamplePoint (2 * stage) (2 * k + 1))
              (circleSamplePoint (2 * stage) (2 * k + 2)) +
            Fan.sumRat
              (Fan.edgeCrossesFrom
                (circleSamplePoint (2 * stage) (2 * k + 2))
                (innerBoundaryFrom (2 * stage) (2 * k + 3)
                  (2 * count)))) := by
            grind [Nat.mul_add, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm, Rat.add_assoc, Rat.add_comm]

theorem innerFanPerimeter_le_refinedInnerFanPerimeter
    (stage : Nat)
    (hlocal : forall k, k < stage -> InnerAreaCellSplitBound stage k) :
    Fan.perimeter (innerFanWidths stage) <=
      Fan.perimeter (innerFanWidths (2 * stage)) := by
  have h :=
    innerEdgeCrosses_le_refinedInnerEdgeCrosses
      stage hlocal stage 0 (by omega)
  have h' :
      0 + Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage 0)
          (innerBoundaryFrom stage (0 + 1) stage)) <=
      0 + Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint (2 * stage) (2 * 0))
          (innerBoundaryFrom (2 * stage) (2 * 0 + 1) (2 * stage))) := by
    exact (Rat.add_le_add_left).2 h
  simpa [innerFanWidths, innerBoundary, Fan.sectorFanWidths,
    Fan.perimeter, innerBoundaryFrom, piCircleArea.innerBoundaryFrom,
    Fan.edgeCrossesFrom, Fan.sumRat, pointCross_origin_left] using h'

theorem innerQuarterArea_mono_of_inner_area_cell_bounds
    (stage : Nat) (hstage : 0 < stage)
    (hlocal : forall k, k < stage -> InnerAreaCellSplitBound stage k) :
    innerQuarterArea stage <= innerQuarterArea (2 * stage) := by
  have hper :=
    innerFanPerimeter_le_refinedInnerFanPerimeter stage hlocal
  have hnonnegCoarse : 0 <= Fan.sumRat (innerFanWidths stage) :=
    Fan.sumRat_nonneg (innerFanWidths stage)
      (sectorFanBounds stage hstage).innerWidths_nonneg
  have hfinePos : 0 < 2 * stage := by omega
  have hnonnegFine : 0 <= Fan.sumRat (innerFanWidths (2 * stage)) :=
    Fan.sumRat_nonneg (innerFanWidths (2 * stage))
      (sectorFanBounds (2 * stage) hfinePos).innerWidths_nonneg
  rw [innerQuarterArea_eq_variable_unit_fan stage hnonnegCoarse]
  rw [innerQuarterArea_eq_variable_unit_fan (2 * stage) hnonnegFine]
  rw [innerFanPieces, innerFanPieces]
  rw [Fan.variableArea_unitPieces_eq_area,
    Fan.variableArea_unitPieces_eq_area]
  rw [Fan.area_one_eq_half_perimeter,
    Fan.area_one_eq_half_perimeter]
  exact div_two_le_div_two hper

theorem refinedOuterEdgeCrosses_le_outerEdgeCrosses
    (stage : Nat)
    (hlocal : forall k, k < stage -> OuterAreaCellSplitBound stage k) :
    forall count k, k + count <= stage ->
      Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint (2 * stage) (2 * k))
          (outerBoundaryFrom (2 * stage) (2 * k) (2 * count))) <=
      Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage k)
          (outerBoundaryFrom stage k count))
  | 0, k, _hbound => by
      simp [outerBoundaryFrom, piCircleArea.outerBoundaryFrom,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
  | count + 1, k, hbound => by
      have hk : k < stage := by omega
      have htailBound : k + 1 + count <= stage := by omega
      have hhead := hlocal k hk
      have htail :=
        refinedOuterEdgeCrosses_le_outerEdgeCrosses
          stage hlocal count (k + 1) htailBound
      simp [outerBoundaryFrom, piCircleArea.outerBoundaryFrom,
        Fan.edgeCrossesFrom, Fan.perimeter, Fan.sumRat]
      calc
        pointCross (circleSamplePoint (2 * stage) (2 * k))
            (outerTangentPoint (2 * stage) (2 * k)) +
          (pointCross (outerTangentPoint (2 * stage) (2 * k))
              (circleSamplePoint (2 * stage) (2 * k + 1)) +
            (pointCross (circleSamplePoint (2 * stage) (2 * k + 1))
                (outerTangentPoint (2 * stage) (2 * k + 1)) +
              (pointCross (outerTangentPoint (2 * stage) (2 * k + 1))
                  (circleSamplePoint (2 * stage) (2 * k + 1 + 1)) +
                Fan.sumRat
                  (Fan.edgeCrossesFrom
                    (circleSamplePoint (2 * stage) (2 * k + 1 + 1))
                    (outerBoundaryFrom (2 * stage) (2 * k + 1 + 1)
                      (2 * count)))))) <=
          outerTangentCrossSum stage k +
            Fan.sumRat
              (Fan.edgeCrossesFrom
                (circleSamplePoint stage (k + 1))
                (outerBoundaryFrom stage (k + 1) count)) := by
            have hcombined := Fan.rat_add_le_add hhead htail
            have hidx : 2 + 2 * k = 1 + (1 + 2 * k) := by omega
            simpa [OuterAreaCellSplitBound, outerTangentCrossSum,
              Fan.perimeter, hidx, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm, Rat.add_assoc, Rat.add_comm] using hcombined
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

theorem refinedOuterFanPerimeter_le_outerFanPerimeter
    (stage : Nat)
    (hlocal : forall k, k < stage -> OuterAreaCellSplitBound stage k) :
    Fan.perimeter (outerFanWidths (2 * stage)) <=
      Fan.perimeter (outerFanWidths stage) := by
  have h :=
    refinedOuterEdgeCrosses_le_outerEdgeCrosses
      stage hlocal stage 0 (by omega)
  have h' :
      0 + Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint (2 * stage) (2 * 0))
          (outerBoundaryFrom (2 * stage) (2 * 0) (2 * stage))) <=
      0 + Fan.perimeter
        (Fan.edgeCrossesFrom
          (circleSamplePoint stage 0)
          (outerBoundaryFrom stage 0 stage)) := by
    exact (Rat.add_le_add_left).2 h
  simpa [outerFanWidths, outerBoundary, Fan.sectorFanWidths,
    Fan.perimeter, outerBoundaryFrom, piCircleArea.outerBoundaryFrom,
    Fan.edgeCrossesFrom, Fan.sumRat, pointCross_origin_left] using h'

theorem outerQuarterArea_antitone_of_outer_area_cell_bounds
    (stage : Nat) (hstage : 0 < stage)
    (hlocal : forall k, k < stage -> OuterAreaCellSplitBound stage k) :
    outerQuarterArea (2 * stage) <= outerQuarterArea stage := by
  have hper :=
    refinedOuterFanPerimeter_le_outerFanPerimeter stage hlocal
  have hnonnegCoarse : 0 <= Fan.sumRat (outerFanWidths stage) :=
    (sectorFanBounds stage hstage).outerWidths_sum_nonneg
  have hfinePos : 0 < 2 * stage := by omega
  have hnonnegFine : 0 <= Fan.sumRat (outerFanWidths (2 * stage)) :=
    (sectorFanBounds (2 * stage) hfinePos).outerWidths_sum_nonneg
  rw [outerQuarterArea_eq_area_one stage hnonnegCoarse]
  rw [outerQuarterArea_eq_area_one (2 * stage) hnonnegFine]
  rw [Fan.area_one_eq_half_perimeter,
    Fan.area_one_eq_half_perimeter]
  exact div_two_le_div_two hper

structure AreaStageRefines (coarse fine : Nat) where
  innerQuarterArea_mono :
    innerQuarterArea coarse <= innerQuarterArea fine
  outerQuarterArea_antitone :
    outerQuarterArea fine <= outerQuarterArea coarse

theorem areaStageRefines_of_area_cell_bounds
    (stage : Nat) (hstage : 0 < stage)
    (hinner : forall k, k < stage -> InnerAreaCellSplitBound stage k)
    (houter : forall k, k < stage -> OuterAreaCellSplitBound stage k) :
    AreaStageRefines stage (2 * stage) where
  innerQuarterArea_mono :=
    innerQuarterArea_mono_of_inner_area_cell_bounds
      stage hstage hinner
  outerQuarterArea_antitone :=
    outerQuarterArea_antitone_of_outer_area_cell_bounds
      stage hstage houter

theorem areaStageRefines_rationalCircle
    (stage : Nat) (hstage : 0 < stage) :
    AreaStageRefines stage (2 * stage) :=
  areaStageRefines_of_area_cell_bounds
    stage hstage
    (fun k _hk => innerAreaCellSplitBound stage hstage k)
    (fun k _hk => outerAreaCellSplitBound stage hstage k)

structure CircumferenceStageRefines (coarse fine : Nat) where
  innerQuarterLength_mono :
    (innerQuarterLength coarse).lo <= (innerQuarterLength fine).lo
  outerQuarterLength_antitone :
    (outerQuarterLength fine).hi <= (outerQuarterLength coarse).hi

theorem rationalPointPathLength_cons_cons_lo
    (p q : PiCirclePoint) (rest : List PiCirclePoint) (n : Nat) :
    (rationalPointPathLength (p :: q :: rest) n).lo =
      (pointSegmentLengthInterval p q n).lo +
        (rationalPointPathLength (q :: rest) n).lo := by
  simp [rationalPointPathLength, rationalPointPathLength.totalLength,
    pointSegmentLengthInterval, pointSegmentNormSq]

theorem rationalPointPathLength_cons_cons_hi
    (p q : PiCirclePoint) (rest : List PiCirclePoint) (n : Nat) :
    (rationalPointPathLength (p :: q :: rest) n).hi =
      (pointSegmentLengthInterval p q n).hi +
        (rationalPointPathLength (q :: rest) n).hi := by
  simp [rationalPointPathLength, rationalPointPathLength.totalLength,
    pointSegmentLengthInterval, pointSegmentNormSq]

theorem innerPathLengthLo_le_refinedInnerPathLengthLo
    (stage : Nat)
    (hlocal : forall k, k < stage -> InnerLengthCellSplitBound stage k) :
    forall count k, k + count <= stage ->
      (rationalPointPathLength
        (circleSamplePoint stage k ::
          innerBoundaryFrom stage (k + 1) count)
        (circumferenceSqrtPrecision stage)).lo <=
      (rationalPointPathLength
        (circleSamplePoint (2 * stage) (2 * k) ::
          innerBoundaryFrom (2 * stage) (2 * k + 1) (2 * count))
        (circumferenceSqrtPrecision (2 * stage))).lo
  | 0, _k, _hbound => by
      simp [innerBoundaryFrom, piCircleArea.innerBoundaryFrom,
        rationalPointPathLength, rationalPointPathLength.totalLength]
  | count + 1, k, hbound => by
      have hk : k < stage := by omega
      have htailBound : k + 1 + count <= stage := by omega
      have hhead := hlocal k hk
      have htail :=
        innerPathLengthLo_le_refinedInnerPathLengthLo
          stage hlocal count (k + 1) htailBound
      simp only [innerBoundaryFrom, piCircleArea.innerBoundaryFrom]
      rw [rationalPointPathLength_cons_cons_lo]
      rw [rationalPointPathLength_cons_cons_lo]
      rw [rationalPointPathLength_cons_cons_lo]
      have hcombined := Fan.rat_add_le_add hhead htail
      simpa [InnerLengthCellSplitBound, Nat.mul_add, Nat.add_assoc,
        Nat.add_left_comm, Rat.add_assoc] using hcombined

theorem innerQuarterLength_mono_of_inner_length_cell_bounds
    (stage : Nat)
    (hlocal : forall k, k < stage -> InnerLengthCellSplitBound stage k) :
    (innerQuarterLength stage).lo <=
      (innerQuarterLength (2 * stage)).lo := by
  have h :=
    innerPathLengthLo_le_refinedInnerPathLengthLo
      stage hlocal stage 0 (by omega)
  simpa [innerQuarterLength, innerBoundary, innerBoundaryFrom,
    piCircleArea.innerBoundaryFrom, Nat.add_assoc]
    using h

theorem refinedOuterPathLengthHi_le_outerPathLengthHi
    (stage : Nat)
    (hlocal : forall k, k < stage -> OuterLengthCellSplitBound stage k) :
    forall count k, k + count <= stage ->
      (rationalPointPathLength
        (circleSamplePoint (2 * stage) (2 * k) ::
          outerBoundaryFrom (2 * stage) (2 * k) (2 * count))
        (circumferenceSqrtPrecision (2 * stage))).hi <=
      (rationalPointPathLength
        (circleSamplePoint stage k ::
          outerBoundaryFrom stage k count)
        (circumferenceSqrtPrecision stage)).hi
  | 0, _k, _hbound => by
      simp [outerBoundaryFrom, piCircleArea.outerBoundaryFrom,
        rationalPointPathLength, rationalPointPathLength.totalLength]
  | count + 1, k, hbound => by
      have hk : k < stage := by omega
      have htailBound : k + 1 + count <= stage := by omega
      have hhead := hlocal k hk
      have htail :=
        refinedOuterPathLengthHi_le_outerPathLengthHi
          stage hlocal count (k + 1) htailBound
      simp only [outerBoundaryFrom, piCircleArea.outerBoundaryFrom]
      rw [rationalPointPathLength_cons_cons_hi]
      rw [rationalPointPathLength_cons_cons_hi]
      rw [rationalPointPathLength_cons_cons_hi]
      rw [rationalPointPathLength_cons_cons_hi]
      rw [rationalPointPathLength_cons_cons_hi]
      rw [rationalPointPathLength_cons_cons_hi]
      have hcombined := Fan.rat_add_le_add hhead htail
      simpa [OuterLengthCellSplitBound, Nat.mul_add, Nat.add_assoc,
        Nat.add_left_comm, Rat.add_assoc] using hcombined

theorem outerQuarterLength_antitone_of_outer_length_cell_bounds
    (stage : Nat)
    (hlocal : forall k, k < stage -> OuterLengthCellSplitBound stage k) :
    (outerQuarterLength (2 * stage)).hi <=
      (outerQuarterLength stage).hi := by
  have h :=
    refinedOuterPathLengthHi_le_outerPathLengthHi
      stage hlocal stage 0 (by omega)
  simpa [outerQuarterLength, outerBoundary, outerBoundaryFrom,
    piCircleArea.outerBoundaryFrom, Nat.add_assoc]
    using h

theorem circumferenceStageRefines_of_length_cell_bounds
    (stage : Nat) (_hstage : 0 < stage)
    (hinner : forall k, k < stage -> InnerLengthCellSplitBound stage k)
    (houter : forall k, k < stage -> OuterLengthCellSplitBound stage k) :
    CircumferenceStageRefines stage (2 * stage) where
  innerQuarterLength_mono :=
    innerQuarterLength_mono_of_inner_length_cell_bounds
      stage hinner
  outerQuarterLength_antitone :=
    outerQuarterLength_antitone_of_outer_length_cell_bounds
      stage houter

/-- Target theorem shape: summing the local dyadic cell inequalities gives
stage refinement.  This is intentionally a proposition for now; proving this
is the next small combinatorial step, separate from the cell inequalities
themselves. -/
def DyadicCellBoundsYieldStageRefinement : Prop :=
  forall stage, 0 < stage ->
    DyadicCellRefinementBounds stage ->
      AreaStageRefines stage (2 * stage) /\
      CircumferenceStageRefines stage (2 * stage)

theorem dyadicCellBoundsYieldStageRefinement :
    DyadicCellBoundsYieldStageRefinement := by
  intro stage hstage hcell
  constructor
  · exact areaStageRefines_of_area_cell_bounds
      stage hstage hcell.inner_area hcell.outer_area
  · exact circumferenceStageRefines_of_length_cell_bounds
      stage hstage hcell.inner_length hcell.outer_length

theorem areaInterval_stepRefines_of_stageRefines
    {coarse fine : Nat} (h : AreaStageRefines coarse fine) :
    (piCircleAreaComputeAtStage coarse).lo <=
        (piCircleAreaComputeAtStage fine).lo /\
      (piCircleAreaComputeAtStage fine).hi <=
        (piCircleAreaComputeAtStage coarse).hi := by
  constructor
  · unfold piCircleAreaComputeAtStage
    exact four_mul_le_four_mul h.innerQuarterArea_mono
  · unfold piCircleAreaComputeAtStage
    exact four_mul_le_four_mul h.outerQuarterArea_antitone

theorem circumferenceInterval_stepRefines_of_stageRefines
    {coarse fine : Nat} (h : CircumferenceStageRefines coarse fine) :
    (piCircumferenceCommonComputeAtStage coarse).lo <=
        (piCircumferenceCommonComputeAtStage fine).lo /\
      (piCircumferenceCommonComputeAtStage fine).hi <=
        (piCircumferenceCommonComputeAtStage coarse).hi := by
  constructor
  · unfold piCircumferenceCommonComputeAtStage
    exact div_two_le_div_two
      (four_mul_le_four_mul h.innerQuarterLength_mono)
  · unfold piCircumferenceCommonComputeAtStage
    exact div_two_le_div_two
      (four_mul_le_four_mul h.outerQuarterLength_antitone)

theorem areaStepRefines_of_dyadic_stage_refinement
    (hrefine :
      forall n, AreaStageRefines (piStage n) (piStage (n + 1))) :
    AreaStepRefines := by
  intro n
  rw [piCircleArea_compute_eq, piCircleArea_compute_eq]
  exact areaInterval_stepRefines_of_stageRefines (hrefine n)

theorem areaStepRefines_rationalCircle : AreaStepRefines :=
  areaStepRefines_of_dyadic_stage_refinement
    (fun n => by
      rw [piStage_succ]
      exact areaStageRefines_rationalCircle (piStage n) (piStage_pos n))

theorem circumferenceStepRefines_of_dyadic_stage_refinement
    (hrefine :
      forall n, CircumferenceStageRefines (piStage n) (piStage (n + 1))) :
    CircumferenceStepRefines := by
  intro n
  rw [piCircumference_compute_eq, piCircumference_compute_eq,
    piCircumferenceComputeAtStage_eq_common,
    piCircumferenceComputeAtStage_eq_common]
  exact circumferenceInterval_stepRefines_of_stageRefines (hrefine n)

theorem areaNested_of_endpointMonotone
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
      have hwidth := piCircleArea_ordered m
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
    (hstep : AreaStepRefines) : AreaNested :=
  areaNested_of_endpointMonotone
    (endpointMonotone_of_stepRefines hstep)

theorem circumferenceNested_of_stepRefines
    (hstep : CircumferenceStepRefines) : CircumferenceNested :=
  circumferenceNested_of_endpointMonotone
    (endpointMonotone_of_stepRefines hstep)

theorem leibnizEqArea_of_powerSeriesGeometryAgreement
    (hGeomValid : ArctanGeometry.Valid)
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
  have hgeomScaledValid :
      (((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw).Valid) :=
    fourArctanGeomOneValid_of_geometricValid hGeomValid
  have hleibnizToGeom :
      piLeibniz.Equiv
        ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) :=
    RealRaw.equiv_trans
      leibnizValid fourArctanOneValid hgeomScaledValid
      piLeibniz_equiv_four_arctan_one hscaled
  have hareaNested : AreaNested :=
    areaNested_of_stepRefines areaStepRefines_rationalCircle
  intro n
  have hover := (RealRaw.compareAt_overlap_iff piLeibniz
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) n n).1
    (hleibnizToGeom n)
  have hstage : n <= RealRaw.scaleRatStage 4 n :=
    RealRaw.le_scaleRatStage 4 n
  have hnested := hareaNested n (RealRaw.scaleRatStage 4 n) hstage
  apply (RealRaw.compareAt_overlap_iff piLeibniz piCircleArea n n).2
  rw [← four_arctanGeom_one_compute_eq_piCircleArea_compute n] at hnested
  constructor
  · exact Rat.le_trans hover.1 hnested.2.2
  · exact Rat.le_trans hnested.1 hover.2

theorem leibnizEqArea_of_kernelComparisonRoute
    (route : Taylor.ArctanComparison.KernelComparisonRoute) :
    LeibnizEqArea :=
  leibnizEqArea_of_powerSeriesGeometryAgreement
    route.geometric_valid
    (Taylor.ArctanComparison.powerSeriesAgreesOnUnit_of_kernelComparisonRoute
      route)

theorem areaValid_of_nested_and_shrinking
    (hnested : AreaNested) (hshrink : AreaWidthsShrink) :
    AreaValid := by
  unfold AreaValid RealRaw.ValidCompute
  constructor
  case left =>
    exact piCircleArea_ordered
  case right =>
    constructor
    case left =>
      exact hnested
    case right =>
      exact hshrink

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

theorem areaStepValidCompute_of_stepRefines
    (hstep : AreaStepRefines) (hshrink : AreaWidthsShrink) :
    RealRaw.StepValidCompute piCircleArea.compute := by
  constructor
  · exact piCircleArea_ordered 0
  · constructor
    · intro n
      have href := hstep n
      have hordered := piCircleArea_ordered (n + 1)
      constructor
      · exact href.1
      · constructor
        · unfold QInterval.width at hordered
          grind [Rat.sub_eq_add_neg]
        · exact href.2
    · exact hshrink

theorem circumferenceStepValidCompute_of_stepRefines
    (hstep : CircumferenceStepRefines)
    (hshrink : CircumferenceWidthsShrink) :
    RealRaw.StepValidCompute piCircumference.compute := by
  constructor
  · exact piCircumference_ordered 0
  · constructor
    · intro n
      have href := hstep n
      have hordered := piCircumference_ordered (n + 1)
      constructor
      · exact href.1
      · constructor
        · unfold QInterval.width at hordered
          grind [Rat.sub_eq_add_neg]
        · exact href.2
    · exact hshrink

theorem areaStepPrecisionValidCompute_of_stepRefines
    (hstep : AreaStepRefines) (hprecision : AreaPositivePrecision) :
    RealRaw.StepPrecisionValidCompute piCircleArea.compute := by
  constructor
  · exact piCircleArea_ordered 0
  · constructor
    · intro n
      have href := hstep n
      have hordered := piCircleArea_ordered (n + 1)
      constructor
      · exact href.1
      · constructor
        · unfold QInterval.width at hordered
          grind [Rat.sub_eq_add_neg]
        · exact href.2
    · exact hprecision

theorem circumferenceStepPrecisionValidCompute_of_stepRefines
    (hstep : CircumferenceStepRefines)
    (hprecision : CircumferencePositivePrecision) :
    RealRaw.StepPrecisionValidCompute piCircumference.compute := by
  constructor
  · exact piCircumference_ordered 0
  · constructor
    · intro n
      have href := hstep n
      have hordered := piCircumference_ordered (n + 1)
      constructor
      · exact href.1
      · constructor
        · unfold QInterval.width at hordered
          grind [Rat.sub_eq_add_neg]
        · exact href.2
    · exact hprecision

theorem areaPrecisionValid_of_stepRefines_and_precision
    (hstep : AreaStepRefines) (hprecision : AreaPositivePrecision) :
    RealRaw.PrecisionValidCompute piCircleArea.compute :=
  RealRaw.precisionValidCompute_of_stepPrecisionValidCompute
    (areaStepPrecisionValidCompute_of_stepRefines hstep hprecision)

theorem circumferencePrecisionValid_of_stepRefines_and_precision
    (hstep : CircumferenceStepRefines)
    (hprecision : CircumferencePositivePrecision) :
    RealRaw.PrecisionValidCompute piCircumference.compute :=
  RealRaw.precisionValidCompute_of_stepPrecisionValidCompute
    (circumferenceStepPrecisionValidCompute_of_stepRefines
      hstep hprecision)

theorem areaValid_of_stepRefines_and_shrinking
    (hstep : AreaStepRefines) (hshrink : AreaWidthsShrink) :
    AreaValid :=
  RealRaw.validCompute_of_stepValidCompute
    (areaStepValidCompute_of_stepRefines hstep hshrink)

theorem circumferenceValid_of_stepRefines_and_shrinking
    (hstep : CircumferenceStepRefines)
    (hshrink : CircumferenceWidthsShrink) :
    CircumferenceValid :=
  RealRaw.validCompute_of_stepValidCompute
    (circumferenceStepValidCompute_of_stepRefines hstep hshrink)

structure GeometricValidityRemainders where
  area_nested : AreaNested
  area_widths_shrink : AreaWidthsShrink
  circumference_nested : CircumferenceNested
  circumference_widths_shrink : CircumferenceWidthsShrink

structure GeometricStepRemainders where
  area_step_refines : AreaStepRefines
  area_widths_shrink : AreaWidthsShrink
  circumference_step_refines : CircumferenceStepRefines
  circumference_widths_shrink : CircumferenceWidthsShrink

structure DyadicGeometricStageRefines (n : Nat) where
  area : AreaStageRefines (piStage n) (piStage (n + 1))
  circumference :
    CircumferenceStageRefines (piStage n) (piStage (n + 1))

theorem dyadicGeometricStageRefines_of_cellBounds
    (hyield : DyadicCellBoundsYieldStageRefinement)
    (hcell : forall n, DyadicCellRefinementBounds (piStage n)) :
    forall n, DyadicGeometricStageRefines n := by
  intro n
  have hrefine :=
    hyield (piStage n) (piStage_pos n) (hcell n)
  refine
    { area := ?_
      circumference := ?_ }
  · rw [piStage_succ]
    exact hrefine.1
  · rw [piStage_succ]
    exact hrefine.2

theorem geometricStepRemainders_of_dyadic_stage_refinement
    (hrefine : forall n, DyadicGeometricStageRefines n)
    (harea_widths : AreaWidthsShrink)
    (hcircumference_widths : CircumferenceWidthsShrink) :
    GeometricStepRemainders where
  area_step_refines :=
    areaStepRefines_of_dyadic_stage_refinement
      (fun n => (hrefine n).area)
  area_widths_shrink := harea_widths
  circumference_step_refines :=
    circumferenceStepRefines_of_dyadic_stage_refinement
      (fun n => (hrefine n).circumference)
  circumference_widths_shrink := hcircumference_widths

theorem geometricStepRemainders_of_dyadic_cell_bounds
    (hyield : DyadicCellBoundsYieldStageRefinement)
    (hcell : forall n, DyadicCellRefinementBounds (piStage n))
    (harea_widths : AreaWidthsShrink)
    (hcircumference_widths : CircumferenceWidthsShrink) :
    GeometricStepRemainders :=
  geometricStepRemainders_of_dyadic_stage_refinement
    (dyadicGeometricStageRefines_of_cellBounds hyield hcell)
    harea_widths
    hcircumference_widths

structure GeometricLinearStepRemainders where
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
  area_nested :=
    areaNested_of_stepRefines remainders.area_step_refines
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
      remainders.area_nested
      remainders.area_widths_shrink
  circumference :=
    circumferenceValid_of_nested_and_shrinking
      remainders.circumference_nested
      remainders.circumference_widths_shrink

theorem validityProofs_of_geometric_step_remainders
    (remainders : GeometricStepRemainders) :
    ValidityProofs where
  leibniz := leibnizValid
  machin := machinValid
  area :=
    areaValid_of_stepRefines_and_shrinking
      remainders.area_step_refines
      remainders.area_widths_shrink
  circumference :=
    circumferenceValid_of_stepRefines_and_shrinking
      remainders.circumference_step_refines
      remainders.circumference_widths_shrink

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
  geometric_validity : GeometricValidityRemainders
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

theorem agreementProofs_of_completionRemainders
    (remainders : CompletionRemainders) :
    AgreementProofs where
  leibniz_eq_machin := remainders.leibniz_eq_machin
  leibniz_eq_area := remainders.leibniz_eq_area
  area_eq_circumference := archimedesTheorem

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
  geometric_steps : GeometricStepRemainders
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

def CompletionStepRemainders.toCompletionRemainders
    (remainders : CompletionStepRemainders) : CompletionRemainders where
  geometric_validity :=
    geometricValidityRemainders_of_stepRemainders
      remainders.geometric_steps
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
  geometric_linear_steps : GeometricLinearStepRemainders
  leibniz_eq_machin : LeibnizEqMachin
  leibniz_eq_area : LeibnizEqArea

def CompletionLinearStepRemainders.toCompletionStepRemainders
    (remainders : CompletionLinearStepRemainders) :
    CompletionStepRemainders where
  geometric_steps :=
    geometricStepRemainders_of_linearStepRemainders
      remainders.geometric_linear_steps
  leibniz_eq_machin := remainders.leibniz_eq_machin
  leibniz_eq_area := remainders.leibniz_eq_area

theorem piProofsComplete_of_linearStepRemainders
    (remainders : CompletionLinearStepRemainders) :
    PiProofsComplete :=
  piProofsComplete_of_stepRemainders
    remainders.toCompletionStepRemainders

theorem piProofsComplete_of_kernelComparisonRoute
    (geometric_validity : GeometricValidityRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PiProofsComplete :=
  piProofsComplete_of_completionRemainders
    { geometric_validity := geometric_validity
      leibniz_eq_machin :=
        leibnizEqMachin_of_kernelComparisonRoute route hgeom
      leibniz_eq_area :=
        leibnizEqArea_of_kernelComparisonRoute route }

theorem piProofsComplete_of_stepRemainders_and_kernelComparisonRoute
    (geometric_steps : GeometricStepRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PiProofsComplete :=
  piProofsComplete_of_kernelComparisonRoute
    (geometricValidityRemainders_of_stepRemainders geometric_steps)
    route
    hgeom

theorem piProofsComplete_of_linearStepRemainders_and_kernelComparisonRoute
    (geometric_linear_steps : GeometricLinearStepRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PiProofsComplete :=
  piProofsComplete_of_stepRemainders_and_kernelComparisonRoute
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
    (geometric_validity : GeometricValidityRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PairwiseAgreementProofs :=
  PiProofsComplete.pairwiseAgreement
    (piProofsComplete_of_kernelComparisonRoute
      geometric_validity route hgeom)

theorem pairwiseAgreementProofs_of_stepRemainders_and_kernelComparisonRoute
    (geometric_steps : GeometricStepRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PairwiseAgreementProofs :=
  PiProofsComplete.pairwiseAgreement
    (piProofsComplete_of_stepRemainders_and_kernelComparisonRoute
      geometric_steps route hgeom)

theorem pairwiseAgreementProofs_of_linearStepRemainders_and_kernelComparisonRoute
    (geometric_linear_steps : GeometricLinearStepRemainders)
    (route : Taylor.ArctanComparison.KernelComparisonRoute)
    (hgeom : MachinIdentity.GeometricBranchLaw) :
    PairwiseAgreementProofs :=
  PiProofsComplete.pairwiseAgreement
    (piProofsComplete_of_linearStepRemainders_and_kernelComparisonRoute
      geometric_linear_steps route hgeom)

end PiProofs

end ComputableAnalysis
