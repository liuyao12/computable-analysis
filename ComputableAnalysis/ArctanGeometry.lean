import ComputableAnalysis.Elementary
import ComputableAnalysis.RationalCircle

/-!
# Geometric arctangent

This module keeps the geometric arctangent and its comparison-facing API
outside the rational-circle trigonometry module.  The rational-circle module
contains the circle stages, coordinate algorithms, and identity infrastructure;
comparison with other arctangent representations imports those extra
definitions here.
-/

namespace ComputableAnalysis

namespace ArctanGeometry

/-!
Geometric arctangent.

For rational `x`, the point
`((1 - x^2) / (1 + x^2), 2x / (1 + x^2))` lies on the unit circle at angle
`2 * arctan x`, so the unit-sector area from `0` to this parameter is
`arctan x`.
-/

def stage (n : Nat) : Nat :=
  2 ^ n

theorem stage_pos (n : Nat) : 0 < stage n := by
  unfold stage
  exact Nat.pow_pos (by omega : 0 < 2)

/-- State for the update-loop presentation of geometric arctangent.  The
interval `[lo, hi]` stores current sector-area bounds, and `intervals` stores
the rational parameter intervals being refined. -/
structure AreaLoopState where
  lo : Rat
  hi : Rat
  intervals : List (Rat × Rat)
deriving Repr, DecidableEq

/-- The area added to the inscribed sector approximation when adjacent
parameters `p < q < r` replace the old interval `[p,r]` by two intervals. -/
def arctanAreaIncrement (p q r : Rat) : Rat :=
  (2 * (r - p) * (q - p) * (r - q)) /
    ((1 + p * p) * (1 + q * q) * (1 + r * r))

/-- The area removed from the outer tangent sector approximation when adjacent
parameters `p < q < r` replace the old interval `[p,r]` by two intervals. -/
def arctanAreaDecrement (p q r : Rat) : Rat :=
  ((r - p) * (q - p) * (r - q)) /
    ((1 + p * r) * (1 + p * q) * (1 + q * r))

private theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d := by
  grind

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

/-!
The following cell formulas are the finite comparison layer between the
geometric arctangent and the definite integral of `1 / (1 + u^2)`.  No area
axiom or derivative theorem is used here: everything is a rational inequality
on one cell, then a finite sum over cells.
-/

/-- The exact decreasing kernel whose lower/upper rectangle sums compute
arctangent. -/
def integralKernel (u : Rat) : Rat :=
  1 / (1 + u * u)

/-- Lower rectangle on `[p,r]` for `1/(1+u^2)`, valid on nonnegative cells. -/
def integralLowerStep (p r : Rat) : Rat :=
  (r - p) * integralKernel r

/-- Upper rectangle on `[p,r]` for `1/(1+u^2)`, valid on nonnegative cells. -/
def integralUpperStep (p r : Rat) : Rat :=
  (r - p) * integralKernel p

/-- Inscribed geometric sector cell between rational parameters `p` and `r`. -/
def geometricLowerStep (p r : Rat) : Rat :=
  ((r - p) * (1 + p * r)) /
    ((1 + p * p) * (1 + r * r))

/-- Circumscribed tangent-sector cell between rational parameters `p` and `r`. -/
def geometricUpperStep (p r : Rat) : Rat :=
  (r - p) / (1 + p * r)

def integralCellInterval (p r : Rat) : QInterval :=
  { lo := integralLowerStep p r, hi := integralUpperStep p r }

def geometricCellInterval (p r : Rat) : QInterval :=
  { lo := geometricLowerStep p r, hi := geometricUpperStep p r }

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

private theorem geometricLowerStep_refine_den_identity (p q r : Rat) :
    (q - p) * (1 + p * q) * (1 + r * r) +
      (r - q) * (1 + q * r) * (1 + p * p) =
    (r - p) * (1 + p * r) * (1 + q * q) +
      2 * (r - p) * (q - p) * (r - q) := by
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem geometricLowerStep_refine (p q r : Rat) :
    geometricLowerStep p q + geometricLowerStep q r =
      geometricLowerStep p r + arctanAreaIncrement p q r := by
  let A : Rat := 1 + p * p
  let B : Rat := 1 + q * q
  let C : Rat := 1 + r * r
  let D : Rat := A * B * C
  have hApos : 0 < A := by
    dsimp [A]
    exact RationalCircle.Stage.one_add_square_pos p
  have hBpos : 0 < B := by
    dsimp [B]
    exact RationalCircle.Stage.one_add_square_pos q
  have hCpos : 0 < C := by
    dsimp [C]
    exact RationalCircle.Stage.one_add_square_pos r
  have hDpos : 0 < D := by
    dsimp [D]
    exact Rat.mul_pos (Rat.mul_pos hApos hBpos) hCpos
  have hABne : A * B ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hApos hBpos)
  have hBCne : B * C ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hBpos hCpos)
  have hACne : A * C ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hApos hCpos)
  have hDne : D ≠ 0 := Rat.ne_of_gt hDpos
  apply rat_eq_of_mul_eq_mul_pos hDpos
  calc
    (geometricLowerStep p q + geometricLowerStep q r) * D
        = (q - p) * (1 + p * q) * C +
            (r - q) * (1 + q * r) * A := by
          dsimp [D, A, B, C]
          unfold geometricLowerStep
          rw [Rat.add_mul, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ = (r - p) * (1 + p * r) * B +
          2 * (r - p) * (q - p) * (r - q) := by
          dsimp [A, B, C]
          exact geometricLowerStep_refine_den_identity p q r
    _ = (geometricLowerStep p r + arctanAreaIncrement p q r) * D := by
          dsimp [D, A, B, C]
          unfold geometricLowerStep arctanAreaIncrement
          rw [Rat.add_mul, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem geometricUpperStep_refine_den_identity (p q r : Rat) :
    (q - p) * (1 + q * r) * (1 + p * r) +
      (r - q) * (1 + p * q) * (1 + p * r) =
    (r - p) * (1 + p * q) * (1 + q * r) -
      (r - p) * (q - p) * (r - q) := by
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem geometricUpperStep_refine
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    geometricUpperStep p q + geometricUpperStep q r =
      geometricUpperStep p r - arctanAreaDecrement p q r := by
  let A : Rat := 1 + p * q
  let B : Rat := 1 + q * r
  let C : Rat := 1 + p * r
  let D : Rat := C * A * B
  have hq0 : 0 <= q := Rat.le_trans hp0 hpq
  have hr0 : 0 <= r := Rat.le_trans hq0 hqr
  have hApos : 0 < A := by
    dsimp [A]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hq0
  have hBpos : 0 < B := by
    dsimp [B]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hq0 hr0
  have hCpos : 0 < C := by
    dsimp [C]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0
  have hDpos : 0 < D := by
    dsimp [D]
    exact Rat.mul_pos (Rat.mul_pos hCpos hApos) hBpos
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
  have hCne : C ≠ 0 := Rat.ne_of_gt hCpos
  have hDne : D ≠ 0 := Rat.ne_of_gt hDpos
  apply rat_eq_of_mul_eq_mul_pos hDpos
  calc
    (geometricUpperStep p q + geometricUpperStep q r) * D
        = (q - p) * B * C + (r - q) * A * C := by
          dsimp [D, A, B, C]
          unfold geometricUpperStep
          rw [Rat.add_mul, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ = (r - p) * A * B - (r - p) * (q - p) * (r - q) := by
          dsimp [A, B, C]
          have h := geometricUpperStep_refine_den_identity p q r
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (geometricUpperStep p r - arctanAreaDecrement p q r) * D := by
          dsimp [D, A, B, C]
          unfold geometricUpperStep arctanAreaDecrement
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_assoc,
            Rat.mul_comm, Rat.mul_inv_cancel]

private theorem left_square_le_factor {p r : Rat}
    (hp0 : 0 <= p) (hpr : p <= r) :
    1 + p * p <= 1 + p * r := by
  have hmul : p * p <= p * r :=
    Rat.mul_le_mul_of_nonneg_left hpr hp0
  grind

private theorem factor_le_right_square {p r : Rat}
    (hp0 : 0 <= p) (hpr : p <= r) :
    1 + p * r <= 1 + r * r := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hmul : p * r <= r * r :=
    Rat.mul_le_mul_of_nonneg_right hpr hr0
  grind

theorem integralLowerStep_le_geometricLowerStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    integralLowerStep p r <= geometricLowerStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hfac : 1 + p * p <= 1 + p * r :=
    left_square_le_factor hp0 hpr
  have hmain : (r - p) * (1 + p * p) <= (r - p) * (1 + p * r) :=
    Rat.mul_le_mul_of_nonneg_left hfac hlen
  have hpdenpos : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hrdenpos : 0 < 1 + r * r :=
    RationalCircle.Stage.one_add_square_pos r
  have hrdenne : 1 + r * r ≠ 0 := Rat.ne_of_gt hrdenpos
  have hdenpos : 0 < (1 + p * p) * (1 + r * r) :=
    Rat.mul_pos hpdenpos hrdenpos
  refine Rat.le_of_mul_le_mul_right
    (c := (1 + p * p) * (1 + r * r)) ?_ hdenpos
  unfold integralLowerStep geometricLowerStep integralKernel
  calc
    ((r - p) * (1 / (1 + r * r))) *
        ((1 + p * p) * (1 + r * r))
        = (r - p) * (1 + p * p) := by
          rw [Rat.div_def]
          have hcancel : (1 + r * r) * (1 + r * r)⁻¹ = 1 :=
            Rat.mul_inv_cancel _ hrdenne
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (r - p) * (1 + p * r) := hmain
    _ = (((r - p) * (1 + p * r)) /
        ((1 + p * p) * (1 + r * r))) *
        ((1 + p * p) * (1 + r * r)) := by
          rw [Rat.div_def]
          have hcancel : ((1 + p * p) * (1 + r * r)) *
              (((1 + p * p) * (1 + r * r))⁻¹) = 1 :=
            Rat.mul_inv_cancel _ (Rat.ne_of_gt hdenpos)
          grind [Rat.mul_assoc, Rat.mul_comm]

theorem integralLowerStep_le_geometricUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    integralLowerStep p r <= geometricUpperStep p r := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hprpos : 0 < 1 + p * r :=
    RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0
  have hfac : 1 + p * r <= 1 + r * r :=
    factor_le_right_square hp0 hpr
  have hinv : 1 / (1 + r * r) <= 1 / (1 + p * r) :=
    one_div_le_one_div_of_pos_of_le hprpos hfac
  unfold integralLowerStep geometricUpperStep integralKernel
  repeat rw [Rat.div_def] at hinv ⊢
  simpa [Rat.mul_assoc] using Rat.mul_le_mul_of_nonneg_left hinv hlen

theorem geometricLowerStep_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    geometricLowerStep p r <= integralUpperStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hfac : 1 + p * r <= 1 + r * r :=
    factor_le_right_square hp0 hpr
  have hmain : (r - p) * (1 + p * r) <= (r - p) * (1 + r * r) :=
    Rat.mul_le_mul_of_nonneg_left hfac hlen
  have hpdenpos : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hrdenpos : 0 < 1 + r * r :=
    RationalCircle.Stage.one_add_square_pos r
  have hpdenne : 1 + p * p ≠ 0 := Rat.ne_of_gt hpdenpos
  have hdenpos : 0 < (1 + p * p) * (1 + r * r) :=
    Rat.mul_pos hpdenpos hrdenpos
  refine Rat.le_of_mul_le_mul_right
    (c := (1 + p * p) * (1 + r * r)) ?_ hdenpos
  unfold geometricLowerStep integralUpperStep integralKernel
  calc
    (((r - p) * (1 + p * r)) /
        ((1 + p * p) * (1 + r * r))) *
        ((1 + p * p) * (1 + r * r))
        = (r - p) * (1 + p * r) := by
          rw [Rat.div_def]
          have hcancel : ((1 + p * p) * (1 + r * r)) *
              (((1 + p * p) * (1 + r * r))⁻¹) = 1 :=
            Rat.mul_inv_cancel _ (Rat.ne_of_gt hdenpos)
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (r - p) * (1 + r * r) := hmain
    _ = ((r - p) * (1 / (1 + p * p))) *
        ((1 + p * p) * (1 + r * r)) := by
          rw [Rat.div_def]
          have hcancel : (1 + p * p) * (1 + p * p)⁻¹ = 1 :=
            Rat.mul_inv_cancel _ hpdenne
          grind [Rat.mul_assoc, Rat.mul_comm]

theorem geometricUpperStep_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    geometricUpperStep p r <= integralUpperStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hpdenpos : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hfac : 1 + p * p <= 1 + p * r :=
    left_square_le_factor hp0 hpr
  have hinv : 1 / (1 + p * r) <= 1 / (1 + p * p) :=
    one_div_le_one_div_of_pos_of_le hpdenpos hfac
  unfold geometricUpperStep integralUpperStep integralKernel
  repeat rw [Rat.div_def] at hinv ⊢
  simpa [Rat.mul_assoc] using Rat.mul_le_mul_of_nonneg_left hinv hlen

theorem integralCellInterval_contains_geometricCellInterval
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    (integralCellInterval p r).ContainsInterval
      (geometricCellInterval p r) := by
  unfold QInterval.ContainsInterval integralCellInterval geometricCellInterval
  exact ⟨integralLowerStep_le_geometricLowerStep hp0 hpr,
    geometricUpperStep_le_integralUpperStep hp0 hpr⟩

theorem integralCellInterval_overlaps_geometricCellInterval
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    QInterval.Overlaps (integralCellInterval p r)
      (geometricCellInterval p r) := by
  unfold QInterval.Overlaps integralCellInterval geometricCellInterval
  exact ⟨integralLowerStep_le_geometricUpperStep hp0 hpr,
    geometricLowerStep_le_integralUpperStep hp0 hpr⟩

/-- A finite partition whose cells lie in the nonnegative half-line. -/
def NonnegativeIntervals : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest =>
      0 <= p /\ p <= r /\ NonnegativeIntervals rest

def integralLowerSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => integralLowerStep p r + integralLowerSum rest

def integralUpperSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => integralUpperStep p r + integralUpperSum rest

def geometricLowerSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => geometricLowerStep p r + geometricLowerSum rest

def geometricUpperSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => geometricUpperStep p r + geometricUpperSum rest

def integralSumInterval (intervals : List (Rat × Rat)) : QInterval :=
  { lo := integralLowerSum intervals, hi := integralUpperSum intervals }

def geometricSumInterval (intervals : List (Rat × Rat)) : QInterval :=
  { lo := geometricLowerSum intervals, hi := geometricUpperSum intervals }

theorem integralLowerSum_le_geometricLowerSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralLowerSum intervals <= geometricLowerSum intervals := by
  induction intervals with
  | nil => simp [integralLowerSum, geometricLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [integralLowerSum, geometricLowerSum]
      exact rat_add_le_add
        (integralLowerStep_le_geometricLowerStep hp0 hpr)
        (ih hrest)

theorem integralLowerSum_le_geometricUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralLowerSum intervals <= geometricUpperSum intervals := by
  induction intervals with
  | nil => simp [integralLowerSum, geometricUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [integralLowerSum, geometricUpperSum]
      exact rat_add_le_add
        (integralLowerStep_le_geometricUpperStep hp0 hpr)
        (ih hrest)

theorem geometricLowerSum_le_integralUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    geometricLowerSum intervals <= integralUpperSum intervals := by
  induction intervals with
  | nil => simp [geometricLowerSum, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricLowerSum, integralUpperSum]
      exact rat_add_le_add
        (geometricLowerStep_le_integralUpperStep hp0 hpr)
        (ih hrest)

theorem geometricUpperSum_le_integralUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    geometricUpperSum intervals <= integralUpperSum intervals := by
  induction intervals with
  | nil => simp [geometricUpperSum, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricUpperSum, integralUpperSum]
      exact rat_add_le_add
        (geometricUpperStep_le_integralUpperStep hp0 hpr)
        (ih hrest)

theorem integralSumInterval_contains_geometricSumInterval
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    (integralSumInterval intervals).ContainsInterval
      (geometricSumInterval intervals) := by
  unfold QInterval.ContainsInterval integralSumInterval geometricSumInterval
  exact ⟨integralLowerSum_le_geometricLowerSum intervals hwf,
    geometricUpperSum_le_integralUpperSum intervals hwf⟩

theorem integralSumInterval_overlaps_geometricSumInterval
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    QInterval.Overlaps (integralSumInterval intervals)
      (geometricSumInterval intervals) := by
  unfold QInterval.Overlaps integralSumInterval geometricSumInterval
  exact ⟨integralLowerSum_le_geometricUpperSum intervals hwf,
    geometricLowerSum_le_integralUpperSum intervals hwf⟩

namespace AreaLoopState

def refineAux : Rat -> Rat -> List (Rat × Rat) -> AreaLoopState
  | lo, hi, [] => { lo := lo, hi := hi, intervals := [] }
  | lo, hi, (p, r) :: rest =>
      let q := (p + r) / 2
      let next := refineAux
        (lo + arctanAreaIncrement p q r)
        (hi - arctanAreaDecrement p q r)
        rest
      { next with intervals := (p, q) :: (q, r) :: next.intervals }

end AreaLoopState

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

private theorem refineAux_intervals_nonnegative
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    NonnegativeIntervals
      (AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, NonnegativeIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hq0 : 0 <= q := by
        dsimp [q]
        exact midpoint_nonneg hp0 (Rat.le_trans hp0 hpr)
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      simp [AreaLoopState.refineAux, NonnegativeIntervals, q,
        hp0, hpq, hq0, hqr, htail]

private theorem refineAux_lo_eq_geometricLowerSum_extra
    (extra lo hi : Rat) (intervals : List (Rat × Rat))
    (hlo : lo = extra + geometricLowerSum intervals) :
    let next := AreaLoopState.refineAux lo hi intervals
    next.lo = extra + geometricLowerSum next.intervals := by
  induction intervals generalizing extra lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, geometricLowerSum] at hlo ⊢
      exact hlo
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      let q : Rat := (p + r) / 2
      let extra' : Rat :=
        extra + geometricLowerStep p q + geometricLowerStep q r
      have hstart :
          lo + arctanAreaIncrement p q r =
            extra' + geometricLowerSum rest := by
        dsimp [extra']
        simp [geometricLowerSum] at hlo
        rw [hlo]
        have hlocal := geometricLowerStep_refine p q r
        grind [Rat.add_assoc, Rat.add_comm]
      have htail :=
        ih extra' (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hstart
      simp [AreaLoopState.refineAux, geometricLowerSum]
      simpa [extra', geometricLowerSum, Rat.add_assoc, Rat.add_comm] using htail

private theorem refineAux_hi_eq_geometricUpperSum_extra
    (extra lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals)
    (hhi : hi = extra + geometricUpperSum intervals) :
    let next := AreaLoopState.refineAux lo hi intervals
    next.hi = extra + geometricUpperSum next.intervals := by
  induction intervals generalizing extra lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, geometricUpperSum] at hhi ⊢
      exact hhi
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hq0 : 0 <= q := by
        dsimp [q]
        exact midpoint_nonneg hp0 (Rat.le_trans hp0 hpr)
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      let extra' : Rat :=
        extra + geometricUpperStep p q + geometricUpperStep q r
      have hstart :
          hi - arctanAreaDecrement p q r =
            extra' + geometricUpperSum rest := by
        dsimp [extra']
        simp [geometricUpperSum] at hhi
        rw [hhi]
        have hlocal := geometricUpperStep_refine hp0 hpq hqr
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      have htail :=
        ih extra' (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest hstart
      simp [AreaLoopState.refineAux, geometricUpperSum]
      simpa [extra', geometricUpperSum, Rat.add_assoc, Rat.add_comm] using htail

def refineAreaLoopState (state : AreaLoopState) : AreaLoopState :=
  AreaLoopState.refineAux state.lo state.hi state.intervals

theorem refineAreaLoopState_intervals_nonnegative
    (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals) :
    NonnegativeIntervals (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_intervals_nonnegative lo hi intervals hwf

theorem refineAreaLoopState_lo_eq_geometricLowerSum
    (state : AreaLoopState)
    (hlo : state.lo = geometricLowerSum state.intervals) :
    (refineAreaLoopState state).lo =
      geometricLowerSum (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      have hstart : lo = 0 + geometricLowerSum intervals := by
        grind
      have h := refineAux_lo_eq_geometricLowerSum_extra
        0 lo hi intervals hstart
      unfold refineAreaLoopState
      grind

theorem refineAreaLoopState_hi_eq_geometricUpperSum
    (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals)
    (hhi : state.hi = geometricUpperSum state.intervals) :
    (refineAreaLoopState state).hi =
      geometricUpperSum (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      have hstart : hi = 0 + geometricUpperSum intervals := by
        grind
      have h := refineAux_hi_eq_geometricUpperSum_extra
        0 lo hi intervals hwf hstart
      unfold refineAreaLoopState
      grind

def iterateAreaLoopState : Nat -> AreaLoopState -> AreaLoopState
  | 0, state => state
  | n + 1, state => iterateAreaLoopState n (refineAreaLoopState state)

theorem iterateAreaLoopState_intervals_nonnegative
    (n : Nat) (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals) :
    NonnegativeIntervals (iterateAreaLoopState n state).intervals := by
  induction n generalizing state with
  | zero =>
      simpa [iterateAreaLoopState] using hwf
  | succ n ih =>
      simpa [iterateAreaLoopState] using
        ih (refineAreaLoopState state)
          (refineAreaLoopState_intervals_nonnegative state hwf)

theorem iterateAreaLoopState_lo_eq_geometricLowerSum
    (n : Nat) (state : AreaLoopState)
    (hlo : state.lo = geometricLowerSum state.intervals) :
    (iterateAreaLoopState n state).lo =
      geometricLowerSum (iterateAreaLoopState n state).intervals := by
  induction n generalizing state with
  | zero =>
      simpa [iterateAreaLoopState] using hlo
  | succ n ih =>
      simpa [iterateAreaLoopState] using
        ih (refineAreaLoopState state)
          (refineAreaLoopState_lo_eq_geometricLowerSum state hlo)

theorem iterateAreaLoopState_hi_eq_geometricUpperSum
    (n : Nat) (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals)
    (hhi : state.hi = geometricUpperSum state.intervals) :
    (iterateAreaLoopState n state).hi =
      geometricUpperSum (iterateAreaLoopState n state).intervals := by
  induction n generalizing state with
  | zero =>
      simpa [iterateAreaLoopState] using hhi
  | succ n ih =>
      simpa [iterateAreaLoopState] using
        ih (refineAreaLoopState state)
          (refineAreaLoopState_intervals_nonnegative state hwf)
          (refineAreaLoopState_hi_eq_geometricUpperSum state hwf hhi)

def arctanAreaLoopInitial (x : Rat) : AreaLoopState :=
  { lo := x / (1 + x * x), hi := x, intervals := [(0, x)] }

def arctanAreaLoopState (x : Rat) (n : Nat) : AreaLoopState :=
  iterateAreaLoopState n (arctanAreaLoopInitial x)

theorem arctanAreaLoopInitial_intervals_nonnegative
    {x : Rat} (hx : 0 <= x) :
    NonnegativeIntervals (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, NonnegativeIntervals, hx]

theorem arctanAreaLoopState_intervals_nonnegative
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    NonnegativeIntervals (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_intervals_nonnegative n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_intervals_nonnegative hx)

theorem arctanAreaLoop_integralSum_contains_geometricSum
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (integralSumInterval (arctanAreaLoopState x n).intervals).ContainsInterval
      (geometricSumInterval (arctanAreaLoopState x n).intervals) :=
  integralSumInterval_contains_geometricSumInterval
    (arctanAreaLoopState x n).intervals
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem arctanAreaLoop_integralSum_overlaps_geometricSum
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    QInterval.Overlaps
      (integralSumInterval (arctanAreaLoopState x n).intervals)
      (geometricSumInterval (arctanAreaLoopState x n).intervals) :=
  integralSumInterval_overlaps_geometricSumInterval
    (arctanAreaLoopState x n).intervals
    (arctanAreaLoopState_intervals_nonnegative hx n)

private theorem arctanAreaLoopInitial_lo_eq_geometricLowerSum
    (x : Rat) :
    (arctanAreaLoopInitial x).lo =
      geometricLowerSum (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, geometricLowerSum, geometricLowerStep]
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem arctanAreaLoopInitial_hi_eq_geometricUpperSum
    (x : Rat) :
    (arctanAreaLoopInitial x).hi =
      geometricUpperSum (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, geometricUpperSum, geometricUpperStep]
  rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem arctanAreaLoopState_lo_eq_geometricLowerSum
    (x : Rat) (n : Nat) :
    (arctanAreaLoopState x n).lo =
      geometricLowerSum (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_lo_eq_geometricLowerSum n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_lo_eq_geometricLowerSum x)

theorem arctanAreaLoopState_hi_eq_geometricUpperSum
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (arctanAreaLoopState x n).hi =
      geometricUpperSum (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_hi_eq_geometricUpperSum n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_intervals_nonnegative hx)
    (arctanAreaLoopInitial_hi_eq_geometricUpperSum x)

def positiveLoopComputeAtStage (x : Rat) (n : Nat) : QInterval :=
  let state := arctanAreaLoopState x n
  { lo := state.lo, hi := state.hi }

theorem positiveLoopComputeAtStage_eq_geometricSumInterval
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    positiveLoopComputeAtStage x n =
      geometricSumInterval (arctanAreaLoopState x n).intervals := by
  unfold positiveLoopComputeAtStage geometricSumInterval
  simp [arctanAreaLoopState_lo_eq_geometricLowerSum,
    arctanAreaLoopState_hi_eq_geometricUpperSum hx]

theorem arctanAreaLoop_integralSum_contains_positiveLoop
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (integralSumInterval (arctanAreaLoopState x n).intervals).ContainsInterval
      (positiveLoopComputeAtStage x n) := by
  rw [positiveLoopComputeAtStage_eq_geometricSumInterval hx n]
  exact arctanAreaLoop_integralSum_contains_geometricSum hx n

theorem arctanAreaLoop_integralSum_overlaps_positiveLoop
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    QInterval.Overlaps
      (integralSumInterval (arctanAreaLoopState x n).intervals)
      (positiveLoopComputeAtStage x n) := by
  rw [positiveLoopComputeAtStage_eq_geometricSumInterval hx n]
  exact arctanAreaLoop_integralSum_overlaps_geometricSum hx n

def positiveLoopRaw (x : Rat) : RealRaw where
  compute := positiveLoopComputeAtStage x

/-- Geometric arctangent, presented as an explicit rational update algorithm.
This duplicates the exhaustion algorithm rather than factoring it through the
pi definition, so the later comparison theorem can relate two independent raw
objects. -/
def arctanGeom (x : Rat) : RealRaw :=
  if x = 0 then
    RealRaw.ofRat 0
  else if 0 <= x then
    positiveLoopRaw x
  else
    -positiveLoopRaw (-x)

theorem arctanAreaIncrement_eq_circleAreaIncrement (p m q : Rat) :
    arctanAreaIncrement p m q = circleAreaIncrement p m q := rfl

theorem arctanAreaDecrement_eq_circleAreaDecrement (p m q : Rat) :
    arctanAreaDecrement p m q = circleAreaDecrement p m q := rfl

theorem arctanGeom_nonneg_compute_eq
    {x : Rat} (hx0 : x ≠ 0) (hx : 0 <= x) (n : Nat) :
    (arctanGeom x).compute n = positiveLoopComputeAtStage x n := by
  simp [arctanGeom, positiveLoopRaw, hx0, hx]

theorem arctanGeom_one_compute_eq (n : Nat) :
    (arctanGeom 1).compute n = positiveLoopComputeAtStage 1 n := by
  have hnonzero : ¬(1 : Rat) = 0 := by native_decide
  have hnonneg : (0 : Rat) <= 1 := by native_decide
  exact arctanGeom_nonneg_compute_eq hnonzero hnonneg n

theorem arctanGeom_zero :
    arctanGeom 0 = RealRaw.ofRat 0 := by
  simp [arctanGeom]

def toPiAreaLoopState (state : AreaLoopState) : AreaBoundsLoopState :=
  { lo := state.lo, hi := state.hi, intervals := state.intervals }

theorem refineAux_toPiAreaLoopState
    (lo hi : Rat) (intervals : List (Rat × Rat)) :
    AreaBoundsLoopState.refineAux lo hi intervals =
      toPiAreaLoopState (AreaLoopState.refineAux lo hi intervals) := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaBoundsLoopState.refineAux, AreaLoopState.refineAux,
        toPiAreaLoopState]
  | cons pq rest ih =>
      rcases pq with ⟨p, r⟩
      let q := (p + r) / 2
      simp [AreaBoundsLoopState.refineAux, AreaLoopState.refineAux,
        toPiAreaLoopState, arctanAreaIncrement, circleAreaIncrement,
        arctanAreaDecrement, circleAreaDecrement]
      rw [ih]
      simp [toPiAreaLoopState]

theorem refineAreaBounds_toPiAreaLoopState (state : AreaLoopState) :
    refineAreaBounds (toPiAreaLoopState state) =
      toPiAreaLoopState (refineAreaLoopState state) := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_toPiAreaLoopState lo hi intervals

theorem iterateAreaBounds_toPiAreaLoopState (n : Nat)
    (state : AreaLoopState) :
    iterateAreaBounds n (toPiAreaLoopState state) =
      toPiAreaLoopState (iterateAreaLoopState n state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp [iterateAreaBounds, iterateAreaLoopState]
      rw [refineAreaBounds_toPiAreaLoopState]
      exact ih (refineAreaLoopState state)

theorem piCircleAreaInitial_eq_arctanAreaLoopInitial_one :
    piCircleAreaInitial =
      toPiAreaLoopState (arctanAreaLoopInitial 1) := by
  native_decide

theorem piCircleAreaState_eq_arctanAreaLoopState_one
    (n : Nat) :
    piCircleAreaState n =
      toPiAreaLoopState (arctanAreaLoopState 1 n) := by
  unfold piCircleAreaState arctanAreaLoopState
  rw [piCircleAreaInitial_eq_arctanAreaLoopInitial_one]
  exact iterateAreaBounds_toPiAreaLoopState n (arctanAreaLoopInitial 1)

/-- The comparison target saying that the loop definition of pi agrees stage by
stage with four times the geometric arctangent at `1`. -/
def PiAreaCompatibility : Prop :=
  forall n : Nat,
    (((4 : Nat) * arctanGeom (1 : Rat) : RealRaw).compute n) =
      piCircleArea.compute n

theorem piAreaCompatibility : PiAreaCompatibility := by
  intro n
  have hnonneg : (0 : Rat) <= 4 := by native_decide
  have hstate := piCircleAreaState_eq_arctanAreaLoopState_one n
  change (RealRaw.scaleRat (4 : Rat) (arctanGeom (1 : Rat))).compute n =
    piCircleArea.compute n
  simp [RealRaw.scaleRat, RealRaw.scaleRatCompute, hnonneg,
    arctanGeom_one_compute_eq, positiveLoopComputeAtStage,
    piCircleArea, piCircleAreaCompute, hstate,
    toPiAreaLoopState]

def functionRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ => (arctanGeom x).compute

def representation : Elementary.Arctan.FunctionRepresentation where
  name := "arctan.geom"
  raw := functionRaw

def Valid : Prop :=
  forall x h, RealRaw.ValidCompute (functionRaw.compute x h)

def PowerSeriesAgreesOnUnit : Prop :=
  Elementary.Arctan.Equivalent Elementary.Arctan.powerSeries representation

theorem powerSeries_equiv_geometric_of_agreement
    (h : PowerSeriesAgreesOnUnit) {x : Rat}
    (hx : Elementary.Arctan.powerSeriesDomain x) :
    (arctan x).Equiv (arctanGeom x) := by
  have hgeom : representation.raw.definedAt x := by
    simp [representation, functionRaw]
  simpa [Elementary.Arctan.powerSeries, representation, functionRaw,
    Elementary.Arctan.powerSeriesFunctionRaw, PartialRealFunRaw.AgreeOnOverlap,
    RealRaw.Equiv] using h x hx hgeom

theorem geometric_equiv_powerSeries_of_agreement
    (h : PowerSeriesAgreesOnUnit) {x : Rat}
    (hx : Elementary.Arctan.powerSeriesDomain x) :
    (arctanGeom x).Equiv (arctan x) :=
  RealRaw.equiv_symm
    (powerSeries_equiv_geometric_of_agreement h hx)

end ArctanGeometry

end ComputableAnalysis
