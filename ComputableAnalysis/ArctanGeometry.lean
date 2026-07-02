import ComputableAnalysis.Elementary
import ComputableAnalysis.FTC
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

theorem integralKernel_pos (u : Rat) : 0 < integralKernel u := by
  unfold integralKernel
  rw [Rat.div_def]
  simpa using (Rat.inv_pos).2 (RationalCircle.Stage.one_add_square_pos u)

theorem integralKernel_le_one (u : Rat) : integralKernel u <= 1 := by
  unfold integralKernel
  have hden : 1 <= 1 + u * u := by
    have hsq := RationalCircle.Stage.ratSquare_nonneg u
    grind
  have hone : (0 : Rat) < 1 := by native_decide
  have h := one_div_le_one_div_of_pos_of_le hone hden
  calc
    integralKernel u <= 1 / (1 : Rat) := h
    _ = 1 := by native_decide

theorem integralUpperStep_nonneg {p r : Rat} (hpr : p <= r) :
    0 <= integralUpperStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  unfold integralUpperStep
  exact Rat.mul_nonneg hlen (Rat.le_of_lt (integralKernel_pos p))

theorem integralLowerStep_nonneg {p r : Rat} (hpr : p <= r) :
    0 <= integralLowerStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  unfold integralLowerStep
  exact Rat.mul_nonneg hlen (Rat.le_of_lt (integralKernel_pos r))

theorem integralUpperStep_left_subcell_le
    {p q r : Rat} (_hpq : p <= q) (hqr : q <= r) :
    integralUpperStep p q <= integralUpperStep p r := by
  have hlen : q - p <= r - p := by grind [Rat.sub_eq_add_neg]
  unfold integralUpperStep
  exact Rat.mul_le_mul_of_nonneg_right hlen
    (Rat.le_of_lt (integralKernel_pos p))

theorem integralUpperStep_le_width {p r : Rat} (hpr : p <= r) :
    integralUpperStep p r <= r - p := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  unfold integralUpperStep
  calc
    (r - p) * integralKernel p <= (r - p) * 1 :=
      Rat.mul_le_mul_of_nonneg_left (integralKernel_le_one p) hlen
    _ = r - p := by grind

private theorem containsInterval_refl (I : QInterval) :
    I.ContainsInterval I := by
  unfold QInterval.ContainsInterval
  exact ⟨Rat.le_refl, Rat.le_refl⟩

private theorem containsInterval_trans {I J K : QInterval}
    (hIJ : I.ContainsInterval J) (hJK : J.ContainsInterval K) :
    I.ContainsInterval K := by
  unfold QInterval.ContainsInterval at *
  exact ⟨Rat.le_trans hIJ.1 hJK.1, Rat.le_trans hJK.2 hIJ.2⟩

theorem integralKernel_antitone_nonneg
    {p q : Rat} (hp0 : 0 <= p) (hpq : p <= q) :
    integralKernel q <= integralKernel p := by
  have hsq : 1 + p * p <= 1 + q * q := by
    have hq0 : 0 <= q := Rat.le_trans hp0 hpq
    have hleft : p * p <= p * q :=
      Rat.mul_le_mul_of_nonneg_left hpq hp0
    have hright : p * q <= q * q :=
      Rat.mul_le_mul_of_nonneg_right hpq hq0
    have hmul : p * p <= q * q := Rat.le_trans hleft hright
    grind
  exact one_div_le_one_div_of_pos_of_le
    (RationalCircle.Stage.one_add_square_pos p) hsq

theorem integralLowerStep_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    integralLowerStep p r <= integralUpperStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hk : integralKernel r <= integralKernel p :=
    integralKernel_antitone_nonneg hp0 hpr
  unfold integralLowerStep integralUpperStep
  exact Rat.mul_le_mul_of_nonneg_left hk hlen

theorem integralLowerStep_refine
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    integralLowerStep p r <=
      integralLowerStep p q + integralLowerStep q r := by
  have hqp : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hrq : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hq0 : 0 <= q := Rat.le_trans hp0 hpq
  have hk : integralKernel r <= integralKernel q :=
    integralKernel_antitone_nonneg hq0 hqr
  unfold integralLowerStep
  calc
    (r - p) * integralKernel r
        = (q - p) * integralKernel r + (r - q) * integralKernel r := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ <= (q - p) * integralKernel q + (r - q) * integralKernel r := by
          exact rat_add_le_add
            (Rat.mul_le_mul_of_nonneg_left hk hqp)
            (Rat.le_refl)
    _ = (q - p) * integralKernel q + (r - q) * integralKernel r := rfl

theorem integralUpperStep_refine
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    integralUpperStep p q + integralUpperStep q r <=
      integralUpperStep p r := by
  have hqp : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hrq : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hk : integralKernel q <= integralKernel p :=
    integralKernel_antitone_nonneg hp0 hpq
  unfold integralUpperStep
  calc
    (q - p) * integralKernel p + (r - q) * integralKernel q
        <= (q - p) * integralKernel p + (r - q) * integralKernel p := by
          exact rat_add_le_add
            (Rat.le_refl)
            (Rat.mul_le_mul_of_nonneg_left hk hrq)
    _ = (r - p) * integralKernel p := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem arctanAreaIncrement_nonneg
    {p q r : Rat} (hpq : p <= q) (hqr : q <= r) :
    0 <= arctanAreaIncrement p q r := by
  have hqp : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hrq : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hrp : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hnum :
      0 <= 2 * (r - p) * (q - p) * (r - q) := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg
        (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hrp)
        hqp)
      hrq
  have hden :
      0 < (1 + p * p) * (1 + q * q) * (1 + r * r) := by
    exact Rat.mul_pos
      (Rat.mul_pos
        (RationalCircle.Stage.one_add_square_pos p)
        (RationalCircle.Stage.one_add_square_pos q))
      (RationalCircle.Stage.one_add_square_pos r)
  unfold arctanAreaIncrement
  rw [Rat.div_def]
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))

theorem arctanAreaDecrement_nonneg
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    0 <= arctanAreaDecrement p q r := by
  have hq0 : 0 <= q := Rat.le_trans hp0 hpq
  have hr0 : 0 <= r := Rat.le_trans hq0 hqr
  have hqp : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hrq : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hrp : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hnum : 0 <= (r - p) * (q - p) * (r - q) := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg hrp hqp)
      hrq
  have hden :
      0 < (1 + p * r) * (1 + p * q) * (1 + q * r) := by
    exact Rat.mul_pos
      (Rat.mul_pos
        (RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0)
        (RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hq0))
      (RationalCircle.Stage.one_add_mul_pos_of_nonneg hq0 hr0)
  unfold arctanAreaDecrement
  rw [Rat.div_def]
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))

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

theorem geometricLowerStep_refine_le
    {p q r : Rat} (hpq : p <= q) (hqr : q <= r) :
    geometricLowerStep p r <=
      geometricLowerStep p q + geometricLowerStep q r := by
  have hinc := arctanAreaIncrement_nonneg hpq hqr
  have href := geometricLowerStep_refine p q r
  grind

theorem geometricUpperStep_refine_le
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    geometricUpperStep p q + geometricUpperStep q r <=
      geometricUpperStep p r := by
  have hdec := arctanAreaDecrement_nonneg hp0 hpq hqr
  have href := geometricUpperStep_refine hp0 hpq hqr
  grind [Rat.sub_eq_add_neg]

theorem geometricUpperStep_nonneg
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    0 <= geometricUpperStep p r := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hden : 0 < 1 + p * r :=
    RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0
  unfold geometricUpperStep
  rw [Rat.div_def]
  exact Rat.mul_nonneg hlen (Rat.le_of_lt ((Rat.inv_pos).2 hden))

theorem geometricLowerStep_nonneg
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    0 <= geometricLowerStep p r := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hfactor : 0 <= 1 + p * r := by
    have hmul := Rat.mul_nonneg hp0 hr0
    grind
  have hleft : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hright : 0 < 1 + r * r :=
    RationalCircle.Stage.one_add_square_pos r
  have hden : 0 < (1 + p * p) * (1 + r * r) :=
    Rat.mul_pos hleft hright
  unfold geometricLowerStep
  rw [Rat.div_def]
  exact Rat.mul_nonneg (Rat.mul_nonneg hlen hfactor)
    (Rat.le_of_lt ((Rat.inv_pos).2 hden))

theorem geometricLowerStep_zero_right (p : Rat) :
    geometricLowerStep p p = 0 := by
  grind [geometricLowerStep, Rat.sub_eq_add_neg]

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

private theorem geometric_factor_square_le_square_den
    {p r : Rat} :
    (1 + p * r) * (1 + p * r) <=
      (1 + p * p) * (1 + r * r) := by
  have hsq : 0 <= (r - p) * (r - p) :=
    RationalCircle.Stage.ratSquare_nonneg (r - p)
  calc
    (1 + p * r) * (1 + p * r)
        <= (1 + p * r) * (1 + p * r) + (r - p) * (r - p) := by
          grind
    _ = (1 + p * p) * (1 + r * r) := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem geometricLowerStep_le_geometricUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    geometricLowerStep p r <= geometricUpperStep p r := by
  let A : Rat := 1 + p * r
  let B : Rat := (1 + p * p) * (1 + r * r)
  let L : Rat := r - p
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hApos : 0 < A := by
    dsimp [A]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0
  have hBpos : 0 < B := by
    dsimp [B]
    exact Rat.mul_pos
      (RationalCircle.Stage.one_add_square_pos p)
      (RationalCircle.Stage.one_add_square_pos r)
  have hlen : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hfac : A * A <= B := by
    dsimp [A, B]
    exact geometric_factor_square_le_square_den
  refine Rat.le_of_mul_le_mul_right (c := B * A) ?_
    (Rat.mul_pos hBpos hApos)
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
  unfold geometricLowerStep geometricUpperStep
  dsimp [A, B, L] at hApos hBpos hlen hfac ⊢
  calc
    (((r - p) * (1 + p * r)) / ((1 + p * p) * (1 + r * r))) *
        (((1 + p * p) * (1 + r * r)) * (1 + p * r))
        = (r - p) * ((1 + p * r) * (1 + p * r)) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ <= (r - p) * ((1 + p * p) * (1 + r * r)) :=
          Rat.mul_le_mul_of_nonneg_left hfac hlen
    _ = ((r - p) / (1 + p * r)) *
        (((1 + p * p) * (1 + r * r)) * (1 + p * r)) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

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

/-- A finite partition whose cells lie in the unit interval. -/
def UnitIntervals : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest =>
      0 <= p /\ p <= r /\ r <= 1 /\ UnitIntervals rest

/-- Ordered coverage of `[a,b]` by a finite list of rational cells.  This is
the bookkeeping invariant needed to compare different lower/upper sum
schedules for the same kernel. -/
def CoversInterval : Rat -> Rat -> List (Rat × Rat) -> Prop
  | a, b, [] => a = b
  | a, b, (p, r) :: rest =>
      p = a /\ p <= r /\ CoversInterval r b rest

theorem CoversInterval.start_le_end
    {a b : Rat} {intervals : List (Rat × Rat)}
    (h : CoversInterval a b intervals) :
    a <= b := by
  induction intervals generalizing a with
  | nil =>
      have hab : a = b := by simpa [CoversInterval] using h
      rw [hab]
      exact Rat.le_refl
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp, hpr, hrest⟩
      subst p
      exact Rat.le_trans hpr (ih hrest)

theorem CoversInterval.nonnegative
    {a b : Rat} {intervals : List (Rat × Rat)}
    (ha : 0 <= a) (h : CoversInterval a b intervals) :
    NonnegativeIntervals intervals := by
  induction intervals generalizing a with
  | nil =>
      simp [NonnegativeIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp, hpr, hrest⟩
      subst p
      exact ⟨ha, hpr, ih (Rat.le_trans ha hpr) hrest⟩

theorem CoversInterval.unit
    {a b : Rat} {intervals : List (Rat × Rat)}
    (ha : 0 <= a) (hb : b <= 1)
    (h : CoversInterval a b intervals) :
    UnitIntervals intervals := by
  induction intervals generalizing a with
  | nil =>
      simp [UnitIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hr1 : r <= 1 :=
        Rat.le_trans (CoversInterval.start_le_end hrest) hb
      exact ⟨ha, hpr, hr1, ih hr0 hrest⟩

theorem CoversInterval.append
    {a b c : Rat} {left right : List (Rat × Rat)}
    (hleft : CoversInterval a b left)
    (hright : CoversInterval b c right) :
    CoversInterval a c (left ++ right) := by
  induction left generalizing a with
  | nil =>
      have hab : a = b := by
        simpa [CoversInterval] using hleft
      subst b
      simpa [CoversInterval] using hright
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hleft with ⟨hp, hpr, hrest⟩
      subst p
      simp [CoversInterval]
      exact ⟨hpr, ih hrest⟩

theorem CoversInterval.single
    {a b : Rat} (hab : a <= b) :
    CoversInterval a b [(a, b)] := by
  simp [CoversInterval, hab]

theorem CoversInterval.extend_right
    {a b c : Rat} {intervals : List (Rat × Rat)}
    (h : CoversInterval a b intervals) (hbc : b <= c) :
    CoversInterval a c (intervals ++ [(b, c)]) :=
  CoversInterval.append h (CoversInterval.single hbc)

theorem unitIntervals_nonnegative
    (intervals : List (Rat × Rat))
    (hwf : UnitIntervals intervals) :
    NonnegativeIntervals intervals := by
  induction intervals with
  | nil =>
      simp [NonnegativeIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, _hr1, hrest⟩
      exact ⟨hp0, hpr, ih hrest⟩

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

def intervalSquareSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => (r - p) * (r - p) + intervalSquareSum rest

def integralSumInterval (intervals : List (Rat × Rat)) : QInterval :=
  { lo := integralLowerSum intervals, hi := integralUpperSum intervals }

def geometricSumInterval (intervals : List (Rat × Rat)) : QInterval :=
  { lo := geometricLowerSum intervals, hi := geometricUpperSum intervals }

/-- Cells in the global Farey mesh whose right endpoint lies at or before
`x`.  These give the lower prefix for the monotone arctangent kernel. -/
def fareyLowerCellsUpTo
    (x : Rat) : List RationalCircle.FareyCell -> List (Rat × Rat)
  | [] => []
  | cell :: rest =>
      if cell.right.value <= x then
        cell.toRatInterval :: fareyLowerCellsUpTo x rest
      else
        fareyLowerCellsUpTo x rest

/-- Cells in the global Farey mesh whose left endpoint lies at or before `x`.
This includes the first cell crossing `x`, hence gives the upper prefix. -/
def fareyUpperCellsUpTo
    (x : Rat) : List RationalCircle.FareyCell -> List (Rat × Rat)
  | [] => []
  | cell :: rest =>
      if cell.left.value <= x then
        cell.toRatInterval :: fareyUpperCellsUpTo x rest
      else
        fareyUpperCellsUpTo x rest

def fareyCellIntervals
    (cells : List RationalCircle.FareyCell) : List (Rat × Rat) :=
  cells.map RationalCircle.FareyCell.toRatInterval

theorem fareyCellIntervals_unit
    (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    UnitIntervals (fareyCellIntervals cells) := by
  induction cells with
  | nil =>
      simp [fareyCellIntervals, UnitIntervals]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      rcases hcell with ⟨hl0, hlr, hr1⟩
      change UnitIntervals
        (RationalCircle.FareyCell.toRatInterval cell ::
          fareyCellIntervals rest)
      exact ⟨hl0, hlr, hr1, ih hrest⟩

theorem fareyCellIntervals_nonnegative
    (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    NonnegativeIntervals (fareyCellIntervals cells) :=
  unitIntervals_nonnegative (fareyCellIntervals cells)
    (fareyCellIntervals_unit cells hcells)

theorem fareyCellIntervals_covers
    {left right : RationalCircle.FareyFraction}
    {cells : List RationalCircle.FareyCell}
    (hconnect : RationalCircle.FareyCell.Connects left right cells)
    (hunit : RationalCircle.FareyCell.UnitList cells) :
    CoversInterval left.value right.value (fareyCellIntervals cells) := by
  induction cells generalizing left with
  | nil =>
      have hvalue :
          left.value = right.value := by
        exact congrArg RationalCircle.FareyFraction.value
          (by simpa [RationalCircle.FareyCell.Connects] using hconnect)
      simpa [fareyCellIntervals, CoversInterval] using hvalue
  | cons cell rest ih =>
      rcases hconnect with ⟨hleft, hrestConnect⟩
      rcases hunit with ⟨hcellUnit, hrestUnit⟩
      rcases hcellUnit with ⟨_hl0, hlr, _hr1⟩
      change CoversInterval left.value right.value
        (RationalCircle.FareyCell.toRatInterval cell ::
          fareyCellIntervals rest)
      exact ⟨by
          exact congrArg RationalCircle.FareyFraction.value hleft,
        by simpa [RationalCircle.FareyCell.toRatInterval] using hlr,
        ih hrestConnect hrestUnit⟩

theorem fareyUnitStage_intervals_covers (n : Nat) :
    CoversInterval 0 1
      (fareyCellIntervals (RationalCircle.fareyUnitStage n)) := by
  simpa [RationalCircle.FareyFraction.value_zero,
    RationalCircle.FareyFraction.value_one] using
    fareyCellIntervals_covers
      (RationalCircle.fareyUnitStage_connects n)
      (RationalCircle.fareyUnitStage_unit n)

theorem fareyLowerCellsUpTo_one_eq_intervals
    (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    fareyLowerCellsUpTo 1 cells = fareyCellIntervals cells := by
  induction cells with
  | nil =>
      simp [fareyLowerCellsUpTo, fareyCellIntervals]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      rcases hcell with ⟨_hl0, _hlr, hr1⟩
      simp [fareyLowerCellsUpTo, fareyCellIntervals, hr1, ih hrest]

theorem fareyUpperCellsUpTo_one_eq_intervals
    (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    fareyUpperCellsUpTo 1 cells = fareyCellIntervals cells := by
  induction cells with
  | nil =>
      simp [fareyUpperCellsUpTo, fareyCellIntervals]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      rcases hcell with ⟨_hl0, hlr, hr1⟩
      have hleft : cell.left.value <= (1 : Rat) := Rat.le_trans hlr hr1
      simp [fareyUpperCellsUpTo, fareyCellIntervals, hleft, ih hrest]

def fareyIntegralLowerPrefix
    (x : Rat) (cells : List RationalCircle.FareyCell) : Rat :=
  integralLowerSum (fareyLowerCellsUpTo x cells)

def fareyIntegralUpperPrefix
    (x : Rat) (cells : List RationalCircle.FareyCell) : Rat :=
  integralUpperSum (fareyUpperCellsUpTo x cells)

def fareyIntegralPrefixInterval
    (x : Rat) (cells : List RationalCircle.FareyCell) : QInterval :=
  { lo := fareyIntegralLowerPrefix x cells,
    hi := fareyIntegralUpperPrefix x cells }

/-- The finite Farey approximation to the integral over `[a,b]`, defined as
a difference of global prefixes.  This is the bookkeeping advantage of a
single mesh: adjacent interval additivity is built into the definition. -/
def fareyIntegralBetweenInterval
    (a b : Rat) (cells : List RationalCircle.FareyCell) : QInterval :=
  { lo := fareyIntegralLowerPrefix b cells - fareyIntegralLowerPrefix a cells,
    hi := fareyIntegralUpperPrefix b cells - fareyIntegralUpperPrefix a cells }

def fareyIntegralStageInterval (a b : Rat) (n : Nat) : QInterval :=
  fareyIntegralBetweenInterval a b (RationalCircle.fareyUnitStage n)

def fareyIntegralPrefixStageInterval (x : Rat) (n : Nat) : QInterval :=
  fareyIntegralPrefixInterval x (RationalCircle.fareyUnitStage n)

theorem fareyIntegralBetweenInterval_add
    (a b c : Rat) (cells : List RationalCircle.FareyCell) :
    fareyIntegralBetweenInterval a c cells =
      QInterval.addInterval
        (fareyIntegralBetweenInterval a b cells)
        (fareyIntegralBetweenInterval b c cells) := by
  unfold fareyIntegralBetweenInterval QInterval.addInterval
  simp
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem fareyIntegralStageInterval_add
    (a b c : Rat) (n : Nat) :
    fareyIntegralStageInterval a c n =
      QInterval.addInterval
        (fareyIntegralStageInterval a b n)
        (fareyIntegralStageInterval b c n) := by
  unfold fareyIntegralStageInterval
  exact fareyIntegralBetweenInterval_add a b c _

theorem fareyLowerCellsUpTo_unit
    (x : Rat) (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    UnitIntervals (fareyLowerCellsUpTo x cells) := by
  induction cells with
  | nil =>
      simp [fareyLowerCellsUpTo, UnitIntervals]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      rcases hcell with ⟨hl0, hlr, hr1⟩
      by_cases hright : cell.right.value <= x
      · simp [fareyLowerCellsUpTo, hright, RationalCircle.FareyCell.toRatInterval,
          UnitIntervals, hl0, hlr, hr1, ih hrest]
      · simp [fareyLowerCellsUpTo, hright, ih hrest]

theorem fareyUpperCellsUpTo_unit
    (x : Rat) (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    UnitIntervals (fareyUpperCellsUpTo x cells) := by
  induction cells with
  | nil =>
      simp [fareyUpperCellsUpTo, UnitIntervals]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      rcases hcell with ⟨hl0, hlr, hr1⟩
      by_cases hleft : cell.left.value <= x
      · simp [fareyUpperCellsUpTo, hleft, RationalCircle.FareyCell.toRatInterval,
          UnitIntervals, hl0, hlr, hr1, ih hrest]
      · simp [fareyUpperCellsUpTo, hleft, ih hrest]

theorem fareyIntegralLowerPrefix_le_upperPrefix
    (x : Rat) (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    fareyIntegralLowerPrefix x cells <=
      fareyIntegralUpperPrefix x cells := by
  induction cells with
  | nil =>
      simp [fareyIntegralLowerPrefix, fareyIntegralUpperPrefix,
        fareyLowerCellsUpTo, fareyUpperCellsUpTo, integralLowerSum,
        integralUpperSum]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      rcases hcell with ⟨hl0, hlr, _hr1⟩
      have hcell_le :
          integralLowerStep cell.left.value cell.right.value <=
            integralUpperStep cell.left.value cell.right.value :=
        integralLowerStep_le_integralUpperStep hl0 hlr
      have htail := ih hrest
      by_cases hright : cell.right.value <= x
      · have hleft : cell.left.value <= x := Rat.le_trans hlr hright
        simp [fareyIntegralLowerPrefix, fareyIntegralUpperPrefix,
          fareyLowerCellsUpTo, fareyUpperCellsUpTo, hright, hleft,
          RationalCircle.FareyCell.toRatInterval, integralLowerSum,
          integralUpperSum]
        exact rat_add_le_add hcell_le htail
      · by_cases hleft : cell.left.value <= x
        · have hupper_nonneg :
            0 <= integralUpperStep cell.left.value cell.right.value :=
            integralUpperStep_nonneg hlr
          simp [fareyIntegralLowerPrefix, fareyIntegralUpperPrefix,
            fareyLowerCellsUpTo, fareyUpperCellsUpTo, hright, hleft,
            RationalCircle.FareyCell.toRatInterval, integralUpperSum]
          calc
            integralLowerSum (fareyLowerCellsUpTo x rest) <=
                integralUpperSum (fareyUpperCellsUpTo x rest) := htail
            _ <= integralUpperStep cell.left.value cell.right.value +
                integralUpperSum (fareyUpperCellsUpTo x rest) := by
                grind
        · simp [fareyIntegralLowerPrefix, fareyIntegralUpperPrefix,
            fareyLowerCellsUpTo, fareyUpperCellsUpTo, hright, hleft]
          exact htail

theorem fareyIntegralPrefixInterval_ordered
    (x : Rat) (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    0 <= (fareyIntegralPrefixInterval x cells).width := by
  unfold fareyIntegralPrefixInterval QInterval.width
  have hle := fareyIntegralLowerPrefix_le_upperPrefix x cells hcells
  grind [Rat.sub_eq_add_neg]

theorem fareyIntegralPrefixStageInterval_ordered
    (x : Rat) (n : Nat) :
    0 <= (fareyIntegralPrefixStageInterval x n).width := by
  unfold fareyIntegralPrefixStageInterval
  exact fareyIntegralPrefixInterval_ordered x
    (RationalCircle.fareyUnitStage n) (RationalCircle.fareyUnitStage_unit n)

theorem fareyIntegralLowerPrefix_subdivide_mono
    (x : Rat) (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    fareyIntegralLowerPrefix x cells <=
      fareyIntegralLowerPrefix x
        (RationalCircle.FareyCell.subdivideList cells) := by
  induction cells with
  | nil =>
      simp [fareyIntegralLowerPrefix, fareyLowerCellsUpTo,
        RationalCircle.FareyCell.subdivideList, integralLowerSum]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      rcases hcell with ⟨hl0, hlr, _hr1⟩
      have hpq :
          cell.left.value <= cell.mediant.value :=
        RationalCircle.FareyFraction.value_le_mediant_of_le hlr
      have hqr :
          cell.mediant.value <= cell.right.value :=
        RationalCircle.FareyFraction.mediant_le_value_of_le hlr
      have htail := ih hrest
      by_cases hright : cell.right.value <= x
      · have hmed : cell.mediant.value <= x := Rat.le_trans hqr hright
        have hmed' : (cell.left.mediant cell.right).value <= x := by
          simpa [RationalCircle.FareyCell.mediant] using hmed
        have hhead :=
          integralLowerStep_refine hl0 hpq hqr
        simp [fareyIntegralLowerPrefix, fareyLowerCellsUpTo,
          RationalCircle.FareyCell.subdivideList,
          RationalCircle.FareyCell.toRatInterval,
          RationalCircle.FareyCell.leftChild,
          RationalCircle.FareyCell.rightChild,
          RationalCircle.FareyCell.mediant, hright, hmed',
          integralLowerSum]
        calc
          integralLowerStep cell.left.value cell.right.value +
              integralLowerSum (fareyLowerCellsUpTo x rest)
              <=
            (integralLowerStep cell.left.value cell.mediant.value +
                integralLowerStep cell.mediant.value cell.right.value) +
              integralLowerSum (fareyLowerCellsUpTo x rest) :=
                rat_add_le_add hhead (Rat.le_refl)
          _ <=
            (integralLowerStep cell.left.value cell.mediant.value +
                integralLowerStep cell.mediant.value cell.right.value) +
              integralLowerSum
                (fareyLowerCellsUpTo x
                  (RationalCircle.FareyCell.subdivideList rest)) :=
                rat_add_le_add (Rat.le_refl) htail
          _ =
            integralLowerStep cell.left.value cell.mediant.value +
              (integralLowerStep cell.mediant.value cell.right.value +
                integralLowerSum
                  (fareyLowerCellsUpTo x
                    (RationalCircle.FareyCell.subdivideList rest))) := by
                grind [Rat.add_assoc, Rat.add_comm]
      · by_cases hmed : cell.mediant.value <= x
        · have hleft_nonneg :
            0 <= integralLowerStep cell.left.value cell.mediant.value :=
            integralLowerStep_nonneg hpq
          have hmed' : (cell.left.mediant cell.right).value <= x := by
            simpa [RationalCircle.FareyCell.mediant] using hmed
          simp [fareyIntegralLowerPrefix, fareyLowerCellsUpTo,
            RationalCircle.FareyCell.subdivideList,
            RationalCircle.FareyCell.toRatInterval,
            RationalCircle.FareyCell.leftChild,
            RationalCircle.FareyCell.rightChild,
            RationalCircle.FareyCell.mediant, hright, hmed',
            integralLowerSum]
          calc
            integralLowerSum (fareyLowerCellsUpTo x rest) <=
                integralLowerSum
                  (fareyLowerCellsUpTo x
                    (RationalCircle.FareyCell.subdivideList rest)) := htail
            _ <= integralLowerStep cell.left.value cell.mediant.value +
                integralLowerSum
                  (fareyLowerCellsUpTo x
                    (RationalCircle.FareyCell.subdivideList rest)) := by
                grind
        · simp [fareyIntegralLowerPrefix, fareyLowerCellsUpTo,
            RationalCircle.FareyCell.subdivideList,
            RationalCircle.FareyCell.leftChild,
            RationalCircle.FareyCell.rightChild,
            RationalCircle.FareyCell.mediant, hright,
            show ¬(cell.left.mediant cell.right).value <= x from by
              intro hh
              exact hmed (by
                simpa [RationalCircle.FareyCell.mediant] using hh)]
          exact htail

theorem fareyIntegralUpperPrefix_subdivide_anti
    (x : Rat) (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    fareyIntegralUpperPrefix x
        (RationalCircle.FareyCell.subdivideList cells) <=
      fareyIntegralUpperPrefix x cells := by
  induction cells with
  | nil =>
      simp [fareyIntegralUpperPrefix, fareyUpperCellsUpTo,
        RationalCircle.FareyCell.subdivideList, integralUpperSum]
  | cons cell rest ih =>
      rcases hcells with ⟨hcell, hrest⟩
      rcases hcell with ⟨hl0, hlr, _hr1⟩
      have hpq :
          cell.left.value <= cell.mediant.value :=
        RationalCircle.FareyFraction.value_le_mediant_of_le hlr
      have hqr :
          cell.mediant.value <= cell.right.value :=
        RationalCircle.FareyFraction.mediant_le_value_of_le hlr
      have htail := ih hrest
      by_cases hleft : cell.left.value <= x
      · by_cases hmed : cell.mediant.value <= x
        · have hmed' : (cell.left.mediant cell.right).value <= x := by
            simpa [RationalCircle.FareyCell.mediant] using hmed
          have hhead := integralUpperStep_refine hl0 hpq hqr
          simp [fareyIntegralUpperPrefix, fareyUpperCellsUpTo,
            RationalCircle.FareyCell.subdivideList,
            RationalCircle.FareyCell.toRatInterval,
            RationalCircle.FareyCell.leftChild,
            RationalCircle.FareyCell.rightChild,
            RationalCircle.FareyCell.mediant, hleft, hmed',
            integralUpperSum]
          calc
            integralUpperStep cell.left.value cell.mediant.value +
                (integralUpperStep cell.mediant.value cell.right.value +
                  integralUpperSum
                    (fareyUpperCellsUpTo x
                      (RationalCircle.FareyCell.subdivideList rest)))
                =
              (integralUpperStep cell.left.value cell.mediant.value +
                  integralUpperStep cell.mediant.value cell.right.value) +
                integralUpperSum
                  (fareyUpperCellsUpTo x
                    (RationalCircle.FareyCell.subdivideList rest)) := by
                  grind [Rat.add_assoc, Rat.add_comm]
            _ <=
              (integralUpperStep cell.left.value cell.mediant.value +
                  integralUpperStep cell.mediant.value cell.right.value) +
                integralUpperSum (fareyUpperCellsUpTo x rest) :=
                  rat_add_le_add (Rat.le_refl) htail
            _ <=
              integralUpperStep cell.left.value cell.right.value +
                integralUpperSum (fareyUpperCellsUpTo x rest) :=
                  rat_add_le_add hhead (Rat.le_refl)
        · have hmed' : ¬(cell.left.mediant cell.right).value <= x := by
            intro hh
            exact hmed (by
              simpa [RationalCircle.FareyCell.mediant] using hh)
          have hhead := integralUpperStep_left_subcell_le hpq hqr
          simp [fareyIntegralUpperPrefix, fareyUpperCellsUpTo,
            RationalCircle.FareyCell.subdivideList,
            RationalCircle.FareyCell.toRatInterval,
            RationalCircle.FareyCell.leftChild,
            RationalCircle.FareyCell.rightChild,
            RationalCircle.FareyCell.mediant, hleft, hmed',
            integralUpperSum]
          calc
            integralUpperStep cell.left.value cell.mediant.value +
                integralUpperSum
                  (fareyUpperCellsUpTo x
                    (RationalCircle.FareyCell.subdivideList rest))
                <=
              integralUpperStep cell.left.value cell.mediant.value +
                integralUpperSum (fareyUpperCellsUpTo x rest) :=
                  rat_add_le_add (Rat.le_refl) htail
            _ <=
              integralUpperStep cell.left.value cell.right.value +
                integralUpperSum (fareyUpperCellsUpTo x rest) :=
                  rat_add_le_add hhead (Rat.le_refl)
      · have hmed' : ¬(cell.left.mediant cell.right).value <= x := by
          intro hh
          exact hleft (Rat.le_trans hpq (by
            simpa [RationalCircle.FareyCell.mediant] using hh))
        simp [fareyIntegralUpperPrefix, fareyUpperCellsUpTo,
          RationalCircle.FareyCell.subdivideList,
          RationalCircle.FareyCell.leftChild,
          RationalCircle.FareyCell.rightChild,
          RationalCircle.FareyCell.mediant, hleft, hmed']
        exact htail

theorem fareyIntegralPrefixInterval_subdivide_refines
    (x : Rat) (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    (fareyIntegralPrefixInterval x cells).ContainsInterval
      (fareyIntegralPrefixInterval x
        (RationalCircle.FareyCell.subdivideList cells)) := by
  unfold QInterval.ContainsInterval fareyIntegralPrefixInterval
  exact ⟨fareyIntegralLowerPrefix_subdivide_mono x cells hcells,
    fareyIntegralUpperPrefix_subdivide_anti x cells hcells⟩

theorem fareyIntegralPrefixStageInterval_step_refines
    (x : Rat) (n : Nat) :
    (fareyIntegralPrefixStageInterval x n).ContainsInterval
      (fareyIntegralPrefixStageInterval x (n + 1)) := by
  unfold fareyIntegralPrefixStageInterval
  change (fareyIntegralPrefixInterval x (RationalCircle.fareyUnitStage n)).ContainsInterval
    (fareyIntegralPrefixInterval x
      (RationalCircle.fareyUnitSubdivide (RationalCircle.fareyUnitStage n)))
  unfold RationalCircle.fareyUnitSubdivide
  exact fareyIntegralPrefixInterval_subdivide_refines x
    (RationalCircle.fareyUnitStage n) (RationalCircle.fareyUnitStage_unit n)

theorem fareyIntegralPrefixStageInterval_nested
    (x : Rat) :
    forall n m, n <= m ->
      (fareyIntegralPrefixStageInterval x n).lo <=
        (fareyIntegralPrefixStageInterval x m).lo /\
      (fareyIntegralPrefixStageInterval x m).lo <=
        (fareyIntegralPrefixStageInterval x m).hi /\
      (fareyIntegralPrefixStageInterval x m).hi <=
        (fareyIntegralPrefixStageInterval x n).hi := by
  intro n m hnm
  induction hnm with
  | refl =>
      have hordered := fareyIntegralPrefixStageInterval_ordered x n
      constructor
      · exact Rat.le_refl
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_refl
  | step hnk ih =>
      rename_i k
      have hstep := fareyIntegralPrefixStageInterval_step_refines x k
      unfold QInterval.ContainsInterval at hstep
      have hordered := fareyIntegralPrefixStageInterval_ordered x (k + 1)
      constructor
      · exact Rat.le_trans ih.1 hstep.1
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_trans hstep.2 ih.2.2

theorem fareyLowerCellsUpTo_eq_nil_of_connects_left_gt
    (x : Rat) {left right : RationalCircle.FareyFraction}
    {cells : List RationalCircle.FareyCell}
    (hconnect : RationalCircle.FareyCell.Connects left right cells)
    (hunit : RationalCircle.FareyCell.UnitList cells)
    (hleft : ¬ left.value <= x) :
    fareyLowerCellsUpTo x cells = [] := by
  induction cells generalizing left with
  | nil =>
      simp [fareyLowerCellsUpTo]
  | cons cell rest ih =>
      rcases hconnect with ⟨hcellLeft, hrestConnect⟩
      rcases hunit with ⟨hcellUnit, hrestUnit⟩
      rcases hcellUnit with ⟨_hl0, hlr, _hr1⟩
      have hcellLeftNot : ¬ cell.left.value <= x := by
        rw [hcellLeft]
        exact hleft
      have hcellRightNot : ¬ cell.right.value <= x := by
        intro hright
        exact hcellLeftNot (Rat.le_trans hlr hright)
      have htail :=
        ih hrestConnect hrestUnit hcellRightNot
      simp [fareyLowerCellsUpTo, hcellRightNot, htail]

theorem fareyUpperCellsUpTo_eq_nil_of_connects_left_gt
    (x : Rat) {left right : RationalCircle.FareyFraction}
    {cells : List RationalCircle.FareyCell}
    (hconnect : RationalCircle.FareyCell.Connects left right cells)
    (hunit : RationalCircle.FareyCell.UnitList cells)
    (hleft : ¬ left.value <= x) :
    fareyUpperCellsUpTo x cells = [] := by
  induction cells generalizing left with
  | nil =>
      simp [fareyUpperCellsUpTo]
  | cons cell rest ih =>
      rcases hconnect with ⟨hcellLeft, hrestConnect⟩
      rcases hunit with ⟨hcellUnit, hrestUnit⟩
      rcases hcellUnit with ⟨_hl0, hlr, _hr1⟩
      have hcellLeftNot : ¬ cell.left.value <= x := by
        rw [hcellLeft]
        exact hleft
      have hcellRightNot : ¬ cell.right.value <= x := by
        intro hright
        exact hcellLeftNot (Rat.le_trans hlr hright)
      have htail :=
        ih hrestConnect hrestUnit hcellRightNot
      simp [fareyUpperCellsUpTo, hcellLeftNot, htail]

theorem fareyIntegralLowerPrefix_eq_zero_of_connects_left_gt
    (x : Rat) {left right : RationalCircle.FareyFraction}
    {cells : List RationalCircle.FareyCell}
    (hconnect : RationalCircle.FareyCell.Connects left right cells)
    (hunit : RationalCircle.FareyCell.UnitList cells)
    (hleft : ¬ left.value <= x) :
    fareyIntegralLowerPrefix x cells = 0 := by
  unfold fareyIntegralLowerPrefix
  rw [fareyLowerCellsUpTo_eq_nil_of_connects_left_gt
    x hconnect hunit hleft]
  simp [integralLowerSum]

theorem fareyIntegralUpperPrefix_eq_zero_of_connects_left_gt
    (x : Rat) {left right : RationalCircle.FareyFraction}
    {cells : List RationalCircle.FareyCell}
    (hconnect : RationalCircle.FareyCell.Connects left right cells)
    (hunit : RationalCircle.FareyCell.UnitList cells)
    (hleft : ¬ left.value <= x) :
    fareyIntegralUpperPrefix x cells = 0 := by
  unfold fareyIntegralUpperPrefix
  rw [fareyUpperCellsUpTo_eq_nil_of_connects_left_gt
    x hconnect hunit hleft]
  simp [integralUpperSum]

theorem fareyLowerCellsUpTo_covers_prefix
    (x : Rat) {left right : RationalCircle.FareyFraction}
    {cells : List RationalCircle.FareyCell}
    (hconnect : RationalCircle.FareyCell.Connects left right cells)
    (hunit : RationalCircle.FareyCell.UnitList cells)
    (hleft : left.value <= x) :
    Exists fun y =>
      y <= x /\ CoversInterval left.value y (fareyLowerCellsUpTo x cells) := by
  induction cells generalizing left with
  | nil =>
      exact ⟨left.value, hleft, by simp [fareyLowerCellsUpTo, CoversInterval]⟩
  | cons cell rest ih =>
      rcases hconnect with ⟨hcellLeft, hrestConnect⟩
      rcases hunit with ⟨hcellUnit, hrestUnit⟩
      rcases hcellUnit with ⟨_hl0, hlr, _hr1⟩
      by_cases hright : cell.right.value <= x
      · obtain ⟨y, hyx, hcoverRest⟩ :=
          ih hrestConnect hrestUnit hright
        have hcover :
            CoversInterval left.value y
              ((cell.left.value, cell.right.value) ::
                fareyLowerCellsUpTo x rest) :=
          ⟨congrArg RationalCircle.FareyFraction.value hcellLeft,
            hlr, hcoverRest⟩
        refine ⟨y, hyx, ?_⟩
        simpa [fareyLowerCellsUpTo, hright,
          RationalCircle.FareyCell.toRatInterval] using hcover
      · have htail :
            fareyLowerCellsUpTo x rest = [] :=
          fareyLowerCellsUpTo_eq_nil_of_connects_left_gt
            x hrestConnect hrestUnit hright
        refine ⟨left.value, hleft, ?_⟩
        simp [fareyLowerCellsUpTo, hright, htail, CoversInterval]

theorem fareyUpperCellsUpTo_covers_prefix
    (x : Rat) {left right : RationalCircle.FareyFraction}
    {cells : List RationalCircle.FareyCell}
    (hconnect : RationalCircle.FareyCell.Connects left right cells)
    (hunit : RationalCircle.FareyCell.UnitList cells)
    (hleft : left.value <= x) (hright : x <= right.value) :
    Exists fun y =>
      x <= y /\ CoversInterval left.value y (fareyUpperCellsUpTo x cells) := by
  induction cells generalizing left with
  | nil =>
      have hvalue : left.value = right.value := by
        exact congrArg RationalCircle.FareyFraction.value
          (by simpa [RationalCircle.FareyCell.Connects] using hconnect)
      have hxleft : x <= left.value := by
        rwa [hvalue]
      exact ⟨left.value, hxleft, by simp [fareyUpperCellsUpTo, CoversInterval]⟩
  | cons cell rest ih =>
      rcases hconnect with ⟨hcellLeft, hrestConnect⟩
      rcases hunit with ⟨hcellUnit, hrestUnit⟩
      rcases hcellUnit with ⟨_hl0, hlr, _hr1⟩
      have hcellLeftLe : cell.left.value <= x := by
        rw [hcellLeft]
        exact hleft
      by_cases hcellRightLe : cell.right.value <= x
      · obtain ⟨y, hxy, hcoverRest⟩ :=
          ih hrestConnect hrestUnit hcellRightLe
        have hcover :
            CoversInterval left.value y
              ((cell.left.value, cell.right.value) ::
                fareyUpperCellsUpTo x rest) :=
          ⟨congrArg RationalCircle.FareyFraction.value hcellLeft,
            hlr, hcoverRest⟩
        refine ⟨y, hxy, ?_⟩
        simpa [fareyUpperCellsUpTo, hcellLeftLe,
          RationalCircle.FareyCell.toRatInterval] using hcover
      · have htail :
            fareyUpperCellsUpTo x rest = [] :=
          fareyUpperCellsUpTo_eq_nil_of_connects_left_gt
            x hrestConnect hrestUnit hcellRightLe
        have hxCellRight : x <= cell.right.value := by grind
        have hcover :
            CoversInterval left.value cell.right.value
              [(cell.left.value, cell.right.value)] :=
          ⟨congrArg RationalCircle.FareyFraction.value hcellLeft,
            hlr, by simp [CoversInterval]⟩
        refine ⟨cell.right.value, hxCellRight, ?_⟩
        simpa [fareyUpperCellsUpTo, hcellLeftLe, htail,
          RationalCircle.FareyCell.toRatInterval] using hcover

theorem fareyLowerCellsUpTo_unitStage_covers_prefix
    {x : Rat} (hx0 : 0 <= x) (n : Nat) :
    Exists fun y =>
      y <= x /\
        CoversInterval 0 y
          (fareyLowerCellsUpTo x (RationalCircle.fareyUnitStage n)) := by
  simpa [RationalCircle.FareyFraction.value_zero] using
    fareyLowerCellsUpTo_covers_prefix
      x
      (RationalCircle.fareyUnitStage_connects n)
      (RationalCircle.fareyUnitStage_unit n)
      (by simpa [RationalCircle.FareyFraction.value_zero] using hx0)

theorem fareyUpperCellsUpTo_unitStage_covers_prefix
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    Exists fun y =>
      x <= y /\
        CoversInterval 0 y
          (fareyUpperCellsUpTo x (RationalCircle.fareyUnitStage n)) := by
  simpa [RationalCircle.FareyFraction.value_zero] using
    fareyUpperCellsUpTo_covers_prefix
      x
      (RationalCircle.fareyUnitStage_connects n)
      (RationalCircle.fareyUnitStage_unit n)
      (by simpa [RationalCircle.FareyFraction.value_zero] using hx0)
      (by simpa [RationalCircle.FareyFraction.value_one] using hx1)

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

theorem geometricLowerSum_le_geometricUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    geometricLowerSum intervals <= geometricUpperSum intervals := by
  induction intervals with
  | nil => simp [geometricLowerSum, geometricUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricLowerSum, geometricUpperSum]
      exact rat_add_le_add
        (geometricLowerStep_le_geometricUpperStep hp0 hpr)
        (ih hrest)

theorem integralLowerSum_le_integralUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralLowerSum intervals <= integralUpperSum intervals := by
  induction intervals with
  | nil => simp [integralLowerSum, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [integralLowerSum, integralUpperSum]
      exact rat_add_le_add
        (integralLowerStep_le_integralUpperStep hp0 hpr)
        (ih hrest)

theorem integralLowerSum_nonneg
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= integralLowerSum intervals := by
  induction intervals with
  | nil => simp [integralLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨_hp0, hpr, hrest⟩
      simp [integralLowerSum]
      have hsum := rat_add_le_add
        (integralLowerStep_nonneg hpr)
        (ih hrest)
      grind

theorem integralUpperSum_nonneg
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= integralUpperSum intervals := by
  induction intervals with
  | nil => simp [integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨_hp0, hpr, hrest⟩
      simp [integralUpperSum]
      have hsum := rat_add_le_add
        (integralUpperStep_nonneg hpr)
        (ih hrest)
      grind

theorem integralLowerStep_zero_right (p : Rat) :
    integralLowerStep p p = 0 := by
  grind [integralLowerStep, Rat.sub_eq_add_neg]

theorem integralLowerSum_eq_zero_of_covers_point
    {a : Rat} {intervals : List (Rat × Rat)}
    (ha : 0 <= a) (hcover : CoversInterval a a intervals) :
    integralLowerSum intervals = 0 := by
  induction intervals generalizing a with
  | nil =>
      simp [integralLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hra_le : r <= a := CoversInterval.start_le_end hrest
      have hra : r = a := by grind
      subst r
      have htail := ih ha hrest
      simp [integralLowerSum, integralLowerStep_zero_right, htail]
      grind

theorem geometricUpperSum_nonneg
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= geometricUpperSum intervals := by
  induction intervals with
  | nil => simp [geometricUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricUpperSum]
      have hsum := rat_add_le_add
        (geometricUpperStep_nonneg hp0 hpr)
        (ih hrest)
      grind

theorem geometricLowerSum_nonneg
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= geometricLowerSum intervals := by
  induction intervals with
  | nil => simp [geometricLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricLowerSum]
      have hsum := rat_add_le_add
        (geometricLowerStep_nonneg hp0 hpr)
        (ih hrest)
      grind

theorem geometricLowerSum_eq_zero_of_covers_point
    {a : Rat} {intervals : List (Rat × Rat)}
    (ha : 0 <= a) (hcover : CoversInterval a a intervals) :
    geometricLowerSum intervals = 0 := by
  induction intervals generalizing a with
  | nil =>
      simp [geometricLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hra_le : r <= a := CoversInterval.start_le_end hrest
      have hra : r = a := by grind
      subst r
      have htail := ih ha hrest
      simp [geometricLowerSum, geometricLowerStep_zero_right, htail]
      grind

theorem integralLowerSum_append
    (left right : List (Rat × Rat)) :
    integralLowerSum (left ++ right) =
      integralLowerSum left + integralLowerSum right := by
  induction left with
  | nil =>
      simp [integralLowerSum]
      grind
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [integralLowerSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem integralUpperSum_append
    (left right : List (Rat × Rat)) :
    integralUpperSum (left ++ right) =
      integralUpperSum left + integralUpperSum right := by
  induction left with
  | nil =>
      simp [integralUpperSum]
      grind
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [integralUpperSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem geometricLowerSum_append
    (left right : List (Rat × Rat)) :
    geometricLowerSum (left ++ right) =
      geometricLowerSum left + geometricLowerSum right := by
  induction left with
  | nil =>
      simp [geometricLowerSum]
      grind
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [geometricLowerSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem geometricUpperSum_append
    (left right : List (Rat × Rat)) :
    geometricUpperSum (left ++ right) =
      geometricUpperSum left + geometricUpperSum right := by
  induction left with
  | nil =>
      simp [geometricUpperSum]
      grind
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [geometricUpperSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem integralLowerSum_le_append_of_nonnegative
    (left right : List (Rat × Rat))
    (hright : NonnegativeIntervals right) :
    integralLowerSum left <= integralLowerSum (left ++ right) := by
  rw [integralLowerSum_append]
  have hnonneg := integralLowerSum_nonneg right hright
  grind

theorem geometricLowerSum_le_append_of_nonnegative
    (left right : List (Rat × Rat))
    (hright : NonnegativeIntervals right) :
    geometricLowerSum left <= geometricLowerSum (left ++ right) := by
  rw [geometricLowerSum_append]
  have hnonneg := geometricLowerSum_nonneg right hright
  grind

theorem integralLowerSum_le_integralUpperSum_of_covers
    {a b : Rat} (ha : 0 <= a)
    (lower upper : List (Rat × Rat))
    (hlower : CoversInterval a b lower)
    (hupper : CoversInterval a b upper) :
    integralLowerSum lower <= integralUpperSum upper := by
  let N := lower.length + upper.length
  have main :
      forall N lower upper a b,
        lower.length + upper.length <= N ->
        0 <= a ->
        CoversInterval a b lower ->
        CoversInterval a b upper ->
        integralLowerSum lower <= integralUpperSum upper := by
    intro N
    induction N with
    | zero =>
        intro lower upper a b hlen ha hlower hupper
        cases lower <;> cases upper <;>
          simp [integralLowerSum, integralUpperSum] at hlen ⊢
    | succ N ih =>
        intro lower upper a b hlen ha hlower hupper
        cases lower with
        | nil =>
            have hupperNonneg :
                0 <= integralUpperSum upper :=
              integralUpperSum_nonneg upper
                (CoversInterval.nonnegative ha hupper)
            simpa [integralLowerSum] using hupperNonneg
        | cons lowerHead lowerRest =>
            cases upper with
            | nil =>
                have hab : a = b := by
                  simpa [CoversInterval] using hupper
                subst b
                have hzero :=
                  integralLowerSum_eq_zero_of_covers_point
                    (a := a) (intervals := lowerHead :: lowerRest)
                    ha hlower
                simp [integralUpperSum, hzero]
            | cons upperHead upperRest =>
                rcases lowerHead with ⟨p, r⟩
                rcases upperHead with ⟨p', s⟩
                rcases hlower with ⟨hp, hpr, hlowerRest⟩
                rcases hupper with ⟨hp', hps, hupperRest⟩
                subst p
                subst p'
                by_cases hrs : r <= s
                · have hr0 : 0 <= r := Rat.le_trans ha hpr
                  have hsplitUpper :
                      CoversInterval r b ((r, s) :: upperRest) :=
                    ⟨rfl, hrs, hupperRest⟩
                  have hlenRec :
                      lowerRest.length + (((r, s) :: upperRest).length) <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih lowerRest ((r, s) :: upperRest) r b
                      hlenRec hr0 hlowerRest hsplitUpper
                  have hheadLow :
                      integralLowerStep a r <= integralUpperStep a r :=
                    integralLowerStep_le_integralUpperStep ha hpr
                  have hheadSplit :
                      integralUpperStep a r + integralUpperStep r s <=
                        integralUpperStep a s :=
                    integralUpperStep_refine ha hpr hrs
                  simp [integralLowerSum, integralUpperSum] at hrec ⊢
                  calc
                    integralLowerStep a r + integralLowerSum lowerRest
                        <= integralUpperStep a r +
                            (integralUpperStep r s +
                              integralUpperSum upperRest) :=
                          rat_add_le_add hheadLow hrec
                    _ = (integralUpperStep a r + integralUpperStep r s) +
                            integralUpperSum upperRest := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= integralUpperStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                · have hsr : s <= r := by grind
                  have hs0 : 0 <= s := Rat.le_trans ha hps
                  have hsplitLower :
                      CoversInterval s b ((s, r) :: lowerRest) :=
                    ⟨rfl, hsr, hlowerRest⟩
                  have hlenRec :
                      (((s, r) :: lowerRest).length) + upperRest.length <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih ((s, r) :: lowerRest) upperRest s b
                      hlenRec hs0 hsplitLower hupperRest
                  have hheadSplit :
                      integralLowerStep a r <=
                        integralLowerStep a s + integralLowerStep s r :=
                    integralLowerStep_refine ha hps hsr
                  have hheadLow :
                      integralLowerStep a s <= integralUpperStep a s :=
                    integralLowerStep_le_integralUpperStep ha hps
                  simp [integralLowerSum, integralUpperSum] at hrec ⊢
                  calc
                    integralLowerStep a r + integralLowerSum lowerRest
                        <= (integralLowerStep a s + integralLowerStep s r) +
                            integralLowerSum lowerRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                    _ = integralLowerStep a s +
                            (integralLowerStep s r +
                              integralLowerSum lowerRest) := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= integralLowerStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add Rat.le_refl hrec
                    _ <= integralUpperStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add hheadLow Rat.le_refl
  exact main N lower upper a b (Nat.le_refl N) ha hlower hupper

theorem integralSumInterval_overlaps_of_covers
    {a b : Rat} (ha : 0 <= a)
    (left right : List (Rat × Rat))
    (hleft : CoversInterval a b left)
    (hright : CoversInterval a b right) :
    QInterval.Overlaps (integralSumInterval left)
      (integralSumInterval right) := by
  unfold QInterval.Overlaps integralSumInterval
  exact ⟨
    integralLowerSum_le_integralUpperSum_of_covers
      ha left right hleft hright,
    integralLowerSum_le_integralUpperSum_of_covers
      ha right left hright hleft⟩

theorem integralLowerSum_le_geometricUpperSum_of_covers
    {a b : Rat} (ha : 0 <= a)
    (lower upper : List (Rat × Rat))
    (hlower : CoversInterval a b lower)
    (hupper : CoversInterval a b upper) :
    integralLowerSum lower <= geometricUpperSum upper := by
  let N := lower.length + upper.length
  have main :
      forall N lower upper a b,
        lower.length + upper.length <= N ->
        0 <= a ->
        CoversInterval a b lower ->
        CoversInterval a b upper ->
        integralLowerSum lower <= geometricUpperSum upper := by
    intro N
    induction N with
    | zero =>
        intro lower upper a b hlen ha hlower hupper
        cases lower <;> cases upper <;>
          simp [integralLowerSum, geometricUpperSum] at hlen ⊢
    | succ N ih =>
        intro lower upper a b hlen ha hlower hupper
        cases lower with
        | nil =>
            have hupperNonneg :
                0 <= geometricUpperSum upper :=
              geometricUpperSum_nonneg upper
                (CoversInterval.nonnegative ha hupper)
            simpa [integralLowerSum] using hupperNonneg
        | cons lowerHead lowerRest =>
            cases upper with
            | nil =>
                have hab : a = b := by
                  simpa [CoversInterval] using hupper
                subst b
                have hzero :=
                  integralLowerSum_eq_zero_of_covers_point
                    (a := a) (intervals := lowerHead :: lowerRest)
                    ha hlower
                simp [geometricUpperSum, hzero]
            | cons upperHead upperRest =>
                rcases lowerHead with ⟨p, r⟩
                rcases upperHead with ⟨p', s⟩
                rcases hlower with ⟨hp, hpr, hlowerRest⟩
                rcases hupper with ⟨hp', hps, hupperRest⟩
                subst p
                subst p'
                by_cases hrs : r <= s
                · have hr0 : 0 <= r := Rat.le_trans ha hpr
                  have hsplitUpper :
                      CoversInterval r b ((r, s) :: upperRest) :=
                    ⟨rfl, hrs, hupperRest⟩
                  have hlenRec :
                      lowerRest.length + (((r, s) :: upperRest).length) <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih lowerRest ((r, s) :: upperRest) r b
                      hlenRec hr0 hlowerRest hsplitUpper
                  have hheadLow :
                      integralLowerStep a r <= geometricUpperStep a r :=
                    integralLowerStep_le_geometricUpperStep ha hpr
                  have hheadSplit :
                      geometricUpperStep a r + geometricUpperStep r s <=
                        geometricUpperStep a s :=
                    geometricUpperStep_refine_le ha hpr hrs
                  simp [integralLowerSum, geometricUpperSum] at hrec ⊢
                  calc
                    integralLowerStep a r + integralLowerSum lowerRest
                        <= geometricUpperStep a r +
                            (geometricUpperStep r s +
                              geometricUpperSum upperRest) :=
                          rat_add_le_add hheadLow hrec
                    _ = (geometricUpperStep a r + geometricUpperStep r s) +
                            geometricUpperSum upperRest := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= geometricUpperStep a s +
                            geometricUpperSum upperRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                · have hsr : s <= r := by grind
                  have hs0 : 0 <= s := Rat.le_trans ha hps
                  have hsplitLower :
                      CoversInterval s b ((s, r) :: lowerRest) :=
                    ⟨rfl, hsr, hlowerRest⟩
                  have hlenRec :
                      (((s, r) :: lowerRest).length) + upperRest.length <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih ((s, r) :: lowerRest) upperRest s b
                      hlenRec hs0 hsplitLower hupperRest
                  have hheadSplit :
                      integralLowerStep a r <=
                        integralLowerStep a s + integralLowerStep s r :=
                    integralLowerStep_refine ha hps hsr
                  have hheadLow :
                      integralLowerStep a s <= geometricUpperStep a s :=
                    integralLowerStep_le_geometricUpperStep ha hps
                  simp [integralLowerSum, geometricUpperSum] at hrec ⊢
                  calc
                    integralLowerStep a r + integralLowerSum lowerRest
                        <= (integralLowerStep a s + integralLowerStep s r) +
                            integralLowerSum lowerRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                    _ = integralLowerStep a s +
                            (integralLowerStep s r +
                              integralLowerSum lowerRest) := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= integralLowerStep a s +
                            geometricUpperSum upperRest :=
                          rat_add_le_add Rat.le_refl hrec
                    _ <= geometricUpperStep a s +
                            geometricUpperSum upperRest :=
                          rat_add_le_add hheadLow Rat.le_refl
  exact main N lower upper a b (Nat.le_refl N) ha hlower hupper

theorem geometricLowerSum_le_integralUpperSum_of_covers
    {a b : Rat} (ha : 0 <= a)
    (lower upper : List (Rat × Rat))
    (hlower : CoversInterval a b lower)
    (hupper : CoversInterval a b upper) :
    geometricLowerSum lower <= integralUpperSum upper := by
  let N := lower.length + upper.length
  have main :
      forall N lower upper a b,
        lower.length + upper.length <= N ->
        0 <= a ->
        CoversInterval a b lower ->
        CoversInterval a b upper ->
        geometricLowerSum lower <= integralUpperSum upper := by
    intro N
    induction N with
    | zero =>
        intro lower upper a b hlen ha hlower hupper
        cases lower <;> cases upper <;>
          simp [geometricLowerSum, integralUpperSum] at hlen ⊢
    | succ N ih =>
        intro lower upper a b hlen ha hlower hupper
        cases lower with
        | nil =>
            have hupperNonneg :
                0 <= integralUpperSum upper :=
              integralUpperSum_nonneg upper
                (CoversInterval.nonnegative ha hupper)
            simpa [geometricLowerSum] using hupperNonneg
        | cons lowerHead lowerRest =>
            cases upper with
            | nil =>
                have hab : a = b := by
                  simpa [CoversInterval] using hupper
                subst b
                have hzero :=
                  geometricLowerSum_eq_zero_of_covers_point
                    (a := a) (intervals := lowerHead :: lowerRest)
                    ha hlower
                simp [integralUpperSum, hzero]
            | cons upperHead upperRest =>
                rcases lowerHead with ⟨p, r⟩
                rcases upperHead with ⟨p', s⟩
                rcases hlower with ⟨hp, hpr, hlowerRest⟩
                rcases hupper with ⟨hp', hps, hupperRest⟩
                subst p
                subst p'
                by_cases hrs : r <= s
                · have hr0 : 0 <= r := Rat.le_trans ha hpr
                  have hsplitUpper :
                      CoversInterval r b ((r, s) :: upperRest) :=
                    ⟨rfl, hrs, hupperRest⟩
                  have hlenRec :
                      lowerRest.length + (((r, s) :: upperRest).length) <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih lowerRest ((r, s) :: upperRest) r b
                      hlenRec hr0 hlowerRest hsplitUpper
                  have hheadLow :
                      geometricLowerStep a r <= integralUpperStep a r :=
                    geometricLowerStep_le_integralUpperStep ha hpr
                  have hheadSplit :
                      integralUpperStep a r + integralUpperStep r s <=
                        integralUpperStep a s :=
                    integralUpperStep_refine ha hpr hrs
                  simp [geometricLowerSum, integralUpperSum] at hrec ⊢
                  calc
                    geometricLowerStep a r + geometricLowerSum lowerRest
                        <= integralUpperStep a r +
                            (integralUpperStep r s +
                              integralUpperSum upperRest) :=
                          rat_add_le_add hheadLow hrec
                    _ = (integralUpperStep a r + integralUpperStep r s) +
                            integralUpperSum upperRest := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= integralUpperStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                · have hsr : s <= r := by grind
                  have hs0 : 0 <= s := Rat.le_trans ha hps
                  have hsplitLower :
                      CoversInterval s b ((s, r) :: lowerRest) :=
                    ⟨rfl, hsr, hlowerRest⟩
                  have hlenRec :
                      (((s, r) :: lowerRest).length) + upperRest.length <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih ((s, r) :: lowerRest) upperRest s b
                      hlenRec hs0 hsplitLower hupperRest
                  have hheadSplit :
                      geometricLowerStep a r <=
                        geometricLowerStep a s + geometricLowerStep s r :=
                    geometricLowerStep_refine_le hps hsr
                  have hheadLow :
                      geometricLowerStep a s <= integralUpperStep a s :=
                    geometricLowerStep_le_integralUpperStep ha hps
                  simp [geometricLowerSum, integralUpperSum] at hrec ⊢
                  calc
                    geometricLowerStep a r + geometricLowerSum lowerRest
                        <=
                          (geometricLowerStep a s + geometricLowerStep s r) +
                            geometricLowerSum lowerRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                    _ = geometricLowerStep a s +
                            (geometricLowerStep s r +
                              geometricLowerSum lowerRest) := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= geometricLowerStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add Rat.le_refl hrec
                    _ <= integralUpperStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add hheadLow Rat.le_refl
  exact main N lower upper a b (Nat.le_refl N) ha hlower hupper

theorem integralLowerSum_le_geometricUpperSum_of_covers_right
    {a b c : Rat} (ha : 0 <= a) (hbc : b <= c)
    (lower upper : List (Rat × Rat))
    (hlower : CoversInterval a b lower)
    (hupper : CoversInterval a c upper) :
    integralLowerSum lower <= geometricUpperSum upper := by
  have hlong : CoversInterval a c (lower ++ [(b, c)]) :=
    CoversInterval.extend_right hlower hbc
  have hb0 : 0 <= b :=
    Rat.le_trans ha (CoversInterval.start_le_end hlower)
  have htail : NonnegativeIntervals [(b, c)] := by
    simp [NonnegativeIntervals, hb0, hbc]
  have hprefix :
      integralLowerSum lower <=
        integralLowerSum (lower ++ [(b, c)]) :=
    integralLowerSum_le_append_of_nonnegative lower [(b, c)] htail
  have hcompare :
      integralLowerSum (lower ++ [(b, c)]) <=
        geometricUpperSum upper :=
    integralLowerSum_le_geometricUpperSum_of_covers
      ha (lower ++ [(b, c)]) upper hlong hupper
  exact Rat.le_trans hprefix hcompare

theorem geometricLowerSum_le_integralUpperSum_of_covers_right
    {a b c : Rat} (ha : 0 <= a) (hbc : b <= c)
    (lower upper : List (Rat × Rat))
    (hlower : CoversInterval a b lower)
    (hupper : CoversInterval a c upper) :
    geometricLowerSum lower <= integralUpperSum upper := by
  have hlong : CoversInterval a c (lower ++ [(b, c)]) :=
    CoversInterval.extend_right hlower hbc
  have hb0 : 0 <= b :=
    Rat.le_trans ha (CoversInterval.start_le_end hlower)
  have htail : NonnegativeIntervals [(b, c)] := by
    simp [NonnegativeIntervals, hb0, hbc]
  have hprefix :
      geometricLowerSum lower <=
        geometricLowerSum (lower ++ [(b, c)]) :=
    geometricLowerSum_le_append_of_nonnegative lower [(b, c)] htail
  have hcompare :
      geometricLowerSum (lower ++ [(b, c)]) <=
        integralUpperSum upper :=
    geometricLowerSum_le_integralUpperSum_of_covers
      ha (lower ++ [(b, c)]) upper hlong hupper
  exact Rat.le_trans hprefix hcompare

theorem integralSumInterval_overlaps_geometricSumInterval_of_covers
    {a b : Rat} (ha : 0 <= a)
    (integral geometric : List (Rat × Rat))
    (hintegral : CoversInterval a b integral)
    (hgeometric : CoversInterval a b geometric) :
    QInterval.Overlaps (integralSumInterval integral)
      (geometricSumInterval geometric) := by
  unfold QInterval.Overlaps integralSumInterval geometricSumInterval
  exact ⟨
    integralLowerSum_le_geometricUpperSum_of_covers
      ha integral geometric hintegral hgeometric,
    geometricLowerSum_le_integralUpperSum_of_covers
      ha geometric integral hgeometric hintegral⟩

theorem integralBracketInterval_overlaps_geometricSumInterval_of_covers
    {a lowerEnd x upperEnd : Rat} (ha : 0 <= a)
    (hlowerEnd : lowerEnd <= x) (hupperEnd : x <= upperEnd)
    (lower upper geometric : List (Rat × Rat))
    (hlower : CoversInterval a lowerEnd lower)
    (hupper : CoversInterval a upperEnd upper)
    (hgeometric : CoversInterval a x geometric) :
    QInterval.Overlaps
      { lo := integralLowerSum lower, hi := integralUpperSum upper }
      (geometricSumInterval geometric) := by
  unfold QInterval.Overlaps geometricSumInterval
  exact ⟨
    integralLowerSum_le_geometricUpperSum_of_covers_right
      ha hlowerEnd lower geometric hlower hgeometric,
    geometricLowerSum_le_integralUpperSum_of_covers_right
      ha hupperEnd geometric upper hgeometric hupper⟩

theorem integralSumInterval_ordered
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= (integralSumInterval intervals).width := by
  unfold integralSumInterval QInterval.width
  have hle := integralLowerSum_le_integralUpperSum intervals hwf
  grind [Rat.sub_eq_add_neg]

theorem geometricSumInterval_ordered
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= (geometricSumInterval intervals).width := by
  unfold geometricSumInterval QInterval.width
  have hle := geometricLowerSum_le_geometricUpperSum intervals hwf
  grind [Rat.sub_eq_add_neg]

private theorem one_le_one_add_square (x : Rat) :
    1 <= 1 + x * x := by
  have hsq := RationalCircle.Stage.ratSquare_nonneg x
  grind

private theorem one_le_square_den (p r : Rat) :
    1 <= (1 + p * p) * (1 + r * r) := by
  have hp1 : 1 <= 1 + p * p := one_le_one_add_square p
  have hr1 : 1 <= 1 + r * r := one_le_one_add_square r
  calc
    1 = 1 * 1 := by grind
    _ <= (1 + p * p) * 1 :=
          Rat.mul_le_mul_of_nonneg_right hp1 (by native_decide)
    _ <= (1 + p * p) * (1 + r * r) :=
          Rat.mul_le_mul_of_nonneg_left hr1 (by grind)

private theorem div_le_two_of_sum_le_two {p r D : Rat}
    (hDpos : 0 < D) (hD1 : 1 <= D) (hsum : p + r <= 2) :
    (p + r) / D <= 2 := by
  have hDne : D ≠ 0 := Rat.ne_of_gt hDpos
  apply Rat.le_of_mul_le_mul_right (c := D)
  · calc
      ((p + r) / D) * D = p + r := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= 2 := hsum
      _ <= 2 * D := by
        calc
          (2 : Rat) = 2 * 1 := by grind
          _ <= 2 * D := Rat.mul_le_mul_of_nonneg_left hD1 (by native_decide)
  · exact hDpos

private theorem kernel_diff_le_two_len {p r : Rat}
    (hpr : p <= r) (hr1 : r <= 1) :
    integralKernel p - integralKernel r <= 2 * (r - p) := by
  let A : Rat := 1 + p * p
  let B : Rat := 1 + r * r
  let D : Rat := A * B
  have hApos : 0 < A := by
    dsimp [A]
    exact RationalCircle.Stage.one_add_square_pos p
  have hBpos : 0 < B := by
    dsimp [B]
    exact RationalCircle.Stage.one_add_square_pos r
  have hDpos : 0 < D := by
    dsimp [D]
    exact Rat.mul_pos hApos hBpos
  have hD1 : 1 <= D := by
    dsimp [D, A, B]
    exact one_le_square_den p r
  have hp1 : p <= 1 := Rat.le_trans hpr hr1
  have hsum : p + r <= 2 := by grind
  have hratio : (p + r) / D <= 2 :=
    div_le_two_of_sum_le_two hDpos hD1 hsum
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  apply Rat.le_of_mul_le_mul_right (c := D)
  · calc
      (integralKernel p - integralKernel r) * D =
          (r - p) * (p + r) := by
        dsimp [D, A, B]
        unfold integralKernel
        rw [Rat.div_def, Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel]
      _ = (r - p) * ((p + r) / D) * D := by
        dsimp [D, A, B]
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (r - p) * 2 * D := by
        exact Rat.mul_le_mul_of_nonneg_right
          (Rat.mul_le_mul_of_nonneg_left hratio hlen)
          (Rat.le_of_lt hDpos)
      _ = (2 * (r - p)) * D := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hDpos

theorem integralCellWidth_le_two_square {p r : Rat}
    (hpr : p <= r) (hr1 : r <= 1) :
    integralUpperStep p r - integralLowerStep p r <=
      2 * ((r - p) * (r - p)) := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hdiff := kernel_diff_le_two_len hpr hr1
  unfold integralUpperStep integralLowerStep
  calc
    (r - p) * integralKernel p - (r - p) * integralKernel r
        = (r - p) * (integralKernel p - integralKernel r) := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add]
    _ <= (r - p) * (2 * (r - p)) :=
          Rat.mul_le_mul_of_nonneg_left hdiff hlen
    _ = 2 * ((r - p) * (r - p)) := by
          grind [Rat.mul_assoc, Rat.mul_comm]

theorem integralSumInterval_width_le_two_squareSum
    (intervals : List (Rat × Rat))
    (hwf : UnitIntervals intervals) :
    (integralSumInterval intervals).width <=
      2 * intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      change (0 : Rat) - 0 <= 2 * 0
      native_decide
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨_hp0, hpr, hr1, hrest⟩
      have hcell := integralCellWidth_le_two_square hpr hr1
      have htail := ih hrest
      unfold integralSumInterval QInterval.width
      simp [integralLowerSum, integralUpperSum, intervalSquareSum]
      calc
        integralUpperStep p r + integralUpperSum rest -
              (integralLowerStep p r + integralLowerSum rest)
            = (integralUpperStep p r - integralLowerStep p r) +
                (integralUpperSum rest - integralLowerSum rest) := by
              grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
        _ <= 2 * ((r - p) * (r - p)) +
              2 * intervalSquareSum rest :=
              rat_add_le_add hcell htail
        _ = 2 * (((r - p) * (r - p)) +
              intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

theorem fareyIntegralPrefixInterval_width_le_two_squareSum_add_bound
    (x : Rat) {left right : RationalCircle.FareyFraction}
    {cells : List RationalCircle.FareyCell} {M : Rat}
    (hconnect : RationalCircle.FareyCell.Connects left right cells)
    (hunit : RationalCircle.FareyCell.UnitList cells)
    (hbound : RationalCircle.FareyCell.WidthListAtMost M cells)
    (hM : 0 <= M) :
    (fareyIntegralPrefixInterval x cells).width <=
      2 * RationalCircle.FareyCell.widthSquareSum cells + M := by
  induction cells generalizing left with
  | nil =>
      simp [fareyIntegralPrefixInterval, fareyIntegralLowerPrefix,
        fareyIntegralUpperPrefix, fareyLowerCellsUpTo, fareyUpperCellsUpTo,
        integralLowerSum, integralUpperSum, RationalCircle.FareyCell.widthSquareSum,
        QInterval.width]
      grind
  | cons cell rest ih =>
      rcases hconnect with ⟨hcellLeft, hrestConnect⟩
      rcases hunit with ⟨hcellUnit, hrestUnit⟩
      rcases hbound with ⟨hcellBound, hrestBound⟩
      rcases hcellUnit with ⟨hl0, hlr, hr1⟩
      have htailBound :=
        ih hrestConnect hrestUnit hrestBound
      have hcellGap :
          integralUpperStep cell.left.value cell.right.value -
              integralLowerStep cell.left.value cell.right.value <=
            2 * (cell.width * cell.width) := by
        simpa [RationalCircle.FareyCell.width,
          RationalCircle.FareyCell.toRatInterval] using
          integralCellWidth_le_two_square hlr hr1
      by_cases hright : cell.right.value <= x
      · have hleftSelect : cell.left.value <= x :=
          Rat.le_trans hlr hright
        simp [fareyIntegralPrefixInterval, fareyIntegralLowerPrefix,
          fareyIntegralUpperPrefix, fareyLowerCellsUpTo, fareyUpperCellsUpTo,
          hright, hleftSelect, RationalCircle.FareyCell.toRatInterval,
          integralLowerSum, integralUpperSum, QInterval.width,
          RationalCircle.FareyCell.widthSquareSum] at htailBound ⊢
        calc
          integralUpperStep cell.left.value cell.right.value +
                integralUpperSum (fareyUpperCellsUpTo x rest) -
              (integralLowerStep cell.left.value cell.right.value +
                integralLowerSum (fareyLowerCellsUpTo x rest))
              =
            (integralUpperStep cell.left.value cell.right.value -
                integralLowerStep cell.left.value cell.right.value) +
              (integralUpperSum (fareyUpperCellsUpTo x rest) -
                integralLowerSum (fareyLowerCellsUpTo x rest)) := by
              grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
          _ <=
            2 * (cell.width * cell.width) +
              (2 * RationalCircle.FareyCell.widthSquareSum rest + M) :=
              rat_add_le_add hcellGap htailBound
          _ =
            2 *
                (cell.width * cell.width +
                  RationalCircle.FareyCell.widthSquareSum rest) + M := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
                Rat.mul_assoc, Rat.mul_comm]
      · by_cases hleftSelect : cell.left.value <= x
        · have hlowerTail :
            fareyIntegralLowerPrefix x rest = 0 :=
            fareyIntegralLowerPrefix_eq_zero_of_connects_left_gt
              x hrestConnect hrestUnit hright
          have hupperTail :
            fareyIntegralUpperPrefix x rest = 0 :=
            fareyIntegralUpperPrefix_eq_zero_of_connects_left_gt
              x hrestConnect hrestUnit hright
          have hlowerTailSum :
              integralLowerSum (fareyLowerCellsUpTo x rest) = 0 := by
            simpa [fareyIntegralLowerPrefix] using hlowerTail
          have hupperTailSum :
              integralUpperSum (fareyUpperCellsUpTo x rest) = 0 := by
            simpa [fareyIntegralUpperPrefix] using hupperTail
          have hcellUpper_le_width :
              integralUpperStep cell.left.value cell.right.value <=
                cell.width := by
            simpa [RationalCircle.FareyCell.width] using
              integralUpperStep_le_width hlr
          have hnonnegSquares :
              0 <=
                2 *
                  (cell.width * cell.width +
                    RationalCircle.FareyCell.widthSquareSum rest) := by
            have hs :
                0 <= cell.width * cell.width +
                    RationalCircle.FareyCell.widthSquareSum rest :=
              Rat.add_nonneg
                (RationalCircle.Stage.ratSquare_nonneg cell.width)
                (RationalCircle.FareyCell.widthSquareSum_nonneg rest)
            exact Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hs
          simp [fareyIntegralPrefixInterval, fareyIntegralLowerPrefix,
            fareyIntegralUpperPrefix, fareyLowerCellsUpTo, fareyUpperCellsUpTo,
            hright, hleftSelect, RationalCircle.FareyCell.toRatInterval,
            integralUpperSum, QInterval.width,
            RationalCircle.FareyCell.widthSquareSum,
            hlowerTailSum, hupperTailSum]
          calc
            integralUpperStep cell.left.value cell.right.value + 0 - 0
                <= cell.width := by grind
            _ <= M := hcellBound
            _ <=
                2 *
                    (cell.width * cell.width +
                      RationalCircle.FareyCell.widthSquareSum rest) + M := by
                  grind
        · simp [fareyIntegralPrefixInterval, fareyIntegralLowerPrefix,
            fareyIntegralUpperPrefix, fareyLowerCellsUpTo, fareyUpperCellsUpTo,
            hright, hleftSelect, RationalCircle.FareyCell.widthSquareSum,
            QInterval.width] at htailBound ⊢
          have hcellSquaresNonneg :
              0 <= 2 * (cell.width * cell.width) := by
            exact Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2)
              (RationalCircle.Stage.ratSquare_nonneg cell.width)
          calc
            fareyIntegralUpperPrefix x rest -
                fareyIntegralLowerPrefix x rest
                <=
              2 * RationalCircle.FareyCell.widthSquareSum rest + M :=
                htailBound
            _ <=
              2 *
                  (cell.width * cell.width +
                    RationalCircle.FareyCell.widthSquareSum rest) + M := by
                grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
                  Rat.mul_assoc, Rat.mul_comm]

theorem fareyIntegralPrefixStageInterval_width_le_three_div_succ
    (x : Rat) (n : Nat) :
    (fareyIntegralPrefixStageInterval x n).width <=
      (3 : Rat) / (((n + 1 : Nat) : Rat)) := by
  let M : Rat := 1 / (((n + 1 : Nat) : Rat))
  have hMnonneg : 0 <= M := by
    dsimp [M]
    exact Rat.le_of_lt (one_div_nat_pos (Nat.succ_pos n))
  have hwidthList :
      RationalCircle.FareyCell.WidthListAtMost M
        (RationalCircle.fareyUnitStage n) := by
    dsimp [M]
    exact
      RationalCircle.FareyCell.widthListAtMost_one_div_succ_of_adjacent_denSum
        (RationalCircle.fareyUnitStage_adjacent n)
        (RationalCircle.fareyUnitStage_denSum_ge n)
  have hprefix :
      (fareyIntegralPrefixStageInterval x n).width <=
        2 *
          RationalCircle.FareyCell.widthSquareSum
            (RationalCircle.fareyUnitStage n) + M := by
    simpa [fareyIntegralPrefixStageInterval, M] using
      fareyIntegralPrefixInterval_width_le_two_squareSum_add_bound
        x
        (left := RationalCircle.FareyFraction.zero)
        (right := RationalCircle.FareyFraction.one)
        (cells := RationalCircle.fareyUnitStage n)
        (M := M)
        (RationalCircle.fareyUnitStage_connects n)
        (RationalCircle.fareyUnitStage_unit n)
        hwidthList
        hMnonneg
  have hsquare :=
    RationalCircle.fareyUnitStage_widthSquareSum_le_one_div_succ n
  calc
    (fareyIntegralPrefixStageInterval x n).width
        <=
      2 *
          RationalCircle.FareyCell.widthSquareSum
            (RationalCircle.fareyUnitStage n) + M := hprefix
    _ <= 2 * M + M := by
          exact rat_add_le_add
            (Rat.mul_le_mul_of_nonneg_left (by simpa [M] using hsquare)
              (by native_decide : (0 : Rat) <= 2))
            Rat.le_refl
    _ = (3 : Rat) / (((n + 1 : Nat) : Rat)) := by
          dsimp [M]
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]

theorem fareyIntegralPrefixStageInterval_widthsShrink
    (x : Rat) :
    RealRaw.WidthsShrinkToZero (fareyIntegralPrefixStageInterval x) := by
  intro eps
  refine ⟨3 * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (3 : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (3 : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        3 * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans
    (fareyIntegralPrefixStageInterval_width_le_three_div_succ x n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

def fareyIntegralPrefixRaw (x : Rat) : RealRaw where
  compute := fareyIntegralPrefixStageInterval x

theorem fareyIntegralPrefixRaw_valid (x : Rat) :
    (fareyIntegralPrefixRaw x).Valid := by
  change RealRaw.ValidCompute (fareyIntegralPrefixStageInterval x)
  constructor
  · exact fareyIntegralPrefixStageInterval_ordered x
  · constructor
    · exact fareyIntegralPrefixStageInterval_nested x
    · exact fareyIntegralPrefixStageInterval_widthsShrink x

theorem fareyIntegralLowerPrefix_one_eq_integralLowerSum
    (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    fareyIntegralLowerPrefix 1 cells =
      integralLowerSum (fareyCellIntervals cells) := by
  unfold fareyIntegralLowerPrefix
  rw [fareyLowerCellsUpTo_one_eq_intervals cells hcells]

theorem fareyIntegralUpperPrefix_one_eq_integralUpperSum
    (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    fareyIntegralUpperPrefix 1 cells =
      integralUpperSum (fareyCellIntervals cells) := by
  unfold fareyIntegralUpperPrefix
  rw [fareyUpperCellsUpTo_one_eq_intervals cells hcells]

theorem fareyIntegralPrefixInterval_one_eq_integralSumInterval
    (cells : List RationalCircle.FareyCell)
    (hcells : RationalCircle.FareyCell.UnitList cells) :
    fareyIntegralPrefixInterval 1 cells =
      integralSumInterval (fareyCellIntervals cells) := by
  simp [fareyIntegralPrefixInterval, integralSumInterval,
    fareyIntegralLowerPrefix_one_eq_integralLowerSum cells hcells,
    fareyIntegralUpperPrefix_one_eq_integralUpperSum cells hcells]

def fareyIntegralUnitStageInterval (n : Nat) : QInterval :=
  integralSumInterval
    (fareyCellIntervals (RationalCircle.fareyUnitStage n))

def fareyIntegralUnitRaw : RealRaw where
  compute := fareyIntegralUnitStageInterval

theorem fareyIntegralPrefixStageInterval_one_eq_unitStageInterval
    (n : Nat) :
    fareyIntegralPrefixStageInterval 1 n =
      fareyIntegralUnitStageInterval n := by
  unfold fareyIntegralPrefixStageInterval fareyIntegralUnitStageInterval
  exact fareyIntegralPrefixInterval_one_eq_integralSumInterval
    (RationalCircle.fareyUnitStage n)
    (RationalCircle.fareyUnitStage_unit n)

theorem fareyIntegralPrefixRaw_one_compute_eq_unitRaw (n : Nat) :
    (fareyIntegralPrefixRaw 1).compute n =
      fareyIntegralUnitRaw.compute n :=
  fareyIntegralPrefixStageInterval_one_eq_unitStageInterval n

theorem fareyIntegralUnitRaw_valid :
    fareyIntegralUnitRaw.Valid := by
  change RealRaw.ValidCompute fareyIntegralUnitStageInterval
  have hcompute :
      fareyIntegralUnitStageInterval =
        fareyIntegralPrefixStageInterval 1 := by
    funext n
    exact (fareyIntegralPrefixStageInterval_one_eq_unitStageInterval n).symm
  rw [hcompute]
  exact fareyIntegralPrefixRaw_valid 1

theorem fareyIntegralPrefixRaw_one_equiv_unitRaw :
    (fareyIntegralPrefixRaw 1).Equiv fareyIntegralUnitRaw := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (fareyIntegralPrefixRaw 1) fareyIntegralUnitRaw n n).2
  rw [fareyIntegralPrefixRaw_one_compute_eq_unitRaw n]
  have hordered :=
    RealRaw.interval_order_of_valid fareyIntegralUnitRaw
      fareyIntegralUnitRaw_valid n
  exact ⟨hordered, hordered⟩

private theorem fareyCell_right_value_pos_of_unit_adjacent
    {cell : RationalCircle.FareyCell}
    (hunit : cell.Unit) (hadj : cell.Adjacent) :
    0 < cell.right.value := by
  rcases hunit with ⟨hl0, _hlr, _hr1⟩
  have hwidthPos : 0 < cell.width := by
    rw [RationalCircle.FareyCell.width_eq_inv_den_mul_den_of_adjacent hadj]
    have hldpos : (0 : Rat) < (cell.left.den : Rat) :=
      (Rat.natCast_pos).2 cell.left.den_pos
    have hrdpos : (0 : Rat) < (cell.right.den : Rat) :=
      (Rat.natCast_pos).2 cell.right.den_pos
    have hdenpos :
        (0 : Rat) < (cell.left.den : Rat) * (cell.right.den : Rat) :=
      Rat.mul_pos hldpos hrdpos
    simpa [Rat.div_def] using (Rat.inv_pos).2 hdenpos
  unfold RationalCircle.FareyCell.width at hwidthPos
  grind [Rat.sub_eq_add_neg]

theorem fareyLowerCellsUpTo_zero_eq_nil_of_unit_adjacent
    (cells : List RationalCircle.FareyCell)
    (hunit : RationalCircle.FareyCell.UnitList cells)
    (hadj : RationalCircle.FareyCell.AdjacentList cells) :
    fareyLowerCellsUpTo 0 cells = [] := by
  induction cells with
  | nil =>
      simp [fareyLowerCellsUpTo]
  | cons cell rest ih =>
      rcases hunit with ⟨hcellUnit, hrestUnit⟩
      rcases hadj with ⟨hcellAdj, hrestAdj⟩
      have hrightPos :=
        fareyCell_right_value_pos_of_unit_adjacent hcellUnit hcellAdj
      have hrightNot : ¬ cell.right.value <= 0 := by
        grind
      have htail := ih hrestUnit hrestAdj
      simp [fareyLowerCellsUpTo, hrightNot, htail]

theorem fareyIntegralLowerPrefix_zero_unitStage (n : Nat) :
    fareyIntegralLowerPrefix 0 (RationalCircle.fareyUnitStage n) = 0 := by
  unfold fareyIntegralLowerPrefix
  rw [fareyLowerCellsUpTo_zero_eq_nil_of_unit_adjacent
    (RationalCircle.fareyUnitStage n)
    (RationalCircle.fareyUnitStage_unit n)
    (RationalCircle.fareyUnitStage_adjacent n)]
  simp [integralLowerSum]

theorem fareyIntegralPrefixRaw_zero_equiv_zero :
    (fareyIntegralPrefixRaw 0).Equiv (RealRaw.ofRat 0) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (fareyIntegralPrefixRaw 0) (RealRaw.ofRat 0) n n).2
  let Z := fareyIntegralPrefixStageInterval 0 n
  have hZlo : Z.lo = 0 := by
    dsimp [Z, fareyIntegralPrefixStageInterval,
      fareyIntegralPrefixInterval]
    exact fareyIntegralLowerPrefix_zero_unitStage n
  have hZnonneg : 0 <= Z.hi := by
    have hZordered := fareyIntegralPrefixStageInterval_ordered 0 n
    unfold QInterval.width at hZordered
    rw [hZlo] at hZordered
    grind [Rat.sub_eq_add_neg]
  change QInterval.Overlaps Z ((RealRaw.ofRat 0).compute n)
  simp [RealRaw.ofRat, QInterval.Overlaps, hZlo, hZnonneg]

/-- Verified raw integral over `[a,b]` from the global Farey prefix
construction.  The stage-level `fareyIntegralStageInterval` keeps exact
finite additivity; this raw wrapper uses interval subtraction so validity is
immediate from the two verified prefix raws. -/
def fareyIntegralBetweenRaw (a b : Rat) : RealRaw :=
  fareyIntegralPrefixRaw b - fareyIntegralPrefixRaw a

theorem fareyIntegralBetweenRaw_valid (a b : Rat) :
    (fareyIntegralBetweenRaw a b).Valid := by
  unfold fareyIntegralBetweenRaw
  exact RealRaw.sub_valid
    (fareyIntegralPrefixRaw_valid b)
    (fareyIntegralPrefixRaw_valid a)

theorem fareyIntegralBetweenRaw_compute_eq_subInterval
    (a b : Rat) (n : Nat) :
    (fareyIntegralBetweenRaw a b).compute n =
      QInterval.subInterval
        (fareyIntegralPrefixStageInterval b n)
        (fareyIntegralPrefixStageInterval a n) := by
  rfl

theorem fareyIntegralBetweenRaw_compute_contains_stageInterval
    (a b : Rat) (n : Nat) :
    ((fareyIntegralBetweenRaw a b).compute n).ContainsInterval
      (fareyIntegralStageInterval a b n) := by
  have haOrdered := fareyIntegralPrefixStageInterval_ordered a n
  unfold QInterval.ContainsInterval
  rw [fareyIntegralBetweenRaw_compute_eq_subInterval]
  unfold fareyIntegralPrefixStageInterval fareyIntegralPrefixInterval at haOrdered ⊢
  unfold QInterval.width at haOrdered
  unfold QInterval.subInterval fareyIntegralStageInterval
    fareyIntegralBetweenInterval
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem fareyIntegralBetweenRaw_width_le_six_div_succ
    (a b : Rat) (n : Nat) :
    ((fareyIntegralBetweenRaw a b).compute n).width <=
      (6 : Rat) / (((n + 1 : Nat) : Rat)) := by
  have ha :=
    fareyIntegralPrefixStageInterval_width_le_three_div_succ a n
  have hb :=
    fareyIntegralPrefixStageInterval_width_le_three_div_succ b n
  rw [fareyIntegralBetweenRaw_compute_eq_subInterval]
  unfold QInterval.subInterval QInterval.width
  calc
    (fareyIntegralPrefixStageInterval b n).hi -
          (fareyIntegralPrefixStageInterval a n).lo -
        ((fareyIntegralPrefixStageInterval b n).lo -
          (fareyIntegralPrefixStageInterval a n).hi)
        =
      (fareyIntegralPrefixStageInterval b n).width +
        (fareyIntegralPrefixStageInterval a n).width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    _ <=
      (3 : Rat) / (((n + 1 : Nat) : Rat)) +
        (3 : Rat) / (((n + 1 : Nat) : Rat)) :=
        rat_add_le_add hb ha
    _ = (6 : Rat) / (((n + 1 : Nat) : Rat)) := by
        rw [Rat.div_def]
        grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]

private theorem qinterval_sub_add_sub_overlaps_sub
    {A B C : QInterval}
    (hA : 0 <= A.width) (hB : 0 <= B.width) (hC : 0 <= C.width) :
    QInterval.Overlaps
      (QInterval.addInterval (QInterval.subInterval B A)
        (QInterval.subInterval C B))
      (QInterval.subInterval C A) := by
  unfold QInterval.width at hA hB hC
  unfold QInterval.Overlaps QInterval.addInterval QInterval.subInterval
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem fareyIntegralBetweenRaw_additive
    (a b c : Rat) :
    (fareyIntegralBetweenRaw a b + fareyIntegralBetweenRaw b c).Equiv
      (fareyIntegralBetweenRaw a c) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (fareyIntegralBetweenRaw a b + fareyIntegralBetweenRaw b c)
    (fareyIntegralBetweenRaw a c) n n).2
  have haOrdered := fareyIntegralPrefixStageInterval_ordered a n
  have hbOrdered := fareyIntegralPrefixStageInterval_ordered b n
  have hcOrdered := fareyIntegralPrefixStageInterval_ordered c n
  have hover :=
    qinterval_sub_add_sub_overlaps_sub
      (A := fareyIntegralPrefixStageInterval a n)
      (B := fareyIntegralPrefixStageInterval b n)
      (C := fareyIntegralPrefixStageInterval c n)
      haOrdered hbOrdered hcOrdered
  simpa [fareyIntegralBetweenRaw_compute_eq_subInterval,
    RealRaw.addCompute, QInterval.addInterval] using hover

theorem fareyIntegralBetweenRaw_self_equiv_zero
    (a : Rat) :
    (fareyIntegralBetweenRaw a a).Equiv (RealRaw.ofRat 0) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (fareyIntegralBetweenRaw a a) (RealRaw.ofRat 0) n n).2
  have hordered := fareyIntegralPrefixStageInterval_ordered a n
  rw [fareyIntegralBetweenRaw_compute_eq_subInterval]
  unfold fareyIntegralPrefixStageInterval fareyIntegralPrefixInterval at hordered ⊢
  unfold QInterval.width at hordered
  unfold QInterval.subInterval QInterval.Overlaps
  simp [RealRaw.ofRat]
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem fareyIntegralBetweenRaw_zero_left_equiv_prefix
    (x : Rat) :
    (fareyIntegralBetweenRaw 0 x).Equiv (fareyIntegralPrefixRaw x) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (fareyIntegralBetweenRaw 0 x) (fareyIntegralPrefixRaw x) n n).2
  let X := fareyIntegralPrefixStageInterval x n
  let Z := fareyIntegralPrefixStageInterval 0 n
  have hZlo : Z.lo = 0 := by
    dsimp [Z, fareyIntegralPrefixStageInterval,
      fareyIntegralPrefixInterval]
    exact fareyIntegralLowerPrefix_zero_unitStage n
  have hZnonneg : 0 <= Z.hi := by
    have hZordered := fareyIntegralPrefixStageInterval_ordered 0 n
    unfold QInterval.width at hZordered
    rw [hZlo] at hZordered
    grind [Rat.sub_eq_add_neg]
  have hXordered := fareyIntegralPrefixStageInterval_ordered x n
  rw [fareyIntegralBetweenRaw_compute_eq_subInterval]
  change QInterval.Overlaps (QInterval.subInterval X Z) X
  unfold QInterval.width at hXordered
  unfold QInterval.subInterval QInterval.Overlaps
  rw [hZlo]
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem fareyIntegralBetweenRaw_reverse_compute
    (a b : Rat) (n : Nat) :
    (fareyIntegralBetweenRaw a b).compute n =
      (-(fareyIntegralBetweenRaw b a)).compute n := by
  change (fareyIntegralBetweenRaw a b).compute n =
    RealRaw.negCompute (fareyIntegralBetweenRaw b a) n
  rw [fareyIntegralBetweenRaw_compute_eq_subInterval]
  unfold RealRaw.negCompute
  rw [fareyIntegralBetweenRaw_compute_eq_subInterval]
  unfold QInterval.subInterval
  have hlo :
      (fareyIntegralPrefixStageInterval b n).lo -
          (fareyIntegralPrefixStageInterval a n).hi =
        -((fareyIntegralPrefixStageInterval a n).hi -
          (fareyIntegralPrefixStageInterval b n).lo) := by
    grind [Rat.sub_eq_add_neg]
  have hhi :
      (fareyIntegralPrefixStageInterval b n).hi -
          (fareyIntegralPrefixStageInterval a n).lo =
        -((fareyIntegralPrefixStageInterval a n).lo -
          (fareyIntegralPrefixStageInterval b n).hi) := by
    grind [Rat.sub_eq_add_neg]
  rw [hlo, hhi]

theorem fareyIntegralBetweenRaw_reverse_equiv_neg
    (a b : Rat) :
    (fareyIntegralBetweenRaw a b).Equiv (-(fareyIntegralBetweenRaw b a)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (fareyIntegralBetweenRaw a b)
    (-(fareyIntegralBetweenRaw b a)) n n).2
  rw [fareyIntegralBetweenRaw_reverse_compute]
  have hvalid : (-(fareyIntegralBetweenRaw b a)).Valid :=
    RealRaw.neg_valid (fareyIntegralBetweenRaw_valid b a)
  have hordered := hvalid.1 n
  unfold QInterval.width at hordered
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem fareyIntegralBetweenRaw_add_reverse_equiv_zero
    (a b : Rat) :
    (fareyIntegralBetweenRaw a b + fareyIntegralBetweenRaw b a).Equiv
      (RealRaw.ofRat 0) := by
  have hleftValid :
      (fareyIntegralBetweenRaw a b + fareyIntegralBetweenRaw b a).Valid :=
    RealRaw.add_valid
      (fareyIntegralBetweenRaw_valid a b)
      (fareyIntegralBetweenRaw_valid b a)
  have hselfValid : (fareyIntegralBetweenRaw a a).Valid :=
    fareyIntegralBetweenRaw_valid a a
  have hzeroValid : (RealRaw.ofRat 0).Valid :=
    RealRaw.ofRat_valid 0
  exact RealRaw.equiv_trans hleftValid hselfValid hzeroValid
    (fareyIntegralBetweenRaw_additive a b a)
    (fareyIntegralBetweenRaw_self_equiv_zero a)

theorem fareyIntegralBetweenRaw_zero_right_equiv_neg_prefix
    (x : Rat) :
    (fareyIntegralBetweenRaw x 0).Equiv (-(fareyIntegralPrefixRaw x)) := by
  have hx0Valid : (fareyIntegralBetweenRaw x 0).Valid :=
    fareyIntegralBetweenRaw_valid x 0
  have hnegBetweenValid : (-(fareyIntegralBetweenRaw 0 x)).Valid :=
    RealRaw.neg_valid (fareyIntegralBetweenRaw_valid 0 x)
  have hnegPrefixValid : (-(fareyIntegralPrefixRaw x)).Valid :=
    RealRaw.neg_valid (fareyIntegralPrefixRaw_valid x)
  exact RealRaw.equiv_trans hx0Valid hnegBetweenValid hnegPrefixValid
    (fareyIntegralBetweenRaw_reverse_equiv_neg x 0)
    (RealRaw.neg_equiv (fareyIntegralBetweenRaw_zero_left_equiv_prefix x))

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

private theorem refineAux_intervals_unit
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : UnitIntervals intervals) :
    UnitIntervals
      (AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, UnitIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hr1, hrest⟩
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
      have hq1 : q <= 1 := Rat.le_trans hqr hr1
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      simp [AreaLoopState.refineAux, UnitIntervals, q,
        hp0, hpq, hq0, hqr, hq1, hr1, htail]

private theorem refineAux_intervals_covers
    (lo hi a b : Rat) (intervals : List (Rat × Rat))
    (hcover : CoversInterval a b intervals) :
    CoversInterval a b
      (AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi a with
  | nil =>
      simpa [AreaLoopState.refineAux, CoversInterval] using hcover
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) r hrest
      simp [AreaLoopState.refineAux, CoversInterval]
      exact ⟨hp, hpq, hqr, htail⟩

private theorem midpoint_left_sub (p r : Rat) :
    (p + r) / 2 - p = (r - p) / 2 := by
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

private theorem midpoint_right_sub (p r : Rat) :
    r - (p + r) / 2 = (r - p) / 2 := by
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

private theorem square_midpoint_split (p r : Rat) :
    let q : Rat := (p + r) / 2
    (q - p) * (q - p) + (r - q) * (r - q) =
      ((r - p) * (r - p)) / 2 := by
  intro q
  dsimp [q]
  rw [midpoint_left_sub, midpoint_right_sub]
  repeat rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

private theorem refineAux_squareSum
    (lo hi : Rat) (intervals : List (Rat × Rat)) :
    intervalSquareSum
        (AreaLoopState.refineAux lo hi intervals).intervals =
      intervalSquareSum intervals / 2 := by
  induction intervals generalizing lo hi with
  | nil =>
      change (0 : Rat) = 0 / 2
      native_decide
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      let q : Rat := (p + r) / 2
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r)
      have hsplit := square_midpoint_split p r
      simp [AreaLoopState.refineAux, intervalSquareSum]
      calc
        (q - p) * (q - p) +
              ((r - q) * (r - q) +
                intervalSquareSum
                  (AreaLoopState.refineAux
                    (lo + arctanAreaIncrement p q r)
                    (hi - arctanAreaDecrement p q r) rest).intervals)
            = ((r - p) * (r - p)) / 2 +
                intervalSquareSum rest / 2 := by
              rw [htail]
              dsimp [q] at hsplit
              rw [← hsplit]
              grind [Rat.add_assoc, Rat.add_comm]
        _ = (((r - p) * (r - p)) +
              intervalSquareSum rest) / 2 := by
              rw [Rat.div_def, Rat.div_def, Rat.div_def]
              grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc,
                Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem refineAux_endpoint_refines
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    lo <= (AreaLoopState.refineAux lo hi intervals).lo /\
      (AreaLoopState.refineAux lo hi intervals).hi <= hi := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have hinc : 0 <= arctanAreaIncrement p q r :=
        arctanAreaIncrement_nonneg hpq hqr
      have hdec : 0 <= arctanAreaDecrement p q r :=
        arctanAreaDecrement_nonneg hp0 hpq hqr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      simp [AreaLoopState.refineAux]
      exact ⟨Rat.le_trans (by grind) htail.1,
        Rat.le_trans htail.2 (by grind)⟩

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

private theorem refineAux_integralLowerSum_mono
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralLowerSum intervals <=
      integralLowerSum
        (AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, integralLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      have hhead := integralLowerStep_refine hp0 hpq hqr
      simp [AreaLoopState.refineAux, integralLowerSum]
      calc
        integralLowerStep p r + integralLowerSum rest
            <= (integralLowerStep p q + integralLowerStep q r) +
                integralLowerSum rest :=
              rat_add_le_add hhead (Rat.le_refl)
        _ <= (integralLowerStep p q + integralLowerStep q r) +
              integralLowerSum
                (AreaLoopState.refineAux
                  (lo + arctanAreaIncrement p q r)
                  (hi - arctanAreaDecrement p q r) rest).intervals :=
              rat_add_le_add (Rat.le_refl) htail
        _ = integralLowerStep p q +
              (integralLowerStep q r +
                integralLowerSum
                  (AreaLoopState.refineAux
                    (lo + arctanAreaIncrement p q r)
                    (hi - arctanAreaDecrement p q r) rest).intervals) := by
              grind [Rat.add_assoc, Rat.add_comm]

private theorem refineAux_integralUpperSum_anti
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralUpperSum
        (AreaLoopState.refineAux lo hi intervals).intervals <=
      integralUpperSum intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      have hhead := integralUpperStep_refine hp0 hpq hqr
      simp [AreaLoopState.refineAux, integralUpperSum]
      calc
        integralUpperStep p q +
              (integralUpperStep q r +
                integralUpperSum
                  (AreaLoopState.refineAux
                    (lo + arctanAreaIncrement p q r)
                    (hi - arctanAreaDecrement p q r) rest).intervals)
            = (integralUpperStep p q + integralUpperStep q r) +
                integralUpperSum
                  (AreaLoopState.refineAux
                    (lo + arctanAreaIncrement p q r)
                    (hi - arctanAreaDecrement p q r) rest).intervals := by
              grind [Rat.add_assoc, Rat.add_comm]
        _ <= (integralUpperStep p q + integralUpperStep q r) +
              integralUpperSum rest :=
              rat_add_le_add (Rat.le_refl) htail
        _ <= integralUpperStep p r + integralUpperSum rest :=
              rat_add_le_add hhead (Rat.le_refl)

def refineAreaLoopState (state : AreaLoopState) : AreaLoopState :=
  AreaLoopState.refineAux state.lo state.hi state.intervals

theorem refineAreaLoopState_intervals_nonnegative
    (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals) :
    NonnegativeIntervals (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_intervals_nonnegative lo hi intervals hwf

theorem refineAreaLoopState_intervals_unit
    (state : AreaLoopState)
    (hwf : UnitIntervals state.intervals) :
    UnitIntervals (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_intervals_unit lo hi intervals hwf

theorem refineAreaLoopState_intervals_covers
    (state : AreaLoopState) {a b : Rat}
    (hcover : CoversInterval a b state.intervals) :
    CoversInterval a b (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_intervals_covers lo hi a b intervals hcover

theorem refineAreaLoopState_squareSum
    (state : AreaLoopState) :
    intervalSquareSum (refineAreaLoopState state).intervals =
      intervalSquareSum state.intervals / 2 := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_squareSum lo hi intervals

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

theorem refineAreaLoopState_integralSumInterval_refines
    (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals) :
    (integralSumInterval state.intervals).ContainsInterval
      (integralSumInterval (refineAreaLoopState state).intervals) := by
  cases state with
  | mk lo hi intervals =>
      unfold QInterval.ContainsInterval integralSumInterval refineAreaLoopState
      exact ⟨refineAux_integralLowerSum_mono lo hi intervals hwf,
        refineAux_integralUpperSum_anti lo hi intervals hwf⟩

theorem refineAreaLoopState_endpoint_refines
    (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals) :
    state.lo <= (refineAreaLoopState state).lo /\
      (refineAreaLoopState state).hi <= state.hi := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_endpoint_refines lo hi intervals hwf

def iterateAreaLoopState : Nat -> AreaLoopState -> AreaLoopState
  | 0, state => state
  | n + 1, state => iterateAreaLoopState n (refineAreaLoopState state)

theorem iterateAreaLoopState_succ_refine
    (n : Nat) (state : AreaLoopState) :
    iterateAreaLoopState (n + 1) state =
      refineAreaLoopState (iterateAreaLoopState n state) := by
  induction n generalizing state with
  | zero =>
      rfl
  | succ n ih =>
      simp [iterateAreaLoopState]
      exact ih (refineAreaLoopState state)

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

theorem iterateAreaLoopState_intervals_unit
    (n : Nat) (state : AreaLoopState)
    (hwf : UnitIntervals state.intervals) :
    UnitIntervals (iterateAreaLoopState n state).intervals := by
  induction n generalizing state with
  | zero =>
      simpa [iterateAreaLoopState] using hwf
  | succ n ih =>
      simpa [iterateAreaLoopState] using
        ih (refineAreaLoopState state)
          (refineAreaLoopState_intervals_unit state hwf)

theorem iterateAreaLoopState_intervals_covers
    (n : Nat) (state : AreaLoopState) {a b : Rat}
    (hcover : CoversInterval a b state.intervals) :
    CoversInterval a b (iterateAreaLoopState n state).intervals := by
  induction n generalizing state with
  | zero =>
      simpa [iterateAreaLoopState] using hcover
  | succ n ih =>
      simpa [iterateAreaLoopState] using
        ih (refineAreaLoopState state)
          (refineAreaLoopState_intervals_covers state hcover)

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

theorem arctanAreaLoopState_succ (x : Rat) (n : Nat) :
    arctanAreaLoopState x (n + 1) =
      refineAreaLoopState (arctanAreaLoopState x n) := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_succ_refine n (arctanAreaLoopInitial x)

theorem arctanAreaLoopInitial_intervals_nonnegative
    {x : Rat} (hx : 0 <= x) :
    NonnegativeIntervals (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, NonnegativeIntervals, hx]

theorem arctanAreaLoopInitial_intervals_unit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    UnitIntervals (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, UnitIntervals, hx0, hx1]

theorem arctanAreaLoopInitial_intervals_covers
    {x : Rat} (hx : 0 <= x) :
    CoversInterval 0 x (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, CoversInterval, hx]

theorem arctanAreaLoopState_intervals_nonnegative
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    NonnegativeIntervals (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_intervals_nonnegative n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_intervals_nonnegative hx)

theorem arctanAreaLoopState_intervals_unit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    UnitIntervals (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_intervals_unit n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_intervals_unit hx0 hx1)

theorem arctanAreaLoopState_intervals_covers
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    CoversInterval 0 x (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_intervals_covers n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_intervals_covers hx)

private theorem div_two_pow_succ (a : Rat) (n : Nat) :
    (a / (((2 ^ n : Nat) : Rat))) / 2 =
      a / (((2 ^ (n + 1) : Nat) : Rat)) := by
  let A : Rat := ((2 ^ n : Nat) : Rat)
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have h2 : (2 : Rat) ≠ 0 := by native_decide
  have hA2 : A * 2 ≠ 0 := by
    intro hz
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hpow :
      (((2 ^ (n + 1) : Nat) : Rat)) = A * 2 := by
    dsimp [A]
    exact_mod_cast (by
      simpa using (Nat.pow_succ 2 n))
  rw [hpow]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem arctanAreaLoopInitial_squareSum (x : Rat) :
    intervalSquareSum (arctanAreaLoopInitial x).intervals = x * x := by
  simp [arctanAreaLoopInitial, intervalSquareSum]
  grind [Rat.sub_eq_add_neg]

theorem arctanAreaLoopState_squareSum (x : Rat) (n : Nat) :
    intervalSquareSum (arctanAreaLoopState x n).intervals =
      (x * x) / (((2 ^ n : Nat) : Rat)) := by
  induction n with
  | zero =>
      calc
        intervalSquareSum (arctanAreaLoopState x 0).intervals =
            x * x := by
          simpa [arctanAreaLoopState, iterateAreaLoopState]
            using arctanAreaLoopInitial_squareSum x
        _ = (x * x) / (((2 ^ 0 : Nat) : Rat)) := by
          rw [show (((2 ^ 0 : Nat) : Rat)) = 1 by native_decide]
          rw [Rat.div_def]
          grind
  | succ n ih =>
      rw [arctanAreaLoopState_succ, refineAreaLoopState_squareSum, ih]
      exact div_two_pow_succ (x * x) n

theorem arctanAreaLoopState_one_squareSum (n : Nat) :
    intervalSquareSum (arctanAreaLoopState 1 n).intervals =
      1 / (((2 ^ n : Nat) : Rat)) := by
  simpa using arctanAreaLoopState_squareSum (1 : Rat) n

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

theorem arctanAreaLoop_integralSum_ordered
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    0 <= (integralSumInterval (arctanAreaLoopState x n).intervals).width :=
  integralSumInterval_ordered
    (arctanAreaLoopState x n).intervals
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem arctanAreaLoop_integralSum_step_refines
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (integralSumInterval (arctanAreaLoopState x n).intervals).ContainsInterval
      (integralSumInterval (arctanAreaLoopState x (n + 1)).intervals) := by
  rw [arctanAreaLoopState_succ]
  exact refineAreaLoopState_integralSumInterval_refines
    (arctanAreaLoopState x n)
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem arctanAreaLoop_integralSum_refines_add
    {x : Rat} (hx : 0 <= x) (n k : Nat) :
    (integralSumInterval (arctanAreaLoopState x n).intervals).ContainsInterval
      (integralSumInterval (arctanAreaLoopState x (n + k)).intervals) := by
  induction k with
  | zero =>
      simp
      exact containsInterval_refl
        (integralSumInterval (arctanAreaLoopState x n).intervals)
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by omega]
      exact containsInterval_trans ih
        (arctanAreaLoop_integralSum_step_refines hx (n + k))

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

theorem fareyIntegralPrefixStageInterval_overlaps_positiveLoop
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n m : Nat) :
    QInterval.Overlaps (fareyIntegralPrefixStageInterval x n)
      (positiveLoopComputeAtStage x m) := by
  obtain ⟨lowerEnd, hlowerEnd, hlowerCover⟩ :=
    fareyLowerCellsUpTo_unitStage_covers_prefix hx0 n
  obtain ⟨upperEnd, hupperEnd, hupperCover⟩ :=
    fareyUpperCellsUpTo_unitStage_covers_prefix hx0 hx1 n
  rw [positiveLoopComputeAtStage_eq_geometricSumInterval hx0 m]
  change QInterval.Overlaps
    { lo :=
        integralLowerSum
          (fareyLowerCellsUpTo x (RationalCircle.fareyUnitStage n)),
      hi :=
        integralUpperSum
          (fareyUpperCellsUpTo x (RationalCircle.fareyUnitStage n)) }
    (geometricSumInterval (arctanAreaLoopState x m).intervals)
  exact integralBracketInterval_overlaps_geometricSumInterval_of_covers
    (a := 0) (lowerEnd := lowerEnd) (x := x) (upperEnd := upperEnd)
    (by native_decide)
    hlowerEnd hupperEnd
    (fareyLowerCellsUpTo x (RationalCircle.fareyUnitStage n))
    (fareyUpperCellsUpTo x (RationalCircle.fareyUnitStage n))
    (arctanAreaLoopState x m).intervals
    hlowerCover hupperCover
    (arctanAreaLoopState_intervals_covers hx0 m)

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

theorem positiveLoopComputeAtStage_ordered
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    0 <= (positiveLoopComputeAtStage x n).width := by
  rw [positiveLoopComputeAtStage_eq_geometricSumInterval hx n]
  exact geometricSumInterval_ordered
    (arctanAreaLoopState x n).intervals
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem positiveLoopComputeAtStage_step_refines
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (positiveLoopComputeAtStage x n).lo <=
      (positiveLoopComputeAtStage x (n + 1)).lo /\
    (positiveLoopComputeAtStage x (n + 1)).hi <=
      (positiveLoopComputeAtStage x n).hi := by
  unfold positiveLoopComputeAtStage
  rw [arctanAreaLoopState_succ]
  exact refineAreaLoopState_endpoint_refines
    (arctanAreaLoopState x n)
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem positiveLoopComputeAtStage_nested
    {x : Rat} (hx : 0 <= x) :
    forall n m, n <= m ->
      (positiveLoopComputeAtStage x n).lo <=
        (positiveLoopComputeAtStage x m).lo /\
      (positiveLoopComputeAtStage x m).lo <=
        (positiveLoopComputeAtStage x m).hi /\
      (positiveLoopComputeAtStage x m).hi <=
        (positiveLoopComputeAtStage x n).hi := by
  intro n m hnm
  induction hnm with
  | refl =>
      have hordered := positiveLoopComputeAtStage_ordered hx n
      constructor
      · exact Rat.le_refl
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_refl
  | step hnk ih =>
      rename_i k
      have hstep := positiveLoopComputeAtStage_step_refines hx k
      have hordered := positiveLoopComputeAtStage_ordered hx (k + 1)
      constructor
      · exact Rat.le_trans ih.1 hstep.1
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_trans hstep.2 ih.2.2

/-- Rectangle-sum arctangent computation at a rational endpoint `x`, using the
same midpoint partition schedule as `arctanGeom x`. -/
def arctanIntegralRectangleCompute (x : Rat) (n : Nat) : QInterval :=
  integralSumInterval (arctanAreaLoopState x n).intervals

def arctanIntegralRectangleRaw (x : Rat) : RealRaw where
  compute := arctanIntegralRectangleCompute x

theorem arctanIntegralRectangleCompute_ordered
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    0 <= (arctanIntegralRectangleCompute x n).width := by
  unfold arctanIntegralRectangleCompute
  exact arctanAreaLoop_integralSum_ordered hx n

private theorem arctanIntegralRectangleCompute_step_refines
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (arctanIntegralRectangleCompute x n).ContainsInterval
      (arctanIntegralRectangleCompute x (n + 1)) := by
  unfold arctanIntegralRectangleCompute
  exact arctanAreaLoop_integralSum_step_refines hx n

theorem arctanIntegralRectangleCompute_nested
    {x : Rat} (hx : 0 <= x) :
    forall n m, n <= m ->
      (arctanIntegralRectangleCompute x n).lo <=
        (arctanIntegralRectangleCompute x m).lo /\
      (arctanIntegralRectangleCompute x m).lo <=
        (arctanIntegralRectangleCompute x m).hi /\
      (arctanIntegralRectangleCompute x m).hi <=
        (arctanIntegralRectangleCompute x n).hi := by
  intro n m hnm
  induction hnm with
  | refl =>
      have hordered := arctanIntegralRectangleCompute_ordered hx n
      constructor
      · exact Rat.le_refl
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_refl
  | step hnk ih =>
      rename_i k
      have hstep := arctanIntegralRectangleCompute_step_refines hx k
      unfold QInterval.ContainsInterval at hstep
      have hordered := arctanIntegralRectangleCompute_ordered hx (k + 1)
      constructor
      · exact Rat.le_trans ih.1 hstep.1
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_trans hstep.2 ih.2.2

/-- The rectangle-sum arctangent computation at `1`, using the same midpoint
partition schedule as `arctanGeom`. -/
def arctanIntegralRectangleComputeAtOne (n : Nat) : QInterval :=
  integralSumInterval (arctanAreaLoopState 1 n).intervals

def arctanIntegralRectangleRawAtOne : RealRaw where
  compute := arctanIntegralRectangleComputeAtOne

theorem arctanIntegralRectangleComputeAtOne_ordered (n : Nat) :
    0 <= (arctanIntegralRectangleComputeAtOne n).width := by
  unfold arctanIntegralRectangleComputeAtOne
  exact arctanAreaLoop_integralSum_ordered
    (x := 1) (by native_decide) n

private theorem arctanIntegralRectangleComputeAtOne_step_refines (n : Nat) :
    (arctanIntegralRectangleComputeAtOne n).ContainsInterval
      (arctanIntegralRectangleComputeAtOne (n + 1)) := by
  unfold arctanIntegralRectangleComputeAtOne
  exact arctanAreaLoop_integralSum_step_refines
    (x := 1) (by native_decide) n

theorem arctanIntegralRectangleComputeAtOne_nested :
    forall n m, n <= m ->
      (arctanIntegralRectangleComputeAtOne n).lo <=
        (arctanIntegralRectangleComputeAtOne m).lo /\
      (arctanIntegralRectangleComputeAtOne m).lo <=
        (arctanIntegralRectangleComputeAtOne m).hi /\
      (arctanIntegralRectangleComputeAtOne m).hi <=
        (arctanIntegralRectangleComputeAtOne n).hi := by
  intro n m hnm
  induction hnm with
  | refl =>
      have hordered := arctanIntegralRectangleComputeAtOne_ordered n
      constructor
      · exact Rat.le_refl
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_refl
  | step hnk ih =>
      rename_i k
      have hstep := arctanIntegralRectangleComputeAtOne_step_refines k
      unfold QInterval.ContainsInterval at hstep
      have hordered := arctanIntegralRectangleComputeAtOne_ordered (k + 1)
      constructor
      · exact Rat.le_trans ih.1 hstep.1
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_trans hstep.2 ih.2.2

private theorem succ_le_two_pow_succ (n : Nat) :
    n + 1 <= 2 ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 2 * (n + 1) := by omega
        _ <= 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1 + 1) := by
          rw [Nat.pow_succ]
          omega

private theorem four_mul_one_div_eq_div (N : Nat) :
    4 * (1 / (N : Rat)) = 4 / (N : Rat) := by
  rw [Rat.div_def]
  grind [Rat.mul_assoc]

private theorem two_mul_one_div_two_pow_eq_four_mul_one_div_two_pow_succ
    (n : Nat) :
    2 * (1 / (((2 ^ n : Nat) : Rat))) =
      4 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) := by
  let A : Rat := ((2 ^ n : Nat) : Rat)
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have h2 : (2 : Rat) ≠ 0 := by native_decide
  have hA2 : A * 2 ≠ 0 := by
    intro hz
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hpow :
      (((2 ^ (n + 1) : Nat) : Rat)) = A * 2 := by
    dsimp [A]
    exact_mod_cast (by
      simpa using (Nat.pow_succ 2 n))
  rw [hpow]
  repeat rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem square_le_one_of_unit {x : Rat}
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    x * x <= 1 := by
  have hxx : x * x <= x * 1 :=
    Rat.mul_le_mul_of_nonneg_left hx1 hx0
  calc
    x * x <= x * 1 := hxx
    _ = x := by grind
    _ <= 1 := hx1

private theorem square_div_two_pow_le_one_div_two_pow
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (x * x) / (((2 ^ n : Nat) : Rat)) <=
      1 / (((2 ^ n : Nat) : Rat)) := by
  let D : Rat := ((2 ^ n : Nat) : Rat)
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hinv_nonneg : 0 <= D⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hDpos)
  have hsquare : x * x <= 1 := square_le_one_of_unit hx0 hx1
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right hsquare hinv_nonneg

theorem arctanIntegralRectangleCompute_width_le_four_div_succ
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (arctanIntegralRectangleCompute x n).width <=
      (4 : Rat) / (((n + 1 : Nat) : Rat)) := by
  have hmesh :
      (arctanIntegralRectangleCompute x n).width <=
        2 * (1 / (((2 ^ n : Nat) : Rat))) := by
    unfold arctanIntegralRectangleCompute
    calc
      (integralSumInterval (arctanAreaLoopState x n).intervals).width
          <= 2 * intervalSquareSum
              (arctanAreaLoopState x n).intervals :=
            integralSumInterval_width_le_two_squareSum
              (arctanAreaLoopState x n).intervals
              (arctanAreaLoopState_intervals_unit hx0 hx1 n)
      _ = 2 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
            rw [arctanAreaLoopState_squareSum x n]
      _ <= 2 * (1 / (((2 ^ n : Nat) : Rat))) := by
            exact Rat.mul_le_mul_of_nonneg_left
              (square_div_two_pow_le_one_div_two_pow hx0 hx1 n)
              (by native_decide : (0 : Rat) <= 2)
  calc
    (arctanIntegralRectangleCompute x n).width
        <= 2 * (1 / (((2 ^ n : Nat) : Rat))) := hmesh
    _ = 4 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) :=
          two_mul_one_div_two_pow_eq_four_mul_one_div_two_pow_succ n
    _ <= 4 * (1 / (((n + 1 : Nat) : Rat))) := by
          have hone :
              1 / (((2 ^ (n + 1) : Nat) : Rat)) <=
                1 / (((n + 1 : Nat) : Rat)) :=
            FTC.one_div_nat_antitone (Nat.succ_pos n)
              (Nat.pow_pos (by omega : 0 < 2))
              (succ_le_two_pow_succ n)
          exact Rat.mul_le_mul_of_nonneg_left hone
            (by native_decide : (0 : Rat) <= 4)
    _ = 4 / (((n + 1 : Nat) : Rat)) := by
          exact four_mul_one_div_eq_div (n + 1)

theorem arctanIntegralRectangleCompute_widthsShrink
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    RealRaw.WidthsShrinkToZero (arctanIntegralRectangleCompute x) := by
  intro eps
  refine ⟨4 * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (4 : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (4 : Rat)
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
        4 * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans
    (arctanIntegralRectangleCompute_width_le_four_div_succ hx0 hx1 n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

private theorem width_le_of_contains
    {outer inner : QInterval} (h : outer.ContainsInterval inner) :
    inner.width <= outer.width := by
  unfold QInterval.ContainsInterval at h
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem positiveLoopComputeAtStage_width_le_rectangle
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (positiveLoopComputeAtStage x n).width <=
      (arctanIntegralRectangleCompute x n).width := by
  unfold arctanIntegralRectangleCompute
  exact width_le_of_contains
    (arctanAreaLoop_integralSum_contains_positiveLoop hx n)

theorem positiveLoopComputeAtStage_width_le_four_div_succ
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (positiveLoopComputeAtStage x n).width <=
      (4 : Rat) / (((n + 1 : Nat) : Rat)) :=
  Rat.le_trans (positiveLoopComputeAtStage_width_le_rectangle hx0 n)
    (arctanIntegralRectangleCompute_width_le_four_div_succ hx0 hx1 n)

theorem positiveLoopComputeAtStage_widthsShrink
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    RealRaw.WidthsShrinkToZero (positiveLoopComputeAtStage x) := by
  intro eps
  obtain ⟨N, hN⟩ :=
    arctanIntegralRectangleCompute_widthsShrink hx0 hx1 eps
  refine ⟨N, ?_⟩
  intro n hn
  exact Rat.le_trans
    (positiveLoopComputeAtStage_width_le_rectangle hx0 n)
    (hN n hn)

theorem arctanIntegralRectangleRaw_valid
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleRaw x).Valid := by
  change RealRaw.ValidCompute (arctanIntegralRectangleCompute x)
  constructor
  · exact arctanIntegralRectangleCompute_ordered hx0
  · constructor
    · exact arctanIntegralRectangleCompute_nested hx0
    · exact arctanIntegralRectangleCompute_widthsShrink hx0 hx1

theorem arctanIntegralRectangleComputeAtOne_width_le_four_div_succ
    (n : Nat) :
    (arctanIntegralRectangleComputeAtOne n).width <=
      (4 : Rat) / (((n + 1 : Nat) : Rat)) := by
  have hmesh :
      (arctanIntegralRectangleComputeAtOne n).width <=
        2 * (1 / (((2 ^ n : Nat) : Rat))) := by
    unfold arctanIntegralRectangleComputeAtOne
    calc
      (integralSumInterval (arctanAreaLoopState 1 n).intervals).width
          <= 2 * intervalSquareSum
              (arctanAreaLoopState 1 n).intervals :=
            integralSumInterval_width_le_two_squareSum
              (arctanAreaLoopState 1 n).intervals
              (arctanAreaLoopState_intervals_unit
                (x := 1) (by native_decide) (by native_decide) n)
      _ = 2 * (1 / (((2 ^ n : Nat) : Rat))) := by
            rw [arctanAreaLoopState_one_squareSum n]
  calc
    (arctanIntegralRectangleComputeAtOne n).width
        <= 2 * (1 / (((2 ^ n : Nat) : Rat))) := hmesh
    _ = 4 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) :=
          two_mul_one_div_two_pow_eq_four_mul_one_div_two_pow_succ n
    _ <= 4 * (1 / (((n + 1 : Nat) : Rat))) := by
          have hone :
              1 / (((2 ^ (n + 1) : Nat) : Rat)) <=
                1 / (((n + 1 : Nat) : Rat)) :=
            FTC.one_div_nat_antitone (Nat.succ_pos n)
              (Nat.pow_pos (by omega : 0 < 2))
              (succ_le_two_pow_succ n)
          exact Rat.mul_le_mul_of_nonneg_left hone
            (by native_decide : (0 : Rat) <= 4)
    _ = 4 / (((n + 1 : Nat) : Rat)) := by
          exact four_mul_one_div_eq_div (n + 1)

theorem arctanIntegralRectangleComputeAtOne_widthsShrink :
    RealRaw.WidthsShrinkToZero arctanIntegralRectangleComputeAtOne := by
  intro eps
  refine ⟨4 * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (4 : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (4 : Rat)
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
        4 * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans
    (arctanIntegralRectangleComputeAtOne_width_le_four_div_succ n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

theorem arctanIntegralRectangleRawAtOne_valid :
    arctanIntegralRectangleRawAtOne.Valid := by
  change RealRaw.ValidCompute arctanIntegralRectangleComputeAtOne
  constructor
  · exact arctanIntegralRectangleComputeAtOne_ordered
  · constructor
    · exact arctanIntegralRectangleComputeAtOne_nested
    · exact arctanIntegralRectangleComputeAtOne_widthsShrink

def positiveLoopRaw (x : Rat) : RealRaw where
  compute := positiveLoopComputeAtStage x

theorem positiveLoopRaw_valid_on_unit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (positiveLoopRaw x).Valid := by
  change RealRaw.ValidCompute (positiveLoopComputeAtStage x)
  constructor
  · exact positiveLoopComputeAtStage_ordered hx0
  · constructor
    · exact positiveLoopComputeAtStage_nested hx0
    · exact positiveLoopComputeAtStage_widthsShrink hx0 hx1

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

theorem arctanGeom_valid_on_unit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanGeom x).Valid := by
  by_cases hzero : x = 0
  · subst x
    simpa [arctanGeom] using RealRaw.ofRat_valid (0 : Rat)
  · simpa [arctanGeom, positiveLoopRaw, hzero, hx0] using
      positiveLoopRaw_valid_on_unit hx0 hx1

theorem arctanGeom_valid_on_powerSeriesDomain
    {x : Rat} (hx : Elementary.Arctan.powerSeriesDomain x) :
    (arctanGeom x).Valid := by
  by_cases hx0 : 0 <= x
  · have hnotlt : ¬ x < 0 := by grind
    have hx1 : x <= 1 := by
      simpa [Elementary.Arctan.powerSeriesDomain, qabs, hnotlt] using hx
    exact arctanGeom_valid_on_unit hx0 hx1
  · have hxlt : x < 0 := by grind
    have hneg0 : 0 <= -x := by grind
    have hneg1 : -x <= 1 := by
      simpa [Elementary.Arctan.powerSeriesDomain, qabs, hxlt] using hx
    have hpos : (positiveLoopRaw (-x)).Valid :=
      positiveLoopRaw_valid_on_unit hneg0 hneg1
    have hzero : x ≠ 0 := by grind
    simpa [arctanGeom, hzero, hx0] using RealRaw.neg_valid hpos

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

theorem fareyIntegralPrefixRaw_equiv_arctanGeom_on_unit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (fareyIntegralPrefixRaw x).Equiv (arctanGeom x) := by
  by_cases hzero : x = 0
  · subst x
    simpa [arctanGeom] using fareyIntegralPrefixRaw_zero_equiv_zero
  · intro n
    apply (RealRaw.compareAt_overlap_iff
      (fareyIntegralPrefixRaw x) (arctanGeom x) n n).2
    rw [arctanGeom_nonneg_compute_eq hzero hx0 n]
    exact fareyIntegralPrefixStageInterval_overlaps_positiveLoop
      hx0 hx1 n n

theorem fareyIntegralUnitStageInterval_overlaps_rectangleAtOne
    (n m : Nat) :
    QInterval.Overlaps (fareyIntegralUnitRaw.compute n)
      (arctanIntegralRectangleRawAtOne.compute m) := by
  change QInterval.Overlaps
    (fareyIntegralUnitStageInterval n)
    (arctanIntegralRectangleComputeAtOne m)
  unfold fareyIntegralUnitStageInterval arctanIntegralRectangleComputeAtOne
  exact integralSumInterval_overlaps_of_covers
    (a := 0) (b := 1)
    (by native_decide)
    (fareyCellIntervals (RationalCircle.fareyUnitStage n))
    (arctanAreaLoopState 1 m).intervals
    (fareyUnitStage_intervals_covers n)
    (arctanAreaLoopState_intervals_covers
      (x := 1) (by native_decide) m)

theorem fareyIntegralUnitRaw_equiv_arctanIntegralRectangleRawAtOne :
    fareyIntegralUnitRaw.Equiv arctanIntegralRectangleRawAtOne := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    fareyIntegralUnitRaw arctanIntegralRectangleRawAtOne n n).2
  exact fareyIntegralUnitStageInterval_overlaps_rectangleAtOne n n

/-- Concrete finite comparison target for the Farey arctangent row: every
full-unit Farey rectangle stage overlaps every midpoint/geometric sector stage.
This is the common-refinement obligation left after both schedules have been
verified independently. -/
def FareyMidpointUnitCrossBounds : Prop :=
  forall n m : Nat,
    QInterval.Overlaps (fareyIntegralUnitRaw.compute n)
      (positiveLoopComputeAtStage (1 : Rat) m)

theorem fareyIntegralUnitStageInterval_overlaps_positiveLoopAtOne
    (n m : Nat) :
    QInterval.Overlaps (fareyIntegralUnitRaw.compute n)
      (positiveLoopComputeAtStage (1 : Rat) m) := by
  rw [positiveLoopComputeAtStage_eq_geometricSumInterval
    (x := 1) (by native_decide) m]
  change QInterval.Overlaps
    (fareyIntegralUnitStageInterval n)
    (geometricSumInterval (arctanAreaLoopState 1 m).intervals)
  unfold fareyIntegralUnitStageInterval
  exact integralSumInterval_overlaps_geometricSumInterval_of_covers
    (a := 0) (b := 1)
    (by native_decide)
    (fareyCellIntervals (RationalCircle.fareyUnitStage n))
    (arctanAreaLoopState 1 m).intervals
    (fareyUnitStage_intervals_covers n)
    (arctanAreaLoopState_intervals_covers
      (x := 1) (by native_decide) m)

theorem fareyMidpointUnitCrossBounds :
    FareyMidpointUnitCrossBounds := by
  intro n m
  exact fareyIntegralUnitStageInterval_overlaps_positiveLoopAtOne n m

theorem fareyIntegralUnitRaw_equiv_arctanGeom_one_of_crossBounds
    (h : FareyMidpointUnitCrossBounds) :
    fareyIntegralUnitRaw.Equiv (arctanGeom (1 : Rat)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    fareyIntegralUnitRaw (arctanGeom (1 : Rat)) n n).2
  rw [arctanGeom_one_compute_eq n]
  exact h n n

theorem fareyIntegralUnitRaw_equiv_arctanGeom_one_direct :
    fareyIntegralUnitRaw.Equiv (arctanGeom (1 : Rat)) :=
  fareyIntegralUnitRaw_equiv_arctanGeom_one_of_crossBounds
    fareyMidpointUnitCrossBounds

private def ZeroIntervals : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest => p = 0 ∧ r = 0 ∧ ZeroIntervals rest

private theorem refineAux_zero
    {lo hi : Rat} {intervals : List (Rat × Rat)}
    (hlo : lo = 0) (hhi : hi = 0) (hz : ZeroIntervals intervals) :
    (AreaLoopState.refineAux lo hi intervals).lo = 0 ∧
      (AreaLoopState.refineAux lo hi intervals).hi = 0 ∧
      ZeroIntervals (AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, ZeroIntervals, hlo, hhi]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hz with ⟨hp, hr, hrest⟩
      subst p
      subst r
      subst lo
      subst hi
      have hnext := ih (lo := 0 + arctanAreaIncrement 0 ((0 + 0) / 2) 0)
        (hi := 0 - arctanAreaDecrement 0 ((0 + 0) / 2) 0)
        (by native_decide)
        (by native_decide)
        hrest
      simp [AreaLoopState.refineAux, ZeroIntervals, hnext]
      native_decide

private theorem arctanAreaLoopState_zero (n : Nat) :
    (arctanAreaLoopState 0 n).lo = 0 ∧
      (arctanAreaLoopState 0 n).hi = 0 ∧
      ZeroIntervals (arctanAreaLoopState 0 n).intervals := by
  induction n with
  | zero =>
      simp [arctanAreaLoopState, iterateAreaLoopState, arctanAreaLoopInitial,
        ZeroIntervals]
      native_decide
  | succ n ih =>
      rw [arctanAreaLoopState_succ]
      exact refineAux_zero ih.1 ih.2.1 ih.2.2

theorem positiveLoopComputeAtStage_zero (n : Nat) :
    positiveLoopComputeAtStage 0 n = { lo := 0, hi := 0 } := by
  have h := arctanAreaLoopState_zero n
  simp [positiveLoopComputeAtStage, h.1, h.2.1]

theorem arctanIntegralRectangleRaw_equiv_arctanGeom
    {x : Rat} (hx : 0 <= x) :
    (arctanIntegralRectangleRaw x).Equiv (arctanGeom x) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (arctanIntegralRectangleRaw x) (arctanGeom x) n n).2
  by_cases hzero : x = 0
  · subst x
    have hover := arctanAreaLoop_integralSum_overlaps_positiveLoop
      (x := 0) (by native_decide) n
    rw [positiveLoopComputeAtStage_zero n] at hover
    simpa [arctanIntegralRectangleRaw, arctanIntegralRectangleCompute,
      arctanGeom, RealRaw.ofRat] using hover
  · change QInterval.Overlaps
      (integralSumInterval (arctanAreaLoopState x n).intervals)
      ((arctanGeom x).compute n)
    rw [arctanGeom_nonneg_compute_eq hzero hx n]
    exact arctanAreaLoop_integralSum_overlaps_positiveLoop hx n

theorem arctanIntegralRectangleRawAtOne_equiv_arctanGeom_one :
    arctanIntegralRectangleRawAtOne.Equiv (arctanGeom 1) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    arctanIntegralRectangleRawAtOne (arctanGeom 1) n n).2
  change QInterval.Overlaps
    (integralSumInterval (arctanAreaLoopState 1 n).intervals)
    ((arctanGeom 1).compute n)
  rw [arctanGeom_one_compute_eq n]
  exact arctanAreaLoop_integralSum_overlaps_positiveLoop
    (x := 1) (by native_decide) n

theorem fareyIntegralUnitRaw_equiv_arctanGeom_one :
    fareyIntegralUnitRaw.Equiv (arctanGeom (1 : Rat)) :=
  RealRaw.equiv_trans
    fareyIntegralUnitRaw_valid
    arctanIntegralRectangleRawAtOne_valid
    (arctanGeom_valid_on_unit
      (x := 1) (by native_decide) (by native_decide))
    fareyIntegralUnitRaw_equiv_arctanIntegralRectangleRawAtOne
    arctanIntegralRectangleRawAtOne_equiv_arctanGeom_one

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

def PowerSeriesAgreesAt (x : Rat) : Prop :=
  (arctan x).Equiv (arctanGeom x)

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

theorem powerSeriesAgreesAt_of_agreement
    (h : PowerSeriesAgreesOnUnit) {x : Rat}
    (hx : Elementary.Arctan.powerSeriesDomain x) :
    PowerSeriesAgreesAt x :=
  powerSeries_equiv_geometric_of_agreement h hx

end ArctanGeometry

end ComputableAnalysis
