import ComputableAnalysis.Calculus

/-!
# Single-turn integral candidates

This module records a constructive pattern for a *particular* bounded integral
whose integrand rises and then falls.  It deliberately does not define a
general integral operator.  A client supplies shrinking rational brackets for
the (possibly non-rational) turning point, monotone integral constructions on
the two certified outer pieces, and a finite range enclosure for the shrinking
middle piece.

The resulting candidate is a literal stagewise rational interval computation.
Its width is proved to shrink.  Identifying it with a desired integral remains
a function-specific finite comparison, recorded separately as a completion
certificate.
-/

namespace ComputableAnalysis

namespace Integral

/-- A valid raw real whose interval boxes are known to remain in [a,b].

The raw value is intended to be a non-rational turning point.  No completed
real is introduced: every stage exposes only the rational endpoints of its
current bracket. -/
structure TurningPointBracket (a b : Rat) where
  raw : RealRaw
  valid : raw.Valid
  contained : forall n,
    a <= (raw.compute n).lo /\ (raw.compute n).hi <= b

namespace TurningPointBracket

def left (T : TurningPointBracket a b) (n : Nat) : Rat :=
  (T.raw.compute n).lo

def right (T : TurningPointBracket a b) (n : Nat) : Rat :=
  (T.raw.compute n).hi

def width (T : TurningPointBracket a b) (n : Nat) : Rat :=
  (T.raw.compute n).width

theorem lower_le_left (T : TurningPointBracket a b) (n : Nat) :
    a <= T.left n :=
  (T.contained n).1

theorem right_le_upper (T : TurningPointBracket a b) (n : Nat) :
    T.right n <= b :=
  (T.contained n).2

theorem left_le_right (T : TurningPointBracket a b) (n : Nat) :
    T.left n <= T.right n := by
  have h := T.valid.1 n
  change 0 <= T.right n - T.left n at h
  grind [Rat.sub_eq_add_neg]

theorem left_le_upper (T : TurningPointBracket a b) (n : Nat) :
    T.left n <= b :=
  Rat.le_trans (T.left_le_right n) (T.right_le_upper n)

theorem lower_le_right (T : TurningPointBracket a b) (n : Nat) :
    a <= T.right n :=
  Rat.le_trans (T.lower_le_left n) (T.left_le_right n)

theorem width_nonneg (T : TurningPointBracket a b) (n : Nat) :
    0 <= T.width n :=
  T.valid.1 n

theorem widths_shrink (T : TurningPointBracket a b) :
    RealRaw.WidthsShrinkToZero T.raw.compute :=
  T.valid.2.2

/-- Restrict a function to the certified left monotone piece at one turning
point stage. -/
def leftRestriction {F : FunctionOnInterval}
    (T : TurningPointBracket F.lower F.upper) (n : Nat) :
    FunctionOnInterval :=
  F.restrict F.lower (T.left n) (Rat.le_refl)
    (T.lower_le_left n) (T.left_le_upper n)

/-- Restrict a function to the certified right monotone piece at one turning
point stage. -/
def rightRestriction {F : FunctionOnInterval}
    (T : TurningPointBracket F.lower F.upper) (n : Nat) :
    FunctionOnInterval :=
  F.restrict (T.right n) F.upper (T.lower_le_right n)
    (T.right_le_upper n) (Rat.le_refl)

end TurningPointBracket

/-- A symmetric absolute enclosure for an interval of rational values. -/
def IntervalAbsBound (I : QInterval) (M : Rat) : Prop :=
  0 <= M /\ -M <= I.lo /\ I.hi <= M

/-- Bound the integral over the unresolved turning-point bracket by its
rational length times any interval enclosing the integrand there. -/
def turningPointMiddleBox {a b : Rat}
    (T : TurningPointBracket a b) (valueRange : QInterval) (n : Nat) :
    QInterval :=
  QInterval.scaleByRat (T.width n) valueRange

theorem turningPointMiddleBox_width {a b : Rat}
    (T : TurningPointBracket a b) (valueRange : QInterval) (n : Nat) :
    (turningPointMiddleBox T valueRange n).width =
      T.width n * valueRange.width := by
  unfold turningPointMiddleBox
  exact QInterval.scaleByRat_width_of_nonneg (T.width_nonneg n) valueRange

theorem turningPointMiddleBox_width_nonneg {a b : Rat}
    (T : TurningPointBracket a b) {valueRange : QInterval}
    (hRange : 0 <= valueRange.width) (n : Nat) :
    0 <= (turningPointMiddleBox T valueRange n).width := by
  rw [turningPointMiddleBox_width]
  exact Rat.mul_nonneg (T.width_nonneg n) hRange

theorem turningPointMiddleBox_widths_shrink {a b : Rat}
    (T : TurningPointBracket a b) {valueRange : QInterval}
    (hRange : 0 <= valueRange.width) :
    RealRaw.WidthsShrinkToZero (turningPointMiddleBox T valueRange) := by
  intro eps
  by_cases hzero : valueRange.width = 0
  · refine ⟨0, ?_⟩
    intro n _hn
    rw [turningPointMiddleBox_width, hzero, Rat.mul_zero]
    exact Rat.le_of_lt eps.property
  · have hpos : 0 < valueRange.width := by
      grind
    let scaled : QPos :=
      { val := eps.val / valueRange.width
        property := by
          rw [Rat.div_def]
          exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hpos) }
    obtain ⟨N, hN⟩ := T.widths_shrink scaled
    refine ⟨N, ?_⟩
    intro n hn
    have hwidth := hN n hn
    rw [turningPointMiddleBox_width]
    calc
      T.width n * valueRange.width <=
          scaled.val * valueRange.width :=
        Rat.mul_le_mul_of_nonneg_right hwidth (Rat.le_of_lt hpos)
      _ = eps.val := by
        dsimp [scaled]
        rw [Rat.div_def]
        have hne : valueRange.width ≠ 0 := Rat.ne_of_gt hpos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The middle box is contained in a symmetric interval whose radius is the
turning-point bracket width times a supplied absolute value bound. -/
theorem turningPointMiddleBox_contained_symmetric {a b : Rat}
    (T : TurningPointBracket a b) {valueRange : QInterval} {M : Rat}
    (hbound : IntervalAbsBound valueRange M) (n : Nat) :
    QInterval.ContainsInterval
      { lo := -(M * T.width n), hi := M * T.width n }
      (turningPointMiddleBox T valueRange n) := by
  have hwidth : 0 <= T.width n := T.width_nonneg n
  unfold IntervalAbsBound at hbound
  unfold turningPointMiddleBox QInterval.scaleByRat QInterval.ContainsInterval
  rw [if_pos hwidth]
  constructor
  · have h := Rat.mul_le_mul_of_nonneg_left hbound.2.1 hwidth
    grind [Rat.mul_assoc, Rat.mul_comm]
  · simpa [Rat.mul_comm] using
      Rat.mul_le_mul_of_nonneg_left hbound.2.2 hwidth

/-- The finite data for the up-then-down computation of one particular
integral.  The two outer constructions may depend on the requested stage,
because their rational endpoints are supplied by a shrinking bracket for a
possibly non-rational turning point.

The middle enclosure is deliberately only a range certificate.  A concrete
function-specific proof must still connect this range-scaled box and the two
outer integral boxes to its intended integral value. -/
structure SingleTurnIntegralCandidate (F : FunctionOnInterval) where
  turning : TurningPointBracket F.lower F.upper
  valueRange : QInterval
  valueRange_ordered : 0 <= valueRange.width
  valueRange_abs_bound : exists M, IntervalAbsBound valueRange M
  leftConstruction :
    forall n, MonotoneConstructionFor (turning.leftRestriction n)
  rightConstruction :
    forall n, MonotoneConstructionFor (turning.rightRestriction n)
  middle_encloses :
    forall n x
      (hx : inDomainInterval (turning.left n) (turning.right n) x)
      precision,
      valueRange.ContainsInterval
        (F.compute x
          (And.intro
            (Rat.le_trans (turning.lower_le_left n) hx.1)
            (Rat.le_trans hx.2 (turning.right_le_upper n)))
          precision)
  left_widths_shrink :
    RealRaw.WidthsShrinkToZero
      (fun n =>
        (monotoneIntegralFor (turning.leftRestriction n)
          (leftConstruction n)).compute n)
  right_widths_shrink :
    RealRaw.WidthsShrinkToZero
      (fun n =>
        (monotoneIntegralFor (turning.rightRestriction n)
          (rightConstruction n)).compute n)

namespace SingleTurnIntegralCandidate

def leftBox {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) : QInterval :=
  (monotoneIntegralFor (C.turning.leftRestriction n)
    (C.leftConstruction n)).compute n

def rightBox {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) : QInterval :=
  (monotoneIntegralFor (C.turning.rightRestriction n)
    (C.rightConstruction n)).compute n

def middleBox {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) : QInterval :=
  turningPointMiddleBox C.turning C.valueRange n

/-- The literal three-part stage computation: left monotone piece, bounded
turning-point middle, and right monotone piece. -/
def compute {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) : QInterval :=
  QInterval.addInterval
    (QInterval.addInterval (C.leftBox n) (C.middleBox n))
    (C.rightBox n)

def raw {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) : RealRaw where
  compute := C.compute

theorem leftBox_width_nonneg {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) :
    0 <= (C.leftBox n).width :=
  (monotoneIntegralFor_valid (C.turning.leftRestriction n)
    (C.leftConstruction n)).1 n

theorem rightBox_width_nonneg {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) :
    0 <= (C.rightBox n).width :=
  (monotoneIntegralFor_valid (C.turning.rightRestriction n)
    (C.rightConstruction n)).1 n

theorem middleBox_width_nonneg {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) :
    0 <= (C.middleBox n).width :=
  turningPointMiddleBox_width_nonneg C.turning C.valueRange_ordered n

theorem compute_width {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) :
    (C.compute n).width =
      (C.leftBox n).width + (C.middleBox n).width + (C.rightBox n).width := by
  unfold compute
  rw [QInterval.addInterval_width, QInterval.addInterval_width]

theorem compute_width_nonneg {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) :
    0 <= (C.compute n).width := by
  rw [C.compute_width]
  exact Rat.add_nonneg
    (Rat.add_nonneg (C.leftBox_width_nonneg n) (C.middleBox_width_nonneg n))
    (C.rightBox_width_nonneg n)

theorem middleBox_widths_shrink {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) :
    RealRaw.WidthsShrinkToZero C.middleBox :=
  turningPointMiddleBox_widths_shrink C.turning C.valueRange_ordered

/-- The data's fixed absolute-value certificate gives a stagewise, centred
bound on the unresolved middle contribution.  This is the estimate a concrete
integral-comparison proof uses to make the bracketed turning region harmless. -/
theorem middleBox_contained_symmetric {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) :
    exists M, QInterval.ContainsInterval
      { lo := -(M * C.turning.width n), hi := M * C.turning.width n }
      (C.middleBox n) := by
  obtain ⟨M, hM⟩ := C.valueRange_abs_bound
  exact ⟨M, turningPointMiddleBox_contained_symmetric C.turning hM n⟩

/-- The direct three-part computation has a vanishing width.  This is the
quantitative core of the turning-point method: no monotonicity is demanded on
the unresolved central bracket, only a fixed rational range bound and a
shrinking rational width. -/
theorem compute_widths_shrink {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) :
    RealRaw.WidthsShrinkToZero C.compute := by
  intro eps
  let third : QPos :=
    { val := eps.val / 3
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide)) }
  obtain ⟨Nleft, hleft⟩ := C.left_widths_shrink third
  obtain ⟨Nmiddle, hmiddle⟩ := C.middleBox_widths_shrink third
  obtain ⟨Nright, hright⟩ := C.right_widths_shrink third
  refine ⟨max Nleft (max Nmiddle Nright), ?_⟩
  intro n hn
  have hnleft : Nleft <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hnmiddle : Nmiddle <= n :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hnright : Nright <= n :=
    Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hleft' := hleft n hnleft
  have hmiddle' := hmiddle n hnmiddle
  have hright' := hright n hnright
  rw [C.compute_width]
  calc
    (C.leftBox n).width + (C.middleBox n).width + (C.rightBox n).width <=
        third.val + third.val + third.val :=
      rat_add_le_add (rat_add_le_add hleft' hmiddle') hright'
    _ = eps.val := by
      dsimp [third]
      rw [Rat.div_def]
      have hthree : (3 : Rat) ≠ 0 := by native_decide
      grind [Rat.add_assoc, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

end SingleTurnIntegralCandidate

/-- The function-specific proof obligation that identifies a shrinking
three-part turning-point computation with a chosen integral representative.
This is intentionally not assumed for arbitrary functions. -/
structure SingleTurnIntegralCompletion {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) where
  anchor : RealRaw
  anchor_valid : anchor.Valid
  candidate_equiv_anchor : C.raw.Equiv anchor
  radius : Nat -> Rat
  anchor_width_le_radius : forall n, (anchor.compute n).width <= radius n
  radius_shrinks : ShrinksToZero radius

namespace SingleTurnIntegralCompletion

def stabilizedRaw {F : FunctionOnInterval}
    {C : SingleTurnIntegralCandidate F}
    (completion : SingleTurnIntegralCompletion C) : RealRaw :=
  RealRaw.prefixStabilize C.raw completion.radius

theorem stabilizedRaw_valid {F : FunctionOnInterval}
    {C : SingleTurnIntegralCandidate F}
    (completion : SingleTurnIntegralCompletion C) :
    completion.stabilizedRaw.Valid :=
  RealRaw.prefixStabilize_valid C.compute_widths_shrink
    completion.anchor_valid completion.candidate_equiv_anchor
    completion.anchor_width_le_radius completion.radius_shrinks

theorem stabilizedRaw_equiv_anchor {F : FunctionOnInterval}
    {C : SingleTurnIntegralCandidate F}
    (completion : SingleTurnIntegralCompletion C) :
    completion.stabilizedRaw.Equiv completion.anchor :=
  RealRaw.prefixStabilize_equiv_anchor completion.anchor_valid
    completion.candidate_equiv_anchor completion.anchor_width_le_radius

end SingleTurnIntegralCompletion

end Integral

end ComputableAnalysis
