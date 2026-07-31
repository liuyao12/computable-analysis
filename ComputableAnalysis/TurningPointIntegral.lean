import ComputableAnalysis.Calculus

/-!
# Turning-bracket helper for finite piecewise-monotone integral candidates

This module records the one-bracket component of a *particular* bounded
piecewise-monotone integral.  A general finite-piece computation repeats this
component at every non-rational turn and sums the certified monotone pieces.
The finite rational box arithmetic and its shrinking-width budget are
formalized by `FinitePiecewiseStageAssembly`; semantic coverage of those boxes
remains a per-function certificate.
It deliberately does not define a general integral operator.  A client
supplies a shrinking rational bracket for one turn, monotone integral
constructions on the two certified outer pieces, and a finite range enclosure
for the shrinking middle piece.

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

/-- A rational stage family with a nonnegative width and an explicit
shrinking-width modulus.  No nestedness or interpretation as an integral is
included here: this is the finite arithmetic layer used to assemble supplied
monotone pieces and unresolved turning gaps. -/
structure ShrinkingStage where
  compute : Nat -> QInterval
  width_nonneg : forall n, 0 <= (compute n).width
  widths_shrink : RealRaw.WidthsShrinkToZero compute

/-- Sum finitely many supplied rational stage boxes.  The recursion is
literal: every output box is a finite addition of rational interval boxes at
the same stage. -/
def finiteStageSum : List ShrinkingStage -> Nat -> QInterval
  | [], _ => { lo := 0, hi := 0 }
  | stage :: stages, n =>
      QInterval.addInterval (stage.compute n) (finiteStageSum stages n)

theorem finiteStageSum_width_nonneg (stages : List ShrinkingStage) (n : Nat) :
    0 <= (finiteStageSum stages n).width := by
  induction stages generalizing n with
  | nil =>
      simp only [finiteStageSum]
      change (0 : Rat) <= 0 - 0
      rw [Rat.sub_self]
      exact Rat.le_refl
  | cons stage stages ih =>
      change 0 <=
        (QInterval.addInterval (stage.compute n) (finiteStageSum stages n)).width
      rw [QInterval.addInterval_width]
      exact Rat.add_nonneg (stage.width_nonneg n) (ih n)

/-- A uniform rational width bound composes through a finite stage sum with
the literal factor given by the number of supplied boxes.  This is the
rate-composition rule used when a function-specific construction supplies a
common stage budget. -/
theorem finiteStageSum_width_le_length_mul
    (stages : List ShrinkingStage) (n : Nat) (B : Rat)
    (hbound : forall stage, stage ∈ stages -> (stage.compute n).width <= B) :
    (finiteStageSum stages n).width <= (stages.length : Rat) * B := by
  induction stages generalizing n B with
  | nil =>
      simp only [finiteStageSum, List.length_nil]
      change (0 : Rat) - 0 <= (0 : Rat) * B
      rw [Rat.sub_self, Rat.zero_mul]
      exact Rat.le_refl
  | cons stage stages ih =>
      have hstage : (stage.compute n).width <= B :=
        hbound stage (by simp)
      have hrest :
          (finiteStageSum stages n).width <= (stages.length : Rat) * B :=
        ih n B (fun other hother =>
          hbound other (List.mem_cons_of_mem stage hother))
      change
        (QInterval.addInterval (stage.compute n) (finiteStageSum stages n)).width
          <= ((stages.length + 1 : Nat) : Rat) * B
      rw [QInterval.addInterval_width, Rat.natCast_add]
      have hone : ((1 : Nat) : Rat) = 1 := by native_decide
      rw [hone]
      calc
        (stage.compute n).width + (finiteStageSum stages n).width <=
            B + (stages.length : Rat) * B :=
          rat_add_le_add hstage hrest
        _ = ((stages.length : Rat) + 1) * B := by
          grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm]

/-- A finite sum of shrinking rational stage families has shrinking width.
The proof gives each summand an equal rational portion of the requested error
budget through structural recursion; it invokes neither completeness nor a
general integral theorem. -/
theorem finiteStageSum_widths_shrink (stages : List ShrinkingStage) :
    RealRaw.WidthsShrinkToZero (finiteStageSum stages) := by
  induction stages with
  | nil =>
      intro eps
      refine ⟨0, ?_⟩
      intro n _hn
      simp only [finiteStageSum]
      change (0 : Rat) - 0 <= eps.val
      rw [Rat.sub_self]
      exact Rat.le_of_lt eps.property
  | cons stage stages ih =>
      intro eps
      let half : QPos :=
        { val := eps.val / 2
          property := by
            rw [Rat.div_def]
            exact Rat.mul_pos eps.property
              ((Rat.inv_pos).2 (by native_decide)) }
      obtain ⟨Nstage, hstage⟩ := stage.widths_shrink half
      obtain ⟨Nrest, hrest⟩ := ih half
      refine ⟨max Nstage Nrest, ?_⟩
      intro n hn
      have hnstage : Nstage <= n :=
        Nat.le_trans (Nat.le_max_left _ _) hn
      have hnrest : Nrest <= n :=
        Nat.le_trans (Nat.le_max_right _ _) hn
      have hstage' := hstage n hnstage
      have hrest' := hrest n hnrest
      change
        (QInterval.addInterval (stage.compute n) (finiteStageSum stages n)).width
          <= eps.val
      rw [QInterval.addInterval_width]
      calc
        (stage.compute n).width + (finiteStageSum stages n).width <=
            half.val + half.val :=
          rat_add_le_add hstage' hrest'
        _ = eps.val := by
          dsimp [half]
          rw [Rat.div_def]
          have htwo : (2 : Rat) ≠ 0 := by native_decide
          grind [Rat.add_assoc, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The finite stage assembly used by a supplied piecewise-monotone
construction.  The two lists remain separate so callers retain the
mathematical provenance of monotone-piece boxes and turning-gap range boxes.
This structure proves their finite error-budget aggregation; it does not
claim that arbitrary functions supply either list. -/
structure FinitePiecewiseStageAssembly where
  monotonePieces : List ShrinkingStage
  turningGaps : List ShrinkingStage

namespace FinitePiecewiseStageAssembly

def stages (A : FinitePiecewiseStageAssembly) : List ShrinkingStage :=
  A.monotonePieces ++ A.turningGaps

def compute (A : FinitePiecewiseStageAssembly) (n : Nat) : QInterval :=
  finiteStageSum A.stages n

theorem compute_width_nonneg (A : FinitePiecewiseStageAssembly) (n : Nat) :
    0 <= (A.compute n).width :=
  finiteStageSum_width_nonneg A.stages n

theorem compute_width_le_length_mul (A : FinitePiecewiseStageAssembly)
    (n : Nat) (B : Rat)
    (hbound : forall stage, stage ∈ A.stages -> (stage.compute n).width <= B) :
    (A.compute n).width <= (A.stages.length : Rat) * B :=
  finiteStageSum_width_le_length_mul A.stages n B hbound

theorem compute_widths_shrink (A : FinitePiecewiseStageAssembly) :
    RealRaw.WidthsShrinkToZero A.compute :=
  finiteStageSum_widths_shrink A.stages

end FinitePiecewiseStageAssembly

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

/-- The finite data for the one-bracket helper in one particular integral.
The two outer constructions may depend on the requested stage,
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

/-- The public name emphasizes that this is one reusable turning-bracket
component, not a distinguished kind of one-turn integral.  A finite
piecewise-monotone computation has one such component for each unresolved
turn. -/
abbrev TurningBracketIntegralCandidate (F : FunctionOnInterval) :=
  SingleTurnIntegralCandidate F

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
turning-point middle, and right monotone piece.  The two pieces may have
either opposite orientation: a decreasing-then-increasing `sinc` branch is
as admissible as an increasing-then-decreasing branch. -/
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

/-- View the unresolved turning gap as one term in a finite piecewise stage
assembly. -/
def middleShrinkingStage {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) : ShrinkingStage where
  compute := C.middleBox
  width_nonneg := C.middleBox_width_nonneg
  widths_shrink := C.middleBox_widths_shrink

/-- View the supplied left monotone construction as one term in a finite
piecewise stage assembly. -/
def leftShrinkingStage {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) : ShrinkingStage where
  compute := C.leftBox
  width_nonneg := C.leftBox_width_nonneg
  widths_shrink := C.left_widths_shrink

/-- View the supplied right monotone construction as one term in a finite
piecewise stage assembly. -/
def rightShrinkingStage {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) : ShrinkingStage where
  compute := C.rightBox
  width_nonneg := C.rightBox_width_nonneg
  widths_shrink := C.right_widths_shrink

/-- The existing one-bracket candidate, viewed as the smallest finite
piecewise assembly: two certified monotone pieces and one unresolved turning
gap. -/
def finiteStageAssembly {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) : FinitePiecewiseStageAssembly where
  monotonePieces := [C.leftShrinkingStage, C.rightShrinkingStage]
  turningGaps := [C.middleShrinkingStage]

/-- Finite interval addition is associative and commutative at the endpoint
level, so the generic finite assembly reproduces the candidate's literal
left--middle--right box exactly. -/
theorem finiteStageAssembly_compute {F : FunctionOnInterval}
    (C : SingleTurnIntegralCandidate F) (n : Nat) :
    (C.finiteStageAssembly.compute n) = C.compute n := by
  cases hleft : C.leftBox n
  cases hmiddle : C.middleBox n
  cases hright : C.rightBox n
  simp [finiteStageAssembly, FinitePiecewiseStageAssembly.compute,
    FinitePiecewiseStageAssembly.stages, finiteStageSum,
    QInterval.addInterval, SingleTurnIntegralCandidate.compute,
    leftShrinkingStage, middleShrinkingStage, rightShrinkingStage,
    hleft, hmiddle, hright]
  congr <;> grind [Rat.add_assoc, Rat.add_comm]

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

/-- The direct one-gap calculation has a vanishing width.  This is the
quantitative core repeated at every turn: no monotonicity is demanded on an
unresolved bracket, only a fixed rational range bound and a shrinking
rational width. -/
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

/-- The completion certificate for one reusable turning-bracket component. -/
abbrev TurningBracketIntegralCompletion {F : FunctionOnInterval}
    (C : TurningBracketIntegralCandidate F) :=
  SingleTurnIntegralCompletion C

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
