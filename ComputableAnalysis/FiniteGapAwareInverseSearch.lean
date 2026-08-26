import ComputableAnalysis.FTC

/-!
# Proof-carrying gap-aware inverse search

This module is the reusable assembly layer for inverse branches.  A concrete
function supplies only its finite midpoint decisions, the nesting/precision
proof for the resulting schedule, and the interval-overlap certificate.  The
common construction then packages those data as the project-wide inverse
interface.  Thus separate functions do not need separate copies of the
routine `RealRaw` and inverse-record plumbing.
-/

namespace ComputableAnalysis

/-! A fixed-gap separation certificate already contains the output precision
needed by the gap-aware interface.  The only extra datum is the provider's
explicit schedule translating a strict rational input gap into the fixed
input threshold expected by that certificate.  Keeping this translation as a
parameter makes the adapter reusable without baking in a particular
denominator strategy or invoking density/completeness. -/

def EffectiveInverseSeparation.toGapAware
    {F : FunctionOnInterval} (S : EffectiveInverseSeparation F)
    (stage : forall {x y : Rat}, x < y -> Nat -> Nat)
    (hinput : forall {x y : Rat} (hxy : x < y) (n : Nat),
      x + 1 / ((S.inputPrecision (stage hxy n) : Nat) : Rat) <= y) :
    GapAwareInverseSeparation F where
  kind := S.kind
  outputPrecision := fun {_x _y} hxy n => S.outputPrecision (stage hxy n)
  separated := by
    intro x y hx hy hxy n
    exact S.separated x y hx hy (stage hxy n) (hinput hxy n)

def gapAwareSourceInterval
    (I : GapAwareInvertibleFunctionOnInterval) : QInterval :=
  { lo := I.function.lower, hi := I.function.upper }

theorem gapAwareSourceInterval_subinterval
    (I : GapAwareInvertibleFunctionOnInterval) :
    subintervalOf (gapAwareSourceInterval I)
      I.function.lower I.function.upper := by
  dsimp [gapAwareSourceInterval, GapAwareInvertibleFunctionOnInterval.function]
  exact ⟨Rat.le_refl, I.source_ordered, Rat.le_refl⟩

structure GapAwareInverseBisectionPlan
    (I : GapAwareInvertibleFunctionOnInterval)
    (y : GapAwareInRangeRaw I) where
  /-- The evaluator precision used to inspect the target and midpoint. -/
  precision : Nat → Nat
  /-- The finite number of midpoint decisions made at each target stage. -/
  steps : Nat → Nat
  /-- The interval returned at each target stage. -/
  output : Nat → QInterval
  /-- The output is the standard conservative midpoint computation. -/
  output_eq : ∀ n, output n =
    gapAwareTargetBisectionFixedIterate I.continuous
      (y.value.compute n)
      (gapAwareSourceInterval I)
      (gapAwareSourceInterval_subinterval I)
      (precision n) (steps n)
  decisions : ∀ n k, k < steps n →
    gapAwareTargetBisectionFixedDecision I.continuous
      (y.value.compute n)
      (gapAwareSourceInterval I)
      (gapAwareSourceInterval_subinterval I)
      (precision n) k
  /-- Every scheduled output is ordered. -/
  output_ordered : ∀ n, (output n).lo ≤ (output n).hi
  /-- The scheduled outputs form one nested interval computation. -/
  output_nested : ∀ n m, n ≤ m →
    (output n).lo ≤ (output m).lo ∧ (output m).hi ≤ (output n).hi
  /-- A concrete modulus for the output width. -/
  output_width_le : ∀ n,
    (output n).width ≤ 1 / ((n + 1 : Nat) : Rat)
  /-- Each output interval still contains a value compatible with the target. -/
  value_overlaps : ∀ n,
    QInterval.Overlaps
      (I.continuous.regular.evalInterval
        (output n)
        (by
          rw [output_eq n]
          exact gapAwareTargetBisectionFixedIterate_subinterval
            I.continuous (y.value.compute n)
            (gapAwareSourceInterval I)
            (gapAwareSourceInterval_subinterval I)
            (precision n) (steps n))
        n)
      (y.value.compute n)

/-! A constructor for the usual case where the output is exactly the fixed
midpoint iterator.  The branch-specific proof is consequently reduced to the
four genuinely mathematical obligations: decisions, nesting, width, and
forward-image overlap. -/
def gapAwareInverseBisectionPlanOfFixedIterate
    {I : GapAwareInvertibleFunctionOnInterval}
    {y : GapAwareInRangeRaw I}
    (precision steps : Nat → Nat)
    (hdecisions : ∀ n k, k < steps n →
      gapAwareTargetBisectionFixedDecision I.continuous
        (y.value.compute n) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) (precision n) k)
    (hnested : ∀ n m, n ≤ m →
      (gapAwareTargetBisectionFixedIterate I.continuous
        (y.value.compute n) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) (precision n) (steps n)).lo ≤
      (gapAwareTargetBisectionFixedIterate I.continuous
        (y.value.compute m) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) (precision m) (steps m)).lo ∧
      (gapAwareTargetBisectionFixedIterate I.continuous
        (y.value.compute m) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) (precision m) (steps m)).hi ≤
      (gapAwareTargetBisectionFixedIterate I.continuous
        (y.value.compute n) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) (precision n) (steps n)).hi)
    (hwidth : ∀ n,
      (gapAwareTargetBisectionFixedIterate I.continuous
        (y.value.compute n) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) (precision n) (steps n)).width ≤
        1 / ((n + 1 : Nat) : Rat))
    (hoverlaps : ∀ n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (gapAwareTargetBisectionFixedIterate I.continuous
            (y.value.compute n) (gapAwareSourceInterval I)
            (gapAwareSourceInterval_subinterval I) (precision n) (steps n))
          (gapAwareTargetBisectionFixedIterate_subinterval I.continuous
            (y.value.compute n) (gapAwareSourceInterval I)
            (gapAwareSourceInterval_subinterval I) (precision n) (steps n))
          n)
        (y.value.compute n)) :
    GapAwareInverseBisectionPlan I y where
  precision := precision
  steps := steps
  output := fun n => gapAwareTargetBisectionFixedIterate I.continuous
    (y.value.compute n) (gapAwareSourceInterval I)
    (gapAwareSourceInterval_subinterval I) (precision n) (steps n)
  output_eq := fun _ => rfl
  decisions := hdecisions
  output_ordered := by
    intro n
    exact (gapAwareTargetBisectionFixedIterate_subinterval I.continuous
      (y.value.compute n) (gapAwareSourceInterval I)
      (gapAwareSourceInterval_subinterval I) (precision n) (steps n)).2.1
  output_nested := hnested
  output_width_le := hwidth
  value_overlaps := hoverlaps

/-! The scheduled analogue keeps evaluator precision independent from the
number of midpoint steps.  This is the adapter used by branches whose gap
separation budget is not linear in the requested output stage. -/
structure GapAwareScheduledInverseBisectionPlan
    (I : GapAwareInvertibleFunctionOnInterval)
    (y : GapAwareInRangeRaw I) where
  precision : Nat → Nat
  steps : Nat → Nat
  output : Nat → QInterval
  output_eq : ∀ n, output n =
    gapAwareTargetBisectionScheduledIterate I.continuous
      (y.value.compute n)
      (gapAwareSourceInterval I)
      (gapAwareSourceInterval_subinterval I)
      precision (steps n)
  decisions : ∀ n k, k < steps n →
    gapAwareTargetBisectionScheduledDecision I.continuous
      (y.value.compute n)
      (gapAwareSourceInterval I)
      (gapAwareSourceInterval_subinterval I)
      precision k
  output_ordered : ∀ n, (output n).lo ≤ (output n).hi
  output_nested : ∀ n m, n ≤ m →
    (output n).lo ≤ (output m).lo ∧
      (output m).hi ≤ (output n).hi
  output_width_le : ∀ n,
    (output n).width ≤ 1 / ((n + 1 : Nat) : Rat)
  value_overlaps : ∀ n,
    QInterval.Overlaps
      (I.continuous.regular.evalInterval
        (output n)
        (by
          rw [output_eq n]
          exact gapAwareTargetBisectionScheduledIterate_subinterval
            I.continuous (y.value.compute n)
            (gapAwareSourceInterval I)
            (gapAwareSourceInterval_subinterval I)
            precision (steps n))
        n)
      (y.value.compute n)

def gapAwareScheduledInverseBisectionPlanOfScheduledIterate
    {I : GapAwareInvertibleFunctionOnInterval}
    {y : GapAwareInRangeRaw I}
    (precision steps : Nat → Nat)
    (hdecisions : ∀ n k, k < steps n →
      gapAwareTargetBisectionScheduledDecision I.continuous
        (y.value.compute n) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) precision k)
    (hnested : ∀ n m, n ≤ m →
      (gapAwareTargetBisectionScheduledIterate I.continuous
        (y.value.compute n) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) precision (steps n)).lo ≤
      (gapAwareTargetBisectionScheduledIterate I.continuous
        (y.value.compute m) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) precision (steps m)).lo ∧
      (gapAwareTargetBisectionScheduledIterate I.continuous
        (y.value.compute m) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) precision (steps m)).hi ≤
      (gapAwareTargetBisectionScheduledIterate I.continuous
        (y.value.compute n) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) precision (steps n)).hi)
    (hwidth : ∀ n,
      (gapAwareTargetBisectionScheduledIterate I.continuous
        (y.value.compute n) (gapAwareSourceInterval I)
        (gapAwareSourceInterval_subinterval I) precision (steps n)).width ≤
        1 / ((n + 1 : Nat) : Rat))
    (hoverlaps : ∀ n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (gapAwareTargetBisectionScheduledIterate I.continuous
            (y.value.compute n) (gapAwareSourceInterval I)
            (gapAwareSourceInterval_subinterval I) precision (steps n))
          (gapAwareTargetBisectionScheduledIterate_subinterval
            I.continuous (y.value.compute n) (gapAwareSourceInterval I)
            (gapAwareSourceInterval_subinterval I) precision (steps n)) n)
        (y.value.compute n)) :
    GapAwareScheduledInverseBisectionPlan I y where
  precision := precision
  steps := steps
  output := fun n => gapAwareTargetBisectionScheduledIterate I.continuous
    (y.value.compute n) (gapAwareSourceInterval I)
    (gapAwareSourceInterval_subinterval I) precision (steps n)
  output_eq := fun _ => rfl
  decisions := hdecisions
  output_ordered := by
    intro n
    exact (gapAwareTargetBisectionScheduledIterate_subinterval I.continuous
      (y.value.compute n) (gapAwareSourceInterval I)
      (gapAwareSourceInterval_subinterval I) precision (steps n)).2.1
  output_nested := hnested
  output_width_le := hwidth
  value_overlaps := hoverlaps

theorem GapAwareInverseBisectionPlan.valid_output
    {I : GapAwareInvertibleFunctionOnInterval}
    {y : GapAwareInRangeRaw I}
    (plan : GapAwareInverseBisectionPlan I y) :
    RealRaw.ValidCompute plan.output := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 ≤ (plan.output n).hi - (plan.output n).lo
    grind [plan.output_ordered n]
  · intro n m hnm
    exact ⟨(plan.output_nested n m hnm).1,
      plan.output_ordered m, (plan.output_nested n m hnm).2⟩
  · intro eps
    refine ⟨eps.val.den, ?_⟩
    intro n hn
    have hanti :
        1 / (((n + 1 : Nat) : Rat)) ≤
          1 / (((eps.val.den + 1 : Nat) : Rat)) := by
      apply FTC.one_div_nat_antitone
      · exact Nat.succ_pos eps.val.den
      · exact Nat.succ_pos n
      · omega
    exact Rat.le_trans (plan.output_width_le n)
      (Rat.le_trans hanti
        (FTC.one_div_den_succ_le_of_pos eps.property))

theorem GapAwareScheduledInverseBisectionPlan.valid_output
    {I : GapAwareInvertibleFunctionOnInterval}
    {y : GapAwareInRangeRaw I}
    (plan : GapAwareScheduledInverseBisectionPlan I y) :
    RealRaw.ValidCompute plan.output := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 ≤ (plan.output n).hi - (plan.output n).lo
    grind [plan.output_ordered n]
  · intro n m hnm
    exact ⟨(plan.output_nested n m hnm).1,
      plan.output_ordered m, (plan.output_nested n m hnm).2⟩
  · intro eps
    refine ⟨eps.val.den, ?_⟩
    intro n hn
    have hanti :
        1 / (((n + 1 : Nat) : Rat)) ≤
          1 / (((eps.val.den + 1 : Nat) : Rat)) := by
      apply FTC.one_div_nat_antitone
      · exact Nat.succ_pos eps.val.den
      · exact Nat.succ_pos n
      · omega
    exact Rat.le_trans (plan.output_width_le n)
      (Rat.le_trans hanti
        (FTC.one_div_den_succ_le_of_pos eps.property))

/-! The dependent record above refers to its output function in its fields. -/
set_option autoImplicit false in
def gapAwareInverseBisectionPlanToSearch
    {I : GapAwareInvertibleFunctionOnInterval}
    {y : GapAwareInRangeRaw I}
    (plan : GapAwareInverseBisectionPlan I y) :
    GapAwareInverseBisectionSearch I y where
  compute_preimage := plan.output
  valid_preimage := plan.valid_output
  preimage_subinterval := by
    intro n
    rw [plan.output_eq n]
    exact gapAwareTargetBisectionFixedIterate_subinterval
      I.continuous (y.value.compute n)
      (gapAwareSourceInterval I)
      (gapAwareSourceInterval_subinterval I)
      (plan.precision n) (plan.steps n)
  value_overlaps := plan.value_overlaps

def gapAwareScheduledInverseBisectionPlanToSearch
    {I : GapAwareInvertibleFunctionOnInterval}
    {y : GapAwareInRangeRaw I}
    (plan : GapAwareScheduledInverseBisectionPlan I y) :
    GapAwareInverseBisectionSearch I y where
  compute_preimage := plan.output
  valid_preimage := plan.valid_output
  preimage_subinterval := by
    intro n
    rw [plan.output_eq n]
    exact gapAwareTargetBisectionScheduledIterate_subinterval
      I.continuous (y.value.compute n)
      (gapAwareSourceInterval I)
      (gapAwareSourceInterval_subinterval I)
      plan.precision (plan.steps n)
  value_overlaps := plan.value_overlaps

def gapAwareInverseBisectionPlan_has_search
    {I : GapAwareInvertibleFunctionOnInterval}
    (hplan : ∀ y : GapAwareInRangeRaw I,
      GapAwareInverseBisectionPlan I y) :
    GapAwareHasBisectionSearch I := by
  intro y
  exact gapAwareInverseBisectionPlanToSearch (hplan y)

def gapAwareScheduledInverseBisectionPlan_has_search
    {I : GapAwareInvertibleFunctionOnInterval}
    (hplan : ∀ y : GapAwareInRangeRaw I,
      GapAwareScheduledInverseBisectionPlan I y) :
    GapAwareHasBisectionSearch I := by
  intro y
  exact gapAwareScheduledInverseBisectionPlanToSearch (hplan y)

end ComputableAnalysis
