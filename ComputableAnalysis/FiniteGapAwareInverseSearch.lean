import ComputableAnalysis.Calculus

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
  /-- The scheduled outputs form one nested interval computation. -/
  valid_output : RealRaw.ValidCompute output
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

def gapAwareInverseBisectionPlan_has_search
    {I : GapAwareInvertibleFunctionOnInterval}
    (hplan : ∀ y : GapAwareInRangeRaw I,
      GapAwareInverseBisectionPlan I y) :
    GapAwareHasBisectionSearch I := by
  intro y
  exact gapAwareInverseBisectionPlanToSearch (hplan y)

end ComputableAnalysis
