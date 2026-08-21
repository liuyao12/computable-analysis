import ComputableAnalysis.Pi
import ComputableAnalysis.DirichletSeries

/-!
# A finite cross-check for the Basel benchmark

This module compares two independent finite interval computations: the
Dirichlet-series enclosure for `zeta(2)` and the project's rational area
evaluator for `pi`, after squaring and scaling by `1/6`.  The overlap is a
computable numerical certificate; it is not Euler's Basel identity.
-/

namespace ComputableAnalysis

namespace BaselFiniteComparison

/-- The finite interval produced from the project's certified pi evaluator. -/
def geometricPiSquaredOverSixCompute (n : Nat) : QInterval :=
  (RealRaw.scaleRat (1 / 6) (piCircleArea * piCircleArea)).compute n

/-- The finite common interval extracted from the two independent Basel
enclosures at the checked stages. -/
def baselCommonInterval : QInterval :=
  QInterval.intersection
    (DirichletSeries.zetaTwoInterval 10000)
    (geometricPiSquaredOverSixCompute 8)

/-! Reusable interval interface for the Basel comparison.  The analytic input
is isolated in `hover`; everything else is rational interval bookkeeping. -/
theorem finiteBaselCommonInterval_certificate
    (zeta geometric : QInterval)
    (hzeta : zeta.lo <= zeta.hi)
    (hgeometric : geometric.lo <= geometric.hi)
    (hover : zeta.lo <= geometric.hi /\ geometric.lo <= zeta.hi) :
    (QInterval.intersection zeta geometric).lo <=
        (QInterval.intersection zeta geometric).hi /\
      zeta.ContainsInterval (QInterval.intersection zeta geometric) /\
      geometric.ContainsInterval (QInterval.intersection zeta geometric) := by
  refine ⟨QInterval.intersection_ordered_of_overlaps hzeta hgeometric hover,
    QInterval.intersection_contained_left _ _,
    QInterval.intersection_contained_right _ _⟩

/-- At finite stages, the zeta and geometric `pi^2 / 6` enclosures overlap. -/
theorem zetaTwoInterval_overlaps_projectPiSquaredOverSix_10000_8 :
    (DirichletSeries.zetaTwoInterval 10000).lo <=
        (geometricPiSquaredOverSixCompute 8).hi /\
      (geometricPiSquaredOverSixCompute 8).lo <=
        (DirichletSeries.zetaTwoInterval 10000).hi := by
  native_decide

/-- The two finite evaluators have a nonempty rational interval in common.
This is stronger than a Boolean overlap check: the common interval is an
explicit object that can be carried into subsequent finite comparisons. -/
theorem baselCommonInterval_certificate :
    baselCommonInterval.lo <= baselCommonInterval.hi /\
      (DirichletSeries.zetaTwoInterval 10000).ContainsInterval
        baselCommonInterval /\
      (geometricPiSquaredOverSixCompute 8).ContainsInterval
        baselCommonInterval := by
  refine ⟨?_, ?_, ?_⟩
  · exact QInterval.intersection_ordered_of_overlaps
      (DirichletSeries.zetaTwoInterval_ordered 10000)
      (by native_decide)
      zetaTwoInterval_overlaps_projectPiSquaredOverSix_10000_8
  · exact QInterval.intersection_contained_left _ _
  · exact QInterval.intersection_contained_right _ _

/-- The common finite interval is no wider than either source enclosure, so
it inherits both evaluators' explicit precision budgets. -/
theorem baselCommonInterval_width_le :
    baselCommonInterval.width <=
        (DirichletSeries.zetaTwoInterval 10000).width /\
      baselCommonInterval.width <=
        (geometricPiSquaredOverSixCompute 8).width := by
  constructor
  · exact QInterval.width_le_of_contains
      (QInterval.intersection_contained_left _ _)
  · exact QInterval.width_le_of_contains
      (QInterval.intersection_contained_right _ _)

/-- The midpoint of the common interval is an explicit rational witness
contained in both finite Basel enclosures. -/
theorem baselCommonInterval_midpoint_certificate :
    let q := baselCommonInterval.midpoint
    (DirichletSeries.zetaTwoInterval 10000).lo <= q /\
      q <= (DirichletSeries.zetaTwoInterval 10000).hi /\
      (geometricPiSquaredOverSixCompute 8).lo <= q /\
    q <= (geometricPiSquaredOverSixCompute 8).hi := by
  let q := baselCommonInterval.midpoint
  have hordered : baselCommonInterval.lo <= baselCommonInterval.hi := by
    exact (baselCommonInterval_certificate).1
  have hmid := QInterval.midpoint_mem hordered
  have hzeta := (baselCommonInterval_certificate).2.1
  have hpi := (baselCommonInterval_certificate).2.2
  dsimp [q]
  exact ⟨Rat.le_trans hzeta.1 hmid.1,
    Rat.le_trans hmid.2 hzeta.2,
    Rat.le_trans hpi.1 hmid.1,
    Rat.le_trans hmid.2 hpi.2⟩

/-- A tighter finite cross-check using later stages of both independent
enclosures.  This remains a finite numerical certificate, not the Basel
identity itself. -/
def baselRefinedCommonInterval : QInterval :=
  QInterval.intersection
    (DirichletSeries.zetaTwoInterval 100000)
    (geometricPiSquaredOverSixCompute 10)

theorem zetaTwoInterval_overlaps_projectPiSquaredOverSix_100000_10 :
    (DirichletSeries.zetaTwoInterval 100000).lo <=
        (geometricPiSquaredOverSixCompute 10).hi /\
      (geometricPiSquaredOverSixCompute 10).lo <=
        (DirichletSeries.zetaTwoInterval 100000).hi := by
  native_decide

theorem baselRefinedCommonInterval_certificate :
    baselRefinedCommonInterval.lo <= baselRefinedCommonInterval.hi /\
      (DirichletSeries.zetaTwoInterval 100000).ContainsInterval
        baselRefinedCommonInterval /\
      (geometricPiSquaredOverSixCompute 10).ContainsInterval
        baselRefinedCommonInterval := by
  refine ⟨?_, ?_, ?_⟩
  · exact QInterval.intersection_ordered_of_overlaps
      (DirichletSeries.zetaTwoInterval_ordered 100000)
      (by native_decide)
      zetaTwoInterval_overlaps_projectPiSquaredOverSix_100000_10
  · exact QInterval.intersection_contained_left _ _
  · exact QInterval.intersection_contained_right _ _

theorem baselRefinedCommonInterval_width_le :
    baselRefinedCommonInterval.width <=
        (DirichletSeries.zetaTwoInterval 100000).width /\
      baselRefinedCommonInterval.width <=
        (geometricPiSquaredOverSixCompute 10).width := by
  constructor
  · exact QInterval.width_le_of_contains
      (QInterval.intersection_contained_left _ _)
  · exact QInterval.width_le_of_contains
      (QInterval.intersection_contained_right _ _)

/-- The refined common interval supplies an explicit rational midpoint witness
contained in both later-stage Basel enclosures. -/
theorem baselRefinedCommonInterval_midpoint_certificate :
    let q := baselRefinedCommonInterval.midpoint
    (DirichletSeries.zetaTwoInterval 100000).lo <= q /\
      q <= (DirichletSeries.zetaTwoInterval 100000).hi /\
      (geometricPiSquaredOverSixCompute 10).lo <= q /\
      q <= (geometricPiSquaredOverSixCompute 10).hi := by
  let q := baselRefinedCommonInterval.midpoint
  have hordered : baselRefinedCommonInterval.lo <=
      baselRefinedCommonInterval.hi := by
    exact (baselRefinedCommonInterval_certificate).1
  have hmid := QInterval.midpoint_mem hordered
  have hzeta := (baselRefinedCommonInterval_certificate).2.1
  have hpi := (baselRefinedCommonInterval_certificate).2.2
  dsimp [q]
  exact ⟨Rat.le_trans hzeta.1 hmid.1,
    Rat.le_trans hmid.2 hzeta.2,
    Rat.le_trans hpi.1 hmid.1,
    Rat.le_trans hmid.2 hpi.2⟩

/-! A further finite cross-check at the next available precision stages. -/

def baselHighCommonInterval : QInterval :=
  QInterval.intersection
    (DirichletSeries.zetaTwoInterval 200000)
    (geometricPiSquaredOverSixCompute 12)

theorem zetaTwoInterval_overlaps_projectPiSquaredOverSix_200000_12 :
    (DirichletSeries.zetaTwoInterval 200000).lo <=
        (geometricPiSquaredOverSixCompute 12).hi /\
      (geometricPiSquaredOverSixCompute 12).lo <=
        (DirichletSeries.zetaTwoInterval 200000).hi := by
  native_decide

theorem baselHighCommonInterval_certificate :
    baselHighCommonInterval.lo <= baselHighCommonInterval.hi /\
      (DirichletSeries.zetaTwoInterval 200000).ContainsInterval
        baselHighCommonInterval /\
      (geometricPiSquaredOverSixCompute 12).ContainsInterval
        baselHighCommonInterval := by
  refine ⟨?_, ?_, ?_⟩
  · exact QInterval.intersection_ordered_of_overlaps
      (DirichletSeries.zetaTwoInterval_ordered 200000)
      (by native_decide)
      zetaTwoInterval_overlaps_projectPiSquaredOverSix_200000_12
  · exact QInterval.intersection_contained_left _ _
  · exact QInterval.intersection_contained_right _ _

theorem baselHighCommonInterval_width_le :
    baselHighCommonInterval.width <=
        (DirichletSeries.zetaTwoInterval 200000).width /\
      baselHighCommonInterval.width <=
        (geometricPiSquaredOverSixCompute 12).width := by
  constructor
  · exact QInterval.width_le_of_contains
      (QInterval.intersection_contained_left _ _)
  · exact QInterval.width_le_of_contains
      (QInterval.intersection_contained_right _ _)

/-! The highest checked finite overlap also exports a concrete rational
midpoint, so downstream comparisons need not carry an abstract intersection
object. -/
theorem baselHighCommonInterval_midpoint_certificate :
    let q := baselHighCommonInterval.midpoint
    (DirichletSeries.zetaTwoInterval 200000).lo <= q /\
      q <= (DirichletSeries.zetaTwoInterval 200000).hi /\
      (geometricPiSquaredOverSixCompute 12).lo <= q /\
      q <= (geometricPiSquaredOverSixCompute 12).hi := by
  let q := baselHighCommonInterval.midpoint
  have hordered : baselHighCommonInterval.lo <=
      baselHighCommonInterval.hi := by
    exact (baselHighCommonInterval_certificate).1
  have hmid := QInterval.midpoint_mem hordered
  have hzeta := (baselHighCommonInterval_certificate).2.1
  have hpi := (baselHighCommonInterval_certificate).2.2
  dsimp [q]
  exact ⟨Rat.le_trans hzeta.1 hmid.1,
    Rat.le_trans hmid.2 hzeta.2,
    Rat.le_trans hpi.1 hmid.1,
    Rat.le_trans hmid.2 hpi.2⟩

end BaselFiniteComparison

end ComputableAnalysis
