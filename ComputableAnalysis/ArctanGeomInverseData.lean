import ComputableAnalysis.ArctanScheduledRegular

/-!
# Inverse-search data for the geometric arctangent

The geometric arctangent uses the positive-loop evaluator, while the
rectangle evaluator supplies the interval geometry used to prove strict
separation.  The positive-loop boxes are contained in the corresponding
rectangle boxes, so the latter's finite order and separation certificates
transport to the actual geometric branch.
-/

namespace ComputableAnalysis

private theorem arctanGeom_compute_eq_positiveLoop
    {x : Rat} (hx0 : 0 <= x) (n : Nat) :
    (arctanGeom x).compute n = positiveLoopComputeAtStage x n := by
  by_cases hzero : x = 0
  · subst x
    rw [positiveLoopComputeAtStage_zero]
    simp [arctanGeom]
  · exact arctanGeom_nonneg_compute_eq hzero hx0 n

private theorem arctanGeom_compute_contained_in_rectangle
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    QInterval.ContainsInterval
      (arctanIntegralRectangleCompute x n)
      ((arctanGeom x).compute n) := by
  rw [arctanGeom_compute_eq_positiveLoop hx0 n]
  exact arctanAreaLoop_integralSum_contains_positiveLoop hx0 n

theorem arctanGeomOnUnit_nondecreasing :
    NondecreasingOnInterval arctanGeomOnUnit := by
  intro x y hx hy hxy n
  have hrectangle :=
    ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
      hx.1 hxy n
  have hxcontains := arctanGeom_compute_contained_in_rectangle hx.1 hx.2 n
  have hycontains := arctanGeom_compute_contained_in_rectangle hy.1 hy.2 n
  unfold QInterval.ContainsInterval at hxcontains hycontains
  change ((arctanGeom x).compute n).lo <=
    ((arctanGeom y).compute n).hi
  grind

def arctanGeomOnUnit_monotone :
    MonotoneOnInterval arctanGeomOnUnit :=
  MonotoneOnInterval.ofNondecreasing arctanGeomOnUnit_nondecreasing

/-! The same containment also transports the rectangle branch's explicit
near-continuity estimate.  This is the finite regularity datum needed before
assembling the full interval-regular inverse branch. -/

theorem arctanGeomOnUnit_near_of_qabs_le
    (eps : QPos) (n : Nat) (hn : 4 * (eps.val.den + 1) <= n)
    {x y : Rat}
    (hx : inDomainInterval arctanGeomOnUnit.lower
      arctanGeomOnUnit.upper x)
    (hy : inDomainInterval arctanGeomOnUnit.lower
      arctanGeomOnUnit.upper y)
    (hclose : qabs (y - x) <= eps.val) :
    QInterval.NearAt
      (arctanGeomOnUnit.compute x hx n)
      (arctanGeomOnUnit.compute y hy n) eps := by
  have hrectangle := arctanIntegralRectangleOnUnit_near_of_qabs_le
    eps n hn hx hy hclose
  have hxcontains := arctanGeom_compute_contained_in_rectangle hx.1 hx.2 n
  have hycontains := arctanGeom_compute_contained_in_rectangle hy.1 hy.2 n
  change QInterval.NearAt
    ((arctanGeom x).compute n) ((arctanGeom y).compute n) eps
  change QInterval.NearAt
    (arctanIntegralRectangleCompute x n)
    (arctanIntegralRectangleCompute y n) eps at hrectangle
  unfold QInterval.NearAt at hrectangle ⊢
  unfold QInterval.ContainsInterval at hxcontains hycontains
  grind [QInterval.width, Rat.sub_eq_add_neg]

def arctanGeomOnUnit_effectiveModulus :
    EffectiveModulusFor arctanGeomOnUnit where
  inputPrecision := fun n => n + 1
  evalPrecision := fun n =>
    4 * ((precisionAtStage n).val.den + 1)
  close := by
    intro x y n hx hy hclose
    let eps : QPos := precisionAtStage n
    let N : Nat := 4 * (eps.val.den + 1)
    have hinput : qabs (y - x) <= eps.val := by
      cases n with
      | zero =>
          have hone : (1 : Rat) / 1 = 1 := by native_decide
          simpa [eps, precisionAtStage, hone] using hclose
      | succ n =>
          have hreciprocal :
              1 / (((n + 2 : Nat) : Rat)) <=
                1 / (((n + 1 : Nat) : Rat)) :=
            FTC.one_div_nat_antitone (by omega) (by omega) (by omega)
          simpa [eps, precisionAtStage] using Rat.le_trans hclose hreciprocal
    simpa [eps, N] using
      (arctanGeomOnUnit_near_of_qabs_le eps N (by omega)
        hx hy hinput)

/-! The interval-regularity interface asks for the literal width budget
`1/(n+1)`.  The native positive-loop evaluator has a harmless constant-factor
budget, so expose the same evaluator with an explicit cofinal schedule. -/

def arctanGeomScheduledStage (n : Nat) : Nat := 32 * (n + 1)

def arctanGeomScheduledOnUnit : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x ∧ x <= 1
    compute := fun x _hx n =>
      (ArctanGeometry.arctanGeom x).compute (arctanGeomScheduledStage n)
    rate := fun x _hx => (ArctanGeometry.arctanGeom x).rate }
  lower := 0
  upper := 1
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact ArctanGeometry.arctanGeom_valid_on_unit hx.1 hx.2

theorem arctanGeomScheduledOnUnit_compute_eq
    (x : Rat) (hx : inDomainInterval
      arctanGeomScheduledOnUnit.lower arctanGeomScheduledOnUnit.upper x)
    (n : Nat) :
    arctanGeomScheduledOnUnit.compute x hx n =
      positiveLoopComputeAtStage x (arctanGeomScheduledStage n) := by
  change (ArctanGeometry.arctanGeom x).compute
      (arctanGeomScheduledStage n) = _
  rw [arctanGeom_compute_eq_positiveLoop hx.1
    (arctanGeomScheduledStage n)]

theorem arctanGeomScheduledOnUnit_width_le
    (x : Rat) (hx : inDomainInterval
      arctanGeomScheduledOnUnit.lower arctanGeomScheduledOnUnit.upper x)
    (n : Nat) :
    (arctanGeomScheduledOnUnit.compute x hx n).width <=
      1 / (((n + 1 : Nat) : Rat)) := by
  rw [arctanGeomScheduledOnUnit_compute_eq]
  have h := ArctanGeometry.positiveLoopComputeAtStage_width_le_four_div_succ
    hx.1 hx.2 (arctanGeomScheduledStage n)
  dsimp [arctanGeomScheduledStage] at h ⊢
  rw [show ((32 * (n + 1) + 1 : Nat) : Rat) =
    32 * ((n + 1 : Nat) : Rat) + 1 by norm_num [Rat.natCast_mul,
      Rat.natCast_add]] at h
  have hd : 0 < ((n + 1 : Nat) : Rat) :=
    (Rat.natCast_pos).2 (Nat.succ_pos n)
  rw [Rat.div_def] at h ⊢
  exact Rat.le_trans h (by
    field_simp
    nlinarith)

theorem arctanGeomScheduled_forward_lower_sub_upper_le
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat) :
    (arctanGeomScheduledOnUnit.compute (x + h)
      ⟨by grind, hupper⟩ n).lo -
    (arctanGeomScheduledOnUnit.compute x ⟨hx0, hx1⟩ n).hi <=
      h + 1 / (((n + 1 : Nat) : Rat) / 4) := by
  let S := arctanGeomScheduledStage n
  have hrect :=
    ArctanGeometry.arctanIntegralRectangleCompute_forward_lower_sub_upper_le_step
      hx0 hx1 hpos hupper S
  have hxl := arctanGeom_compute_contained_in_rectangle hx0 hx1 S
  have hxr := arctanGeom_compute_contained_in_rectangle (by grind) hupper S
  have hrectWidthX :=
    ArctanGeometry.arctanIntegralRectangleCompute_width_le_four_div_succ
      hx0 hx1 S
  have hrectWidthY :=
    ArctanGeometry.arctanIntegralRectangleCompute_width_le_four_div_succ
      (by grind) hupper S
  change (positiveLoopComputeAtStage (x + h) S).lo -
      (positiveLoopComputeAtStage x S).hi <= _
  rw [← arctanGeom_compute_eq_positiveLoop (by grind) S,
    ← arctanGeom_compute_eq_positiveLoop hx0 S]
  unfold QInterval.ContainsInterval at hxl hxr
  unfold QInterval.width at hrectWidthX hrectWidthY
  have hrectlo :
      (ArctanGeometry.arctanIntegralRectangleCompute (x + h) S).lo -
          (ArctanGeometry.arctanIntegralRectangleCompute x S).hi <= h := hrect
  grind [QInterval.width, Rat.sub_eq_add_neg]

def arctanGeomScheduledImage
    (I : QInterval)
    (hI : subintervalOf I arctanGeomScheduledOnUnit.lower
      arctanGeomScheduledOnUnit.upper)
    (n : Nat) : QInterval :=
  let hLo : inDomainInterval arctanGeomScheduledOnUnit.lower
      arctanGeomScheduledOnUnit.upper I.lo :=
    ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
  let hHi : inDomainInterval arctanGeomScheduledOnUnit.lower
      arctanGeomScheduledOnUnit.upper I.hi :=
    ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
  let budget : Rat := 1 / (8 * ((n + 1 : Nat) : Rat))
  { lo := (arctanGeomScheduledOnUnit.compute I.lo hLo n).lo - budget,
    hi := (arctanGeomScheduledOnUnit.compute I.hi hHi n).hi + budget }

private theorem arctanGeomScheduledImage_width_le
    (I : QInterval)
    (hI : subintervalOf I arctanGeomScheduledOnUnit.lower
      arctanGeomScheduledOnUnit.upper)
    (n : Nat) :
    (arctanGeomScheduledImage I hI n).width <=
      2 * I.width + 4 * (1 / (8 * ((n + 1 : Nat) : Rat))) := by
  let hLo : inDomainInterval arctanGeomScheduledOnUnit.lower
      arctanGeomScheduledOnUnit.upper I.lo :=
    ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
  let hHi : inDomainInterval arctanGeomScheduledOnUnit.lower
      arctanGeomScheduledOnUnit.upper I.hi :=
    ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
  let d : Rat := ((n + 1 : Nat) : Rat)
  have hcross := arctanGeomScheduled_forward_lower_sub_upper_le
    hI.1 (Rat.le_trans hI.2.1 hI.2.2) hI.2.1 hI.2.2 n
  have hLoWidth := arctanGeomScheduledOnUnit_width_le I.lo hLo n
  have hHiWidth := arctanGeomScheduledOnUnit_width_le I.hi hHi n
  dsimp [arctanGeomScheduledImage]
  unfold QInterval.width at hcross hLoWidth hHiWidth ⊢
  dsimp [d] at hcross hLoWidth hHiWidth ⊢
  grind [Rat.sub_eq_add_neg]

/-! The geometric branch inherits the rectangle branch's effective strict
separation because each geometric box is contained in its matching rectangle
box. -/

def arctanGeomOnUnit_effectiveInverseSeparation :
    EffectiveInverseSeparation arctanGeomOnUnit where
  kind := .nondecreasing
  inputPrecision := fun n => n + 1
  inputPrecision_pos := fun n => Nat.succ_pos n
  outputPrecision := fun n => 64 * (n + 1)
  separated := by
    intro x y hx hy n hsep
    have hrectangle :=
      ArctanGeometry.arctanIntegralRectangleCompute_boxes_strictly_separated
        hx.1 hx.2 hy.1 hy.2 n hsep
    have hxcontains := arctanGeom_compute_contained_in_rectangle
      hx.1 hx.2 (64 * (n + 1))
    have hycontains := arctanGeom_compute_contained_in_rectangle
      hy.1 hy.2 (64 * (n + 1))
    unfold QInterval.ContainsInterval at hxcontains hycontains
    change ((arctanGeom x).compute (64 * (n + 1))).hi <
      ((arctanGeom y).compute (64 * (n + 1))).lo
    grind

end ComputableAnalysis
