import ComputableAnalysis.Calculus

/-!
# Function-specific integral enclosures

A point evaluator is not an integral. This interface records actual partitions,
outer enclosures of every point-value rectangle on each whole cell, and the
literal sum of these enclosures times the cell lengths. Monotonicity or a
function-specific interval estimate supplies the ranges. No parametrized path,
completed scalar field, or generic existence theorem is used.

`CandidateFor` only certifies a number. `EnclosureConstructionFor` additionally
certifies the finite construction for the stated function.
-/
namespace ComputableAnalysis.Integral

/-- The finite, function-specific evidence beneath a real integral. -/
structure EnclosurePlanFor (F : FunctionOnInterval) where
  partition : Nat → RationalPartition F.lower F.upper
  range : (n k : Nat) → k < (partition n).pieces → QInterval
  precision : (n k : Nat) → k < (partition n).pieces → Nat
  ordered : ∀ n k hk, 0 ≤ (range n k hk).width
  contains : ∀ n k hk x (hx : inDomainInterval F.lower F.upper x),
    ((partition n).cell k hk).contains x →
    (range n k hk).ContainsInterval (F.compute x hx (precision n k hk))

namespace EnclosurePlanFor

def stage {F : FunctionOnInterval} (p : EnclosurePlanFor F) (n : Nat) : QInterval :=
  (p.partition n).boundIntegralSum (p.range n)

def raw {F : FunctionOnInterval} (p : EnclosurePlanFor F) : RealRaw where
  compute := p.stage

/-- The finite enclosure retains every later refinement of the point value. -/
theorem contains_later {F : FunctionOnInterval} (p : EnclosurePlanFor F)
    (n k : Nat) (hk : k < (p.partition n).pieces)
    (x : Rat) (hx : inDomainInterval F.lower F.upper x)
    (hc : ((p.partition n).cell k hk).contains x)
    (m : Nat) (hm : p.precision n k hk ≤ m) :
    (p.range n k hk).ContainsInterval (F.compute x hx m) := by
  have h := p.contains n k hk x hx hc
  have hv := F.valid_on x (F.defined_on x hx)
  have hn := hv.2.1 (p.precision n k hk) m hm
  exact ⟨Rat.le_trans h.1 hn.1, Rat.le_trans hn.2.2 h.2⟩

end EnclosurePlanFor

/-- A literal whole-cell enclosure sum with a proved nesting and width schedule.
The integrand is a substantive parameter, unlike in `CandidateFor`. -/
structure EnclosureConstructionFor (F : FunctionOnInterval)
    extends EnclosurePlanFor F where
  certificate : RealRaw.ValidCompute toEnclosurePlanFor.stage

namespace EnclosureConstructionFor

def value {F : FunctionOnInterval} (c : EnclosureConstructionFor F) : RealRaw :=
  c.toEnclosurePlanFor.raw

theorem valid {F : FunctionOnInterval} (c : EnclosureConstructionFor F) :
    c.value.Valid := c.certificate

def toCandidate {F : FunctionOnInterval} (c : EnclosureConstructionFor F) :
    CandidateFor F := ⟨c.toEnclosurePlanFor.stage, c.certificate⟩

/-- Existing interval-range schedules preserve their complete local evidence. -/
def ofIntervalRegularSchedule
    {F : FunctionOnInterval} {regular : IntervalRegularOn F}
    {hab : F.lower ≤ F.upper}
    (s : IntervalRegularDarbouxSchedule F regular hab) : EnclosureConstructionFor F where
  partition n := RationalPartition.uniform F.lower F.upper (s.pieces n) (s.pieces_pos n) hab
  range n k hk := intervalRegularDarbouxRange F regular
    (RationalPartition.uniform F.lower F.upper (s.pieces n) (s.pieces_pos n) hab)
    k hk (s.evalPrecision n)
  precision n _ _ := s.evalPrecision n
  ordered := by
    intro n k hk
    let P := RationalPartition.uniform F.lower F.upper (s.pieces n) (s.pieces_pos n) hab
    let C := P.cell k hk
    have hx : inDomainInterval F.lower F.upper C.lower :=
      ⟨C.lower_mem, Rat.le_trans C.ordered C.upper_mem⟩
    have hr := intervalRegularDarbouxRange_contains_point_value F regular P k hk
      C.lower (Rat.le_refl) C.ordered (s.evalPrecision n)
    have hv := (F.valid_on C.lower (F.defined_on C.lower hx)).1 (s.evalPrecision n)
    change 0 ≤ (F.compute C.lower hx (s.evalPrecision n)).width at hv
    unfold QInterval.ContainsInterval QInterval.width at *
    grind only
  contains := by
    intro n k hk x hx hc
    exact intervalRegularDarbouxRange_contains_point_value F regular _ k hk x
      hc.1 hc.2 (s.evalPrecision n)
  certificate := intervalRegularDarbouxScheduleRaw_valid s

/-- Endpoint-ordered monotone rectangles are an instance of the same rule. -/
def ofNondecreasingSchedule
    {F : FunctionOnInterval} {regular : IntervalRegularOn F}
    {mono : NondecreasingOnInterval F} {hab : F.lower ≤ F.upper}
    (s : MonotoneDarbouxSchedule F regular mono hab)
    (ordered : EndpointOrderedNondecreasingOnInterval F) : EnclosureConstructionFor F where
  partition n := RationalPartition.uniform F.lower F.upper (s.pieces n) (s.pieces_pos n) hab
  range n k hk := nondecreasingDarbouxRange F
    (RationalPartition.uniform F.lower F.upper (s.pieces n) (s.pieces_pos n) hab)
    k hk (s.evalPrecision n)
  precision n _ _ := s.evalPrecision n
  ordered := by
    intro n k hk
    exact nondecreasingDarbouxRange_width_nonneg F mono _ k hk (s.evalPrecision n)
  contains := by
    intro n k hk x hx hc
    exact endpointOrderedNondecreasingDarbouxRange_contains_point_value
      F ordered _ k hk x hx hc.1 hc.2 (s.evalPrecision n)
  certificate := monotoneDarbouxScheduleRaw_valid s

/-- The decreasing endpoint construction needs no change of integration variable. -/
def ofNonincreasingSchedule
    {F : FunctionOnInterval} {regular : IntervalRegularOn F}
    {mono : NonincreasingOnInterval F} {hab : F.lower ≤ F.upper}
    (s : NonincreasingDarbouxSchedule F regular mono hab)
    (ordered : EndpointOrderedNonincreasingOnInterval F) : EnclosureConstructionFor F where
  partition n := RationalPartition.uniform F.lower F.upper (s.pieces n) (s.pieces_pos n) hab
  range n k hk := nonincreasingDarbouxRange F
    (RationalPartition.uniform F.lower F.upper (s.pieces n) (s.pieces_pos n) hab)
    k hk (s.evalPrecision n)
  precision n _ _ := s.evalPrecision n
  ordered := by
    intro n k hk
    exact nonincreasingDarbouxRange_width_nonneg F mono _ k hk (s.evalPrecision n)
  contains := by
    intro n k hk x hx hc
    exact endpointOrderedNonincreasingDarbouxRange_contains_point_value
      F ordered _ k hk x hx hc.1 hc.2 (s.evalPrecision n)
  certificate := nonincreasingDarbouxScheduleRaw_valid s

/-- One actual interval, one constant range, and its rectangle product. -/
def constantPlan (c a b : Rat) (hab : a ≤ b) :
    EnclosurePlanFor (FunctionOnInterval.exactRat (fun _ => c) a b) where
  partition _ := RationalPartition.uniform a b 1 (by decide) hab
  range _ _ _ := ⟨c,c⟩
  precision _ _ _ := 0
  ordered := by intro n k hk; change 0 ≤ c-c; grind
  contains := by intro n k hk x hx hc; exact ⟨Rat.le_refl, Rat.le_refl⟩

theorem constantPlan_stage (c a b : Rat) (hab : a ≤ b) (n : Nat) :
    (constantPlan c a b hab).stage n = ⟨(b-a)*c, (b-a)*c⟩ := by
  simp [constantPlan, EnclosurePlanFor.stage, RationalPartition.boundIntegralSum,
    RationalPartition.boundIntegralTerm, RationalPartition.uniform,
    RationalPartition.cell, RationalSubinterval.scaleBound, leftPoint,
    mesh, QInterval.addInterval, QInterval.scaleByRat, RationalSubinterval.width] <;> grind

def constant (c a b : Rat) (hab : a ≤ b) :
    EnclosureConstructionFor (FunctionOnInterval.exactRat (fun _ => c) a b) where
  toEnclosurePlanFor := constantPlan c a b hab
  certificate := by
    have he : (constantPlan c a b hab).stage = (RealRaw.ofRat ((b-a)*c)).compute := by
      funext n; exact constantPlan_stage c a b hab n
    rw [he]; exact RealRaw.ofRat_valid _

theorem constant_value (c a b : Rat) (hab : a ≤ b) :
    (constant c a b hab).value.Equiv (RealRaw.ofRat ((b-a)*c)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps ((constantPlan c a b hab).stage n) _
  rw [constantPlan_stage]
  exact ⟨Rat.le_refl, Rat.le_refl⟩

end EnclosureConstructionFor

/-- A fast or stabilized computation is an integral only with a comparison to
shrinking whole-cell enclosure sums for that same integrand. -/
structure EnclosureRealizationFor (F : FunctionOnInterval) where
  plan : EnclosurePlanFor F
  widths_shrink : RealRaw.WidthsShrinkToZero plan.stage
  value : RealRaw
  valid : value.Valid
  agreement : value.Equiv plan.raw

/-- Derivative-bound FTC already supplies whole-cell ranges. This adapter keeps
that evidence instead of discarding it into the former two-field interface. -/
def enclosurePlanOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hdF : dF.Valid) (hdomain : ∀ x, inDomainInterval a b x → dF.domain x) :
    EnclosurePlanFor (FunctionOnInterval.ofRealFunRaw dF a b hdomain hdF) where
  partition n := h.choosePartition (precisionAtStage n)
  range n k hk := (h.derivativeBound (precisionAtStage n) k hk).bound
    (h.chooseBoundStage (precisionAtStage n))
  precision n k hk := (h.derivativeBound (precisionAtStage n) k hk).evalPrecision
    (h.chooseBoundStage (precisionAtStage n))
  ordered n k hk := (h.derivativeBound (precisionAtStage n) k hk).bound_ordered _
  contains n k hk x hx hc :=
    (h.derivativeBound (precisionAtStage n) k hk).contains_values _ x hc

/-- Endpoint evaluation is permitted after the whole-cell FTC comparison. -/
def enclosureRealizationOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveDerivativeBoundFTC F dF a b)
    (hdF : dF.Valid) (hdomain : ∀ x, inDomainInterval a b x → dF.domain x)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b)) :
    EnclosureRealizationFor (FunctionOnInterval.ofRealFunRaw dF a b hdomain hdF) where
  plan := enclosurePlanOfEffectiveFTC h hdF hdomain
  widths_shrink := h.toDerivativeBoundFTC.boundedIntegralRaw_widths_shrink
  value := endpointDifferenceRaw F a b hendpoint
  valid := hendpoint
  agreement := RealRaw.equiv_symm (h.boundedIntegralRaw_equiv_endpointDifference hendpoint)

end ComputableAnalysis.Integral
