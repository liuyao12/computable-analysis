import ComputableAnalysis.ElementaryCircleAngle
import ComputableAnalysis.ArctanScheduledRegularCore
import ComputableAnalysis.FiniteInverseSearchInterface
import ComputableAnalysis.ModularForms.ExponentialConjugation

/-! Constructed principal elementary inverse branches. The inverse search
uses the rational circle chart, where each comparison is exact rational
arithmetic. Angles are obtained from the certified arctangent sampler. -/
namespace ComputableAnalysis.ElementaryAngleSearch
open ComplexRaw RiemannHilbert FunctionTheory ArctanGeometry ModularForms
open ElementaryCircleAngle SeriesLimitLaws
set_option maxHeartbeats 2000000

/-- Finite rational search data, not an assumed inverse identity. -/
structure SearchOnUnit where
  certificate : FiniteInverseSearchCertificate
  lower : 0 ≤ certificate.initialInterval.lo
  upper : certificate.initialInterval.hi ≤ 1

/-- Enough exact rational bisections for the requested error, without
excessively large midpoint denominators. -/
@[irreducible] def bracketStage (n : Nat) : Nat := Nat.log2 (2*(n+1))+1

theorem bracketStage_monotone {n m : Nat} (hnm : n ≤ m) : bracketStage n ≤ bracketStage m := by
  unfold bracketStage
  have hn : 2*(n+1) ≠ 0 := by omega
  have hm : 2*(m+1) ≠ 0 := by omega
  have hl := (Nat.le_log2 hm).2 (Nat.le_trans (Nat.log2_self_le hn) (by omega : 2*(n+1) ≤ 2*(m+1)))
  omega
def bracket (y : SearchOnUnit) (n : Nat) : QInterval :=
  y.certificate.toRealRaw.compute (bracketStage n)

theorem bracket_subinterval (y : SearchOnUnit) (n : Nat) :
    0 ≤ (bracket y n).lo ∧ (bracket y n).lo ≤ (bracket y n).hi ∧ (bracket y n).hi ≤ 1 := by
  have ho := monotoneTargetBisectionIterate_ordered
    (f := y.certificate.map) y.certificate.target y.certificate.ordered (bracketStage n)
  have hs := monotoneTargetBisectionIterate_subinterval
    (f := y.certificate.map) y.certificate.target y.certificate.ordered (bracketStage n)
  exact ⟨Rat.le_trans y.lower hs.1,ho,Rat.le_trans hs.2 y.upper⟩

theorem bracket_nested (y : SearchOnUnit) {n m : Nat} (hnm : n ≤ m) :
    (bracket y n).lo ≤ (bracket y m).lo ∧ (bracket y m).hi ≤ (bracket y n).hi := by
  apply monotoneTargetBisectionIterate_later_subinterval
    (f := y.certificate.map) y.certificate.target y.certificate.ordered
  exact bracketStage_monotone hnm

theorem bracket_contains_target (y : SearchOnUnit) (n : Nat) :
    y.certificate.map (bracket y n).lo ≤ y.certificate.target ∧
      y.certificate.target ≤ y.certificate.map (bracket y n).hi :=
  y.certificate.stage_bracket (bracketStage n)

theorem bracket_width (y : SearchOnUnit) (n : Nat) :
    (bracket y n).width ≤ 1/(((2*(n+1):Nat):Rat)) := by
  have hw := y.certificate.stage_width (bracketStage n)
  have hi : y.certificate.initialInterval.width ≤ 1 := by
    unfold QInterval.width
    have hl := y.lower
    have hu := y.upper
    grind only
  have hp : 0 < (2^(bracketStage n):Rat) := by exact_mod_cast Nat.pow_pos (by omega : 0 < 2)
  have hdiv : (bracket y n).width ≤ 1/(2^(bracketStage n):Rat) := by
    rw [show (bracket y n).width = _ from hw]
    simp only [Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hi (Rat.le_of_lt (Rat.inv_pos.mpr hp))
  apply Rat.le_trans hdiv
  have hpow : 2*(n+1) ≤ 2^(bracketStage n) := by
    have ht := Nat.lt_log2_self (n := 2*(n+1))
    unfold bracketStage
    omega
  have hrat : ((2*(n+1):Nat):Rat) ≤ (2^(bracketStage n):Rat) := by exact_mod_cast hpow
  have hl : 0 < ((2*(n+1):Nat):Rat) := by exact_mod_cast (by omega : 0 < 2*(n+1))
  let A : Rat := ((2*(n+1):Nat):Rat)
  let B : Rat := 2^(bracketStage n)
  apply Rat.le_of_mul_le_mul_right (c := A*B)
  · change (1/B)*(A*B) ≤ (1/A)*(A*B)
    calc
      (1/B)*(A*B) = A := by rw [Rat.mul_comm A B,←Rat.mul_assoc,Rat.div_mul_cancel (Rat.ne_of_gt hp),Rat.one_mul]
      _ ≤ B := hrat
      _ = (1/A)*(A*B) := by rw [←Rat.mul_assoc,Rat.div_mul_cancel (Rat.ne_of_gt hl),Rat.one_mul]
  · exact Rat.mul_pos hl hp

def midpointSlope (y : SearchOnUnit) (n : Nat) : UnitSlope where
  val := (bracket y n).midpoint
  nonnegative := Rat.le_trans (bracket_subinterval y n).1
    (QInterval.midpoint_mem (bracket_subinterval y n).2.1).1
  le_one := Rat.le_trans (QInterval.midpoint_mem (bracket_subinterval y n).2.1).2
    (bracket_subinterval y n).2.2


def image (y : SearchOnUnit) (n : Nat) : QInterval :=
  arctanScheduledRectangleOnUnit_intervalRegular.evalInterval
    (bracket y n) (bracket_subinterval y n) n

theorem image_width (y : SearchOnUnit) (n : Nat) :
    0 ≤ (image y n).width ∧ (image y n).width ≤ 1/((n+1:Nat):Rat) :=
  arctanScheduledRectangleOnUnit_intervalRegular.output_width _ _ _ (bracket_width y n)

def pointCandidate (y : SearchOnUnit) (n : Nat) : QComplex :=
  ⟨0,2*((arctanScheduledRectangleRaw (midpointSlope y n).val).compute n).midpoint⟩

def angleCandidate (y : SearchOnUnit) : ComplexRaw where
  compute n := QBox.point (pointCandidate y n)

def radius (n : Nat) : Rat := 2/((n+1:Nat):Rat)

theorem radius_nonnegative (n : Nat) : 0 ≤ radius n :=
  Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast Nat.succ_pos n)))

theorem radius_shrinks : ShrinksToZero radius := by
  apply shrinksToZero_of_natOverSuccBound (C := 2)
  intro n; exact Rat.le_refl

theorem candidate_in_image (y : SearchOnUnit) {n m : Nat} (hnm : n ≤ m) :
    2*(image y n).lo ≤ (pointCandidate y m).im ∧
      (pointCandidate y m).im ≤ 2*(image y n).hi := by
  let x := (midpointSlope y m).val
  have hx : inDomainInterval 0 1 x := ⟨(midpointSlope y m).nonnegative,(midpointSlope y m).le_one⟩
  have hs := bracket_nested y hnm
  have hm := QInterval.midpoint_mem (bracket_subinterval y m).2.1
  have hin := arctanScheduledRectangleOnUnit_intervalRegular.contains_point_values
    (bracket y n) (bracket_subinterval y n) x hx n
    (Rat.le_trans hs.1 hm.1) (Rat.le_trans hm.2 hs.2)
  have hv := arctanScheduledRectangleRaw_valid hx.1 hx.2
  have hn := hv.2.1 n m hnm
  have hp := QInterval.midpoint_mem (RealRaw.interval_order_of_valid _ hv m)
  change (image y n).lo ≤ ((arctanScheduledRectangleRaw x).compute n).lo ∧
    ((arctanScheduledRectangleRaw x).compute n).hi ≤ (image y n).hi at hin
  dsimp [pointCandidate]
  constructor <;> grind only

theorem candidate_future (y : SearchOnUnit) :
    ∀ n m, n ≤ m → ((angleCandidate y).compute m).NestedIn
      (QBox.expand ((angleCandidate y).compute n) (radius n)) := by
  intro n m hnm
  have ha := candidate_in_image y hnm
  have hb := candidate_in_image y (Nat.le_refl n)
  have hw := (image_width y n).2
  have hr := radius_nonnegative n
  change (QBox.point (pointCandidate y m)).NestedIn
    (QBox.expand (QBox.point (pointCandidate y n)) (radius n))
  simp only [QBox.NestedIn,QBox.point,QBox.expand,QComplex.le_def]
  have hre (k : Nat) : (pointCandidate y k).re = 0 := rfl
  rw [hre n,hre m]
  dsimp [radius] at *
  unfold QInterval.width at hw
  constructor <;> constructor <;> grind only

def angleValue (y : SearchOnUnit) : ComplexRaw := cauchyStabilize (angleCandidate y) radius

theorem angleValue_valid (y : SearchOnUnit) : (angleValue y).Valid := by
  apply cauchyStabilize_valid
  · intro n; exact QComplex.le_refl _
  · intro eps; refine ⟨0,?_⟩; intro n _
    exact ⟨by simpa [angleCandidate,QBox.point,QBox.width,Rat.sub_self] using Rat.le_of_lt eps.property,
      by simpa [angleCandidate,QBox.point,QBox.height,Rat.sub_self] using Rat.le_of_lt eps.property⟩
  · exact candidate_future y
  · exact radius_shrinks

theorem angleValue_contains_future (y : SearchOnUnit) {n m : Nat} (hnm : n ≤ m) :
    (QBox.point (pointCandidate y m)).NestedIn ((angleValue y).compute n) :=
  cauchyStabilize_contains_external (candidate := angleCandidate y) (radius := radius)
    (external := fun k => QBox.point (pointCandidate y k)) (candidate_future y) n m hnm

theorem small_of_samples {z : ComplexRaw} {E : Rat}
    (hs : ∀ n, ∃ p : QComplex, (z.compute n).lo ≤ p ∧ p ≤ (z.compute n).hi ∧
      qabs p.re ≤ E ∧ qabs p.im ≤ E) : Small z E := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n m; obtain ⟨p,hlo,hhi,hr,hi⟩ := hs m
    exact Rat.le_trans (Rat.le_trans (Rat.neg_le_neg hr) (neg_qabs_le_self p.re)) hhi.1
  · intro n m; obtain ⟨p,hlo,hhi,hr,hi⟩ := hs n
    exact Rat.le_trans hlo.1 (Rat.le_trans (self_le_qabs p.re) hr)
  · intro n m; obtain ⟨p,hlo,hhi,hr,hi⟩ := hs m
    exact Rat.le_trans (Rat.le_trans (Rat.neg_le_neg hi) (neg_qabs_le_self p.im)) hhi.2
  · intro n m; obtain ⟨p,hlo,hhi,hr,hi⟩ := hs n
    exact Rat.le_trans hlo.2 (Rat.le_trans (self_le_qabs p.im) hi)

theorem angleValue_small (y : SearchOnUnit) : Small (angleValue y) 2 := by
  apply small_of_samples
  intro n
  let x := midpointSlope y n
  have hp := QInterval.midpoint_mem (RealRaw.interval_order_of_valid _
    (arctanScheduledRectangleRaw_valid x.nonnegative x.le_one) n)
  have hl := arctanIntegralRectangleCompute_lower_nonnegative x.nonnegative (arctanScheduledStage n)
  have hh := arctanIntegralRectangleCompute_upper_le_input x.nonnegative (arctanScheduledStage n)
  have hx := x.le_one
  refine ⟨pointCandidate y n,(angleValue_contains_future y (Nat.le_refl n)).1,
    (angleValue_contains_future y (Nat.le_refl n)).2,?_,?_⟩
  · change qabs (0:Rat) ≤ 2; decide
  · have hp' : (ArctanGeometry.arctanIntegralRectangleCompute x.val (arctanScheduledStage n)).lo ≤
        ((arctanScheduledRectangleRaw x.val).compute n).midpoint ∧
        ((arctanScheduledRectangleRaw x.val).compute n).midpoint ≤
        (ArctanGeometry.arctanIntegralRectangleCompute x.val (arctanScheduledStage n)).hi := hp
    apply qabs_le_of_neg_le_le
    · change -(2:Rat) ≤ 2*((arctanScheduledRectangleRaw x.val).compute n).midpoint
      grind only
    · change 2*((arctanScheduledRectangleRaw x.val).compute n).midpoint ≤ 2
      grind only

def scheduledAngle (y : SearchOnUnit) (N : Nat) : Scalar :=
  ⟨imaginaryAxis (RealRaw.scaleRat 2 (arctanScheduledRectangleRaw (midpointSlope y N).val)),
    imaginaryAxis_valid (RealRaw.scaleRat_valid
      (arctanScheduledRectangleRaw_valid (midpointSlope y N).nonnegative (midpointSlope y N).le_one))⟩

theorem scheduledAngle_agrees (y : SearchOnUnit) (N : Nat) :
    (scheduledAngle y N).val.Equiv (imaginaryAngle (midpointSlope y N)).val :=
  imaginaryAxis_equiv (RealRaw.scaleRat_valid (arctanScheduledRectangleRaw_valid (midpointSlope y N).nonnegative (midpointSlope y N).le_one))
    (twiceArctangent_valid (midpointSlope y N)) (RealRaw.scaleRat_equiv
    (arctanScheduledRectangleRaw_equiv_arctanGeom (midpointSlope y N).nonnegative (midpointSlope y N).le_one))

theorem scheduledAngle_in_image (y : SearchOnUnit) {N M : Nat} (hNM : N ≤ M) :
    2*(image y N).lo ≤ ((scheduledAngle y N).val.compute M).lo.im ∧
      ((scheduledAngle y N).val.compute M).hi.im ≤ 2*(image y N).hi := by
  let x := midpointSlope y N
  have hm := QInterval.midpoint_mem (bracket_subinterval y N).2.1
  have hin := arctanScheduledRectangleOnUnit_intervalRegular.contains_point_values
    (bracket y N) (bracket_subinterval y N) x.val ⟨x.nonnegative,x.le_one⟩ N hm.1 hm.2
  have hv := arctanScheduledRectangleRaw_valid x.nonnegative x.le_one
  have hn := hv.2.1 N M hNM
  change (image y N).lo ≤ ((arctanScheduledRectangleRaw x.val).compute N).lo ∧
    ((arctanScheduledRectangleRaw x.val).compute N).hi ≤ (image y N).hi at hin
  simp only [scheduledAngle,imaginaryAxis,mulI,ofRealRaw,Rat.neg_zero,RealRaw.scaleRat,RealRaw.scaleRatCompute,
    if_pos (show (0:Rat)≤2 by decide)]
  change 2*(image y N).lo ≤ 2*((arctanScheduledRectangleRaw x.val).compute M).lo ∧
    2*((arctanScheduledRectangleRaw x.val).compute M).hi ≤ 2*(image y N).hi
  constructor <;> grind only

theorem angleValue_scheduled_error (y : SearchOnUnit) (N : Nat) :
    Small (sub (angleValue y) (scheduledAngle y N).val) (radius N) := by
  apply small_of_samples
  intro k
  let M := max N k
  have hNk : N ≤ M := Nat.le_max_left _ _
  have hk : k ≤ M := Nat.le_max_right _ _
  let p := pointCandidate y M
  let q := ((scheduledAngle y N).val.compute M).center
  have hp := angleValue_contains_future y hk
  have hq := QBox.center_mem (valid_ordered (scheduledAngle y N).property M)
  have hn := valid_nestedIn (scheduledAngle y N).property hk
  have hqk : ((scheduledAngle y N).val.compute k).lo ≤ q ∧ q ≤ ((scheduledAngle y N).val.compute k).hi :=
    ⟨QComplex.le_trans hn.1 hq.1,QComplex.le_trans hq.2 hn.2⟩
  have hpI := candidate_in_image y hNk
  have hqI := scheduledAngle_in_image y hNk
  have hw := (image_width y N).2
  have hr := radius_nonnegative N
  have hs := QBox.add_contains hp.1 hp.2 (QBox.neg_contains hqk).1 (QBox.neg_contains hqk).2
  refine ⟨QComplex.sub p q,hs.1,hs.2,?_,?_⟩
  · have hre : q.re = 0 := by
      simp [q,scheduledAngle,imaginaryAxis,mulI,ofRealRaw,QBox.center,Rat.neg_zero,Rat.add_zero,Rat.div_def,Rat.zero_mul]
    change qabs (0+ -q.re) ≤ radius N
    rw [hre]; simpa [Rat.neg_zero,Rat.add_zero,qabs] using hr
  · have hqi : ((scheduledAngle y N).val.compute M).lo.im ≤ q.im ∧
        q.im ≤ ((scheduledAngle y N).val.compute M).hi.im := ⟨hq.1.2,hq.2.2⟩
    apply qabs_le_of_neg_le_le
    all_goals change _ ≤ _
    all_goals simp only [QComplex.sub,QComplex.add,QComplex.neg]
    all_goals change _ ≤ _
    all_goals unfold QInterval.width at hw; dsimp [radius]; grind only

theorem angleValue_geometric_error (y : SearchOnUnit) (N : Nat) :
    Small (sub (angleValue y) (imaginaryAngle (midpointSlope y N)).val) (radius N) :=
  Small.congr (sub_valid (angleValue_valid y) (scheduledAngle y N).property)
    (sub_valid (angleValue_valid y) (imaginaryAngle (midpointSlope y N)).property)
    (FunctionTheory.sub_congr (equiv_refl _ (angleValue_valid y)) (scheduledAngle_agrees y N))
    (angleValue_scheduled_error y N)

def angleScalar (y : SearchOnUnit) : Scalar := ⟨angleValue y,angleValue_valid y⟩

theorem angle_exponential_circle_error (y : SearchOnUnit) (N : Nat) :
    Small (sub (entireExponentialValue (angleScalar y)).val
      (ofQComplex (GeometricRotationODE.pointComplex (midpointSlope y N).val)))
      (exponentialQuadraticConstant geometricFactorRadius*radius N) := by
  have hb := entireExponential_lipschitz geometricFactorRadius
    (imaginaryAngle (midpointSlope y N)) (angleScalar y)
    ⟨2,by decide,by decide,imaginaryAngle_small _⟩
    ⟨2,by decide,by decide,angleValue_small y⟩
    (radius N) (radius_nonnegative N) (angleValue_geometric_error y N)
  change Small _ (exponentialQuadraticConstant geometricFactorRadius*radius N) at hb
  exact Small.congr (sub_valid (entireExponentialValue _).property (entireExponentialValue _).property)
    (sub_valid (entireExponentialValue _).property (ofQComplex_valid _))
    (FunctionTheory.sub_congr (equiv_refl _ (entireExponentialValue _).property)
      (exponential_twiceArctangent (midpointSlope y N))) hb

theorem angleValue_axis (y : SearchOnUnit) :
    (imaginaryAxis ((angleValue y).imagPart)).Equiv (angleValue y) := by
  intro n
  have hp := angleValue_contains_future y (Nat.le_refl n)
  have hi := QBox.center_mem (valid_ordered (angleValue_valid y) n)
  let p : QComplex := ⟨0,((angleValue y).compute n).center.im⟩
  have h0 : ((angleValue y).compute n).lo.re ≤ 0 ∧ 0 ≤ ((angleValue y).compute n).hi.re :=
    ⟨hp.1.1,hp.2.1⟩
  apply (compareAt_overlap_iff _ _ n n).mpr
  exact QBox.overlaps_of_common_point (point := p)
    ⟨⟨Rat.le_refl,hi.1.2⟩,⟨Rat.le_refl,hi.2.2⟩⟩
    ⟨⟨h0.1,hi.1.2⟩,⟨h0.2,hi.2.2⟩⟩


end ComputableAnalysis.ElementaryAngleSearch
