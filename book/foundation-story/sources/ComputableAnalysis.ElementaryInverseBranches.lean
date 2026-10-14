import ComputableAnalysis.ElementaryAngleSearch
import ComputableAnalysis.ArctanScheduledRegularCore
import ComputableAnalysis.FiniteInverseSearchInterface
import ComputableAnalysis.ModularForms.ExponentialConjugation

/-! Constructed principal elementary inverse branches. The inverse search
uses the rational circle chart, where each comparison is exact rational
arithmetic. Angles are obtained from the certified arctangent sampler. -/
namespace ComputableAnalysis.ElementaryInverseBranches
open ComplexRaw RiemannHilbert FunctionTheory ArctanGeometry ModularForms
open ElementaryCircleAngle SeriesLimitLaws
set_option maxHeartbeats 2000000

def sineChart (t : Rat) : Rat := 2*t/(1+t*t)

theorem denominator_pos (t : Rat) : 0 < 1+t*t := by
  have ht : 0 ≤ t*t := by
    by_cases h : 0 ≤ t
    · exact Rat.mul_nonneg h h
    · have hn : 0 ≤ -t := by grind
      have hp := Rat.mul_nonneg hn hn
      grind only
  grind only

theorem sineChart_difference (a b : Rat) :
    sineChart b-sineChart a =
      2*(b-a)*(1-a*b)/((1+a*a)*(1+b*b)) := by
  have ha := Rat.mul_inv_cancel (1+a*a) (Rat.ne_of_gt (denominator_pos a))
  have hb := Rat.mul_inv_cancel (1+b*b) (Rat.ne_of_gt (denominator_pos b))
  unfold sineChart
  rw [Rat.div_def,Rat.div_def,Rat.div_def,Rat.inv_mul_rev]
  grind only

theorem sineChart_order_lipschitz {a b : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    0 ≤ sineChart b-sineChart a ∧ sineChart b-sineChart a ≤ 2*(b-a) := by
  have hb0 : 0 ≤ b := Rat.le_trans ha hab
  have ha1 : a ≤ 1 := Rat.le_trans hab hb
  have hp := Rat.mul_nonneg ha hb0
  have hpu := rat_mul_le_mul_of_nonneg ha ha1 hb0 hb
  have ha2 := Rat.mul_nonneg ha ha
  have hb2 := Rat.mul_nonneg hb0 hb0
  have hd : 0 < (1+a*a)*(1+b*b) := Rat.mul_pos (denominator_pos a) (denominator_pos b)
  have hdi := Rat.le_of_lt (Rat.inv_pos.mpr hd)
  have hdc := Rat.mul_inv_cancel ((1+a*a)*(1+b*b)) (Rat.ne_of_gt hd)
  have hden : 1 ≤ (1+a*a)*(1+b*b) := by
    have hmul := Rat.mul_nonneg ha2 hb2
    grind only
  have hinv : ((1+a*a)*(1+b*b))⁻¹ ≤ 1 := by
    have hm := Rat.mul_le_mul_of_nonneg_right hden hdi
    grind only
  have hdiff : 0 ≤ b-a := by grind only
  rw [sineChart_difference,Rat.div_def]
  have hc : 0 ≤ 1-a*b := by grind only
  have hcu : 1-a*b ≤ 1 := by grind only
  have hn := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide : (0:Rat)≤2) hdiff) hc) hdi
  have hm := rat_mul_le_mul_of_nonneg hc hcu hdi hinv
  have hs := Rat.mul_le_mul_of_nonneg_left hm (Rat.mul_nonneg (by decide : (0:Rat)≤2) hdiff)
  constructor <;> grind only

structure UnitTarget where
  val : Rat
  nonnegative : 0 ≤ val
  le_one : val ≤ 1

def search (y : UnitTarget) : FiniteInverseSearchCertificate where
  map := sineChart
  target := y.val
  initialInterval := ⟨0,1⟩
  stage := 0
  ordered := by decide
  lower_bracket := by rw [show sineChart 0 = 0 by decide +kernel]; exact y.nonnegative
  upper_bracket := by rw [show sineChart 1 = 1 by decide +kernel]; exact y.le_one

def angleSearch (y : UnitTarget) : ElementaryAngleSearch.SearchOnUnit where
  certificate := search y
  lower := Rat.le_refl
  upper := Rat.le_refl

abbrev bracketStage := ElementaryAngleSearch.bracketStage

abbrev bracket (y : UnitTarget) (n : Nat) : QInterval := ElementaryAngleSearch.bracket (angleSearch y) n

theorem bracket_subinterval (y : UnitTarget) (n : Nat) :
    0 ≤ (bracket y n).lo ∧ (bracket y n).lo ≤ (bracket y n).hi ∧ (bracket y n).hi ≤ 1 := ElementaryAngleSearch.bracket_subinterval (angleSearch y) n

theorem bracket_nested (y : UnitTarget) {n m : Nat} (hnm : n ≤ m) :
    (bracket y n).lo ≤ (bracket y m).lo ∧ (bracket y m).hi ≤ (bracket y n).hi := ElementaryAngleSearch.bracket_nested (angleSearch y) hnm

theorem bracket_contains_target (y : UnitTarget) (n : Nat) :
    sineChart (bracket y n).lo ≤ y.val ∧ y.val ≤ sineChart (bracket y n).hi := ElementaryAngleSearch.bracket_contains_target (angleSearch y) n

theorem bracket_width (y : UnitTarget) (n : Nat) :
    (bracket y n).width ≤ 1/(((2*(n+1):Nat):Rat)) := ElementaryAngleSearch.bracket_width (angleSearch y) n

abbrev midpointSlope (y : UnitTarget) (n : Nat) : UnitSlope := ElementaryAngleSearch.midpointSlope (angleSearch y) n

abbrev image (y : UnitTarget) (n : Nat) : QInterval := ElementaryAngleSearch.image (angleSearch y) n

theorem image_width (y : UnitTarget) (n : Nat) :
    0 ≤ (image y n).width ∧ (image y n).width ≤ 1/((n+1:Nat):Rat) := ElementaryAngleSearch.image_width (angleSearch y) n

abbrev pointCandidate (y : UnitTarget) (n : Nat) : QComplex := ElementaryAngleSearch.pointCandidate (angleSearch y) n

abbrev angleCandidate (y : UnitTarget) : ComplexRaw := ElementaryAngleSearch.angleCandidate (angleSearch y)

abbrev radius (n : Nat) : Rat := ElementaryAngleSearch.radius n

theorem radius_nonnegative (n : Nat) : 0 ≤ radius n := ElementaryAngleSearch.radius_nonnegative n

theorem radius_shrinks : ShrinksToZero radius := ElementaryAngleSearch.radius_shrinks

theorem candidate_in_image (y : UnitTarget) {n m : Nat} (hnm : n ≤ m) :
    2*(image y n).lo ≤ (pointCandidate y m).im ∧
      (pointCandidate y m).im ≤ 2*(image y n).hi := ElementaryAngleSearch.candidate_in_image (angleSearch y) hnm

theorem candidate_future (y : UnitTarget) :
    ∀ n m, n ≤ m → ((angleCandidate y).compute m).NestedIn
      (QBox.expand ((angleCandidate y).compute n) (radius n)) := ElementaryAngleSearch.candidate_future (angleSearch y)

abbrev angleValue (y : UnitTarget) : ComplexRaw := ElementaryAngleSearch.angleValue (angleSearch y)

theorem angleValue_valid (y : UnitTarget) : (angleValue y).Valid := ElementaryAngleSearch.angleValue_valid (angleSearch y)

theorem angleValue_contains_future (y : UnitTarget) {n m : Nat} (hnm : n ≤ m) :
    (QBox.point (pointCandidate y m)).NestedIn ((angleValue y).compute n) := ElementaryAngleSearch.angleValue_contains_future (angleSearch y) hnm

theorem small_of_samples {z : ComplexRaw} {E : Rat}
    (hs : ∀ n, ∃ p : QComplex, (z.compute n).lo ≤ p ∧ p ≤ (z.compute n).hi ∧
      qabs p.re ≤ E ∧ qabs p.im ≤ E) : Small z E := ElementaryAngleSearch.small_of_samples hs

theorem angleValue_small (y : UnitTarget) : Small (angleValue y) 2 := ElementaryAngleSearch.angleValue_small (angleSearch y)

abbrev scheduledAngle (y : UnitTarget) (N : Nat) : Scalar := ElementaryAngleSearch.scheduledAngle (angleSearch y) N

theorem scheduledAngle_agrees (y : UnitTarget) (N : Nat) :
    (scheduledAngle y N).val.Equiv (imaginaryAngle (midpointSlope y N)).val := ElementaryAngleSearch.scheduledAngle_agrees (angleSearch y) N

theorem scheduledAngle_in_image (y : UnitTarget) {N M : Nat} (hNM : N ≤ M) :
    2*(image y N).lo ≤ ((scheduledAngle y N).val.compute M).lo.im ∧
      ((scheduledAngle y N).val.compute M).hi.im ≤ 2*(image y N).hi := ElementaryAngleSearch.scheduledAngle_in_image (angleSearch y) hNM

theorem angleValue_scheduled_error (y : UnitTarget) (N : Nat) :
    Small (sub (angleValue y) (scheduledAngle y N).val) (radius N) := ElementaryAngleSearch.angleValue_scheduled_error (angleSearch y) N

theorem angleValue_geometric_error (y : UnitTarget) (N : Nat) :
    Small (sub (angleValue y) (imaginaryAngle (midpointSlope y N)).val) (radius N) := ElementaryAngleSearch.angleValue_geometric_error (angleSearch y) N

theorem midpoint_target_error (y : UnitTarget) (N : Nat) :
    qabs (sineChart (midpointSlope y N).val-y.val) ≤ 2*(bracket y N).width := by
  have hb := bracket_subinterval y N
  have hm := QInterval.midpoint_mem hb.2.1
  have ht := bracket_contains_target y N
  have hlo := sineChart_order_lipschitz hb.1 hm.1 (Rat.le_trans hm.2 hb.2.2)
  have hhi := sineChart_order_lipschitz (Rat.le_trans hb.1 hm.1) hm.2 hb.2.2
  have hfull := sineChart_order_lipschitz hb.1 hb.2.1 hb.2.2
  have hlo' : sineChart (bracket y N).lo ≤ sineChart (midpointSlope y N).val := by
    change sineChart (bracket y N).lo ≤ sineChart (bracket y N).midpoint
    grind only
  have hhi' : sineChart (midpointSlope y N).val ≤ sineChart (bracket y N).hi := by
    change sineChart (bracket y N).midpoint ≤ sineChart (bracket y N).hi
    grind only
  have hc := qabs_sub_le_of_common_bounds hlo' hhi' ht.1 ht.2
  unfold QInterval.width
  exact Rat.le_trans hc hfull.2


abbrev angleScalar (y : UnitTarget) : Scalar := ElementaryAngleSearch.angleScalar (angleSearch y)

theorem angle_exponential_circle_error (y : UnitTarget) (N : Nat) :
    Small (sub (entireExponentialValue (angleScalar y)).val
      (ofQComplex (GeometricRotationODE.pointComplex (midpointSlope y N).val)))
      (exponentialQuadraticConstant geometricFactorRadius*radius N) := ElementaryAngleSearch.angle_exponential_circle_error (angleSearch y) N

theorem angle_exponential_sine_inverse (y : UnitTarget) :
    (entireExponentialValue (angleScalar y)).val.imagPart.Equiv (RealRaw.ofRat y.val) := by
  let f := (entireExponentialValue (angleScalar y)).val
  let z := sub (imaginaryAxis f.imagPart) (ofQComplex ⟨0,y.val⟩)
  let C := exponentialQuadraticConstant geometricFactorRadius
  have hC : 0 ≤ C := exponentialQuadraticConstant_nonnegative _
  have hs : ShrinksToZero (fun N => (C+1)*radius N) :=
    shrinks_scale radius radius_shrinks (C+1) (Rat.add_nonneg hC (by decide))
  have hz : Small z 0 := by
    apply small_closed z 0 (fun N => (C+1)*radius N) hs
    intro N
    have he := angle_exponential_circle_error y N
    have ht := midpoint_target_error y N
    have hb := bracket_width y N
    have hr := radius_nonnegative N
    have hl := neg_qabs_le_self (sineChart (midpointSlope y N).val-y.val)
    have hu := self_le_qabs (sineChart (midpointSlope y N).val-y.val)
    refine ⟨?_,?_,?_,?_⟩ <;> intro n m <;>
      simp only [z,sub,add,neg,imaginaryAxis,mulI,ofRealRaw,ofQComplex,QBox.add,QBox.neg,
        QBox.point,QComplex.add,QComplex.neg,realPart,imagPart,RealRaw.ofRat,
        Rat.zero_add,Rat.add_zero,Rat.neg_zero]
    · change -((C+1)*radius N) ≤ 0
      have hm := Rat.mul_nonneg (Rat.add_nonneg hC (by decide : (0:Rat)≤1)) hr
      grind only
    · change (0:Rat) ≤ (C+1)*radius N
      exact Rat.mul_nonneg (Rat.add_nonneg hC (by decide)) hr
    · have hi := he.2.2.1 n m
      simp only [sub,add,neg,ofQComplex,QBox.add,QBox.neg,QBox.point,QComplex.add,QComplex.neg,
        imagPart,RealRaw.ofRat] at hi
      change -(C*radius N) ≤ (f.compute m).hi.im+ -sineChart (midpointSlope y N).val at hi
      change -((C+1)*radius N) ≤ (f.compute m).hi.im+ -y.val
      dsimp [radius,ElementaryAngleSearch.radius] at *
      have hden : ((2*(N+1):Nat):Rat) = 2*((N+1:Nat):Rat) := by rw [Rat.natCast_mul]; rfl
      rw [hden,Rat.div_def,Rat.inv_mul_rev] at hb
      unfold QInterval.width at ht hb
      have h2 : (2:Rat)⁻¹=1/2 := by decide +kernel
      rw [h2] at hb
      grind only
    · have hi := he.2.2.2 n m
      simp only [sub,add,neg,ofQComplex,QBox.add,QBox.neg,QBox.point,QComplex.add,QComplex.neg,
        imagPart,RealRaw.ofRat] at hi
      change (f.compute n).lo.im+ -sineChart (midpointSlope y N).val ≤ C*radius N at hi
      change (f.compute n).lo.im+ -y.val ≤ (C+1)*radius N
      dsimp [radius,ElementaryAngleSearch.radius] at *
      have hden : ((2*(N+1):Nat):Rat) = 2*((N+1:Nat):Rat) := by rw [Rat.natCast_mul]; rfl
      rw [hden,Rat.div_def,Rat.inv_mul_rev] at hb
      unfold QInterval.width at ht hb
      have h2 : (2:Rat)⁻¹=1/2 := by decide +kernel
      rw [h2] at hb
      grind only
  exact imagPart_equiv (equiv_of_small_sub_zero (imaginaryAxis f.imagPart) (ofQComplex ⟨0,y.val⟩) hz)

def arcsinePositiveValue (y : UnitTarget) : RealRaw := (angleValue y).imagPart

theorem arcsinePositiveValue_valid (y : UnitTarget) : (arcsinePositiveValue y).Valid :=
  imagPart_valid (angleValue_valid y)

theorem angleValue_axis (y : UnitTarget) :
    (imaginaryAxis (arcsinePositiveValue y)).Equiv (angleValue y) := ElementaryAngleSearch.angleValue_axis (angleSearch y)

/-- Evaluation at a represented angle is derived from the rational exponential
sampler; it is not the elementary function's primary input interface. -/
def sineAtAngle (x : RealRaw) (hx : x.Valid) : RealRaw :=
  (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val.imagPart

theorem sineAtAngle_valid (x : RealRaw) (hx : x.Valid) : (sineAtAngle x hx).Valid :=
  imagPart_valid (entireExponentialValue _).property

theorem sineAtAngle_congr {x y : RealRaw} (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    (sineAtAngle x hx).Equiv (sineAtAngle y hy) :=
  imagPart_equiv (entireExponentialValue_congr _ _ (imaginaryAxis_equiv hx hy hxy))

theorem arcsinePositive_sine_inverse (y : UnitTarget) :
    (sineAtAngle (arcsinePositiveValue y) (arcsinePositiveValue_valid y)).Equiv (RealRaw.ofRat y.val) :=
  RealRaw.equiv_trans (sineAtAngle_valid _ _) (imagPart_valid (entireExponentialValue _).property)
    (RealRaw.ofRat_valid _) (imagPart_equiv
      (entireExponentialValue_congr _ _ (angleValue_axis y))) (angle_exponential_sine_inverse y)


theorem sineAtAngle_neg (x : RealRaw) (hx : x.Valid) :
    (sineAtAngle (RealRaw.neg x) (RealRaw.neg_valid hx)).Equiv (RealRaw.neg (sineAtAngle x hx)) := by
  let z : Scalar := ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩
  let w : Scalar := ⟨imaginaryAxis (RealRaw.neg x),imaginaryAxis_valid (RealRaw.neg_valid hx)⟩
  have hi : (exponentialConjugateInput z).val.Equiv w.val := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    simp only [exponentialConjugateInput,z,w,conj,imaginaryAxis,mulI,ofRealRaw,
      QBox.conj,RealRaw.neg,RealRaw.negCompute,Rat.neg_zero,Rat.neg_neg,QBox.Overlaps,QComplex.le_def]
    have ho := RealRaw.interval_order_of_valid x hx n
    unfold QInterval.width at ho
    constructor <;> constructor <;> grind only
  have he := equiv_trans (conj_valid _ (entireExponentialValue z).property)
    (entireExponentialValue (exponentialConjugateInput z)).property (entireExponentialValue w).property
    (entireExponential_conjugation z) (entireExponentialValue_congr _ _ hi)
  exact RealRaw.equiv_symm (imagPart_equiv he)

def arcsineValue (x : Rat) (hx : Elementary.arcsinDomain x) : RealRaw :=
  if h0 : 0 ≤ x then arcsinePositiveValue ⟨x,h0,hx.2⟩
  else RealRaw.neg (arcsinePositiveValue ⟨-x,by grind only,by have h := hx.1; grind only⟩)

theorem arcsineValue_valid (x : Rat) (hx : Elementary.arcsinDomain x) : (arcsineValue x hx).Valid := by
  unfold arcsineValue
  split
  · exact arcsinePositiveValue_valid _
  · exact RealRaw.neg_valid (arcsinePositiveValue_valid _)

/-- The exact sine inverse law for every rational target in the closed unit
interval. Search evidence and shrinking schedules are constructed internally. -/
theorem arcsine_sine_inverse (x : Rat) (hx : Elementary.arcsinDomain x) :
    (sineAtAngle (arcsineValue x hx) (arcsineValue_valid x hx)).Equiv (RealRaw.ofRat x) := by
  unfold arcsineValue
  split
  · exact arcsinePositive_sine_inverse _
  · let y : UnitTarget := ⟨-x,by grind only,by have h := hx.1; grind only⟩
    have he := sineAtAngle_neg (arcsinePositiveValue y) (arcsinePositiveValue_valid y)
    have hp := RealRaw.neg_equiv (arcsinePositive_sine_inverse y)
    have hq : (RealRaw.neg (RealRaw.ofRat y.val)).Equiv (RealRaw.ofRat x) := by
      intro n
      apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
      simp only [RealRaw.neg,RealRaw.negCompute,RealRaw.ofRat,y,Rat.neg_neg,QInterval.Overlaps]
      exact ⟨Rat.le_refl,Rat.le_refl⟩
    have hqv : (RealRaw.neg (RealRaw.ofRat y.val)).Valid := RealRaw.neg_valid (RealRaw.ofRat_valid y.val)
    exact RealRaw.equiv_trans (sineAtAngle_valid _ _) (RealRaw.neg_valid (sineAtAngle_valid _ _))
      (RealRaw.ofRat_valid x) he (RealRaw.equiv_trans (RealRaw.neg_valid (sineAtAngle_valid _ _))
        hqv (RealRaw.ofRat_valid x) hp hq)

def arcsine : PartialRealFunRaw where
  definedAt := Elementary.arcsinDomain
  compute x hx := (arcsineValue x hx).compute

theorem arcsine_valid : arcsine.Valid := arcsineValue_valid

def arcsineFunction : PartialRealFunction := PartialRealFunction.ofRaw arcsine arcsine_valid

def arcsineRaw : Elementary.ArcsinRaw where
  compute := arcsine.compute

theorem arcsineRaw_spec : Elementary.ArcsinSpec arcsineRaw := arcsine_valid


theorem le_of_shrinking_error {a b : Rat} {rate : Nat → Rat}
    (hr : ShrinksToZero rate) (start : Nat) (hb : ∀ n, start ≤ n → a ≤ b+rate n) : a ≤ b := by
  by_cases h : a ≤ b
  · exact h
  · have hg : 0 < a-b := by grind only
    have he : 0 < (a-b)/2 := by
      rw [Rat.div_def]; exact Rat.mul_pos hg (by decide +kernel)
    obtain ⟨N,hN⟩ := hr ⟨(a-b)/2,he⟩
    let M := max start N
    have h1 := hb M (Nat.le_max_left _ _)
    have h2 := hN M (Nat.le_max_right _ _)
    have hhalf : ((a-b)/2)*2=a-b := Rat.div_mul_cancel (by decide +kernel)
    grind only

theorem arcsinePositive_range (y : UnitTarget) :
    (RealRaw.ofRat 0).Le (arcsinePositiveValue y) ∧
      (arcsinePositiveValue y).Le GeometricPiRotation.halfPi := by
  constructor
  · intro n m
    have hp := (angleValue_contains_future y (Nat.le_refl m)).2.2
    let t := midpointSlope y m
    have ho := QInterval.midpoint_mem (RealRaw.interval_order_of_valid _
      (arctanScheduledRectangleRaw_valid t.nonnegative t.le_one) m)
    have hl := arctanIntegralRectangleCompute_lower_nonnegative t.nonnegative (arctanScheduledStage m)
    change 0 ≤ ((arctanScheduledRectangleRaw t.val).compute m).lo at hl
    change 0 ≤ ((angleValue y).compute m).hi.im
    change 2*((arctanScheduledRectangleRaw t.val).compute m).midpoint ≤ ((angleValue y).compute m).hi.im at hp
    grind only
  · let top := RealRaw.scaleRat 2 (arctanScheduledRectangleRaw 1)
    have htop : top.Valid := RealRaw.scaleRat_valid
      (arctanScheduledRectangleRaw_valid (by decide) (Rat.le_refl))
    have hle : (arcsinePositiveValue y).Le top := by
      apply RealRaw.le_of_sameStage (arcsinePositiveValue_valid y) htop
      intro k
      apply le_of_shrinking_error radius_shrinks k
      intro M hkM
      let t := midpointSlope y M
      have hp := (angleValue_contains_future y hkM).1.2
      have ho := QInterval.midpoint_mem (RealRaw.interval_order_of_valid _
        (arctanScheduledRectangleRaw_valid t.nonnegative t.le_one) M)
      have hc := arctanIntegralRectangleCompute_lower_le_upper_of_le t.nonnegative t.le_one (arctanScheduledStage M)
      have hw := arctanScheduledRectangleOnUnit_width_le t.val t.nonnegative t.le_one M
      have hrec := FTC.one_div_nat_antitone (Nat.succ_pos M)
        (by omega : 0 < 16*(M+1)) (by omega : M+1 ≤ 16*(M+1))
      have hw' := Rat.le_trans hw hrec
      have hn := htop.2.1 k M hkM
      change ((arcsinePositiveValue y).compute k).lo ≤
        2*((arctanScheduledRectangleRaw t.val).compute M).midpoint at hp
      change ((arctanScheduledRectangleRaw t.val).compute M).lo ≤ ((arctanScheduledRectangleRaw t.val).compute M).midpoint ∧
        ((arctanScheduledRectangleRaw t.val).compute M).midpoint ≤ ((arctanScheduledRectangleRaw t.val).compute M).hi at ho
      change ((arctanScheduledRectangleRaw t.val).compute M).lo ≤ ((arctanScheduledRectangleRaw 1).compute M).hi at hc
      change ((arctanScheduledRectangleRaw t.val).compute M).hi-((arctanScheduledRectangleRaw t.val).compute M).lo ≤ 1/((M+1:Nat):Rat) at hw'
      have htM : (top.compute M).hi = 2*((arctanScheduledRectangleRaw 1).compute M).hi := by
        simp only [top,RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos (show (0:Rat)≤2 by decide)]
      have hb := hn.2.2
      rw [htM] at hb
      dsimp [radius,ElementaryAngleSearch.radius]
      grind only
    have he : top.Equiv GeometricPiRotation.halfPi :=
      RealRaw.equiv_trans htop GeometricPiRotation.halfPiUnscheduled_valid GeometricPiRotation.halfPi_valid
        (RealRaw.scaleRat_equiv (arctanScheduledRectangleRaw_equiv_arctanGeom (by decide) (Rat.le_refl)))
        (RealRaw.equiv_symm GeometricPiRotation.halfPi_equiv_unscheduled)
    exact RealRaw.le_trans htop hle (RealRaw.le_of_equiv htop GeometricPiRotation.halfPi_valid he)


theorem zero_le_halfPi : (RealRaw.ofRat 0).Le GeometricPiRotation.halfPi := by
  intro n m
  have hb := GeometricPiRotation.halfPi_bounds m
  have ho := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPi_valid m
  change 0 ≤ (GeometricPiRotation.halfPi.compute m).hi
  unfold QInterval.width at ho
  grind only

theorem neg_halfPi_le_zero : (RealRaw.neg GeometricPiRotation.halfPi).Le (RealRaw.ofRat 0) := by
  intro n m
  have hb := zero_le_halfPi m n
  change -(GeometricPiRotation.halfPi.compute n).hi ≤ 0
  change 0 ≤ (GeometricPiRotation.halfPi.compute n).hi at hb
  grind only

theorem arcsine_range (x : Rat) (hx : Elementary.arcsinDomain x) :
    (RealRaw.neg GeometricPiRotation.halfPi).Le (arcsineValue x hx) ∧
      (arcsineValue x hx).Le GeometricPiRotation.halfPi := by
  unfold arcsineValue
  split
  · have hr := arcsinePositive_range (⟨x,by assumption,hx.2⟩ : UnitTarget)
    exact ⟨RealRaw.le_trans (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) neg_halfPi_le_zero hr.1,hr.2⟩
  · let y : UnitTarget := ⟨-x,by grind only,by have h := hx.1; grind only⟩
    have hr := arcsinePositive_range y
    constructor
    · exact RealRaw.le_neg_le_neg hr.2
    · have hle : (RealRaw.neg (arcsinePositiveValue y)).Le (RealRaw.ofRat 0) := by
        intro n m
        have hp := hr.1 m n
        change -((arcsinePositiveValue y).compute n).hi ≤ 0
        change 0 ≤ ((arcsinePositiveValue y).compute n).hi at hp
        grind only
      exact RealRaw.le_trans (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) hle zero_le_halfPi

def cosineAtAngle (x : RealRaw) (hx : x.Valid) : RealRaw :=
  (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val.realPart

theorem cosineAtAngle_valid (x : RealRaw) (hx : x.Valid) : (cosineAtAngle x hx).Valid :=
  realPart_valid (entireExponentialValue _).property

theorem cosineAtAngle_congr {x y : RealRaw} (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    (cosineAtAngle x hx).Equiv (cosineAtAngle y hy) :=
  realPart_equiv (entireExponentialValue_congr _ _ (imaginaryAxis_equiv hx hy hxy))

theorem imaginaryUnit_conjugate_realPart (z : ComplexRaw) (hz : z.Valid) :
    (mul (ofQComplex RotationSeries.imaginaryUnit) (conj z)).realPart.Equiv z.imagPart := by
  intro n
  let p := (z.compute n).center
  have hp := QBox.center_mem (valid_ordered hz n)
  have hc : ((conj z).compute n).lo ≤ QComplex.conj p ∧ QComplex.conj p ≤ ((conj z).compute n).hi :=
    ⟨⟨hp.1.1,Rat.neg_le_neg hp.2.2⟩,⟨hp.2.1,Rat.neg_le_neg hp.1.2⟩⟩
  have hm := QBox.mul_contains (A := QBox.point RotationSeries.imaginaryUnit) (B := (conj z).compute n)
    (z := RotationSeries.imaginaryUnit) (w := QComplex.conj p)
    (QComplex.le_refl _) (QComplex.le_refl _) hc.1 hc.2
  have hr : (QComplex.mul RotationSeries.imaginaryUnit (QComplex.conj p)).re = p.im := by
    simp only [RotationSeries.imaginaryUnit,QComplex.mul,QComplex.conj,Rat.zero_mul,Rat.one_mul]
    grind only
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  have hml := hm.1.1
  have hmu := hm.2.1
  rw [hr] at hml hmu
  exact ⟨Rat.le_trans hml hp.2.2,Rat.le_trans hp.1.2 hmu⟩

theorem cosine_halfPi_sub (x : RealRaw) (hx : x.Valid) :
    (cosineAtAngle (RealRaw.sub GeometricPiRotation.halfPi x)
      (RealRaw.sub_valid GeometricPiRotation.halfPi_valid hx)).Equiv (sineAtAngle x hx) := by
  let z : Scalar := ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩
  let p : Scalar := ⟨GeometricPiRotation.imaginaryHalf,GeometricPiRotation.imaginaryHalf_valid⟩
  let q := exponentialConjugateInput z
  let s : Scalar := ⟨imaginaryAxis (RealRaw.sub GeometricPiRotation.halfPi x),
    imaginaryAxis_valid (RealRaw.sub_valid GeometricPiRotation.halfPi_valid hx)⟩
  let sum : Scalar := ⟨add p.val q.val,add_valid p.property q.property⟩
  have hin : s.val.Equiv sum.val := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    simp only [s,sum,p,q,z,exponentialConjugateInput,GeometricPiRotation.imaginaryHalf,
      imaginaryAxis,mulI,ofRealRaw,RealRaw.sub,RealRaw.subCompute,RealRaw.neg,RealRaw.negCompute,
      RealRaw.add,RealRaw.addCompute,conj,add,QBox.add,QBox.conj,QComplex.add,QBox.Overlaps,QComplex.le_def,Rat.neg_zero,Rat.zero_add]
    have hxorder := RealRaw.interval_order_of_valid x hx n
    have hporder := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPi_valid n
    unfold QInterval.width at hxorder hporder
    constructor <;> constructor <;> grind only
  have h1 := equiv_trans (entireExponentialValue s).property (entireExponentialValue sum).property
    (mul_valid (entireExponentialValue p).property (entireExponentialValue q).property)
    (entireExponentialValue_congr s sum hin) (equiv_symm (entireExponential_addition p q))
  have h2 := mul_equiv (entireExponentialValue p).property (ofQComplex_valid _)
    (entireExponentialValue q).property (conj_valid _ (entireExponentialValue z).property)
    entireExponential_geometric_quarterTurn (equiv_symm (entireExponential_conjugation z))
  have he := equiv_trans (entireExponentialValue s).property
    (mul_valid (entireExponentialValue p).property (entireExponentialValue q).property)
    (mul_valid (ofQComplex_valid _) (conj_valid _ (entireExponentialValue z).property)) h1 h2
  exact RealRaw.equiv_trans (cosineAtAngle_valid _ _)
    (realPart_valid (mul_valid (ofQComplex_valid _) (conj_valid _ (entireExponentialValue z).property)))
    (sineAtAngle_valid _ _) (realPart_equiv he)
    (imaginaryUnit_conjugate_realPart _ (entireExponentialValue z).property)

def arccosineValue (x : Rat) (hx : Elementary.arcsinDomain x) : RealRaw :=
  RealRaw.sub GeometricPiRotation.halfPi (arcsineValue x hx)

theorem arccosineValue_valid (x : Rat) (hx : Elementary.arcsinDomain x) : (arccosineValue x hx).Valid :=
  RealRaw.sub_valid GeometricPiRotation.halfPi_valid (arcsineValue_valid x hx)

theorem arccosine_cosine_inverse (x : Rat) (hx : Elementary.arcsinDomain x) :
    (cosineAtAngle (arccosineValue x hx) (arccosineValue_valid x hx)).Equiv (RealRaw.ofRat x) :=
  RealRaw.equiv_trans (cosineAtAngle_valid _ _) (sineAtAngle_valid _ _) (RealRaw.ofRat_valid _)
    (cosine_halfPi_sub _ (arcsineValue_valid x hx)) (arcsine_sine_inverse x hx)

theorem arccosine_range (x : Rat) (hx : Elementary.arcsinDomain x) :
    (RealRaw.ofRat 0).Le (arccosineValue x hx) ∧
      (arccosineValue x hx).Le ElementaryRational.pi := by
  have hr := arcsine_range x hx
  constructor
  · intro n m
    have hb := hr.2 m m
    change 0 ≤ (GeometricPiRotation.halfPi.compute m).hi-((arcsineValue x hx).compute m).lo
    change ((arcsineValue x hx).compute m).lo ≤ (GeometricPiRotation.halfPi.compute m).hi at hb
    grind only
  · intro n m
    have hb := hr.1 m n
    have ho := RealRaw.le_refl GeometricPiRotation.halfPi GeometricPiRotation.halfPi_valid n m
    change -(GeometricPiRotation.halfPi.compute m).hi ≤ ((arcsineValue x hx).compute n).hi at hb
    change (GeometricPiRotation.halfPi.compute n).lo ≤ (GeometricPiRotation.halfPi.compute m).hi at ho
    change (GeometricPiRotation.halfPi.compute n).lo-((arcsineValue x hx).compute n).hi ≤
      2*(GeometricPiRotation.halfPi.compute m).hi
    grind only

def arccosine : PartialRealFunRaw where
  definedAt := Elementary.arcsinDomain
  compute x hx := (arccosineValue x hx).compute

theorem arccosine_valid : arccosine.Valid := arccosineValue_valid

def arccosineFunction : PartialRealFunction := PartialRealFunction.ofRaw arccosine arccosine_valid

end ComputableAnalysis.ElementaryInverseBranches
