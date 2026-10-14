import ComputableAnalysis.ElementaryInverseBranches
import ComputableAnalysis.ElementaryAngleSearch
import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal

/-! The principal arctangent is constructed for every rational target.
Bisection takes place in the rational stereographic circle chart. The
geometric angle evaluator and its exponential comparison certify the result. -/
namespace ComputableAnalysis.ElementaryArctangentBranch
open ComplexRaw RiemannHilbert FunctionTheory ModularForms SeriesLimitLaws
open ElementaryCircleAngle ElementaryInverseBranches ArctanGeometry
set_option maxHeartbeats 2000000

structure PositiveTarget where
  val : Rat
  nonnegative : 0 ≤ val

def upper (y : PositiveTarget) : Rat := (y.val+1)/(y.val+2)
def tangentChart (t : Rat) : Rat := 2*t/(1-t*t)
def residual (y : PositiveTarget) (t : Rat) : Rat := 2*t-y.val*(1-t*t)

theorem upper_bounds (y : PositiveTarget) : 0 ≤ upper y ∧ upper y < 1 := by
  have hy := y.nonnegative
  have hd : 0 < y.val+2 := by grind only
  have hi := Rat.inv_pos.mpr hd
  have hc := Rat.div_mul_cancel (a := y.val+1) (Rat.ne_of_gt hd)
  constructor
  · unfold upper; rw [Rat.div_def]; exact Rat.mul_nonneg (by grind only) (Rat.le_of_lt hi)
  · apply Rat.lt_of_mul_lt_mul_right (c := y.val+2)
    · change ((y.val+1)/(y.val+2))*(y.val+2) < 1*(y.val+2)
      rw [hc]; grind only
    · exact Rat.le_of_lt hd

theorem tangent_denominator_pos {t : Rat} (h0 : 0 ≤ t) (h1 : t < 1) : 0 < 1-t*t := by
  have hm := Rat.mul_lt_mul_of_pos_right h1 (by grind only : 0 < (1:Rat))
  have hs := rat_mul_le_mul_of_nonneg h0 (Rat.le_of_lt h1) h0 (Rat.le_of_lt h1)
  have ht := Rat.mul_lt_mul_of_pos_left h1 (by grind only : 0 < (1:Rat))
  have hb := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h1) h0
  grind only

theorem upper_residual (y : PositiveTarget) : 0 ≤ residual y (upper y) := by
  let d := y.val+2
  have hd : 0 < d := by have hy := y.nonnegative; dsimp [d]; grind only
  have hc := Rat.div_mul_cancel (a := y.val+1) (Rat.ne_of_gt hd)
  have hs := Rat.mul_nonneg y.nonnegative y.nonnegative
  have hp := Rat.mul_pos hd hd
  apply Rat.le_of_mul_le_mul_right (c := d*d)
  · change 0*(d*d) ≤ (2*((y.val+1)/d)-y.val*(1-((y.val+1)/d)*((y.val+1)/d)))*(d*d)
    have he : (2*((y.val+1)/d)-y.val*(1-((y.val+1)/d)*((y.val+1)/d)))*(d*d) = 3*y.val+4 := by
      dsimp [d] at *
      grind only
    rw [he]; have hy := y.nonnegative; grind only
  · exact hp

def search (y : PositiveTarget) : ElementaryAngleSearch.SearchOnUnit where
  certificate := {
    map := tangentChart
    target := y.val
    initialInterval := ⟨0,upper y⟩
    stage := 0
    ordered := (upper_bounds y).1
    lower_bracket := by rw [show tangentChart 0 = 0 by decide +kernel]; exact y.nonnegative
    upper_bracket := by
      have hd := tangent_denominator_pos (upper_bounds y).1 (upper_bounds y).2
      have hc := Rat.div_mul_cancel (a := 2*upper y) (Rat.ne_of_gt hd)
      apply Rat.le_of_mul_le_mul_right (c := 1-upper y*upper y)
      · have hr := upper_residual y
        unfold residual at hr
        change y.val*(1-upper y*upper y) ≤ (2*upper y/(1-upper y*upper y))*(1-upper y*upper y)
        rw [hc]; grind only
      · exact hd }
  lower := Rat.le_refl
  upper := Rat.le_of_lt (upper_bounds y).2

theorem bracket_upper (y : PositiveTarget) (n : Nat) : (ElementaryAngleSearch.bracket (search y) n).hi ≤ upper y :=
  (monotoneTargetBisectionIterate_subinterval (f := tangentChart) y.val (upper_bounds y).1 (ElementaryAngleSearch.bracketStage n)).2

theorem residual_difference (y : PositiveTarget) (a b : Rat) :
    residual y b-residual y a = (b-a)*(2+y.val*(a+b)) := by
  unfold residual; grind only

def lipschitz (y : PositiveTarget) : Rat := 2+2*y.val

theorem lipschitz_nonnegative (y : PositiveTarget) : 0 ≤ lipschitz y := by
  have hy := y.nonnegative; unfold lipschitz; grind only

theorem residual_order_lipschitz (y : PositiveTarget) {a b : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    0 ≤ residual y b-residual y a ∧ residual y b-residual y a ≤ lipschitz y*(b-a) := by
  have hb0 := Rat.le_trans ha hab
  have ha1 := Rat.le_trans hab hb
  have hdiff : 0 ≤ b-a := by grind only
  have hs : 0 ≤ a+b := Rat.add_nonneg ha hb0
  have hsu : a+b ≤ 2 := by grind only
  have hc := Rat.mul_nonneg y.nonnegative hs
  have hcu := Rat.mul_le_mul_of_nonneg_left hsu y.nonnegative
  have hp := Rat.mul_nonneg hdiff (by grind only : 0 ≤ 2+y.val*(a+b))
  have hpu := Rat.mul_le_mul_of_nonneg_left (by have hy := y.nonnegative; dsimp [lipschitz]; grind only : 2+y.val*(a+b) ≤ lipschitz y) hdiff
  rw [residual_difference]
  constructor <;> grind only

theorem bracket_residual (y : PositiveTarget) (N : Nat) :
    residual y (ElementaryAngleSearch.bracket (search y) N).lo ≤ 0 ∧ 0 ≤ residual y (ElementaryAngleSearch.bracket (search y) N).hi := by
  have hb := ElementaryAngleSearch.bracket_contains_target (search y) N
  change tangentChart (ElementaryAngleSearch.bracket (search y) N).lo ≤ y.val ∧ y.val ≤ tangentChart (ElementaryAngleSearch.bracket (search y) N).hi at hb
  have hs := ElementaryAngleSearch.bracket_subinterval (search y) N
  have hu := bracket_upper y N
  have huu := (upper_bounds y).2
  constructor
  · have hd := tangent_denominator_pos hs.1 (by grind only)
    have hc := Rat.div_mul_cancel (a := 2*(ElementaryAngleSearch.bracket (search y) N).lo) (Rat.ne_of_gt hd)
    have hm := Rat.mul_le_mul_of_nonneg_right hb.1 (Rat.le_of_lt hd)
    change (2*(ElementaryAngleSearch.bracket (search y) N).lo/(1-(ElementaryAngleSearch.bracket (search y) N).lo*(ElementaryAngleSearch.bracket (search y) N).lo))*(1-(ElementaryAngleSearch.bracket (search y) N).lo*(ElementaryAngleSearch.bracket (search y) N).lo) ≤ _ at hm
    rw [hc] at hm; unfold residual; grind only
  · have hd := tangent_denominator_pos (Rat.le_trans hs.1 hs.2.1) (by grind only)
    have hc := Rat.div_mul_cancel (a := 2*(ElementaryAngleSearch.bracket (search y) N).hi) (Rat.ne_of_gt hd)
    have hm := Rat.mul_le_mul_of_nonneg_right hb.2 (Rat.le_of_lt hd)
    change _ ≤ (2*(ElementaryAngleSearch.bracket (search y) N).hi/(1-(ElementaryAngleSearch.bracket (search y) N).hi*(ElementaryAngleSearch.bracket (search y) N).hi))*(1-(ElementaryAngleSearch.bracket (search y) N).hi*(ElementaryAngleSearch.bracket (search y) N).hi) at hm
    rw [hc] at hm; unfold residual; grind only

theorem midpoint_residual (y : PositiveTarget) (N : Nat) :
    qabs (residual y (ElementaryAngleSearch.midpointSlope (search y) N).val) ≤ lipschitz y*(ElementaryAngleSearch.bracket (search y) N).width := by
  have hb := ElementaryAngleSearch.bracket_subinterval (search y) N
  have hm := QInterval.midpoint_mem hb.2.1
  have hr := bracket_residual y N
  have hl := residual_order_lipschitz y hb.1 hm.1 (Rat.le_trans hm.2 hb.2.2)
  have hh := residual_order_lipschitz y (Rat.le_trans hb.1 hm.1) hm.2 hb.2.2
  have hf := residual_order_lipschitz y hb.1 hb.2.1 hb.2.2
  have hcommon := qabs_sub_le_of_common_bounds
    (by grind only : residual y (ElementaryAngleSearch.bracket (search y) N).lo ≤ residual y (ElementaryAngleSearch.bracket (search y) N).midpoint)
    (by grind only : residual y (ElementaryAngleSearch.bracket (search y) N).midpoint ≤ residual y (ElementaryAngleSearch.bracket (search y) N).hi) hr.1 hr.2
  have hc : qabs (residual y (ElementaryAngleSearch.midpointSlope (search y) N).val) ≤
      residual y (ElementaryAngleSearch.bracket (search y) N).hi-residual y (ElementaryAngleSearch.bracket (search y) N).lo := by
    simpa [ElementaryAngleSearch.midpointSlope,Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero] using hcommon
  exact Rat.le_trans hc hf.2

def valuePositive (y : PositiveTarget) : RealRaw := (ElementaryAngleSearch.angleValue (search y)).imagPart

theorem valuePositive_valid (y : PositiveTarget) : (valuePositive y).Valid :=
  imagPart_valid (ElementaryAngleSearch.angleValue_valid (search y))

def exponential (y : PositiveTarget) : ComplexRaw :=
  (entireExponentialValue (ElementaryAngleSearch.angleScalar (search y))).val

theorem exponential_valid (y : PositiveTarget) : (exponential y).Valid :=
  (entireExponentialValue _).property

theorem exponential_agrees_angle (y : PositiveTarget) :
    (entireExponentialValue ⟨imaginaryAxis (valuePositive y),imaginaryAxis_valid (valuePositive_valid y)⟩).val.Equiv
      (exponential y) :=
  entireExponentialValue_congr _ _ (ElementaryAngleSearch.angleValue_axis (search y))

theorem bracket_width_radius (y : PositiveTarget) (N : Nat) :
    (ElementaryAngleSearch.bracket (search y) N).width ≤ ElementaryAngleSearch.radius N := by
  have h := ElementaryAngleSearch.bracket_width (search y) N
  have hden : ((2*(N+1):Nat):Rat) = 2*((N+1:Nat):Rat) := by rw [Rat.natCast_mul]; rfl
  rw [hden,Rat.div_def,Rat.inv_mul_rev] at h
  have h2 : (2:Rat)⁻¹=1/2 := by decide +kernel
  rw [h2] at h
  have hp : 0 ≤ ((N+1:Nat):Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast Nat.succ_pos N))
  dsimp [ElementaryAngleSearch.radius]; rw [Rat.div_def]; grind only

theorem circle_residual (y : PositiveTarget) (N : Nat) :
    qabs ((GeometricRotationODE.pointComplex (ElementaryAngleSearch.midpointSlope (search y) N).val).im-
      y.val*(GeometricRotationODE.pointComplex (ElementaryAngleSearch.midpointSlope (search y) N).val).re) ≤
        lipschitz y*ElementaryAngleSearch.radius N := by
  let t := (ElementaryAngleSearch.midpointSlope (search y) N).val
  have hd := denominator_pos t
  have hc := Rat.mul_inv_cancel (1+t*t) (Rat.ne_of_gt hd)
  have ht := Rat.mul_nonneg (ElementaryAngleSearch.midpointSlope (search y) N).nonnegative
    (ElementaryAngleSearch.midpointSlope (search y) N).nonnegative
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr hd)
  have hiu : (1+t*t)⁻¹ ≤ 1 := by
    have hm := Rat.mul_le_mul_of_nonneg_right (by grind only : 1 ≤ 1+t*t) hi
    grind only
  have hr := midpoint_residual y N
  have hb := bracket_width_radius y N
  have he : (GeometricRotationODE.pointComplex t).im-y.val*(GeometricRotationODE.pointComplex t).re =
      residual y t*(1+t*t)⁻¹ := by
    simp only [GeometricRotationODE.pointComplex,RationalCircle.Stage.point,Rat.div_def,residual]
    grind only
  change qabs ((GeometricRotationODE.pointComplex t).im-y.val*(GeometricRotationODE.pointComplex t).re) ≤ _
  rw [he,qabs_mul,qabs_eq_self_of_nonneg hi]
  have hm := Rat.mul_le_mul_of_nonneg_left hiu (qabs_nonneg (residual y t))
  have hu := Rat.mul_le_mul_of_nonneg_left hb (lipschitz_nonnegative y)
  grind only

theorem exponential_sine_cosine (y : PositiveTarget) :
    (exponential y).imagPart.Equiv (RealRaw.scaleRat y.val (exponential y).realPart) := by
  let f := exponential y
  let z := imaginaryAxis (RealRaw.sub f.imagPart (RealRaw.scaleRat y.val f.realPart))
  let C := exponentialQuadraticConstant geometricFactorRadius
  let D := C*(1+y.val)+lipschitz y
  have hC : 0 ≤ C := exponentialQuadraticConstant_nonnegative _
  have hD : 0 ≤ D := Rat.add_nonneg (Rat.mul_nonneg hC (Rat.add_nonneg (by decide) y.nonnegative)) (lipschitz_nonnegative y)
  have hs := shrinks_scale ElementaryAngleSearch.radius ElementaryAngleSearch.radius_shrinks D hD
  have hz : Small z 0 := by
    apply small_closed z 0 (fun N => D*ElementaryAngleSearch.radius N) hs
    intro N
    let p := GeometricRotationODE.pointComplex (ElementaryAngleSearch.midpointSlope (search y) N).val
    have he := ElementaryAngleSearch.angle_exponential_circle_error (search y) N
    have hr := circle_residual y N
    have hlo := neg_qabs_le_self (p.im-y.val*p.re)
    have hhi := self_le_qabs (p.im-y.val*p.re)
    have hR := ElementaryAngleSearch.radius_nonnegative N
    have hDR := Rat.mul_nonneg hD hR
    refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    · change -(0+D*ElementaryAngleSearch.radius N) ≤ 0
      grind only
    · change (0:Rat) ≤ 0+D*ElementaryAngleSearch.radius N
      grind only
    · have him := he.2.2.1 0 m
      have hre := he.2.1 m 0
      change -(C*ElementaryAngleSearch.radius N) ≤ (f.compute m).hi.im+ -p.im at him
      change (f.compute m).lo.re+ -p.re ≤ C*ElementaryAngleSearch.radius N at hre
      have hm := Rat.mul_le_mul_of_nonneg_left hre y.nonnegative
      simp only [z,imaginaryAxis,mulI,ofRealRaw,RealRaw.sub,RealRaw.subCompute,
        RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos y.nonnegative,imagPart,realPart]
      change -(0+D*ElementaryAngleSearch.radius N) ≤
        (f.compute m).hi.im-y.val*(f.compute m).lo.re
      dsimp [D] at *; grind only
    · have him := he.2.2.2 n 0
      have hre := he.1 0 n
      change (f.compute n).lo.im+ -p.im ≤ C*ElementaryAngleSearch.radius N at him
      change -(C*ElementaryAngleSearch.radius N) ≤ (f.compute n).hi.re+ -p.re at hre
      have hm := Rat.mul_le_mul_of_nonneg_left hre y.nonnegative
      simp only [z,imaginaryAxis,mulI,ofRealRaw,RealRaw.sub,RealRaw.subCompute,
        RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos y.nonnegative,imagPart,realPart]
      change (f.compute n).lo.im-y.val*(f.compute n).hi.re ≤ 0+D*ElementaryAngleSearch.radius N
      dsimp [D] at *; grind only
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  have hl := hz.2.2.1 n n
  have hu := hz.2.2.2 n n
  change -(0:Rat) ≤ (f.compute n).hi.im-((RealRaw.scaleRat y.val f.realPart).compute n).lo at hl
  change (f.compute n).lo.im-((RealRaw.scaleRat y.val f.realPart).compute n).hi ≤ (0:Rat) at hu
  change (f.compute n).lo.im ≤ ((RealRaw.scaleRat y.val f.realPart).compute n).hi ∧
    ((RealRaw.scaleRat y.val f.realPart).compute n).lo ≤ (f.compute n).hi.im
  constructor <;> grind only

def cosineLower (y : PositiveTarget) : Rat :=
  (1-upper y*upper y)/(1+upper y*upper y)

theorem cosineLower_positive (y : PositiveTarget) : 0 < cosineLower y :=
  Rat.mul_pos (tangent_denominator_pos (upper_bounds y).1 (upper_bounds y).2)
    (Rat.inv_pos.mpr (denominator_pos (upper y)))

theorem circle_cosine_lower (y : PositiveTarget) (N : Nat) :
    cosineLower y ≤ (GeometricRotationODE.pointComplex (ElementaryAngleSearch.midpointSlope (search y) N).val).re := by
  let t := (ElementaryAngleSearch.midpointSlope (search y) N).val
  let u := upper y
  have ht := (ElementaryAngleSearch.midpointSlope (search y) N).nonnegative
  have hu : t ≤ u := Rat.le_trans (QInterval.midpoint_mem (ElementaryAngleSearch.bracket_subinterval (search y) N).2.1).2 (bracket_upper y N)
  have hu0 := (upper_bounds y).1
  have hs := rat_mul_le_mul_of_nonneg ht hu ht hu
  have ha := Rat.mul_inv_cancel (1+t*t) (Rat.ne_of_gt (denominator_pos t))
  have hb := Rat.mul_inv_cancel (1+u*u) (Rat.ne_of_gt (denominator_pos u))
  have hd := Rat.mul_pos (denominator_pos t) (denominator_pos u)
  have he : (GeometricRotationODE.pointComplex t).re-cosineLower y =
      2*(u*u-t*t)/((1+t*t)*(1+u*u)) := by
    simp only [GeometricRotationODE.pointComplex,RationalCircle.Stage.point,cosineLower,Rat.div_def,Rat.inv_mul_rev]
    dsimp [u] at *; grind only
  have hn : 0 ≤ 2*(u*u-t*t)/((1+t*t)*(1+u*u)) :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by grind only)) (Rat.le_of_lt (Rat.inv_pos.mpr hd))
  change cosineLower y ≤ (GeometricRotationODE.pointComplex t).re
  rw [←he] at hn; grind only

theorem exponential_cosine_lower (y : PositiveTarget) :
    (RealRaw.ofRat (cosineLower y)).Le (exponential y).realPart := by
  intro n m
  let C := exponentialQuadraticConstant geometricFactorRadius
  have hs := shrinks_scale ElementaryAngleSearch.radius ElementaryAngleSearch.radius_shrinks C
    (exponentialQuadraticConstant_nonnegative _)
  apply le_of_shrinking_error hs m
  intro N _
  have he := (ElementaryAngleSearch.angle_exponential_circle_error (search y) N).1 0 m
  have hp := circle_cosine_lower y N
  change -(C*ElementaryAngleSearch.radius N) ≤ ((exponential y).compute m).hi.re +
    -(GeometricRotationODE.pointComplex (ElementaryAngleSearch.midpointSlope (search y) N).val).re at he
  change cosineLower y ≤ ((exponential y).compute m).hi.re+C*ElementaryAngleSearch.radius N
  grind only

theorem valuePositive_cosine_lower (y : PositiveTarget) :
    (RealRaw.ofRat (cosineLower y)).Le (cosineAtAngle (valuePositive y) (valuePositive_valid y)) :=
  RealRaw.le_trans (realPart_valid (exponential_valid y)) (exponential_cosine_lower y)
    (RealRaw.le_of_equiv (realPart_valid (exponential_valid y)) (cosineAtAngle_valid _ _)
      (RealRaw.equiv_symm (realPart_equiv (exponential_agrees_angle y))))

theorem valuePositive_sine_cosine (y : PositiveTarget) :
    (sineAtAngle (valuePositive y) (valuePositive_valid y)).Equiv
      (RealRaw.scaleRat y.val (cosineAtAngle (valuePositive y) (valuePositive_valid y))) :=
  RealRaw.equiv_trans (sineAtAngle_valid _ _) (imagPart_valid (exponential_valid y))
    (RealRaw.scaleRat_valid (cosineAtAngle_valid _ _))
    (imagPart_equiv (exponential_agrees_angle y))
    (RealRaw.equiv_trans (imagPart_valid (exponential_valid y))
      (RealRaw.scaleRat_valid (realPart_valid (exponential_valid y)))
      (RealRaw.scaleRat_valid (cosineAtAngle_valid _ _)) (exponential_sine_cosine y)
      (RealRaw.scaleRat_equiv (RealRaw.equiv_symm (realPart_equiv (exponential_agrees_angle y)))))

theorem valuePositive_range (y : PositiveTarget) :
    (RealRaw.ofRat 0).Le (valuePositive y) ∧
      (valuePositive y).Le GeometricPiRotation.halfPi := by
  constructor
  · intro n m
    have hp := (ElementaryAngleSearch.angleValue_contains_future (search y) (Nat.le_refl m)).2.2
    let t := ElementaryAngleSearch.midpointSlope (search y) m
    have ho := QInterval.midpoint_mem (RealRaw.interval_order_of_valid _
      (arctanScheduledRectangleRaw_valid t.nonnegative t.le_one) m)
    have hl := arctanIntegralRectangleCompute_lower_nonnegative t.nonnegative (arctanScheduledStage m)
    change 0 ≤ ((arctanScheduledRectangleRaw t.val).compute m).lo at hl
    change 0 ≤ ((ElementaryAngleSearch.angleValue (search y)).compute m).hi.im
    change 2*((arctanScheduledRectangleRaw t.val).compute m).midpoint ≤ ((ElementaryAngleSearch.angleValue (search y)).compute m).hi.im at hp
    grind only
  · let top := RealRaw.scaleRat 2 (arctanScheduledRectangleRaw 1)
    have htop : top.Valid := RealRaw.scaleRat_valid
      (arctanScheduledRectangleRaw_valid (by decide) (Rat.le_refl))
    have hle : (valuePositive y).Le top := by
      apply RealRaw.le_of_sameStage (valuePositive_valid y) htop
      intro k
      apply le_of_shrinking_error ElementaryAngleSearch.radius_shrinks k
      intro M hkM
      let t := ElementaryAngleSearch.midpointSlope (search y) M
      have hp := (ElementaryAngleSearch.angleValue_contains_future (search y) hkM).1.2
      have ho := QInterval.midpoint_mem (RealRaw.interval_order_of_valid _
        (arctanScheduledRectangleRaw_valid t.nonnegative t.le_one) M)
      have hc := arctanIntegralRectangleCompute_lower_le_upper_of_le t.nonnegative t.le_one (arctanScheduledStage M)
      have hw := arctanScheduledRectangleOnUnit_width_le t.val t.nonnegative t.le_one M
      have hrec := FTC.one_div_nat_antitone (Nat.succ_pos M)
        (by omega : 0 < 16*(M+1)) (by omega : M+1 ≤ 16*(M+1))
      have hw' := Rat.le_trans hw hrec
      have hn := htop.2.1 k M hkM
      change ((valuePositive y).compute k).lo ≤
        2*((arctanScheduledRectangleRaw t.val).compute M).midpoint at hp
      change ((arctanScheduledRectangleRaw t.val).compute M).lo ≤ ((arctanScheduledRectangleRaw t.val).compute M).midpoint ∧
        ((arctanScheduledRectangleRaw t.val).compute M).midpoint ≤ ((arctanScheduledRectangleRaw t.val).compute M).hi at ho
      change ((arctanScheduledRectangleRaw t.val).compute M).lo ≤ ((arctanScheduledRectangleRaw 1).compute M).hi at hc
      change ((arctanScheduledRectangleRaw t.val).compute M).hi-((arctanScheduledRectangleRaw t.val).compute M).lo ≤ 1/((M+1:Nat):Rat) at hw'
      have htM : (top.compute M).hi = 2*((arctanScheduledRectangleRaw 1).compute M).hi := by
        simp only [top,RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos (show (0:Rat)≤2 by decide)]
      have hb := hn.2.2
      rw [htM] at hb
      dsimp [ElementaryAngleSearch.radius]
      grind only
    have he : top.Equiv GeometricPiRotation.halfPi :=
      RealRaw.equiv_trans htop GeometricPiRotation.halfPiUnscheduled_valid GeometricPiRotation.halfPi_valid
        (RealRaw.scaleRat_equiv (arctanScheduledRectangleRaw_equiv_arctanGeom (by decide) (Rat.le_refl)))
        (RealRaw.equiv_symm GeometricPiRotation.halfPi_equiv_unscheduled)
    exact RealRaw.le_trans htop hle (RealRaw.le_of_equiv htop GeometricPiRotation.halfPi_valid he)

theorem cosineAtAngle_neg (x : RealRaw) (hx : x.Valid) :
    (cosineAtAngle (RealRaw.neg x) (RealRaw.neg_valid hx)).Equiv (cosineAtAngle x hx) := by
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
  have hr := realPart_equiv he
  change (cosineAtAngle x hx).Equiv (cosineAtAngle (RealRaw.neg x) (RealRaw.neg_valid hx)) at hr
  exact RealRaw.equiv_symm hr

def value (x : Rat) : RealRaw :=
  if h0 : 0 ≤ x then valuePositive ⟨x,h0⟩
  else RealRaw.neg (valuePositive ⟨-x,by grind only⟩)

theorem value_valid (x : Rat) : (value x).Valid := by
  unfold value; split
  · exact valuePositive_valid _
  · exact RealRaw.neg_valid (valuePositive_valid _)

def lowerBound (x : Rat) : Rat :=
  if h0 : 0 ≤ x then cosineLower ⟨x,h0⟩ else cosineLower ⟨-x,by grind only⟩

theorem lowerBound_positive (x : Rat) : 0 < lowerBound x := by
  unfold lowerBound; split <;> exact cosineLower_positive _

theorem value_cosine_lower (x : Rat) :
    (RealRaw.ofRat (lowerBound x)).Le (cosineAtAngle (value x) (value_valid x)) := by
  unfold value lowerBound; split
  · exact valuePositive_cosine_lower _
  · let y : PositiveTarget := ⟨-x,by grind only⟩
    exact RealRaw.le_trans (cosineAtAngle_valid _ _) (valuePositive_cosine_lower y)
      (RealRaw.le_of_equiv (cosineAtAngle_valid _ _) (cosineAtAngle_valid _ _)
        (RealRaw.equiv_symm (cosineAtAngle_neg _ (valuePositive_valid y))))

theorem neg_scale_neg (x : Rat) (hx : x < 0) (c : RealRaw) (hc : c.Valid) :
    (RealRaw.neg (RealRaw.scaleRat (-x) c)).Equiv (RealRaw.scaleRat x c) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid _ (RealRaw.scaleRat_valid (r := x) hc) n
  simp only [RealRaw.neg,RealRaw.negCompute,RealRaw.scaleRat,RealRaw.scaleRatCompute,
    if_pos (show 0 ≤ -x by grind only),if_neg (show ¬0 ≤ x by grind only),
    Rat.neg_mul,Rat.neg_neg]
  unfold QInterval.width at ho
  simp only [RealRaw.scaleRat,RealRaw.scaleRatCompute,if_neg (show ¬0 ≤ x by grind only)] at ho
  constructor <;> grind only

theorem value_sine_cosine (x : Rat) :
    (sineAtAngle (value x) (value_valid x)).Equiv
      (RealRaw.scaleRat x (cosineAtAngle (value x) (value_valid x))) := by
  unfold value; split
  · exact valuePositive_sine_cosine _
  · let y : PositiveTarget := ⟨-x,by grind only⟩
    let c := cosineAtAngle (valuePositive y) (valuePositive_valid y)
    have h1 := sineAtAngle_neg _ (valuePositive_valid y)
    have h2 := RealRaw.neg_equiv (valuePositive_sine_cosine y)
    have h3 := neg_scale_neg x (by grind only) c (cosineAtAngle_valid _ _)
    have h4 := RealRaw.scaleRat_equiv (RealRaw.equiv_symm (cosineAtAngle_neg _ (valuePositive_valid y))) (r := x)
    exact RealRaw.equiv_trans (sineAtAngle_valid _ _) (RealRaw.neg_valid (sineAtAngle_valid _ _))
      (RealRaw.scaleRat_valid (cosineAtAngle_valid _ _)) h1
      (RealRaw.equiv_trans (RealRaw.neg_valid (sineAtAngle_valid _ _))
        (RealRaw.neg_valid (RealRaw.scaleRat_valid (cosineAtAngle_valid _ _)))
        (RealRaw.scaleRat_valid (cosineAtAngle_valid _ _)) h2
        (RealRaw.equiv_trans (RealRaw.neg_valid (RealRaw.scaleRat_valid (cosineAtAngle_valid _ _)))
          (RealRaw.scaleRat_valid (cosineAtAngle_valid _ _))
          (RealRaw.scaleRat_valid (cosineAtAngle_valid _ _)) h3 h4))

theorem value_range (x : Rat) :
    (RealRaw.neg GeometricPiRotation.halfPi).Le (value x) ∧
      (value x).Le GeometricPiRotation.halfPi := by
  unfold value; split
  · have hr := valuePositive_range (⟨x,by assumption⟩ : PositiveTarget)
    exact ⟨RealRaw.le_trans (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) neg_halfPi_le_zero hr.1,hr.2⟩
  · let y : PositiveTarget := ⟨-x,by grind only⟩
    have hr := valuePositive_range y
    constructor
    · exact RealRaw.le_neg_le_neg hr.2
    · have hle : (RealRaw.neg (valuePositive y)).Le (RealRaw.ofRat 0) := by
        intro n m
        have hp := hr.1 m n
        change -((valuePositive y).compute n).hi ≤ 0
        change 0 ≤ ((valuePositive y).compute n).hi at hp
        grind only
      exact RealRaw.le_trans (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) hle zero_le_halfPi

def arctangent : PartialRealFunRaw where
  definedAt _ := True
  compute x _ := (value x).compute

theorem arctangent_valid : arctangent.Valid := fun x _ => value_valid x

def arctangentFunction : PartialRealFunction := PartialRealFunction.ofRaw arctangent arctangent_valid

theorem real_scale_as_product (r : Rat) (c : RealRaw) (hc : c.Valid) :
    (ofRealRaw (RealRaw.scaleRat r c)).Equiv (mul (ofQComplex ⟨r,0⟩) (ofRealRaw c)) := by
  intro n
  let p := ((ofRealRaw c).compute n).center
  have hp := QBox.center_mem (valid_ordered (ofRealRaw_valid _ hc) n)
  have hs := QBox.scaleRat_contains (r := r) hp.1 hp.2
  have hm := QBox.mul_contains (A := QBox.point ⟨r,0⟩) (B := (ofRealRaw c).compute n)
    (z := ⟨r,0⟩) (w := p) (QComplex.le_refl _) (QComplex.le_refl _) hp.1 hp.2
  have he : QComplex.scaleRat r p = QComplex.mul ⟨r,0⟩ p := by
    simp only [QComplex.scaleRat,QComplex.mul,Rat.zero_mul,Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero,Rat.zero_add]
  apply (compareAt_overlap_iff _ _ n n).mpr
  apply QBox.overlaps_of_common_point (point := QComplex.scaleRat r p)
  · by_cases hr : 0 ≤ r
    · simpa only [p,ofRealRaw,RealRaw.scaleRat,RealRaw.scaleRatCompute,QBox.scaleRat,
        QComplex.scaleRat,Rat.mul_zero,if_pos hr] using hs
    · simpa only [p,ofRealRaw,RealRaw.scaleRat,RealRaw.scaleRatCompute,QBox.scaleRat,
        QComplex.scaleRat,Rat.mul_zero,if_neg hr] using hs
  · rw [he]; exact hm

def cosineScalar (x : Rat) : Scalar :=
  ⟨ofRealRaw (cosineAtAngle (value x) (value_valid x)),ofRealRaw_valid _ (cosineAtAngle_valid _ _)⟩

theorem cosine_nonzero (x : Rat) : NonzeroBoxSearch.Nonzero (cosineScalar x) := by
  intro hz
  have hr := realPart_equiv hz
  have he : (cosineAtAngle (value x) (value_valid x)).Equiv (RealRaw.ofRat 0) := hr
  have ho := RealRaw.le_of_equiv (cosineAtAngle_valid _ _) (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) he
  have hb := RealRaw.le_trans (cosineAtAngle_valid _ _) (value_cosine_lower x) ho 0 0
  change lowerBound x ≤ 0 at hb
  have hp := lowerBound_positive x
  grind only

/-- Tangent evaluated at a derived represented angle; the reciprocal uses
proved nonvanishing of the actual cosine output. -/
def tangentValue (x : Rat) : RealRaw :=
  (mul (ofRealRaw (sineAtAngle (value x) (value_valid x)))
    (RepresentedReciprocal.inverse (cosineScalar x) (cosine_nonzero x)).val).realPart

theorem tangentValue_valid (x : Rat) : (tangentValue x).Valid :=
  realPart_valid (mul_valid (ofRealRaw_valid _ (sineAtAngle_valid _ _))
    (RepresentedReciprocal.inverse (cosineScalar x) (cosine_nonzero x)).property)

/-- Exact tangent inverse identity for every rational target. -/
theorem arctangent_tangent_inverse (x : Rat) : (tangentValue x).Equiv (RealRaw.ofRat x) := by
  let c := cosineScalar x
  let r := RepresentedReciprocal.inverse c (cosine_nonzero x)
  let s : Scalar := ⟨ofRealRaw (sineAtAngle (value x) (value_valid x)),ofRealRaw_valid _ (sineAtAngle_valid _ _)⟩
  have hsc := equiv_trans s.property
    (ofRealRaw_valid _ (RealRaw.scaleRat_valid (cosineAtAngle_valid _ _)))
    (mul_valid (ofQComplex_valid _) c.property)
    (ofRealRaw_equiv_of_equiv (sineAtAngle_valid _ _)
      (RealRaw.scaleRat_valid (cosineAtAngle_valid _ _)) (value_sine_cosine x))
    (real_scale_as_product x _ (cosineAtAngle_valid _ _))
  have hunit := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid c.property r.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse c (cosine_nonzero x))
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := s.property)
    (hright := mul_valid (ofQComplex_valid _) c.property) hsc
  have he : (mul s.val r.val).Equiv (ofQComplex ⟨x,0⟩) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid s.property r.property) (hright := ofQComplex_valid _)
    let S := ComplexRawQuotient.ofRaw s.val s.property
    let C := ComplexRawQuotient.ofRaw c.val c.property
    let R := ComplexRawQuotient.ofRaw r.val r.property
    let X := ComplexRawQuotient.ofRaw (ofQComplex ⟨x,0⟩) (ofQComplex_valid _)
    change C*R=1 at hunit
    change S=X*C at hs
    change S*R=X
    grind only
  exact realPart_equiv he

def arctangentRaw : Elementary.ArctanRaw where
  compute x _ := (value x).compute

theorem arctangentRaw_spec : Elementary.ArctanSpec arctangentRaw := fun x _ => value_valid x

theorem cosine_halfPi_zero :
    (cosineAtAngle GeometricPiRotation.halfPi GeometricPiRotation.halfPi_valid).Equiv (RealRaw.ofRat 0) :=
  realPart_equiv entireExponential_geometric_quarterTurn

theorem value_ne_halfPi (x : Rat) : ¬ (value x).Equiv GeometricPiRotation.halfPi := by
  intro hx
  have hc := RealRaw.equiv_trans (cosineAtAngle_valid _ _) (cosineAtAngle_valid _ _)
    (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) (cosineAtAngle_congr (value_valid x) GeometricPiRotation.halfPi_valid hx) cosine_halfPi_zero
  apply cosine_nonzero x
  exact ofRealRaw_equiv_of_equiv (cosineAtAngle_valid _ _) (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) hc

theorem value_ne_neg_halfPi (x : Rat) : ¬ (value x).Equiv (RealRaw.neg GeometricPiRotation.halfPi) := by
  intro hx
  have hc := RealRaw.equiv_trans (cosineAtAngle_valid _ _) (cosineAtAngle_valid _ _)
    (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) (cosineAtAngle_congr (value_valid x) (RealRaw.neg_valid GeometricPiRotation.halfPi_valid) hx)
    (RealRaw.equiv_trans (cosineAtAngle_valid _ _) (cosineAtAngle_valid _ _) (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0)
      (cosineAtAngle_neg _ GeometricPiRotation.halfPi_valid) cosine_halfPi_zero)
  apply cosine_nonzero x
  exact ofRealRaw_equiv_of_equiv (cosineAtAngle_valid _ _) (show (RealRaw.ofRat 0).Valid from RealRaw.ofRat_valid 0) hc

end ComputableAnalysis.ElementaryArctangentBranch
