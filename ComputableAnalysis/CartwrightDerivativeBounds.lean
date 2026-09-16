import ComputableAnalysis.CartwrightMomentBounds

/-! Finite first-order circle estimates with both mesh and evaluation errors.
These inequalities, not an assumed endpoint formula, drive the calculus proof. -/
namespace ComputableAnalysis.CartwrightClockBounds
open ClosedArctanInverse ArctanGeometry SinPiIntegral GeometricSineSecant
open GeometricRotationODE

private theorem residual_clock {a b : Rat} (ha : Unit a) (hb : Unit b) (q : Nat) :
    qabs ((A (center b q) q).lo-(A (center a q) q).lo-(b-a)*(A 1 q).lo) ≤ 6*delta q := by
  have h1:=center_residual a ha q; have h2:=center_residual b hb q
  have ht:=qabs_sub_le ((A (center b q) q).lo-b*(A 1 q).lo)
    ((A (center a q) q).lo-a*(A 1 q).lo)
  have he : ((A (center b q) q).lo-b*(A 1 q).lo)-
    ((A (center a q) q).lo-a*(A 1 q).lo)=
    (A (center b q) q).lo-(A (center a q) q).lo-(b-a)*(A 1 q).lo := by grind
  rw [he] at ht; grind

/-- One uniform finite bound for the sine derivative on the complete chart. -/
theorem sine_step_error {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a≤b) (q : Nat) :
    qabs (s b q-s a q-(b-a)*p q*c a q) ≤ 17000*((b-a)*(b-a)+delta q) := by
  have hu:=center_unit a q; have hv:=center_unit b q
  have hs:=sine_angle_residual hu.1 hu.2 hv.1 hv.2 q
    (a:=(A (center b q) q).lo) (b:=(A (center a q) q).lo) Rat.le_refl
    (RealRaw.interval_order_of_valid _ (arctanIntegralRectangleRaw_valid hv.1 hv.2) q)
    Rat.le_refl (RealRaw.interval_order_of_valid _ (arctanIntegralRectangleRaw_valid hu.1 hu.2) q)
  have wa:=clock_width _ hu q; have wb:=clock_width _ hv q
  have hd:=center_distance ha hb q
  have hh0 : 0≤b-a := by grind
  rw [qabs_eq_self_of_nonneg hh0] at hd
  have e0:=Rat.le_of_lt (meshRadius_pos q)
  have e1:=delta_le_one q
  have ee:=Rat.mul_le_mul_of_nonneg_left e1 e0
  have d0:=qabs_nonneg (center b q-center a q)
  have dsq : qabs (center b q-center a q)*qabs (center b q-center a q) ≤
      8*(b-a)*(b-a)+800*delta q := by
    have h1:=Rat.mul_le_mul_of_nonneg_right hd d0
    have h2:=Rat.mul_le_mul_of_nonneg_left hd (show 0≤2*(b-a)+20*delta q by grind)
    have sq : 0≤(2*(b-a)-20*delta q)*(2*(b-a)-20*delta q) := rat_square_nonneg_basic _
    grind
  have hr:=residual_clock ha hb q
  have cb:=ClockTrigonometry.sample_bounds a q
  have hmul:=Rat.mul_le_mul_of_nonneg_left hr (show 0≤2*c a q by grind)
  have hsmall:=Rat.mul_le_mul_of_nonneg_right cb.2.1 (show 0≤6*delta q by grind)
  have ht:=qabs_add_le
    (s b q-s a q-2*c a q*((A (center b q) q).lo-(A (center a q) q).lo))
    (2*c a q*((A (center b q) q).lo-(A (center a q) q).lo-(b-a)*(A 1 q).lo))
  have he : (s b q-s a q-2*c a q*((A (center b q) q).lo-(A (center a q) q).lo))+
      (2*c a q*((A (center b q) q).lo-(A (center a q) q).lo-(b-a)*(A 1 q).lo)) =
      s b q-s a q-(b-a)*p q*c a q := by unfold p; grind
  rw [he,qabs_mul,qabs_eq_self_of_nonneg (show 0≤2*c a q by grind)] at ht
  change qabs (s b q-s a q-2*c a q*((A (center b q) q).lo-(A (center a q) q).lo))≤_ at hs
  have sq0:=Rat.mul_nonneg hh0 hh0
  grind

theorem sine_distance {a b : Rat} (ha : Unit a) (hb : Unit b) (q : Nat) :
    qabs (s b q-s a q)≤4*qabs (b-a)+40*delta q := by
  have h:=center_distance ha hb q
  have hu:=center_unit a q; have hv:=center_unit b q
  have hs:=rationalCircleSin_difference_le_qabs hv.1 hv.2 hu.1 hu.2
  change qabs (s b q-s a q)≤2*qabs (center b q-center a q) at hs
  grind

/-- The cosine rule is derived by reflection from the same finite sine rule. -/
theorem cosine_step_error {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a≤b) (q : Nat) :
    qabs (c b q-c a q+(b-a)*p q*s a q) ≤ 20000*((b-a)*(b-a)+delta q) := by
  have ha' : Unit (1-a) := by have h0:=ha.1;have h1:=ha.2;constructor <;> grind
  have hb' : Unit (1-b) := by have h0:=hb.1;have h1:=hb.2;constructor <;> grind
  have hd:=sine_step_error hb' ha' (by grind) q
  rw [show 1-a-(1-b)=b-a by grind] at hd
  have hca:=(ClockTrigonometry.sample_complement ha q).2
  have hcb:=(ClockTrigonometry.sample_complement hb q).2
  have hsb:=(ClockTrigonometry.sample_complement hb q).1
  have hs:=sine_distance ha hb q
  have hh0 : 0≤b-a := by grind
  have hh1 : b-a≤1 := by have h0:=ha.1;have h1:=hb.2;grind
  rw [qabs_eq_self_of_nonneg hh0] at hs
  have htri:=qabs_add_le (s a q-s b q) (s b q-c (1-b) q)
  have he0 : s a q-s b q+(s b q-c (1-b) q)=s a q-c (1-b) q := by grind
  rw [he0] at htri
  have hf1 : qabs (s a q-s b q)=qabs (s b q-s a q) := by
    rw [show s a q-s b q= -(s b q-s a q) by grind,qabs_neg]
  have hf2 : qabs (s b q-c (1-b) q)=qabs (c (1-b) q-s b q) := by
    rw [show s b q-c (1-b) q= -(c (1-b) q-s b q) by grind,qabs_neg]
  rw [hf1,hf2] at htri
  have hp:=p_bounds q
  have e0:=Rat.le_of_lt (meshRadius_pos q)
  have hm0 : 0≤(b-a)*p q := Rat.mul_nonneg hh0 (by grind)
  have hm1 := Rat.mul_le_mul_of_nonneg_left hp.2 hh0
  have herr : qabs ((b-a)*p q*(s a q-c (1-b) q))≤8*(b-a)*(b-a)+552*delta q := by
    rw [qabs_mul,qabs_eq_self_of_nonneg hm0]
    have he : qabs (s a q-c (1-b) q)≤4*(b-a)+276*delta q := by grind
    have h1:=Rat.mul_le_mul_of_nonneg_left he hm0
    have h2:=Rat.mul_le_mul_of_nonneg_right hm1 (show 0≤4*(b-a)+276*delta q by grind)
    have h3:=Rat.mul_le_mul_of_nonneg_right hh1 e0
    grind
  have ht1:=qabs_sub_le (s (1-a) q-c a q) (s (1-b) q-c b q)
  have ht2:=qabs_sub_le ((s (1-a) q-c a q)-(s (1-b) q-c b q))
    (s (1-a) q-s (1-b) q-(b-a)*p q*c (1-b) q)
  have ht3:=qabs_add_le (((s (1-a) q-c a q)-(s (1-b) q-c b q))-
    (s (1-a) q-s (1-b) q-(b-a)*p q*c (1-b) q))
    ((b-a)*p q*(s a q-c (1-b) q))
  have he : ((s (1-a) q-c a q)-(s (1-b) q-c b q))-
    (s (1-a) q-s (1-b) q-(b-a)*p q*c (1-b) q)+
    (b-a)*p q*(s a q-c (1-b) q)=c b q-c a q+(b-a)*p q*s a q := by grind
  rw [he] at ht3
  have sq0:=Rat.mul_nonneg hh0 hh0
  grind

end ComputableAnalysis.CartwrightClockBounds
