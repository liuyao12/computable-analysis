import ComputableAnalysis.ClockTrigIdentities
import ComputableAnalysis.CosinePrimitiveData

/-!
# Uniform finite bounds for the arctangent clock

All expressions in the estimates are rational. The frequency approximants
come from the existing rectangle presentation of twice A(1), proved equivalent
to geometric pi/2. The moment algorithm samples the existing circle evaluator.
No integral endpoint theorem is used for these estimates.
-/
namespace ComputableAnalysis.CartwrightClockBounds
open ClosedArctanInverse ArctanGeometry SinPiIntegral IntervalSelections
open GeometricRotationODE GeometricSineSecant

abbrev Unit (x : Rat) : Prop := 0 ≤ x ∧ x ≤ 1
abbrev delta := ClosedArctanInverse.meshRadius
abbrev s := ClockTrigonometry.s
abbrev c := ClockTrigonometry.c

def frequency : RealRaw := RealRaw.scaleRat 2 (arctanIntegralRectangleRaw 1)
def p (q : Nat) : Rat := 2 * (A 1 q).lo

theorem frequency_valid : frequency.Valid :=
  RealRaw.scaleRat_valid (arctanIntegralRectangleRaw_valid (by decide) (by decide))

theorem p_mem (q : Nat) : InBox (p q) (frequency.compute q) := by
  exact scale_mem ⟨Rat.le_refl,RealRaw.interval_order_of_valid _
    (arctanIntegralRectangleRaw_valid (x:=1) (by decide) (by decide)) q⟩ (by decide)

theorem p_bounds (q : Nat) : 1 ≤ p q ∧ p q ≤ 2 := by
  have h := arctanIntegralRectangleCompute_tangent_box_contains (x := 1) (by decide) q
  have hl := arctanIntegralRectangleCompute_input_mul_kernel_le_lower (x := 1) (by decide) q
  have ho := RealRaw.interval_order_of_valid _
    (arctanIntegralRectangleRaw_valid (x:=1) (by decide) (by decide)) q
  have hk : integralKernel 1 = (1 : Rat)/2 := by decide +kernel
  rw [hk] at hl
  change _ ∧ (A 1 q).hi ≤ 1 at h
  change (A 1 q).lo ≤ (A 1 q).hi at ho
  change 1*(1/2) ≤ (A 1 q).lo at hl
  unfold p
  simp only [Rat.div_def] at hl
  constructor <;> grind

theorem delta_le_one (q : Nat) : delta q ≤ 1 := by
  have h := meshRadius_antitone (Nat.zero_le q)
  have hz : meshRadius 0 = 1 := by decide +kernel
  rw [hz] at h
  exact h

private theorem prefix_mono {a b : Rat} (hab : a ≤ b) (q : Nat) :
    ((ClosedArctanInverse.stabilized a).compute q).lo ≤
      ((ClosedArctanInverse.stabilized b).compute q).lo ∧
    ((ClosedArctanInverse.stabilized a).compute q).hi ≤
      ((ClosedArctanInverse.stabilized b).compute q).hi := by
  induction q with
  | zero =>
      have h := ClockTrigonometry.center_mono hab 0
      change center a 0 - radius 0 ≤ center b 0 - radius 0 ∧
        center a 0 + radius 0 ≤ center b 0 + radius 0
      constructor <;> grind
  | succ q ih =>
      have h := ClockTrigonometry.center_mono hab (q+1)
      change (RealRaw.prefixStabilizeCompute (candidate a).compute radius q).lo ≤
        (RealRaw.prefixStabilizeCompute (candidate b).compute radius q).lo ∧
        (RealRaw.prefixStabilizeCompute (candidate a).compute radius q).hi ≤
        (RealRaw.prefixStabilizeCompute (candidate b).compute radius q).hi at ih
      change max _ (center a (q+1)-radius (q+1)) ≤ max _ (center b (q+1)-radius (q+1)) ∧
        min _ (center a (q+1)+radius (q+1)) ≤ min _ (center b (q+1)+radius (q+1))
      constructor <;> grind

theorem source_mono {a b : Rat} (hab : a ≤ b) (q : Nat) :
    ((ClosedArctanInverse.raw a).compute q).lo ≤ ((ClosedArctanInverse.raw b).compute q).lo ∧
    ((ClosedArctanInverse.raw a).compute q).hi ≤ ((ClosedArctanInverse.raw b).compute q).hi := by
  have h := prefix_mono hab q
  dsimp only [ClosedArctanInverse.raw, QInterval.intersection]
  constructor <;> grind

theorem cos_coordinate_antitone {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    rationalCircleCos b ≤ rationalCircleCos a := by
  have h := (rationalCircleCosInterval_width_le (U := {lo:=a,hi:=b}) ⟨ha,hab,hb⟩).1
  change 0 ≤ rationalCircleCos a-rationalCircleCos b at h
  grind

theorem cosine_endpoints_antitone {a b : Rat} (ha : Unit a) (hb : Unit b)
    (hab : a ≤ b) (q : Nat) :
    ((ClockTrigonometry.cosine b).compute q).lo ≤ ((ClockTrigonometry.cosine a).compute q).lo ∧
    ((ClockTrigonometry.cosine b).compute q).hi ≤ ((ClockTrigonometry.cosine a).compute q).hi := by
  have hs := source_mono hab q
  have hu := raw_unit a ha q
  have hv := raw_unit b hb q
  exact ⟨cos_coordinate_antitone (Rat.le_trans hu.1 hu.2.1) hs.2 hv.2.2,
    cos_coordinate_antitone hu.1 hs.1 (Rat.le_trans hv.2.1 hv.2.2)⟩

theorem cosine_box_bounds {t : Rat} (ht : Unit t) (q : Nat) :
    0 ≤ ((ClockTrigonometry.cosine t).compute q).lo ∧
      ((ClockTrigonometry.cosine t).compute q).hi ≤ 1 := by
  have h := raw_unit t ht q
  exact ⟨(rationalCircleCos_bounds (Rat.le_trans h.1 h.2.1) h.2.2).1,
    (rationalCircleCos_bounds h.1 (Rat.le_trans h.2.1 h.2.2)).2⟩

theorem cosine_width {t : Rat} (ht : Unit t) (q : Nat) :
    ((ClockTrigonometry.cosine t).compute q).width ≤ 224*delta q := by
  have h := (rationalCircleCosInterval_width_le (raw_unit t ht q)).2
  have w := raw_width t q
  change ((ClockTrigonometry.cosine t).compute q).width ≤ _ at h
  grind

/-- Uniform separation of inverse-clock centres at one evaluation stage. -/
theorem center_distance {a b : Rat} (ha : Unit a) (hb : Unit b) (q : Nat) :
    qabs (center b q-center a q) ≤ 2*qabs (b-a)+20*delta q := by
  have h1 := center_residual a ha q
  have h2 := center_residual b hb q
  have hi := clock_inverse_bound (center_unit b q) (center_unit a q) q q
  have wa := clock_width _ (center_unit a q) q
  have wb := clock_width _ (center_unit b q) q
  have hk := arctanIntegralRectangleCompute_tangent_box_contains (x:=1) (by decide) q
  have ho := RealRaw.interval_order_of_valid _
    (arctanIntegralRectangleRaw_valid (x:=1) (by decide) (by decide)) q
  have hz := arctanIntegralRectangleCompute_lower_nonnegative (x:=1) (by decide) q
  have hA : 0 ≤ (A 1 q).lo ∧ (A 1 q).lo ≤ 1 := ⟨hz, Rat.le_trans ho hk.2⟩
  have ht := qabs_sub_le ((A (center b q) q).lo-b*(A 1 q).lo)
    ((A (center a q) q).lo-a*(A 1 q).lo)
  have he : ((A (center b q) q).lo-b*(A 1 q).lo)-
      ((A (center a q) q).lo-a*(A 1 q).lo) =
      ((A (center b q) q).lo-(A (center a q) q).lo)-(b-a)*(A 1 q).lo := by grind
  rw [he] at ht
  have hsum := qabs_add_le
    (((A (center b q) q).lo-(A (center a q) q).lo)-(b-a)*(A 1 q).lo)
    ((b-a)*(A 1 q).lo)
  rw [show (((A (center b q) q).lo-(A (center a q) q).lo)-(b-a)*(A 1 q).lo)+
    (b-a)*(A 1 q).lo = (A (center b q) q).lo-(A (center a q) q).lo by grind] at hsum
  have hm := Rat.mul_le_mul_of_nonneg_left hA.2 (qabs_nonneg (b-a))
  rw [qabs_mul,qabs_eq_self_of_nonneg hA.1] at hsum
  grind

theorem cosine_distance {a b : Rat} (ha : Unit a) (hb : Unit b) (q : Nat) :
    qabs (c b q-c a q) ≤ 8*qabs (b-a)+80*delta q := by
  have h := center_distance ha hb q
  have hu := center_unit b q; have hv := center_unit a q
  have hc := rationalCircleCos_difference_le_qabs hu.1 hu.2 hv.1 hv.2
  change qabs (c b q-c a q) ≤ 4*qabs (center b q-center a q) at hc
  grind

theorem cosine_box_distance {a b : Rat} (ha : Unit a) (hb : Unit b) (q : Nat) :
    ((ClockTrigonometry.cosine a).compute q).hi-
      ((ClockTrigonometry.cosine b).compute q).lo ≤ 8*qabs (b-a)+528*delta q := by
  have ha0 := ClockTrigonometry.c_mem ha q
  have hb0 := ClockTrigonometry.c_mem hb q
  have wa := cosine_width ha q; have wb := cosine_width hb q
  have hc := cosine_distance ha hb q
  have hl := neg_qabs_le_self (c b q-c a q)
  unfold InBox QInterval.width at *
  grind

end ComputableAnalysis.CartwrightClockBounds
