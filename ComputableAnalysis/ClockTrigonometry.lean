import ComputableAnalysis.ClosedArctanInverse
import ComputableAnalysis.CosineFTC
import ComputableAnalysis.CosineIntegralViaFTC
import ComputableAnalysis.IntervalSelections

/-!
# Closed trigonometry from the rational arctangent clock

The internal argument t is a fraction of a quarter turn, 0 <= t <= 1.
The public `sinPi` and `cosPi` below retain the earlier pi-normalized argument.
No inverse provider is assumed: ClosedArctanInverse.provider is constructed.
-/
namespace ComputableAnalysis
namespace ClockTrigonometry
open ClosedArctanInverse ArctanGeometry SinPiIntegral IntervalSelections
open GeometricRotationODE

private theorem target_separation (f : Rat -> Rat) {a b : Rat} (hab : a <= b)
    (I : QInterval) (hI : I.lo <= I.hi) (n : Nat) :
    monotoneTargetBisectionIterate f a n I = monotoneTargetBisectionIterate f b n I ∨
    (monotoneTargetBisectionIterate f a n I).hi <=
      (monotoneTargetBisectionIterate f b n I).lo := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    let L := monotoneTargetBisectionIterate f a n I
    let R := monotoneTargetBisectionIterate f b n I
    have hL := monotoneTargetBisectionIterate_ordered (f:=f) a hI n
    have hR := monotoneTargetBisectionIterate_ordered (f:=f) b hI n
    change L=R ∨ L.hi <= R.lo at ih
    change monotoneTargetBisectionStep f a L = monotoneTargetBisectionStep f b R ∨
      (monotoneTargetBisectionStep f a L).hi <= (monotoneTargetBisectionStep f b R).lo
    rcases ih with he | hs
    · rw [he]
      by_cases hb : b <= f R.midpoint
      · have ha : a <= f R.midpoint := Rat.le_trans hab hb
        simp only [monotoneTargetBisectionStep,if_pos ha,if_pos hb]
        exact Or.inl trivial
      · by_cases ha : a <= f R.midpoint
        · simp only [monotoneTargetBisectionStep,if_pos ha,if_neg hb]
          exact Or.inr Rat.le_refl
        · simp only [monotoneTargetBisectionStep,if_neg ha,if_neg hb]
          exact Or.inl trivial
    · have hl := monotoneTargetBisectionStep_subinterval (f:=f) a hL
      have hr := monotoneTargetBisectionStep_subinterval (f:=f) b hR
      exact Or.inr (Rat.le_trans hl.2 (Rat.le_trans hs hr.1))

theorem center_mono {s t : Rat} (hst : s <= t) (n : Nat) : center s n <= center t n := by
  have h := Rat.mul_le_mul_of_nonneg_right hst
    (arctanIntegralRectangleCompute_lower_nonnegative (by decide : (0 : Rat) <= 1) n)
  have hd := target_separation (fun x => (A x n).lo) h ({lo:=0,hi:=1} : QInterval) (by decide) n
  change locate s n=locate t n ∨ (locate s n).hi <= (locate t n).lo at hd
  rcases hd with he | hh
  · unfold center; rw [he]; exact Rat.le_refl
  · exact Rat.le_trans (locate_unit s n).2.1 hh

/-- Quarter-turn sine and cosine: two coordinates of the same closed source. -/
def sine (t : Rat) : RealRaw where
  compute := fun n => rationalCircleSinInterval ((ClosedArctanInverse.raw t).compute n)
def cosine (t : Rat) : RealRaw where
  compute := fun n => rationalCircleCosInterval ((ClosedArctanInverse.raw t).compute n)

theorem sine_valid {t : Rat} (ht : Unit t) : (sine t).Valid :=
  rationalCircleSinInterval_valid (ClosedArctanInverse.raw t).compute (ClosedArctanInverse.raw_valid t ht)
    (fun n => let h:=ClosedArctanInverse.raw_unit t ht n; ⟨h.1,h.2.2⟩)
theorem cosine_valid {t : Rat} (ht : Unit t) : (cosine t).Valid := by
  have hh : 0 <= t/2 ∧ t/2 <= (1 : Rat)/2 := by
    have h0:=ht.1; have h1:=ht.2
    simp only [Rat.div_def]; constructor <;> grind
  have h := cosPiRawOfArctan_valid ClosedArctanInverse.provider (t/2) hh
  have he : 2*(t/2)=t := by simp only [Rat.div_def]; grind
  change RealRaw.ValidCompute (fun n => rationalCircleCosInterval
    ((ClosedArctanInverse.raw (2*(t/2))).compute n)) at h
  rw [he] at h
  exact h

def s (t : Rat) (n : Nat) : Rat := rationalCircleSin (center t n)
def c (t : Rat) (n : Nat) : Rat := rationalCircleCos (center t n)

theorem s_mem {t : Rat} (ht : Unit t) (n : Nat) : InBox (s t n) ((sine t).compute n) := by
  have hc := raw_contains_centers t ht n n (Nat.le_refl n)
  have hu := ClosedArctanInverse.raw_unit t ht n
  have hv := center_unit t n
  change ((ClosedArctanInverse.raw t).compute n).lo <= center t n ∧
    center t n <= ((ClosedArctanInverse.raw t).compute n).hi at hc
  exact ⟨rationalCircleSin_mono_public hu.1 hc.1 hv.2,
    rationalCircleSin_mono_public hv.1 hc.2 hu.2.2⟩

theorem c_mem {t : Rat} (ht : Unit t) (n : Nat) : InBox (c t n) ((cosine t).compute n) := by
  have hc := raw_contains_centers t ht n n (Nat.le_refl n)
  have hu := ClosedArctanInverse.raw_unit t ht n
  have hv := center_unit t n
  change ((ClosedArctanInverse.raw t).compute n).lo <= center t n ∧
    center t n <= ((ClosedArctanInverse.raw t).compute n).hi at hc
  have hL := rationalCircleCos_difference_le_qabs hv.1 hv.2 hu.1 (Rat.le_trans hu.2.1 hu.2.2)
  have hR := rationalCircleCos_difference_le_qabs hu.1 (Rat.le_trans hu.2.1 hu.2.2) hv.1 hv.2
  -- Monotonicity is read from the interval-width theorem, avoiding a private lemma.
  have h1 := (rationalCircleCosInterval_width_le
    (U:={lo:=((ClosedArctanInverse.raw t).compute n).lo,hi:=center t n}) ⟨hu.1,hc.1,hv.2⟩).1
  have h2 := (rationalCircleCosInterval_width_le
    (U:={lo:=center t n,hi:=((ClosedArctanInverse.raw t).compute n).hi}) ⟨hv.1,hc.2,hu.2.2⟩).1
  unfold QInterval.width rationalCircleCosInterval at h1 h2
  change rationalCircleCos ((ClosedArctanInverse.raw t).compute n).hi <= c t n ∧
    c t n <= rationalCircleCos ((ClosedArctanInverse.raw t).compute n).lo
  dsimp [c]
  constructor <;> grind

theorem add_mem {X Y : RealRaw} {x y : Rat} {n : Nat}
    (hx : InBox x (X.compute n)) (hy : InBox y (Y.compute n)) :
    InBox (x+y) ((X+Y).compute n) := by
  change _ <= x+y ∧ x+y <= _
  change (X.compute n).lo+(Y.compute n).lo <= x+y ∧ x+y <= (X.compute n).hi+(Y.compute n).hi
  unfold InBox at hx hy
  constructor <;> grind

theorem rat_mem (x : Rat) (n : Nat) : InBox x ((RealRaw.ofRat x).compute n) := ⟨Rat.le_refl,Rat.le_refl⟩

/-- Eliminate arbitrary proof-side rational slack to obtain literal all-stage overlap. -/
theorem equiv_of_samples {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    (x y : Nat -> Rat) (hx : ∀ n, InBox (x n) (X.compute n))
    (hy : ∀ n, InBox (y n) (Y.compute n))
    (he : ∀ eps : QPos, ∃ N, ∀ n, N <= n -> qabs (x n-y n) <= eps.val) : X.Equiv Y := by
  have h := expanded_overlaps_of_selected_error hX hY x y hx hy 0 (by
    intro eps
    obtain ⟨N,hN⟩ := he eps
    refine ⟨N,fun n hn => ?_⟩
    have hh:=hN n hn
    rw [show y n-x n = -(x n-y n) by grind,qabs_neg,Rat.zero_add]
    exact hh)
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hh := h n n
  unfold QInterval.expand QInterval.Overlaps at hh
  unfold QInterval.Overlaps
  constructor <;> grind

theorem equiv_of_sample_equality {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    (x y : Nat -> Rat) (hx : ∀ n, InBox (x n) (X.compute n))
    (hy : ∀ n, InBox (y n) (Y.compute n)) (he : ∀ n, x n=y n) : X.Equiv Y := by
  apply equiv_of_samples hX hY x y hx hy
  intro eps
  refine ⟨0,fun n _ => ?_⟩
  rw [he n,Rat.sub_self]
  have hz : qabs (0 : Rat)=0 := by decide +kernel
  rw [hz]; exact Rat.le_of_lt eps.property

theorem equiv_of_geometric_error {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    (x y : Nat -> Rat) (hx : ∀ n, InBox (x n) (X.compute n))
    (hy : ∀ n, InBox (y n) (Y.compute n)) (K : Nat)
    (he : ∀ n, qabs (x n-y n) <= (K : Rat)*meshRadius n) : X.Equiv Y := by
  have hs : ShrinksToZero (fun n => (K : Rat)*meshRadius n) := by
    apply shrinksToZero_of_natOverSuccBound (C:=K)
    intro n
    have hh := Rat.mul_le_mul_of_nonneg_left (meshRadius_le n) (Rat.natCast_nonneg (a:=K))
    simpa only [Rat.div_def,Rat.one_mul,Rat.mul_assoc] using hh
  apply equiv_of_samples hX hY x y hx hy
  intro eps
  obtain ⟨N,hN⟩ := hs eps
  exact ⟨N,fun n hn => Rat.le_trans (he n) (hN n hn)⟩

theorem sample_unit (t : Rat) (n : Nat) : c t n*c t n+s t n*s t n=1 := by
  exact RationalCircle.Trigonometry.cos_sq_add_sin_sq (center t n)

theorem pythagorean {t : Rat} (ht : Unit t) :
    (RealRaw.mul (cosine t) (cosine t)+RealRaw.mul (sine t) (sine t)).Equiv (RealRaw.ofRat 1) := by
  apply equiv_of_sample_equality
    (RealRaw.add_valid (RealRaw.mul_valid (cosine_valid ht) (cosine_valid ht))
      (RealRaw.mul_valid (sine_valid ht) (sine_valid ht))) (RealRaw.ofRat_valid 1)
    (fun n=>c t n*c t n+s t n*s t n) (fun _=>1)
    (fun n=>add_mem (mul_mem (c_mem ht n) (c_mem ht n)) (mul_mem (s_mem ht n) (s_mem ht n)))
    (rat_mem 1)
  exact sample_unit t


def differenceParameter (u v : Rat) : Rat := (v-u)/(1+u*v)

theorem differenceParameter_unit {u v : Rat} (hu : Unit u) (hv : Unit v) (huv : u <= v) :
    Unit (differenceParameter u v) := by
  have hp : 0 < 1+u*v := by have h:=Rat.mul_nonneg hu.1 hv.1; grind
  have hi := Rat.le_of_lt ((Rat.inv_pos).2 hp)
  have hc := Rat.mul_inv_cancel (1+u*v) (Rat.ne_of_gt hp)
  have hn : 0 <= v-u := by grind
  have hn1 : v-u <= 1+u*v := by have hm:=Rat.mul_nonneg hu.1 hv.1; have h0:=hu.1; have h1:=hv.2; grind
  have hm := Rat.mul_le_mul_of_nonneg_right hn1 hi
  rw [hc] at hm
  exact ⟨Rat.mul_nonneg hn hi,hm⟩

/-- Difference law for the clock, before constructing angular sine identities. -/
theorem difference_clock_error {u v : Rat} (hu : Unit u) (hv : Unit v)
    (huv : u <= v) (n : Nat) :
    qabs ((A (differenceParameter u v) n).lo-((A v n).lo-(A u n).lo)) <= 6*meshRadius n := by
  by_cases heq : u=v
  · subst v
    have hw : differenceParameter u u=0 := by
      simp only [differenceParameter,Rat.sub_self,Rat.div_def,Rat.zero_mul]
    rw [hw,arctanIntegralRectangleCompute_zero_lower,Rat.sub_self,Rat.sub_self]
    have hz : qabs (0 : Rat)=0 := by decide +kernel
    rw [hz]; exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (meshRadius_pos n))
  · have hp : 0 < v-u := by grind
    have hcancel : u+(v-u)=v := by grind
    have he := arctanIntegralRectangleRaw_forward_difference_equiv_tangentChartIncrement
      hu.1 hu.2 hp (by rw [hcancel]; exact hv.2)
    rw [hcancel] at he
    have hw : tangentChartIncrement u (v-u)=differenceParameter u v := by
      unfold tangentChartIncrement differenceParameter
      congr 1
      grind
    rw [hw] at he
    have ho := (RealRaw.compareAt_overlap_iff _ _ n n).1 (he n)
    change (A v n).lo-(A u n).hi <= (A (differenceParameter u v) n).hi ∧
      (A (differenceParameter u v) n).lo <= (A v n).hi-(A u n).lo at ho
    have wu := clock_width u hu n
    have wv := clock_width v hv n
    have ww := clock_width _ (differenceParameter_unit hu hv huv) n
    unfold QInterval.width at *
    have hr0 := Rat.le_of_lt (meshRadius_pos n)
    apply qabs_le_of_neg_le_le <;> grind

/-- Rational coordinate difference formula. All denominators are positive. -/
theorem difference_coordinates {u v : Rat} (hu : Unit u) (hv : Unit v) :
    rationalCircleCos (differenceParameter u v)=rationalCircleCos v*rationalCircleCos u+
      rationalCircleSin v*rationalCircleSin u ∧
    rationalCircleSin (differenceParameter u v)=rationalCircleSin v*rationalCircleCos u-
      rationalCircleCos v*rationalCircleSin u := by
  have hp : 0 < 1+u*v := by have h:=Rat.mul_nonneg hu.1 hv.1; grind
  have hd : RationalCircle.Trigonometry.chartAddDen v (-u) ≠ 0 := by
    unfold RationalCircle.Trigonometry.chartAddDen
    have he : 1-v*(-u)=1+u*v := by grind
    rw [he]; exact Rat.ne_of_gt hp
  have hc := RationalCircle.Trigonometry.composedCos_eq_cos_chartAdd hd
  have hs := RationalCircle.Trigonometry.composedSin_eq_sin_chartAdd hd
  have he : RationalCircle.Trigonometry.chartAddParameter v (-u)=differenceParameter u v := by
    unfold RationalCircle.Trigonometry.chartAddParameter RationalCircle.Trigonometry.chartAddNum
      RationalCircle.Trigonometry.chartAddDen differenceParameter
    congr 1 <;> grind
  rw [he] at hc hs
  change rationalCircleCos v*rationalCircleCos (-u)-rationalCircleSin v*rationalCircleSin (-u)=rationalCircleCos (differenceParameter u v) at hc
  change rationalCircleCos v*rationalCircleSin (-u)+rationalCircleSin v*rationalCircleCos (-u)=rationalCircleSin (differenceParameter u v) at hs
  have hcos : rationalCircleCos (-u)=rationalCircleCos u := RationalCircle.Trigonometry.cos_neg u
  have hsin : rationalCircleSin (-u)= -rationalCircleSin u := RationalCircle.Trigonometry.sin_neg u
  rw [hcos,hsin] at hc hs
  constructor <;> grind

/-- The closed inverse transports the clock difference into a difference of
normalized quarter-turn inputs with an explicit rational error budget. -/
theorem center_difference {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a <= b) (n : Nat) :
    qabs (center (b-a) n-differenceParameter (center a n) (center b n)) <= 38*meshRadius n := by
  have hd : Unit (b-a) := by have a0:=ha.1; have b1:=hb.2; constructor <;> grind
  have hu := center_unit a n
  have hv := center_unit b n
  have hc := center_mono hab n
  have hw := differenceParameter_unit hu hv hc
  have huE := center_residual a ha n
  have hvE := center_residual b hb n
  have hdE := center_residual (b-a) hd n
  have hwE := difference_clock_error hu hv hc n
  let p := (A 1 n).lo
  let u := center a n
  let v := center b n
  let z := center (b-a) n
  let w := differenceParameter u v
  have ht1 := qabs_sub_le ((A v n).lo-b*p) ((A u n).lo-a*p)
  have he1 : ((A v n).lo-b*p)-((A u n).lo-a*p)=((A v n).lo-(A u n).lo)-(b-a)*p := by grind
  rw [he1] at ht1
  have ht2 := qabs_add_le ((A w n).lo-((A v n).lo-(A u n).lo))
    (((A v n).lo-(A u n).lo)-(b-a)*p)
  have he2 : ((A w n).lo-((A v n).lo-(A u n).lo))+
    (((A v n).lo-(A u n).lo)-(b-a)*p)=(A w n).lo-(b-a)*p := by grind
  rw [he2] at ht2
  have ht3 := qabs_sub_le ((A z n).lo-(b-a)*p) ((A w n).lo-(b-a)*p)
  have he3 : ((A z n).lo-(b-a)*p)-((A w n).lo-(b-a)*p)=(A z n).lo-(A w n).lo := by grind
  rw [he3] at ht3
  have inv := clock_inverse_bound (center_unit (b-a) n) hw n n
  have wz := clock_width z (center_unit (b-a) n) n
  have ww := clock_width w hw n
  grind

theorem sample_difference {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a <= b) (n : Nat) :
    qabs (c (b-a) n-(c b n*c a n+s b n*s a n)) <= 152*meshRadius n ∧
    qabs (s (b-a) n-(s b n*c a n-c b n*s a n)) <= 76*meshRadius n := by
  have hu := center_unit a n
  have hv := center_unit b n
  have hw := differenceParameter_unit hu hv (center_mono hab n)
  have hz := center_unit (b-a) n
  have hc := center_difference ha hb hab n
  have hC := rationalCircleCos_difference_le_qabs hz.1 hz.2 hw.1 hw.2
  have hS := rationalCircleSin_difference_le_qabs hz.1 hz.2 hw.1 hw.2
  have he := difference_coordinates hu hv
  rw [he.1] at hC
  rw [he.2] at hS
  constructor <;> dsimp [c,s] <;> grind

theorem cosine_difference {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a <= b) :
    (cosine (b-a)).Equiv (RealRaw.mul (cosine b) (cosine a)+RealRaw.mul (sine b) (sine a)) := by
  have hd : Unit (b-a) := by have h0:=ha.1; have h1:=hb.2; constructor <;> grind
  apply equiv_of_geometric_error (cosine_valid hd)
    (RealRaw.add_valid (RealRaw.mul_valid (cosine_valid hb) (cosine_valid ha))
      (RealRaw.mul_valid (sine_valid hb) (sine_valid ha)))
    (c (b-a)) (fun n=>c b n*c a n+s b n*s a n) (c_mem hd)
    (fun n=>add_mem (mul_mem (c_mem hb n) (c_mem ha n)) (mul_mem (s_mem hb n) (s_mem ha n))) 152
  exact fun n => (sample_difference ha hb hab n).1

theorem sine_difference {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a <= b) :
    (sine (b-a)).Equiv (RealRaw.mul (sine b) (cosine a)-RealRaw.mul (cosine b) (sine a)) := by
  have hd : Unit (b-a) := by have h0:=ha.1; have h1:=hb.2; constructor <;> grind
  apply equiv_of_geometric_error (sine_valid hd)
    (RealRaw.sub_valid (RealRaw.mul_valid (sine_valid hb) (cosine_valid ha))
      (RealRaw.mul_valid (cosine_valid hb) (sine_valid ha)))
    (s (b-a)) (fun n=>s b n*c a n-c b n*s a n) (s_mem hd)
    (fun n=>sub_mem (mul_mem (s_mem hb n) (c_mem ha n)) (mul_mem (c_mem hb n) (s_mem ha n))) 76
  exact fun n => (sample_difference ha hb hab n).2

end ClockTrigonometry
end ComputableAnalysis
