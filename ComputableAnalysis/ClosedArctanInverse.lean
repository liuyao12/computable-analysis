import ComputableAnalysis.DyadicMesh
import ComputableAnalysis.SectorAreaReparametrization
import ComputableAnalysis.FiniteBisectionIteration

/-!
# A closed inverse of the rational arctangent clock

The computation bisects the rational lower rectangle sum, not an undecidable
comparison of represented numbers. Its target is t times that same sum at 1.
An explicit rational widening accounts for quadrature uncertainty. Retaining
all earlier widened boxes gives a nested, shrinking inverse computation.
No pi evaluator is used by the executable source search.
-/
namespace ComputableAnalysis
namespace ClosedArctanInverse
open ArctanGeometry

abbrev A (x : Rat) (n : Nat) : QInterval := arctanIntegralRectangleCompute x n

theorem clock_width (x : Rat) (hx : Unit x) (n : Nat) : (A x n).width <= 2*meshRadius n := by
  have hsum := integralSumInterval_width_le_two_squareSum
    (arctanAreaLoopState x n).intervals (arctanAreaLoopState_intervals_unit hx.1 hx.2 n)
  rw [arctanAreaLoopState_squareSum] at hsum
  have hs := Rat.mul_le_mul_of_nonneg_left hx.2 hx.1
  have hsq : x*x <= 1 := by grind
  have hn : 0 <= (2 ^ n : Rat)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 (Rat.pow_pos (by decide)))
  have hm := Rat.mul_le_mul_of_nonneg_right hsq hn
  change (A x n).width <= 2*(x*x / ((2^n : Nat) : Rat)) at hsum
  rw [Rat.natCast_pow] at hsum
  have htwo : ((2 : Nat) : Rat) = 2 := by decide
  rw [htwo] at hsum
  simp only [meshRadius, Rat.div_def, Rat.one_mul] at *
  grind

/-- Cross-stage bounds from two finite covers of the same interval. -/
theorem clock_increment {x y : Rat} (hx : Unit x) (hy : Unit y) (hxy : x <= y) (n m : Nat) :
    (A x n).lo+(y-x)/2 <= (A y m).hi ∧ (A y m).lo <= (A x n).hi+(y-x) := by
  let L := (arctanAreaLoopState x n).intervals
  let R := (arctanAreaLoopState y m).intervals
  have hL : CoversInterval 0 x L := arctanAreaLoopState_intervals_covers hx.1 n
  have hR : CoversInterval 0 y R := arctanAreaLoopState_intervals_covers hy.1 m
  have hext : CoversInterval 0 y (L++[(x,y)]) := CoversInterval.extend_right hL hxy
  have hl := integralLowerSum_le_integralUpperSum_of_covers (by decide : (0 : Rat) <= 0)
    (L++[(x,y)]) R hext hR
  have hu := integralLowerSum_le_integralUpperSum_of_covers (by decide : (0 : Rat) <= 0)
    R (L++[(x,y)]) hR hext
  rw [integralLowerSum_append] at hl
  rw [integralUpperSum_append] at hu
  simp only [integralLowerSum, integralUpperSum, Rat.add_zero] at hl hu
  have hK : (1 : Rat)/2 <= integralKernel y := by
    have hs := Rat.mul_le_mul_of_nonneg_left hy.2 hy.1
    have hsq : y*y <= 1 := by grind
    exact one_div_le_one_div_of_pos_of_le
      (RationalCircle.Stage.one_add_square_pos y) (by grind)
  have hmul := Rat.mul_le_mul_of_nonneg_left hK (by grind : 0 <= y-x)
  have hupper := integralUpperStep_le_width hxy
  change (A x n).lo+integralLowerStep x y <= (A y m).hi at hl
  change (A y m).lo <= (A x n).hi+integralUpperStep x y at hu
  unfold integralLowerStep at hl
  simp only [Rat.div_def] at hmul ⊢
  constructor <;> grind

/-- Inverse separation with explicit finite quadrature errors. -/
theorem clock_inverse_bound {x y : Rat} (hx : Unit x) (hy : Unit y) (n m : Nat) :
    qabs (x-y) <= 2*(qabs ((A x n).lo-(A y m).lo)+(A x n).width+(A y m).width) := by
  have wX := arctanIntegralRectangleCompute_ordered hx.1 n
  have wY := arctanIntegralRectangleCompute_ordered hy.1 m
  have ha := self_le_qabs ((A x n).lo-(A y m).lo)
  have hb := neg_qabs_le_self ((A x n).lo-(A y m).lo)
  by_cases hxy : x <= y
  · have h := (clock_increment hx hy hxy n m).1
    rw [show x-y = -(y-x) by grind, qabs_neg, qabs_eq_self_of_nonneg (by grind : 0 <= y-x)]
    unfold QInterval.width at *
    simp only [Rat.div_def] at h
    grind
  · have h := (clock_increment hy hx (by grind) m n).1
    rw [qabs_eq_self_of_nonneg (by grind : 0 <= x-y)]
    unfold QInterval.width at *
    simp only [Rat.div_def] at h
    grind

def locate (t : Rat) (n : Nat) : QInterval :=
  monotoneTargetBisectionIterate (fun x => (A x n).lo) (t*(A 1 n).lo) n {lo:=0,hi:=1}

def center (t : Rat) (n : Nat) : Rat := (locate t n).lo

theorem locate_unit (t : Rat) (n : Nat) : subintervalOf (locate t n) 0 1 := by
  have ho := monotoneTargetBisectionIterate_ordered
    (f := fun x => (A x n).lo) (I := {lo:=0,hi:=1}) (t*(A 1 n).lo) (by decide) n
  have hs := monotoneTargetBisectionIterate_subinterval
    (f := fun x => (A x n).lo) (I := {lo:=0,hi:=1}) (t*(A 1 n).lo) (by decide) n
  exact ⟨hs.1,ho,hs.2⟩

theorem center_unit (t : Rat) (n : Nat) : Unit (center t n) := by
  have hh := locate_unit t n
  exact ⟨hh.1,Rat.le_trans hh.2.1 hh.2.2⟩

theorem locate_width (t : Rat) (n : Nat) : (locate t n).width = meshRadius n := by
  have h := monotoneTargetBisectionIterate_width (f := fun x => (A x n).lo)
      (I := {lo:=0,hi:=1}) (t*(A 1 n).lo) n
  rw [show ({lo:=0,hi:=1} : QInterval).width = 1 by decide +kernel] at h
  exact h

theorem locate_bracket (t : Rat) (ht : Unit t) (n : Nat) :
    (A (locate t n).lo n).lo <= t*(A 1 n).lo ∧
      t*(A 1 n).lo <= (A (locate t n).hi n).lo := by
  unfold locate
  apply monotoneBisectionIterate_preserves_target_bracket (f := fun x => (A x n).lo)
    (I := {lo:=0,hi:=1}) (t*(A 1 n).lo) (by decide)
  · change (A 0 n).lo <= _
    rw [arctanIntegralRectangleCompute_zero_lower]
    exact Rat.mul_nonneg ht.1 (arctanIntegralRectangleCompute_lower_nonnegative (by decide) n)
  · have hh := Rat.mul_le_mul_of_nonneg_right ht.2
      (arctanIntegralRectangleCompute_lower_nonnegative (by decide : (0 : Rat) <= 1) n)
    simpa only [Rat.one_mul] using hh

theorem center_residual (t : Rat) (ht : Unit t) (n : Nat) :
    qabs ((A (center t n) n).lo-t*(A 1 n).lo) <= 3*meshRadius n := by
  have hb := locate_bracket t ht n
  change (A (center t n) n).lo <= _ ∧ _ <= _ at hb
  have hu := locate_unit t n
  have hc := center_unit t n
  have hr : Unit (locate t n).hi := ⟨Rat.le_trans hu.1 hu.2.1,hu.2.2⟩
  have hi := (clock_increment hc hr hu.2.1 n n).2
  have hw := clock_width (center t n) hc n
  have hmesh := locate_width t n
  change (locate t n).hi-center t n = meshRadius n at hmesh
  have ho := RealRaw.interval_order_of_valid _ (arctanIntegralRectangleRaw_valid hr.1 hr.2) n
  have habs : qabs ((A (center t n) n).lo-t*(A 1 n).lo) =
      t*(A 1 n).lo-(A (center t n) n).lo := by
    rw [show (A (center t n) n).lo-t*(A 1 n).lo =
        -(t*(A 1 n).lo-(A (center t n) n).lo) by grind,
      qabs_neg,qabs_eq_self_of_nonneg (by change 0 <= _; grind)]
  rw [habs]
  change (A (center t n) n).lo <= _ ∧ _ <= _ at hb
  change (A (locate t n).hi n).lo <= (A (center t n) n).hi+_ at hi
  unfold QInterval.width at hw
  grind

/-- Quantitative Cauchy estimate for the independently located rational roots. -/
theorem centers_close (t : Rat) (ht : Unit t) (n m : Nat) :
    qabs (center t n-center t m) <= 14*(meshRadius n+meshRadius m) := by
  have hn := center_residual t ht n
  have hm := center_residual t ht m
  have hnU := center_unit t n
  have hmU := center_unit t m
  have wx := clock_width _ hnU n
  have wy := clock_width _ hmU m
  have w1n := clock_width 1 (by constructor <;> decide) n
  have w1m := clock_width 1 (by constructor <;> decide) m
  have h1ov := (RealRaw.compareAt_overlap_iff _ _ n m).1
    (RealRaw.allStagesOverlap_refl (arctanIntegralRectangleRaw 1)
      (arctanIntegralRectangleRaw_valid (by decide) (by decide)) n m)
  change (A 1 n).Overlaps (A 1 m) at h1ov
  have hbase : qabs ((A 1 n).lo-(A 1 m).lo) <= 2*(meshRadius n+meshRadius m) := by
    unfold QInterval.Overlaps QInterval.width at *
    have zn := Rat.le_of_lt (meshRadius_pos n)
    have zm := Rat.le_of_lt (meshRadius_pos m)
    apply qabs_le_of_neg_le_le <;> grind
  have htarget : qabs (t*(A 1 n).lo-t*(A 1 m).lo) <= 2*(meshRadius n+meshRadius m) := by
    rw [show t*(A 1 n).lo-t*(A 1 m).lo = t*((A 1 n).lo-(A 1 m).lo) by grind,
      qabs_mul,qabs_eq_self_of_nonneg ht.1]
    have h := Rat.mul_le_mul_of_nonneg_right ht.2 (qabs_nonneg ((A 1 n).lo-(A 1 m).lo))
    grind
  have h12 := qabs_add_le ((A (center t n) n).lo-t*(A 1 n).lo)
    (t*(A 1 n).lo-t*(A 1 m).lo)
  have h123 := qabs_sub_le
    (((A (center t n) n).lo-t*(A 1 n).lo)+(t*(A 1 n).lo-t*(A 1 m).lo))
    ((A (center t m) m).lo-t*(A 1 m).lo)
  have he : ((A (center t n) n).lo-t*(A 1 n).lo)+(t*(A 1 n).lo-t*(A 1 m).lo)-
      ((A (center t m) m).lo-t*(A 1 m).lo) =
      (A (center t n) n).lo-(A (center t m) m).lo := by grind
  rw [he] at h123
  have hi := clock_inverse_bound hnU hmU n m
  grind

def candidate (t : Rat) : RealRaw where
  compute := fun n => {lo:=center t n,hi:=center t n}

def radius (n : Nat) : Rat := 28*meshRadius n

theorem radius_shrinks : ShrinksToZero radius := by
  apply shrinksToZero_of_natOverSuccBound (C:=28)
  intro n
  have h := Rat.mul_le_mul_of_nonneg_left (meshRadius_le n) (by decide : (0 : Rat) <= 28)
  simpa only [radius,Rat.div_def,Rat.one_mul, show ((28 : Nat) : Rat) = 28 by decide +kernel] using h

theorem candidate_future (t : Rat) (ht : Unit t) (n m : Nat) (hnm : n <= m) :
    (QInterval.expand ((candidate t).compute n) (radius n)).ContainsInterval ((candidate t).compute m) := by
  have hh := centers_close t ht n m
  have hm := meshRadius_antitone hnm
  have hu := self_le_qabs (center t n-center t m)
  have hl := neg_qabs_le_self (center t n-center t m)
  change center t n-radius n <= center t m ∧ center t m <= center t n+radius n
  unfold radius
  constructor <;> grind

def stabilized (t : Rat) : RealRaw := RealRaw.prefixStabilize (candidate t) radius

theorem stabilized_valid (t : Rat) (ht : Unit t) : (stabilized t).Valid := by
  apply RealRaw.prefixStabilize_valid_of_future
    (fun n => by change 0 <= center t n-center t n; grind)
    (candidate := candidate t) (radius := radius)
  · intro eps
    exact ⟨0,fun n _ => by change center t n-center t n <= eps.val; have hp := eps.property; grind⟩
  · exact candidate_future t ht
  · exact radius_shrinks

def raw (t : Rat) : RealRaw where
  compute := fun n => QInterval.intersection {lo:=0,hi:=1} ((stabilized t).compute n)

theorem raw_contains_centers (t : Rat) (ht : Unit t) (n m : Nat) (hnm : n <= m) :
    (raw t).compute n |>.ContainsInterval ((candidate t).compute m) := by
  exact QInterval.intersection_contains (center_unit t m)
    (RealRaw.prefixStabilize_contains_future (candidate_future t ht) n m hnm)

theorem raw_unit (t : Rat) (ht : Unit t) (n : Nat) : subintervalOf ((raw t).compute n) 0 1 := by
  have h := raw_contains_centers t ht n n (Nat.le_refl _)
  have hc := QInterval.intersection_contained_left ({lo:=0,hi:=1} : QInterval) ((stabilized t).compute n)
  exact ⟨hc.1,Rat.le_trans h.1 h.2,hc.2⟩

theorem raw_valid (t : Rat) (ht : Unit t) : (raw t).Valid := by
  have H := stabilized_valid t ht
  refine ⟨?_,?_,?_⟩
  · intro n
    have h := (raw_unit t ht n).2.1
    change 0 <= ((raw t).compute n).hi-((raw t).compute n).lo
    grind
  · intro n m hnm
    have h := H.2.1 n m hnm
    refine ⟨?_,(raw_unit t ht m).2.1,?_⟩
    · change max 0 _ <= max 0 _
      grind
    · change min 1 _ <= min 1 _
      grind
  · intro eps
    obtain ⟨N,hN⟩ := H.2.2 eps
    exact ⟨N,fun n hn => Rat.le_trans (QInterval.width_le_of_contains
      (QInterval.intersection_contained_right ({lo:=0,hi:=1} : QInterval) ((stabilized t).compute n))) (hN n hn)⟩


private theorem le_of_slack {a b : Rat} (h : ∀ eps : QPos, a <= b+eps.val) : a <= b := by
  by_cases hab : a <= b
  · exact hab
  · let eps : QPos := ⟨(a-b)/2, by
      rw [Rat.div_def]
      exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 (by decide))⟩
    have hh := h eps
    dsimp [eps] at hh
    simp only [Rat.div_def] at hh
    grind

open SectorAreaReparametrization

/-- The native interval image of every retained source box overlaps every
stage of its scaled endpoint target. This closes the inverse's semantic
obligation rather than assuming a preimage has been attained. -/
theorem image_overlaps (t : Rat) (ht : Unit t) (k q j : Nat) :
    (arctanOnUnitRegular_intervalRegular.evalInterval ((raw t).compute k)
      (raw_unit t ht k) q).Overlaps ((arctanOnUnitRegularTarget t ht).value.compute j) := by
  let X := arctanOnUnitRegular_intervalRegular.evalInterval ((raw t).compute k) (raw_unit t ht k) q
  let Y := (arctanOnUnitRegularTarget t ht).value.compute j
  have hslack : ∀ eps : QPos, X.lo <= Y.hi+eps.val ∧ Y.lo <= X.hi+eps.val := by
    intro eps
    obtain ⟨N,hN⟩ := radius_shrinks eps
    let n := max N (max k (angleOnUnitRegularSchedule.stage j))
    have hnN : N <= n := by dsimp [n]; omega
    have hnk : k <= n := by dsimp [n]; omega
    have hnj : angleOnUnitRegularSchedule.stage j <= n := by dsimp [n]; omega
    have hc := raw_contains_centers t ht k n hnk
    have hu := center_unit t n
    have hp := arctanOnUnitRegular_intervalRegular.contains_point_values
      ((raw t).compute k) (raw_unit t ht k) (center t n) hu q hc.1 hc.2
    rw [arctanOnUnitRegular_compute (center t n) hu q] at hp
    have hov := (RealRaw.compareAt_overlap_iff _ _ (angleOnUnitRegularSchedule.stage q) n).1
      (RealRaw.allStagesOverlap_refl (arctanIntegralRectangleRaw (center t n))
        (arctanIntegralRectangleRaw_valid hu.1 hu.2) (angleOnUnitRegularSchedule.stage q) n)
    change (A (center t n) (angleOnUnitRegularSchedule.stage q)).Overlaps (A (center t n) n) at hov
    have wy := (arctanIntegralRectangleRaw_valid (by decide : (0 : Rat) <= 1) (by decide)).2.1
      (angleOnUnitRegularSchedule.stage j) n hnj
    change (A 1 (angleOnUnitRegularSchedule.stage j)).lo <= (A 1 n).lo ∧
      (A 1 n).lo <= (A 1 n).hi ∧ (A 1 n).hi <= (A 1 (angleOnUnitRegularSchedule.stage j)).hi at wy
    have yl := Rat.mul_le_mul_of_nonneg_left wy.1 ht.1
    have yh := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans wy.2.1 wy.2.2) ht.1
    have ylo : Y.lo = t*(A 1 (angleOnUnitRegularSchedule.stage j)).lo := by
      simp only [Y,arctanOnUnitRegularTarget,RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos ht.1]
      rw [arctanOnUnitRegularUpper_compute]
    have yhi : Y.hi = t*(A 1 (angleOnUnitRegularSchedule.stage j)).hi := by
      simp only [Y,arctanOnUnitRegularTarget,RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos ht.1]
      rw [arctanOnUnitRegularUpper_compute]
    rw [← ylo] at yl
    rw [← yhi] at yh
    have res := center_residual t ht n
    have wn := clock_width _ hu n
    have rb := hN n hnN
    have zn := Rat.le_of_lt (meshRadius_pos n)
    have hpos := self_le_qabs ((A (center t n) n).lo-t*(A 1 n).lo)
    have hneg := neg_qabs_le_self ((A (center t n) n).lo-t*(A 1 n).lo)
    change X.ContainsInterval (A (center t n) (angleOnUnitRegularSchedule.stage q)) at hp
    unfold QInterval.ContainsInterval QInterval.Overlaps QInterval.width radius at *
    constructor <;> grind
  exact ⟨le_of_slack (fun eps => (hslack eps).1), le_of_slack (fun eps => (hslack eps).2)⟩

/-- A fully inhabited inverse search: the executable function is specified
above and all validity, range and forward-identity fields are proved. -/
def search (t : Rat) (ht : Unit t) :
    InverseBisectionSearch arctanOnUnitRegular_invertible (arctanOnUnitRegularTarget t ht) where
  compute_preimage := (raw t).compute
  valid_preimage := raw_valid t ht
  preimage_subinterval := raw_unit t ht
  value_overlaps := fun n => image_overlaps t ht n n n
  forward_equiv_target := by
    apply ContinuousFunctionOnInterval.applyRealRaw_equiv_of_applyCandidate_overlap
      arctanOnUnitRegular_continuous (raw t) (raw_valid t ht) (raw_unit t ht)
      (arctanOnUnitRegularTarget t ht).value (arctanOnUnitRegularTarget t ht).value_valid
    intro n
    exact image_overlaps t ht
      (arctanOnUnitRegular_continuous.inputStage (raw t) (raw_valid t ht) n) n n

/-- The closed provider for the existing public geometric sine and cosine. -/
def provider : IntegralIdentities.ArctanInverseBisection where
  branch := arctanOnUnitRegular_invertible
  branch_separation_resolves := arctanOnUnitRegular_separation_resolves
  branch_is_geometric := arctanOnUnitRegular_equivalent_geometric
  targetAt := arctanOnUnitRegularTarget
  targetAt_equiv_halfQuarterTurn := arctanOnUnitRegularTarget_equiv_halfQuarterTurn
  bisectionAt := search

/-- Runtime equation: no hidden inverse provider remains. -/
theorem provider_compute (t : Rat) (ht : Unit t) (n : Nat) :
    (provider.tangentAt t ht).compute n = (raw t).compute n := rfl

/-- Explicit convergence rate of the source boxes. -/
theorem raw_width (t : Rat) (n : Nat) : ((raw t).compute n).width <= 56*meshRadius n := by
  have h1 := QInterval.width_le_of_contains
    (QInterval.intersection_contained_right ({lo:=0,hi:=1} : QInterval) ((stabilized t).compute n))
  have h2 := RealRaw.prefixStabilize_width_le_current_expand (candidate t) radius n
  change ((stabilized t).compute n).width <= _ at h2
  change ((raw t).compute n).width <= _ at h1
  have hzero : ((candidate t).compute n).width = 0 := by change center t n-center t n=0; grind
  rw [hzero] at h2
  dsimp [radius] at h2
  grind

end ClosedArctanInverse
end ComputableAnalysis
