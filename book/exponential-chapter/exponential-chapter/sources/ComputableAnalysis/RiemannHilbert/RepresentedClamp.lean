import ComputableAnalysis.RiemannHilbert.UnitIntervalApproximation

/-! Clamping arbitrary valid represented reals into the closed unit
interval. The evaluator applies the rational clamp to box endpoints;
monotonicity and the exact distance bound prove validity and continuity. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
open ComplexRaw FunctionTheory

theorem clamp_mono {a b : Rat} (h : a ≤ b) : clamp a ≤ clamp b := by
  unfold clamp
  grind

theorem clamp_width {a b : Rat} (h : a ≤ b) : clamp b-clamp a ≤ b-a := by
  unfold clamp
  grind

theorem clamp_sub_le (a b R : Rat) (hR : 0 ≤ R) (hab : a-b ≤ R) : clamp a-clamp b ≤ R := by
  by_cases h : a ≤ b
  · have hm := clamp_mono h
    grind only
  · have hw := clamp_width (Rat.le_of_lt (show b < a by grind only))
    grind only

theorem clamp_complement (a : Rat) : clamp (1-a)=1-clamp a := by
  unfold clamp
  grind

def clipRaw (x : RealRaw) : RealRaw where
  compute n := { lo := clamp (x.compute n).lo,hi := clamp (x.compute n).hi }

theorem clipRaw_ordered (x : RealRaw) (hx : x.Valid) (n : Nat) :
    0 ≤ (clipRaw x |>.compute n).width := by
  have h := clamp_mono (RealRaw.interval_order_of_valid x hx n)
  change 0 ≤ clamp (x.compute n).hi-clamp (x.compute n).lo
  grind only

theorem clipRaw_valid (x : RealRaw) (hx : x.Valid) : (clipRaw x).Valid := by
  refine ⟨clipRaw_ordered x hx,?_,?_⟩
  · intro n m hnm
    have h := hx.2.1 n m hnm
    exact ⟨clamp_mono h.1,clamp_mono h.2.1,clamp_mono h.2.2⟩
  · intro eps
    obtain ⟨N,hN⟩ := hx.2.2 eps
    refine ⟨N,fun n hn => ?_⟩
    exact Rat.le_trans (clamp_width (RealRaw.interval_order_of_valid x hx n)) (hN n hn)

def clip (x : RealRaw) (hx : x.Valid) : Point where
  value := clipRaw x
  valid := clipRaw_valid x hx
  lower _ m := (clamp_bounds (x.compute m).hi).1
  upper n _ := (clamp_bounds (x.compute n).lo).2

theorem clip_congr (x y : RealRaw) (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) : clip x hx ≈ clip y hy := by
  intro n
  have h := (RealRaw.compareAt_overlap_iff x y n n).1 (hxy n)
  exact (RealRaw.compareAt_overlap_iff _ _ n n).2 ⟨clamp_mono h.1,clamp_mono h.2⟩

theorem clip_identity (t : Point) : clip t.value t.valid ≈ t := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hl := t.lower 0 n
  have hu := t.upper n 0
  have ho := RealRaw.interval_order_of_valid t.value t.valid n
  change 0 ≤ (t.value.compute n).hi at hl
  change (t.value.compute n).lo ≤ 1 at hu
  change clamp (t.value.compute n).lo ≤ (t.value.compute n).hi ∧
    (t.value.compute n).lo ≤ clamp (t.value.compute n).hi
  unfold clamp
  grind

theorem clip_zero (x : RealRaw) (hx : x.Valid) (h0 : x.Le (RealRaw.ofRat 0)) : clip x hx ≈ zero := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hl := h0 n 0
  change (x.compute n).lo ≤ 0 at hl
  have hr := clamp_bounds (x.compute n).hi
  change clamp (x.compute n).lo ≤ 0 ∧ 0 ≤ clamp (x.compute n).hi
  unfold clamp at *
  grind

theorem clip_one (x : RealRaw) (hx : x.Valid) (h1 : (RealRaw.ofRat 1).Le x) : clip x hx ≈ one := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hh := h1 0 n
  change 1 ≤ (x.compute n).hi at hh
  have hr := clamp_bounds (x.compute n).lo
  change clamp (x.compute n).lo ≤ 1 ∧ 1 ≤ clamp (x.compute n).hi
  unfold clamp at *
  grind

theorem clip_distance (x y : RealRaw) (hx : x.Valid) (hy : y.Valid) (R : Rat) (hR : 0 ≤ R)
    (hxy : Small (sub (ofRealRaw x) (ofRealRaw y)) R) :
    Small (sub (scalar (clip x hx)).val (scalar (clip y hy)).val) R := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n m
    have h := hxy.1 n m
    change -R ≤ (x.compute m).hi + -(y.compute m).lo at h
    have hc := clamp_sub_le (y.compute m).lo (x.compute m).hi R hR (by grind only)
    change -R ≤ clamp (x.compute m).hi + -clamp (y.compute m).lo
    grind only
  · intro n m
    have h := hxy.2.1 n m
    change (x.compute n).lo + -(y.compute n).hi ≤ R at h
    have hc := clamp_sub_le (x.compute n).lo (y.compute n).hi R hR (by grind only)
    change clamp (x.compute n).lo + -clamp (y.compute n).hi ≤ R
    grind only
  · intro n m
    change -R ≤ (0 : Rat)+ -0
    grind only
  · intro n m
    change (0 : Rat)+ -0 ≤ R
    grind only

end ComputableAnalysis.RiemannHilbert.UnitInterval
