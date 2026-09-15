import ComputableAnalysis.IntervalSelections
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# An optional interpretation in Mathlib's real field

This file is outside the independent foundation. `Represents X r` says
literally that every rational output box of X contains the Mathlib real r.
No correctness of a numerical integral is assumed by this interpretation.
-/
namespace MathlibComparison
open ComputableAnalysis Filter Topology IntervalSelections

def Represents (X : RealRaw) (r : ℝ) : Prop :=
  ∀ n, ((X.compute n).lo : ℝ) ≤ r ∧ r ≤ ((X.compute n).hi : ℝ)

lemma rational_tolerance {eps : ℝ} (h : 0 < eps) :
    ∃ q : QPos, (q.val : ℝ) < eps := by
  obtain ⟨q,hq0,hq1⟩ := exists_rat_btwn h
  exact ⟨⟨q,by exact_mod_cast hq0⟩,hq1⟩

lemma qabs_cast (x : Rat) : (qabs x : ℝ) = |(x : ℝ)| := by
  unfold qabs
  split <;> rename_i h
  · have hn : (x : ℝ) < 0 := by exact_mod_cast h
    simp [abs_of_neg hn]
  · have hn : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_of_not_gt h)
    simp [abs_of_nonneg hn]

lemma selected_tendsto {X : RealRaw} {r : ℝ} (hX : X.Valid)
    (hr : Represents X r) (s : Nat → Rat)
    (hs : ∀ n, InBox (s n) (X.compute n)) :
    Tendsto (fun n => (s n : ℝ)) atTop (𝓝 r) := by
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨q,hq⟩ := rational_tolerance heps
  obtain ⟨N,hN⟩ := hX.2.2 q
  refine ⟨N,fun n hn => ?_⟩
  have hw : ((X.compute n).hi : ℝ)-((X.compute n).lo : ℝ) ≤ (q.val : ℝ) := by
    exact_mod_cast hN n hn
  have hl : ((X.compute n).lo : ℝ) ≤ (s n : ℝ) := by exact_mod_cast (hs n).1
  have hu : (s n : ℝ) ≤ ((X.compute n).hi : ℝ) := by exact_mod_cast (hs n).2
  have hh := hr n
  rw [Real.dist_eq]
  exact abs_lt.2 ⟨by linarith,by linarith⟩

lemma lower_tendsto {X : RealRaw} {r : ℝ} (hX : X.Valid) (hr : Represents X r) :
    Tendsto (fun n => ((X.compute n).lo : ℝ)) atTop (𝓝 r) :=
  selected_tendsto hX hr _ (fun n => ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ hX n⟩)

lemma upper_tendsto {X : RealRaw} {r : ℝ} (hX : X.Valid) (hr : Represents X r) :
    Tendsto (fun n => ((X.compute n).hi : ℝ)) atTop (𝓝 r) :=
  selected_tendsto hX hr _ (fun n => ⟨RealRaw.interval_order_of_valid _ hX n,Rat.le_refl⟩)

lemma represents_of_tendsto {X : RealRaw} {r : ℝ} (hX : X.Valid)
    (s : Nat → Rat) (hs : ∀ n, InBox (s n) (X.compute n))
    (ht : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 r)) : Represents X r := by
  intro n
  constructor
  · apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop n] with m hm
    have hh := IntervalSelections.contains_later hX hm (hs m)
    exact_mod_cast hh.1
  · apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop n] with m hm
    have hh := IntervalSelections.contains_later hX hm (hs m)
    exact_mod_cast hh.2

lemma represents_of_equiv {X Y : RealRaw} {r : ℝ}
    (hX : X.Valid) (hY : Y.Valid) (h : X.Equiv Y) (hr : Represents X r) : Represents Y r := by
  have hall := RealRaw.allStagesOverlap_of_equiv hX hY h
  intro n
  constructor
  · apply ge_of_tendsto (upper_tendsto hX hr)
    filter_upwards [] with m
    have hh := (RealRaw.compareAt_overlap_iff _ _ m n).1 (hall m n)
    exact_mod_cast hh.2
  · apply le_of_tendsto (lower_tendsto hX hr)
    filter_upwards [] with m
    have hh := (RealRaw.compareAt_overlap_iff _ _ m n).1 (hall m n)
    exact_mod_cast hh.1

lemma equiv_of_represents {X Y : RealRaw} {r : ℝ}
    (hx : Represents X r) (hy : Represents Y r) : X.Equiv Y := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  constructor
  · exact_mod_cast le_trans (hx n).1 (hy n).2
  · exact_mod_cast le_trans (hy n).1 (hx n).2

lemma represents_rat (q : Rat) : Represents (RealRaw.ofRat q) (q : ℝ) :=
  fun _ => ⟨le_rfl,le_rfl⟩

lemma represents_mul {X Y : RealRaw} {x y : ℝ}
    (hX : X.Valid) (hY : Y.Valid) (hx : Represents X x) (hy : Represents Y y) :
    Represents (RealRaw.mul X Y) (x*y) := by
  apply represents_of_tendsto (RealRaw.mul_valid hX hY)
    (fun n => (X.compute n).lo * (Y.compute n).lo)
  · intro n
    exact mul_mem
      ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ hX n⟩
      ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ hY n⟩
  · simpa only [Rat.cast_mul] using (lower_tendsto hX hx).mul (lower_tendsto hY hy)

lemma represents_sub {X Y : RealRaw} {x y : ℝ}
    (hx : Represents X x) (hy : Represents Y y) : Represents (X-Y) (x-y) := by
  intro n
  change (((X.compute n).lo-(Y.compute n).hi : Rat) : ℝ) ≤ x-y ∧
    x-y ≤ (((X.compute n).hi-(Y.compute n).lo : Rat) : ℝ)
  push_cast
  exact ⟨sub_le_sub (hx n).1 (hy n).2,sub_le_sub (hx n).2 (hy n).1⟩

lemma represents_add {X Y : RealRaw} {x y : ℝ}
    (hx : Represents X x) (hy : Represents Y y) : Represents (X+Y) (x+y) := by
  intro n
  change (((X.compute n).lo+(Y.compute n).lo : Rat) : ℝ) ≤ x+y ∧
    x+y ≤ (((X.compute n).hi+(Y.compute n).hi : Rat) : ℝ)
  push_cast
  exact ⟨add_le_add (hx n).1 (hy n).1,add_le_add (hx n).2 (hy n).2⟩

lemma represents_scale (q : Rat) {X : RealRaw} {x : ℝ} (hx : Represents X x) :
    Represents (RealRaw.scaleRat q X) ((q : ℝ)*x) := by
  intro n
  change ((RealRaw.scaleRatCompute q X n).lo : ℝ) ≤ (q : ℝ)*x ∧ (q : ℝ)*x ≤ ((RealRaw.scaleRatCompute q X n).hi : ℝ)
  unfold RealRaw.scaleRatCompute
  dsimp only
  split <;> rename_i hq
  · have h : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    simp only [Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left (hx n).1 h,mul_le_mul_of_nonneg_left (hx n).2 h⟩
  · have h : (q : ℝ) ≤ (0 : ℝ) := by exact_mod_cast (le_of_lt (lt_of_not_ge hq))
    simp only [Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonpos_left (hx n).2 h,mul_le_mul_of_nonpos_left (hx n).1 h⟩

end MathlibComparison
