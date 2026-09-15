import MathlibComparison.IntervalModel

/-!
# A one-way interpretation of the independent foundation in Mathlib

Completeness is used here, in the comparison package only. This does not
supply a numerical evaluator for an arbitrary Mathlib real. Native raw
computations and their validity proofs are unchanged.
-/
namespace MathlibComparison
open ComputableAnalysis Filter Topology

/-- Noncomputable semantic value of a valid rational-interval computation.
The validity proof ensures this supremum has the intended meaning. -/
noncomputable def denote (X : RealRaw) (_hX : X.Valid) : ℝ :=
  sSup (Set.range (fun n => ((X.compute n).lo : ℝ)))

lemma denote_represents (X : RealRaw) (hX : X.Valid) : Represents X (denote X hX) := by
  let lows : Set ℝ := Set.range (fun n => ((X.compute n).lo : ℝ))
  have hne : lows.Nonempty := ⟨_, ⟨0,rfl⟩⟩
  have hub (n : Nat) : ∀ z ∈ lows, z ≤ ((X.compute n).hi : ℝ) := by
    intro z hz
    obtain ⟨m,rfl⟩ := hz
    dsimp only
    exact_mod_cast (RealRaw.le_refl X hX m n)
  have hb : BddAbove lows := ⟨((X.compute 0).hi : ℝ),hub 0⟩
  intro n
  exact ⟨le_csSup hb ⟨n,rfl⟩,csSup_le hne (hub n)⟩

lemma represents_unique {X : RealRaw} (hX : X.Valid) {r s : ℝ}
    (hr : Represents X r) (hs : Represents X s) : r = s :=
  tendsto_nhds_unique (lower_tendsto hX hr) (lower_tendsto hX hs)

/-- Every valid native computation has exactly one Mathlib interpretation. -/
theorem existsUnique_represents (X : RealRaw) (hX : X.Valid) :
    ∃! r : ℝ, Represents X r :=
  ⟨denote X hX,denote_represents X hX,fun _ hr =>
    represents_unique hX hr (denote_represents X hX)⟩

lemma denote_eq_of_represents {X : RealRaw} (hX : X.Valid) {r : ℝ}
    (hr : Represents X r) : denote X hX = r :=
  represents_unique hX (denote_represents X hX) hr

/-- Native equivalence is exactly equality of interpretations, on valid raws. -/
theorem equiv_iff_denote_eq {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid) :
    X.Equiv Y ↔ denote X hX = denote Y hY := by
  constructor
  · intro h
    exact represents_unique hY
      (represents_of_equiv hX hY h (denote_represents X hX)) (denote_represents Y hY)
  · intro h
    apply equiv_of_represents (denote_represents X hX)
    rw [h]
    exact denote_represents Y hY

/-- Native order is also preserved and reflected by the interpretation. -/
theorem le_iff_denote_le {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid) :
    X.Le Y ↔ denote X hX ≤ denote Y hY := by
  constructor
  · intro h
    have hb (n : Nat) : ((X.compute n).lo : ℝ) ≤ denote Y hY := by
      apply ge_of_tendsto (upper_tendsto hY (denote_represents Y hY))
      exact Eventually.of_forall (fun m => by exact_mod_cast h n m)
    apply le_of_tendsto (lower_tendsto hX (denote_represents X hX))
    exact Eventually.of_forall hb
  · intro h n m
    have hx := (denote_represents X hX n).1
    have hy := (denote_represents Y hY m).2
    exact_mod_cast le_trans hx (le_trans h hy)

lemma denote_rat (q : Rat) :
    denote (RealRaw.ofRat q) (RealRaw.ofRat_valid q) = (q : ℝ) :=
  denote_eq_of_represents _ (represents_rat q)

lemma denote_add {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid) :
    denote (X+Y) (RealRaw.add_valid hX hY) = denote X hX + denote Y hY :=
  denote_eq_of_represents _ (represents_add (denote_represents X hX) (denote_represents Y hY))

lemma denote_sub {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid) :
    denote (X-Y) (RealRaw.sub_valid hX hY) = denote X hX - denote Y hY :=
  denote_eq_of_represents _ (represents_sub (denote_represents X hX) (denote_represents Y hY))

lemma denote_mul {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid) :
    denote (RealRaw.mul X Y) (RealRaw.mul_valid hX hY) = denote X hX * denote Y hY :=
  denote_eq_of_represents _ (represents_mul hX hY (denote_represents X hX) (denote_represents Y hY))

lemma denote_scale (q : Rat) {X : RealRaw} (hX : X.Valid) :
    denote (RealRaw.scaleRat q X) (RealRaw.scaleRat_valid hX) = (q : ℝ)*denote X hX :=
  denote_eq_of_represents _ (represents_scale q (denote_represents X hX))

end MathlibComparison
