import ComputableAnalysis.Calculus

/-!
# Fixed-schedule FTC closure with two independent precisions

A mesh index and an evaluation stage are different parameters. At stage `n`
we intersect the enclosures from meshes `0,...,n`, each evaluated at stage
`n`. This retains each fixed mesh while its finitely many samples converge.
It does not require a uniform modulus for a changing collection of samples.

The endpoint computation occurs only in the proof. The executable integral
reads only finite sums and their rational discretization-error bounds.
-/

namespace ComputableAnalysis
namespace Integral.Dovetail

/-- Finite intersection over mesh indices, at a fixed evaluation stage. -/
def intersectMeshes (C : Nat -> Nat -> QInterval) (q : Nat) : Nat -> QInterval
  | 0 => C 0 q
  | k+1 => QInterval.intersection (intersectMeshes C q k) (C (k+1) q)

private theorem contains_trans {I J K : QInterval}
    (hIJ : I.ContainsInterval J) (hJK : J.ContainsInterval K) :
    I.ContainsInterval K :=
  ⟨Rat.le_trans hIJ.1 hJK.1, Rat.le_trans hJK.2 hIJ.2⟩

theorem intersectMeshes_contains {C : Nat -> Nat -> QInterval}
    (q : Nat) {k n : Nat} (hkn : k <= n) :
    (C k q).ContainsInterval (intersectMeshes C q n) := by
  induction n with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      exact ⟨Rat.le_refl, Rat.le_refl⟩
  | succ n ih =>
      by_cases hk : k = n+1
      · subst k
        exact QInterval.intersection_contained_right _ _
      · exact contains_trans (ih (by omega))
          (QInterval.intersection_contained_left _ _)

private theorem intersectMeshes_contains_of_each
    {C : Nat -> Nat -> QInterval} {q n : Nat} {J : QInterval}
    (h : ∀ k, k <= n -> (C k q).ContainsInterval J) :
    (intersectMeshes C q n).ContainsInterval J := by
  induction n with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ n ih =>
      exact QInterval.intersection_contains
        (ih (fun k hk => h k (by omega))) (h (n+1) (Nat.le_refl _))

/-- Overlap with every stage of one shrinking anchor forces an interval to
be ordered. Merely overlapping one coarse anchor box would not suffice. -/
theorem ordered_of_all_anchor_overlaps {I : QInterval} {A : RealRaw}
    (hA : A.Valid) (h : ∀ t, I.Overlaps (A.compute t)) : I.lo <= I.hi := by
  by_cases hgood : I.lo <= I.hi
  · exact hgood
  · apply False.elim
    have hgap : 0 < (I.lo-I.hi)/2 := by
      rw [Rat.div_def]
      exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 (by decide))
    obtain ⟨N, hN⟩ := hA.2.2 ⟨(I.lo-I.hi)/2, hgap⟩
    have hw := hN N (Nat.le_refl N)
    have ho := h N
    unfold QInterval.Overlaps QInterval.width at *
    simp only [Rat.div_def] at hw
    grind

private theorem intersectMeshes_overlap {C : Nat -> Nat -> QInterval}
    {A : RealRaw} (h : ∀ k q t, (C k q).Overlaps (A.compute t))
    (q n t : Nat) : (intersectMeshes C q n).Overlaps (A.compute t) := by
  induction n with
  | zero => exact h 0 q t
  | succ n ih =>
      have hn := h (n+1) q t
      change max (intersectMeshes C q n).lo (C (n+1) q).lo <=
          (A.compute t).hi ∧
        (A.compute t).lo <= min (intersectMeshes C q n).hi (C (n+1) q).hi
      unfold QInterval.Overlaps at ih hn
      constructor <;> grind

/-- No stopping test and no access to the primitive are hidden here. -/
def raw (R : Nat -> RealRaw) (radius : Nat -> Rat) : RealRaw where
  compute := fun n => intersectMeshes
    (fun k q => QInterval.expand ((R k).compute q) (radius k)) n n

theorem raw_contains_mesh (R : Nat -> RealRaw) (radius : Nat -> Rat)
    (n k : Nat) (hk : k <= n) :
    (QInterval.expand ((R k).compute n) (radius k)).ContainsInterval
      ((raw R radius).compute n) := intersectMeshes_contains n hk

/-- Fixed-mesh validity and an explicit shrinking discretization error close
an FTC proof even when the integrand has only pointwise evaluation rates. -/
theorem raw_valid {R : Nat -> RealRaw} {radius : Nat -> Rat} {A : RealRaw}
    (hR : ∀ k, (R k).Valid) (hA : A.Valid)
    (hr : ShrinksToZero radius)
    (hover : ∀ k q t,
      (QInterval.expand ((R k).compute q) (radius k)).Overlaps (A.compute t)) :
    (raw R radius).Valid := by
  have hall (n t : Nat) : ((raw R radius).compute n).Overlaps (A.compute t) :=
    intersectMeshes_overlap hover n n t
  have hord (n : Nat) : ((raw R radius).compute n).lo <=
      ((raw R radius).compute n).hi := ordered_of_all_anchor_overlaps hA (hall n)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 <= ((raw R radius).compute n).hi - ((raw R radius).compute n).lo
    have ho := hord n
    grind
  · intro n m hnm
    have hn : ((raw R radius).compute n).ContainsInterval
        ((raw R radius).compute m) := by
      apply intersectMeshes_contains_of_each
      intro k hk
      have hc := raw_contains_mesh R radius m k (by omega)
      have hnest := (hR k).2.1 n m hnm
      apply contains_trans (J := QInterval.expand ((R k).compute m) (radius k))
      · unfold QInterval.expand QInterval.ContainsInterval
        constructor <;> grind
      · exact hc
    exact ⟨hn.1, hord m, hn.2⟩
  · intro eps
    let half : QPos := ⟨eps.val/2, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
    let quarter : QPos := ⟨eps.val/4, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
    obtain ⟨K, hK⟩ := hr quarter
    obtain ⟨N, hN⟩ := (hR K).2.2 half
    refine ⟨max K N, ?_⟩
    intro n hn
    have hc := QInterval.width_le_of_contains
      (raw_contains_mesh R radius n K (by omega))
    rw [QInterval.expand_width] at hc
    have hw := hN n (by omega)
    have he := hK K (Nat.le_refl K)
    dsimp [half, quarter] at hw he
    simp only [Rat.div_def] at hw he
    grind

theorem raw_equiv_endpoint {R : Nat -> RealRaw} {radius : Nat -> Rat} {A : RealRaw}
    (hover : ∀ k q t,
      (QInterval.expand ((R k).compute q) (radius k)).Overlaps (A.compute t)) :
    (raw R radius).Equiv A := by
  intro n
  exact (RealRaw.compareAt_overlap_iff _ _ n n).2
    (intersectMeshes_overlap hover n n n)

/-- The same literal finite-sum program in the domain-aware integral API. -/
def constructionFor (F : FunctionOnInterval)
    (R : Nat -> RealRaw) (radius : Nat -> Rat) (A : RealRaw)
    (hR : ∀ k, (R k).Valid) (hA : A.Valid)
    (hr : ShrinksToZero radius)
    (hover : ∀ k q t,
      (QInterval.expand ((R k).compute q) (radius k)).Overlaps (A.compute t)) :
    Integral.ConstructionFor F where
  compute := (raw R radius).compute
  certificate := raw_valid hR hA hr hover

/-- Intersect finitely many mesh enclosures at the current evaluation stage.
Unlike `raw`, each fixed mesh may have a nonzero limiting width. -/
def ofBoxes (C : Nat -> Nat -> QInterval) : RealRaw where
  compute := fun n => intersectMeshes C n n

private theorem intersect_lo_le {C : Nat -> Nat -> QInterval} (q n : Nat) (r : Rat)
    (h : ∀ k, k <= n -> (C k q).lo <= r) :
    (intersectMeshes C q n).lo <= r := by
  induction n with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ n ih =>
      have hprev := ih (fun k hk => h k (by omega))
      have hlast := h (n+1) (Nat.le_refl _)
      change max (intersectMeshes C q n).lo (C (n+1) q).lo <= r
      grind

private theorem le_intersect_hi {C : Nat -> Nat -> QInterval} (q n : Nat) (r : Rat)
    (h : ∀ k, k <= n -> r <= (C k q).hi) :
    r <= (intersectMeshes C q n).hi := by
  induction n with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ n ih =>
      have hprev := ih (fun k hk => h k (by omega))
      have hlast := h (n+1) (Nat.le_refl _)
      change r <= min (intersectMeshes C q n).hi (C (n+1) q).hi
      grind

/-- Compatibility, refinement, and a fixed-mesh width criterion suffice.
In particular a convexity proof can supply compatibility without assuming
that a derivative value already exists. -/
theorem ofBoxes_valid {C : Nat -> Nat -> QInterval}
    (compatible : ∀ k l q t, (C k q).lo <= (C l t).hi)
    (nested : ∀ k q t, q <= t -> (C k q).ContainsInterval (C k t))
    (small : ∀ eps : QPos, ∃ k N, ∀ n, N <= n -> (C k n).width <= eps.val) :
    (ofBoxes C).Valid := by
  have ordered (n : Nat) : ((ofBoxes C).compute n).lo <= ((ofBoxes C).compute n).hi := by
    apply le_intersect_hi n n
    intro l _hl
    apply intersect_lo_le n n
    intro k _hk
    exact compatible k l n n
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have ho := ordered n
    change 0 <= ((ofBoxes C).compute n).hi-((ofBoxes C).compute n).lo
    grind
  · intro n m hnm
    have hh : ((ofBoxes C).compute n).ContainsInterval ((ofBoxes C).compute m) := by
      apply intersectMeshes_contains_of_each
      intro k hk
      exact contains_trans (nested k n m hnm) (intersectMeshes_contains m (by omega : k <= m))
    exact ⟨hh.1, ordered m, hh.2⟩
  · intro eps
    obtain ⟨k, N, hN⟩ := small eps
    refine ⟨max k N, ?_⟩
    intro n hn
    exact Rat.le_trans (QInterval.width_le_of_contains (intersectMeshes_contains n (by omega : k <= n)))
      (hN n (by omega))

theorem ofBoxes_equiv {C : Nat -> Nat -> QInterval} {A : RealRaw}
    (h : ∀ k q t, (C k q).Overlaps (A.compute t)) :
    (ofBoxes C).Equiv A := by
  intro n
  exact (RealRaw.compareAt_overlap_iff _ _ n n).2 (intersectMeshes_overlap h n n n)

end Integral.Dovetail
end ComputableAnalysis
