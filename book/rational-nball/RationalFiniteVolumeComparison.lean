import RationalProductVolume

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

/-- Empty or nonempty point hulls have a finite rational H-presentation with
only genuine cutting hyperplanes in positive dimension. -/
theorem pointHull_nonzero_halfspaces (n : Nat) (hn : 0 < n) (P : Polytope n) :
    ∃ cuts : Finset (Point n × ℚ), (∀ ac ∈ cuts,ac.1 ≠ 0) ∧
      ∀ x, x ∈ body P ↔ ∀ ac ∈ cuts,dot ac.1 x ≤ ac.2 := by
  classical
  by_cases hP : P.Nonempty
  · obtain ⟨cuts,hcuts⟩ := pointHull_halfspaces P
    obtain ⟨p,hp⟩ := hP
    have hpbody : p ∈ body P := subset_convexHull ℚ (P : Set (Point n)) hp
    refine ⟨cuts.filter (fun ac => ac.1 ≠ 0),?_,?_⟩
    · intro ac hac; exact (Finset.mem_filter.mp hac).2
    · intro x
      constructor
      · intro hx ac hac
        exact (hcuts x).mp hx ac (Finset.mem_filter.mp hac).1
      · intro hx
        apply (hcuts x).mpr
        intro ac hac
        by_cases ha : ac.1=0
        · have hc := (hcuts p).mp hpbody ac hac
          simpa [ha,dot] using hc
        · exact hx ac (Finset.mem_filter.mpr ⟨hac,ha⟩)
  · have he : P=∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    let i : Fin n := ⟨0,hn⟩
    have ha : axis i ≠ (0 : Point n) := by
      intro hz; have h := congrFun hz i; simp [axis] at h
    refine ⟨{(axis i,-1),(-axis i,-1)},?_,?_⟩
    · intro ac hac
      simp only [Finset.mem_insert,Finset.mem_singleton] at hac
      rcases hac with rfl | rfl
      · exact ha
      · exact neg_ne_zero.mpr ha
    · intro x
      simp only [body,Finset.coe_empty,convexHull_empty,Set.mem_empty_iff_false,false_iff]
      intro hx
      have h1 := hx (axis i,-1) (by simp)
      have h2 := hx (-axis i,-1) (by simp)
      simp only [dot_axis] at h1
      have hneg : dot (-axis i) x= -x i := by simp [dot,Finset.sum_neg_distrib,axis]
      rw [hneg] at h2
      linarith

/-- A finite binary sign pattern; its type records the number of cuts. -/
def CutPattern : Nat → Type
  | 0 => Unit
  | k+1 => Bool × CutPattern k

instance cutPatternFintype : (k : Nat) → Fintype (CutPattern k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 => @instFintypeProd Bool (CutPattern k) inferInstance (cutPatternFintype k)

def cellPoly {n : Nat} (P : Polytope n) :
    (cuts : List (Point n × ℚ)) → CutPattern cuts.length → Polytope n
  | [],_ => P
  | (a,c)::rest,σ => cellPoly (if σ.1 then clipVertices P a c else clipVertices P (-a) (-c)) rest σ.2

def cellTest {n : Nat} : (cuts : List (Point n × ℚ)) → CutPattern cuts.length → Point n → Prop
  | [],_,_ => True
  | (a,c)::rest,σ,x => (if σ.1 then dot a x ≤ c else c ≤ dot a x) ∧ cellTest rest σ.2 x

theorem mem_body_cellPoly {n : Nat} (P : Polytope n) (cuts : List (Point n × ℚ))
    (σ : CutPattern cuts.length) (x : Point n) :
    x ∈ body (cellPoly P cuts σ) ↔ x ∈ body P ∧ cellTest cuts σ x := by
  induction cuts generalizing P with
  | nil => simp [cellPoly,cellTest]
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    obtain ⟨b,σ⟩ := σ
    cases b <;> simp only [cellPoly,cellTest,Bool.false_eq_true,if_false,if_true,ih,
      body_clip_eq,Set.mem_inter_iff,Set.mem_ofPred_eq]
    · have hneg : dot (-a) x= -dot a x := by simp [dot,Finset.sum_neg_distrib]
      rw [hneg,neg_le_neg_iff]
      tauto
    · tauto

theorem cellPoly_subset {n : Nat} {P Q : Polytope n} (hPQ : body P ⊆ body Q)
    (cuts : List (Point n × ℚ)) (σ : CutPattern cuts.length) :
    body (cellPoly P cuts σ) ⊆ body (cellPoly Q cuts σ) := by
  intro x hx
  rw [mem_body_cellPoly] at hx ⊢
  exact ⟨hPQ hx.1,hx.2⟩

theorem cellPoly_volume_sum {n : Nat} (V : Axioms n) (P : Polytope n)
    (cuts : List (Point n × ℚ)) (hnormal : ∀ ac ∈ cuts,ac.1 ≠ 0) :
    (∑ σ : CutPattern cuts.length,V.volume (cellPoly P cuts σ))=V.volume P := by
  induction cuts generalizing P with
  | nil =>
    change (∑ σ : Unit,V.volume P)=V.volume P
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_unit,nsmul_eq_mul,Nat.cast_one,one_mul]
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    have ha := hnormal (a,c) (List.mem_cons_self ..)
    have hr : ∀ ac ∈ rest, ac.1 ≠ 0 := fun ac hac => hnormal ac (List.mem_cons_of_mem _ hac)
    change (∑ σ : Bool × CutPattern rest.length,
      V.volume (cellPoly (if σ.1 then clipVertices P a c else clipVertices P (-a) (-c)) rest σ.2))=V.volume P
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool,Bool.false_eq_true,if_false,if_true]
    rw [ih _ hr,ih _ hr,← volume_clip_add V P a c ha]

/-- Every cell lies on one of the two closed sides of every listed cut. -/
theorem cellPoly_side {n : Nat} (P : Polytope n) (cuts : List (Point n × ℚ))
    (σ : CutPattern cuts.length) (ac : Point n × ℚ) (hac : ac ∈ cuts) :
    (∀ x ∈ body (cellPoly P cuts σ),dot ac.1 x ≤ ac.2) ∨
      (∀ x ∈ body (cellPoly P cuts σ),ac.2 ≤ dot ac.1 x) := by
  induction cuts generalizing P with
  | nil => simp at hac
  | cons bc rest ih =>
    rcases List.mem_cons.mp hac with rfl | hac
    · obtain ⟨a,c⟩ := ac
      obtain ⟨b,σ⟩ := σ
      cases b with
      | false =>
        right; intro x hx
        have ht := ((mem_body_cellPoly P ((a,c)::rest) (false,σ) x).mp hx).2.1
        exact ht
      | true =>
        left; intro x hx
        have ht := ((mem_body_cellPoly P ((a,c)::rest) (true,σ) x).mp hx).2.1
        exact ht
    · exact ih _ σ.2 hac

noncomputable def vertexAverage {n : Nat} (P : Polytope n) : Point n :=
  (P.card:ℚ)⁻¹ • ∑ p ∈ P,p

theorem vertexAverage_mem {n : Nat} (P : Polytope n) (hP : P.Nonempty) :
    vertexAverage P ∈ body P := by
  have hpos : 0 < ∑ p ∈ P,(1:ℚ) := by
    simpa using (show 0 < (P.card:ℚ) by exact_mod_cast hP.card_pos)
  have hm := P.centerMass_id_mem_convexHull (fun p hp => (by decide : (0:ℚ) ≤ 1)) hpos
  simpa [body,Finset.centerMass,vertexAverage] using hm

theorem dot_vertexAverage {n : Nat} (P : Polytope n) (a : Point n) :
    dot a (vertexAverage P)=(∑ p ∈ P,dot a p)/(P.card:ℚ) := by
  simp only [vertexAverage,dot,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  have he (i : Fin n) : a i*((P.card:ℚ)⁻¹*∑ p ∈ P,p i)=
      (P.card:ℚ)⁻¹*(∑ p ∈ P,a i*p i) := by
    rw [← Finset.mul_sum]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum,Finset.sum_comm,div_eq_mul_inv,mul_comm]

/-- A centroid on a supporting plane forces the whole rational hull onto
that plane; the proof is a finite sum of nonnegative rational terms. -/
theorem vertexAverage_supporting_plane {n : Nat} (P : Polytope n) (hP : P.Nonempty)
    (a : Point n) (c : ℚ) (hside : ∀ x ∈ body P,c ≤ dot a x)
    (haverage : dot a (vertexAverage P) ≤ c) : ∀ x ∈ body P,dot a x=c := by
  have hcard : 0 < (P.card:ℚ) := by exact_mod_cast hP.card_pos
  have hsumle : (∑ p ∈ P,dot a p) ≤ c*(P.card:ℚ) := by
    rw [dot_vertexAverage] at haverage
    exact (div_le_iff₀ hcard).mp haverage
  have hterms : ∀ p ∈ P,0 ≤ dot a p-c := by
    intro p hp
    exact sub_nonneg.mpr (hside p (subset_convexHull ℚ (P : Set (Point n)) hp))
  have hzero : (∑ p ∈ P,(dot a p-c))=0 := by
    have hn := Finset.sum_nonneg hterms
    simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul] at hn ⊢
    nlinarith
  have hv : ∀ p ∈ P,dot a p=c := by
    intro p hp
    have he := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hzero p hp
    linarith
  have hc : Convex ℚ {x : Point n | dot a x=c} := by
    intro x hx y hy r s hr hs hrs
    change dot a (fun i => r*x i+s*y i)=c
    simp only [dot,mul_add,Finset.sum_add_distrib,mul_left_comm,← Finset.mul_sum]
    change r*dot a x+s*dot a y=c
    rw [hx,hy,← add_mul,hrs,one_mul]
  exact convexHull_min (fun p hp => hv p hp) hc

theorem cell_contained_of_average {n : Nat} (C Q : Polytope n) (hC : C.Nonempty)
    (cuts : Finset (Point n × ℚ))
    (hQ : ∀ x,x ∈ body Q ↔ ∀ ac ∈ cuts,dot ac.1 x ≤ ac.2)
    (hside : ∀ ac ∈ cuts,
      (∀ x ∈ body C,dot ac.1 x ≤ ac.2) ∨ (∀ x ∈ body C,ac.2 ≤ dot ac.1 x))
    (haverage : vertexAverage C ∈ body Q) : body C ⊆ body Q := by
  intro x hx
  apply (hQ x).mpr
  intro ac hac
  rcases hside ac hac with hl | hr
  · exact hl x hx
  · have ha := (hQ (vertexAverage C)).mp haverage ac hac
    exact (vertexAverage_supporting_plane C hC ac.1 ac.2 hr ha x hx).le

/-- A common-cut cell is wholly inside a polytope, or its intersection with
that polytope is flat. There is no assumed triangulation or volume inequality. -/
theorem cell_subset_or_flat {n : Nat} (T Q : Polytope n) (hQT : body Q ⊆ body T)
    (allCuts : List (Point n × ℚ)) (σ : CutPattern allCuts.length)
    (cuts : Finset (Point n × ℚ)) (hnormal : ∀ ac ∈ cuts,ac.1 ≠ 0)
    (hQ : ∀ x,x ∈ body Q ↔ ∀ ac ∈ cuts,dot ac.1 x ≤ ac.2)
    (hinclude : ∀ ac ∈ cuts,ac ∈ allCuts)
    (hC : (cellPoly T allCuts σ).Nonempty) :
    body (cellPoly T allCuts σ) ⊆ body Q ∨ Flat (body (cellPoly Q allCuts σ)) := by
  let C := cellPoly T allCuts σ
  have hav := vertexAverage_mem C hC
  by_cases ha : vertexAverage C ∈ body Q
  · exact Or.inl (cell_contained_of_average C Q hC cuts hQ
      (fun ac hac => cellPoly_side T allCuts σ ac (hinclude ac hac)) ha)
  · right
    have hn : ¬ ∀ ac ∈ cuts,dot ac.1 (vertexAverage C) ≤ ac.2 := by
      intro h; exact ha ((hQ _).mpr h)
    obtain ⟨ac,hh⟩ := not_forall.mp hn
    obtain ⟨hac,hle⟩ := Classical.not_imp.mp hh
    have hside := cellPoly_side T allCuts σ ac (hinclude ac hac)
    have hr : ∀ x ∈ body C,ac.2 ≤ dot ac.1 x := by
      rcases hside with hl | hr
      · exact (hle (hl _ hav)).elim
      · exact hr
    refine ⟨ac.1,ac.2,hnormal ac hac,?_⟩
    intro x hx
    have hxT := cellPoly_subset hQT allCuts σ hx
    have hxQ := ((mem_body_cellPoly Q allCuts σ x).mp hx).1
    exact le_antisymm ((hQ x).mp hxQ ac hac) (hr x hxT)

private noncomputable def commonCuts {n : Nat} {ι : Type} [Fintype ι]
    (cuts : ι → Finset (Point n × ℚ)) : List (Point n × ℚ) :=
  Finset.univ.toList.flatMap (fun i => (cuts i).toList)

private theorem commonCuts_mem {n : Nat} {ι : Type} [Fintype ι]
    (cuts : ι → Finset (Point n × ℚ)) (ac : Point n × ℚ) :
    ac ∈ commonCuts cuts ↔ ∃ i,ac ∈ cuts i := by
  classical
  simp [commonCuts,List.mem_flatMap]

/-- A convex polytope covered by a finite family of rational polytopes has
volume at most the sum of their volumes. This follows by actual common cuts. -/
theorem finite_cover_volume_le {n : Nat} (hn : 0 < n) {ι : Type} [Fintype ι]
    (V : Axioms n) (T : Polytope n) (Q : ι → Polytope n)
    (hcover : ∀ x ∈ body T,∃ i,x ∈ body (Q i)) :
    V.volume T ≤ ∑ i,V.volume (Q i) := by
  classical
  choose cuts hnormal hQ using fun i => pointHull_nonzero_halfspaces n hn (Q i)
  let allCuts := commonCuts cuts
  have hall : ∀ ac ∈ allCuts,ac.1 ≠ 0 := by
    intro ac hac
    obtain ⟨i,hi⟩ := (commonCuts_mem cuts ac).mp hac
    exact hnormal i ac hi
  have hcell : ∀ σ : CutPattern allCuts.length,
      V.volume (cellPoly T allCuts σ) ≤ ∑ i,V.volume (cellPoly (Q i) allCuts σ) := by
    intro σ
    let C := cellPoly T allCuts σ
    by_cases hC : C.Nonempty
    · have hm := vertexAverage_mem C hC
      have ht := ((mem_body_cellPoly T allCuts σ _).mp hm).1
      obtain ⟨i,hi⟩ := hcover _ ht
      have hcontain := cell_contained_of_average C (Q i) hC (cuts i) (hQ i)
        (fun ac hac => cellPoly_side T allCuts σ ac
          ((commonCuts_mem cuts ac).mpr ⟨i,hac⟩)) hi
      have hsub : body C ⊆ body (cellPoly (Q i) allCuts σ) := by
        intro x hx
        rw [mem_body_cellPoly]
        exact ⟨hcontain hx,((mem_body_cellPoly T allCuts σ x).mp hx).2⟩
      exact le_trans (volume_mono V _ _ hsub)
        (Finset.single_le_sum (fun j _ => volume_nonneg V _) (Finset.mem_univ i))
    · have he : C=∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      have hz : V.volume C=0 := volume_empty_body V _ (by simp [he,body])
      rw [hz]
      exact Finset.sum_nonneg (fun i _ => volume_nonneg V _)
  calc
    V.volume T = ∑ σ : CutPattern allCuts.length,V.volume (cellPoly T allCuts σ) :=
      (cellPoly_volume_sum V T allCuts hall).symm
    _ ≤ ∑ σ : CutPattern allCuts.length,∑ i,V.volume (cellPoly (Q i) allCuts σ) :=
      Finset.sum_le_sum (fun σ _ => hcell σ)
    _ = ∑ i,∑ σ : CutPattern allCuts.length,V.volume (cellPoly (Q i) allCuts σ) := Finset.sum_comm
    _ = ∑ i,V.volume (Q i) := Finset.sum_congr rfl (fun i _ => cellPoly_volume_sum V _ allCuts hall)

/-- A finite family with flat overlaps contained in a convex polytope has
sum of volumes at most that polytope's volume, proved by common rational cuts. -/
theorem finite_disjoint_volume_le {n : Nat} (hn : 0 < n) {ι : Type} [Fintype ι]
    (V : Axioms n) (T : Polytope n) (Q : ι → Polytope n)
    (hcontain : ∀ i,body (Q i) ⊆ body T)
    (hflat : ∀ i j,i ≠ j → Flat (body (Q i) ∩ body (Q j))) :
    (∑ i,V.volume (Q i)) ≤ V.volume T := by
  classical
  choose cuts hnormal hQ using fun i => pointHull_nonzero_halfspaces n hn (Q i)
  let allCuts := commonCuts cuts
  have hall : ∀ ac ∈ allCuts,ac.1 ≠ 0 := by
    intro ac hac
    obtain ⟨i,hi⟩ := (commonCuts_mem cuts ac).mp hac
    exact hnormal i ac hi
  have hcell : ∀ σ : CutPattern allCuts.length,
      (∑ i,V.volume (cellPoly (Q i) allCuts σ)) ≤ V.volume (cellPoly T allCuts σ) := by
    intro σ
    by_cases hz : ∀ i,V.volume (cellPoly (Q i) allCuts σ)=0
    · simp only [hz,Finset.sum_const_zero]
      exact volume_nonneg V _
    · obtain ⟨i,hi⟩ := not_forall.mp hz
      have hC : (cellPoly T allCuts σ).Nonempty := by
        by_contra he
        have he0 : cellPoly T allCuts σ=∅ := Finset.not_nonempty_iff_eq_empty.mp he
        have hem : body (cellPoly (Q i) allCuts σ)=∅ := by
          ext x
          constructor
          · intro hx
            have ht := cellPoly_subset (hcontain i) allCuts σ hx
            simpa [he0,body] using ht
          · intro hx; exact False.elim hx
        exact hi (volume_empty_body V _ hem)
      have hsub : body (cellPoly T allCuts σ) ⊆ body (Q i) := by
        rcases cell_subset_or_flat T (Q i) (hcontain i) allCuts σ (cuts i) (hnormal i) (hQ i)
          (fun ac hac => (commonCuts_mem cuts ac).mpr ⟨i,hac⟩) hC with hs | hf
        · exact hs
        · exact (hi (volume_flat n V _ hf)).elim
      have hother : ∀ j,j ≠ i → V.volume (cellPoly (Q j) allCuts σ)=0 := by
        intro j hji
        obtain ⟨a,c,ha,hac⟩ := hflat j i hji
        apply volume_flat
        refine ⟨a,c,ha,?_⟩
        intro x hx
        exact hac x ⟨((mem_body_cellPoly _ _ _ _).mp hx).1,
          hsub (cellPoly_subset (hcontain j) allCuts σ hx)⟩
      rw [Finset.sum_eq_single i]
      · exact volume_mono V _ _ (cellPoly_subset (hcontain i) allCuts σ)
      · intro j hj hji; exact hother j hji
      · simp
  calc
    (∑ i,V.volume (Q i)) = ∑ i,∑ σ : CutPattern allCuts.length,V.volume (cellPoly (Q i) allCuts σ) :=
      Finset.sum_congr rfl (fun i _ => (cellPoly_volume_sum V _ allCuts hall).symm)
    _ = ∑ σ : CutPattern allCuts.length,∑ i,V.volume (cellPoly (Q i) allCuts σ) := Finset.sum_comm
    _ ≤ ∑ σ : CutPattern allCuts.length,V.volume (cellPoly T allCuts σ) :=
      Finset.sum_le_sum (fun σ _ => hcell σ)
    _ = V.volume T := cellPoly_volume_sum V T allCuts hall

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.pointHull_nonzero_halfspaces
#print axioms ComputableAnalysis.RationalPolytopeVolume.mem_body_cellPoly
#print axioms ComputableAnalysis.RationalPolytopeVolume.cellPoly_subset
#print axioms ComputableAnalysis.RationalPolytopeVolume.cellPoly_volume_sum
#print axioms ComputableAnalysis.RationalPolytopeVolume.cellPoly_side
#print axioms ComputableAnalysis.RationalPolytopeVolume.vertexAverage_mem
#print axioms ComputableAnalysis.RationalPolytopeVolume.dot_vertexAverage
#print axioms ComputableAnalysis.RationalPolytopeVolume.vertexAverage_supporting_plane
#print axioms ComputableAnalysis.RationalPolytopeVolume.cell_contained_of_average
#print axioms ComputableAnalysis.RationalPolytopeVolume.cell_subset_or_flat
#print axioms ComputableAnalysis.RationalPolytopeVolume.finite_cover_volume_le
#print axioms ComputableAnalysis.RationalPolytopeVolume.finite_disjoint_volume_le

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.pointHull_nonzero_halfspaces,
    `ComputableAnalysis.RationalPolytopeVolume.mem_body_cellPoly,
    `ComputableAnalysis.RationalPolytopeVolume.cellPoly_subset,
    `ComputableAnalysis.RationalPolytopeVolume.cellPoly_volume_sum,
    `ComputableAnalysis.RationalPolytopeVolume.cellPoly_side,
    `ComputableAnalysis.RationalPolytopeVolume.vertexAverage_mem,
    `ComputableAnalysis.RationalPolytopeVolume.dot_vertexAverage,
    `ComputableAnalysis.RationalPolytopeVolume.vertexAverage_supporting_plane,
    `ComputableAnalysis.RationalPolytopeVolume.cell_contained_of_average,
    `ComputableAnalysis.RationalPolytopeVolume.cell_subset_or_flat,
    `ComputableAnalysis.RationalPolytopeVolume.finite_cover_volume_le,
    `ComputableAnalysis.RationalPolytopeVolume.finite_disjoint_volume_le]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
