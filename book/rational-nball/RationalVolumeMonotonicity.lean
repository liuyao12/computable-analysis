import RationalSimplexEdgeCuts
import RationalHalfspaceElimination
import RationalOrthantBodies

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

/-- Exact membership after a finite sequence of halfspace cuts. -/
theorem mem_body_retained {n : Nat} (P : Polytope n)
    (cuts : List (Point n × ℚ)) (x : Point n) :
    x ∈ body (retainedAfterCuts P cuts) ↔
    x ∈ body P ∧ ∀ ac ∈ cuts,dot ac.1 x ≤ ac.2 := by
  induction cuts generalizing P with
  | nil => simp [retainedAfterCuts]
  | cons ac rest ih =>
    rw [retainedAfterCuts,ih,body_clip_eq]
    simp [and_assoc,and_left_comm]

/-- Finite cut positivity entails finite cut monotonicity; this is applied
below with positivity derived from explicit simplex dissections. -/
theorem volume_retained_le_of_cut_nonneg {n : Nat} (V : Axioms n)
    (P : Polytope n)
    (hpos : ∀ cuts : List (Point n × ℚ),0 ≤ V.volume (retainedAfterCuts P cuts))
    (cuts : List (Point n × ℚ)) :
    V.volume (retainedAfterCuts P cuts) ≤ V.volume P := by
  induction cuts generalizing P with
  | nil => exact le_rfl
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    have hclip : V.volume (clipVertices P a c) ≤ V.volume P := by
      by_cases ha : a=0
      · by_cases hc : 0 ≤ c
        · have he : body (clipVertices P a c)=body P := by
            rw [body_clip_eq]; simp [ha,dot,hc]
          rw [V.extensional _ _ he]
        · have he : body (clipVertices P a c)=∅ := by
            rw [body_clip_eq]; simp [ha,dot,hc]
          rw [volume_empty_body V _ he]
          exact hpos []
      · have hh := volume_clip_add V P a c ha
        have hn := hpos [(-a,-c)]
        change 0 ≤ V.volume (clipVertices P (-a) (-c)) at hn
        linarith
    have hn : ∀ cs : List (Point n × ℚ),
        0 ≤ V.volume (retainedAfterCuts (clipVertices P a c) cs) :=
      fun cs => hpos ((a,c)::cs)
    exact (ih _ hn).trans hclip

theorem mem_body_affineCube (n : Nat) (b : Point n) (r : ℚ)
    (hr : 0 < r) (x : Point n) :
    x ∈ body (affineCube n b r) ↔ ∀ i,b i ≤ x i ∧ x i ≤ b i+r := by
  rw [affineCube,body_translated,body_transformed]
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩ i
    have hi := (mem_body_cube n 1 (by norm_num) z).mp hz i
    simp only [Pi.add_apply,Matrix.mulVec_diagonal]
    constructor <;> nlinarith
  · intro hx
    let z : Point n := fun i => (x i-b i)/r
    have hz : z ∈ body (cube n 1) := by
      apply (mem_body_cube n 1 (by norm_num) z).mpr
      intro i
      constructor
      · exact div_nonneg (sub_nonneg.mpr (hx i).1) hr.le
      · apply (div_le_one hr).mpr
        linarith [(hx i).2]
    refine ⟨_,⟨z,hz,rfl⟩,?_⟩
    ext i
    simp only [Pi.add_apply,Matrix.mulVec_diagonal,z]
    field_simp
    ring

/-- A finite rational hull fits inside an explicitly bounded rational cube. -/
theorem pointHull_bounded_cube {n : Nat} (P : Polytope n) :
    ∃ b : Point n,∃ r : ℚ,0 < r ∧ body P ⊆ body (affineCube n b r) := by
  classical
  let B : ℚ := (∑ p ∈ P,∑ i,|p i|)+1
  have hB : 0 < B := by
    have hh : 0 ≤ (∑ p ∈ P,∑ i,|p i|) :=
      Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
    dsimp [B]; linarith
  refine ⟨fun _ => -B,2*B,by linarith,?_⟩
  apply convexHull_min _ (convex_convexHull ℚ _)
  intro p hp
  apply (mem_body_affineCube n _ _ (by linarith) p).mpr
  intro i
  have h1 : |p i| ≤ ∑ j,|p j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (p j)) (Finset.mem_univ i)
  have h2 : (∑ j,|p j|) ≤ ∑ q ∈ P,∑ j,|q j| :=
    Finset.single_le_sum (fun q _ => Finset.sum_nonneg (fun j _ => abs_nonneg (q j))) hp
  have hh : |p i| ≤ B := by dsimp [B]; linarith
  obtain ⟨hlo,hhi⟩ := abs_le.mp hh
  constructor <;> linarith

/-- Containment of arbitrary rational convex polytopes implies volume
monotonicity. Both hulls are represented by finite rational cuts of one
bounding cube; the proof uses only constructed dissections and the derived
simplex formula, with no monotonicity or positivity axiom. -/
theorem volume_mono {n : Nat} (V : Axioms n) (P Q : Polytope n)
    (hPQ : body P ⊆ body Q) : V.volume P ≤ V.volume Q := by
  classical
  obtain ⟨b,r,hr,hQ⟩ := pointHull_bounded_cube Q
  let C := affineCube n b r
  obtain ⟨pCuts,hp⟩ := pointHull_halfspaces P
  obtain ⟨qCuts,hq⟩ := pointHull_halfspaces Q
  let ps := pCuts.toList
  let qs := qCuts.toList
  have heQ : body (retainedAfterCuts C qs)=body Q := by
    ext x
    rw [mem_body_retained]
    simp only [qs,Finset.mem_toList]
    constructor
    · rintro ⟨_,hx⟩; exact (hq x).mpr hx
    · intro hx; exact ⟨hQ hx,(hq x).mp hx⟩
  have heP : body (retainedAfterCuts (retainedAfterCuts C qs) ps)=body P := by
    ext x
    rw [mem_body_retained,heQ]
    simp only [ps,Finset.mem_toList]
    constructor
    · rintro ⟨_,hx⟩; exact (hp x).mpr hx
    · intro hx; exact ⟨hPQ hx,(hp x).mp hx⟩
  have hnon : ∀ cs : List (Point n × ℚ),
      0 ≤ V.volume (retainedAfterCuts (retainedAfterCuts C qs) cs) := by
    intro cs
    have append_eq : ∀ (P : Polytope n) (as bs : List (Point n × ℚ)),
        retainedAfterCuts P (as++bs)=retainedAfterCuts (retainedAfterCuts P as) bs := by
      intro P as bs
      induction as generalizing P with
      | nil => rfl
      | cons ac rest ih => exact ih _
    rw [← append_eq]
    exact retained_affineCube_volume_nonneg n V b r hr (qs++cs)
  have hh := volume_retained_le_of_cut_nonneg V (retainedAfterCuts C qs) hnon ps
  rw [V.extensional _ _ heP,V.extensional _ _ heQ] at hh
  exact hh

/-- Nonnegativity of every rational convex polytope is now a theorem. -/
theorem volume_nonneg {n : Nat} (V : Axioms n) (P : Polytope n) : 0 ≤ V.volume P := by
  have he : body (∅ : Polytope n)=∅ := by simp [body]
  have hh := volume_mono V (∅ : Polytope n) P (by rw [he]; exact Set.empty_subset _)
  rw [volume_empty_body V _ he] at hh
  exact hh


/-- Checking every generating point against every defining halfspace is
sufficient for the volume inequality. All checks are rational and finite. -/
theorem volume_mono_of_vertex_halfspace_checks {n : Nat} (V : Axioms n)
    (P Q : Polytope n) (cuts : Finset (Point n × ℚ))
    (hQ : ∀ x : Point n,x ∈ body Q ↔ ∀ ac ∈ cuts,dot ac.1 x ≤ ac.2)
    (hchecks : ∀ p ∈ P,∀ ac ∈ cuts,dot ac.1 p ≤ ac.2) :
    V.volume P ≤ V.volume Q := by
  apply volume_mono V P Q
  apply convexHull_min _ (convex_convexHull ℚ _)
  intro p hp
  exact (hQ p).mpr (hchecks p hp)

/-- Every actual rational cut weakly decreases volume. -/
theorem volume_clip_le {n : Nat} (V : Axioms n) (P : Polytope n)
    (a : Point n) (c : ℚ) : V.volume (clipVertices P a c) ≤ V.volume P :=
  volume_mono V _ _ (fun _x hx => (body_clip_subset P a c hx).1)

/-- Removed cap positivity follows from the simplex formula and cuts. -/
theorem volume_cap_nonneg {n : Nat} (V : Axioms n) (P : Polytope n)
    (a : Point n) (c : ℚ) : 0 ≤ V.volume (clipVertices P (-a) (-c)) :=
  volume_nonneg V _

noncomputable def orthantInnerPoly {n : Nat} (samples : Finset (Point n)) : Polytope n :=
  insert 0 samples

noncomputable def orthantOuterPoly {n : Nat} (samples : Finset (Point n)) : Polytope n :=
  retainedAfterCuts (cube n 1) (samples.toList.map (fun a => (a,1)))

theorem body_orthantInnerPoly {n : Nat} (samples : Finset (Point n)) :
    body (orthantInnerPoly samples)=RationalOrthantBodies.inner samples := by
  classical
  simp [body,orthantInnerPoly,RationalOrthantBodies.inner]

/-- Axis tangents are retained. The literal clipped cube agrees with the
coordinate-halfspace and tangent presentation of the outer polytope. -/
theorem body_orthantOuterPoly {n : Nat} (samples : Finset (Point n))
    (haxes : ∀ i,axis i ∈ samples) :
    body (orthantOuterPoly samples)=RationalOrthantBodies.outer samples := by
  classical
  ext x
  rw [orthantOuterPoly,mem_body_retained,mem_body_cube n 1 (by norm_num)]
  simp only [List.forall_mem_map,Finset.mem_toList]
  constructor
  · rintro ⟨hx,ht⟩
    exact ⟨fun i => (hx i).1,ht⟩
  · intro hx
    exact ⟨RationalOrthantBodies.outer_axis_bound samples haxes x hx,hx.2⟩

/-- The actual inscribed hull and clipped circumscribed polytope have
ordered volumes, in every dimension, with axes included among the samples. -/
theorem orthant_inner_volume_le_outer {n : Nat} (V : Axioms n)
    (samples : Finset (Point n)) (haxes : ∀ i,axis i ∈ samples)
    (hunit : ∀ p ∈ samples,normSq p=1)
    (hpositive : ∀ p ∈ samples,∀ i,0 ≤ p i) :
    V.volume (orthantInnerPoly samples) ≤ V.volume (orthantOuterPoly samples) := by
  apply volume_mono
  rw [body_orthantInnerPoly,body_orthantOuterPoly samples haxes]
  exact (RationalOrthantBodies.inner_subset_ball samples hunit hpositive).trans
    (RationalOrthantBodies.ball_subset_outer samples hunit)

/-- Incremental insertion makes the actual inner volume increase. -/
theorem orthant_inner_volume_refines {n : Nat} (V : Axioms n)
    {S T : Finset (Point n)} (hST : S ⊆ T) :
    V.volume (orthantInnerPoly S) ≤ V.volume (orthantInnerPoly T) := by
  apply volume_mono
  rw [body_orthantInnerPoly,body_orthantInnerPoly]
  exact RationalOrthantBodies.inner_refines hST

/-- Incremental tangent insertion makes the actual outer volume decrease. -/
theorem orthant_outer_volume_refines {n : Nat} (V : Axioms n)
    {S T : Finset (Point n)} (hST : S ⊆ T) (haxes : ∀ i,axis i ∈ S) :
    V.volume (orthantOuterPoly T) ≤ V.volume (orthantOuterPoly S) := by
  apply volume_mono
  rw [body_orthantOuterPoly T (fun i => hST (haxes i)),body_orthantOuterPoly S haxes]
  exact RationalOrthantBodies.outer_refines hST

/-- An inner stage can be compared to any outer stage, without requiring
that their sampling sets agree or that one includes the other. -/
theorem orthant_cross_volume_le {n : Nat} (V : Axioms n)
    (S T : Finset (Point n)) (haxes : ∀ i,axis i ∈ T)
    (hSunit : ∀ p ∈ S,normSq p=1)
    (hSpositive : ∀ p ∈ S,∀ i,0 ≤ p i)
    (hTunit : ∀ p ∈ T,normSq p=1) :
    V.volume (orthantInnerPoly S) ≤ V.volume (orthantOuterPoly T) := by
  apply volume_mono
  rw [body_orthantInnerPoly,body_orthantOuterPoly T haxes]
  exact (RationalOrthantBodies.inner_subset_ball S hSunit hSpositive).trans
    (RationalOrthantBodies.ball_subset_outer T hTunit)

/-- The actual finite stage bounds are nested and lie in the unit interval.
Convergence of their width remains a separate geometric obligation. -/
theorem orthant_bracket_refinement {n : Nat} (V : Axioms n)
    (S T : Finset (Point n)) (hST : S ⊆ T) (haxes : ∀ i,axis i ∈ S)
    (hunit : ∀ p ∈ T,normSq p=1)
    (hpositive : ∀ p ∈ T,∀ i,0 ≤ p i) :
    0 ≤ V.volume (orthantInnerPoly S) ∧
    V.volume (orthantInnerPoly S) ≤ V.volume (orthantInnerPoly T) ∧
    V.volume (orthantInnerPoly T) ≤ V.volume (orthantOuterPoly T) ∧
    V.volume (orthantOuterPoly T) ≤ V.volume (orthantOuterPoly S) ∧
    V.volume (orthantOuterPoly S) ≤ 1 := by
  refine ⟨volume_nonneg V _,orthant_inner_volume_refines V hST,
    orthant_inner_volume_le_outer V T (fun i => hST (haxes i)) hunit hpositive,
    orthant_outer_volume_refines V hST haxes,?_⟩
  have hh := volume_mono V (orthantOuterPoly S) (cube n 1)
    (retained_body_subset _ _)
  simpa only [V.unit_cube] using hh

end ComputableAnalysis.RationalPolytopeVolume

namespace ComputableAnalysis.RationalPolytopeVolume
#print axioms mem_body_retained
#print axioms volume_retained_le_of_cut_nonneg
#print axioms mem_body_affineCube
#print axioms pointHull_bounded_cube
#print axioms volume_mono
#print axioms volume_nonneg
#print axioms volume_mono_of_vertex_halfspace_checks
#print axioms volume_clip_le
#print axioms volume_cap_nonneg
#print axioms body_orthantInnerPoly
#print axioms body_orthantOuterPoly
#print axioms orthant_inner_volume_le_outer
#print axioms orthant_inner_volume_refines
#print axioms orthant_outer_volume_refines
#print axioms orthant_cross_volume_le
#print axioms orthant_bracket_refinement
end ComputableAnalysis.RationalPolytopeVolume

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.mem_body_retained,
    `ComputableAnalysis.RationalPolytopeVolume.volume_retained_le_of_cut_nonneg,
    `ComputableAnalysis.RationalPolytopeVolume.mem_body_affineCube,
    `ComputableAnalysis.RationalPolytopeVolume.pointHull_bounded_cube,
    `ComputableAnalysis.RationalPolytopeVolume.volume_mono,
    `ComputableAnalysis.RationalPolytopeVolume.volume_nonneg,
    `ComputableAnalysis.RationalPolytopeVolume.volume_mono_of_vertex_halfspace_checks,
    `ComputableAnalysis.RationalPolytopeVolume.volume_clip_le,
    `ComputableAnalysis.RationalPolytopeVolume.volume_cap_nonneg,
    `ComputableAnalysis.RationalPolytopeVolume.body_orthantInnerPoly,
    `ComputableAnalysis.RationalPolytopeVolume.body_orthantOuterPoly,
    `ComputableAnalysis.RationalPolytopeVolume.orthant_inner_volume_le_outer,
    `ComputableAnalysis.RationalPolytopeVolume.orthant_inner_volume_refines,
    `ComputableAnalysis.RationalPolytopeVolume.orthant_outer_volume_refines,
    `ComputableAnalysis.RationalPolytopeVolume.orthant_cross_volume_le,
    `ComputableAnalysis.RationalPolytopeVolume.orthant_bracket_refinement]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
