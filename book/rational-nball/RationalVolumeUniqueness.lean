import RationalVolumeMonotonicity

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies

/-- Rational dissections determine the volume of a clipped affine cube. -/
theorem retained_affineCube_volume_unique (n : Nat) (V W : Axioms n)
    (b : Point n) (r : ℚ) (hr : 0 < r) (cuts : List (Point n × ℚ)) :
    V.volume (retainedAfterCuts (affineCube n b r) cuts)=
      W.volume (retainedAfterCuts (affineCube n b r) cuts) := by
  classical
  let A : Matrix (Fin n) (Fin n) ℚ := Matrix.diagonal (fun _ => r)
  have hA : A.det ≠ 0 := by simp [A,Matrix.det_diagonal,ne_of_gt hr]
  let p (σ : Equiv.Perm (Fin n)) := matrixVertices ((staircaseMatrix n).submatrix σ σ)
  have hd : Dissection (cube n 1) (fun σ => vertexSimplex (p σ)) := by
    simpa only [p,vertexSimplex_matrix,reindexed_staircase_eq_transformed]
      using cube_staircase_dissection n
  have ht := dissection_translated _ _ (dissection_transformed _ _ hd A hA) b
  simp only [transformed_vertexSimplex,translated_vertexSimplex] at ht
  have hc := dissection_retained cuts _ _ ht
  change V.volume (retainedAfterCuts (translated (transformed (cube n 1) A) b) cuts)=
    W.volume (retainedAfterCuts (translated (transformed (cube n 1) A) b) cuts)
  rw [V.dissection _ _ hc,W.dissection _ _ hc]
  exact Finset.sum_congr rfl (fun i _ => retained_simplex_volume_unique V W _ cuts)

/-- The finite rational volume axioms have at most one volume function.
This is derived from cuts and the simplex formula, not assumed in a record. -/
theorem volume_unique {n : Nat} (V W : Axioms n) (P : Polytope n) :
    V.volume P=W.volume P := by
  classical
  obtain ⟨b,r,hr,hP⟩ := pointHull_bounded_cube P
  obtain ⟨cuts,hcuts⟩ := pointHull_halfspaces P
  have he : body (retainedAfterCuts (affineCube n b r) cuts.toList)=body P := by
    ext x
    rw [mem_body_retained]
    simp only [Finset.mem_toList]
    constructor
    · rintro ⟨_,hx⟩; exact (hcuts x).mpr hx
    · intro hx; exact ⟨hP hx,(hcuts x).mp hx⟩
  rw [← V.extensional _ _ he,← W.extensional _ _ he]
  exact retained_affineCube_volume_unique n V W b r hr _

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.retained_affineCube_volume_unique
#print axioms ComputableAnalysis.RationalPolytopeVolume.volume_unique

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.retained_affineCube_volume_unique,
    `ComputableAnalysis.RationalPolytopeVolume.volume_unique]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
