import RationalProductVolume

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

noncomputable def dilated {n : Nat} (P : Polytope n) (r : ℚ) : Polytope n :=
  transformed P (Matrix.diagonal (fun _ => r))

theorem diagonal_mulVec {n : Nat} (r : ℚ) (p : Point n) :
    (Matrix.diagonal (fun _ : Fin n => r)).mulVec p=r • p := by
  ext i; simp [Matrix.mulVec,dotProduct,Matrix.diagonal]

theorem body_dilated {n : Nat} (P : Polytope n) (r : ℚ) :
    body (dilated P r)=(fun p => r • p) '' body P := by
  rw [dilated,body_transformed]
  congr 1
  funext p; exact diagonal_mulVec r p

theorem dilated_translated {n : Nat} (P : Polytope n) (r : ℚ) (b : Point n) :
    dilated (translated P b) r=translated (dilated P r) (r • b) := by
  classical
  simp only [dilated,transformed,translated,Finset.image_image]
  congr 1
  funext p
  change (Matrix.diagonal (fun _ : Fin n => r)).mulVec (p+b)=
    (Matrix.diagonal (fun _ : Fin n => r)).mulVec p+r • b
  rw [diagonal_mulVec,diagonal_mulVec,smul_add]

theorem dilated_transformed {n : Nat} (P : Polytope n) (r : ℚ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    dilated (transformed P A) r=transformed (dilated P r) A := by
  classical
  simp only [dilated,transformed_composition]
  congr 1
  ext i j
  simp [Matrix.mul_apply,Matrix.diagonal,mul_comm]

theorem dilated_cube_volume {n : Nat} (V : Axioms n) (r : ℚ) (hr : 0 < r) :
    V.volume (dilated (cube n 1) r)=r^n := by
  cases n with
  | zero =>
    have he : dilated (cube 0 1) r=cube 0 1 := by
      classical
      have hm : (Matrix.diagonal (fun _ : Fin 0 => r)).mulVec = id := by
        funext x; exact Subsingleton.elim _ _
      simp only [dilated,transformed,hm,Finset.image_id]
    rw [he,V.unit_cube,pow_zero]
  | succ n =>
    rw [dilated,transformed_cube_volume]
    · simp [Matrix.det_diagonal]
    · simp only [Matrix.det_diagonal,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      exact pow_pos hr _

noncomputable def dilationAxioms {n : Nat} (V : Axioms n) (r : ℚ) (hr : 0 < r) : Axioms n where
  volume := fun P => V.volume (dilated P r)/r^n
  extensional := by
    intro P Q he
    have hb : body (dilated P r)=body (dilated Q r) := by rw [body_dilated,body_dilated,he]
    rw [V.extensional _ _ hb]
  translation := by
    intro P b
    rw [dilated_translated,V.translation]
  determinant_one := by
    intro P A hA
    rw [dilated_transformed,V.determinant_one _ _ hA]
  dissection := by
    intro ι inst P pieces hd
    have hdet : (Matrix.diagonal (fun _ : Fin n => r)).det ≠ 0 := by
      simp [Matrix.det_diagonal,ne_of_gt hr]
    rw [show dilated P r=transformed P (Matrix.diagonal (fun _ => r)) from rfl,
      V.dissection _ _ (dissection_transformed _ _ hd _ hdet)]
    simp only [dilated,div_eq_mul_inv,Finset.sum_mul]
  unit_cube := by
    rw [dilated_cube_volume V r hr,div_self (ne_of_gt (pow_pos hr n))]

/-- Scaling all rational coordinates multiplies every polytope's volume by
r^n; neither this law nor determinant scaling is a new axiom. -/
theorem dilated_volume {n : Nat} (V : Axioms n) (P : Polytope n) (r : ℚ) (hr : 0 < r) :
    V.volume (dilated P r)=r^n*V.volume P := by
  have he := volume_unique (dilationAxioms V r hr) V P
  change V.volume (dilated P r)/r^n=V.volume P at he
  have hn : r^n ≠ 0 := ne_of_gt (pow_pos hr n)
  exact ((div_eq_iff hn).mp he).trans (mul_comm _ _)

theorem dilated_volume_nonneg_dimension {n : Nat} (hn : 0 < n) (V : Axioms n)
    (P : Polytope n) (r : ℚ) (hr : 0 ≤ r) :
    V.volume (dilated P r)=r^n*V.volume P := by
  rcases hr.eq_or_lt with rfl | hr
  · have hf : Flat (body (dilated P 0)) := by
      let i : Fin n := ⟨0,hn⟩
      refine ⟨axis i,0,?_,?_⟩
      · intro hz; have h := congrFun hz i; simp [axis] at h
      · intro x hx
        rw [body_dilated] at hx
        obtain ⟨p,hp,rfl⟩ := hx
        simp [dot]
    rw [volume_flat n V _ hf,zero_pow (by omega),zero_mul]
  · exact dilated_volume V P r hr

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.diagonal_mulVec
#print axioms ComputableAnalysis.RationalPolytopeVolume.body_dilated
#print axioms ComputableAnalysis.RationalPolytopeVolume.dilated_translated
#print axioms ComputableAnalysis.RationalPolytopeVolume.dilated_transformed
#print axioms ComputableAnalysis.RationalPolytopeVolume.dilated_cube_volume
#print axioms ComputableAnalysis.RationalPolytopeVolume.dilated_volume
#print axioms ComputableAnalysis.RationalPolytopeVolume.dilated_volume_nonneg_dimension

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.diagonal_mulVec,
    `ComputableAnalysis.RationalPolytopeVolume.body_dilated,
    `ComputableAnalysis.RationalPolytopeVolume.dilated_translated,
    `ComputableAnalysis.RationalPolytopeVolume.dilated_transformed,
    `ComputableAnalysis.RationalPolytopeVolume.dilated_cube_volume,
    `ComputableAnalysis.RationalPolytopeVolume.dilated_volume,
    `ComputableAnalysis.RationalPolytopeVolume.dilated_volume_nonneg_dimension]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
