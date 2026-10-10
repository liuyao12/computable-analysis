import RationalVolumeUniqueness

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

private def joinHeight (n : Nat) : (ℚ × Point n) →ₗ[ℚ] Point (n+1) where
  toFun := fun hx => Fin.cons hx.1 hx.2
  map_add' := by intro a b; ext i; refine Fin.cases rfl (fun j => rfl) i
  map_smul' := by intro a b; ext i; refine Fin.cases rfl (fun j => rfl) i

/-- A literal rational prism: its two vertex layers are at heights zero and r. -/
def prism {n : Nat} (P : Polytope n) (r : ℚ) : Polytope (n+1) :=
  (({0,r} : Finset ℚ) ×ˢ P).image (fun hp => Fin.cons hp.1 hp.2)

theorem body_prism {n : Nat} (P : Polytope n) (r : ℚ) (hr : 0 ≤ r) :
    body (prism P r)= {x : Point (n+1) | 0 ≤ x 0 ∧ x 0 ≤ r ∧
      (fun i => x i.succ) ∈ body P} := by
  classical
  have he : body (prism P r)= (joinHeight n) ''
      (convexHull ℚ ({0,r} : Set ℚ) ×ˢ body P) := by
    have hp : (((( {0,r} : Finset ℚ) ×ˢ P) : Finset (ℚ × Point n)) : Set (ℚ × Point n)) =
        ({0,r} : Set ℚ) ×ˢ (P : Set (Point n)) := by
      ext x; simp
    simp only [body,prism,Finset.coe_image]
    rw [hp]
    change convexHull ℚ ((joinHeight n) '' (({0,r} : Set ℚ) ×ˢ (P : Set (Point n)))) = _
    rw [← (joinHeight n).image_convexHull,convexHull_prod]
  rw [he,convexHull_pair,segment_eq_Icc hr]
  ext x
  constructor
  · rintro ⟨⟨h,p⟩,⟨hh,hp⟩,rfl⟩
    exact ⟨hh.1,hh.2,hp⟩
  · rintro ⟨h0,hr,hp⟩
    refine ⟨(x 0,fun i => x i.succ),⟨⟨h0,hr⟩,hp⟩,?_⟩
    ext i; refine Fin.cases rfl (fun j => rfl) i

/-- Lifting a rational affine map of the base to a height-preserving matrix.
The b term is a shear, so its determinant is the determinant of A. -/
def heightMatrix {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (b : Point n) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Fin.cases (Fin.cons 1 (fun _ => 0)) (fun i => Fin.cons (b i) (fun j => A i j))

theorem heightMatrix_det {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (b : Point n) :
    (heightMatrix A b).det=A.det := by
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
  simp only [heightMatrix,Fin.cases_zero,Fin.cons_zero,Fin.val_zero,pow_zero,one_mul,
    Fin.cases_succ,Fin.cons_succ,mul_zero,Finset.sum_const_zero,add_zero]
  change ((heightMatrix A b).submatrix Fin.succ (Fin.succAbove 0)).det +
    (∑ x : Fin n, 0 * ((heightMatrix A b).submatrix Fin.succ x.succ.succAbove).det) = A.det
  simp only [zero_mul,Finset.sum_const_zero,add_zero]
  have hm : (heightMatrix A b).submatrix Fin.succ (Fin.succAbove 0)=A := by
    ext i j
    simp [Matrix.submatrix,heightMatrix]
  rw [hm]

theorem heightMatrix_mulVec_zero {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (b : Point n) (x : Point (n+1)) : (heightMatrix A b).mulVec x 0=x 0 := by
  simp [Matrix.mulVec,dotProduct,heightMatrix,Fin.sum_univ_succ]

theorem heightMatrix_mulVec_succ {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (b : Point n) (x : Point (n+1)) (i : Fin n) :
    (heightMatrix A b).mulVec x i.succ=b i*x 0+A.mulVec (fun j => x j.succ) i := by
  simp [Matrix.mulVec,dotProduct,heightMatrix,Fin.sum_univ_succ]

/-- A base dissection lifts to a dissection of its rational prism. -/
theorem prism_dissection {n : Nat} {ι : Type} [Fintype ι]
    (P : Polytope n) (pieces : ι → Polytope n) (hd : Dissection P pieces)
    (r : ℚ) (hr : 0 ≤ r) : Dissection (prism P r) (fun i => prism (pieces i) r) := by
  constructor
  · intro x
    simp only [body_prism _ _ hr,Set.mem_ofPred_eq]
    rw [hd.1]
    constructor
    · rintro ⟨h0,hr,⟨i,hi⟩⟩; exact ⟨i,h0,hr,hi⟩
    · rintro ⟨i,h0,hr,hi⟩; exact ⟨h0,hr,i,hi⟩
  · intro i j hij
    obtain ⟨a,c,ha,hac⟩ := hd.2 i j hij
    refine ⟨Fin.cons 0 a,c,?_,?_⟩
    · intro hz
      apply ha
      ext k
      have hk := congrFun hz k.succ
      simpa using hk
    · intro x hx
      rw [body_prism _ _ hr,body_prism _ _ hr] at hx
      have hc := hac (fun k => x k.succ) ⟨hx.1.2.2,hx.2.2.2⟩
      simpa [dot,Fin.sum_univ_succ] using hc

theorem prism_translated {n : Nat} (P : Polytope n) (r : ℚ) (b : Point n) :
    prism (translated P b) r = translated (prism P r) (Fin.cons 0 b) := by
  classical
  ext x
  simp only [prism,translated,Finset.mem_image,Finset.mem_product]
  constructor
  · rintro ⟨⟨h,q⟩,⟨hh,⟨p,hp,rfl⟩⟩,rfl⟩
    refine ⟨Fin.cons h p,⟨(h,p),⟨hh,hp⟩,rfl⟩,?_⟩
    ext i; refine Fin.cases (by simp) (fun j => rfl) i
  · rintro ⟨q,⟨⟨h,p⟩,⟨hh,hp⟩,rfl⟩,rfl⟩
    refine ⟨(h,fun i => p i+b i),⟨hh,⟨p,hp,rfl⟩⟩,?_⟩
    ext i; refine Fin.cases (by simp) (fun j => rfl) i

theorem prism_transformed {n : Nat} (P : Polytope n) (r : ℚ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    prism (transformed P A) r = transformed (prism P r) (heightMatrix A 0) := by
  classical
  have he (h : ℚ) (p : Point n) :
      (heightMatrix A 0).mulVec (Fin.cons h p)=Fin.cons h (A.mulVec p) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [heightMatrix_mulVec_zero]
    · simp [heightMatrix_mulVec_succ]
  ext x
  simp only [prism,transformed,Finset.mem_image,Finset.mem_product]
  constructor
  · rintro ⟨⟨h,q⟩,⟨hh,⟨p,hp,rfl⟩⟩,rfl⟩
    exact ⟨Fin.cons h p,⟨(h,p),⟨hh,hp⟩,rfl⟩,he h p⟩
  · rintro ⟨q,⟨⟨h,p⟩,⟨hh,hp⟩,rfl⟩,rfl⟩
    exact ⟨(h,A.mulVec p),⟨hh,⟨p,hp,rfl⟩⟩,(he h p).symm⟩

theorem prism_unit_cube_body {n : Nat} (r : ℚ) (hr : 0 ≤ r) :
    body (prism (cube n 1) r)=body (box 0 (Fin.cons r (fun _ => 1))) := by
  ext x
  rw [body_prism _ _ hr,mem_body_box _ _ (by intro i; refine Fin.cases hr (fun j => by simp) i)]
  simp only [Set.mem_ofPred_eq,mem_body_cube n 1 (by decide)]
  constructor
  · rintro ⟨h0,hr,hp⟩ i
    refine Fin.cases ⟨h0,hr⟩ (fun j => hp j) i
  · intro h
    exact ⟨(h 0).1,(h 0).2,fun j => h j.succ⟩

/-- Prisms produce another volume satisfying exactly the existing base axioms. -/
noncomputable def prismAxioms {n : Nat} (V : Axioms (n+1)) (r : ℚ) (hr : 0 < r) :
    Axioms n where
  volume := fun P => V.volume (prism P r)/r
  extensional := by
    intro P Q he
    have hb : body (prism P r)=body (prism Q r) := by
      rw [body_prism _ _ hr.le,body_prism _ _ hr.le,he]
    rw [V.extensional _ _ hb]
  translation := by
    intro P b
    rw [prism_translated,V.translation]
  determinant_one := by
    intro P A hA
    rw [prism_transformed,V.determinant_one _ _ (by rw [heightMatrix_det,hA])]
  dissection := by
    intro ι inst P pieces hd
    rw [V.dissection _ _ (prism_dissection P pieces hd r hr.le)]
    simp only [div_eq_mul_inv,Finset.sum_mul]
  unit_cube := by
    rw [V.extensional _ _ (prism_unit_cube_body r hr.le)]
    have hp : ∀ i : Fin (n+1), 0 < (Fin.cons r (fun _ : Fin n => (1:ℚ)) : Point (n+1)) i := by
      intro i; cases i using Fin.cases
      · simpa using hr
      · simp
    have he := box_volume_positive n V (Fin.cons r (fun _ => 1)) hp
    change V.volume (box (fun _ => 0) (Fin.cons r (fun _ => 1)))/r=1
    rw [he]
    simp [Fin.prod_univ_succ,ne_of_gt hr]

/-- Exact prism volume, derived from finite dissections and volume uniqueness. -/
theorem prism_volume {n : Nat} (V : Axioms n) (W : Axioms (n+1))
    (P : Polytope n) (r : ℚ) (hr : 0 < r) :
    W.volume (prism P r)=r*V.volume P := by
  have he := volume_unique (prismAxioms W r hr) V P
  change W.volume (prism P r)/r=V.volume P at he
  exact (div_eq_iff (ne_of_gt hr)).mp he |>.trans (mul_comm _ _)

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.body_prism
#print axioms ComputableAnalysis.RationalPolytopeVolume.heightMatrix_det
#print axioms ComputableAnalysis.RationalPolytopeVolume.heightMatrix_mulVec_zero
#print axioms ComputableAnalysis.RationalPolytopeVolume.heightMatrix_mulVec_succ
#print axioms ComputableAnalysis.RationalPolytopeVolume.prism_dissection
#print axioms ComputableAnalysis.RationalPolytopeVolume.prism_translated
#print axioms ComputableAnalysis.RationalPolytopeVolume.prism_transformed
#print axioms ComputableAnalysis.RationalPolytopeVolume.prism_unit_cube_body
#print axioms ComputableAnalysis.RationalPolytopeVolume.prism_volume

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.body_prism,
    `ComputableAnalysis.RationalPolytopeVolume.heightMatrix_det,
    `ComputableAnalysis.RationalPolytopeVolume.heightMatrix_mulVec_zero,
    `ComputableAnalysis.RationalPolytopeVolume.heightMatrix_mulVec_succ,
    `ComputableAnalysis.RationalPolytopeVolume.prism_dissection,
    `ComputableAnalysis.RationalPolytopeVolume.prism_translated,
    `ComputableAnalysis.RationalPolytopeVolume.prism_transformed,
    `ComputableAnalysis.RationalPolytopeVolume.prism_unit_cube_body,
    `ComputableAnalysis.RationalPolytopeVolume.prism_volume]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
