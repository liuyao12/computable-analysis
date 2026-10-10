import RationalSimplexDissection
import RationalVolumeScaling
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies

/-- Composition acts on the geometric finite vertex presentation. -/
theorem transformed_composition {n : Nat} (P : Polytope n)
    (A B : Matrix (Fin n) (Fin n) ℚ) :
    transformed (transformed P B) A = transformed P (A*B) := by
  classical
  simp only [transformed,Finset.image_image]
  congr 1
  funext x
  exact Matrix.mulVec_mulVec x A B

/-- Positive determinant simplex volume is derived from edge dissections and
special-linear invariance; general determinant scaling is not an axiom. -/
theorem transformed_simplex_volume (n : Nat) (V : Axioms (n+1))
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (hA : 0 < A.det) :
    V.volume (transformed (standardSimplex (n+1)) A) =
      A.det/(Nat.factorial (n+1):ℚ) := by
  let D := firstStretch n A.det
  let S := A*D⁻¹
  have hD : D.det=A.det := firstStretch_det n A.det
  have hunit : IsUnit D.det := isUnit_iff_ne_zero.mpr (hD ▸ ne_of_gt hA)
  have hS : S.det=1 := by
    dsimp [S]
    rw [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,hD]
    exact mul_inv_cancel₀ (ne_of_gt hA)
  have he : S*D=A := Matrix.nonsing_inv_mul_cancel_right D A hunit
  have hv := V.determinant_one (stretchedSimplex n A.det) S hS
  rw [stretchedSimplex,transformed_composition,he] at hv
  rw [hv]
  exact stretchedSimplex_volume n V A.det hA

/-- The ordered rational vertices give the standard affine-simplex presentation. -/
noncomputable def vertexSimplex {n : Nat} (p : RationalSimplex.Vertices n) : Polytope n :=
  Finset.univ.image p

theorem vertexSimplex_affine {n : Nat} (p : RationalSimplex.Vertices n) :
    vertexSimplex p = translated
      (transformed (standardSimplex n) (RationalSimplex.edgeMatrix p)) (p 0) := by
  classical
  ext x
  simp only [vertexSimplex,Finset.mem_image,Finset.mem_univ,true_and,
    translated,transformed]
  constructor
  · rintro ⟨j,rfl⟩
    refine Fin.cases ?_ (fun k => ?_) j
    · refine ⟨0,⟨0,by simp [standardSimplex],by simp⟩,?_⟩
      simp
    · refine ⟨fun i => p k.succ i-p 0 i,⟨axis k,by simp [standardSimplex],?_⟩,?_⟩
      · ext i; simp [RationalSimplex.edgeMatrix,Matrix.mulVec,dotProduct,axis]
      · ext i; simp
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    simp only [standardSimplex,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hz
    rcases hz with rfl | ⟨j,rfl⟩
    · exact ⟨0,by simp⟩
    · refine ⟨j.succ,?_⟩
      ext i
      simp [RationalSimplex.edgeMatrix,Matrix.mulVec,dotProduct,axis]

/-- Geometric volume agrees with the rational determinant coefficient on a
positively oriented nondegenerate simplex, in every positive dimension. -/
theorem vertexSimplex_volume_positive (n : Nat) (V : Axioms (n+1))
    (p : RationalSimplex.Vertices (n+1))
    (hp : 0 < (RationalSimplex.edgeMatrix p).det) :
    V.volume (vertexSimplex p) = RationalSimplex.determinantCoefficient p := by
  rw [vertexSimplex_affine,V.translation,
    transformed_simplex_volume n V _ hp]
  rfl

/-- Exchange the origin and first axis vertex by a rational affine map. -/
def simplexFlip (n : Nat) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  firstStretch n (-1)*edgeShear n (-1)

theorem simplexFlip_det (n : Nat) : (simplexFlip n).det = -1 := by
  simp [simplexFlip,Matrix.det_mul,firstStretch_det,edgeShear_det]

theorem simplexFlip_axis (n : Nat) (j : Fin (n+1)) :
    (simplexFlip n).mulVec (axis j)+axis 0 =
      if j=0 then 0 else axis j := by
  by_cases hj : j=0
  · subst j
    ext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [simplexFlip,← Matrix.mulVec_mulVec,firstStretch_mulVec_zero,
        edgeShear_mulVec_zero,axis,eq_comm]
    · simp [simplexFlip,← Matrix.mulVec_mulVec,firstStretch_mulVec_succ,
        edgeShear_mulVec_succ,axis]
  · obtain ⟨k,rfl⟩ := Fin.eq_succ_of_ne_zero hj
    ext i
    refine Fin.cases ?_ (fun l => ?_) i
    · simp [simplexFlip,← Matrix.mulVec_mulVec,firstStretch_mulVec_zero,
        edgeShear_mulVec_zero,axis,eq_comm]
    · simp [simplexFlip,← Matrix.mulVec_mulVec,firstStretch_mulVec_succ,
        edgeShear_mulVec_succ,axis]

theorem simplexFlip_preserves (n : Nat) :
    translated (transformed (standardSimplex (n+1)) (simplexFlip n)) (axis 0) =
      standardSimplex (n+1) := by
  classical
  ext x
  simp only [translated,transformed,Finset.mem_image,standardSimplex,
    Finset.mem_insert,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    rcases hz with rfl | ⟨j,rfl⟩
    · right; exact ⟨0,by simp⟩
    · change ((simplexFlip n).mulVec (axis j)+axis 0=0) ∨
        ∃ k, axis k=(simplexFlip n).mulVec (axis j)+axis 0
      rw [simplexFlip_axis]
      split_ifs with hj
      · exact Or.inl rfl
      · exact Or.inr ⟨j,rfl⟩
  · rintro (rfl | ⟨j,rfl⟩)
    · refine ⟨(simplexFlip n).mulVec (axis 0),⟨axis 0,Or.inr ⟨0,rfl⟩,rfl⟩,?_⟩
      ext i
      simpa using congrFun (simplexFlip_axis n 0) i
    · by_cases hj : j=0
      · subst j; exact ⟨0,⟨0,Or.inl rfl,by simp⟩,by simp⟩
      · refine ⟨(simplexFlip n).mulVec (axis j),⟨axis j,Or.inr ⟨j,rfl⟩,rfl⟩,?_⟩
        ext i
        simpa [hj] using congrFun (simplexFlip_axis n j) i

theorem transformed_translation {n : Nat} (P : Polytope n) (b : Point n)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    transformed (translated P b) A = translated (transformed P A) (A.mulVec b) := by
  classical
  simp only [transformed,translated,Finset.image_image]
  congr 1
  funext x
  ext i
  have h := congrFun (Matrix.mulVec_add A x b) i
  exact h

theorem transformed_simplex_volume_negative (n : Nat) (V : Axioms (n+1))
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (hA : A.det < 0) :
    V.volume (transformed (standardSimplex (n+1)) A) =
      -A.det/(Nat.factorial (n+1):ℚ) := by
  have hp := congrArg (fun P => transformed P A) (simplexFlip_preserves n)
  rw [transformed_translation,transformed_composition] at hp
  rw [← hp,V.translation,transformed_simplex_volume]
  · simp [Matrix.det_mul,simplexFlip_det]
  · simpa [Matrix.det_mul,simplexFlip_det] using neg_pos.mpr hA

/-- A singular rational affine simplex lies in a rational hyperplane. -/
theorem transformed_simplex_flat {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.det=0) :
    Flat (body (transformed (standardSimplex n) A)) := by
  have hnot : ¬ Function.Injective A.vecMul := by
    intro hinj
    have hu := Matrix.vecMul_injective_iff_isUnit.mp hinj
    have hd := (Matrix.isUnit_iff_isUnit_det A).mp hu
    simpa [hA] using hd
  rw [Function.Injective] at hnot
  push Not at hnot
  rcases hnot with ⟨u,v,huv,hne⟩
  have hn : u-v ≠ 0 := sub_ne_zero.mpr hne
  have hk : A.vecMul (u-v)=0 := by
    rw [Matrix.sub_vecMul,huv,sub_self]
  refine ⟨u-v,0,hn,?_⟩
  intro x hx
  rw [body_transformed] at hx
  rcases hx with ⟨y,hy,rfl⟩
  change dotProduct (u-v) (A.mulVec y)=0
  rw [Matrix.dotProduct_mulVec,hk,zero_dotProduct]

theorem vertexSimplex_volume_zero (n : Nat) (V : Axioms n)
    (p : RationalSimplex.Vertices n) (hp : (RationalSimplex.edgeMatrix p).det=0) :
    V.volume (vertexSimplex p) = 0 := by
  rw [vertexSimplex_affine,V.translation]
  exact volume_flat n V _ (transformed_simplex_flat _ hp)

/-- Orientation belongs to an ordered simplex, not to its underlying hull. -/
noncomputable def simplexVolume {n : Nat} (V : Axioms n)
    (p : RationalSimplex.Vertices n) : ℚ :=
  if (RationalSimplex.edgeMatrix p).det < 0 then -V.volume (vertexSimplex p)
  else V.volume (vertexSimplex p)

/-- The determinant coefficient is proved to be the volume of every ordered
rational simplex, including degenerate and negatively oriented cases. -/
theorem simplexVolume_eq_coefficient (n : Nat) (V : Axioms n)
    (p : RationalSimplex.Vertices n) :
    simplexVolume V p = RationalSimplex.determinantCoefficient p := by
  cases n with
  | zero =>
    have hp : vertexSimplex p=cube 0 1 := by
      classical
      ext x
      have he : x=p 0 := Subsingleton.elim _ _
      subst x
      simp [vertexSimplex,cube,box]
      exact Subsingleton.elim _ _
    simp [simplexVolume,RationalSimplex.determinantCoefficient,Matrix.det_isEmpty,
      hp,V.unit_cube]
  | succ n =>
    by_cases hn : (RationalSimplex.edgeMatrix p).det < 0
    · rw [simplexVolume,if_pos hn,vertexSimplex_affine,V.translation,
        transformed_simplex_volume_negative n V _ hn]
      dsimp [RationalSimplex.determinantCoefficient]
      ring
    · rw [simplexVolume,if_neg hn]
      by_cases hz : (RationalSimplex.edgeMatrix p).det=0
      · rw [vertexSimplex_volume_zero _ V p hz]
        simp [RationalSimplex.determinantCoefficient,hz]
      · exact vertexSimplex_volume_positive n V p
          (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz))

/-- Expanding every coordinate by any rational factor gives the induced
orientation and the expected power law, in every dimension. -/
theorem simplexVolume_dilation (n : Nat) (V : Axioms n)
    (p : RationalSimplex.Vertices n) (k : ℚ) :
    simplexVolume V (RationalSimplex.dilated k p) = k^n*simplexVolume V p := by
  rw [simplexVolume_eq_coefficient,simplexVolume_eq_coefficient]
  exact RationalSimplex.determinantCoefficient_dilation k p

/-- A supplied, geometrically verified positive triangulation computes the
same axiomatic volume. This does not assume a triangulation constructor. -/
theorem triangulation_volume {n : Nat} (V : Axioms n) (P : Polytope n)
    {ι : Type} [Fintype ι] (p : ι → RationalSimplex.Vertices n)
    (hd : Dissection P (fun j => vertexSimplex (p j)))
    (hp : ∀ j,0 ≤ (RationalSimplex.edgeMatrix (p j)).det) :
    V.volume P = ∑ j,RationalSimplex.determinantCoefficient (p j) := by
  rw [V.dissection P _ hd]
  apply Finset.sum_congr rfl
  intro j _
  have h := simplexVolume_eq_coefficient n V (p j)
  simpa only [simplexVolume,if_neg (not_lt_of_ge (hp j))] using h

/-- Two positive triangulations of the same body have equal rational sums. -/
theorem triangulation_independence {n : Nat} (V : Axioms n) (P Q : Polytope n)
    (he : body P=body Q) {ι κ : Type} [Fintype ι] [Fintype κ]
    (p : ι → RationalSimplex.Vertices n) (q : κ → RationalSimplex.Vertices n)
    (hp : Dissection P (fun j => vertexSimplex (p j)))
    (hq : Dissection Q (fun j => vertexSimplex (q j)))
    (hop : ∀ j,0 ≤ (RationalSimplex.edgeMatrix (p j)).det)
    (hoq : ∀ j,0 ≤ (RationalSimplex.edgeMatrix (q j)).det) :
    (∑ j,RationalSimplex.determinantCoefficient (p j)) =
      ∑ j,RationalSimplex.determinantCoefficient (q j) := by
  rw [← triangulation_volume V P p hp hop,← triangulation_volume V Q q hq hoq]
  exact V.extensional P Q he

#print axioms transformed_simplex_volume
#print axioms vertexSimplex_volume_positive
#print axioms vertexSimplex_volume_zero
#print axioms simplexVolume_eq_coefficient
#print axioms simplexVolume_dilation
#print axioms triangulation_volume
#print axioms triangulation_independence
end ComputableAnalysis.RationalPolytopeVolume

open Lean
run_cmd do
  let endpoints := [
    `ComputableAnalysis.RationalPolytopeVolume.cube_grid_dissection,
    `ComputableAnalysis.RationalPolytopeVolume.cube_positive,
    `ComputableAnalysis.RationalPolytopeVolume.orientedCubeVolume_dilation,
    `ComputableAnalysis.RationalPolytopeVolume.cube_staircase_dissection,
    `ComputableAnalysis.RationalPolytopeVolume.standardSimplex_volume,
    `ComputableAnalysis.RationalPolytopeVolume.simplex_edge_dissection,
    `ComputableAnalysis.RationalPolytopeVolume.stretchedSimplex_volume,
    `ComputableAnalysis.RationalPolytopeVolume.simplexVolume_eq_coefficient,
    `ComputableAnalysis.RationalPolytopeVolume.simplexVolume_dilation,
    `ComputableAnalysis.RationalPolytopeVolume.triangulation_volume,
    `ComputableAnalysis.RationalPolytopeVolume.triangulation_independence]
  for name in endpoints do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env endpoints
  let forbidden := deps.filter fun n => let s := n.toString;
    s == "sorryAx" || s == "Real" || s.startsWith "Real." ||
    s == "Complex" || s.startsWith "Complex." ||
    s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden dependencies: {forbidden}"
  logInfo m!"PASS: {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration; trusted axioms only"
