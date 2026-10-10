import RationalSimplexVolume

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies

/-- Invertible rational maps transport actual coverage and flat-overlap
proofs. No transformed-volume axiom is invoked in this geometric lemma. -/
theorem dissection_transformed {n : Nat} {ι : Type} [Fintype ι]
    (P : Polytope n) (pieces : ι → Polytope n) (hd : Dissection P pieces)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.det ≠ 0) :
    Dissection (transformed P A) (fun j => transformed (pieces j) A) := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hunit)
  constructor
  · intro x
    simp only [body_transformed,Set.mem_image]
    constructor
    · rintro ⟨y,hy,rfl⟩
      rcases (hd.1 y).mp hy with ⟨j,hj⟩
      exact ⟨j,y,hj,rfl⟩
    · rintro ⟨j,y,hy,rfl⟩
      exact ⟨y,(hd.1 y).mpr ⟨j,hy⟩,rfl⟩
  · intro j k hjk
    rcases hd.2 j k hjk with ⟨a,c,ha,hac⟩
    let normal := A⁻¹.vecMul a
    have hreconstruct : A.vecMul normal=a := by
      dsimp [normal]
      rw [Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul A hunit,Matrix.vecMul_one]
    have hn : normal ≠ 0 := by
      intro hz
      rw [hz,Matrix.zero_vecMul] at hreconstruct
      exact ha hreconstruct.symm
    refine ⟨normal,c,hn,?_⟩
    intro x hx
    rw [body_transformed] at hx
    rcases hx.1 with ⟨y,hy,hxy⟩
    have hxk : x ∈ body (transformed (pieces k) A) := hx.2
    rw [body_transformed] at hxk
    rcases hxk with ⟨z,hz,hxz⟩
    have he : y=z := hinj (hxy.trans hxz.symm)
    subst z
    rw [← hxy]
    change dotProduct normal (A.mulVec y)=c
    rw [Matrix.dotProduct_mulVec,hreconstruct]
    exact hac y ⟨hy,hz⟩

/-- Matrix images of an ordered simplex have the transformed vertex hull. -/
theorem transformed_vertexSimplex {n : Nat} (p : RationalSimplex.Vertices n)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    transformed (vertexSimplex p) A = vertexSimplex (RationalSimplex.transformed A p) := by
  classical
  simp only [transformed,vertexSimplex,RationalSimplex.transformed,Finset.image_image]
  rfl

/-- General determinant scaling follows for every supplied positive
triangulation; the transformed triangulation's geometry is constructed. -/
theorem triangulated_volume_transform {n : Nat} (V : Axioms n) (P : Polytope n)
    {ι : Type} [Fintype ι] (p : ι → RationalSimplex.Vertices n)
    (hd : Dissection P (fun j => vertexSimplex (p j)))
    (hp : ∀ j,0 ≤ (RationalSimplex.edgeMatrix (p j)).det)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : 0 < A.det) :
    V.volume (transformed P A)=A.det*V.volume P := by
  have ht := dissection_transformed P _ hd A (ne_of_gt hA)
  simp only [transformed_vertexSimplex] at ht
  have hpos : ∀ j,0 ≤ (RationalSimplex.edgeMatrix
      (RationalSimplex.transformed A (p j))).det := by
    intro j
    rw [RationalSimplex.edgeMatrix_transformed,Matrix.det_mul]
    exact mul_nonneg hA.le (hp j)
  rw [triangulation_volume V _ _ ht hpos,triangulation_volume V P p hd hp]
  simp only [RationalSimplex.determinantCoefficient_linear,Finset.mul_sum]

/-- A cube's staircase dissection supplies the geometry needed to derive
its volume under every positive-determinant rational map. -/
theorem transformed_cube_volume (n : Nat) (V : Axioms (n+1))
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (hA : 0 < A.det) :
    V.volume (transformed (cube (n+1) 1) A)=A.det := by
  classical
  have hd := dissection_transformed _ _ (cube_staircase_dissection (n+1)) A (ne_of_gt hA)
  rw [V.dissection _ _ hd]
  have hp (σ : Equiv.Perm (Fin (n+1))) :
      V.volume (transformed (reindexed (staircase (n+1)) σ) A)=
        A.det/((n+1).factorial:ℚ) := by
    rw [reindexed_staircase_eq_transformed,transformed_composition,transformed_simplex_volume]
    · simp [Matrix.det_mul,Matrix.det_submatrix_equiv_self,staircaseMatrix_det]
    · simpa [Matrix.det_mul,Matrix.det_submatrix_equiv_self,staircaseMatrix_det] using hA
  simp only [hp,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,
    nsmul_eq_mul]
  have hf : ((n+1).factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
  field_simp

/-- The vertex presentation of a rational box is the diagonal image of the
unit cube; this is a finite equality, including possible zero side lengths. -/
theorem transformed_cube_diagonal (n : Nat) (r : Point n) :
    transformed (cube n 1) (Matrix.diagonal r)=box (fun _ => 0) r := by
  classical
  ext x
  simp only [transformed,Finset.mem_image,cube,box,Fintype.mem_piFinset,
    Finset.mem_insert,Finset.mem_singleton,Matrix.mulVec_diagonal]
  constructor
  · rintro ⟨y,hy,rfl⟩ i
    rcases hy i with h | h
    · left; simp [Matrix.mulVec_diagonal,h]
    · right; simp [Matrix.mulVec_diagonal,h]
  · intro hx
    refine ⟨fun i => if x i=0 then 0 else 1,?_,?_⟩
    · intro i; dsimp; split_ifs <;> simp
    · ext i
      rcases hx i with h | h
      · simp [Matrix.mulVec_diagonal,h]
      · rw [Matrix.mulVec_diagonal,h]
        by_cases hz : r i=0
        · simp [hz]
        · simp [hz]

/-- Rational rectangular-box volume is derived from the cube dissection
and the already proved simplex formula, not assumed as a product axiom. -/
theorem box_volume_positive (n : Nat) (V : Axioms (n+1)) (r : Point (n+1))
    (hr : ∀ i,0 < r i) :
    V.volume (box (fun _ => 0) r)=∏ i,r i := by
  rw [← transformed_cube_diagonal,transformed_cube_volume]
  · exact Matrix.det_diagonal
  · rw [Matrix.det_diagonal]
    exact Finset.prod_pos (fun i _ => hr i)

theorem box_volume_positive_dimension (n : Nat) (hn : 0 < n) (V : Axioms n)
    (r : Point n) (hr : ∀ i,0 < r i) :
    V.volume (box (fun _ => 0) r)=∏ i,r i := by
  cases n with
  | zero => omega
  | succ n => exact box_volume_positive n V r hr

/-- Product volume for rational boxes is a theorem of the supplied volume
axioms in each dimension. It is not an additional product-volume axiom. -/
theorem box_product_volume (n m : Nat) (hn : 0 < n) (hm : 0 < m)
    (V : ∀ d,Axioms d) (r : Point n) (s : Point m)
    (hr : ∀ i,0 < r i) (hs : ∀ i,0 < s i) :
    (V (n+m)).volume (box (fun _ => 0) (Fin.append r s)) =
      (V n).volume (box (fun _ => 0) r)*(V m).volume (box (fun _ => 0) s) := by
  have hpos : ∀ i,0 < Fin.append r s i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j; simpa using hr j
    · intro j; simpa using hs j
  rw [box_volume_positive_dimension (n+m) (by omega) (V (n+m)) _ hpos,
    box_volume_positive_dimension n hn (V n) r hr,
    box_volume_positive_dimension m hm (V m) s hs,Fin.prod_univ_add]
  simp

#print axioms dissection_transformed
#print axioms triangulated_volume_transform
#print axioms transformed_cube_volume
#print axioms box_volume_positive
#print axioms box_product_volume
end ComputableAnalysis.RationalPolytopeVolume

open Lean
run_cmd do
  let endpoints := [
    `ComputableAnalysis.RationalPolytopeVolume.dissection_transformed,
    `ComputableAnalysis.RationalPolytopeVolume.triangulated_volume_transform,
    `ComputableAnalysis.RationalPolytopeVolume.transformed_cube_volume,
    `ComputableAnalysis.RationalPolytopeVolume.box_product_volume]
  for name in endpoints do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  let deps := RationalProofAudit.audit (← Lean.getEnv) endpoints
  let forbidden := deps.filter fun n => let s := n.toString;
    s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." ||
    s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden dependencies: {forbidden}"
  logInfo m!"PASS: {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration; trusted axioms only"
