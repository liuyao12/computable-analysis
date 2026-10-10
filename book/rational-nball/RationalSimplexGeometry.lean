import RationalPolytopeVolume
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fin.Tuple.Sort

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies

noncomputable def standardSimplex (n : Nat) : Polytope n := by
  classical
  exact insert 0 (Finset.univ.image axis)

theorem mem_body_standardSimplex (n : Nat) (x : Point n) :
    x ∈ body (standardSimplex n) ↔ (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1 := by
  classical
  let C : Set (Point n) := {y | (∀ i,0 ≤ y i) ∧ (∑ i,y i) ≤ 1}
  have hconv : Convex ℚ C := by
    intro y hy z hz a b ha hb hab
    constructor
    · intro i; exact add_nonneg (mul_nonneg ha (hy.1 i)) (mul_nonneg hb (hz.1 i))
    · change (∑ i, (a*y i+b*z i)) ≤ 1
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
      have h1 := mul_le_mul_of_nonneg_left hy.2 ha
      have h2 := mul_le_mul_of_nonneg_left hz.2 hb
      nlinarith
  constructor
  · apply convexHull_min _ hconv
    intro y hy
    simp only [standardSimplex, Finset.coe_insert, Finset.coe_image,
      Finset.coe_univ, Set.mem_insert_iff, Set.mem_image, Set.mem_univ, true_and] at hy
    rcases hy with rfl | ⟨i,rfl⟩
    · simp [C]
    · constructor
      · intro j; simp [axis]; split <;> norm_num
      · simp [axis, Finset.sum_ite_eq']
  · intro hx
    apply mem_convexHull_of_exists_fintype
      (Fin.cases (1-∑ i,x i) x) (Fin.cases 0 axis)
    · intro j; refine Fin.cases ?_ ?_ j
      · simp; linarith [hx.2]
      · intro i; simpa using hx.1 i
    · simp [Fin.sum_univ_succ]
    · intro j; refine Fin.cases ?_ ?_ j
      · simp [standardSimplex]
      · intro i; simp [standardSimplex]
    · ext i
      simp [Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, axis, Finset.sum_ite_eq']

 theorem body_transformed {n : Nat} (P : Polytope n)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    body (transformed P A) = A.mulVec '' body P := by
  classical
  simp only [body,transformed,Finset.coe_image]
  exact (A.mulVecLin.image_convexHull _).symm

/-- Integer triangular matrix of the staircase simplex. -/
def staircaseMatrix (n : Nat) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if j ≤ i then 1 else 0

theorem staircaseMatrix_det (n : Nat) : (staircaseMatrix n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [staircaseMatrix]
  · intro i j hij
    simp [staircaseMatrix,show ¬ j ≤ i by exact not_le.mpr hij]



/-- Staircase vertices, including the origin at the last index. -/
def stairVertex (n : Nat) (j : Fin (n+1)) : Point n :=
  fun i => if j.val ≤ i.val then 1 else 0
noncomputable def staircase (n : Nat) : Polytope n := by
  classical
  exact Finset.univ.image (stairVertex n)

private theorem prefix_sum (f : Nat → ℚ) (m i : Nat) (hi : i < m) :
    (∑ j ∈ Finset.range m, if j ≤ i then f j else 0) =
      ∑ j ∈ Finset.range (i+1), f j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

private def augmented (n : Nat) (x : Point n) (j : Nat) : ℚ :=
  if j = 0 then 0 else if h : j-1 < n then x ⟨j-1,h⟩ else 1

private theorem augmented_zero (n : Nat) (x : Point n) : augmented n x 0 = 0 := by
  simp [augmented]
private theorem augmented_last (n : Nat) (x : Point n) : augmented n x (n+1) = 1 := by
  simp [augmented]
private theorem augmented_coord (n : Nat) (x : Point n) (i : Fin n) :
    augmented n x (i.val+1) = x i := by
  simp [augmented,i.isLt]

private theorem augmented_step (n : Nat) (x : Point n)
    (hbox : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hmono : Monotone x)
    (j : Nat) (hj : j ≤ n) : augmented n x j ≤ augmented n x (j+1) := by
  cases j with
  | zero =>
    by_cases hn : 0 < n
    · simpa [augmented,hn] using (hbox ⟨0,hn⟩).1
    · simp [augmented,hn]
  | succ j =>
    have hjn : j < n := by omega
    by_cases hnext : j+1 < n
    · simpa [augmented,hjn,hnext] using
        hmono (show (⟨j,hjn⟩ : Fin n) ≤ ⟨j+1,hnext⟩ by simp)
    · have he : j+1=n := by omega
      simpa [augmented,hjn,hnext] using (hbox ⟨j,hjn⟩).2

/-- The ordered-coordinate region is exactly the finite staircase hull. -/
theorem mem_body_staircase (n : Nat) (x : Point n) :
    x ∈ body (staircase n) ↔ (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ Monotone x := by
  classical
  let C : Set (Point n) := {y | (∀ i,0 ≤ y i ∧ y i ≤ 1) ∧ Monotone y}
  have hconv : Convex ℚ C := by
    intro y hy z hz a b ha hb hab
    constructor
    · intro i
      constructor
      · exact add_nonneg (mul_nonneg ha (hy.1 i).1) (mul_nonneg hb (hz.1 i).1)
      · change a*y i+b*z i ≤ 1
        nlinarith [(hy.1 i).2,(hz.1 i).2]
    · intro i j hij
      change a*y i+b*z i ≤ a*y j+b*z j
      exact add_le_add (mul_le_mul_of_nonneg_left (hy.2 hij) ha)
        (mul_le_mul_of_nonneg_left (hz.2 hij) hb)
  constructor
  · apply convexHull_min _ hconv
    intro y hy
    simp only [staircase,Finset.coe_image,Finset.coe_univ,Set.mem_image,
      Set.mem_univ,true_and] at hy
    rcases hy with ⟨j,rfl⟩
    constructor
    · intro i; simp [stairVertex]; split <;> norm_num
    · intro i k hik
      simp only [stairVertex]
      split_ifs with hi hk
      · rfl
      · have := Fin.le_iff_val_le_val.mp hik; omega
      · norm_num
      · rfl
  · rintro ⟨hbox,hmono⟩
    let y := augmented n x
    let w : Fin (n+1) → ℚ := fun j => y (j.val+1)-y j.val
    apply mem_convexHull_of_exists_fintype w (stairVertex n)
    · intro j
      exact sub_nonneg.mpr (augmented_step n x hbox hmono j.val (by omega))
    · change (∑ j : Fin (n+1), (y (j.val+1)-y j.val)) = 1
      rw [Fin.sum_univ_eq_sum_range (fun j => y (j+1)-y j),Finset.sum_range_sub]
      simp [y,augmented_zero,augmented_last]
    · intro j; simp [staircase]
    · ext i
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      change (∑ j : Fin (n+1), w j * stairVertex n j i) = x i
      simp only [w,stairVertex,mul_ite,mul_one,mul_zero]
      rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ i.val then y (j+1)-y j else 0),prefix_sum _ (n+1) i.val (by omega),
        Finset.sum_range_sub]
      simp [y,augmented_zero,augmented_coord]



/-- Matrix images of the standard simplex consist of the origin and columns. -/
theorem transformed_standardSimplex {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) :
    transformed (standardSimplex n) A =
      insert 0 (Finset.univ.image (fun j i => A i j)) := by
  classical
  have hc (j : Fin n) : A.mulVec (axis j) = fun i => A i j := by
    ext i; simp [Matrix.mulVec,dotProduct,axis,mul_ite]
  simp [transformed,standardSimplex,Finset.image_insert,Finset.image_image,Function.comp_def,hc]

theorem staircase_eq_transformed (n : Nat) :
    staircase n = transformed (standardSimplex n) (staircaseMatrix n) := by
  classical
  rw [transformed_standardSimplex]
  ext x
  simp only [staircase,Finset.mem_image,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨j,rfl⟩
    by_cases hj : j.val < n
    · right; refine ⟨⟨j.val,hj⟩,?_⟩
      ext i; simp [staircaseMatrix,stairVertex,Fin.le_iff_val_le_val]
    · left; ext i
      simp [stairVertex,show ¬ j.val ≤ i.val by have := i.isLt; omega]
  · rintro (rfl | ⟨j,rfl⟩)
    · refine ⟨Fin.last n,?_⟩
      ext i; simp [stairVertex,show ¬ n ≤ i.val by omega]
    · refine ⟨j.castSucc,?_⟩
      ext i; simp only [stairVertex,staircaseMatrix,Fin.val_castSucc,Fin.le_iff_val_le_val]

noncomputable def reindexed {n : Nat} (P : Polytope n)
    (σ : Equiv.Perm (Fin n)) : Polytope n := by
  classical
  exact P.image (fun x i => x (σ i))

 theorem body_reindexed {n : Nat} (P : Polytope n) (σ : Equiv.Perm (Fin n)) :
    body (reindexed P σ) = (fun x i => x (σ i)) '' body P := by
  classical
  let L : Point n →ₗ[ℚ] Point n :=
    { toFun := fun x i => x (σ i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  simp only [body,reindexed,Finset.coe_image]
  exact (L.image_convexHull _).symm

 theorem mem_body_reindexed {n : Nat} (P : Polytope n)
    (σ : Equiv.Perm (Fin n)) (x : Point n) :
    x ∈ body (reindexed P σ) ↔ (fun i => x (σ.symm i)) ∈ body P := by
  rw [body_reindexed]
  constructor
  · rintro ⟨y,hy,rfl⟩; simpa using hy
  · intro hx
    refine ⟨fun i => x (σ.symm i),hx,?_⟩
    ext i; simp

/-- The column permutation changes only the presentation, so this matrix has
both the staircase hull's permuted body and determinant one. -/
theorem reindexed_staircase_eq_transformed (n : Nat) (σ : Equiv.Perm (Fin n)) :
    reindexed (staircase n) σ =
      transformed (standardSimplex n) ((staircaseMatrix n).submatrix σ σ) := by
  classical
  rw [staircase_eq_transformed,transformed_standardSimplex,
    transformed_standardSimplex]
  simp only [reindexed,Finset.image_insert,Finset.image_image]
  ext x
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_image,
    Finset.mem_univ,true_and,Matrix.submatrix_apply]
  constructor
  · rintro (h | ⟨j,hj⟩)
    · left; exact h
    · right; exact ⟨σ.symm j,by simpa using hj⟩
  · rintro (h | ⟨j,hj⟩)
    · left; exact h
    · right; exact ⟨σ j,hj⟩

theorem staircase_piece_volume (n : Nat) (V : Axioms n) (σ : Equiv.Perm (Fin n)) :
    V.volume (reindexed (staircase n) σ) = V.volume (standardSimplex n) := by
  rw [reindexed_staircase_eq_transformed]
  exact V.determinant_one _ _ (by rw [Matrix.det_submatrix_equiv_self,staircaseMatrix_det])



/-- Exact staircase dissection of the rational cube, including tied coordinates. -/
theorem cube_staircase_dissection (n : Nat) :
    Dissection (cube n 1) (fun σ : Equiv.Perm (Fin n) => reindexed (staircase n) σ) := by
  classical
  constructor
  · intro x
    rw [mem_body_cube n 1 (by norm_num)]
    constructor
    · intro hx
      refine ⟨(Tuple.sort x).symm,?_⟩
      rw [mem_body_reindexed,mem_body_staircase]
      refine ⟨fun i => hx _,?_⟩
      intro i j hij
      exact Tuple.monotone_sort x hij
    · rintro ⟨σ,hσ⟩ i
      rw [mem_body_reindexed,mem_body_staircase] at hσ
      simpa using hσ.1 (σ i)
  · intro σ τ hστ
    let π : Equiv.Perm (Fin n) := σ.symm.trans τ
    have hπ : π ≠ 1 := by
      intro he; apply hστ; apply Equiv.ext; intro i
      have hi := congrArg (fun p : Equiv.Perm (Fin n) => p (σ i)) he
      simpa [π] using hi.symm
    have hnot : ¬ Monotone π := fun h => hπ (Equiv.Perm.monotone_iff π |>.mp h)
    change ¬ ∀ ⦃i j⦄, i ≤ j → π i ≤ π j at hnot
    push Not at hnot
    obtain ⟨i,j,hij,hrev⟩ := hnot
    have hijne : i ≠ j := by intro h; subst j; exact (lt_irrefl _ hrev)
    have hab : σ.symm i ≠ σ.symm j := fun h => hijne (σ.symm.injective h)
    have hnormal : axis (σ.symm i)-axis (σ.symm j) ≠ (0 : Point n) := by
      intro h
      have he := congrFun h (σ.symm i)
      simp [axis,hab] at he
    refine ⟨axis (σ.symm i)-axis (σ.symm j),0,hnormal,?_⟩
    intro x hx
    have hσ := (mem_body_staircase n _).mp ((mem_body_reindexed _ σ x).mp hx.1)
    have hτ := (mem_body_staircase n _).mp ((mem_body_reindexed _ τ x).mp hx.2)
    have h1 := hσ.2 hij
    have h2 := hτ.2 hrev.le
    have h2' : x (σ.symm j) ≤ x (σ.symm i) := by simpa [π] using h2
    have he : x (σ.symm i) = x (σ.symm j) := le_antisymm h1 h2'
    simp [dot,sub_mul,Finset.sum_sub_distrib,axis,he]

/-- Simplex normalization, conditional on determinant-one invariance, derived
from the geometrically checked cube dissection
The numerical simplex formula is not assumed. Deriving affine invariance
from weaker volume axioms is a separate obligation. -/
theorem standardSimplex_volume (n : Nat) (V : Axioms n) :
    V.volume (standardSimplex n) = 1/(n.factorial:ℚ) := by
  classical
  have h := V.dissection (cube n 1)
    (fun σ : Equiv.Perm (Fin n) => reindexed (staircase n) σ)
    (cube_staircase_dissection n)
  simp only [V.unit_cube,staircase_piece_volume,Finset.sum_const,
    Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul] at h
  have hn : (n.factorial:ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply (eq_div_iff hn).mpr
  simpa [mul_comm] using h.symm

#print axioms cube_staircase_dissection
#print axioms standardSimplex_volume

end ComputableAnalysis.RationalPolytopeVolume

open Lean
run_cmd do
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env [
    `ComputableAnalysis.RationalPolytopeVolume.cube_staircase_dissection,
    `ComputableAnalysis.RationalPolytopeVolume.standardSimplex_volume]
  let forbidden := deps.filter fun n => let s := n.toString; s == "sorryAx" || s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden dependencies: {forbidden}"
  logInfo m!"PASS: {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
