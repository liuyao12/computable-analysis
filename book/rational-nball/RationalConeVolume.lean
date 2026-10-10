import RationalPrismVolume
import Mathlib.Analysis.Convex.Join

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

private def baseLayerMap (n : Nat) : Point n →ᵃ[ℚ] Point (n+1) where
  toFun := fun p => (Fin.cons (1:ℚ) p : Point (n+1))
  linear := {
    toFun := fun p => (Fin.cons (0:ℚ) p : Point (n+1))
    map_add' := by intro a b; ext i; refine Fin.cases (by simp) (fun j => rfl) i
    map_smul' := by intro a b; ext i; refine Fin.cases (by simp) (fun j => rfl) i }
  map_vadd' := by intro p v; ext i; refine Fin.cases (by simp) (fun j => rfl) i

def cone {n : Nat} (P : Polytope n) : Polytope (n+1) :=
  insert 0 (P.image (Fin.cons 1))

/-- An exact rational point description, including the degenerate empty base. -/
theorem mem_body_cone {n : Nat} (P : Polytope n) (x : Point (n+1)) :
    x ∈ body (cone P) ↔ x=0 ∨ ∃ t : ℚ, ∃ p : Point n,
      0 < t ∧ t ≤ 1 ∧ p ∈ body P ∧ x=t • Fin.cons 1 p := by
  classical
  by_cases hP : P.Nonempty
  · have he : body (cone P)= ⋃ p ∈ body P, segment ℚ 0 (Fin.cons 1 p) := by
      simp only [body,cone,Finset.coe_insert,Finset.coe_image]
      rw [convexHull_insert (by obtain ⟨p,hp⟩ := hP; exact ⟨Fin.cons 1 p,⟨p,hp,rfl⟩⟩)]
      change convexJoin ℚ {0} (convexHull ℚ ((baseLayerMap n) '' (P : Set (Point n)))) = _
      rw [← (baseLayerMap n).image_convexHull,convexJoin_singleton_left]
      ext x
      simp only [Set.mem_iUnion,Set.mem_image]
      constructor
      · rintro ⟨q,⟨p,hp,rfl⟩,hx⟩; exact ⟨p,hp,hx⟩
      · rintro ⟨p,hp,hx⟩; exact ⟨Fin.cons 1 p,⟨p,hp,rfl⟩,hx⟩
    rw [he]
    simp only [Set.mem_iUnion,segment_eq_image,Set.mem_image,Set.mem_Icc]
    constructor
    · rintro ⟨p,hp,t,⟨ht0,ht1⟩,he⟩
      simp only [smul_zero,zero_add] at he
      by_cases ht : t=0
      · left; simpa [ht] using he.symm
      · right; exact ⟨t,p,lt_of_le_of_ne ht0 (Ne.symm ht),ht1,hp,he.symm⟩
    · rintro (rfl | ⟨t,p,ht0,ht1,hp,rfl⟩)
      · obtain ⟨p,hp⟩ := hP
        refine ⟨p,subset_convexHull ℚ (P : Set (Point n)) hp,0,⟨le_rfl,by decide⟩,?_⟩
        simp
      · exact ⟨p,hp,t,⟨ht0.le,ht1⟩,by simp⟩
  · have he : P=∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    simp [body,cone,convexHull_empty,convexHull_singleton]

/-- Cone over a dissection: include the common apex as a separate flat piece
so even empty index types and empty bases are handled correctly. -/
theorem cone_dissection {n : Nat} {ι : Type} [Fintype ι]
    (P : Polytope n) (pieces : ι → Polytope n) (hd : Dissection P pieces) :
    Dissection (cone P) (fun i : Option ι => i.elim {0} (fun j => cone (pieces j))) := by
  classical
  constructor
  · intro x
    rw [mem_body_cone]
    constructor
    · rintro (rfl | ⟨t,p,ht0,ht1,hp,rfl⟩)
      · exact ⟨none,by simp [body,convexHull_singleton]⟩
      · obtain ⟨i,hi⟩ := (hd.1 p).mp hp
        exact ⟨some i,(mem_body_cone _ _).mpr (Or.inr ⟨t,p,ht0,ht1,hi,rfl⟩)⟩
    · rintro ⟨i,hi⟩
      cases i with
      | none => left; simpa [body,convexHull_singleton] using hi
      | some i =>
        rcases (mem_body_cone _ _).mp hi with he | ⟨t,p,ht0,ht1,hp,he⟩
        · exact Or.inl he
        · exact Or.inr ⟨t,p,ht0,ht1,(hd.1 p).mpr ⟨i,hp⟩,he⟩
  · intro i j hij
    have hflat : Flat ({0} : Set (Point (n+1))) := by
      refine ⟨axis 0,0,?_,?_⟩
      · intro he; have h := congrFun he 0; simp [axis] at h
      · intro x hx; simpa using Set.mem_singleton_iff.mp hx ▸ (show dot (axis 0) 0=0 by simp [dot])
    cases i with
    | none =>
      obtain ⟨a,c,ha,hac⟩ := hflat
      refine ⟨a,c,ha,fun x hx => hac x ?_⟩
      simpa [body,convexHull_singleton] using hx.1
    | some i => cases j with
      | none =>
        obtain ⟨a,c,ha,hac⟩ := hflat
        refine ⟨a,c,ha,fun x hx => hac x ?_⟩
        simpa [body,convexHull_singleton] using hx.2
      | some j =>
        obtain ⟨a,c,ha,hac⟩ := hd.2 i j (by simpa using hij)
        refine ⟨Fin.cons (-c) a,0,?_,?_⟩
        · intro hz; apply ha; ext k; have h := congrFun hz k.succ; simpa using h
        · intro x hx
          rcases (mem_body_cone _ _).mp hx.1 with rfl | ⟨t,p,ht0,ht1,hp,rfl⟩
          · simp [dot]
          · rcases (mem_body_cone _ _).mp hx.2 with hz | ⟨u,q,hu0,hu1,hq,he⟩
            · have h := congrFun hz 0; simp at h; exact (ne_of_gt ht0 h).elim
            · have htu : t=u := by have h := congrFun he 0; simpa using h
              have hpq : p=q := by
                ext k
                have h := congrFun he k.succ
                simp only [Pi.smul_apply,smul_eq_mul,Fin.cons_succ,← htu] at h
                exact mul_left_cancel₀ (ne_of_gt ht0) h
              subst q
              have hc := hac p ⟨hp,hq⟩
              simp only [dot,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Pi.smul_apply,smul_eq_mul]
              rw [show (∑ i : Fin n, a i*(t*p i))=t*dot a p by simp [dot,Finset.mul_sum]; congr 1; ext i; ring,hc]
              ring

theorem cone_translated {n : Nat} (P : Polytope n) (b : Point n) :
    cone (translated P b)=transformed (cone P) (heightMatrix 1 b) := by
  classical
  have h0 : (heightMatrix (1 : Matrix (Fin n) (Fin n) ℚ) b).mulVec 0=0 := by simp
  have he (p : Point n) : (heightMatrix (1 : Matrix (Fin n) (Fin n) ℚ) b).mulVec (Fin.cons 1 p)=
      Fin.cons 1 (fun i => p i+b i) := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp [heightMatrix_mulVec_zero]
    · simp [heightMatrix_mulVec_succ,add_comm]
  simp only [cone,translated,transformed,Finset.image_insert,h0,Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro p hp
  exact (he p).symm

theorem cone_transformed {n : Nat} (P : Polytope n) (A : Matrix (Fin n) (Fin n) ℚ) :
    cone (transformed P A)=transformed (cone P) (heightMatrix A 0) := by
  classical
  have h0 : (heightMatrix A 0).mulVec 0=0 := by simp
  have he (p : Point n) : (heightMatrix A 0).mulVec (Fin.cons 1 p)=Fin.cons 1 (A.mulVec p) := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp [heightMatrix_mulVec_zero]
    · simp [heightMatrix_mulVec_succ]
  simp only [cone,transformed,Finset.image_insert,h0,Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro p hp
  exact (he p).symm

/-- Put the apex second in the ordered list, giving determinant -det(base). -/
def coneVertices {n : Nat} (p : RationalSimplex.Vertices n) : RationalSimplex.Vertices (n+1) :=
  Fin.cons (Fin.cons 1 (p 0)) (Fin.cons 0 (fun i => Fin.cons 1 (p i.succ)))

theorem cone_vertexSimplex {n : Nat} (p : RationalSimplex.Vertices n) :
    cone (vertexSimplex p)=vertexSimplex (coneVertices p) := by
  classical
  ext x
  simp only [cone,vertexSimplex,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (rfl | ⟨q,⟨i,rfl⟩,rfl⟩)
    · exact ⟨(0 : Fin (n+1)).succ,rfl⟩
    · cases i using Fin.cases with
      | zero => exact ⟨0,rfl⟩
      | succ i => exact ⟨i.succ.succ,rfl⟩
  · rintro ⟨i,rfl⟩
    cases i using Fin.cases with
    | zero => exact Or.inr ⟨p 0,⟨0,rfl⟩,rfl⟩
    | succ i => cases i using Fin.cases with
      | zero => exact Or.inl rfl
      | succ i => exact Or.inr ⟨p i.succ,⟨i.succ,rfl⟩,rfl⟩

theorem coneVertices_det {n : Nat} (p : RationalSimplex.Vertices n) :
    (RationalSimplex.edgeMatrix (coneVertices p)).det= -(RationalSimplex.edgeMatrix p).det := by
  have hrow : ∀ j : Fin (n+1), RationalSimplex.edgeMatrix (coneVertices p) 0 j =
      (Fin.cons (-1 : ℚ) (fun _ : Fin n => 0) : Point (n+1)) j := by
    intro j; cases j using Fin.cases <;> simp [RationalSimplex.edgeMatrix,coneVertices]
  have hminor : (RationalSimplex.edgeMatrix (coneVertices p)).submatrix Fin.succ (Fin.succAbove 0)=
      RationalSimplex.edgeMatrix p := by
    ext i j; simp [Matrix.submatrix,RationalSimplex.edgeMatrix,coneVertices]
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
  simp only [hrow,Fin.cons_zero,Fin.cons_succ,Fin.val_zero,pow_zero,one_mul,
    mul_zero,zero_mul,Finset.sum_const_zero,add_zero,hminor]
  ring

theorem cone_simplex_volume {n : Nat} (V : Axioms n) (W : Axioms (n+1))
    (p : RationalSimplex.Vertices n) :
    W.volume (cone (vertexSimplex p))=V.volume (vertexSimplex p)/((n+1:Nat):ℚ) := by
  rw [cone_vertexSimplex,vertexSimplex_volume_eq_abs,coneVertices_det,abs_neg,
    vertexSimplex_volume_eq_abs,Nat.factorial_succ,Nat.cast_mul]
  rw [div_div]
  congr 1
  ring

theorem volume_cone_dissection {n : Nat} {ι : Type} [Fintype ι]
    (V : Axioms (n+1)) (P : Polytope n) (pieces : ι → Polytope n)
    (hd : Dissection P pieces) :
    V.volume (cone P)=∑ i, V.volume (cone (pieces i)) := by
  rw [V.dissection _ _ (cone_dissection P pieces hd),Fintype.sum_option]
  have he : V.volume ({0} : Polytope (n+1))=0 := by
    apply volume_flat
    refine ⟨axis 0,0,?_,?_⟩
    · intro hz; have h := congrFun hz 0; simp [axis] at h
    · intro x hx
      have hx0 : x=0 := by simpa [body,convexHull_singleton] using hx
      subst x; simp [dot]
  change V.volume ({0} : Polytope (n+1)) + (∑ i, V.volume (cone (pieces i))) = _
  rw [he,zero_add]

/-- Exact cone volume for a supplied explicit simplicial dissection. -/
theorem cone_volume_of_simplex_dissection {n : Nat} {ι : Type} [Fintype ι]
    (V : Axioms n) (W : Axioms (n+1)) (P : Polytope n)
    (p : ι → RationalSimplex.Vertices n) (hd : Dissection P (fun i => vertexSimplex (p i))) :
    W.volume (cone P)=V.volume P/((n+1:Nat):ℚ) := by
  rw [volume_cone_dissection W P _ hd,V.dissection P _ hd]
  simp only [cone_simplex_volume V W,div_eq_mul_inv,Finset.sum_mul]

theorem cone_unit_cube_volume {n : Nat} (W : Axioms (n+1)) :
    W.volume (cone (cube n 1))=1/((n+1:Nat):ℚ) := by
  classical
  let V := prismAxioms W 1 (by decide)
  let p (σ : Equiv.Perm (Fin n)) := matrixVertices ((staircaseMatrix n).submatrix σ σ)
  have hd : Dissection (cube n 1) (fun σ => vertexSimplex (p σ)) := by
    simpa only [p,vertexSimplex_matrix,reindexed_staircase_eq_transformed]
      using cube_staircase_dissection n
  rw [cone_volume_of_simplex_dissection V W _ p hd,V.unit_cube]

/-- Rescaling cone volumes produces the existing base volume axioms.
Base translations are determinant-one shears in the ambient cone. -/
noncomputable def coneAxioms {n : Nat} (V : Axioms (n+1)) : Axioms n where
  volume := fun P => ((n+1:Nat):ℚ)*V.volume (cone P)
  extensional := by
    intro P Q he
    have hb : body (cone P)=body (cone Q) := by
      ext x; simp only [mem_body_cone,he]
    rw [V.extensional _ _ hb]
  translation := by
    intro P b
    rw [cone_translated,V.determinant_one _ _ (by rw [heightMatrix_det,Matrix.det_one])]
  determinant_one := by
    intro P A hA
    rw [cone_transformed,V.determinant_one _ _ (by rw [heightMatrix_det,hA])]
  dissection := by
    intro ι inst P pieces hd
    rw [volume_cone_dissection V _ _ hd,Finset.mul_sum]
  unit_cube := by
    rw [cone_unit_cube_volume]
    have hn : ((n+1:Nat):ℚ) ≠ 0 := by positivity
    exact mul_div_cancel₀ 1 hn

/-- Exact cone volume for every rational convex polytope, without requiring
callers to supply a triangulation. -/
theorem cone_volume {n : Nat} (V : Axioms n) (W : Axioms (n+1)) (P : Polytope n) :
    W.volume (cone P)=V.volume P/((n+1:Nat):ℚ) := by
  have he := volume_unique (coneAxioms W) V P
  change ((n+1:Nat):ℚ)*W.volume (cone P)=V.volume P at he
  have hn : ((n+1:Nat):ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hn).mpr
  rw [mul_comm,he]

/-- The ordinary cone lies in its cylinder when the base contains the origin. -/
theorem cone_subset_prism {n : Nat} (P : Polytope n) (hP : (0 : Point n) ∈ body P) :
    body (cone P) ⊆ body (prism P 1) := by
  intro x hx
  rw [body_prism _ _ (by decide)]
  rcases (mem_body_cone _ _).mp hx with rfl | ⟨t,p,ht0,ht1,hp,rfl⟩
  · exact ⟨by simp,by simp,by convert hP using 1; funext i; rfl⟩
  · have hs : t • p ∈ body P := by
      have he := (convex_convexHull ℚ (P : Set (Point n))) hP hp
        (sub_nonneg.mpr ht1) ht0.le (by ring : (1-t)+t=1)
      simpa only [body,smul_zero,zero_add] using he
    exact ⟨by simpa using ht0.le,by simpa using ht1,hs⟩

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.mem_body_cone
#print axioms ComputableAnalysis.RationalPolytopeVolume.cone_dissection
#print axioms ComputableAnalysis.RationalPolytopeVolume.cone_translated
#print axioms ComputableAnalysis.RationalPolytopeVolume.cone_transformed
#print axioms ComputableAnalysis.RationalPolytopeVolume.cone_vertexSimplex
#print axioms ComputableAnalysis.RationalPolytopeVolume.coneVertices_det
#print axioms ComputableAnalysis.RationalPolytopeVolume.cone_simplex_volume
#print axioms ComputableAnalysis.RationalPolytopeVolume.volume_cone_dissection
#print axioms ComputableAnalysis.RationalPolytopeVolume.cone_volume_of_simplex_dissection
#print axioms ComputableAnalysis.RationalPolytopeVolume.cone_unit_cube_volume
#print axioms ComputableAnalysis.RationalPolytopeVolume.cone_volume
#print axioms ComputableAnalysis.RationalPolytopeVolume.cone_subset_prism

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.mem_body_cone,
    `ComputableAnalysis.RationalPolytopeVolume.cone_dissection,
    `ComputableAnalysis.RationalPolytopeVolume.cone_translated,
    `ComputableAnalysis.RationalPolytopeVolume.cone_transformed,
    `ComputableAnalysis.RationalPolytopeVolume.cone_vertexSimplex,
    `ComputableAnalysis.RationalPolytopeVolume.coneVertices_det,
    `ComputableAnalysis.RationalPolytopeVolume.cone_simplex_volume,
    `ComputableAnalysis.RationalPolytopeVolume.volume_cone_dissection,
    `ComputableAnalysis.RationalPolytopeVolume.cone_volume_of_simplex_dissection,
    `ComputableAnalysis.RationalPolytopeVolume.cone_unit_cube_volume,
    `ComputableAnalysis.RationalPolytopeVolume.cone_volume,
    `ComputableAnalysis.RationalPolytopeVolume.cone_subset_prism]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
