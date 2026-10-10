import RationalPrismVolume

namespace ComputableAnalysis.RationalPolytopeVolume
open RationalConvexBodies
set_option maxHeartbeats 2000000

private def joinBlocks (n m : Nat) : (Point n × Point m) →ₗ[ℚ] Point (n+m) where
  toFun := fun xy => Fin.append xy.1 xy.2
  map_add' := by intro a b; ext i; refine Fin.addCases (fun j => by simp) (fun j => by simp) i
  map_smul' := by intro a b; ext i; refine Fin.addCases (fun j => by simp) (fun j => by simp) i

noncomputable def productPoly {n m : Nat} (P : Polytope n) (Q : Polytope m) : Polytope (n+m) := by
  classical
  exact (P ×ˢ Q).image (fun xy => Fin.append xy.1 xy.2)

def leftCoords {n m : Nat} (x : Point (n+m)) : Point n := fun i => x (i.castAdd m)
def rightCoords {n m : Nat} (x : Point (n+m)) : Point m := fun i => x (i.natAdd n)

@[simp] theorem leftCoords_append {n m : Nat} (p : Point n) (q : Point m) :
    leftCoords (Fin.append p q)=p := by
  funext i; simp [leftCoords]

@[simp] theorem rightCoords_append {n m : Nat} (p : Point n) (q : Point m) :
    rightCoords (Fin.append p q)=q := by
  funext i; simp [rightCoords]

theorem body_productPoly {n m : Nat} (P : Polytope n) (Q : Polytope m) :
    body (productPoly P Q) = {x | leftCoords x ∈ body P ∧ rightCoords x ∈ body Q} := by
  classical
  have hp : body (productPoly P Q)=(joinBlocks n m) '' (body P ×ˢ body Q) := by
    unfold body productPoly
    rw [Finset.coe_image,Finset.coe_product]
    change convexHull ℚ ((joinBlocks n m) '' ((P : Set (Point n)) ×ˢ (Q : Set (Point m)))) = _
    rw [← (joinBlocks n m).image_convexHull,convexHull_prod]
  rw [hp]
  ext x
  constructor
  · rintro ⟨⟨p,q⟩,⟨hp,hq⟩,rfl⟩
    change leftCoords (Fin.append p q) ∈ body P ∧ rightCoords (Fin.append p q) ∈ body Q
    rw [leftCoords_append,rightCoords_append]
    exact ⟨hp,hq⟩
  · rintro ⟨hp,hq⟩
    refine ⟨(leftCoords x,rightCoords x),⟨hp,hq⟩,?_⟩
    ext i; refine Fin.addCases (fun j => by simp [joinBlocks,leftCoords])
      (fun j => by simp [joinBlocks,rightCoords]) i

def blockMatrix {n m : Nat} (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin m) (Fin m) ℚ) :
    Matrix (Fin (n+m)) (Fin (n+m)) ℚ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

theorem blockMatrix_det {n m : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (B : Matrix (Fin m) (Fin m) ℚ) : (blockMatrix A B).det=A.det*B.det := by
  rw [blockMatrix,Matrix.det_reindex_self,Matrix.det_fromBlocks_zero₂₁]

theorem blockMatrix_mulVec {n m : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (B : Matrix (Fin m) (Fin m) ℚ) (p : Point n) (q : Point m) :
    (blockMatrix A B).mulVec (Fin.append p q)=Fin.append (A.mulVec p) (B.mulVec q) := by
  ext i
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_add]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [blockMatrix,Matrix.reindex_apply,Matrix.fromBlocks,Matrix.mulVec,dotProduct]
  · simp [blockMatrix,Matrix.reindex_apply,Matrix.fromBlocks,Matrix.mulVec,dotProduct]

theorem productPoly_transformed {n m : Nat} (P : Polytope n) (Q : Polytope m)
    (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin m) (Fin m) ℚ) :
    productPoly (transformed P A) (transformed Q B)=transformed (productPoly P Q) (blockMatrix A B) := by
  classical
  ext x
  simp only [productPoly,transformed,Finset.mem_image,Finset.mem_product]
  constructor
  · rintro ⟨⟨p,q⟩,⟨⟨u,hu,rfl⟩,⟨v,hv,rfl⟩⟩,rfl⟩
    exact ⟨Fin.append u v,⟨(u,v),⟨hu,hv⟩,rfl⟩,blockMatrix_mulVec A B u v⟩
  · rintro ⟨y,⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩,rfl⟩
    exact ⟨(A.mulVec u,B.mulVec v),⟨⟨u,hu,rfl⟩,⟨v,hv,rfl⟩⟩,(blockMatrix_mulVec A B u v).symm⟩

theorem productPoly_translated {n m : Nat} (P : Polytope n) (Q : Polytope m)
    (a : Point n) (b : Point m) :
    productPoly (translated P a) (translated Q b)=translated (productPoly P Q) (Fin.append a b) := by
  classical
  ext x
  simp only [productPoly,translated,Finset.mem_image,Finset.mem_product]
  constructor
  · rintro ⟨⟨p,q⟩,⟨⟨u,hu,rfl⟩,⟨v,hv,rfl⟩⟩,rfl⟩
    refine ⟨Fin.append u v,⟨(u,v),⟨hu,hv⟩,rfl⟩,?_⟩
    ext i; refine Fin.addCases (fun j => by simp) (fun j => by simp) i
  · rintro ⟨y,⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩,rfl⟩
    refine ⟨(fun i => u i+a i,fun i => v i+b i),⟨⟨u,hu,rfl⟩,⟨v,hv,rfl⟩⟩,?_⟩
    ext i; refine Fin.addCases (fun j => by simp) (fun j => by simp) i

/-- Product dissections use exactly the already-proved flat-overlap criterion. -/
theorem productPoly_dissection_left {n m : Nat} {ι : Type} [Fintype ι]
    (P : Polytope n) (Q : Polytope m) (pieces : ι → Polytope n) (hd : Dissection P pieces) :
    Dissection (productPoly P Q) (fun i => productPoly (pieces i) Q) := by
  constructor
  · intro x
    simp only [body_productPoly,Set.mem_ofPred_eq]
    rw [hd.1]
    constructor
    · rintro ⟨⟨i,hi⟩,hq⟩; exact ⟨i,hi,hq⟩
    · rintro ⟨i,hi,hq⟩; exact ⟨⟨i,hi⟩,hq⟩
  · intro i j hij
    obtain ⟨a,c,ha,hac⟩ := hd.2 i j hij
    refine ⟨Fin.append a 0,c,?_,?_⟩
    · intro hz; apply ha; ext k
      have h := congrFun hz (k.castAdd m); simpa using h
    · intro x hx
      rw [body_productPoly,body_productPoly] at hx
      have h := hac (leftCoords x) ⟨hx.1.1,hx.2.1⟩
      simpa [dot,Fin.sum_univ_add,leftCoords] using h

theorem productPoly_dissection_right {n m : Nat} {ι : Type} [Fintype ι]
    (P : Polytope n) (Q : Polytope m) (pieces : ι → Polytope m) (hd : Dissection Q pieces) :
    Dissection (productPoly P Q) (fun i => productPoly P (pieces i)) := by
  constructor
  · intro x
    simp only [body_productPoly,Set.mem_ofPred_eq]
    rw [hd.1]
    constructor
    · rintro ⟨hp,⟨i,hi⟩⟩; exact ⟨i,hp,hi⟩
    · rintro ⟨i,hp,hi⟩; exact ⟨hp,i,hi⟩
  · intro i j hij
    obtain ⟨a,c,ha,hac⟩ := hd.2 i j hij
    refine ⟨Fin.append 0 a,c,?_,?_⟩
    · intro hz; apply ha; ext k
      have h := congrFun hz (k.natAdd n); simpa using h
    · intro x hx
      rw [body_productPoly,body_productPoly] at hx
      have h := hac (rightCoords x) ⟨hx.1.2,hx.2.2⟩
      simpa [dot,Fin.sum_univ_add,rightCoords] using h

theorem productPoly_cubes {n m : Nat} : body (productPoly (cube n 1) (cube m 1))=body (cube (n+m) 1) := by
  ext x
  rw [body_productPoly,mem_body_cube _ _ (by decide)]
  simp only [Set.mem_ofPred_eq,mem_body_cube n 1 (by decide),mem_body_cube m 1 (by decide)]
  constructor
  · rintro ⟨hp,hq⟩ i
    refine Fin.addCases (fun j => hp j) (fun j => hq j) i
  · intro h
    exact ⟨fun i => h (i.castAdd m),fun i => h (i.natAdd n)⟩

private theorem transformed_one_eq {n : Nat} (P : Polytope n) : transformed P 1=P := by
  classical
  have he : (1 : Matrix (Fin n) (Fin n) ℚ).mulVec = id := by
    funext x; simp
  simp only [transformed,he,Finset.image_id]

private theorem translated_zero_eq {n : Nat} (P : Polytope n) : translated P 0=P := by
  classical
  simp [translated]

/-- Tensoring with a unit cube satisfies the base volume axioms. -/
noncomputable def cubeProductAxioms {n m : Nat} (W : Axioms (n+m)) : Axioms n where
  volume := fun P => W.volume (productPoly P (cube m 1))
  extensional := by
    intro P Q he
    apply W.extensional
    rw [body_productPoly,body_productPoly,he]
  translation := by
    intro P a
    have ht := productPoly_translated P (cube m 1) a 0
    rw [translated_zero_eq] at ht
    rw [ht,W.translation]
  determinant_one := by
    intro P A hA
    have ht := productPoly_transformed P (cube m 1) A 1
    rw [transformed_one_eq] at ht
    rw [ht,W.determinant_one _ _ (by rw [blockMatrix_det,hA,Matrix.det_one,one_mul])]
  dissection := by
    intro ι inst P pieces hd
    exact W.dissection _ _ (productPoly_dissection_left _ _ _ hd)
  unit_cube := by
    rw [W.extensional _ _ productPoly_cubes,W.unit_cube]

theorem productPoly_cube_volume {n m : Nat} (V : Axioms n) (W : Axioms (n+m)) (P : Polytope n) :
    W.volume (productPoly P (cube m 1))=V.volume P :=
  volume_unique (cubeProductAxioms W) V P

/-- A normalized product functional, adding a positive unit contribution so
no assumption that the fixed polytope has positive volume is needed. -/
noncomputable def productRightAxioms {n m : Nat} (V : Axioms n) (U : Axioms m)
    (W : Axioms (n+m)) (P : Polytope n) : Axioms m where
  volume := fun Q => (W.volume (productPoly P Q)+U.volume Q)/(V.volume P+1)
  extensional := by
    intro Q R he
    have hp : body (productPoly P Q)=body (productPoly P R) := by
      rw [body_productPoly,body_productPoly,he]
    rw [W.extensional _ _ hp,U.extensional _ _ he]
  translation := by
    intro Q b
    have ht := productPoly_translated P Q 0 b
    rw [translated_zero_eq] at ht
    rw [ht,W.translation,U.translation]
  determinant_one := by
    intro Q B hB
    have ht := productPoly_transformed P Q 1 B
    rw [transformed_one_eq] at ht
    rw [ht,W.determinant_one _ _ (by rw [blockMatrix_det,Matrix.det_one,hB,one_mul]),
      U.determinant_one _ _ hB]
  dissection := by
    intro ι inst Q pieces hd
    rw [W.dissection _ _ (productPoly_dissection_right _ _ _ hd),U.dissection _ _ hd,
      ← Finset.sum_add_distrib]
    simp only [div_eq_mul_inv,Finset.sum_mul]
  unit_cube := by
    rw [productPoly_cube_volume V W,U.unit_cube]
    have hn := volume_nonneg V P
    have hz : V.volume P+1 ≠ 0 := by linarith
    exact div_self hz

/-- Product volume for arbitrary rational convex polytopes follows from the
original axioms, including zero-volume factors. -/
theorem productPoly_volume {n m : Nat} (V : Axioms n) (U : Axioms m) (W : Axioms (n+m))
    (P : Polytope n) (Q : Polytope m) :
    W.volume (productPoly P Q)=V.volume P*U.volume Q := by
  have he := volume_unique (productRightAxioms V U W P) U Q
  change (W.volume (productPoly P Q)+U.volume Q)/(V.volume P+1)=U.volume Q at he
  have hn := volume_nonneg V P
  have hz : V.volume P+1 ≠ 0 := by linarith
  have hmul := (div_eq_iff hz).mp he
  nlinarith

end ComputableAnalysis.RationalPolytopeVolume

-- ARCHIMEDES AUDIT
#print axioms ComputableAnalysis.RationalPolytopeVolume.body_productPoly
#print axioms ComputableAnalysis.RationalPolytopeVolume.blockMatrix_det
#print axioms ComputableAnalysis.RationalPolytopeVolume.blockMatrix_mulVec
#print axioms ComputableAnalysis.RationalPolytopeVolume.productPoly_transformed
#print axioms ComputableAnalysis.RationalPolytopeVolume.productPoly_translated
#print axioms ComputableAnalysis.RationalPolytopeVolume.productPoly_dissection_left
#print axioms ComputableAnalysis.RationalPolytopeVolume.productPoly_dissection_right
#print axioms ComputableAnalysis.RationalPolytopeVolume.productPoly_cubes
#print axioms ComputableAnalysis.RationalPolytopeVolume.productPoly_cube_volume
#print axioms ComputableAnalysis.RationalPolytopeVolume.productPoly_volume

open Lean
run_cmd do
  let names := [`ComputableAnalysis.RationalPolytopeVolume.body_productPoly,
    `ComputableAnalysis.RationalPolytopeVolume.blockMatrix_det,
    `ComputableAnalysis.RationalPolytopeVolume.blockMatrix_mulVec,
    `ComputableAnalysis.RationalPolytopeVolume.productPoly_transformed,
    `ComputableAnalysis.RationalPolytopeVolume.productPoly_translated,
    `ComputableAnalysis.RationalPolytopeVolume.productPoly_dissection_left,
    `ComputableAnalysis.RationalPolytopeVolume.productPoly_dissection_right,
    `ComputableAnalysis.RationalPolytopeVolume.productPoly_cubes,
    `ComputableAnalysis.RationalPolytopeVolume.productPoly_cube_volume,
    `ComputableAnalysis.RationalPolytopeVolume.productPoly_volume]
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env names
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: {names.length} checked rational geometry endpoints; {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
