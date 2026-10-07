import ComputableAnalysis.ModularForms.LatticeRectangleRows
import ComputableAnalysis.ModularForms.SymmetricLatticeShift
import ComputableAnalysis.ModularForms.RepresentedSumAppend

/-! Agreement of increasing and symmetric finite integer-coordinate sums. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

def symmetricLatticeCoordinates : Nat → List Int
  | 0 => [0]
  | N+1 => symmetricLatticeCoordinates N++[-((N+1:Nat):Int),((N+1:Nat):Int)]

theorem mem_symmetricLatticeCoordinates (x : Int) (N : Nat) :
    x ∈ symmetricLatticeCoordinates N ↔ -(N:Int)≤x ∧ x≤(N:Int) := by
  induction N with
  | zero => simp only [symmetricLatticeCoordinates,List.mem_singleton]; omega
  | succ N ih =>
    simp only [symmetricLatticeCoordinates,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,ih]
    omega

theorem symmetricLatticeCoordinates_nodup (N : Nat) :
    (symmetricLatticeCoordinates N).Nodup := by
  induction N with
  | zero => simp [symmetricLatticeCoordinates,List.nodup_cons]
  | succ N ih =>
    apply List.nodup_append.mpr
    refine ⟨ih,?_,?_⟩
    · apply List.nodup_cons.mpr
      constructor
      · intro h
        have he := List.mem_singleton.mp h
        omega
      · simp [List.nodup_cons]
    · intro x hx y hy he
      have hb := (mem_symmetricLatticeCoordinates x N).mp hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      omega

theorem latticeCoordinates_symmetric_perm (N : Nat) :
    (latticeCoordinates N).Perm (symmetricLatticeCoordinates N) := by
  apply (List.perm_ext_iff_of_nodup (latticeCoordinates_nodup N)
    (symmetricLatticeCoordinates_nodup N)).mpr
  intro x
  rw [mem_latticeCoordinates,mem_symmetricLatticeCoordinates]

end ComputableAnalysis.ModularForms.QuadraticOrder163

namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert QuadraticOrder163

private theorem sumMap_valid (f : Int → ComplexRaw) (hf : ∀ x, (f x).Valid)
    (xs : List Int) : (LocalODE.sum (xs.map f)).Valid := by
  apply LocalODE.sum_valid
  intro z hz
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
  exact hf x

private def sumClass (f : Int → ComplexRaw) (hf : ∀ x, (f x).Valid)
    (xs : List Int) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (LocalODE.sum (xs.map f)) (sumMap_valid f hf xs)

private theorem sumClass_append (f : Int → ComplexRaw) (hf : ∀ x, (f x).Valid)
    (xs ys : List Int) : sumClass f hf (xs++ys)=sumClass f hf xs+sumClass f hf ys := by
  have h := representedSum_append (xs.map f) (ys.map f)
    (by intro z hz; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz; exact hf x)
    (by intro z hz; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz; exact hf x)
  simp only [← List.map_append] at h
  exact ComplexRawQuotient.ofRaw_eq_ofRaw h

private theorem sumClass_symmetric (f : Int → ComplexRaw) (hf : ∀ x, (f x).Valid)
    (N : Nat) : sumClass f hf (symmetricLatticeCoordinates N)=
      symmetricLatticeSum (fun x => ComplexRawQuotient.ofRaw (f x) (hf x)) N := by
  induction N with
  | zero =>
    change ComplexRawQuotient.ofRaw (f 0) (hf 0)+0=ComplexRawQuotient.ofRaw (f 0) (hf 0)
    exact ComplexRawQuotient.add_zero _
  | succ N ih =>
    rw [symmetricLatticeCoordinates,sumClass_append,ih]
    change symmetricLatticeSum (fun x => ComplexRawQuotient.ofRaw (f x) (hf x)) N+
      (ComplexRawQuotient.ofRaw (f (-((N+1:Nat):Int))) (hf _)+
        (ComplexRawQuotient.ofRaw (f ((N+1:Nat):Int)) (hf _)+0))=_
    simp only [symmetricLatticeSum.eq_2]
    grind only

/-- Increasing finite coordinate sums agree with the symmetric prefix algebra. -/
theorem representedSum_latticeCoordinates (f : Int → ComplexRaw)
    (hf : ∀ x, (f x).Valid) (N : Nat) :
    ComplexRawQuotient.ofRaw (LocalODE.sum ((latticeCoordinates N).map f))
      (sumMap_valid f hf (latticeCoordinates N))=
      symmetricLatticeSum (fun x => ComplexRawQuotient.ofRaw (f x) (hf x)) N := by
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := sumMap_valid f hf (latticeCoordinates N))
    (hright := sumMap_valid f hf (symmetricLatticeCoordinates N))
    (representedSum_reindex f hf (latticeCoordinates_symmetric_perm N))
  exact h.trans (sumClass_symmetric f hf N)

end ComputableAnalysis.ModularForms
