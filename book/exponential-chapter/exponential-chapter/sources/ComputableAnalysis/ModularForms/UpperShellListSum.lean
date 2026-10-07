import ComputableAnalysis.ModularForms.LatticeFiniteReindexing
import ComputableAnalysis.ModularForms.UpperLatticeShells

/-! Agreement between recursive shell sums and explicit finite term lists. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

private def listValue (zs : List ComplexRaw) (hz : ∀ z ∈ zs, z.Valid) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (LocalODE.sum zs) (LocalODE.sum_valid zs hz)

private theorem listValue_append (as bs : List ComplexRaw)
    (ha : ∀ z ∈ as, z.Valid) (hb : ∀ z ∈ bs, z.Valid) :
    listValue (as++bs) (by intro z hz; rcases List.mem_append.mp hz with h|h; exact ha z h; exact hb z h)=
      listValue as ha+listValue bs hb := by
  induction as with
  | nil => exact (ComplexRawQuotient.zero_add _).symm
  | cons a as ih =>
    have hav := ha a (by simp)
    have hat : ∀ z ∈ as, z.Valid := by intro z hz; exact ha z (by simp [hz])
    change ComplexRawQuotient.ofRaw a hav+listValue (as++bs) (by intro z hz; rcases List.mem_append.mp hz with h|h; exact hat z h; exact hb z h) =
      (ComplexRawQuotient.ofRaw a hav+listValue as hat)+listValue bs hb
    rw [ih hat]
    exact (ComplexRawQuotient.add_assoc _ _ _).symm


private theorem upperTermList_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k n : Nat) :
    ∀ zz ∈ (List.range n).map (upperShellTerm z hz r hr k), zz.Valid := by
  intro zz hzz
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hzz
  exact upperShellTerm_valid z hz r hr k i

private theorem upperShellPrefix_listValue (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k n : Nat) :
    ComplexRawQuotient.ofRaw (upperShellPrefix z hz r hr k n) (upperShellPrefix_valid z hz r hr k n)=
      listValue ((List.range n).map (upperShellTerm z hz r hr k)) (upperTermList_valid z hz r hr k n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : (List.range (n+1)).map (upperShellTerm z hz r hr k)=
        (List.range n).map (upperShellTerm z hz r hr k)++[upperShellTerm z hz r hr k n] := by
      rw [List.range_succ,List.map_append]
      rfl
    change ComplexRawQuotient.ofRaw (upperShellPrefix z hz r hr k n) (upperShellPrefix_valid z hz r hr k n)+
      ComplexRawQuotient.ofRaw (upperShellTerm z hz r hr k n) (upperShellTerm_valid z hz r hr k n) = _
    rw [ih]
    have hs := listValue_append ((List.range n).map (upperShellTerm z hz r hr k))
      [upperShellTerm z hz r hr k n] (upperTermList_valid z hz r hr k n)
      (by intro zz hzz; simp only [List.mem_singleton] at hzz; subst zz; exact upperShellTerm_valid z hz r hr k n)
    simp only [he]
    rw [hs]
    change _ = _+(ComplexRawQuotient.ofRaw (upperShellTerm z hz r hr k n) (upperShellTerm_valid z hz r hr k n)+0)
    grind only

/-- The actual recursive shell sum equals the executable sum of its explicit
finite list of inverse-power terms. -/
theorem upperShellSum_list_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) :
    (upperShellSum z hz r hr k).Equiv
      (LocalODE.sum ((List.range (8*r)).map (upperShellTerm z hz r hr k))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := upperShellSum_valid z hz r hr k)
    (hright := LocalODE.sum_valid _ (upperTermList_valid z hz r hr k (8*r)))
  exact upperShellPrefix_listValue z hz r hr k (8*r)

/-- Any verified permutation of the shell indices computes the same shell value. -/
theorem upperShellSum_reindex (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) (is : List Nat)
    (hi : (List.range (8*r)).Perm is) :
    (upperShellSum z hz r hr k).Equiv (LocalODE.sum (is.map (upperShellTerm z hz r hr k))) := by
  have hv : (LocalODE.sum (is.map (upperShellTerm z hz r hr k))).Valid := by
    apply LocalODE.sum_valid
    intro zz hzz
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hzz
    exact upperShellTerm_valid z hz r hr k i
  exact ComplexRaw.equiv_trans (upperShellSum_valid z hz r hr k)
    (LocalODE.sum_valid _ (upperTermList_valid z hz r hr k (8*r))) hv
    (upperShellSum_list_equiv z hz r hr k)
    (representedSum_reindex _ (upperShellTerm_valid z hz r hr k) hi)

end ComputableAnalysis.ModularForms
