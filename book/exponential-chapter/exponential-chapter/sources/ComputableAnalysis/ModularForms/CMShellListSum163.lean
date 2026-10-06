import ComputableAnalysis.ModularForms.LatticeFiniteReindexing
import ComputableAnalysis.ModularForms.CMLatticeShellSum163

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
  | nil => change listValue bs hb=0+listValue bs hb; grind
  | cons a as ih =>
    have hav := ha a (by simp)
    have hat : ∀ z ∈ as, z.Valid := by intro z hz; exact ha z (by simp [hz])
    change ComplexRawQuotient.ofRaw a hav+listValue (as++bs) (by intro z hz; rcases List.mem_append.mp hz with h|h; exact hat z h; exact hb z h) =
      (ComplexRawQuotient.ofRaw a hav+listValue as hat)+listValue bs hb
    rw [ih hat]
    grind

namespace QuadraticOrder163

private theorem termList_valid (r : Nat) (hr : 0<r) (k n : Nat) :
    ∀ z ∈ (List.range n).map (shellTerm r hr k), z.Valid := by
  intro z hz
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
  exact shellTerm_valid r hr k i

private theorem shellPrefix_listValue (r : Nat) (hr : 0<r) (k n : Nat) :
    ComplexRawQuotient.ofRaw (shellPrefix r hr k n) (shellPrefix_valid r hr k n)=
      listValue ((List.range n).map (shellTerm r hr k)) (termList_valid r hr k n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : (List.range (n+1)).map (shellTerm r hr k)=
        (List.range n).map (shellTerm r hr k)++[shellTerm r hr k n] := by
      rw [List.range_succ,List.map_append]
      rfl
    change ComplexRawQuotient.ofRaw (shellPrefix r hr k n) (shellPrefix_valid r hr k n)+
      ComplexRawQuotient.ofRaw (shellTerm r hr k n) (shellTerm_valid r hr k n) = _
    rw [ih]
    have hs := listValue_append ((List.range n).map (shellTerm r hr k))
      [shellTerm r hr k n] (termList_valid r hr k n)
      (by intro z hz; simp only [List.mem_singleton] at hz; subst z; exact shellTerm_valid r hr k n)
    simp only [he]
    rw [hs]
    change _ = _+(ComplexRawQuotient.ofRaw (shellTerm r hr k n) (shellTerm_valid r hr k n)+0)
    grind

/-- The actual recursive shell sum equals the executable sum of its explicit
finite list of inverse-power terms. -/
theorem shellSum_list_equiv (r : Nat) (hr : 0<r) (k : Nat) :
    (shellSum r hr k).Equiv
      (LocalODE.sum ((List.range (8*r)).map (shellTerm r hr k))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := shellSum_valid r hr k)
    (hright := LocalODE.sum_valid _ (termList_valid r hr k (8*r)))
  exact shellPrefix_listValue r hr k (8*r)

/-- Any verified permutation of the shell indices computes the same shell value. -/
theorem shellSum_reindex (r : Nat) (hr : 0<r) (k : Nat) (is : List Nat)
    (hi : (List.range (8*r)).Perm is) :
    (shellSum r hr k).Equiv (LocalODE.sum (is.map (shellTerm r hr k))) := by
  have hv : (LocalODE.sum (is.map (shellTerm r hr k))).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
    exact shellTerm_valid r hr k i
  exact ComplexRaw.equiv_trans (shellSum_valid r hr k)
    (LocalODE.sum_valid _ (termList_valid r hr k (8*r))) hv
    (shellSum_list_equiv r hr k)
    (representedSum_reindex _ (shellTerm_valid r hr k) hi)

end QuadraticOrder163
end ComputableAnalysis.ModularForms
