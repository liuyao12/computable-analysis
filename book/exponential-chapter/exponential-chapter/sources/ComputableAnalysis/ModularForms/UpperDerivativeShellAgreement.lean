import ComputableAnalysis.ModularForms.LatticeFiniteReindexing
import ComputableAnalysis.ModularForms.UpperFiniteDerivative

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


private theorem derivativeTermList_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k n : Nat) :
    ∀ zz ∈ (List.range n).map (derivativeShellTerm z hz r hr k), zz.Valid := by
  intro zz hzz
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hzz
  exact derivativeShellTerm_valid z hz r hr k i

private theorem derivativeShellPrefix_listValue (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k n : Nat) :
    ComplexRawQuotient.ofRaw (derivativeShellPrefix z hz r hr k n) (derivativeShellPrefix_valid z hz r hr k n)=
      listValue ((List.range n).map (derivativeShellTerm z hz r hr k)) (derivativeTermList_valid z hz r hr k n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : (List.range (n+1)).map (derivativeShellTerm z hz r hr k)=
        (List.range n).map (derivativeShellTerm z hz r hr k)++[derivativeShellTerm z hz r hr k n] := by
      rw [List.range_succ,List.map_append]
      rfl
    change ComplexRawQuotient.ofRaw (derivativeShellPrefix z hz r hr k n) (derivativeShellPrefix_valid z hz r hr k n)+
      ComplexRawQuotient.ofRaw (derivativeShellTerm z hz r hr k n) (derivativeShellTerm_valid z hz r hr k n) = _
    rw [ih]
    have hs := listValue_append ((List.range n).map (derivativeShellTerm z hz r hr k))
      [derivativeShellTerm z hz r hr k n] (derivativeTermList_valid z hz r hr k n)
      (by intro zz hzz; simp only [List.mem_singleton] at hzz; subst zz; exact derivativeShellTerm_valid z hz r hr k n)
    simp only [he]
    rw [hs]
    change _ = _+(ComplexRawQuotient.ofRaw (derivativeShellTerm z hz r hr k n) (derivativeShellTerm_valid z hz r hr k n)+0)
    grind only

/-- The actual recursive shell sum equals the executable sum of its explicit
finite list of derivative terms. -/
theorem derivativeShellSum_list_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) :
    (derivativeShellSum z hz r hr k).Equiv
      (LocalODE.sum ((List.range (8*r)).map (derivativeShellTerm z hz r hr k))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := derivativeShellPrefix_valid z hz r hr k (8*r))
    (hright := LocalODE.sum_valid _ (derivativeTermList_valid z hz r hr k (8*r)))
  exact derivativeShellPrefix_listValue z hz r hr k (8*r)

/-- Any verified permutation of the shell indices computes the same shell value. -/
theorem derivativeShellSum_reindex (z : Scalar) (hz : InUpperHalfPlane z.val) (r : Nat) (hr : 0<r) (k : Nat) (is : List Nat)
    (hi : (List.range (8*r)).Perm is) :
    (derivativeShellSum z hz r hr k).Equiv (LocalODE.sum (is.map (derivativeShellTerm z hz r hr k))) := by
  have hv : (LocalODE.sum (is.map (derivativeShellTerm z hz r hr k))).Valid := by
    apply LocalODE.sum_valid
    intro zz hzz
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hzz
    exact derivativeShellTerm_valid z hz r hr k i
  exact ComplexRaw.equiv_trans (derivativeShellPrefix_valid z hz r hr k (8*r))
    (LocalODE.sum_valid _ (derivativeTermList_valid z hz r hr k (8*r))) hv
    (derivativeShellSum_list_equiv z hz r hr k)
    (representedSum_reindex _ (derivativeShellTerm_valid z hz r hr k) hi)

theorem derivativeShellPoints_term_list (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k r : Nat) (hr : 0<r) :
    (QuadraticOrder163.shellPoints r).map (upperPointDerivative z hz k)=
      (List.range (8*r)).map (derivativeShellTerm z hz r hr k) := by
  simp only [QuadraticOrder163.shellPoints,List.map_map]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map,List.length_finRange] at h1
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range]
    exact (derivativeShellTerm_point z hz r hr k i h1).symm

theorem derivativeShellSum_finiteMap_derivative (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k r : Nat) (hr : 0<r) :
    (derivativeShellSum z hz r hr k).Equiv
      ((upperFiniteMap_holomorphic k (QuadraticOrder163.shellPoints r)).derivative z hz).val := by
  rw [upperFiniteMap_derivative,derivativeShellPoints_term_list z hz k r hr]
  exact derivativeShellSum_list_equiv z hz r hr k

/-- The regional shell estimate applies to the actual holomorphic derivative. -/
theorem upperFiniteShell_derivative_region_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (r : Nat) (hr : 0<r) (k : Nat) :
    FunctionTheory.Small
      ((upperFiniteMap_holomorphic k (QuadraticOrder163.shellPoints r)).derivative z hz).val
      (((8*r:Nat):Rat)*(2*((k:Rat)*(r:Rat))*
        (2*(latticeRegionReciprocalConstant R H eta/(r:Rat)))^(k+1))) := by
  exact FunctionTheory.Small.congr (derivativeShellPrefix_valid z hz r hr k (8*r))
    ((upperFiniteMap_holomorphic k (QuadraticOrder163.shellPoints r)).derivative z hz).property
    (derivativeShellSum_finiteMap_derivative z hz k r hr)
    (derivativeShellSum_region_bound z hz R H eta N hR hH heta hregion hheight r hr k)

end ComputableAnalysis.ModularForms
