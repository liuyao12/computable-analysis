import ComputableAnalysis.ModularForms.CMFiniteAnnuli163
import ComputableAnalysis.ModularForms.CMShellListSum163

/-! A uniform executable inverse-power term on order elements. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert

def pointPower (k : Nat) (u : QuadraticOrder163) : ComplexRaw :=
  if hu : u≠zero then LocalODE.power (complexInverse u hu).val k else ComplexRaw.zero

theorem pointPower_valid (k : Nat) (u : QuadraticOrder163) : (pointPower k u).Valid := by
  unfold pointPower
  split
  · exact LocalODE.power_valid _ (complexInverse _ _).property k
  · exact ComplexRaw.ofQComplex_valid _

theorem pointPower_shellPoint (k r : Nat) (hr : 0<r) (i : Fin (8*r)) :
    pointPower k (shellPoint r i)=shellTerm r hr k i.val := by
  simp only [pointPower,shellTerm,dif_pos (shellPoint_nonzero r hr i),dif_pos i.isLt]

theorem shellPoints_term_list (k r : Nat) (hr : 0<r) :
    (shellPoints r).map (pointPower k)=(List.range (8*r)).map (shellTerm r hr k) := by
  simp only [shellPoints,List.map_map]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map,List.length_finRange] at h1
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range]
    exact pointPower_shellPoint k r hr _

theorem shellSum_point_list_equiv (k r : Nat) (hr : 0<r) :
    (shellSum r hr k).Equiv (LocalODE.sum ((shellPoints r).map (pointPower k))) := by
  rw [shellPoints_term_list k r hr]
  exact shellSum_list_equiv r hr k

theorem pointPower_conjugate (k : Nat) (u : QuadraticOrder163) :
    (ComplexRaw.conj (pointPower k u)).Equiv (pointPower k (conjugate u)) := by
  by_cases hu : u≠zero
  · simp only [pointPower,dif_pos hu,dif_pos (conjugate_nonzero u hu)]
    exact complexInverse_power_conjugate u hu k
  · have he : u=zero := by
      by_cases hz : u=zero
      · exact hz
      · exact False.elim (hu hz)
    subst u
    simp only [pointPower,conjugate,zero]
    intro n
    apply (ComplexRaw.compareAt_overlap_iff _ _ n n).mpr
    change (⟨(0:Rat),0⟩ : QComplex) ≤ ⟨0,0⟩ ∧ (⟨(0:Rat),0⟩ : QComplex) ≤ ⟨0,0⟩
    decide +kernel

end ComputableAnalysis.ModularForms.QuadraticOrder163
