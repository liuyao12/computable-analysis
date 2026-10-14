import ComputableAnalysis.ModularForms.CMFiniteAnnuli163
import ComputableAnalysis.ModularForms.UpperShellListSum

/-! A uniform executable inverse-power term on order elements. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163

def upperPointPower (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) (u : QuadraticOrder163) : ComplexRaw :=
  if hu : u≠zero then LocalODE.power (latticeInverse z hz u hu).val k else ComplexRaw.zero

theorem upperPointPower_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) (u : QuadraticOrder163) : (upperPointPower z hz k u).Valid := by
  unfold upperPointPower
  split
  · exact LocalODE.power_valid _ (latticeInverse z hz _ _).property k
  · exact ComplexRaw.ofQComplex_valid _

theorem upperPointPower_shellPoint (z : Scalar) (hz : InUpperHalfPlane z.val) (k r : Nat) (hr : 0<r) (i : Fin (8*r)) :
    upperPointPower z hz k (shellPoint r i)=upperShellTerm z hz r hr k i.val := by
  simp only [upperPointPower,upperShellTerm,dif_pos (shellPoint_nonzero r hr i),dif_pos i.isLt]

theorem upperShellPoints_term_list (z : Scalar) (hz : InUpperHalfPlane z.val) (k r : Nat) (hr : 0<r) :
    (shellPoints r).map (upperPointPower z hz k)=(List.range (8*r)).map (upperShellTerm z hz r hr k) := by
  simp only [shellPoints,List.map_map]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map,List.length_finRange] at h1
    simp only [List.getElem_map,List.getElem_finRange,List.getElem_range]
    exact upperPointPower_shellPoint z hz k r hr _

theorem upperShellSum_point_list_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (k r : Nat) (hr : 0<r) :
    (upperShellSum z hz r hr k).Equiv (LocalODE.sum ((shellPoints r).map (upperPointPower z hz k))) := by
  rw [upperShellPoints_term_list z hz k r hr]
  exact upperShellSum_list_equiv z hz r hr k

end ComputableAnalysis.ModularForms
