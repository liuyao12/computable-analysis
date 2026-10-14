import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeJoined

/-! Second differentiability of the actual canonical lattice sum on the full upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedCanonicalFirstDerivativeMap : DomainFunctions.Map where
  domain := pairedPartialFractionMap.domain
  eval := pairedPartialFractionDerivative
  domain_congr := pairedPartialFractionMap.domain_congr
  eval_congr := pairedPartialFractionDerivative_congr

def pairedSecondDerivativeCutoff (a : Scalar) : Nat := pairedInternalBound a+2

theorem pairedSecondDerivativeCutoff_room (a : Scalar) :
    Small a.val ((pairedSecondDerivativeCutoff a:Rat)-1) := by
  apply (pairedInternalBound_small a).mono
  simp only [pairedSecondDerivativeCutoff,Rat.natCast_add]
  rw [show ((2:Nat):Rat)=2 by decide +kernel]
  grind only

theorem pairedSecondDerivativeCutoff_neighbor_room (a z : Scalar)
    (hd : Small (sub z.val a.val) 1) :
    Small z.val ((pairedSecondDerivativeCutoff a:Rat)-1) := by
  have h := LocalODE.small_add (pairedInternalBound_small a) hd
  have he : (pairedInternalBound a:Rat)+1=(pairedSecondDerivativeCutoff a:Rat)-1 := by
    simp only [pairedSecondDerivativeCutoff,Rat.natCast_add]
    rw [show ((2:Nat):Rat)=2 by decide +kernel]
    grind only
  rw [he] at h
  exact Small.congr (add_valid a.property (sub_valid z.property a.property)) z.property
    (SeriesLimitLaws.add_difference z.val a.val z.property a.property) h

def pairedCanonicalSecondDerivative (a : Scalar) (ha : InUpperHalfPlane a.val) : Scalar :=
  pairedGlobalSecondDerivativeAssembly a ha (pairedSecondDerivativeCutoff a)
    (pairedCutoff_room_small _ a (pairedSecondDerivativeCutoff_room a))

def pairedCanonicalFirstDerivativeMap_hasDerivativeAt (a : Scalar)
    (ha : InUpperHalfPlane a.val) :
    HasDerivativeAt pairedCanonicalFirstDerivativeMap a ha (pairedCanonicalSecondDerivative a ha) where
  delta eps := minRadius ⟨1,by decide +kernel⟩
    ((pairedJoinedFirstDerivativeDiskMap_hasDerivativeAt (pairedSecondDerivativeCutoff a) a
      ⟨ha,pairedCutoff_room_small _ a (pairedSecondDerivativeCutoff_room a)⟩).delta eps)
  estimate eps H z hz hH hd := by
    let B := pairedSecondDerivativeCutoff a
    have hunit : H.val≤1 := Rat.le_trans hH (minRadius_left _ _)
    have hzroom := pairedSecondDerivativeCutoff_neighbor_room a z (hd.mono hunit)
    let hA : (pairedJoinedFirstDerivativeDiskMap B).domain a :=
      ⟨ha,pairedCutoff_room_small B a (pairedSecondDerivativeCutoff_room a)⟩
    let hZ : (pairedJoinedFirstDerivativeDiskMap B).domain z :=
      ⟨hz,pairedCutoff_room_small B z hzroom⟩
    have h := (pairedJoinedFirstDerivativeDiskMap_hasDerivativeAt B a hA).estimate eps H z hZ
      (Rat.le_trans hH (minRadius_right _ _)) hd
    have he := FunctionTheory.sub_congr
      (FunctionTheory.sub_congr (pairedJoinedFirstDerivativeDiskMap_canonical B z hZ hzroom)
        (pairedJoinedFirstDerivativeDiskMap_canonical B a hA (pairedSecondDerivativeCutoff_room a)))
      (equiv_refl _ (mul_valid (pairedCanonicalSecondDerivative a ha).property (sub_valid z.property a.property)))
    exact Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _)
      (DomainFunctions.remainder_valid pairedCanonicalFirstDerivativeMap a ha
        (pairedCanonicalSecondDerivative a ha) z hz) he h

end ComputableAnalysis.ModularForms
