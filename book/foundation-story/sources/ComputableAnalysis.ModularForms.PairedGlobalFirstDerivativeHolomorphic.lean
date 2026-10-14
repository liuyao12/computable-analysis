import ComputableAnalysis.ModularForms.PairedSecondDerivativeAssemblyContinuity

/-! Continuous actual second derivative and holomorphic canonical first derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedSecondContinuityCutoff (a : Scalar) : Nat := pairedInternalBound a+3

theorem pairedSecondContinuityCutoff_room (a : Scalar) :
    Small a.val ((pairedSecondContinuityCutoff a:Rat)-2) := by
  apply (pairedInternalBound_small a).mono
  simp only [pairedSecondContinuityCutoff,Rat.natCast_add]
  rw [show ((3:Nat):Rat)=3 by decide +kernel]
  grind only

theorem pairedSecondContinuityCutoff_neighbor_room (a z : Scalar)
    (hd : Small (sub z.val a.val) 1) : Small z.val ((pairedSecondContinuityCutoff a:Rat)-2) := by
  have h := LocalODE.small_add (pairedInternalBound_small a) hd
  have he : (pairedInternalBound a:Rat)+1=(pairedSecondContinuityCutoff a:Rat)-2 := by
    simp only [pairedSecondContinuityCutoff,Rat.natCast_add]
    rw [show ((3:Nat):Rat)=3 by decide +kernel]
    grind only
  rw [he] at h
  exact Small.congr (add_valid a.property (sub_valid z.property a.property)) z.property
    (SeriesLimitLaws.add_difference z.val a.val z.property a.property) h

noncomputable def pairedCanonicalSecondDerivative_continuous :
    ContinuousOn pairedCanonicalFirstDerivativeMap.domain pairedCanonicalSecondDerivative where
  delta a ha eps := minRadius ⟨1,by decide +kernel⟩
    ((pairedGlobalSecondDerivativeAssembly_continuous (pairedSecondContinuityCutoff a)).delta a
      ⟨ha,(pairedSecondContinuityCutoff_room a).mono (by grind only)⟩ eps)
  estimate a ha eps z hz hd := by
    let B := pairedSecondContinuityCutoff a
    have hzroom := pairedSecondContinuityCutoff_neighbor_room a z (hd.mono (minRadius_left _ _))
    have haroom := pairedSecondContinuityCutoff_room a
    let hA : (pairedGlobalFirstDerivativeTailMap B).domain a := ⟨ha,haroom.mono (by grind only)⟩
    let hZ : (pairedGlobalFirstDerivativeTailMap B).domain z := ⟨hz,hzroom.mono (by grind only)⟩
    have h := (pairedGlobalSecondDerivativeAssembly_continuous B).estimate a hA eps z hZ
      (hd.mono (minRadius_right _ _))
    exact Small.congr
      (sub_valid (pairedGlobalSecondDerivativeAssembly z hz B hZ.2).property
        (pairedGlobalSecondDerivativeAssembly a ha B hA.2).property)
      (sub_valid (pairedCanonicalSecondDerivative z hz).property (pairedCanonicalSecondDerivative a ha).property)
      (FunctionTheory.sub_congr (pairedCanonicalSecondDerivative_cutoff B z hz hzroom)
        (pairedCanonicalSecondDerivative_cutoff B a ha haroom)) h

noncomputable def pairedCanonicalFirstDerivativeMap_holomorphic : Holomorphic pairedCanonicalFirstDerivativeMap where
  openDomain := pairedCanonicalFirstDerivativeMap_open
  derivative := pairedCanonicalSecondDerivative
  atPoint := pairedCanonicalFirstDerivativeMap_hasDerivativeAt
  derivative_congr := pairedCanonicalSecondDerivative_congr
  continuousDerivative := pairedCanonicalSecondDerivative_continuous

end ComputableAnalysis.ModularForms
