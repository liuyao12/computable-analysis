import ComputableAnalysis.ModularForms.PairedDerivativeTailContinuity

/-! Continuous derivatives and holomorphicity of the actual full reciprocal series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedJoinedDerivative_continuous (B : Nat) :
    ContinuousOn (pairedJoinedMap B).domain (pairedJoinedDerivative B) :=
  sumContinuous _ _
    (restrictContinuous (pairedFiniteMap_holomorphic (4*B)).derivative
      (pairedFiniteMap_holomorphic (4*B)).continuousDerivative
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz.1))
    (pairedTailDiskDerivative_continuous B)

def pairedWholeJoinedDerivative_continuous (B : Nat) :
    ContinuousOn (pairedWholeJoinedMap B).domain (pairedWholeJoinedDerivative B) :=
  sumContinuous _ _
    (restrictContinuous (integerReciprocalMap_holomorphic 0).derivative
      (integerReciprocalMap_holomorphic 0).continuousDerivative
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz.1))
    (pairedJoinedDerivative_continuous B)

def pairedContinuityCutoff (a : Scalar) : Nat := pairedInternalBound a+2

theorem pairedContinuityCutoff_room (a : Scalar) :
    Small a.val (((pairedContinuityCutoff a):Rat)-1) := by
  apply (pairedInternalBound_small a).mono
  have he : ((pairedContinuityCutoff a):Rat)=((pairedInternalBound a):Rat)+2 := by
    simp only [pairedContinuityCutoff,Rat.natCast_add,show ((2:Nat):Rat)=2 by decide +kernel]
  rw [he]
  grind only

theorem pairedContinuityCutoff_neighbor_room (a z : Scalar)
    (hd : Small (sub z.val a.val) 1) :
    Small z.val (((pairedContinuityCutoff a):Rat)-1) := by
  have h := pairedDerivativeCutoff_neighbor a z hd
  have he : ((pairedDerivativeCutoff a):Rat)=((pairedContinuityCutoff a):Rat)-1 := by
    simp only [pairedDerivativeCutoff,pairedContinuityCutoff,Rat.natCast_add,
      show ((1:Nat):Rat)=1 by decide +kernel,show ((2:Nat):Rat)=2 by decide +kernel]
    grind only
  rw [he] at h
  exact h

def pairedPartialFractionDerivative_continuous :
    ContinuousOn pairedPartialFractionMap.domain pairedPartialFractionDerivative where
  delta a ha eps := minRadius ⟨1,by decide +kernel⟩
    ((pairedWholeJoinedDerivative_continuous (pairedContinuityCutoff a)).delta a
      ⟨ha,pairedCutoff_room_small _ a (pairedContinuityCutoff_room a)⟩ eps)
  estimate a ha eps z hz hd := by
    let B := pairedContinuityCutoff a
    have hroomA := pairedContinuityCutoff_room a
    have hroomZ := pairedContinuityCutoff_neighbor_room a z (hd.mono (minRadius_left _ _))
    let hA : (pairedWholeJoinedMap B).domain a := ⟨ha,pairedCutoff_room_small B a hroomA⟩
    let hZ : (pairedWholeJoinedMap B).domain z := ⟨hz,pairedCutoff_room_small B z hroomZ⟩
    have h := (pairedWholeJoinedDerivative_continuous B).estimate a hA eps z hZ
      (hd.mono (minRadius_right _ _))
    have he := FunctionTheory.sub_congr (pairedPartialFractionDerivative_cutoff B z hz hroomZ)
      (pairedPartialFractionDerivative_cutoff B a ha hroomA)
    exact Small.congr (sub_valid (pairedWholeJoinedDerivative B z hZ).property
      (pairedWholeJoinedDerivative B a hA).property)
      (sub_valid (pairedPartialFractionDerivative z hz).property (pairedPartialFractionDerivative a ha).property) he h

def pairedPartialFractionMap_holomorphic : DomainFunctions.Holomorphic pairedPartialFractionMap where
  openDomain := pairedPartialFractionMap_open
  derivative := pairedPartialFractionDerivative
  atPoint := pairedPartialFractionMap_hasDerivativeAt
  derivative_congr := pairedPartialFractionDerivative_congr
  continuousDerivative := pairedPartialFractionDerivative_continuous

end ComputableAnalysis.ModularForms
