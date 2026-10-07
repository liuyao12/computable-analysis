import ComputableAnalysis.ModularForms.PairedGlobalDerivative
import ComputableAnalysis.RiemannHilbert.DomainDerivativeUniqueness
import ComputableAnalysis.RiemannHilbert.DomainDerivativeInvariance

/-! Representation invariance and cutoff agreement of actual reciprocal-series derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedPartialFractionMap_open : OpenDomain pairedPartialFractionMap :=
  ⟨upperRadius,upperRadius_inside⟩

theorem pairedPartialFractionDerivative_congr (a b : Scalar)
    (ha : InUpperHalfPlane a.val) (hb : InUpperHalfPlane b.val) (hab : a.val.Equiv b.val) :
    (pairedPartialFractionDerivative a ha).val.Equiv (pairedPartialFractionDerivative b hb).val :=
  ((pairedPartialFractionMap_hasDerivativeAt a ha).congrPoint hb hab).unique
    (pairedPartialFractionMap_hasDerivativeAt b hb) pairedPartialFractionMap_open

theorem pairedPartialFractionDerivative_unique (a : Scalar) (ha : InUpperHalfPlane a.val)
    (d : Scalar) (hd : HasDerivativeAt pairedPartialFractionMap a ha d) :
    d.val.Equiv (pairedPartialFractionDerivative a ha).val :=
  hd.unique (pairedPartialFractionMap_hasDerivativeAt a ha) pairedPartialFractionMap_open

theorem pairedCutoff_room_small (B : Nat) (a : Scalar)
    (hroom : Small a.val ((B:Rat)-1)) : Small a.val (B:Rat) :=
  hroom.mono (by grind only)

theorem pairedCutoff_room_neighbor (B : Nat) (a z : Scalar)
    (hroom : Small a.val ((B:Rat)-1)) (hd : Small (sub z.val a.val) 1) : Small z.val (B:Rat) := by
  have h := LocalODE.small_add hroom hd
  have he : ((B:Rat)-1)+1=(B:Rat) := by grind only
  rw [he] at h
  exact Small.congr (add_valid a.property (sub_valid z.property a.property)) z.property
    (SeriesLimitLaws.add_difference z.val a.val z.property a.property) h

def pairedPartialFractionMap_cutoffDerivative (B : Nat) (a : Scalar)
    (ha : InUpperHalfPlane a.val) (hroom : Small a.val ((B:Rat)-1)) :
    HasDerivativeAt pairedPartialFractionMap a ha
      (pairedWholeJoinedDerivative B a ⟨ha,pairedCutoff_room_small B a hroom⟩) where
  delta eps := minRadius ⟨1,by decide +kernel⟩
    ((pairedWholeJoinedMap_hasDerivativeAt B a ⟨ha,pairedCutoff_room_small B a hroom⟩).delta eps)
  estimate eps H z hz hH hd := by
    have hunit : H.val≤1 := Rat.le_trans hH (minRadius_left _ _)
    have hzB := pairedCutoff_room_neighbor B a z hroom (hd.mono hunit)
    let hA : (pairedWholeJoinedMap B).domain a := ⟨ha,pairedCutoff_room_small B a hroom⟩
    let hZ : (pairedWholeJoinedMap B).domain z := ⟨hz,hzB⟩
    have h := (pairedWholeJoinedMap_hasDerivativeAt B a hA).estimate eps H z hZ
      (Rat.le_trans hH (minRadius_right _ _)) hd
    have he := FunctionTheory.sub_congr
      (FunctionTheory.sub_congr (pairedWholeJoinedMap_eval B z hZ) (pairedWholeJoinedMap_eval B a hA))
      (equiv_refl _ (mul_valid (pairedWholeJoinedDerivative B a hA).property (sub_valid z.property a.property)))
    exact Small.congr (DomainFunctions.remainder_valid (pairedWholeJoinedMap B) a hA
      (pairedWholeJoinedDerivative B a hA) z hZ)
      (DomainFunctions.remainder_valid pairedPartialFractionMap a ha (pairedWholeJoinedDerivative B a hA) z hz) he h

theorem pairedPartialFractionDerivative_cutoff (B : Nat) (a : Scalar)
    (ha : InUpperHalfPlane a.val) (hroom : Small a.val ((B:Rat)-1)) :
    (pairedWholeJoinedDerivative B a ⟨ha,pairedCutoff_room_small B a hroom⟩).val.Equiv
      (pairedPartialFractionDerivative a ha).val :=
  pairedPartialFractionDerivative_unique a ha _ (pairedPartialFractionMap_cutoffDerivative B a ha hroom)

end ComputableAnalysis.ModularForms
