import ComputableAnalysis.ModularForms.PairedJoinedDerivative

/-! Differentiability of the actual reciprocal series on the full upper half plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedPartialFractionMap : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨upperPairedPartialFractionValue z hz,upperPairedPartialFractionValue_valid z hz⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := pairedPartialFractionValue_congr z w
    (upperScalar_nonzero z hz) (upperScalar_nonzero w hw)
    (upperPairedSeriesDomain z hz) (upperPairedSeriesDomain w hw) he

def pairedDerivativeCutoff (a : Scalar) : Nat := pairedInternalBound a+1

theorem pairedDerivativeCutoff_small (a : Scalar) : Small a.val ((pairedDerivativeCutoff a):Rat) := by
  apply (pairedInternalBound_small a).mono
  exact_mod_cast (show pairedInternalBound a≤pairedDerivativeCutoff a by unfold pairedDerivativeCutoff; omega)

theorem pairedDerivativeCutoff_neighbor (a z : Scalar)
    (hd : Small (sub z.val a.val) 1) : Small z.val ((pairedDerivativeCutoff a):Rat) := by
  have h := LocalODE.small_add (pairedInternalBound_small a) hd
  have hc : ((pairedInternalBound a):Rat)+1=((pairedDerivativeCutoff a):Rat) := by
    simp only [pairedDerivativeCutoff,Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
  rw [hc] at h
  exact Small.congr (add_valid a.property (sub_valid z.property a.property)) z.property
    (SeriesLimitLaws.add_difference z.val a.val z.property a.property) h

def pairedPartialFractionDerivative (a : Scalar) (ha : InUpperHalfPlane a.val) : Scalar :=
  pairedWholeJoinedDerivative (pairedDerivativeCutoff a) a ⟨ha,pairedDerivativeCutoff_small a⟩

def pairedPartialFractionMap_hasDerivativeAt (a : Scalar) (ha : InUpperHalfPlane a.val) :
    HasDerivativeAt pairedPartialFractionMap a ha (pairedPartialFractionDerivative a ha) where
  delta eps := minRadius ⟨1,by decide +kernel⟩
    ((pairedWholeJoinedMap_hasDerivativeAt (pairedDerivativeCutoff a) a
      ⟨ha,pairedDerivativeCutoff_small a⟩).delta eps)
  estimate eps H z hz hH hd := by
    have hunit : H.val≤1 := Rat.le_trans hH (minRadius_left _ _)
    have hzB := pairedDerivativeCutoff_neighbor a z (hd.mono hunit)
    let B := pairedDerivativeCutoff a
    let hA : (pairedWholeJoinedMap B).domain a := ⟨ha,pairedDerivativeCutoff_small a⟩
    let hZ : (pairedWholeJoinedMap B).domain z := ⟨hz,hzB⟩
    have h := (pairedWholeJoinedMap_hasDerivativeAt B a hA).estimate eps H z hZ
      (Rat.le_trans hH (minRadius_right _ _)) hd
    have he := FunctionTheory.sub_congr
      (FunctionTheory.sub_congr (pairedWholeJoinedMap_eval B z hZ) (pairedWholeJoinedMap_eval B a hA))
      (equiv_refl _ (mul_valid (pairedPartialFractionDerivative a ha).property
        (sub_valid z.property a.property)))
    exact Small.congr (DomainFunctions.remainder_valid (pairedWholeJoinedMap B) a hA
      (pairedWholeJoinedDerivative B a hA) z hZ)
      (DomainFunctions.remainder_valid pairedPartialFractionMap a ha (pairedPartialFractionDerivative a ha) z hz) he h

def pairedPartialFractionMap_continuous :
    ContinuousOn pairedPartialFractionMap.domain pairedPartialFractionMap.eval :=
  continuousOn_of_derivative pairedPartialFractionMap pairedPartialFractionDerivative
    pairedPartialFractionMap_hasDerivativeAt

end ComputableAnalysis.ModularForms
