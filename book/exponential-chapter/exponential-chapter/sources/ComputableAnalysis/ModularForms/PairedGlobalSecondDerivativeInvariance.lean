import ComputableAnalysis.ModularForms.PairedGlobalTwiceDifferentiable

/-! Representation invariance and uniqueness of the actual global second derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedCanonicalFirstDerivativeMap_open : OpenDomain pairedCanonicalFirstDerivativeMap :=
  ⟨upperRadius,upperRadius_inside⟩

theorem pairedCanonicalSecondDerivative_congr (a b : Scalar)
    (ha : InUpperHalfPlane a.val) (hb : InUpperHalfPlane b.val) (he : a.val.Equiv b.val) :
    (pairedCanonicalSecondDerivative a ha).val.Equiv (pairedCanonicalSecondDerivative b hb).val :=
  ((pairedCanonicalFirstDerivativeMap_hasDerivativeAt a ha).congrPoint hb he).unique
    (pairedCanonicalFirstDerivativeMap_hasDerivativeAt b hb) pairedCanonicalFirstDerivativeMap_open

theorem pairedCanonicalSecondDerivative_unique (a : Scalar) (ha : InUpperHalfPlane a.val)
    (d : Scalar) (hd : HasDerivativeAt pairedCanonicalFirstDerivativeMap a ha d) :
    d.val.Equiv (pairedCanonicalSecondDerivative a ha).val :=
  hd.unique (pairedCanonicalFirstDerivativeMap_hasDerivativeAt a ha) pairedCanonicalFirstDerivativeMap_open

def pairedCanonicalSecondDerivativeMap : DomainFunctions.Map where
  domain := pairedCanonicalFirstDerivativeMap.domain
  eval := pairedCanonicalSecondDerivative
  domain_congr := pairedCanonicalFirstDerivativeMap.domain_congr
  eval_congr := pairedCanonicalSecondDerivative_congr

def pairedCanonicalFirstDerivativeMap_cutoffSecondDerivative (B : Nat) (a : Scalar)
    (ha : InUpperHalfPlane a.val) (hroom : Small a.val ((B:Rat)-2)) :
    HasDerivativeAt pairedCanonicalFirstDerivativeMap a ha
      (pairedGlobalSecondDerivativeAssembly a ha B (hroom.mono (by grind only))) where
  delta eps := minRadius ⟨1,by decide +kernel⟩
    ((pairedJoinedFirstDerivativeDiskMap_hasDerivativeAt B a
      ⟨ha,hroom.mono (by grind only)⟩).delta eps)
  estimate eps H z hz hH hd := by
    have hunit : H.val≤1 := Rat.le_trans hH (minRadius_left _ _)
    have hzr := LocalODE.small_add hroom (hd.mono hunit)
    have hzroom : Small z.val ((B:Rat)-1) :=
      (Small.congr (add_valid a.property (sub_valid z.property a.property)) z.property
        (SeriesLimitLaws.add_difference z.val a.val z.property a.property) hzr).mono (by grind only)
    have haroom : Small a.val ((B:Rat)-1) := hroom.mono (by grind only)
    let hA : (pairedJoinedFirstDerivativeDiskMap B).domain a := ⟨ha,hroom.mono (by grind only)⟩
    let hZ : (pairedJoinedFirstDerivativeDiskMap B).domain z := ⟨hz,pairedCutoff_room_small B z hzroom⟩
    have h := (pairedJoinedFirstDerivativeDiskMap_hasDerivativeAt B a hA).estimate eps H z hZ
      (Rat.le_trans hH (minRadius_right _ _)) hd
    have he := FunctionTheory.sub_congr
      (FunctionTheory.sub_congr (pairedJoinedFirstDerivativeDiskMap_canonical B z hZ hzroom)
        (pairedJoinedFirstDerivativeDiskMap_canonical B a hA haroom))
      (equiv_refl _ (mul_valid (pairedGlobalSecondDerivativeAssembly a ha B hA.2).property
        (sub_valid z.property a.property)))
    exact Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _)
      (DomainFunctions.remainder_valid pairedCanonicalFirstDerivativeMap a ha
        (pairedGlobalSecondDerivativeAssembly a ha B hA.2) z hz) he h

theorem pairedCanonicalSecondDerivative_cutoff (B : Nat) (a : Scalar)
    (ha : InUpperHalfPlane a.val) (hroom : Small a.val ((B:Rat)-2)) :
    (pairedGlobalSecondDerivativeAssembly a ha B (hroom.mono (by grind only))).val.Equiv
      (pairedCanonicalSecondDerivative a ha).val :=
  pairedCanonicalSecondDerivative_unique a ha _
    (pairedCanonicalFirstDerivativeMap_cutoffSecondDerivative B a ha hroom)

end ComputableAnalysis.ModularForms
