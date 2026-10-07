import ComputableAnalysis.ModularForms.PairedSmallDiskRemainderIdentity

/-! Differentiability of the actual regular part through zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedRegularPartMap : DomainFunctions.Map where
  domain := LocalODE.interior (1/4)
  eval z hz := ⟨pairedRegularPart z (LocalODE.interior_bound _ z hz),
    pairedRegularPart_valid z (LocalODE.interior_bound _ z hz)⟩
  domain_congr z w he := by
    constructor
    · rintro ⟨r,hr,hrq,hz⟩
      exact ⟨r,hr,hrq,Small.congr z.property w.property he hz⟩
    · rintro ⟨r,hr,hrq,hw⟩
      exact ⟨r,hr,hrq,Small.congr w.property z.property (equiv_symm he) hw⟩
  eval_congr z w hz hw he := pairedRegularPart_congr z w
    (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ w hw) he

def pairedRegularPartDerivative (a : Scalar) (ha : pairedRegularPartMap.domain a) : Scalar :=
  ⟨pairedSmallDiskDerivativeValue a (LocalODE.interior_bound _ a ha),
    pairedSmallDiskDerivativeValue_valid a (LocalODE.interior_bound _ a ha)⟩

def pairedRegularPartMap_hasDerivativeAt (a : Scalar) (ha : pairedRegularPartMap.domain a) :
    HasDerivativeAt pairedRegularPartMap a ha (pairedRegularPartDerivative a ha) where
  delta eps := divideRadius eps ⟨262144,by decide +kernel⟩
  estimate eps H z hz hH hd := by
    have hi := pairedSmallDiskRemainder_identity a z ha hz H.val (Rat.le_of_lt H.property) hd
    have vR := DomainFunctions.remainder_valid pairedRegularPartMap a ha
      (pairedRegularPartDerivative a ha) z hz
    have h := Small.congr (pairedSmallDiskRemainder_valid a z ha hz) vR hi
      (pairedSmallDiskRemainder_bound a z ha hz H.val (Rat.le_of_lt H.property) hd)
    apply h.mono
    have hm := Rat.mul_le_mul_of_nonneg_left hH (show (0:Rat)≤262144 by decide)
    rw [divideRadius_identity eps ⟨262144,by decide +kernel⟩] at hm
    exact Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)

theorem pairedRegularPartDerivative_congr (a b : Scalar)
    (ha : pairedRegularPartMap.domain a) (hb : pairedRegularPartMap.domain b)
    (he : a.val.Equiv b.val) :
    (pairedRegularPartDerivative a ha).val.Equiv (pairedRegularPartDerivative b hb).val :=
  pairedSmallDiskDerivativeValue_congr a b (LocalODE.interior_bound _ a ha)
    (LocalODE.interior_bound _ b hb) he

end ComputableAnalysis.ModularForms
