import ComputableAnalysis.ModularForms.PairedOffPoleTailRemainderAgreement

/-! Actual off-pole lattice holomorphicity across the real axis. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailMap_hasDerivativeAt (B : Nat) (a : Scalar)
    (ha : (pairedOffPoleTailMap B).domain a) :
    HasDerivativeAt (pairedOffPoleTailMap B) a ha (pairedOffPoleTailDerivativeValue B a ha) where
  delta eps := divideRadius eps ⟨2*pairedOffPoleTailRemainderCoefficient B+1,by
    have hc := pairedOffPoleTailRemainderCoefficient_nonneg B
    grind only⟩
  estimate eps H z hz hH hd := by
    have hb := pairedOffPoleTail_sum_remainder_bound B a z ha hz H.val (Rat.le_of_lt H.property) hd
    apply hb.mono
    have hc := pairedOffPoleTailRemainderCoefficient_nonneg B
    have hden : 0≤2*pairedOffPoleTailRemainderCoefficient B+1 := by grind only
    have hm := Rat.mul_le_mul_of_nonneg_left hH hden
    rw [divideRadius_identity eps ⟨2*pairedOffPoleTailRemainderCoefficient B+1,by grind only⟩] at hm
    have hH0 := Rat.le_of_lt H.property
    have hquad := Rat.mul_le_mul_of_nonneg_right hm hH0
    have hH2 := Rat.mul_nonneg hH0 hH0
    grind only

noncomputable def pairedOffPoleTailMap_holomorphic (B : Nat) : Holomorphic (pairedOffPoleTailMap B) where
  openDomain := ⟨LocalODE.interiorRadius (B:Rat),LocalODE.interiorRadius_inside (B:Rat)⟩
  derivative := pairedOffPoleTailDerivativeValue B
  atPoint := pairedOffPoleTailMap_hasDerivativeAt B
  derivative_congr z w hz hw he := pairedOffPoleTailDerivativeValue_congr B z w hz hw he
  continuousDerivative := pairedOffPoleTailDerivativeMap_continuous B

noncomputable def pairedOffPoleAssemblyMap_holomorphic (B : Nat) : Holomorphic (pairedOffPoleAssemblyMap B) :=
  (integerReciprocalOffPoleMap_holomorphic 0).intersectionSum
    ((pairedFiniteOffPoleMap_holomorphic (4*B)).intersectionSum (pairedOffPoleTailMap_holomorphic B))

end ComputableAnalysis.ModularForms
