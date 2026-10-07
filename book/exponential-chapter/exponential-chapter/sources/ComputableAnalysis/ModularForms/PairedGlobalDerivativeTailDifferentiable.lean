import ComputableAnalysis.ModularForms.PairedGlobalDerivativeTailRemainderIdentity
import ComputableAnalysis.ModularForms.PairedTailDerivative

/-! Actual differentiation of the infinite global first-derivative tail. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedGlobalFirstDerivativeTailMap (B : Nat) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val ∧ Small z.val (B:Rat)
  eval z hz := ⟨pairedDerivativeTailValue z hz.1 B,pairedDerivativeTailValue_valid z hz.1 B hz.2⟩
  domain_congr := (pairedTailDiskMap B).domain_congr
  eval_congr z w hz hw he := pairedDerivativeTailValue_congr z w hz.1 hw.1 B hz.2 hw.2 he

def pairedGlobalFirstDerivativeTailMap_hasDerivativeAt (B : Nat) (a : Scalar)
    (ha : (pairedGlobalFirstDerivativeTailMap B).domain a) :
    HasDerivativeAt (pairedGlobalFirstDerivativeTailMap B) a ha
      ⟨pairedGlobalSecondDerivativeTailValue a ha.1 B,
        pairedGlobalSecondDerivativeTailValue_valid a ha.1 B ha.2⟩ where
  delta eps := divideRadius eps ⟨25165824,by decide +kernel⟩
  estimate eps H z hz hH hd := by
    have h := pairedGlobalDerivativeTail_sum_remainder_bound a z ha.1 hz.1 B ha.2 hz.2
      H.val (Rat.le_of_lt H.property) hd
    apply h.mono
    have hm := Rat.mul_le_mul_of_nonneg_left hH (show (0:Rat)≤25165824 by decide)
    rw [divideRadius_identity eps ⟨25165824,by decide +kernel⟩] at hm
    exact Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)

end ComputableAnalysis.ModularForms
