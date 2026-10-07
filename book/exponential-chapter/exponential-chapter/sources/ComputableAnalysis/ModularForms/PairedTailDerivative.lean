import ComputableAnalysis.ModularForms.PairedTailRemainderIdentity

/-! Differentiability of the actual reciprocal tail from the identified remainder limit. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedTailDiskMap (B : Nat) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val ∧ Small z.val (B:Rat)
  eval z hz := ⟨pairedTailValue z B hz.2,pairedTailValue_valid z B hz.2⟩
  domain_congr z w he := by
    constructor
    · intro h
      exact ⟨(upperOpenData.invariant z w he).mp h.1,Small.congr z.property w.property he h.2⟩
    · intro h
      exact ⟨(upperOpenData.invariant z w he).mpr h.1,Small.congr w.property z.property (equiv_symm he) h.2⟩
  eval_congr z w hz hw he := pairedTailValue_congr z w B hz.2 hw.2 he

def pairedTailDiskDerivative (B : Nat) (a : Scalar) (ha : (pairedTailDiskMap B).domain a) : Scalar :=
  ⟨pairedDerivativeTailValue a ha.1 B,pairedDerivativeTailValue_valid a ha.1 B ha.2⟩

def pairedTailDiskMap_hasDerivativeAt (B : Nat) (a : Scalar) (ha : (pairedTailDiskMap B).domain a) :
    HasDerivativeAt (pairedTailDiskMap B) a ha (pairedTailDiskDerivative B a ha) where
  delta eps := divideRadius eps ⟨1048576,by decide +kernel⟩
  estimate eps H z hz hH hd := by
    have hi := pairedTailRemainder_identity B a z ha.1 hz.1 ha.2 hz.2 H.val
      (Rat.le_of_lt H.property) hd
    have vR := DomainFunctions.remainder_valid (pairedTailDiskMap B) a ha
      (pairedTailDiskDerivative B a ha) z hz
    have h := Small.congr (pairedTailRemainder_valid B a z ha.1 hz.1 ha.2 hz.2) vR hi
      (pairedTailRemainder_bound B a z ha.1 hz.1 ha.2 hz.2 H.val (Rat.le_of_lt H.property) hd)
    apply h.mono
    have hm := Rat.mul_le_mul_of_nonneg_left hH (show (0:Rat)≤1048576 by decide)
    rw [divideRadius_identity eps ⟨1048576,by decide +kernel⟩] at hm
    have hp := Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)
    exact hp

end ComputableAnalysis.ModularForms
