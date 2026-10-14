import ComputableAnalysis.ModularForms.PairedOffPoleTailContinuity

/-! Explicit actual derivative terms for the tail on its full interior disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailInverse (B n : Nat) (z : Scalar) (hz : LocalODE.interior (B:Rat) z) : Scalar :=
  RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare (pairedTailShift B n)))
    (pairedIntegerDenominator_nonzero z (B:Rat) (pairedTailShift B n) Rat.natCast_nonneg
      (LocalODE.interior_bound _ z hz) (by unfold pairedTailShift; omega) (pairedTailShift_large B n))

def pairedOffPoleTailDerivativeTerm (B n : Nat) (z : Scalar) (hz : LocalODE.interior (B:Rat) z) : Scalar :=
  let i := pairedOffPoleTailInverse B n z hz
  let zz := scalarSum z z
  ⟨sub (add i.val i.val) (mul (mul zz.val zz.val) (mul i.val i.val)),
    sub_valid (add_valid i.property i.property)
      (mul_valid (mul_valid zz.property zz.property) (mul_valid i.property i.property))⟩

theorem pairedOffPoleTailTermMap_derivative (B n : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) :
    ((pairedOffPoleTailTermMap_holomorphic B n).derivative z hz).val.Equiv
      (pairedOffPoleTailDerivativeTerm B n z hz).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((pairedOffPoleTailTermMap_holomorphic B n).derivative z hz).property)
    (hright := (pairedOffPoleTailDerivativeTerm B n z hz).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (pairedOffPoleTailInverse B n z hz).val
    (pairedOffPoleTailInverse B n z hz).property
  let A := ComplexRawQuotient.ofQComplex ⟨(2:Rat),0⟩
  change (-(I*I)*(1*(1*(0+1*Z)+(0+1*Z)*1)))*(0+A*Z)+I*A=
    (I+I)-((Z+Z)*(Z+Z))*(I*I)
  have htwo : A=((2:Int):ComplexRawQuotient.Value) := by
    simpa only [show ((2:Int):Rat)=2 by decide +kernel] using integer_constant (2:Int)
  rw [htwo]
  grind only

def pairedOffPoleTailTermMap_hasDerivativeAt (B n : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) :
    HasDerivativeAt (pairedOffPoleTailTermMap B n) z hz (pairedOffPoleTailDerivativeTerm B n z hz) :=
  ((pairedOffPoleTailTermMap_holomorphic B n).atPoint z hz).congrDerivative
    (pairedOffPoleTailTermMap_derivative B n z hz)

end ComputableAnalysis.ModularForms
