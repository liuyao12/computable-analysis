import ComputableAnalysis.ModularForms.IntegerPowerRowInvariance
import ComputableAnalysis.ModularForms.PairedReciprocalSquarePrefixes

/-! Exact comparison of the actual power-two pairs with reciprocal-square pairs. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem power_two_square (a : Scalar) :
    (LocalODE.power a.val 2).Equiv (mul a.val a.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := LocalODE.power_valid _ a.property 2)
    (hright := mul_valid a.property a.property)
  rw [ScalarAlgebra.ofRaw_power]
  let A := ComplexRawQuotient.ofRaw a.val a.property
  change (1*A)*A=A*A
  grind only

theorem upperPairedIntegerPower_square_agreement (z : Scalar)
    (hz : InUpperHalfPlane z.val) (n : Nat) :
    (upperPairedIntegerPower z hz 2 n).val.Equiv
      (upperPairedReciprocalSquare z hz n).val := by
  have hm := RepresentedReciprocal.inverse_congr
    (integerShiftScalar z (-((n:Nat):Int))) (pairedMinus z (boundaryIntegerScalar n))
    (upperScalar_nonzero _ (integerShiftScalar_upper z hz _))
    (upperShiftMinus_nonzero z hz (n:Rat)) (integerShiftScalar_minus z n)
  have hp := RepresentedReciprocal.inverse_congr
    (integerShiftScalar z ((n:Nat):Int)) (pairedPlus z (boundaryIntegerScalar n))
    (upperScalar_nonzero _ (integerShiftScalar_upper z hz _))
    (upperShiftPlus_nonzero z hz (n:Rat)) (integerShiftScalar_plus z n)
  have side (a b : Scalar) (he : a.val.Equiv b.val) :
      (LocalODE.power a.val 2).Equiv (mul b.val b.val) :=
    equiv_trans (LocalODE.power_valid _ a.property 2)
      (mul_valid a.property a.property) (mul_valid b.property b.property)
      (power_two_square a) (mul_equiv a.property b.property a.property b.property he he)
  exact add_equiv (side _ _ hm) (side _ _ hp)

theorem upperPairedIntegerPower_square_prefix_agreement (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    (ScalarSeries.block (fun n => (upperPairedIntegerPower z hz 2 (n+1)).val) 0 N).Equiv
      (ScalarSeries.block (fun n => (upperPairedReciprocalSquare z hz (n+1)).val) 0 N) :=
  ScalarSeries.block_congr _ _ (fun n => upperPairedIntegerPower_square_agreement z hz (n+1)) 0 N

end ComputableAnalysis.ModularForms
