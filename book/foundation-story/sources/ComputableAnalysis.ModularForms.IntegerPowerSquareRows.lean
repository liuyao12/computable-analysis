import ComputableAnalysis.ModularForms.IntegerPowerSquareTails
import ComputableAnalysis.ModularForms.PairedReciprocalSquareSum
import ComputableAnalysis.ModularForms.ReciprocalSquarePiFourier

/-! Comparison of the constructed power-two row with the established square sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerPowerRowAssembly_square_agreement (z : Scalar)
    (hz : InUpperHalfPlane z.val) (B : Nat) (hB : Small z.val (B:Rat)) :
    (integerPowerRowAssembly z hz 2 B).Equiv
      (pairedReciprocalSquareAssembly z hz B hB).val := by
  let i := upperIntegerReciprocal z hz 0
  have hc : ((integerReciprocalPowerMap 0 2).eval z hz).val.Equiv (mul i.val i.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((integerReciprocalPowerMap 0 2).eval z hz).property)
      (hright := mul_valid i.property i.property)
    change ComplexRawQuotient.ofRaw (LocalODE.power i.val 2) (LocalODE.power_valid _ i.property 2)=_
    rw [ScalarAlgebra.ofRaw_power]
    let I := ComplexRawQuotient.ofRaw i.val i.property
    change (1*I)*I=I*I
    grind only
  have hp := upperPairedIntegerPower_square_prefix_agreement z hz (4*B)
  have ht := pairedIntegerPower_square_tail_agreement z hz B hB
  have ha := add_equiv (add_equiv hc hp) ht
  apply equiv_trans (integerPowerRowAssembly_valid z hz 2 B (by omega) hB)
    (add_valid (add_valid (mul_valid i.property i.property)
      (ScalarSeries.block_valid _ (fun n => (upperPairedReciprocalSquare z hz (n+1)).property) 0 (4*B)))
      (pairedReciprocalSquareTailValue_valid z hz B hB))
    (pairedReciprocalSquareAssembly z hz B hB).property ha
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
  let C := ComplexRawQuotient.ofRaw (mul i.val i.val) (mul_valid i.property i.property)
  let P := ComplexRawQuotient.ofRaw
    (ScalarSeries.block (fun n => (upperPairedReciprocalSquare z hz (n+1)).val) 0 (4*B))
    (ScalarSeries.block_valid _ (fun n => (upperPairedReciprocalSquare z hz (n+1)).property) 0 (4*B))
  let T := ComplexRawQuotient.ofRaw (pairedReciprocalSquareTailValue z hz B)
    (pairedReciprocalSquareTailValue_valid z hz B hB)
  change (C+P)+T=C+(P+T)
  grind only

theorem integerReciprocalPowerRowSum_square_agreement (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    (integerReciprocalPowerRowSum z hz 2 (by omega)).val.Equiv
      (pairedReciprocalSquareSum z hz).val :=
  integerPowerRowAssembly_square_agreement z hz _ (pairedDerivativeCutoff_small z)

theorem integerReciprocalPowerRowSum_square_pi_fourier (z : Scalar)
    (hz : InUpperHalfPlane z.val) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (integerReciprocalPowerRowSum z hz 2 (by omega)).val.Equiv
      (neg (scaleRat 4 (mul (mul geometricPiScalar.val geometricPiScalar.val)
        (weightedNomeSum (nome.eval z hz) r)))) :=
  equiv_trans (integerReciprocalPowerRowSum z hz 2 (by omega)).property
    (pairedReciprocalSquareSum z hz).property
    (neg_valid (scaleRat_valid (r := 4) (mul_valid
      (mul_valid geometricPiScalar.property geometricPiScalar.property)
      (weightedNomeSum_valid (nome.eval z hz) r hr hlocal hq))))
    (integerReciprocalPowerRowSum_square_agreement z hz)
    (pairedReciprocalSquareSum_pi_fourier z hz r hr hlocal hq)

end ComputableAnalysis.ModularForms
