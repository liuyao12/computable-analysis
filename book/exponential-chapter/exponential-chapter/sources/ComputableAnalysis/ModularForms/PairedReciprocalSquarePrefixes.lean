import ComputableAnalysis.ModularForms.PairedDerivativePrefixAgreement

/-! Reciprocal-square pairs and their exact finite derivative-prefix identity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def squareScalarValue (a : Scalar) : ComplexRawQuotient.Value :=
  ComplexRawQuotient.ofRaw a.val a.property

def upperPairedReciprocalSquare (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) : Scalar :=
  let i := RepresentedReciprocal.inverse (pairedMinus z (boundaryIntegerScalar n))
    (upperShiftMinus_nonzero z hz (n:Rat))
  let j := RepresentedReciprocal.inverse (pairedPlus z (boundaryIntegerScalar n))
    (upperShiftPlus_nonzero z hz (n:Rat))
  scalarSum (scalarProduct i i) (scalarProduct j j)

theorem upperPairedReciprocalSquare_derivative (z : Scalar)
    (hz : InUpperHalfPlane z.val) (n : Nat) :
    (upperPairedReciprocalSquare z hz n).val.Equiv
      (neg (upperPairedReciprocalDerivative z hz n).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (upperPairedReciprocalSquare z hz n).property)
    (hright := neg_valid (upperPairedReciprocalDerivative z hz n).property)
  let I := squareScalarValue (RepresentedReciprocal.inverse
    (pairedMinus z (boundaryIntegerScalar n)) (upperShiftMinus_nonzero z hz (n:Rat)))
  let J := squareScalarValue (RepresentedReciprocal.inverse
    (pairedPlus z (boundaryIntegerScalar n)) (upperShiftPlus_nonzero z hz (n:Rat)))
  change I*I+J*J= -(-(I*I)+ -(J*J))
  grind only

theorem reciprocalSquare_block_neg (t : Nat → ComplexRaw) (ht : ∀ n, (t n).Valid) (N : Nat) :
    (ScalarSeries.block (fun n => neg (t n)) 0 N).Equiv
      (neg (ScalarSeries.block t 0 N)) := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ (fun n => neg_valid (ht n)) 0 0)
      (hright := neg_valid (ScalarSeries.block_valid t ht 0 0))
    change (0:ComplexRawQuotient.Value)= -0
    grind only
  | succ N ih =>
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ScalarSeries.block_valid _ (fun n => neg_valid (ht n)) 0 N)
      (hright := neg_valid (ScalarSeries.block_valid t ht 0 N)) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ (fun n => neg_valid (ht n)) 0 (N+1))
      (hright := neg_valid (ScalarSeries.block_valid t ht 0 (N+1)))
    let S := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => neg (t n)) 0 N)
      (ScalarSeries.block_valid _ (fun n => neg_valid (ht n)) 0 N)
    let D := ComplexRawQuotient.ofRaw (ScalarSeries.block t 0 N) (ScalarSeries.block_valid t ht 0 N)
    let T := ComplexRawQuotient.ofRaw (t N) (ht N)
    change S= -D at hi
    simp only [ScalarSeries.block.eq_2,Nat.zero_add]
    change S+ -T= -(D+T)
    generalize S=s, D=d, T=u at hi ⊢
    grind only

theorem upperPairedReciprocalSquare_prefix_derivative (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    (ScalarSeries.block (fun n => (upperPairedReciprocalSquare z hz (n+1)).val) 0 N).Equiv
      (neg (ScalarSeries.block (fun n => (upperPairedReciprocalDerivative z hz (n+1)).val) 0 N)) := by
  exact equiv_trans
    (ScalarSeries.block_valid _ (fun n => (upperPairedReciprocalSquare z hz (n+1)).property) 0 N)
    (ScalarSeries.block_valid _ (fun n => neg_valid (upperPairedReciprocalDerivative z hz (n+1)).property) 0 N)
    (neg_valid (ScalarSeries.block_valid _ (fun n => (upperPairedReciprocalDerivative z hz (n+1)).property) 0 N))
    (ScalarSeries.block_congr _ _ (fun n => upperPairedReciprocalSquare_derivative z hz (n+1)) 0 N)
    (reciprocalSquare_block_neg _ (fun n => (upperPairedReciprocalDerivative z hz (n+1)).property) N)

end ComputableAnalysis.ModularForms
