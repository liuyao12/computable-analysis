import ComputableAnalysis.ModularForms.UpperSquareDerivativeAgreement
import ComputableAnalysis.ModularForms.UpperLocalDerivativeTails

/-! Exact differences of the actual derivative shell prefixes. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory

private def blockValue (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (derivativeWeightFourTailBlock z hz N k) (derivativeWeightFourTailBlock_valid z hz N k)

private theorem blockValue_succ (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : blockValue z hz N (k+1)=
    blockValue z hz N k+ComplexRawQuotient.ofRaw
      (derivativeShellSum z hz (N+k+1) (by omega) 4)
      (derivativeShellPrefix_valid z hz _ _ 4 _) := rfl

private theorem blockValue_split (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : blockValue z hz 0 (N+k)=blockValue z hz 0 N+blockValue z hz N k := by
  induction k with
  | zero => exact (ComplexRawQuotient.add_zero _).symm
  | succ k ih =>
    have he : N+(k+1)=(N+k)+1 := by omega
    rw [he,blockValue_succ z hz,blockValue_succ z hz,ih]
    have hidx : 0+(N+k)+1=N+k+1 := by omega
    simp only [hidx]
    exact ComplexRawQuotient.add_assoc _ _ _


theorem derivativeWeightFourPrefix_difference (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) :
    (ComplexRaw.sub (derivativeWeightFourTailBlock z hz 0 (N+k)) (derivativeWeightFourTailBlock z hz 0 N)).Equiv
      (derivativeWeightFourTailBlock z hz N k) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.sub_valid (derivativeWeightFourTailBlock_valid z hz _ _) (derivativeWeightFourTailBlock_valid z hz _ _))
    (hright := derivativeWeightFourTailBlock_valid z hz _ _)
  change blockValue z hz 0 (N+k)+ -blockValue z hz 0 N=blockValue z hz N k
  rw [blockValue_split z hz N k, ComplexRawQuotient.add_comm (blockValue z hz 0 N) (blockValue z hz N k)]
  exact ScalarAlgebra.sub_add_cancel _ _

private def sixBlockValue (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (derivativeWeightSixTailBlock z hz N k) (derivativeWeightSixTailBlock_valid z hz N k)

private theorem sixBlockValue_succ (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : sixBlockValue z hz N (k+1)=
    sixBlockValue z hz N k+ComplexRawQuotient.ofRaw
      (derivativeShellSum z hz (N+k+1) (by omega) 6)
      (derivativeShellPrefix_valid z hz _ _ 6 _) := rfl

private theorem sixBlockValue_split (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : sixBlockValue z hz 0 (N+k)=sixBlockValue z hz 0 N+sixBlockValue z hz N k := by
  induction k with
  | zero => exact (ComplexRawQuotient.add_zero _).symm
  | succ k ih =>
    have he : N+(k+1)=(N+k)+1 := by omega
    rw [he,sixBlockValue_succ z hz,sixBlockValue_succ z hz,ih]
    have hidx : 0+(N+k)+1=N+k+1 := by omega
    simp only [hidx]
    exact ComplexRawQuotient.add_assoc _ _ _


theorem derivativeWeightSixPrefix_difference (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) :
    (ComplexRaw.sub (derivativeWeightSixTailBlock z hz 0 (N+k)) (derivativeWeightSixTailBlock z hz 0 N)).Equiv
      (derivativeWeightSixTailBlock z hz N k) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.sub_valid (derivativeWeightSixTailBlock_valid z hz _ _) (derivativeWeightSixTailBlock_valid z hz _ _))
    (hright := derivativeWeightSixTailBlock_valid z hz _ _)
  change sixBlockValue z hz 0 (N+k)+ -sixBlockValue z hz 0 N=sixBlockValue z hz N k
  rw [sixBlockValue_split z hz N k, ComplexRawQuotient.add_comm (sixBlockValue z hz 0 N) (sixBlockValue z hz N k)]
  exact ScalarAlgebra.sub_add_cancel _ _

theorem derivativeWeightFourPrefix_local_cauchy (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val)
    (k n : Nat) (hkn : k≤n) :
    Small (ComplexRaw.sub (derivativeWeightFourTailBlock z hz 0 (n+1))
      (derivativeWeightFourTailBlock z hz 0 (k+1))) (localDerivativeWeightFourTailRate a ha k) := by
  have he : (k+1)+(n-k)=n+1 := by omega
  have hd := derivativeWeightFourPrefix_difference z hz (k+1) (n-k)
  rw [he] at hd
  exact Small.congr (derivativeWeightFourTailBlock_valid z hz _ _)
    (ComplexRaw.sub_valid (derivativeWeightFourTailBlock_valid z hz _ _)
      (derivativeWeightFourTailBlock_valid z hz _ _))
    (ComplexRaw.equiv_symm hd)
    (derivativeWeightFourTailBlock_local_small a ha z hz hs k (n-k))

theorem derivativeWeightSixPrefix_local_cauchy (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val)
    (k n : Nat) (hkn : k≤n) :
    Small (ComplexRaw.sub (derivativeWeightSixTailBlock z hz 0 (n+1))
      (derivativeWeightSixTailBlock z hz 0 (k+1))) (localDerivativeWeightSixTailRate a ha k) := by
  have he : (k+1)+(n-k)=n+1 := by omega
  have hd := derivativeWeightSixPrefix_difference z hz (k+1) (n-k)
  rw [he] at hd
  exact Small.congr (derivativeWeightSixTailBlock_valid z hz _ _)
    (ComplexRaw.sub_valid (derivativeWeightSixTailBlock_valid z hz _ _)
      (derivativeWeightSixTailBlock_valid z hz _ _))
    (ComplexRaw.equiv_symm hd)
    (derivativeWeightSixTailBlock_local_small a ha z hz hs k (n-k))

end ComputableAnalysis.ModularForms
