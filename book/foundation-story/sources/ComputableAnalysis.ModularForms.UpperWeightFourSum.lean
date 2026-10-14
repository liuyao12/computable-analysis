import ComputableAnalysis.ModularForms.UpperWeightFourTails
import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws
import ComputableAnalysis.RiemannHilbert.RepresentedCauchySum

/-! Constructed weight-four lattice sum at every represented upper-half-plane input. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory
set_option maxRecDepth 8192

def upperWeightFourTailRate (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) : Rat :=
  upperWeightFourTailConstant z hz*reciprocalSquare (n+1)

theorem upperWeightFourTailRate_shrinks (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ShrinksToZero (upperWeightFourTailRate z hz) := by
  have he : ShrinksToZero (fun n => reciprocalSquare (n+1)) := by
    apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    change reciprocalSquare (n+1)≤1/((n+1:Nat):Rat)
    exact reciprocalSquare_le_reciprocal (n+1) (by omega)
  have hC : 0≤upperWeightFourTailConstant z hz := by
    unfold upperWeightFourTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz)))
  exact SeriesLimitLaws.shrinks_scale (fun n => reciprocalSquare (n+1)) he
    (upperWeightFourTailConstant z hz) hC


private def blockValue (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (upperWeightFourTailBlock z hz N k) (upperWeightFourTailBlock_valid z hz N k)

private theorem blockValue_succ (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : blockValue z hz N (k+1)=
    blockValue z hz N k+ComplexRawQuotient.ofRaw
      (upperShellSum z hz (N+k+1) (by omega) 4)
      (upperShellSum_valid z hz _ _ _) := rfl

private theorem blockValue_split (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : blockValue z hz 0 (N+k)=blockValue z hz 0 N+blockValue z hz N k := by
  induction k with
  | zero => exact (ComplexRawQuotient.add_zero _).symm
  | succ k ih =>
    have he : N+(k+1)=(N+k)+1 := by omega
    rw [he,blockValue_succ z hz,blockValue_succ z hz,ih]
    have hidx : 0+(N+k)+1=N+k+1 := by omega
    simp only [hidx]
    exact ComplexRawQuotient.add_assoc _ _ _


theorem upperWeightFourPrefix_difference (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) :
    (ComplexRaw.sub (upperWeightFourTailBlock z hz 0 (N+k)) (upperWeightFourTailBlock z hz 0 N)).Equiv
      (upperWeightFourTailBlock z hz N k) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.sub_valid (upperWeightFourTailBlock_valid z hz _ _) (upperWeightFourTailBlock_valid z hz _ _))
    (hright := upperWeightFourTailBlock_valid z hz _ _)
  change blockValue z hz 0 (N+k)+ -blockValue z hz 0 N=blockValue z hz N k
  rw [blockValue_split z hz N k, ComplexRawQuotient.add_comm (blockValue z hz 0 N) (blockValue z hz N k)]
  exact ScalarAlgebra.sub_add_cancel _ _

def upperWeightFourPrefix (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) : ComplexRaw := upperWeightFourTailBlock z hz 0 (n+1)

theorem upperWeightFourPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) : (upperWeightFourPrefix z hz n).Valid := upperWeightFourTailBlock_valid z hz _ _

theorem upperWeightFourPrefix_cauchy (z : Scalar) (hz : InUpperHalfPlane z.val) (k n : Nat) (hkn : k≤n) :
    Small (ComplexRaw.sub (upperWeightFourPrefix z hz n) (upperWeightFourPrefix z hz k)) (upperWeightFourTailRate z hz k) := by
  have he : (k+1)+(n-k)=n+1 := by omega
  have h := upperWeightFourPrefix_difference z hz (k+1) (n-k)
  rw [he] at h
  exact Small.congr (upperWeightFourTailBlock_valid z hz _ _)
    (ComplexRaw.sub_valid (upperWeightFourPrefix_valid z hz n) (upperWeightFourPrefix_valid z hz k))
    (ComplexRaw.equiv_symm h) (upperWeightFourTailBlock_uniform_small z hz (k+1) (n-k) (by omega))


def upperWeightFourLatticeSum (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  RepresentedCauchySum.value (upperWeightFourPrefix z hz) (upperWeightFourPrefix_valid z hz) (upperWeightFourTailRate z hz)

theorem upperWeightFourLatticeSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val) : (upperWeightFourLatticeSum z hz).Valid :=
  RepresentedCauchySum.value_valid (upperWeightFourPrefix z hz) (upperWeightFourPrefix_valid z hz)
    (upperWeightFourTailRate z hz) (upperWeightFourTailRate_shrinks z hz) (upperWeightFourPrefix_cauchy z hz)

theorem upperWeightFourLatticeSum_close_prefix (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (ComplexRaw.sub (upperWeightFourLatticeSum z hz) (upperWeightFourPrefix z hz N)) (upperWeightFourTailRate z hz N) :=
  RepresentedCauchySum.value_close_prefix (upperWeightFourPrefix z hz) (upperWeightFourPrefix_valid z hz)
    (upperWeightFourTailRate z hz) (upperWeightFourPrefix_cauchy z hz) N

end ComputableAnalysis.ModularForms
