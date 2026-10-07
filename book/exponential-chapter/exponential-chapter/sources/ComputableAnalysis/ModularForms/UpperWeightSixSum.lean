import ComputableAnalysis.ModularForms.UpperWeightSixTails
import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws
import ComputableAnalysis.RiemannHilbert.RepresentedCauchySum

/-! Constructed weight-six lattice sum at every represented upper-half-plane input. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory
set_option maxRecDepth 8192

def upperWeightSixTailRate (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) : Rat :=
  upperWeightSixTailConstant z hz*reciprocalSquare (n+1)

theorem upperWeightSixTailRate_shrinks (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ShrinksToZero (upperWeightSixTailRate z hz) := by
  have he : ShrinksToZero (fun n => reciprocalSquare (n+1)) := by
    apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    change reciprocalSquare (n+1)≤1/((n+1:Nat):Rat)
    exact reciprocalSquare_le_reciprocal (n+1) (by omega)
  have hC : 0≤upperWeightSixTailConstant z hz := by
    unfold upperWeightSixTailConstant
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg
      (Rat.mul_nonneg (by decide) (latticeReciprocalConstant_nonnegative z hz)))
  exact SeriesLimitLaws.shrinks_scale (fun n => reciprocalSquare (n+1)) he
    (upperWeightSixTailConstant z hz) hC


private def blockValue (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (upperWeightSixTailBlock z hz N k) (upperWeightSixTailBlock_valid z hz N k)

private theorem blockValue_succ (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) : blockValue z hz N (k+1)=
    blockValue z hz N k+ComplexRawQuotient.ofRaw
      (upperShellSum z hz (N+k+1) (by omega) 6)
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


theorem upperWeightSixPrefix_difference (z : Scalar) (hz : InUpperHalfPlane z.val) (N k : Nat) :
    (ComplexRaw.sub (upperWeightSixTailBlock z hz 0 (N+k)) (upperWeightSixTailBlock z hz 0 N)).Equiv
      (upperWeightSixTailBlock z hz N k) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.sub_valid (upperWeightSixTailBlock_valid z hz _ _) (upperWeightSixTailBlock_valid z hz _ _))
    (hright := upperWeightSixTailBlock_valid z hz _ _)
  change blockValue z hz 0 (N+k)+ -blockValue z hz 0 N=blockValue z hz N k
  rw [blockValue_split z hz N k, ComplexRawQuotient.add_comm (blockValue z hz 0 N) (blockValue z hz N k)]
  exact ScalarAlgebra.sub_add_cancel _ _

def upperWeightSixPrefix (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) : ComplexRaw := upperWeightSixTailBlock z hz 0 (n+1)

theorem upperWeightSixPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) : (upperWeightSixPrefix z hz n).Valid := upperWeightSixTailBlock_valid z hz _ _

theorem upperWeightSixPrefix_cauchy (z : Scalar) (hz : InUpperHalfPlane z.val) (k n : Nat) (hkn : k≤n) :
    Small (ComplexRaw.sub (upperWeightSixPrefix z hz n) (upperWeightSixPrefix z hz k)) (upperWeightSixTailRate z hz k) := by
  have he : (k+1)+(n-k)=n+1 := by omega
  have h := upperWeightSixPrefix_difference z hz (k+1) (n-k)
  rw [he] at h
  exact Small.congr (upperWeightSixTailBlock_valid z hz _ _)
    (ComplexRaw.sub_valid (upperWeightSixPrefix_valid z hz n) (upperWeightSixPrefix_valid z hz k))
    (ComplexRaw.equiv_symm h) (upperWeightSixTailBlock_uniform_small z hz (k+1) (n-k) (by omega))


def upperWeightSixLatticeSum (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  RepresentedCauchySum.value (upperWeightSixPrefix z hz) (upperWeightSixPrefix_valid z hz) (upperWeightSixTailRate z hz)

theorem upperWeightSixLatticeSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val) : (upperWeightSixLatticeSum z hz).Valid :=
  RepresentedCauchySum.value_valid (upperWeightSixPrefix z hz) (upperWeightSixPrefix_valid z hz)
    (upperWeightSixTailRate z hz) (upperWeightSixTailRate_shrinks z hz) (upperWeightSixPrefix_cauchy z hz)

theorem upperWeightSixLatticeSum_close_prefix (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (ComplexRaw.sub (upperWeightSixLatticeSum z hz) (upperWeightSixPrefix z hz N)) (upperWeightSixTailRate z hz N) :=
  RepresentedCauchySum.value_close_prefix (upperWeightSixPrefix z hz) (upperWeightSixPrefix_valid z hz)
    (upperWeightSixTailRate z hz) (upperWeightSixPrefix_cauchy z hz) N

end ComputableAnalysis.ModularForms
