import ComputableAnalysis.ModularForms.UpperDerivativePrefixDifference
import ComputableAnalysis.RiemannHilbert.RepresentedCauchySum

/-! Executable represented limits of the actual derivative prefixes. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory

def neighborhoodDerivativeWeightFourSum (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  RepresentedCauchySum.value (fun n => derivativeWeightFourTailBlock z hz 0 (n+1))
    (fun n => derivativeWeightFourTailBlock_valid z hz 0 (n+1))
    (localDerivativeWeightFourTailRate a ha)

theorem neighborhoodDerivativeWeightFourSum_valid (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val) :
    (neighborhoodDerivativeWeightFourSum a ha z hz).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (localDerivativeWeightFourTailRate_shrinks a ha)
    (derivativeWeightFourPrefix_local_cauchy a ha z hz hs)

theorem neighborhoodDerivativeWeightFourSum_close_prefix (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val) (n : Nat) :
    Small (ComplexRaw.sub (neighborhoodDerivativeWeightFourSum a ha z hz)
      (derivativeWeightFourTailBlock z hz 0 (n+1))) (localDerivativeWeightFourTailRate a ha n) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (derivativeWeightFourPrefix_local_cauchy a ha z hz hs) n

theorem neighborhoodDerivativeWeightFourSum_close_square_derivative
    (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val) (n : Nat) :
    Small (ComplexRaw.sub (neighborhoodDerivativeWeightFourSum a ha z hz)
      ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).derivative z hz).val)
      (localDerivativeWeightFourTailRate a ha n) := by
  have hv := neighborhoodDerivativeWeightFourSum_valid a ha z hz hs
  exact Small.congr (ComplexRaw.sub_valid hv (derivativeWeightFourTailBlock_valid z hz _ _))
    (ComplexRaw.sub_valid hv ((upperFiniteMap_holomorphic 4
      (QuadraticOrder163.squarePoints (n+1))).derivative z hz).property)
    (FunctionTheory.sub_congr (ComplexRaw.equiv_refl _ hv)
      (ComplexRaw.equiv_symm (upperSquareWeightFour_derivative_tailBlock z hz (n+1))))
    (neighborhoodDerivativeWeightFourSum_close_prefix a ha z hz hs n)

def neighborhoodDerivativeWeightSixSum (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  RepresentedCauchySum.value (fun n => derivativeWeightSixTailBlock z hz 0 (n+1))
    (fun n => derivativeWeightSixTailBlock_valid z hz 0 (n+1))
    (localDerivativeWeightSixTailRate a ha)

theorem neighborhoodDerivativeWeightSixSum_valid (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val) :
    (neighborhoodDerivativeWeightSixSum a ha z hz).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (localDerivativeWeightSixTailRate_shrinks a ha)
    (derivativeWeightSixPrefix_local_cauchy a ha z hz hs)

theorem neighborhoodDerivativeWeightSixSum_close_prefix (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val) (n : Nat) :
    Small (ComplexRaw.sub (neighborhoodDerivativeWeightSixSum a ha z hz)
      (derivativeWeightSixTailBlock z hz 0 (n+1))) (localDerivativeWeightSixTailRate a ha n) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (derivativeWeightSixPrefix_local_cauchy a ha z hz hs) n

theorem neighborhoodDerivativeWeightSixSum_close_square_derivative
    (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val) (n : Nat) :
    Small (ComplexRaw.sub (neighborhoodDerivativeWeightSixSum a ha z hz)
      ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).derivative z hz).val)
      (localDerivativeWeightSixTailRate a ha n) := by
  have hv := neighborhoodDerivativeWeightSixSum_valid a ha z hz hs
  exact Small.congr (ComplexRaw.sub_valid hv (derivativeWeightSixTailBlock_valid z hz _ _))
    (ComplexRaw.sub_valid hv ((upperFiniteMap_holomorphic 6
      (QuadraticOrder163.squarePoints (n+1))).derivative z hz).property)
    (FunctionTheory.sub_congr (ComplexRaw.equiv_refl _ hv)
      (ComplexRaw.equiv_symm (upperSquareWeightSix_derivative_tailBlock z hz (n+1))))
    (neighborhoodDerivativeWeightSixSum_close_prefix a ha z hz hs n)

end ComputableAnalysis.ModularForms
