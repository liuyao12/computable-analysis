import ComputableAnalysis.ModularForms.UpperDerivativeCenterIndependence

/-! Representation invariance of the constructed derivative sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory

theorem derivativeWeightFourTailBlock_zero_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (he : z.val.Equiv w.val) (N : Nat) :
    (derivativeWeightFourTailBlock z hz 0 N).Equiv
      (derivativeWeightFourTailBlock w hw 0 N) := by
  have hd := (upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints N)).derivative_congr
    z w hz hw he
  exact ComplexRaw.equiv_trans (derivativeWeightFourTailBlock_valid z hz 0 N)
    ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints N)).derivative z hz).property
    (derivativeWeightFourTailBlock_valid w hw 0 N)
    (ComplexRaw.equiv_symm (upperSquareWeightFour_derivative_tailBlock z hz N))
    (ComplexRaw.equiv_trans
      ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints N)).derivative z hz).property
      ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints N)).derivative w hw).property
      (derivativeWeightFourTailBlock_valid w hw 0 N) hd
      (upperSquareWeightFour_derivative_tailBlock w hw N))

theorem derivativeWeightFourSum_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (he : z.val.Equiv w.val) :
    (derivativeWeightFourSum z hz).Equiv (derivativeWeightFourSum w hw) := by
  apply RepresentedCauchySum.value_congr
    (fun n => derivativeWeightFourTailBlock z hz 0 (n+1))
    (fun n => derivativeWeightFourTailBlock w hw 0 (n+1))
    (fun n => derivativeWeightFourTailBlock_valid z hz 0 (n+1))
    (fun n => derivativeWeightFourTailBlock_valid w hw 0 (n+1))
    (localDerivativeWeightFourTailRate z hz) (localDerivativeWeightFourTailRate w hw)
    (localDerivativeWeightFourTailRate_shrinks z hz) (localDerivativeWeightFourTailRate_shrinks w hw)
    (localDerivativeWeightFourTailRate_nonnegative z hz) (localDerivativeWeightFourTailRate_nonnegative w hw)
    (derivativeWeightFourPrefix_local_cauchy z hz z hz (upperSelf_near z hz))
    (derivativeWeightFourPrefix_local_cauchy w hw w hw (upperSelf_near w hw))
  intro n
  exact derivativeWeightFourTailBlock_zero_congr z w hz hw he (n+1)

theorem derivativeWeightSixTailBlock_zero_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (he : z.val.Equiv w.val) (N : Nat) :
    (derivativeWeightSixTailBlock z hz 0 N).Equiv
      (derivativeWeightSixTailBlock w hw 0 N) := by
  have hd := (upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints N)).derivative_congr
    z w hz hw he
  exact ComplexRaw.equiv_trans (derivativeWeightSixTailBlock_valid z hz 0 N)
    ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints N)).derivative z hz).property
    (derivativeWeightSixTailBlock_valid w hw 0 N)
    (ComplexRaw.equiv_symm (upperSquareWeightSix_derivative_tailBlock z hz N))
    (ComplexRaw.equiv_trans
      ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints N)).derivative z hz).property
      ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints N)).derivative w hw).property
      (derivativeWeightSixTailBlock_valid w hw 0 N) hd
      (upperSquareWeightSix_derivative_tailBlock w hw N))

theorem derivativeWeightSixSum_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (he : z.val.Equiv w.val) :
    (derivativeWeightSixSum z hz).Equiv (derivativeWeightSixSum w hw) := by
  apply RepresentedCauchySum.value_congr
    (fun n => derivativeWeightSixTailBlock z hz 0 (n+1))
    (fun n => derivativeWeightSixTailBlock w hw 0 (n+1))
    (fun n => derivativeWeightSixTailBlock_valid z hz 0 (n+1))
    (fun n => derivativeWeightSixTailBlock_valid w hw 0 (n+1))
    (localDerivativeWeightSixTailRate z hz) (localDerivativeWeightSixTailRate w hw)
    (localDerivativeWeightSixTailRate_shrinks z hz) (localDerivativeWeightSixTailRate_shrinks w hw)
    (localDerivativeWeightSixTailRate_nonnegative z hz) (localDerivativeWeightSixTailRate_nonnegative w hw)
    (derivativeWeightSixPrefix_local_cauchy z hz z hz (upperSelf_near z hz))
    (derivativeWeightSixPrefix_local_cauchy w hw w hw (upperSelf_near w hw))
  intro n
  exact derivativeWeightSixTailBlock_zero_congr z w hz hw he (n+1)

def derivativeWeightFourMap : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨derivativeWeightFourSum z hz,derivativeWeightFourSum_valid z hz⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := derivativeWeightFourSum_congr z w hz hw he

theorem derivativeWeightFourSum_local_close_square_derivative
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val) (n : Nat) :
    Small (ComplexRaw.sub (derivativeWeightFourSum z hz)
      ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).derivative z hz).val)
      (localDerivativeWeightFourTailRate a ha n) := by
  have hv := ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).derivative z hz).property
  exact Small.congr
    (ComplexRaw.sub_valid (neighborhoodDerivativeWeightFourSum_valid a ha z hz hs) hv)
    (ComplexRaw.sub_valid (derivativeWeightFourSum_valid z hz) hv)
    (FunctionTheory.sub_congr
      (ComplexRaw.equiv_symm (derivativeWeightFourSum_neighborhood_agreement a ha z hz hs))
      (ComplexRaw.equiv_refl _ hv))
    (neighborhoodDerivativeWeightFourSum_close_square_derivative a ha z hz hs n)

def derivativeWeightSixMap : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨derivativeWeightSixSum z hz,derivativeWeightSixSum_valid z hz⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := derivativeWeightSixSum_congr z w hz hw he

theorem derivativeWeightSixSum_local_close_square_derivative
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val) (n : Nat) :
    Small (ComplexRaw.sub (derivativeWeightSixSum z hz)
      ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).derivative z hz).val)
      (localDerivativeWeightSixTailRate a ha n) := by
  have hv := ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).derivative z hz).property
  exact Small.congr
    (ComplexRaw.sub_valid (neighborhoodDerivativeWeightSixSum_valid a ha z hz hs) hv)
    (ComplexRaw.sub_valid (derivativeWeightSixSum_valid z hz) hv)
    (FunctionTheory.sub_congr
      (ComplexRaw.equiv_symm (derivativeWeightSixSum_neighborhood_agreement a ha z hz hs))
      (ComplexRaw.equiv_refl _ hv))
    (neighborhoodDerivativeWeightSixSum_close_square_derivative a ha z hz hs n)

end ComputableAnalysis.ModularForms
