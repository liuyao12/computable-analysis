import ComputableAnalysis.ModularForms.UpperDerivativeContinuity
import ComputableAnalysis.ModularForms.UpperLocalValueTails
import ComputableAnalysis.ModularForms.UpperLatticeSumCongruence
import ComputableAnalysis.ModularForms.UpperSquarePrefixAgreement
import ComputableAnalysis.RiemannHilbert.DomainRemainderComparison

/-! Actual full lattice-map remainders approach the certified finite remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def upperWeightFourLatticeMap : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨upperWeightFourLatticeSum z hz,upperWeightFourLatticeSum_valid z hz⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := upperWeightFourLatticeSum_congr z w hz hw he

theorem upperWeightFourLatticeSum_local_close_square
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val) (n : Nat) :
    Small (sub (upperWeightFourLatticeSum z hz)
      ((upperFiniteMap 4 (QuadraticOrder163.squarePoints (n+1))).eval z hz).val)
      (localWeightFourTailRate a ha n) := by
  have hv := upperWeightFourLatticeSum_valid z hz
  exact Small.congr (sub_valid hv (upperWeightFourPrefix_valid z hz n))
    (sub_valid hv ((upperFiniteMap 4 (QuadraticOrder163.squarePoints (n+1))).eval z hz).property)
    (FunctionTheory.sub_congr (equiv_refl _ hv)
      (equiv_symm (upperSquareWeightFour_prefix_equiv z hz n)))
    (upperWeightFourLatticeSum_local_close_prefix a ha z hz hs n)

theorem upperWeightFourLatticeMap_remainder_close_finite
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val)
    (H : QPos) (hza : Small (sub z.val a.val) H.val) (n : Nat) :
    Small (sub (remainder upperWeightFourLatticeMap a ha ⟨_,derivativeWeightFourSum_valid a ha⟩ z hz)
      (remainder (upperFiniteMap 4 (QuadraticOrder163.squarePoints (n+1))) a ha
        ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).derivative a ha) z hz))
      (localWeightFourTailRate a ha n+localWeightFourTailRate a ha n+
        2*localDerivativeWeightFourTailRate a ha n*H.val) := by
  exact remainder_comparison_bound _ _ a z ha hz ha hz _ _ _ _ _ _
    (localDerivativeWeightFourTailRate_nonnegative a ha n) (Rat.le_of_lt H.property)
    (upperWeightFourLatticeSum_local_close_square a ha z hz hs n)
    (upperWeightFourLatticeSum_local_close_square a ha a ha (upperSelf_near a ha) n)
    (derivativeWeightFourSum_local_close_square_derivative a ha a ha (upperSelf_near a ha) n) hza

def upperWeightSixLatticeMap : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨upperWeightSixLatticeSum z hz,upperWeightSixLatticeSum_valid z hz⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := upperWeightSixLatticeSum_congr z w hz hw he

theorem upperWeightSixLatticeSum_local_close_square
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val) (n : Nat) :
    Small (sub (upperWeightSixLatticeSum z hz)
      ((upperFiniteMap 6 (QuadraticOrder163.squarePoints (n+1))).eval z hz).val)
      (localWeightSixTailRate a ha n) := by
  have hv := upperWeightSixLatticeSum_valid z hz
  exact Small.congr (sub_valid hv (upperWeightSixPrefix_valid z hz n))
    (sub_valid hv ((upperFiniteMap 6 (QuadraticOrder163.squarePoints (n+1))).eval z hz).property)
    (FunctionTheory.sub_congr (equiv_refl _ hv)
      (equiv_symm (upperSquareWeightSix_prefix_equiv z hz n)))
    (upperWeightSixLatticeSum_local_close_prefix a ha z hz hs n)

theorem upperWeightSixLatticeMap_remainder_close_finite
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val)
    (H : QPos) (hza : Small (sub z.val a.val) H.val) (n : Nat) :
    Small (sub (remainder upperWeightSixLatticeMap a ha ⟨_,derivativeWeightSixSum_valid a ha⟩ z hz)
      (remainder (upperFiniteMap 6 (QuadraticOrder163.squarePoints (n+1))) a ha
        ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).derivative a ha) z hz))
      (localWeightSixTailRate a ha n+localWeightSixTailRate a ha n+
        2*localDerivativeWeightSixTailRate a ha n*H.val) := by
  exact remainder_comparison_bound _ _ a z ha hz ha hz _ _ _ _ _ _
    (localDerivativeWeightSixTailRate_nonnegative a ha n) (Rat.le_of_lt H.property)
    (upperWeightSixLatticeSum_local_close_square a ha z hz hs n)
    (upperWeightSixLatticeSum_local_close_square a ha a ha (upperSelf_near a ha) n)
    (derivativeWeightSixSum_local_close_square_derivative a ha a ha (upperSelf_near a ha) n) hza

end ComputableAnalysis.ModularForms
