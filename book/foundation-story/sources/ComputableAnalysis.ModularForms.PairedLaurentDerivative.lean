import ComputableAnalysis.ModularForms.PairedLaurentCharts

/-! Exact principal part and bounded regular term of the Laurent-chart derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedZeroLaurentMap_derivative (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    (pairedZeroLaurentMap_holomorphic.derivative z hz).val.Equiv
      (add (ReciprocalDifference.derivative z hz.2).val (pairedRegularPartDerivative z hz.1).val) :=
  equiv_refl _ (pairedZeroLaurentMap_holomorphic.derivative z hz).property

private theorem laurentDerivativeSquareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem laurentDerivativeSquareBlock_zero_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [laurentDerivativeSquareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only

theorem pairedSmallDiskDerivativeValue_bound (z : Scalar) (hz : Small z.val (1/4)) :
    Small (pairedSmallDiskDerivativeValue z hz) 2048 := by
  let t := fun n => (pairedSmallDiskDerivativeTerm z hz n).val
  have ht : ∀ n, (t n).Valid := fun n => (pairedSmallDiskDerivativeTerm z hz n).property
  apply SeriesLimitLaws.small_of_prefix_bound _ (pairedSmallDiskDerivativeValue_valid z hz)
    (fun N => ScalarSeries.block t 0 (N+1)) (fun N => ScalarSeries.block_valid t ht 0 (N+1))
    2048 (fun N => ((1024:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) (pairedReciprocalTail_shrinks 1024)
  · exact pairedSmallDiskDerivativeValue_close z hz
  · intro N
    apply (inverseSquare_block_bound t 1024 (pairedSmallDiskDerivativeTerm_bound z hz) 0 (N+1)).mono
    have h := Rat.mul_le_mul_of_nonneg_left (laurentDerivativeSquareBlock_zero_bound (N+1))
      (show (0:Rat)≤1024 by decide)
    simpa only [show ((1024:Nat):Rat)=1024 by decide +kernel, show (1024:Rat)*2=2048 by decide +kernel] using h

theorem pairedZeroLaurentMap_regular_derivative_bound (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    Small (sub (pairedZeroLaurentMap_holomorphic.derivative z hz).val
      (ReciprocalDifference.derivative z hz.2).val) 2048 := by
  have he : (sub (pairedZeroLaurentMap_holomorphic.derivative z hz).val
      (ReciprocalDifference.derivative z hz.2).val).Equiv (pairedRegularPartDerivative z hz.1).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedZeroLaurentMap_holomorphic.derivative z hz).property
        (ReciprocalDifference.derivative z hz.2).property)
      (hright := (pairedRegularPartDerivative z hz.1).property)
    let I := ComplexRawQuotient.ofRaw (ReciprocalDifference.derivative z hz.2).val
      (ReciprocalDifference.derivative z hz.2).property
    let D := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz.1).val (pairedRegularPartDerivative z hz.1).property
    change (I+D)-I=D
    grind only
  exact Small.congr (pairedRegularPartDerivative z hz.1).property
    (sub_valid (pairedZeroLaurentMap_holomorphic.derivative z hz).property (ReciprocalDifference.derivative z hz.2).property)
    (equiv_symm he) (pairedSmallDiskDerivativeValue_bound z (LocalODE.interior_bound _ z hz.1))

end ComputableAnalysis.ModularForms
