import ComputableAnalysis.ModularForms.IndexedBoundaryDecay
import ComputableAnalysis.ModularForms.PairedLatticePrefixes

/-! Literal symmetric reciprocal sums represent the prefixes of the convergent paired series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def upperSymmetricReciprocalPrefix (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) : ComplexRaw :=
  add (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).val
    (upperPairedLatticePrefix z hz N)

theorem upperSymmetricReciprocalPrefix_valid (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    (upperSymmetricReciprocalPrefix z hz N).Valid :=
  add_valid (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).property
    (upperPairedLatticePrefix_valid z hz N)

theorem upperIntegerReciprocal_zero (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperIntegerReciprocal z hz 0).val.Equiv
      (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).val := by
  apply RepresentedReciprocal.inverse_congr
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerShiftScalar z 0).property) (hright := z.property)
  change ComplexRawQuotient.ofRaw (integerAffine 1 0 z.val) _ =
    ComplexRawQuotient.ofRaw z.val z.property
  rw [integerAffine_class]
  grind only

theorem upperPairedLatticeTerm_class (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) :
    ComplexRawQuotient.ofRaw (upperPairedLatticeTerm z hz n).val
      (upperPairedLatticeTerm z hz n).property =
      upperIntegerReciprocalClass z hz (-((n+1:Nat):Int)) +
        upperIntegerReciprocalClass z hz ((n+1:Nat):Int) := by
  have hm := RepresentedReciprocal.inverse_congr
    (pairedMinus z (boundaryIntegerScalar (n+1))) (integerShiftScalar z (-((n+1:Nat):Int)))
    (upperShiftMinus_nonzero z hz ((n+1:Nat):Rat))
    (upperScalar_nonzero _ (integerShiftScalar_upper z hz _))
    (equiv_symm (integerShiftScalar_minus z (n+1)))
  have hp := RepresentedReciprocal.inverse_congr
    (pairedPlus z (boundaryIntegerScalar (n+1))) (integerShiftScalar z ((n+1:Nat):Int))
    (upperShiftPlus_nonzero z hz ((n+1:Nat):Rat))
    (upperScalar_nonzero _ (integerShiftScalar_upper z hz _))
    (equiv_symm (integerShiftScalar_plus z (n+1)))
  have h := add_equiv hm hp
  exact ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (upperPairedLatticeTerm z hz n).property)
    (hright := add_valid (upperIntegerReciprocal z hz _).property
      (upperIntegerReciprocal z hz _).property) h

theorem upperSymmetricReciprocalPrefix_class (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    ComplexRawQuotient.ofRaw (upperSymmetricReciprocalPrefix z hz N)
      (upperSymmetricReciprocalPrefix_valid z hz N) =
      symmetricLatticeSum (upperIntegerReciprocalClass z hz) N := by
  induction N with
  | zero =>
    have h := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (upperIntegerReciprocal z hz 0).property)
      (hright := (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).property)
      (upperIntegerReciprocal_zero z hz)
    change ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).val
      (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).property + 0 =
      upperIntegerReciprocalClass z hz 0
    change upperIntegerReciprocalClass z hz 0 = _ at h
    grind only
  | succ N ih =>
    have ht := upperPairedLatticeTerm_class z hz N
    let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).val
      (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).property
    let B := ComplexRawQuotient.ofRaw (upperPairedLatticePrefix z hz N)
      (upperPairedLatticePrefix_valid z hz N)
    let T := ComplexRawQuotient.ofRaw (upperPairedLatticeTerm z hz N).val
      (upperPairedLatticeTerm z hz N).property
    change I+B=symmetricLatticeSum (upperIntegerReciprocalClass z hz) N at ih
    simp only [upperSymmetricReciprocalPrefix,upperPairedLatticePrefix,ScalarSeries.block.eq_2,
      Nat.zero_add,symmetricLatticeSum.eq_2]
    change I+(B+T)=symmetricLatticeSum (upperIntegerReciprocalClass z hz) N +
      upperIntegerReciprocalClass z hz (-((N+1:Nat):Int)) +
      upperIntegerReciprocalClass z hz ((N+1:Nat):Int)
    change T=upperIntegerReciprocalClass z hz (-((N+1:Nat):Int)) +
      upperIntegerReciprocalClass z hz ((N+1:Nat):Int) at ht
    rw [ht,← ih]
    grind only

theorem upperSymmetricReciprocalPrefix_close (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperPairedPartialFractionValue z hz)
      (upperSymmetricReciprocalPrefix z hz (4*pairedInternalBound z+(N+1))))
      (((16*pairedInternalBound z:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) := by
  have h := upperPairedLatticePrefix_close z hz N
  let K := 4*pairedInternalBound z+(N+1)
  have he : (sub (pairedSeriesValue z (upperPairedSeriesDomain z hz))
      (upperPairedLatticePrefix z hz K)).Equiv
      (sub (upperPairedPartialFractionValue z hz) (upperSymmetricReciprocalPrefix z hz K)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedSeriesValue_valid z (upperPairedSeriesDomain z hz))
        (upperPairedLatticePrefix_valid z hz K))
      (hright := sub_valid (upperPairedPartialFractionValue_valid z hz)
        (upperSymmetricReciprocalPrefix_valid z hz K))
    let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).val
      (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).property
    let S := ComplexRawQuotient.ofRaw (pairedSeriesValue z (upperPairedSeriesDomain z hz))
      (pairedSeriesValue_valid z (upperPairedSeriesDomain z hz))
    let P := ComplexRawQuotient.ofRaw (upperPairedLatticePrefix z hz K)
      (upperPairedLatticePrefix_valid z hz K)
    change S-P=(I+S)-(I+P)
    grind only
  exact Small.congr (sub_valid (pairedSeriesValue_valid z (upperPairedSeriesDomain z hz))
    (upperPairedLatticePrefix_valid z hz K))
    (sub_valid (upperPairedPartialFractionValue_valid z hz)
      (upperSymmetricReciprocalPrefix_valid z hz K)) he h

end ComputableAnalysis.ModularForms
