import ComputableAnalysis.ModularForms.PairedGlobalOffPoleIntegerDomain

/-! Actual symmetric prefixes and explicit errors for the global off-pole value. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def globalOffPoleIntegerReciprocalClass (z : Scalar) (hz : pairedOffPoleDomain z) (k : Int) :
    ComplexRawQuotient.Value :=
  ComplexRawQuotient.ofRaw (globalOffPoleIntegerReciprocal z hz k).val
    (globalOffPoleIntegerReciprocal z hz k).property

def globalOffPoleSymmetricPrefix (z : Scalar) (hz : pairedOffPoleDomain z) (N : Nat) : ComplexRaw :=
  add (RepresentedReciprocal.inverse z hz.1).val
    (ScalarSeries.block (fun n => (pairedFullTerm z hz.2 n).val) 0 N)

theorem globalOffPoleSymmetricPrefix_valid (z : Scalar) (hz : pairedOffPoleDomain z) (N : Nat) :
    (globalOffPoleSymmetricPrefix z hz N).Valid :=
  add_valid (RepresentedReciprocal.inverse z hz.1).property
    (ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hz.2 n).property) 0 N)

theorem globalOffPoleFullTerm_class (z : Scalar) (hz : pairedOffPoleDomain z) (n : Nat) :
    ComplexRawQuotient.ofRaw (pairedFullTerm z hz.2 n).val (pairedFullTerm z hz.2 n).property =
      globalOffPoleIntegerReciprocalClass z hz (-((n+1:Nat):Int))+
        globalOffPoleIntegerReciprocalClass z hz ((n+1:Nat):Int) := by
  exact ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedFullTerm z hz.2 n).property)
    (hright := add_valid (globalOffPoleIntegerReciprocal z hz _).property
      (globalOffPoleIntegerReciprocal z hz _).property)
    (equiv_symm (pairedReciprocalOffPoleTermMap_full_agreement n z
      ⟨⟨trivial,pairedOffPoleDomain_integer_nonzero z hz _⟩,
        ⟨trivial,pairedOffPoleDomain_integer_nonzero z hz _⟩⟩ hz.2))

theorem globalOffPoleSymmetricPrefix_class (z : Scalar) (hz : pairedOffPoleDomain z) (N : Nat) :
    ComplexRawQuotient.ofRaw (globalOffPoleSymmetricPrefix z hz N)
      (globalOffPoleSymmetricPrefix_valid z hz N) =
      symmetricLatticeSum (globalOffPoleIntegerReciprocalClass z hz) N := by
  induction N with
  | zero =>
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (globalOffPoleIntegerReciprocal z hz 0).property)
      (hright := (RepresentedReciprocal.inverse z hz.1).property)
      (RepresentedReciprocal.inverse_congr _ _ _ _ (integerShiftScalar_zero_equiv z))
    change ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz.1).val
      (RepresentedReciprocal.inverse z hz.1).property+0=globalOffPoleIntegerReciprocalClass z hz 0
    change globalOffPoleIntegerReciprocalClass z hz 0=_ at hi
    grind only
  | succ N ih =>
    have ht := globalOffPoleFullTerm_class z hz N
    let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz.1).val
      (RepresentedReciprocal.inverse z hz.1).property
    let P := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => (pairedFullTerm z hz.2 n).val) 0 N)
      (ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hz.2 n).property) 0 N)
    let T := ComplexRawQuotient.ofRaw (pairedFullTerm z hz.2 N).val (pairedFullTerm z hz.2 N).property
    change I+P=symmetricLatticeSum (globalOffPoleIntegerReciprocalClass z hz) N at ih
    simp only [globalOffPoleSymmetricPrefix,ScalarSeries.block.eq_2,Nat.zero_add,symmetricLatticeSum.eq_2]
    change I+(P+T)=symmetricLatticeSum (globalOffPoleIntegerReciprocalClass z hz) N+
      globalOffPoleIntegerReciprocalClass z hz (-((N+1:Nat):Int))+
      globalOffPoleIntegerReciprocalClass z hz ((N+1:Nat):Int)
    change T=_ at ht
    rw [ht,← ih]
    grind only

theorem globalOffPoleSymmetricPrefix_close (z : Scalar) (hz : pairedOffPoleDomain z) (N : Nat) :
    Small (sub (pairedGlobalOffPoleAssemblyMap.eval z hz).val
      (globalOffPoleSymmetricPrefix z hz (4*pairedInternalBound z+(N+1))))
      (((16*pairedInternalBound z:Nat):Rat)*((N+1:Nat):Rat)⁻¹) := by
  let K := 4*pairedInternalBound z+(N+1)
  have hs := pairedFullValue_close z hz.2 (pairedInternalBound z) (pairedInternalBound_small z) N
  have he : (sub (pairedSeriesValue z hz.2)
      (ScalarSeries.block (fun n => (pairedFullTerm z hz.2 n).val) 0 K)).Equiv
      (sub (pairedPartialFractionValue z hz.1 hz.2) (globalOffPoleSymmetricPrefix z hz K)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedSeriesValue_valid z hz.2)
        (ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hz.2 n).property) 0 K))
      (hright := sub_valid (pairedPartialFractionValue_valid z hz.1 hz.2)
        (globalOffPoleSymmetricPrefix_valid z hz K))
    let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz.1).val
      (RepresentedReciprocal.inverse z hz.1).property
    let S := ComplexRawQuotient.ofRaw (pairedSeriesValue z hz.2) (pairedSeriesValue_valid z hz.2)
    let P := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => (pairedFullTerm z hz.2 n).val) 0 K)
      (ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hz.2 n).property) 0 K)
    change S-P=(I+S)-(I+P)
    grind only
  have hc := Small.congr
    (sub_valid (pairedSeriesValue_valid z hz.2)
      (ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hz.2 n).property) 0 K))
    (sub_valid (pairedPartialFractionValue_valid z hz.1 hz.2) (globalOffPoleSymmetricPrefix_valid z hz K)) he hs
  exact Small.congr
    (sub_valid (pairedPartialFractionValue_valid z hz.1 hz.2) (globalOffPoleSymmetricPrefix_valid z hz K))
    (sub_valid (pairedGlobalOffPoleAssemblyMap.eval z hz).property (globalOffPoleSymmetricPrefix_valid z hz K))
    (FunctionTheory.sub_congr (equiv_symm (pairedGlobalOffPoleAssemblyMap_canonicalValue z hz))
      (equiv_refl _ (globalOffPoleSymmetricPrefix_valid z hz K))) hc

theorem globalOffPoleSymmetricPrefix_shift_identity (z : Scalar) (hz : pairedOffPoleDomain z) (N : Nat) :
    (sub (globalOffPoleSymmetricPrefix (integerShiftScalar z 1) (pairedOffPoleDomain_shift z hz 1) N)
      (globalOffPoleSymmetricPrefix z hz N)).Equiv
      (sub (globalOffPoleIntegerReciprocal z hz ((N:Int)+1)).val
        (globalOffPoleIntegerReciprocal z hz (-(N:Int))).val) := by
  let w := integerShiftScalar z 1
  let hw := pairedOffPoleDomain_shift z hz 1
  have ht (j : Int) : globalOffPoleIntegerReciprocalClass w hw j=
      globalOffPoleIntegerReciprocalClass z hz (j+1) := by
    have h := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (globalOffPoleIntegerReciprocal w hw j).property)
      (hright := (globalOffPoleIntegerReciprocal z hz (1+j)).property)
      (globalOffPoleIntegerReciprocal_shift z hz 1 j)
    simpa only [globalOffPoleIntegerReciprocalClass,show (1:Int)+j=j+1 by omega] using h
  have hfun : globalOffPoleIntegerReciprocalClass w hw=
      (fun j => globalOffPoleIntegerReciprocalClass z hz (j+1)) := funext ht
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (globalOffPoleSymmetricPrefix_valid w hw N) (globalOffPoleSymmetricPrefix_valid z hz N))
    (hright := sub_valid (globalOffPoleIntegerReciprocal z hz ((N:Int)+1)).property
      (globalOffPoleIntegerReciprocal z hz (-(N:Int))).property)
  change ComplexRawQuotient.ofRaw (globalOffPoleSymmetricPrefix w hw N)
      (globalOffPoleSymmetricPrefix_valid w hw N)-
    ComplexRawQuotient.ofRaw (globalOffPoleSymmetricPrefix z hz N)
      (globalOffPoleSymmetricPrefix_valid z hz N)=
    globalOffPoleIntegerReciprocalClass z hz ((N:Int)+1)-globalOffPoleIntegerReciprocalClass z hz (-(N:Int))
  rw [globalOffPoleSymmetricPrefix_class,globalOffPoleSymmetricPrefix_class]
  change symmetricLatticeSum (globalOffPoleIntegerReciprocalClass w hw) N-
    symmetricLatticeSum (globalOffPoleIntegerReciprocalClass z hz) N=
    globalOffPoleIntegerReciprocalClass z hz ((N:Int)+1)-globalOffPoleIntegerReciprocalClass z hz (-(N:Int))
  rw [hfun,symmetricLatticeSum_shift]

end ComputableAnalysis.ModularForms
