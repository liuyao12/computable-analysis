import ComputableAnalysis.ModularForms.PairedOffPoleSecondDerivativeAgreement
import ComputableAnalysis.ModularForms.PairedCutoffAgreement
import ComputableAnalysis.ModularForms.PairedFactorDomain

/-! Cutoff independence of the actual lattice assemblies on their full common domain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions NonzeroBoxSearch

theorem pairedFiniteOffPoleMap_term_mem (N n : Nat) (z : Scalar)
    (hz : (pairedFiniteOffPoleMap N).domain z) (hn : n<N) :
    (pairedReciprocalOffPoleTermMap n).domain z := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h : n<N
    · exact ih hz.1 h
    · have he : n=N := by omega
      subst n
      exact hz.2

theorem pairedReciprocalOffPoleTermMap_denominator_nonzero (n : Nat) (z : Scalar)
    (hz : (pairedReciprocalOffPoleTermMap n).domain z) :
    Nonzero (pairedLiteralDenominator z (pairedIntegerSquare (n+1))) := by
  have hm := (nonzero_congr _ _ (integerShiftScalar_minus z (n+1))).mp hz.1.2
  have hp := (nonzero_congr _ _ (integerShiftScalar_plus z (n+1))).mp hz.2.2
  have he : (pairedProduct z (boundaryIntegerScalar (n+1))).val.Equiv
      (pairedLiteralDenominator z (pairedIntegerSquare (n+1))).val :=
    FunctionTheory.sub_congr (equiv_refl _ (mul_valid z.property z.property))
      (rationalRealSquare_equiv ((n+1:Nat):Rat))
  exact (nonzero_congr _ _ he).mp (pairedProduct_nonzero z (boundaryIntegerScalar (n+1)) hm hp)

theorem pairedOffPoleAssemblyMap_seriesDomain (B : Nat) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z) : PairedSeriesDomain z := by
  intro n
  by_cases hn : n<4*B
  · exact pairedReciprocalOffPoleTermMap_denominator_nonzero n z
      (pairedFiniteOffPoleMap_term_mem (4*B) n z hz.2.1 hn)
  · have he : pairedTailShift B (n-4*B)=n+1 := by unfold pairedTailShift; omega
    exact pairedIntegerDenominator_nonzero z (B:Rat) (n+1) Rat.natCast_nonneg
      (LocalODE.interior_bound _ z hz.2.2) (by omega)
      (by rw [← he]; exact pairedTailShift_large B (n-4*B))

theorem pairedReciprocalOffPoleTermMap_full_agreement (n : Nat) (z : Scalar)
    (hz : (pairedReciprocalOffPoleTermMap n).domain z) (hd : PairedSeriesDomain z) :
    ((pairedReciprocalOffPoleTermMap n).eval z hz).val.Equiv (pairedFullTerm z hd n).val := by
  let a := boundaryIntegerScalar (n+1)
  have hm := (nonzero_congr _ _ (integerShiftScalar_minus z (n+1))).mp hz.1.2
  have hp := (nonzero_congr _ _ (integerShiftScalar_plus z (n+1))).mp hz.2.2
  have hmi := RepresentedReciprocal.inverse_congr _ _ hz.1.2 hm (integerShiftScalar_minus z (n+1))
  have hpi := RepresentedReciprocal.inverse_congr _ _ hz.2.2 hp (integerShiftScalar_plus z (n+1))
  have hsum : ((pairedReciprocalOffPoleTermMap n).eval z hz).val.Equiv
      (pairedReciprocal z a hm hp).val := add_equiv hmi hpi
  have hi := RepresentedReciprocal.inverse_congr (pairedProduct z a)
    (pairedLiteralDenominator z (pairedIntegerSquare (n+1)))
    (pairedProduct_nonzero z a hm hp) (hd n)
    (FunctionTheory.sub_congr (equiv_refl _ (mul_valid z.property z.property))
      (rationalRealSquare_equiv ((n+1:Nat):Rat)))
  have hq := mul_equiv (add_valid z.property z.property) (add_valid z.property z.property)
    (RepresentedReciprocal.inverse _ (pairedProduct_nonzero z a hm hp)).property
    (RepresentedReciprocal.inverse _ (hd n)).property (equiv_refl _ (add_valid z.property z.property)) hi
  exact equiv_trans ((pairedReciprocalOffPoleTermMap n).eval z hz).property
    (pairedReciprocal z a hm hp).property (pairedFullTerm z hd n).property hsum
    (equiv_trans (pairedReciprocal z a hm hp).property (pairedQuotient z a hm hp).property
      (pairedFullTerm z hd n).property (pairedReciprocal_quotient z a hm hp) hq)

theorem pairedFiniteOffPoleMap_full_agreement (N : Nat) (z : Scalar)
    (hz : (pairedFiniteOffPoleMap N).domain z) (hd : PairedSeriesDomain z) :
    ((pairedFiniteOffPoleMap N).eval z hz).val.Equiv
      (ScalarSeries.block (fun n => (pairedFullTerm z hd n).val) 0 N) := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((pairedFiniteOffPoleMap 0).eval z hz).property)
      (hright := ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hd n).property) 0 0)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change 0+0*Z=0
    grind only
  | succ N ih =>
    have h := add_equiv (ih hz.1) (pairedReciprocalOffPoleTermMap_full_agreement N z hz.2 hd)
    simpa only [pairedFiniteOffPoleMap,intersectionSum,scalarSum,ScalarSeries.block.eq_2,Nat.zero_add] using h

theorem pairedOffPoleAssemblyMap_cutoff_agreement (B C : Nat) (z : Scalar)
    (hB : (pairedOffPoleAssemblyMap B).domain z) (hC : (pairedOffPoleAssemblyMap C).domain z) :
    ((pairedOffPoleAssemblyMap B).eval z hB).val.Equiv
      ((pairedOffPoleAssemblyMap C).eval z hC).val := by
  let hd := pairedOffPoleAssemblyMap_seriesDomain B z hB
  have hb := add_equiv (pairedFiniteOffPoleMap_full_agreement (4*B) z hB.2.1 hd)
    (equiv_refl _ ((pairedOffPoleTailMap B).eval z hB.2.2).property)
  have hc := add_equiv (pairedFiniteOffPoleMap_full_agreement (4*C) z hC.2.1 hd)
    (equiv_refl _ ((pairedOffPoleTailMap C).eval z hC.2.2).property)
  have he := equiv_trans
    (add_valid ((pairedFiniteOffPoleMap (4*B)).eval z hB.2.1).property ((pairedOffPoleTailMap B).eval z hB.2.2).property)
    (pairedFullValue_valid z hd B (LocalODE.interior_bound _ z hB.2.2))
    (add_valid ((pairedFiniteOffPoleMap (4*C)).eval z hC.2.1).property ((pairedOffPoleTailMap C).eval z hC.2.2).property)
    hb (equiv_trans (pairedFullValue_valid z hd B (LocalODE.interior_bound _ z hB.2.2))
      (pairedFullValue_valid z hd C (LocalODE.interior_bound _ z hC.2.2))
      (add_valid ((pairedFiniteOffPoleMap (4*C)).eval z hC.2.1).property ((pairedOffPoleTailMap C).eval z hC.2.2).property)
      (pairedFullValue_cutoff z hd B C (LocalODE.interior_bound _ z hB.2.2) (LocalODE.interior_bound _ z hC.2.2))
      (equiv_symm hc))
  exact add_equiv (equiv_refl _ ((integerReciprocalOffPoleMap 0).eval z hB.1).property) he

end ComputableAnalysis.ModularForms
