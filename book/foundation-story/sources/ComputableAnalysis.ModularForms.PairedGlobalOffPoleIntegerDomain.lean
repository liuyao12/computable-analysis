import ComputableAnalysis.ModularForms.PairedGlobalOffPoleLaurentAgreement

/-! Exact integer-shift pole exclusions and actual reciprocal families on the global domain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions NonzeroBoxSearch

theorem pairedOffPoleDomain_integer_nonzero (z : Scalar) (hz : pairedOffPoleDomain z) (k : Int) :
    Nonzero (integerShiftScalar z k) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact (nonzero_congr _ _ (integerShiftScalar_zero_equiv z)).mpr hz.1
    | succ n =>
      exact (nonzero_congr _ _ (integerShiftScalar_plus z (n+1))).mpr
        (pairedSeriesDomain_factors z hz.2 n).2
  | negSucc n =>
    have h := (nonzero_congr _ _ (integerShiftScalar_minus z (n+1))).mpr
      (pairedSeriesDomain_factors z hz.2 n).1
    simpa only [show Int.negSucc n= -((n+1:Nat):Int) by omega] using h

theorem pairedOffPoleDomain_of_integer_nonzero (z : Scalar)
    (hz : ∀ k : Int, Nonzero (integerShiftScalar z k)) : pairedOffPoleDomain z := by
  refine ⟨(nonzero_congr _ _ (integerShiftScalar_zero_equiv z)).mp (hz 0),?_⟩
  intro n
  exact pairedReciprocalOffPoleTermMap_denominator_nonzero n z
    ⟨⟨trivial,hz (-((n+1:Nat):Int))⟩,⟨trivial,hz ((n+1:Nat):Int)⟩⟩

theorem pairedOffPoleDomain_integer_iff (z : Scalar) :
    pairedOffPoleDomain z ↔ ∀ k : Int, Nonzero (integerShiftScalar z k) :=
  ⟨pairedOffPoleDomain_integer_nonzero z,pairedOffPoleDomain_of_integer_nonzero z⟩

theorem pairedOffPoleDomain_shift (z : Scalar) (hz : pairedOffPoleDomain z) (k : Int) :
    pairedOffPoleDomain (integerShiftScalar z k) := by
  apply pairedOffPoleDomain_of_integer_nonzero
  intro j
  exact (nonzero_congr _ _ (integerShiftScalar_composition z k j)).mpr
    (pairedOffPoleDomain_integer_nonzero z hz (k+j))

def globalOffPoleIntegerReciprocal (z : Scalar) (hz : pairedOffPoleDomain z) (k : Int) : Scalar :=
  RepresentedReciprocal.inverse (integerShiftScalar z k) (pairedOffPoleDomain_integer_nonzero z hz k)

theorem globalOffPoleIntegerReciprocal_shift (z : Scalar) (hz : pairedOffPoleDomain z) (k j : Int) :
    (globalOffPoleIntegerReciprocal (integerShiftScalar z k) (pairedOffPoleDomain_shift z hz k) j).val.Equiv
      (globalOffPoleIntegerReciprocal z hz (k+j)).val :=
  RepresentedReciprocal.inverse_congr _ _ _ _ (integerShiftScalar_composition z k j)

end ComputableAnalysis.ModularForms
