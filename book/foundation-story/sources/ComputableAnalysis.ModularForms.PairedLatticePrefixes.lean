import ComputableAnalysis.ModularForms.PairedUpperDomain

/-! Literal symmetric lattice prefixes agree with the constructed quotient prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def upperPairedLatticeTerm (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) : Scalar :=
  pairedReciprocal z ⟨ofQComplex ⟨((n+1:Nat):Rat),0⟩,ofQComplex_valid _⟩
    (upperShiftMinus_nonzero z hz ((n+1:Nat):Rat)) (upperShiftPlus_nonzero z hz ((n+1:Nat):Rat))

theorem upperPairedLatticeTerm_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) (n : Nat) :
    (upperPairedLatticeTerm z hz n).val.Equiv
      (pairedFullTerm z (upperPairedSeriesDomain z hz) n).val := by
  let a : Scalar := ⟨ofQComplex ⟨((n+1:Nat):Rat),0⟩,ofQComplex_valid _⟩
  let hm := upperShiftMinus_nonzero z hz ((n+1:Nat):Rat)
  let hp := upperShiftPlus_nonzero z hz ((n+1:Nat):Rat)
  have hi := RepresentedReciprocal.inverse_congr (pairedProduct z a)
    (pairedLiteralDenominator z (pairedIntegerSquare (n+1)))
    (pairedProduct_nonzero z a hm hp) (upperPairedSeriesDomain z hz n)
    (FunctionTheory.sub_congr (equiv_refl _ (mul_valid z.property z.property))
      (rationalRealSquare_equiv ((n+1:Nat):Rat)))
  have hq := mul_equiv (add_valid z.property z.property) (add_valid z.property z.property)
    (RepresentedReciprocal.inverse _ (pairedProduct_nonzero z a hm hp)).property
    (RepresentedReciprocal.inverse _ (upperPairedSeriesDomain z hz n)).property
    (equiv_refl _ (add_valid z.property z.property)) hi
  exact equiv_trans (upperPairedLatticeTerm z hz n).property (pairedQuotient z a hm hp).property
    (pairedFullTerm z (upperPairedSeriesDomain z hz) n).property
    (pairedReciprocal_quotient z a hm hp) hq

def upperPairedLatticePrefix (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => (upperPairedLatticeTerm z hz n).val) 0 N

theorem upperPairedLatticePrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    (upperPairedLatticePrefix z hz N).Valid :=
  ScalarSeries.block_valid _ (fun n => (upperPairedLatticeTerm z hz n).property) 0 N

theorem upperPairedLatticePrefix_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    (upperPairedLatticePrefix z hz N).Equiv
      (ScalarSeries.block (fun n => (pairedFullTerm z (upperPairedSeriesDomain z hz) n).val) 0 N) :=
  ScalarSeries.block_congr _ _ (upperPairedLatticeTerm_agreement z hz) 0 N

theorem upperPairedLatticePrefix_close (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (pairedSeriesValue z (upperPairedSeriesDomain z hz))
      (upperPairedLatticePrefix z hz (4*pairedInternalBound z+(N+1))))
      (((16*pairedInternalBound z:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) := by
  have h := pairedFullValue_close z (upperPairedSeriesDomain z hz) (pairedInternalBound z)
    (pairedInternalBound_small z) N
  exact Small.congr
    (sub_valid (pairedSeriesValue_valid z (upperPairedSeriesDomain z hz))
      (ScalarSeries.block_valid _ (fun n => (pairedFullTerm z (upperPairedSeriesDomain z hz) n).property) 0 _))
    (sub_valid (pairedSeriesValue_valid z (upperPairedSeriesDomain z hz)) (upperPairedLatticePrefix_valid z hz _))
    (FunctionTheory.sub_congr (equiv_refl _ (pairedSeriesValue_valid z (upperPairedSeriesDomain z hz)))
      (equiv_symm (upperPairedLatticePrefix_agreement z hz _))) h

end ComputableAnalysis.ModularForms
