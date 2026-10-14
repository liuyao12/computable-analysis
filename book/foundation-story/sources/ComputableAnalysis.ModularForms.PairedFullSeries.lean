import ComputableAnalysis.ModularForms.PairedTailSeries

/-! Full executable paired partial fractions, joining finite terms and a proved tail. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def PairedSeriesDomain (z : Scalar) : Prop :=
  ∀ n : Nat, NonzeroBoxSearch.Nonzero (pairedLiteralDenominator z (pairedIntegerSquare (n+1)))

theorem pairedSeriesDomain_congr (z w : Scalar) (he : z.val.Equiv w.val) :
    PairedSeriesDomain z ↔ PairedSeriesDomain w := by
  have h (n : Nat) := NonzeroBoxSearch.nonzero_congr
    (pairedLiteralDenominator z (pairedIntegerSquare (n+1)))
    (pairedLiteralDenominator w (pairedIntegerSquare (n+1)))
    (FunctionTheory.sub_congr (mul_equiv z.property w.property z.property w.property he he)
      (equiv_refl _ (ofQComplex_valid _)))
  exact ⟨fun hd n => (h n).mp (hd n),fun hd n => (h n).mpr (hd n)⟩

def pairedFullTerm (z : Scalar) (hd : PairedSeriesDomain z) (n : Nat) : Scalar :=
  ⟨mul (add z.val z.val)
    (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare (n+1))) (hd n)).val,
    mul_valid (add_valid z.property z.property)
      (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare (n+1))) (hd n)).property⟩

def pairedFullValue (z : Scalar) (hd : PairedSeriesDomain z) (B : Nat)
    (hz : Small z.val (B:Rat)) : ComplexRaw :=
  add (ScalarSeries.block (fun n => (pairedFullTerm z hd n).val) 0 (4*B)) (pairedTailValue z B hz)

theorem pairedFullValue_valid (z : Scalar) (hd : PairedSeriesDomain z) (B : Nat)
    (hz : Small z.val (B:Rat)) : (pairedFullValue z hd B hz).Valid :=
  add_valid (ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hd n).property) 0 (4*B))
    (pairedTailValue_valid z B hz)

theorem pairedFullTerm_congr (z w : Scalar) (hd : PairedSeriesDomain z)
    (hw : PairedSeriesDomain w) (he : z.val.Equiv w.val) (n : Nat) :
    (pairedFullTerm z hd n).val.Equiv (pairedFullTerm w hw n).val := by
  have hi := RepresentedReciprocal.inverse_congr
    (pairedLiteralDenominator z (pairedIntegerSquare (n+1)))
    (pairedLiteralDenominator w (pairedIntegerSquare (n+1))) (hd n) (hw n)
    (FunctionTheory.sub_congr (mul_equiv z.property w.property z.property w.property he he)
      (equiv_refl _ (ofQComplex_valid _)))
  exact mul_equiv (add_valid z.property z.property) (add_valid w.property w.property)
    (RepresentedReciprocal.inverse _ (hd n)).property (RepresentedReciprocal.inverse _ (hw n)).property
    (add_equiv he he) hi

theorem pairedFullValue_congr (z w : Scalar) (hd : PairedSeriesDomain z)
    (hw : PairedSeriesDomain w) (B : Nat) (hzB : Small z.val (B:Rat)) (hwB : Small w.val (B:Rat))
    (he : z.val.Equiv w.val) : (pairedFullValue z hd B hzB).Equiv (pairedFullValue w hw B hwB) :=
  add_equiv (ScalarSeries.block_congr _ _ (pairedFullTerm_congr z w hd hw he) 0 (4*B))
    (pairedTailValue_congr z w B hzB hwB he)

def pairedCotangentSeries (z : Scalar) (h0 : NonzeroBoxSearch.Nonzero z)
    (hd : PairedSeriesDomain z) (B : Nat) (hz : Small z.val (B:Rat)) : ComplexRaw :=
  add (RepresentedReciprocal.inverse z h0).val (pairedFullValue z hd B hz)

theorem pairedCotangentSeries_valid (z : Scalar) (h0 : NonzeroBoxSearch.Nonzero z)
    (hd : PairedSeriesDomain z) (B : Nat) (hz : Small z.val (B:Rat)) :
    (pairedCotangentSeries z h0 hd B hz).Valid :=
  add_valid (RepresentedReciprocal.inverse z h0).property (pairedFullValue_valid z hd B hz)

end ComputableAnalysis.ModularForms
