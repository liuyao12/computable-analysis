import ComputableAnalysis.ModularForms.PairedCanonicalValue
import ComputableAnalysis.ModularForms.UpperHalfPlane

/-! Concrete nonzero-domain evidence for paired series on the upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem upperScalar_nonzero (z : Scalar) (hz : InUpperHalfPlane z.val) :
    NonzeroBoxSearch.Nonzero z := by
  intro he
  obtain ⟨N,hN⟩ := hz
  have h := (compareAt_overlap_iff _ _ N N).mp (he N)
  have hl := h.1.2
  change (z.val.compute N).lo.im≤0 at hl
  change 0<(z.val.compute N).lo.im at hN
  grind only

theorem upperShiftMinus_nonzero (z : Scalar) (hz : InUpperHalfPlane z.val) (a : Rat) :
    NonzeroBoxSearch.Nonzero (pairedMinus z ⟨ofQComplex ⟨a,0⟩,ofQComplex_valid _⟩) := by
  apply upperScalar_nonzero
  obtain ⟨N,hN⟩ := hz
  change 0<(z.val.compute N).lo.im at hN
  refine ⟨N,?_⟩
  change 0<(z.val.compute N).lo.im + -0
  simpa only [Rat.neg_zero,Rat.add_zero] using hN

theorem upperShiftPlus_nonzero (z : Scalar) (hz : InUpperHalfPlane z.val) (a : Rat) :
    NonzeroBoxSearch.Nonzero (pairedPlus z ⟨ofQComplex ⟨a,0⟩,ofQComplex_valid _⟩) := by
  apply upperScalar_nonzero
  obtain ⟨N,hN⟩ := hz
  change 0<(z.val.compute N).lo.im at hN
  refine ⟨N,?_⟩
  change 0<(z.val.compute N).lo.im + 0
  simpa only [Rat.add_zero] using hN

theorem rationalRealSquare_equiv (a : Rat) :
    (mul (ofQComplex ⟨a,0⟩) (ofQComplex ⟨a,0⟩)).Equiv (ofQComplex ⟨a*a,0⟩) := by
  have h := qcomplexLeftMul_equiv_mul_ofQComplex (⟨a,0⟩ : QComplex) (ofQComplex_valid ⟨a,0⟩)
  have hq := qcomplexLeftMul_ofQComplex (⟨a,0⟩ : QComplex) ⟨a,0⟩
  have he : QComplex.mul (⟨a,0⟩ : QComplex) ⟨a,0⟩=⟨a*a,0⟩ := by
    simp [QComplex.mul,Rat.mul_zero,Rat.zero_mul,Rat.sub_eq_add_neg,Rat.add_zero,Rat.neg_zero]
  rw [he] at hq
  exact equiv_trans (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))
    (qcomplexLeftMul_valid _ (ofQComplex_valid _)) (ofQComplex_valid _) (equiv_symm h) hq

theorem upperPairedSeriesDomain (z : Scalar) (hz : InUpperHalfPlane z.val) : PairedSeriesDomain z := by
  intro n
  let a : Scalar := ⟨ofQComplex ⟨((n+1:Nat):Rat),0⟩,ofQComplex_valid _⟩
  have hm := upperShiftMinus_nonzero z hz ((n+1:Nat):Rat)
  have hp := upperShiftPlus_nonzero z hz ((n+1:Nat):Rat)
  have hn := pairedProduct_nonzero z a hm hp
  apply (NonzeroBoxSearch.nonzero_congr (pairedProduct z a)
    (pairedLiteralDenominator z (pairedIntegerSquare (n+1)))
    (FunctionTheory.sub_congr (equiv_refl _ (mul_valid z.property z.property))
      (rationalRealSquare_equiv ((n+1:Nat):Rat)))).mp
  exact hn

def upperPairedPartialFractionValue (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  pairedPartialFractionValue z (upperScalar_nonzero z hz) (upperPairedSeriesDomain z hz)

theorem upperPairedPartialFractionValue_valid (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperPairedPartialFractionValue z hz).Valid :=
  pairedPartialFractionValue_valid z (upperScalar_nonzero z hz) (upperPairedSeriesDomain z hz)

end ComputableAnalysis.ModularForms
