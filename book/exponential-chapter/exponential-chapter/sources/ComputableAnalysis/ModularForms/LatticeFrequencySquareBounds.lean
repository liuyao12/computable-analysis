import ComputableAnalysis.ModularForms.LatticeFrequencyBounds

/-! Tight rational radicand bounds for the geometric quarter-turn comparison. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem latticeFrequencySquare_ge_four :
    (RealRaw.ofRat 4).Le latticeFrequencySquare := by
  intro n m
  have hs := (pairedRiccatiCenterConstant_prefix_error 7).2.1 m 0
  change (pairedRiccatiCenterConstant.val.compute m).lo.re+
    -(3*pairedZeroSquarePrefix 8)≤24*(8:Rat)⁻¹ at hs
  have hp : 3*pairedZeroSquarePrefix 8+24*(8:Rat)⁻¹≤ -4 := by decide +kernel
  change 4≤ -(pairedRiccatiCenterConstant.val.compute m).lo.re
  generalize (pairedRiccatiCenterConstant.val.compute m).lo.re=r at hs ⊢
  grind only

theorem latticeFrequencySquare_le_sixteen :
    latticeFrequencySquare.Le (RealRaw.ofRat 16) := by
  intro n m
  have hs := (pairedRiccatiCenterConstant_prefix_error 7).1 0 n
  change -(24*(8:Rat)⁻¹)≤(pairedRiccatiCenterConstant.val.compute n).hi.re+
    -(3*pairedZeroSquarePrefix 8) at hs
  have hp : -16≤3*pairedZeroSquarePrefix 8-24*(8:Rat)⁻¹ := by decide +kernel
  change -(pairedRiccatiCenterConstant.val.compute n).hi.re≤16
  generalize (pairedRiccatiCenterConstant.val.compute n).hi.re=r at hs ⊢
  grind only

theorem latticeFrequencySquare_quarter_guard_overlap (n : Nat) :
    (latticeFrequencySquare.compute n).Overlaps (⟨4,16⟩ : QInterval) :=
  ⟨latticeFrequencySquare_le_sixteen n 0,latticeFrequencySquare_ge_four 0 n⟩

end ComputableAnalysis.ModularForms
