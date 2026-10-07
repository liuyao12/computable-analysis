import ComputableAnalysis.ModularForms.RationalSeparatedReciprocalBound

/-! Tight rational centers are separated for inputs outside a pole neighborhood. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem outsideQuarterDisk_center_separated (z : Scalar) (N : Nat)
    (hout : ¬LocalODE.interior (1/4) z)
    (hw : (z.val.compute N).width≤(1:Rat)/16)
    (hh : (z.val.compute N).height≤(1:Rat)/16) :
    (1:Rat)/8≤(z.val.compute N).center.re ∨ (z.val.compute N).center.re≤ -(1:Rat)/8 ∨
    (1:Rat)/8≤(z.val.compute N).center.im ∨ (z.val.compute N).center.im≤ -(1:Rat)/8 := by
  apply Classical.byContradiction
  intro h
  let q := (z.val.compute N).center
  have hq : BoxApproximation.coordinateBound q≤(1:Rat)/8 := by
    unfold BoxApproximation.coordinateBound qabs
    dsimp [q] at *
    grind
  have hs := (BoxApproximation.rational_small q).mono hq
  have he := BoxApproximation.center_error z N (1/16) (by decide +kernel) hw hh
  have hb := LocalODE.small_add hs he
  have hi := Small.congr
    (add_valid (ofQComplex_valid q) (sub_valid z.property (ofQComplex_valid q))) z.property
    (SeriesLimitLaws.add_difference z.val (ofQComplex q) z.property (ofQComplex_valid q)) hb
  exact hout ⟨(1:Rat)/8+1/16,(by decide +kernel),(by decide +kernel),hi⟩

end ComputableAnalysis.ModularForms
