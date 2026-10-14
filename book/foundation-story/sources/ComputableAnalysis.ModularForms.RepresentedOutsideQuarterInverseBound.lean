import ComputableAnalysis.ModularForms.PairedPoleCenterSeparation

/-! Uniform actual inverse bounds outside the quarter pole neighborhood. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem representedInverse_outside_quarter_bound (z : Scalar)
    (hz : NonzeroBoxSearch.Nonzero z) (hout : ¬LocalODE.interior (1/4) z) :
    Small (RepresentedReciprocal.inverse z hz).val 64 := by
  obtain ⟨N,hN⟩ := z.property.2.2 ⟨1/16,by decide +kernel⟩
  let w := verticalTailScalar z N
  have he := verticalTailScalar_equiv z N
  have hw : NonzeroBoxSearch.Nonzero w := (NonzeroBoxSearch.nonzero_congr w z he).mpr hz
  have ho : ¬LocalODE.interior (1/4) w := fun h => hout (Centered.interior_congr _ w z he h)
  let k := ReciprocalAnchor.stage w hw
  have hwidth := hN (N+k) (by omega)
  have hsep := outsideQuarterDisk_center_separated w k ho hwidth.1 hwidth.2
  have hq := rationalSeparated_inverse_coordinate_bound (w.val.compute k).center (1/8)
    (by decide +kernel) (by
      simpa only [show -(1:Rat)/8= -((1:Rat)/8) by decide +kernel] using hsep)
  have ha : Small (ReciprocalAnchor.anchor w hw).val 8 :=
    (BoxApproximation.rational_small (RationalReciprocal.inverse (ReciprocalAnchor.center w hw) )).mono (by
      simpa only [ReciprocalAnchor.center, k, show (1:Rat)/(1/8)=8 by decide +kernel] using hq)
  have hs := Small.mul (ReciprocalAnchor.anchor w hw).property
    (ScalarNeumannInverse.value (ReciprocalAnchor.normalized w hw)
      (ReciprocalAnchor.residual_small w hw)).property
    (show (0:Rat)≤8 by decide +kernel) (show (0:Rat)≤4 by decide +kernel) ha
    (ScalarNeumannInverse.value_bound _ _)
  have hb : Small (RepresentedReciprocal.inverse w hw).val 64 := hs.mono (by decide +kernel)
  exact Small.congr (RepresentedReciprocal.inverse w hw).property
    (RepresentedReciprocal.inverse z hz).property (RepresentedReciprocal.inverse_congr w z hw hz he) hb

end ComputableAnalysis.ModularForms
