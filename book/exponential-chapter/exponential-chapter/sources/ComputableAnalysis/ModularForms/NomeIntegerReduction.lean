import ComputableAnalysis.ModularForms.RepresentedIntegerRounding
import ComputableAnalysis.ModularForms.CMGrowthTightBounds163
import ComputableAnalysis.ModularForms.Nome

/-! An executable integer reduction of an arbitrary represented input.
The reduced nome exponent has imaginary coordinate in the proved kernel
strip. No period or kernel classification is assumed here. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Round only the represented real coordinate of the supplied input. -/
def nomeReductionInteger (z : Scalar) : Int :=
  representedIntegerRounding z.val.realPart (realPart_valid z.property)

def nomeIntegerRemainder (z : Scalar) : Scalar :=
  ⟨sub z.val (ofQComplex ⟨(nomeReductionInteger z:Rat),0⟩),sub_valid z.property (ofQComplex_valid _)⟩

theorem nomeIntegerRemainder_real_bounds (z : Scalar) :
    (RealRaw.ofRat (-5/8)).Le (nomeIntegerRemainder z).val.realPart ∧
      (nomeIntegerRemainder z).val.realPart.Le (RealRaw.ofRat (5/8)) := by
  have h := representedIntegerRounding_bounds z.val.realPart (realPart_valid z.property)
  constructor
  · intro n m
    have hh := h.1 0 m
    change (nomeReductionInteger z:Rat)-5/8≤(z.val.compute m).hi.re at hh
    change -5/8≤(z.val.compute m).hi.re+ -(nomeReductionInteger z:Rat)
    grind only
  · intro n m
    have hh := h.2 n 0
    change (z.val.compute n).lo.re≤(nomeReductionInteger z:Rat)+5/8 at hh
    change (z.val.compute n).lo.re+ -(nomeReductionInteger z:Rat)≤5/8
    grind only

/-- Semantic real-coordinate bounds give the fixed imaginary-coordinate
bound for the actual nome exponent, even if the supplied boxes overshoot. -/
theorem nomeSlope_imaginary_bound_of_real_bound (z : Scalar)
    (hl : (RealRaw.ofRat (-5/8)).Le z.val.realPart)
    (hu : z.val.realPart.Le (RealRaw.ofRat (5/8))) :
    (RealRaw.ofRat (-4)).Le (scalarProduct nomeSlope z).val.imagPart ∧
      (scalarProduct nomeSlope z).val.imagPart.Le (RealRaw.ofRat 4) := by
  have bound (n : Nat) :
      ((scalarProduct nomeSlope z).val.compute n).lo.im≤4 ∧
        -4≤((scalarProduct nomeSlope z).val.compute n).hi.im := by
    let h := (GeometricPiRotation.halfPi.compute n).lo
    let r := maxRat2 (z.val.compute n).lo.re (-5/8)
    have hpi := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPi_valid n
    have hpilo := (GeometricPiRotation.halfPi_bounds n).1
    have hpihi := halfPi_upper_eight_fifths n 0
    change h≤8/5 at hpihi
    have h0 : 0≤h := by dsimp [h]; grind only
    have hz := valid_ordered z.property n
    have hzr := hz.1
    change (z.val.compute n).lo.re≤(z.val.compute n).hi.re at hzr
    have hlo := hl 0 n
    have hhi := hu n 0
    change -5/8≤(z.val.compute n).hi.re at hlo
    change (z.val.compute n).lo.re≤5/8 at hhi
    have hr : (z.val.compute n).lo.re≤r ∧ r≤(z.val.compute n).hi.re ∧ -5/8≤r ∧ r≤5/8 := by
      dsimp [r]; unfold maxRat2; split <;> grind only
    have hs : (nomeSlope.val.compute n).lo≤(⟨0,4*h⟩ : QComplex) ∧
        (⟨0,4*h⟩ : QComplex)≤(nomeSlope.val.compute n).hi := by
      simp only [nomeSlope,scaleRat,mulI,ofRealRaw,QBox.scaleRat,
        if_pos (show (0:Rat)≤4 by decide +kernel),QComplex.le_def,Rat.neg_zero,Rat.mul_zero]
      change ((0:Rat)≤0 ∧ 4*h≤4*h) ∧ (0≤0 ∧ 4*h≤4*(GeometricPiRotation.halfPi.compute n).hi)
      have hm := Rat.mul_le_mul_of_nonneg_left hpi (show (0:Rat)≤4 by decide +kernel)
      exact ⟨⟨Rat.le_refl,Rat.le_refl⟩,⟨Rat.le_refl,hm⟩⟩
    let p : QComplex := ⟨r,(z.val.compute n).lo.im⟩
    have hp : (z.val.compute n).lo≤p ∧ p≤(z.val.compute n).hi :=
      ⟨⟨hr.1,Rat.le_refl⟩,⟨hr.2.1,hz.2⟩⟩
    have hm := QBox.mul_contains hs.1 hs.2 hp.1 hp.2
    have hml := hm.1.2
    have hmu := hm.2.2
    change ((scalarProduct nomeSlope z).val.compute n).lo.im≤0*(z.val.compute n).lo.im+4*h*r at hml
    change 0*(z.val.compute n).lo.im+4*h*r≤((scalarProduct nomeSlope z).val.compute n).hi.im at hmu
    have hb := Rat.mul_le_mul_of_nonneg_left hr.2.2.2 h0
    have ht := Rat.mul_le_mul_of_nonneg_right hpihi (show (0:Rat)≤5/8 by decide +kernel)
    have ha := Rat.mul_le_mul_of_nonneg_left hr.2.2.1 h0
    constructor <;> grind only
  constructor
  · intro n m
    exact (bound m).2
  · intro n m
    exact (bound n).1

/-- The executable remainder has nome exponent in the fixed kernel strip,
with all precision and integer choices internal to the construction. -/
theorem nomeIntegerRemainder_exponent_bounds (z : Scalar) :
    (RealRaw.ofRat (-4)).Le (scalarProduct nomeSlope (nomeIntegerRemainder z)).val.imagPart ∧
      (scalarProduct nomeSlope (nomeIntegerRemainder z)).val.imagPart.Le (RealRaw.ofRat 4) :=
  nomeSlope_imaginary_bound_of_real_bound (nomeIntegerRemainder z)
    (nomeIntegerRemainder_real_bounds z).1 (nomeIntegerRemainder_real_bounds z).2

end ComputableAnalysis.ModularForms
