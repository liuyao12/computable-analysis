import ComputableAnalysis.RiemannHilbert.CenteredUniqueness

/-! Translation of actual represented holomorphic functions, with the
derivative and effective open-neighborhood witnesses transported explicitly. -/
namespace ComputableAnalysis.RiemannHilbert.Centered
open ComplexRaw FunctionTheory

theorem offset_congr (c d z w : Scalar) (hcd : c.val.Equiv d.val) (hzw : z.val.Equiv w.val) :
    (offset c z).val.Equiv (offset d w).val := FunctionTheory.sub_congr hzw hcd

theorem offset_difference (c w z : Scalar) :
    (sub (offset c z).val (offset c w).val).Equiv (sub z.val w.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (offset c z).property (offset c w).property)
    (hright := sub_valid z.property w.property)
  change (ComplexRawQuotient.ofRaw z.val z.property-ComplexRawQuotient.ofRaw c.val c.property)-
    (ComplexRawQuotient.ofRaw w.val w.property-ComplexRawQuotient.ofRaw c.val c.property)=
      ComplexRawQuotient.ofRaw z.val z.property-ComplexRawQuotient.ofRaw w.val w.property
  grind

theorem offset_self (c : Scalar) : (offset c c).val.Equiv zero := add_neg_equiv c.val c.property

theorem domain_congr (c d z w : Scalar) (R : Rat)
    (hcd : c.val.Equiv d.val) (hzw : z.val.Equiv w.val) :
    domain c R z ↔ domain d R w :=
  ⟨interior_congr R (offset c z) (offset d w) (offset_congr c d z w hcd hzw),
   interior_congr R (offset d w) (offset c z) (equiv_symm (offset_congr c d z w hcd hzw))⟩

end ComputableAnalysis.RiemannHilbert.Centered

namespace ComputableAnalysis.RiemannHilbert.CertifiedFunctions
open ComplexRaw FunctionTheory

def translateInput (c : Scalar) (f : Map) : Map where
  domain z := f.domain (Centered.offset c z)
  eval z := f.eval (Centered.offset c z)
  valid z hz := f.valid (Centered.offset c z) hz
  domain_congr z w hzw := f.domain_congr _ _
    (Centered.offset_congr c c z w (equiv_refl _ c.property) hzw)
  eval_congr z w hz hw hzw := f.eval_congr _ _ hz hw
    (Centered.offset_congr c c z w (equiv_refl _ c.property) hzw)

def translateDerivative (c : Scalar) {f : Map} (h : Holomorphic f) :
    Holomorphic (translateInput c f) where
  openDomain := {
    radius := fun z hz => h.openDomain.radius (Centered.offset c z) hz
    inside := fun w hw z hzw =>
      h.openDomain.inside (Centered.offset c w) hw (Centered.offset c z)
        (Small.congr (sub_valid z.property w.property)
          (sub_valid (Centered.offset c z).property (Centered.offset c w).property)
          (equiv_symm (Centered.offset_difference c w z)) hzw) }
  derivative z := h.derivative (Centered.offset c z)
  atPoint w hw := {
    point_mem := hw
    derivative_valid := (h.atPoint (Centered.offset c w) hw).derivative_valid
    delta := (h.atPoint (Centered.offset c w) hw).delta
    estimate := fun eps H z hz hH hzw => by
      let x := Centered.offset c w
      let y := Centered.offset c z
      let d := h.derivative x
      have hxy := Small.congr (sub_valid z.property w.property) (sub_valid y.property x.property)
        (equiv_symm (Centered.offset_difference c w z)) hzw
      have he := (h.atPoint x hw).estimate eps H y hz hH hxy
      have hd := (h.atPoint x hw).derivative_valid
      have hfx := f.valid x hw
      have hfy := f.valid y hz
      exact Small.congr
        (sub_valid (sub_valid hfy hfx) (mul_valid hd (sub_valid y.property x.property)))
        (sub_valid (sub_valid hfy hfx) (mul_valid hd (sub_valid z.property w.property)))
        (FunctionTheory.sub_congr (equiv_refl _ (sub_valid hfy hfx))
          (mul_equiv hd hd (sub_valid y.property x.property) (sub_valid z.property w.property)
            (equiv_refl d hd) (Centered.offset_difference c w z))) he }
  derivative_congr z w hz hw hzw := h.derivative_congr _ _ hz hw
    (Centered.offset_congr c c z w (equiv_refl _ c.property) hzw)
  continuousDerivative := {
    delta := fun z hz eps => h.continuousDerivative.delta (Centered.offset c z) hz eps
    estimate := fun w hw eps z hz hzw =>
      h.continuousDerivative.estimate (Centered.offset c w) hw eps (Centered.offset c z) hz
        (Small.congr (sub_valid z.property w.property)
          (sub_valid (Centered.offset c z).property (Centered.offset c w).property)
          (equiv_symm (Centered.offset_difference c w z)) hzw) }

end ComputableAnalysis.RiemannHilbert.CertifiedFunctions
