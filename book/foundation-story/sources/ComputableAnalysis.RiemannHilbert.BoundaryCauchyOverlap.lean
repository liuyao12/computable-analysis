import ComputableAnalysis.RiemannHilbert.BoundaryCauchyExamples
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicLocality

/-! Boundary projections agree on intersecting computed balls even when the
expansion centers are different. Their genuine holomorphic derivatives agree
by the proved derivative uniqueness law. This is actual local gluing evidence,
not an assumed annular splitting or global section. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchyOverlap
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false
variable (d e : Data)

theorem value (hJ : d.rectangle=e.rectangle)
    (hf : ∀ w (hd : d.source.domain w) (he : e.source.domain w), d.source.eval w hd≈e.source.eval w he)
    (z w : Scalar) (hz : (BoundaryCauchySeries.function d).domain z) (hw : (BoundaryCauchySeries.function e).domain w)
    (hzw : z≈w) : (BoundaryCauchySeries.function d).eval z hz≈(BoundaryCauchySeries.function e).eval w hw := by
  apply Setoid.trans (BoundaryCauchyReconstruction.projection d z hz)
  apply Setoid.trans (BoundaryCauchyAgreement.moment_agreement
    (BoundaryCauchyNear.data d z hz) (BoundaryCauchyNear.data e w hw) hJ hzw hf 0)
  exact equiv_symm (BoundaryCauchyReconstruction.projection e w hw)

theorem derivative (hJ : d.rectangle=e.rectangle)
    (hf : ∀ w (hd : d.source.domain w) (he : e.source.domain w), d.source.eval w hd≈e.source.eval w he)
    (z : Scalar) (hz : (BoundaryCauchySeries.function d).domain z) (hw : (BoundaryCauchySeries.function e).domain z) :
    (BoundaryCauchySeries.holomorphic d).derivative z hz≈(BoundaryCauchySeries.holomorphic e).derivative z hw := by
  let f := BoundaryCauchySeries.function d
  let g := BoundaryCauchySeries.function e
  let hF := BoundaryCauchySeries.holomorphic d
  let hG := BoundaryCauchySeries.holomorphic e
  let I := intersectionOpenData hF hG
  let r := onDomain g I.invariant (fun _ hm => hm.2)
  let hr := hG.onDomain I (fun _ hm => hm.2)
  have ht : HasDerivativeAt f z hz (hG.derivative z hw) := HasDerivativeAt.of_local f r hr.openDomain
    (fun _ hm => hm.1)
    (fun p hp => equiv_symm (value d e hJ hf p p hp.1 hp.2 (equiv_refl _ p.property)))
    z hz ⟨hz,hw⟩ _ (hr.atPoint z ⟨hz,hw⟩)
  exact (hF.atPoint z hz).unique ht hF.openDomain

end ComputableAnalysis.RiemannHilbert.BoundaryCauchyOverlap
