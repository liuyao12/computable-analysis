import ComputableAnalysis.ModularForms.PairedRiccatiUniformRectangleCover

/-! Finite coverage by neighborhoods controlling actual derivative variation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

inductive RectangleVariationCover (g : Scalar → Scalar) (eps : QPos) :
    QInterval × QInterval → Prop
  | neighborhood (J : QInterval × QInterval) (a : Scalar)
      (bound : ∀ q : QComplex, rationalRectangleContains J q →
        Small (sub (g ⟨ofQComplex q,ofQComplex_valid _⟩).val (g a).val) eps.val) :
      RectangleVariationCover g eps J
  | split (J : QInterval × QInterval)
      (ll : RectangleVariationCover g eps (bisectRectangle J (false,false)))
      (lr : RectangleVariationCover g eps (bisectRectangle J (false,true)))
      (rl : RectangleVariationCover g eps (bisectRectangle J (true,false)))
      (rr : RectangleVariationCover g eps (bisectRectangle J (true,true))) :
      RectangleVariationCover g eps J

theorem continuous_rectangle_variation_cover (g : Scalar → Scalar)
    (hc : ContinuousOn (fun _ : Scalar => True) (fun a _ => g a))
    (eps : QPos) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) : RectangleVariationCover g eps J := by
  apply represented_rectangle_cover (RectangleVariationCover g eps) J hX hY
  · intro K ll lr rl rr
    exact RectangleVariationCover.split K ll lr rl rr
  · intro x y hx hy hxl hxu hyl hyu
    let a : Scalar := ⟨coordinateComplex x y,coordinateComplex_valid x y hx hy⟩
    let H := hc.delta a trivial eps
    refine ⟨H, ?_⟩
    intro K hKx hKy
    apply RectangleVariationCover.neighborhood K a
    intro q hq
    exact hc.estimate a trivial eps ⟨ofQComplex q,ofQComplex_valid _⟩ trivial
      (rectangleNear_complex_displacement K x y H hKx hKy q hq)

noncomputable def pairedRiccatiDerivativeValue (a : Scalar) : Scalar :=
  pairedEntireRiccatiMap_holomorphic.derivative a trivial

theorem pairedRiccatiDerivative_rectangle_variation_cover (eps : QPos)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    RectangleVariationCover pairedRiccatiDerivativeValue eps J :=
  continuous_rectangle_variation_cover pairedRiccatiDerivativeValue
    pairedEntireRiccatiMap_holomorphic.continuousDerivative eps J hX hY

end ComputableAnalysis.ModularForms
