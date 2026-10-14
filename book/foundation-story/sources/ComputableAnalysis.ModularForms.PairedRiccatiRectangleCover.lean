import ComputableAnalysis.ModularForms.RectangleCoordinateComplex
import ComputableAnalysis.ModularForms.PairedEntireGlobalDerivativeBound

/-! Finite rectangle coverage by actual Riccati derivative neighborhoods.
The radii are local; no uniform quadratic cell model is asserted. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def rationalRectangleContains (J : QInterval × QInterval) (q : QComplex) : Prop :=
  J.1.lo≤q.re ∧ q.re≤J.1.hi ∧ J.2.lo≤q.im ∧ q.im≤J.2.hi

inductive RiccatiDerivativeRectangleCover (eps : QPos) : QInterval × QInterval → Prop
  | neighborhood (J : QInterval × QInterval) (a : Scalar) (H : QPos)
      (radius : H.val≤((pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta eps).val)
      (contains : ∀ q : QComplex, rationalRectangleContains J q →
        Small (sub (ofQComplex q) a.val) H.val) : RiccatiDerivativeRectangleCover eps J
  | split (J : QInterval × QInterval)
      (ll : RiccatiDerivativeRectangleCover eps (bisectRectangle J (false,false)))
      (lr : RiccatiDerivativeRectangleCover eps (bisectRectangle J (false,true)))
      (rl : RiccatiDerivativeRectangleCover eps (bisectRectangle J (true,false)))
      (rr : RiccatiDerivativeRectangleCover eps (bisectRectangle J (true,true))) :
      RiccatiDerivativeRectangleCover eps J

theorem pairedRiccati_finite_rectangle_cover (eps : QPos) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    RiccatiDerivativeRectangleCover eps J := by
  apply represented_rectangle_cover (RiccatiDerivativeRectangleCover eps) J hX hY
  · intro K ll lr rl rr
    exact RiccatiDerivativeRectangleCover.split K ll lr rl rr
  · intro x y hx hy hxl hxu hyl hyu
    let a : Scalar := ⟨coordinateComplex x y,coordinateComplex_valid x y hx hy⟩
    let H := (pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta eps
    refine ⟨H, ?_⟩
    intro K hKx hKy
    apply RiccatiDerivativeRectangleCover.neighborhood K a H Rat.le_refl
    intro q hq
    exact rectangleNear_complex_displacement K x y H hKx hKy q hq

end ComputableAnalysis.ModularForms
