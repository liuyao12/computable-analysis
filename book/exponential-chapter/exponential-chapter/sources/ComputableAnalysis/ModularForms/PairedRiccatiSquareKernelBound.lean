import ComputableAnalysis.ModularForms.PairedRiccatiCauchyKernelBound
import ComputableAnalysis.PDE.CauchyContour

/-! Large-square separation for the actual squared Cauchy kernel. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions
open PDE.CauchyContour

theorem scaledSquarePoint_coordinate_separated (edge : HalfEdge) (u R : Rat) :
    let q := QComplex.scaleRat R (point edge u)
    R≤q.re ∨ q.re≤ -R ∨ R≤q.im ∨ q.im≤ -R := by
  cases edge with
  | mk quarter upper =>
    cases quarter <;> cases upper <;>
      simp [point,rotation,orientation,QComplex.mul,QComplex.scaleRat] <;> grind only

theorem pairedEntireRiccatiMap_square_kernel_bound (z : Scalar) (edge : HalfEdge)
    (u R : Rat) (hR : 0<R) :
    Small (mul (pairedEntireRiccatiMap.eval z trivial).val
      (mul (ofQComplex (RationalReciprocal.inverse (QComplex.scaleRat R (point edge u))))
        (ofQComplex (RationalReciprocal.inverse (QComplex.scaleRat R (point edge u))))))
      (21479360*(1/R)*(1/R)) :=
  pairedEntireRiccatiMap_squared_kernel_bound z _ R hR
    (scaledSquarePoint_coordinate_separated edge u R)

end ComputableAnalysis.ModularForms
