import ComputableAnalysis.ModularForms.PairedRiccatiKernelProductContinuity

/-! Local kernel-product variation derived from actual Riccati derivative evidence. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions PDE.CauchyContour

theorem pairedEntireRiccatiMap_local_difference_bound (a z : Scalar) (H : QPos)
    (hH : H.val≤((pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta unitError).val)
    (hza : Small (sub z.val a.val) H.val) :
    Small (sub (pairedEntireRiccatiMap.eval z trivial).val
      (pairedEntireRiccatiMap.eval a trivial).val)
      ((derivativeRate (pairedEntireRiccatiMap_holomorphic.derivative a trivial)).val*H.val) :=
  (pairedEntireRiccatiMap_holomorphic.atPoint a trivial).difference_bound H z trivial hH hza

theorem pairedRiccati_square_kernel_product_local_bound (a z : Scalar) (H : QPos)
    (hH : H.val≤((pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta unitError).val)
    (hza : Small (sub z.val a.val) H.val)
    (edge : HalfEdge) (u v R : Rat) (hR : 0<R)
    (hu : 0≤u) (hu1 : u≤1) (hv : 0≤v) (hv1 : v≤1) :
    let E := (derivativeRate (pairedEntireRiccatiMap_holomorphic.derivative a trivial)).val*H.val
    let p := rationalSquaredKernel (QComplex.scaleRat R (point edge u))
    let q := rationalSquaredKernel (QComplex.scaleRat R (point edge v))
    Small (sub (mul (pairedEntireRiccatiMap.eval z trivial).val p.val)
      (mul (pairedEntireRiccatiMap.eval a trivial).val q.val))
      (2*E*(2*(1/R)*(1/R))+2*5369840*((2*((2*R)*(R*R)⁻¹)^3*R)*qabs (u-v))) :=
  pairedRiccati_square_kernel_product_difference_bound z a edge u v R _ hR hu hu1 hv hv1
    (Rat.mul_nonneg (Rat.le_of_lt (derivativeRate _).property) (Rat.le_of_lt H.property))
    (pairedEntireRiccatiMap_local_difference_bound a z H hH hza)

end ComputableAnalysis.ModularForms
