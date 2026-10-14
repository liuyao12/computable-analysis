import ComputableAnalysis.ModularForms.RepresentedSquareKernelContinuity

/-! Combining actual Riccati variation with the constructed kernel modulus. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory PDE.CauchyContour

def rationalSquaredKernel (q : QComplex) : Scalar :=
  ⟨mul (ofQComplex (RationalReciprocal.inverse q)) (ofQComplex (RationalReciprocal.inverse q)),
    mul_valid (ofQComplex_valid _) (ofQComplex_valid _)⟩

theorem rationalSquaredKernel_separated_bound (q : QComplex) (R : Rat) (hR : 0<R)
    (hq : R≤q.re ∨ q.re≤ -R ∨ R≤q.im ∨ q.im≤ -R) :
    Small (rationalSquaredKernel q).val (2*(1/R)*(1/R)) := by
  have hi := (BoxApproximation.rational_small _).mono
    (rationalSeparated_inverse_coordinate_bound q R hR hq)
  have hn : 0≤(1:Rat)/R := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr hR))
  exact Small.mul (ofQComplex_valid _) (ofQComplex_valid _) hn hn hi hi

theorem pairedRiccati_square_kernel_product_difference_bound (z w : Scalar)
    (edge : HalfEdge) (u v R E : Rat) (hR : 0<R)
    (hu : 0≤u) (hu1 : u≤1) (hv : 0≤v) (hv1 : v≤1) (hE : 0≤E)
    (he : Small (sub (pairedEntireRiccatiMap.eval z trivial).val
      (pairedEntireRiccatiMap.eval w trivial).val) E) :
    let p := rationalSquaredKernel (QComplex.scaleRat R (point edge u))
    let q := rationalSquaredKernel (QComplex.scaleRat R (point edge v))
    Small (sub (mul (pairedEntireRiccatiMap.eval z trivial).val p.val)
      (mul (pairedEntireRiccatiMap.eval w trivial).val q.val))
      (2*E*(2*(1/R)*(1/R))+2*5369840*((2*((2*R)*(R*R)⁻¹)^3*R)*qabs (u-v))) := by
  let p := rationalSquaredKernel (QComplex.scaleRat R (point edge u))
  let q := rationalSquaredKernel (QComplex.scaleRat R (point edge v))
  have hp := rationalSquaredKernel_separated_bound _ R hR
    (scaledSquarePoint_coordinate_separated edge u R)
  have hd := representedSquareKernel_parameter_bound edge u v R hu hu1 hv hv1 hR
  have hn : 0≤(1:Rat)/R := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr hR))
  have hm : 0≤(R*R)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hR hR))
  have hk : 0≤(2*R)*(R*R)⁻¹ := Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hR)) hm
  have hpow : 0≤((2*R)*(R*R)⁻¹)^3 := Rat.pow_nonneg hk
  exact SeriesLimitLaws.product_close _ _ _ _
    (pairedEntireRiccatiMap.eval z trivial).property p.property
    (pairedEntireRiccatiMap.eval w trivial).property q.property
    _ _ _ _ hE
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hpow)
      (Rat.le_of_lt hR)) (qabs_nonneg _))
    (by decide +kernel) (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hn) hn)
    he hd (pairedEntireRiccatiMap_global_bound w) hp

end ComputableAnalysis.ModularForms
