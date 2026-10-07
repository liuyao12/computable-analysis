import ComputableAnalysis.ModularForms.PairedSquareKernelLipschitz
import ComputableAnalysis.ModularForms.PairedSquareDensityOscillation

/-! Explicit rational Lipschitz constants for the actual oriented density. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

def squareDensityLipschitzConstant (R : Rat) : Rat :=
  2*squareKernelLipschitzConstant R*R

theorem squareKernelLipschitzConstant_nonneg (R : Rat) (hR : 0<R) :
    0≤squareKernelLipschitzConstant R := by
  have hi : 0≤(1:Rat)/R := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr hR))
  have hk : 0≤((2*R)*(R*R)⁻¹)^3 := Rat.pow_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hR))
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hR hR))))
  unfold squareKernelLipschitzConstant
  apply Rat.add_nonneg
  · exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hR))
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hi) hi)
  · exact Rat.mul_nonneg (by decide +kernel)
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hk) (Rat.le_of_lt hR))

theorem squareDensityLipschitzConstant_nonneg (R : Rat) (hR : 0<R) :
    0≤squareDensityLipschitzConstant R :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (squareKernelLipschitzConstant_nonneg R hR))
    (Rat.le_of_lt hR)

theorem pairedSquareDensity_parameter_lipschitz (a : Scalar) (edge : HalfEdge)
    (R u v : Rat) (hR : 0<R) (hu : 0≤u) (hu1 : u≤1) (hv : 0≤v) (hv1 : v≤1) :
    Small (sub (pairedSquareDensity a edge u R) (pairedSquareDensity a edge v R))
      (squareDensityLipschitzConstant R*qabs (u-v)) := by
  have hE : 0≤squareKernelLipschitzConstant R*qabs (u-v) :=
    Rat.mul_nonneg (squareKernelLipschitzConstant_nonneg R hR) (qabs_nonneg _)
  let U := actualSquareKernelSample a edge R u
  let V := actualSquareKernelSample a edge R v
  let C : Scalar := ⟨ofQComplex (QComplex.scaleRat R (velocity edge)),ofQComplex_valid _⟩
  have hc := (BoxApproximation.rational_small _).mono
    (scaledSquareVelocity_coordinate_bound edge R (Rat.le_of_lt hR))
  have hb := Small.mul (sub_valid U.property V.property) C.property
    hE (Rat.le_of_lt hR)
    (actualSquareKernel_parameter_lipschitz a edge R u v hR hu hu1 hv hv1) hc
  have he : 2*(squareKernelLipschitzConstant R*qabs (u-v))*R=
      squareDensityLipschitzConstant R*qabs (u-v) := by
    unfold squareDensityLipschitzConstant
    grind only
  rw [he] at hb
  have hd := Small.congr (mul_valid (sub_valid U.property V.property) C.property)
    (sub_valid (mul_valid U.property C.property) (mul_valid V.property C.property))
    (constantProduct_difference U V C) hb
  cases hed : edge.upper
  · have hneg := SeriesLimitLaws.small_neg hd
    have hev : (neg (sub (mul U.val C.val) (mul V.val C.val))).Equiv
        (sub (neg (mul U.val C.val)) (neg (mul V.val C.val))) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := neg_valid (sub_valid (mul_valid U.property C.property) (mul_valid V.property C.property)))
        (hright := sub_valid (neg_valid (mul_valid U.property C.property))
          (neg_valid (mul_valid V.property C.property)))
      let X := ComplexRawQuotient.ofRaw U.val U.property
      let Y := ComplexRawQuotient.ofRaw V.val V.property
      let Z := ComplexRawQuotient.ofRaw C.val C.property
      change -(X*Z-Y*Z)= -(X*Z)- -(Y*Z)
      grind only
    have hn' := Small.congr
      (neg_valid (sub_valid (mul_valid U.property C.property) (mul_valid V.property C.property)))
      (sub_valid (neg_valid (mul_valid U.property C.property)) (neg_valid (mul_valid V.property C.property))) hev hneg
    simpa only [pairedSquareDensity,hed,Bool.false_eq_true,if_false,U,V,C,actualSquareKernelSample,rationalSquaredKernel] using hn'
  · simpa only [pairedSquareDensity,hed,if_true,U,V,C,actualSquareKernelSample,rationalSquaredKernel] using hd

end ComputableAnalysis.ModularForms
