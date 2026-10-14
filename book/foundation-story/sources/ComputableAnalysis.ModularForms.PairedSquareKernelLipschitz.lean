import ComputableAnalysis.ModularForms.PairedRiccatiGlobalSegmentVariation
import ComputableAnalysis.ModularForms.PairedSquareKernelOscillation

/-! An explicit rational parameter Lipschitz constant for actual square kernels. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

def squareKernelLipschitzConstant (R : Rat) : Rat :=
  2*2854864386*R*(2*(1/R)*(1/R))+
    2*5369840*(2*((2*R)*(R*R)⁻¹)^3*R)

theorem actualSquareRiccati_parameter_difference (a : Scalar) (edge : HalfEdge)
    (R u v : Rat) (hR : 0<R) :
    let z : Scalar := ⟨add a.val (ofQComplex (QComplex.scaleRat R (point edge u))),
      add_valid a.property (ofQComplex_valid _)⟩
    let w : Scalar := ⟨add a.val (ofQComplex (QComplex.scaleRat R (point edge v))),
      add_valid a.property (ofQComplex_valid _)⟩
    Small (sub (pairedEntireRiccatiMap.eval z trivial).val
      (pairedEntireRiccatiMap.eval w trivial).val) (2854864386*R*qabs (u-v)) := by
  intro z w
  by_cases huv : u=v
  · subst v
    have he : zero.Equiv (sub (pairedEntireRiccatiMap.eval z trivial).val
        (pairedEntireRiccatiMap.eval z trivial).val) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ofQComplex_valid _)
        (hright := sub_valid (pairedEntireRiccatiMap.eval z trivial).property
          (pairedEntireRiccatiMap.eval z trivial).property)
      let Z := ComplexRawQuotient.ofRaw (pairedEntireRiccatiMap.eval z trivial).val
        (pairedEntireRiccatiMap.eval z trivial).property
      change 0=Z-Z
      grind only
    have hb := Small.congr (ofQComplex_valid _)
      (sub_valid (pairedEntireRiccatiMap.eval z trivial).property
        (pairedEntireRiccatiMap.eval z trivial).property) he (Small.zero (Rat.le_refl (a:=0)))
    have ha : qabs (u-u)=0 := by unfold qabs; grind
    rw [ha,Rat.mul_zero]
    exact hb
  · have hdist : 0<qabs (u-v) := qabs_pos_of_ne (by intro h; apply huv; grind only)
    let W : QPos := ⟨R*qabs (u-v),Rat.mul_pos hR hdist⟩
    let qu := QComplex.scaleRat R (point edge u)
    let qv := QComplex.scaleRat R (point edge v)
    have hnorm := scaledSquarePoint_difference_norm edge u v R (Rat.le_of_lt hR)
    have hc := (BoxApproximation.rational_small (QComplex.sub qu qv)).mono
      (Rat.le_trans (rational_coordinateBound_le_normBound _) (by rw [hnorm]; exact Rat.le_refl))
    have hs := Small.congr (ofQComplex_valid _)
      (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
      (equiv_symm (rationalRaw_sub_constants qu qv)) hc
    have hd := Small.congr (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
      (sub_valid z.property w.property)
      (equiv_symm (Centered.translate_difference a
        ⟨ofQComplex qv,ofQComplex_valid _⟩ ⟨ofQComplex qu,ofQComplex_valid _⟩)) hs
    have hb := pairedRiccati_affine_segment_variation w z W hd
    exact hb.mono (by change 2854864386*(R*qabs (u-v))≤2854864386*R*qabs (u-v); grind only)

theorem actualSquareKernel_parameter_lipschitz (a : Scalar) (edge : HalfEdge)
    (R u v : Rat) (hR : 0<R) (hu : 0≤u) (hu1 : u≤1) (hv : 0≤v) (hv1 : v≤1) :
    Small (sub (actualSquareKernelSample a edge R u).val
      (actualSquareKernelSample a edge R v).val)
      (squareKernelLipschitzConstant R*qabs (u-v)) := by
  have he := actualSquareRiccati_parameter_difference a edge R u v hR
  have hb := pairedRiccati_square_kernel_product_difference_bound
    ⟨add a.val (ofQComplex (QComplex.scaleRat R (point edge u))),add_valid a.property (ofQComplex_valid _)⟩
    ⟨add a.val (ofQComplex (QComplex.scaleRat R (point edge v))),add_valid a.property (ofQComplex_valid _)⟩
    edge u v R (2854864386*R*qabs (u-v)) hR hu hu1 hv hv1
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hR)) (qabs_nonneg _)) he
  apply hb.mono
  unfold squareKernelLipschitzConstant
  grind only

end ComputableAnalysis.ModularForms
