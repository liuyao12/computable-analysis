import ComputableAnalysis.RiemannHilbert.InverseFieldAlgebra

/-! Quantitative inverse differentiation from forward derivative errors.
Uniform inverse bounds and forward errors construct the inverse error
radius; no inverse derivative or differentiability conclusion is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat} {D : Scalar → Prop}

private theorem inverse_bound_factor (V Q H E : Rat) :
    V*(((2*Q+1)*H)*(V*E))=(((V*V*(2*Q+1))*H)*E) := by grind only

private theorem inverse_remainder_factor (V Q H E eta : Rat) :
    2*H*((V*V*(2*Q+1)*H)*(Q*(V*E)))+V*((eta*H)*(V*E)) =
      (V*V*eta+2*V*V*V*(2*Q+1)*Q*H)*(H*E) := by grind only

theorem inverseRate_nonneg (V Q : Rat) (hV : 0 ≤ V) (hQ : 0 ≤ Q) :
    0 ≤ 2*V*V*V*(2*Q+1)*Q :=
  Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hV) hV) hV)
    (by grind only)) hQ

theorem inverse_difference_bound (F : (z : Scalar) → D z → LinearIso n n)
    (DF : Field (n := n) (m := n) D) (V Q : Rat) (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hInv : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E →
      CoordinateBound ((inverseField F z hz).eval x) (V*E))
    (hDF : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E →
      CoordinateBound ((DF z hz).eval x) (Q*E))
    (w z : Scalar) (hw : D w) (hz : D z) (H : QPos)
    (hzw : Small (sub z.val w.val) H.val)
    (hrem : ∀ E, 0 ≤ E → ∀ x, CoordinateBound x E →
      CoordinateBound (operatorRemainder (forwardField F) DF w z hw hz x) (H.val*E))
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((ValueMap.difference (inverseField F z hz) (inverseField F w hw)).eval x)
      (((V*V*(2*Q+1))*H.val)*E) := by
  have hy := hInv w hw E hE x hx
  have hd := operator_difference_bound (forwardField F) DF Q hQ hDF w z hw hz H hzw hrem
    (V*E) (Rat.mul_nonneg hV hE) ((inverseField F w hw).eval x) hy
  have hs := hInv z hz (((2*Q+1)*H.val)*(V*E))
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.add_nonneg (Rat.mul_nonneg (by decide +kernel) hQ) (by decide +kernel)) (Rat.le_of_lt H.property)) (Rat.mul_nonneg hV hE))
    (Fiber.sub ((forwardField F w hw).eval ((inverseField F w hw).eval x))
      ((forwardField F z hz).eval ((inverseField F w hw).eval x)))
    (fun i => RepresentedCauchySum.small_sub_symm _ _ _ (hd i))
  have he := inverse_bound_factor V Q H.val E
  rw [he] at hs
  exact bound_congr (Setoid.symm (inverse_difference F w z hw hz x)) hs

def inverseErrorShare (V : Rat) (hV : 0 ≤ V) (eps : QPos) : QPos :=
  ⟨eps.val/(2*(V*V+1)), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (Rat.mul_pos (by decide +kernel)
      (by have := Rat.mul_nonneg hV hV; grind only)))⟩

def inverseQuadraticRadius (V Q : Rat) (hV : 0 ≤ V) (hQ : 0 ≤ Q) (eps : QPos) : QPos :=
  ⟨eps.val/(2*(2*V*V*V*(2*Q+1)*Q+1)), by
    rw [Rat.div_def]
    have hp := inverseRate_nonneg V Q hV hQ
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (Rat.mul_pos (by decide +kernel) (by grind only)))⟩

def inverseDelta (V Q : Rat) (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (deltaF : QPos → QPos) (eps : QPos) : QPos :=
  smallerRadius (deltaF (inverseErrorShare V hV eps))
    (smallerRadius (deltaF ⟨1,by decide +kernel⟩) (inverseQuadraticRadius V Q hV hQ eps))

theorem inverse_error_budget (V Q : Rat) (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (eps H : QPos) (hH : H.val ≤ (inverseQuadraticRadius V Q hV hQ eps).val) :
    V*V*(inverseErrorShare V hV eps).val+2*V*V*V*(2*Q+1)*Q*H.val ≤ eps.val := by
  let eta := inverseErrorShare V hV eps
  let r := inverseQuadraticRadius V Q hV hQ eps
  let S := 2*V*V*V*(2*Q+1)*Q
  have hS : 0 ≤ S := inverseRate_nonneg V Q hV hQ
  have hVV := Rat.mul_nonneg hV hV
  have he : eta.val*(2*(V*V+1))=eps.val :=
    Rat.div_mul_cancel (by
      have h : 0 < 2*(V*V+1) := by grind only
      exact Rat.ne_of_gt h)
  have hr : r.val*(2*(S+1))=eps.val :=
    Rat.div_mul_cancel (by
      have h : 0 < 2*(S+1) := by grind only
      exact Rat.ne_of_gt h)
  have hm := Rat.mul_le_mul_of_nonneg_right (show V*V ≤ V*V+1 by grind only) (Rat.le_of_lt eta.property)
  have hn := Rat.mul_le_mul_of_nonneg_left hH (show 0 ≤ S+1 by grind only)
  have ho := Rat.mul_le_mul_of_nonneg_right (show S ≤ S+1 by grind only) (Rat.le_of_lt H.property)
  change V*V*eta.val+S*H.val ≤ eps.val
  change (S+1)*H.val ≤ (S+1)*r.val at hn
  grind only

theorem inverse_uniform_remainder (F : (z : Scalar) → D z → LinearIso n n)
    (DF : Field (n := n) (m := n) D) (V Q : Rat) (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hInv : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E →
      CoordinateBound ((inverseField F z hz).eval x) (V*E))
    (hDF : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E →
      CoordinateBound ((DF z hz).eval x) (Q*E))
    (deltaF : QPos → QPos)
    (hrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaF eps).val →
      Small (sub z.val w.val) H.val → ∀ E, 0 ≤ E → ∀ x, CoordinateBound x E →
      CoordinateBound (operatorRemainder (forwardField F) DF w z hw hz x) ((eps.val*H.val)*E))
    (eps H : QPos) (w z : Scalar) (hw : D w) (hz : D z)
    (hH : H.val ≤ (inverseDelta V Q hV hQ deltaF eps).val)
    (hzw : Small (sub z.val w.val) H.val)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound (operatorRemainder (inverseField F) (inverseSlope F DF) w z hw hz x)
      ((eps.val*H.val)*E) := by
  let eta := inverseErrorShare V hV eps
  have hFa := Rat.le_trans hH (smallerRadius_le_left _ _)
  have hF1 := Rat.le_trans (Rat.le_trans hH (smallerRadius_le_right _ _)) (smallerRadius_le_left _ _)
  have hQuad := Rat.le_trans (Rat.le_trans hH (smallerRadius_le_right _ _)) (smallerRadius_le_right _ _)
  have hy := hInv w hw E hE x hx
  have hc := hDF w hw (V*E) (Rat.mul_nonneg hV hE) ((inverseField F w hw).eval x) hy
  have hdiff := inverse_difference_bound F DF V Q hV hQ hInv hDF w z hw hz H hzw
    (by intro B hB y hb; simpa only [Rat.one_mul] using hrem ⟨1,by decide +kernel⟩ H w z hw hz hF1 hzw B hB y hb)
    (Q*(V*E)) (Rat.mul_nonneg hQ (Rat.mul_nonneg hV hE))
    ((DF w hw).eval ((inverseField F w hw).eval x)) hc
  have hscale := bound_scale
    (x := Fiber.sub ((inverseField F w hw).eval ((DF w hw).eval ((inverseField F w hw).eval x)))
      ((inverseField F z hz).eval ((DF w hw).eval ((inverseField F w hw).eval x)))) (c := ⟨sub z.val w.val,sub_valid z.property w.property⟩)
    (Rat.le_of_lt H.property)
    (Rat.mul_nonneg (Rat.mul_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg hV hV) (Rat.add_nonneg (Rat.mul_nonneg (by decide +kernel) hQ) (by decide +kernel))) (Rat.le_of_lt H.property))
      (Rat.mul_nonneg hQ (Rat.mul_nonneg hV hE)))
    hzw (fun i => RepresentedCauchySum.small_sub_symm _ _ _ (hdiff i))
  have hr := hInv z hz ((eta.val*H.val)*(V*E))
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt eta.property) (Rat.le_of_lt H.property))
      (Rat.mul_nonneg hV hE))
    _ (hrem eta H w z hw hz hFa hzw (V*E) (Rat.mul_nonneg hV hE) ((inverseField F w hw).eval x) hy)
  have hs := bound_congr (Setoid.symm (inverse_remainder F DF w z hw hz x)) (bound_sub hscale hr)
  intro i
  apply (hs i).mono
  have hb := inverse_error_budget V Q hV hQ eps H hQuad
  have hm := Rat.mul_le_mul_of_nonneg_right hb (Rat.mul_nonneg (Rat.le_of_lt H.property) hE)
  change 2*H.val*((V*V*(2*Q+1)*H.val)*(Q*(V*E)))+V*((eta.val*H.val)*(V*E)) ≤ (eps.val*H.val)*E
  change (V*V*eta.val+2*V*V*V*(2*Q+1)*Q*H.val)*(H.val*E) ≤ eps.val*(H.val*E) at hm
  rw [inverse_remainder_factor]
  simpa only [Rat.mul_assoc] using hm

end ComputableAnalysis.RiemannHilbert.LinearField
