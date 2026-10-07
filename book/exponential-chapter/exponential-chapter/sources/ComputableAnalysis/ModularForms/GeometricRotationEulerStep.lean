import ComputableAnalysis.GeometricRotationODE

/-! Quadratic local errors for rational Euler steps of the geometric rotation chart. -/
namespace ComputableAnalysis.ModularForms
open GeometricRotationODE

private theorem secantToStep (x v h : Rat) (hh : h≠0) (hb : qabs (x/h-v)≤12*qabs h) :
    qabs (x-h*v)≤12*qabs h*qabs h := by
  have hc := Rat.mul_inv_cancel h hh
  have he : x-h*v=(x/h-v)*h := by grind [Rat.div_def]
  rw [he,qabs_mul]
  exact Rat.mul_le_mul_of_nonneg_right hb (qabs_nonneg h)

theorem geometricRotation_euler_re_error (t h : Rat)
    (ht0 : 0≤t) (ht1 : t≤1) (hth0 : 0≤t+h) (hth1 : t+h≤1) :
    qabs (pointRe (t+h)-pointRe t-h*pointReDerivative t)≤12*qabs h*qabs h := by
  by_cases hh : h=0
  · subst h; simp [qabs,Rat.add_zero,Rat.sub_self,Rat.sub_eq_add_neg,Rat.neg_zero]
  · exact secantToStep _ _ h hh (pointRe_secant_error_le_twelve ht0 ht1 hth0 hth1 hh)

theorem geometricRotation_euler_im_error (t h : Rat)
    (ht0 : 0≤t) (ht1 : t≤1) (hth0 : 0≤t+h) (hth1 : t+h≤1) :
    qabs (pointIm (t+h)-pointIm t-h*pointImDerivative t)≤12*qabs h*qabs h := by
  by_cases hh : h=0
  · subst h; simp [qabs,Rat.add_zero,Rat.sub_self,Rat.sub_eq_add_neg,Rat.neg_zero]
  · exact secantToStep _ _ h hh (pointIm_secant_error_le_twelve ht0 ht1 hth0 hth1 hh)

def geometricRotationEulerStep (t h : Rat) : QComplex :=
  QComplex.add (pointComplex t)
    (QComplex.mul ⟨h,0⟩ (QComplex.mul (angularVelocity t) (pointComplex t)))

theorem geometricRotationEulerStep_re_bound (t h : Rat)
    (ht0 : 0≤t) (ht1 : t≤1) (hth0 : 0≤t+h) (hth1 : t+h≤1) :
    qabs ((pointComplex (t+h)).re-(geometricRotationEulerStep t h).re)≤12*qabs h*qabs h := by
  unfold geometricRotationEulerStep
  rw [← pointComplexDerivative_eq_angularVelocity_mul_point]
  change qabs (pointRe (t+h)-(pointRe t+(h*pointReDerivative t-0*pointImDerivative t)))≤_
  have he : pointRe (t+h)-(pointRe t+(h*pointReDerivative t-0*pointImDerivative t))=
      pointRe (t+h)-pointRe t-h*pointReDerivative t := by grind
  rw [he]
  exact geometricRotation_euler_re_error t h ht0 ht1 hth0 hth1

theorem geometricRotationEulerStep_im_bound (t h : Rat)
    (ht0 : 0≤t) (ht1 : t≤1) (hth0 : 0≤t+h) (hth1 : t+h≤1) :
    qabs ((pointComplex (t+h)).im-(geometricRotationEulerStep t h).im)≤12*qabs h*qabs h := by
  unfold geometricRotationEulerStep
  rw [← pointComplexDerivative_eq_angularVelocity_mul_point]
  change qabs (pointIm (t+h)-(pointIm t+(h*pointImDerivative t+0*pointReDerivative t)))≤_
  have he : pointIm (t+h)-(pointIm t+(h*pointImDerivative t+0*pointReDerivative t))=
      pointIm (t+h)-pointIm t-h*pointImDerivative t := by grind
  rw [he]
  exact geometricRotation_euler_im_error t h ht0 ht1 hth0 hth1

end ComputableAnalysis.ModularForms
