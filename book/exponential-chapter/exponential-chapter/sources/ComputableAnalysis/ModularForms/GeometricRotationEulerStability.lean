import ComputableAnalysis.ModularForms.GeometricRotationEulerStep

/-! Rational stability of Euler steps for the geometric rotation equation. -/
namespace ComputableAnalysis.ModularForms
open GeometricRotationODE

def geometricRotationEulerAt (t h : Rat) (p : QComplex) : QComplex :=
  ⟨p.re-h*(2/(1+t*t))*p.im,p.im+h*(2/(1+t*t))*p.re⟩

theorem geometricRotationSpeed_bound (t : Rat) : qabs (2/(1+t*t))≤2 := by
  have ht : 0≤t*t := by
    by_cases h : 0≤t
    · exact Rat.mul_nonneg h h
    · have hn : 0≤ -t := by grind
      have hm := Rat.mul_nonneg hn hn
      grind only
  have hp : 0<1+t*t := by grind
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hc := Rat.mul_inv_cancel (1+t*t) (Rat.ne_of_gt hp)
  have hb : 0≤2/(1+t*t) := Rat.mul_nonneg (by decide) hi
  rw [qabs_eq_self_of_nonneg hb]
  apply Rat.le_of_mul_le_mul_right (c := 1+t*t)
  · have he : (2/(1+t*t))*(1+t*t)=2 := by grind [Rat.div_def]
    rw [he]
    grind
  · exact hp

theorem geometricRotationEulerAt_chart (t h : Rat) :
    geometricRotationEulerAt t h (pointComplex t)=geometricRotationEulerStep t h := by
  apply RotationSeries.qcomplex_ext <;>
    simp [geometricRotationEulerAt,geometricRotationEulerStep,angularVelocity,QComplex.mul,QComplex.add]
  · grind
  · grind

private theorem eulerCoordinate_stability (x y c E : Rat) (hE : 0≤E)
    (hx : qabs x≤E) (hy : qabs y≤E) (hc : qabs c≤2) (h : Rat) :
    qabs (x+h*c*y)≤(1+2*qabs h)*E := by
  have hp := qabs_mul h c
  have hhc : qabs (h*c)≤2*qabs h := by
    rw [hp]
    have hm := Rat.mul_le_mul_of_nonneg_left hc (qabs_nonneg h)
    grind
  have hprod : qabs ((h*c)*y)≤(2*qabs h)*E := by
    rw [qabs_mul]
    have h1 := Rat.mul_le_mul_of_nonneg_left hy (qabs_nonneg (h*c))
    have h2 := Rat.mul_le_mul_of_nonneg_right hhc hE
    exact Rat.le_trans h1 h2
  have hs := qabs_add_le x ((h*c)*y)
  have he : x+h*c*y=x+(h*c)*y := by grind
  rw [he]
  grind only

theorem geometricRotationEulerAt_re_stability (t h : Rat) (p q : QComplex) (E : Rat)
    (hE : 0≤E) (hre : qabs (p.re-q.re)≤E) (him : qabs (p.im-q.im)≤E) :
    qabs ((geometricRotationEulerAt t h p).re-(geometricRotationEulerAt t h q).re)≤
      (1+2*qabs h)*E := by
  have hb := eulerCoordinate_stability (p.re-q.re) (q.im-p.im) (2/(1+t*t)) E hE hre
    (by
      have he : q.im-p.im= -(p.im-q.im) := by grind
      rw [he,qabs_neg]
      exact him) (geometricRotationSpeed_bound t) h
  have he : (geometricRotationEulerAt t h p).re-(geometricRotationEulerAt t h q).re=
      (p.re-q.re)+h*(2/(1+t*t))*(q.im-p.im) := by dsimp [geometricRotationEulerAt]; grind
  rw [he]
  exact hb

theorem geometricRotationEulerAt_im_stability (t h : Rat) (p q : QComplex) (E : Rat)
    (hE : 0≤E) (hre : qabs (p.re-q.re)≤E) (him : qabs (p.im-q.im)≤E) :
    qabs ((geometricRotationEulerAt t h p).im-(geometricRotationEulerAt t h q).im)≤
      (1+2*qabs h)*E := by
  have hb := eulerCoordinate_stability (p.im-q.im) (p.re-q.re) (2/(1+t*t)) E hE him hre
    (geometricRotationSpeed_bound t) h
  have he : (geometricRotationEulerAt t h p).im-(geometricRotationEulerAt t h q).im=
      (p.im-q.im)+h*(2/(1+t*t))*(p.re-q.re) := by dsimp [geometricRotationEulerAt]; grind
  rw [he]
  exact hb

private theorem coordinateError_add (x y z A B : Rat)
    (hxy : qabs (x-y)≤A) (hzy : qabs (z-y)≤B) : qabs (x-z)≤A+B := by
  have he : y-z= -(z-y) := by grind
  have hyz : qabs (y-z)≤B := by rw [he,qabs_neg]; exact hzy
  have ht := qabs_add_le (x-y) (y-z)
  have hs : (x-y)+(y-z)=x-z := by grind
  rw [hs] at ht
  grind only

theorem geometricRotationEulerAt_error_step (t h : Rat) (p : QComplex) (E : Rat)
    (ht0 : 0≤t) (ht1 : t≤1) (hth0 : 0≤t+h) (hth1 : t+h≤1) (hE : 0≤E)
    (hre : qabs (p.re-(pointComplex t).re)≤E)
    (him : qabs (p.im-(pointComplex t).im)≤E) :
    qabs ((geometricRotationEulerAt t h p).re-(pointComplex (t+h)).re)≤
      (1+2*qabs h)*E+12*qabs h*qabs h ∧
    qabs ((geometricRotationEulerAt t h p).im-(pointComplex (t+h)).im)≤
      (1+2*qabs h)*E+12*qabs h*qabs h := by
  have hsr := geometricRotationEulerAt_re_stability t h p (pointComplex t) E hE hre him
  have hsi := geometricRotationEulerAt_im_stability t h p (pointComplex t) E hE hre him
  rw [geometricRotationEulerAt_chart] at hsr hsi
  exact ⟨coordinateError_add _ _ _ _ _ hsr (geometricRotationEulerStep_re_bound t h ht0 ht1 hth0 hth1),
    coordinateError_add _ _ _ _ _ hsi (geometricRotationEulerStep_im_bound t h ht0 ht1 hth0 hth1)⟩

end ComputableAnalysis.ModularForms
