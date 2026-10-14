import ComputableAnalysis.ModularForms.ExponentialQuadraticRemainder
import ComputableAnalysis.ModularForms.GeometricRotationEulerStability

/-! Actual exponential errors for rational geometric Euler factors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def geometricAngularIncrement (t h : Rat) : Scalar :=
  ⟨ofQComplex ⟨0,h*(2/(1+t*t))⟩,ofQComplex_valid _⟩

def geometricEulerFactor (t h : Rat) : Scalar :=
  ⟨ofQComplex ⟨1,h*(2/(1+t*t))⟩,ofQComplex_valid _⟩

def geometricFactorRadius : QPos := ⟨3,by decide⟩

theorem geometricAngularIncrement_small (t h : Rat) (hh : 0≤h) :
    Small (geometricAngularIncrement t h).val (2*h) := by
  have hv := geometricRotationSpeed_bound t
  have hm := Rat.mul_le_mul_of_nonneg_left hv hh
  have he : qabs (h*(2/(1+t*t)))=h*qabs (2/(1+t*t)) := by
    rw [qabs_mul,qabs_eq_self_of_nonneg hh]
  have hb : qabs (h*(2/(1+t*t)))≤2*h := by rw [he]; grind only
  have hlo := neg_qabs_le_self (h*(2/(1+t*t)))
  have hhi := self_le_qabs (h*(2/(1+t*t)))
  refine ⟨?_,?_,?_,?_⟩
  · intro n m; change -(2*h)≤0; grind
  · intro n m; change (0:Rat)≤2*h; exact Rat.mul_nonneg (by decide) hh
  · intro n m; change -(2*h)≤h*(2/(1+t*t)); grind only
  · intro n m; change h*(2/(1+t*t))≤2*h; exact Rat.le_trans hhi hb

theorem geometricAngularIncrement_chart (t h : Rat) (hh : 0≤h) (h1 : h≤1) :
    (exponentialChart geometricFactorRadius).domain (geometricAngularIncrement t h) :=
  ⟨2*h,Rat.mul_nonneg (by decide) hh,by change 2*h<(3:Rat); grind,
    geometricAngularIncrement_small t h hh⟩

theorem geometricEulerFactor_linear (t h : Rat) :
    (add (ofQComplex QComplex.one) (geometricAngularIncrement t h).val).Equiv
      (geometricEulerFactor t h).val := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  simp only [geometricAngularIncrement,geometricEulerFactor,add,ofQComplex,QBox.add,QBox.point,
    QComplex.add,QComplex.one,QBox.Overlaps,QComplex.le_def]
  constructor <;> constructor <;> grind

theorem geometricEulerFactor_exponential_error (t h : Rat) (hh : 0≤h) (h1 : h≤1) :
    Small (sub (entireExponentialValue (geometricAngularIncrement t h)).val (geometricEulerFactor t h).val)
      (4*exponentialQuadraticConstant geometricFactorRadius*h*h) := by
  have hb := entireExponential_linear_error geometricFactorRadius (geometricAngularIncrement t h)
    (geometricAngularIncrement_chart t h hh h1) (2*h) (Rat.mul_nonneg (by decide) hh)
    (geometricAngularIncrement_small t h hh)
  have he : exponentialQuadraticConstant geometricFactorRadius*(2*h)^2=
      4*exponentialQuadraticConstant geometricFactorRadius*h*h := by
    simp only [Rat.pow_succ,Rat.pow_zero]
    grind
  rw [he] at hb
  exact Small.congr
    (sub_valid (entireExponentialValue (geometricAngularIncrement t h)).property
      (add_valid (ofQComplex_valid _) (geometricAngularIncrement t h).property))
    (sub_valid (entireExponentialValue (geometricAngularIncrement t h)).property (geometricEulerFactor t h).property)
    (FunctionTheory.sub_congr (equiv_refl _ (entireExponentialValue (geometricAngularIncrement t h)).property)
      (geometricEulerFactor_linear t h)) hb

theorem geometricEulerFactor_step (t h : Rat) (p : QComplex) :
    QComplex.mul ⟨1,h*(2/(1+t*t))⟩ p=geometricRotationEulerAt t h p := by
  apply RotationSeries.qcomplex_ext <;> simp only [QComplex.mul,geometricRotationEulerAt] <;> grind

end ComputableAnalysis.ModularForms
