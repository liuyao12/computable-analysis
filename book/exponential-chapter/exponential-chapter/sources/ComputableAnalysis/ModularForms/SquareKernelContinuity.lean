import ComputableAnalysis.ModularForms.RationalSquaredKernelContinuity

/-! Concrete geometric bounds for squared kernels on rational square edges. -/
namespace ComputableAnalysis.ModularForms
open QComplex PDE.CauchyContour

theorem scaledSquarePoint_norm_bounds (edge : HalfEdge) (u R : Rat)
    (hu : 0≤u) (hu1 : u≤1) (hR : 0<R) :
    normBound (scaleRat R (point edge u))≤2*R ∧
      R*R≤normSq (scaleRat R (point edge u)) := by
  have hRu : 0≤R*u := Rat.mul_nonneg (Rat.le_of_lt hR) hu
  have hRu1 : R*u≤R := by
    have h := Rat.mul_le_mul_of_nonneg_left hu1 (Rat.le_of_lt hR)
    simpa only [Rat.mul_one] using h
  have hsq : 0≤(R*u)*(R*u) := Rat.mul_nonneg hRu hRu
  cases edge with
  | mk quarter upper =>
    cases quarter <;> cases upper <;>
      unfold point rotation orientation scaleRat mul normBound normSq qabs <;>
      simp only [if_true] <;> grind

theorem squareSquaredInverse_difference_bound (edge : HalfEdge) (u v R : Rat)
    (hu : 0≤u) (hu1 : u≤1) (hv : 0≤v) (hv1 : v≤1) (hR : 0<R) :
    normBound (sub
      (mul (inverse (scaleRat R (point edge u))) (inverse (scaleRat R (point edge u))))
      (mul (inverse (scaleRat R (point edge v))) (inverse (scaleRat R (point edge v)))))≤
      2*((2*R)*(R*R)⁻¹)^3*
        normBound (sub (scaleRat R (point edge u)) (scaleRat R (point edge v))) := by
  have hU := scaledSquarePoint_norm_bounds edge u R hu hu1 hR
  have hV := scaledSquarePoint_norm_bounds edge v R hv hv1 hR
  exact rationalSquaredInverse_difference_bound _ _ (2*R) (R*R)
    (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hR)) (Rat.mul_pos hR hR)
    hU.1 hV.1 hU.2 hV.2

end ComputableAnalysis.ModularForms
