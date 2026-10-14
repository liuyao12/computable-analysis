import ComputableAnalysis.ModularForms.SquareKernelContinuity

/-! Kernel continuity expressed directly in square-edge parameter distance. -/
namespace ComputableAnalysis.ModularForms
open QComplex PDE.CauchyContour

theorem scaledSquarePoint_difference_norm (edge : HalfEdge) (u v R : Rat)
    (hR : 0≤R) :
    normBound (sub (scaleRat R (point edge u)) (scaleRat R (point edge v)))=
      R*qabs (u-v) := by
  have ha : qabs (R*(u-v))=R*qabs (u-v) := by
    rw [qabs_mul]
    have h : qabs R=R := by unfold qabs; split <;> grind only
    rw [h]
  have hb : qabs (-(R*(u-v)))=R*qabs (u-v) := by
    unfold qabs at *
    grind
  cases edge with
  | mk quarter upper =>
    cases quarter <;> cases upper <;>
      unfold point rotation orientation scaleRat mul sub add neg normBound <;>
      simp only [if_true] <;> unfold qabs at * <;> grind

theorem squareSquaredInverse_parameter_bound (edge : HalfEdge) (u v R : Rat)
    (hu : 0≤u) (hu1 : u≤1) (hv : 0≤v) (hv1 : v≤1) (hR : 0<R) :
    normBound (sub
      (mul (inverse (scaleRat R (point edge u))) (inverse (scaleRat R (point edge u))))
      (mul (inverse (scaleRat R (point edge v))) (inverse (scaleRat R (point edge v)))))≤
      (2*((2*R)*(R*R)⁻¹)^3*R)*qabs (u-v) := by
  have h := squareSquaredInverse_difference_bound edge u v R hu hu1 hv hv1 hR
  rw [scaledSquarePoint_difference_norm edge u v R (Rat.le_of_lt hR)] at h
  exact Rat.le_trans h (by grind only)

end ComputableAnalysis.ModularForms
