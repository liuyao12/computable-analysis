import ComputableAnalysis.RiemannHilbert.MatrixCompositionRemainders
import ComputableAnalysis.RiemannHilbert.UniformCoordinateRemainder

/-! Uniform operator remainders under a supplied scalar coordinate map.
The computed radius separates the matrix remainder from the coordinate
remainder. All estimates apply to actual represented points and vectors;
no derivative identity or analytic existence is assumed by the algebra. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory LocalSystem
variable {n m : Nat} {D E : Scalar → Prop}

def coordinateField (G : Field (n := n) (m := m) D)
    (g : ∀ z, E z → Scalar) (himage : ∀ z hz, D (g z hz)) : Field (n := n) (m := m) E :=
  fun z hz => G (g z hz) (himage z hz)

def coordinateSlope (DG : Field (n := n) (m := m) D)
    (g dg : ∀ z, E z → Scalar) (himage : ∀ z hz, D (g z hz)) : Field (n := n) (m := m) E :=
  fun z hz => (DG (g z hz) (himage z hz)).followedBy (Fiber.scaleMap (dg z hz))

theorem coordinateSlope_linear (DG : Field (n := n) (m := m) D)
    (g dg : ∀ z, E z → Scalar) (himage : ∀ z hz, D (g z hz))
    (hDG : ∀ z hz, IsLinear (DG z hz)) (z : Scalar) (hz : E z) :
    IsLinear (coordinateSlope DG g dg himage z hz) :=
  IsLinear.followedBy (hDG _ _) (Fiber.scaleMap_linear _)

theorem coordinateField_bound (G : Field (n := n) (m := m) D)
    (g : ∀ z, E z → Scalar) (himage : ∀ z hz, D (g z hz)) (P : Rat)
    (hG : ∀ z hz A, 0 ≤ A → ∀ x, CoordinateBound x A → CoordinateBound ((G z hz).eval x) (P*A))
    (z : Scalar) (hz : E z) (A : Rat) (hA : 0 ≤ A) (x : Fiber n) (hx : CoordinateBound x A) :
    CoordinateBound ((coordinateField G g himage z hz).eval x) (P*A) := hG _ _ A hA x hx

theorem coordinateSlope_bound (DG : Field (n := n) (m := m) D)
    (g dg : ∀ z, E z → Scalar) (himage : ∀ z hz, D (g z hz)) (Q K : Rat)
    (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hDG : ∀ z hz A, 0 ≤ A → ∀ x, CoordinateBound x A → CoordinateBound ((DG z hz).eval x) (Q*A))
    (hdg : ∀ z hz, Small (dg z hz).val K)
    (z : Scalar) (hz : E z) (A : Rat) (hA : 0 ≤ A) (x : Fiber n) (hx : CoordinateBound x A) :
    CoordinateBound ((coordinateSlope DG g dg himage z hz).eval x) ((2*K*Q)*A) := by
  have h := bound_scale (c := dg z hz) (x := (DG (g z hz) (himage z hz)).eval x)
    hK (Rat.mul_nonneg hQ hA) (hdg z hz) (hDG (g z hz) (himage z hz) A hA x hx)
  have he : 2*K*(Q*A)=(2*K*Q)*A := by grind only
  rw [he] at h
  exact h

def coordinateDelta (L Q : Rat) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (deltaF deltaG : QPos → QPos) (eps : QPos) : QPos :=
  let eta := UniformCoordinate.errorShare L Q hL hQ eps
  smallerRadius (UniformCoordinate.scaledRadius L hL (deltaF eta)) (deltaG eta)

theorem coordinate_uniform_remainder (G DG : Field (n := n) (m := m) D)
    (g dg : ∀ z, E z → Scalar) (himage : ∀ z hz, D (g z hz))
    (L Q : Rat) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hDG : ∀ z hz A, 0 ≤ A → ∀ x, CoordinateBound x A → CoordinateBound ((DG z hz).eval x) (Q*A))
    (hLip : ∀ w z hw hz (H : QPos), Small (sub z.val w.val) H.val →
      Small (sub (g z hz).val (g w hw).val) (L*H.val))
    (deltaF deltaG : QPos → QPos)
    (hFrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaF eps).val → Small (sub z.val w.val) H.val →
      ∀ A, 0 ≤ A → ∀ x, CoordinateBound x A →
        CoordinateBound (operatorRemainder G DG w z hw hz x) ((eps.val*H.val)*A))
    (hGrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaG eps).val → Small (sub z.val w.val) H.val →
      Small (sub (sub (g z hz).val (g w hw).val) (mul (dg w hw).val (sub z.val w.val))) (eps.val*H.val))
    (eps H : QPos) (w z : Scalar) (hw : E w) (hz : E z)
    (hH : H.val ≤ (coordinateDelta L Q hL hQ deltaF deltaG eps).val)
    (hzw : Small (sub z.val w.val) H.val)
    (A : Rat) (hA : 0 ≤ A) (x : Fiber n) (hx : CoordinateBound x A) :
    CoordinateBound (operatorRemainder (coordinateField G g himage) (coordinateSlope DG g dg himage)
      w z hw hz x) ((eps.val*H.val)*A) := by
  let eta := UniformCoordinate.errorShare L Q hL hQ eps
  let step : QPos := ⟨(L+1)*H.val,Rat.mul_pos (by grind only) H.property⟩
  have hF : step.val ≤ (deltaF eta).val :=
    UniformCoordinate.scaledRadius_bound L hL _ H (Rat.le_trans hH (smallerRadius_le_left _ _))
  have hC : H.val ≤ (deltaG eta).val := Rat.le_trans hH (smallerRadius_le_right _ _)
  have hImage : Small (sub (g z hz).val (g w hw).val) step.val :=
    (hLip w z hw hz H hzw).mono (by dsimp [step]; have h := H.property; grind only)
  have h1 := hFrem eta step (g w hw) (g z hz) (himage w hw) (himage z hz) hF hImage A hA x hx
  let r : Scalar := ⟨sub (sub (g z hz).val (g w hw).val) (mul (dg w hw).val (sub z.val w.val)),
    sub_valid (sub_valid (g z hz).property (g w hw).property)
      (mul_valid (dg w hw).property (sub_valid z.property w.property))⟩
  have h2 := bound_scale (c := r) (x := (DG (g w hw) (himage w hw)).eval x)
    (Rat.mul_nonneg (Rat.le_of_lt eta.property) (Rat.le_of_lt H.property)) (Rat.mul_nonneg hQ hA)
    (hGrem eta H w z hw hz hC hzw) (hDG _ _ A hA x hx)
  have he := UniformCoordinate.remainder_algebra ((G (g z hz) (himage z hz)).eval x)
    ((G (g w hw) (himage w hw)).eval x) ((DG (g w hw) (himage w hw)).eval x)
    ⟨sub z.val w.val,sub_valid z.property w.property⟩ (dg w hw)
    ⟨sub (g z hz).val (g w hw).val,sub_valid (g z hz).property (g w hw).property⟩
  have hb := bound_congr (Setoid.symm he) (bound_add h1 h2)
  intro j
  apply (hb j).mono
  have hbudget := Rat.mul_le_mul_of_nonneg_right (UniformCoordinate.error_budget L Q hL hQ eps H) hA
  change (eta.val*((L+1)*H.val))*A+2*(eta.val*H.val)*(Q*A) ≤ (eps.val*H.val)*A
  change (eta.val*((L+1)*H.val)+2*(eta.val*H.val)*Q)*A ≤ (eps.val*H.val)*A at hbudget
  grind only

end ComputableAnalysis.RiemannHilbert.LinearField
