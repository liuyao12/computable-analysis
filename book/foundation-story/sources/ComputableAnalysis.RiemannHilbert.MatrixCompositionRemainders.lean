import ComputableAnalysis.RiemannHilbert.HolomorphicMatrixDifferentiation
import ComputableAnalysis.RiemannHilbert.LinearFieldProductBounds

/-! Uniform differentiation of actual finite operator compositions. The
radius is independent of the input vector and its coordinate bound. Exact
agreement transfers the resulting estimates to any equal derivative name. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory LocalSystem
variable {n m k : Nat} {D E : Scalar → Prop}

def compositionSlope (G DG : Field (n := n) (m := m) D)
    (H DH : Field (n := m) (m := k) E) (hDE : ∀ z, D z → E z) :
    Field (n := n) (m := k) D :=
  fun z hz => ValueMap.sum ((G z hz).followedBy (DH z (hDE z hz)))
    ((DG z hz).followedBy (H z (hDE z hz)))

theorem compositionSlope_linear (G DG : Field (n := n) (m := m) D)
    (H DH : Field (n := m) (m := k) E) (hDE : ∀ z, D z → E z)
    (hG : ∀ z hz, IsLinear (G z hz)) (hDG : ∀ z hz, IsLinear (DG z hz))
    (hH : ∀ z hz, IsLinear (H z hz)) (hDH : ∀ z hz, IsLinear (DH z hz))
    (z : Scalar) (hz : D z) : IsLinear (compositionSlope G DG H DH hDE z hz) :=
  ValueMap.sum_linear _ _ (IsLinear.followedBy (hG z hz) (hDH z (hDE z hz)))
    (IsLinear.followedBy (hDG z hz) (hH z (hDE z hz)))

theorem operatorRemainder_congr (G DG H DH : Field (n := n) (m := m) D)
    (hG : ∀ z hz, (G z hz).Equiv (H z hz))
    (hDG : ∀ z hz, (DG z hz).Equiv (DH z hz))
    (w z : Scalar) (hw : D w) (hz : D z) (x : Fiber n) :
    operatorRemainder G DG w z hw hz x ≈ operatorRemainder H DH w z hw hz x :=
  Fiber.sub_congr (Fiber.sub_congr (hG z hz x) (hG w hw x))
    (Fiber.scale_congr (equiv_refl _ (sub_valid z.property w.property)) (hDG w hw x))

/-- The actual entry derivative of a composition agrees with the operator
product rule on every represented vector, including at rank zero. -/
theorem composeFields_derivative (G : Field (n := n) (m := m) D)
    (H : Field (n := m) (m := k) E) (hD : ScalarTopology.OpenData D)
    (hE : ∀ z w, z ≈ w → (E z ↔ E w)) (hDE : ∀ z, D z → E z)
    (hG : ∀ z w hz hw, z ≈ w → (G z hz).Equiv (G w hw))
    (hH : ∀ z w hz hw, z ≈ w → (H z hz).Equiv (H w hw))
    (hGl : ∀ z hz, IsLinear (G z hz)) (hHl : ∀ z hz, IsLinear (H z hz))
    (hGM : MatrixHolomorphic G hD.invariant hG) (hHM : MatrixHolomorphic H hE hH)
    (z : Scalar) (hz : D z) :
    (derivativeField (composeFields_holomorphic G H hD hE hDE hG hH hGl hHl hGM hHM) z hz).Equiv
      (compositionSlope G (derivativeField hGM) H (derivativeField hHM) hDE z hz) := by
  apply (ValueMap.linear_equiv_iff_basis _ _ (derivativeField_linear _ z hz)
    (compositionSlope_linear G _ H _ hDE hGl (derivativeField_linear hGM) hHl
      (derivativeField_linear hHM) z hz)).mpr
  intro i j
  have hd := action_derivative hHl hHM (appliedToConstant G hD.invariant hG (Fiber.basis i))
    (appliedToConstant_holomorphic G hD hG hGl hGM (Fiber.basis i)) hDE z hz
  have hi := appliedToConstant_derivative hD hGl hGM (Fiber.basis i) z hz
  exact equiv_trans ((matrixEntry (derivativeField
    (composeFields_holomorphic G H hD hE hDE hG hH hGl hHl hGM hHM)) i j z hz).property)
    ((DomainVectorFunctions.derivative
      (action H hH (appliedToConstant G hD.invariant hG (Fiber.basis i)) hDE)
      (action_holomorphic H hE hH hHl hHM _
        (appliedToConstant_holomorphic G hD hG hGl hGM (Fiber.basis i)) hDE) z hz).property j)
    (((compositionSlope G (derivativeField hGM) H (derivativeField hHM) hDE z hz).eval
      (Fiber.basis i)).property j)
    (derivativeField_entry _ i j z hz)
    (Setoid.trans hd (Fiber.add_congr (Setoid.refl _) ((H z (hDE z hz)).congr hi)) j)

/-- Uniform operator remainders compose with a radius independent of the
vector and its bound. The quantitative product estimate carries the common
input bound through all three finite remainder terms. -/
theorem compose_uniform_remainder (G DG : Field (n := n) (m := m) D)
    (H DH : Field (n := m) (m := k) D) (hHl : ∀ z hz, IsLinear (H z hz))
    (P Q B C : Rat) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hHbound : ∀ z hz A, 0 ≤ A → ∀ x, CoordinateBound x A → CoordinateBound ((H z hz).eval x) (P*A))
    (hDHbound : ∀ z hz A, 0 ≤ A → ∀ x, CoordinateBound x A → CoordinateBound ((DH z hz).eval x) (Q*A))
    (hGbound : ∀ z hz A, 0 ≤ A → ∀ x, CoordinateBound x A → CoordinateBound ((G z hz).eval x) (B*A))
    (hDGbound : ∀ z hz A, 0 ≤ A → ∀ x, CoordinateBound x A → CoordinateBound ((DG z hz).eval x) (C*A))
    (deltaG deltaH : QPos → QPos)
    (hGrem : ∀ (eps R : QPos) w z hw hz, R.val ≤ (deltaG eps).val →
      Small (sub z.val w.val) R.val → ∀ A, 0 ≤ A → ∀ x, CoordinateBound x A →
        CoordinateBound (operatorRemainder G DG w z hw hz x) ((eps.val*R.val)*A))
    (hHrem : ∀ (eps R : QPos) w z hw hz, R.val ≤ (deltaH eps).val →
      Small (sub z.val w.val) R.val → ∀ A, 0 ≤ A → ∀ x, CoordinateBound x A →
        CoordinateBound (operatorRemainder H DH w z hw hz x) ((eps.val*R.val)*A))
    (eps R : QPos) (w z : Scalar) (hw : D w) (hz : D z)
    (hR : R.val ≤ (productDelta P Q B C hP hQ hB hC deltaG deltaH eps).val)
    (hzw : Small (sub z.val w.val) R.val)
    (A : Rat) (hA : 0 ≤ A) (x : Fiber n) (hx : CoordinateBound x A) :
    CoordinateBound (operatorRemainder (composeFields G H (fun _ hz => hz))
      (compositionSlope G DG H DH (fun _ hz => hz)) w z hw hz x) ((eps.val*R.val)*A) := by
  let eta := errorShare P B hP hB eps
  have hGa := Rat.le_trans (Rat.le_trans hR (smallerRadius_le_left _ _)) (smallerRadius_le_left _ _)
  have hHa := Rat.le_trans (Rat.le_trans hR (smallerRadius_le_left _ _)) (smallerRadius_le_right _ _)
  have hH1 := Rat.le_trans (Rat.le_trans hR (smallerRadius_le_right _ _)) (smallerRadius_le_left _ _)
  have hQuad := Rat.le_trans (Rat.le_trans hR (smallerRadius_le_right _ _)) (smallerRadius_le_right _ _)
  have h1 := hHbound z hz ((eta.val*R.val)*A)
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt eta.property) (Rat.le_of_lt R.property)) hA)
    _ (hGrem eta R w z hw hz hGa hzw A hA x hx)
  let d : Scalar := ⟨sub z.val w.val,sub_valid z.property w.property⟩
  have hs := bound_scale (c := d) (x := (DG w hw).eval x)
    (Rat.le_of_lt R.property) (Rat.mul_nonneg hC hA) hzw (hDGbound w hw A hA x hx)
  have h2 := operator_difference_bound H DH Q hQ hDHbound w z hw hz R hzw
    (by intro L hL y hy; simpa only [Rat.one_mul] using hHrem ⟨1,by decide +kernel⟩ R w z hw hz hH1 hzw L hL y hy)
    (2*R.val*(C*A))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt R.property)) (Rat.mul_nonneg hC hA))
    (Fiber.scale d ((DG w hw).eval x)) hs
  have h3 := hHrem eta R w z hw hz hHa hzw (B*A) (Rat.mul_nonneg hB hA)
    ((G w hw).eval x) (hGbound w hw A hA x hx)
  have hb := bound_congr (Setoid.symm (product_remainder H DH
    (fun z hz => (G z hz).eval x) (fun z hz => (DG z hz).eval x) hHl w z hw hz))
    (bound_add (bound_add h1 h2) h3)
  intro i
  apply (hb i).mono
  have he := Rat.mul_le_mul_of_nonneg_right (error_budget P Q B C hP hQ hB hC eps R hQuad) hA
  change P*((eta.val*R.val)*A)+((2*Q+1)*R.val)*(2*R.val*(C*A))+(eta.val*R.val)*(B*A) ≤ (eps.val*R.val)*A
  change ((P*eta.val+eta.val*B)*R.val+(2*(2*Q+1)*C)*R.val*R.val)*A ≤ (eps.val*R.val)*A at he
  grind only

end ComputableAnalysis.RiemannHilbert.LinearField
