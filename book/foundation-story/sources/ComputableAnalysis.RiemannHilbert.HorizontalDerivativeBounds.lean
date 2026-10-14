import ComputableAnalysis.RiemannHilbert.HolomorphicMatrixDifferentiation

/-! A justified value bound and the actual connection equation imply a
derivative bound for every supplied horizontal linear map. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory LocalSystem
set_option autoImplicit false
variable {n m : Nat} {D : Scalar→Prop}

def compatibleDerivativeBound (P U V : Rat) : Rat := V*P+P*U

theorem compatibleDerivativeBound_nonneg (P U V : Rat) (hP : 0≤P) (hU : 0≤U) (hV : 0≤V) :
    0≤compatibleDerivativeBound P U V := Rat.add_nonneg (Rat.mul_nonneg hV hP) (Rat.mul_nonneg hP hU)

theorem compatible_derivative_linear (G DG : Field (n := n) (m := m) D)
    (A : UniformSegment.OperatorField (n := n) D) (B : UniformSegment.OperatorField (n := m) D)
    (hcompat : Compatible G DG A B)
    (hG : ∀ z hz, IsLinear (G z hz)) (hA : ∀ z hz, IsLinear (A z hz))
    (hB : ∀ z hz, IsLinear (B z hz)) (z : Scalar) (hz : D z) : IsLinear (DG z hz) :=
  IsLinear.congr (ValueMap.difference_linear _ _
    (IsLinear.followedBy (hG z hz) (hB z hz)) (IsLinear.followedBy (hA z hz) (hG z hz)))
    (ValueMap.equiv_symm (fun x => Compatible.derivative_difference DG A B hcompat z hz x))

theorem compatible_derivative_bound (G DG : Field (n := n) (m := m) D)
    (A : UniformSegment.OperatorField (n := n) D) (B : UniformSegment.OperatorField (n := m) D)
    (hcompat : Compatible G DG A B) (P U V : Rat) (hP : 0≤P) (hU : 0≤U)
    (hG : ∀ z hz E, 0≤E→∀ x, CoordinateBound x E→CoordinateBound ((G z hz).eval x) (P*E))
    (hA : ∀ z hz E, 0≤E→∀ x, CoordinateBound x E→CoordinateBound ((A z hz).eval x) (U*E))
    (hB : ∀ z hz E, 0≤E→∀ x, CoordinateBound x E→CoordinateBound ((B z hz).eval x) (V*E))
    (z : Scalar) (hz : D z) (E : Rat) (hE : 0≤E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((DG z hz).eval x) (compatibleDerivativeBound P U V*E) := by
  have hb := hB z hz (P*E) (Rat.mul_nonneg hP hE) ((G z hz).eval x) (hG z hz E hE x hx)
  have ha := hG z hz (U*E) (Rat.mul_nonneg hU hE) ((A z hz).eval x) (hA z hz E hE x hx)
  have hs := bound_congr (Setoid.symm (Compatible.derivative_difference DG A B hcompat z hz x)) (bound_sub hb ha)
  have he : V*(P*E)+P*(U*E)=compatibleDerivativeBound P U V*E := by
    dsimp [compatibleDerivativeBound]
    grind only
  rw [he] at hs
  exact hs

end ComputableAnalysis.RiemannHilbert.LinearField
