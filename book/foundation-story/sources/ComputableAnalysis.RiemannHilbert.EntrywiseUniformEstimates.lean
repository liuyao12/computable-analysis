import ComputableAnalysis.RiemannHilbert.FiniteMatrixBounds
import ComputableAnalysis.RiemannHilbert.UniformMatrixDerivative

/-! Finite entry estimates imply actual operator estimates. The first-order
remainder is itself a linear map, so basis expansion proves a uniform bound
for every represented vector, including empty and rectangular ranks. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory LocalSystem DomainFunctions
set_option autoImplicit false
variable {n m : Nat} {D : Scalar → Prop}

def remainderMap (G DG : Field (n := n) (m := m) D)
    (w z : Scalar) (hw : D w) (hz : D z) : ValueMap (Fiber n) (Fiber m) :=
  ValueMap.difference (ValueMap.difference (G z hz) (G w hw))
    ((DG w hw).followedBy (Fiber.scaleMap ⟨sub z.val w.val,sub_valid z.property w.property⟩))

theorem remainderMap_linear (G DG : Field (n := n) (m := m) D)
    (hG : ∀ z hz, IsLinear (G z hz)) (hDG : ∀ z hz, IsLinear (DG z hz))
    (w z : Scalar) (hw : D w) (hz : D z) : IsLinear (remainderMap G DG w z hw hz) :=
  ValueMap.difference_linear _ _ (ValueMap.difference_linear _ _ (hG z hz) (hG w hw))
    (IsLinear.followedBy (hDG w hw) (Fiber.scaleMap_linear _))

def entryError (n : Nat) (eps : QPos) : QPos :=
  divideRadius eps ⟨2*(n : Rat)+1,by have hn : 0 ≤ (n : Rat) := Rat.natCast_nonneg; grind only⟩

theorem entryError_budget (n : Nat) (eps : QPos) : 2*(n : Rat)*(entryError n eps).val ≤ eps.val := by
  have he := divideRadius_identity eps (⟨2*(n : Rat)+1,by have hn : 0 ≤ (n : Rat) := Rat.natCast_nonneg; grind only⟩ : QPos)
  have hm := Rat.mul_le_mul_of_nonneg_right (show 2*(n : Rat) ≤ 2*(n : Rat)+1 by grind only)
    (Rat.le_of_lt (entryError n eps).property)
  change (2*(n : Rat)+1)*(entryError n eps).val = eps.val at he
  grind only

theorem operator_bound_from_entries (G : Field (n := n) (m := m) D)
    (hG : ∀ z hz, IsLinear (G z hz)) (B : Rat) (hB : 0 ≤ B)
    (hb : ∀ z hz i j, Small (((G z hz).eval (Fiber.basis i)).val j) B)
    (z : Scalar) (hz : D z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((G z hz).eval x) ((2*(n : Rat)*B)*E) :=
  ValueMap.linear_bound_of_basis (G z hz) (hG z hz) B hB (hb z hz) x E hE hx

theorem operator_uniform_remainder_from_entries (G DG : Field (n := n) (m := m) D)
    (hG : ∀ z hz, IsLinear (G z hz)) (hDG : ∀ z hz, IsLinear (DG z hz))
    (delta : QPos → QPos)
    (hrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (delta eps).val →
      Small (sub z.val w.val) H.val → ∀ i j,
      Small ((operatorRemainder G DG w z hw hz (Fiber.basis i)).val j) (eps.val*H.val))
    (eps H : QPos) (w z : Scalar) (hw : D w) (hz : D z)
    (hH : H.val ≤ (delta (entryError n eps)).val) (hzw : Small (sub z.val w.val) H.val)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound (operatorRemainder G DG w z hw hz x) ((eps.val*H.val)*E) := by
  let eta := entryError n eps
  have hb := ValueMap.linear_bound_of_basis (remainderMap G DG w z hw hz)
    (remainderMap_linear G DG hG hDG w z hw hz) (eta.val*H.val)
    (Rat.mul_nonneg (Rat.le_of_lt eta.property) (Rat.le_of_lt H.property))
    (hrem eta H w z hw hz hH hzw) x E hE hx
  intro j
  apply (hb j).mono
  have hm := Rat.mul_le_mul_of_nonneg_right (entryError_budget n eps)
    (Rat.mul_nonneg (Rat.le_of_lt H.property) hE)
  change (2*(n : Rat)*(eta.val*H.val))*E ≤ (eps.val*H.val)*E
  grind only

end ComputableAnalysis.RiemannHilbert.LinearField
