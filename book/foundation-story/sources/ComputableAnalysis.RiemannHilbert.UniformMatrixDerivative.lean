import ComputableAnalysis.RiemannHilbert.HorizontalDerivativeBounds
import ComputableAnalysis.RiemannHilbert.InverseFieldHolomorphic

/-! Actual entry and operator derivative agreement from supplied uniform
operator errors. The slope is justified by finite differences; it is not
silently identified with the derivative of a separate holomorphic witness. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory LocalSystem DomainFunctions
set_option autoImplicit false
variable {n m : Nat} {D : Scalar→Prop}

def uniformEntryDerivativeAt (G DG : Field (n := n) (m := m) D)
    (hD : ∀ z w, z≈w→(D z↔D w))
    (hG : ∀ z w hz hw, z≈w→(G z hz).Equiv (G w hw))
    (delta : QPos→QPos)
    (hrem : ∀ (eps H : QPos) w z hw hz, H.val≤(delta eps).val→
      Small (sub z.val w.val) H.val→∀ E, 0≤E→∀ x, CoordinateBound x E→
      CoordinateBound (operatorRemainder G DG w z hw hz x) ((eps.val*H.val)*E))
    (i : Fin n) (j : Fin m) (a : Scalar) (ha : D a) :
    HasDerivativeAt (entryMap G hD hG i j) a ha (Fiber.coordinate ((DG a ha).eval (Fiber.basis i)) j) where
  delta eps := delta (inputError (initialBound (Fiber.basis i)) (initialBound_nonneg _) eps)
  estimate eps H z hz hH hza := by
    let E := initialBound (Fiber.basis i)
    let eta := inputError E (initialBound_nonneg _) eps
    have hb := hrem eta H a z ha hz hH hza E (initialBound_nonneg _) (Fiber.basis i) (initialBound_valid _) j
    let d := Fiber.coordinate ((DG a ha).eval (Fiber.basis i)) j
    have he : ((operatorRemainder G DG a z ha hz (Fiber.basis i)).val j).Equiv
        (DomainFunctions.remainder (entryMap G hD hG i j) a ha d z hz) :=
      FunctionTheory.sub_congr
        (equiv_refl _ (sub_valid (((G z hz).eval (Fiber.basis i)).property j) (((G a ha).eval (Fiber.basis i)).property j)))
        (mul_comm_equiv _ _ (sub_valid z.property a.property) d.property)
    have hs := Small.congr ((operatorRemainder G DG a z ha hz (Fiber.basis i)).property j)
      (DomainFunctions.remainder_valid (entryMap G hD hG i j) a ha d z hz) he hb
    apply hs.mono
    have hm := Rat.mul_le_mul_of_nonneg_right (inputError_bound E (initialBound_nonneg _) eps) (Rat.le_of_lt H.property)
    change (eta.val*H.val)*E≤eps.val*H.val
    change eta.val*E*H.val≤eps.val*H.val at hm
    grind only

/-- Use the supplied, justified slope as the literal derivative evaluator.
First-order radii come directly from its uniform errors. Actual derivative
uniqueness transfers name invariance and continuity from the existing witness. -/
def MatrixHolomorphic.withUniformSlope (G DG : Field (n := n) (m := m) D)
    (O : ScalarTopology.OpenData D)
    (hG : ∀ z w hz hw, z≈w→(G z hz).Equiv (G w hw))
    (hM : MatrixHolomorphic G O.invariant hG) (delta : QPos→QPos)
    (hrem : ∀ (eps H : QPos) w z hw hz, H.val≤(delta eps).val→
      Small (sub z.val w.val) H.val→∀ E, 0≤E→∀ x, CoordinateBound x E→
      CoordinateBound (operatorRemainder G DG w z hw hz x) ((eps.val*H.val)*E)) :
    MatrixHolomorphic G O.invariant hG := by
  intro i j
  let d := fun z hz => Fiber.coordinate ((DG z hz).eval (Fiber.basis i)) j
  have he : ∀ z hz, (hM i j).derivative z hz≈d z hz := fun z hz =>
    ((hM i j).atPoint z hz).unique (uniformEntryDerivativeAt G DG O.invariant hG delta hrem i j z hz)
      (hM i j).openDomain
  exact {
    openDomain := (hM i j).openDomain
    derivative := d
    atPoint := uniformEntryDerivativeAt G DG O.invariant hG delta hrem i j
    derivative_congr z w hz hw hzw := equiv_trans (d z hz).property ((hM i j).derivative z hz).property (d w hw).property
      (equiv_symm (he z hz)) (equiv_trans ((hM i j).derivative z hz).property ((hM i j).derivative w hw).property
        (d w hw).property ((hM i j).derivative_congr z w hz hw hzw) (he w hw))
    continuousDerivative := {
      delta := (hM i j).continuousDerivative.delta
      estimate a ha eps z hz hza := Small.congr
        (sub_valid ((hM i j).derivative z hz).property ((hM i j).derivative a ha).property)
        (sub_valid (d z hz).property (d a ha).property)
        (FunctionTheory.sub_congr (he z hz) (he a ha))
        ((hM i j).continuousDerivative.estimate a ha eps z hz hza) } }

theorem derivativeField_from_uniform (G DG : Field (n := n) (m := m) D)
    (O : ScalarTopology.OpenData D)
    (hG : ∀ z w hz hw, z≈w→(G z hz).Equiv (G w hw))
    (hM : MatrixHolomorphic G O.invariant hG) (hDG : ∀ z hz, IsLinear (DG z hz))
    (delta : QPos→QPos)
    (hrem : ∀ (eps H : QPos) w z hw hz, H.val≤(delta eps).val→
      Small (sub z.val w.val) H.val→∀ E, 0≤E→∀ x, CoordinateBound x E→
      CoordinateBound (operatorRemainder G DG w z hw hz x) ((eps.val*H.val)*E))
    (a : Scalar) (ha : D a) : (derivativeField hM a ha).Equiv (DG a ha) := by
  apply (ValueMap.linear_equiv_iff_basis _ _ (derivativeField_linear hM a ha) (hDG a ha)).mpr
  intro i j
  exact equiv_trans ((matrixEntry (derivativeField hM) i j a ha).property)
    ((hM i j).derivative a ha).property (((DG a ha).eval (Fiber.basis i)).property j)
    (derivativeField_entry hM i j a ha)
    (((hM i j).atPoint a ha).unique
      (uniformEntryDerivativeAt G DG O.invariant hG delta hrem i j a ha) (hM i j).openDomain)

end ComputableAnalysis.RiemannHilbert.LinearField
