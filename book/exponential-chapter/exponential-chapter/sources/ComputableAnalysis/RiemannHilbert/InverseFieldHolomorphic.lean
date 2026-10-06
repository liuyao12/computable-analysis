import ComputableAnalysis.RiemannHilbert.InverseFieldBounds
import ComputableAnalysis.RiemannHilbert.MatrixFieldContinuityLaws

/-! Holomorphicity of the actual inverse evaluator is derived from forward
derivative remainders, derivative continuity, and a justified inverse bound.
The derivative is constructed, with rational radii in every complex direction. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory LocalSystem DomainFunctions
variable {n : Nat} {D : Scalar → Prop}

def inputError (E : Rat) (hE : 0 ≤ E) (eps : QPos) : QPos :=
  divideRadius eps ⟨E+1,by grind only⟩

theorem inputError_bound (E : Rat) (hE : 0 ≤ E) (eps : QPos) :
    (inputError E hE eps).val*E ≤ eps.val := by
  have he := divideRadius_identity eps (⟨E+1,by grind only⟩ : QPos)
  have hm := Rat.mul_le_mul_of_nonneg_left (show E ≤ E+1 by grind only)
    (Rat.le_of_lt (inputError E hE eps).property)
  change (E+1)*(inputError E hE eps).val=eps.val at he
  grind only

private theorem input_remainder_budget (E eps eta H : Rat) (h : eta*E ≤ eps) (hH : 0 ≤ H) :
    (eta*H)*E ≤ eps*H := by
  have hm := Rat.mul_le_mul_of_nonneg_right h hH
  grind only

theorem inverseField_congr (F : (z : Scalar) → D z → LinearIso n n)
    (hF : ∀ z w hz hw, z.val.Equiv w.val → (forwardField F z hz).Equiv (forwardField F w hw))
    (z w : Scalar) (hz : D z) (hw : D w) (hzw : z.val.Equiv w.val) :
    (inverseField F z hz).Equiv (inverseField F w hw) :=
  ValueIso.inverse_congr (F z hz).toValueIso (F w hw).toValueIso (hF z w hz hw hzw)

theorem inverseSlope_congr (F : (z : Scalar) → D z → LinearIso n n)
    (DF : Field (n := n) (m := n) D)
    (hF : ∀ z w hz hw, z.val.Equiv w.val → (forwardField F z hz).Equiv (forwardField F w hw))
    (hDF : ∀ z w hz hw, z.val.Equiv w.val → (DF z hz).Equiv (DF w hw))
    (z w : Scalar) (hz : D z) (hw : D w) (hzw : z.val.Equiv w.val) :
    (inverseSlope F DF z hz).Equiv (inverseSlope F DF w hw) := fun x =>
  Fiber.sub_congr (Setoid.refl _)
    (ValueMap.followedBy_congr
      (ValueMap.followedBy_congr (inverseField_congr F hF z w hz hw hzw) (hDF z w hz hw hzw))
      (inverseField_congr F hF z w hz hw hzw) x)

theorem inverseSlope_linear (F : (z : Scalar) → D z → LinearIso n n)
    (DF : Field (n := n) (m := n) D) (hDF : ∀ z hz, IsLinear (DF z hz))
    (z : Scalar) (hz : D z) : IsLinear (inverseSlope F DF z hz) :=
  ValueMap.difference_linear _ _ (ValueMap.zeroBetween_linear n n)
    (IsLinear.followedBy (IsLinear.followedBy (F z hz).inverse.linear (hDF z hz)) (F z hz).inverse.linear)

def inverseVectorMap (F : (z : Scalar) → D z → LinearIso n n) (hD : ScalarTopology.OpenData D)
    (hF : ∀ z w hz hw, z.val.Equiv w.val → (forwardField F z hz).Equiv (forwardField F w hw))
    (x : Fiber n) : DomainVectorFunctions.Map n where
  domain := D
  eval z hz := (inverseField F z hz).eval x
  domain_congr := hD.invariant
  eval_congr z w hz hw hzw := inverseField_congr F hF z w hz hw hzw x

section Construction
variable (F : (z : Scalar) → D z → LinearIso n n) (DF : Field (n := n) (m := n) D)
variable (hD : ScalarTopology.OpenData D)
variable (hF : ∀ z w hz hw, z.val.Equiv w.val → (forwardField F z hz).Equiv (forwardField F w hw))
variable (hDFcongr : ∀ z w hz hw, z.val.Equiv w.val → (DF z hz).Equiv (DF w hw))
variable (V Q : Rat) (hV : 0 ≤ V) (hQ : 0 ≤ Q)
variable (hInv : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E →
  CoordinateBound ((inverseField F z hz).eval x) (V*E))
variable (hDFbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E →
  CoordinateBound ((DF z hz).eval x) (Q*E))
variable (deltaF : QPos → QPos)
variable (hrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaF eps).val →
  Small (sub z.val w.val) H.val → ∀ E, 0 ≤ E → ∀ x, CoordinateBound x E →
  CoordinateBound (operatorRemainder (forwardField F) DF w z hw hz x) ((eps.val*H.val)*E))

def inverseCoordinateDerivative (x : Fiber n) (j : Fin n) (w : Scalar) (hw : D w) :
    DomainFunctions.HasDerivativeAt (DomainVectorFunctions.coordinate (inverseVectorMap F hD hF x) j)
      w hw (Fiber.coordinate ((inverseSlope F DF w hw).eval x) j) where
  delta eps := inverseDelta V Q hV hQ deltaF (inputError (initialBound x) (initialBound_nonneg _) eps)
  estimate eps H z hz hH hzw := by
    let E := initialBound x
    let eta := inputError E (initialBound_nonneg _) eps
    have hr := inverse_uniform_remainder F DF V Q hV hQ hInv hDFbound deltaF hrem
      eta H w z hw hz hH hzw E (initialBound_nonneg _) x (initialBound_valid _)
    have hb := (hr j).mono (input_remainder_budget E eps.val eta.val H.val
      (inputError_bound E (initialBound_nonneg _) eps) (Rat.le_of_lt H.property))
    let d : Scalar := ⟨sub z.val w.val,sub_valid z.property w.property⟩
    exact Small.congr
      ((operatorRemainder (inverseField F) (inverseSlope F DF) w z hw hz x).property j)
      (DomainFunctions.remainder_valid _ _ _ _ _ _)
      (FunctionTheory.sub_congr
        (equiv_refl _ (sub_valid (((inverseField F z hz).eval x).property j)
          (((inverseField F w hw).eval x).property j)))
        (mul_comm_equiv d.val ((Fiber.coordinate ((inverseSlope F DF w hw).eval x) j).val)
          d.property (Fiber.coordinate ((inverseSlope F DF w hw).eval x) j).property)) hb

def inverseEntryDerivative (i j : Fin n) (w : Scalar) (hw : D w) :
    DomainFunctions.HasDerivativeAt (entryMap (inverseField F) hD.invariant (inverseField_congr F hF) i j)
      w hw (matrixEntry (inverseSlope F DF) i j w hw) :=
  inverseCoordinateDerivative F DF hD hF V Q hV hQ hInv hDFbound deltaF hrem (Fiber.basis i) j w hw

def inverseMatrixContinuous : MatrixContinuous (inverseField F) := fun i j =>
  continuousOn_of_derivative (entryMap (inverseField F) hD.invariant (inverseField_congr F hF) i j)
    (matrixEntry (inverseSlope F DF) i j)
    (inverseEntryDerivative F DF hD hF V Q hV hQ hInv hDFbound deltaF hrem i j)

def inverseSlopeContinuous (hDFlinear : ∀ z hz, IsLinear (DF z hz))
    (hDFcontinuous : MatrixContinuous DF) : MatrixContinuous (inverseSlope F DF) := by
  let hG := inverseMatrixContinuous F DF hD hF V Q hV hQ hInv hDFbound deltaF hrem
  let hP := matrixCompositionContinuous (inverseField F) DF hDFlinear hG hDFcontinuous
  let hT := matrixCompositionContinuous (fun z hz => (inverseField F z hz).followedBy (DF z hz))
    (inverseField F) (fun z hz => (F z hz).inverse.linear) hP hG
  intro i j
  apply baseContinuous_congr (DomainFunctions.negateContinuous _ (hT i j))
  intro z hz
  exact equiv_symm (zero_add_equiv _ (neg_valid
    (((inverseField F z hz).eval ((DF z hz).eval ((inverseField F z hz).eval (Fiber.basis i)))).property j)))

def inverseMatrixHolomorphic (hDFlinear : ∀ z hz, IsLinear (DF z hz))
    (hDFcontinuous : MatrixContinuous DF) :
    MatrixHolomorphic (inverseField F) hD.invariant (inverseField_congr F hF) := fun i j => {
  openDomain := ⟨hD.radius,hD.inside⟩
  derivative := matrixEntry (inverseSlope F DF) i j
  atPoint := inverseEntryDerivative F DF hD hF V Q hV hQ hInv hDFbound deltaF hrem i j
  derivative_congr := fun z w hz hw hzw => inverseSlope_congr F DF hF hDFcongr z w hz hw hzw (Fiber.basis i) j
  continuousDerivative := inverseSlopeContinuous F DF hD hF V Q hV hQ hInv hDFbound deltaF hrem hDFlinear hDFcontinuous i j }

def inverseVectorHolomorphic (hDFlinear : ∀ z hz, IsLinear (DF z hz))
    (hDFcontinuous : MatrixContinuous DF) (x : Fiber n) :
    DomainVectorFunctions.Holomorphic (inverseVectorMap F hD hF x) where
  openDomain := ⟨hD.radius,hD.inside⟩
  coordinates j := {
    openDomain := ⟨hD.radius,hD.inside⟩
    derivative := fun z hz => Fiber.coordinate ((inverseSlope F DF z hz).eval x) j
    atPoint := inverseCoordinateDerivative F DF hD hF V Q hV hQ hInv hDFbound deltaF hrem x j
    derivative_congr := fun z w hz hw hzw => inverseSlope_congr F DF hF hDFcongr z w hz hw hzw x j
    continuousDerivative := baseActionContinuous (inverseSlope F DF) (inverseSlope_linear F DF hDFlinear)
      (inverseSlopeContinuous F DF hD hF V Q hV hQ hInv hDFbound deltaF hrem hDFlinear hDFcontinuous)
      (fun _ _ => x) (fun i => baseConstantContinuous D (Fiber.coordinate x i)) j }

end Construction
end ComputableAnalysis.RiemannHilbert.LinearField
