import ComputableAnalysis.RiemannHilbert.ScalarFiberContinuity
import ComputableAnalysis.RiemannHilbert.LinearFieldProduct

/-! A varying finite-rank linear map acts jointly continuously when its
finitely many matrix entries have supplied effective scalar continuity.
Finite matrix expansion constructs the joint modulus without a uniform
operator bound over the whole base domain. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory DomainFunctions ScalarFiberTopology
variable {n m : Nat} {D : Scalar → Prop}

def matrixEntry (G : Field (n := n) (m := m) D) (i : Fin n) (j : Fin m) (z : Scalar) (hz : D z) : Scalar :=
  Fiber.coordinate ((G z hz).eval (Fiber.basis i)) j

abbrev MatrixContinuous (G : Field (n := n) (m := m) D) :=
  ∀ i : Fin n, ∀ j : Fin m, DomainFunctions.ContinuousOn D (matrixEntry G i j)

def prefixCoordinate (G : Field (n := n) (m := m) D) (k : Nat) (j : Fin m)
    (p : Point n) (hp : D p.1) : Scalar :=
  Fiber.coordinate (ValueMap.imageBasisPrefix (G p.1 hp) p.2 k) j

def prefixCoordinateContinuous (G : Field (n := n) (m := m) D) (hG : MatrixContinuous G) :
    (k : Nat) → (j : Fin m) → ScalarContinuousOn (fun p : Point n => D p.1) (prefixCoordinate G k j)
  | 0, _ => scalarConstant ⟨ComplexRaw.zero,ofQComplex_valid _⟩
  | k+1, j => by
    by_cases hk : k < n
    · let i : Fin n := ⟨k,hk⟩
      have hterm : ScalarContinuousOn (fun p : Point n => D p.1)
          (fun p hp => scalarProduct (Fiber.coordinate p.2 i) (matrixEntry G i j p.1 hp)) :=
        scalarProductContinuous _ _ (fiberCoordinateContinuous i) (scalarLift (matrixEntry G i j) (hG i j))
      have hsum := scalarSumContinuous (prefixCoordinate G k j)
        (fun p hp => scalarProduct (Fiber.coordinate p.2 i) (matrixEntry G i j p.1 hp))
        (prefixCoordinateContinuous G hG k j) hterm
      apply hsum.congr
      intro p hp
      change (add ((ValueMap.imageBasisPrefix (G p.1 hp) p.2 k).val j)
        (mul (p.2.val i) (((G p.1 hp).eval (Fiber.basis i)).val j))).Equiv
        ((ValueMap.imageBasisPrefix (G p.1 hp) p.2 (k+1)).val j)
      rw [ValueMap.imageBasisPrefix,dif_pos hk]
      exact equiv_refl _ (add_valid
        ((ValueMap.imageBasisPrefix (G p.1 hp) p.2 k).property j)
        (mul_valid (p.2.property i) (((G p.1 hp).eval (Fiber.basis i)).property j)))
    · apply (prefixCoordinateContinuous G hG k j).congr
      intro p hp
      change ((ValueMap.imageBasisPrefix (G p.1 hp) p.2 k).val j).Equiv
        ((ValueMap.imageBasisPrefix (G p.1 hp) p.2 (k+1)).val j)
      rw [ValueMap.imageBasisPrefix,dif_neg hk]
      exact equiv_refl _ ((ValueMap.imageBasisPrefix (G p.1 hp) p.2 k).property j)

def matrixActionContinuous (G : Field (n := n) (m := m) D) (hG : MatrixContinuous G) :
    VectorContinuousOn (fun p : Point n => D p.1)
      (fun p hp => ValueMap.imageBasisPrefix (G p.1 hp) p.2 n) :=
  vectorOfCoordinates _ (fun j => prefixCoordinateContinuous G hG n j)

/-- Joint continuity of the actual operator evaluator, derived through its
exact finite matrix action at arbitrary represented base and fiber inputs. -/
def evaluationContinuous (G : Field (n := n) (m := m) D)
    (hlinear : ∀ z hz, IsLinear (G z hz)) (hG : MatrixContinuous G) :
    VectorContinuousOn (fun p : Point n => D p.1) (fun p hp => (G p.1 hp).eval p.2) :=
  (matrixActionContinuous G hG).congr
    (fun p hp => Setoid.symm (ValueMap.matrix_action (G p.1 hp) (hlinear p.1 hp) p.2))

def productEvaluationContinuous (G : Field (n := n) (m := m) D)
    (hlinear : ∀ z hz, IsLinear (G z hz)) (hG : MatrixContinuous G) :
    ScalarFiberTopology.ContinuousOn (fun p : Point n => D p.1)
      (fun p hp => (p.1,(G p.1 hp).eval p.2)) :=
  productContinuous _ _ baseContinuous (evaluationContinuous G hlinear hG)

theorem productEvaluation_congr (G : Field (n := n) (m := m) D)
    (hG : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw))
    (z w : Point n) (hz : D z.1) (hw : D w.1) (hzw : z ≈ w) :
    (z.1,(G z.1 hz).eval z.2) ≈ (w.1,(G w.1 hw).eval w.2) :=
  ⟨hzw.1,Setoid.trans ((G z.1 hz).congr hzw.2) (hG z.1 w.1 hz hw hzw.1 w.2)⟩

theorem productEvaluation_preimage_isOpen (G : Field (n := n) (m := m) D)
    (hD : ScalarTopology.IsOpen D) (hlinear : ∀ z hz, IsLinear (G z hz))
    (hG : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw))
    (hc : MatrixContinuous G) (U : Point m → Prop) (hU : ScalarFiberTopology.IsOpen U) :
    ScalarFiberTopology.IsOpen
      (preimage (fun p : Point n => D p.1) (fun p hp => (p.1,(G p.1 hp).eval p.2)) U) :=
  preimage_isOpen _ (isOpen_base D hD) _ (productEvaluation_congr G hG)
    (productEvaluationContinuous G hlinear hc) U hU

end ComputableAnalysis.RiemannHilbert.LinearField
