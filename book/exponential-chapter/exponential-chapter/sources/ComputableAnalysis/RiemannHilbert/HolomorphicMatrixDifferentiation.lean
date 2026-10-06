import ComputableAnalysis.RiemannHilbert.FiniteColumnMaps
import ComputableAnalysis.RiemannHilbert.HolomorphicMatrixComposition
import ComputableAnalysis.RiemannHilbert.DomainVectorLocality
import ComputableAnalysis.RiemannHilbert.ConnectionFrameChange
import ComputableAnalysis.RiemannHilbert.CoordinateConnectionPullback

/-! Differentiation of actual finite matrix actions. Entry derivatives construct
a linear derivative evaluator; finite scalar sum/product rules prove the
operator product rule on arbitrary represented vector fields. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory DomainFunctions
variable {n m : Nat} {D : Scalar → Prop}
variable {G : Field (n := n) (m := m) D}
variable {hD : ∀ z w, z ≈ w → (D z ↔ D w)}
variable {hG : ∀ z w hz hw, z ≈ w → (G z hz).Equiv (G w hw)}

def derivativeColumn (hM : MatrixHolomorphic G hD hG) (z : Scalar) (hz : D z) (i : Fin n) : Fiber m :=
  ⟨fun j => ((hM i j).derivative z hz).val,fun j => ((hM i j).derivative z hz).property⟩

def derivativeField (hM : MatrixHolomorphic G hD hG) : Field (n := n) (m := m) D :=
  fun z hz => ValueMap.ofColumns (derivativeColumn hM z hz)

theorem derivativeField_linear (hM : MatrixHolomorphic G hD hG) (z : Scalar) (hz : D z) :
    IsLinear (derivativeField hM z hz) := ValueMap.ofColumns_linear _

theorem derivativeField_entry (hM : MatrixHolomorphic G hD hG) (i : Fin n) (j : Fin m)
    (z : Scalar) (hz : D z) :
    (matrixEntry (derivativeField hM) i j z hz).val.Equiv ((hM i j).derivative z hz).val :=
  ValueMap.ofColumns_basis (derivativeColumn hM z hz) i j

theorem derivativeField_congr (hM : MatrixHolomorphic G hD hG) (z w : Scalar)
    (hz : D z) (hw : D w) (hzw : z ≈ w) :
    (derivativeField hM z hz).Equiv (derivativeField hM w hw) :=
  ValueMap.ofColumns_congr _ _ (fun i j => (hM i j).derivative_congr z w hz hw hzw)

theorem derivativeField_unique (hM hN : MatrixHolomorphic G hD hG) (z : Scalar) (hz : D z) :
    (derivativeField hM z hz).Equiv (derivativeField hN z hz) :=
  ValueMap.ofColumns_congr _ _ (fun i j => (hM i j).derivative_unique (hN i j) z hz)

theorem prefixMap_derivative (hM : MatrixHolomorphic G hD hG)
    (f : DomainVectorFunctions.Map n) (hf : DomainVectorFunctions.Holomorphic f)
    (hFD : ∀ z, f.domain z → D z) (k : Nat) (j : Fin m) (z : Scalar) (hz : f.domain z) :
    ((prefixMap_holomorphic G hD hG hM f hf hFD k j).derivative z hz).val.Equiv
      ((Fiber.add (ValueMap.columnPrefix (derivativeColumn hM z (hFD z hz)) (f.eval z hz) k)
        (ValueMap.imageBasisPrefix (G z (hFD z hz)) (DomainVectorFunctions.derivative f hf z hz) k)).val j) := by
  induction k with
  | zero =>
    change zero.Equiv (add zero zero)
    exact equiv_symm (zero_add_equiv _ (ofQComplex_valid _))
  | succ k ih =>
    by_cases hk : k < n
    · let i : Fin n := ⟨k,hk⟩
      simp only [prefixMap_holomorphic,dif_pos hk]
      change (add ((prefixMap_holomorphic G hD hG hM f hf hFD k j).derivative z hz).val
        (add (mul ((DomainVectorFunctions.derivative f hf z hz).val i) (((G z (hFD z hz)).eval (Fiber.basis i)).val j))
          (mul ((f.eval z hz).val i) (((hM i j).derivative z (hFD z hz)).val)))).Equiv _
      rw [ValueMap.columnPrefix,ValueMap.imageBasisPrefix,dif_pos hk,dif_pos hk]
      let A := ValueMap.columnPrefix (derivativeColumn hM z (hFD z hz)) (f.eval z hz) k
      let B := ValueMap.imageBasisPrefix (G z (hFD z hz)) (DomainVectorFunctions.derivative f hf z hz) k
      let C := Fiber.scale (Fiber.coordinate (DomainVectorFunctions.derivative f hf z hz) i)
        ((G z (hFD z hz)).eval (Fiber.basis i))
      let E := Fiber.scale (Fiber.coordinate (f.eval z hz) i) (derivativeColumn hM z (hFD z hz) i)
      exact equiv_trans
        (add_valid ((prefixMap_holomorphic G hD hG hM f hf hFD k j).derivative z hz).property
          (add_valid (C.property j) (E.property j)))
        ((Fiber.add (Fiber.add A B) (Fiber.add E C)).property j)
        ((Fiber.add (Fiber.add A E) (Fiber.add B C)).property j)
        (add_equiv ih (add_comm_equiv _ _ (C.property j) (E.property j)))
        (Fiber.add_four A B E C j)
    · simp only [prefixMap_holomorphic,dif_neg hk]
      change ((prefixMap_holomorphic G hD hG hM f hf hFD k j).derivative z hz).val.Equiv _
      rw [ValueMap.columnPrefix,ValueMap.imageBasisPrefix,dif_neg hk,dif_neg hk]
      exact ih

theorem action_derivative (hlinear : ∀ z hz, IsLinear (G z hz))
    (hM : MatrixHolomorphic G hD hG) (f : DomainVectorFunctions.Map n)
    (hf : DomainVectorFunctions.Holomorphic f) (hFD : ∀ z, f.domain z → D z)
    (z : Scalar) (hz : f.domain z) :
    DomainVectorFunctions.derivative (action G hG f hFD)
      (action_holomorphic G hD hG hlinear hM f hf hFD) z hz ≈
      Fiber.add ((derivativeField hM z (hFD z hz)).eval (f.eval z hz))
        ((G z (hFD z hz)).eval (DomainVectorFunctions.derivative f hf z hz)) := by
  intro j
  exact equiv_trans
    ((DomainVectorFunctions.derivative (action G hG f hFD)
      (action_holomorphic G hD hG hlinear hM f hf hFD) z hz).property j)
    ((Fiber.add ((derivativeField hM z (hFD z hz)).eval (f.eval z hz))
      (ValueMap.imageBasisPrefix (G z (hFD z hz)) (DomainVectorFunctions.derivative f hf z hz) n)).property j)
    ((Fiber.add ((derivativeField hM z (hFD z hz)).eval (f.eval z hz))
      ((G z (hFD z hz)).eval (DomainVectorFunctions.derivative f hf z hz))).property j)
    (prefixMap_derivative hM f hf hFD n j z hz)
    (Fiber.add_congr (Setoid.refl _) (Setoid.symm (ValueMap.matrix_action
      (G z (hFD z hz)) (hlinear z (hFD z hz)) (DomainVectorFunctions.derivative f hf z hz))) j)

theorem appliedToConstant_derivative (hOpen : ScalarTopology.OpenData D)
    (hlinear : ∀ z hz, IsLinear (G z hz)) (hM : MatrixHolomorphic G hOpen.invariant hG)
    (x : Fiber n) (z : Scalar) (hz : D z) :
    DomainVectorFunctions.derivative (appliedToConstant G hOpen.invariant hG x)
      (appliedToConstant_holomorphic G hOpen hG hlinear hM x) z hz ≈
      (derivativeField hM z hz).eval x :=
  Setoid.trans (action_derivative hlinear hM _ (DomainVectorFunctions.constantOn_holomorphic hOpen x)
    (fun _ hz => hz) z hz)
    (Setoid.trans (Fiber.add_congr (Setoid.refl _) ((hlinear z hz).zero)) (Fiber.add_zero _))

theorem horizontal_action (hlinear : ∀ z hz, IsLinear (G z hz))
    (hM : MatrixHolomorphic G hD hG)
    (A : UniformSegment.OperatorField (n := n) D) (B : UniformSegment.OperatorField (n := m) D)
    (hcompat : Compatible G (derivativeField hM) A B)
    (f : DomainVectorFunctions.Map n) (hf : DomainVectorFunctions.Holomorphic f)
    (hFD : ∀ z, f.domain z → D z)
    (hsource : CoordinateConnection.Horizontal f hf (fun z hz => A z (hFD z hz))) :
    CoordinateConnection.Horizontal (action G hG f hFD)
      (action_holomorphic G hD hG hlinear hM f hf hFD) (fun z hz => B z (hFD z hz)) := by
  intro z hz
  exact Setoid.trans (action_derivative hlinear hM f hf hFD z hz)
    (Setoid.trans (Fiber.add_congr (Setoid.refl _) ((G z (hFD z hz)).congr (hsource z hz)))
      (hcompat z (hFD z hz) (f.eval z hz)))

theorem Compatible.derivative_difference (DG : Field (n := n) (m := m) D)
    (A : UniformSegment.OperatorField (n := n) D) (B : UniformSegment.OperatorField (n := m) D)
    (hcompat : Compatible G DG A B) (z : Scalar) (hz : D z) (x : Fiber n) :
    (DG z hz).eval x ≈ Fiber.sub ((B z hz).eval ((G z hz).eval x))
      ((G z hz).eval ((A z hz).eval x)) := by
  intro j
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((DG z hz).eval x).property j)
    (hright := (Fiber.sub ((B z hz).eval ((G z hz).eval x)) ((G z hz).eval ((A z hz).eval x))).property j)
  let X := ComplexRawQuotient.ofRaw (((DG z hz).eval x).val j) (((DG z hz).eval x).property j)
  let Y := ComplexRawQuotient.ofRaw (((G z hz).eval ((A z hz).eval x)).val j)
    (((G z hz).eval ((A z hz).eval x)).property j)
  let Z := ComplexRawQuotient.ofRaw (((B z hz).eval ((G z hz).eval x)).val j)
    (((B z hz).eval ((G z hz).eval x)).property j)
  have hc : X+Y=Z := ComplexRawQuotient.ofRaw_eq_ofRaw (hcompat z hz x j)
  change X=Z-Y
  rw [←hc]
  grind only

end ComputableAnalysis.RiemannHilbert.LinearField
