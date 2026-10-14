import ComputableAnalysis.RiemannHilbert.ContourSystemChart
import ComputableAnalysis.RiemannHilbert.SystemChartInverseHolomorphic

/-! Constructed local holomorphic solutions and invertible fundamental
frames for any supplied linear holomorphic coefficient field. Their
derivatives solve the original function equation, and the computed inverse
frame is holomorphic. No power-series presentation is required of callers. -/
namespace ComputableAnalysis.RiemannHilbert.ConstructedSystemODE
open ComplexRaw FunctionTheory LocalSystem DomainFunctions LinearField
set_option autoImplicit false
variable {n : Nat} {D : Scalar → Prop}
variable (G : Field (n := n) (m := n) D) (O : ScalarTopology.OpenData D)
    (hG : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hM : MatrixHolomorphic G O.invariant hG) (b : Scalar) (hb : D b)

def solution (initial : Fiber n) : DomainVectorFunctions.Map n where
  domain := domain G O hG hM b hb
  eval z hz := (chart G O hG hM b hb).value initial z (domain_chart G O hG hM b hb z hz)
  domain_congr := (ConstructedMatrixTaylor.openData G O hG hM b hb).invariant
  eval_congr z w hz hw he := (chart G O hG hM b hb).value_congr (chart G O hG hM b hb) initial initial
    (equiv_refl _ b.property) (fun _ => ValueMap.equiv_refl _) (Setoid.refl _) z w he
    (domain_chart G O hG hM b hb z hz) (domain_chart G O hG hM b hb w hw)

def solution_holomorphic (initial : Fiber n) : DomainVectorFunctions.Holomorphic (solution G O hG hM b hb initial) where
  openDomain := ⟨(ConstructedMatrixTaylor.openData G O hG hM b hb).radius,
    (ConstructedMatrixTaylor.openData G O hG hM b hb).inside⟩
  coordinates i := (ofCertifiedHolomorphic ((chart G O hG hM b hb).coordinate_holomorphic initial i)).transfer
    (DomainVectorFunctions.coordinate (solution G O hG hM b hb initial) i) (domain_chart G O hG hM b hb)
    ⟨(ConstructedMatrixTaylor.openData G O hG hM b hb).radius,(ConstructedMatrixTaylor.openData G O hG hM b hb).inside⟩
    (fun z hz => equiv_refl _ (((solution G O hG hM b hb initial).eval z hz).property i))

theorem solution_derivative (initial : Fiber n) (z : Scalar) (hz : domain G O hG hM b hb z) :
    DomainVectorFunctions.derivative (solution G O hG hM b hb initial) (solution_holomorphic G O hG hM b hb initial) z hz≈
      (chart G O hG hM b hb).derivative initial z (domain_chart G O hG hM b hb z hz) :=
  fun i => equiv_refl _ (((chart G O hG hM b hb).derivative initial z (domain_chart G O hG hM b hb z hz)).property i)

/-- Actual local existence for the original coefficient field, for every
valid represented initial vector and every finite rank, including zero. -/
theorem solution_ode (hlinear : ∀ z hz, IsLinear (G z hz)) (initial : Fiber n) (z : Scalar)
    (hz : domain G O hG hM b hb z) (ha : D z) :
    DomainVectorFunctions.derivative (solution G O hG hM b hb initial) (solution_holomorphic G O hG hM b hb initial) z hz≈
      (G z ha).eval ((solution G O hG hM b hb initial).eval z hz) := by
  let c := chart G O hG hM b hb
  let hc := domain_chart G O hG hM b hb z hz
  exact Setoid.trans (b := c.derivative initial z hc) (solution_derivative G O hG hM b hb initial z hz)
    (Setoid.trans (b := (c.operator z hc).eval (c.value initial z hc)) (c.value_ode initial z hc)
      (operator_agrees G O hG hM b hb hlinear z hz ha (c.value initial z hc)))

theorem solution_initial (initial : Fiber n) :
    (solution G O hG hM b hb initial).eval b (center_mem G O hG hM b hb)≈initial :=
  (chart G O hG hM b hb).value_initial initial

theorem solution_bound (initial : Fiber n) (z : Scalar) (hz : domain G O hG hM b hb z) :
    CoordinateBound ((solution G O hG hM b hb initial).eval z hz) (4*initialBound initial) :=
  (chart G O hG hM b hb).value_bound initial z (domain_chart G O hG hM b hb z hz)

theorem solution_congr (hN : MatrixHolomorphic G O.invariant hG) (c : Scalar) (hc : D c)
    (initial other : Fiber n) (hbc : b≈c) (hi : initial≈other) (z w : Scalar) (hzw : z≈w)
    (hz : domain G O hG hM b hb z) (hw : domain G O hG hN c hc w) :
    (solution G O hG hM b hb initial).eval z hz≈(solution G O hG hN c hc other).eval w hw :=
  (chart G O hG hM b hb).value_congr (chart G O hG hN c hc) initial other hbc
    (ConstructedMatrixTaylor.coefficientOperators_congr G O hG hM b hb hN c hc hbc) hi z w hzw
    (domain_chart G O hG hM b hb z hz) (domain_chart G O hG hN c hc w hw)

/-- An actual represented Neumann inverse of the constructed solution map. -/
def fundamentalFrame (z : Scalar) (hz : domain G O hG hM b hb z) : LinearIso n n :=
  (chart G O hG hM b hb).valueIso z (domain_chart G O hG hM b hb z hz)

theorem fundamentalFrame_value (initial : Fiber n) (z : Scalar) (hz : domain G O hG hM b hb z) :
    (fundamentalFrame G O hG hM b hb z hz).toValueIso.forward.eval initial≈
      (solution G O hG hM b hb initial).eval z hz := Setoid.refl _

theorem fundamentalFrame_initial :
    (fundamentalFrame G O hG hM b hb b (center_mem G O hG hM b hb)).toValueIso.forward.Equiv ValueMap.identity :=
  solution_initial G O hG hM b hb

theorem fundamentalFrame_names (z w : Scalar) (hz : domain G O hG hM b hb z) (hw : domain G O hG hM b hb w)
    (he : z≈w) :
    (fundamentalFrame G O hG hM b hb z hz).toValueIso.forward.Equiv
      (fundamentalFrame G O hG hM b hb w hw).toValueIso.forward :=
  fun x => (solution G O hG hM b hb x).eval_congr z w hz hw he

def fundamentalFrame_holomorphic : MatrixHolomorphic (forwardField (fundamentalFrame G O hG hM b hb))
    (ConstructedMatrixTaylor.openData G O hG hM b hb).invariant (fundamentalFrame_names G O hG hM b hb) :=
  fun i j => ((chart G O hG hM b hb).evaluation_holomorphic i j).transfer
    (entryMap (forwardField (fundamentalFrame G O hG hM b hb)) (ConstructedMatrixTaylor.openData G O hG hM b hb).invariant
      (fundamentalFrame_names G O hG hM b hb) i j) (domain_chart G O hG hM b hb)
    ⟨(ConstructedMatrixTaylor.openData G O hG hM b hb).radius,(ConstructedMatrixTaylor.openData G O hG hM b hb).inside⟩
    (fun z hz => equiv_refl _ (((fundamentalFrame G O hG hM b hb z hz).toValueIso.forward.eval (Fiber.basis i)).property j))

def inverseFrame_holomorphic : MatrixHolomorphic (inverseField (fundamentalFrame G O hG hM b hb))
    (ConstructedMatrixTaylor.openData G O hG hM b hb).invariant
    (inverseField_congr (fundamentalFrame G O hG hM b hb) (fundamentalFrame_names G O hG hM b hb)) :=
  fun i j => ((chart G O hG hM b hb).inverseEvaluation_holomorphic i j).transfer
    (entryMap (inverseField (fundamentalFrame G O hG hM b hb)) (ConstructedMatrixTaylor.openData G O hG hM b hb).invariant
      (inverseField_congr (fundamentalFrame G O hG hM b hb) (fundamentalFrame_names G O hG hM b hb)) i j)
    (domain_chart G O hG hM b hb)
    ⟨(ConstructedMatrixTaylor.openData G O hG hM b hb).radius,(ConstructedMatrixTaylor.openData G O hG hM b hb).inside⟩
    (fun z hz => equiv_refl _ (((fundamentalFrame G O hG hM b hb z hz).toValueIso.backward.eval (Fiber.basis i)).property j))

/-- The actual matrix derivative of the fundamental frame is the supplied
coefficient operator composed with the frame evaluator. -/
theorem fundamentalFrame_ode (hlinear : ∀ z hz, IsLinear (G z hz)) (z : Scalar)
    (hz : domain G O hG hM b hb z) (ha : D z) :
    (derivativeField (fundamentalFrame_holomorphic G O hG hM b hb) z hz).Equiv
      ((fundamentalFrame G O hG hM b hb z hz).toValueIso.forward.followedBy (G z ha)) := by
  let F := fundamentalFrame G O hG hM b hb z hz
  let hF := fundamentalFrame_holomorphic G O hG hM b hb
  apply (ValueMap.linear_equiv_iff_basis _ _ (derivativeField_linear hF z hz) (IsLinear.followedBy F.linear (hlinear z ha))).2
  intro i j
  exact equiv_trans (matrixEntry (derivativeField hF) i j z hz).property ((hF i j).derivative z hz).property
    (((F.toValueIso.forward.followedBy (G z ha)).eval (Fiber.basis i)).property j)
    (derivativeField_entry hF i j z hz) (solution_ode G O hG hM b hb hlinear (Fiber.basis i) z hz ha j)

theorem inverseFrame_ode (hlinear : ∀ z hz, IsLinear (G z hz)) (z : Scalar)
    (hz : domain G O hG hM b hb z) (ha : D z) :
    (derivativeField (inverseFrame_holomorphic G O hG hM b hb) z hz).Equiv
      (ValueMap.difference (ValueMap.zeroBetween n n)
        ((G z ha).followedBy (fundamentalFrame G O hG hM b hb z hz).toValueIso.backward)) := by
  let c := chart G O hG hM b hb
  let hc := domain_chart G O hG hM b hb z hz
  let F := fundamentalFrame G O hG hM b hb z hz
  let hI := inverseFrame_holomorphic G O hG hM b hb
  apply (ValueMap.linear_equiv_iff_basis _ _ (derivativeField_linear hI z hz)
    (ValueMap.difference_linear _ _ (ValueMap.zeroBetween_linear n n) (IsLinear.followedBy (hlinear z ha) F.inverse.linear))).2
  intro i j
  have hs := c.inverseSolution_derivative (Fiber.basis i) z hc
  have he := Fiber.sub_congr (Setoid.refl (Fiber.zero n))
    (F.toValueIso.backward.congr (operator_agrees G O hG hM b hb hlinear z hz ha (Fiber.basis i)))
  exact equiv_trans (matrixEntry (derivativeField hI) i j z hz).property ((hI i j).derivative z hz).property
    ((Fiber.sub (Fiber.zero n) (F.toValueIso.backward.eval ((G z ha).eval (Fiber.basis i)))).property j)
    (derivativeField_entry hI i j z hz) (Setoid.trans hs he j)

theorem fundamentalFrame_congr (hN : MatrixHolomorphic G O.invariant hG) (c : Scalar) (hc : D c) (hbc : b≈c)
    (z w : Scalar) (hzw : z≈w) (hz : domain G O hG hM b hb z) (hw : domain G O hG hN c hc w) :
    (fundamentalFrame G O hG hM b hb z hz).toValueIso.forward.Equiv
      (fundamentalFrame G O hG hN c hc w hw).toValueIso.forward :=
  fun x => solution_congr G O hG hM b hb hN c hc x x hbc (Setoid.refl _) z w hzw hz hw

theorem inverseFrame_congr (hN : MatrixHolomorphic G O.invariant hG) (c : Scalar) (hc : D c) (hbc : b≈c)
    (z w : Scalar) (hzw : z≈w) (hz : domain G O hG hM b hb z) (hw : domain G O hG hN c hc w) :
    (fundamentalFrame G O hG hM b hb z hz).toValueIso.backward.Equiv
      (fundamentalFrame G O hG hN c hc w hw).toValueIso.backward :=
  ValueIso.inverse_congr _ _ (fundamentalFrame_congr G O hG hM b hb hN c hc hbc z w hzw hz hw)

/-- Effective open-domain data, holomorphy witnesses and represented names
may all change; the exact local solution is unchanged on the common domain. -/
theorem solution_data_congr (P : ScalarTopology.OpenData D)
    (hNnames : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hN : MatrixHolomorphic G P.invariant hNnames) (c : Scalar) (hc : D c)
    (initial other : Fiber n) (hbc : b≈c) (hi : initial≈other) (z w : Scalar) (hzw : z≈w)
    (hz : domain G O hG hM b hb z) (hw : domain G P hNnames hN c hc w) :
    (solution G O hG hM b hb initial).eval z hz≈(solution G P hNnames hN c hc other).eval w hw :=
  (chart G O hG hM b hb).value_congr (chart G P hNnames hN c hc) initial other hbc
    (ConstructedMatrixTaylor.coefficientOperators_data_congr G O hG hM b hb P hNnames hN c hc hbc) hi z w hzw
    (domain_chart G O hG hM b hb z hz) (domain_chart G P hNnames hN c hc w hw)

theorem fundamentalFrame_data_congr (P : ScalarTopology.OpenData D)
    (hNnames : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hN : MatrixHolomorphic G P.invariant hNnames) (c : Scalar) (hc : D c) (hbc : b≈c)
    (z w : Scalar) (hzw : z≈w) (hz : domain G O hG hM b hb z) (hw : domain G P hNnames hN c hc w) :
    (fundamentalFrame G O hG hM b hb z hz).toValueIso.forward.Equiv
      (fundamentalFrame G P hNnames hN c hc w hw).toValueIso.forward :=
  fun x => solution_data_congr G O hG hM b hb P hNnames hN c hc x x hbc (Setoid.refl _) z w hzw hz hw

theorem inverseFrame_data_congr (P : ScalarTopology.OpenData D)
    (hNnames : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hN : MatrixHolomorphic G P.invariant hNnames) (c : Scalar) (hc : D c) (hbc : b≈c)
    (z w : Scalar) (hzw : z≈w) (hz : domain G O hG hM b hb z) (hw : domain G P hNnames hN c hc w) :
    (fundamentalFrame G O hG hM b hb z hz).toValueIso.backward.Equiv
      (fundamentalFrame G P hNnames hN c hc w hw).toValueIso.backward :=
  ValueIso.inverse_congr _ _ (fundamentalFrame_data_congr G O hG hM b hb P hNnames hN c hc hbc z w hzw hz hw)

end ComputableAnalysis.RiemannHilbert.ConstructedSystemODE
