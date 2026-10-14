import ComputableAnalysis.RiemannHilbert.AnalyticSolutionGerms

/-! Evaluation of actual horizontal solution germs is invertible. The inverse
is an executable contour/Taylor ODE construction, and the inverse laws are
proved using local uniqueness against arbitrary holomorphic solutions. -/
namespace ComputableAnalysis.RiemannHilbert.AnalyticSolutionGerm
open ComplexRaw FunctionTheory LocalSystem DomainFunctions LinearField
set_option autoImplicit false
variable {n : Nat} {D : Scalar → Prop}
variable (G : Field (n := n) (m := n) D) (O : ScalarTopology.OpenData D)
    (hG : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hM : MatrixHolomorphic G O.invariant hG) (hlinear : ∀ z hz, IsLinear (G z hz))
    (b : Scalar) (hb : D b)

def ofInitial (initial : Fiber n) : Name G b where
  function := ConstructedSystemODE.solution G O hG hM b hb initial
  holomorphic := ConstructedSystemODE.solution_holomorphic G O hG hM b hb initial
  base_mem := ConstructedSystemODE.center_mem G O hG hM b hb
  contained := ConstructedSystemODE.domain_original G O hG hM b hb
  horizontal z hz := ConstructedSystemODE.solution_ode G O hG hM b hb hlinear initial z hz _

theorem ofInitial_evaluation (initial : Fiber n) :
    evaluation.eval (ofInitial G O hG hM hlinear b hb initial)≈initial :=
  ConstructedSystemODE.solution_initial G O hG hM b hb initial

/-- A supplied actual holomorphic horizontal function represents exactly
the germ constructed from its initial value. The radius and error data are
computed beneath this statement, rather than supplied by its caller. -/
theorem ofInitial_agreement (x : Name G b) (initial : Fiber n)
    (hi : evaluation.eval x≈initial) : ofInitial G O hG hM hlinear b hb initial≈x := by
  let R := ConstructedSystemODE.comparisonRadius G O hG hM b hb x.function x.holomorphic x.base_mem
  let hs := ConstructedSystemODE.comparison_system G O hG hM b hb x.function x.holomorphic x.base_mem
  let hx := ConstructedSystemODE.comparison_original G O hG hM b hb x.function x.holomorphic x.base_mem
  refine ⟨R,hs,hx,?_⟩
  intro z hz ha hc
  exact ConstructedSystemODE.solution_unique_local G O hG hM b hb x.function x.holomorphic x.base_mem
    hlinear initial hi (fun w hw _ => x.horizontal w hw) z hz

include O hG hM hlinear hb in
/-- For this ODE, neighborhood agreement is equivalent to equality of
initial values. Neighborhood agreement was defined independently above. -/
theorem agreement_iff_evaluation (x y : Name G b) : x≈y ↔ evaluation.eval x≈evaluation.eval y := by
  constructor
  · exact evaluation_congr
  · intro he
    exact Setoid.trans (Setoid.symm (ofInitial_agreement G O hG hM hlinear b hb x _ he))
      (ofInitial_agreement G O hG hM hlinear b hb y _ (Setoid.refl _))

def initialMap : ValueMap (Fiber n) (Name G b) where
  eval := ofInitial G O hG hM hlinear b hb
  congr {x y} he := (agreement_iff_evaluation G O hG hM hlinear b hb _ _).2
    (Setoid.trans (ofInitial_evaluation G O hG hM hlinear b hb x)
      (Setoid.trans he (Setoid.symm (ofInitial_evaluation G O hG hM hlinear b hb y))))

/-- An isomorphism from genuine horizontal germs to represented vectors,
valid for arbitrary supplied holomorphic coefficients and all finite ranks. -/
def evaluationIso : ValueIso (Name G b) (Fiber n) where
  forward := evaluation
  backward := initialMap G O hG hM hlinear b hb
  backward_forward x := ofInitial_agreement G O hG hM hlinear b hb x _ (Setoid.refl _)
  forward_backward := ofInitial_evaluation G O hG hM hlinear b hb

theorem initialMap_data_congr (P : ScalarTopology.OpenData D)
    (hH : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hN : MatrixHolomorphic G P.invariant hH) (initial other : Fiber n) (hi : initial≈other) :
    ofInitial G O hG hM hlinear b hb initial≈ofInitial G P hH hN hlinear b hb other :=
  (agreement_iff_evaluation G O hG hM hlinear b hb _ _).2
    (Setoid.trans (ofInitial_evaluation G O hG hM hlinear b hb initial)
      (Setoid.trans hi (Setoid.symm (ofInitial_evaluation G P hH hN hlinear b hb other))))

theorem initialMap_base_congr (c : Scalar) (hc : D c) (hbc : b≈c) (initial other : Fiber n)
    (hi : initial≈other) :
    relabel c hbc (ofInitial G O hG hM hlinear b hb initial)≈ofInitial G O hG hM hlinear c hc other :=
  (agreement_iff_evaluation G O hG hM hlinear c hc _ _).2
    (Setoid.trans (relabel_evaluation c hbc _)
      (Setoid.trans (ofInitial_evaluation G O hG hM hlinear b hb initial)
        (Setoid.trans hi (Setoid.symm (ofInitial_evaluation G O hG hM hlinear c hc other)))))

end ComputableAnalysis.RiemannHilbert.AnalyticSolutionGerm
