import ComputableAnalysis.RiemannHilbert.ContourMatrixTaylor
import ComputableAnalysis.RiemannHilbert.LocalSystemEntrySeries
import ComputableAnalysis.RiemannHilbert.CenteredSystemChart
import ComputableAnalysis.RiemannHilbert.ChartDataInvariance

/-! A system chart constructed from any supplied finite-rank holomorphic
coefficient field. Its actual coefficient evaluator is proved equal to
the supplied linear operator, rather than assumed in the chart data. -/
namespace ComputableAnalysis.RiemannHilbert.ConstructedSystemODE
open ComplexRaw FunctionTheory LocalSystem DomainFunctions LinearField
set_option autoImplicit false
variable {n : Nat} {D : Scalar → Prop}
variable (G : Field (n := n) (m := n) D) (O : ScalarTopology.OpenData D)
    (hG : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hM : MatrixHolomorphic G O.invariant hG) (b : Scalar) (hb : D b)

def chart : SystemChart n where
  center := b
  coefficients := ConstructedMatrixTaylor.coefficientOperators G O hG hM b hb
  linear := ConstructedMatrixTaylor.coefficientOperators_linear G O hG hM b hb
  M := (n : Rat)*ConstructedMatrixTaylor.bound G O hG b hb
  K := (ConstructedMatrixTaylor.rate G O hG hM b hb).val
  nonnegM := Rat.mul_nonneg Rat.natCast_nonneg (ConstructedMatrixTaylor.bound_nonneg G O hG b hb)
  nonnegK := Rat.le_of_lt (ConstructedMatrixTaylor.rate G O hG hM b hb).property
  compatible := ConstructedMatrixTaylor.rate_dominates G O hG hM b hb
  majorant := ConstructedMatrixTaylor.coefficientOperators_bound G O hG hM b hb

def radius : QPos := ConstructedMatrixTaylor.radius G O hG hM b hb

def domain (z : Scalar) : Prop := Centered.domain b (radius G O hG hM b hb).val z

theorem center_mem : domain G O hG hM b hb b := Centered.center_mem b (radius G O hG hM b hb)

theorem domain_chart (z : Scalar) (hz : domain G O hG hM b hb z) : (chart G O hG hM b hb).domain z :=
  interior_mono _ _ (Centered.offset b z) (ConstructedMatrixTaylor.radius_ode_le G O hG hM b hb) hz

theorem domain_original (z : Scalar) (hz : domain G O hG hM b hb z) : D z :=
  ConstructedMatrixTaylor.radius_domain G O hG hM b hb z hz

/-- The actual operator sum in the ODE solver reconstructs the supplied
coefficient field throughout the common computed neighborhood. -/
theorem operator_agrees (hlinear : ∀ z hz, IsLinear (G z hz)) (z : Scalar)
    (hz : domain G O hG hM b hb z) (ha : D z) :
    ((chart G O hG hM b hb).operator z (domain_chart G O hG hM b hb z hz)).Equiv (G z ha) := by
  let c := chart G O hG hM b hb
  have hc := domain_chart G O hG hM b hb z hz
  apply (ValueMap.linear_equiv_iff_basis (c.operator z hc) (G z ha) (c.operator_linear z hc) (hlinear z ha)).2
  intro i j
  have he := coefficientValueMap_entry_series c.coefficients c.M c.K c.nonnegM c.nonnegK c.majorant b
    (ConstructedMatrixTaylor.coefficients G O hG hM b hb i j) (ConstructedMatrixTaylor.coefficients_valid G O hG hM b hb i j)
    (ConstructedMatrixTaylor.bound G O hG b hb) c.K (radius G O hG hM b hb).val
    (ConstructedMatrixTaylor.bound_nonneg G O hG b hb) c.nonnegK (Rat.le_of_lt (radius G O hG hM b hb).property)
    (ConstructedMatrixTaylor.coefficients_bound G O hG hM b hb i j) (ConstructedMatrixTaylor.radius_budget G O hG hM b hb) i j
    (ConstructedMatrixTaylor.coefficientOperators_entry G O hG hM b hb i j) z hc hz
  exact equiv_trans (((c.operator z hc).eval (Fiber.basis i)).property j)
    ((ConstructedMatrixTaylor.entry G O hG hM b hb i j).eval z hz).property (((G z ha).eval (Fiber.basis i)).property j)
    he (ConstructedMatrixTaylor.entry_agrees G O hG hM b hb i j z hz ha)

end ComputableAnalysis.RiemannHilbert.ConstructedSystemODE
