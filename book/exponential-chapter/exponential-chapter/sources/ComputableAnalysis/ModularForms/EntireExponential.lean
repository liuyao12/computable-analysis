import ComputableAnalysis.ModularForms.ExponentialCharts
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicLocality

/-! Entire represented exponential obtained from agreeing factorial-series
charts. Every point has an executable evaluator; internal chart radii are hidden. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

/-- A chart large enough for the actual input's initial rational box. -/
def exponentialInputRadius (z : Scalar) : QPos :=
  ⟨LocalODE.boxCoordinateBound (z.val.compute 0)+1,
    by have h := LocalODE.boxCoordinateBound_nonneg (z.val.compute 0); grind only⟩

theorem exponentialInputRadius_mem (z : Scalar) :
    (exponentialChart (exponentialInputRadius z)).domain z := by
  refine ⟨LocalODE.boxCoordinateBound (z.val.compute 0),
    LocalODE.boxCoordinateBound_nonneg _, ?_, LocalODE.small_from_box z.val z.property 0⟩
  change LocalODE.boxCoordinateBound (z.val.compute 0) <
    LocalODE.boxCoordinateBound (z.val.compute 0)+1
  grind only

/-- The value is computed using a certified chart chosen from the input box. -/
def entireExponentialValue (z : Scalar) : Scalar :=
  ⟨(exponentialChart (exponentialInputRadius z)).eval z,
    (exponentialChart (exponentialInputRadius z)).valid z (exponentialInputRadius_mem z)⟩

theorem entireExponentialValue_congr (z w : Scalar) (hzw : z.val.Equiv w.val) :
    (entireExponentialValue z).val.Equiv (entireExponentialValue w).val :=
  exponentialChart_agreement _ _ z w (exponentialInputRadius_mem z) (exponentialInputRadius_mem w) hzw

def entireExponential : DomainFunctions.Map where
  domain _ := True
  eval z _ := entireExponentialValue z
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ hzw := entireExponentialValue_congr z w hzw

/-- Every supplied exponential chart agrees with the global evaluator. -/
theorem entireExponential_chart (R : QPos) (z : Scalar) (hz : (exponentialChart R).domain z) :
    ((exponentialChart R).eval z).Equiv (entireExponentialValue z).val :=
  exponentialChart_agreement R (exponentialInputRadius z) z z hz
    (exponentialInputRadius_mem z) (equiv_refl _ z.property)

/-- Actual holomorphicity on all valid represented complex inputs, derived
from local derivatives and proved overlap agreement. -/
def entireExponential_holomorphic : DomainFunctions.Holomorphic entireExponential :=
  DomainFunctions.holomorphic_of_local entireExponential
    (fun a _ => DomainFunctions.ofCertified (exponentialChart (exponentialInputRadius a)))
    (fun a _ => DomainFunctions.ofCertifiedHolomorphic (exponentialChart_holomorphic (exponentialInputRadius a)))
    (fun a _ => exponentialInputRadius_mem a)
    (fun _ _ _ _ => trivial)
    (fun a _ z hz => entireExponential_chart (exponentialInputRadius a) z hz)

end ComputableAnalysis.ModularForms
