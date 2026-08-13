import ComputableAnalysis.Calculus

/-!
# Finite quadrature mean-value certificate

For a positive finite quadrature rule, an exact cell integral has an average
between any rational lower and upper bounds for the integrand.  This is the
computable replacement for selecting an intermediate point in the classical
Mean Value Theorem: it returns a rational interval for the average, not an
unavailable attained real point.
-/

namespace ComputableAnalysis

namespace Integral

theorem finiteQuadrature_average_between_bounds
    {eval : Rat -> Rat} {integralBetween : Rat -> Rat -> Rat}
    {a b p r lower upper : Rat} (nodes : List (Rat × Rat))
    (hnodes : ∀ node, node ∈ nodes -> 0 <= node.1 ∧ node.1 <= 1)
    (hweights : ∀ node, node ∈ nodes -> 0 <= node.2)
    (hsum : quadratureWeightSum nodes = 1)
    (hformula : ∀ p r : Rat,
      integralBetween p r = (r - p) * quadratureEvalSum eval p r nodes)
    (hap : a <= p) (hpr : p < r) (hrb : r <= b)
    (hlower : ∀ {x : Rat}, p <= x -> x <= r -> lower <= eval x)
    (hupper : ∀ {x : Rat}, p <= x -> x <= r -> eval x <= upper) :
    lower <= integralBetween p r / (r - p) ∧
      integralBetween p r / (r - p) <= upper := by
  exact (exactCellOrderPreservation_of_positive_quadrature
    a b nodes hnodes hweights hsum hformula).integral_average_between_bounds
    hap hpr hrb hlower hupper

end Integral

end ComputableAnalysis
