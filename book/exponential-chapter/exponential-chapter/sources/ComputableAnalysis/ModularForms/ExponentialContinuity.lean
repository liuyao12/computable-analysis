import ComputableAnalysis.ModularForms.ExponentialDerivative
import ComputableAnalysis.RiemannHilbert.GeneralSeriesContinuity

/-! Quantitative value continuity of the actual entire exponential. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem entireExponential_lipschitz (R : QPos) (a z : Scalar)
    (ha : (exponentialChart R).domain a) (hz : (exponentialChart R).domain z)
    (H : Rat) (hH : 0 ≤ H) (hza : Small (sub z.val a.val) H) :
    Small (sub (entireExponentialValue z).val (entireExponentialValue a).val)
      (16*exponentialBudget (exponentialRatio R)*(exponentialRatio R)^2*H) := by
  have hC := exponentialBudget_nonnegative _ (exponentialRatio_positive R)
  have hK := Rat.le_of_lt (exponentialRatio_positive R)
  have hR := Rat.le_of_lt R.property
  have h := BoundedSeries.sumDerivative_lipschitz exponentialCoefficients a.val z.val
    exponentialCoefficients_valid a.property z.property
    (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val H
    hC hK hR hH (exponentialCoefficients_small _ (exponentialRatio_positive R))
    (LocalODE.interior_bound R.val a ha) (LocalODE.interior_bound R.val z hz)
    hza (exponentialRatio_local R)
  have da := ((exponentialChart_holomorphic R).atPoint a ha).derivative_valid
  have dz := ((exponentialChart_holomorphic R).atPoint z hz).derivative_valid
  have ea := equiv_trans da ((exponentialChart R).valid a ha) (entireExponentialValue a).property
    (exponentialChart_derivative_value R a ha) (entireExponential_chart R a ha)
  have ez := equiv_trans dz ((exponentialChart R).valid z hz) (entireExponentialValue z).property
    (exponentialChart_derivative_value R z hz) (entireExponential_chart R z hz)
  exact Small.congr (sub_valid dz da)
    (sub_valid (entireExponentialValue z).property (entireExponentialValue a).property)
    (FunctionTheory.sub_congr ez ea) h

end ComputableAnalysis.ModularForms
