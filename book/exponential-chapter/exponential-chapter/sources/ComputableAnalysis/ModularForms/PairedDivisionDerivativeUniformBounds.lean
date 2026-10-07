import ComputableAnalysis.ModularForms.PairedOffPoleRiccatiDerivativeBound

/-! Uniform first and second division-series derivative bounds on the pole disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedRegularDivisionDerivativeValue_uniform_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    Small (pairedRegularDivisionDerivativeValue z hz) 128 := by
  have h := inverseSquareSeriesValue_bound _
    (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 64
    (pairedRegularDivisionDerivativeTerm_square_bound z hz)
  exact h.mono (by decide +kernel)

theorem pairedDivisionSecondDerivativeValue_uniform_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    Small (pairedDivisionSecondDerivativeValue z hz) 2304 := by
  have h := inverseSquareSeriesValue_bound _
    (fun n => (pairedDivisionSecondDerivativeTerm z hz n).property) 1152
    (pairedDivisionSecondDerivativeTerm_bound z hz)
  exact h.mono (by decide +kernel)

theorem pairedRegularDivisionMap_derivative_uniform_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    Small (pairedRegularDivisionMap_holomorphic.derivative z hz).val 128 :=
  pairedRegularDivisionDerivativeValue_uniform_bound z hz

theorem pairedDivisionFirstDerivativeMap_derivative_uniform_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    Small (pairedDivisionFirstDerivativeMap_holomorphic.derivative z hz).val 2304 :=
  pairedDivisionSecondDerivativeValue_uniform_bound z hz

end ComputableAnalysis.ModularForms
