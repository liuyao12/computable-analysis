import ComputableAnalysis.RiemannHilbert.LocalSeriesHolomorphic
import ComputableAnalysis.RiemannHilbert.PrerequisiteExamples

/-! Instantiating the analytic derivative law for the unit scalar coefficient. -/
namespace ComputableAnalysis.RiemannHilbert.AnalyticExamples
open ComplexRaw FunctionTheory LocalODE PrerequisiteExamples

theorem one_small : Small ComplexRaw.one 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m; change (-1 : Rat) ≤ 1; decide +kernel
  · intro n m; change (1 : Rat) ≤ 1; decide +kernel
  · intro n m; change (-1 : Rat) ≤ 0; decide +kernel
  · intro n m; change (0 : Rat) ≤ 1; decide +kernel

theorem unit_coefficient_bound (n : Nat) : Small (unitCoefficient n) (1*(2 : Rat)^n) := by
  unfold unitCoefficient
  by_cases hn : n = 0
  · subst n
    rw [if_pos rfl]
    simpa only [Rat.pow_zero, Rat.mul_one] using one_small
  · rw [if_neg hn]
    exact Small.zero (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel)))

def unitSeries : CertifiedFunctions.Map :=
  seriesMap unitCoefficient ComplexRaw.one unitCoefficient_valid (ofQComplex_valid _)
    1 1 2 (1/32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    unit_coefficient_bound one_small (by decide +kernel)

def unitSeries_derivative (a : Scalar) (ha : interior (1/32) a) :
    CertifiedFunctions.HasDerivativeAt unitSeries a
      (sumDerivative unitCoefficient ComplexRaw.one a.val unitCoefficient_valid (ofQComplex_valid _)
        a.property 1 2 (1/32)) :=
  seriesMap_derivative unitCoefficient ComplexRaw.one unitCoefficient_valid (ofQComplex_valid _)
    1 1 2 (1/32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    unit_coefficient_bound one_small (by decide +kernel) a ha


def unitSeries_holomorphic : CertifiedFunctions.Holomorphic unitSeries :=
  seriesMap_holomorphic unitCoefficient ComplexRaw.one unitCoefficient_valid (ofQComplex_valid _)
    1 1 2 (1/32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) unit_coefficient_bound one_small (by decide +kernel)

def noisyOne : Scalar :=
  ⟨unitSeries.eval ⟨zero, ofQComplex_valid _⟩,
    unitSeries.valid _ ⟨0, by decide +kernel, by decide +kernel, Small.zero (by decide +kernel)⟩⟩

theorem noisyOne_equiv : noisyOne.val.Equiv one :=
  seriesMap_initial unitCoefficient one unitCoefficient_valid (ofQComplex_valid _)
    1 1 2 (1/32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) unit_coefficient_bound one_small (by decide +kernel)

theorem noisyOne_interior : interior 2 noisyOne :=
  ⟨1, by decide +kernel, by decide +kernel,
    Small.congr (ofQComplex_valid _) noisyOne.property (equiv_symm noisyOne_equiv) one_small⟩

end ComputableAnalysis.RiemannHilbert.AnalyticExamples
