import ComputableAnalysis.ModularForms.DyadicOscillationCauchy
import ComputableAnalysis.ModularForms.PairedSquareDensityOscillation
import ComputableAnalysis.ModularForms.PairedRiccatiFullSquareSums

/-! Fixed-radius Cauchy estimates for actual oriented density averages. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

def pairedSquareDensitySample (a : Scalar) (edge : HalfEdge) (R u : Rat) : Scalar :=
  ⟨pairedSquareDensity a edge u R, pairedSquareDensity_valid a edge u R⟩

def pairedSquareDyadicAverage (a : Scalar) (edge : HalfEdge) (R : Rat) (n : Nat) : Scalar :=
  dyadicSampleAverage (pairedSquareDensitySample a edge R) ⟨0,1⟩ n

theorem pairedSquareDensity_dyadic_cauchy (a : Scalar) (edge : HalfEdge)
    (R : Rat) (hR : 0<R) (eps : QPos) :
    ∃ N, ∀ n m, N≤n → N≤m →
      Small (sub (pairedSquareDyadicAverage a edge R n).val
        (pairedSquareDyadicAverage a edge R m).val) eps.val :=
  dyadicAverage_cauchy_of_cell_oscillation (pairedSquareDensitySample a edge R)
    (pairedSquareDensity_dyadic_oscillation a edge R hR) eps

end ComputableAnalysis.ModularForms
