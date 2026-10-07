import ComputableAnalysis.ModularForms.PairedOffPoleChartRecognition

/-! A terminating executable rational-box chart search for every valid represented input. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def riccatiChartRecognized (z : Scalar) (N : Nat) : Bool :=
  offPoleChartRecognized z N || poleChartRecognized z N

theorem riccatiChartRecognized_eventually (z : Scalar) :
    ∃ M, ∀ N, M≤N → riccatiChartRecognized z N=true := by
  rcases pairedRiccatiCharts_cover z with hz | ⟨k,hk⟩
  · obtain ⟨M,hM⟩ := offPoleChartRecognized_eventually z hz
    exact ⟨M,fun N hN => Bool.or_eq_true_iff.mpr (Or.inl (hM N hN))⟩
  · obtain ⟨M,hM⟩ := poleChartRecognized_eventually k z hk
    exact ⟨M,fun N hN => Bool.or_eq_true_iff.mpr (Or.inr (hM N hN))⟩

def riccatiChartSearchStage (z : Scalar) : Nat :=
  PrecisionSearch.firstFrom (riccatiChartRecognized z) (riccatiChartRecognized_eventually z) 0

theorem riccatiChartSearchStage_success (z : Scalar) :
    offPoleChartRecognized z (riccatiChartSearchStage z)=true ∨
      poleChartRecognized z (riccatiChartSearchStage z)=true :=
  Bool.or_eq_true_iff.mp (PrecisionSearch.firstFrom_spec (riccatiChartRecognized z)
    (riccatiChartRecognized_eventually z) 0).2

end ComputableAnalysis.ModularForms
