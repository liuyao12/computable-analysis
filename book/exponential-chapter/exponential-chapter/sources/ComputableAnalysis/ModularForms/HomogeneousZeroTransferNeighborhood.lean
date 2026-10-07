import ComputableAnalysis.ModularForms.HomogeneousZeroNeighborhood
import ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic

/-! A constructed local zero-transfer implication at every actual domain point. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 2000000

theorem homogeneous_zero_transfer_neighborhood (f g : DomainFunctions.Map)
    (hf : Holomorphic f) (hg : Holomorphic g) (hfg : ∀ z, f.domain z → g.domain z)
    (heq : ∀ z hz, (hf.derivative z hz).val.Equiv
      (mul (g.eval z (hfg z hz)).val (f.eval z hz).val))
    (a : Scalar) (ha : f.domain a) :
    ∃ R : QPos, ∀ z w (hz : f.domain z) (hw : f.domain w),
      Small (sub z.val a.val) R.val → Small (sub w.val a.val) R.val →
      (f.eval z hz).val.Equiv zero → (f.eval w hw).val.Equiv zero := by
  classical
  by_cases he : (f.eval a ha).val.Equiv zero
  · refine ⟨HomogeneousZeroNeighborhood.radius f g hf hg hfg a ha,?_⟩
    intro z w hz hw hza hwa hz0
    exact HomogeneousZeroNeighborhood.zero_neighborhood f g hf hg hfg a ha heq he w hwa
  · let F := compose ReciprocalHolomorphic.function f
    let hF := ReciprocalHolomorphic.holomorphic.compose hf
    have hfa : F.domain a := ⟨ha,he⟩
    refine ⟨hF.openDomain.radius a hfa,?_⟩
    intro z w hz hw hza hwa hz0
    have hdz := hF.openDomain.inside a hfa z hza
    have hn := compose_outer_mem hdz
    exact False.elim (hn hz0)

end ComputableAnalysis.ModularForms
