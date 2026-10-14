import ComputableAnalysis.RiemannHilbert.DomainHolomorphicIntersectionSum
import ComputableAnalysis.RiemannHilbert.DomainDerivativeUniqueness

/-! Derivative agreement for actual holomorphic maps that agree on their open overlap. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

theorem Holomorphic.derivative_equiv_on_overlap {f g : Map} (hf : Holomorphic f) (hg : Holomorphic g)
    (he : ∀ z, ∀ hz : f.domain z, ∀ hw : g.domain z, (f.eval z hz).val.Equiv (g.eval z hw).val)
    (z : Scalar) (hz : f.domain z) (hw : g.domain z) :
    (hf.derivative z hz).val.Equiv (hg.derivative z hw).val := by
  let ho := intersectionOpenData hf hg
  let localMap := DomainFunctions.onDomain f ho.invariant (fun _ h => h.1)
  let hf' : Holomorphic localMap := hf.onDomain ho (fun _ h => h.1)
  let hg' : Holomorphic localMap := hg.transfer localMap (fun _ h => h.2)
    ⟨ho.radius,ho.inside⟩ (fun z h => equiv_symm (he z h.1 h.2))
  exact hf'.derivative_unique hg' z ⟨hz,hw⟩

end ComputableAnalysis.RiemannHilbert.DomainFunctions
