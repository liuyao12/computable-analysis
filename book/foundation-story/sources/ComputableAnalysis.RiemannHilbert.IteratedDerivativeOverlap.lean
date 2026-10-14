import ComputableAnalysis.RiemannHilbert.IteratedHolomorphicDerivatives
import ComputableAnalysis.RiemannHilbert.DomainDerivativeOverlap

/-! Equality of actual iterated derivatives on the open overlap of supplied
holomorphic maps. Only their values are assumed equal; every derivative
agreement is obtained from derivative uniqueness. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory
set_option autoImplicit false

theorem iteratedDerivative_overlap (f g : Map) (hf : Holomorphic f) (hg : Holomorphic g)
    (he : ∀ z hz hw, f.eval z hz≈g.eval z hw) (n : Nat) (z : Scalar)
    (hz : f.domain z) (hw : g.domain z) :
    (iteratedDerivativeMap f hf n).eval z ((iteratedDerivative_domain f hf n z).2 hz)≈
      (iteratedDerivativeMap g hg n).eval z ((iteratedDerivative_domain g hg n z).2 hw) := by
  induction n generalizing z with
  | zero => exact he z hz hw
  | succ n ih =>
    exact (iteratedDerivativeHolomorphic f hf n).derivative_equiv_on_overlap
      (iteratedDerivativeHolomorphic g hg n)
      (fun w hf' hg' => ih w ((iteratedDerivative_domain f hf n w).1 hf')
        ((iteratedDerivative_domain g hg n w).1 hg')) z
      ((iteratedDerivative_domain f hf n z).2 hz) ((iteratedDerivative_domain g hg n z).2 hw)

theorem iteratedDerivative_witness (f : Map) (hf hg : Holomorphic f) (n : Nat)
    (z : Scalar) (hz : f.domain z) :
    (iteratedDerivativeMap f hf n).eval z ((iteratedDerivative_domain f hf n z).2 hz)≈
      (iteratedDerivativeMap f hg n).eval z ((iteratedDerivative_domain f hg n z).2 hz) :=
  iteratedDerivative_overlap f f hf hg (fun w _ _ => equiv_refl _ (f.eval w _).property) n z hz hz

theorem iteratedDerivative_congr (f : Map) (hf hg : Holomorphic f) (n : Nat)
    (z w : Scalar) (hz : f.domain z) (hw : f.domain w) (he : z≈w) :
    (iteratedDerivativeMap f hf n).eval z ((iteratedDerivative_domain f hf n z).2 hz)≈
      (iteratedDerivativeMap f hg n).eval w ((iteratedDerivative_domain f hg n w).2 hw) :=
  Setoid.trans (iteratedDerivative_witness f hf hg n z hz)
    ((iteratedDerivativeMap f hg n).eval_congr z w
      ((iteratedDerivative_domain f hg n z).2 hz) ((iteratedDerivative_domain f hg n w).2 hw) he)

end ComputableAnalysis.RiemannHilbert.DomainFunctions
