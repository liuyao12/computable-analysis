import ComputableAnalysis.RiemannHilbert.ContourDerivativeHolomorphic

/-! Constructed derivatives of every finite order retain the entire supplied
holomorphic domain. The witnesses are obtained by the proved derivative
closure, with no higher differentiability hypothesis. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory
set_option autoImplicit false

def iteratedHolomorphicDerivative (f : Map) (hf : Holomorphic f) : Nat → (Σ g : Map, Holomorphic g)
  | 0 => ⟨f,hf⟩
  | n+1 => let g := iteratedHolomorphicDerivative f hf n
           ⟨derivativeMap g.1 g.2,g.2.derivative_holomorphic⟩

def iteratedDerivativeMap (f : Map) (hf : Holomorphic f) (n : Nat) : Map := (iteratedHolomorphicDerivative f hf n).1

def iteratedDerivativeHolomorphic (f : Map) (hf : Holomorphic f) (n : Nat) : Holomorphic (iteratedDerivativeMap f hf n) :=
  (iteratedHolomorphicDerivative f hf n).2

theorem iteratedDerivative_domain (f : Map) (hf : Holomorphic f) (n : Nat) (z : Scalar) :
    (iteratedDerivativeMap f hf n).domain z↔f.domain z := by
  induction n with
  | zero => exact Iff.rfl
  | succ n ih => exact ih

theorem iteratedDerivative_zero (f : Map) (hf : Holomorphic f) (z : Scalar) (hz : f.domain z) :
    (iteratedDerivativeMap f hf 0).eval z hz≈f.eval z hz := equiv_refl _ (f.eval z hz).property

theorem iteratedDerivative_one (f : Map) (hf : Holomorphic f) (z : Scalar) (hz : f.domain z) :
    (iteratedDerivativeMap f hf 1).eval z ((iteratedDerivative_domain f hf 1 z).2 hz)≈hf.derivative z hz :=
  equiv_refl _ (hf.derivative z hz).property

theorem iteratedDerivative_successor (f : Map) (hf : Holomorphic f) (n : Nat) (z : Scalar) (hz : f.domain z) :
    (iteratedDerivativeMap f hf (n+1)).eval z ((iteratedDerivative_domain f hf (n+1) z).2 hz)≈
      (iteratedDerivativeHolomorphic f hf n).derivative z ((iteratedDerivative_domain f hf n z).2 hz) :=
  equiv_refl _ ((iteratedDerivativeHolomorphic f hf n).derivative z _).property

end ComputableAnalysis.RiemannHilbert.DomainFunctions
