import ComputableAnalysis.RiemannHilbert.CoordinateConnectionPullback
import ComputableAnalysis.RiemannHilbert.DomainVectorScaling
import ComputableAnalysis.RiemannHilbert.ReciprocalSecondDerivative

/-! Holomorphicity of the constructed coordinate pullback coefficient.
The coordinate derivative must be justified as holomorphic; this evidence
is constructed for the actual reciprocal sphere transition. -/
namespace ComputableAnalysis.RiemannHilbert.CoordinateConnection
open ComplexRaw FunctionTheory
variable {n : Nat}

def action (f : DomainVectorFunctions.Map n) (A : Field (n := n) f.domain)
    (hA : ∀ z w hz hw, z.val.Equiv w.val → (A z hz).Equiv (A w hw))
    (x : Fiber n) : DomainVectorFunctions.Map n where
  domain := f.domain
  eval z hz := (A z hz).eval x
  domain_congr := f.domain_congr
  eval_congr z w hz hw hzw := hA z w hz hw hzw x

def HolomorphicCoefficient (f : DomainVectorFunctions.Map n) (A : Field (n := n) f.domain)
    (hA : ∀ z w hz hw, z.val.Equiv w.val → (A z hz).Equiv (A w hw)) : Type :=
  ∀ x : Fiber n, DomainVectorFunctions.Holomorphic (action f A hA x)

def pullback_holomorphic (f : DomainVectorFunctions.Map n) (A : Field (n := n) f.domain)
    (hA : ∀ z w hz hw, z.val.Equiv w.val → (A z hz).Equiv (A w hw))
    (hhol : HolomorphicCoefficient f A hA) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g)
    (hDg : DomainFunctions.Holomorphic (DomainFunctions.derivativeMap g hg)) :
    HolomorphicCoefficient (DomainVectorFunctions.pullback f g) (pullback f g hg A)
      (pullback_point_congr f g hg A hA) := by
  intro x
  exact DomainVectorFunctions.scaled_holomorphic
    (DomainVectorFunctions.pullback (action f A hA x) g)
    (DomainVectorFunctions.pullback_holomorphic (action f A hA x) (hhol x) g hg)
    (DomainFunctions.derivativeMap g hg) hDg
    (fun _ hz => DomainVectorFunctions.pullback_inner_mem (f := action f A hA x) (g := g) hz)

def reciprocal_holomorphic (f : DomainVectorFunctions.Map n) (A : Field (n := n) f.domain)
    (hA : ∀ z w hz hw, z.val.Equiv w.val → (A z hz).Equiv (A w hw))
    (hhol : HolomorphicCoefficient f A hA) :
    HolomorphicCoefficient (DomainVectorFunctions.pullback f ReciprocalHolomorphic.function)
      (pullback f ReciprocalHolomorphic.function ReciprocalHolomorphic.holomorphic A)
      (pullback_point_congr f ReciprocalHolomorphic.function ReciprocalHolomorphic.holomorphic A hA) :=
  pullback_holomorphic f A hA hhol ReciprocalHolomorphic.function ReciprocalHolomorphic.holomorphic
    ReciprocalHolomorphic.derivativeHolomorphic

end ComputableAnalysis.RiemannHilbert.CoordinateConnection
