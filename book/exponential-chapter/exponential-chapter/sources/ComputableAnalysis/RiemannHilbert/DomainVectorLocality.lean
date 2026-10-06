import ComputableAnalysis.RiemannHilbert.DomainHolomorphicLocality
import ComputableAnalysis.RiemannHilbert.DomainVectorHolomorphicLaws

/-! Local actual holomorphic vector evaluators construct global witnesses.
The domain radius is retained even at rank zero. Exact derivative agreement
is independent of every scalar/vector holomorphic witness choice. -/
namespace ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
open ComplexRaw FunctionTheory
variable {n : Nat}

theorem derivative_unique (f : Map n) (hf hg : Holomorphic f) (a : Scalar) (ha : f.domain a) :
    derivative f hf a ha ≈ derivative f hg a ha :=
  fun i => (hf i).derivative_unique (hg i) a ha

def holomorphic_of_local (f : Map n) (g : ∀ a, f.domain a → Map n)
    (hg : ∀ a ha, Holomorphic (g a ha)) (mem : ∀ a ha, (g a ha).domain a)
    (hInclude : ∀ a ha z, (g a ha).domain z → f.domain z)
    (agree : ∀ a ha z hz, (g a ha).eval z hz ≈ f.eval z (hInclude a ha z hz)) : Holomorphic f where
  openDomain := {
    radius a ha := (hg a ha).openDomain.radius a (mem a ha)
    inside a ha z hza := hInclude a ha z ((hg a ha).openDomain.inside a (mem a ha) z hza) }
  coordinates i := DomainFunctions.holomorphic_of_local (coordinate f i)
    (fun a ha => coordinate (g a ha) i) (fun a ha => (hg a ha).coordinates i) mem hInclude
    (fun a ha z hz => agree a ha z hz i)

end ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
