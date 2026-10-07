import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums

/-! Actual holomorphic sums on the intersection of the supplied domains. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def intersectionSum (f g : Map) : Map where
  domain z := f.domain z ∧ g.domain z
  eval z hz := scalarSum (f.eval z hz.1) (g.eval z hz.2)
  domain_congr z w he := and_congr (f.domain_congr z w he) (g.domain_congr z w he)
  eval_congr z w hz hw he := add_equiv (f.eval_congr z w hz.1 hw.1 he)
    (g.eval_congr z w hz.2 hw.2 he)

def intersectionOpenData {f g : Map} (hf : Holomorphic f) (hg : Holomorphic g) :
    ScalarTopology.OpenData (intersectionSum f g).domain where
  invariant := (intersectionSum f g).domain_congr
  radius z hz := minRadius (hf.openDomain.radius z hz.1) (hg.openDomain.radius z hz.2)
  inside a ha z hd := ⟨hf.openDomain.inside a ha.1 z (hd.mono (minRadius_left _ _)),
    hg.openDomain.inside a ha.2 z (hd.mono (minRadius_right _ _))⟩

def Holomorphic.intersectionSum {f g : Map} (hf : Holomorphic f) (hg : Holomorphic g) :
    Holomorphic (intersectionSum f g) := by
  let ho := intersectionOpenData hf hg
  let hf' := hf.onDomain ho (fun _ hz => hz.1)
  let hg' := hg.onDomain ho (fun _ hz => hz.2)
  exact hf'.sumOn hg' (fun _ hz => hz)

end ComputableAnalysis.RiemannHilbert.DomainFunctions
