import ComputableAnalysis.RiemannHilbert.DomainContinuity

/-! Holomorphic composition for executable domain-dependent maps:
the domain is proved open, the chain-rule derivative is constructed,
and its continuity and representation invariance are derived. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def composeOpen (f g : Map) (hf : OpenDomain f) (hg : OpenDomain g)
    (hc : ContinuousOn g.domain g.eval) : OpenDomain (compose f g) where
  radius a ha := minRadius (hg.radius a (compose_inner_mem ha))
    (hc.delta a (compose_inner_mem ha) (hf.radius (g.eval a (compose_inner_mem ha)) (compose_outer_mem ha)))
  inside a ha z hza := by
    have hz := hg.inside a (compose_inner_mem ha) z (hza.mono (minRadius_left _ _))
    have himage := hc.estimate a (compose_inner_mem ha) _ z hz (hza.mono (minRadius_right _ _))
    exact ⟨hz, hf.inside _ (compose_outer_mem ha) (g.eval z hz) himage⟩

def Holomorphic.continuous {f : Map} (h : Holomorphic f) : ContinuousOn f.domain f.eval :=
  continuousOn_of_derivative f h.derivative h.atPoint

def Holomorphic.compose {f g : Map} (hf : Holomorphic f) (hg : Holomorphic g) :
    Holomorphic (compose f g) where
  openDomain := composeOpen f g hf.openDomain hg.openDomain hg.continuous
  derivative a ha := scalarProduct (hf.derivative (g.eval a (compose_inner_mem ha)) (compose_outer_mem ha))
    (hg.derivative a (compose_inner_mem ha))
  atPoint a ha := composeDerivative f g a ha _ _
    (hf.atPoint (g.eval a (compose_inner_mem ha)) (compose_outer_mem ha))
    (hg.atPoint a (compose_inner_mem ha))
  derivative_congr a b ha hb hab :=
    mul_equiv (hf.derivative (g.eval a (compose_inner_mem ha)) (compose_outer_mem ha)).property
      (hf.derivative (g.eval b (compose_inner_mem hb)) (compose_outer_mem hb)).property
      (hg.derivative a (compose_inner_mem ha)).property (hg.derivative b (compose_inner_mem hb)).property
      (hf.derivative_congr _ _ _ _ (g.eval_congr _ _ _ _ hab))
      (hg.derivative_congr _ _ _ _ hab)
  continuousDerivative := productContinuous _ _
    (composeContinuous f g hf.derivative hf.continuousDerivative hg.continuous)
    (restrictContinuous hg.derivative hg.continuousDerivative (fun _ hz => compose_inner_mem hz))

end ComputableAnalysis.RiemannHilbert.DomainFunctions
