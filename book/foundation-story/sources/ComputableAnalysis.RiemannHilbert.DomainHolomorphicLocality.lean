import ComputableAnalysis.RiemannHilbert.DomainDerivativeUniqueness
import ComputableAnalysis.RiemannHilbert.DomainDerivativeInvariance

/-! Actual holomorphicity is local on a represented open domain.
Supplied local evaluators agree with the actual target on their domains.
Derivative uniqueness constructs agreement of the different local choices;
global derivative errors and derivative continuity are derived, not assumed. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def HasDerivativeAt.of_local (f g : Map) (hgOpen : OpenDomain g)
    (hgf : ∀ z, g.domain z → f.domain z)
    (he : ∀ z hz, (g.eval z hz).val.Equiv (f.eval z (hgf z hz)).val)
    (a : Scalar) (ha : f.domain a) (hga : g.domain a) (d : Scalar)
    (h : HasDerivativeAt g a hga d) : HasDerivativeAt f a ha d where
  delta eps := minRadius (h.delta eps) (hgOpen.radius a hga)
  estimate eps H z hz hH hza := by
    have hgZ := hgOpen.inside a hga z (hza.mono (Rat.le_trans hH (minRadius_right _ _)))
    have hs := h.estimate eps H z hgZ (Rat.le_trans hH (minRadius_left _ _)) hza
    exact Small.congr (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _)
      (FunctionTheory.sub_congr (FunctionTheory.sub_congr (he z hgZ) (he a hga))
        (equiv_refl _ (mul_valid d.property (sub_valid z.property a.property)))) hs

def localOpenDomain (f : Map) (g : ∀ a, f.domain a → Map)
    (hg : ∀ a ha, Holomorphic (g a ha)) (mem : ∀ a ha, (g a ha).domain a)
    (hInclude : ∀ a ha z, (g a ha).domain z → f.domain z) : OpenDomain f where
  radius a ha := (hg a ha).openDomain.radius a (mem a ha)
  inside a ha z hza := hInclude a ha z ((hg a ha).openDomain.inside a (mem a ha) z hza)

def localDerivative (f : Map) (g : ∀ a, f.domain a → Map)
    (hg : ∀ a ha, Holomorphic (g a ha)) (mem : ∀ a ha, (g a ha).domain a)
    (a : Scalar) (ha : f.domain a) : Scalar := (hg a ha).derivative a (mem a ha)

def localDerivative_atPoint (f : Map) (g : ∀ a, f.domain a → Map)
    (hg : ∀ a ha, Holomorphic (g a ha)) (mem : ∀ a ha, (g a ha).domain a)
    (hInclude : ∀ a ha z, (g a ha).domain z → f.domain z)
    (agree : ∀ a ha z hz, (g a ha).eval z hz ≈ f.eval z (hInclude a ha z hz))
    (a : Scalar) (ha : f.domain a) : HasDerivativeAt f a ha (localDerivative f g hg mem a ha) :=
  HasDerivativeAt.of_local f (g a ha) (hg a ha).openDomain (hInclude a ha) (agree a ha)
    a ha (mem a ha) _ ((hg a ha).atPoint a (mem a ha))

theorem localDerivative_agreement (f : Map) (g : ∀ a, f.domain a → Map)
    (hg : ∀ a ha, Holomorphic (g a ha)) (mem : ∀ a ha, (g a ha).domain a)
    (hInclude : ∀ a ha z, (g a ha).domain z → f.domain z)
    (agree : ∀ a ha z hz, (g a ha).eval z hz ≈ f.eval z (hInclude a ha z hz))
    (a : Scalar) (ha : f.domain a) (z : Scalar) (hz : (g a ha).domain z) :
    localDerivative f g hg mem z (hInclude a ha z hz) ≈ (hg a ha).derivative z hz :=
  (localDerivative_atPoint f g hg mem hInclude agree z (hInclude a ha z hz)).unique
    (HasDerivativeAt.of_local f (g a ha) (hg a ha).openDomain (hInclude a ha) (agree a ha)
      z _ hz _ ((hg a ha).atPoint z hz)) (localOpenDomain f g hg mem hInclude)

def localDerivative_continuous (f : Map) (g : ∀ a, f.domain a → Map)
    (hg : ∀ a ha, Holomorphic (g a ha)) (mem : ∀ a ha, (g a ha).domain a)
    (hInclude : ∀ a ha z, (g a ha).domain z → f.domain z)
    (agree : ∀ a ha z hz, (g a ha).eval z hz ≈ f.eval z (hInclude a ha z hz)) :
    ContinuousOn f.domain (localDerivative f g hg mem) where
  delta a ha eps := minRadius ((hg a ha).openDomain.radius a (mem a ha))
    ((hg a ha).continuousDerivative.delta a (mem a ha) eps)
  estimate a ha eps z hz hza := by
    have hgZ := (hg a ha).openDomain.inside a (mem a ha) z (hza.mono (minRadius_left _ _))
    have hs := (hg a ha).continuousDerivative.estimate a (mem a ha) eps z hgZ
      (hza.mono (minRadius_right _ _))
    exact Small.congr
      (sub_valid ((hg a ha).derivative z hgZ).property ((hg a ha).derivative a (mem a ha)).property)
      (sub_valid (localDerivative f g hg mem z hz).property (localDerivative f g hg mem a ha).property)
      (FunctionTheory.sub_congr (equiv_symm (localDerivative_agreement f g hg mem hInclude agree a ha z hgZ))
        (equiv_refl _ ((hg a ha).derivative a (mem a ha)).property)) hs

/-- Actual local holomorphic witnesses construct a global witness on the
entire target domain. The local choices need not themselves be invariant:
uniqueness proves derivative-name invariance and choice agreement. -/
def holomorphic_of_local (f : Map) (g : ∀ a, f.domain a → Map)
    (hg : ∀ a ha, Holomorphic (g a ha)) (mem : ∀ a ha, (g a ha).domain a)
    (hInclude : ∀ a ha z, (g a ha).domain z → f.domain z)
    (agree : ∀ a ha z hz, (g a ha).eval z hz ≈ f.eval z (hInclude a ha z hz)) : Holomorphic f where
  openDomain := localOpenDomain f g hg mem hInclude
  derivative := localDerivative f g hg mem
  atPoint := localDerivative_atPoint f g hg mem hInclude agree
  derivative_congr a b ha hb hab :=
    (localDerivative_atPoint f g hg mem hInclude agree a ha).unique
      ((localDerivative_atPoint f g hg mem hInclude agree b hb).congrPoint ha (equiv_symm hab))
      (localOpenDomain f g hg mem hInclude)
  continuousDerivative := localDerivative_continuous f g hg mem hInclude agree

end ComputableAnalysis.RiemannHilbert.DomainFunctions
