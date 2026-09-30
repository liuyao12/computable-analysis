import ComputableAnalysis.DerivativeContinuationPolynomial

/-! The primary open-domain complex derivative contract. Existing stronger
holomorphic estimates remain available to clients requiring derivative continuity. -/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw

private def meet (r s : QPos) : QPos :=
  ⟨min r.val s.val, by have := r.property; have := s.property; grind⟩

/-- Holomorphicity implies continuity of the computed function. -/
def HolomorphicOn.continuous {f : Map} (h : HolomorphicOn f) : ContinuousOn f.domain f.eval :=
  h.toDifferentiableOn.continuous

/-- The extra derivative-continuity evidence enters the legacy stronger interface. -/
def HolomorphicOn.toLegacy {f : Map} (h : HolomorphicOn f)
    (c : ContinuousOn f.domain h.derivative) : Holomorphic f :=
  h.toDifferentiableOn.holomorphic h.openDomain c

private def intersection {f g k : Map} (hf : OpenDomain f) (hg : OpenDomain g)
    (hk : ∀ z, k.domain z ↔ f.domain z ∧ g.domain z) : OpenDomain k where
  radius := fun a ha h => meet (hf.radius a ha ((hk a).mp h).1) (hg.radius a ha ((hk a).mp h).2)
  inside := by
    intro a ha h z hz hza
    exact (hk z).mpr ⟨hf.inside a ha ((hk a).mp h).1 z hz (hza.mono (by dsimp [meet]; grind)),
      hg.inside a ha ((hk a).mp h).2 z hz (hza.mono (by dsimp [meet]; grind))⟩

def HolomorphicOn.add {f g : Map} (hf : HolomorphicOn f) (hg : HolomorphicOn g) :
    HolomorphicOn (f.add g) where
  openDomain := intersection hf.openDomain hg.openDomain (fun _ => Iff.rfl)
  derivative := fun a => ComplexRaw.add (hf.derivative a) (hg.derivative a)
  atPoint := fun a ha h => (hf.atPoint a ha h.1).add (hg.atPoint a ha h.2)
  derivative_congr := fun ha hb h1 h2 he => add_equiv
    (hf.derivative_congr ha hb h1.1 h2.1 he) (hg.derivative_congr ha hb h1.2 h2.2 he)

def HolomorphicOn.mul {f g : Map} (hf : HolomorphicOn f) (hg : HolomorphicOn g) :
    HolomorphicOn (f.mul g) where
  openDomain := intersection hf.openDomain hg.openDomain (fun _ => Iff.rfl)
  derivative := fun a => ComplexRaw.add (ComplexRaw.mul (hf.derivative a) (g.eval a))
    (ComplexRaw.mul (f.eval a) (hg.derivative a))
  atPoint := fun a ha h => (hf.atPoint a ha h.1).mul (hg.atPoint a ha h.2)
  derivative_congr := by
    intro a b ha hb h1 h2 he
    exact add_equiv
      (mul_equiv (hf.atPoint a ha h1.1).derivative_valid (hf.atPoint b hb h2.1).derivative_valid
        (g.valid a ha h1.2) (g.valid b hb h2.2)
        (hf.derivative_congr ha hb h1.1 h2.1 he) (g.eval_congr ha hb h1.2 h2.2 he))
      (mul_equiv (f.valid a ha h1.1) (f.valid b hb h2.1)
        (hg.atPoint a ha h1.2).derivative_valid (hg.atPoint b hb h2.2).derivative_valid
        (f.eval_congr ha hb h1.1 h2.1 he) (hg.derivative_congr ha hb h1.2 h2.2 he))

/-- Composition retains the inverse-image domain and constructs its neighborhood. -/
def HolomorphicOn.comp {f g : Map} (hg : HolomorphicOn g) (hf : HolomorphicOn f) :
    HolomorphicOn (g.comp f) where
  openDomain := {
    radius := fun a ha h => meet (hf.openDomain.radius a ha h.1)
      (hf.continuous.delta a ha h.1 (hg.openDomain.radius (f.eval a) (f.valid a ha h.1) h.2))
    inside := by
      intro a ha h z hz hza
      have hfz := hf.openDomain.inside a ha h.1 z hz (hza.mono (by dsimp [meet]; grind))
      exact ⟨hfz,hg.openDomain.inside (f.eval a) (f.valid a ha h.1) h.2 (f.eval z)
        (f.valid z hz hfz) (hf.continuous.estimate a ha h.1 _ z hz hfz (hza.mono (by dsimp [meet]; grind)))⟩ }
  derivative := fun z => ComplexRaw.mul (hg.derivative (f.eval z)) (hf.derivative z)
  atPoint := fun a ha h => (hf.atPoint a ha h.1).comp (hg.atPoint _ (f.valid a ha h.1) h.2)
  derivative_congr := by
    intro a b ha hb h1 h2 he
    exact mul_equiv
      (hg.atPoint _ (f.valid a ha h1.1) h1.2).derivative_valid
      (hg.atPoint _ (f.valid b hb h2.1) h2.2).derivative_valid
      (hf.atPoint a ha h1.1).derivative_valid (hf.atPoint b hb h2.1).derivative_valid
      (hg.derivative_congr (f.valid a ha h1.1) (f.valid b hb h2.1) h1.2 h2.2
        (f.eval_congr ha hb h1.1 h2.1 he)) (hf.derivative_congr ha hb h1.1 h2.1 he)

/-- Derivative uniqueness follows from the open-domain theorem. -/
theorem HolomorphicOn.derivative_unique {f : Map} (h k : HolomorphicOn f)
    (a : ComplexRaw) (ha : a.Valid) (hfa : f.domain a) :
    (h.derivative a).Equiv (k.derivative a) :=
  (h.atPoint a ha hfa).unique h.openDomain (k.atPoint a ha hfa)

/-- Every represented polynomial inhabits the primary contract. -/
def PolynomialFunction.holomorphicOn (p : PolynomialFunction) : HolomorphicOn p.map where
  toDifferentiableOn := p.differentiable
  openDomain := { radius := fun _ _ _ => ⟨1,by decide⟩
                  inside := fun _ _ _ z _ _ => p.entire z }

end ComputableAnalysis.FunctionTheory
