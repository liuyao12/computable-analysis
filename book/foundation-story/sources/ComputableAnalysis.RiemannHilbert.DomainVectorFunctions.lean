import ComputableAnalysis.RiemannHilbert.DomainHolomorphicComposition

/-! Finite represented vector fields and their actual holomorphic coordinate
witnesses. Pullback is executable, respects represented points, and obtains
its derivative from the proved scalar chain rule. -/
namespace ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
open ComplexRaw FunctionTheory
variable {n : Nat}

structure Map (n : Nat) where
  domain : Scalar → Prop
  eval : (z : Scalar) → domain z → Fiber n
  domain_congr : ∀ z w, z.val.Equiv w.val → (domain z ↔ domain w)
  eval_congr : ∀ z w hz hw, z.val.Equiv w.val → eval z hz ≈ eval w hw

def coordinate (f : Map n) (i : Fin n) : DomainFunctions.Map where
  domain := f.domain
  eval z hz := ⟨(f.eval z hz).val i, (f.eval z hz).property i⟩
  domain_congr := f.domain_congr
  eval_congr z w hz hw hzw := f.eval_congr z w hz hw hzw i

structure OpenDomain (f : Map n) where
  radius : ∀ a, f.domain a → QPos
  inside : ∀ a ha z, Small (sub z.val a.val) (radius a ha).val → f.domain z

structure Holomorphic (f : Map n) where
  openDomain : OpenDomain f
  coordinates : ∀ i, DomainFunctions.Holomorphic (coordinate f i)

instance (f : Map n) : CoeFun (Holomorphic f) (fun _ => ∀ i, DomainFunctions.Holomorphic (coordinate f i)) :=
  ⟨fun h => h.coordinates⟩

def derivative (f : Map n) (hf : Holomorphic f) (z : Scalar) (hz : f.domain z) : Fiber n :=
  ⟨fun i => ((hf i).derivative z hz).val, fun i => ((hf i).derivative z hz).property⟩

def pullbackDomain (f : Map n) (g : DomainFunctions.Map) (z : Scalar) : Prop :=
  ∃ hg : g.domain z, f.domain (g.eval z hg)

theorem pullback_inner_mem {f : Map n} {g : DomainFunctions.Map} {z : Scalar}
    (hz : pullbackDomain f g z) : g.domain z := by obtain ⟨hg,_⟩ := hz; exact hg

theorem pullback_outer_mem {f : Map n} {g : DomainFunctions.Map} {z : Scalar}
    (hz : pullbackDomain f g z) : f.domain (g.eval z (pullback_inner_mem hz)) := by
  obtain ⟨hg,hf⟩ := hz
  exact hf

def pullback (f : Map n) (g : DomainFunctions.Map) : Map n where
  domain := pullbackDomain f g
  eval z hz := f.eval (g.eval z (pullback_inner_mem hz)) (pullback_outer_mem hz)
  domain_congr z w hzw := by
    constructor
    · rintro ⟨hz,hfz⟩
      have hw := (g.domain_congr z w hzw).1 hz
      exact ⟨hw, (f.domain_congr _ _ (g.eval_congr z w hz hw hzw)).1 hfz⟩
    · rintro ⟨hw,hfw⟩
      have hz := (g.domain_congr z w hzw).2 hw
      exact ⟨hz, (f.domain_congr _ _ (g.eval_congr z w hz hw hzw)).2 hfw⟩
  eval_congr z w hz hw hzw := f.eval_congr _ _ (pullback_outer_mem hz) (pullback_outer_mem hw)
    (g.eval_congr z w (pullback_inner_mem hz) (pullback_inner_mem hw) hzw)

def pullback_open (f : Map n) (hf : OpenDomain f) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) : OpenDomain (pullback f g) where
  radius a ha := DomainFunctions.minRadius (hg.openDomain.radius a (pullback_inner_mem ha))
    (hg.continuous.delta a (pullback_inner_mem ha)
      (hf.radius (g.eval a (pullback_inner_mem ha)) (pullback_outer_mem ha)))
  inside a ha z hza := by
    have hz := hg.openDomain.inside a (pullback_inner_mem ha) z
      (hza.mono (DomainFunctions.minRadius_left _ _))
    have himage := hg.continuous.estimate a (pullback_inner_mem ha) _ z hz
      (hza.mono (DomainFunctions.minRadius_right _ _))
    exact ⟨hz,hf.inside _ (pullback_outer_mem ha) (g.eval z hz) himage⟩

def pullback_holomorphic (f : Map n) (hf : Holomorphic f) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) : Holomorphic (pullback f g) where
  openDomain := pullback_open f hf.openDomain g hg
  coordinates i := (hf i).compose hg

theorem pullback_derivative (f : Map n) (hf : Holomorphic f) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) (z : Scalar) (hz : pullbackDomain f g z) :
    derivative (pullback f g) (pullback_holomorphic f hf g hg) z hz ≈
      Fiber.scale (hg.derivative z (pullback_inner_mem hz))
        (derivative f hf (g.eval z (pullback_inner_mem hz)) (pullback_outer_mem hz)) :=
  fun i => mul_comm_equiv _ _
    ((hf i).derivative (g.eval z (pullback_inner_mem hz)) (pullback_outer_mem hz)).property
    (hg.derivative z (pullback_inner_mem hz)).property

theorem derivative_congr (f : Map n) (hf : Holomorphic f) (z w : Scalar)
    (hz : f.domain z) (hw : f.domain w) (hzw : z.val.Equiv w.val) :
    derivative f hf z hz ≈ derivative f hf w hw :=
  fun i => (hf i).derivative_congr z w hz hw hzw

end ComputableAnalysis.RiemannHilbert.DomainVectorFunctions
