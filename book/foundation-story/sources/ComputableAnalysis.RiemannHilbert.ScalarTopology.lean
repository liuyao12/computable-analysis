import ComputableAnalysis.RiemannHilbert.SphereChartIsomorphisms
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicComposition
import ComputableAnalysis.RiemannHilbert.TranslatedHolomorphic

/-! The rational-neighborhood topology on valid represented complex values.
Open sets respect equality of represented values. Executable neighborhood
data are kept separate from arbitrary existential open-set witnesses. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarTopology
open ComplexRaw FunctionTheory DomainFunctions

structure IsOpen (D : Scalar → Prop) : Prop where
  invariant : ∀ z w, z ≈ w → (D z ↔ D w)
  neighborhood : ∀ a, D a → ∃ r : QPos, ∀ z, Small (sub z.val a.val) r.val → D z

structure OpenData (D : Scalar → Prop) where
  invariant : ∀ z w, z ≈ w → (D z ↔ D w)
  radius : ∀ a, D a → QPos
  inside : ∀ a ha z, Small (sub z.val a.val) (radius a ha).val → D z

theorem OpenData.isOpen {D : Scalar → Prop} (h : OpenData D) : IsOpen D :=
  ⟨h.invariant, fun a ha => ⟨h.radius a ha, h.inside a ha⟩⟩

def wholeData : OpenData (fun _ => True) :=
  ⟨fun _ _ _ => Iff.rfl,fun _ _ => unitError,fun _ _ _ _ => trivial⟩

def OpenData.congr {D E : Scalar → Prop} (hD : OpenData D) (hDE : ∀ z, D z ↔ E z) : OpenData E where
  invariant z w hzw := ⟨fun h => (hDE w).1 ((hD.invariant z w hzw).1 ((hDE z).2 h)),
    fun h => (hDE z).1 ((hD.invariant z w hzw).2 ((hDE w).2 h))⟩
  radius a ha := hD.radius a ((hDE a).2 ha)
  inside a ha z hza := (hDE z).1 (hD.inside a ((hDE a).2 ha) z hza)

def OpenData.inter {D E : Scalar → Prop} (hD : OpenData D) (hE : OpenData E) : OpenData (fun z => D z ∧ E z) where
  invariant z w hzw := ⟨fun h => ⟨(hD.invariant z w hzw).1 h.1,(hE.invariant z w hzw).1 h.2⟩,
    fun h => ⟨(hD.invariant z w hzw).2 h.1,(hE.invariant z w hzw).2 h.2⟩⟩
  radius a ha := minRadius (hD.radius a ha.1) (hE.radius a ha.2)
  inside a ha z hza := ⟨hD.inside a ha.1 z (hza.mono (minRadius_left _ _)),
    hE.inside a ha.2 z (hza.mono (minRadius_right _ _))⟩

theorem isOpen_univ : IsOpen (fun _ => True) :=
  ⟨fun _ _ _ => Iff.rfl, fun _ _ => ⟨unitError, fun _ _ => trivial⟩⟩

theorem isOpen_empty : IsOpen (fun _ => False) :=
  ⟨fun _ _ _ => Iff.rfl, fun _ h => False.elim h⟩

theorem isOpen_inter {D E : Scalar → Prop} (hD : IsOpen D) (hE : IsOpen E) :
    IsOpen (fun z => D z ∧ E z) where
  invariant z w hzw := ⟨fun h => ⟨(hD.invariant z w hzw).1 h.1, (hE.invariant z w hzw).1 h.2⟩,
    fun h => ⟨(hD.invariant z w hzw).2 h.1, (hE.invariant z w hzw).2 h.2⟩⟩
  neighborhood a ha := by
    obtain ⟨r,hr⟩ := hD.neighborhood a ha.1
    obtain ⟨s,hs⟩ := hE.neighborhood a ha.2
    exact ⟨minRadius r s, fun z hz => ⟨hr z (hz.mono (minRadius_left _ _)), hs z (hz.mono (minRadius_right _ _))⟩⟩

theorem isOpen_union {I : Sort u} (D : I → Scalar → Prop) (hD : ∀ i, IsOpen (D i)) :
    IsOpen (fun z => ∃ i, D i z) where
  invariant z w hzw := ⟨fun ⟨i,hi⟩ => ⟨i,(hD i).invariant z w hzw |>.1 hi⟩,
    fun ⟨i,hi⟩ => ⟨i,(hD i).invariant z w hzw |>.2 hi⟩⟩
  neighborhood a ha := by
    obtain ⟨i,hi⟩ := ha
    obtain ⟨r,hr⟩ := (hD i).neighborhood a hi
    exact ⟨r,fun z hz => ⟨i,hr z hz⟩⟩

theorem isOpen_congr {D E : Scalar → Prop} (hDE : ∀ z, D z ↔ E z) (hD : IsOpen D) : IsOpen E where
  invariant z w hzw := ⟨fun h => (hDE w).1 ((hD.invariant z w hzw).1 ((hDE z).2 h)),
    fun h => (hDE z).1 ((hD.invariant z w hzw).2 ((hDE w).2 h))⟩
  neighborhood a ha := by
    obtain ⟨r,hr⟩ := hD.neighborhood a ((hDE a).2 ha)
    exact ⟨r,fun z hz => (hDE z).1 (hr z hz)⟩

def ofDomain (f : DomainFunctions.Map) (hf : DomainFunctions.OpenDomain f) : OpenData f.domain :=
  ⟨f.domain_congr,hf.radius,hf.inside⟩

def nonzeroData : OpenData NonzeroBoxSearch.Nonzero :=
  ofDomain ReciprocalHolomorphic.function ReciprocalHolomorphic.holomorphic.openDomain

theorem isOpen_nonzero : IsOpen NonzeroBoxSearch.Nonzero := nonzeroData.isOpen

def preimage (f : DomainFunctions.Map) (D : Scalar → Prop) (z : Scalar) : Prop :=
  ∃ hf : f.domain z, D (f.eval z hf)

theorem preimage_inner {f : DomainFunctions.Map} {D : Scalar → Prop} {z : Scalar}
    (hz : preimage f D z) : f.domain z := by obtain ⟨h,_⟩ := hz; exact h

theorem preimage_outer {f : DomainFunctions.Map} {D : Scalar → Prop} {z : Scalar}
    (hz : preimage f D z) : D (f.eval z (preimage_inner hz)) := by obtain ⟨h,hD⟩ := hz; exact hD

theorem preimage_invariant (f : DomainFunctions.Map) (D : Scalar → Prop)
    (hD : ∀ z w, z ≈ w → (D z ↔ D w)) (z w : Scalar) (hzw : z ≈ w) :
    preimage f D z ↔ preimage f D w := by
  constructor
  · rintro ⟨hz,hDz⟩
    have hw := (f.domain_congr z w hzw).1 hz
    exact ⟨hw,(hD _ _ (f.eval_congr z w hz hw hzw)).1 hDz⟩
  · rintro ⟨hw,hDw⟩
    have hz := (f.domain_congr z w hzw).2 hw
    exact ⟨hz,(hD _ _ (f.eval_congr z w hz hw hzw)).2 hDw⟩

def preimageData (f : DomainFunctions.Map) (hf : DomainFunctions.OpenDomain f)
    (hc : ContinuousOn f.domain f.eval) (D : Scalar → Prop) (hD : OpenData D) : OpenData (preimage f D) where
  invariant := preimage_invariant f D hD.invariant
  radius a ha := minRadius (hf.radius a (preimage_inner ha))
    (hc.delta a (preimage_inner ha) (hD.radius (f.eval a (preimage_inner ha)) (preimage_outer ha)))
  inside a ha z hza := by
    have hz := hf.inside a (preimage_inner ha) z (hza.mono (minRadius_left _ _))
    exact ⟨hz,hD.inside _ (preimage_outer ha) (f.eval z hz)
      (hc.estimate a (preimage_inner ha) _ z hz (hza.mono (minRadius_right _ _)))⟩

theorem isOpen_preimage (f : DomainFunctions.Map) (hf : DomainFunctions.OpenDomain f)
    (hc : ContinuousOn f.domain f.eval) (D : Scalar → Prop) (hD : IsOpen D) : IsOpen (preimage f D) where
  invariant := preimage_invariant f D hD.invariant
  neighborhood a ha := by
    obtain ⟨r,hr⟩ := hD.neighborhood (f.eval a (preimage_inner ha)) (preimage_outer ha)
    refine ⟨minRadius (hf.radius a (preimage_inner ha)) (hc.delta a (preimage_inner ha) r), ?_⟩
    intro z hza
    have hz := hf.inside a (preimage_inner ha) z (hza.mono (minRadius_left _ _))
    exact ⟨hz,hr (f.eval z hz) (hc.estimate a (preimage_inner ha) r z hz (hza.mono (minRadius_right _ _)))⟩

def ball (a : Scalar) (r : QPos) (z : Scalar) : Prop := Centered.domain a r.val z

def ballData (a : Scalar) (r : QPos) : OpenData (ball a r) where
  invariant z w hzw := Centered.domain_congr a a z w r.val (equiv_refl _ a.property) hzw
  radius z hz := LocalODE.interiorRadius r.val (Centered.offset a z) hz
  inside z hz w hw := LocalODE.interiorRadius_inside r.val (Centered.offset a z) hz (Centered.offset a w)
    (Small.congr (sub_valid w.property z.property)
      (sub_valid (Centered.offset a w).property (Centered.offset a z).property)
      (equiv_symm (Centered.offset_difference a z w)) hw)

theorem isOpen_ball (a : Scalar) (r : QPos) : IsOpen (ball a r) := (ballData a r).isOpen

theorem ball_center (a : Scalar) (r : QPos) : ball a r a := Centered.center_mem a r

theorem ball_bound (a : Scalar) (r : QPos) (z : Scalar) (hz : ball a r z) :
    Small (sub z.val a.val) r.val := LocalODE.interior_bound r.val (Centered.offset a z) hz

end ComputableAnalysis.RiemannHilbert.ScalarTopology
