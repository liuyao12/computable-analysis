import ComputableAnalysis.RiemannHilbert.RepresentedUnitInterval

/-! Relative topology and quantitative continuity on all represented real
parameters in the closed unit interval. Topological continuity is separate
from executable local moduli. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
open ComplexRaw FunctionTheory DomainFunctions

structure IsOpen (U : Point → Prop) : Prop where
  invariant : ∀ s t, s ≈ t → (U s ↔ U t)
  neighborhood : ∀ s, U s → ∃ r : QPos, ∀ t,
    Small (sub (scalar t).val (scalar s).val) r.val → U t

theorem isOpen_univ : IsOpen (fun _ => True) :=
  ⟨fun _ _ _ => Iff.rfl,fun _ _ => ⟨unitError,fun _ _ => trivial⟩⟩

theorem isOpen_empty : IsOpen (fun _ => False) :=
  ⟨fun _ _ _ => Iff.rfl,fun _ h => False.elim h⟩

theorem isOpen_inter {U V : Point → Prop} (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (fun t => U t ∧ V t) where
  invariant s t hst := ⟨fun h => ⟨(hU.invariant s t hst).1 h.1,(hV.invariant s t hst).1 h.2⟩,
    fun h => ⟨(hU.invariant s t hst).2 h.1,(hV.invariant s t hst).2 h.2⟩⟩
  neighborhood s hs := by
    obtain ⟨r,hr⟩ := hU.neighborhood s hs.1
    obtain ⟨v,hv⟩ := hV.neighborhood s hs.2
    exact ⟨minRadius r v,fun t ht => ⟨hr t (ht.mono (minRadius_left _ _)),hv t (ht.mono (minRadius_right _ _))⟩⟩

theorem isOpen_union {I : Sort u} (U : I → Point → Prop) (hU : ∀ i, IsOpen (U i)) :
    IsOpen (fun t => ∃ i, U i t) where
  invariant s t hst := ⟨fun ⟨i,h⟩ => ⟨i,(hU i).invariant s t hst |>.1 h⟩,
    fun ⟨i,h⟩ => ⟨i,(hU i).invariant s t hst |>.2 h⟩⟩
  neighborhood s hs := by
    obtain ⟨i,hi⟩ := hs
    obtain ⟨r,hr⟩ := (hU i).neighborhood s hi
    exact ⟨r,fun t ht => ⟨i,hr t ht⟩⟩

theorem isOpen_congr {U V : Point → Prop} (hUV : ∀ t, U t ↔ V t) (hU : IsOpen U) : IsOpen V where
  invariant s t hst := (hUV s).symm.trans ((hU.invariant s t hst).trans (hUV t))
  neighborhood s hs := by
    obtain ⟨r,hr⟩ := hU.neighborhood s ((hUV s).2 hs)
    exact ⟨r,fun t ht => (hUV t).1 (hr t ht)⟩

theorem scalarPreimage_isOpen (D : Scalar → Prop) (hD : ScalarTopology.IsOpen D) :
    IsOpen (fun t => D (scalar t)) :=
  ⟨fun _ _ h => hD.invariant _ _ (scalar_congr h),fun s hs => by
    obtain ⟨r,hr⟩ := hD.neighborhood (scalar s) hs
    exact ⟨r,fun t ht => hr (scalar t) ht⟩⟩

def IsOpenAsSubspace (U : Point → Prop) : Prop :=
  ∃ D : Scalar → Prop, ScalarTopology.IsOpen D ∧ ∀ t, U t ↔ D (scalar t)

theorem isOpen_iff_subspace (U : Point → Prop) : IsOpen U ↔ IsOpenAsSubspace U := by
  constructor
  · intro hU
    let J := {j : Point × QPos // ∀ t, ScalarTopology.ball (scalar j.1) j.2 (scalar t) → U t}
    let D : Scalar → Prop := fun z => ∃ j : J, ScalarTopology.ball (scalar j.val.1) j.val.2 z
    refine ⟨D,ScalarTopology.isOpen_union _ (fun j : J => ScalarTopology.isOpen_ball _ _),?_⟩
    intro t
    constructor
    · intro ht
      obtain ⟨r,hr⟩ := hU.neighborhood t ht
      exact ⟨⟨(t,r),fun s hs => hr s (ScalarTopology.ball_bound _ _ _ hs)⟩,ScalarTopology.ball_center _ _⟩
    · rintro ⟨j,hj⟩
      exact j.property t hj
  · rintro ⟨D,hD,hUD⟩
    exact isOpen_congr (fun t => (hUD t).symm) (scalarPreimage_isOpen D hD)

structure ScalarContinuousData (f : Point → Scalar) where
  congr : ∀ s t, s ≈ t → f s ≈ f t
  delta : Point → QPos → QPos
  estimate : ∀ s eps t, Small (sub (scalar t).val (scalar s).val) (delta s eps).val →
    Small (sub (f t).val (f s).val) eps.val

def ScalarContinuous (f : Point → Scalar) : Prop :=
  ∀ D, ScalarTopology.IsOpen D → IsOpen (fun t => D (f t))

theorem ScalarContinuousData.continuous {f : Point → Scalar} (hf : ScalarContinuousData f) :
    ScalarContinuous f := by
  intro D hD
  refine ⟨fun s t h => hD.invariant _ _ (hf.congr s t h),?_⟩
  intro s hs
  obtain ⟨r,hr⟩ := hD.neighborhood (f s) hs
  exact ⟨hf.delta s r,fun t ht => hr (f t) (hf.estimate s r t ht)⟩

def ofDomainContinuous (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (hmem : ∀ t : Point, f.domain (scalar t)) : ScalarContinuousData (fun t => f.eval (scalar t) (hmem t)) where
  congr s t hst := f.eval_congr _ _ (hmem s) (hmem t) (scalar_congr hst)
  delta s eps := hc.delta (scalar s) (hmem s) eps
  estimate s eps t ht := hc.estimate _ (hmem s) eps _ (hmem t) ht

def constantContinuousData (a : Scalar) : ScalarContinuousData (fun _ => a) where
  congr _ _ _ := equiv_refl _ a.property
  delta _ eps := eps
  estimate _ eps _ _ := Small.congr (ofQComplex_valid _) (sub_valid a.property a.property)
    (equiv_symm (add_neg_equiv a.val a.property)) (Small.zero (Rat.le_of_lt eps.property))

def Continuous (f : Point → Point) : Prop := ∀ U, IsOpen U → IsOpen (fun t => U (f t))

theorem continuous_identity : Continuous (fun t => t) := fun _ h => h

theorem continuous_compose {f g : Point → Point} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun t => f (g t)) := fun U hU => hg (fun t => U (f t)) (hf U hU)

theorem continuous_reverse : Continuous reverse := by
  intro U hU
  refine ⟨fun s t h => hU.invariant _ _ (reverse_congr h),?_⟩
  intro s hs
  obtain ⟨r,hr⟩ := hU.neighborhood (reverse s) hs
  exact ⟨r,fun t ht => hr (reverse t) (reverse_distance s t r.val ht)⟩

theorem ScalarContinuous.reverse {f : Point → Scalar} (hf : ScalarContinuous f) :
    ScalarContinuous (fun t => f (reverse t)) := fun D hD => continuous_reverse _ (hf D hD)

end ComputableAnalysis.RiemannHilbert.UnitInterval
