import ComputableAnalysis.RiemannHilbert.UnitIntervalTopology

/-! Product neighborhoods on two arbitrary represented real unit parameters.
The same rational radius controls both coordinates; this gives the product
topology, as witnessed by the rectangle-neighborhood characterization. -/
namespace ComputableAnalysis.RiemannHilbert.UnitSquare
open ComplexRaw FunctionTheory DomainFunctions

abbrev Point := UnitInterval.Point × UnitInterval.Point

instance : Setoid Point where
  r s t := s.1 ≈ t.1 ∧ s.2 ≈ t.2
  iseqv := ⟨fun s => ⟨Setoid.refl s.1,Setoid.refl s.2⟩,
    fun h => ⟨Setoid.symm h.1,Setoid.symm h.2⟩,
    fun h k => ⟨Setoid.trans h.1 k.1,Setoid.trans h.2 k.2⟩⟩

def Near (s t : Point) (r : QPos) : Prop :=
  Small (sub (UnitInterval.scalar t.1).val (UnitInterval.scalar s.1).val) r.val ∧
  Small (sub (UnitInterval.scalar t.2).val (UnitInterval.scalar s.2).val) r.val

theorem Near.mono {s t : Point} {r v : QPos} (h : Near s t r) (hrv : r.val ≤ v.val) : Near s t v :=
  ⟨h.1.mono hrv,h.2.mono hrv⟩

structure IsOpen (U : Point → Prop) : Prop where
  invariant : ∀ s t, s ≈ t → (U s ↔ U t)
  neighborhood : ∀ s, U s → ∃ r : QPos, ∀ t, Near s t r → U t

theorem isOpen_univ : IsOpen (fun _ => True) :=
  ⟨fun _ _ _ => Iff.rfl,fun _ _ => ⟨unitError,fun _ _ => trivial⟩⟩

theorem isOpen_empty : IsOpen (fun _ => False) :=
  ⟨fun _ _ _ => Iff.rfl,fun _ h => False.elim h⟩

theorem isOpen_inter {U V : Point → Prop} (hU : IsOpen U) (hV : IsOpen V) : IsOpen (fun s => U s ∧ V s) where
  invariant s t hst := ⟨fun h => ⟨(hU.invariant s t hst).1 h.1,(hV.invariant s t hst).1 h.2⟩,
    fun h => ⟨(hU.invariant s t hst).2 h.1,(hV.invariant s t hst).2 h.2⟩⟩
  neighborhood s hs := by
    obtain ⟨r,hr⟩ := hU.neighborhood s hs.1
    obtain ⟨v,hv⟩ := hV.neighborhood s hs.2
    exact ⟨minRadius r v,fun t ht => ⟨hr t (ht.mono (minRadius_left _ _)),hv t (ht.mono (minRadius_right _ _))⟩⟩

theorem isOpen_union {I : Sort u} (U : I → Point → Prop) (hU : ∀ i, IsOpen (U i)) : IsOpen (fun t => ∃ i, U i t) where
  invariant s t hst := ⟨fun ⟨i,h⟩ => ⟨i,(hU i).invariant s t hst |>.1 h⟩,
    fun ⟨i,h⟩ => ⟨i,(hU i).invariant s t hst |>.2 h⟩⟩
  neighborhood s hs := by
    obtain ⟨i,hi⟩ := hs
    obtain ⟨r,hr⟩ := (hU i).neighborhood s hi
    exact ⟨r,fun t ht => ⟨i,hr t ht⟩⟩

theorem isOpen_congr {U V : Point → Prop} (hUV : ∀ s, U s ↔ V s) (hU : IsOpen U) : IsOpen V where
  invariant s t hst := (hUV s).symm.trans ((hU.invariant s t hst).trans (hUV t))
  neighborhood s hs := by
    obtain ⟨r,hr⟩ := hU.neighborhood s ((hUV s).2 hs)
    exact ⟨r,fun t ht => (hUV t).1 (hr t ht)⟩

theorem firstPreimage_isOpen {U : UnitInterval.Point → Prop} (hU : UnitInterval.IsOpen U) : IsOpen (fun s : Point => U s.1) where
  invariant s t hst := hU.invariant s.1 t.1 hst.1
  neighborhood s hs := by
    obtain ⟨r,hr⟩ := hU.neighborhood s.1 hs
    exact ⟨r,fun t ht => hr t.1 ht.1⟩

theorem secondPreimage_isOpen {U : UnitInterval.Point → Prop} (hU : UnitInterval.IsOpen U) : IsOpen (fun s : Point => U s.2) where
  invariant s t hst := hU.invariant s.2 t.2 hst.2
  neighborhood s hs := by
    obtain ⟨r,hr⟩ := hU.neighborhood s.2 hs
    exact ⟨r,fun t ht => hr t.2 ht.2⟩

theorem rectangle_isOpen {U V : UnitInterval.Point → Prop} (hU : UnitInterval.IsOpen U) (hV : UnitInterval.IsOpen V) :
    IsOpen (fun s : Point => U s.1 ∧ V s.2) := isOpen_inter (firstPreimage_isOpen hU) (secondPreimage_isOpen hV)

theorem rectangle_neighborhood {U : Point → Prop} (hU : IsOpen U) (s : Point) (hs : U s) :
    ∃ V W : UnitInterval.Point → Prop, UnitInterval.IsOpen V ∧ UnitInterval.IsOpen W ∧
      V s.1 ∧ W s.2 ∧ ∀ t : Point, V t.1 → W t.2 → U t := by
  obtain ⟨r,hr⟩ := hU.neighborhood s hs
  let V := fun t => ScalarTopology.ball (UnitInterval.scalar s.1) r (UnitInterval.scalar t)
  let W := fun t => ScalarTopology.ball (UnitInterval.scalar s.2) r (UnitInterval.scalar t)
  refine ⟨V,W,UnitInterval.scalarPreimage_isOpen _ (ScalarTopology.isOpen_ball _ _),
    UnitInterval.scalarPreimage_isOpen _ (ScalarTopology.isOpen_ball _ _),
    ScalarTopology.ball_center _ _,ScalarTopology.ball_center _ _,?_⟩
  intro t ht1 ht2
  exact hr t ⟨ScalarTopology.ball_bound _ _ _ ht1,ScalarTopology.ball_bound _ _ _ ht2⟩

theorem firstSlice_isOpen {U : Point → Prop} (hU : IsOpen U) (s : UnitInterval.Point) : UnitInterval.IsOpen (fun t => U (s,t)) where
  invariant t v htv := hU.invariant _ _ ⟨Setoid.refl s,htv⟩
  neighborhood t ht := by
    obtain ⟨r,hr⟩ := hU.neighborhood (s,t) ht
    exact ⟨r,fun v hv => hr (s,v) ⟨Small.congr (ofQComplex_valid _)
      (sub_valid (UnitInterval.scalar s).property (UnitInterval.scalar s).property)
      (equiv_symm (add_neg_equiv _ (UnitInterval.scalar s).property)) (Small.zero (Rat.le_of_lt r.property)),hv⟩⟩

def reverseFirst (s : Point) : Point := (UnitInterval.reverse s.1,s.2)
def reverseSecond (s : Point) : Point := (s.1,UnitInterval.reverse s.2)

theorem reverseFirst_preimage {U : Point → Prop} (hU : IsOpen U) : IsOpen (fun s => U (reverseFirst s)) where
  invariant s t hst := hU.invariant _ _ ⟨UnitInterval.reverse_congr hst.1,hst.2⟩
  neighborhood s hs := by
    obtain ⟨r,hr⟩ := hU.neighborhood (reverseFirst s) hs
    exact ⟨r,fun t ht => hr (reverseFirst t) ⟨UnitInterval.reverse_distance s.1 t.1 r.val ht.1,ht.2⟩⟩

theorem reverseSecond_preimage {U : Point → Prop} (hU : IsOpen U) : IsOpen (fun s => U (reverseSecond s)) where
  invariant s t hst := hU.invariant _ _ ⟨hst.1,UnitInterval.reverse_congr hst.2⟩
  neighborhood s hs := by
    obtain ⟨r,hr⟩ := hU.neighborhood (reverseSecond s) hs
    exact ⟨r,fun t ht => hr (reverseSecond t) ⟨ht.1,UnitInterval.reverse_distance s.2 t.2 r.val ht.2⟩⟩

end ComputableAnalysis.RiemannHilbert.UnitSquare
