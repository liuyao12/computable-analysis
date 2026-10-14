import ComputableAnalysis.RiemannHilbert.FiberTopology

/-! The rational-neighborhood product topology on a represented complex
base coordinate and a finite-rank fiber. Both coordinates may vary. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarFiberTopology
open ComplexRaw FunctionTheory DomainFunctions
variable {n m : Nat}

abbrev Point (n : Nat) := Scalar × Fiber n

instance (n : Nat) : Setoid (Point n) where
  r x y := x.1.val.Equiv y.1.val ∧ x.2 ≈ y.2
  iseqv := ⟨fun x => ⟨equiv_refl _ x.1.property,Setoid.refl x.2⟩,
    fun h => ⟨equiv_symm h.1,Setoid.symm h.2⟩,
    fun {x y z} h k => ⟨equiv_trans x.1.property y.1.property z.1.property h.1 k.1,
      Setoid.trans h.2 k.2⟩⟩

def Near (z a : Point n) (r : QPos) : Prop :=
  Small (sub z.1.val a.1.val) r.val ∧ FiberTopology.Near z.2 a.2 r

theorem Near.mono {z a : Point n} {r s : QPos} (h : Near z a r) (hrs : r.val ≤ s.val) :
    Near z a s := ⟨h.1.mono hrs,h.2.mono hrs⟩

theorem near_self (a : Point n) (r : QPos) : Near a a r :=
  ⟨Small.congr (ofQComplex_valid _) (sub_valid a.1.property a.1.property)
      (equiv_symm (add_neg_equiv _ a.1.property)) (Small.zero (Rat.le_of_lt r.property)),
    FiberTopology.near_self a.2 r⟩

structure IsOpen (D : Point n → Prop) : Prop where
  invariant : ∀ z w, z ≈ w → (D z ↔ D w)
  neighborhood : ∀ a, D a → ∃ r : QPos, ∀ z, Near z a r → D z

structure OpenData (D : Point n → Prop) where
  invariant : ∀ z w, z ≈ w → (D z ↔ D w)
  radius : ∀ a, D a → QPos
  inside : ∀ a ha z, Near z a (radius a ha) → D z

theorem OpenData.isOpen {D : Point n → Prop} (h : OpenData D) : IsOpen D :=
  ⟨h.invariant,fun a ha => ⟨h.radius a ha,h.inside a ha⟩⟩

def wholeData : OpenData (n := n) (fun _ => True) :=
  ⟨fun _ _ _ => Iff.rfl,fun _ _ => unitError,fun _ _ _ _ => trivial⟩

theorem isOpen_univ : IsOpen (n := n) (fun _ => True) := wholeData.isOpen

theorem isOpen_empty : IsOpen (n := n) (fun _ => False) :=
  ⟨fun _ _ _ => Iff.rfl,fun _ h => False.elim h⟩

theorem isOpen_congr {D E : Point n → Prop} (hDE : ∀ z, D z ↔ E z) (hD : IsOpen D) : IsOpen E where
  invariant z w hzw := ⟨fun h => (hDE w).1 ((hD.invariant z w hzw).1 ((hDE z).2 h)),
    fun h => (hDE z).1 ((hD.invariant z w hzw).2 ((hDE w).2 h))⟩
  neighborhood a ha := by
    obtain ⟨r,hr⟩ := hD.neighborhood a ((hDE a).2 ha)
    exact ⟨r,fun z hz => (hDE z).1 (hr z hz)⟩

theorem isOpen_inter {D E : Point n → Prop} (hD : IsOpen D) (hE : IsOpen E) :
    IsOpen (fun z => D z ∧ E z) where
  invariant z w hzw := ⟨fun h => ⟨(hD.invariant z w hzw).1 h.1,(hE.invariant z w hzw).1 h.2⟩,
    fun h => ⟨(hD.invariant z w hzw).2 h.1,(hE.invariant z w hzw).2 h.2⟩⟩
  neighborhood a ha := by
    obtain ⟨r,hr⟩ := hD.neighborhood a ha.1
    obtain ⟨s,hs⟩ := hE.neighborhood a ha.2
    exact ⟨minRadius r s,fun z hz =>
      ⟨hr z (hz.mono (minRadius_left _ _)),hs z (hz.mono (minRadius_right _ _))⟩⟩

theorem isOpen_union {I : Sort u} (D : I → Point n → Prop) (hD : ∀ i, IsOpen (D i)) :
    IsOpen (fun z => ∃ i, D i z) where
  invariant z w hzw := ⟨fun ⟨i,hi⟩ => ⟨i,((hD i).invariant z w hzw).1 hi⟩,
    fun ⟨i,hi⟩ => ⟨i,((hD i).invariant z w hzw).2 hi⟩⟩
  neighborhood a ha := by
    obtain ⟨i,hi⟩ := ha
    obtain ⟨r,hr⟩ := (hD i).neighborhood a hi
    exact ⟨r,fun z hz => ⟨i,hr z hz⟩⟩

def baseData (D : Scalar → Prop) (hD : ScalarTopology.OpenData D) : OpenData (n := n) (fun z => D z.1) where
  invariant z w hzw := hD.invariant z.1 w.1 hzw.1
  radius a ha := hD.radius a.1 ha
  inside a ha z hz := hD.inside a.1 ha z.1 hz.1

theorem isOpen_base (D : Scalar → Prop) (hD : ScalarTopology.IsOpen D) :
    IsOpen (n := n) (fun z => D z.1) where
  invariant z w hzw := hD.invariant z.1 w.1 hzw.1
  neighborhood a ha := by
    obtain ⟨r,hr⟩ := hD.neighborhood a.1 ha
    exact ⟨r,fun z hz => hr z.1 hz.1⟩

theorem isOpen_fiber (D : Fiber n → Prop) (hD : FiberTopology.IsOpen D) :
    IsOpen (fun z : Point n => D z.2) where
  invariant z w hzw := hD.invariant z.2 w.2 hzw.2
  neighborhood a ha := by
    obtain ⟨r,hr⟩ := hD.neighborhood a.2 ha
    exact ⟨r,fun z hz => hr z.2 hz.2⟩

theorem isOpen_rectangle (D : Scalar → Prop) (E : Fiber n → Prop)
    (hD : ScalarTopology.IsOpen D) (hE : FiberTopology.IsOpen E) :
    IsOpen (fun z : Point n => D z.1 ∧ E z.2) := isOpen_inter (isOpen_base D hD) (isOpen_fiber E hE)

theorem rectangle_neighborhood {D : Point n → Prop} (hD : IsOpen D) (a : Point n) (ha : D a) :
    ∃ r : QPos, ∀ z, ScalarTopology.ball a.1 r z.1 → FiberTopology.ball a.2 r z.2 → D z := by
  obtain ⟨r,hr⟩ := hD.neighborhood a ha
  exact ⟨r,fun z hz hx => hr z ⟨ScalarTopology.ball_bound a.1 r z.1 hz,
    FiberTopology.ball_near a.2 r z.2 hx⟩⟩

structure ContinuousOn (D : Point n → Prop) (f : ∀ z, D z → Point m) where
  delta : ∀ a, D a → QPos → QPos
  estimate : ∀ a ha eps z hz, Near z a (delta a ha eps) → Near (f z hz) (f a ha) eps

def preimage (D : Point n → Prop) (f : ∀ z, D z → Point m) (U : Point m → Prop) (z : Point n) : Prop :=
  ∃ hz : D z, U (f z hz)

theorem preimage_isOpen (D : Point n → Prop) (hD : IsOpen D) (f : ∀ z, D z → Point m)
    (hfc : ∀ z w hz hw, z ≈ w → f z hz ≈ f w hw) (hf : ContinuousOn D f)
    (U : Point m → Prop) (hU : IsOpen U) : IsOpen (preimage D f U) where
  invariant z w hzw := by
    constructor
    · rintro ⟨hz,hu⟩
      have hw := (hD.invariant z w hzw).1 hz
      exact ⟨hw,(hU.invariant _ _ (hfc z w hz hw hzw)).1 hu⟩
    · rintro ⟨hw,hu⟩
      have hz := (hD.invariant z w hzw).2 hw
      exact ⟨hz,(hU.invariant _ _ (hfc z w hz hw hzw)).2 hu⟩
  neighborhood a ha := by
    obtain ⟨ha,hUa⟩ := ha
    obtain ⟨r,hr⟩ := hD.neighborhood a ha
    obtain ⟨s,hs⟩ := hU.neighborhood (f a ha) hUa
    refine ⟨minRadius r (hf.delta a ha s),?_⟩
    intro z hz
    have hDz := hr z (hz.mono (minRadius_left _ _))
    exact ⟨hDz,hs (f z hDz) (hf.estimate a ha s z hDz (hz.mono (minRadius_right _ _)))⟩

end ComputableAnalysis.RiemannHilbert.ScalarFiberTopology
