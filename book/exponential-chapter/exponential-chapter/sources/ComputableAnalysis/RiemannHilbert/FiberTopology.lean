import ComputableAnalysis.RiemannHilbert.ScalarTopology
import ComputableAnalysis.RiemannHilbert.FiniteFiberBasis
import ComputableAnalysis.RiemannHilbert.LinearDifference

/-! Finite-coordinate topology with rational neighborhoods. Arbitrary open
sets use existential witnesses; executable neighborhood data remain explicit.
Every supplied finite-rank linear map is proved continuous from its computed
basis bound, including maps with rank-zero source or target. -/
namespace ComputableAnalysis.RiemannHilbert.FiberTopology
open ComplexRaw FunctionTheory DomainFunctions LocalSystem
variable {n m : Nat}

def Near (z a : Fiber n) (r : QPos) : Prop := CoordinateBound (Fiber.sub z a) r.val

theorem Near.mono {z a : Fiber n} {r s : QPos} (h : Near z a r) (hrs : r.val ≤ s.val) :
    Near z a s := fun i => (h i).mono hrs

theorem Near.congr {z z' a a' : Fiber n} {r : QPos} (hz : z ≈ z') (ha : a ≈ a')
    (h : Near z a r) : Near z' a' r := bound_congr (Fiber.sub_congr hz ha) h

theorem near_self (a : Fiber n) (r : QPos) : Near a a r :=
  fun i => (Fiber.sub_zero_bound (Setoid.refl a) i).mono (Rat.le_of_lt r.property)

structure IsOpen (D : Fiber n → Prop) : Prop where
  invariant : ∀ z w, z ≈ w → (D z ↔ D w)
  neighborhood : ∀ a, D a → ∃ r : QPos, ∀ z, Near z a r → D z

structure OpenData (D : Fiber n → Prop) where
  invariant : ∀ z w, z ≈ w → (D z ↔ D w)
  radius : ∀ a, D a → QPos
  inside : ∀ a ha z, Near z a (radius a ha) → D z

theorem OpenData.isOpen {D : Fiber n → Prop} (h : OpenData D) : IsOpen D :=
  ⟨h.invariant,fun a ha => ⟨h.radius a ha,h.inside a ha⟩⟩

def wholeData : OpenData (n := n) (fun _ => True) :=
  ⟨fun _ _ _ => Iff.rfl,fun _ _ => unitError,fun _ _ _ _ => trivial⟩

theorem isOpen_univ : IsOpen (n := n) (fun _ => True) := wholeData.isOpen

theorem isOpen_empty : IsOpen (n := n) (fun _ => False) :=
  ⟨fun _ _ _ => Iff.rfl,fun _ h => False.elim h⟩

theorem isOpen_congr {D E : Fiber n → Prop} (hDE : ∀ z, D z ↔ E z) (hD : IsOpen D) : IsOpen E where
  invariant z w hzw := ⟨fun h => (hDE w).1 ((hD.invariant z w hzw).1 ((hDE z).2 h)),
    fun h => (hDE z).1 ((hD.invariant z w hzw).2 ((hDE w).2 h))⟩
  neighborhood a ha := by
    obtain ⟨r,hr⟩ := hD.neighborhood a ((hDE a).2 ha)
    exact ⟨r,fun z hz => (hDE z).1 (hr z hz)⟩

def OpenData.inter {D E : Fiber n → Prop} (hD : OpenData D) (hE : OpenData E) :
    OpenData (fun z => D z ∧ E z) where
  invariant z w hzw := ⟨fun h => ⟨(hD.invariant z w hzw).1 h.1,(hE.invariant z w hzw).1 h.2⟩,
    fun h => ⟨(hD.invariant z w hzw).2 h.1,(hE.invariant z w hzw).2 h.2⟩⟩
  radius a ha := minRadius (hD.radius a ha.1) (hE.radius a ha.2)
  inside a ha z hz := ⟨hD.inside a ha.1 z (hz.mono (minRadius_left _ _)),
    hE.inside a ha.2 z (hz.mono (minRadius_right _ _))⟩

theorem isOpen_inter {D E : Fiber n → Prop} (hD : IsOpen D) (hE : IsOpen E) :
    IsOpen (fun z => D z ∧ E z) where
  invariant z w hzw := ⟨fun h => ⟨(hD.invariant z w hzw).1 h.1,(hE.invariant z w hzw).1 h.2⟩,
    fun h => ⟨(hD.invariant z w hzw).2 h.1,(hE.invariant z w hzw).2 h.2⟩⟩
  neighborhood a ha := by
    obtain ⟨r,hr⟩ := hD.neighborhood a ha.1
    obtain ⟨s,hs⟩ := hE.neighborhood a ha.2
    exact ⟨minRadius r s,fun z hz =>
      ⟨hr z (hz.mono (minRadius_left _ _)),hs z (hz.mono (minRadius_right _ _))⟩⟩

theorem isOpen_union {I : Sort u} (D : I → Fiber n → Prop) (hD : ∀ i, IsOpen (D i)) :
    IsOpen (fun z => ∃ i, D i z) where
  invariant z w hzw := ⟨fun ⟨i,hi⟩ => ⟨i,(hD i).invariant z w hzw |>.1 hi⟩,
    fun ⟨i,hi⟩ => ⟨i,(hD i).invariant z w hzw |>.2 hi⟩⟩
  neighborhood a ha := by
    obtain ⟨i,hi⟩ := ha
    obtain ⟨r,hr⟩ := (hD i).neighborhood a hi
    exact ⟨r,fun z hz => ⟨i,hr z hz⟩⟩

def finiteRadius : List QPos → QPos
  | [] => unitError
  | r::rs => minRadius r (finiteRadius rs)

theorem finiteRadius_le (r : QPos) (rs : List QPos) (hr : r ∈ rs) :
    (finiteRadius rs).val ≤ r.val := by
  induction rs with
  | nil => simp at hr
  | cons s rs ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst r
      exact minRadius_left _ _
    · exact Rat.le_trans (minRadius_right _ _) (ih h)

def coordinatePreimage (i : Fin n) (D : Scalar → Prop) : Fiber n → Prop :=
  fun x => D (Fiber.coordinate x i)

def coordinatePreimageData (i : Fin n) (D : Scalar → Prop) (hD : ScalarTopology.OpenData D) :
    OpenData (coordinatePreimage i D) where
  invariant z w hzw := hD.invariant (Fiber.coordinate z i) (Fiber.coordinate w i) (hzw i)
  radius a ha := hD.radius (Fiber.coordinate a i) ha
  inside a ha z hz := hD.inside (Fiber.coordinate a i) ha (Fiber.coordinate z i) (hz i)

theorem isOpen_coordinatePreimage (i : Fin n) (D : Scalar → Prop) (hD : ScalarTopology.IsOpen D) :
    IsOpen (coordinatePreimage i D) where
  invariant z w hzw := hD.invariant (Fiber.coordinate z i) (Fiber.coordinate w i) (hzw i)
  neighborhood a ha := by
    obtain ⟨r,hr⟩ := hD.neighborhood (Fiber.coordinate a i) ha
    exact ⟨r,fun z hz => hr (Fiber.coordinate z i) (hz i)⟩

def coordinateProductData (D : Fin n → Scalar → Prop) (hD : ∀ i, ScalarTopology.OpenData (D i)) :
    OpenData (fun x => ∀ i, D i (Fiber.coordinate x i)) where
  invariant z w hzw := ⟨fun h i => ((hD i).invariant (Fiber.coordinate z i) (Fiber.coordinate w i) (hzw i)).1 (h i),
    fun h i => ((hD i).invariant (Fiber.coordinate z i) (Fiber.coordinate w i) (hzw i)).2 (h i)⟩
  radius a ha := finiteRadius (List.ofFn (fun i => (hD i).radius (Fiber.coordinate a i) (ha i)))
  inside a ha z hz i := (hD i).inside (Fiber.coordinate a i) (ha i) (Fiber.coordinate z i)
    ((hz i).mono (finiteRadius_le _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))

theorem isOpen_finite_inter {I : Type u} (is : List I) (D : I → Fiber n → Prop)
    (hD : ∀ i ∈ is, IsOpen (D i)) : IsOpen (fun z => ∀ i ∈ is, D i z) := by
  induction is with
  | nil => exact isOpen_congr (fun z => by simp) isOpen_univ
  | cons i is ih =>
    apply isOpen_congr (D := fun z => D i z ∧ ∀ j ∈ is, D j z) (fun z => by simp)
    exact isOpen_inter (hD i (by simp)) (ih (fun j hj => hD j (by simp [hj])))

/-- The coordinate product topology holds without choosing a family of
existential radii by an abstract choice operation. -/
theorem isOpen_coordinateProduct (D : Fin n → Scalar → Prop) (hD : ∀ i, ScalarTopology.IsOpen (D i)) :
    IsOpen (fun x => ∀ i, D i (Fiber.coordinate x i)) := by
  have h := isOpen_finite_inter (List.ofFn (fun i : Fin n => i))
    (fun i => coordinatePreimage i (D i)) (fun i _ => isOpen_coordinatePreimage i (D i) (hD i))
  apply isOpen_congr (hD := h)
  intro z
  constructor
  · intro hz i
    exact hz i (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro hz i _
    exact hz i

def ball (a : Fiber n) (r : QPos) (z : Fiber n) : Prop :=
  ∀ i, ScalarTopology.ball (Fiber.coordinate a i) r (Fiber.coordinate z i)

def ballData (a : Fiber n) (r : QPos) : OpenData (ball a r) :=
  coordinateProductData (fun i => ScalarTopology.ball (Fiber.coordinate a i) r)
    (fun i => ScalarTopology.ballData (Fiber.coordinate a i) r)

theorem isOpen_ball (a : Fiber n) (r : QPos) : IsOpen (ball a r) := (ballData a r).isOpen

theorem ball_center (a : Fiber n) (r : QPos) : ball a r a :=
  fun i => ScalarTopology.ball_center (Fiber.coordinate a i) r

theorem ball_near (a : Fiber n) (r : QPos) (z : Fiber n) (hz : ball a r z) : Near z a r :=
  fun i => ScalarTopology.ball_bound (Fiber.coordinate a i) r (Fiber.coordinate z i) (hz i)

theorem ball_neighborhood {D : Fiber n → Prop} (hD : IsOpen D) (a : Fiber n) (ha : D a) :
    ∃ r : QPos, ball a r a ∧ ∀ z, ball a r z → D z := by
  obtain ⟨r,hr⟩ := hD.neighborhood a ha
  exact ⟨r,ball_center a r,fun z hz => hr z (ball_near a r z hz)⟩

theorem near_ball (a : Fiber n) (r s : QPos) (hsr : s.val < r.val)
    (z : Fiber n) (hz : Near z a s) : ball a r z :=
  fun i => ⟨s.val,Rat.le_of_lt s.property,hsr,hz i⟩

/-- Uniform rational coordinate balls form a neighborhood basis. -/
theorem isOpen_iff_balls (D : Fiber n → Prop)
    (hD : ∀ z w, z ≈ w → (D z ↔ D w)) :
    IsOpen D ↔ ∀ a, D a → ∃ r : QPos, ∀ z, ball a r z → D z := by
  constructor
  · intro h a ha
    obtain ⟨r,_,hr⟩ := ball_neighborhood h a ha
    exact ⟨r,hr⟩
  · intro h
    refine ⟨hD,?_⟩
    intro a ha
    obtain ⟨r,hr⟩ := h a ha
    let s : QPos := ⟨r.val/2,by have := r.property; grind⟩
    have hsr : s.val < r.val := by have := r.property; dsimp [s]; grind
    exact ⟨s,fun z hz => hr z (near_ball a r s hsr z hz)⟩

theorem rank_zero_equiv (x y : Fiber 0) : x ≈ y := fun i => Fin.elim0 i

theorem rank_zero_isOpen (D : Fiber 0 → Prop)
    (hD : ∀ z w, z ≈ w → (D z ↔ D w)) : IsOpen D :=
  ⟨hD,fun a ha => ⟨unitError,fun z _ => (hD a z (rank_zero_equiv a z)).1 ha⟩⟩

structure ContinuousData (f : ValueMap (Fiber n) (Fiber m)) where
  delta : Fiber n → QPos → QPos
  estimate : ∀ a eps z, Near z a (delta a eps) → Near (f.eval z) (f.eval a) eps

def Continuous (f : ValueMap (Fiber n) (Fiber m)) : Prop :=
  ∀ D, IsOpen D → IsOpen (fun z => D (f.eval z))

def ContinuousData.preimageData {f : ValueMap (Fiber n) (Fiber m)}
    (hf : ContinuousData f) (D : Fiber m → Prop) (hD : OpenData D) :
    OpenData (fun z => D (f.eval z)) where
  invariant z w hzw := hD.invariant (f.eval z) (f.eval w) (f.congr hzw)
  radius a ha := hf.delta a (hD.radius (f.eval a) ha)
  inside a ha z hz := hD.inside _ ha (f.eval z) (hf.estimate a _ z hz)

theorem ContinuousData.continuous {f : ValueMap (Fiber n) (Fiber m)} (hf : ContinuousData f) :
    Continuous f := by
  intro D hD
  refine ⟨fun z w hzw => hD.invariant (f.eval z) (f.eval w) (f.congr hzw),?_⟩
  intro a ha
  obtain ⟨r,hr⟩ := hD.neighborhood (f.eval a) ha
  exact ⟨hf.delta a r,fun z hz => hr (f.eval z) (hf.estimate a r z hz)⟩

theorem continuous_congr {f g : ValueMap (Fiber n) (Fiber m)}
    (hf : Continuous f) (hfg : f.Equiv g) : Continuous g := by
  intro D hD
  exact isOpen_congr (fun x => hD.invariant _ _ (hfg x)) (hf D hD)

theorem continuous_followedBy {k : Nat} {f : ValueMap (Fiber n) (Fiber m)}
    {g : ValueMap (Fiber m) (Fiber k)} (hf : Continuous f) (hg : Continuous g) :
    Continuous (f.followedBy g) := fun D hD => hf _ (hg D hD)

def linearRate (f : ValueMap (Fiber n) (Fiber m)) : QPos :=
  ⟨f.linearBound+1,by have := f.linearBound_nonneg; grind⟩

/-- Executable epsilon-delta data derived from finite basis evaluation. -/
def linearContinuousData (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f) :
    ContinuousData f where
  delta _ eps := divideRadius eps (linearRate f)
  estimate a eps z hz := by
    have hd : 0 ≤ (divideRadius eps (linearRate f)).val :=
      Rat.le_of_lt (divideRadius eps (linearRate f)).property
    have hs := ValueMap.difference_bound f hf f.linearBound (f.linear_bound hf)
      _ hd z a hz
    intro i
    apply (hs i).mono
    have hP : f.linearBound ≤ (linearRate f).val := by unfold linearRate; grind
    have h := Rat.mul_le_mul_of_nonneg_right hP hd
    rw [divideRadius_identity] at h
    exact h

theorem linear_continuous (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f) : Continuous f :=
  (linearContinuousData f hf).continuous

theorem linearIso_open_iff (f : LinearIso n m) (D : Fiber m → Prop)
    (hD : ∀ z w, z ≈ w → (D z ↔ D w)) :
    IsOpen (fun z => D (f.toValueIso.forward.eval z)) ↔ IsOpen D := by
  constructor
  · intro h
    have hb := linear_continuous f.toValueIso.backward f.inverse.linear _ h
    exact isOpen_congr (fun z => hD _ _ (f.toValueIso.forward_backward z)) hb
  · exact linear_continuous f.toValueIso.forward f.linear D

end ComputableAnalysis.RiemannHilbert.FiberTopology
