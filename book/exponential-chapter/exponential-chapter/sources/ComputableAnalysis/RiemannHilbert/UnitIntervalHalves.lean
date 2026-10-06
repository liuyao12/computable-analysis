import ComputableAnalysis.RiemannHilbert.RepresentedClamp
import ComputableAnalysis.RiemannHilbert.DomainProductRule

/-! Executable rescaled half-interval parameters for concatenation.
Clipping gives total unit parameters, exact branch identities and a global
distance bound, without deciding the order of an input represented real. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
open ComplexRaw FunctionTheory DomainFunctions

def midpoint : Point := rational (1/2) (by decide +kernel) (by decide +kernel)

def twiceShift (t : Point) (b : Rat) : RealRaw :=
  RealRaw.add (RealRaw.scaleRat 2 t.value) (RealRaw.ofRat b)

theorem twiceShift_valid (t : Point) (b : Rat) : (twiceShift t b).Valid :=
  RealRaw.add_valid (RealRaw.scaleRat_valid t.valid) (RealRaw.ofRat_valid b)

def leftParameter (t : Point) : Point := clip (twiceShift t 0) (twiceShift_valid t 0)
def rightParameter (t : Point) : Point := clip (twiceShift t (-1)) (twiceShift_valid t (-1))

theorem twiceShift_congr (s t : Point) (b : Rat) (hst : s ≈ t) : (twiceShift s b).Equiv (twiceShift t b) :=
  RealRaw.add_equiv (RealRaw.scaleRat_valid s.valid) (RealRaw.scaleRat_valid t.valid)
    (RealRaw.ofRat_valid b) (RealRaw.ofRat_valid b)
    (RealRaw.scaleRat_equiv hst) (RealRaw.equiv_refl (RealRaw.ofRat b) (RealRaw.ofRat_valid b))

theorem leftParameter_congr {s t : Point} (h : s ≈ t) : leftParameter s ≈ leftParameter t :=
  clip_congr _ _ (twiceShift_valid s 0) (twiceShift_valid t 0) (twiceShift_congr s t 0 h)

theorem rightParameter_congr {s t : Point} (h : s ≈ t) : rightParameter s ≈ rightParameter t :=
  clip_congr _ _ (twiceShift_valid s (-1)) (twiceShift_valid t (-1)) (twiceShift_congr s t (-1) h)

theorem twiceShift_distance (s t : Point) (b R : Rat) (hR : 0 ≤ R)
    (h : Small (sub (scalar t).val (scalar s).val) R) :
    Small (sub (ofRealRaw (twiceShift t b)) (ofRealRaw (twiceShift s b))) (2*R) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n m
    have hm := h.1 n m
    change -R ≤ (t.value.compute m).hi + -(s.value.compute m).lo at hm
    change -(2*R) ≤ (2*(t.value.compute m).hi+b) + -(2*(s.value.compute m).lo+b)
    grind only
  · intro n m
    have hn := h.2.1 n m
    change (t.value.compute n).lo + -(s.value.compute n).hi ≤ R at hn
    change (2*(t.value.compute n).lo+b) + -(2*(s.value.compute n).hi+b) ≤ 2*R
    grind only
  · intro n m
    change -(2*R) ≤ (0 : Rat)+ -0
    grind only
  · intro n m
    change (0 : Rat)+ -0 ≤ 2*R
    grind only

theorem leftParameter_distance (s t : Point) (R : Rat) (hR : 0 ≤ R)
    (h : Small (sub (scalar t).val (scalar s).val) R) :
    Small (sub (scalar (leftParameter t)).val (scalar (leftParameter s)).val) (2*R) :=
  clip_distance _ _ (twiceShift_valid t 0) (twiceShift_valid s 0) (2*R)
    (by grind only) (twiceShift_distance s t 0 R hR h)

theorem rightParameter_distance (s t : Point) (R : Rat) (hR : 0 ≤ R)
    (h : Small (sub (scalar t).val (scalar s).val) R) :
    Small (sub (scalar (rightParameter t)).val (scalar (rightParameter s)).val) (2*R) :=
  clip_distance _ _ (twiceShift_valid t (-1)) (twiceShift_valid s (-1)) (2*R)
    (by grind only) (twiceShift_distance s t (-1) R hR h)

structure ContinuousData (f : Point → Point) where
  congr : ∀ s t, s ≈ t → f s ≈ f t
  delta : Point → QPos → QPos
  estimate : ∀ s eps t, Small (sub (scalar t).val (scalar s).val) (delta s eps).val →
    Small (sub (scalar (f t)).val (scalar (f s)).val) eps.val

theorem ContinuousData.continuous {f : Point → Point} (hf : ContinuousData f) : Continuous f := by
  intro U hU
  refine ⟨fun s t hst => hU.invariant _ _ (hf.congr s t hst),?_⟩
  intro s hs
  obtain ⟨r,hr⟩ := hU.neighborhood (f s) hs
  exact ⟨hf.delta s r,fun t ht => hr (f t) (hf.estimate s r t ht)⟩

def leftParameterContinuousData : ContinuousData leftParameter where
  congr _ _ h := leftParameter_congr h
  delta _ eps := halfError eps
  estimate s eps t ht := by
    have h := leftParameter_distance s t (halfError eps).val (Rat.le_of_lt (halfError eps).property) ht
    rw [halfError_identity] at h
    exact h

def rightParameterContinuousData : ContinuousData rightParameter where
  congr _ _ h := rightParameter_congr h
  delta _ eps := halfError eps
  estimate s eps t ht := by
    have h := rightParameter_distance s t (halfError eps).val (Rat.le_of_lt (halfError eps).property) ht
    rw [halfError_identity] at h
    exact h

def doubled (t : Point) (ht : t.value.Le (RealRaw.ofRat (1/2))) : Point where
  value := twiceShift t 0
  valid := twiceShift_valid t 0
  lower n m := by
    have h := t.lower 0 m
    change 0 ≤ (t.value.compute m).hi at h
    change 0 ≤ 2*(t.value.compute m).hi+0
    grind only
  upper n m := by
    have h := ht n 0
    change (t.value.compute n).lo ≤ 1/2 at h
    change 2*(t.value.compute n).lo+0 ≤ 1
    grind only

def secondHalf (t : Point) (ht : (RealRaw.ofRat (1/2)).Le t.value) : Point where
  value := twiceShift t (-1)
  valid := twiceShift_valid t (-1)
  lower n m := by
    have h := ht 0 m
    change 1/2 ≤ (t.value.compute m).hi at h
    change 0 ≤ 2*(t.value.compute m).hi+ -1
    grind only
  upper n m := by
    have h := t.upper n 0
    change (t.value.compute n).lo ≤ 1 at h
    change 2*(t.value.compute n).lo+ -1 ≤ 1
    grind only

theorem leftParameter_on_first (t : Point) (ht : t.value.Le (RealRaw.ofRat (1/2))) :
    leftParameter t ≈ doubled t ht := clip_identity (doubled t ht)

theorem rightParameter_on_first (t : Point) (ht : t.value.Le (RealRaw.ofRat (1/2))) : rightParameter t ≈ zero :=
  clip_zero _ (twiceShift_valid t (-1)) (by
    intro n m
    have h := ht n 0
    change (t.value.compute n).lo ≤ 1/2 at h
    change 2*(t.value.compute n).lo+ -1 ≤ 0
    grind only)

theorem leftParameter_on_second (t : Point) (ht : (RealRaw.ofRat (1/2)).Le t.value) : leftParameter t ≈ one :=
  clip_one _ (twiceShift_valid t 0) (by
    intro n m
    have h := ht 0 m
    change 1/2 ≤ (t.value.compute m).hi at h
    change 1 ≤ 2*(t.value.compute m).hi+0
    grind only)

theorem rightParameter_on_second (t : Point) (ht : (RealRaw.ofRat (1/2)).Le t.value) :
    rightParameter t ≈ secondHalf t ht := clip_identity (secondHalf t ht)

theorem parameter_order_total (s t : Point) : s.value.Le t.value ∨ t.value.Le s.value := by
  classical
  by_cases h : s.value.Le t.value
  · exact Or.inl h
  · right
    intro n m
    by_cases hnm : (t.value.compute n).lo ≤ (s.value.compute m).hi
    · exact hnm
    · exfalso
      apply h
      intro i j
      have hs := (RealRaw.compareAt_overlap_iff s.value s.value i m).1
        (RealRaw.allStagesOverlap_refl s.value s.valid i m)
      have ht := (RealRaw.compareAt_overlap_iff t.value t.value n j).1
        (RealRaw.allStagesOverlap_refl t.value t.valid n j)
      have hs' : (s.value.compute i).lo ≤ (s.value.compute m).hi := hs.1
      have ht' : (t.value.compute n).lo ≤ (t.value.compute j).hi := ht.1
      grind only

theorem leftParameter_zero : leftParameter zero ≈ zero := clip_zero _ (twiceShift_valid zero 0) (by
  intro n m
  change 2*0+0 ≤ 0
  decide +kernel)

theorem rightParameter_zero : rightParameter zero ≈ zero := clip_zero _ (twiceShift_valid zero (-1)) (by
  intro n m
  change 2*0+ -1 ≤ 0
  decide +kernel)

theorem leftParameter_one : leftParameter one ≈ one := clip_one _ (twiceShift_valid one 0) (by
  intro n m
  change 1 ≤ 2*1+0
  decide +kernel)

theorem rightParameter_one : rightParameter one ≈ one := clip_one _ (twiceShift_valid one (-1)) (by
  intro n m
  change 1 ≤ 2*1+ -1
  decide +kernel)

theorem leftParameter_midpoint : leftParameter midpoint ≈ one := leftParameter_on_second midpoint (by
  intro n m
  exact Rat.le_refl)

theorem rightParameter_midpoint : rightParameter midpoint ≈ zero := rightParameter_on_first midpoint (by
  intro n m
  exact Rat.le_refl)

theorem leftParameter_reverse (t : Point) : leftParameter (reverse t) ≈ reverse (rightParameter t) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have ho := RealRaw.interval_order_of_valid t.value t.valid n
  have hm := clamp_mono (show 2*(t.value.compute n).lo+ -1 ≤ 2*(t.value.compute n).hi+ -1 by grind only)
  have helo : 2*(1-(t.value.compute n).hi)+0 = 1-(2*(t.value.compute n).hi+ -1) := by grind only
  have hehi : 2*(1-(t.value.compute n).lo)+0 = 1-(2*(t.value.compute n).lo+ -1) := by grind only
  change clamp (2*(1-(t.value.compute n).hi)+0) ≤ 1-clamp (2*(t.value.compute n).lo+ -1) ∧
    1-clamp (2*(t.value.compute n).hi+ -1) ≤ clamp (2*(1-(t.value.compute n).lo)+0)
  rw [helo,hehi,clamp_complement,clamp_complement]
  grind only

theorem rightParameter_reverse (t : Point) : rightParameter (reverse t) ≈ reverse (leftParameter t) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have ho := RealRaw.interval_order_of_valid t.value t.valid n
  have hm := clamp_mono (show 2*(t.value.compute n).lo+0 ≤ 2*(t.value.compute n).hi+0 by grind only)
  have helo : 2*(1-(t.value.compute n).hi)+ -1 = 1-(2*(t.value.compute n).hi+0) := by grind only
  have hehi : 2*(1-(t.value.compute n).lo)+ -1 = 1-(2*(t.value.compute n).lo+0) := by grind only
  change clamp (2*(1-(t.value.compute n).hi)+ -1) ≤ 1-clamp (2*(t.value.compute n).lo+0) ∧
    1-clamp (2*(t.value.compute n).hi+0) ≤ clamp (2*(1-(t.value.compute n).lo)+ -1)
  rw [helo,hehi,clamp_complement,clamp_complement]
  grind only

end ComputableAnalysis.RiemannHilbert.UnitInterval
