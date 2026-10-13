import ComputableAnalysis.Basic

/-! Limits and derivatives of rational-input functions, without an irrational
function evaluation. Limits use arbitrarily small enlargements of target boxes;
admissible input brackets are valid, domain-contained and never degenerate. -/
namespace ComputableAnalysis
namespace RawLimit

/-- Exact membership of a valid represented value in a rational interval. -/
def InInterval (y : RealRaw) (I : QInterval) : Prop :=
  (RealRaw.ofRat I.lo).Le y ∧ y.Le (RealRaw.ofRat I.hi)

/-- A sequence of valid represented values converges to a valid represented
value. The positive allowance handles degenerate and one-sided target names. -/
def TendsTo (u : Nat → RealRaw) (x : RealRaw) : Prop :=
  x.Valid ∧ (∀ n, (u n).Valid) ∧
  ∀ m (eps : QPos), ∃ N, ∀ n, N ≤ n →
    InInterval (u n) (QInterval.expand (x.compute m) eps.val)

/-- Explicit two-index view: `n` selects a represented value and `k` refines
that value. Every row is valid; no diagonal schedule is imposed. -/
def BisequenceTendsTo (Q : Nat → Nat → QInterval) (x : RealRaw) : Prop :=
  TendsTo (fun n => { compute := Q n }) x

set_option maxHeartbeats 1000000

theorem unique {u : Nat → RealRaw} {x y : RealRaw}
    (hx : TendsTo u x) (hy : TendsTo u y) : x.Equiv y := by
  apply RealRaw.allStagesOverlap_equiv
  intro m k
  apply (RealRaw.compareAt_overlap_iff x y m k).2
  have cross : ∀ X Y : RealRaw, TendsTo u X → TendsTo u Y →
      ∀ i j, (X.compute i).lo ≤ (Y.compute j).hi := by
    intro X Y hX hY i j
    by_cases hgood : (X.compute i).lo ≤ (Y.compute j).hi
    · exact hgood
    exfalso
    have hp : 0 < (X.compute i).lo-(Y.compute j).hi := by grind
    let eps : QPos := ⟨((X.compute i).lo-(Y.compute j).hi)/4,
      by rw [Rat.div_def]; exact Rat.mul_pos hp (Rat.inv_pos.mpr (by decide +kernel))⟩
    obtain ⟨N,hN⟩ := hX.2.2 i eps
    obtain ⟨M,hM⟩ := hY.2.2 j eps
    let n := max N M
    have hlo := (hN n (Nat.le_max_left N M)).1
    have hhi := (hM n (Nat.le_max_right N M)).2
    have hc := RealRaw.le_trans (hX.2.1 n) hlo hhi 0 0
    change (X.compute i).lo-eps.val ≤ (Y.compute j).hi+eps.val at hc
    dsimp [eps] at hc
    grind only [Rat.div_def]
  exact ⟨cross x y hx hy m k,cross y x hy hx k m⟩

theorem congr_target {u : Nat → RealRaw} {x y : RealRaw}
    (h : TendsTo u x) (hy : y.Valid) (hxy : x.Equiv y) : TendsTo u y := by
  refine ⟨hy,h.2.1,?_⟩
  intro m eps
  let half : QPos := ⟨eps.val/2,by rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  obtain ⟨k,hk⟩ := h.1.2.2 half
  have hw := hk k (Nat.le_refl k)
  have hov := (RealRaw.compareAt_overlap_iff x y k m).1
    (RealRaw.allStagesOverlap_of_equiv h.1 hy hxy k m)
  unfold QInterval.Overlaps at hov
  obtain ⟨N,hN⟩ := h.2.2 k half
  refine ⟨N,fun n hn => ?_⟩
  have hu := hN n hn
  constructor
  · intro i j
    have hl := hu.1 0 j
    change (x.compute k).lo-half.val ≤ ((u n).compute j).hi at hl
    change (y.compute m).lo-eps.val ≤ ((u n).compute j).hi
    dsimp [half] at hw hl
    grind only [QInterval.width, Rat.div_def]
  · intro i j
    have hh := hu.2 i 0
    change ((u n).compute i).lo ≤ (x.compute k).hi+half.val at hh
    change ((u n).compute i).lo ≤ (y.compute m).hi+eps.val
    dsimp [half] at hw hh
    grind only [QInterval.width, Rat.div_def]

theorem congr_target_iff {u : Nat → RealRaw} {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    TendsTo u x ↔ TendsTo u y :=
  ⟨fun h => congr_target h hy hxy,
   fun h => congr_target h hx (RealRaw.equiv_symm hxy)⟩

theorem bisequence_unique {Q : Nat → Nat → QInterval} {x y : RealRaw}
    (hx : BisequenceTendsTo Q x) (hy : BisequenceTendsTo Q y) : x.Equiv y :=
  unique hx hy

theorem bisequence_congr_target {Q : Nat → Nat → QInterval} {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    BisequenceTendsTo Q x ↔ BisequenceTendsTo Q y :=
  congr_target_iff hx hy hxy

theorem congr_sequence {u v : Nat → RealRaw} {x : RealRaw}
    (h : TendsTo u x) (hv : ∀ n, (v n).Valid)
    (huv : ∀ n, (u n).Equiv (v n)) : TendsTo v x := by
  refine ⟨h.1,hv,?_⟩
  intro m eps
  obtain ⟨N,hN⟩ := h.2.2 m eps
  refine ⟨N,fun n hn => ?_⟩
  have hb := hN n hn
  exact ⟨RealRaw.le_trans (h.2.1 n) hb.1
    (RealRaw.le_of_equiv (h.2.1 n) (hv n) (huv n)),
    RealRaw.le_trans (h.2.1 n)
      (RealRaw.le_of_equiv (hv n) (h.2.1 n) (RealRaw.equiv_symm (huv n))) hb.2⟩

theorem constant (x : RealRaw) (hx : x.Valid) : TendsTo (fun _ => x) x := by
  refine ⟨hx,fun _ => hx,fun m eps => ⟨0,fun _ _ => ?_⟩⟩
  constructor
  · intro i j
    have h := RealRaw.le_refl x hx m j
    change (x.compute m).lo-eps.val ≤ (x.compute j).hi
    have := eps.property
    grind
  · intro i j
    have h := RealRaw.le_refl x hx i m
    change (x.compute i).lo ≤ (x.compute m).hi+eps.val
    have := eps.property
    grind

/-- An independently valid sequence trapped in shrinking boxes of the target
has that limit. It need not use a prescribed convergence rate. -/
theorem of_enclosures {u : Nat → RealRaw} {x : RealRaw}
    (hx : x.Valid) (hu : ∀ n, (u n).Valid)
    (hb : ∀ n, InInterval (u n) (x.compute n)) : TendsTo u x := by
  refine ⟨hx,hu,fun m eps => ⟨m,fun n hn => ?_⟩⟩
  have nest := hx.2.1 m n hn
  have bound := hb n
  constructor
  · intro i j
    have h := bound.1 0 j
    change (x.compute n).lo ≤ ((u n).compute j).hi at h
    change (x.compute m).lo-eps.val ≤ ((u n).compute j).hi
    have := eps.property
    grind
  · intro i j
    have h := bound.2 i 0
    change ((u n).compute i).lo ≤ (x.compute n).hi at h
    change ((u n).compute i).lo ≤ (x.compute m).hi+eps.val
    have := eps.property
    grind

end RawLimit

namespace BracketDerivative

/-- Brackets remain inside the rational domain at EVERY stage and have
strictly positive width at EVERY stage. Non-emptiness is required separately. -/
def Admissible (domain : Rat → Prop) (x A : RealRaw) : Prop :=
  x.Valid ∧ A.Valid ∧ A.Equiv x ∧
  ∀ n, (A.compute n).lo < (A.compute n).hi ∧
    ∀ r, (A.compute n).lo ≤ r → r ≤ (A.compute n).hi → domain r

/-- The two rational endpoint evaluations are the only evaluations used. -/
def secant (f : Rat → RealRaw) (a b : Rat) : RealRaw :=
  RealRaw.scaleRat (1/(b-a)) (f b-f a)

def secants (f : Rat → RealRaw) (A : RealRaw) : Nat → RealRaw :=
  fun n => secant f (A.compute n).lo (A.compute n).hi

theorem secant_valid {f : Rat → RealRaw} {a b : Rat}
    (ha : (f a).Valid) (hb : (f b).Valid) : (secant f a b).Valid :=
  RealRaw.scaleRat_valid (RealRaw.sub_valid hb ha)

theorem secants_valid {domain : Rat → Prop} {f : Rat → RealRaw} {x A : RealRaw}
    (hf : ∀ r, domain r → (f r).Valid) (hA : Admissible domain x A) :
    ∀ n, (secants f A n).Valid := by
  intro n
  have h := hA.2.2.2 n
  exact secant_valid (hf _ (h.2 _ (Rat.le_refl) (Rat.le_of_lt h.1)))
    (hf _ (h.2 _ (Rat.le_of_lt h.1) (Rat.le_refl)))

/-- A derivative is a common limit of all admissible secants, with no
irrational evaluation of the primary function and no prescribed algorithm. -/
def HasDerivativeAt (domain : Rat → Prop) (f : Rat → RealRaw) (x d : RealRaw) : Prop :=
  x.Valid ∧ d.Valid ∧ (∀ r, domain r → (f r).Valid) ∧
  (∃ A, Admissible domain x A) ∧
  ∀ A, Admissible domain x A → RawLimit.TendsTo (secants f A) d

theorem admissible_congr {domain : Rat → Prop} {x y A : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    Admissible domain x A ↔ Admissible domain y A := by
  constructor
  · intro h
    exact ⟨hy,h.2.1,RealRaw.equiv_trans h.2.1 hx hy h.2.2.1 hxy,h.2.2.2⟩
  · intro h
    exact ⟨hx,h.2.1,RealRaw.equiv_trans h.2.1 hy hx h.2.2.1
      (RealRaw.equiv_symm hxy),h.2.2.2⟩

theorem unique {domain : Rat → Prop} {f : Rat → RealRaw} {x d e : RealRaw}
    (hd : HasDerivativeAt domain f x d) (he : HasDerivativeAt domain f x e) : d.Equiv e := by
  obtain ⟨A,hA⟩ := hd.2.2.2.1
  exact RawLimit.unique (hd.2.2.2.2 A hA) (he.2.2.2.2 A hA)

theorem congr_point {domain : Rat → Prop} {f : Rat → RealRaw} {x y d : RealRaw}
    (h : HasDerivativeAt domain f x d) (hy : y.Valid) (hxy : x.Equiv y) :
    HasDerivativeAt domain f y d := by
  refine ⟨hy,h.2.1,h.2.2.1,?_,?_⟩
  · obtain ⟨A,hA⟩ := h.2.2.2.1
    exact ⟨A,(admissible_congr h.1 hy hxy).1 hA⟩
  · intro A hA
    exact h.2.2.2.2 A ((admissible_congr h.1 hy hxy).2 hA)

theorem congr_value {domain : Rat → Prop} {f : Rat → RealRaw} {x d e : RealRaw}
    (h : HasDerivativeAt domain f x d) (he : e.Valid) (hde : d.Equiv e) :
    HasDerivativeAt domain f x e := by
  exact ⟨h.1,he,h.2.2.1,h.2.2.2.1,fun A hA =>
    RawLimit.congr_target (h.2.2.2.2 A hA) he hde⟩

theorem congr_point_iff {domain : Rat → Prop} {f : Rat → RealRaw} {x y d : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    HasDerivativeAt domain f x d ↔ HasDerivativeAt domain f y d :=
  ⟨fun h => congr_point h hy hxy,
   fun h => congr_point h hx (RealRaw.equiv_symm hxy)⟩

theorem congr_value_iff {domain : Rat → Prop} {f : Rat → RealRaw} {x d e : RealRaw}
    (hd : d.Valid) (he : e.Valid) (hde : d.Equiv e) :
    HasDerivativeAt domain f x d ↔ HasDerivativeAt domain f x e :=
  ⟨fun h => congr_value h he hde,
   fun h => congr_value h hd (RealRaw.equiv_symm hde)⟩

theorem congr_function {domain : Rat → Prop} {f g : Rat → RealRaw} {x d : RealRaw}
    (h : HasDerivativeAt domain f x d)
    (hg : ∀ r, domain r → (g r).Valid)
    (hfg : ∀ r, domain r → (f r).Equiv (g r)) :
    HasDerivativeAt domain g x d := by
  refine ⟨h.1,h.2.1,hg,h.2.2.2.1,?_⟩
  intro A hA
  apply RawLimit.congr_sequence (h.2.2.2.2 A hA) (secants_valid hg hA)
  intro n
  have ha := hA.2.2.2 n
  have hlo := ha.2 _ (Rat.le_refl) (Rat.le_of_lt ha.1)
  have hhi := ha.2 _ (Rat.le_of_lt ha.1) (Rat.le_refl)
  exact RealRaw.scaleRat_equiv
    (RealRaw.sub_equiv (h.2.2.1 _ hhi) (hg _ hhi)
      (h.2.2.1 _ hlo) (hg _ hlo) (hfg _ hhi) (hfg _ hlo))

end BracketDerivative
end ComputableAnalysis
