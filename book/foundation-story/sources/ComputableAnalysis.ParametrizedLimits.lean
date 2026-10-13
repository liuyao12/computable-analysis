import ComputableAnalysis.PowerSeries

/-! Parametrized, covered rational enclosures and their exact limit laws. -/
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
that value. Every row is valid; the covered-diagonal compatibility theorem is below. -/
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

def allowance (n : Nat) : Rat := ((1:Rat)/2)^n

theorem allowance_pos (n : Nat) : 0 < allowance n :=
  Rat.pow_pos (by decide +kernel)

theorem allowance_antitone {n m : Nat} (h : n≤m) : allowance m≤allowance n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact Rat.le_refl
  | succ k ih =>
    change ((1:Rat)/2)^(n+k+1) ≤ ((1:Rat)/2)^n
    rw [Rat.pow_succ]
    have hn : 0≤((1:Rat)/2)^(n+k) := Rat.pow_nonneg (by decide +kernel)
    have hm := Rat.mul_le_mul_of_nonneg_left (by decide +kernel : (1:Rat)/2≤1) hn
    exact Rat.le_trans (by simpa only [Rat.mul_one, allowance] using hm) (ih (by omega))

theorem allowance_shrinks (eps : QPos) : ∃ N, ∀ n, N≤n → allowance n≤eps.val := by
  refine ⟨RationalMajorant.halfDecayShift 1 eps,fun n hn => ?_⟩
  have h := RationalMajorant.halfDecayShift_spec_of_le (by decide +kernel : (0:Rat)≤1) eps hn
  simpa only [Rat.one_mul,allowance] using h

def enlarged (x : RealRaw) : RealRaw where
  compute n := QInterval.expand (x.compute n) (allowance n)

theorem enlarged_valid {x : RealRaw} (hx : x.Valid) : (enlarged x).Valid := by
  refine ⟨?_,?_,?_⟩
  · intro n
    have ho := hx.1 n
    have hp := allowance_pos n
    change 0≤(x.compute n).hi+allowance n-((x.compute n).lo-allowance n)
    grind only [QInterval.width]
  · intro n m hnm
    have hn := hx.2.1 n m hnm
    have hd := allowance_antitone hnm
    have hp := allowance_pos m
    change (x.compute n).lo-allowance n≤(x.compute m).lo-allowance m ∧
      (x.compute m).lo-allowance m≤(x.compute m).hi+allowance m ∧
      (x.compute m).hi+allowance m≤(x.compute n).hi+allowance n
    constructor
    · grind only
    constructor <;> grind only
  · intro eps
    let e : QPos := ⟨eps.val/4,by rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
    obtain ⟨N,hN⟩ := hx.2.2 e
    obtain ⟨M,hM⟩ := allowance_shrinks e
    refine ⟨max N M,fun n hn => ?_⟩
    have h1 := hN n (Nat.le_trans (Nat.le_max_left N M) hn)
    have h2 := hM n (Nat.le_trans (Nat.le_max_right N M) hn)
    change (x.compute n).hi+allowance n-((x.compute n).lo-allowance n)≤eps.val
    dsimp [e] at h1 h2
    have := eps.property
    grind only [QInterval.width,Rat.div_def]

theorem enlarged_equiv {x : RealRaw} (hx : x.Valid) : (enlarged x).Equiv x := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have h := hx.1 n
  have hp := allowance_pos n
  change (x.compute n).lo-allowance n≤(x.compute n).hi ∧
    (x.compute n).lo≤(x.compute n).hi+allowance n
  constructor <;> grind only [QInterval.width]


/-- Both refinement indices eventually pass every finite stage. Monotonicity
is optional: validity is required of the selected output intervals themselves. -/
def Cofinal (s : Nat → Nat) : Prop :=
  ∀ N, ∃ K, ∀ k, K ≤ k → N ≤ s k

def diagonal (Q : Nat → Nat → QInterval) (n m : Nat → Nat) : RealRaw where
  compute k := Q (n k) (m k)

/-- A selected valid diagonal must cover every observation at the selected
input resolution. `tests` describes whole neighborhoods or complete tails,
never just the one sample selected by the parametrization. -/
def HasEnclosureValue (tests : Nat → RealRaw → Prop) (c : RealRaw) : Prop :=
  c.Valid ∧ ∃ Q n m, Cofinal n ∧ Cofinal m ∧
    (diagonal Q n m).Valid ∧ (diagonal Q n m).Equiv c ∧
    ∀ k y, tests (n k) y → InInterval y ((diagonal Q n m).compute k)

theorem cofinal_id : Cofinal (fun k => k) := fun N => ⟨N, fun _ h => h⟩

theorem cofinal_of_ge (s : Nat → Nat) (h : ∀ k, k ≤ s k) : Cofinal s :=
  fun N => ⟨N, fun k hk => Nat.le_trans hk (h k)⟩

theorem inInterval_congr {y z : RealRaw} {I : QInterval}
    (hy : y.Valid) (hz : z.Valid) (h : y.Equiv z) (hb : InInterval y I) :
    InInterval z I :=
  ⟨RealRaw.le_trans hy hb.1 (RealRaw.le_of_equiv hy hz h),
   RealRaw.le_trans hy (RealRaw.le_of_equiv hz hy (RealRaw.equiv_symm h)) hb.2⟩

/-- Uniqueness compares two arbitrary covered diagonals using a common
observation at a finer input resolution. It constructs no canonical value. -/
theorem HasEnclosureValue.unique {tests : Nat → RealRaw → Prop} {c d : RealRaw}
    (antitone : ∀ i j, i ≤ j → ∀ y, tests j y → tests i y)
    (inhabited : ∀ i, ∃ y, y.Valid ∧ tests i y)
    (hc : HasEnclosureValue tests c) (hd : HasEnclosureValue tests d) : c.Equiv d := by
  obtain ⟨vc,Q,n,m,_,_,vC,eC,bC⟩ := hc
  obtain ⟨vd,R,p,q,_,_,vD,eD,bD⟩ := hd
  have eq : (diagonal Q n m).Equiv (diagonal R p q) := by
    intro k
    obtain ⟨y,vy,hy⟩ := inhabited (max (n k) (p k))
    have a := bC k y (antitone _ _ (Nat.le_max_left _ _) y hy)
    have b := bD k y (antitone _ _ (Nat.le_max_right _ _) y hy)
    apply (RealRaw.compareAt_overlap_iff _ _ k k).2
    exact ⟨RealRaw.le_trans vy a.1 b.2 0 0,
      RealRaw.le_trans vy b.1 a.2 0 0⟩
  exact RealRaw.equiv_trans vc vC vd (RealRaw.equiv_symm eC)
    (RealRaw.equiv_trans vC vD vd eq eD)

theorem HasEnclosureValue.congr_value {tests : Nat → RealRaw → Prop} {c d : RealRaw}
    (h : HasEnclosureValue tests c) (hd : d.Valid) (hcd : c.Equiv d) :
    HasEnclosureValue tests d := by
  obtain ⟨hc,Q,n,m,hn,hm,hC,hCc,hcover⟩ := h
  exact ⟨hd,Q,n,m,hn,hm,hC,RealRaw.equiv_trans hC hc hd hCc hcd,hcover⟩

/-- A sequence limit has a covered diagonal for the entire remaining tail. -/
def HasParametrizedLimit (u : Nat → RealRaw) (c : RealRaw) : Prop :=
  (∀ j, (u j).Valid) ∧ HasEnclosureValue (fun n y => ∃ j, n ≤ j ∧ y = u j) c

theorem parametrizedLimit_iff {u : Nat → RealRaw} {c : RealRaw} :
    HasParametrizedLimit u c ↔ TendsTo u c := by
  constructor
  · rintro ⟨hu,hc,Q,n,m,hn,hm,hC,hCc,cover⟩
    have h : TendsTo u (diagonal Q n m) := by
      refine ⟨hC,hu,fun k eps => ⟨n k,fun j hj => ?_⟩⟩
      have b := cover k (u j) ⟨j,hj,rfl⟩
      constructor
      · intro i t
        have h := b.1 i t
        have := eps.property
        change (Q (n k) (m k)).lo-eps.val ≤ ((u j).compute t).hi
        change (Q (n k) (m k)).lo ≤ ((u j).compute t).hi at h
        grind only
      · intro i t
        have h := b.2 i t
        have := eps.property
        change ((u j).compute i).lo ≤ (Q (n k) (m k)).hi+eps.val
        change ((u j).compute i).lo ≤ (Q (n k) (m k)).hi at h
        grind only
    exact congr_target h hc hCc
  · intro h
    classical
    let threshold : Nat → Nat := fun k =>
      Classical.choose (h.2.2 k ⟨allowance k,allowance_pos k⟩)
    let n : Nat → Nat := fun k => max k (threshold k)
    refine ⟨h.2.1,h.1,(fun _ k => (enlarged c).compute k),n,(fun k => k),
      cofinal_of_ge n (fun k => Nat.le_max_left _ _),cofinal_id,
      enlarged_valid h.1,enlarged_equiv h.1,?_⟩
    intro k y hy
    obtain ⟨j,hj,rfl⟩ := hy
    exact Classical.choose_spec (h.2.2 k ⟨allowance k,allowance_pos k⟩) j
      (Nat.le_trans (Nat.le_max_right _ _) hj)

theorem HasParametrizedLimit.unique {u : Nat → RealRaw} {c d : RealRaw}
    (hc : HasParametrizedLimit u c) (hd : HasParametrizedLimit u d) : c.Equiv d :=
  RawLimit.unique (parametrizedLimit_iff.mp hc) (parametrizedLimit_iff.mp hd)

/-- Regression against a diagonal that skips every unfavorable sample.
The alternating sequence has valid constant subsequences, but no covered
parametrized limit, for any valid represented target. -/
theorem alternating_no_parametrizedLimit (c : RealRaw) :
    ¬ HasParametrizedLimit (fun j => RealRaw.ofRat (if j % 2 = 0 then 0 else 1)) c := by
  rintro ⟨hu,hc,Q,n,m,hn,hm,hC,hCc,cover⟩
  obtain ⟨K,hK⟩ := hC.2.2 ⟨1/2,by decide +kernel⟩
  have hw := hK K (Nat.le_refl _)
  have he : (2*n K) % 2 = 0 := by omega
  have ho : (2*n K+1) % 2 ≠ 0 := by omega
  have b0 := cover K _ ⟨2*n K,by omega,rfl⟩
  have b1 := cover K _ ⟨2*n K+1,by omega,rfl⟩
  simp only [he,ho,if_pos] at b0 b1
  have lo := b0.1 0 0
  have hi := b1.2 0 0
  change (Q (n K) (m K)).lo ≤ 0 at lo
  change 1 ≤ (Q (n K) (m K)).hi at hi
  change (Q (n K) (m K)).hi-(Q (n K) (m K)).lo ≤ 1/2 at hw
  grind only [Rat.div_def]

theorem inInterval_of_contains_compute {y : RealRaw} {I : QInterval}
    (hy : y.Valid) (k : Nat) (h : I.ContainsInterval (y.compute k)) : InInterval y I := by
  constructor
  · intro i j
    have b := RealRaw.le_refl y hy k j
    change I.lo ≤ (y.compute j).hi
    exact Rat.le_trans h.1 b
  · intro i j
    have b := RealRaw.le_refl y hy i k
    change (y.compute i).lo ≤ I.hi
    exact Rat.le_trans b h.2

theorem inInterval_of_sub_bound {y c : RealRaw} (hy : y.Valid) (hc : c.Valid)
    (eps : Rat) (lower : (RealRaw.ofRat (-eps)).Le (RealRaw.sub y c))
    (upper : (RealRaw.sub y c).Le (RealRaw.ofRat eps)) (k : Nat) :
    InInterval y (QInterval.expand (c.compute k) eps) := by
  have cancel := RealRaw.sub_add_cancel_equiv hy hc
  have vz := RealRaw.add_valid (RealRaw.sub_valid hy hc) hc
  have lo := RealRaw.le_add_le_add lower (RealRaw.le_refl c hc)
  have hi := RealRaw.le_add_le_add upper (RealRaw.le_refl c hc)
  have lo' := RealRaw.le_trans vz lo (RealRaw.le_of_equiv vz hy cancel)
  have hi' := RealRaw.le_trans vz (RealRaw.le_of_equiv hy vz (RealRaw.equiv_symm cancel)) hi
  constructor
  · intro i j
    have h := lo' k j
    change (c.compute k).lo-eps ≤ (y.compute j).hi
    change -eps+(c.compute k).lo ≤ (y.compute j).hi at h
    grind only
  · intro i j
    have h := hi' i k
    change (y.compute i).lo ≤ (c.compute k).hi+eps
    change (y.compute i).lo ≤ eps+(c.compute k).hi at h
    grind only

theorem inInterval_intersection {y : RealRaw} {I J : QInterval}
    (hI : InInterval y I) (hJ : InInterval y J) :
    InInterval y (QInterval.intersection I J) := by
  constructor
  · intro i j
    have a := hI.1 i j
    have b := hJ.1 i j
    change max I.lo J.lo ≤ (y.compute j).hi
    change I.lo ≤ (y.compute j).hi at a
    change J.lo ≤ (y.compute j).hi at b
    grind
  · intro i j
    have a := hI.2 i j
    have b := hJ.2 i j
    change (y.compute i).lo ≤ min I.hi J.hi
    change (y.compute i).lo ≤ I.hi at a
    change (y.compute i).lo ≤ J.hi at b
    grind

/-- Finite intersections enforce output nesting without assuming an anchor
value or a pre-existing extension at an irrational input. -/
def prefixCompute (B : Nat → QInterval) : Nat → QInterval
  | 0 => B 0
  | k+1 => QInterval.intersection (prefixCompute B k) (B (k+1))

def prefixRaw (B : Nat → QInterval) : RealRaw where
  compute := prefixCompute B

def runningMax (s : Nat → Nat) : Nat → Nat
  | 0 => s 0
  | k+1 => max (runningMax s k) (s (k+1))

theorem runningMax_ge (s : Nat → Nat) (k : Nat) : s k ≤ runningMax s k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => exact Nat.le_max_right _ _

theorem prefix_cover {tests : Nat → RealRaw → Prop} {s : Nat → Nat} {B : Nat → QInterval}
    (anti : ∀ i j, i ≤ j → ∀ y, tests j y → tests i y)
    (cover : ∀ k y, tests (s k) y → InInterval y (B k)) :
    ∀ k y, tests (runningMax s k) y → InInterval y ((prefixRaw B).compute k) := by
  intro k
  induction k with
  | zero => exact cover 0
  | succ k ih =>
    intro y hy
    exact inInterval_intersection
      (ih y (anti _ _ (Nat.le_max_left _ _) y hy))
      (cover (k+1) y (anti _ _ (Nat.le_max_right _ _) y hy))

theorem prefix_current (B : Nat → QInterval) (k : Nat) :
    (B k).ContainsInterval ((prefixRaw B).compute k) := by
  cases k with
  | zero => exact ⟨Rat.le_refl,Rat.le_refl⟩
  | succ k => exact QInterval.intersection_contained_right _ _

theorem prefix_valid {tests : Nat → RealRaw → Prop} {s : Nat → Nat} {B : Nat → QInterval}
    (anti : ∀ i j, i ≤ j → ∀ y, tests j y → tests i y)
    (inhabited : ∀ i, ∃ y, y.Valid ∧ tests i y)
    (cover : ∀ k y, tests (s k) y → InInterval y (B k))
    (shrinks : RealRaw.WidthsShrinkToZero B) : (prefixRaw B).Valid := by
  have ordered : ∀ k, ((prefixRaw B).compute k).lo ≤ ((prefixRaw B).compute k).hi := by
    intro k
    obtain ⟨y,vy,hy⟩ := inhabited (runningMax s k)
    have h := prefix_cover anti cover k y hy
    exact RealRaw.le_trans vy h.1 h.2 0 0
  refine ⟨fun k => ?_,?_,?_⟩
  · have h := ordered k
    change 0 ≤ ((prefixRaw B).compute k).hi-((prefixRaw B).compute k).lo
    grind only
  · intro k l hkl
    induction hkl with
    | refl => exact ⟨Rat.le_refl,ordered k,Rat.le_refl⟩
    | @step l hkl ih =>
      have h := QInterval.intersection_contained_left (prefixCompute B l) (B (l+1))
      exact ⟨Rat.le_trans ih.1 h.1,ordered _,Rat.le_trans h.2 ih.2.2⟩
  · intro eps
    obtain ⟨N,hN⟩ := shrinks eps
    exact ⟨N,fun k hk => Rat.le_trans (QInterval.width_le_of_contains (prefix_current B k)) (hN k hk)⟩

/-- This constructor performs only finite rational intersections. The
inhabited shrinking observations prove validity, rather than assuming it. -/
theorem prefix_hasEnclosureValue {tests : Nat → RealRaw → Prop} {s : Nat → Nat}
    {B : Nat → QInterval}
    (anti : ∀ i j, i ≤ j → ∀ y, tests j y → tests i y)
    (inhabited : ∀ i, ∃ y, y.Valid ∧ tests i y)
    (hs : ∀ k, k ≤ s k)
    (cover : ∀ k y, tests (s k) y → InInterval y (B k))
    (shrinks : RealRaw.WidthsShrinkToZero B) :
    HasEnclosureValue tests (prefixRaw B) := by
  have hv := prefix_valid anti inhabited cover shrinks
  exact ⟨hv,(fun _ m => (prefixRaw B).compute m),runningMax s,(fun k => k),
    cofinal_of_ge _ (fun k => Nat.le_trans (hs k) (runningMax_ge s k)),cofinal_id,
    hv,RealRaw.equiv_refl _ hv,prefix_cover anti cover⟩

/-- Neighborhood convergence is a useful compatibility presentation of the
covered-diagonal definition, without any requested precision schedule. -/
def NeighborhoodTendsTo (tests : Nat → RealRaw → Prop) (c : RealRaw) : Prop :=
  c.Valid ∧ ∀ k (eps : QPos), ∃ N, ∀ y, tests N y →
    InInterval y (QInterval.expand (c.compute k) eps.val)

theorem enclosureValue_iff {tests : Nat → RealRaw → Prop} {c : RealRaw}
    (anti : ∀ i j, i ≤ j → ∀ y, tests j y → tests i y) :
    HasEnclosureValue tests c ↔ NeighborhoodTendsTo tests c := by
  constructor
  · rintro ⟨hc,Q,n,m,hn,hm,hC,hCc,cover⟩
    refine ⟨hc,fun k eps => ?_⟩
    obtain ⟨i,hi⟩ := hC.2.2 eps
    have width := hi i (Nat.le_refl _)
    have ov := (RealRaw.compareAt_overlap_iff _ _ i k).mp
      (RealRaw.allStagesOverlap_of_equiv hC hc hCc i k)
    refine ⟨n i,fun y hy => ?_⟩
    have b := cover i y hy
    constructor
    · intro a t
      have h := b.1 a t
      change (c.compute k).lo-eps.val ≤ (y.compute t).hi
      change (Q (n i) (m i)).lo ≤ (y.compute t).hi at h
      change (Q (n i) (m i)).hi-(Q (n i) (m i)).lo ≤ eps.val at width
      unfold QInterval.Overlaps at ov
      change (Q (n i) (m i)).lo ≤ (c.compute k).hi ∧
        (c.compute k).lo ≤ (Q (n i) (m i)).hi at ov
      grind only
    · intro a t
      have h := b.2 a t
      change (y.compute a).lo ≤ (c.compute k).hi+eps.val
      change (y.compute a).lo ≤ (Q (n i) (m i)).hi at h
      change (Q (n i) (m i)).hi-(Q (n i) (m i)).lo ≤ eps.val at width
      unfold QInterval.Overlaps at ov
      change (Q (n i) (m i)).lo ≤ (c.compute k).hi ∧
        (c.compute k).lo ≤ (Q (n i) (m i)).hi at ov
      grind only
  · intro h
    classical
    let s := fun k => Classical.choose (h.2 k ⟨allowance k,allowance_pos k⟩)
    let n := fun k => max k (s k)
    refine ⟨h.1,(fun _ m => (enlarged c).compute m),n,(fun k => k),
      cofinal_of_ge n (fun k => Nat.le_max_left _ _),cofinal_id,
      enlarged_valid h.1,enlarged_equiv h.1,?_⟩
    intro k y hy
    exact Classical.choose_spec (h.2 k ⟨allowance k,allowance_pos k⟩) y
      (anti _ _ (Nat.le_max_right _ _) y hy)

end RawLimit
end ComputableAnalysis
