import ComputableAnalysis.Calculus
import ComputableAnalysis.ComplexMultiplication

/-! Finite rational selections from nested boxes. These lemmas eliminate
arbitrary rational slack; they do not introduce scalar real values. -/
namespace ComputableAnalysis
namespace IntervalSelections

def InBox (q : Rat) (I : QInterval) : Prop := I.lo <= q ∧ q <= I.hi

theorem contains_later {X : RealRaw} (hX : X.Valid) {n m : Nat}
    (hnm : n <= m) {x : Rat} (hx : InBox x (X.compute m)) :
    InBox x (X.compute n) := by
  have hh := hX.2.1 n m hnm
  exact ⟨Rat.le_trans hh.1 hx.1, Rat.le_trans hx.2 hh.2.2⟩

/-- A rational point, with its stage explicit, is not an unspecified value of
an interval or an element of an assumed completed real line. -/
theorem endpoint_le_of_eventually {X Y : RealRaw}
    (hX : X.Valid) (hY : Y.Valid) (x y : Nat -> Rat)
    (hx : ∀ n, InBox (x n) (X.compute n))
    (hy : ∀ n, InBox (y n) (Y.compute n)) (c : Rat)
    (h : ∀ eps : QPos, ∃ N, ∀ n, N <= n -> x n <= y n+c+eps.val) :
    ∀ n m, (X.compute n).lo <= (Y.compute m).hi+c := by
  intro i j
  by_cases hh : (X.compute i).lo <= (Y.compute j).hi+c
  · exact hh
  · apply False.elim
    let eps : QPos := ⟨((X.compute i).lo-((Y.compute j).hi+c))/2, by
      rw [Rat.div_def]
      exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 (by decide))⟩
    obtain ⟨N, hN⟩ := h eps
    let n := max N (max i j)
    have hi := contains_later hX (n := i) (m := n) (by dsimp [n]; omega) (hx n)
    have hj := contains_later hY (n := j) (m := n) (by dsimp [n]; omega) (hy n)
    have hn := hN n (by dsimp [n]; omega)
    dsimp [eps] at hn
    simp only [Rat.div_def] at hn
    unfold InBox at hi hj
    grind

theorem le_of_eventually {X Y : RealRaw}
    (hX : X.Valid) (hY : Y.Valid) (x y : Nat -> Rat)
    (hx : ∀ n, InBox (x n) (X.compute n))
    (hy : ∀ n, InBox (y n) (Y.compute n))
    (h : ∀ eps : QPos, ∃ N, ∀ n, N <= n -> x n <= y n+eps.val) :
    X.Le Y := by
  have hh := endpoint_le_of_eventually hX hY x y hx hy 0
    (by simpa only [Rat.add_zero] using h)
  simpa only [Rat.add_zero, RealRaw.Le] using hh

theorem sub_mem {I J : QInterval} {x y : Rat}
    (hx : InBox x I) (hy : InBox y J) :
    InBox (x-y) (QInterval.subInterval I J) := by
  unfold InBox QInterval.subInterval at *
  constructor <;> grind

theorem scale_mem {I : QInterval} {x r : Rat}
    (hx : InBox x I) (hr : 0 <= r) :
    InBox (r*x) (QInterval.scaleByRat r I) := by
  unfold InBox QInterval.scaleByRat
  rw [if_pos hr]
  exact ⟨Rat.mul_le_mul_of_nonneg_left hx.1 hr,
    Rat.mul_le_mul_of_nonneg_left hx.2 hr⟩

theorem mul_mem {X Y : RealRaw} {x y : Rat} {n : Nat}
    (hx : InBox x (X.compute n)) (hy : InBox y (Y.compute n)) :
    InBox (x*y) ((RealRaw.mul X Y).compute n) :=
  QBox.mulRealInterval_contains hx.1 hx.2 hy.1 hy.2

theorem secant_mem {F : RealFunRaw} {x y fx fy : Rat} (hxy : x < y) (n : Nat)
    (hx : InBox fx (F.compute x n)) (hy : InBox fy (F.compute y n)) :
    InBox ((fy-fx)/(y-x)) (secantSlopeIntervalOfRealFun F x y n) := by
  have hp : 0 < y-x := by grind
  have hi : 0 <= 1/(y-x) := by
    simp only [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 hp)
  have hh := scale_mem (sub_mem hy hx) hi
  change InBox ((fy-fx)/(y-x))
    (QInterval.scaleByRat (1/(y-x)) (QInterval.subInterval (F.compute y n) (F.compute x n)))
  have he : (fy-fx)/(y-x) = (1/(y-x))*(fy-fx) := by
    simp only [Rat.div_def, Rat.one_mul]
    exact Rat.mul_comm _ _
  rw [he]
  exact hh

/-- A late finite estimate with arbitrarily small rational slack yields
all-stage overlap of a widened computation with its independent anchor. -/
theorem expanded_overlaps_of_selected_error {X Y : RealRaw}
    (hX : X.Valid) (hY : Y.Valid) (x y : Nat -> Rat)
    (hx : ∀ n, InBox (x n) (X.compute n))
    (hy : ∀ n, InBox (y n) (Y.compute n)) (r : Rat)
    (h : ∀ eps : QPos, ∃ N, ∀ n, N <= n -> qabs (y n-x n) <= r+eps.val) :
    ∀ q t, (QInterval.expand (X.compute q) r).Overlaps (Y.compute t) := by
  have hl := endpoint_le_of_eventually hX hY x y hx hy r (by
    intro eps
    obtain ⟨N, hN⟩ := h eps
    refine ⟨N, ?_⟩
    intro n hn
    have hh := hN n hn
    have hneg := neg_qabs_le_self (y n-x n)
    grind)
  have hr := endpoint_le_of_eventually hY hX y x hy hx r (by
    intro eps
    obtain ⟨N, hN⟩ := h eps
    refine ⟨N, ?_⟩
    intro n hn
    have hh := hN n hn
    have hpos := self_le_qabs (y n-x n)
    grind)
  intro q t
  have h1 := hl q t
  have h2 := hr t q
  unfold QInterval.expand QInterval.Overlaps
  constructor <;> grind

end IntervalSelections
end ComputableAnalysis
