import ComputableAnalysis.Series

/-! # Explicit alternating remainders
Reusable bounds for an arbitrary inclusive prefix and every sufficiently late
interval of a certified alternating computation. -/
namespace ComputableAnalysis.Series.AlternatingRaw

/-- After `n` terms the error is bounded by the first omitted magnitude. -/
theorem interval_remainder (S : AlternatingRaw) (n m : Nat) (hm : n ≤ 2*m) :
    partialSum S.term n - S.term n ≤ (S.interval m).lo ∧
    (S.interval m).hi ≤ partialSum S.term n + S.term n := by
  rw [S.interval_eq_endpoints]
  by_cases heven : n % 2 = 0
  · have hn : n = 2*(n/2) := by omega
    have hlo := S.even_partialSum_mono (n := n/2) (m := m) (by omega)
    have hhi := S.odd_partialSum_antitone (n := n/2) (m := m) (by omega)
    rw [partialSum_even_succ S.term (n/2)] at hhi
    rw [← hn] at hlo hhi
    have ht := S.term_nonneg n
    constructor <;> dsimp <;> grind
  · have hn : n = 2*(n/2)+1 := by omega
    have hlo := S.even_partialSum_mono (n := n/2+1) (m := m) (by omega)
    have hhi := S.odd_partialSum_antitone (n := n/2) (m := m) (by omega)
    rw [show 2*(n/2+1) = n+1 by omega, partialSum] at hlo
    rw [← hn] at hhi
    have hsign : signedTerm S.term n = -S.term n := by
      simp [signedTerm, alternatingSign, heven]
      grind
    rw [hsign] at hlo
    have ht := S.term_nonneg n
    constructor <;> dsimp <;> grind

/-- The limiting raw value lies in the explicit remainder enclosure.
Order uses all pairs of rational approximation stages. -/
theorem remainder (S : AlternatingRaw) (n : Nat) :
    (RealRaw.ofRat (partialSum S.term n - S.term n)).Le S.toRealRaw ∧
    S.toRealRaw.Le (RealRaw.ofRat (partialSum S.term n + S.term n)) := by
  have hv := S.toRealRaw_valid
  constructor
  · intro i j
    have h := S.interval_remainder n (n+j) (by omega)
    have hn := hv.2.1 j (n+j) (by omega)
    have ho := RealRaw.interval_order_of_valid S.toRealRaw hv (n+j)
    change partialSum S.term n - S.term n ≤ (S.interval j).hi
    change (S.interval j).lo ≤ (S.interval (n+j)).lo ∧
      (S.interval (n+j)).lo ≤ (S.interval (n+j)).hi ∧
      (S.interval (n+j)).hi ≤ (S.interval j).hi at hn
    exact Rat.le_trans h.1 (Rat.le_trans ho hn.2.2)
  · intro j i
    have h := S.interval_remainder n (n+j) (by omega)
    have hn := hv.2.1 j (n+j) (by omega)
    have ho := RealRaw.interval_order_of_valid S.toRealRaw hv (n+j)
    change (S.interval j).lo ≤ partialSum S.term n + S.term n
    exact Rat.le_trans hn.1 (Rat.le_trans ho h.2)

end ComputableAnalysis.Series.AlternatingRaw
