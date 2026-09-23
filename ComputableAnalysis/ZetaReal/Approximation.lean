import ComputableAnalysis.ZetaReal.Schedule

namespace ComputableAnalysis.ZetaReal
open FormalPowerSeries

/-- A rational polynomial approximation with two independently certified cutoffs. -/
def approx (q m : Nat) (hq : 0 < q) (s : Rat) (n : Nat) : Rat :=
  let K := outerCutoff q m hq n
  rectangle s K (innerCutoff m K n)

/-- Comparison with any larger rectangle, not an assumed infinite sum. -/
theorem approx_rectangle {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s)
    (n K N : Nat) (hK : outerCutoff q m hq n ≤ K)
    (hN : innerCutoff m (outerCutoff q m hq n) n ≤ N) :
    qabs (rectangle s K N-approx q m hq s n) ≤ 2*(budget n).val := by
  let k := outerCutoff q m hq n
  let nn := innerCutoff m k n
  have ho := rectangle_outer_tail hs (outerCutoff_ge q m hq n) (K-k) N
  have hi := rectangle_inner_tail hs (innerCutoff_pos m k n) k (N-nn)
  have hb := outerBudget_covers hq hs (outerCutoff_ge q m hq n)
  have hc := outerCutoff_budget q m hq n
  have hd := innerCutoff_budget m k n
  have hek : k+(K-k)=K := Nat.add_sub_of_le hK
  have hen : nn+(N-nn)=N := Nat.add_sub_of_le hN
  change qabs (rectangle s (k+(K-k)) N-rectangle s k N) ≤ _ at ho
  rw [hek] at ho
  change qabs (rectangle s k (nn+(N-nn))-rectangle s k nn) ≤ _ at hi
  rw [hen] at hi
  have htriangle := qabs_add_le (rectangle s K N-rectangle s k N)
    (rectangle s k N-rectangle s k nn)
  have he : rectangle s K N-approx q m hq s n =
      (rectangle s K N-rectangle s k N)+(rectangle s k N-rectangle s k nn) := by
    change rectangle s K N-rectangle s k nn = _
    grind only
  rw [he]
  grind only

/-- Finite Cauchy estimate; the two schedules need not be synchronized. -/
theorem approx_cauchy {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s)
    (i j : Nat) : qabs (approx q m hq s i-approx q m hq s j) ≤
      2*(budget i).val+2*(budget j).val := by
  let K := max (outerCutoff q m hq i) (outerCutoff q m hq j)
  let N := max (innerCutoff m (outerCutoff q m hq i) i) (innerCutoff m (outerCutoff q m hq j) j)
  have hi := approx_rectangle hq hs i K N (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hj := approx_rectangle hq hs j K N (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have h := qabs_sub_le (rectangle s K N-approx q m hq s j) (rectangle s K N-approx q m hq s i)
  have he : approx q m hq s i-approx q m hq s j =
      (rectangle s K N-approx q m hq s j)-(rectangle s K N-approx q m hq s i) := by grind only
  rw [he]
  grind only

def candidate (q m : Nat) (hq : 0 < q) (s : Rat) : RealRaw where
  compute n := let a := approx q m hq s n; ⟨a,a⟩

def raw (q m : Nat) (hq : 0 < q) (s : Rat) : RealRaw :=
  RealRaw.prefixStabilize (candidate q m hq s) (fun n => 4*(budget n).val)

theorem candidate_future {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s)
    (i j : Nat) (hij : i ≤ j) :
    (QInterval.expand ((candidate q m hq s).compute i) (4*(budget i).val)).ContainsInterval
      ((candidate q m hq s).compute j) := by
  have h := approx_cauchy hq hs i j
  have ha := budget_antitone hij
  have hlo := neg_qabs_le_self (approx q m hq s i-approx q m hq s j)
  have hhi := self_le_qabs (approx q m hq s i-approx q m hq s j)
  constructor <;> change _ ≤ _ <;> dsimp [candidate, QInterval.expand] <;> grind only

theorem radius_shrinks : ShrinksToZero (fun n => 4*(budget n).val) := by
  apply shrinksToZero_of_natOverSuccBound (C := 1)
  intro n
  have h := (budget n).property
  have hi := Rat.mul_inv_cancel (32*((n : Rat)+1)) (by have := Rat.natCast_nonneg (a := n); grind)
  have hj := Rat.mul_inv_cancel ((n : Rat)+1) (by have := Rat.natCast_nonneg (a := n); grind)
  simp only [Rat.natCast_add]
  dsimp [budget] at *
  rw [Rat.div_def, Rat.one_mul] at *
  apply Rat.le_of_mul_le_mul_right (c := 32*((n : Rat)+1)) ?_ (by have := Rat.natCast_nonneg (a := n); grind)
  have he : 4*(32*((n : Rat)+1))⁻¹*(32*((n : Rat)+1)) = 4 := by
    calc
      4*(32*((n : Rat)+1))⁻¹*(32*((n : Rat)+1)) =
          4*((32*((n : Rat)+1))*(32*((n : Rat)+1))⁻¹) := by grind only
      _ = 4 := by rw [hi]; grind
  have hf : 1/((n : Rat)+1)*(32*((n : Rat)+1)) = 32 := by
    calc
      1/((n : Rat)+1)*(32*((n : Rat)+1)) =
          32*(((n : Rat)+1)*((n : Rat)+1)⁻¹) := by rw [Rat.div_def]; grind only
      _ = 32 := by rw [hj]; grind
  change 4*(32*((n : Rat)+1))⁻¹*(32*((n : Rat)+1)) ≤ 1/((n : Rat)+1)*(32*((n : Rat)+1))
  rw [he, hf]
  decide

theorem raw_valid {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s) : (raw q m hq s).Valid := by
  apply RealRaw.prefixStabilize_valid_of_future
  · intro n; change (0 : Rat) ≤ approx q m hq s n-approx q m hq s n; grind
  · apply shrinksToZero_of_natOverSuccBound (C := 0)
    intro n; change approx q m hq s n-approx q m hq s n ≤ _; simp; grind
  · exact candidate_future hq hs
  · exact radius_shrinks

theorem raw_enclosure (q m : Nat) (hq : 0 < q) (s : Rat) (n : Nat) :
    ({lo := approx q m hq s n-4*(budget n).val,
      hi := approx q m hq s n+4*(budget n).val} : QInterval).ContainsInterval
      ((raw q m hq s).compute n) :=
  RealRaw.prefixStabilize_contained_in_current_expand _ _ n

end ComputableAnalysis.ZetaReal
