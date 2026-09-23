import ComputableAnalysis.ZetaReal.Dirichlet

namespace ComputableAnalysis.ZetaReal

/-- The first `N` Dirichlet terms, with their binomial powers approximated
at one common, certified degree. -/
def dirichletApprox (q m : Nat) (hq : 0 < q) (s : Rat) (N i : Nat) : Rat :=
  rectangle s (outerCutoff q m hq i) N

theorem dirichletApprox_extension {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s)
    (N i K : Nat) (hK : outerCutoff q m hq i ≤ K) :
    qabs (rectangle s K N-dirichletApprox q m hq s N i) ≤ (budget i).val := by
  have h := rectangle_outer_tail hs (outerCutoff_ge q m hq i) (K-outerCutoff q m hq i) N
  rw [Nat.add_sub_of_le hK] at h
  exact Rat.le_trans h (Rat.le_trans (outerBudget_covers hq hs (outerCutoff_ge q m hq i)) (outerCutoff_budget q m hq i))

theorem dirichletApprox_cauchy {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s)
    (N i j : Nat) : qabs (dirichletApprox q m hq s N i-dirichletApprox q m hq s N j) ≤
      (budget i).val+(budget j).val := by
  let K := max (outerCutoff q m hq i) (outerCutoff q m hq j)
  have hi := dirichletApprox_extension hq hs N i K (Nat.le_max_left _ _)
  have hj := dirichletApprox_extension hq hs N j K (Nat.le_max_right _ _)
  have ht := qabs_sub_le (rectangle s K N-dirichletApprox q m hq s N j)
    (rectangle s K N-dirichletApprox q m hq s N i)
  have he : dirichletApprox q m hq s N i-dirichletApprox q m hq s N j =
      (rectangle s K N-dirichletApprox q m hq s N j)-(rectangle s K N-dirichletApprox q m hq s N i) := by grind only
  rw [he]; grind only

def dirichletCandidate (q m : Nat) (hq : 0 < q) (s : Rat) (N : Nat) : RealRaw where
  compute i := let a := dirichletApprox q m hq s N i; ⟨a,a⟩

/-- A valid finite Dirichlet sum, including nonintegral exponents. -/
def dirichletRaw (q m : Nat) (hq : 0 < q) (s : Rat) (N : Nat) : RealRaw :=
  RealRaw.prefixStabilize (dirichletCandidate q m hq s N) (fun i => 2*(budget i).val)

theorem dirichletRaw_valid {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s) (N : Nat) :
    (dirichletRaw q m hq s N).Valid := by
  apply RealRaw.prefixStabilize_valid_of_future
  · intro i; change (0 : Rat) ≤ dirichletApprox q m hq s N i-dirichletApprox q m hq s N i; grind
  · apply shrinksToZero_of_natOverSuccBound (C := 0)
    intro i; change dirichletApprox q m hq s N i-dirichletApprox q m hq s N i ≤ _; simp; grind
  · intro i j hij
    have h := dirichletApprox_cauchy hq hs N i j
    have ha := budget_antitone hij
    have hl := neg_qabs_le_self (dirichletApprox q m hq s N i-dirichletApprox q m hq s N j)
    have hh := self_le_qabs (dirichletApprox q m hq s N i-dirichletApprox q m hq s N j)
    constructor <;> dsimp [dirichletCandidate, QInterval.expand] <;> grind only
  · intro eps
    obtain ⟨i,hi⟩ := radius_shrinks eps
    refine ⟨i, fun j hj => ?_⟩
    have h := hi j hj
    have hp := (budget j).property
    grind only

theorem dirichletRaw_enclosure (q m : Nat) (hq : 0 < q) (s : Rat) (N i : Nat) :
    ({lo := dirichletApprox q m hq s N i-2*(budget i).val,
      hi := dirichletApprox q m hq s N i+2*(budget i).val} : QInterval).ContainsInterval
      ((dirichletRaw q m hq s N).compute i) :=
  RealRaw.prefixStabilize_contained_in_current_expand _ _ i

/-- Individual real powers are the successive finite Dirichlet sums.
The next theorem connects this valid computation to the explicit power polynomial. -/
def inversePowerRaw (q m : Nat) (hq : 0 < q) (s : Rat) (n : Nat) : RealRaw :=
  RealRaw.sub (dirichletRaw q m hq s (n+1)) (dirichletRaw q m hq s n)

theorem inversePowerRaw_valid {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s) (n : Nat) :
    (inversePowerRaw q m hq s n).Valid :=
  RealRaw.sub_valid (dirichletRaw_valid hq hs (n+1)) (dirichletRaw_valid hq hs n)

theorem inversePowerRaw_enclosure (q m : Nat) (hq : 0 < q) (s : Rat) (n i : Nat) :
    ({lo := inversePowerApprox s n (outerCutoff q m hq i)-4*(budget i).val,
      hi := inversePowerApprox s n (outerCutoff q m hq i)+4*(budget i).val} : QInterval).ContainsInterval
      ((inversePowerRaw q m hq s n).compute i) := by
  have ha := dirichletRaw_enclosure q m hq s (n+1) i
  have hb := dirichletRaw_enclosure q m hq s n i
  have he : dirichletApprox q m hq s (n+1) i-dirichletApprox q m hq s n i = inversePowerApprox s n (outerCutoff q m hq i) := by
    unfold dirichletApprox
    rw [rectangle_dirichlet, rectangle_dirichlet, FormalPowerSeries.sumBelow_succ]
    grind only
  rcases ha with ⟨hal,hah⟩
  rcases hb with ⟨hbl,hbh⟩
  constructor <;> change _ ≤ _ <;> dsimp [inversePowerRaw, RealRaw.sub, RealRaw.subCompute, RealRaw.addCompute, RealRaw.negCompute] <;> grind only

theorem dirichletApprox_to_zeta {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s)
    (i N j : Nat) (hN : innerCutoff m (outerCutoff q m hq i) i ≤ N) (hij : i ≤ j) :
    qabs (dirichletApprox q m hq s N j-approx q m hq s j) ≤ 7*(budget i).val := by
  have hc := dirichletApprox_cauchy hq hs N j i
  have ha := approx_cauchy hq hs i j
  have hi := rectangle_inner_tail hs (innerCutoff_pos m (outerCutoff q m hq i) i)
    (outerCutoff q m hq i) (N-innerCutoff m (outerCutoff q m hq i) i)
  rw [Nat.add_sub_of_le hN] at hi
  have hb := innerCutoff_budget m (outerCutoff q m hq i) i
  have hmono := budget_antitone hij
  have ht := qabs_add_le_three
    (dirichletApprox q m hq s N j-dirichletApprox q m hq s N i)
    (dirichletApprox q m hq s N i-approx q m hq s i)
    (approx q m hq s i-approx q m hq s j)
  change qabs (dirichletApprox q m hq s N i-approx q m hq s i) ≤ _ at hi
  have he : dirichletApprox q m hq s N j-approx q m hq s j =
      (dirichletApprox q m hq s N j-dirichletApprox q m hq s N i)+
      (dirichletApprox q m hq s N i-approx q m hq s i)+(approx q m hq s i-approx q m hq s j) := by grind only
  rw [he]; grind only

/-- Effective convergence of the actual finite Dirichlet sums to zeta.
Every point in either output box is covered; no limit object is assumed. -/
theorem dirichlet_convergence {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s)
    (eps : QPos) : ∃ N₀ j₀, ∀ N j, N₀ ≤ N → j₀ ≤ j → ∀ u v : Rat,
      ((dirichletRaw q m hq s N).compute j).lo ≤ u → u ≤ ((dirichletRaw q m hq s N).compute j).hi →
      ((raw q m hq s).compute j).lo ≤ v → v ≤ ((raw q m hq s).compute j).hi → qabs (u-v) ≤ eps.val := by
  obtain ⟨i,hi⟩ := radius_shrinks (⟨eps.val/4, by rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide))⟩ : QPos)
  refine ⟨innerCutoff m (outerCutoff q m hq i) i,i,?_⟩
  intro N j hN hj u v hul huh hvl hvh
  have ha := dirichletApprox_to_zeta hq hs i N j hN hj
  have hb := dirichletRaw_enclosure q m hq s N j
  have hc := raw_enclosure q m hq s j
  have hd := budget_antitone hj
  have he := hi i (Nat.le_refl i)
  have hp := (budget i).property
  have hlo := neg_qabs_le_self (dirichletApprox q m hq s N j-approx q m hq s j)
  have hhi := self_le_qabs (dirichletApprox q m hq s N j-approx q m hq s j)
  rcases hb with ⟨hbl,hbh⟩
  rcases hc with ⟨hcl,hch⟩
  change 4*(budget i).val ≤ eps.val/4 at he
  apply qabs_le_of_neg_le_le <;> grind [Rat.div_def]

end ComputableAnalysis.ZetaReal
