import ComputableAnalysis.GeometricSeriesCalculus

/-! Generalized binomial coefficients for a real-exponent zeta computation.
All estimates are finite rational inequalities, uniform away from exponent one. -/
namespace ComputableAnalysis.ZetaReal
open FormalPowerSeries

/-- Coefficients of `(1-z)^(s-2)`. At integer `s>=2` the series terminates. -/
def coefficient (s : Rat) : Nat → Rat
  | 0 => 1
  | k+1 => coefficient s k*((k : Rat)+2-s)/((k : Rat)+1)

theorem coefficient_step (s : Rat) (k : Nat) :
    ((k : Rat)+1)*coefficient s (k+1) = ((k : Rat)+2-s)*coefficient s k := by
  have hk := Rat.natCast_nonneg (a := k)
  have hi := Rat.mul_inv_cancel ((k : Rat)+1) (by grind)
  simp only [coefficient, Rat.div_def]
  grind only

theorem coefficient_zero (s : Rat) : coefficient s 0=1 := rfl

/-- A rational closed chart covering any supplied exponent strictly above one. -/
def InChart (q m : Nat) (s : Rat) : Prop :=
  1+1/((q : Rat)+1) ≤ s ∧ s ≤ (m : Rat)+2

def magnitude (s : Rat) (k : Nat) : Rat := qabs (coefficient s k)
def bound (m : Nat) : Rat := ((m : Rat)+3)^(m+1)
def ratio (q : Nat) : Rat := (2*(q : Rat)+2)/(2*(q : Rat)+3)

theorem chart_gt_one {q m : Nat} {s : Rat} (hs : InChart q m s) : 1 < s := by
  have hq := Rat.natCast_nonneg (a := q)
  have hp : 0 < 1/((q : Rat)+1) := by
    rw [Rat.div_def]; exact Rat.mul_pos (by decide) (Rat.inv_pos.mpr (by grind))
  unfold InChart at hs
  grind

theorem magnitude_step {s : Rat} {m k : Nat} (hs : s ≤ (m : Rat)+2) (hk : m+1 ≤ k) :
    ((k : Rat)+1)*magnitude s (k+1) = ((k : Rat)+2-s)*magnitude s k := by
  have hkm : (m : Rat)+1 ≤ (k : Rat) := by
    have := (Rat.natCast_le_natCast (a := m+1) (b := k)).mpr hk
    simp only [Rat.natCast_add] at this
    exact this
  have hn := Rat.natCast_nonneg (a := k)
  have h := congrArg qabs (coefficient_step s k)
  rw [qabs_mul, qabs_mul, qabs_eq_self_of_nonneg (by grind : 0 ≤ (k : Rat)+1),
    qabs_eq_self_of_nonneg (by grind : 0 ≤ (k : Rat)+2-s)] at h
  exact h

theorem magnitude_nonneg (s : Rat) (k : Nat) : 0 ≤ magnitude s k := qabs_nonneg _

theorem magnitude_decreasing {s : Rat} {m k : Nat}
    (hs1 : 1 ≤ s) (hs : s ≤ (m : Rat)+2) (hk : m+1 ≤ k) :
    magnitude s (k+1) ≤ magnitude s k := by
  have h := magnitude_step hs hk
  have hn := Rat.natCast_nonneg (a := k)
  have hm := magnitude_nonneg s k
  have hx := Rat.mul_nonneg (by grind : 0 ≤ s-1) hm
  apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) (by grind only) (by grind)

theorem magnitude_antitone {s : Rat} {m n k : Nat}
    (hs1 : 1 ≤ s) (hs : s ≤ (m : Rat)+2) (hn : m+1 ≤ n) (hnk : n ≤ k) :
    magnitude s k ≤ magnitude s n := by
  induction hnk with
  | refl => exact Rat.le_refl
  | @step k hnk ih =>
    exact Rat.le_trans (magnitude_decreasing (k := k) hs1 hs (Nat.le_trans hn hnk)) ih

/-- The exact difference identity supplies the outer summation tail. -/
theorem magnitude_difference {s : Rat} {m k : Nat} (hs : s ≤ (m : Rat)+2) (hk : m+1 ≤ k) :
    (s-1)*magnitude s k = ((k : Rat)+1)*(magnitude s k-magnitude s (k+1)) := by
  have := magnitude_step hs hk
  grind only

private theorem magnitude_growth {s : Rat} {m : Nat}
    (hs1 : 1 ≤ s) (hs : s ≤ (m : Rat)+2) (k : Nat) :
    magnitude s k ≤ ((m : Rat)+3)^k := by
  induction k with
  | zero => simp only [magnitude, coefficient, Rat.pow_zero]; exact (by decide +kernel : qabs (1 : Rat) ≤ 1)
  | succ k ih =>
    have hk := Rat.natCast_nonneg (a := k)
    have hm := Rat.natCast_nonneg (a := m)
    have ha : qabs ((k : Rat)+2-s) ≤ ((m : Rat)+3)*((k : Rat)+1) := by
      apply qabs_le_of_neg_le_le <;> have := Rat.mul_nonneg hk hm <;> grind only
    have h := congrArg qabs (coefficient_step s k)
    rw [qabs_mul, qabs_mul, qabs_eq_self_of_nonneg (by grind : 0 ≤ (k : Rat)+1)] at h
    have h1 := Rat.mul_le_mul_of_nonneg_right ha (magnitude_nonneg s k)
    have h2 := Rat.mul_le_mul_of_nonneg_left ih
      (Rat.mul_nonneg (by grind : 0 ≤ (m : Rat)+3) (by grind : 0 ≤ (k : Rat)+1))
    rw [Rat.pow_succ]
    apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) ?_ (by grind)
    change ((k : Rat)+1)*qabs (coefficient s (k+1)) ≤ _
    change qabs (coefficient s k) ≤ _ at ih
    unfold magnitude at h1 h2
    grind only

theorem magnitude_bound {q m : Nat} {s : Rat} (hs : InChart q m s) (k : Nat) :
    magnitude s k ≤ bound m := by
  have hs1 := Rat.le_of_lt (chart_gt_one hs)
  by_cases hk : k ≤ m+1
  · exact Rat.le_trans (magnitude_growth hs1 hs.2 k)
      (pow_mono_exponent (by have := Rat.natCast_nonneg (a := m); grind) hk)
  · exact Rat.le_trans (magnitude_antitone hs1 hs.2 (Nat.le_refl _) (by omega))
      (magnitude_growth hs1 hs.2 (m+1))

/-- One dyadic block contracts uniformly on the whole exponent chart. -/
theorem magnitude_double {q m N : Nat} {s : Rat}
    (hs : InChart q m s) (hN : m+1 ≤ N) :
    magnitude s (2*N) ≤ ratio q*magnitude s N := by
  have hs1 := Rat.le_of_lt (chart_gt_one hs)
  have hNpos : (0 : Rat) < (N : Rat) := (Rat.natCast_pos).mpr (by omega)
  have hq := Rat.natCast_nonneg (a := q)
  have hqi := Rat.mul_inv_cancel ((q : Rat)+1) (by grind)
  have hdelta : 1 ≤ (s-1)*((q : Rat)+1) := by
    have h := Rat.mul_le_mul_of_nonneg_right hs.1 (by grind : 0 ≤ (q : Rat)+1)
    simp only [Rat.div_def] at h
    grind only
  have step (i : Nat) (hi : i < N) :
      magnitude s (2*N) ≤ 2*(N : Rat)*((q : Rat)+1)*
        (magnitude s (N+i)-magnitude s (N+i+1)) := by
    have hm := magnitude_antitone hs1 hs.2 (by omega : m+1 ≤ N+i) (by omega : N+i ≤ 2*N)
    have hd := magnitude_difference hs.2 (by omega : m+1 ≤ N+i)
    have hdiff : 0 ≤ magnitude s (N+i)-magnitude s (N+i+1) := by
      have := magnitude_decreasing hs1 hs.2 (by omega : m+1 ≤ N+i); grind
    have hn : ((N+i : Nat) : Rat)+1 ≤ 2*(N : Rat) := by
      have h := (Rat.natCast_le_natCast (a := N+i+1) (b := 2*N)).mpr (by omega)
      simp only [Rat.natCast_add, Rat.natCast_mul] at h ⊢
      exact h
    have h1 := Rat.mul_le_mul_of_nonneg_right hdelta (magnitude_nonneg s (N+i))
    have h2 := Rat.mul_le_mul_of_nonneg_right hn
      (Rat.mul_nonneg (by grind : 0 ≤ (q : Rat)+1) hdiff)
    calc
      magnitude s (2*N) ≤ magnitude s (N+i) := hm
      _ ≤ ((s-1)*magnitude s (N+i))*((q : Rat)+1) := by grind only
      _ = (((N+i : Nat) : Rat)+1)*((q : Rat)+1)*
          (magnitude s (N+i)-magnitude s (N+i+1)) := by rw [hd]; grind only
      _ ≤ _ := by grind only
  have all (k : Nat) (hk : k ≤ N) :
      (k : Rat)*magnitude s (2*N) ≤ 2*(N : Rat)*((q : Rat)+1)*
        (magnitude s N-magnitude s (N+k)) := by
    induction k with
    | zero => simp; grind
    | succ k ih =>
      have h := step k (by omega)
      have hprev := ih (by omega)
      simp only [Rat.natCast_add]
      rw [show N+(k+1)=N+k+1 by omega]
      grind only
  have h := all N (Nat.le_refl N)
  rw [show N+N=2*N by omega] at h
  have hsmall : magnitude s (2*N) ≤ 2*((q : Rat)+1)*(magnitude s N-magnitude s (2*N)) := by
    apply Rat.le_of_mul_le_mul_left (c := (N : Rat)) (by grind only) hNpos
  have hi := Rat.mul_inv_cancel (2*(q : Rat)+3) (by grind)
  have he : (2*(q : Rat)+3)*(ratio q*magnitude s N) = (2*(q : Rat)+2)*magnitude s N := by
    unfold ratio
    rw [Rat.div_def]
    grind only
  apply Rat.le_of_mul_le_mul_left (c := 2*(q : Rat)+3) ?_ (by grind)
  rw [he]
  clear step all h hqi hdelta
  grind only

def cutoff (m j : Nat) : Nat := (m+1)*2^j

theorem cutoff_ge (m j : Nat) : m+1 ≤ cutoff m j := by
  have h : 1 ≤ 2^j := Nat.one_le_pow j 2 (by decide)
  unfold cutoff
  have := Nat.mul_le_mul_left (m+1) h
  omega

theorem ratio_bounds (q : Nat) : 0 ≤ ratio q ∧ ratio q < 1 := by
  have hq := Rat.natCast_nonneg (a := q)
  have hi := Rat.mul_inv_cancel (2*(q : Rat)+3) (by grind)
  have hp := Rat.inv_pos.mpr (by grind : 0 < 2*(q : Rat)+3)
  unfold ratio
  rw [Rat.div_def]
  constructor
  · exact Rat.mul_nonneg (by grind) (Rat.le_of_lt hp)
  · grind only

theorem magnitude_decay {q m : Nat} {s : Rat} (hs : InChart q m s) (j : Nat) :
    magnitude s (cutoff m j) ≤ bound m*(ratio q)^j := by
  induction j with
  | zero => simpa [cutoff] using magnitude_bound hs (m+1)
  | succ j ih =>
    have hd := magnitude_double hs (cutoff_ge m j)
    have hi := Rat.mul_le_mul_of_nonneg_left ih (ratio_bounds q).1
    have he : cutoff m (j+1)=2*cutoff m j := by simp [cutoff, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    rw [he, Rat.pow_succ]
    grind only

end ComputableAnalysis.ZetaReal
