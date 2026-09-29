import ComputableAnalysis.IntegerPowerImproper

/-! Integral comparison for the independently computed reciprocal-power series. -/
namespace ComputableAnalysis.IntegerPowerIntegral

/-- The first `N` terms, starting at denominator one. -/
def partialSum (p : Nat) : Nat → Rat
  | 0 => 0
  | N+1 => partialSum p N + integrand p ((N+1 : Nat) : Rat)

theorem integrand_nonneg (p : Nat) {x : Rat} (hx : 0 < x) : 0 ≤ integrand p x :=
  Rat.pow_nonneg (Rat.le_of_lt ((Rat.inv_pos).2 hx))

theorem partial_mono (p : Nat) {N M : Nat} (hNM : N ≤ M) : partialSum p N ≤ partialSum p M := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero => exact Rat.le_refl
  | succ d ih =>
    rw [show N+(d+1)=(N+d)+1 by omega, partialSum]
    have h := integrand_nonneg p (x := ((N+d+1 : Nat) : Rat)) ((Rat.natCast_pos).2 (by omega))
    grind only

theorem compact_add (k : Nat) (a b c : Rat) :
    compact k a b + compact k b c = compact k a c := by
  simp only [compact_eq_tail_sub]
  grind only

/-- The integral test is derived by summing the actual cell inequalities. -/
theorem finite_integral_comparison (k N d : Nat) (hN : 0 < N) :
    compact k ((N+1 : Nat) : Rat) ((N+d+1 : Nat) : Rat) ≤
      partialSum (k+2) (N+d)-partialSum (k+2) N ∧
    partialSum (k+2) (N+d)-partialSum (k+2) N ≤
      compact k (N : Rat) ((N+d : Nat) : Rat) := by
  induction d with
  | zero => simp only [Nat.add_zero, compact_eq_tail_sub]; constructor <;> grind only
  | succ d ih =>
    have ha : 0 < ((N+d : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
    have hb : 0 < ((N+d+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
    have hl := (compact_cell_bounds k ha (b := ((N+d+1 : Nat) : Rat)) (by push_cast; grind)).1
    have hu := (compact_cell_bounds k hb (b := ((N+d+2 : Nat) : Rat)) (by push_cast; grind)).2
    have e1 : ((N+d+1 : Nat) : Rat)-((N+d : Nat) : Rat)=1 := by push_cast; grind
    have e2 : ((N+d+2 : Nat) : Rat)-((N+d+1 : Nat) : Rat)=1 := by push_cast; grind
    rw [e1, Rat.one_mul] at hl
    rw [e2, Rat.one_mul] at hu
    rw [show N+(d+1)=(N+d)+1 by omega, partialSum]
    have ht1 := compact_add k (N : Rat) ((N+d : Nat) : Rat) ((N+d+1 : Nat) : Rat)
    have ht2 := compact_add k ((N+1 : Nat) : Rat) ((N+d+1 : Nat) : Rat) ((N+d+2 : Nat) : Rat)
    simp only [Nat.add_assoc] at *
    constructor <;> grind only

/-- A sharper series computation: its uncertainty is the improper integral
beyond the last included integer, with its exponent dependence retained. -/
def series (k : Nat) : RealRaw where
  compute n := ⟨partialSum (k+2) (n+1), partialSum (k+2) (n+1)+tail k ((n+1 : Nat) : Rat)⟩

theorem series_contains_partial (k n M : Nat) (hnM : n+1 ≤ M) :
    ((series k).compute n).lo ≤ partialSum (k+2) M ∧
      partialSum (k+2) M ≤ ((series k).compute n).hi := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hnM
  have h := (finite_integral_comparison k (n+1) d (by omega)).2
  have ht := tail_nonneg k (R := ((n+1+d : Nat) : Rat)) ((Rat.natCast_pos).2 (by omega))
  rw [compact_eq_tail_sub] at h
  exact ⟨partial_mono _ (by omega), by change _ ≤ partialSum (k+2) (n+1)+tail k _; grind only⟩

theorem series_width (k n : Nat) : ((series k).compute n).width = tail k ((n+1 : Nat) : Rat) := by
  unfold series QInterval.width
  grind only

theorem series_valid (k : Nat) : (series k).Valid := by
  refine ⟨?_,?_,?_⟩
  · intro n
    rw [series_width]
    exact tail_nonneg _ ((Rat.natCast_pos).2 (by omega))
  · intro n m hnm
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (show n+1 ≤ m+1 by omega)
    have h := (finite_integral_comparison k (n+1) d (by omega)).2
    rw [← hd, compact_eq_tail_sub] at h
    have ht := tail_nonneg k (R := ((m+1 : Nat) : Rat)) ((Rat.natCast_pos).2 (by omega))
    have hp := partial_mono (k+2) (show n+1 ≤ m+1 by omega)
    change partialSum (k+2) (n+1) ≤ partialSum (k+2) (m+1) ∧
      partialSum (k+2) (m+1) ≤ partialSum (k+2) (m+1)+tail k ((m+1 : Nat) : Rat) ∧
      partialSum (k+2) (m+1)+tail k ((m+1 : Nat) : Rat) ≤ partialSum (k+2) (n+1)+tail k ((n+1 : Nat) : Rat)
    grind only
  · apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    rw [series_width]
    exact tail_le_reciprocal k (by exact_mod_cast (by omega : 1 ≤ n+1))

/-- Convergence is stated against all boxes of the supplied represented value. -/
def SumsTo (p : Nat) (I : RealRaw) : Prop :=
  I.Valid ∧ ∀ eps : QPos, ∃ N, ∀ n, N ≤ n → ∀ stage,
    (I.compute stage).lo ≤ partialSum p n+eps.val ∧
    partialSum p n ≤ (I.compute stage).hi+eps.val

theorem series_sumsTo (k : Nat) : SumsTo (k+2) (series k) := by
  refine ⟨series_valid k, ?_⟩
  intro eps
  obtain ⟨N,hN⟩ := (series_valid k).2.2 eps
  refine ⟨N+1, ?_⟩
  intro n hn s
  let m := max n (s+1)
  have hs := series_contains_partial k s m (Nat.le_max_right _ _)
  have hn' := series_contains_partial k (n-1) m (by dsimp [m]; omega)
  have he : n-1+1=n := by omega
  have hw := hN (n-1) (by omega)
  rw [series_width] at hw
  change partialSum (k+2) (n-1+1) ≤ partialSum (k+2) m ∧
    partialSum (k+2) m ≤ partialSum (k+2) (n-1+1)+tail k ((n-1+1 : Nat) : Rat) at hn'
  rw [he] at hn' hw
  have hm := partial_mono (k+2) (show n ≤ m from Nat.le_max_left _ _)
  have heps := eps.property
  constructor
  · exact Rat.le_trans hs.1 (by grind only)
  · exact Rat.le_trans hm (Rat.le_trans hs.2 (by grind only))

/-- A finite lower estimate for harmonic blocks, used at the boundary exponent. -/
theorem harmonic_block_lower (N d : Nat) (hN : 0 < N) :
    (d : Rat)*(((N+d : Nat) : Rat)⁻¹) ≤ partialSum 1 (N+d)-partialSum 1 N := by
  have h : ∀ j, j ≤ d → (j : Rat)*(((N+d : Nat) : Rat)⁻¹) ≤
      partialSum 1 (N+j)-partialSum 1 N := by
    intro j hj
    induction j with
    | zero => simp only [Nat.add_zero]; change 0 * _ ≤ _ - _; grind only
    | succ j ih =>
      have hi := ih (by omega)
      have hm := inverse_antitone (a := ((N+j+1 : Nat) : Rat)) (b := ((N+d : Nat) : Rat))
        ((Rat.natCast_pos).2 (by omega)) (by exact_mod_cast (by omega : N+j+1 ≤ N+d))
      rw [show N+(j+1)=(N+j)+1 by omega, partialSum]
      simp only [integrand, Rat.pow_succ, Rat.pow_zero, Rat.one_mul, Rat.natCast_add] at *
      grind only
  exact h d (Nat.le_refl _)

theorem harmonic_double (N : Nat) (hN : 0 < N) : partialSum 1 N+1/2 ≤ partialSum 1 (2*N) := by
  have h := harmonic_block_lower N N hN
  have hn : (N : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hN)
  have hc := Rat.mul_inv_cancel (N : Rat) hn
  have hh : (N : Rat)*(((N+N : Nat) : Rat)⁻¹)=1/2 := by
    rw [show ((N+N : Nat) : Rat)=2*(N : Rat) by push_cast; grind, Rat.inv_mul_rev, ← Rat.mul_assoc, hc]
    simp only [Rat.one_mul, Rat.div_def]
  rw [hh, show N+N=2*N by omega] at h
  grind only

theorem harmonic_dyadic (j : Nat) : (j : Rat)/2 ≤ partialSum 1 (2^j) := by
  induction j with
  | zero => change 0/2 ≤ partialSum 1 1; rw [Rat.div_def, Rat.zero_mul]; exact partial_mono 1 (Nat.zero_le _)
  | succ j ih =>
    have h := harmonic_double (2^j) (Nat.two_pow_pos j)
    rw [Nat.pow_succ]
    rw [Nat.mul_comm (2^j) 2]
    simp only [Rat.natCast_add]
    grind only

/-- Effective divergence at the critical exponent: an explicit stage for each
finite target, with persistence at every later stage. -/
theorem harmonic_diverges (target n : Nat) (hn : 2^(2*target) ≤ n) :
    (target : Rat) ≤ partialSum 1 n := by
  have h := harmonic_dyadic (2*target)
  have hm := partial_mono 1 hn
  simp only [Rat.natCast_mul] at h
  grind only

theorem partial_zero (n : Nat) : partialSum 0 n = (n : Rat) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [partialSum, ih, integrand, Rat.pow_zero, Rat.natCast_add]; rfl

private theorem rat_le_num_natAbs_succ (q : Rat) :
    q <= (((q.num.natAbs : Nat) : Rat) + 1) := by
  by_cases hqpos : 0 < q
  · have hdenpos : 0 < ((q.den : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
    apply Rat.le_of_mul_le_mul_right (c := ((q.den : Nat) : Rat))
    · rw [Rat.mul_comm q ((q.den : Nat) : Rat), rat_den_mul_self]
      have hnumpos : 0 < q.num := rat_num_pos_of_pos hqpos
      have hnum_nonneg : 0 <= q.num := Int.le_of_lt hnumpos
      have hcast : (((q.num.natAbs : Nat) : Rat)) = (q.num : Rat) := by
        exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
      calc
        (q.num : Rat) = ((q.num.natAbs : Nat) : Rat) := by rw [hcast]
        _ <= (((q.num.natAbs : Nat) : Rat) + 1) := by
          exact_mod_cast (Nat.le_succ q.num.natAbs)
        _ <= (((q.num.natAbs : Nat) : Rat) + 1) *
            ((q.den : Nat) : Rat) := by
          exact_mod_cast (Nat.le_mul_of_pos_right (q.num.natAbs + 1)
            (Nat.pos_of_ne_zero q.den_nz))
    · exact hdenpos
  · have hqnonpos : q <= 0 := by grind
    have hzero : (0 : Rat) <= (((q.num.natAbs : Nat) : Rat) + 1) := by
      exact_mod_cast (Nat.zero_le (q.num.natAbs + 1))
    exact Rat.le_trans hqnonpos hzero


/-- Convergence is independent of the raw name of its represented value. -/
theorem SumsTo.congr {p : Nat} {I J : RealRaw} (hI : SumsTo p I)
    (hJ : J.Valid) (he : I.Equiv J) : SumsTo p J := by
  refine ⟨hJ, ?_⟩
  intro eps
  obtain ⟨N,hN⟩ := hI.2 eps
  refine ⟨N, ?_⟩
  intro n hn s
  have hu : I.Le (RealRaw.ofRat (partialSum p n+eps.val)) := fun t _ => (hN n hn t).1
  have hl : (RealRaw.ofRat (partialSum p n-eps.val)).Le I := by
    intro _ t
    have h := (hN n hn t).2
    change partialSum p n-eps.val ≤ (I.compute t).hi
    grind only
  have hju := RealRaw.le_trans hI.1 (RealRaw.le_of_equiv hJ hI.1 (RealRaw.equiv_symm he)) hu s 0
  have hjl := RealRaw.le_trans hI.1 hl (RealRaw.le_of_equiv hI.1 hJ he) 0 s
  change (J.compute s).lo ≤ partialSum p n+eps.val at hju
  change partialSum p n-eps.val ≤ (J.compute s).hi at hjl
  exact ⟨hju,by grind only⟩

theorem SumsTo.unique {p : Nat} {I J : RealRaw} (hI : SumsTo p I) (hJ : SumsTo p J) : I.Equiv J := by
  have hle : ∀ X Y : RealRaw, SumsTo p X → SumsTo p Y → X.Le Y := by
    intro X Y hX hY s t
    by_cases h : (X.compute s).lo ≤ (Y.compute t).hi
    · exact h
    exfalso
    let eps : QPos := ⟨((X.compute s).lo-(Y.compute t).hi)/3, by grind⟩
    obtain ⟨N,hN⟩ := hX.2 eps
    obtain ⟨M,hM⟩ := hY.2 eps
    have hx := (hN (max N M) (Nat.le_max_left _ _) s).1
    have hy := (hM (max N M) (Nat.le_max_right _ _) t).2
    dsimp [eps] at hx hy
    grind only
  exact RealRaw.equiv_of_le_of_ge (hle I J hI hJ) (hle J I hJ hI)

/-- The full convergence classification on the explicit natural-exponent domain. -/
theorem natural_series_converges_iff (p : Nat) : (∃ I, SumsTo p I) ↔ 2 ≤ p := by
  constructor
  · intro ⟨I,hI⟩
    by_cases hp : 2 ≤ p
    · exact hp
    exfalso
    obtain ⟨N,hN⟩ := hI.2 ⟨1,by decide⟩
    let C := (I.compute 0).hi+1
    let T := C.num.natAbs+2
    have hC := rat_le_num_natAbs_succ C
    have hT : C < (T : Rat) := by dsimp [T]; push_cast; grind only
    have hbound := (hN (max N (max T (2^(2*T)))) (Nat.le_max_left _ _) 0).2
    change partialSum p (max N (max T (2^(2*T)))) ≤ C at hbound
    have hlarge : (T : Rat) ≤ partialSum p (max N (max T (2^(2*T)))) := by
      match p with
      | 0 => rw [partial_zero]; exact_mod_cast (show T ≤ max N (max T (2^(2*T))) by omega)
      | 1 => exact harmonic_diverges T _ (by omega)
      | p+2 => omega
    grind only
  · intro hp
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hp
    have he : p=k+2 := by omega
    rw [he]
    exact ⟨series k,series_sumsTo k⟩

/-- The integrand is literally reciprocal to the natural power. -/
theorem integrand_eq_one_div (p : Nat) (x : Rat) : integrand p x=1/(x^p) := by
  unfold integrand
  rw [Rat.div_def, Rat.one_mul]
  induction p with
  | zero => rw [Rat.pow_zero, Rat.pow_zero, one_inverse]
  | succ p ih => rw [Rat.pow_succ, Rat.pow_succ, Rat.inv_mul_rev, ih]; grind only

end ComputableAnalysis.IntegerPowerIntegral
