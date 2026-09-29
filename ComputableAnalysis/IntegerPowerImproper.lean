import ComputableAnalysis.IntegerPowerIntegral
import ComputableAnalysis.ImproperIntegralBounds

/-!
The improper reciprocal-power computation for exponents `k+2`, with an actual
compact integral at every truncation and bounds on every later truncation.
-/
namespace ComputableAnalysis.IntegerPowerIntegral

theorem one_inverse : (1 : Rat)⁻¹=1 := by
  have h := Rat.mul_inv_cancel (1 : Rat) (by decide)
  simpa only [Rat.one_mul] using h

theorem one_power (k : Nat) : (1 : Rat)^k=1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Rat.pow_succ, ih, Rat.mul_one]

/-- Rational error remaining beyond a positive truncation. -/
def tail (k : Nat) (R : Rat) : Rat := (R⁻¹)^(k+1)/((k : Rat)+1)

theorem tail_nonneg (k : Nat) {R : Rat} (hR : 0 < R) : 0 ≤ tail k R := by
  unfold tail
  rw [Rat.div_def]
  exact Rat.mul_nonneg (Rat.pow_nonneg (Rat.le_of_lt ((Rat.inv_pos).2 hR)))
    (Rat.le_of_lt ((Rat.inv_pos).2 (by have := Rat.natCast_nonneg (a := k); grind)))

theorem tail_antitone (k : Nat) {R S : Rat} (hR : 0 < R) (hRS : R ≤ S) :
    tail k S ≤ tail k R := by
  unfold tail
  simp only [Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right
    (power_mono (k+1) (Rat.le_of_lt ((Rat.inv_pos).2 (by grind))) (inverse_antitone hR hRS))
    (Rat.le_of_lt ((Rat.inv_pos).2 (by have := Rat.natCast_nonneg (a := k); grind)))

theorem compact_eq_tail_sub (k : Nat) (a b : Rat) :
    compact k a b = tail k a-tail k b := by
  unfold compact tail
  simp only [Rat.div_def]
  grind only

theorem power_le_one {r : Rat} (hr : 0 ≤ r) (hr1 : r ≤ 1) (k : Nat) : r^k ≤ 1 := by
  have h := power_mono k hr hr1
  simpa only [one_power] using h

theorem tail_le_reciprocal (k : Nat) {R : Rat} (hR : 1 ≤ R) : tail k R ≤ 1/R := by
  have hRp : 0 < R := by grind
  have hr : 0 ≤ R⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hRp)
  have hr1 : R⁻¹ ≤ 1 := by simpa only [one_inverse] using inverse_antitone (a := 1) (by decide) hR
  have hp := power_le_one hr hr1 k
  have hm := Rat.mul_le_mul_of_nonneg_right hp hr
  have hk : 1 ≤ (k : Rat)+1 := by have := Rat.natCast_nonneg (a := k); grind
  have hki : ((k : Rat)+1)⁻¹ ≤ 1 := by
    simpa only [one_inverse] using inverse_antitone (a := 1) (by decide) hk
  have hh := Rat.mul_le_mul_of_nonneg_left hki (Rat.pow_nonneg hr (n := k+1))
  unfold tail
  simp only [Rat.div_def, Rat.one_mul, Rat.pow_succ] at hh ⊢
  grind only

/-- Stage `n` integrates exactly from `1` to `n+1`; its upper endpoint adds
an explicit tail. Both endpoints are computed by rational arithmetic. -/
def infinity (k : Nat) : RealRaw where
  compute n := ⟨compact k 1 ((n+1 : Nat) : Rat), 1/((k : Rat)+1)⟩

theorem tail_one (k : Nat) : tail k 1 = 1/((k : Rat)+1) := by rw [tail, one_inverse, one_power]

theorem infinity_width (k n : Nat) :
    ((infinity k).compute n).width = tail k ((n+1 : Nat) : Rat) := by
  change 1/((k : Rat)+1)-compact k 1 ((n+1 : Nat) : Rat) = _
  rw [compact_eq_tail_sub, tail_one]
  grind only

theorem infinity_valid (k : Nat) : (infinity k).Valid := by
  refine ⟨?_,?_,?_⟩
  · intro n
    rw [infinity_width]
    exact tail_nonneg k ((Rat.natCast_pos).2 (by omega))
  · intro n m hnm
    have hm := tail_nonneg k (R := ((m+1 : Nat) : Rat)) ((Rat.natCast_pos).2 (by omega))
    have h := tail_antitone k (R := ((n+1 : Nat) : Rat)) (S := ((m+1 : Nat) : Rat))
      ((Rat.natCast_pos).2 (by omega)) (by exact_mod_cast (by omega : n+1 ≤ m+1))
    change compact k 1 ((n+1 : Nat) : Rat) ≤ compact k 1 ((m+1 : Nat) : Rat) ∧
      compact k 1 ((m+1 : Nat) : Rat) ≤ 1/((k : Rat)+1) ∧ 1/((k : Rat)+1) ≤ 1/((k : Rat)+1)
    simp only [compact_eq_tail_sub, tail_one]
    grind only
  · apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    rw [infinity_width]
    exact tail_le_reciprocal k (by exact_mod_cast (by omega : 1 ≤ n+1))

/-- The stage encloses every later compact truncation, not merely its own
closed-form endpoint. This is the semantic tail estimate. -/
theorem infinity_contains_compact (k n : Nat) {R : Rat}
    (hR : ((n+1 : Nat) : Rat) ≤ R) :
    ((infinity k).compute n).lo ≤ compact k 1 R ∧
      compact k 1 R ≤ ((infinity k).compute n).hi := by
  have hn : 0 < ((n+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
  have hm := tail_antitone k hn hR
  have hz := tail_nonneg k (R := R) (by grind)
  change compact k 1 ((n+1 : Nat) : Rat) ≤ compact k 1 R ∧ compact k 1 R ≤ 1/((k : Rat)+1)
  simp only [compact_eq_tail_sub, tail_one]
  grind only

/-- An exact identity between valid represented values. -/
theorem infinity_exact (k : Nat) :
    (infinity k).Equiv (RealRaw.ofRat (1/((k : Rat)+1))) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have h := tail_nonneg k (R := ((n+1 : Nat) : Rat)) ((Rat.natCast_pos).2 (by omega))
  change compact k 1 ((n+1 : Nat) : Rat) ≤ 1/((k : Rat)+1) ∧ 1/((k : Rat)+1) ≤ 1/((k : Rat)+1)
  rw [compact_eq_tail_sub, tail_one]
  grind only

/-- The compact family in the exhaustion is fully specified. -/
def infinityTruncation (k n : Nat) : FunctionOnInterval :=
  FunctionOnInterval.exactRat (integrand (k+2)) 1 ((n+1 : Nat) : Rat)

theorem infinity_hasIntegralLimit (k : Nat) :
    Integral.HasIntegralLimit (infinityTruncation k) (infinity k) := by
  refine ⟨infinity_valid k, ?_, ?_⟩
  · intro n
    exact ⟨RealRaw.ofRat (compact k 1 ((n+1 : Nat) : Rat)),
      compact_hasIntegral k (by decide) (by exact_mod_cast (by omega : 1 ≤ n+1))⟩
  · intro eps
    obtain ⟨N,hN⟩ := (infinity_valid k).2.2 eps
    refine ⟨N, ?_⟩
    intro n hn J hJ s t
    have he := compact_exact k (a := 1) (b := ((n+1 : Nat) : Rat)) (by decide)
      (by exact_mod_cast (by omega : 1 ≤ n+1)) hJ
    have ho := (RealRaw.compareAt_overlap_iff _ _ t t).1 (he t)
    have hs := infinity_contains_compact k s (R := ((s+1 : Nat) : Rat)) (Rat.le_refl)
    have hw := hN n hn
    rw [infinity_width] at hw
    change (J.compute t).lo ≤ compact k 1 ((n+1 : Nat) : Rat) ∧
      compact k 1 ((n+1 : Nat) : Rat) ≤ (J.compute t).hi at ho
    change compact k 1 ((s+1 : Nat) : Rat) ≤ (J.compute t).hi+eps.val ∧
      (J.compute t).lo ≤ 1/((k : Rat)+1)+eps.val
    simp only [compact_eq_tail_sub, tail_one] at ho hs ⊢
    have hnonneg := tail_nonneg k (R := ((n+1 : Nat) : Rat)) ((Rat.natCast_pos).2 (by omega))
    have hnonnegs := tail_nonneg k (R := ((s+1 : Nat) : Rat)) ((Rat.natCast_pos).2 (by omega))
    have heps := eps.property
    grind only

/-- Any other justified limit along this exhaustion has the same exact value. -/
theorem infinity_exact_of_hasIntegralLimit (k : Nat) {I : RealRaw}
    (hI : Integral.HasIntegralLimit (infinityTruncation k) I) :
    I.Equiv (RealRaw.ofRat (1/((k : Rat)+1))) :=
  RealRaw.equiv_trans hI.valid (infinity_valid k) (RealRaw.ofRat_valid _)
    (hI.unique (infinity_hasIntegralLimit k)) (infinity_exact k)

/-- The truncations actually exhaust the positive half-line. -/
theorem infinity_exhausts (R : Rat) : ∃ n : Nat, R ≤ ((n+1 : Nat) : Rat) := by
  refine ⟨R.num.natAbs, ?_⟩
  have h := Integral.rational_upper_natural R
  push_cast
  exact h

/-- The reciprocal cutoffs are positive and approach zero with an explicit
rational denominator modulus. -/
theorem zero_cutoff_shrinks : ShrinksToZero (fun n => (((n+1 : Nat) : Rat)⁻¹)) := by
  apply shrinksToZero_of_natOverSuccBound (C := 1)
  intro n
  change _ ≤ 1/((n+1 : Nat) : Rat)
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.le_refl

end ComputableAnalysis.IntegerPowerIntegral
