import ComputableAnalysis.IntegerPowerImproper

/-! The other endpoint: polynomial powers converge at zero; reciprocal powers
diverge there. Compact witnesses precede the exhaustion argument. -/
namespace ComputableAnalysis.IntegerPowerIntegral
open Integral

def monomialCompact (k : Nat) (a b : Rat) : Rat := (b^(k+1)-a^(k+1))/((k : Rat)+1)

theorem monomial_cell_bounds (k : Nat) {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b-a)*a^k ≤ monomialCompact k a b ∧ monomialCompact k a b ≤ (b-a)*b^k := by
  have hs := slope_bounds k ha hab
  have hd := power_difference k a b
  have hl := Rat.mul_le_mul_of_nonneg_left hs.1 (show 0 ≤ b-a by grind)
  have hu := Rat.mul_le_mul_of_nonneg_left hs.2 (show 0 ≤ b-a by grind)
  have hk : 0 < (k : Rat)+1 := by have := Rat.natCast_nonneg (a := k); grind
  have he : monomialCompact k a b*((k : Rat)+1)=b^(k+1)-a^(k+1) := by
    unfold monomialCompact
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hk), Rat.mul_one]
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := (k : Rat)+1) ?_ hk
    rw [he, hd]
    have he' : (b-a)*a^k*((k : Rat)+1)=(b-a)*(((k : Rat)+1)*a^k) := by grind only
    rw [he']; exact hl
  · apply Rat.le_of_mul_le_mul_right (c := (k : Rat)+1) ?_ hk
    rw [he, hd]
    have he' : (b-a)*b^k*((k : Rat)+1)=(b-a)*(((k : Rat)+1)*b^k) := by grind only
    rw [he']; exact hu

theorem monomial_hasIntegral (k : Nat) {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) :
    HasIntegral (FunctionOnInterval.exactRat (fun x => x^k) a b) (RealRaw.ofRat (monomialCompact k a b)) := by
  have hc : ExactCellOrderPreservation (fun x => x^k)
      (fun u v => v^(k+1)/((k : Rat)+1)-u^(k+1)/((k : Rat)+1)) a b := by
    have he : (fun u v => v^(k+1)/((k : Rat)+1)-u^(k+1)/((k : Rat)+1))=monomialCompact k := by
      funext u v
      unfold monomialCompact
      simp only [Rat.div_def]
      grind only
    rw [he]
    constructor
    · intro u v c hau huv _hvb hf
      have hl := (monomial_cell_bounds k (by grind : 0 ≤ u) huv).1
      exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left (hf (Rat.le_refl) huv) (by grind)) hl
    · intro u v c hau huv _hvb hf
      have hu := (monomial_cell_bounds k (by grind : 0 ≤ u) huv).2
      exact Rat.le_trans hu (Rat.mul_le_mul_of_nonneg_left (hf huv (Rat.le_refl)) (by grind))
  have ht := monotone_tight (fun x => x^k) a b hab (fun x y hx hxy _ => power_mono k (by grind) hxy)
  have h := ExactCellOrderPreservation.hasIntegral hc ht
  have he : b^(k+1)/((k : Rat)+1)-a^(k+1)/((k : Rat)+1)=monomialCompact k a b := by
    unfold monomialCompact
    simp only [Rat.div_def]
    grind only
  rw [he] at h
  exact h

/-- This computes the improper integral of `x^k`, that is, exponent `p=-k`. -/
def zeroTruncation (k n : Nat) : FunctionOnInterval :=
  FunctionOnInterval.exactRat (fun x => x^k) (((n+1 : Nat) : Rat)⁻¹) 1

theorem zero_compact_agreement (k n : Nat) :
    monomialCompact k (((n+1 : Nat) : Rat)⁻¹) 1 = compact k 1 ((n+1 : Nat) : Rat) := by
  unfold monomialCompact compact
  rw [one_inverse, one_power]

theorem zero_hasIntegralLimit (k : Nat) :
    HasIntegralLimit (zeroTruncation k) (infinity k) := by
  have hc (n : Nat) : HasIntegral (zeroTruncation k n) (RealRaw.ofRat (compact k 1 ((n+1 : Nat) : Rat))) := by
    have hn : 0 < ((n+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
    have h := monomial_hasIntegral k (Rat.le_of_lt ((Rat.inv_pos).2 hn))
      (show (((n+1 : Nat) : Rat)⁻¹) ≤ 1 by simpa only [one_inverse] using inverse_antitone (a := 1) (by decide) (by exact_mod_cast (by omega : 1 ≤ n+1)))
    rw [zero_compact_agreement] at h
    exact h
  refine ⟨infinity_valid k, fun n => ⟨_,hc n⟩, ?_⟩
  intro eps
  obtain ⟨N,hN⟩ := (infinity_hasIntegralLimit k).converges eps
  refine ⟨N, ?_⟩
  intro n hn J hJ
  have hE := hJ.unique (hc n)
  have hK := compact_hasIntegral k (a := 1) (b := ((n+1 : Nat) : Rat)) (by decide)
    (by exact_mod_cast (by omega : 1 ≤ n+1))
  exact hN n hn J (hK.congr hJ.valid (RealRaw.equiv_symm hE))

/-- Every justified exhaustion value has the exact formula `1/(k+1)`. -/
theorem zero_exact_of_hasIntegralLimit (k : Nat) {I : RealRaw}
    (hI : HasIntegralLimit (zeroTruncation k) I) : I.Equiv (RealRaw.ofRat (1/((k : Rat)+1))) :=
  RealRaw.equiv_trans hI.valid (infinity_valid k) (RealRaw.ofRat_valid _)
    (hI.unique (zero_hasIntegralLimit k)) (infinity_exact k)

theorem one_le_power (k : Nat) {x : Rat} (hx : 1 ≤ x) : 1 ≤ x^k := by
  have h := power_mono k (a := 1) (by decide) hx
  rw [one_power] at h
  exact h

/-- At zero the reciprocal-power truncations grow at least linearly in this
explicit reciprocal cutoff parameter. -/
theorem zero_reciprocal_lower (k n : Nat) :
    (n : Rat)/((k : Rat)+1) ≤ compact k (((n+1 : Nat) : Rat)⁻¹) 1 := by
  have hn : 1 ≤ ((n+1 : Nat) : Rat) := by exact_mod_cast (by omega : 1 ≤ n+1)
  have hp := one_le_power k hn
  have hm := Rat.mul_le_mul_of_nonneg_right hp (show 0 ≤ ((n+1 : Nat) : Rat) by exact_mod_cast (Nat.zero_le (n+1)))
  have hi : 0 ≤ ((k : Rat)+1)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 (by have := Rat.natCast_nonneg (a := k); grind))
  unfold compact
  rw [Rat.inv_inv, one_inverse, one_power, Rat.pow_succ]
  have hg : (n : Rat) ≤ ((n+1 : Nat) : Rat)^k*((n+1 : Nat) : Rat)-1 := by
    simp only [Rat.one_mul, Rat.natCast_add] at hm ⊢
    grind only
  exact Rat.mul_le_mul_of_nonneg_right hg hi

/-- Effective divergence for every integer exponent at least two. Each value
here is separately certified as the compact integral. -/
theorem zero_reciprocal_diverges (k target n : Nat) (hn : (k+1)*target ≤ n) :
    (target : Rat) ≤ compact k (((n+1 : Nat) : Rat)⁻¹) 1 := by
  have h := zero_reciprocal_lower k n
  have hk : 0 < (k : Rat)+1 := by have := Rat.natCast_nonneg (a := k); grind
  have hcast : ((k : Rat)+1)*(target : Rat) ≤ (n : Rat) := by exact_mod_cast hn
  have hm := Rat.mul_le_mul_of_nonneg_right hcast (Rat.le_of_lt ((Rat.inv_pos).2 hk))
  have he : (((k : Rat)+1)*(target : Rat))*((k : Rat)+1)⁻¹=(target : Rat) := by
    have := Rat.mul_inv_cancel ((k : Rat)+1) (Rat.ne_of_gt hk)
    grind only
  rw [he] at hm
  exact Rat.le_trans hm h

/-- No finite improper value exists for the reciprocal powers at zero. -/
theorem zero_reciprocal_not_hasIntegralLimit (k : Nat) (I : RealRaw) :
    ¬ HasIntegralLimit (fun n => FunctionOnInterval.exactRat (integrand (k+2))
      (((((k+1)*n+1 : Nat) : Rat))⁻¹) 1) I := by
  apply no_limit_of_growing_lower_bounds (I := I)
  intro n J hJ s t
  have hr : 0 < ((((k+1)*n+1 : Nat) : Rat)) := (Rat.natCast_pos).2 (by omega)
  have he := compact_exact k ((Rat.inv_pos).2 hr)
    (show (((((k+1)*n+1 : Nat) : Rat))⁻¹) ≤ 1 by
      simpa only [one_inverse] using inverse_antitone (a := 1) (by decide)
        (show 1 ≤ ((((k+1)*n+1 : Nat) : Rat)) by exact_mod_cast (by omega : 1 ≤ (k+1)*n+1))) hJ
  have ho := (RealRaw.compareAt_overlap_iff _ _ t t).1 (he t)
  have hl := zero_reciprocal_diverges k n ((k+1)*n) (Nat.le_refl _)
  exact Rat.le_trans hl ho.2

/-- Nonnegative polynomial powers diverge at infinity. -/
theorem monomial_infinity_diverges (k : Nat) (I : RealRaw) :
    ¬ HasIntegralLimit (fun n => FunctionOnInterval.exactRat (fun x => x^k)
      1 ((n+1 : Nat) : Rat)) I := by
  apply no_limit_of_growing_lower_bounds (I := I)
  intro n J hJ s t
  have hn : 1 ≤ ((n+1 : Nat) : Rat) := by exact_mod_cast (by omega : 1 ≤ n+1)
  have hc := monomial_hasIntegral k (a := 1) (b := ((n+1 : Nat) : Rat)) (by decide) hn
  have ho := (RealRaw.compareAt_overlap_iff _ _ t t).1 (hJ.unique hc t)
  have hl := (monomial_cell_bounds k (a := 1) (b := ((n+1 : Nat) : Rat)) (by decide) hn).1
  rw [one_power, Rat.mul_one] at hl
  have he : ((n+1 : Nat) : Rat)-1=(n : Rat) := by push_cast; grind only
  rw [he] at hl
  exact Rat.le_trans hl ho.2

end ComputableAnalysis.IntegerPowerIntegral
