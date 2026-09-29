import ComputableAnalysis.RealPowerSeries
import ComputableAnalysis.IntegerPowerSeries

/-! The divergent side of the power test, including the critical exponent.
Finite harmonic blocks give explicit growing lower bounds. -/
namespace ComputableAnalysis
open Integral FormalPowerSeries ZetaReal BinomialPower BinomialPower.Global

namespace BinomialPower.Global
private theorem coefficient_at_one (k : Nat) : coefficient 1 k=1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := coefficient_step 1 k
    rw [ih] at h
    have hk := Rat.natCast_nonneg (a := k)
    have he : ((k : Rat)+1)*coefficient 1 (k+1)=((k : Rat)+1)*1 := by grind only
    have hi := Rat.mul_inv_cancel ((k : Rat)+1) (by grind)
    have hmul := congrArg (fun a : Rat => a*((k : Rat)+1)⁻¹) he
    grind only

private theorem coefficient_ge_one {s : Rat} (hs : s ≤ 1) (k : Nat) : 1 ≤ coefficient s k := by
  induction k with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have h := coefficient_step s k
    have hk := Rat.natCast_nonneg (a := k)
    have hm := Rat.mul_le_mul_of_nonneg_left ih (show 0 ≤ (k : Rat)+2-s by grind)
    apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) ?_ (by grind)
    grind only

private theorem polynomial_ge_one_parameter {s x : Rat} (hs : s ≤ 1) (hx : 0 ≤ x) (K : Nat) :
    powerPolynomial 1 K x ≤ powerPolynomial s K x := by
  apply sumBelow_le
  intro k _
  rw [coefficient_at_one]
  exact Rat.mul_le_mul_of_nonneg_right (coefficient_ge_one hs k) (Rat.pow_nonneg hx (n := k))

private theorem geometric_polynomial_identity {x : Rat} (hx : x < 1) (K : Nat) :
    powerPolynomial 1 K x=(1-x)⁻¹-x^K*(1-x)⁻¹ := by
  have h := powerPolynomial_parameter_succ 1 x K
  have hp := powerPolynomial_integer 0 (K+1) (by omega) x
  have hz : ((0 : Nat) : Rat)=0 := by decide
  rw [hz] at hp
  simp only [Rat.zero_add,Rat.pow_zero] at hp
  rw [show (1 : Rat)+1=2 by decide +kernel,hp,coefficient_at_one] at h
  have hi := Rat.mul_inv_cancel (1-x) (by grind)
  have hm := congrArg (fun a : Rat => a*(1-x)⁻¹) h
  have he : ((1-x)*powerPolynomial 1 K x)*(1-x)⁻¹=powerPolynomial 1 K x := by
    rw [Rat.mul_comm (1-x) _,Rat.mul_assoc,hi,Rat.mul_one]
  rw [Rat.add_mul,he] at hm
  grind only

/-- Weak exponent comparison at the boundary; it needs no decision whether
the represented exponent is strictly below or exactly equal to one. -/
theorem canonical_ge_reciprocal (p : Real) (hp : p.preferred.Le (RealRaw.ofRat 1))
    {x : Rat} (hx : 0 ≤ x) (hx1 : x < 1) :
    (RealRaw.ofRat (1-x)⁻¹).Le (canonicalValue p x) := by
  intro i j
  let A := chart p x hx hx1
  let s := (p.compute (A.observation p j)).lo
  have hs : s ≤ 1 := hp (A.observation p j) 0
  have hsA : (p.compute (A.observation p j)).lo ≤ s ∧ s ≤ (p.compute (A.observation p j)).hi :=
    ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ p.valid _⟩
  have hrec : 0 < (1-x)⁻¹ := Rat.inv_pos.mpr (by grind)
  rw [canonicalValue,dif_pos (And.intro hx hx1)]
  change (1-x)⁻¹ ≤ ((A.value p x).compute j).hi
  by_cases hgoal : (1-x)⁻¹ ≤ ((A.value p x).compute j).hi
  · exact hgoal
  exfalso
  let eps : QPos := ⟨((1-x)⁻¹-((A.value p x).compute j).hi)/2,by grind⟩
  obtain ⟨N,hN⟩ := geometric_shrinks hx hx1 (Rat.le_of_lt hrec) eps
  let K := max N (A.cutoff j)
  have hsmall := hN K (Nat.le_max_left _ _)
  have hV := A.value_contains (K := K) (chart_bounds p x hx hx1) hx (Rat.le_refl) (Nat.le_max_right _ _) hsA
  have hP := polynomial_ge_one_parameter hs hx K
  rw [geometric_polynomial_identity hx1 K] at hP
  change (1-x)⁻¹*x^K ≤ ((1-x)⁻¹-((A.value p x).compute j).hi)/2 at hsmall
  grind only
end BinomialPower.Global

namespace PowerIntegral

theorem infinity_ge_reciprocal (p : Real) (hp : p.preferred.Le (RealRaw.ofRat 1))
    {x : Rat} (hx : 1 ≤ x) : (RealRaw.ofRat x⁻¹).Le (infinityValue p x) := by
  have hi := inverse_unit_bounds hx
  have hr := Rat.mul_nonneg (Rat.le_of_lt hi.1) (Rat.le_of_lt hi.1)
  have h := canonical_ge_reciprocal p hp (show 0 ≤ 1-x⁻¹ by grind) (show 1-x⁻¹ < 1 by grind)
  rw [show 1-(1-x⁻¹)=x⁻¹ by grind only,Rat.inv_inv] at h
  intro i j
  have hm := Rat.mul_le_mul_of_nonneg_left (h i j) hr
  change x⁻¹*x⁻¹*x ≤ x⁻¹*x⁻¹*((canonicalValue p (1-x⁻¹)).compute j).hi at hm
  have hc : x⁻¹*x⁻¹*x=x⁻¹ := by rw [Rat.mul_assoc,Rat.inv_mul_cancel x (by grind),Rat.mul_one]
  rw [hc] at hm
  simp only [infinityValue,RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos hr]
  exact hm

theorem zero_ge_reciprocal (p : Real) (hp : (RealRaw.ofRat 1).Le p.preferred)
    {x : Rat} (hx : 0 < x) (hx1 : x ≤ 1) : (RealRaw.ofRat x⁻¹).Le (value p x) := by
  have hs : (parameter p).preferred.Le (RealRaw.ofRat 1) := by
    intro i j
    have h := hp j i
    change 1 ≤ (p.compute i).hi at h
    change 2-(p.compute i).hi ≤ 1
    grind only
  have h := canonical_ge_reciprocal (parameter p) hs (show 0 ≤ 1-x by grind) (show 1-x < 1 by grind)
  rw [show 1-(1-x)=x by grind only] at h
  exact h

theorem partialSum_ge_harmonic (p : Real) (hp : p.preferred.Le (RealRaw.ofRat 1)) (N : Nat) :
    (RealRaw.ofRat (IntegerPowerIntegral.partialSum 1 N)).Le (partialSum p N) := by
  induction N with
  | zero => exact RealRaw.le_refl _ (RealRaw.ofRat_valid 0)
  | succ N ih =>
    intro i j
    have h := infinity_ge_reciprocal p hp (x := ((N+1 : Nat) : Rat))
      (by exact_mod_cast (show 1 ≤ N+1 by omega)) i j
    have hprev := ih i j
    change IntegerPowerIntegral.partialSum 1 N ≤ ((partialSum p N).compute j).hi at hprev
    change (((N+1 : Nat) : Rat)⁻¹) ≤ ((infinityValue p ((N+1 : Nat) : Rat)).compute j).hi at h
    change IntegerPowerIntegral.partialSum 1 (N+1) ≤
      ((partialSum p N).compute j).hi+((infinityValue p ((1+N : Nat) : Rat)).compute j).hi
    rw [IntegerPowerIntegral.partialSum,show 1+N=N+1 by omega]
    simp only [IntegerPowerIntegral.integrand,Rat.pow_succ,Rat.pow_zero,Rat.one_mul]
    grind only

/-- Effective divergence with an explicit harmonic-block index for each target. -/
theorem series_diverges (p : Real) (hp : p.preferred.Le (RealRaw.ofRat 1)) (target N : Nat)
    (hN : 2^(2*target) ≤ N) : (RealRaw.ofRat (target : Rat)).Le (partialSum p N) := by
  have h := IntegerPowerIntegral.harmonic_diverges target N hN
  intro i j
  exact Rat.le_trans h (partialSum_ge_harmonic p hp N i j)

theorem not_sumsTo (p : Real) (hp : p.preferred.Le (RealRaw.ofRat 1)) (I : RealRaw) : ¬ SumsTo p I := by
  intro hI
  obtain ⟨N,hN⟩ := hI.2 ⟨1,by decide⟩
  let target := ((I.compute 0).hi+3).num.natAbs+1
  have hlarge := rational_upper_natural ((I.compute 0).hi+3)
  have ht : (I.compute 0).hi+3 ≤ (target : Rat) := by
    simpa only [target,Rat.natCast_add,show ((1 : Nat) : Rat)=1 by decide] using hlarge
  let M := max N (2^(2*target))
  have hdiv := series_diverges p hp target M (Nat.le_max_right _ _)
  obtain ⟨k,hk⟩ := (partialSum_valid p M).2.2 ⟨1,by decide⟩
  have hw := hk k (Nat.le_refl _)
  have hclose := (hN M (Nat.le_max_left _ _) 0 k).2
  have hl := hdiv 0 k
  change ((partialSum p M).compute k).hi-((partialSum p M).compute k).lo ≤ 1 at hw
  change ((partialSum p M).compute k).lo ≤ (I.compute 0).hi+1 at hclose
  change (target : Rat) ≤ ((partialSum p M).compute k).hi at hl
  grind only

/-- Full convergence classification, with arbitrary valid represented exponents. -/
theorem series_converges_iff (p : Real) : (∃ I, SumsTo p I) ↔ AboveOne p := by
  constructor
  · intro ⟨I,hI⟩
    by_cases hp : AboveOne p
    · exact hp
    exfalso
    apply not_sumsTo p (fun n _ => ?_) I hI
    change (p.compute n).lo ≤ 1
    by_cases h : (p.compute n).lo ≤ 1
    · exact h
    · exact False.elim (hp ⟨n,by grind⟩)
  · intro hp
    exact ⟨series p hp,series_sumsTo p hp⟩

end PowerIntegral
end ComputableAnalysis
