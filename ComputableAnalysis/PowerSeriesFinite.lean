import ComputableAnalysis.PowerIntegralOrder

/-! Finite integral comparison for independently evaluated represented-power
series. The summands are computed before convergence is asserted. -/
namespace ComputableAnalysis.PowerIntegral
open Integral FormalPowerSeries BinomialPower BinomialPower.Global

def sumFrom (p : Real) (N : Nat) : Nat → RealRaw
  | 0 => RealRaw.ofRat 0
  | d+1 => RealRaw.add (sumFrom p N d) (infinityValue p ((N+d : Nat) : Rat))

theorem sumFrom_valid (p : Real) {N : Nat} (hN : 0 < N) (d : Nat) : (sumFrom p N d).Valid := by
  induction d with
  | zero => exact RealRaw.ofRat_valid 0
  | succ d ih => exact RealRaw.add_valid ih (infinityValue_valid p (by exact_mod_cast (show 1 ≤ N+d by omega)))

theorem sumFrom_nonneg (p : Real) {N : Nat} (hN : 0 < N) (d : Nat) :
    (RealRaw.ofRat 0).Le (sumFrom p N d) := by
  induction d with
  | zero => exact RealRaw.le_refl _ (RealRaw.ofRat_valid 0)
  | succ d ih =>
    intro i j
    have h := infinity_nonneg p (show 1 ≤ ((N+d : Nat) : Rat) by exact_mod_cast (show 1 ≤ N+d by omega)) i j
    have hprev := ih i j
    change 0 ≤ ((sumFrom p N d).compute j).hi+((infinityValue p ((N+d : Nat) : Rat)).compute j).hi
    change 0 ≤ ((sumFrom p N d).compute j).hi at hprev
    change 0 ≤ ((infinityValue p ((N+d : Nat) : Rat)).compute j).hi at h
    grind only

def integerPartition (N d : Nat) (hd : 0 < d) : RationalPartition (N : Rat) ((N+d : Nat) : Rat) where
  pieces := d
  positive := hd
  point k := ((N+k : Nat) : Rat)
  left_endpoint := by simp only [Nat.add_zero]
  right_endpoint := rfl
  monotone := by intro i j hij _; exact_mod_cast (show N+i ≤ N+j by omega)

def integerBounds (p : Real) (hp : (RealRaw.ofRat 0).Le p.preferred)
    (N d : Nat) (hN : 0 < N) (hd : 0 < d) (stage : Nat) :
    Bounds (infinityFunction p (N : Rat) ((N+d : Nat) : Rat) (by exact_mod_cast (show 1 ≤ N by omega))) where
  partition := integerPartition N d hd
  lower k := ((infinityValue p ((N+k+1 : Nat) : Rat)).compute stage).lo
  upper k := ((infinityValue p ((N+k : Nat) : Rat)).compute stage).hi
  lower_le := by
    intro k hk x hx n
    change ((N+k : Nat) : Rat) ≤ x ∧ x ≤ ((N+(k+1) : Nat) : Rat) at hx
    have hbase : 1 ≤ ((N+k : Nat) : Rat) := by exact_mod_cast (show 1 ≤ N+k by omega)
    exact infinity_antitone p hp (Rat.le_trans hbase hx.1) (by simpa only [Nat.add_assoc] using hx.2) stage n
  upper_ge := by
    intro k hk x hx n
    change ((N+k : Nat) : Rat) ≤ x ∧ x ≤ ((N+(k+1) : Nat) : Rat) at hx
    exact infinity_antitone p hp (by exact_mod_cast (show 1 ≤ N+k by omega)) hx.1 n stage

theorem integerBounds_sums (p : Real) (hp : (RealRaw.ofRat 0).Le p.preferred)
    (N d : Nat) (hN : 0 < N) (hd : 0 < d) (stage : Nat) :
    (integerBounds p hp N d hN hd stage).lowerSum=((sumFrom p (N+1) d).compute stage).lo ∧
    (integerBounds p hp N d hN hd stage).upperSum=((sumFrom p N d).compute stage).hi := by
  have width (k : Nat) : (((N+(k+1) : Nat) : Rat)-((N+k : Nat) : Rat))=1 := by
    simp only [Rat.natCast_add,show ((1 : Nat) : Rat)=1 by decide]
    grind only
  have hlo (K : Nat) : rectangleSum (fun k => (((N+(k+1) : Nat) : Rat)-((N+k : Nat) : Rat))*
      ((infinityValue p ((N+k+1 : Nat) : Rat)).compute stage).lo) K = ((sumFrom p (N+1) K).compute stage).lo := by
    induction K with
    | zero => rfl
    | succ K ih =>
      rw [rectangleSum,width,Rat.one_mul,ih]
      change _= ((sumFrom p (N+1) K).compute stage).lo+((infinityValue p ((N+1+K : Nat) : Rat)).compute stage).lo
      rw [show N+K+1=N+1+K by omega]
  have hhi (K : Nat) : rectangleSum (fun k => (((N+(k+1) : Nat) : Rat)-((N+k : Nat) : Rat))*
      ((infinityValue p ((N+k : Nat) : Rat)).compute stage).hi) K = ((sumFrom p N K).compute stage).hi := by
    induction K with
    | zero => rfl
    | succ K ih => rw [rectangleSum,width,Rat.one_mul,ih]; rfl
  exact ⟨hlo d,hhi d⟩

/-- The two inequalities of the integral test, from certified whole-cell
bounds for the already constructed compact integrals. -/
theorem finite_integral_comparison (p : Real) (hp : (RealRaw.ofRat 0).Le p.preferred)
    (N d : Nat) (hN : 0 < N) (hd : 0 < d) :
    (sumFrom p (N+1) d).Le
      (infinityCompact p (N : Rat) ((N+d : Nat) : Rat)
        (by exact_mod_cast (show 1 ≤ N by omega)) (by exact_mod_cast (show N ≤ N+d by omega))) ∧
    (infinityCompact p (N : Rat) ((N+d : Nat) : Rat)
        (by exact_mod_cast (show 1 ≤ N by omega)) (by exact_mod_cast (show N ≤ N+d by omega))).Le
      (sumFrom p N d) := by
  have hI := infinityCompact_hasIntegral p (a := (N : Rat)) (b := ((N+d : Nat) : Rat))
    (by exact_mod_cast (show 1 ≤ N by omega)) (by exact_mod_cast (show N ≤ N+d by omega))
  constructor
  · intro i j
    have h := (hI.bounds (integerBounds p hp N d hN hd i) j).1
    rw [(integerBounds_sums p hp N d hN hd i).1] at h
    exact h
  · intro i j
    have h := (hI.bounds (integerBounds p hp N d hN hd j) i).2
    rw [(integerBounds_sums p hp N d hN hd j).2] at h
    exact h

/-- Explicit compact tail bounds, uniform over all larger finite endpoints. -/
theorem infinityCompact_tail (p : Real) (hp : AboveOne p) (j : Nat) {a b : Rat}
    (ha : 1 ≤ a) (hab : a ≤ b) (hcut : a⁻¹ ≤ endpointCutoff (endpointM p) j) :
    Within (RealRaw.ofRat 0) (infinityCompact p a b ha hab)
      (2*endpointError (endpointQ p hp) (endpointM p) j) := by
  have hai := inverse_unit_bounds ha
  have hbi := inverse_unit_bounds (Rat.le_trans ha hab)
  have hgap := inverse_gap ha hab
  let A := chart p (1-b⁻¹) (by grind) (by grind)
  have hA := chart_bounds p (1-b⁻¹) (by grind) (by grind)
  intro i k
  let n := max (separationStage p hp) (A.observation p k)
  let s := (p.compute n).lo
  have hs : (p.compute n).lo ≤ s ∧ s ≤ (p.compute n).hi := ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ p.valid _⟩
  have hsC := endpoint_chart p hp (show separationStage p hp ≤ n by exact Nat.le_max_left _ _) hs
  have hn := p.valid.2.1 (A.observation p k) n (Nat.le_max_right _ _)
  have hsA : (p.compute (A.observation p k)).lo ≤ s ∧ s ≤ (p.compute (A.observation p k)).hi :=
    ⟨hn.1,Rat.le_trans hn.2.1 hn.2.2⟩
  let L := max (A.cutoff k) (ZetaReal.cutoff (endpointM p) j)
  have hI := A.integral_contains hA (show 0 ≤ 1-a⁻¹ by grind)
    (show 1-a⁻¹ ≤ 1-b⁻¹ by grind) (show 1-b⁻¹ ≤ A.radius by exact Rat.le_refl)
    (show A.cutoff k ≤ L by exact Nat.le_max_left _ _) hsA
  rw [integrated_prefix_eq,integrated_prefix_eq] at hI
  have h1 := integrated_endpoint_error_le_cutoff hsC j L (Nat.le_max_right _ _) (Rat.le_of_lt hai.1) hcut
  have h2 := integrated_endpoint_error_le_cutoff hsC j L (Nat.le_max_right _ _) (Rat.le_of_lt hbi.1)
    (show b⁻¹ ≤ endpointCutoff (endpointM p) j by grind)
  have h1l := neg_qabs_le_self (ZetaReal.integratedPowerPolynomial s L (1-a⁻¹)-1/(s-1))
  have h1h := self_le_qabs (ZetaReal.integratedPowerPolynomial s L (1-a⁻¹)-1/(s-1))
  have h2l := neg_qabs_le_self (ZetaReal.integratedPowerPolynomial s L (1-b⁻¹)-1/(s-1))
  have h2h := self_le_qabs (ZetaReal.integratedPowerPolynomial s L (1-b⁻¹)-1/(s-1))
  change 0 ≤ ((A.integral p (1-a⁻¹) (1-b⁻¹)).compute k).hi+_ ∧
    ((A.integral p (1-a⁻¹) (1-b⁻¹)).compute k).lo ≤ 0+_
  constructor <;> grind only

theorem aboveOne_nonneg (p : Real) (hp : AboveOne p) : (RealRaw.ofRat 0).Le p.preferred := by
  intro i j
  have h := separationStage_spec p hp
  have ho := (RealRaw.compareAt_overlap_iff _ _ (separationStage p hp) j).1
    (RealRaw.allStagesOverlap_refl _ p.valid (separationStage p hp) j)
  change (p.compute (separationStage p hp)).lo ≤ (p.compute j).hi ∧ _ at ho
  change 0 ≤ (p.compute j).hi
  grind only

/-- Finite series tails inherit the independently proved improper-integral
bound. No infinite sum occurs in the proof. -/
theorem sumFrom_tail (p : Real) (hp : AboveOne p) (j N d : Nat) (hN : 0 < N)
    (hcut : (N : Rat)⁻¹ ≤ endpointCutoff (endpointM p) j) :
    Within (RealRaw.ofRat 0) (sumFrom p (N+1) d)
      (2*endpointError (endpointQ p hp) (endpointM p) j) := by
  have hnon := sumFrom_nonneg p (show 0 < N+1 by omega) d
  have herr0 : 0 ≤ 2*endpointError (endpointQ p hp) (endpointM p) j := by
    have hq := Rat.natCast_nonneg (a := endpointQ p hp)
    have h1 := Rat.mul_nonneg (Rat.mul_nonneg (show 0 ≤ 2*((endpointQ p hp : Nat) : Rat)+2 by grind)
      (bound_nonneg (endpointM p))) (Rat.pow_nonneg (ZetaReal.ratio_bounds (endpointQ p hp)).1 (n := j))
    have h2 := Rat.pow_nonneg (by decide +kernel : (0 : Rat) ≤ 1/2) (n := j)
    unfold endpointError
    grind only
  by_cases hd : d=0
  · subst d
    intro i k
    change 0 ≤ 0+_ ∧ 0 ≤ 0+_
    constructor <;> grind only
  have hI := infinityCompact_hasIntegral p (a := (N : Rat)) (b := ((N+d : Nat) : Rat))
    (by exact_mod_cast (show 1 ≤ N by omega)) (by exact_mod_cast (show N ≤ N+d by omega))
  have hcomp := (finite_integral_comparison p (aboveOne_nonneg p hp) N d hN (by omega)).1
  have htail := infinityCompact_tail p hp j
    (show 1 ≤ (N : Rat) by exact_mod_cast (show 1 ≤ N by omega))
    (show (N : Rat) ≤ ((N+d : Nat) : Rat) by exact_mod_cast (show N ≤ N+d by omega)) hcut
  have hup : (sumFrom p (N+1) d).Le (RealRaw.ofRat (2*endpointError (endpointQ p hp) (endpointM p) j)) :=
    RealRaw.le_trans hI.valid hcomp (fun k _ => by
      have h := (htail 0 k).2
      change ((infinityCompact p (N : Rat) ((N+d : Nat) : Rat) _ _).compute k).lo ≤ 0+2*endpointError (endpointQ p hp) (endpointM p) j at h
      change ((infinityCompact p (N : Rat) ((N+d : Nat) : Rat) _ _).compute k).lo ≤ 2*endpointError (endpointQ p hp) (endpointM p) j
      grind only)
  intro i k
  have hl := hnon i k
  have hh := hup k i
  change 0 ≤ ((sumFrom p (N+1) d).compute k).hi at hl
  change ((sumFrom p (N+1) d).compute k).lo ≤ 2*endpointError (endpointQ p hp) (endpointM p) j at hh
  change 0 ≤ ((sumFrom p (N+1) d).compute k).hi+_ ∧ ((sumFrom p (N+1) d).compute k).lo ≤ 0+_
  constructor <;> grind only

end ComputableAnalysis.PowerIntegral
