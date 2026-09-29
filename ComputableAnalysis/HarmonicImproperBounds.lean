import ComputableAnalysis.IntegerPowerAtZero
import ComputableAnalysis.IntegerPowerSeries

/-! Explicit lower rectangles for the critical improper integral. Divergence
is witnessed by finite areas; no value at infinity is introduced. -/
namespace ComputableAnalysis.IntegerPowerIntegral
open Integral

def dyadic (n : Nat) : Rat := (2 : Rat)^n

theorem dyadic_pos (n : Nat) : 0 < dyadic n := Rat.pow_pos (by decide)

theorem dyadic_step (n : Nat) : dyadic (n+1)=2*dyadic n := by
  rw [dyadic, Rat.pow_succ]
  grind only [dyadic]

theorem dyadic_mono {n m : Nat} (h : n ≤ m) : dyadic n ≤ dyadic m := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Rat.le_refl
  | succ d ih =>
    rw [show n+(d+1)=(n+d)+1 by omega, dyadic_step]
    have hp := dyadic_pos (n+d)
    grind only

theorem dyadic_ge_stage (n : Nat) : ((n+1 : Nat) : Rat) ≤ dyadic n := by
  induction n with
  | zero => change (1 : Rat) ≤ 1; exact Rat.le_refl
  | succ n ih =>
    rw [dyadic_step]
    have hn := Rat.natCast_nonneg (a := n)
    simp only [Rat.natCast_add] at ih ⊢
    grind only

theorem dyadic_cutoff_shrinks : ShrinksToZero (fun n => (dyadic n)⁻¹) := by
  apply shrinksToZero_of_natOverSuccBound (C := 1)
  intro n
  change _ ≤ 1/((n+1 : Nat) : Rat)
  rw [Rat.div_def, Rat.one_mul]
  exact inverse_antitone ((Rat.natCast_pos).2 (by omega)) (dyadic_ge_stage n)

/-- A finite geometric partition, with arbitrary positive rational scale. -/
def dyadicPartition (a : Rat) (ha : 0 < a) (N : Nat) (hN : 0 < N) :
    RationalPartition a (a*dyadic N) where
  pieces := N
  positive := hN
  point k := a*dyadic k
  left_endpoint := by change a*1=a; exact Rat.mul_one _
  right_endpoint := rfl
  monotone := fun i j hij _ => Rat.mul_le_mul_of_nonneg_left (dyadic_mono hij) (Rat.le_of_lt ha)

/-- Both bounds hold at every rational point of every cell. -/
def harmonicBounds (a : Rat) (ha : 0 < a) (N : Nat) (hN : 0 < N) :
    Bounds (FunctionOnInterval.exactRat (fun x => x⁻¹) a (a*dyadic N)) where
  partition := dyadicPartition a ha N hN
  lower k := (a*dyadic (k+1))⁻¹
  upper k := (a*dyadic k)⁻¹
  lower_le := by
    intro k hk x hx n
    exact inverse_antitone (by have hp := Rat.mul_pos ha (dyadic_pos k); change a*dyadic k ≤ x ∧ _ at hx; grind) hx.2
  upper_ge := by
    intro k hk x hx n
    exact inverse_antitone (Rat.mul_pos ha (dyadic_pos k)) hx.1

theorem harmonic_lower_cell (a : Rat) (ha : 0 < a) (k : Nat) :
    (a*dyadic (k+1)-a*dyadic k)*(a*dyadic (k+1))⁻¹=1/2 := by
  rw [dyadic_step]
  have he : a*(2*dyadic k)=2*(a*dyadic k) := by grind only
  rw [he, Rat.inv_mul_rev]
  have hc := Rat.mul_inv_cancel (a*dyadic k) (Rat.ne_of_gt (Rat.mul_pos ha (dyadic_pos k)))
  rw [Rat.div_def, Rat.one_mul]
  grind only

theorem harmonic_upper_cell (a : Rat) (ha : 0 < a) (k : Nat) :
    (a*dyadic (k+1)-a*dyadic k)*(a*dyadic k)⁻¹=1 := by
  rw [dyadic_step]
  have hc := Rat.mul_inv_cancel (a*dyadic k) (Rat.ne_of_gt (Rat.mul_pos ha (dyadic_pos k)))
  grind only

theorem harmonic_bounds_sums (a : Rat) (ha : 0 < a) (N : Nat) (hN : 0 < N) :
    (harmonicBounds a ha N hN).lowerSum=(N : Rat)/2 ∧
      (harmonicBounds a ha N hN).upperSum=(N : Rat) := by
  have hc (r : Rat) (n : Nat) : rectangleSum (fun _ => r) n = (n : Rat)*r := by
    induction n with
    | zero => change 0=0*r; grind
    | succ n ih => simp only [rectangleSum, ih, Rat.natCast_add]; grind
  unfold Bounds.lowerSum Bounds.upperSum harmonicBounds dyadicPartition
  simp only [harmonic_lower_cell a ha, harmonic_upper_cell a ha, hc, Rat.mul_one, Rat.div_def, Rat.one_mul]
  trivial

/-- At infinity, a finite partition already forces arbitrarily large area. -/
theorem harmonic_infinity_lower (target : Nat) {I : RealRaw}
    (hI : HasIntegral (FunctionOnInterval.exactRat (fun x => x⁻¹)
      1 (1*dyadic (2*target+1))) I) :
    (RealRaw.ofRat (target : Rat)).Le I := by
  intro _ n
  have hb := (hI.bounds (harmonicBounds 1 (by decide) (2*target+1) (by omega)) n).1
  rw [(harmonic_bounds_sums 1 (by decide) (2*target+1) (by omega)).1] at hb
  change (target : Rat) ≤ (I.compute n).hi
  simp only [Rat.natCast_add, Rat.natCast_mul] at hb
  grind only

/-- The same lower-area certificate applies near zero by scaling the partition.
Its upper endpoint is exactly one, by the next theorem. -/
theorem harmonic_zero_lower (target : Nat) {I : RealRaw}
    (hI : HasIntegral (FunctionOnInterval.exactRat (fun x => x⁻¹)
      (dyadic (2*target+1))⁻¹ ((dyadic (2*target+1))⁻¹*dyadic (2*target+1))) I) :
    (RealRaw.ofRat (target : Rat)).Le I := by
  intro _ n
  have ha := (Rat.inv_pos).2 (dyadic_pos (2*target+1))
  have hb := (hI.bounds (harmonicBounds _ ha (2*target+1) (by omega)) n).1
  rw [(harmonic_bounds_sums _ ha (2*target+1) (by omega)).1] at hb
  change (target : Rat) ≤ (I.compute n).hi
  simp only [Rat.natCast_add, Rat.natCast_mul] at hb
  grind only

theorem harmonic_zero_endpoint (N : Nat) : (dyadic N)⁻¹*dyadic N=1 :=
  Rat.inv_mul_cancel _ (Rat.ne_of_gt (dyadic_pos N))

/-- Nonexistence of a finite improper value, justified by the explicit lower
rectangles above. This does not pretend to construct a compact log evaluator. -/
theorem harmonic_infinity_diverges (I : RealRaw) :
    ¬ HasIntegralLimit (fun n => FunctionOnInterval.exactRat (fun x => x⁻¹)
      1 (1*dyadic (2*n+1))) I :=
  no_limit_of_growing_lower_bounds (fun n _ h => harmonic_infinity_lower n h) I

theorem harmonic_zero_diverges (I : RealRaw) :
    ¬ HasIntegralLimit (fun n => FunctionOnInterval.exactRat (fun x => x⁻¹)
      (dyadic (2*n+1))⁻¹ ((dyadic (2*n+1))⁻¹*dyadic (2*n+1))) I :=
  no_limit_of_growing_lower_bounds (fun n _ h => harmonic_zero_lower n h) I

end ComputableAnalysis.IntegerPowerIntegral
