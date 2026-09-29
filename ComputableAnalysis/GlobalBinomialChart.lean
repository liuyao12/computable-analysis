import ComputableAnalysis.BinomialCompactBounds
import ComputableAnalysis.RealParameterSample

/-! Explicit schedules for binomial evaluation on a whole positive compact
base interval. They are derived from finite majorants, independently of tails
of improper integrals or Dirichlet sums. -/
namespace ComputableAnalysis.BinomialPower.Global
open FormalPowerSeries ZetaReal

structure Chart where
  order : Nat
  radius : Rat
  nonneg : 0 ≤ radius
  belowOne : radius < 1

def Chart.outer (A : Chart) : Rat := (1+A.radius)/2
def Chart.ratio (A : Chart) : Rat := 2*A.radius/(1+A.radius)
def Chart.tailBound (A : Chart) : Rat := ((1-A.outer)⁻¹)^A.order
def Chart.parameterLip (A : Chart) : Rat := ((1-A.radius)⁻¹)^(A.order+1)

theorem Chart.outer_pos (A : Chart) : 0 < A.outer := by dsimp [outer]; have := A.nonneg; grind

theorem Chart.outer_lt (A : Chart) : A.outer < 1 := by dsimp [outer]; have := A.belowOne; grind

theorem Chart.ratio_bounds (A : Chart) : 0 ≤ A.ratio ∧ A.ratio < 1 := by
  have h0 := A.nonneg
  have h1 := A.belowOne
  have hi := Rat.inv_pos.mpr (show 0 < 1+A.radius by grind)
  have hc := Rat.mul_inv_cancel (1+A.radius) (by grind)
  have hp := Rat.mul_pos (show 0 < 1-A.radius by grind) hi
  unfold ratio
  rw [Rat.div_def]
  constructor
  · exact Rat.mul_nonneg (by grind) (Rat.le_of_lt hi)
  · grind only

theorem Chart.ratio_outer (A : Chart) : A.ratio*A.outer=A.radius := by
  have hc := Rat.mul_inv_cancel (1+A.radius) (by have := A.nonneg; grind)
  unfold ratio outer
  simp only [Rat.div_def]
  grind only

theorem Chart.tailBound_pos (A : Chart) : 0 < A.tailBound :=
  Rat.pow_pos (Rat.inv_pos.mpr (by have := A.outer_lt; grind))

theorem Chart.parameterLip_pos (A : Chart) : 0 < A.parameterLip :=
  Rat.pow_pos (Rat.inv_pos.mpr (by have := A.belowOne; grind))

private def budgetWitness (p : Nat → Prop) [DecidablePred p]
    (hex : ∃ N, ∀ n, N ≤ n → p n) (n : Nat := 0) : Subtype p :=
  if h : p n then ⟨n,h⟩ else budgetWitness p hex (n+1)
termination_by Classical.choose hex-n
decreasing_by
  have hs := Classical.choose_spec hex
  have hn : n < Classical.choose hex := by
    by_cases hn : n < Classical.choose hex
    · exact hn
    · exact False.elim (h (hs n (by omega)))
  omega

def Chart.request (A : Chart) (n : Nat) : Nat :=
  (budgetWitness (fun K => A.tailBound*A.ratio^K ≤ ((1 : Rat)/2)^n)
    (geometric_shrinks A.ratio_bounds.1 A.ratio_bounds.2
      (Rat.le_of_lt A.tailBound_pos) (RealParameterSample.tolerance n))).val

theorem Chart.request_spec (A : Chart) (n : Nat) :
    A.tailBound*A.ratio^(A.request n) ≤ ((1 : Rat)/2)^n :=
  (budgetWitness (fun K => A.tailBound*A.ratio^K ≤ ((1 : Rat)/2)^n)
    (geometric_shrinks A.ratio_bounds.1 A.ratio_bounds.2
      (Rat.le_of_lt A.tailBound_pos) (RealParameterSample.tolerance n))).property

def Chart.cutoff (A : Chart) : Nat → Nat
  | 0 => A.request 0
  | n+1 => max (A.cutoff n) (max (n+1) (A.request (n+1)))

theorem Chart.cutoff_request (A : Chart) (n : Nat) : A.request n ≤ A.cutoff n := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ n => exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem Chart.cutoff_mono (A : Chart) {n K : Nat} (hnK : n ≤ K) : A.cutoff n ≤ A.cutoff K := by
  induction hnK with
  | refl => exact Nat.le_refl _
  | @step K _ ih => exact Nat.le_trans ih (Nat.le_max_left _ _)

theorem Chart.cutoff_ge (A : Chart) (n : Nat) : n ≤ A.cutoff n := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem Chart.cutoff_spec (A : Chart) (n : Nat) : A.tailBound*A.ratio^(A.cutoff n) ≤ ((1 : Rat)/2)^n :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left
    (pow_antitone_exponent A.ratio_bounds.1 (Rat.le_of_lt A.ratio_bounds.2) (A.cutoff_request n))
    (Rat.le_of_lt A.tailBound_pos)) (A.request_spec n)

def Chart.sampleShift (A : Chart) : Nat := RationalMajorant.halfDecayShift A.parameterLip ⟨1,by decide⟩

theorem Chart.sampleShift_spec (A : Chart) : A.parameterLip*((1 : Rat)/2)^(A.sampleShift) ≤ 1 :=
  RationalMajorant.halfDecayShift_spec (Rat.le_of_lt A.parameterLip_pos) ⟨1,by decide⟩

theorem pow_addition (x : Rat) (n k : Nat) : x^(n+k)=x^n*x^k := by
  induction k with
  | zero => simp only [Nat.add_zero,Rat.pow_zero,Rat.mul_one]
  | succ k ih => rw [show n+(k+1)=(n+k)+1 by omega,Rat.pow_succ,ih,Rat.pow_succ]; grind only

theorem Chart.parameter_error (A : Chart) (n : Nat) :
    A.parameterLip*((1 : Rat)/2)^(n+A.sampleShift) ≤ ((1 : Rat)/2)^n := by
  rw [pow_addition]
  have h := Rat.mul_le_mul_of_nonneg_right A.sampleShift_spec
    (Rat.pow_nonneg (by decide +kernel : (0 : Rat) ≤ 1/2) (n := n))
  grind only

theorem Chart.polynomial_tail (A : Chart) {s x : Rat}
    (hs : qabs (2-s) ≤ (A.order : Rat)) (hx0 : 0 ≤ x) (hx : x ≤ A.radius)
    {n K : Nat} (hK : A.cutoff n ≤ K) :
    qabs (powerPolynomial s K x-powerPolynomial s (A.cutoff n) x) ≤ ((1 : Rat)/2)^n := by
  have h := compact_polynomial_tail hs A.ratio_bounds.1 (Rat.le_of_lt A.ratio_bounds.2)
    (Rat.le_of_lt A.outer_pos) A.outer_lt hx0 (by rw [A.ratio_outer]; exact hx)
    (A.cutoff n) (K-A.cutoff n)
  rw [Nat.add_sub_of_le hK] at h
  have hn := A.cutoff_spec n
  change _ ≤ A.ratio^(A.cutoff n)*A.tailBound at h
  grind only

theorem Chart.polynomial_parameter (A : Chart) {s t x : Rat}
    (hs : qabs (2-s) ≤ (A.order : Rat)) (ht : qabs (2-t) ≤ (A.order : Rat))
    (hx0 : 0 ≤ x) (hx : x ≤ A.radius) (K : Nat) :
    qabs (powerPolynomial s K x-powerPolynomial t K x) ≤ A.parameterLip*qabs (s-t) :=
  compact_parameter_lipschitz hs ht hx0 hx A.belowOne K

end ComputableAnalysis.BinomialPower.Global
