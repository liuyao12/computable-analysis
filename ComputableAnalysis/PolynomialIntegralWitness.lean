import ComputableAnalysis.GeometricIntegral
import ComputableAnalysis.IntegralUniformApproximation

/-! Exact compact polynomial integrals with actual rectangle witnesses.
These are used as independent finite approximants to noninteger powers. -/
namespace ComputableAnalysis.FormalPowerSeries
open Integral FinitePolynomial

def truncateCoefficient (c : Coeffs) (N k : Nat) : Rat := if k<N then c k else 0

def polynomialMajorant (c : Coeffs) (N : Nat) : Rat :=
  sumBelow (fun k => qabs (c k)*(2 : Rat)^k) N

private theorem positive_sum (f : Nat → Rat) (hf : ∀ k, 0 ≤ f k) (N : Nat) :
    0 ≤ sumBelow f N := by
  induction N with
  | zero => exact Rat.le_refl
  | succ N ih => rw [sumBelow_succ]; exact Rat.add_nonneg ih (hf N)

private theorem positive_term_le_sum (f : Nat → Rat) (hf : ∀ k, 0 ≤ f k) {N k : Nat} (hk : k<N) :
    f k ≤ sumBelow f N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [sumBelow_succ]
    by_cases he : k=N
    · subst k; have := positive_sum f hf N; grind only
    · have := ih (by omega)
      have := hf N
      grind only

theorem polynomialMajorant_nonneg (c : Coeffs) (N : Nat) : 0 ≤ polynomialMajorant c N :=
  positive_sum _ (fun k => Rat.mul_nonneg (qabs_nonneg (c k)) (Rat.pow_nonneg (by decide) (n := k))) N

theorem truncateCoefficient_bound (c : Coeffs) (N k : Nat) :
    qabs (truncateCoefficient c N k) ≤ polynomialMajorant c N*((1 : Rat)/2)^k := by
  have hp := Rat.pow_nonneg (by decide +kernel : (0 : Rat) ≤ 1/2) (n := k)
  by_cases hk : k<N
  · have h := positive_term_le_sum (fun j => qabs (c j)*(2 : Rat)^j)
      (fun j => Rat.mul_nonneg (qabs_nonneg (c j)) (Rat.pow_nonneg (by decide) (n := j))) hk
    have hm := Rat.mul_le_mul_of_nonneg_right h hp
    have hpow : (2 : Rat)^k*((1 : Rat)/2)^k=1 := by
      rw [pow_product,show (2 : Rat)*(1/2)=1 by decide +kernel]
      have hone (j : Nat) : (1 : Rat)^j=1 := by
        induction j with
        | zero => rfl
        | succ j ih => rw [Rat.pow_succ,ih,Rat.mul_one]
      exact hone k
    have he : qabs (c k)*2^k*((1 : Rat)/2)^k=qabs (c k) := by grind only
    rw [he] at hm
    simpa only [truncateCoefficient,if_pos hk,polynomialMajorant] using hm
  · rw [truncateCoefficient,if_neg hk,qabs_eq_self_of_nonneg (Rat.le_refl : (0 : Rat) ≤ 0)]
    exact Rat.mul_nonneg (polynomialMajorant_nonneg c N) hp

theorem truncate_prefix (c : Coeffs) (N K : Nat) (hNK : N ≤ K) (x : Rat) :
    sumBelow (fun k => truncateCoefficient c N k*x^k) K=sumBelow (fun k => c k*x^k) N := by
  have hbase : sumBelow (fun k => truncateCoefficient c N k*x^k) N=sumBelow (fun k => c k*x^k) N := by
    apply sumBelow_congr
    intro k hk
    rw [truncateCoefficient,if_pos hk]
  induction hNK with
  | refl => exact hbase
  | @step K hNK ih =>
    have hz : truncateCoefficient c N K=0 := by unfold truncateCoefficient; exact if_neg (Nat.not_lt_of_ge hNK)
    rw [sumBelow_succ,ih,hz,Rat.zero_mul,Rat.add_zero]

theorem truncate_integral (c : Coeffs) (N K : Nat) (hNK : N ≤ K) (x : Rat) :
    integratedTaylorPrefix (truncateCoefficient c N) K x=integratedTaylorPrefix c N x := by
  have hbase (j : Nat) (hj : j ≤ N) :
      integratedTaylorPrefix (truncateCoefficient c N) j x=integratedTaylorPrefix c j x := by
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [integratedTaylorPrefix]
      rw [ih (by omega)]
      have hz : truncateCoefficient c N j=c j := by unfold truncateCoefficient; exact if_pos (by omega)
      rw [hz]
  induction hNK with
  | refl => exact hbase N (Nat.le_refl N)
  | @step K hNK ih =>
    simp only [integratedTaylorPrefix]
    rw [ih]
    have hz : truncateCoefficient c N K=0 := by unfold truncateCoefficient; exact if_neg (Nat.not_lt_of_ge hNK)
    rw [hz,Rat.zero_mul,Rat.add_zero]

/-- An exact finite polynomial, as a function on the supplied segment. -/
def polynomialFunction (c : Coeffs) (N : Nat) (a b : Rat) : FunctionOnInterval :=
  onInterval (fun x => RealRaw.ofRat (sumBelow (fun k => c k*x^k) N)) a b
    (fun x _ => RealRaw.ofRat_valid _)

/-- Constructed exact compact integral witnesses for all signed rational
polynomials, with arbitrary coefficients and any segment in the unit interval. -/
theorem polynomial_hasIntegral (c : Coeffs) (N : Nat) {a b : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    HasIntegral (polynomialFunction c N a b)
      (RealRaw.ofRat (integratedTaylorPrefix c N b-integratedTaylorPrefix c N a)) := by
  let d := truncateCoefficient c N
  let M := polynomialMajorant c N
  have hM : 0 ≤ M := polynomialMajorant_nonneg c N
  have hd : ∀ k, qabs (d k) ≤ M*((1 : Rat)/2)^k := truncateCoefficient_bound c N
  have valid (x : Rat) (hx : a ≤ x ∧ x ≤ b) : (geometricRaw d M x).Valid :=
    geometricRaw_valid hM (R := 1/2) (by decide +kernel) hd
      (by rw [qabs_eq_self_of_nonneg (by grind)]; grind)
  apply hasIntegral_of_uniform_approximation
    (g := fun _ x => geometricRaw d M x) (hg := fun _ => valid)
    (J := fun _ => geometricIntegral d M a b) (e := fun _ => 0)
    hab (RealRaw.ofRat_valid _)
  · intro n; exact geometricIntegral_hasIntegral hM hd ha hab hb
  · intro eps; exact ⟨0,fun _ _ => Rat.le_of_lt eps.property⟩
  · intro n x hx i j
    have h := geometricRaw_contains_prefix hM (R := 1/2) (by decide +kernel) hd
      (x := x) (by rw [qabs_eq_self_of_nonneg (by grind)]; grind) (Nat.le_max_left j N)
    change _ ≤ sumBelow (fun k => truncateCoefficient c N k*x^k) (max j N) ∧ _ ≤ _ at h
    rw [truncate_prefix c N (max j N) (Nat.le_max_right _ _) x] at h
    change sumBelow (fun k => c k*x^k) N ≤ _+0 ∧ _ ≤ sumBelow (fun k => c k*x^k) N+0
    constructor <;> grind only
  · intro n i j
    let K := max j N
    have ends (x : Rat) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :=
      geometricRaw_contains_prefix (c := integralCoefficient d) (M := 2*M) (R := 1/2)
        (by grind) (by decide +kernel) (integralCoefficient_bound hM hd)
        (x := x) (by rw [qabs_eq_self_of_nonneg hx0]; grind : (1 : Rat)/2*qabs x ≤ 1/2)
        (show j ≤ K+1 by dsimp [K]; omega)
    have ea := ends a ha (by grind)
    have eb := ends b (by grind) hb
    rw [integral_prefix] at ea eb
    change _ ≤ integratedTaylorPrefix (truncateCoefficient c N) K a ∧ _ ≤ _ at ea
    change _ ≤ integratedTaylorPrefix (truncateCoefficient c N) K b ∧ _ ≤ _ at eb
    rw [truncate_integral c N K (by dsimp [K]; omega) a] at ea
    rw [truncate_integral c N K (by dsimp [K]; omega) b] at eb
    change integratedTaylorPrefix c N b-integratedTaylorPrefix c N a ≤
      ((geometricRaw (integralCoefficient d) (2*M) b).compute j).hi-
        ((geometricRaw (integralCoefficient d) (2*M) a).compute j).lo+0 ∧
      ((geometricRaw (integralCoefficient d) (2*M) b).compute j).lo-
        ((geometricRaw (integralCoefficient d) (2*M) a).compute j).hi ≤
      integratedTaylorPrefix c N b-integratedTaylorPrefix c N a+0
    constructor <;> grind only

end ComputableAnalysis.FormalPowerSeries
