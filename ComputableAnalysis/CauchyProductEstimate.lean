import ComputableAnalysis.GeometricSeriesCalculus

namespace ComputableAnalysis.FormalPowerSeries

theorem pow_sum (x : Rat) (m n : Nat) : x^(m+n)=x^m*x^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show m+(n+1)=(m+n)+1 by omega, Rat.pow_succ, ih, Rat.pow_succ]
      grind

theorem sumBelow_split (f : Nat → Rat) (m n : Nat) :
    sumBelow f (m+n)=sumBelow f m+sumBelow (fun k => f (m+k)) n := by
  induction n with
  | zero => simp; grind
  | succ n ih =>
      rw [show m+(n+1)=(m+n)+1 by omega, sumBelow_succ, ih, sumBelow_succ]
      grind

/-- Exact finite triangular rearrangement; no infinite sums occur. -/
theorem cauchy_triangle (a b : Coeffs) (N : Nat) :
    sumBelow (cauchyProduct a b) N = sumBelow (fun k => b k*sumBelow a (N-k)) N := by
  induction N with
  | zero => rfl
  | succ n ih =>
      rw [sumBelow_succ, ih, sumBelow_succ]
      have he : sumBelow (fun k => b k*sumBelow a (n+1-k)) n =
          sumBelow (fun k => b k*sumBelow a (n-k)) n+
            sumBelow (fun k => b k*a (n-k)) n := by
        rw [← sumBelow_add]
        apply sumBelow_congr
        intro k hk
        rw [show n+1-k=(n-k)+1 by omega, sumBelow_succ]
        grind
      rw [he, cauchyProduct_split]
      have hc : sumBelow (fun k => b k*a (n-k)) n = sumBelow (fun k => a (n-k)*b k) n := by
        apply sumBelow_congr
        intro k _
        grind
      rw [hc]
      have hOne : sumBelow a 1=a 0 := by
        rw [show 1=0+1 by rfl, sumBelow_succ, sumBelow_zero]
        grind
      rw [show n+1-n=1 by omega, hOne]
      grind

theorem cauchy_terms (a b : Coeffs) (x : Rat) (n : Nat) :
    cauchyProduct (fun k => a k*x^k) (fun k => b k*x^k) n =
      cauchyProduct a b n*x^n := by
  unfold cauchyProduct
  have hmul := sumBelow_mul (x^n) (fun k => a (n-k)*b k) (n+1)
  rw [Rat.mul_comm, ← hmul]
  apply sumBelow_congr
  intro k hk
  have hp : x^(n-k)*x^k=x^n := by rw [← pow_sum, show n-k+k=n by omega]
  grind

/-- The finite product differs from the triangular coefficient sum only
by an explicitly controlled corner. -/
theorem cauchy_prefix_error {a b : Coeffs} {M : Rat}
    (hM : 0 ≤ M)
    (ha : ∀ n, qabs (a n) ≤ M*((1 : Rat)/8)^n)
    (hb : ∀ n, qabs (b n) ≤ M*((1 : Rat)/8)^n) (N : Nat) :
    qabs (sumBelow a N*sumBelow b N-sumBelow (cauchyProduct a b) N) ≤
      M*M*((1 : Rat)/2)^N := by
  rw [cauchy_triangle]
  have he : sumBelow a N*sumBelow b N-
      sumBelow (fun k => b k*sumBelow a (N-k)) N =
      sumBelow (fun k => b k*(sumBelow a N-sumBelow a (N-k))) N := by
    have h1 := sumBelow_mul (sumBelow a N) b N
    have h2 := sumBelow_add (fun k => b k*(sumBelow a N-sumBelow a (N-k)))
      (fun k => b k*sumBelow a (N-k)) N
    have heq : (fun k => b k*(sumBelow a N-sumBelow a (N-k))+b k*sumBelow a (N-k)) =
        (fun k => sumBelow a N*b k) := by funext k; grind
    rw [heq, h1] at h2
    grind
  rw [he]
  have hterm (k : Nat) (hk : k<N) :
      qabs (b k*(sumBelow a N-sumBelow a (N-k))) ≤
        (N : Rat)*M*M*((1 : Rat)/8)^N := by
    have hs : sumBelow a N-sumBelow a (N-k) = sumBelow (fun j => a (N-k+j)) k := by
      have he := sumBelow_split a (N-k) k
      rw [show N-k+k=N by omega] at he
      grind
    have hs' : b k*sumBelow (fun j => a (N-k+j)) k =
        sumBelow (fun j => b k*a (N-k+j)) k := (sumBelow_mul _ _ _).symm
    rw [hs, hs']
    have hbnd (j : Nat) (_hj : j<k) :
        qabs (b k*a (N-k+j)) ≤ M*M*((1 : Rat)/8)^N := by
      have h1 := Rat.mul_le_mul_of_nonneg_right (hb k) (qabs_nonneg (a (N-k+j)))
      have h2 := Rat.mul_le_mul_of_nonneg_left (ha (N-k+j))
        (Rat.mul_nonneg hM (Rat.pow_nonneg (n := k) (by decide +kernel : (0 : Rat) ≤ 1/8)))
      have hp : ((1 : Rat)/8)^k*((1 : Rat)/8)^(N-k+j)=((1 : Rat)/8)^N*((1 : Rat)/8)^j := by
        rw [← pow_sum, ← pow_sum, show k+(N-k+j)=N+j by omega]
      have hj : ((1 : Rat)/8)^j ≤ 1 := by
        clear h1 h2 hp
        induction j with
        | zero => simp
        | succ j ih => rw [Rat.pow_succ]; grind
      have hn0 : 0 ≤ M*M*((1 : Rat)/8)^N :=
        Rat.mul_nonneg (Rat.mul_nonneg hM hM) (Rat.pow_nonneg (by decide +kernel))
      have h3 := Rat.mul_le_mul_of_nonneg_left hj hn0
      rw [qabs_mul]
      have heq : (M*((1 : Rat)/8)^k)*(M*((1 : Rat)/8)^(N-k+j)) =
          M*M*(((1 : Rat)/8)^k*((1 : Rat)/8)^(N-k+j)) := by grind
      rw [heq, hp] at h2
      grind only
    have hbnd' := sumBelow_abs_le hbnd
    have hkn : (k : Rat) ≤ (N : Rat) := by exact_mod_cast (show k ≤ N by omega)
    have hm := Rat.mul_le_mul_of_nonneg_right hkn
      (Rat.mul_nonneg (Rat.mul_nonneg hM hM) (Rat.pow_nonneg (n := N) (by decide +kernel : (0 : Rat) ≤ 1/8)))
    grind only
  have hs := sumBelow_abs_le hterm
  have hn := nat_succ_le_two_pow N
  have hn0 : (0 : Rat) ≤ (N : Rat) := Rat.natCast_nonneg
  have hpow : 0 ≤ (2 : Rat)^N := Rat.pow_nonneg (by decide)
  have hN1 := Rat.mul_le_mul_of_nonneg_right (show (N : Rat) ≤ (2 : Rat)^N by simp only [Rat.natCast_add] at hn; grind) hn0
  have hN2 := Rat.mul_le_mul_of_nonneg_left (show (N : Rat) ≤ (2 : Rat)^N by simp only [Rat.natCast_add] at hn; grind) hpow
  have hprod : (2 : Rat)^N*2^N*((1 : Rat)/8)^N=((1 : Rat)/2)^N := by
    rw [pow_product, pow_product]
    congr 1
    decide +kernel
  have hN : (N : Rat)*(N : Rat) ≤ (2 : Rat)^N*2^N := by grind
  have hm := Rat.mul_le_mul_of_nonneg_right hN
    (Rat.mul_nonneg (Rat.mul_nonneg hM hM) (Rat.pow_nonneg (n := N) (by decide +kernel : (0 : Rat) ≤ 1/8)))
  have heq : (2 : Rat)^N*2^N*(M*M*((1 : Rat)/8)^N) = M*M*((1 : Rat)/2)^N := by
    rw [← hprod]; grind
  rw [heq] at hm
  grind only

end ComputableAnalysis.FormalPowerSeries
