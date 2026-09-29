import ComputableAnalysis.BinomialPowerPolynomial

/-! Uniform binomial bounds on every compact subinterval of the positive
base domain. Integer reciprocal powers provide finite majorants; no infinite
series test or improper integral is used. -/
namespace ComputableAnalysis.BinomialPower
open FormalPowerSeries ZetaReal

def majorant (m : Nat) (k : Nat) : Rat := coefficient (2-(m : Rat)) k

theorem majorant_step (m k : Nat) :
    ((k : Rat)+1)*majorant m (k+1)=((k : Rat)+(m : Rat))*majorant m k := by
  have h := coefficient_step (2-(m : Rat)) k
  unfold majorant
  grind only

theorem majorant_nonneg (m k : Nat) : 0 ≤ majorant m k := by
  induction k with
  | zero => exact (by decide : (0 : Rat) ≤ 1)
  | succ k ih =>
    have h := majorant_step m k
    have hk := Rat.natCast_nonneg (a := k)
    have hm := Rat.natCast_nonneg (a := m)
    have hh := Rat.mul_nonneg (show 0 ≤ (k : Rat)+(m : Rat) by grind) ih
    apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) ?_ (by grind)
    grind only

theorem majorant_mono (m k : Nat) : majorant m k ≤ majorant (m+1) k := by
  induction k with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have h1 := majorant_step m k
    have h2 := majorant_step (m+1) k
    have hm := Rat.natCast_nonneg (a := m)
    have hk := Rat.natCast_nonneg (a := k)
    have hmul := Rat.mul_le_mul_of_nonneg_left ih (show 0 ≤ (k : Rat)+(m : Rat) by grind)
    have hpos := majorant_nonneg (m+1) k
    simp only [Rat.natCast_add] at h2
    apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) ?_ (by grind)
    grind only

theorem coefficient_majorant {s : Rat} {m : Nat} (hs : qabs (2-s) ≤ (m : Rat)) (k : Nat) :
    qabs (coefficient s k) ≤ majorant m k := by
  induction k with
  | zero => change qabs (1 : Rat) ≤ 1; decide +kernel
  | succ k ih =>
    have hk := Rat.natCast_nonneg (a := k)
    have hm := Rat.natCast_nonneg (a := m)
    have ht := qabs_add_le (k : Rat) (2-s)
    rw [qabs_eq_self_of_nonneg hk] at ht
    have hfac : qabs ((k : Rat)+2-s) ≤ (k : Rat)+(m : Rat) := by
      rw [show (k : Rat)+2-s=(k : Rat)+(2-s) by grind only]
      grind only
    have he := congrArg qabs (coefficient_step s k)
    rw [qabs_mul,qabs_mul,qabs_eq_self_of_nonneg (by grind : 0 ≤ (k : Rat)+1)] at he
    have h1 := Rat.mul_le_mul_of_nonneg_right hfac (qabs_nonneg (coefficient s k))
    have h2 := Rat.mul_le_mul_of_nonneg_left ih (show 0 ≤ (k : Rat)+(m : Rat) by grind)
    have h3 := majorant_step m k
    apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) ?_ (by grind)
    grind only

theorem coefficient_parameter_majorant {s t : Rat} {m : Nat}
    (hs : qabs (2-s) ≤ (m : Rat)) (ht : qabs (2-t) ≤ (m : Rat)) (k : Nat) :
    qabs (coefficient s k-coefficient t k) ≤ majorant (m+1) k*qabs (s-t) := by
  induction k with
  | zero => simp [coefficient,majorant,qabs]; grind [qabs_nonneg]
  | succ k ih =>
    have hk := Rat.natCast_nonneg (a := k)
    have hm := Rat.natCast_nonneg (a := m)
    have hfac : qabs ((k : Rat)+2-s) ≤ (k : Rat)+(m : Rat) := by
      have h := qabs_add_le (k : Rat) (2-s)
      rw [qabs_eq_self_of_nonneg hk] at h
      rw [show (k : Rat)+2-s=(k : Rat)+(2-s) by grind only]
      grind only
    have he : ((k : Rat)+1)*(coefficient s (k+1)-coefficient t (k+1)) =
        ((k : Rat)+2-s)*(coefficient s k-coefficient t k)+coefficient t k*(t-s) := by
      have h1 := coefficient_step s k
      have h2 := coefficient_step t k
      grind only
    have ha := congrArg qabs he
    rw [qabs_mul,qabs_eq_self_of_nonneg (by grind : 0 ≤ (k : Rat)+1)] at ha
    have htri := qabs_add_le (((k : Rat)+2-s)*(coefficient s k-coefficient t k)) (coefficient t k*(t-s))
    simp only [qabs_mul] at htri
    rw [show qabs (t-s)=qabs (s-t) by rw [show t-s= -(s-t) by grind only,qabs_neg]] at htri
    have h1 := Rat.mul_le_mul_of_nonneg_right hfac (qabs_nonneg (coefficient s k-coefficient t k))
    have h2 := Rat.mul_le_mul_of_nonneg_left ih (show 0 ≤ (k : Rat)+(m : Rat) by grind)
    have h3 := Rat.mul_le_mul_of_nonneg_right (coefficient_majorant ht k) (qabs_nonneg (s-t))
    have h4 := Rat.mul_le_mul_of_nonneg_right (majorant_mono m k) (qabs_nonneg (s-t))
    have hstep := congrArg (fun a : Rat => a*qabs (s-t)) (majorant_step (m+1) k)
    simp only [Rat.natCast_add] at hstep
    apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) ?_ (by grind)
    grind only

theorem majorant_prefix_nonneg (m K : Nat) {z : Rat} (hz : 0 ≤ z) :
    0 ≤ powerPolynomial (2-(m : Rat)) K z := by
  induction K with
  | zero => exact Rat.le_refl
  | succ K ih =>
    have h := Rat.mul_nonneg (majorant_nonneg m K) (Rat.pow_nonneg hz (n := K))
    unfold powerPolynomial at *
    rw [sumBelow_succ]
    change 0 ≤ coefficient (2-(m : Rat)) K*z^K at h
    grind only

/-- Every finite positive majorant sum is bounded by a rational reciprocal
integer power. This precedes and justifies all ensuing infinite computations. -/
theorem majorant_prefix_bound (m K : Nat) {z : Rat} (hz : 0 ≤ z) (hz1 : z < 1) :
    powerPolynomial (2-(m : Rat)) K z ≤ ((1-z)⁻¹)^m := by
  induction m generalizing K with
  | zero =>
    cases K with
    | zero => simp only [powerPolynomial, sumBelow_zero, Rat.pow_zero]; decide
    | succ K =>
      have h := powerPolynomial_integer 0 (K+1) (by omega) z
      have hn0 : ((0 : Nat) : Rat)=0 := by decide
      rw [hn0] at h
      rw [hn0]
      change powerPolynomial (2-(0 : Rat)) (K+1) z ≤ (1-z)⁻¹^0
      rw [show (2 : Rat)-0=0+2 by grind, h]
      simp only [Rat.pow_zero]
      exact Rat.le_refl
  | succ m ih =>
    have h := powerPolynomial_parameter_succ (1-(m : Rat)) z K
    have hprev := ih (K+1)
    have hnon := Rat.mul_nonneg (majorant_nonneg (m+1) K) (Rat.pow_nonneg hz (n := K))
    have hs : 1-(m : Rat)+1=2-(m : Rat) := by grind only
    have hs' : 2-((m+1 : Nat) : Rat)=1-(m : Rat) := by simp only [Rat.natCast_add]; grind only
    rw [hs] at h
    rw [hs']
    change 0 ≤ coefficient (2-((m+1 : Nat) : Rat)) K*z^K at hnon
    rw [hs'] at hnon
    have hi := Rat.mul_inv_cancel (1-z) (by grind)
    have he : (1-z)*((1-z)⁻¹)^(m+1)=((1-z)⁻¹)^m := by rw [Rat.pow_succ]; grind only
    apply Rat.le_of_mul_le_mul_left (c := 1-z) ?_ (by grind)
    rw [he]
    grind only

/-- A uniform exponent modulus on any compact positive-base segment. -/
theorem compact_parameter_lipschitz {s t z rho : Rat} {m : Nat}
    (hs : qabs (2-s) ≤ (m : Rat)) (ht : qabs (2-t) ≤ (m : Rat))
    (hz : 0 ≤ z) (hzrho : z ≤ rho) (hrho : rho < 1) (K : Nat) :
    qabs (powerPolynomial s K z-powerPolynomial t K z) ≤
      ((1-rho)⁻¹)^(m+1)*qabs (s-t) := by
  have he : powerPolynomial s K z-powerPolynomial t K z =
      sumBelow (fun k => (coefficient s k-coefficient t k)*z^k) K := by
    induction K with
    | zero => change (0 : Rat)-0=0; grind
    | succ K ih => unfold powerPolynomial at *; rw [sumBelow_succ,sumBelow_succ,sumBelow_succ]; grind only
  rw [he]
  have habs := abs_sumBelow_le (fun k => (coefficient s k-coefficient t k)*z^k) K
  have hbound := sumBelow_le (f := fun k => qabs ((coefficient s k-coefficient t k)*z^k))
    (g := fun k => qabs (s-t)*(majorant (m+1) k*rho^k)) (n := K) (by
      intro k _
      rw [qabs_mul,qabs_eq_self_of_nonneg (Rat.pow_nonneg hz (n := k))]
      have h1 := Rat.mul_le_mul_of_nonneg_right (coefficient_parameter_majorant hs ht k)
        (Rat.pow_nonneg hz (n := k))
      have h2 := Rat.mul_le_mul_of_nonneg_left (pow_base_mono hz hzrho k)
        (Rat.mul_nonneg (majorant_nonneg (m+1) k) (qabs_nonneg (s-t)))
      grind only)
  rw [sumBelow_mul] at hbound
  have hlast := Rat.mul_le_mul_of_nonneg_left (majorant_prefix_bound (m+1) K (Rat.le_trans hz hzrho) hrho)
    (qabs_nonneg (s-t))
  change qabs (s-t)*sumBelow (fun k => majorant (m+1) k*rho^k) K ≤ _ at hlast
  grind only

theorem sumBelow_split_at (f : Nat → Rat) (n d : Nat) :
    sumBelow f (n+d)=sumBelow f n+sumBelow (fun k => f (n+k)) d := by
  induction d with
  | zero => simp only [Nat.add_zero,sumBelow_zero]; grind
  | succ d ih => rw [show n+(d+1)=(n+d)+1 by omega,sumBelow_succ,ih,sumBelow_succ]; grind only

theorem pow_antitone_exponent {q : Rat} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n K : Nat} (hnK : n ≤ K) :
    q^K ≤ q^n := by
  induction hnK with
  | refl => exact Rat.le_refl
  | @step K _ ih =>
    have h := Rat.mul_le_mul_of_nonneg_left hq1 (Rat.pow_nonneg hq0 (n := K))
    rw [Rat.pow_succ]
    grind only

/-- A compact geometric tail, obtained from a finite positive majorant at a
slightly larger argument. Its proof does not invoke any summability theorem. -/
theorem compact_polynomial_tail {s z q R : Rat} {m : Nat}
    (hs : qabs (2-s) ≤ (m : Rat))
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hz0 : 0 ≤ z) (hz : z ≤ q*R) (n d : Nat) :
    qabs (powerPolynomial s (n+d) z-powerPolynomial s n z) ≤
      q^n*((1-R)⁻¹)^m := by
  have he : powerPolynomial s (n+d) z-powerPolynomial s n z =
      sumBelow (fun j => coefficient s (n+j)*z^(n+j)) d := by
    unfold powerPolynomial
    rw [sumBelow_split_at]
    grind only
  rw [he]
  have ht (j : Nat) : qabs (coefficient s (n+j)*z^(n+j)) ≤
      q^n*(majorant m (n+j)*R^(n+j)) := by
    let k := n+j
    have h1 := Rat.mul_le_mul_of_nonneg_right (coefficient_majorant hs k)
      (Rat.pow_nonneg hz0 (n := k))
    have h2 := Rat.mul_le_mul_of_nonneg_left (pow_base_mono hz0 hz k) (majorant_nonneg m k)
    rw [← pow_product] at h2
    have h3 := Rat.mul_le_mul_of_nonneg_right (pow_antitone_exponent hq0 hq1 (show n ≤ k by dsimp [k]; omega))
      (Rat.mul_nonneg (majorant_nonneg m k) (Rat.pow_nonneg hR0 (n := k)))
    rw [qabs_mul,qabs_eq_self_of_nonneg (Rat.pow_nonneg hz0 (n := n+j))]
    change qabs (coefficient s k)*z^k ≤ q^n*(majorant m k*R^k)
    grind only
  have habs := abs_sumBelow_le (fun j => coefficient s (n+j)*z^(n+j)) d
  have hsum := sumBelow_le (fun j (_ : j<d) => ht j)
  rw [sumBelow_mul] at hsum
  have hsplit := sumBelow_split_at (fun k => majorant m k*R^k) n d
  have hnon := majorant_prefix_nonneg m n hR0
  have hbound := majorant_prefix_bound m (n+d) hR0 hR1
  change 0 ≤ sumBelow (fun k => majorant m k*R^k) n at hnon
  change sumBelow (fun k => majorant m k*R^k) (n+d) ≤ _ at hbound
  have htail : sumBelow (fun j => majorant m (n+j)*R^(n+j)) d ≤ ((1-R)⁻¹)^m := by grind only
  have hlast := Rat.mul_le_mul_of_nonneg_left htail (Rat.pow_nonneg hq0 (n := n))
  grind only

/-- A completely rational tail schedule exists for every strict geometric
ratio. Bernoulli's finite inequality supplies the termination bound. -/
theorem geometric_shrinks {q M : Rat} (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 ≤ M) :
    ShrinksToZero (fun n => M*q^n) := by
  have weighted (n : Nat) : q^n*(1+(n : Rat)*(1-q)) ≤ 1 := by
    induction n with
    | zero => simp only [Rat.pow_zero]; grind
    | succ n ih =>
      have hq := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hq1) (Rat.pow_nonneg hq0 (n := n))
      have hn := Rat.natCast_nonneg (a := n)
      have hsq := Rat.mul_nonneg (show 0 ≤ 1-q by grind) (show 0 ≤ 1-q by grind)
      have hterm := Rat.mul_nonneg (Rat.mul_nonneg (show 0 ≤ (n : Rat)+1 by grind) hsq) (Rat.pow_nonneg hq0 (n := n))
      rw [Rat.pow_succ]
      simp only [Rat.natCast_add]
      grind only
  intro eps
  have ht : 0 < eps.val*(1-q)/(M+1) := by
    rw [Rat.div_def]
    exact Rat.mul_pos (Rat.mul_pos eps.property (by grind)) (Rat.inv_pos.mpr (by grind))
  obtain ⟨N,hN⟩ := shrinksToZero_of_natOverSuccBound (C := 1)
    (width := fun n => 1/((n+1 : Nat) : Rat)) (fun _ => Rat.le_refl) ⟨_,ht⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hw := weighted n
  have he := hN n hn
  have hnp := Rat.natCast_nonneg (a := n)
  have hpow := Rat.pow_nonneg hq0 (n := n)
  have hdrop := Rat.mul_nonneg hq0 hpow
  have hcan := Rat.mul_inv_cancel (((n+1 : Nat) : Rat)) (by exact_mod_cast (show n+1 ≠ 0 by omega))
  have hi := Rat.mul_inv_cancel (M+1) (by grind)
  have he1 := Rat.mul_le_mul_of_nonneg_right he (show 0 ≤ M+1 by grind)
  have he2 := Rat.mul_le_mul_of_nonneg_right he1 (show 0 ≤ ((n+1 : Nat) : Rat) by exact_mod_cast (show 0 ≤ n+1 by omega))
  have hweighted : q^n*(((n+1 : Nat) : Rat)*(1-q)) ≤ 1 := by
    simp only [Rat.natCast_add]
    grind only
  have hproduct := Rat.mul_le_mul_of_nonneg_left he2 hpow
  have hupper := Rat.mul_le_mul_of_nonneg_left hweighted (Rat.le_of_lt eps.property)
  simp only [Rat.div_def,Rat.one_mul] at hproduct
  have hc1 : (((n+1 : Nat) : Rat)⁻¹)*(M+1)*((n+1 : Nat) : Rat)=M+1 := by grind only
  have hc2 : eps.val*(1-q)*(M+1)⁻¹*(M+1)*((n+1 : Nat) : Rat)=eps.val*((n+1 : Nat) : Rat)*(1-q) := by grind only
  rw [hc1,hc2] at hproduct
  grind only

end ComputableAnalysis.BinomialPower
