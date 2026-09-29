import ComputableAnalysis.PowerCompactIntegral

/-! Finite estimates at the singular endpoint. All sums in this module are
finite; neither an improper integral nor a series test is a premise. -/
namespace ComputableAnalysis.BinomialPower
open FormalPowerSeries ZetaReal Integral FinitePolynomial

theorem chart_gap {q m : Nat} {s : Rat} (hs : InChart q m s) :
    1 ≤ (s-1)*((q : Rat)+1) := by
  have hq := Rat.natCast_nonneg (a := q)
  have hi := Rat.mul_inv_cancel ((q : Rat)+1) (by grind)
  have h := Rat.mul_le_mul_of_nonneg_right hs.1 (show 0 ≤ (q : Rat)+1 by grind)
  simp only [Rat.div_def] at h
  grind only

theorem integrated_term_bound {q m k : Nat} {s z : Rat}
    (hs : InChart q m s) (hk : m+1 ≤ k) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    qabs (coefficient s k*z^(k+1)/((k : Rat)+1)) ≤
      ((q : Rat)+1)*(magnitude s k-magnitude s (k+1)) := by
  have hn := Rat.natCast_nonneg (a := k)
  have hq := Rat.natCast_nonneg (a := q)
  have hi := Rat.mul_inv_cancel ((k : Rat)+1) (by grind)
  have hinv := Rat.le_of_lt (Rat.inv_pos.mpr (show 0 < (k : Rat)+1 by grind))
  have hp := Rat.pow_nonneg hz (n := k+1)
  have hpow : z^(k+1) ≤ 1 := by
    have h := pow_antitone_exponent hz hz1 (show 0 ≤ k+1 by omega)
    simpa only [Rat.pow_zero] using h
  have hmul := Rat.mul_le_mul_of_nonneg_left hpow (magnitude_nonneg s k)
  have hgap := Rat.mul_le_mul_of_nonneg_right (chart_gap hs) (magnitude_nonneg s k)
  have hd := magnitude_difference hs.2 hk
  rw [Rat.div_def,qabs_mul,qabs_mul,qabs_eq_self_of_nonneg hp,qabs_eq_self_of_nonneg hinv]
  apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) ?_ (by grind)
  change ((k : Rat)+1)*(magnitude s k*z^(k+1)*((k : Rat)+1)⁻¹) ≤ _
  have hc : ((k : Rat)+1)*(magnitude s k*z^(k+1)*((k : Rat)+1)⁻¹)=magnitude s k*z^(k+1) := by
    rw [Rat.mul_comm (magnitude s k*z^(k+1)) _,← Rat.mul_assoc,hi,Rat.one_mul]
  rw [hc]
  have hh := congrArg (fun x : Rat => x*((q : Rat)+1)) hd
  grind only

/-- Uniform weighted tails, including the boundary point `z=1`. -/
theorem integrated_endpoint_tail {q m K : Nat} {s z : Rat}
    (hs : InChart q m s) (hK : m+1 ≤ K) (hz : 0 ≤ z) (hz1 : z ≤ 1) (d : Nat) :
    qabs (integratedPowerPolynomial s (K+d) z-integratedPowerPolynomial s K z) ≤
      ((q : Rat)+1)*magnitude s K := by
  have ht (n : Nat) :
      qabs (integratedPowerPolynomial s (K+n) z-integratedPowerPolynomial s K z) ≤
        ((q : Rat)+1)*(magnitude s K-magnitude s (K+n)) := by
    induction n with
    | zero =>
      simp only [Nat.add_zero,Rat.sub_self,Rat.mul_zero]
      decide +kernel
    | succ n ih =>
      have h := integrated_term_bound hs (show m+1 ≤ K+n by omega) hz hz1
      have he : integratedPowerPolynomial s (K+(n+1)) z-integratedPowerPolynomial s K z =
          (integratedPowerPolynomial s (K+n) z-integratedPowerPolynomial s K z)+
            coefficient s (K+n)*z^(K+n+1)/(((K+n : Nat) : Rat)+1) := by
        unfold integratedPowerPolynomial
        rw [show K+(n+1)=(K+n)+1 by omega,sumBelow_succ]
        grind only
      rw [he]
      have htri := qabs_add_le (integratedPowerPolynomial s (K+n) z-integratedPowerPolynomial s K z)
        (coefficient s (K+n)*z^(K+n+1)/(((K+n : Nat) : Rat)+1))
      rw [show K+(n+1)=K+n+1 by omega]
      grind only
  have h := ht d
  have hq := Rat.natCast_nonneg (a := q)
  have hnon := Rat.mul_nonneg (show 0 ≤ (q : Rat)+1 by grind) (magnitude_nonneg s (K+d))
  grind only

theorem integrated_at_one {q m : Nat} {s : Rat} (hs : InChart q m s) (K : Nat) :
    qabs (integratedPowerPolynomial s K 1-1/(s-1)) ≤ ((q : Rat)+1)*magnitude s K := by
  have hone (j : Nat) : (1 : Rat)^j=1 := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Rat.pow_succ,ih,Rat.one_mul]
  have he := integratedPowerPolynomial_identity s 1 K
  have hp := powerPolynomial_parameter_succ s 1 K
  rw [hone K] at hp
  have hspos : 0 < s-1 := by have := chart_gt_one hs; grind
  have hi := Rat.mul_inv_cancel (s-1) (Rat.ne_of_gt hspos)
  have hid : (s-1)*(integratedPowerPolynomial s K 1-1/(s-1))= -coefficient s K := by
    simp only [Rat.div_def] at *
    grind only
  have habs := congrArg qabs hid
  rw [qabs_mul,qabs_eq_self_of_nonneg (Rat.le_of_lt hspos),qabs_neg] at habs
  have h := Rat.mul_le_mul_of_nonneg_right (chart_gap hs) (magnitude_nonneg s K)
  apply Rat.le_of_mul_le_mul_left (c := s-1) ?_ hspos
  change (s-1)*qabs (integratedPowerPolynomial s K 1-1/(s-1)) ≤ _
  change 1*magnitude s K ≤ _ at h
  unfold magnitude at h ⊢
  grind only

theorem polynomial_chart_bound {q m : Nat} {s z : Rat}
    (hs : InChart q m s) (hz : 0 ≤ z) (hz1 : z ≤ 1) (K : Nat) :
    qabs (powerPolynomial s K z) ≤ (K : Rat)*bound m := by
  induction K with
  | zero =>
      simp only [powerPolynomial,sumBelow_zero]
      have hn : ((0 : Nat) : Rat)=0 := by decide
      rw [hn,Rat.zero_mul]
      decide +kernel
  | succ K ih =>
    have hp := Rat.pow_nonneg hz (n := K)
    have hp1 : z^K ≤ 1 := by simpa only [Rat.pow_zero] using pow_antitone_exponent hz hz1 (Nat.zero_le K)
    have h1 := Rat.mul_le_mul_of_nonneg_left hp1 (magnitude_nonneg s K)
    have h2 := magnitude_bound hs K
    have ht := qabs_add_le (powerPolynomial s K z) (coefficient s K*z^K)
    rw [qabs_mul,qabs_eq_self_of_nonneg hp] at ht
    unfold powerPolynomial at *
    rw [sumBelow_succ]
    simp only [Rat.natCast_add]
    unfold magnitude at h1 h2
    grind only

theorem integrated_endpoint_variation {q m : Nat} {s z : Rat}
    (hs : InChart q m s) (hz : 0 ≤ z) (hz1 : z ≤ 1) (K : Nat) :
    qabs (integratedPowerPolynomial s K 1-integratedPowerPolynomial s K z) ≤
      (1-z)*((K : Rat)*bound m) := by
  have h := polynomial_integral_bound (coefficient s) (fun _ => 0) K 0 (e := (K : Rat)*bound m) hz hz1 (Rat.le_refl) (by
    intro x hx hx1
    have h := polynomial_chart_bound hs (Rat.le_trans hz hx) hx1 K
    rw [sumBelow_zero]
    change qabs (powerPolynomial s K x-0) ≤ _
    rw [show powerPolynomial s K x-0=powerPolynomial s K x by grind only]
    exact h)
  rw [Global.integrated_prefix_eq,Global.integrated_prefix_eq] at h
  change qabs ((integratedPowerPolynomial s K 1-integratedPowerPolynomial s K z)-(0-0)) ≤ _ at h
  have he : (integratedPowerPolynomial s K 1-integratedPowerPolynomial s K z)-(0-0)=
    integratedPowerPolynomial s K 1-integratedPowerPolynomial s K z := by grind only
  rw [he] at h
  exact h

def endpointCutoff (m j : Nat) : Rat :=
  ((1 : Rat)/2)^j/(1+(cutoff m j : Rat)*bound m)

def endpointError (q m j : Nat) : Rat :=
  2*((q : Rat)+1)*bound m*(ratio q)^j+((1 : Rat)/2)^j

theorem bound_nonneg (m : Nat) : 0 ≤ bound m :=
  Rat.pow_nonneg (by have := Rat.natCast_nonneg (a := m); grind)

theorem endpointCutoff_bounds (m j : Nat) : 0 < endpointCutoff m j ∧ endpointCutoff m j ≤ 1 := by
  have hn := Rat.natCast_nonneg (a := cutoff m j)
  have hprod := Rat.mul_nonneg hn (bound_nonneg m)
  have hp := Rat.pow_pos (by decide +kernel : (0 : Rat) < 1/2) (n := j)
  have hp1 : ((1 : Rat)/2)^j ≤ 1 := by
    simpa only [Rat.pow_zero] using pow_antitone_exponent (by decide +kernel : (0 : Rat) ≤ 1/2)
      (by decide +kernel : (1 : Rat)/2 ≤ 1) (Nat.zero_le j)
  have hi := Rat.mul_inv_cancel (1+(cutoff m j : Rat)*bound m) (by grind)
  have hinv := Rat.inv_pos.mpr (show 0 < 1+(cutoff m j : Rat)*bound m by grind)
  unfold endpointCutoff
  rw [Rat.div_def]
  constructor
  · exact Rat.mul_pos hp hinv
  · apply Rat.le_of_mul_le_mul_right (c := 1+(cutoff m j : Rat)*bound m) ?_ (by grind)
    rw [Rat.mul_assoc, Rat.inv_mul_cancel _ (by grind : 1+(cutoff m j : Rat)*bound m ≠ 0),Rat.mul_one]
    grind only

/-- An explicit finite polynomial error at a computable endpoint approaching zero. -/
theorem integrated_endpoint_error_le_cutoff {q m : Nat} {s : Rat}
    (hs : InChart q m s) (j L : Nat) (hL : cutoff m j ≤ L) {a : Rat}
    (ha0 : 0 ≤ a) (hac : a ≤ endpointCutoff m j) :
    qabs (integratedPowerPolynomial s L (1-a)-1/(s-1)) ≤ endpointError q m j := by
  let K := cutoff m j
  have hcut := endpointCutoff_bounds m j
  have ha : 0 ≤ a ∧ a ≤ 1 := ⟨ha0,Rat.le_trans hac hcut.2⟩
  have ht := integrated_endpoint_tail hs (cutoff_ge m j)
    (show 0 ≤ 1-a by grind) (show 1-a ≤ 1 by grind) (L-K)
  rw [show cutoff m j+(L-K)=L by dsimp [K]; omega] at ht
  have ho := integrated_at_one hs K
  have hv := integrated_endpoint_variation hs (show 0 ≤ 1-a by grind)
    (show 1-a ≤ 1 by grind) K
  have he := magnitude_decay hs j
  have hq := Rat.natCast_nonneg (a := q)
  have hh := Rat.mul_le_mul_of_nonneg_left he (show 0 ≤ (q : Rat)+1 by grind)
  have hprod := Rat.mul_nonneg (Rat.natCast_nonneg (a := K)) (bound_nonneg m)
  have hi := Rat.mul_inv_cancel (1+(K : Rat)*bound m) (by grind)
  have hsmallCut : endpointCutoff m j*((K : Rat)*bound m) ≤ ((1 : Rat)/2)^j := by
    have hpow := Rat.pow_nonneg (by decide +kernel : (0 : Rat) ≤ 1/2) (n := j)
    have hinv := Rat.le_of_lt (Rat.inv_pos.mpr (show 0 < 1+(K : Rat)*bound m by grind))
    have hnon := Rat.mul_nonneg hpow hinv
    dsimp [endpointCutoff]
    rw [Rat.div_def]
    change ((1 : Rat)/2)^j*(1+(K : Rat)*bound m)⁻¹*((K : Rat)*bound m) ≤ _
    have heq : ((1 : Rat)/2)^j*(1+(K : Rat)*bound m)⁻¹*(1+(K : Rat)*bound m)=((1 : Rat)/2)^j := by
      rw [Rat.mul_assoc,Rat.inv_mul_cancel _ (by grind : 1+(K : Rat)*bound m ≠ 0),Rat.mul_one]
    have hmul := Rat.mul_le_mul_of_nonneg_left (show (K : Rat)*bound m ≤ 1+(K : Rat)*bound m by grind) hnon
    rw [heq] at hmul
    exact hmul
  have hsmall := Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hac hprod) hsmallCut
  have htri1 := qabs_add_le (integratedPowerPolynomial s L (1-a)-integratedPowerPolynomial s K (1-a))
    (integratedPowerPolynomial s K (1-a)-integratedPowerPolynomial s K 1)
  have htri2 := qabs_add_le (integratedPowerPolynomial s L (1-a)-integratedPowerPolynomial s K 1)
    (integratedPowerPolynomial s K 1-1/(s-1))
  rw [show integratedPowerPolynomial s K (1-a)-integratedPowerPolynomial s K 1=
    -(integratedPowerPolynomial s K 1-integratedPowerPolynomial s K (1-a)) by grind only,qabs_neg] at htri1
  rw [show (integratedPowerPolynomial s L (1-a)-integratedPowerPolynomial s K (1-a))+
    (-(integratedPowerPolynomial s K 1-integratedPowerPolynomial s K (1-a)))=
      integratedPowerPolynomial s L (1-a)-integratedPowerPolynomial s K 1 by grind only] at htri1
  rw [show (integratedPowerPolynomial s L (1-a)-integratedPowerPolynomial s K 1)+
    (integratedPowerPolynomial s K 1-1/(s-1))=integratedPowerPolynomial s L (1-a)-1/(s-1) by grind only] at htri2
  change qabs (integratedPowerPolynomial s L (1-a)-1/(s-1)) ≤ _
  unfold endpointError
  change magnitude s K ≤ _ at he
  change ((q : Rat)+1)*magnitude s K ≤ _ at hh
  grind only

theorem integrated_endpoint_error {q m : Nat} {s : Rat}
    (hs : InChart q m s) (j L : Nat) (hL : cutoff m j ≤ L) :
    qabs (integratedPowerPolynomial s L (1-endpointCutoff m j)-1/(s-1)) ≤ endpointError q m j :=
  integrated_endpoint_error_le_cutoff hs j L hL (Rat.le_of_lt (endpointCutoff_bounds m j).1) (Rat.le_refl)

end ComputableAnalysis.BinomialPower
