import ComputableAnalysis.Basel.EulerSieve

namespace ComputableAnalysis.Basel.EulerSieve
open DirichletSeries

 theorem weight_bounds {p : Nat} (hp : BasicPrime p) : 0≤weight p ∧ weight p≤1/4 := by
  have h4 : 4≤p*p := by have := Nat.mul_le_mul hp.1 hp.1; omega
  have he : weight p=1/((p*p:Nat):Rat) := by simp only [weight, Rat.natCast_mul]
  rw [he]
  constructor
  · exact Rat.le_of_lt (one_div_nat_pos (by omega))
  · have h := Series.one_div_nat_antitone_series (n:=4) (m:=p*p) (by omega) (by omega) h4
    exact h

 theorem coefficient_bounds {ps : List Nat} (hps : ∀p, p∈ps → BasicPrime p) :
    0<coefficient ps ∧ coefficient ps≤1 := by
  induction ps with
  | nil => simp only [coefficient]; constructor <;> decide
  | cons p ps ih =>
    have hp := weight_bounds (hps p (by simp))
    have ht := ih (by intro q hq; exact hps q (by simp [hq]))
    have hpos : 0<1-weight p := by grind only [Rat.div_def]
    have hle : 1-weight p≤1 := by grind only
    constructor
    · exact Rat.mul_pos hpos ht.1
    · have := rat_mul_le_mul_of_nonneg (Rat.le_of_lt hpos) hle (Rat.le_of_lt ht.1) ht.2
      change (1-weight p)*coefficient ps≤1; grind only

 theorem zeta_tail_uniform {q n : Nat} (hqn : q≤n) :
    0≤zetaTwoPartial n-zetaTwoPartial q ∧
      zetaTwoPartial n-zetaTwoPartial q≤2/((q+1:Nat):Rat) := by
  constructor
  · have := zetaTwoPartial_le_of_le hqn; grind only
  · by_cases hq : q=0
    · subst q
      have := zetaTwoPartial_le_two n
      simp only [zetaTwoPartial]; grind only [Rat.div_def]
    · have hp : 0<q := by omega
      have ht := zetaTwoPartial_add_finiteTail_le_interval_hi q (n-q) hp
      rw [show q+(n-q)=n by omega] at ht
      change zetaTwoPartial n≤zetaTwoPartial q+zetaTwoTailBound q at ht
      simp only [zetaTwoTailBound, if_neg hq] at ht
      have hrat : 0<(q:Rat) := Rat.natCast_pos.mpr hp
      have hsuc : 0<((q+1:Nat):Rat) := Rat.natCast_pos.mpr (Nat.succ_pos _)
      have hc := Rat.mul_inv_cancel (q:Rat) (by grind only)
      have hd := Rat.mul_inv_cancel ((q+1:Nat):Rat) (by grind only)
      have h1 : (1:Rat)≤(q:Rat) := by exact_mod_cast hp
      have he : 1/(q:Rat)≤2/((q+1:Nat):Rat) := by
        apply (Rat.le_of_mul_le_mul_right · hrat)
        apply (Rat.le_of_mul_le_mul_right · hsuc)
        have hc' := congrArg (fun x=>x*((q+1:Nat):Rat)) hc
        have hd' := congrArg (fun x=>x*(2*(q:Rat))) hd
        simp only [Rat.natCast_add] at *
        grind only [Rat.div_def]
      grind only

 theorem reciprocal_floor_le (p n : Nat) (hp : 0<p) :
    1/((n/p+1:Nat):Rat)≤(p:Rat)/((n+1:Nat):Rat) := by
  have hd := Nat.mod_add_div n p
  have hm := Nat.mod_lt n hp
  have hnat : n+1≤p*(n/p+1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  have hr := Rat.natCast_le_natCast.mpr hnat
  have ap : 0<((n/p+1:Nat):Rat) := Rat.natCast_pos.mpr (Nat.succ_pos _)
  have bp : 0<((n+1:Nat):Rat) := Rat.natCast_pos.mpr (Nat.succ_pos _)
  have ac := Rat.mul_inv_cancel ((n/p+1:Nat):Rat) (by grind only)
  have bc := Rat.mul_inv_cancel ((n+1:Nat):Rat) (by grind only)
  apply (Rat.le_of_mul_le_mul_right · ap)
  apply (Rat.le_of_mul_le_mul_right · bp)
  have ac' := congrArg (fun x=>x*((n+1:Nat):Rat)) ac
  have bc' := congrArg (fun x=>x*(p:Rat)*((n/p+1:Nat):Rat)) bc
  simp only [Rat.natCast_mul] at hr
  grind only [Rat.div_def]

/-- Quantitative finite Euler-product comparison, before any assumption
that the prime list is exhaustive. -/
 theorem sieve_error {ps : List Nat} (hps : ∀p, p∈ps → BasicPrime p)
    (hnd : ps.Nodup) (n : Nat) :
    qabs (sieve ps n-coefficient ps*zetaTwoPartial n) ≤ (budget ps:Rat)/((n+1:Nat):Rat) := by
  induction ps generalizing n with
  | nil => rw [sieve_nil]; simp [coefficient, budget, qabs]; grind only [Rat.div_def]
  | cons p ps ih =>
    have hp := hps p (by simp)
    have ht : ∀q, q∈ps → BasicPrime q := by intro q hq; exact hps q (by simp [hq])
    have hn := List.nodup_cons.mp hnd
    have hN := ih ht hn.2 n
    have hQ := ih ht hn.2 (n/p)
    have hw := weight_bounds hp
    have hc := coefficient_bounds ht
    have hz := zeta_tail_uniform (show n/p≤n from Nat.div_le_self n p)
    have he : sieve (p::ps) n-coefficient (p::ps)*zetaTwoPartial n =
        (sieve ps n-coefficient ps*zetaTwoPartial n) +
        (-weight p)*(sieve ps (n/p)-coefficient ps*zetaTwoPartial (n/p)) +
        (weight p*coefficient ps)*(zetaTwoPartial n-zetaTwoPartial (n/p)) := by
      rw [sieve_cons hp ht hn.1]; dsimp [coefficient]; grind only
    rw [he]
    have hab := qabs_add_le_three (sieve ps n-coefficient ps*zetaTwoPartial n)
      ((-weight p)*(sieve ps (n/p)-coefficient ps*zetaTwoPartial (n/p)))
      ((weight p*coefficient ps)*(zetaTwoPartial n-zetaTwoPartial (n/p)))
    rw [qabs_mul, qabs_neg, qabs_eq_self_of_nonneg hw.1,
      qabs_mul, qabs_eq_self_of_nonneg (Rat.mul_nonneg hw.1 (Rat.le_of_lt hc.1)),
      qabs_eq_self_of_nonneg hz.1] at hab
    have hw1 : weight p≤1 := by grind only [Rat.div_def]
    have hwc : weight p*coefficient ps≤1 := by
      have := rat_mul_le_mul_of_nonneg hw.1 hw1 (Rat.le_of_lt hc.1) hc.2
      grind only
    have hsmallQ := Rat.mul_le_mul_of_nonneg_right hw1 (qabs_nonneg (sieve ps (n/p)-coefficient ps*zetaTwoPartial (n/p)))
    have hsmallZ := Rat.mul_le_mul_of_nonneg_right hwc hz.1
    have hrf := reciprocal_floor_le p n (by have := hp.1; omega)
    have hK : 0≤(budget ps:Rat)+2 := by have : 0≤(budget ps:Rat) := Rat.natCast_nonneg; grind only
    have hrate := Rat.mul_le_mul_of_nonneg_left hrf hK
    simp only [budget, Rat.natCast_add, Rat.natCast_mul]
    grind only [Rat.div_def]

end ComputableAnalysis.Basel.EulerSieve
