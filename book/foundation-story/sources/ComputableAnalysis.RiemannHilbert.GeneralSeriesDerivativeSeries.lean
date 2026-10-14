import ComputableAnalysis.RiemannHilbert.CenteredSeriesEstimates

/-! The actual derivative series has a constructed geometric coefficient
majorant. Its sum agrees with the derivative of the original series. -/
namespace ComputableAnalysis.RiemannHilbert.BoundedSeries
open ComplexRaw FunctionTheory LocalODE
set_option autoImplicit false

def derivativeCoefficients (c : Nat → ComplexRaw) (k : Nat) : ComplexRaw :=
  scaleRat ((k+1:Nat):Rat) (c (k+1))

theorem derivativeCoefficients_valid (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid) (k : Nat) :
    (derivativeCoefficients c k).Valid := scaleRat_valid (hc (k+1))

private theorem successor_bound (k : Nat) : k+1≤2^k := by
  induction k with
  | zero => decide
  | succ k ih => calc
      k+1+1≤2*(k+1) := by omega
      _≤2*2^k := Nat.mul_le_mul_left 2 ih
      _=2^(k+1) := by rw [Nat.pow_succ]; omega

private theorem two_power_cast (k : Nat) : ((2^k:Nat):Rat)=(2:Rat)^k := by
  induction k with
  | zero => decide +kernel
  | succ k ih => rw [Nat.pow_succ,Rat.natCast_mul,Rat.pow_succ,ih]; rfl

theorem derivativeCoefficients_majorant (c : Nat → ComplexRaw) (_hc : ∀ k, (c k).Valid)
    (C K : Rat) (hC : 0≤C) (hK : 0≤K) (hb : ∀ k, Small (c k) (C*K^k)) (k : Nat) :
    Small (derivativeCoefficients c k) ((C*K)*(2*K)^k) := by
  have hn : 0≤((k+1:Nat):Rat) := Rat.le_of_lt (Rat.natCast_pos.mpr (Nat.succ_pos k))
  have hs := LocalODE.small_scale hn (hb (k+1))
  apply hs.mono
  have hcast : ((k+1:Nat):Rat)≤(2:Rat)^k := by
    rw [←two_power_cast]; exact_mod_cast successor_bound k
  have hmul : ((k+1:Nat):Rat)*(C*K^(k+1))≤(2:Rat)^k*(C*K^(k+1)) := Rat.mul_le_mul_of_nonneg_right hcast (Rat.mul_nonneg hC (Rat.pow_nonneg hK))
  have he : (2:Rat)^k*(C*K^(k+1))=(C*K)*(2*K)^k := by
    rw [Rat.pow_succ,LocalODE.rational_mul_pow]; grind only
  rw [he] at hmul
  exact hmul

theorem derivativeCoefficients_term (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid)
    (z : ComplexRaw) (hz : z.Valid) (k : Nat) :
    (LocalODE.seriesTerm (derivativeCoefficients c) z k).Equiv (derivativeTerm c z k) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := LocalODE.seriesTerm_valid _ z (derivativeCoefficients_valid c hc) hz k)
    (hright := derivativeTerm_valid c z hc hz k)
  change ComplexRawQuotient.scaleRat ((k+1:Nat):Rat) (ComplexRawQuotient.ofRaw (c (k+1)) (hc (k+1)))*
    ComplexRawQuotient.ofRaw (LocalODE.power z k) (LocalODE.power_valid z hz k)=
    ComplexRawQuotient.scaleRat ((k+1:Nat):Rat) (ComplexRawQuotient.ofRaw (c (k+1)) (hc (k+1))*
      ComplexRawQuotient.ofRaw (LocalODE.power z k) (LocalODE.power_valid z hz k))
  exact (ComplexRawQuotient.scaleRat_mul _ _ _).symm

theorem derivativeCoefficients_sum (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid)
    (z : ComplexRaw) (hz : z.Valid) (C K R S : Rat) (hC : 0≤C) (hK : 0≤K) (hR : 0≤R) (hS : 0≤S)
    (hb : ∀ k, Small (c k) (C*K^k)) (hzR : Small z R) (hzS : Small z S)
    (hl : 4*K*R≤(1:Rat)/2) (hs : 4*K*S≤(1:Rat)/2) :
    (sumValue (derivativeCoefficients c) z (derivativeCoefficients_valid c hc) hz (C*K) (2*K) S).Equiv
      (sumDerivative c z hc hz C K R) := by
  change (ScalarSeries.value (LocalODE.seriesTerm (derivativeCoefficients c) z)
    (LocalODE.seriesTerm_valid _ z (derivativeCoefficients_valid c hc) hz) (C*K) (2*(2*K)*S)).Equiv
      (ScalarSeries.value (derivativeTerm c z) (derivativeTerm_valid c z hc hz) (C*K) (4*K*R))
  have hs' : 2*(2*K)*S≤(1:Rat)/2 := by grind only
  exact ScalarSeries.value_congr _ _ _ _ (C*K) (2*(2*K)*S) (C*K) (4*K*R)
    (Rat.mul_nonneg hC hK) (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.mul_nonneg (by decide +kernel) hK)) hS)
    (Rat.mul_nonneg hC hK) (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hK) hR) hs' hl
    (LocalODE.seriesTerm_bound _ z (derivativeCoefficients_valid c hc) hz (C*K) (2*K) S
      (Rat.mul_nonneg hC hK) (Rat.mul_nonneg (by decide +kernel) hK) hS (derivativeCoefficients_majorant c hc C K hC hK hb) hzS)
    (fun k => by simpa only [Rat.mul_assoc] using derivativeTerm_majorant c z hc hz C K R hC hK hR hb hzR k)
    (derivativeCoefficients_term c hc z hz)

end ComputableAnalysis.RiemannHilbert.BoundedSeries
