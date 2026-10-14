import ComputableAnalysis.ModularForms.WideEulerFactorRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
private theorem index_bounds (N : Nat) :
    ((N+2:Nat):Rat)*((N+1:Nat):Rat)≤2*(4:Rat)^N ∧
    ((N+2:Nat):Rat)^2≤4*(4:Rat)^N := by
  have h := Rat.natCast_le_natCast.mpr (LocalODE.quadratic_index_bound N)
  rw [Rat.natCast_mul,Rat.natCast_mul,LocalODE.cast_four_pow] at h
  change ((N+2:Nat):Rat)*((N+1:Nat):Rat)≤2*(4:Rat)^N at h
  refine ⟨h,?_⟩
  have hc : ((N+2:Nat):Rat)≤2*((N+1:Nat):Rat) := by
    have hn : (N+2)≤2*(N+1) := by omega
    have hh := Rat.natCast_le_natCast.mpr hn
    rw [Rat.natCast_mul] at hh
    exact hh
  have hm := Rat.mul_le_mul_of_nonneg_left hc (Rat.natCast_nonneg : 0≤((N+2:Nat):Rat))
  have htwo := Rat.mul_le_mul_of_nonneg_left h (show (0:Rat)≤2 by decide +kernel)
  rw [Rat.pow_succ,Rat.pow_one]
  grind only

private theorem powers_bound (t : Rat) (ht : 0≤t) (ht1 : t≤1) (N : Nat) :
    (t^(N+1))^2≤t^N := by
  have hone : t^N≤1 := by
    induction N with
    | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
    | succ N ih =>
      rw [Rat.pow_succ]
      have h := Rat.mul_le_mul_of_nonneg_right ih ht
      grind only
  have hp : 0≤t^N := Rat.pow_nonneg ht
  have hstep : t^(N+1)≤t^N := by
    rw [Rat.pow_succ]
    simpa only [Rat.mul_one] using Rat.mul_le_mul_of_nonneg_left ht1 hp
  have hnext : t^(N+1)≤1 := Rat.le_trans hstep hone
  have hnp : 0≤t^(N+1) := Rat.pow_nonneg ht
  have hs := Rat.mul_le_mul_of_nonneg_left hnext hnp
  rw [Rat.pow_succ,Rat.pow_one]
  grind only

private theorem product_power_identity (t : Rat) (N : Nat) :
    (4:Rat)^N*t^N=(4*t)^N := by
  induction N with
  | zero => simp only [Rat.pow_zero,Rat.mul_one]
  | succ N ih => rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_succ]; grind only

private theorem square_product (X P H : Rat) :
    (2*X*P*H)^2=4*X^2*P^2*H^2 := by
  simp only [Rat.pow_succ,Rat.pow_one]
  grind only

private theorem finish_majorant (K X Y P T W V H : Rat)
    (hK : 0≤K) (hH : 0≤H) (h1 : X^2*P^2≤4*(W*T))
    (h2 : X*Y*T≤2*W*T) (he : W*T=V) :
    1104*K*(2*X*P*H)^2+96*K*4*X*Y*T*H^2≤18432*K*V*H^2 := by
  have hh : 0≤H^2 := Rat.pow_nonneg hH
  have hf := Rat.mul_le_mul_of_nonneg_left h1
    (Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤4416 by decide +kernel) hK) hh)
  have hs := Rat.mul_le_mul_of_nonneg_left h2
    (Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤384 by decide +kernel) hK) hh)
  calc
    _ = 4416*K*H^2*(X^2*P^2)+384*K*H^2*(X*Y*T) := by
      rw [square_product]
      grind only
    _ ≤ 4416*K*H^2*(4*(W*T))+384*K*H^2*(2*W*T) := by grind only
    _ = 18432*K*V*H^2 := by
      have he2 : 2*W*T=2*(W*T) := by grind only
      rw [he2,he]
      grind only

private theorem remainder_majorant (K t H : Rat) (hK : 0≤K) (ht : 0≤t) (ht1 : t≤1) (hHp : 0≤H) (N : Nat) :
    1104*K*(2*((N+2:Nat):Rat)*t^(N+1)*H)^2+
      96*K*4*((N+2:Nat):Rat)*((N+1:Nat):Rat)*t^N*H^2 ≤
      18432*K*(4*t)^N*H^2 := by
  obtain ⟨hxy,hxx⟩ := index_bounds N
  have hp := powers_bound t ht ht1 N
  have hH : 0≤H^2 := Rat.pow_nonneg hHp
  have htn : 0≤t^N := Rat.pow_nonneg ht
  have hx : 0≤((N+2:Nat):Rat)^2 := Rat.pow_nonneg Rat.natCast_nonneg
  have hfirst1 := Rat.mul_le_mul_of_nonneg_left hp hx
  have hfirst2 := Rat.mul_le_mul_of_nonneg_right hxx htn
  have hfirst : ((N+2:Nat):Rat)^2*(t^(N+1))^2≤4*((4:Rat)^N*t^N) := by grind only
  have hs1 := Rat.mul_le_mul_of_nonneg_right hxy htn
  exact finish_majorant K ((N+2:Nat):Rat) ((N+1:Nat):Rat) (t^(N+1)) (t^N)
    ((4:Rat)^N) ((4*t)^N) H hK hHp hfirst hs1 (product_power_identity t N)



/-- Higher Euler factors have quadratic remainders with a geometric degree majorant. -/
theorem wideEulerFactorPower_geometric_remainder_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hRMax : R≤(1:Rat)/64) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (DomainFunctions.remainder (tauMapPower (tauEulerFactorMap (N+1)) 24) a trivial
      ((tauMapPower_holomorphic (tauEulerFactorMap (N+1)) (tauEulerFactorMap_holomorphic (N+1)) 24).derivative a trivial)
      z trivial) (tauEulerFactorRemainderConstant*(8*R)^N*H^2) := by
  have h := wideEulerFactorPower_quadratic_remainder_bound a z R H hR hRMax hH ha hz hza N
  have ht : 0≤2*R := Rat.mul_nonneg (by decide +kernel) hR
  have hmax := Rat.mul_le_mul_of_nonneg_left hRMax (show (0:Rat)≤2 by decide +kernel)
  have hm := remainder_majorant ((4:Rat)^22) (2*R) H (by decide +kernel) ht
    (Rat.le_trans hmax (by decide +kernel)) hH N
  apply h.mono
  have hp : (4:Rat)^23=(4:Rat)^22*4 := Rat.pow_succ 4 22
  rw [hp]
  rw [show (2:Rat)*((24:Nat):Rat)*((23:Nat):Rat)=1104 by decide +kernel]
  have hc : ((24:Nat):Rat)=24 := rfl
  rw [hc]
  unfold tauEulerFactorRemainderConstant
  have he : (4:Rat)*(2*R)=8*R := by grind only
  rw [he] at hm
  have heq :
      (48*((4:Rat)^22*4))*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2)=
      96*(4:Rat)^22*4*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2 := by grind only
  have hc48 : (2:Rat)*(24*((4:Rat)^22*4))=48*((4:Rat)^22*4) := by grind only
  rw [hc48]
  change 1104*(4:Rat)^22*(2*((N+2:Nat):Rat)*(2*R)^(N+1)*H)^2+
    (48*((4:Rat)^22*4))*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2)≤_
  rw [heq]
  exact hm

/-- The affine base factor fits the same constant as all higher factors. -/
theorem wideEulerFirstFactorPower_geometric_remainder_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hRMax : R≤(1:Rat)/64) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder (tauMapPower (tauEulerFactorMap 0) 24) a trivial
      ((tauMapPower_holomorphic (tauEulerFactorMap 0) (tauEulerFactorMap_holomorphic 0) 24).derivative a trivial)
      z trivial) (tauEulerFactorRemainderConstant*H^2) := by
  apply (wideEulerFirstFactorPower_quadratic_remainder_bound a z R H hR hRMax hH ha hz hza).mono
  have hh : 0≤H^2 := Rat.pow_nonneg hH
  have hk : 0≤(4:Rat)^22 := by decide +kernel
  have hm := Rat.mul_le_mul_of_nonneg_right
    (show (4416:Rat)≤18432 by decide +kernel) (Rat.mul_nonneg hk hh)
  unfold tauEulerFactorRemainderConstant
  simp only [Rat.pow_succ,Rat.pow_one] at hm ⊢
  grind only


end ComputableAnalysis.ModularForms
