import ComputableAnalysis.ModularForms.TauEulerPowerVariation
import ComputableAnalysis.ModularForms.TauFiniteDerivativeBounds

/-! Constructed geometric data for whole-product quadratic propagation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Adding a higher factor propagates a quadratic bound with all factor,
value and slope evidence constructed from the common represented disk. -/
theorem finiteDiscriminantEulerRemainder_quadratic_step (a z : Scalar) (R H K : Rat)
    (hR : 0≤R) (hRMax : R≤(1:Rat)/1024) (hH : 0≤H) (hK : 0≤K)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H)
    (N : Nat) (hprev : Small (finiteDiscriminantEulerRemainder a z (N+1)).val (K*H^2)) :
    Small (finiteDiscriminantEulerRemainder a z (N+2)).val
      ((K+96*K*(2*R)^(N+2)+4*tauEulerFactorRemainderConstant*(8*R)^N+
        786432*(4:Rat)^23*(4*R)^(N+1))*H^2) := by
  have hR512 : R≤(1:Rat)/512 := Rat.le_trans hRMax (by decide +kernel)
  have ht : 0≤2*R := Rat.mul_nonneg (by decide +kernel) hR
  have hu : 0≤4*R := Rat.mul_nonneg (by decide +kernel) hR
  have hv : 0≤8*R := Rat.mul_nonneg (by decide +kernel) hR
  have hh : 0≤H^2 := Rat.pow_nonneg hH
  have hc : 0≤tauEulerFactorRemainderConstant := by decide +kernel
  have hV : 0≤48*(2*R)^((N+1)+1) := Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg ht)
  have hL : 0≤96*(4:Rat)^23*(4*R)^(N+1)*H := Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hu)) hH
  have hF : 0≤tauEulerFactorRemainderConstant*(8*R)^N*H^2 := Rat.mul_nonneg
    (Rat.mul_nonneg hc (Rat.pow_nonneg hv)) hh
  have h := finiteDiscriminantEulerRemainder_step_bound a z (N+1)
    (K*H^2) 2 2048 H (48*(2*R)^((N+1)+1))
    (96*(4:Rat)^23*(4*R)^(N+1)*H) (tauEulerFactorRemainderConstant*(8*R)^N*H^2)
    (Rat.mul_nonneg hK hh) (by decide +kernel) (by decide +kernel) hH hV hL hF
    hprev (finiteDiscriminantEulerProduct_bound a R hR hRMax ha (N+1))
    (finiteDiscriminantEulerSlope_bound a R hR hRMax ha (N+1)) hza
    (tauEulerFactor_deviation_bound z R hR hR512 hz (N+1))
    (tauEulerFactorValue_geometric_variation_bound a z R H hR hR512 hH ha hz hza (N+1))
    (tauEulerFactorPower_geometric_remainder_bound a z R H hR hR512 hH ha hz hza N)
  have he :
      ((K*H^2+2*(K*H^2)*(48*(2*R)^((N+1)+1)))+
        (2*2*(tauEulerFactorRemainderConstant*(8*R)^N*H^2)+
          2*(2*2048*H)*(96*(4:Rat)^23*(4*R)^(N+1)*H))) =
      (K+96*K*(2*R)^(N+2)+4*tauEulerFactorRemainderConstant*(8*R)^N+
        786432*(4:Rat)^23*(4*R)^(N+1))*H^2 := by
    simp only [Rat.pow_succ] 
    grind only
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
