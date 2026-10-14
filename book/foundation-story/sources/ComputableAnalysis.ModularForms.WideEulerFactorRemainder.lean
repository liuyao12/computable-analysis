import ComputableAnalysis.ModularForms.WideEulerTailDerivativeLimit
import ComputableAnalysis.ModularForms.TauEulerGeometricRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
theorem wideEulerFactorMap_value_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/64) (hq : Small q.val r) (N : Nat) :
    Small ((tauEulerFactorMap N).eval q trivial).val 2 := by
  have hone : Small one 1 := by
    simpa only [LocalODE.power,Rat.pow_zero] using
      LocalODE.power_small zero (ofQComplex_valid _) 0 Rat.le_refl (Small.zero Rat.le_refl) 0
  have hp := LocalODE.power_small _ q.property r hr hq (N+1)
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤2 by decide +kernel)
  have ht1 : 2*r≤1 := Rat.le_trans hmax (by decide +kernel)
  have hh := tauEulerGeometricPower_le_first (2*r) ht ht1 N
  exact (SeriesLimitLaws.small_sub hone hp).mono (by grind only)

theorem wideEulerFactorPower_quadratic_remainder_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hRMax : R≤(1:Rat)/64) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (DomainFunctions.remainder (tauMapPower (tauEulerFactorMap (N+1)) 24) a trivial
      ((tauMapPower_holomorphic (tauEulerFactorMap (N+1)) (tauEulerFactorMap_holomorphic (N+1)) 24).derivative a trivial)
      z trivial)
      (2*((24:Nat):Rat)*((23:Nat):Rat)*(4:Rat)^22*
        (2*((N+2:Nat):Rat)*(2*R)^(N+1)*H)^2+
        2*(((24:Nat):Rat)*(4:Rat)^23)*
          (2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2)) := by
  let L := 2*((N+2:Nat):Rat)*(2*R)^(N+1)*H
  let E := 2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2
  have ht : 0≤2*R := Rat.mul_nonneg (by decide +kernel) hR
  have hL : 0≤L := Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) (Rat.pow_nonneg ht)) hH
  have hE : 0≤E := Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) Rat.natCast_nonneg)
    (Rat.pow_nonneg ht)) (Rat.pow_nonneg hH)
  have h := tauMapPower_quadratic_remainder_bound (tauEulerFactorMap (N+1))
    (tauEulerFactorMap_holomorphic (N+1)) a z trivial trivial 2 L E (by decide +kernel) hL hE
    (wideEulerFactorMap_value_bound a R hR hRMax ha (N+1))
    (wideEulerFactorMap_value_bound z R hR hRMax hz (N+1))
    (tauEulerFactorMap_variation_bound a z R H hR hH ha hz hza (N+1))
    (tauEulerFactorMap_quadratic_remainder_bound a z R H hR hH ha hz hza N) 22
  rw [show (2:Rat)*2=4 by decide +kernel] at h
  exact h

theorem wideEulerFirstFactorPower_quadratic_remainder_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hRMax : R≤(1:Rat)/64) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder (tauMapPower (tauEulerFactorMap 0) 24) a trivial
      ((tauMapPower_holomorphic (tauEulerFactorMap 0) (tauEulerFactorMap_holomorphic 0) 24).derivative a trivial)
      z trivial) (2*((24:Nat):Rat)*((23:Nat):Rat)*(4:Rat)^22*(2*H)^2) := by
  have hv := tauEulerFactorMap_variation_bound a z R H hR hH ha hz hza 0
  have hv' : Small (sub ((tauEulerFactorMap 0).eval z trivial).val
      ((tauEulerFactorMap 0).eval a trivial).val) (2*H) := by
    simpa only [Nat.zero_add,Rat.pow_zero,show ((1:Nat):Rat)=1 by rfl,Rat.mul_one] using hv
  have h := tauMapPower_quadratic_remainder_bound (tauEulerFactorMap 0)
    (tauEulerFactorMap_holomorphic 0) a z trivial trivial 2 (2*H) 0
    (by decide +kernel) (Rat.mul_nonneg (by decide +kernel) hH) Rat.le_refl
    (wideEulerFactorMap_value_bound a R hR hRMax ha 0)
    (wideEulerFactorMap_value_bound z R hR hRMax hz 0) hv'
    (tauEulerFactorMap_affine_remainder a z) 22
  simpa only [show (2:Rat)*2=4 by decide +kernel,Rat.mul_zero,Rat.add_zero] using h


end ComputableAnalysis.ModularForms
