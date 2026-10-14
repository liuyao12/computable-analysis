import ComputableAnalysis.ModularForms.TauFiniteProductRemainder

/-! Displacement-sensitive bounds for actual degree-24 Euler factors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Power-map variation follows from the supplied actual base variation. -/
theorem tauMapPower_variation_bound (f : DomainFunctions.Map) (a z : Scalar)
    (ha : f.domain a) (hz : f.domain z) (R L : Rat) (hR : 0≤R) (hL : 0≤L)
    (haR : Small (f.eval a ha).val R) (hzR : Small (f.eval z hz).val R)
    (hvariation : Small (sub (f.eval z hz).val (f.eval a ha).val) L) (n : Nat) :
    Small (sub ((tauMapPower f (n+1)).eval z hz).val ((tauMapPower f (n+1)).eval a ha).val)
      (2*((n+1:Nat):Rat)*(2*R)^n*L) :=
  LocalODE.power_difference_bound _ _ (f.eval a ha).property (f.eval z hz).property
    R L hR hL haR hzR hvariation n

/-- Every degree-24 Euler factor retains the input displacement in its
variation bound, including the first factor. -/
theorem tauEulerFactorValue_variation_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hRMax : R≤(1:Rat)/512) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (tauEulerFactorValue z N).val (tauEulerFactorValue a N).val)
      (96*(4:Rat)^23*((N+1:Nat):Rat)*(2*R)^N*H) := by
  have ht : 0≤2*R := Rat.mul_nonneg (by decide +kernel) hR
  have hL : 0≤2*((N+1:Nat):Rat)*(2*R)^N*H := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg)
      (Rat.pow_nonneg ht)) hH
  have h := tauMapPower_variation_bound (tauEulerFactorMap N) a z trivial trivial 2
    (2*((N+1:Nat):Rat)*(2*R)^N*H) (by decide +kernel) hL
    (tauEulerFactorMap_value_bound a R hR hRMax ha N)
    (tauEulerFactorMap_value_bound z R hR hRMax hz N)
    (tauEulerFactorMap_variation_bound a z R H hR hH ha hz hza N) 23
  have he : (2:Rat)*((24:Nat):Rat)*(2*2)^23*(2*((N+1:Nat):Rat)*(2*R)^N*H)=
      96*(4:Rat)^23*((N+1:Nat):Rat)*(2*R)^N*H := by grind only
  rw [he] at h
  exact h

private theorem index_bound (N : Nat) : ((N+1:Nat):Rat)≤(2:Rat)^N := by
  induction N with
  | zero => change (1:Rat)≤1; exact Rat.le_refl
  | succ N ih =>
    have hn : 0≤(N:Rat) := Rat.natCast_nonneg
    have hh := Rat.mul_le_mul_of_nonneg_left ih (show (0:Rat)≤2 by decide +kernel)
    rw [Rat.pow_succ]
    simp only [Rat.natCast_add,show ((1:Nat):Rat)=1 by rfl] at *
    grind only

private theorem product_power (t : Rat) (N : Nat) :
    (2:Rat)^N*t^N=(2*t)^N := by
  induction N with
  | zero => simp only [Rat.pow_zero,Rat.mul_one]
  | succ N ih => rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_succ]; grind only

/-- A summable geometric variation majorant, uniform in the factor index. -/
theorem tauEulerFactorValue_geometric_variation_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hRMax : R≤(1:Rat)/512) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (tauEulerFactorValue z N).val (tauEulerFactorValue a N).val)
      (96*(4:Rat)^23*(4*R)^N*H) := by
  have h := tauEulerFactorValue_variation_bound a z R H hR hRMax hH ha hz hza N
  have ht : 0≤2*R := Rat.mul_nonneg (by decide +kernel) hR
  have hi := Rat.mul_le_mul_of_nonneg_right (index_bound N)
    (Rat.pow_nonneg ht : 0≤(2*R)^N)
  rw [product_power] at hi
  have he : (2:Rat)*(2*R)=4*R := by grind only
  rw [he] at hi
  have hk : 0≤96*(4:Rat)^23 := by decide +kernel
  have hm := Rat.mul_le_mul_of_nonneg_right
    (Rat.mul_le_mul_of_nonneg_left hi hk) hH
  apply h.mono
  have heq : 96*(4:Rat)^23*((N+1:Nat):Rat)*(2*R)^N*H=
      (96*(4:Rat)^23)*(((N+1:Nat):Rat)*(2*R)^N)*H := by grind only
  rw [heq]
  exact hm

end ComputableAnalysis.ModularForms
