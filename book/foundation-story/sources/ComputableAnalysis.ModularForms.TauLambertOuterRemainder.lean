import ComputableAnalysis.ModularForms.TauLambertCompositionRemainder

/-! Quadratic control of the outer Lambert remainder at monomial values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The outer remainder retains monomial degree decay and the squared displacement. -/
theorem tauLambertPower_outer_remainder_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hl : 4*R≤(1:Rat)/2) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (sub (nomeLambertPower z R N) (nomeLambertPower a R N))
      (mul (sub (nomePowerScalar z N).val (nomePowerScalar a N).val)
        (lambertDiskDerivative (nomePowerScalar a N) (nomePowerRadius R N)
          (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hl N)
          (nomePowerScalar_small a R hR ha N)).val))
      (1024*(2*((N+1:Nat):Rat)*(2*R)^N*H)^2) := by
  have ht : 0≤2*R := Rat.mul_nonneg (by decide +kernel) hR
  have hD : 0≤2*((N+1:Nat):Rat)*(2*R)^N*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg)
      (Rat.pow_nonneg ht)) hH
  exact lambertFactor_remainder_bound (nomePowerScalar a N) (nomePowerScalar z N)
    (nomePowerRadius R N) (nomePowerRadius R N) (2*((N+1:Nat):Rat)*(2*R)^N*H)
    (nomePowerRadius_nonneg R hR N) (nomePowerRadius_nonneg R hR N) hD
    (nomePowerRadius_local R hR hl N) (nomePowerRadius_local R hR hl N)
    (nomePowerScalar_small a R hR ha N) (nomePowerScalar_small z R hR hz N)
    (LocalODE.power_difference_bound a.val z.val a.property z.property R H hR hH ha hz hd N)

end ComputableAnalysis.ModularForms
