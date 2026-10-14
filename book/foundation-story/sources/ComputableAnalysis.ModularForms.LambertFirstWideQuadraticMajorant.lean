import ComputableAnalysis.ModularForms.LambertThirdWideQuadraticMajorant
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem lambertFirstWide_quadratic_coefficient_bound (N : Nat) (H : Rat) (hH : 0≤H) :
    (((N+2:Nat):Rat)^1)*(1024*(2*((N+2:Nat):Rat)*(2*(1/64:Rat))^(N+1)*H)^2+
      64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*(1/64:Rat))^N*H^2))≤
      33792*((1:Rat)/2)^N*H^2 := by
  let u : Rat := ((N+2:Nat):Rat)
  have hu : 0≤u := Rat.natCast_nonneg
  have hu1 : 1≤u := by
    dsimp [u]
    have h : 1≤N+2 := by omega
    exact_mod_cast h
  have hup : u^1≤u^3 := by
    have h2 : u≤u^2 := by
      have h := Rat.mul_le_mul_of_nonneg_right hu1 hu
      rw [Rat.pow_succ u 1,Rat.pow_one]
      grind only
    have h3 : u^2≤u^3 := by
      have h := Rat.mul_le_mul_of_nonneg_right hu1 (Rat.pow_nonneg hu (n := 2))
      rw [Rat.pow_succ u 2]
      grind only
    rw [Rat.pow_one]
    exact Rat.le_trans h2 h3
  let B := 1024*(2*u*(2*(1/64:Rat))^(N+1)*H)^2+
    64*(2*u*((N+1:Nat):Rat)*(2*(1/64:Rat))^N*H^2)
  have hs : 0≤2*u*(2*(1/64:Rat))^(N+1)*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hu)
      (Rat.pow_nonneg (by decide +kernel))) hH
  have hb : 0≤B := Rat.add_nonneg
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hs))
    (Rat.mul_nonneg (by decide +kernel) (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel) hu) Rat.natCast_nonneg) (Rat.pow_nonneg (by decide +kernel))) (Rat.pow_nonneg hH)))
  have hm := Rat.mul_le_mul_of_nonneg_right hup hb
  exact Rat.le_trans hm (lambertThirdWide_quadratic_coefficient_bound N H hH)
end ComputableAnalysis.ModularForms
