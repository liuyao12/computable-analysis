import ComputableAnalysis.ModularForms.LambertWideQuadraticMajorant
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem lambertThirdWide_quadratic_coefficient_bound (N : Nat) (H : Rat) (hH : 0≤H) :
    (((N+2:Nat):Rat)^3)*(1024*(2*((N+2:Nat):Rat)*(2*(1/64:Rat))^(N+1)*H)^2+
      64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*(1/64:Rat))^N*H^2))≤
      33792*((1:Rat)/2)^N*H^2 := by
  let u : Rat := ((N+2:Nat):Rat)
  have hu : 0≤u := Rat.natCast_nonneg
  have hu1 : 1≤u := by
    dsimp [u]
    have h : 1≤N+2 := by omega
    exact_mod_cast h
  have h34 := Rat.mul_le_mul_of_nonneg_right hu1 (Rat.pow_nonneg hu (n := 3))
  have h45 := Rat.mul_le_mul_of_nonneg_right hu1 (Rat.pow_nonneg hu (n := 4))
  have hup : u^3≤u^5 := by
    rw [Rat.pow_succ u 3] at h45
    have h4 : u^3≤u^4 := by rw [Rat.pow_succ u 3]; grind only
    have h5 : u^4≤u^5 := by rw [Rat.pow_succ u 4]; grind only
    exact Rat.le_trans h4 h5
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
  exact Rat.le_trans hm (lambertFifthWide_quadratic_coefficient_bound N H hH)
end ComputableAnalysis.ModularForms
