import ComputableAnalysis.ModularForms.LambertSeventhWeightBound
import ComputableAnalysis.ModularForms.LambertWideFirstRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem half_power_le_one (n : Nat) : ((1:Rat)/32)^n≤1 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [Rat.pow_succ]
    have h := Rat.mul_le_mul_of_nonneg_right ih (show (0:Rat)≤1/32 by decide +kernel)
    exact Rat.le_trans h (by decide +kernel)

/-- The complete literal weight-six quadratic coefficient has a summable majorant on the wider disk. -/
theorem lambertFifthWide_quadratic_coefficient_bound (N : Nat) (H : Rat) (hH : 0≤H) :
    (((N+2:Nat):Rat)^5)*(1024*(2*((N+2:Nat):Rat)*(2*(1/64:Rat))^(N+1)*H)^2+
      64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*(1/64:Rat))^N*H^2))≤
      33792*((1:Rat)/2)^N*H^2 := by
  let u : Rat := ((N+2:Nat):Rat)
  let v : Rat := ((N+1:Nat):Rat)
  let t : Rat := ((1:Rat)/32)^N
  have hu : 0≤u := Rat.natCast_nonneg
  have hv : 0≤v := Rat.natCast_nonneg
  have hvu : v≤u := by dsimp [v,u]; simp only [Rat.natCast_add]; grind only
  have ht : 0≤t := Rat.pow_nonneg (by decide +kernel)
  have ht1 : t≤1 := half_power_le_one N
  have hs : 0≤H^2 := Rat.pow_nonneg hH
  have htsq : t*t≤t := by
    have h := Rat.mul_le_mul_of_nonneg_right ht1 ht
    simpa only [Rat.one_mul] using h
  have hp : (2*(1/64:Rat))^(N+1)=t*(1/32) := by
    rw [show (2:Rat)*(1/64)=1/32 by decide +kernel,Rat.pow_succ]
  have he : u^5*(1024*(2*u*(t*(1/32))*H)^2+64*(2*u*v*t*H^2))=
      4*u^7*t*t*H^2+128*u^6*v*t*H^2 := by grind only
  have h1 := Rat.mul_le_mul_of_nonneg_left htsq
    (Rat.mul_nonneg (show (0:Rat)≤4 by decide +kernel) (Rat.pow_nonneg hu (n := 7)))
  have h1h := Rat.mul_le_mul_of_nonneg_right h1 hs
  have h2 := Rat.mul_le_mul_of_nonneg_left hvu (Rat.pow_nonneg hu (n := 6))
  have h2t := Rat.mul_le_mul_of_nonneg_right h2 ht
  have h2h := Rat.mul_le_mul_of_nonneg_right h2t hs
  have hb : 4*u^7*t*t*H^2+128*u^6*v*t*H^2≤132*u^7*t*H^2 := by
    have hpow : u^6*u=u^7 := (Rat.pow_succ u 6).symm
    rw [hpow] at h2t h2h
    grind only
  have hw := Rat.mul_le_mul_of_nonneg_right (lambertShiftedSeventhWeight_sharp_bound N)
    (Rat.mul_nonneg ht hs)
  have hpow : (16:Rat)^N*((1:Rat)/32)^N=((1:Rat)/2)^N := by
    rw [←LocalODE.rational_mul_pow]
    congr 1
    decide +kernel
  have hc : 132*u^7*t*H^2≤33792*((1:Rat)/2)^N*H^2 := by
    have hh := Rat.mul_le_mul_of_nonneg_left hw (show (0:Rat)≤132 by decide +kernel)
    dsimp [u,t] at hh
    have halg : 132*(256*(16:Rat)^N*(((1:Rat)/32)^N*H^2))=
        33792*(((16:Rat)^N*((1:Rat)/32)^N))*H^2 := by grind only
    rw [halg,hpow] at hh
    calc
      132*u^7*t*H^2=132*(((N+2:Nat):Rat)^7*(((1:Rat)/32)^N*H^2)) := by dsimp [u,t]; grind only
      _ ≤ 33792*((1:Rat)/2)^N*H^2 := hh
  rw [hp,show (2:Rat)*(1/64)=1/32 by decide +kernel]
  change u^5*(1024*(2*u*(t*(1/32))*H)^2+64*(2*u*v*t*H^2))≤_
  rw [he]
  exact Rat.le_trans hb hc
end ComputableAnalysis.ModularForms
