import ComputableAnalysis.ModularForms.TauWeightedLambertFirstRemainder

/-! Geometric control of the cubic index factors in Lambert remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private theorem cube_two_power (N : Nat) : ((2:Rat)^N)^3=(8:Rat)^N := by
  induction N with
  | zero => decide +kernel
  | succ N ih =>
    rw [Rat.pow_succ (2:Rat) N, Rat.pow_succ (8:Rat) N]
    have he : ((2:Rat)^N*2)^3=((2:Rat)^N)^3*8 := by
      simp only [Rat.pow_succ, Rat.pow_one]
      grind only
    rw [he, ih]

/-- The cubic degree factor can be absorbed by an exponential majorant. -/
theorem tauLambertIndex_cube_bound (N : Nat) : ((N+2:Nat):Rat)^3≤8*(8:Rat)^N := by
  have hi := lambertIndex_bound (N+1)
  rw [Rat.pow_succ] at hi
  let u : Rat := ((N+2:Nat):Rat)
  let v : Rat := (2:Rat)^N*2
  have hu : 0≤u := Rat.natCast_nonneg
  have hv : 0≤v := Rat.mul_nonneg (Rat.pow_nonneg (by decide +kernel)) (by decide +kernel)
  have h1 := Rat.mul_le_mul_of_nonneg_right hi hu
  have h2 := Rat.mul_le_mul_of_nonneg_left hi hv
  have hs : u*u≤v*v := by grind only
  have h3 := Rat.mul_le_mul_of_nonneg_right hs hu
  have h4 := Rat.mul_le_mul_of_nonneg_left hi (Rat.mul_nonneg hv hv)
  have hc : u^3≤v^3 := by
    simp only [Rat.pow_succ, Rat.pow_one]
    grind only
  have he : v^3=8*(8:Rat)^N := by
    have hp := cube_two_power N
    dsimp [v]
    have hh : ((2:Rat)^N*2)^3=8*((2:Rat)^N)^3 := by
      simp only [Rat.pow_succ, Rat.pow_one]
      grind only
    rw [hh,hp]
  rw [he] at hc
  exact hc

private theorem product_power (t : Rat) (N : Nat) : (8:Rat)^N*t^N=(8*t)^N := by
  induction N with
  | zero => simp only [Rat.pow_zero, Rat.mul_one]
  | succ N ih => rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_succ]; grind only

/-- Cubic times geometric coefficients admit a directly summable majorant. -/
theorem tauLambertIndex_cube_geometric_bound (t : Rat) (ht : 0≤t) (N : Nat) :
    ((N+2:Nat):Rat)^3*t^N≤8*(8*t)^N := by
  have h := Rat.mul_le_mul_of_nonneg_right (tauLambertIndex_cube_bound N)
    (Rat.pow_nonneg ht : 0≤t^N)
  have he : (8*(8:Rat)^N)*t^N=8*((8:Rat)^N*t^N) := by grind only
  rw [he, product_power] at h
  exact h

end ComputableAnalysis.ModularForms
