import ComputableAnalysis.ModularForms.TauLambertTermVariation

/-! Summable geometric variation majorants for actual weighted Lambert terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem square_two_power (N : Nat) : ((2:Rat)^N)^2=(4:Rat)^N := by
  induction N with
  | zero => simp only [Rat.pow_zero,Rat.pow_succ,Rat.mul_one]
  | succ N ih =>
    rw [Rat.pow_succ (2:Rat) N,Rat.pow_succ (4:Rat) N]
    have he : ((2:Rat)^N*2)^2=((2:Rat)^N)^2*4 := by
      simp only [Rat.pow_succ,Rat.pow_zero]
      grind only
    rw [he,ih]

private theorem index_square_bound (N : Nat) : ((N+1:Nat):Rat)^2≤(4:Rat)^N := by
  have hi := lambertIndex_bound N
  have h1 := Rat.mul_le_mul_of_nonneg_right hi (Rat.natCast_nonneg : 0≤((N+1:Nat):Rat))
  have h2 := Rat.mul_le_mul_of_nonneg_left hi (Rat.pow_nonneg (show (0:Rat)≤2 by decide +kernel) : 0≤(2:Rat)^N)
  have he := square_two_power N
  have hs : ((N+1:Nat):Rat)^2≤((2:Rat)^N)^2 := by
    rw [Rat.pow_succ,Rat.pow_one,Rat.pow_succ,Rat.pow_one]
    grind only
  rw [he] at hs
  exact hs

private theorem product_power (t : Rat) (N : Nat) : (4:Rat)^N*t^N=(4*t)^N := by
  induction N with
  | zero => simp only [Rat.pow_zero,Rat.mul_one]
  | succ N ih => rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_succ]; grind only

/-- Pure geometric control of weighted Lambert term variation at every index. -/
theorem weightedLambertOneTerm_geometric_difference_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hlocal : 4*R≤(1:Rat)/2) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (weightedLambertTerm z R 1 N) (weightedLambertTerm a R 1 N)) (128*(8*R)^N*H) := by
  have h := weightedLambertOneTerm_difference_bound a z R H hR hlocal hH ha hz hza N
  have ht : 0≤2*R := Rat.mul_nonneg (by decide +kernel) hR
  have hi := Rat.mul_le_mul_of_nonneg_right (index_square_bound N) (Rat.pow_nonneg ht : 0≤(2*R)^N)
  rw [product_power] at hi
  have he : (4:Rat)*(2*R)=8*R := by grind only
  rw [he] at hi
  have hm := Rat.mul_le_mul_of_nonneg_right
    (Rat.mul_le_mul_of_nonneg_left hi (show (0:Rat)≤128 by decide +kernel)) hH
  apply h.mono
  have heq : 128*((N+1:Nat):Rat)^2*(2*R)^N*H=128*(((N+1:Nat):Rat)^2*(2*R)^N)*H := by grind only
  rw [heq]
  exact hm

/-- The variation coefficients shrink geometrically on the nome disk. -/
theorem weightedLambertOneVariation_majorant_shrinks (R : Rat) (hR : 0≤R)
    (hRM : R≤(1:Rat)/1024) : ShrinksToZero (fun N => 128*(8*R)^N) := by
  have ht : 0≤8*R := Rat.mul_nonneg (by decide +kernel) hR
  have hm := Rat.mul_le_mul_of_nonneg_left hRM (show (0:Rat)≤8 by decide +kernel)
  simpa only [show (4:Rat)*32=128 by decide +kernel] using
    LocalODE.tail_bound_shrinks 32 (8*R) (by decide +kernel) ht (Rat.le_trans hm (by decide +kernel))

end ComputableAnalysis.ModularForms
