import ComputableAnalysis.ModularForms.LambertSharperSlopeBound
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

/-- The two index factors in the quadratic remainder retain a summable base-sixteen bound. -/
theorem lambertSeventhWeight_sharp_bound (n : Nat) : ((n+1:Nat):Rat)^7≤16*(16:Rat)^n := by
  have hx : 0≤((n+1:Nat):Rat) := Rat.natCast_nonneg
  have h1 := Rat.mul_le_mul_of_nonneg_right (lambertSixthWeight_sharp_bound n) hx
  have h2 := Rat.mul_le_mul_of_nonneg_left (lambertIndex_bound n)
    (Rat.mul_nonneg (show (0:Rat)≤16 by decide +kernel)
      (Rat.pow_nonneg (show (0:Rat)≤8 by decide +kernel) (n := n)))
  have hp : (8:Rat)^n*(2:Rat)^n=(16:Rat)^n := by
    rw [←LocalODE.rational_mul_pow]
    congr 1
    decide +kernel
  have he : 16*(8:Rat)^n*(2:Rat)^n=16*(16:Rat)^n := by
    have ha : 16*(8:Rat)^n*(2:Rat)^n=16*((8:Rat)^n*(2:Rat)^n) := by grind only
    rw [ha,hp]
  rw [he] at h2
  rw [Rat.pow_succ]
  exact Rat.le_trans h1 h2

/-- Shifted higher-term indices have the same explicit geometric rate. -/
theorem lambertShiftedSeventhWeight_sharp_bound (n : Nat) : ((n+2:Nat):Rat)^7≤256*(16:Rat)^n := by
  have h := lambertSeventhWeight_sharp_bound (n+1)
  have hi : n+1+1=n+2 := by omega
  rw [hi,Rat.pow_succ 16 n] at h
  have he : 16*((16:Rat)^n*16)=256*(16:Rat)^n := by grind only
  rw [he] at h
  exact h
end ComputableAnalysis.ModularForms
