import ComputableAnalysis.ModularForms.LambertSharperWeightBound
import ComputableAnalysis.ModularForms.TauWeightedLambertSlopeBounds
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The additional index factor in the actual slope has a base-eight majorant. -/
theorem lambertSixthWeight_sharp_bound (n : Nat) : ((n+1:Nat):Rat)^6≤16*(8:Rat)^n := by
  have hx : 0≤((n+1:Nat):Rat) := Rat.natCast_nonneg
  have h1 := Rat.mul_le_mul_of_nonneg_right (lambertFifthWeight_sharp_bound n) hx
  have h2 := Rat.mul_le_mul_of_nonneg_left (lambertIndex_bound n)
    (Rat.mul_nonneg (show (0:Rat)≤16 by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤4 by decide +kernel) (n := n)))
  have hp : (4:Rat)^n*(2:Rat)^n=(8:Rat)^n := by
    rw [←LocalODE.rational_mul_pow]
    congr 1
    decide +kernel
  rw [Rat.pow_succ]
  have he : 16*(4:Rat)^n*(2:Rat)^n=16*(8:Rat)^n := by
    have hh : 16*(4:Rat)^n*(2:Rat)^n=16*((4:Rat)^n*(2:Rat)^n) := by grind only
    rw [hh,hp]
  rw [he] at h2
  exact Rat.le_trans h1 h2

/-- A sharper geometric bound for the literal actual weight-six slope. -/
theorem weightedLambertFifthSlope_sharp_bound (q : Scalar) (R : Rat) (hR : 0≤R)
    (hl : 4*R≤(1:Rat)/2) (hq : Small q.val R) (n : Nat) :
    Small (weightedLambertSlope q R 5 hR hl hq n).val (1024*(16*R)^n) := by
  have h := weightedLambertSlope_bound q R 5 hR hl hq n
  have hm := Rat.mul_le_mul_of_nonneg_right (lambertSixthWeight_sharp_bound n)
    (Rat.pow_nonneg (Rat.mul_nonneg (show (0:Rat)≤2 by decide +kernel) hR) : 0≤(2*R)^n)
  have hp : (8:Rat)^n*(2*R)^n=(16*R)^n := by
    rw [←LocalODE.rational_mul_pow]
    congr 1
    grind only
  have hh := Rat.mul_le_mul_of_nonneg_left hm (show (0:Rat)≤64 by decide +kernel)
  have he : 64*(16*(8:Rat)^n*(2*R)^n)=1024*(16*R)^n := by
    have ha : 64*(16*(8:Rat)^n*(2*R)^n)=1024*((8:Rat)^n*(2*R)^n) := by grind only
    rw [ha,hp]
  rw [he] at hh
  apply h.mono
  calc
    64*((n+1:Nat):Rat)^(5+1)*(2*R)^n = 64*(((n+1:Nat):Rat)^6*(2*R)^n) := by grind only
    _ ≤ 1024*(16*R)^n := hh
end ComputableAnalysis.ModularForms
