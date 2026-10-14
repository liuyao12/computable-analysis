import ComputableAnalysis.ModularForms.TauLambertGeometricVariation
import ComputableAnalysis.ModularForms.LambertHolomorphic

/-! Executable chain-rule slope candidates for weighted Lambert terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The weighted monomial slope times the actual Lambert derivative. -/
def weightedLambertOneSlope (q : Scalar) (R : Rat) (hR : 0≤R)
    (hl : 4*R≤(1:Rat)/2) (hq : Small q.val R) (N : Nat) : Scalar :=
  let d := lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius R N)
    (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hl N)
    (nomePowerScalar_small q R hR hq N)
  ⟨scaleRat (((N+1:Nat):Rat)^2) (mul (LocalODE.power q.val N) d.val),
    scaleRat_valid (mul_valid (LocalODE.power_valid _ q.property N) d.property)⟩

/-- A summable polynomial-times-geometric bound for the literal slope. -/
theorem weightedLambertOneSlope_bound (q : Scalar) (R : Rat) (hR : 0≤R)
    (hl : 4*R≤(1:Rat)/2) (hq : Small q.val R) (N : Nat) :
    Small (weightedLambertOneSlope q R hR hl hq N).val
      (64*((N+1:Nat):Rat)^2*(2*R)^N) := by
  have hg := nomeGeometricSum_bound (nomePowerScalar q N) (nomePowerRadius R N)
    (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hl N)
    (nomePowerScalar_small q R hR hq N)
  have hv := nomeGeometricSum_valid (nomePowerScalar q N) (nomePowerRadius R N)
    (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hl N)
    (nomePowerScalar_small q R hR hq N)
  have hd := Small.mul hv hv (by decide +kernel : (0:Rat)≤4) (by decide +kernel : (0:Rat)≤4) hg hg
  have hp := LocalODE.power_small q.val q.property R hR hq N
  have hm := Small.mul (LocalODE.power_valid _ q.property N)
    (lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius R N)
      (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hl N)
      (nomePowerScalar_small q R hR hq N)).property
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) hR))
    (by decide +kernel : (0:Rat)≤2*4*4) hp hd
  have hs := LocalODE.small_scale
    (Rat.pow_nonneg (n := 2) (Rat.natCast_nonneg : (0:Rat)≤((N+1:Nat):Rat))) hm
  change Small (weightedLambertOneSlope q R hR hl hq N).val
    (((N+1:Nat):Rat)^2*(2*(2*R)^N*(2*4*4))) at hs
  have he : ((N+1:Nat):Rat)^2*(2*(2*R)^N*(2*4*4))=
      64*((N+1:Nat):Rat)^2*(2*R)^N := by grind only
  rw [he] at hs
  exact hs

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

/-- Pure geometric majorant for the executable weighted slope candidate. -/
theorem weightedLambertOneSlope_geometric_bound (q : Scalar) (R : Rat) (hR : 0≤R)
    (hl : 4*R≤(1:Rat)/2) (hq : Small q.val R) (N : Nat) :
    Small (weightedLambertOneSlope q R hR hl hq N).val (64*(8*R)^N) := by
  have h := weightedLambertOneSlope_bound q R hR hl hq N
  have hi := Rat.mul_le_mul_of_nonneg_right (index_square_bound N)
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel : (0:Rat)≤2) hR) : 0≤(2*R)^N)
  rw [product_power] at hi
  have he : (4:Rat)*(2*R)=8*R := by grind only
  rw [he] at hi
  have hm := Rat.mul_le_mul_of_nonneg_left hi (by decide +kernel : (0:Rat)≤64)
  apply h.mono
  grind only

/-- The slope candidate respects represented equality and independent radii. -/
theorem weightedLambertOneSlope_congr (q w : Scalar) (R S : Rat)
    (hR : 0≤R) (hS : 0≤S) (hlR : 4*R≤(1:Rat)/2) (hlS : 4*S≤(1:Rat)/2)
    (hq : Small q.val R) (hw : Small w.val S) (he : q.val.Equiv w.val) (N : Nat) :
    (weightedLambertOneSlope q R hR hlR hq N).val.Equiv
      (weightedLambertOneSlope w S hS hlS hw N).val := by
  have hd := lambertDiskDerivative_congr (nomePowerScalar q N) (nomePowerScalar w N)
    (nomePowerRadius R N) (nomePowerRadius S N)
    (nomePowerRadius_nonneg R hR N) (nomePowerRadius_nonneg S hS N)
    (nomePowerRadius_local R hR hlR N) (nomePowerRadius_local S hS hlS N)
    (nomePowerScalar_small q R hR hq N) (nomePowerScalar_small w S hS hw N)
    (LocalODE.power_congr q.val w.val q.property w.property he (N+1))
  exact scaleRat_equiv (mul_equiv (LocalODE.power_valid _ q.property N)
    (LocalODE.power_valid _ w.property N)
    (lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius R N)
      (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hlR N)
      (nomePowerScalar_small q R hR hq N)).property
    (lambertDiskDerivative (nomePowerScalar w N) (nomePowerRadius S N)
      (nomePowerRadius_nonneg S hS N) (nomePowerRadius_local S hS hlS N)
      (nomePowerScalar_small w S hS hw N)).property
    (LocalODE.power_congr q.val w.val q.property w.property he N) hd)

end ComputableAnalysis.ModularForms
