import ComputableAnalysis.ModularForms.PairedRegularDivisionDifferentiable

/-! Summable derivative differences for the division series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedRegularDivisionDerivativeTerm_difference_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (sub (pairedRegularDivisionDerivativeTerm z hz n).val
      (pairedRegularDivisionDerivativeTerm a ha n).val) (2304*reciprocalSquare (n+1)*H) := by
  let da := pairedSmallDisk_domain a (1/4) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ a ha)
  let dz := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ z hz)
  let r := reciprocalSquare (n+1)
  let M := 4*r
  let ia := (pairedSmallDiskLiteralInverseMap n).eval a ha
  let iz := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let D := ReciprocalDifference.derivative (pairedLiteralDenominator z (pairedIntegerSquare (n+1))) (dz n)
  let A := ReciprocalDifference.derivative (pairedLiteralDenominator a (pairedIntegerSquare (n+1))) (da n)
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hr : 0≤r := by
    dsimp [r]; unfold reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have hm : 0≤M := Rat.mul_nonneg (by decide) hr
  have hi : Small ia.val M := pairedSmallDiskLiteralInverse_bound a (LocalODE.interior_bound _ a ha) n
  have hj : Small iz.val M := pairedSmallDiskLiteralInverse_bound z (LocalODE.interior_bound _ z hz) n
  have hD := pairedUniformReciprocalDerivative_difference _ _ (da n) (dz n) M H hm hH hi hj
    (pairedLiteralDenominator_difference_bound a z (LocalODE.interior_bound _ a ha)
      (LocalODE.interior_bound _ z hz) _ H hH hd)
  have hA : Small A.val (2*M*M) := SeriesLimitLaws.small_neg (Small.mul ia.property ia.property hm hm hi hi)
  have hs : Small (sub (add z.val z.val) (add a.val a.val)) (H+H) :=
    Small.congr (add_valid (sub_valid z.property a.property) (sub_valid z.property a.property))
      (sub_valid (add_valid z.property z.property) (add_valid a.property a.property))
      (equiv_symm (SeriesLimitLaws.addition_difference z.val a.val z.val a.val
        z.property a.property z.property a.property)) (LocalODE.small_add hd hd)
  have hG := LocalODE.small_add (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ z hz)
  have hb := SeriesLimitLaws.product_close D.val (add z.val z.val) A.val (add a.val a.val)
    D.property (add_valid z.property z.property) A.property (add_valid a.property a.property)
    (16*M*M*M*H) (H+H) (2*M*M) (1/4+1/4)
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hm) hm) hm) hH)
    (Rat.add_nonneg hH hH) (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hm) hm)
    (by decide +kernel) hD hs hA hG
  have he := SeriesLimitLaws.addition_difference (mul D.val (add z.val z.val))
    (mul A.val (add a.val a.val)) (mul D.val (add z.val z.val)) (mul A.val (add a.val a.val))
    (mul_valid D.property (add_valid z.property z.property)) (mul_valid A.property (add_valid a.property a.property))
    (mul_valid D.property (add_valid z.property z.property)) (mul_valid A.property (add_valid a.property a.property))
  have hh := Small.congr
    (add_valid (sub_valid (mul_valid D.property (add_valid z.property z.property)) (mul_valid A.property (add_valid a.property a.property)))
      (sub_valid (mul_valid D.property (add_valid z.property z.property)) (mul_valid A.property (add_valid a.property a.property))))
    (sub_valid (pairedRegularDivisionDerivativeTerm z hz n).property (pairedRegularDivisionDerivativeTerm a ha n).property)
    (equiv_symm he) (LocalODE.small_add hb hb)
  apply hh.mono
  have hr1 := reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
  rw [show reciprocalSquare 1=1 by decide +kernel] at hr1
  have hsqr := Rat.mul_le_mul_of_nonneg_left hr1 hr
  have hcub := Rat.mul_le_mul_of_nonneg_left hr1 (Rat.mul_nonneg hr hr)
  have hsH := Rat.mul_le_mul_of_nonneg_right hsqr hH
  have hcH := Rat.mul_le_mul_of_nonneg_right hcub hH
  dsimp [M,r] at *
  grind only

end ComputableAnalysis.ModularForms
