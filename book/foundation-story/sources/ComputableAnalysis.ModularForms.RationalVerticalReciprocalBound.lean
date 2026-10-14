import ComputableAnalysis.ModularForms.RationalReciprocalBound
import ComputableAnalysis.ModularForms.UpperLatticeSampleReciprocal

/-! Reciprocal bounds independent of the real coordinate above a horizontal line. -/
namespace ComputableAnalysis.ModularForms

private theorem vertical_square_nonnegative (x : Rat) : 0≤x*x := by
  by_cases h : 0≤x
  · exact Rat.mul_nonneg h h
  · have hm := Rat.mul_nonneg (show 0≤ -x by grind only) (show 0≤ -x by grind only)
    grind only

theorem rationalVertical_norm_positive (a b eta : Rat) (heta : 0<eta) (hb : eta≤b) :
    0<a*a+b*b := by
  have ha := vertical_square_nonnegative a
  have hbp : 0<b := by grind only
  have hbb := Rat.mul_pos hbp hbp
  grind only

theorem rationalVertical_reciprocal_bounds (a b eta : Rat)
    (heta : 0<eta) (hb : eta≤b) :
    (-(1/eta)≤a/(a*a+b*b) ∧ a/(a*a+b*b)≤1/eta) ∧
    (-(1/eta)≤ -b/(a*a+b*b) ∧ -b/(a*a+b*b)≤1/eta) := by
  let D := a*a+b*b
  have hD : 0<D := rationalVertical_norm_positive a b eta heta hb
  have he := Rat.mul_inv_cancel eta (Rat.ne_of_gt heta)
  have hd := Rat.mul_inv_cancel D (Rat.ne_of_gt hD)
  have haa := vertical_square_nonnegative a
  have hbb := Rat.mul_nonneg (show 0≤b by grind only) (show 0≤b-eta by grind only)
  have hm := vertical_square_nonnegative (a-eta)
  have hp := vertical_square_nonnegative (a+eta)
  have hbe := Rat.mul_nonneg (show 0≤b-eta by grind only) (show 0≤b+eta by grind only)
  have haU : a*eta≤D := by dsimp [D] at *; grind only
  have haL : -a*eta≤D := by dsimp [D] at *; grind only
  have hbU : b*eta≤D := by dsimp [D]; grind only
  have bound (x : Rat) (hx : x*eta≤D) : x/D≤1/eta := by
    apply Rat.le_of_mul_le_mul_right (c := D*eta)
    · calc
        _ = x*eta := by grind [Rat.div_def]
        _ ≤ D := hx
        _ = _ := by grind [Rat.div_def]
    · exact Rat.mul_pos hD heta
  have h1 := bound a haU
  have h2 := bound (-a) haL
  have h3 := bound b hbU
  have h4 := bound (-b) (show -b*eta≤D by
    have hn := Rat.mul_nonneg (show 0≤b by grind only) (Rat.le_of_lt heta)
    grind only)
  constructor <;> constructor <;> grind [Rat.div_def]

theorem rationalIntegerTranslate_reciprocal_bounds (q : QComplex) (k : Int) (eta : Rat)
    (heta : 0<eta) (hq : eta≤q.im) :
    (-(1/eta)≤(rationalLatticeInverse q (k:Rat) 1).re ∧
      (rationalLatticeInverse q (k:Rat) 1).re≤1/eta) ∧
    (-(1/eta)≤(rationalLatticeInverse q (k:Rat) 1).im ∧
      (rationalLatticeInverse q (k:Rat) 1).im≤1/eta) := by
  simpa only [rationalLatticeInverse,rationalLatticeNorm,Rat.one_mul] using
    rationalVertical_reciprocal_bounds ((k:Rat)+q.re) q.im eta heta hq

theorem representedIntegerTranslate_sample_reciprocal_bounds
    (z : RiemannHilbert.Scalar) (N n : Nat) (hn : N≤n) (eta : Rat)
    (heta : 0<eta) (hN : eta≤(z.val.compute N).lo.im)
    (q : QComplex) (hq : (z.val.compute n).lo≤q ∧ q≤(z.val.compute n).hi)
    (k : Int) :
    (-(1/eta)≤(rationalLatticeInverse q (k:Rat) 1).re ∧
      (rationalLatticeInverse q (k:Rat) 1).re≤1/eta) ∧
    (-(1/eta)≤(rationalLatticeInverse q (k:Rat) 1).im ∧
      (rationalLatticeInverse q (k:Rat) 1).im≤1/eta) := by
  have hs := (z.property.2.1 N n hn).2.2.1
  exact rationalIntegerTranslate_reciprocal_bounds q k eta heta
    (Rat.le_trans hN (Rat.le_trans hs hq.1.2))

end ComputableAnalysis.ModularForms
