import ComputableAnalysis.RiemannHilbert.BoundaryCauchyAgreement

/-! Homogeneous bounds on the actual native Cauchy moments. Quantitative
data can be replaced by independently justified bounds without replacing the
original evaluator. Agreement of quadrature limits proves the transfer. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryCauchyHomogeneousEstimates
open ComplexRaw FunctionTheory DomainFunctions RectangularContour BoundaryCauchyPowers
set_option autoImplicit false

def constant (J : QInterval × QInterval) (R : Rat) : Rat :=
  16*scalarBound inverseGeometricPeriod*(J.1.width+J.2.width)*R

theorem constant_nonneg (J : QInterval × QInterval)
    (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi) (R : Rat) (hR : 0≤R) :
    0≤constant J R := by
  have hX : 0≤J.1.width := by unfold QInterval.width; grind only
  have hY : 0≤J.2.width := by unfold QInterval.width; grind only
  exact Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) (scalarBound_pos inverseGeometricPeriod)))
    (Rat.add_nonneg hX hY)) hR

theorem moment_bound (d : Data) (k : Nat) :
    Small (moment d k).val (constant d.rectangle d.reciprocalBound.val*d.valueBound.val*
      (2*d.reciprocalBound.val)^k) := by
  have hx : 0≤d.rectangle.1.width := by unfold QInterval.width; have h := d.xOrder; grind only
  have hy : 0≤d.rectangle.2.width := by unfold QInterval.width; have h := d.yOrder; grind only
  have hs := Small.mul inverseGeometricPeriod.property (value d (k+1)).property
    (Rat.le_of_lt (scalarBound_pos inverseGeometricPeriod))
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.add_nonneg hx hy))
      (Rat.le_of_lt d.valueBound.property)) (Rat.pow_nonneg
        (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) d.reciprocalBound.property))))
    (scalar_small inverseGeometricPeriod) (value_bound d (k+1))
  have he : 2*scalarBound inverseGeometricPeriod*
      (4*(d.rectangle.1.width+d.rectangle.2.width)*d.valueBound.val*(2*d.reciprocalBound.val)^(k+1))=
      constant d.rectangle d.reciprocalBound.val*d.valueBound.val*(2*d.reciprocalBound.val)^k := by
    dsimp [constant]
    rw [Rat.pow_succ]
    grind only
  simpa only [moment,scalarProduct,he] using hs

def rebounded (d : Data) (B R : QPos)
    (hB : RectangleBoundaryValueBound d.source d.rectangle d.sourceDomains B)
    (hR : RectangleBoundaryValueBound (ribbonPoleReciprocal d.center)
      d.rectangle d.reciprocalDomains R) : Data :=
  { d with valueBound := B, reciprocalBound := R, values := hB, reciprocals := hR }

theorem rebounded_agrees (d : Data) (B R : QPos)
    (hB : RectangleBoundaryValueBound d.source d.rectangle d.sourceDomains B)
    (hR : RectangleBoundaryValueBound (ribbonPoleReciprocal d.center)
      d.rectangle d.reciprocalDomains R) (k : Nat) :
    moment d k≈moment (rebounded d B R hB hR) k :=
  BoundaryCauchyAgreement.moment_agreement d (rebounded d B R hB hR) rfl (Setoid.refl _)
    (fun _ hd _ => equiv_refl _ (d.source.eval _ hd).property) k

theorem original_moment_bound (d : Data) (B R : QPos)
    (hB : RectangleBoundaryValueBound d.source d.rectangle d.sourceDomains B)
    (hR : RectangleBoundaryValueBound (ribbonPoleReciprocal d.center)
      d.rectangle d.reciprocalDomains R) (k : Nat) :
    Small (moment d k).val (constant d.rectangle R.val*B.val*(2*R.val)^k) :=
  Small.congr (moment (rebounded d B R hB hR) k).property (moment d k).property
    (equiv_symm (rebounded_agrees d B R hB hR k)) (moment_bound (rebounded d B R hB hR) k)

end ComputableAnalysis.RiemannHilbert.BoundaryCauchyHomogeneousEstimates
