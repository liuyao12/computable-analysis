import ComputableAnalysis.ModularForms.RationalLatticeNumeratorBounds

/-! Uniform reciprocal-radius bounds for actual rational lattice samples. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

def rationalLatticeInverse (q : QComplex) (x y : Rat) : QComplex :=
  ⟨(x+y*q.re)/rationalLatticeNorm q x y,-(y*q.im)/rationalLatticeNorm q x y⟩

def latticeReciprocalConstant (z : Scalar) (hz : InUpperHalfPlane z.val) : Rat :=
  let R := latticeRegionWidth z hz
  let H := latticeRegionHeight z hz
  let eta := latticeRegionMargin z hz
  (2*eta*eta+2*R*R+1)*(1+R+H)/(eta*eta)

theorem latticeReciprocalConstant_nonnegative (z : Scalar) (hz : InUpperHalfPlane z.val) :
    0≤latticeReciprocalConstant z hz := by
  have hR := latticeRegionWidth_nonnegative z hz
  have hH := latticeRegionHeight_nonnegative z hz
  have he := latticeRegionMargin_positive z hz
  have he2 := Rat.mul_pos he he
  have hR2 := Rat.mul_nonneg hR hR
  have hC : 0≤2*latticeRegionMargin z hz*latticeRegionMargin z hz+
      2*latticeRegionWidth z hz*latticeRegionWidth z hz+1 := by grind
  have hA : 0≤1+latticeRegionWidth z hz+latticeRegionHeight z hz := by grind
  exact Rat.mul_nonneg (Rat.mul_nonneg hC hA) (Rat.le_of_lt (Rat.inv_pos.mpr he2))

/-- Uniform bounds on every later rational sample of the supplied represented input.
The only index hypotheses describe membership in a square shell. -/
theorem latticeSample_inverse_bounds (z : Scalar) (hz : InUpperHalfPlane z.val)
    (n : Nat) (hn : latticeRegionStage z hz≤n) (q : QComplex)
    (hq : (z.val.compute n).lo≤q ∧ q≤(z.val.compute n).hi)
    (x y r : Rat) (hr : 0<r) (hx : -r≤x ∧ x≤r) (hy : -r≤y ∧ y≤r)
    (hout : r≤x ∨ x≤ -r ∨ r≤y ∨ y≤ -r) :
    (-(latticeReciprocalConstant z hz/r)≤(rationalLatticeInverse q x y).re ∧
      (rationalLatticeInverse q x y).re≤latticeReciprocalConstant z hz/r) ∧
    (-(latticeReciprocalConstant z hz/r)≤(rationalLatticeInverse q x y).im ∧
      (rationalLatticeInverse q x y).im≤latticeReciprocalConstant z hz/r) := by
  have hs := latticeRegion_sample z _ _ (latticeRegionStage z hz) n
    (latticeRegionSearch_spec z hz) hn q hq
  have hh := latticeRegion_sample_height z hz n hn q hq
  exact rationalLattice_box_reciprocal_bounds q x y r
    (latticeRegionWidth z hz) (latticeRegionHeight z hz) (latticeRegionMargin z hz)
    hr (latticeRegionWidth_nonnegative z hz) (latticeRegionHeight_nonnegative z hz)
    (latticeRegionMargin_positive z hz) hx hy hs.1 ⟨hs.2,hh⟩ hout

theorem rationalLatticeInverse_product (q : QComplex) (x y : Rat)
    (hN : rationalLatticeNorm q x y≠0) :
    QComplex.mul ⟨x+y*q.re,y*q.im⟩ (rationalLatticeInverse q x y)=QComplex.one := by
  have hc := Rat.mul_inv_cancel (rationalLatticeNorm q x y) hN
  simp only [QComplex.mul,QComplex.one,rationalLatticeInverse]
  congr 1
  · unfold rationalLatticeNorm at hc
    grind [Rat.div_def,rationalLatticeNorm]
  · grind [Rat.div_def]

end ComputableAnalysis.ModularForms
