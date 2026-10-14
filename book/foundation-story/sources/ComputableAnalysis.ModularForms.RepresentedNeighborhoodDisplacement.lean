import ComputableAnalysis.ModularForms.BisectionCoverPrinciple
import ComputableAnalysis.RiemannHilbert.RepresentedAffineSegments

/-! Exact real neighborhoods give complex displacement bounds along affine
segments, including when the neighborhood center is irrational. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem realNeighborhood_complex_displacement (x : RealRaw) (q r : Rat)
    (hr : 0≤r) (hl : RealRaw.Le (RealRaw.ofRat (q-r)) x)
    (hh : RealRaw.Le x (RealRaw.ofRat (q+r))) :
    Small (sub (ofRealRaw (RealRaw.ofRat q)) (ofRealRaw x)) r := by
  constructor
  · intro n m
    have hb := hh m 0
    change (x.compute m).lo ≤ q+r at hb
    change -r ≤ q + -(x.compute m).lo
    grind only
  · constructor
    · intro n m
      have hb := hl 0 n
      change q-r ≤ (x.compute n).hi at hb
      change q + -(x.compute n).hi ≤ r
      grind only
    · constructor <;> intro n m <;> change _ ≤ _ <;>
        simp [sub,add,neg,ofRealRaw,RealRaw.ofRat,imagPart,
          QBox.add,QBox.neg,QComplex.add] <;> grind only

theorem representedAffine_rational_neighborhood (p q : Scalar)
    (t : UnitInterval.Point) (u : Rat) (hu0 : 0≤u) (hu1 : u≤1)
    (W r : Rat) (hW : 0≤W) (hr : 0≤r)
    (hd : Small (AffineSegment.displacement p q).val W)
    (hl : RealRaw.Le (RealRaw.ofRat (u-r)) t.value)
    (hh : RealRaw.Le t.value (RealRaw.ofRat (u+r))) :
    Small (sub (AffineSegment.point p q u).val
      (RepresentedAffineSegment.point p q t).val) (2*W*r) := by
  have ht := realNeighborhood_complex_displacement t.value u r hr hl hh
  have hb := RepresentedAffineSegment.difference_bound p q t
    (UnitInterval.rational u hu0 hu1) W r hW hr hd ht
  exact Small.congr
    (sub_valid (RepresentedAffineSegment.point p q (UnitInterval.rational u hu0 hu1)).property
      (RepresentedAffineSegment.point p q t).property)
    (sub_valid (AffineSegment.point p q u).property (RepresentedAffineSegment.point p q t).property)
    (add_equiv
      (RepresentedAffineSegment.rational_agreement p q u hu0 hu1)
      (neg_equiv (equiv_refl _ (RepresentedAffineSegment.point p q t).property))) hb

end ComputableAnalysis.ModularForms
