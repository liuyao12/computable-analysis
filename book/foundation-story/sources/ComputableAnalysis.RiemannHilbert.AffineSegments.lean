import ComputableAnalysis.RiemannHilbert.TranslatedHolomorphic

/-! Affine segments with arbitrary represented complex endpoints. Convex
coverage of a centered disk is proved from rational coordinate bounds. -/
namespace ComputableAnalysis.RiemannHilbert.AffineSegment
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

def displacement (p q : Scalar) : Scalar := Centered.offset p q
def point (p q : Scalar) (t : Rat) : Scalar := Centered.translate p (RadialSegment.point (displacement p q) t)

theorem point_zero (p q : Scalar) : (point p q 0).val.Equiv p.val :=
  equiv_trans (point p q 0).property (add_valid p.property (ofQComplex_valid _)) p.property
    (add_equiv (equiv_refl _ p.property) (RadialSegment.point_zero (displacement p q))) (add_zero_equiv _ p.property)

theorem point_one (p q : Scalar) : (point p q 1).val.Equiv q.val :=
  equiv_trans (point p q 1).property (Centered.translate p (displacement p q)).property q.property
    (add_equiv (equiv_refl _ p.property) (RadialSegment.point_one (displacement p q))) (Centered.translate_offset p q)

theorem difference (p q : Scalar) (s t : Rat) :
    (sub (point p q t).val (point p q s).val).Equiv (scaleRat (t-s) (displacement p q).val) :=
  equiv_trans (sub_valid (point p q t).property (point p q s).property)
    (sub_valid (RadialSegment.point (displacement p q) t).property (RadialSegment.point (displacement p q) s).property)
    (scaleRat_valid (displacement p q).property)
    (Centered.translate_difference p (RadialSegment.point (displacement p q) s) (RadialSegment.point (displacement p q) t))
    (RadialSegment.difference (displacement p q) s t)

theorem difference_bound (p q : Scalar) (W s t : Rat)
    (hW : Small (displacement p q).val W) (hst : 0 ≤ t-s) :
    Small (sub (point p q t).val (point p q s).val) ((t-s)*W) :=
  Small.congr (scaleRat_valid (displacement p q).property)
    (sub_valid (point p q t).property (point p q s).property) (equiv_symm (difference p q s t))
    (small_scale hst hW)

theorem scale_difference (p q : Scalar) (s t : Rat) (x : Fiber n) :
    Fiber.scale ⟨sub (point p q t).val (point p q s).val, sub_valid (point p q t).property (point p q s).property⟩ x ≈
      ratScale (t-s) (Fiber.scale (displacement p q) x) := by
  have h := Fiber.scale_congr
    (a := ⟨sub (point p q t).val (point p q s).val, sub_valid (point p q t).property (point p q s).property⟩)
    (b := ⟨scaleRat (t-s) (displacement p q).val, scaleRat_valid (displacement p q).property⟩)
    (difference p q s t) (Setoid.refl x)
  intro i
  exact equiv_trans
    ((Fiber.scale ⟨sub (point p q t).val (point p q s).val, sub_valid (point p q t).property (point p q s).property⟩ x).property i)
    (mul_valid (scaleRat_valid (displacement p q).property) (x.property i))
    ((ratScale (t-s) (Fiber.scale (displacement p q) x)).property i) (h i)
    (equiv_symm (scaleRat_mul_equiv (t-s) (displacement p q).val (x.val i) (displacement p q).property (x.property i)))

private theorem scale_neg (t : Rat) (X : ScalarAlgebra.Value) :
    ComplexRawQuotient.scaleRat t (-X) = -ComplexRawQuotient.scaleRat t X := by
  rw [ComplexRawQuotient.neg_eq_scaleRat_neg_one X, ComplexRawQuotient.scaleRat_scaleRat,
    ComplexRawQuotient.neg_scaleRat]
  congr 1
  grind

private theorem scale_sub (t : Rat) (X Y : ScalarAlgebra.Value) :
    ComplexRawQuotient.scaleRat t (X-Y) =
      ComplexRawQuotient.scaleRat t X-ComplexRawQuotient.scaleRat t Y := by
  change ComplexRawQuotient.scaleRat t (X+ -Y) = _
  rw [ComplexRawQuotient.scaleRat_add, scale_neg]
  rfl

private theorem scale_complement (t : Rat) (X : ScalarAlgebra.Value) :
    ComplexRawQuotient.scaleRat (1-t) X = X-ComplexRawQuotient.scaleRat t X := by
  have h := ComplexRawQuotient.add_scaleRat (1-t) t X
  have ht : 1-t+t=1 := by grind
  rw [ht, ComplexRawQuotient.scaleRat_one] at h
  grind

theorem offset_barycentric (c p q : Scalar) (t : Rat) :
    (Centered.offset c (point p q t)).val.Equiv
      (add (scaleRat (1-t) (Centered.offset c p).val) (scaleRat t (Centered.offset c q).val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (Centered.offset c (point p q t)).property)
    (hright := add_valid (scaleRat_valid (Centered.offset c p).property) (scaleRat_valid (Centered.offset c q).property))
  let X := ComplexRawQuotient.ofRaw p.val p.property
  let Y := ComplexRawQuotient.ofRaw q.val q.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  change (X+ComplexRawQuotient.scaleRat t (Y-X))-C =
    ComplexRawQuotient.scaleRat (1-t) (X-C)+ComplexRawQuotient.scaleRat t (Y-C)
  rw [scale_sub, scale_sub, scale_sub, scale_complement, scale_complement]
  grind

theorem mem (c p q : Scalar) (R : Rat) (hp : Centered.domain c R p) (hq : Centered.domain c R q)
    (t : Rat) (ht : UniformPath.unitInterval t) : Centered.domain c R (point p q t) := by
  obtain ⟨rp,hrp,hrpR,hpr⟩ := hp
  obtain ⟨rq,hrq,hrqR,hqr⟩ := hq
  let r := max rp rq
  have hr : 0 ≤ r := by dsimp [r]; grind
  have hrR : r < R := by dsimp [r]; grind
  have hpB : Small (Centered.offset c p).val r := hpr.mono (by dsimp [r]; grind)
  have hqB : Small (Centered.offset c q).val r := hqr.mono (by dsimp [r]; grind)
  have h1 : 0 ≤ 1-t := by grind
  have hs := small_add (small_scale h1 hpB) (small_scale ht.1 hqB)
  have he : (1-t)*r+t*r=r := by grind
  rw [he] at hs
  exact ⟨r,hr,hrR,Small.congr
    (add_valid (scaleRat_valid (Centered.offset c p).property) (scaleRat_valid (Centered.offset c q).property))
    (Centered.offset c (point p q t)).property (equiv_symm (offset_barycentric c p q t)) hs⟩

end ComputableAnalysis.RiemannHilbert.AffineSegment
