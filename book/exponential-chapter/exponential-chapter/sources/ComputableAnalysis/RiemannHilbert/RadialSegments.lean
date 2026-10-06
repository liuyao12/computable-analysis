import ComputableAnalysis.RiemannHilbert.UniformPathUniqueness

/-! Rational meshes along segments with arbitrary represented complex endpoints. -/
namespace ComputableAnalysis.RiemannHilbert.RadialSegment
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

def point (z : Scalar) (t : Rat) : Scalar := ⟨scaleRat t z.val, scaleRat_valid z.property⟩

theorem point_zero (z : Scalar) : (point z 0).val.Equiv zero :=
  scaleRat_zeroScalar_equiv z.val z.property

theorem point_one (z : Scalar) : (point z 1).val.Equiv z.val :=
  scaleRat_one_equiv z.val z.property

theorem difference (z : Scalar) (s t : Rat) :
    (sub (point z t).val (point z s).val).Equiv (scaleRat (t-s) z.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (point z t).property (point z s).property)
    (hright := scaleRat_valid z.property)
  change ComplexRawQuotient.scaleRat t (ComplexRawQuotient.ofRaw z.val z.property)+
    -ComplexRawQuotient.scaleRat s (ComplexRawQuotient.ofRaw z.val z.property) =
    ComplexRawQuotient.scaleRat (t-s) (ComplexRawQuotient.ofRaw z.val z.property)
  rw [ComplexRawQuotient.neg_scaleRat, ComplexRawQuotient.add_scaleRat]
  rw [Rat.sub_eq_add_neg]

theorem difference_bound (z : Scalar) (R s t : Rat) (hz : Small z.val R) (hst : 0 ≤ t-s) :
    Small (sub (point z t).val (point z s).val) ((t-s)*R) :=
  Small.congr (scaleRat_valid z.property) (sub_valid (point z t).property (point z s).property)
    (equiv_symm (difference z s t)) (small_scale hst hz)

theorem mem (R : Rat) (z : Scalar) (hz : interior R z) (t : Rat) (ht : UniformPath.unitInterval t) :
    interior R (point z t) := by
  obtain ⟨r,hr,hrR,hzr⟩ := hz
  refine ⟨r,hr,hrR,?_⟩
  apply (small_scale ht.1 hzr).mono
  have h := Rat.mul_le_mul_of_nonneg_right ht.2 hr
  simpa only [Rat.one_mul] using h

theorem scale_difference (z : Scalar) (s t : Rat) (x : Fiber n) :
    Fiber.scale ⟨sub (point z t).val (point z s).val,
      sub_valid (point z t).property (point z s).property⟩ x ≈
      ratScale (t-s) (Fiber.scale z x) := by
  have he := Fiber.scale_congr
    (a := ⟨sub (point z t).val (point z s).val, sub_valid (point z t).property (point z s).property⟩)
    (b := ⟨scaleRat (t-s) z.val, scaleRat_valid z.property⟩)
    (difference z s t) (Setoid.refl x)
  intro d
  exact equiv_trans
    ((Fiber.scale ⟨sub (point z t).val (point z s).val,
      sub_valid (point z t).property (point z s).property⟩ x).property d)
    (mul_valid (scaleRat_valid z.property) (x.property d))
    ((ratScale (t-s) (Fiber.scale z x)).property d) (he d)
    (equiv_symm (scaleRat_mul_equiv (t-s) z.val (x.val d) z.property (x.property d)))

end ComputableAnalysis.RiemannHilbert.RadialSegment
