import ComputableAnalysis.ModularForms.LatticeProductZeroPropagation

/-! Whole represented affine segments stay in the upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 2000000

theorem representedAffine_box_sample (p q : Scalar) (t : UnitInterval.Point) (n : Nat) :
    let r := UnitInterval.clamp (((t.value.compute n).lo+(t.value.compute n).hi)/2)
    let x := QComplex.add (p.val.compute n).lo
      (QComplex.mul (QComplex.sub (q.val.compute n).lo (p.val.compute n).lo) (QComplex.ofRat r))
    x≤((RepresentedAffineSegment.point p q t).val.compute n).hi := by
  let r := UnitInterval.clamp (((t.value.compute n).lo+(t.value.compute n).hi)/2)
  have hp := ComplexRaw.valid_ordered p.property n
  have hq := ComplexRaw.valid_ordered q.property n
  have hpord := hp
  simp only [QBox.Ordered,QComplex.le_def] at hp hq
  have ht := UnitInterval.clamped_midpoint_mem t n
  have hs : ((UnitInterval.scalar t).val.compute n).lo≤QComplex.ofRat r ∧
      QComplex.ofRat r≤((UnitInterval.scalar t).val.compute n).hi :=
    ⟨⟨ht.1,Rat.le_refl⟩,⟨ht.2,Rat.le_refl⟩⟩
  have hdiff : ((Centered.offset p q).val.compute n).lo≤
      QComplex.sub (q.val.compute n).lo (p.val.compute n).lo ∧
      QComplex.sub (q.val.compute n).lo (p.val.compute n).lo≤((Centered.offset p q).val.compute n).hi := by
    constructor <;> simp only [Centered.offset,sub,neg,add,QBox.add,QBox.neg,QComplex.add,QComplex.sub,QComplex.neg,QComplex.le_def]
      <;> grind only
  have hm := QBox.mul_contains hdiff.1 hdiff.2 hs.1 hs.2
  have ha := QBox.add_contains (QComplex.le_refl (p.val.compute n).lo) hpord hm.1 hm.2
  exact ha.2

theorem representedAffine_upper_mem (p q : Scalar) (hp : InUpperHalfPlane p.val)
    (hq : InUpperHalfPlane q.val) (t : UnitInterval.Point) :
    InUpperHalfPlane (RepresentedAffineSegment.point p q t).val := by
  obtain ⟨Np,hp⟩ := hp
  obtain ⟨Nq,hq⟩ := hq
  change 0<(p.val.compute Np).lo.im at hp
  change 0<(q.val.compute Nq).lo.im at hq
  let m := min (p.val.compute Np).lo.im (q.val.compute Nq).lo.im
  have hm : 0<m := by grind
  let eps : QPos := ⟨m/2,by rw [Rat.div_def]; exact Rat.mul_pos hm (by decide +kernel)⟩
  let z := RepresentedAffineSegment.point p q t
  obtain ⟨K,hK⟩ := (ComplexRaw.imagPart_valid z.property).2.2 eps
  let M := max Np (max Nq K)
  have hpM := (p.property.2.1 Np M (Nat.le_max_left _ _)).2.2.1
  have hqM := (q.property.2.1 Nq M (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))).2.2.1
  have hw := hK M (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have hs := representedAffine_box_sample p q t M
  let r := UnitInterval.clamp (((t.value.compute M).lo+(t.value.compute M).hi)/2)
  have hr := UnitInterval.clamp_bounds (((t.value.compute M).lo+(t.value.compute M).hi)/2)
  have h1 : 0≤1-r := by dsimp [r]; grind only
  have hp0 : m≤(p.val.compute M).lo.im := by grind
  have hq0 : m≤(q.val.compute M).lo.im := by grind
  have hpl := Rat.mul_le_mul_of_nonneg_left hp0 h1
  have hql := Rat.mul_le_mul_of_nonneg_left hq0 hr.1
  have hb := hs.2
  simp only [QComplex.add,QComplex.mul,QComplex.sub,QComplex.neg,QComplex.ofRat,Rat.mul_zero,Rat.zero_add,Rat.add_zero] at hb
  change (p.val.compute M).lo.im+((q.val.compute M).lo.im+ -(p.val.compute M).lo.im)*r≤(z.val.compute M).hi.im at hb
  change (z.val.compute M).hi.im-(z.val.compute M).lo.im≤m/2 at hw
  refine ⟨M,?_⟩
  change 0<(z.val.compute M).lo.im
  grind only

theorem latticeHalfShift_upper_mem (z : Scalar) (hz : InUpperHalfPlane z.val) :
    InUpperHalfPlane (latticeHalfShiftMap.eval z trivial).val := by
  have he : (latticeHalfShiftMap.eval z trivial).val.Equiv (translate (1/2) z.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (latticeHalfShiftMap.eval z trivial).property) (hright := translate_valid _ z.property)
    let Z := gridScalarValue z
    let H := gridScalarValue latticeHalfPoint
    change H+1*Z=Z+H
    grind only
  exact (upperHalfPlane_congr (latticeHalfShiftMap.eval z trivial).property
    (translate_valid _ z.property) he).mpr (translate_mem (1/2) hz)

theorem latticeProductError_upper_mem (z : Scalar) (hz : InUpperHalfPlane z.val) :
    latticeHalfShiftProductErrorMap.domain z :=
  ⟨⟨pairedGlobalOffPole_upper_mem z hz,
    ⟨trivial,pairedGlobalOffPole_upper_mem _ (latticeHalfShift_upper_mem z hz)⟩⟩,trivial⟩

theorem latticeProductError_upper_segment_mem (p q : Scalar)
    (hp : InUpperHalfPlane p.val) (hq : InUpperHalfPlane q.val) (t : UnitInterval.Point) :
    latticeHalfShiftProductErrorMap.domain (RepresentedAffineSegment.point p q t) :=
  latticeProductError_upper_mem _ (representedAffine_upper_mem p q hp hq t)

theorem latticeProductError_upper_segment_zero (p q : Scalar)
    (hp : InUpperHalfPlane p.val) (hq : InUpperHalfPlane q.val)
    (he : (latticeHalfShiftProductErrorMap.eval p (latticeProductError_upper_mem p hp)).val.Equiv zero) :
    (latticeHalfShiftProductErrorMap.eval q (latticeProductError_upper_mem q hq)).val.Equiv zero :=
  latticeProductError_segment_zero p q (latticeProductError_upper_mem p hp)
    (latticeProductError_upper_mem q hq) (latticeProductError_upper_segment_mem p q hp hq) he

end ComputableAnalysis.ModularForms
