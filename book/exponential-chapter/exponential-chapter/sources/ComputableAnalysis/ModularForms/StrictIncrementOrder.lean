import ComputableAnalysis.ModularForms.RationalRotationStrictDecrease

/-! Exact represented order from a strict value-increment comparison. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem negative_increment_order (a b : Scalar)
    (h : (sub b.val a.val).realPart.Neg) : b.val.realPart.Le a.val.realPart := by
  obtain ⟨N,hN⟩ := h
  change (b.val.compute N).hi.re+ -(a.val.compute N).lo.re<0 at hN
  intro n m
  let M := max N (max n m)
  have hbN := (b.property.2.1 N M (Nat.le_max_left _ _)).2.1
  have haN := (a.property.2.1 N M (Nat.le_max_left _ _)).1
  have hbn := (b.property.2.1 n M (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))).1
  have ham := (a.property.2.1 m M (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))).2.1
  have hbo := valid_ordered b.property M
  have hao := valid_ordered a.property M
  have h5 := hbo.1
  have h6 := hao.1
  change (b.val.compute n).lo.re≤(a.val.compute m).hi.re
  grind only

theorem negative_increment_not_equiv (a b : Scalar)
    (h : (sub b.val a.val).realPart.Neg) : ¬b.val.realPart.Equiv a.val.realPart := by
  obtain ⟨N,hN⟩ := h
  change (b.val.compute N).hi.re+ -(a.val.compute N).lo.re<0 at hN
  intro he
  have ho := (RealRaw.compareAt_overlap_iff _ _ N N).1 (he N)
  have hh := ho.2
  change (a.val.compute N).lo.re≤(b.val.compute N).hi.re at hh
  grind only

theorem rational_rotation_order (u v : Rat) (hu : 1≤u) (hv : v≤2) (huv : u<v) :
    (angleRotationMap.eval (rationalAngleScalar v) ⟨trivial,trivial⟩).val.realPart.Le
      (angleRotationMap.eval (rationalAngleScalar u) ⟨trivial,trivial⟩).val.realPart :=
  negative_increment_order _ _ (rational_rotation_strict_decrease u v hu hv huv)

theorem rational_rotation_real_coordinate_distinct (u v : Rat)
    (hu : 1≤u) (hv : v≤2) (huv : u<v) :
    ¬(angleRotationMap.eval (rationalAngleScalar v) ⟨trivial,trivial⟩).val.realPart.Equiv
      (angleRotationMap.eval (rationalAngleScalar u) ⟨trivial,trivial⟩).val.realPart :=
  negative_increment_not_equiv _ _ (rational_rotation_strict_decrease u v hu hv huv)

theorem rational_rotation_order_of_le (u v : Rat) (hu : 1≤u) (hv : v≤2) (huv : u≤v) :
    (angleRotationMap.eval (rationalAngleScalar v) ⟨trivial,trivial⟩).val.realPart.Le
      (angleRotationMap.eval (rationalAngleScalar u) ⟨trivial,trivial⟩).val.realPart := by
  by_cases h : u<v
  · exact rational_rotation_order u v hu hv h
  · have he : u=v := by grind only
    subst v
    exact RealRaw.le_refl _ (realPart_valid
      (angleRotationMap.eval (rationalAngleScalar u) ⟨trivial,trivial⟩).property)

end ComputableAnalysis.ModularForms
