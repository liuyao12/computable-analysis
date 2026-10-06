import ComputableAnalysis.RiemannHilbert.UnitIntervalSegments

/-! Exact composition laws for represented affine reparametrization.
All endpoints and all parameters may have non-singleton interval names. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
open ComplexRaw FunctionTheory

theorem affine_parameter_compose (p q : Scalar) (s t u : Point) :
    RepresentedAffineSegment.point (RepresentedAffineSegment.point p q s) (RepresentedAffineSegment.point p q t) u ≈
      RepresentedAffineSegment.point p q (segment s t u) := by
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (scalar (segment s t u)).property)
    (hright := (RepresentedAffineSegment.point (scalar s) (scalar t) u).property) (segment_scalar s t u)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (RepresentedAffineSegment.point (RepresentedAffineSegment.point p q s) (RepresentedAffineSegment.point p q t) u).property)
    (hright := (RepresentedAffineSegment.point p q (segment s t u)).property)
  let P := ComplexRawQuotient.ofRaw p.val p.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let S := ComplexRawQuotient.ofRaw (scalar s).val (scalar s).property
  let T := ComplexRawQuotient.ofRaw (scalar t).val (scalar t).property
  let U := ComplexRawQuotient.ofRaw (scalar u).val (scalar u).property
  let V := ComplexRawQuotient.ofRaw (scalar (segment s t u)).val (scalar (segment s t u)).property
  change V=S+(T-S)*U at he
  change (P+(Q-P)*S)+((P+(Q-P)*T)-(P+(Q-P)*S))*U=P+(Q-P)*V
  grind only

theorem segment_compose (a b s t u : Point) : segment (segment a b s) (segment a b t) u ≈ segment a b (segment s t u) := by
  apply scalar_reflects
  exact Setoid.trans (segment_scalar (segment a b s) (segment a b t) u)
    (Setoid.trans (RepresentedAffineSegment.point_congr (segment_scalar a b s) (segment_scalar a b t) (Setoid.refl u))
      (Setoid.trans (affine_parameter_compose (scalar a) (scalar b) s t u)
        (Setoid.symm (segment_scalar a b (segment s t u)))))

theorem segment_first_restriction (a b s t : Point) :
    segment a (segment a b s) t ≈ segment a b (segment zero s t) :=
  Setoid.trans (segment_congr (Setoid.symm (segment_zero a b)) (Setoid.refl _) (Setoid.refl t))
    (segment_compose a b zero s t)

theorem segment_second_restriction (a b s t : Point) :
    segment (segment a b s) b t ≈ segment a b (segment s one t) :=
  Setoid.trans (segment_congr (Setoid.refl _) (Setoid.symm (segment_one a b)) (Setoid.refl t))
    (segment_compose a b s one t)

end ComputableAnalysis.RiemannHilbert.UnitInterval
