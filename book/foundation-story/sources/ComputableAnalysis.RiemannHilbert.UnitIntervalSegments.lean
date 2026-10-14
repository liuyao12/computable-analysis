import ComputableAnalysis.RiemannHilbert.UnitIntervalScalarAlgebra

/-! Affine reparametrization between arbitrary represented unit parameters.
The whole-image bound comes from the proved represented affine convexity
theorem; the output is not restricted to rational subdivision points. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
open ComplexRaw FunctionTheory DomainFunctions

def halfScalar : Scalar := ⟨ofQComplex ⟨1/2,0⟩,ofQComplex_valid _⟩

theorem centeredHalf_bound (t : Point) : Small (Centered.offset halfScalar (scalar t)).val (1/2) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n m
    have h := t.lower 0 m
    change 0 ≤ (t.value.compute m).hi at h
    change -(1/2 : Rat) ≤ (t.value.compute m).hi+ -(1/2)
    grind only
  · intro n m
    have h := t.upper n 0
    change (t.value.compute n).lo ≤ 1 at h
    change (t.value.compute n).lo+ -(1/2) ≤ (1/2 : Rat)
    grind only
  · intro n m
    change -(1/2 : Rat) ≤ 0+ -0
    decide +kernel
  · intro n m
    change (0 : Rat)+ -0 ≤ 1/2
    decide +kernel

def segmentRaw (a b t : Point) : RealRaw :=
  (RepresentedAffineSegment.point (scalar a) (scalar b) t).val.realPart

theorem segmentRaw_valid (a b t : Point) : (segmentRaw a b t).Valid :=
  realPart_valid (RepresentedAffineSegment.point (scalar a) (scalar b) t).property

theorem segment_bound (a b t : Point) :
    Small (Centered.offset halfScalar (RepresentedAffineSegment.point (scalar a) (scalar b) t)).val (1/2) :=
  RepresentedAffineSegment.offset_bound halfScalar (scalar a) (scalar b) t (1/2)
    (centeredHalf_bound a) (centeredHalf_bound b)

def segment (a b t : Point) : Point where
  value := segmentRaw a b t
  valid := segmentRaw_valid a b t
  lower n m := by
    have h := (segment_bound a b t).1 n m
    change -(1/2 : Rat) ≤ ((RepresentedAffineSegment.point (scalar a) (scalar b) t).val.compute m).hi.re+ -(1/2) at h
    change 0 ≤ ((RepresentedAffineSegment.point (scalar a) (scalar b) t).val.compute m).hi.re
    grind only
  upper n m := by
    have h := (segment_bound a b t).2.1 n m
    change ((RepresentedAffineSegment.point (scalar a) (scalar b) t).val.compute n).lo.re+ -(1/2) ≤ (1/2 : Rat) at h
    change ((RepresentedAffineSegment.point (scalar a) (scalar b) t).val.compute n).lo.re ≤ 1
    grind only

theorem segment_congr {a a' b b' s t : Point} (ha : a ≈ a') (hb : b ≈ b') (hst : s ≈ t) :
    segment a b s ≈ segment a' b' t :=
  realPart_equiv (RepresentedAffineSegment.point_congr (scalar_congr ha) (scalar_congr hb) hst)

theorem segment_zero (a b : Point) : segment a b zero ≈ a :=
  realPart_equiv (RepresentedAffineSegment.point_zero (scalar a) (scalar b))

theorem segment_one (a b : Point) : segment a b one ≈ b :=
  realPart_equiv (RepresentedAffineSegment.point_one (scalar a) (scalar b))

theorem segment_self (a t : Point) : segment a a t ≈ a :=
  realPart_equiv (RepresentedAffineSegment.point_self (scalar a) t)

theorem segment_reverse (a b t : Point) : segment a b (reverse t) ≈ segment b a t :=
  realPart_equiv (RepresentedAffineSegment.reverse (scalar a) (scalar b) t)

theorem segment_imaginary (a b t : Point) (n : Nat) :
    ((RepresentedAffineSegment.point (scalar a) (scalar b) t).val.compute n).lo.im = 0 ∧
      ((RepresentedAffineSegment.point (scalar a) (scalar b) t).val.compute n).hi.im = 0 := by
  simp [RepresentedAffineSegment.point,RepresentedAffineSegment.function,DomainFunctions.affine,Centered.offset,
    scalar,scalarSum,scalarProduct,ComplexRaw.sub,ComplexRaw.add,ComplexRaw.neg,ComplexRaw.mul,ofRealRaw,
    QBox.add,QBox.neg,QBox.mul,QBox.mulRealInterval,QComplex.add,min4,max4,minRat,maxRat2] <;> grind

theorem segment_scalar (a b t : Point) : scalar (segment a b t) ≈ RepresentedAffineSegment.point (scalar a) (scalar b) t := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).2
  have ho := valid_ordered (RepresentedAffineSegment.point (scalar a) (scalar b) t).property n
  have hi := segment_imaginary a b t n
  change (_ ≤ _ ∧ (0 : Rat) ≤ _) ∧ (_ ≤ _ ∧ _ ≤ (0 : Rat))
  exact ⟨⟨ho.1,by rw [hi.2]; exact Rat.le_refl⟩,⟨ho.1,by rw [hi.1]; exact Rat.le_refl⟩⟩

def segmentContinuousData (a b : Point) : ContinuousData (segment a b) where
  congr _ _ hst := segment_congr (Setoid.refl a) (Setoid.refl b) hst
  delta := (RepresentedAffineSegment.continuousData (scalar a) (scalar b)).delta
  estimate s eps t ht := by
    have h := (RepresentedAffineSegment.continuousData (scalar a) (scalar b)).estimate s eps t ht
    exact ⟨h.1,h.2.1,fun _ _ => by change -eps.val ≤ (0 : Rat)+ -0; have he := eps.property; grind only,
      fun _ _ => by change (0 : Rat)+ -0 ≤ eps.val; have he := eps.property; grind only⟩

theorem segment_identity (t : Point) : segment zero one t ≈ t := by
  apply scalar_reflects
  apply Setoid.trans (segment_scalar zero one t)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (RepresentedAffineSegment.point (scalar zero) (scalar one) t).property) (hright := (scalar t).property)
  let T := ComplexRawQuotient.ofRaw (scalar t).val (scalar t).property
  change 0+(1-0)*T=T
  grind only

end ComputableAnalysis.RiemannHilbert.UnitInterval
