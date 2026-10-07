import ComputableAnalysis.ModularForms.LocalWeightedRemainderBound

/-! Exact affine midpoint cancellation with arbitrary represented coefficients.
For a rectangle, x and y are its two half-side vectors; the omitted common
factor two can be restored by represented scaling. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def affineMidpointModel (a d z : Scalar) : Scalar :=
  scalarSum a (scalarProduct d z)

def midpointWeightedCycle (right left top bottom x y : Scalar) : Scalar :=
  scalarSum
    (scalarSum (scalarProduct right y) (scalarProduct left (scalarNeg y)))
    (scalarSum (scalarProduct top (scalarNeg x)) (scalarProduct bottom x))

theorem affineMidpointCycle_zero (a d x y : Scalar) :
    (midpointWeightedCycle (affineMidpointModel a d x)
      (affineMidpointModel a d (scalarNeg x))
      (affineMidpointModel a d y) (affineMidpointModel a d (scalarNeg y)) x y).val.Equiv zero := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (midpointWeightedCycle (affineMidpointModel a d x)
      (affineMidpointModel a d (scalarNeg x))
      (affineMidpointModel a d y) (affineMidpointModel a d (scalarNeg y)) x y).property)
    (hright := ofQComplex_valid _)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let Y := ComplexRawQuotient.ofRaw y.val y.property
  change ((A+D*X)*Y+(A+D*(-X))*(-Y))+
    ((A+D*Y)*(-X)+(A+D*(-Y))*X)=0
  grind only

theorem midpointWeightedCycle_difference (r l t b r' l' t' b' x y : Scalar) :
    (sub (midpointWeightedCycle r l t b x y).val
      (midpointWeightedCycle r' l' t' b' x y).val).Equiv
      (midpointWeightedCycle
        ⟨sub r.val r'.val,sub_valid r.property r'.property⟩
        ⟨sub l.val l'.val,sub_valid l.property l'.property⟩
        ⟨sub t.val t'.val,sub_valid t.property t'.property⟩
        ⟨sub b.val b'.val,sub_valid b.property b'.property⟩ x y).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (midpointWeightedCycle r l t b x y).property
      (midpointWeightedCycle r' l' t' b' x y).property)
    (hright := (midpointWeightedCycle
      ⟨sub r.val r'.val,sub_valid r.property r'.property⟩
      ⟨sub l.val l'.val,sub_valid l.property l'.property⟩
      ⟨sub t.val t'.val,sub_valid t.property t'.property⟩
      ⟨sub b.val b'.val,sub_valid b.property b'.property⟩ x y).property)
  let R := ComplexRawQuotient.ofRaw r.val r.property
  let L := ComplexRawQuotient.ofRaw l.val l.property
  let T := ComplexRawQuotient.ofRaw t.val t.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let R' := ComplexRawQuotient.ofRaw r'.val r'.property
  let L' := ComplexRawQuotient.ofRaw l'.val l'.property
  let T' := ComplexRawQuotient.ofRaw t'.val t'.property
  let B' := ComplexRawQuotient.ofRaw b'.val b'.property
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let Y := ComplexRawQuotient.ofRaw y.val y.property
  change ((R*Y+L*(-Y))+(T*(-X)+B*X))-
    ((R'*Y+L'*(-Y))+(T'*(-X)+B'*X))=
      ((R-R')*Y+(L-L')*(-Y))+((T-T')*(-X)+(B-B')*X)
  grind only

end ComputableAnalysis.ModularForms
