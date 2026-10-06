import ComputableAnalysis.RiemannHilbert.RationalLogarithmCharts

/-! Chart membership from a genuine reciprocal bound and distance from
the center. The normalized coordinate agrees with the reciprocal times
the displacement for every valid represented input. -/
namespace ComputableAnalysis.RiemannHilbert.RelativeLogarithm
open ComplexRaw FunctionTheory LocalODE NonzeroBoxSearch

theorem point_offset (c : Scalar) (hc : Nonzero c) (z : Scalar) :
    (point c hc z).val.Equiv (mul (RepresentedReciprocal.inverse c hc).val (sub z.val c.val)) := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (RepresentedReciprocal.inverse c hc).property c.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.inverse_mul c hc)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (point c hc z).property)
    (hright := mul_valid (RepresentedReciprocal.inverse c hc).property (sub_valid z.property c.property))
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  change R*C=1 at hi
  change -1+R*Z=R*(Z-C)
  grind only

theorem point_bound (c : Scalar) (hc : Nonzero c) (z : Scalar) (L H : Rat)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hi : Small (RepresentedReciprocal.inverse c hc).val L)
    (hz : Small (sub z.val c.val) H) : Small (point c hc z).val (2*L*H) :=
  Small.congr (mul_valid (RepresentedReciprocal.inverse c hc).property (sub_valid z.property c.property))
    (point c hc z).property (equiv_symm (point_offset c hc z))
    (Small.mul (RepresentedReciprocal.inverse c hc).property (sub_valid z.property c.property) hL hH hi hz)

theorem domain_of_distance (c : Scalar) (hc : Nonzero c) (z : Scalar) (L H : Rat)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hi : Small (RepresentedReciprocal.inverse c hc).val L)
    (hz : Small (sub z.val c.val) H) (hsmall : 2*L*H < LocalLogarithm.radius.val) : domain c hc z :=
  ⟨2*L*H,Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hL) hH,hsmall,point_bound c hc z L H hL hH hi hz⟩

end ComputableAnalysis.RiemannHilbert.RelativeLogarithm
