import ComputableAnalysis.RiemannHilbert.ContourDerivativeCauchy

/-! A justified derivative bound controls every represented segment.
Executable local bounds are constructed from the supplied holomorphy data;
no uniform modulus is selected from an existential compactness statement. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem domainSegment_difference_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (p q : Scalar) (hp : f.domain p) (hq : f.domain q) (W B : QPos)
    (hdom : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (hd : Small (AffineSegment.displacement p q).val W.val)
    (hder : ∀ t : UnitInterval.Point,
      Small (hf.derivative (RepresentedAffineSegment.point p q t) (hdom t)).val B.val) :
    Small (sub (f.eval q hq).val (f.eval p hp).val) (4*B.val*W.val) := by
  let d : Scalar := ⟨zero,ofQComplex_valid _⟩
  have hr := domainSegment_remainder_bound f hf p q d hp hq W B hdom hd (by
    intro t
    have he : gridScalarSub (hf.derivative _ (hdom t)) d≈hf.derivative _ (hdom t) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := (gridScalarSub (hf.derivative _ (hdom t)) d).property)
        (hright := (hf.derivative _ (hdom t)).property)
      change gridScalarValue (hf.derivative _ (hdom t))-0=gridScalarValue (hf.derivative _ (hdom t))
      grind only
    exact Small.congr (hf.derivative _ (hdom t)).property
      (sub_valid (hf.derivative _ (hdom t)).property d.property) (equiv_symm he) (hder t))
  have he : (remainder f p hp d q hq).Equiv (sub (f.eval q hq).val (f.eval p hp).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := DomainFunctions.remainder_valid f p hp d q hq)
      (hright := sub_valid (f.eval q hq).property (f.eval p hp).property)
    let P := gridScalarValue (f.eval p hp)
    let Q := gridScalarValue (f.eval q hq)
    let Z := gridScalarValue q-gridScalarValue p
    change (Q-P)-0*Z=Q-P
    grind only
  exact Small.congr (DomainFunctions.remainder_valid f p hp d q hq)
    (sub_valid (f.eval q hq).property (f.eval p hp).property) he hr

def localHolomorphicRadius (f : DomainFunctions.Map) (hf : Holomorphic f) (a : Scalar) (ha : f.domain a) : QPos :=
  minRadius (hf.openDomain.radius a ha)
    (minRadius (hf.continuous.delta a ha unitError) (hf.continuousDerivative.delta a ha unitError))

def localHolomorphicValueBound (f : DomainFunctions.Map) (a : Scalar) (ha : f.domain a) : QPos :=
  ⟨scalarBound (f.eval a ha)+1,by have h := scalarBound_pos (f.eval a ha); grind only⟩

def localHolomorphicDerivativeBound (f : DomainFunctions.Map) (hf : Holomorphic f) (a : Scalar) (ha : f.domain a) : QPos :=
  ⟨scalarBound (hf.derivative a ha)+1,by have h := scalarBound_pos (hf.derivative a ha); grind only⟩

theorem localHolomorphic_domain (f : DomainFunctions.Map) (hf : Holomorphic f) (a : Scalar) (ha : f.domain a)
    (z : Scalar) (hz : Small (Centered.offset a z).val (localHolomorphicRadius f hf a ha).val) : f.domain z :=
  hf.openDomain.inside a ha z (hz.mono (minRadius_left _ _))

theorem localHolomorphic_value_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (a : Scalar) (ha : f.domain a)
    (z : Scalar) (hz : f.domain z) (hza : Small (Centered.offset a z).val (localHolomorphicRadius f hf a ha).val) :
    Small (f.eval z hz).val (localHolomorphicValueBound f a ha).val := by
  have hn : (localHolomorphicRadius f hf a ha).val≤(hf.continuous.delta a ha unitError).val :=
    Rat.le_trans (minRadius_right _ _) (minRadius_left _ _)
  have hs := LocalODE.small_add (scalar_small (f.eval a ha)) (hf.continuous.estimate a ha unitError z hz (hza.mono hn))
  exact Small.congr (add_valid (f.eval a ha).property (sub_valid (f.eval z hz).property (f.eval a ha).property))
    (f.eval z hz).property (SeriesLimitLaws.add_difference _ _ (f.eval z hz).property (f.eval a ha).property) hs

theorem localHolomorphic_derivative_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (a : Scalar) (ha : f.domain a)
    (z : Scalar) (hz : f.domain z) (hza : Small (Centered.offset a z).val (localHolomorphicRadius f hf a ha).val) :
    Small (hf.derivative z hz).val (localHolomorphicDerivativeBound f hf a ha).val := by
  have hn : (localHolomorphicRadius f hf a ha).val≤(hf.continuousDerivative.delta a ha unitError).val :=
    Rat.le_trans (minRadius_right _ _) (minRadius_right _ _)
  have hs := LocalODE.small_add (scalar_small (hf.derivative a ha))
    (hf.continuousDerivative.estimate a ha unitError z hz (hza.mono hn))
  exact Small.congr (add_valid (hf.derivative a ha).property (sub_valid (hf.derivative z hz).property (hf.derivative a ha).property))
    (hf.derivative z hz).property (SeriesLimitLaws.add_difference _ _ (hf.derivative z hz).property (hf.derivative a ha).property) hs

theorem localHolomorphic_difference_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (a : Scalar) (ha : f.domain a)
    (p q : Scalar) (hp : Small (Centered.offset a p).val (localHolomorphicRadius f hf a ha).val)
    (hq : Small (Centered.offset a q).val (localHolomorphicRadius f hf a ha).val)
    (W : QPos) (hd : Small (sub q.val p.val) W.val) :
    Small (sub (f.eval q (localHolomorphic_domain f hf a ha q hq)).val
      (f.eval p (localHolomorphic_domain f hf a ha p hp)).val)
      (4*(localHolomorphicDerivativeBound f hf a ha).val*W.val) := by
  let hdome := fun t => localHolomorphic_domain f hf a ha (RepresentedAffineSegment.point p q t)
    (RepresentedAffineSegment.offset_bound a p q t _ hp hq)
  exact domainSegment_difference_bound f hf p q _ _ W (localHolomorphicDerivativeBound f hf a ha) hdome hd
    (fun t => localHolomorphic_derivative_bound f hf a ha _ (hdome t)
      (RepresentedAffineSegment.offset_bound a p q t _ hp hq))

end ComputableAnalysis.RiemannHilbert.RectangularContour
