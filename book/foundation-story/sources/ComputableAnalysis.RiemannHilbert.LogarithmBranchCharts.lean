import ComputableAnalysis.RiemannHilbert.ScalarExponentialLaws
import ComputableAnalysis.RiemannHilbert.RelativeLogarithmCocycle

/-! Actual local logarithm germs with a supplied scalar normalization.
Recentered germs agree on a constructed open neighborhood, with genuine
holomorphicity, derivative and exponential semantics. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmBranchCharts
open ComplexRaw FunctionTheory LocalODE DomainFunctions NonzeroBoxSearch
set_option maxHeartbeats 1000000

def function (c : Scalar) (hc : Nonzero c) (a : Scalar) : DomainFunctions.Map where
  domain := RelativeLogarithm.domain c hc
  eval z hz := MatrixExponential.propagatedBranch c hc a z hz
  domain_congr := (RelativeLogarithm.function c hc).domain_congr
  eval_congr z w hz hw hzw := add_equiv (equiv_refl _ a.property)
    ((RelativeLogarithm.function c hc).eval_congr z w hz hw hzw)

theorem remainder_agreement (c : Scalar) (hc : Nonzero c) (a w z : Scalar)
    (hw : RelativeLogarithm.domain c hc w) (hz : RelativeLogarithm.domain c hc z) (d : Scalar) :
    (DomainFunctions.remainder (function c hc a) w hw d z hz).Equiv
      (DomainFunctions.remainder (RelativeLogarithm.function c hc) w hw d z hz) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _) (hright := DomainFunctions.remainder_valid _ _ _ _ _ _)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let W := ComplexRawQuotient.ofRaw ((RelativeLogarithm.function c hc).eval w hw).val ((RelativeLogarithm.function c hc).eval w hw).property
  let Z := ComplexRawQuotient.ofRaw ((RelativeLogarithm.function c hc).eval z hz).val ((RelativeLogarithm.function c hc).eval z hz).property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let H := ComplexRawQuotient.ofRaw (sub z.val w.val) (sub_valid z.property w.property)
  change ((A+Z)-(A+W))-D*H=(Z-W)-D*H
  grind only

def holomorphic (c : Scalar) (hc : Nonzero c) (a : Scalar) : DomainFunctions.Holomorphic (function c hc a) where
  openDomain := {
    radius := (RelativeLogarithm.holomorphic c hc).openDomain.radius
    inside := (RelativeLogarithm.holomorphic c hc).openDomain.inside }
  derivative := (RelativeLogarithm.holomorphic c hc).derivative
  atPoint w hw := {
    delta := ((RelativeLogarithm.holomorphic c hc).atPoint w hw).delta
    estimate eps H z hz hH hzw := Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _)
      (DomainFunctions.remainder_valid _ _ _ _ _ _) (equiv_symm (remainder_agreement c hc a w z hw hz _))
      (((RelativeLogarithm.holomorphic c hc).atPoint w hw).estimate eps H z hz hH hzw) }
  derivative_congr := (RelativeLogarithm.holomorphic c hc).derivative_congr
  continuousDerivative := (RelativeLogarithm.holomorphic c hc).continuousDerivative

theorem exponential (c : Scalar) (hc : Nonzero c) (a : Scalar)
    (ha : (MatrixExponential.scalarExponential a).val.Equiv c.val) (z : Scalar) (hz : (function c hc a).domain z) :
    (MatrixExponential.scalarExponential ((function c hc a).eval z hz)).val.Equiv z.val :=
  MatrixExponential.propagatedBranch_exponential c hc a ha z hz

theorem initial (c : Scalar) (hc : Nonzero c) (a : Scalar) :
    ((function c hc a).eval c (RelativeLogarithm.center_mem c hc)).val.Equiv a.val :=
  equiv_trans ((function c hc a).eval c (RelativeLogarithm.center_mem c hc)).property
    (add_valid a.property (ofQComplex_valid _)) a.property
    (add_equiv (equiv_refl _ a.property) (RelativeLogarithm.initial c hc)) (add_zero_equiv _ a.property)

theorem derivative_reciprocal (c : Scalar) (hc : Nonzero c) (a : Scalar)
    (hF : DomainFunctions.Holomorphic (function c hc a)) (z : Scalar) (hz : (function c hc a).domain z) :
    (hF.derivative z hz).val.Equiv (RepresentedReciprocal.inverse z (RelativeLogarithm.nonzero c hc z hz)).val :=
  equiv_trans (hF.derivative z hz).property ((holomorphic c hc a).derivative z hz).property
    (RepresentedReciprocal.inverse z (RelativeLogarithm.nonzero c hc z hz)).property
    (hF.derivative_unique (holomorphic c hc a) z hz)
    (RelativeLogarithm.derivative_reciprocal c hc (RelativeLogarithm.holomorphic c hc) z hz)

theorem value_congr (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (a b : Scalar)
    (hcd : c.val.Equiv d.val) (hab : a.val.Equiv b.val) (z w : Scalar)
    (hz : (function c hc a).domain z) (hw : (function d hd b).domain w) (hzw : z.val.Equiv w.val) :
    ((function c hc a).eval z hz).val.Equiv ((function d hd b).eval w hw).val :=
  add_equiv hab (RelativeLogarithm.value_congr c d hc hd hcd z w hz hw hzw)

/-- Recentring uses the continued value of the existing germ. The new
germ agrees with it throughout the open overlap through the next center. -/
theorem recenter_agreement (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (a : Scalar)
    (hcd : RelativeLogarithm.domain c hc d) (z : Scalar)
    (hz : RelativeLogarithm.commonDomain c d hc hd z) :
    ((function c hc a).eval z hz.1).val.Equiv
      ((function d hd ((function c hc a).eval d hcd)).eval z hz.2).val := by
  have hlog := RelativeLogarithm.cocycle c d hc hd hcd z hz
  have hs := add_equiv (equiv_refl _ a.property) hlog
  exact equiv_trans ((function c hc a).eval z hz.1).property
    (add_valid a.property (add_valid ((RelativeLogarithm.function c hc).eval d hcd).property
      ((RelativeLogarithm.function d hd).eval z hz.2).property))
    ((function d hd ((function c hc a).eval d hcd)).eval z hz.2).property hs
    (equiv_symm (add_assoc_equiv a.val ((RelativeLogarithm.function c hc).eval d hcd).val
      ((RelativeLogarithm.function d hd).eval z hz.2).val a.property
      ((RelativeLogarithm.function c hc).eval d hcd).property ((RelativeLogarithm.function d hd).eval z hz.2).property))

def overlapRadius (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d)
    (hcd : RelativeLogarithm.domain c hc d) : QPos :=
  QPos.minimum ((RelativeLogarithm.holomorphic c hc).openDomain.radius d hcd)
    ((RelativeLogarithm.holomorphic d hd).openDomain.radius d (RelativeLogarithm.center_mem d hd))

theorem overlapRadius_inside (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d)
    (hcd : RelativeLogarithm.domain c hc d) (z : Scalar)
    (hzd : Small (sub z.val d.val) (overlapRadius c d hc hd hcd).val) :
    RelativeLogarithm.commonDomain c d hc hd z :=
  ⟨(RelativeLogarithm.holomorphic c hc).openDomain.inside d hcd z (hzd.mono (QPos.minimum_le_left _ _)),
    (RelativeLogarithm.holomorphic d hd).openDomain.inside d (RelativeLogarithm.center_mem d hd) z
      (hzd.mono (QPos.minimum_le_right _ _))⟩

end ComputableAnalysis.RiemannHilbert.LogarithmBranchCharts
