import ComputableAnalysis.RiemannHilbert.LocalLogarithmUniform
import ComputableAnalysis.RiemannHilbert.DomainAffineFunction
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicValueLaws

/-! A normalized local logarithm at every nonzero represented center.
The reciprocal, normalized coordinate, open chart, actual derivative and
normalization are constructed. No logarithm value at the center is supplied. -/
namespace ComputableAnalysis.RiemannHilbert.RelativeLogarithm
open ComplexRaw FunctionTheory LocalODE DomainFunctions NonzeroBoxSearch
set_option maxHeartbeats 800000

def normalizedCoordinate (c : Scalar) (hc : Nonzero c) : DomainFunctions.Map :=
  affine (scalarNeg oneScalar) (RepresentedReciprocal.inverse c hc)

def point (c : Scalar) (hc : Nonzero c) (z : Scalar) : Scalar :=
  (normalizedCoordinate c hc).eval z True.intro

def domain (c : Scalar) (hc : Nonzero c) (z : Scalar) : Prop := interior LocalLogarithm.radius.val (point c hc z)

def function (c : Scalar) (hc : Nonzero c) : DomainFunctions.Map where
  domain := domain c hc
  eval z hz := LocalLogarithm.function.eval (point c hc z) hz
  domain_congr z w hzw := LocalLogarithm.function.domain_congr _ _
    ((normalizedCoordinate c hc).eval_congr z w True.intro True.intro hzw)
  eval_congr z w hz hw hzw := LocalLogarithm.function.eval_congr _ _ hz hw
    ((normalizedCoordinate c hc).eval_congr z w True.intro True.intro hzw)

def holomorphic (c : Scalar) (hc : Nonzero c) : DomainFunctions.Holomorphic (function c hc) :=
  let h := LocalLogarithm.holomorphic.compose (affine_holomorphic (scalarNeg oneScalar) (RepresentedReciprocal.inverse c hc))
  h.transfer (function c hc) (fun _ hz => ⟨True.intro,hz⟩)
    { radius := fun a ha => h.openDomain.radius a ⟨True.intro,ha⟩
      inside := fun a ha z hza => compose_outer_mem (h.openDomain.inside a ⟨True.intro,ha⟩ z hza) }
    (fun z hz => equiv_refl _ (LocalLogarithm.function.eval (point c hc z) hz).property)

theorem derivative_inverse (c : Scalar) (hc : Nonzero c) (z : Scalar) (hz : domain c hc z) :
    (mul z.val ((holomorphic c hc).derivative z hz).val).Equiv one := by
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (LocalLogarithm.onePlus (point c hc z)).property (LocalLogarithm.derivativeValue (point c hc z) hz).property)
    (hright := ofQComplex_valid _) (LocalLogarithm.derivativeValue_inverse (point c hc z) hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid z.property ((holomorphic c hc).derivative z hz).property) (hright := ofQComplex_valid _)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let C := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  let D := ComplexRawQuotient.ofRaw (LocalLogarithm.derivativeValue (point c hc z) hz).val
    (LocalLogarithm.derivativeValue (point c hc z) hz).property
  change (1+(-1+C*Z))*D=1 at hd
  change Z*(D*C)=1
  grind only

theorem nonzero (c : Scalar) (hc : Nonzero c) (z : Scalar) (hz : domain c hc z) : Nonzero z :=
  RepresentedReciprocal.nonzero_of_inverse z ((holomorphic c hc).derivative z hz) (derivative_inverse c hc z hz)

theorem derivative_reciprocal (c : Scalar) (hc : Nonzero c)
    (hH : DomainFunctions.Holomorphic (function c hc)) (z : Scalar) (hz : domain c hc z) :
    (hH.derivative z hz).val.Equiv (RepresentedReciprocal.inverse z (nonzero c hc z hz)).val :=
  equiv_trans (hH.derivative z hz).property ((holomorphic c hc).derivative z hz).property
    (RepresentedReciprocal.inverse z (nonzero c hc z hz)).property
    (hH.derivative_unique (holomorphic c hc) z hz)
    (equiv_symm (RepresentedReciprocal.inverse_unique z (nonzero c hc z hz)
      ((holomorphic c hc).derivative z hz) (derivative_inverse c hc z hz)))

theorem point_center (c : Scalar) (hc : Nonzero c) : (point c hc c).val.Equiv zero := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (RepresentedReciprocal.inverse c hc).property c.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.inverse_mul c hc)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (point c hc c).property) (hright := ofQComplex_valid _)
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let V := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  change V*C=1 at hi
  change -1+V*C=0
  grind only

theorem center_mem (c : Scalar) (hc : Nonzero c) : domain c hc c :=
  Centered.interior_congr LocalLogarithm.radius.val ⟨zero, ofQComplex_valid _⟩ (point c hc c)
    (equiv_symm (point_center c hc)) (interior_zero _ LocalLogarithm.radius.property)

theorem initial (c : Scalar) (hc : Nonzero c) : ((function c hc).eval c (center_mem c hc)).val.Equiv zero :=
  equiv_trans ((function c hc).eval c (center_mem c hc)).property
    (LocalLogarithm.function.eval ⟨zero, ofQComplex_valid _⟩ (interior_zero _ LocalLogarithm.radius.property)).property
    (ofQComplex_valid _)
    (LocalLogarithm.function.eval_congr (point c hc c) ⟨zero, ofQComplex_valid _⟩
      (center_mem c hc) (interior_zero _ LocalLogarithm.radius.property) (point_center c hc)) LocalLogarithm.initial

theorem point_congr (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : c.val.Equiv d.val)
    (z w : Scalar) (hzw : z.val.Equiv w.val) : (point c hc z).val.Equiv (point d hd w).val :=
  add_equiv (equiv_refl _ (scalarNeg oneScalar).property)
    (mul_equiv (RepresentedReciprocal.inverse c hc).property (RepresentedReciprocal.inverse d hd).property
      z.property w.property (RepresentedReciprocal.inverse_congr c d hc hd hcd) hzw)

theorem domain_congr (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : c.val.Equiv d.val)
    (z w : Scalar) (hzw : z.val.Equiv w.val) : domain c hc z ↔ domain d hd w :=
  LocalLogarithm.function.domain_congr _ _ (point_congr c d hc hd hcd z w hzw)

theorem value_congr (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : c.val.Equiv d.val)
    (z w : Scalar) (hz : domain c hc z) (hw : domain d hd w) (hzw : z.val.Equiv w.val) :
    ((function c hc).eval z hz).val.Equiv ((function d hd).eval w hw).val :=
  LocalLogarithm.function.eval_congr _ _ hz hw (point_congr c d hc hd hcd z w hzw)

def chartPoint (c w : Scalar) : Scalar :=
  ⟨mul c.val (LocalLogarithm.onePlus w).val, mul_valid c.property (LocalLogarithm.onePlus w).property⟩

theorem point_chartPoint (c : Scalar) (hc : Nonzero c) (w : Scalar) :
    (point c hc (chartPoint c w)).val.Equiv w.val := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (RepresentedReciprocal.inverse c hc).property c.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.inverse_mul c hc)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (point c hc (chartPoint c w)).property) (hright := w.property)
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  change R*C=1 at hi
  change -1+R*(C*(1+W))=W
  grind only

theorem chartPoint_mem (c : Scalar) (hc : Nonzero c) (w : Scalar)
    (hw : interior LocalLogarithm.radius.val w) : domain c hc (chartPoint c w) :=
  Centered.interior_congr LocalLogarithm.radius.val w (point c hc (chartPoint c w))
    (equiv_symm (point_chartPoint c hc w)) hw

theorem chartPoint_congr (c d w v : Scalar) (hcd : c.val.Equiv d.val) (hwv : w.val.Equiv v.val) :
    (chartPoint c w).val.Equiv (chartPoint d v).val :=
  mul_equiv c.property d.property (LocalLogarithm.onePlus w).property (LocalLogarithm.onePlus v).property hcd
    (add_equiv (equiv_refl _ (ofQComplex_valid _)) hwv)

theorem value_chartPoint (c : Scalar) (hc : Nonzero c) (w : Scalar)
    (hw : interior LocalLogarithm.radius.val w) :
    ((function c hc).eval (chartPoint c w) (chartPoint_mem c hc w hw)).val.Equiv (LocalLogarithm.function.eval w hw).val :=
  LocalLogarithm.function.eval_congr (point c hc (chartPoint c w)) w (chartPoint_mem c hc w hw) hw
    (point_chartPoint c hc w)

end ComputableAnalysis.RiemannHilbert.RelativeLogarithm
