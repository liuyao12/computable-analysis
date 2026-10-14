import ComputableAnalysis.RiemannHilbert.RelativeLogarithm
import ComputableAnalysis.RiemannHilbert.ExponentialODEUniqueness

/-! Uniform estimates for the actual normalized logarithm. A bound on the
computed center reciprocal controls the affine coordinate, actual derivative
and quadratic remainder. The logarithm chart covers every affine segment
between its represented points. -/
namespace ComputableAnalysis.RiemannHilbert.RelativeLogarithm
open ComplexRaw FunctionTheory LocalODE DomainFunctions NonzeroBoxSearch
set_option maxHeartbeats 800000

def inverseBound (c : Scalar) (hc : Nonzero c) : Rat := scalarBound (RepresentedReciprocal.inverse c hc)

theorem inverseBound_pos (c : Scalar) (hc : Nonzero c) : 0 < inverseBound c hc := scalarBound_pos _

theorem inverse_bound (c : Scalar) (hc : Nonzero c) :
    Small (RepresentedReciprocal.inverse c hc).val (inverseBound c hc) := scalar_small _

theorem point_difference (c : Scalar) (hc : Nonzero c) (w z : Scalar) :
    (sub (point c hc z).val (point c hc w).val).Equiv
      (mul (RepresentedReciprocal.inverse c hc).val (sub z.val w.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (point c hc z).property (point c hc w).property)
    (hright := mul_valid (RepresentedReciprocal.inverse c hc).property (sub_valid z.property w.property))
  let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change (-1+R*Z)-(-1+R*W)=R*(Z-W)
  grind only

theorem point_difference_bound (c : Scalar) (hc : Nonzero c) (w z : Scalar) (H : Rat)
    (hH : 0 ≤ H) (hzw : Small (sub z.val w.val) H) :
    Small (sub (point c hc z).val (point c hc w).val) (2*inverseBound c hc*H) :=
  Small.congr (mul_valid (RepresentedReciprocal.inverse c hc).property (sub_valid z.property w.property))
    (sub_valid (point c hc z).property (point c hc w).property) (equiv_symm (point_difference c hc w z))
    (Small.mul (RepresentedReciprocal.inverse c hc).property (sub_valid z.property w.property)
      (Rat.le_of_lt (inverseBound_pos c hc)) hH (inverse_bound c hc) hzw)

theorem value_bound (c : Scalar) (hc : Nonzero c) (z : Scalar) (hz : domain c hc z) :
    Small ((function c hc).eval z hz).val 4 := LocalLogarithm.value_bound (point c hc z) hz

theorem derivative_bound (c : Scalar) (hc : Nonzero c) (z : Scalar) (hz : domain c hc z) :
    Small ((holomorphic c hc).derivative z hz).val (8*inverseBound c hc) := by
  change Small (mul (LocalLogarithm.derivativeValue (point c hc z) hz).val
    (RepresentedReciprocal.inverse c hc).val) (8*inverseBound c hc)
  have h := Small.mul (LocalLogarithm.derivativeValue (point c hc z) hz).property
    (RepresentedReciprocal.inverse c hc).property (by decide : (0 : Rat) ≤ 4)
    (Rat.le_of_lt (inverseBound_pos c hc)) (LocalLogarithm.derivative_bound (point c hc z) hz) (inverse_bound c hc)
  simpa only [show (2 : Rat)*4=8 by decide +kernel] using h

theorem reciprocal_bound (c : Scalar) (hc : Nonzero c) (z : Scalar) (hz : domain c hc z) :
    Small (RepresentedReciprocal.inverse z (nonzero c hc z hz)).val (8*inverseBound c hc) :=
  Small.congr ((holomorphic c hc).derivative z hz).property
    (RepresentedReciprocal.inverse z (nonzero c hc z hz)).property
    (derivative_reciprocal c hc (holomorphic c hc) z hz) (derivative_bound c hc z hz)

theorem remainder_agreement (c : Scalar) (hc : Nonzero c) (w z : Scalar) (hw : domain c hc w) (hz : domain c hc z) :
    (DomainFunctions.remainder (function c hc) w hw ((holomorphic c hc).derivative w hw) z hz).Equiv
      (DomainFunctions.remainder LocalLogarithm.function (point c hc w) hw
        (LocalLogarithm.derivativeValue (point c hc w) hw) (point c hc z) hz) := by
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := sub_valid (point c hc z).property (point c hc w).property)
    (hright := mul_valid (RepresentedReciprocal.inverse c hc).property (sub_valid z.property w.property))
    (point_difference c hc w z)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _) (hright := DomainFunctions.remainder_valid _ _ _ _ _ _)
  let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  let D := ComplexRawQuotient.ofRaw (LocalLogarithm.derivativeValue (point c hc w) hw).val
    (LocalLogarithm.derivativeValue (point c hc w) hw).property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let PW := ComplexRawQuotient.ofRaw (point c hc w).val (point c hc w).property
  let PZ := ComplexRawQuotient.ofRaw (point c hc z).val (point c hc z).property
  let LW := ComplexRawQuotient.ofRaw ((function c hc).eval w hw).val ((function c hc).eval w hw).property
  let LZ := ComplexRawQuotient.ofRaw ((function c hc).eval z hz).val ((function c hc).eval z hz).property
  change PZ-PW=R*(Z-W) at hd
  change (LZ-LW)-(D*R)*(Z-W)=(LZ-LW)-D*(PZ-PW)
  grind only

def remainderBound (c : Scalar) (hc : Nonzero c) : Rat := 64*(inverseBound c hc)^2

theorem remainderBound_nonneg (c : Scalar) (hc : Nonzero c) : 0 ≤ remainderBound c hc :=
  Rat.mul_nonneg (by decide) (Rat.pow_nonneg (Rat.le_of_lt (inverseBound_pos c hc)))

theorem quadratic_remainder (c : Scalar) (hc : Nonzero c) (w z : Scalar) (hw : domain c hc w) (hz : domain c hc z)
    (H : Rat) (hH : 0 ≤ H) (hzw : Small (sub z.val w.val) H) :
    Small (DomainFunctions.remainder (function c hc) w hw ((holomorphic c hc).derivative w hw) z hz)
      (remainderBound c hc*H^2) := by
  have he : 16*(2*inverseBound c hc*H)^2=remainderBound c hc*H^2 := by
    simp only [remainderBound, Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
    grind only
  have h := LocalLogarithm.quadratic_remainder (point c hc w) (point c hc z) hw hz
    (2*inverseBound c hc*H) (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.le_of_lt (inverseBound_pos c hc))) hH)
    (point_difference_bound c hc w z H hH hzw)
  rw [he] at h
  exact Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _) (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (equiv_symm (remainder_agreement c hc w z hw hz)) h

def uniformDelta (c : Scalar) (hc : Nonzero c) (eps : QPos) : QPos :=
  ⟨eps.val/(remainderBound c hc+1), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by have := remainderBound_nonneg c hc; grind only))⟩

theorem uniform_remainder (c : Scalar) (hc : Nonzero c) (eps H : QPos) (w z : Scalar)
    (hw : domain c hc w) (hz : domain c hc z) (hH : H.val ≤ (uniformDelta c hc eps).val)
    (hzw : Small (sub z.val w.val) H.val) :
    Small (DomainFunctions.remainder (function c hc) w hw ((holomorphic c hc).derivative w hw) z hz) (eps.val*H.val) := by
  have hs := quadratic_remainder c hc w z hw hz H.val (Rat.le_of_lt H.property) hzw
  have hb := remainderBound_nonneg c hc
  have hm := Rat.mul_le_mul_of_nonneg_right hH (show 0 ≤ remainderBound c hc+1 by grind only)
  have he : (uniformDelta c hc eps).val*(remainderBound c hc+1)=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt (by grind only))
  rw [he] at hm
  have hprod : remainderBound c hc*H.val ≤ eps.val := by have := H.property; grind only
  have hh := Rat.mul_le_mul_of_nonneg_right hprod (Rat.le_of_lt H.property)
  apply hs.mono
  simpa only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul, Rat.mul_assoc] using hh

theorem lipschitz (c : Scalar) (hc : Nonzero c) (w z : Scalar) (hw : domain c hc w) (hz : domain c hc z)
    (H : QPos) (hzw : Small (sub z.val w.val) H.val) :
    Small (sub ((function c hc).eval z hz).val ((function c hc).eval w hw).val) (18*inverseBound c hc*H.val) := by
  let J : QPos := ⟨2*inverseBound c hc*H.val, Rat.mul_pos (Rat.mul_pos (by decide) (inverseBound_pos c hc)) H.property⟩
  have h := LocalLogarithm.lipschitz (point c hc w) (point c hc z) hw hz J
    (point_difference_bound c hc w z H.val (Rat.le_of_lt H.property) hzw)
  have he : 9*J.val=18*inverseBound c hc*H.val := by dsimp [J]; grind only
  rw [he] at h
  exact h

theorem point_affine (c : Scalar) (hc : Nonzero c) (p q : Scalar) (t : Rat) :
    (point c hc (AffineSegment.point p q t)).val.Equiv
      (AffineSegment.point (point c hc p) (point c hc q) t).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (point c hc (AffineSegment.point p q t)).property)
    (hright := (AffineSegment.point (point c hc p) (point c hc q) t).property)
  let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  let P := ComplexRawQuotient.ofRaw p.val p.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  change -1+R*(P+ComplexRawQuotient.scaleRat t (Q-P)) =
    (-1+R*P)+ComplexRawQuotient.scaleRat t ((-1+R*Q)-(-1+R*P))
  rw [ComplexRawQuotient.mul_add, ComplexRawQuotient.mul_scaleRat]
  have he : R*(Q-P)=(-1+R*Q)-(-1+R*P) := by grind only
  rw [he, ComplexRawQuotient.add_assoc]

theorem affine_mem (c : Scalar) (hc : Nonzero c) (p q : Scalar) (hp : domain c hc p) (hq : domain c hc q)
    (t : Rat) (ht : UniformPath.unitInterval t) : domain c hc (AffineSegment.point p q t) :=
  Centered.interior_congr LocalLogarithm.radius.val _ _ (equiv_symm (point_affine c hc p q t))
    (MatrixExponential.disc_affine_mem LocalLogarithm.radius (point c hc p) (point c hc q) hp hq t ht)

end ComputableAnalysis.RiemannHilbert.RelativeLogarithm
