import ComputableAnalysis.RiemannHilbert.ContourDisplacedGeometry
import ComputableAnalysis.RiemannHilbert.ContourInnerKernelError

/-! Actual displaced-pole inner contours have a mesh-independent error:
numerator continuity and center displacement are controlled separately. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RepresentedReciprocal
set_option autoImplicit false

theorem innerBoundary_product_left (a : Scalar) (f : QComplex → Scalar) (R : QPos) (M : Nat) (hM : 0<M) :
    innerBoundary (fun q => scalarProduct a (f q)) R M ≈ scalarProduct a (innerBoundary f R M) := by
  let zeroScalar := rationalRectangleScalar QComplex.zero
  have hp (q : QComplex) : scalarProduct a (f q) ≈ sampleLinear a zeroScalar f f q := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (scalarProduct a (f q)).property)
      (hright := (sampleLinear a zeroScalar f f q).property)
    change gridScalarValue a*gridScalarValue (f q)=
      gridScalarValue a*gridScalarValue (f q)+0*gridScalarValue (f q)
    grind only
  refine Setoid.trans (innerBoundary_congr_on_frame _ _ R M hM (fun q _ => hp q)) ?_
  refine Setoid.trans (innerBoundary_linear a zeroScalar f f R M) ?_
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarSum (scalarProduct a (innerBoundary f R M))
      (scalarProduct zeroScalar (innerBoundary f R M))).property)
    (hright := (scalarProduct a (innerBoundary f R M)).property)
  change gridScalarValue a*gridScalarValue (innerBoundary f R M)+0*gridScalarValue (innerBoundary f R M)=
    gridScalarValue a*gridScalarValue (innerBoundary f R M)
  grind only

theorem innerBoundary_difference_identity (f g : QComplex → Scalar) (R : QPos) (M : Nat) (hM : 0<M) :
    innerBoundary (fun q => gridScalarSub (f q) (g q)) R M ≈
      gridScalarSub (innerBoundary f R M) (innerBoundary g R M) := by
  have he (q : QComplex) : gridScalarSub (f q) (g q) ≈
      sampleLinear oneScalar (scalarNeg oneScalar) f g q := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (gridScalarSub (f q) (g q)).property)
      (hright := (sampleLinear oneScalar (scalarNeg oneScalar) f g q).property)
    change gridScalarValue (f q)-gridScalarValue (g q)=1*gridScalarValue (f q)+(-1)*gridScalarValue (g q)
    grind only
  refine Setoid.trans (innerBoundary_congr_on_frame _ _ R M hM (fun q _ => he q)) ?_
  refine Setoid.trans (innerBoundary_linear oneScalar (scalarNeg oneScalar) f g R M) ?_
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarSum (scalarProduct oneScalar (innerBoundary f R M))
      (scalarProduct (scalarNeg oneScalar) (innerBoundary g R M))).property)
    (hright := (gridScalarSub (innerBoundary f R M) (innerBoundary g R M)).property)
  change 1*gridScalarValue (innerBoundary f R M)+(-1)*gridScalarValue (innerBoundary g R M)=
    gridScalarValue (innerBoundary f R M)-gridScalarValue (innerBoundary g R M)
  grind only

theorem innerBoundary_difference_bound (f g : QComplex → Scalar) (R : QPos) (M : Nat) (hM : 0<M)
    (E : Rat) (hE : 0≤E)
    (hfg : ∀ q, frameDomain R (rationalRectangleScalar q) → Small (sub (f q).val (g q).val) E) :
    Small (sub (innerBoundary f R M).val (innerBoundary g R M).val) (16*R.val*E) := by
  have hs := innerBoundary_bound (fun q => gridScalarSub (f q) (g q)) R M hM E hE hfg
  have hi := Rat.mul_inv_cancel (M:Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr hM))
  have he : 16*(M:Rat)*E*(R.val/(M:Rat))=16*R.val*E := by
    simp only [Rat.div_def]; grind only
  rw [he] at hs
  exact Small.congr (innerBoundary (fun q => gridScalarSub (f q) (g q)) R M).property
    (sub_valid (innerBoundary f R M).property (innerBoundary g R M).property)
    (innerBoundary_difference_identity f g R M hM) hs

theorem frame_displaced_inverse_bound (R : QPos) (d : Scalar) (hd : Small d.val (R.val/64))
    (q : QComplex) (hq : frameDomain R (rationalRectangleScalar q)) :
    Small (inverse (Centered.offset d (rationalRectangleScalar q)) (displacedFrame_nonzero R d hd _ hq)).val
      (4/R.val) := by
  let w := rationalRectangleScalar q
  let u := inverse (Centered.offset d w) (displacedFrame_nonzero R d hd w hq)
  let v := inverse w (frameDomain_nonzero R w hq)
  have hi := Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
  have hH : 0≤R.val/64 := by have hp := R.property; simp only [Rat.div_def]; grind only
  have hdif := frame_reciprocal_displacement_bound R d (R.val/64) hH Rat.le_refl hd q hq (displacedFrame_nonzero R d hd _ hq)
  have he : 128*(R.val/64)/(R.val*R.val)=2/R.val := by
    simp only [Rat.div_def,Rat.inv_mul_rev]; grind only
  rw [he] at hdif
  have hs := LocalODE.small_add (frame_rational_inverse_bound R q hq (frameDomain_nonzero R _ hq)) hdif
  have he' : 2/R.val+2/R.val=4/R.val := by simp only [Rat.div_def]; grind only
  rw [he'] at hs
  exact Small.congr (add_valid v.property (sub_valid u.property v.property)) u.property
    (SeriesLimitLaws.add_difference u.val v.val u.property v.property) hs

def displacedInnerPrefix (f : DomainFunctions.Map) (b c : Scalar) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate c z))
    (hc : Small (Centered.offset c b).val (R.val/64)) (M : Nat) : Scalar :=
  innerBoundary (displacedFrameSample f b c R hdom hc) R M

theorem displaced_product_difference (F A U V : Scalar) :
    (sub (scalarProduct F U).val (scalarProduct A V).val).Equiv
      (add (mul (sub F.val A.val) U.val) (mul A.val (sub U.val V.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scalarProduct F U).property (scalarProduct A V).property)
    (hright := add_valid (mul_valid (sub_valid F.property A.property) U.property)
      (mul_valid A.property (sub_valid U.property V.property)))
  change gridScalarValue F*gridScalarValue U-gridScalarValue A*gridScalarValue V=
    (gridScalarValue F-gridScalarValue A)*gridScalarValue U+
      gridScalarValue A*(gridScalarValue U-gridScalarValue V)
  grind only

theorem displacedInnerPrefix_center_estimate (f : DomainFunctions.Map) (b c : Scalar) (hb : f.domain b)
    (R : QPos) (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate c z))
    (H : Rat) (hH : 0≤H) (hHR : H≤R.val/64) (hc : Small (Centered.offset c b).val H)
    (eps : QPos)
    (hclose : ∀ z hz, Small (sub (f.eval (Centered.translate c z) (hdom z hz)).val (f.eval b hb).val) eps.val)
    (M : Nat) (hM : 0<M) :
    Small (sub (displacedInnerPrefix f b c R hdom (hc.mono hHR) M).val
      (scalarProduct (f.eval b hb) (reciprocalInnerPrefix R M)).val)
      (128*eps.val+4096*scalarBound (f.eval b hb)*H/R.val) := by
  let A := f.eval b hb
  let sample := displacedFrameSample f b c R hdom (hc.mono hHR)
  let comparison := fun q => scalarProduct A (reciprocalFrameSample R q)
  let E := 8*eps.val/R.val+256*scalarBound A*H/(R.val*R.val)
  have hi := Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
  have hri : 0≤R.val⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr R.property)
  have hE : 0≤E := by
    have heps := Rat.le_of_lt eps.property
    have hA := Rat.le_of_lt (scalarBound_pos A)
    dsimp [E]; simp only [Rat.div_def,Rat.inv_mul_rev]
    exact Rat.add_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) heps) hri)
      (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hA) hH)
        (Rat.mul_nonneg hri hri))
  have hs := innerBoundary_difference_bound sample comparison R M hM E hE (by
    intro q hq
    let w := rationalRectangleScalar q
    let F := f.eval (Centered.translate c w) (hdom w hq)
    let U := inverse (Centered.offset (Centered.offset c b) w) (displacedFrame_nonzero R _ (hc.mono hHR) w hq)
    let V := inverse w (frameDomain_nonzero R w hq)
    have hU := frame_displaced_inverse_bound R _ (hc.mono hHR) q hq
    have hV := frame_reciprocal_displacement_bound R _ H hH hHR hc q hq (displacedFrame_nonzero R _ (hc.mono hHR) _ hq)
    have hfirst := Small.mul (sub_valid F.property A.property) U.property
      (Rat.le_of_lt eps.property) (Rat.mul_nonneg (by decide +kernel) hri) (hclose w hq) hU
    have hsecond := Small.mul A.property (sub_valid U.property V.property)
      (Rat.le_of_lt (scalarBound_pos A)) (by
        simp only [Rat.div_def,Rat.inv_mul_rev]
        exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hH) (Rat.mul_nonneg hri hri)) (scalar_small A) hV
    have he1 : 2*eps.val*(4/R.val)=8*eps.val/R.val := by simp only [Rat.div_def]; grind only
    have he2 : 2*scalarBound A*(128*H/(R.val*R.val))=256*scalarBound A*H/(R.val*R.val) := by
      simp only [Rat.div_def]; grind only
    change Small (mul (sub F.val A.val) U.val) (2*eps.val*(4/R.val)) at hfirst
    rw [he1] at hfirst; rw [he2] at hsecond
    have hsum := LocalODE.small_add hfirst hsecond
    have hprod := Small.congr
      (add_valid (mul_valid (sub_valid F.property A.property) U.property)
        (mul_valid A.property (sub_valid U.property V.property)))
      (sub_valid (scalarProduct F U).property (scalarProduct A V).property)
      (equiv_symm (displaced_product_difference F A U V)) hsum
    exact Small.congr (sub_valid (scalarProduct F U).property (scalarProduct A V).property)
      (sub_valid (sample q).property (comparison q).property)
      (FunctionTheory.sub_congr (equiv_symm (displacedFrameSample_value f b c R hdom (hc.mono hHR) q hq))
        (mul_equiv A.property A.property V.property (reciprocalFrameSample R q).property
          (equiv_refl _ A.property) (equiv_symm (reciprocalFrameSample_value R q hq)))) hprod)
  have he : 16*R.val*E=128*eps.val+4096*scalarBound A*H/R.val := by
    dsimp [E]; simp only [Rat.div_def,Rat.inv_mul_rev]; grind only
  rw [he] at hs
  exact Small.congr (sub_valid (innerBoundary sample R M).property (innerBoundary comparison R M).property)
    (sub_valid (displacedInnerPrefix f b c R hdom (hc.mono hHR) M).property
      (scalarProduct A (reciprocalInnerPrefix R M)).property)
    (FunctionTheory.sub_congr (equiv_refl _ (innerBoundary sample R M).property)
      (innerBoundary_product_left A (reciprocalFrameSample R) R M hM)) hs

end ComputableAnalysis.RiemannHilbert.RectangularContour
