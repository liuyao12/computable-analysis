import ComputableAnalysis.RiemannHilbert.RelativeLogarithmUniform

/-! Exact additive overlap identity for the actual normalized logarithm
charts. Uniform derivative remainders and convex segment coverage prove the
identity throughout the overlap through the next center. -/
namespace ComputableAnalysis.RiemannHilbert.RelativeLogarithm
open ComplexRaw FunctionTheory LocalODE LocalSystem NonzeroBoxSearch
set_option maxHeartbeats 1500000

def commonDomain (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (z : Scalar) :=
  domain c hc z ∧ domain d hd z

def overlapValue (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : domain c hc d)
    (z : Scalar) (hz : commonDomain c d hc hd z) : Scalar :=
  ⟨sub (sub ((function c hc).eval z hz.1).val ((function c hc).eval d hcd).val)
      ((function d hd).eval z hz.2).val,
    sub_valid (sub_valid ((function c hc).eval z hz.1).property ((function c hc).eval d hcd).property)
      ((function d hd).eval z hz.2).property⟩

def overlapField (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : domain c hc d) :
    UniformSegment.Field (n := 1) (commonDomain c d hc hd) :=
  fun z hz => ⟨fun _ => (overlapValue c d hc hd hcd z hz).val,fun _ => (overlapValue c d hc hd hcd z hz).property⟩

theorem derivative_common (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d)
    (w : Scalar) (hw : commonDomain c d hc hd w) :
    ((holomorphic c hc).derivative w hw.1).val.Equiv ((holomorphic d hd).derivative w hw.2).val :=
  RepresentedReciprocal.unique w _ _ (derivative_inverse c hc w hw.1) (derivative_inverse d hd w hw.2)

theorem overlapField_remainder (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : domain c hc d)
    (w z : Scalar) (hw : commonDomain c d hc hd w) (hz : commonDomain c d hc hd z) (i : Fin 1) :
    ((UniformSegment.remainder (fun _ _ => ValueMap.zeroBetween 1 1) (overlapField c d hc hd hcd) w z hw hz).val i).Equiv
      (sub (DomainFunctions.remainder (function c hc) w hw.1 ((holomorphic c hc).derivative w hw.1) z hz.1)
        (DomainFunctions.remainder (function d hd) w hw.2 ((holomorphic d hd).derivative w hw.2) z hz.2)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (UniformSegment.remainder (fun _ _ => ValueMap.zeroBetween 1 1) (overlapField c d hc hd hcd) w z hw hz).property i)
    (hright := sub_valid (DomainFunctions.remainder_valid _ _ _ _ _ _) (DomainFunctions.remainder_valid _ _ _ _ _ _))
  have hD := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((holomorphic c hc).derivative w hw.1).property)
    (hright := ((holomorphic d hd).derivative w hw.2).property) (derivative_common c d hc hd w hw)
  let CZ := ComplexRawQuotient.ofRaw ((function c hc).eval z hz.1).val ((function c hc).eval z hz.1).property
  let CW := ComplexRawQuotient.ofRaw ((function c hc).eval w hw.1).val ((function c hc).eval w hw.1).property
  let CD := ComplexRawQuotient.ofRaw ((function c hc).eval d hcd).val ((function c hc).eval d hcd).property
  let DZ := ComplexRawQuotient.ofRaw ((function d hd).eval z hz.2).val ((function d hd).eval z hz.2).property
  let DW := ComplexRawQuotient.ofRaw ((function d hd).eval w hw.2).val ((function d hd).eval w hw.2).property
  let DC := ComplexRawQuotient.ofRaw ((holomorphic c hc).derivative w hw.1).val ((holomorphic c hc).derivative w hw.1).property
  let DD := ComplexRawQuotient.ofRaw ((holomorphic d hd).derivative w hw.2).val ((holomorphic d hd).derivative w hw.2).property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change DC=DD at hD
  change (((CZ-CD)-DZ)-((CW-CD)-DW))-(Z-W)*0=((CZ-CW)-DC*(Z-W))-((DZ-DW)-DD*(Z-W))
  grind only

def overlapDelta (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (eps : QPos) : QPos :=
  QPos.minimum (uniformDelta c hc (DomainFunctions.halfError eps)) (uniformDelta d hd (DomainFunctions.halfError eps))

theorem overlapField_uniform_remainder (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : domain c hc d)
    (eps H : QPos) (w z : Scalar) (hw : commonDomain c d hc hd w) (hz : commonDomain c d hc hd z)
    (hH : H.val ≤ (overlapDelta c d hc hd eps).val) (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound (UniformSegment.remainder (fun _ _ => ValueMap.zeroBetween 1 1) (overlapField c d hc hd hcd) w z hw hz) (eps.val*H.val) := by
  have hl := uniform_remainder c hc (DomainFunctions.halfError eps) H w z hw.1 hz.1
    (Rat.le_trans hH (QPos.minimum_le_left _ _)) hzw
  have hr := uniform_remainder d hd (DomainFunctions.halfError eps) H w z hw.2 hz.2
    (Rat.le_trans hH (QPos.minimum_le_right _ _)) hzw
  have hs := SeriesLimitLaws.small_sub hl hr
  have he : (DomainFunctions.halfError eps).val*H.val+(DomainFunctions.halfError eps).val*H.val=eps.val*H.val := by
    have hh := DomainFunctions.halfError_identity eps
    grind only
  rw [he] at hs
  intro i
  exact Small.congr (sub_valid (DomainFunctions.remainder_valid _ _ _ _ _ _) (DomainFunctions.remainder_valid _ _ _ _ _ _))
    ((UniformSegment.remainder (fun _ _ => ValueMap.zeroBetween 1 1) (overlapField c d hc hd hcd) w z hw hz).property i)
    (equiv_symm (overlapField_remainder c d hc hd hcd w z hw hz i)) hs

theorem overlapField_initial (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : domain c hc d) :
    overlapField c d hc hd hcd d ⟨hcd,center_mem d hd⟩ ≈ Fiber.zero 1 := by
  intro i
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := ((function d hd).eval d (center_mem d hd)).property)
    (hright := ofQComplex_valid _) (initial d hd)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (overlapField c d hc hd hcd d ⟨hcd,center_mem d hd⟩).property i) (hright := ofQComplex_valid _)
  let V := ComplexRawQuotient.ofRaw ((function c hc).eval d hcd).val ((function c hc).eval d hcd).property
  let W := ComplexRawQuotient.ofRaw ((function d hd).eval d (center_mem d hd)).val ((function d hd).eval d (center_mem d hd)).property
  change W=0 at hi
  change (V-V)-W=0
  grind only

theorem overlapField_bound (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : domain c hc d)
    (z : Scalar) (hz : commonDomain c d hc hd z) : CoordinateBound (overlapField c d hc hd hcd z hz) 12 := by
  intro i
  have hs := SeriesLimitLaws.small_sub (SeriesLimitLaws.small_sub (value_bound c hc z hz.1) (value_bound c hc d hcd))
    (value_bound d hd z hz.2)
  have he : (4+4+4 : Rat)=12 := by decide +kernel
  rw [he] at hs
  exact hs

/-- The actual relative logarithms have the additive cocycle identity on
their convex open overlap containing the next center. It is derived from
uniform analytic estimates, not merely exponential agreement at a point. -/
theorem cocycle (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : domain c hc d)
    (z : Scalar) (hz : commonDomain c d hc hd z) :
    ((function c hc).eval z hz.1).val.Equiv
      (add ((function c hc).eval d hcd).val ((function d hd).eval z hz.2).val) := by
  let D := commonDomain c d hc hd
  let f := overlapField c d hc hd hcd
  let W := MatrixExponential.pointRadius (AffineSegment.displacement d z)
  have hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw := by
    intro z w hz hw hzw i
    exact FunctionTheory.sub_congr (FunctionTheory.sub_congr
      ((function c hc).eval_congr z w hz.1 hw.1 hzw)
      (equiv_refl _ ((function c hc).eval d hcd).property)) ((function d hd).eval_congr z w hz.2 hw.2 hzw)
  have hzero := UniformSegment.zero D d z ⟨hcd,center_mem d hd⟩ hz
    (fun t ht => ⟨affine_mem c hc d z hcd hz.1 t ht,affine_mem d hd d z (center_mem d hd) hz.2 t ht⟩)
    W (interior_bound W.val (AffineSegment.displacement d z) (MatrixExponential.pointRadius_inside _))
    (fun _ _ => ValueMap.zeroBetween 1 1) f 0 12 (by decide +kernel)
    (by simp only [Rat.mul_zero]; decide +kernel) (by decide +kernel) hfcongr (overlapField_initial c d hc hd hcd)
    (overlapField_bound c d hc hd hcd)
    (by
      intro _ _ B hB x hx
      change CoordinateBound (Fiber.zero 1) (0*B)
      rw [Rat.zero_mul]
      exact bound_zero 0 (by decide +kernel))
    (overlapDelta c d hc hd) (overlapField_uniform_remainder c d hc hd hcd)
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (f z hz).property 0) (hright := ofQComplex_valid _) (hzero 0)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((function c hc).eval z hz.1).property)
    (hright := add_valid ((function c hc).eval d hcd).property ((function d hd).eval z hz.2).property)
  let C := ComplexRawQuotient.ofRaw ((function c hc).eval z hz.1).val ((function c hc).eval z hz.1).property
  let A := ComplexRawQuotient.ofRaw ((function c hc).eval d hcd).val ((function c hc).eval d hcd).property
  let B := ComplexRawQuotient.ofRaw ((function d hd).eval z hz.2).val ((function d hd).eval z hz.2).property
  change (C-A)-B=0 at hh
  change C=A+B
  grind only

end ComputableAnalysis.RiemannHilbert.RelativeLogarithm
