import ComputableAnalysis.RiemannHilbert.RelativeLogarithmCocycle

/-! Exact constancy of the difference of two actual relative logarithms on
an arbitrary nonempty overlap. Convex coverage and uniform estimates choose
the internal subdivision; neither center need belong to the other chart. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert LocalODE LocalSystem
open NonzeroBoxSearch RelativeLogarithm
private def scalarClass (z : Scalar) := ComplexRawQuotient.ofRaw z.val z.property

private def differenceValue (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d)
    (p : Scalar) (hp : commonDomain c d hc hd p)
    (z : Scalar) (hz : commonDomain c d hc hd z) : Scalar :=
  ⟨sub (sub ((function c hc).eval z hz.1).val ((function d hd).eval z hz.2).val)
    (sub ((function c hc).eval p hp.1).val ((function d hd).eval p hp.2).val),
    sub_valid (sub_valid ((function c hc).eval z hz.1).property ((function d hd).eval z hz.2).property)
      (sub_valid ((function c hc).eval p hp.1).property ((function d hd).eval p hp.2).property)⟩

private def differenceField (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d)
    (p : Scalar) (hp : commonDomain c d hc hd p) : UniformSegment.Field (n := 1) (commonDomain c d hc hd) :=
  fun z hz => ⟨fun _ => (differenceValue c d hc hd p hp z hz).val,
    fun _ => (differenceValue c d hc hd p hp z hz).property⟩

private theorem field_remainder (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d)
    (p : Scalar) (hp : commonDomain c d hc hd p)
    (w z : Scalar) (hw : commonDomain c d hc hd w) (hz : commonDomain c d hc hd z) (i : Fin 1) :
    ((UniformSegment.remainder (fun _ _ => ValueMap.zeroBetween 1 1)
      (differenceField c d hc hd p hp) w z hw hz).val i).Equiv
      (sub (DomainFunctions.remainder (function c hc) w hw.1 ((holomorphic c hc).derivative w hw.1) z hz.1)
        (DomainFunctions.remainder (function d hd) w hw.2 ((holomorphic d hd).derivative w hw.2) z hz.2)) := by
  have hD := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((holomorphic c hc).derivative w hw.1).property)
    (hright := ((holomorphic d hd).derivative w hw.2).property) (derivative_common c d hc hd w hw)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (UniformSegment.remainder (fun _ _ => ValueMap.zeroBetween 1 1)
      (differenceField c d hc hd p hp) w z hw hz).property i)
    (hright := sub_valid (DomainFunctions.remainder_valid _ _ _ _ _ _) (DomainFunctions.remainder_valid _ _ _ _ _ _))
  let CZ := scalarClass ((function c hc).eval z hz.1)
  let DZ := scalarClass ((function d hd).eval z hz.2)
  let CW := scalarClass ((function c hc).eval w hw.1)
  let DW := scalarClass ((function d hd).eval w hw.2)
  let CP := scalarClass ((function c hc).eval p hp.1)
  let DP := scalarClass ((function d hd).eval p hp.2)
  let DC := scalarClass ((holomorphic c hc).derivative w hw.1)
  let DD := scalarClass ((holomorphic d hd).derivative w hw.2)
  let W := scalarClass w
  let Z := scalarClass z
  change DC=DD at hD
  change (((CZ-DZ)-(CP-DP))-((CW-DW)-(CP-DP)))-(Z-W)*0=
    ((CZ-CW)-DC*(Z-W))-((DZ-DW)-DD*(Z-W))
  grind only

private theorem field_uniform_remainder (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d)
    (p : Scalar) (hp : commonDomain c d hc hd p)
    (eps H : QPos) (w z : Scalar) (hw : commonDomain c d hc hd w) (hz : commonDomain c d hc hd z)
    (hH : H.val≤(overlapDelta c d hc hd eps).val) (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound (UniformSegment.remainder (fun _ _ => ValueMap.zeroBetween 1 1)
      (differenceField c d hc hd p hp) w z hw hz) (eps.val*H.val) := by
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
    ((UniformSegment.remainder (fun _ _ => ValueMap.zeroBetween 1 1)
      (differenceField c d hc hd p hp) w z hw hz).property i)
    (equiv_symm (field_remainder c d hc hd p hp w z hw hz i)) hs

/-- Two arbitrary relative logarithm branches have the same difference at
all inputs of their actual overlap. No mutual-center inclusion is required. -/
theorem relativeLogarithm_overlap_difference_constant (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d)
    (p z : Scalar) (hp : commonDomain c d hc hd p) (hz : commonDomain c d hc hd z) :
    (sub ((function c hc).eval z hz.1).val ((function d hd).eval z hz.2).val).Equiv
      (sub ((function c hc).eval p hp.1).val ((function d hd).eval p hp.2).val) := by
  let D := commonDomain c d hc hd
  let f := differenceField c d hc hd p hp
  let W := MatrixExponential.pointRadius (AffineSegment.displacement p z)
  have hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw := by
    intro z w hz hw he i
    exact FunctionTheory.sub_congr
      (FunctionTheory.sub_congr ((function c hc).eval_congr z w hz.1 hw.1 he)
        ((function d hd).eval_congr z w hz.2 hw.2 he))
      (equiv_refl _ (sub_valid ((function c hc).eval p hp.1).property ((function d hd).eval p hp.2).property))
  have hf0 : f p hp ≈ Fiber.zero 1 := by
    intro i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (f p hp).property i) (hright := ofQComplex_valid _)
    let C := scalarClass ((function c hc).eval p hp.1)
    let E := scalarClass ((function d hd).eval p hp.2)
    change (C-E)-(C-E)=0
    grind only
  have hfB : ∀ w hw, CoordinateBound (f w hw) 16 := by
    intro w hw i
    have hs := SeriesLimitLaws.small_sub
      (SeriesLimitLaws.small_sub (value_bound c hc w hw.1) (value_bound d hd w hw.2))
      (SeriesLimitLaws.small_sub (value_bound c hc p hp.1) (value_bound d hd p hp.2))
    have he : (4+4+(4+4):Rat)=16 := by decide +kernel
    rw [he] at hs
    exact hs
  have hzero := UniformSegment.zero D p z hp hz
    (fun t ht => ⟨affine_mem c hc p z hp.1 hz.1 t ht,affine_mem d hd p z hp.2 hz.2 t ht⟩)
    W (interior_bound W.val (AffineSegment.displacement p z) (MatrixExponential.pointRadius_inside _))
    (fun _ _ => ValueMap.zeroBetween 1 1) f 0 16 (by decide +kernel)
    (by simp only [Rat.mul_zero]; decide +kernel) (by decide +kernel) hfcongr hf0 hfB
    (by
      intro _ _ B hB x hx
      change CoordinateBound (Fiber.zero 1) (0*B)
      rw [Rat.zero_mul]
      exact bound_zero 0 (by decide +kernel))
    (overlapDelta c d hc hd) (field_uniform_remainder c d hc hd p hp)
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (f z hz).property 0) (hright := ofQComplex_valid _) (hzero 0)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid ((function c hc).eval z hz.1).property ((function d hd).eval z hz.2).property)
    (hright := sub_valid ((function c hc).eval p hp.1).property ((function d hd).eval p hp.2).property)
  let A := scalarClass ((function c hc).eval z hz.1)
  let B := scalarClass ((function d hd).eval z hz.2)
  let C := scalarClass ((function c hc).eval p hp.1)
  let E := scalarClass ((function d hd).eval p hp.2)
  change (A-B)-(C-E)=0 at hh
  change A-B=C-E
  grind only

end ComputableAnalysis.ModularForms
