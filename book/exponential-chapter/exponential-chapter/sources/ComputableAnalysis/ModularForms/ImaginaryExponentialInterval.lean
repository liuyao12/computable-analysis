import ComputableAnalysis.ModularForms.BoundedAngleFromBounds

/-! Exact injectivity of the actual imaginary exponential on the semantic
angle interval [1,2], without restrictions on the supplied interval names. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

/-- The actual angle map agrees with the actual exponential of the imaginary
embedding, for every valid represented real argument. -/
theorem angleRotationMap_real_exponential (x : RealRaw) (hx : x.Valid) :
    (angleRotationMap.eval ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩ ⟨trivial,trivial⟩).val.Equiv
      (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val := by
  let z : Scalar := ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩
  let a := (DomainFunctions.affine ⟨zero,ofQComplex_valid _⟩ latticeImaginaryUnit).eval z trivial
  let b : Scalar := ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩
  have hc : (qcomplexLeftMul ⟨0,1⟩ z.val).Equiv b.val := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    have he : (qcomplexLeftMul ⟨0,1⟩ z.val).compute n=b.val.compute n := by
      change (add (scaleRat 0 z.val) (scaleRat 1 (mulI z.val))).compute n=_
      dsimp [z,b,imaginaryAxis,ofRealRaw,mulI,scaleRat,add,QBox.scaleRat,QBox.add,QComplex.add]
      simp only [if_pos (show (0:Rat)≤1 by decide +kernel),Rat.zero_mul,Rat.one_mul,
        Rat.zero_add,Rat.add_zero]
    rw [he]
    have ho := valid_ordered b.property n
    exact ⟨ho,ho⟩
  have hq := qcomplexLeftMul_equiv_mul_ofQComplex ⟨0,1⟩ z.property
  have ha : a.val.Equiv (mul latticeImaginaryUnit.val z.val) :=
    zero_add_equiv _ (mul_valid latticeImaginaryUnit.property z.property)
  exact entireExponentialValue_congr a b
    (equiv_trans a.property (mul_valid latticeImaginaryUnit.property z.property) b.property ha
      (equiv_trans (mul_valid latticeImaginaryUnit.property z.property)
        (qcomplexLeftMul_valid ⟨0,1⟩ z.property) b.property (equiv_symm hq) hc))

/-- Semantic interval membership suffices for angle uniqueness. Computed
boxes and rescheduling choices are internal to the theorem. -/
theorem angleRotationMap_interval_unique (x y : RealRaw) (hx : x.Valid) (hy : y.Valid)
    (hxl : (RealRaw.ofRat 1).Le x) (hxu : x.Le (RealRaw.ofRat 2))
    (hyl : (RealRaw.ofRat 1).Le y) (hyu : y.Le (RealRaw.ofRat 2))
    (he : (angleRotationMap.eval ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩ ⟨trivial,trivial⟩).val.realPart.Equiv
      (angleRotationMap.eval ⟨ofRealRaw y,ofRealRaw_valid _ hy⟩ ⟨trivial,trivial⟩).val.realPart) :
    x.Equiv y := by
  let A := boundedAngleFromBounds x hx hxl hxu
  let B := boundedAngleFromBounds y hy hyl hyu
  let X : Scalar := ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩
  let Y : Scalar := ⟨ofRealRaw y,ofRealRaw_valid _ hy⟩
  have ha := angleRotationMap.eval_congr A.scalar X ⟨trivial,trivial⟩ ⟨trivial,trivial⟩
    (ofRealRaw_equiv_of_equiv A.valid hx (boundedAngleFromBounds_agreement x hx hxl hxu))
  have hb := angleRotationMap.eval_congr B.scalar Y ⟨trivial,trivial⟩ ⟨trivial,trivial⟩
    (ofRealRaw_equiv_of_equiv B.valid hy (boundedAngleFromBounds_agreement y hy hyl hyu))
  have hu := represented_rotation_angle_unique A B
    (RealRaw.equiv_trans (realPart_valid (angleRotationMap.eval A.scalar ⟨trivial,trivial⟩).property)
      (realPart_valid (angleRotationMap.eval X ⟨trivial,trivial⟩).property)
      (realPart_valid (angleRotationMap.eval B.scalar ⟨trivial,trivial⟩).property)
      (realPart_equiv ha)
      (RealRaw.equiv_trans (realPart_valid (angleRotationMap.eval X ⟨trivial,trivial⟩).property)
        (realPart_valid (angleRotationMap.eval Y ⟨trivial,trivial⟩).property)
        (realPart_valid (angleRotationMap.eval B.scalar ⟨trivial,trivial⟩).property) he
        (RealRaw.equiv_symm (realPart_equiv hb))))
  exact RealRaw.equiv_trans hx A.valid hy
    (RealRaw.equiv_symm (boundedAngleFromBounds_agreement x hx hxl hxu))
    (RealRaw.equiv_trans A.valid B.valid hy hu (boundedAngleFromBounds_agreement y hy hyl hyu))

/-- The imaginary exponential is injective throughout the semantic interval
[1,2], for arbitrary valid represented real inputs. -/
theorem entireExponential_imaginary_interval_injective (x y : RealRaw) (hx : x.Valid) (hy : y.Valid)
    (hxl : (RealRaw.ofRat 1).Le x) (hxu : x.Le (RealRaw.ofRat 2))
    (hyl : (RealRaw.ofRat 1).Le y) (hyu : y.Le (RealRaw.ofRat 2))
    (he : (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val.Equiv
      (entireExponentialValue ⟨imaginaryAxis y,imaginaryAxis_valid hy⟩).val) : x.Equiv y :=
  angleRotationMap_interval_unique x y hx hy hxl hxu hyl hyu
    (realPart_equiv
      (equiv_trans (angleRotationMap.eval ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩ ⟨trivial,trivial⟩).property
        (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).property
        (angleRotationMap.eval ⟨ofRealRaw y,ofRealRaw_valid _ hy⟩ ⟨trivial,trivial⟩).property
        (angleRotationMap_real_exponential x hx)
        (equiv_trans (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).property
          (entireExponentialValue ⟨imaginaryAxis y,imaginaryAxis_valid hy⟩).property
          (angleRotationMap.eval ⟨ofRealRaw y,ofRealRaw_valid _ hy⟩ ⟨trivial,trivial⟩).property he
          (equiv_symm (angleRotationMap_real_exponential y hy)))))

end ComputableAnalysis.ModularForms
