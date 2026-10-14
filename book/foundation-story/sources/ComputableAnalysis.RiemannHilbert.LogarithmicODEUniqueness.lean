import ComputableAnalysis.RiemannHilbert.LogarithmicModelUniform

/-! Exact comparison of supplied justified solutions of A/z throughout a
normalized logarithm chart. The actual inverse frame has constructed uniform
remainders and reduces comparison to the zero equation. Neither a residue
smallness condition nor a caller-selected segment radius is required. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField NonzeroBoxSearch
set_option maxHeartbeats 1000000
variable {n : Nat}

/-- Conditional uniqueness for actual solution fields with supplied uniform
solution evidence. All frame estimates and segment choices are constructed. -/
theorem ode_equal_on (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (D : Scalar → Prop) (hD : ∀ z, D z → RelativeLogarithm.domain c hc z)
    (p q : Scalar) (hp : D p) (hq : D q)
    (coverage : ∀ t, UniformPath.unitInterval t → D (AffineSegment.point p q t))
    (f g : UniformSegment.Field (n := n) D)
    (B C : Rat) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw)
    (hgcongr : ∀ z w hz hw, z.val.Equiv w.val → g z hz ≈ g w hw)
    (hinitial : f p hp ≈ g p hp)
    (hfB : ∀ z hz, CoordinateBound (f z hz) B) (hgB : ∀ z hz, CoordinateBound (g z hz) C)
    (deltaF deltaG : QPos → QPos)
    (hfrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaF eps).val →
      Small (sub z.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (fun z hz => operator A c hc z (hD z hz)) f w z hw hz) (eps.val*H.val))
    (hgrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaG eps).val →
      Small (sub z.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (fun z hz => operator A c hc z (hD z hz)) g w z hw hz) (eps.val*H.val)) :
    f q hq ≈ g q hq := by
  let G : Field (n := n) (m := n) D := fun z hz => inverseField (frame A hA c hc) z (hD z hz)
  let DG : Field (n := n) (m := n) D := fun z hz => inverseSlope A hA c hc z (hD z hz)
  let Op : UniformSegment.OperatorField (n := n) D := fun z hz => operator A c hc z (hD z hz)
  let Z := ValueMap.zeroBetween n n
  let P := valueBound (MatrixExponential.negativeOperator A)
  let Q := derivativeBound (MatrixExponential.negativeOperator A) c hc
  let U := operatorBound A c hc
  have hP := valueBound_nonneg (MatrixExponential.negativeOperator A)
  have hQ := derivativeBound_nonneg (MatrixExponential.negativeOperator A) c hc
  have hU := operatorBound_nonneg A c hc
  let dG := uniformDelta (MatrixExponential.negativeOperator A) c hc
  let df := productDelta P Q B (U*B) hP hQ hB (Rat.mul_nonneg hU hB) deltaF dG
  let dg := productDelta P Q C (U*C) hP hQ hC (Rat.mul_nonneg hU hC) deltaG dG
  let W := MatrixExponential.pointRadius (AffineSegment.displacement p q)
  have hs := UniformSegment.equal D p q hp hq coverage W
    (interior_bound W.val _ (MatrixExponential.pointRadius_inside _)) (fun _ _ => Z) (product G f) (product G g)
    0 (P*B) (P*C) (by decide)
    (by simpa only [Rat.mul_zero] using (by decide +kernel : (0 : Rat) ≤ (1 : Rat)/2))
    (Rat.mul_nonneg hP hB) (Rat.mul_nonneg hP hC)
    (product_congr G f (fun z w hz hw hzw => inverse_congr A hA c hc z w (hD z hz) (hD w hw) hzw) hfcongr)
    (product_congr G g (fun z w hz hw hzw => inverse_congr A hA c hc z w (hD z hz) (hD w hw) hzw) hgcongr)
    ((G p hp).congr hinitial)
    (fun z hz => inverse_bound A hA c hc z (hD z hz) B hB _ (hfB z hz))
    (fun z hz => inverse_bound A hA c hc z (hD z hz) C hC _ (hgB z hz))
    (fun _ _ => ValueMap.zeroBetween_linear n n)
    (by intro _ _ _ _ _ _; simpa only [Z, ValueMap.zeroBetween, Rat.zero_mul] using (bound_zero (n := n) 0 (by decide)))
    df dg
    (horizontal_product_remainder G DG Op (fun _ _ => Z) f
      (fun z hz => (frame A hA c hc z (hD z hz)).inverse.linear) (fun z hz => inverseSlope_compatible A hA c hc z (hD z hz))
      P Q U B hP hQ hU hB (fun z hz => inverse_bound A hA c hc z (hD z hz)) (fun z hz => inverseSlope_bound A hA c hc z (hD z hz))
      (fun z hz => operator_bound A hA c hc z (hD z hz)) hfB deltaF dG hfrem (fun eps H w z hw hz => inverse_uniform_remainder A hA c hc eps H w z (hD w hw) (hD z hz)))
    (horizontal_product_remainder G DG Op (fun _ _ => Z) g
      (fun z hz => (frame A hA c hc z (hD z hz)).inverse.linear) (fun z hz => inverseSlope_compatible A hA c hc z (hD z hz))
      P Q U C hP hQ hU hC (fun z hz => inverse_bound A hA c hc z (hD z hz)) (fun z hz => inverseSlope_bound A hA c hc z (hD z hz))
      (fun z hz => operator_bound A hA c hc z (hD z hz)) hgB deltaG dG hgrem (fun eps H w z hw hz => inverse_uniform_remainder A hA c hc eps H w z (hD w hw) (hD z hz)))
  exact (frame A hA c hc q (hD q hq)).toValueIso.inverse.forward_reflects hs

/-- Conditional uniqueness for actual solution fields with supplied uniform
solution evidence. All frame estimates and segment choices are constructed. -/
theorem ode_equal (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p q : Scalar) (hp : RelativeLogarithm.domain c hc p) (hq : RelativeLogarithm.domain c hc q)
    (f g : UniformSegment.Field (n := n) (RelativeLogarithm.domain c hc))
    (B C : Rat) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw)
    (hgcongr : ∀ z w hz hw, z.val.Equiv w.val → g z hz ≈ g w hw)
    (hinitial : f p hp ≈ g p hp)
    (hfB : ∀ z hz, CoordinateBound (f z hz) B) (hgB : ∀ z hz, CoordinateBound (g z hz) C)
    (deltaF deltaG : QPos → QPos)
    (hfrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaF eps).val →
      Small (sub z.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (operator A c hc) f w z hw hz) (eps.val*H.val))
    (hgrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaG eps).val →
      Small (sub z.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (operator A c hc) g w z hw hz) (eps.val*H.val)) :
    f q hq ≈ g q hq :=
  ode_equal_on A hA c hc (RelativeLogarithm.domain c hc) (fun _ hz => hz) p q hp hq
    (RelativeLogarithm.affine_mem c hc p q hp hq) f g B C hB hC hfcongr hgcongr hinitial hfB hgB deltaF deltaG hfrem hgrem

end ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
