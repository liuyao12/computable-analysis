import ComputableAnalysis.RiemannHilbert.ExponentialFrameHolomorphic

/-! Exact uniqueness for supplied constant-coefficient solutions on every
finite disc. The proved inverse exponential turns the equation into the zero
equation, so no smallness assumption on the segment or residue is needed. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField
variable {n : Nat}

theorem offset_zero (z : Scalar) :
    (Centered.offset ⟨zero, ofQComplex_valid _⟩ z).val.Equiv z.val :=
  equiv_trans (Centered.offset ⟨zero, ofQComplex_valid _⟩ z).property
    (Centered.translate ⟨zero, ofQComplex_valid _⟩ (Centered.offset ⟨zero, ofQComplex_valid _⟩ z)).property z.property
    (equiv_symm (zero_add_equiv _ (Centered.offset ⟨zero, ofQComplex_valid _⟩ z).property))
    (Centered.translate_offset ⟨zero, ofQComplex_valid _⟩ z)

theorem disc_affine_mem (R : QPos) (p q : Scalar) (hp : interior R.val p) (hq : interior R.val q)
    (t : Rat) (ht : UniformPath.unitInterval t) : interior R.val (AffineSegment.point p q t) := by
  have hc := AffineSegment.mem ⟨zero, ofQComplex_valid _⟩ p q R.val
    (Centered.interior_congr R.val p (Centered.offset ⟨zero, ofQComplex_valid _⟩ p) (equiv_symm (offset_zero p)) hp)
    (Centered.interior_congr R.val q (Centered.offset ⟨zero, ofQComplex_valid _⟩ q) (equiv_symm (offset_zero q)) hq) t ht
  exact Centered.interior_congr R.val _ _ (offset_zero (AffineSegment.point p q t)) hc

theorem disc_inverse_compatible (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (R : QPos) :
    Compatible (discField (negativeOperator A) (negativeOperator_linear A hA) R)
      (discSlope (negativeOperator A) (negativeOperator_linear A hA) R)
      (fun _ _ => A) (fun _ _ => ValueMap.zeroBetween n n) := by
  intro z _ x
  exact Setoid.trans (Fiber.add_congr (negativeOperator_value A _)
      (Setoid.symm (negative_exponential_commutes A hA z x)))
    (Setoid.trans (Fiber.add_comm _ _) (fun i => add_neg_equiv _
      ((A.eval ((value (negativeOperator A) (negativeOperator_linear A hA) z).eval x)).property i)))

/-- A conditional uniqueness law for supplied solution fields with justified
uniform first-order remainders. Bounds and radii are evidence for the fields;
there is no restriction on the residue or the distance between endpoints. -/
theorem constant_ode_equal_on_disc (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (p q : Scalar) (hp : interior R.val p) (hq : interior R.val q)
    (f g : UniformSegment.Field (n := n) (interior R.val))
    (B C : Rat) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw)
    (hgcongr : ∀ z w hz hw, z.val.Equiv w.val → g z hz ≈ g w hw)
    (hinitial : f p hp ≈ g p hp)
    (hfB : ∀ z hz, CoordinateBound (f z hz) B) (hgB : ∀ z hz, CoordinateBound (g z hz) C)
    (deltaF deltaG : QPos → QPos)
    (hfrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaF eps).val →
      Small (sub z.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (fun _ _ => A) f w z hw hz) (eps.val*H.val))
    (hgrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaG eps).val →
      Small (sub z.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (fun _ _ => A) g w z hw hz) (eps.val*H.val)) :
    f q hq ≈ g q hq := by
  let G := discField (negativeOperator A) (negativeOperator_linear A hA) R
  let DG := discSlope (negativeOperator A) (negativeOperator_linear A hA) R
  let Z := ValueMap.zeroBetween n n
  let P := discValueBound (negativeOperator A) R
  let Q := discDerivativeBound (negativeOperator A) R
  let U := ValueMap.linearBound A
  have hP := discValueBound_nonneg (negativeOperator A) R
  have hQ := discDerivativeBound_nonneg (negativeOperator A) R
  have hU := ValueMap.linearBound_nonneg A
  let df := productDelta P Q B (U*B) hP hQ hB (Rat.mul_nonneg hU hB) deltaF (discDelta (negativeOperator A) R)
  let dg := productDelta P Q C (U*C) hP hQ hC (Rat.mul_nonneg hU hC) deltaG (discDelta (negativeOperator A) R)
  let W := pointRadius (AffineSegment.displacement p q)
  have hs := UniformSegment.equal (interior R.val) p q hp hq (disc_affine_mem R p q hp hq)
    W (interior_bound W.val _ (pointRadius_inside _)) (fun _ _ => Z) (product G f) (product G g)
    0 (P*B) (P*C) (by decide)
    (by simpa only [Rat.mul_zero] using (by decide +kernel : (0 : Rat) ≤ (1 : Rat)/2))
    (Rat.mul_nonneg hP hB) (Rat.mul_nonneg hP hC)
    (product_congr G f (fun z w _ _ hzw => field_congr (negativeOperator A) (negativeOperator_linear A hA) z w True.intro True.intro hzw) hfcongr)
    (product_congr G g (fun z w _ _ hzw => field_congr (negativeOperator A) (negativeOperator_linear A hA) z w True.intro True.intro hzw) hgcongr)
    ((G p hp).congr hinitial)
    (fun z hz => discField_bound _ (negativeOperator_linear A hA) R z hz B hB _ (hfB z hz))
    (fun z hz => discField_bound _ (negativeOperator_linear A hA) R z hz C hC _ (hgB z hz))
    (fun _ _ => ValueMap.zeroBetween_linear n n)
    (by intro _ _ _ _ _ _; simpa only [Z, ValueMap.zeroBetween, Rat.zero_mul] using (bound_zero (n := n) 0 (by decide)))
    df dg
    (horizontal_product_remainder G DG (fun _ _ => A) (fun _ _ => Z) f
      (fun z _ => value_linear _ (negativeOperator_linear A hA) z) (disc_inverse_compatible A hA R)
      P Q U B hP hQ hU hB (discField_bound _ (negativeOperator_linear A hA) R)
      (discSlope_bound _ (negativeOperator_linear A hA) R)
      (fun _ _ => ValueMap.linear_bound A hA) hfB deltaF (discDelta (negativeOperator A) R)
      hfrem (disc_uniform_remainder _ (negativeOperator_linear A hA) R))
    (horizontal_product_remainder G DG (fun _ _ => A) (fun _ _ => Z) g
      (fun z _ => value_linear _ (negativeOperator_linear A hA) z) (disc_inverse_compatible A hA R)
      P Q U C hP hQ hU hC (discField_bound _ (negativeOperator_linear A hA) R)
      (discSlope_bound _ (negativeOperator_linear A hA) R)
      (fun _ _ => ValueMap.linear_bound A hA) hgB deltaG (discDelta (negativeOperator A) R)
      hgrem (disc_uniform_remainder _ (negativeOperator_linear A hA) R))
  exact (frame A hA q).toValueIso.inverse.forward_reflects hs

end ComputableAnalysis.RiemannHilbert.MatrixExponential
