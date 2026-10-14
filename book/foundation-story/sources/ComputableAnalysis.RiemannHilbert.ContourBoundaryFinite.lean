import ComputableAnalysis.RiemannHilbert.ContourBoundaryBounds
import ComputableAnalysis.RiemannHilbert.ContourInnerBounds

/-! Exact linearity and mesh-independent bounds for actual rectangular
boundary quadratures. Only boundary samples enter the hypotheses. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions BoxApproximation
set_option autoImplicit false

theorem rectangleGridHorizontalPoint_boundary (J : QInterval × QInterval) (M j k : Nat)
    (hX : J.1.lo≤J.1.hi) (hM : 0<M) (hj : j<M) (hk : k=0 ∨ k=M) :
    rationalRectangleBoundaryContains J (rectangleGridHorizontalPoint J M j k) := by
  have ht := intervalGridTag_mem_interval J.1 M j hX hM hj
  rcases hk with hk|hk
  · subst k
    rw [rectangleGridHorizontalPoint_bottom]
    exact Or.inl ⟨ht.1,ht.2,Rat.le_refl,Rat.le_refl⟩
  · subst k
    rw [rectangleGridHorizontalPoint_top J M j hM]
    exact Or.inr (Or.inl ⟨ht.1,ht.2,Rat.le_refl,Rat.le_refl⟩)

theorem rectangleGridVerticalPoint_boundary (J : QInterval × QInterval) (M j k : Nat)
    (hY : J.2.lo≤J.2.hi) (hM : 0<M) (hk : k<M) (hj : j=0 ∨ j=M) :
    rationalRectangleBoundaryContains J (rectangleGridVerticalPoint J M j k) := by
  have ht := intervalGridTag_mem_interval J.2 M k hY hM hk
  rcases hj with hj|hj
  · subst j
    rw [rectangleGridVerticalPoint_left]
    exact Or.inr (Or.inr (Or.inl ⟨Rat.le_refl,Rat.le_refl,ht.1,ht.2⟩))
  · subst j
    rw [rectangleGridVerticalPoint_right J M k hM]
    exact Or.inr (Or.inr (Or.inr ⟨Rat.le_refl,Rat.le_refl,ht.1,ht.2⟩))

theorem rectangleGridBoundary_linear (a b : Scalar) (f g : QComplex → Scalar)
    (J : QInterval × QInterval) (M : Nat) :
    rectangleGridBoundary (sampleLinear a b f g) J M ≈
      scalarSum (scalarProduct a (rectangleGridBoundary f J M))
        (scalarProduct b (rectangleGridBoundary g J M)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (rectangleGridBoundary (sampleLinear a b f g) J M).property)
    (hright := (scalarSum (scalarProduct a (rectangleGridBoundary f J M))
      (scalarProduct b (rectangleGridBoundary g J M))).property)
  change gridScalarValue (rectangleGridBoundary (sampleLinear a b f g) J M)=
    gridScalarValue a*gridScalarValue (rectangleGridBoundary f J M)+
      gridScalarValue b*gridScalarValue (rectangleGridBoundary g J M)
  have hH (k : Nat) :
      gridScalarValue (gridScalarSum M (fun j => rectangleGridHorizontal (sampleLinear a b f g) J M j k))=
      gridScalarValue a*gridScalarValue (gridScalarSum M (fun j => rectangleGridHorizontal f J M j k))+
      gridScalarValue b*gridScalarValue (gridScalarSum M (fun j => rectangleGridHorizontal g J M j k)) := by
    simp only [gridScalarSum_value,horizontalSample_linear]
    exact gridValueSum_linear M _ _ _ _
  have hV (j : Nat) :
      gridScalarValue (gridScalarSum M (fun k => rectangleGridVertical (sampleLinear a b f g) J M j k))=
      gridScalarValue a*gridScalarValue (gridScalarSum M (fun k => rectangleGridVertical f J M j k))+
      gridScalarValue b*gridScalarValue (gridScalarSum M (fun k => rectangleGridVertical g J M j k)) := by
    simp only [gridScalarSum_value,verticalSample_linear]
    exact gridValueSum_linear M _ _ _ _
  simp only [rectangleGridBoundary,gridScalarBoundary,gridScalarValue_add,gridScalarSum_value,gridScalarValue_sub,gridValueSum_sub] at hH hV ⊢
  have hb := hH 0
  have ht := hH M
  have hr := hV M
  have hl := hV 0
  grind only

theorem rectangleGridBoundary_difference (f g : QComplex → Scalar) (J : QInterval × QInterval) (M : Nat) :
    rectangleGridBoundary (fun q => gridScalarSub (f q) (g q)) J M ≈
      gridScalarSub (rectangleGridBoundary f J M) (rectangleGridBoundary g J M) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (rectangleGridBoundary (fun q => gridScalarSub (f q) (g q)) J M).property)
    (hright := (gridScalarSub (rectangleGridBoundary f J M) (rectangleGridBoundary g J M)).property)
  have hH (j k : Nat) :
      gridScalarValue (rectangleGridHorizontal (fun q => gridScalarSub (f q) (g q)) J M j k)=
      gridScalarValue (rectangleGridHorizontal f J M j k)-gridScalarValue (rectangleGridHorizontal g J M j k) := by
    let F := gridScalarValue (f (rectangleGridHorizontalPoint J M j k))
    let G := gridScalarValue (g (rectangleGridHorizontalPoint J M j k))
    let V := gridScalarValue (rationalRectangleScalar ⟨rectangleGridStepX J M,0⟩)
    change (F-G)*V=F*V-G*V
    grind only
  have hV (j k : Nat) :
      gridScalarValue (rectangleGridVertical (fun q => gridScalarSub (f q) (g q)) J M j k)=
      gridScalarValue (rectangleGridVertical f J M j k)-gridScalarValue (rectangleGridVertical g J M j k) := by
    let F := gridScalarValue (f (rectangleGridVerticalPoint J M j k))
    let G := gridScalarValue (g (rectangleGridVerticalPoint J M j k))
    let V := gridScalarValue (rationalRectangleScalar ⟨0,rectangleGridStepY J M⟩)
    change (F-G)*V=F*V-G*V
    grind only
  change gridScalarValue (rectangleGridBoundary (fun q => gridScalarSub (f q) (g q)) J M)=
    gridScalarValue (rectangleGridBoundary f J M)-gridScalarValue (rectangleGridBoundary g J M)
  simp only [rectangleGridBoundary,gridScalarBoundary,gridScalarValue_add,gridScalarSum_value,
    gridScalarValue_sub,hH,hV,gridValueSum_sub]
  grind only

theorem rectangleGridBoundary_bound (f : QComplex → Scalar) (J : QInterval × QInterval) (M : Nat)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (hM : 0<M) (E : Rat) (hE : 0≤E)
    (hf : ∀ q, rationalRectangleBoundaryContains J q → Small (f q).val E) :
    Small (rectangleGridBoundary f J M).val (4*(J.1.width+J.2.width)*E) := by
  have hsx := intervalGridStep_nonneg J.1 M hX hM
  have hsy := intervalGridStep_nonneg J.2 M hY hM
  have hhor (j k : Nat) (hj : j<M) (hk : k=0 ∨ k=M) :
      Small (rectangleGridHorizontal f J M j k).val (2*E*intervalGridStep J.1 M) := by
    exact Small.mul (f _).property (rationalRectangleScalar _).property hE hsx
      (hf _ (rectangleGridHorizontalPoint_boundary J M j k hX hM hj hk))
      (by apply (rational_small _).mono; change coordinateBound ⟨intervalGridStep J.1 M,0⟩≤intervalGridStep J.1 M; unfold coordinateBound qabs; grind)
  have hver (j k : Nat) (hk : k<M) (hj : j=0 ∨ j=M) :
      Small (rectangleGridVertical f J M j k).val (2*E*intervalGridStep J.2 M) := by
    exact Small.mul (f _).property (rationalRectangleScalar _).property hE hsy
      (hf _ (rectangleGridVerticalPoint_boundary J M j k hY hM hk hj))
      (by apply (rational_small _).mono; change coordinateBound ⟨0,intervalGridStep J.2 M⟩≤intervalGridStep J.2 M; unfold coordinateBound qabs; grind)
  have hH := gridScalarSum_bound M
    (fun j => gridScalarSub (rectangleGridHorizontal f J M j 0) (rectangleGridHorizontal f J M j M))
    ((2*E*intervalGridStep J.1 M)+(2*E*intervalGridStep J.1 M))
    (by have hh := Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤2 by decide +kernel) hE) hsx; grind only)
    (fun j hj => SeriesLimitLaws.small_sub (hhor j 0 hj (Or.inl rfl)) (hhor j M hj (Or.inr rfl)))
  have hV := gridScalarSum_bound M
    (fun k => gridScalarSub (rectangleGridVertical f J M M k) (rectangleGridVertical f J M 0 k))
    ((2*E*intervalGridStep J.2 M)+(2*E*intervalGridStep J.2 M))
    (by have hh := Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤2 by decide +kernel) hE) hsy; grind only)
    (fun k hk => SeriesLimitLaws.small_sub (hver M k hk (Or.inr rfl)) (hver 0 k hk (Or.inl rfl)))
  have h := LocalODE.small_add hH hV
  have hx := intervalGridStep_total J.1 M hM
  have hy := intervalGridStep_total J.2 M hM
  have he : (M:Rat)*((2*E*intervalGridStep J.1 M)+(2*E*intervalGridStep J.1 M))+
      (M:Rat)*((2*E*intervalGridStep J.2 M)+(2*E*intervalGridStep J.2 M))=4*(J.1.width+J.2.width)*E := by grind only
  rw [he] at h
  exact h

theorem rectangleGridBoundary_difference_bound (f g : QComplex → Scalar) (J : QInterval × QInterval) (M : Nat)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (hM : 0<M) (E : Rat) (hE : 0≤E)
    (hf : ∀ q, rationalRectangleBoundaryContains J q → Small (sub (f q).val (g q).val) E) :
    Small (sub (rectangleGridBoundary f J M).val (rectangleGridBoundary g J M).val)
      (4*(J.1.width+J.2.width)*E) :=
  Small.congr (rectangleGridBoundary (fun q => gridScalarSub (f q) (g q)) J M).property
    (sub_valid (rectangleGridBoundary f J M).property (rectangleGridBoundary g J M).property)
    (rectangleGridBoundary_difference f g J M)
    (rectangleGridBoundary_bound _ J M hX hY hM E hE hf)

end ComputableAnalysis.RiemannHilbert.RectangularContour
