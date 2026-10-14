import ComputableAnalysis.RiemannHilbert.RectangularPoleSearch
import ComputableAnalysis.RiemannHilbert.ContourEffectiveReciprocalBounds

/-! A uniform actual reciprocal bound on all four represented boundary
edges, computed for every interior or exterior pole. No pointwise reciprocal
bound, rational pole, or interior source extension is supplied by the caller. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularPoleReciprocal
open ComplexRaw FunctionTheory DomainFunctions RectangularContour RepresentedReciprocal BoxApproximation
set_option autoImplicit false
variable (inside : Bool) (J : QInterval × QInterval) (b : Scalar) (hb : RectangularPoleSearch.domain inside J b)

def offsetBound : QPos :=
  ⟨LocalODE.boxCoordinateBound ⟨⟨J.1.lo,J.2.lo⟩,⟨J.1.hi,J.2.hi⟩⟩ +
    LocalODE.boxCoordinateBound (b.val.compute 0)+1,by
      have h := LocalODE.boxCoordinateBound_nonneg ⟨⟨J.1.lo,J.2.lo⟩,⟨J.1.hi,J.2.hi⟩⟩
      have h' := LocalODE.boxCoordinateBound_nonneg (b.val.compute 0)
      grind only⟩

def referenceBound : QPos :=
  ⟨(offsetBound J b).val/((RectangularPoleSearch.clearance inside J b hb).val*
    (RectangularPoleSearch.clearance inside J b hb).val),by
      rw [Rat.div_def]
      exact Rat.mul_pos (offsetBound J b).property
        (Rat.inv_pos.mpr (Rat.mul_pos (RectangularPoleSearch.clearance inside J b hb).property
          (RectangularPoleSearch.clearance inside J b hb).property))⟩

def tolerance : QPos :=
  ⟨1/(16*(referenceBound inside J b hb).val),by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.inv_pos.mpr (Rat.mul_pos (by decide +kernel) (referenceBound inside J b hb).property)⟩

theorem tolerance_budget : 16*(referenceBound inside J b hb).val*(tolerance inside J b hb).val=1 := by
  change 16*(referenceBound inside J b hb).val*(1/(16*(referenceBound inside J b hb).val))=1
  rw [Rat.div_def,Rat.one_mul]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.mul_pos (by decide +kernel) (referenceBound inside J b hb).property))

def approximationStage : Nat :=
  PrecisionSearch.firstFrom (PrecisionSearch.adequate b.val (tolerance inside J b hb))
    (PrecisionSearch.eventually_adequate b.val b.property (tolerance inside J b hb))
    (RectangularPoleSearch.stage inside J b hb)

theorem approximation_spec : RectangularPoleSearch.stage inside J b hb≤approximationStage inside J b hb ∧
    (b.val.compute (approximationStage inside J b hb)).width≤(tolerance inside J b hb).val ∧
    (b.val.compute (approximationStage inside J b hb)).height≤(tolerance inside J b hb).val := by
  have h := PrecisionSearch.firstFrom_spec (PrecisionSearch.adequate b.val (tolerance inside J b hb))
    (PrecisionSearch.eventually_adequate b.val b.property (tolerance inside J b hb))
    (RectangularPoleSearch.stage inside J b hb)
  exact ⟨h.1,by simpa [PrecisionSearch.adequate,approximationStage] using h.2⟩

def center : QComplex := (b.val.compute (approximationStage inside J b hb)).center

theorem center_mem : (b.val.compute (RectangularPoleSearch.stage inside J b hb)).lo≤center inside J b hb ∧
    center inside J b hb≤(b.val.compute (RectangularPoleSearch.stage inside J b hb)).hi := by
  have h := valid_nestedIn b.property (approximation_spec inside J b hb).1
  have hc := QBox.center_mem (valid_ordered b.property (approximationStage inside J b hb))
  exact ⟨QComplex.le_trans h.1 hc.1,QComplex.le_trans hc.2 h.2⟩

theorem center_error : Small (Centered.offset (rationalRectangleScalar (center inside J b hb)) b).val
    (tolerance inside J b hb).val :=
  BoxApproximation.center_error b (approximationStage inside J b hb) _
    (Rat.le_of_lt (tolerance inside J b hb).property) (approximation_spec inside J b hb).2.1
    (approximation_spec inside J b hb).2.2

theorem boundary_mem (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi) (q : QComplex)
    (hq : rationalRectangleBoundaryContains J q) : rationalRectangleContains J q := by
  rcases hq with hq|hq|hq|hq <;>
    dsimp [rationalRectangleContains,horizontalIntervalRectangle,verticalIntervalRectangle] at hq ⊢ <;> grind only

theorem offset_bounds (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi) (q : QComplex)
    (hq : rationalRectangleBoundaryContains J q) :
    coordinateBound (QComplex.sub q (center inside J b hb))≤(offsetBound J b).val ∧
      ((RectangularPoleSearch.clearance inside J b hb).val≤(QComplex.sub q (center inside J b hb)).re ∨
        (QComplex.sub q (center inside J b hb)).re≤ -(RectangularPoleSearch.clearance inside J b hb).val ∨
        (RectangularPoleSearch.clearance inside J b hb).val≤(QComplex.sub q (center inside J b hb)).im ∨
        (QComplex.sub q (center inside J b hb)).im≤ -(RectangularPoleSearch.clearance inside J b hb).val) := by
  let B := b.val.compute (RectangularPoleSearch.stage inside J b hb)
  let D := RectangularPoleSearch.clearance inside J b hb
  let c := center inside J b hb
  have hc := center_mem inside J b hb
  have hqJ := boundary_mem J hx hy q hq
  constructor
  · have hj := LocalODE.boxCoordinateBound_bounds ⟨⟨J.1.lo,J.2.lo⟩,⟨J.1.hi,J.2.hi⟩⟩
    have hb0 := BoxApproximation.center_bound b (approximationStage inside J b hb)
    have hcc := coordinateBound_bounds c
    change coordinateBound c≤LocalODE.boxCoordinateBound (b.val.compute 0) at hb0
    dsimp [coordinateBound,qabs,QComplex.sub,QComplex.neg,QComplex.add,offsetBound,rationalRectangleContains] at *
    split <;> split <;> grind
  · have hs := RectangularPoleSearch.margin_spec inside J B
    change (if inside then D.val≤B.lo.re-J.1.lo ∧ D.val≤J.1.hi-B.hi.re ∧
      D.val≤B.lo.im-J.2.lo ∧ D.val≤J.2.hi-B.hi.im else
      B.hi.re+D.val≤J.1.lo ∨ J.1.hi+D.val≤B.lo.re ∨
      B.hi.im+D.val≤J.2.lo ∨ J.2.hi+D.val≤B.lo.im) at hs
    change (B.lo.re≤c.re ∧ B.lo.im≤c.im) ∧ (c.re≤B.hi.re ∧ c.im≤B.hi.im) at hc
    change D.val≤q.re + -c.re ∨ q.re + -c.re≤ -D.val ∨
      D.val≤q.im + -c.im ∨ q.im + -c.im≤ -D.val
    cases inside
    · simp only [Bool.false_eq_true,if_false] at hs
      dsimp [rationalRectangleContains] at hqJ
      grind only
    · simp only [if_true] at hs
      rcases hq with hq|hq|hq|hq <;>
        dsimp [rationalRectangleContains,horizontalIntervalRectangle,verticalIntervalRectangle] at hq <;> grind only

theorem reference_nonzero (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi) (q : QComplex)
    (hq : rationalRectangleBoundaryContains J q) :
    NonzeroBoxSearch.Nonzero (rationalRectangleScalar (QComplex.sub q (center inside J b hb))) :=
  let w := QComplex.sub q (center inside J b hb)
  representedRectangle_nonzero (⟨w.re,w.re⟩,⟨w.im,w.im⟩) (RectangularPoleSearch.clearance inside J b hb)
    (offset_bounds inside J b hb hx hy q hq).2 _
    (rationalRectangle_represented_mem _ w ⟨Rat.le_refl,Rat.le_refl,Rat.le_refl,Rat.le_refl⟩)

theorem reference_inverse_bound (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi) (q : QComplex)
    (hq : rationalRectangleBoundaryContains J q)
    (hn : NonzeroBoxSearch.Nonzero (rationalRectangleScalar (QComplex.sub q (center inside J b hb)))) :
    Small (inverse (rationalRectangleScalar (QComplex.sub q (center inside J b hb))) hn).val
      (referenceBound inside J b hb).val := by
  let w := QComplex.sub q (center inside J b hb)
  let D := RectangularPoleSearch.clearance inside J b hb
  have hs := offset_bounds inside J b hb hx hy q hq
  have hnorm : D.val*D.val≤QComplex.normSq w := by
    have hx := rat_square_nonneg_basic w.re
    have hy := rat_square_nonneg_basic w.im
    rcases hs.2 with h|h|h|h
    · have h := square_lower_of_separated D w.re (Or.inl h); unfold QComplex.normSq; grind only
    · have h := square_lower_of_separated D w.re (Or.inr h); unfold QComplex.normSq; grind only
    · have h := square_lower_of_separated D w.im (Or.inl h); unfold QComplex.normSq; grind only
    · have h := square_lower_of_separated D w.im (Or.inr h); unfold QComplex.normSq; grind only
  have hp : 0<QComplex.normSq w := by have h := Rat.mul_pos D.property D.property; grind only
  have hc := RationalReciprocal.coordinateBound_inverse w (offsetBound J b).val (D.val*D.val)
    (Rat.le_of_lt (offsetBound J b).property) (Rat.mul_pos D.property D.property) hnorm hs.1
  exact Small.congr (ofQComplex_valid _) (inverse _ hn).property
    (equiv_symm (rational_inverse_agreement w hn (Rat.ne_of_gt hp))) ((rational_small _).mono hc)

def bound : QPos := ⟨8*(referenceBound inside J b hb).val,
  Rat.mul_pos (by decide +kernel) (referenceBound inside J b hb).property⟩

theorem sample_bound (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi) (q : QComplex)
    (hq : rationalRectangleBoundaryContains J q) (hz : (ribbonPoleReciprocal b).domain (rationalRectangleScalar q)) :
    Small ((ribbonPoleReciprocal b).eval (rationalRectangleScalar q) hz).val (bound inside J b hb).val := by
  let w := rationalRectangleScalar (QComplex.sub q (center inside J b hb))
  let z := (ribbonPoleOffset b).eval (rationalRectangleScalar q) trivial
  have hn := reference_nonzero inside J b hb hx hy q hq
  have he : gridScalarSub z w≈scalarNeg (Centered.offset (rationalRectangleScalar (center inside J b hb)) b) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (gridScalarSub z w).property)
      (hright := (scalarNeg (Centered.offset (rationalRectangleScalar (center inside J b hb)) b)).property)
    change (-gridScalarValue b+1*gridScalarValue (rationalRectangleScalar q))-
      (gridScalarValue (rationalRectangleScalar q)-gridScalarValue (rationalRectangleScalar (center inside J b hb)))=
      -(gridScalarValue b-gridScalarValue (rationalRectangleScalar (center inside J b hb)))
    grind only
  have hd := Small.congr (neg_valid (Centered.offset (rationalRectangleScalar (center inside J b hb)) b).property)
    (sub_valid z.property w.property) (equiv_symm he) (SeriesLimitLaws.small_neg (center_error inside J b hb))
  obtain ⟨hnz,hbound⟩ := inverse_near_exists_bound w z hn _ _
    (Rat.le_of_lt (referenceBound inside J b hb).property) (Rat.le_of_lt (tolerance inside J b hb).property)
    (reference_inverse_bound inside J b hb hx hy q hq hn) hd
    (by rw [tolerance_budget]; exact Rat.le_refl)
  exact hbound

include inside hb in
theorem boundaryDomains (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi) :
    RectangleBoundaryDomains (ribbonPoleReciprocal b) J := by
  cases inside
  · apply rectangleBoundaryDomains_of_rectangle _ J hx hy
    intro w hw
    exact ⟨trivial,AnnularPoleGeometry.offset_nonzero J b w hb hw⟩
  · exact rectanglePoleReciprocalBoundaryDomains J b hb

theorem boundary_bound (hx : J.1.lo≤J.1.hi) (hy : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains (ribbonPoleReciprocal b) J) :
    RectangleBoundaryValueBound (ribbonPoleReciprocal b) J hd (bound inside J b hb) :=
  rectangleBoundaryValueBound_of_rational _ (ribbonPoleReciprocal_holomorphic b).continuous J hx hy hd
    (bound inside J b hb) (sample_bound inside J b hb hx hy)

end ComputableAnalysis.RiemannHilbert.RectangularPoleReciprocal
