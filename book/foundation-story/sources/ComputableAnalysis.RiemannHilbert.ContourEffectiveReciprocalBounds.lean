import ComputableAnalysis.RiemannHilbert.ContourBoundaryValueBounds
import ComputableAnalysis.RiemannHilbert.ContourDerivativeRational

/-! Explicit reciprocal bounds on a rational square around an arbitrary
represented pole. Rational separation and perturbation give the sample bound;
continuity extends it to all represented points on the four edges. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RepresentedReciprocal BoxApproximation
set_option autoImplicit false

theorem rationalCenteredBoundary_offset_bounds (c q : QComplex) (R : QPos)
    (hq : rationalRectangleBoundaryContains (rationalCenteredRectangle c R.val) q) :
    Small (ofQComplex (QComplex.sub q c)) R.val ∧
    (R.val≤(QComplex.sub q c).re ∨ (QComplex.sub q c).re≤ -R.val ∨
      R.val≤(QComplex.sub q c).im ∨ (QComplex.sub q c).im≤ -R.val) := by
  have hp := R.property
  have coords : -R.val≤q.re-c.re ∧ q.re-c.re≤R.val ∧
      -R.val≤q.im-c.im ∧ q.im-c.im≤R.val := by
    rcases hq with hq|hq|hq|hq <;>
      dsimp [rationalRectangleContains,rationalCenteredRectangle,horizontalIntervalRectangle,verticalIntervalRectangle] at hq <;>
      grind only
  constructor
  · refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    · change -R.val≤q.re + -c.re; grind only
    · change q.re + -c.re≤R.val; grind only
    · change -R.val≤q.im + -c.im; grind only
    · change q.im + -c.im≤R.val; grind only
  · rcases hq with hq|hq|hq|hq <;>
      dsimp [rationalRectangleContains,rationalCenteredRectangle,horizontalIntervalRectangle,verticalIntervalRectangle] at hq
    · apply Or.inr (Or.inr (Or.inr ?_)); change q.im + -c.im≤ -R.val; grind only
    · apply Or.inr (Or.inr (Or.inl ?_)); change R.val≤q.im + -c.im; grind only
    · apply Or.inr (Or.inl ?_); change q.re + -c.re≤ -R.val; grind only
    · apply Or.inl; change R.val≤q.re + -c.re; grind only

theorem rationalCenteredBoundary_offset_nonzero (c q : QComplex) (R : QPos)
    (hq : rationalRectangleBoundaryContains (rationalCenteredRectangle c R.val) q) :
    NonzeroBoxSearch.Nonzero (rationalRectangleScalar (QComplex.sub q c)) :=
  let w := QComplex.sub q c
  representedRectangle_nonzero (⟨w.re,w.re⟩,⟨w.im,w.im⟩) R
    (rationalCenteredBoundary_offset_bounds c q R hq).2 _
    (rationalRectangle_represented_mem _ w ⟨Rat.le_refl,Rat.le_refl,Rat.le_refl,Rat.le_refl⟩)

theorem rationalCenteredBoundary_literal_inverse_bound (c q : QComplex) (R : QPos)
    (hq : rationalRectangleBoundaryContains (rationalCenteredRectangle c R.val) q)
    (hn : NonzeroBoxSearch.Nonzero (rationalRectangleScalar (QComplex.sub q c))) :
    Small (inverse (rationalRectangleScalar (QComplex.sub q c)) hn).val (1/R.val) := by
  let w := QComplex.sub q c
  have hs := rationalCenteredBoundary_offset_bounds c q R hq
  have hR2 := Rat.mul_pos R.property R.property
  have hnorm : R.val*R.val≤QComplex.normSq w := by
    have hx := rat_square_nonneg_basic w.re
    have hy := rat_square_nonneg_basic w.im
    rcases hs.2 with h|h|h|h
    · have h := square_lower_of_separated R w.re (Or.inl h); unfold QComplex.normSq; grind only
    · have h := square_lower_of_separated R w.re (Or.inr h); unfold QComplex.normSq; grind only
    · have h := square_lower_of_separated R w.im (Or.inl h); unfold QComplex.normSq; grind only
    · have h := square_lower_of_separated R w.im (Or.inr h); unfold QComplex.normSq; grind only
  have hp : 0<QComplex.normSq w := by grind only
  have hb := RationalReciprocal.coordinateBound_inverse w R.val (R.val*R.val)
    (Rat.le_of_lt R.property) hR2 hnorm (rational_coordinate_bound w R.val hs.1)
  have he : R.val/(R.val*R.val)=1/R.val := by
    simp only [Rat.div_def,Rat.inv_mul_rev]
    have hi := Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
    grind only
  rw [he] at hb
  exact Small.congr (ofQComplex_valid _) (inverse _ hn).property
    (equiv_symm (rational_inverse_agreement w hn (Rat.ne_of_gt hp))) ((rational_small _).mono hb)

theorem rationalCenteredBoundary_pole_inverse_bound (c q : QComplex) (R : QPos) (b : Scalar)
    (hb : Small (Centered.offset (rationalRectangleScalar c) b).val (R.val/64))
    (hq : rationalRectangleBoundaryContains (rationalCenteredRectangle c R.val) q)
    (hz : (ribbonPoleReciprocal b).domain (rationalRectangleScalar q)) :
    Small ((ribbonPoleReciprocal b).eval (rationalRectangleScalar q) hz).val (8/R.val) := by
  let w := rationalRectangleScalar (QComplex.sub q c)
  let z := (ribbonPoleOffset b).eval (rationalRectangleScalar q) trivial
  have hn := rationalCenteredBoundary_offset_nonzero c q R hq
  have he : gridScalarSub z w≈scalarNeg (Centered.offset (rationalRectangleScalar c) b) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (gridScalarSub z w).property)
      (hright := (scalarNeg (Centered.offset (rationalRectangleScalar c) b)).property)
    change (-gridScalarValue b+1*gridScalarValue (rationalRectangleScalar q))-
      (gridScalarValue (rationalRectangleScalar q)-gridScalarValue (rationalRectangleScalar c))=
      -(gridScalarValue b-gridScalarValue (rationalRectangleScalar c))
    grind only
  have hd := Small.congr (neg_valid (Centered.offset (rationalRectangleScalar c) b).property)
    (sub_valid z.property w.property) (equiv_symm he) (SeriesLimitLaws.small_neg hb)
  have hB : 0≤1/R.val := by rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr R.property)
  have hH : 0≤R.val/64 := by rw [Rat.div_def]; exact Rat.mul_nonneg (Rat.le_of_lt R.property) (by decide +kernel)
  have hbudget : 16*(1/R.val)*(R.val/64)≤1 := by
    simp only [Rat.div_def,Rat.one_mul]
    have hi := Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
    grind only
  obtain ⟨hnz,hbound⟩ := inverse_near_exists_bound w z hn (1/R.val) (R.val/64) hB hH
    (rationalCenteredBoundary_literal_inverse_bound c q R hq hn) hd hbudget
  have heB : 8*(1/R.val)=8/R.val := by simp only [Rat.div_def,Rat.one_mul]
  rw [heB] at hbound
  exact hbound

def centeredBoundaryReciprocalBound (R : QPos) : QPos :=
  ⟨8/R.val,by rw [Rat.div_def]; exact Rat.mul_pos (by decide +kernel) (Rat.inv_pos.mpr R.property)⟩

theorem rationalCenteredBoundary_pole_value_bound (c : QComplex) (R : QPos) (b : Scalar)
    (hb : Small (Centered.offset (rationalRectangleScalar c) b).val (R.val/64))
    (hd : RectangleBoundaryDomains (ribbonPoleReciprocal b) (rationalCenteredRectangle c R.val)) :
    RectangleBoundaryValueBound (ribbonPoleReciprocal b) (rationalCenteredRectangle c R.val) hd
      (centeredBoundaryReciprocalBound R) :=
  rectangleBoundaryValueBound_of_rational _ (ribbonPoleReciprocal_holomorphic b).continuous _
    (rationalCenteredRectangle_ordered c R).1 (rationalCenteredRectangle_ordered c R).2 hd
    (centeredBoundaryReciprocalBound R) (rationalCenteredBoundary_pole_inverse_bound c · R b hb)

end ComputableAnalysis.RiemannHilbert.RectangularContour
