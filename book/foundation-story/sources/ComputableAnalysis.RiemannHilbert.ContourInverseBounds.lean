import ComputableAnalysis.RiemannHilbert.ContourCauchyKernel

/-! Rational separation on the entire frame supplies a uniform bound for
actual represented reciprocal samples, without deciding represented equality. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions BoxApproximation
set_option autoImplicit false

theorem rational_coordinate_bound (q : QComplex) (B : Rat) (hs : Small (ofQComplex q) B) :
    coordinateBound q≤B := by
  have h1 : -B≤q.re := hs.1 0 0
  have h2 : q.re≤B := hs.2.1 0 0
  have h3 : -B≤q.im := hs.2.2.1 0 0
  have h4 : q.im≤B := hs.2.2.2 0 0
  unfold coordinateBound qabs max
  grind

theorem square_lower_of_separated (R : QPos) (x : Rat) (hx : R.val≤x ∨ x≤ -R.val) :
    R.val*R.val≤x*x := by
  have positive (y : Rat) (hy : R.val≤y) : R.val*R.val≤y*y := by
    have hy0 : 0≤y := Rat.le_trans (Rat.le_of_lt R.property) hy
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hy (Rat.le_of_lt R.property))
      (Rat.mul_le_mul_of_nonneg_right hy hy0)
  rcases hx with hx|hx
  · exact positive x hx
  · have h := positive (-x) (by grind only)
    grind only

theorem frame_rational_norm_lower (R : QPos) (q : QComplex)
    (hq : frameDomain R (rationalRectangleScalar q)) : R.val*R.val≤QComplex.normSq q := by
  obtain ⟨j,k,hi,hq⟩ := hq
  have hr : rationalRectangleContains (squareFrameTile R j k) q :=
    ⟨hq.1 0 0,hq.2.1 0 0,hq.2.2.1 0 0,hq.2.2.2 0 0⟩
  have hx0 := rat_square_nonneg_basic q.re
  have hy0 := rat_square_nonneg_basic q.im
  rcases squareFrameTile_separated R j k hi with hs|hs|hs|hs
  · have hl := square_lower_of_separated R q.re (Or.inl (Rat.le_trans hs hr.1))
    unfold QComplex.normSq
    grind only
  · have hl := square_lower_of_separated R q.re (Or.inr (Rat.le_trans hr.2.1 hs))
    unfold QComplex.normSq
    grind only
  · have hl := square_lower_of_separated R q.im (Or.inl (Rat.le_trans hs hr.2.2.1))
    unfold QComplex.normSq
    grind only
  · have hl := square_lower_of_separated R q.im (Or.inr (Rat.le_trans hr.2.2.2 hs))
    unfold QComplex.normSq
    grind only

theorem rational_inverse_agreement (q : QComplex) (hz : NonzeroBoxSearch.Nonzero (rationalRectangleScalar q))
    (hn : QComplex.normSq q≠0) :
    RepresentedReciprocal.inverse (rationalRectangleScalar q) hz ≈
      rationalRectangleScalar (RationalReciprocal.inverse q) := by
  have hp := RationalReciprocal.raw_mul_constants q (RationalReciprocal.inverse q)
  rw [RationalReciprocal.mul_inverse q hn] at hp
  exact RepresentedReciprocal.inverse_unique _ hz _ hp

theorem frame_rational_inverse_bound (R : QPos) (q : QComplex)
    (hq : frameDomain R (rationalRectangleScalar q))
    (hz : NonzeroBoxSearch.Nonzero (rationalRectangleScalar q)) :
    Small (RepresentedReciprocal.inverse (rationalRectangleScalar q) hz).val (2/R.val) := by
  have hnorm := frame_rational_norm_lower R q hq
  have hR2 : 0<R.val*R.val := Rat.mul_pos R.property R.property
  have hnpos : 0<QComplex.normSq q := by grind only
  have hn : QComplex.normSq q≠0 := Rat.ne_of_gt hnpos
  have hc := rational_coordinate_bound q (2*R.val) (frameDomain_bound R _ hq)
  have hb := RationalReciprocal.coordinateBound_inverse q (2*R.val) (R.val*R.val)
    (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt R.property)) hR2 hnorm hc
  have he : (2*R.val)/(R.val*R.val)=2/R.val := by
    simp only [Rat.div_def,Rat.inv_mul_rev]
    have hi := Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
    grind only
  rw [he] at hb
  exact Small.congr (ofQComplex_valid _) (RepresentedReciprocal.inverse _ hz).property
    (equiv_symm (rational_inverse_agreement q hz hn)) ((rational_small _).mono hb)

end ComputableAnalysis.RiemannHilbert.RectangularContour
