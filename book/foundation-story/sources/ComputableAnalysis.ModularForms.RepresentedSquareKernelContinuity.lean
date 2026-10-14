import ComputableAnalysis.ModularForms.SquareKernelParameterBound

/-! Rational kernel moduli transferred to the actual represented products. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem rational_coordinateBound_le_normBound (q : QComplex) :
    BoxApproximation.coordinateBound q≤QComplex.normBound q := by
  have hr := qabs_nonneg q.re
  have hi := qabs_nonneg q.im
  unfold BoxApproximation.coordinateBound QComplex.normBound
  grind

theorem rationalRaw_sub_constants (p q : QComplex) :
    (sub (ofQComplex p) (ofQComplex q)).Equiv (ofQComplex (QComplex.sub p q)) := by
  intro k
  apply (compareAt_overlap_iff _ _ k k).mpr
  apply QBox.overlaps_of_common_point (point := QComplex.sub p q)
  · have hn := QBox.neg_contains (A := QBox.point q) ⟨QComplex.le_refl _,QComplex.le_refl _⟩
    exact QBox.add_contains (QComplex.le_refl _) (QComplex.le_refl _) hn.1 hn.2
  · exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩

theorem representedRationalSquare_difference_bound (p q : QComplex) (B : Rat)
    (hb : QComplex.normBound (QComplex.sub (QComplex.mul p p) (QComplex.mul q q))≤B) :
    Small (sub (mul (ofQComplex p) (ofQComplex p))
      (mul (ofQComplex q) (ofQComplex q))) B := by
  have he := equiv_trans
    (sub_valid (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)))
    (sub_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
    (FunctionTheory.sub_congr (RationalReciprocal.raw_mul_constants p p)
      (RationalReciprocal.raw_mul_constants q q))
    (rationalRaw_sub_constants (QComplex.mul p p) (QComplex.mul q q))
  have hs := (BoxApproximation.rational_small _).mono
    (Rat.le_trans (rational_coordinateBound_le_normBound _) hb)
  exact Small.congr (ofQComplex_valid _)
    (sub_valid (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))) (equiv_symm he) hs

theorem representedSquareKernel_parameter_bound (edge : PDE.CauchyContour.HalfEdge)
    (u v R : Rat) (hu : 0≤u) (hu1 : u≤1) (hv : 0≤v) (hv1 : v≤1) (hR : 0<R) :
    let p := RationalReciprocal.inverse (QComplex.scaleRat R (PDE.CauchyContour.point edge u))
    let q := RationalReciprocal.inverse (QComplex.scaleRat R (PDE.CauchyContour.point edge v))
    Small (sub (mul (ofQComplex p) (ofQComplex p))
      (mul (ofQComplex q) (ofQComplex q)))
      ((2*((2*R)*(R*R)⁻¹)^3*R)*qabs (u-v)) := by
  apply representedRationalSquare_difference_bound
  exact squareSquaredInverse_parameter_bound edge u v R hu hu1 hv hv1 hR

end ComputableAnalysis.ModularForms
