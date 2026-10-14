import ComputableAnalysis.ModularForms.PairedRiccatiFullSquareSums

/-! Representation invariance of actual square-contour approximants. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions PDE.CauchyContour

theorem pairedSquareDensity_congr (a b : Scalar) (he : a.val.Equiv b.val)
    (edge : HalfEdge) (u R : Rat) :
    (pairedSquareDensity a edge u R).Equiv (pairedSquareDensity b edge u R) := by
  let q := QComplex.scaleRat R (point edge u)
  let za : Scalar := ⟨add a.val (ofQComplex q),add_valid a.property (ofQComplex_valid _)⟩
  let zb : Scalar := ⟨add b.val (ofQComplex q),add_valid b.property (ofQComplex_valid _)⟩
  have hz : za.val.Equiv zb.val := add_equiv he (equiv_refl _ (ofQComplex_valid _))
  have hv := pairedEntireRiccatiMap.eval_congr za zb trivial trivial hz
  have hk := equiv_refl (mul (ofQComplex (RationalReciprocal.inverse q))
    (ofQComplex (RationalReciprocal.inverse q))) (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))
  have hp := mul_equiv (pairedEntireRiccatiMap.eval za trivial).property
    (pairedEntireRiccatiMap.eval zb trivial).property
    (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))
    (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) hv hk
  have hd := mul_equiv
    (mul_valid (pairedEntireRiccatiMap.eval za trivial).property (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)))
    (mul_valid (pairedEntireRiccatiMap.eval zb trivial).property (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)))
    (ofQComplex_valid _) (ofQComplex_valid _) hp
    (equiv_refl (ofQComplex (QComplex.scaleRat R (velocity edge))) (ofQComplex_valid _))
  dsimp only [pairedSquareDensity]
  split
  · exact hd
  · exact neg_equiv hd

theorem pairedSquareHalfEdgeSum_congr (a b : Scalar) (he : a.val.Equiv b.val)
    (edge : HalfEdge) (R : Rat) (N : Nat) :
    (pairedSquareHalfEdgeSum a edge R N).Equiv (pairedSquareHalfEdgeSum b edge R N) :=
  scaleRat_equiv (ScalarSeries.block_congr _ _
    (fun _ => pairedSquareDensity_congr a b he edge _ R) 0 N)

theorem pairedSquareEdgeListSum_congr (a b : Scalar) (he : a.val.Equiv b.val)
    (R : Rat) (N : Nat) (es : List HalfEdge) :
    (pairedSquareEdgeListSum a R N es).Equiv (pairedSquareEdgeListSum b R N es) := by
  induction es with
  | nil => exact equiv_refl _ (ofQComplex_valid _)
  | cons e es ih => exact add_equiv (pairedSquareHalfEdgeSum_congr a b he e R N) ih

theorem pairedSquareContourSum_congr (a b : Scalar) (he : a.val.Equiv b.val)
    (R : Rat) (N : Nat) :
    (pairedSquareContourSum a R N).Equiv (pairedSquareContourSum b R N) :=
  pairedSquareEdgeListSum_congr a b he R N square

end ComputableAnalysis.ModularForms
