import ComputableAnalysis.RiemannHilbert.ContourRationalSums

/-! The actual reciprocal boundary agrees with the literal rational period
quadrature. Dilation cancels in every oriented half-edge sample. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions PDE.CauchyContour
set_option autoImplicit false

def literalSquareProduct (R : QPos) (e : HalfEdge) (u : Rat) : QComplex :=
  QComplex.mul (QComplex.inverse (QComplex.scaleRat R.val (point e u)))
    (QComplex.scaleRat R.val (velocity e))

theorem literalSquareProduct_oriented (R : QPos) (e : HalfEdge) (u : Rat) :
    QComplex.scaleRat (orientation e) (literalSquareProduct R e u)=pullback e u := by
  have hs := scaledPullback_eq QComplex.zero R.val (Rat.ne_of_gt R.property) e u
  have hq : QComplex.sub (QComplex.add QComplex.zero (QComplex.scaleRat R.val (point e u)))
      QComplex.zero=QComplex.scaleRat R.val (point e u) := by
    rw [QComplex.zero_add_cert]
    simp only [QComplex.sub,QComplex.add,QComplex.neg,QComplex.zero,QComplex.scaleRat,
      QComplex.mk.injEq]
    constructor <;> grind only
  simp only [scaledPullback,hq] at hs
  exact hs

theorem literalSquareAverage_agreement (R : QPos) (e : HalfEdge) (M : Nat) :
    (commonSquareKernelAverage literalReciprocalSample e R M).val.Equiv
      (ofQComplex (QComplex.scaleRat (1/(M:Rat))
        (rationalGridSum M (fun j => literalSquareProduct R e (squareMidpointParameter M j))))) := by
  let terms := fun j => scalarProduct
    (literalReciprocalSample (QComplex.scaleRat R.val (point e (squareMidpointParameter M j))))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity e)))
  let rationalTerms := fun j => literalSquareProduct R e (squareMidpointParameter M j)
  have he (j : Nat) : (terms j).val.Equiv (ofQComplex (rationalTerms j)) :=
    RationalReciprocal.raw_mul_constants _ _
  have hs := gridScalarSum_congr M terms (fun j => rationalRectangleScalar (rationalTerms j)) he
  have ht := gridScalarSum_rational M rationalTerms
  have hu := scaleRat_equiv (r := 1/(M:Rat))
    (equiv_trans (gridScalarSum M terms).property
      (gridScalarSum M (fun j => rationalRectangleScalar (rationalTerms j))).property
      (ofQComplex_valid _) hs ht)
  have hscale := rationalRectangleScalar_scale (rationalGridSum M rationalTerms) (1/(M:Rat))
  change ofQComplex _ = scaleRat _ (ofQComplex _) at hscale
  rw [←hscale] at hu
  exact hu

theorem literalSquareOrientedAverage (R : QPos) (e : HalfEdge) (M : Nat) :
    (if e.upper then commonSquareKernelAverage literalReciprocalSample e R M
      else scalarNeg (commonSquareKernelAverage literalReciprocalSample e R M)).val.Equiv
      (ofQComplex (rationalGridSum M (fun j => QComplex.scaleRat (1/(M:Rat))
        (pullback e (squareMidpointParameter M j))))) := by
  have ho : (fun j => pullback e (squareMidpointParameter M j))=
      (fun j => QComplex.scaleRat (orientation e)
        (literalSquareProduct R e (squareMidpointParameter M j))) := by
    funext j
    exact (literalSquareProduct_oriented R e _).symm
  rw [rationalGridSum_scale,ho,rationalGridSum_scale]
  have ha := literalSquareAverage_agreement R e M
  cases hb : e.upper
  · simp only [hb,Bool.false_eq_true,↓reduceIte,orientation]
    have hn := neg_equiv ha
    rw [rational_constant_neg] at hn
    have hq (q : QComplex) : QComplex.neg (QComplex.scaleRat (1/(M:Rat)) q)=
        QComplex.scaleRat (1/(M:Rat)) (QComplex.scaleRat (-1) q) := by
      simp only [QComplex.neg,QComplex.scaleRat,QComplex.mk.injEq]
      constructor <;> grind only
    rw [hq] at hn
    exact hn
  · simp only [hb,↓reduceIte,orientation,QComplex.scaleRat,Rat.one_mul]
    exact ha

theorem literalSquareEdgeList_agreement (R : QPos) (M : Nat) (es : List HalfEdge) :
    (commonSquareKernelEdgeList literalReciprocalSample R M es).val.Equiv
      (ofQComplex (rationalGridSum M (fun j => QComplex.scaleRat (1/(M:Rat))
        (rationalSquareDensity es (squareMidpointParameter M j))))) := by
  induction es with
  | nil =>
    have hz : rationalGridSum M (fun _ => QComplex.zero)=QComplex.zero := by
      induction M with
      | zero => rfl
      | succ M ih => simp only [rationalGridSum,ih,QComplex.add_zero_cert]
    simp only [rationalSquareDensity,List.map_nil,List.foldr_nil]
    have hs : QComplex.scaleRat (1/(M:Rat)) QComplex.zero=QComplex.zero := by
      simp only [QComplex.scaleRat,QComplex.zero,Rat.mul_zero]
    simp only [hs,hz]
    exact equiv_refl _ (ofQComplex_valid _)
  | cons e es ih =>
    have ha := literalSquareOrientedAverage R e M
    have hs := add_equiv ha ih
    have hq : rationalGridSum M (fun j => QComplex.scaleRat (1/(M:Rat))
        (rationalSquareDensity (e::es) (squareMidpointParameter M j)))=
      QComplex.add
        (rationalGridSum M (fun j => QComplex.scaleRat (1/(M:Rat)) (pullback e (squareMidpointParameter M j))))
        (rationalGridSum M (fun j => QComplex.scaleRat (1/(M:Rat)) (rationalSquareDensity es (squareMidpointParameter M j)))) := by
      simp only [rationalSquareDensity,List.map_cons,List.foldr_cons]
      rw [rationalGridSum_scale,rationalGridSum_add]
      simp only [rationalGridSum_scale]
      simp only [QComplex.scaleRat,QComplex.add,QComplex.mk.injEq]
      constructor <;> grind only
    rw [hq]
    exact hs

theorem reciprocalInnerPrefix_rational (R : QPos) (M : Nat) (hM : 0<M) :
    innerBoundary (reciprocalFrameSample R) R M ≈
      rationalRectangleScalar (rationalGridSum M (fun j =>
        QComplex.scaleRat (1/(M:Rat)) (density (squareMidpointParameter M j)))) := by
  exact Setoid.trans (innerBoundary_congr_on_frame _ _ R M hM (literalReciprocalSample_value R))
    (Setoid.trans (commonInnerSquareContour_agreement literalReciprocalSample R M hM)
      (literalSquareEdgeList_agreement R M square))

end ComputableAnalysis.RiemannHilbert.RectangularContour
