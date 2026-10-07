import ComputableAnalysis.ModularForms.PairedRiccatiSquareSums

/-! Valid represented full-square midpoint sums and their large-radius bounds. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions PDE.CauchyContour

theorem pairedSquareDensity_valid (a : Scalar) (edge : HalfEdge) (u R : Rat) :
    (pairedSquareDensity a edge u R).Valid := by
  dsimp only [pairedSquareDensity]
  split
  · exact mul_valid (mul_valid (pairedEntireRiccatiMap.eval _ trivial).property
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))) (ofQComplex_valid _)
  · exact neg_valid (mul_valid (mul_valid (pairedEntireRiccatiMap.eval _ trivial).property
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))) (ofQComplex_valid _))

theorem pairedSquareHalfEdgeSum_valid (a : Scalar) (edge : HalfEdge) (R : Rat) (N : Nat) :
    (pairedSquareHalfEdgeSum a edge R N).Valid :=
  scaleRat_valid (ScalarSeries.block_valid _ (fun _ => pairedSquareDensity_valid a edge _ R) 0 N)

def pairedSquareEdgeListSum (a : Scalar) (R : Rat) (N : Nat) : List HalfEdge → ComplexRaw
  | [] => zero
  | e::es => add (pairedSquareHalfEdgeSum a e R N) (pairedSquareEdgeListSum a R N es)

theorem pairedSquareEdgeListSum_valid (a : Scalar) (R : Rat) (N : Nat) (es : List HalfEdge) :
    (pairedSquareEdgeListSum a R N es).Valid := by
  induction es with
  | nil => exact ofQComplex_valid _
  | cons e es ih => exact add_valid (pairedSquareHalfEdgeSum_valid a e R N) ih

theorem pairedSquareEdgeListSum_bound (a : Scalar) (R : Rat) (hR : 0<R)
    (N : Nat) (hN : 0<N) (es : List HalfEdge) :
    Small (pairedSquareEdgeListSum a R N es) ((es.length:Rat)*(42958720*(1/R))) := by
  induction es with
  | nil => exact Small.zero (by change (0:Rat)≤0*(42958720*(1/R)); rw [Rat.zero_mul]; decide +kernel)
  | cons e es ih =>
    have hs := LocalODE.small_add (pairedSquareHalfEdgeSum_bound a e R hR N hN) ih
    have he : 42958720*(1/R)+(es.length:Rat)*(42958720*(1/R))=
        ((e::es).length:Rat)*(42958720*(1/R)) := by
      simp only [List.length_cons,Rat.natCast_add]
      change _=(es.length+1:Rat)*(42958720*(1/R))
      grind only
    rw [he] at hs
    exact hs

def pairedSquareContourSum (a : Scalar) (R : Rat) (N : Nat) : ComplexRaw :=
  pairedSquareEdgeListSum a R N square

theorem pairedSquareContourSum_valid (a : Scalar) (R : Rat) (N : Nat) :
    (pairedSquareContourSum a R N).Valid := pairedSquareEdgeListSum_valid a R N square

theorem pairedSquareContourSum_bound (a : Scalar) (R : Rat) (hR : 0<R)
    (N : Nat) (hN : 0<N) :
    Small (pairedSquareContourSum a R N) (343669760*(1/R)) := by
  have hs := pairedSquareEdgeListSum_bound a R hR N hN square
  exact hs.mono (by change (8:Rat)*(42958720*(1/R))≤343669760*(1/R); grind only)

end ComputableAnalysis.ModularForms
