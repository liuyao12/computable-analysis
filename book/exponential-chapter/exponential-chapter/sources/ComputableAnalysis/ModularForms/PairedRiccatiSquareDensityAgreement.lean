import ComputableAnalysis.ModularForms.PairedRiccatiCauchyIntegrandAgreement

/-! The finite square densities are pullbacks of the justified holomorphic integrand. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions PDE.CauchyContour

def pairedSquareOffset (edge : HalfEdge) (u R : Rat) : Scalar :=
  ⟨ofQComplex (QComplex.scaleRat R (point edge u)),ofQComplex_valid _⟩

theorem pairedSquareOffset_nonzero (edge : HalfEdge) (u R : Rat) (hR : 0<R) :
    NonzeroBoxSearch.Nonzero (pairedSquareOffset edge u R) :=
  rationalConstant_nonzero _ (scaledSquarePoint_normSq_nonzero edge u R hR)

def pairedSquareAnalyticDensity (a : Scalar) (edge : HalfEdge) (u R : Rat) (hR : 0<R) : Scalar :=
  let z := pairedSquareOffset edge u R
  let f := (pairedRiccatiCauchyIntegrandMap a).eval z (pairedSquareOffset_nonzero edge u R hR)
  let v : Scalar := ⟨ofQComplex (QComplex.scaleRat R (velocity edge)),ofQComplex_valid _⟩
  let d := scalarProduct f v
  if edge.upper then d else ⟨neg d.val,neg_valid d.property⟩

theorem pairedSquareAnalyticDensity_agreement (a : Scalar) (edge : HalfEdge)
    (u R : Rat) (hR : 0<R) :
    (pairedSquareAnalyticDensity a edge u R hR).val.Equiv (pairedSquareDensity a edge u R) := by
  have hi := pairedRiccatiCauchyIntegrandMap_rational_agreement a
    (QComplex.scaleRat R (point edge u)) (scaledSquarePoint_normSq_nonzero edge u R hR)
    (pairedSquareOffset_nonzero edge u R hR)
  have hd := mul_equiv
    ((pairedRiccatiCauchyIntegrandMap a).eval (pairedSquareOffset edge u R)
      (pairedSquareOffset_nonzero edge u R hR)).property
    (mul_valid (pairedEntireRiccatiMap.eval
      ⟨add a.val (ofQComplex (QComplex.scaleRat R (point edge u))),add_valid a.property (ofQComplex_valid _)⟩ trivial).property
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)))
    (ofQComplex_valid _) (ofQComplex_valid _) hi
    (equiv_refl (ofQComplex (QComplex.scaleRat R (velocity edge))) (ofQComplex_valid _))
  dsimp only [pairedSquareAnalyticDensity,pairedSquareDensity,scalarProduct]
  split
  · exact hd
  · exact neg_equiv hd

end ComputableAnalysis.ModularForms
