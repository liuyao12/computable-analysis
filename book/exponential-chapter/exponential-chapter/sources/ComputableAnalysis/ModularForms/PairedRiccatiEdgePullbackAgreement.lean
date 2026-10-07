import ComputableAnalysis.ModularForms.PairedRiccatiEdgePullback

/-! Justified rational edge membership and exact pullback evaluator agreement. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions PDE.CauchyContour

theorem pairedRiccatiEdgePullbackMap_rational_mem (a : Scalar) (edge : HalfEdge)
    (u R : Rat) (hR : 0<R) :
    (pairedRiccatiEdgePullbackMap a edge R).domain ⟨ofQComplex ⟨u,0⟩,ofQComplex_valid _⟩ := by
  refine ⟨trivial,?_⟩
  apply (NonzeroBoxSearch.nonzero_congr _ _ (pairedSquareEdgeParameterMap_rational_eval edge u R)).mpr
  exact pairedSquareOffset_nonzero edge u R hR

theorem pairedRiccatiEdgePullbackMap_rational_agreement (a : Scalar) (edge : HalfEdge)
    (u R : Rat) (hR : 0<R) :
    ((pairedRiccatiEdgePullbackMap a edge R).eval ⟨ofQComplex ⟨u,0⟩,ofQComplex_valid _⟩
      (pairedRiccatiEdgePullbackMap_rational_mem a edge u R hR)).val.Equiv
      ((pairedRiccatiCauchyIntegrandMap a).eval (pairedSquareOffset edge u R)
        (pairedSquareOffset_nonzero edge u R hR)).val :=
  (pairedRiccatiCauchyIntegrandMap a).eval_congr _ _ _ _
    (pairedSquareEdgeParameterMap_rational_eval edge u R)

end ComputableAnalysis.ModularForms
