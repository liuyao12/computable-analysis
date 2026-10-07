import ComputableAnalysis.ModularForms.SquareEdgeAffineAgreement

/-! Arbitrary-error cell oscillation for the actual square-edge kernel product. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

def actualSquareKernelSample (a : Scalar) (edge : HalfEdge) (R u : Rat) : Scalar :=
  let z : Scalar := ⟨add a.val (ofQComplex (QComplex.scaleRat R (point edge u))),
    add_valid a.property (ofQComplex_valid _)⟩
  let f := pairedEntireRiccatiMap.eval z trivial
  let k := rationalSquaredKernel (QComplex.scaleRat R (point edge u))
  ⟨mul f.val k.val, mul_valid f.property k.property⟩

theorem squareKernelSample_affine_agreement (a : Scalar) (edge : HalfEdge) (R u : Rat)
    (hu : 0≤u) :
    (riccatiSquareKernelSample (squareEdgeOrigin a edge R) (squareEdgeEnd a edge R)
      edge R u).val.Equiv (actualSquareKernelSample a edge R u).val := by
  apply mul_equiv
    (pairedEntireRiccatiMap.eval (AffineSegment.point (squareEdgeOrigin a edge R)
      (squareEdgeEnd a edge R) u) trivial).property
    (pairedEntireRiccatiMap.eval
      ⟨add a.val (ofQComplex (QComplex.scaleRat R (point edge u))),
        add_valid a.property (ofQComplex_valid _)⟩ trivial).property
    (rationalSquaredKernel _).property (rationalSquaredKernel _).property
  · exact pairedEntireRiccatiMap.eval_congr _ _ trivial trivial
      (squareEdge_affine_agreement a edge R u hu)
  · exact equiv_refl _ (rationalSquaredKernel _).property

theorem actualSquareKernel_dyadic_oscillation (a : Scalar) (edge : HalfEdge)
    (R : Rat) (hR : 0<R) (eps : QPos) :
    ∃ N, ∀ choice : Nat → Bool, ∀ n, N≤n → ∀ u v : Rat,
      (bisectionInterval ⟨0,1⟩ choice n).lo≤u →
      u≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      (bisectionInterval ⟨0,1⟩ choice n).lo≤v →
      v≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      Small (sub (actualSquareKernelSample a edge R u).val
        (actualSquareKernelSample a edge R v).val) eps.val := by
  let W : QPos := ⟨R,hR⟩
  have hv := (BoxApproximation.rational_small _).mono
    (scaledSquareVelocity_coordinate_bound edge R (Rat.le_of_lt hR))
  have hd := Small.congr (ofQComplex_valid _)
    (AffineSegment.displacement (squareEdgeOrigin a edge R) (squareEdgeEnd a edge R)).property
    (equiv_symm (squareEdge_displacement a edge R)) hv
  obtain ⟨N,hN⟩ := pairedRiccati_dyadic_kernel_oscillation
    (squareEdgeOrigin a edge R) (squareEdgeEnd a edge R) W hd edge R hR eps
  refine ⟨N, ?_⟩
  intro choice n hn u v hulo huhi hvlo hvhi
  have he := bisectionInterval_nested (⟨0,1⟩ : QInterval)
    (by decide +kernel) choice 0 n (Nat.zero_le n)
  have hu := squareKernelSample_affine_agreement a edge R u (Rat.le_trans he.1 hulo)
  have hv := squareKernelSample_affine_agreement a edge R v (Rat.le_trans he.1 hvlo)
  exact Small.congr
    (sub_valid (riccatiSquareKernelSample (squareEdgeOrigin a edge R)
      (squareEdgeEnd a edge R) edge R u).property
      (riccatiSquareKernelSample (squareEdgeOrigin a edge R)
        (squareEdgeEnd a edge R) edge R v).property)
    (sub_valid (actualSquareKernelSample a edge R u).property
      (actualSquareKernelSample a edge R v).property)
    (FunctionTheory.sub_congr hu hv) (hN choice n hn u v hulo huhi hvlo hvhi)

end ComputableAnalysis.ModularForms
