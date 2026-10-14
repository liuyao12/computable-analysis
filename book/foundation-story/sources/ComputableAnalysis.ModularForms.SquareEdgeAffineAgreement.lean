import ComputableAnalysis.ModularForms.PairedRiccatiEdgePullback
import ComputableAnalysis.ModularForms.PairedRiccatiDyadicKernelOscillation

/-! The actual translated square edge is an affine segment. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

def squareEdgeOrigin (a : Scalar) (edge : HalfEdge) (R : Rat) : Scalar :=
  ⟨add a.val (ofQComplex (QComplex.scaleRat R (point edge 0))),
    add_valid a.property (ofQComplex_valid _)⟩

def squareEdgeEnd (a : Scalar) (edge : HalfEdge) (R : Rat) : Scalar :=
  let p := squareEdgeOrigin a edge R
  ⟨add p.val (ofQComplex (QComplex.scaleRat R (velocity edge))),
    add_valid p.property (ofQComplex_valid _)⟩

theorem squareEdge_displacement (a : Scalar) (edge : HalfEdge) (R : Rat) :
    (AffineSegment.displacement (squareEdgeOrigin a edge R) (squareEdgeEnd a edge R)).val.Equiv
      (ofQComplex (QComplex.scaleRat R (velocity edge))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (AffineSegment.displacement (squareEdgeOrigin a edge R)
      (squareEdgeEnd a edge R)).property) (hright := ofQComplex_valid _)
  let P := ComplexRawQuotient.ofRaw (squareEdgeOrigin a edge R).val
    (squareEdgeOrigin a edge R).property
  let V := ComplexRawQuotient.ofRaw (ofQComplex (QComplex.scaleRat R (velocity edge)))
    (ofQComplex_valid _)
  change (P+V)-P=V
  grind only

theorem squareEdge_affine_agreement (a : Scalar) (edge : HalfEdge) (R u : Rat)
    (hu : 0≤u) :
    (AffineSegment.point (squareEdgeOrigin a edge R) (squareEdgeEnd a edge R) u).val.Equiv
      (add a.val (ofQComplex (QComplex.scaleRat R (point edge u)))) := by
  let v := QComplex.scaleRat R (velocity edge)
  have hs := ComplexRaw.scaleRat_equiv_of_nonneg hu (squareEdge_displacement a edge R)
  have hc : (scaleRat u (ofQComplex v)).Equiv (ofQComplex (QComplex.scaleRat u v)) := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    simp [scaleRat,ofQComplex,QBox.scaleRat,hu,QBox.Overlaps,QComplex.le_def,QComplex.scaleRat]
  have hm : (mul (ofQComplex v) (ofQComplex ⟨u,0⟩)).Equiv
      (ofQComplex (QComplex.scaleRat u v)) := by
    have h := RationalReciprocal.raw_mul_constants v ⟨u,0⟩
    have he : QComplex.mul v ⟨u,0⟩=QComplex.scaleRat u v := by
      cases v
      simp [QComplex.mul,QComplex.scaleRat]
      constructor <;> grind only
    rw [he] at h
    exact h
  have hv := equiv_trans (scaleRat_valid (ofQComplex_valid _))
    (ofQComplex_valid _) (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) hc (equiv_symm hm)
  have hp := add_equiv (equiv_refl _ (squareEdgeOrigin a edge R).property)
    (equiv_trans (scaleRat_valid (AffineSegment.displacement
      (squareEdgeOrigin a edge R) (squareEdgeEnd a edge R)).property)
      (scaleRat_valid (ofQComplex_valid _))
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) hs hv)
  have hx := add_equiv (equiv_refl _ a.property)
    (pairedSquareEdgeParameterMap_rational_eval edge u R)
  have hassoc : (add (squareEdgeOrigin a edge R).val
      (mul (ofQComplex v) (ofQComplex ⟨u,0⟩))).Equiv
      (add a.val ((pairedSquareEdgeParameterMap edge R).eval
        ⟨ofQComplex ⟨u,0⟩,ofQComplex_valid _⟩ trivial).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (squareEdgeOrigin a edge R).property
        (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)))
      (hright := add_valid a.property ((pairedSquareEdgeParameterMap edge R).eval
        ⟨ofQComplex ⟨u,0⟩,ofQComplex_valid _⟩ trivial).property)
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let C := ComplexRawQuotient.ofRaw (ofQComplex (QComplex.scaleRat R (point edge 0))) (ofQComplex_valid _)
    let V := ComplexRawQuotient.ofRaw (ofQComplex v) (ofQComplex_valid _)
    let U := ComplexRawQuotient.ofRaw (ofQComplex ⟨u,0⟩) (ofQComplex_valid _)
    change (A+C)+V*U=A+(C+V*U)
    grind only
  exact equiv_trans
    (AffineSegment.point (squareEdgeOrigin a edge R) (squareEdgeEnd a edge R) u).property
    (add_valid (squareEdgeOrigin a edge R).property (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)))
    (add_valid a.property (ofQComplex_valid _)) hp
    (equiv_trans
      (add_valid (squareEdgeOrigin a edge R).property (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)))
      (add_valid a.property ((pairedSquareEdgeParameterMap edge R).eval
        ⟨ofQComplex ⟨u,0⟩,ofQComplex_valid _⟩ trivial).property)
      (add_valid a.property (ofQComplex_valid _)) hassoc hx)

end ComputableAnalysis.ModularForms
