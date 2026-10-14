import ComputableAnalysis.ModularForms.PairedRiccatiSquareDensityAgreement

/-! Holomorphic edge pullbacks with represented parameter inputs. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions PDE.CauchyContour

def pairedSquareEdgeParameterMap (edge : HalfEdge) (R : Rat) : DomainFunctions.Map :=
  affine ⟨ofQComplex (QComplex.scaleRat R (point edge 0)),ofQComplex_valid _⟩
    ⟨ofQComplex (QComplex.scaleRat R (velocity edge)),ofQComplex_valid _⟩

def pairedSquareEdgeParameterMap_holomorphic (edge : HalfEdge) (R : Rat) :
    Holomorphic (pairedSquareEdgeParameterMap edge R) :=
  affine_holomorphic _ _

def pairedRiccatiEdgePullbackMap (a : Scalar) (edge : HalfEdge) (R : Rat) : DomainFunctions.Map :=
  compose (pairedRiccatiCauchyIntegrandMap a) (pairedSquareEdgeParameterMap edge R)

noncomputable def pairedRiccatiEdgePullbackMap_holomorphic (a : Scalar) (edge : HalfEdge) (R : Rat) :
    Holomorphic (pairedRiccatiEdgePullbackMap a edge R) :=
  (pairedRiccatiCauchyIntegrandMap_holomorphic a).compose
    (pairedSquareEdgeParameterMap_holomorphic edge R)

theorem pairedSquareEdgeParameterMap_rational_eval (edge : HalfEdge) (u R : Rat) :
    ((pairedSquareEdgeParameterMap edge R).eval
      ⟨ofQComplex ⟨u,0⟩,ofQComplex_valid _⟩ trivial).val.Equiv
      (pairedSquareOffset edge u R).val := by
  let c := QComplex.scaleRat R (point edge 0)
  let v := QComplex.scaleRat R (velocity edge)
  have hm := RationalReciprocal.raw_mul_constants v ⟨u,0⟩
  have ha : (add (ofQComplex c) (ofQComplex (QComplex.mul v ⟨u,0⟩))).Equiv
      (ofQComplex (QComplex.add c (QComplex.mul v ⟨u,0⟩))) := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩
  have h := equiv_trans
    (add_valid (ofQComplex_valid _) (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)))
    (add_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
    (add_equiv (equiv_refl _ (ofQComplex_valid _)) hm) ha
  have he : QComplex.add c (QComplex.mul v ⟨u,0⟩)=QComplex.scaleRat R (point edge u) := by
    cases edge with
    | mk quarter upper =>
      cases quarter <;> cases upper <;>
        simp only [c,v,point,velocity,rotation,orientation,QComplex.add,QComplex.mul,
          QComplex.scaleRat,QComplex.mk.injEq] <;> constructor <;> grind
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
