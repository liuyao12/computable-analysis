import ComputableAnalysis.ModularForms.SquareFrameWeightedSides
import ComputableAnalysis.ModularForms.DyadicSampleReversal

/-! Lower-half orientation expressed through the common Cartesian density. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem squareHalfEdge_reflected_point (quarter : Quarter) (S u : Rat) :
    cartesianSquarePoint ⟨quarter,false⟩ S u=cartesianSquarePoint ⟨quarter,true⟩ S (-u) := by
  cases quarter <;> simp only [cartesianSquarePoint,orientation,Bool.false_eq_true,
    ↓reduceIte,QComplex.mk.injEq] <;> constructor <;> grind only

theorem squareHalfEdge_reflected_velocity (quarter : Quarter) (S : Rat) :
    QComplex.scaleRat S (velocity ⟨quarter,false⟩)=
      QComplex.scaleRat (-1) (QComplex.scaleRat S (velocity ⟨quarter,true⟩)) := by
  cases quarter <;> simp only [velocity,orientation,rotation,Bool.false_eq_true,
    ↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq] <;>
    constructor <;> grind only

theorem squareHalfEdge_reflected_density (c : Scalar) (quarter : Quarter) (S u : Rat) :
    (cartesianSquareKernelDensity c ⟨quarter,false⟩ S u).val.Equiv
      (cartesianSquareKernelDensity c ⟨quarter,true⟩ S (-u)).val := by
  let z := rationalRiccatiKernelSample c (cartesianSquarePoint ⟨quarter,true⟩ S (-u))
  let q := QComplex.scaleRat S (velocity ⟨quarter,true⟩)
  have hb := rationalWeightedSample_scale z q (-1)
  have hn := neg_equiv hb
  have hs : (neg (scaleRat (-1) (scalarProduct z (rationalRectangleScalar q)).val)).Equiv
      (scalarProduct z (rationalRectangleScalar q)).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (scaleRat_valid (scalarProduct z (rationalRectangleScalar q)).property))
      (hright := (scalarProduct z (rationalRectangleScalar q)).property)
    rw [ComplexRawQuotient.ofRaw_neg,ComplexRawQuotient.ofRaw_scaleRat]
    have he := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := neg_valid (scalarProduct z (rationalRectangleScalar q)).property)
      (hright := scaleRat_valid (scalarProduct z (rationalRectangleScalar q)).property)
      (neg_equiv_scaleRat_neg_one _ (scalarProduct z (rationalRectangleScalar q)).property)
    rw [ComplexRawQuotient.ofRaw_neg,ComplexRawQuotient.ofRaw_scaleRat] at he
    rw [←he]
    grind only
    all_goals first
      | exact (scalarProduct z (rationalRectangleScalar q)).property
      | exact scaleRat_valid (scalarProduct z (rationalRectangleScalar q)).property
  have h := equiv_trans
    (neg_valid (scalarProduct z (rationalRectangleScalar (QComplex.scaleRat (-1) q))).property)
    (neg_valid (scaleRat_valid (scalarProduct z (rationalRectangleScalar q)).property))
    (scalarProduct z (rationalRectangleScalar q)).property hn hs
  simp only [cartesianSquareKernelDensity,Bool.false_eq_true,↓reduceIte,
    squareHalfEdge_reflected_point,squareHalfEdge_reflected_velocity]
  exact h

theorem pairedSquareDensitySample_lower_reflection (c : Scalar) (quarter : Quarter) (S u : Rat) :
    (pairedSquareDensitySample c ⟨quarter,false⟩ S u).val.Equiv
      (pairedSquareDensitySample c ⟨quarter,true⟩ S (-u)).val := by
  have h := squareHalfEdge_reflected_density c quarter S u
  rw [cartesianSquareKernelDensity_agreement,cartesianSquareKernelDensity_agreement] at h
  exact h

theorem pairedSquareDensitySample_lower_sum_reflection (c : Scalar) (quarter : Quarter)
    (S : Rat) (parameters : Nat → Rat) (M : Nat) :
    (gridScalarSum M (fun j => pairedSquareDensitySample c ⟨quarter,false⟩ S (parameters j))).val.Equiv
      (gridScalarSum M (fun j => pairedSquareDensitySample c ⟨quarter,true⟩ S (-(parameters j)))).val :=
  gridScalarSum_congr M _ _ (fun j => pairedSquareDensitySample_lower_reflection c quarter S (parameters j))

end ComputableAnalysis.ModularForms

