import ComputableAnalysis.ModularForms.RationalMidpointGrid

/-! Full weighted cell agreement, including orientation and side lengths. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def fullRectangleMidpointCycle (f : QComplex → Scalar) (J : QInterval × QInterval) : Scalar :=
  let c := midpointWeightedCycle (f (rectangleRight J)) (f (rectangleLeft J))
    (f (rectangleTop J)) (f (rectangleBottom J))
    (rationalRectangleScalar (rectangleHalfX J)) (rationalRectangleScalar (rectangleHalfY J))
  ⟨scaleRat 2 c.val,scaleRat_valid c.property⟩

theorem gridCell_full_steps (J : QInterval × QInterval) (M j k : Nat) :
    gridScalarValue (rationalRectangleScalar ⟨rectangleGridStepX J M,0⟩)=
      gridScalarValue (rationalRectangleScalar (rectangleHalfX (rectangleGridCell J M j k)))+
      gridScalarValue (rationalRectangleScalar (rectangleHalfX (rectangleGridCell J M j k))) ∧
    gridScalarValue (rationalRectangleScalar ⟨0,rectangleGridStepY J M⟩)=
      gridScalarValue (rationalRectangleScalar (rectangleHalfY (rectangleGridCell J M j k)))+
      gridScalarValue (rationalRectangleScalar (rectangleHalfY (rectangleGridCell J M j k))) := by
  have hw := rectangleGridCell_widths J M j k
  have hx : QComplex.add (rectangleHalfX (rectangleGridCell J M j k))
      (rectangleHalfX (rectangleGridCell J M j k))=⟨rectangleGridStepX J M,0⟩ := by
    simp only [rectangleHalfX,QComplex.add,QComplex.mk.injEq,hw.1]
    grind only
  have hy : QComplex.add (rectangleHalfY (rectangleGridCell J M j k))
      (rectangleHalfY (rectangleGridCell J M j k))=⟨0,rectangleGridStepY J M⟩ := by
    simp only [rectangleHalfY,QComplex.add,QComplex.mk.injEq,hw.2]
    grind only
  have twice (u v : QComplex) (he : QComplex.add u u=v) :
      gridScalarValue (rationalRectangleScalar v)=
        gridScalarValue (rationalRectangleScalar u)+gridScalarValue (rationalRectangleScalar u) := by
    have hs : scalarSum (rationalRectangleScalar u) (rationalRectangleScalar u)=rationalRectangleScalar v := by
      apply Subtype.ext
      change ofQComplex (QComplex.add u u)=ofQComplex v
      rw [he]
    have hb := gridScalarValue_add (rationalRectangleScalar u) (rationalRectangleScalar u)
    rw [hs] at hb
    exact hb
  exact ⟨twice _ _ hx,twice _ _ hy⟩

theorem gridValue_scale_two (z : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 2 z=z+z := by
  have he : (2:Rat)=1+1 := by decide +kernel
  rw [he,←ComplexRawQuotient.add_scaleRat,ComplexRawQuotient.scaleRat_one]

theorem weightedGridCell_midpoint_agreement (f : QComplex → Scalar)
    (J : QInterval × QInterval) (M j k : Nat) :
    (gridScalarCell (rectangleGridHorizontal f J M) (rectangleGridVertical f J M) j k).val.Equiv
      (fullRectangleMidpointCycle f (rectangleGridCell J M j k)).val := by
  have hm := rectangleGridCell_midpoints J M j k
  have hs := gridCell_full_steps J M j k
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarCell (rectangleGridHorizontal f J M) (rectangleGridVertical f J M) j k).property)
    (hright := (fullRectangleMidpointCycle f (rectangleGridCell J M j k)).property)
  let R := gridScalarValue (f (rectangleGridVerticalPoint J M (j+1) k))
  let L := gridScalarValue (f (rectangleGridVerticalPoint J M j k))
  let T := gridScalarValue (f (rectangleGridHorizontalPoint J M j (k+1)))
  let B := gridScalarValue (f (rectangleGridHorizontalPoint J M j k))
  let X := gridScalarValue (rationalRectangleScalar (rectangleHalfX (rectangleGridCell J M j k)))
  let Y := gridScalarValue (rationalRectangleScalar (rectangleHalfY (rectangleGridCell J M j k)))
  let HX := gridScalarValue (rationalRectangleScalar ⟨rectangleGridStepX J M,0⟩)
  let HY := gridScalarValue (rationalRectangleScalar ⟨0,rectangleGridStepY J M⟩)
  have hhx : HX=X+X := hs.1
  have hhy : HY=Y+Y := hs.2
  change _=ComplexRawQuotient.scaleRat 2
    (gridScalarValue (midpointWeightedCycle (f (rectangleRight (rectangleGridCell J M j k)))
      (f (rectangleLeft (rectangleGridCell J M j k)))
      (f (rectangleTop (rectangleGridCell J M j k)))
      (f (rectangleBottom (rectangleGridCell J M j k)))
      (rationalRectangleScalar (rectangleHalfX (rectangleGridCell J M j k)))
      (rationalRectangleScalar (rectangleHalfY (rectangleGridCell J M j k)))))
  rw [hm.1,hm.2.1,hm.2.2.1,hm.2.2.2]
  change (B*HX-T*HX)+(R*HY-L*HY)=ComplexRawQuotient.scaleRat 2
    ((R*Y+L*(-Y))+(T*(-X)+B*X))
  rw [gridValue_scale_two,hhx,hhy]
  grind only

theorem gridScalarSum_congr (n : Nat) (f g : Nat → Scalar)
    (he : ∀ j, (f j).val.Equiv (g j).val) :
    (gridScalarSum n f).val.Equiv (gridScalarSum n g).val := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih => exact add_equiv ih (he n)

def rectangleGridCycleSum (f : QComplex → Scalar) (J : QInterval × QInterval) (M : Nat) : Scalar :=
  gridScalarSum M (fun j => gridScalarSum M (fun k => fullRectangleMidpointCycle f (rectangleGridCell J M j k)))

def rectangleGridBoundary (f : QComplex → Scalar) (J : QInterval × QInterval) (M : Nat) : Scalar :=
  gridScalarBoundary (rectangleGridHorizontal f J M) (rectangleGridVertical f J M) M M

theorem rectangleGridCycleSum_boundary_agreement (f : QComplex → Scalar)
    (J : QInterval × QInterval) (M : Nat) :
    (rectangleGridCycleSum f J M).val.Equiv (rectangleGridBoundary f J M).val := by
  let h := rectangleGridHorizontal f J M
  let v := rectangleGridVertical f J M
  let cells := gridScalarSum M (fun j => gridScalarSum M (fun k => gridScalarCell h v j k))
  have hc : cells.val.Equiv (rectangleGridCycleSum f J M).val :=
    gridScalarSum_congr M _ _ (fun j => gridScalarSum_congr M _ _
      (fun k => weightedGridCell_midpoint_agreement f J M j k))
  exact equiv_trans (rectangleGridCycleSum f J M).property cells.property
    (rectangleGridBoundary f J M).property (equiv_symm hc)
    (representedGrid_discrete_stokes h v M M)

theorem pairedRiccatiGridCell_agreement (J : QInterval × QInterval) (M j k : Nat) :
    (gridScalarCell
      (rectangleGridHorizontal (fun q => pairedEntireRiccatiMap.eval (rationalRectangleScalar q) trivial) J M)
      (rectangleGridVertical (fun q => pairedEntireRiccatiMap.eval (rationalRectangleScalar q) trivial) J M) j k).val.Equiv
      (pairedRiccatiFullRectangleCycle (rectangleGridCell J M j k)).val :=
  weightedGridCell_midpoint_agreement
    (fun q => pairedEntireRiccatiMap.eval (rationalRectangleScalar q) trivial) J M j k

end ComputableAnalysis.ModularForms
