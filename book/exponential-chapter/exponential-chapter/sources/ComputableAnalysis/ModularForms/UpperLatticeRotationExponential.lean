import ComputableAnalysis.ModularForms.LatticeRotationCrossError

/-! Exact lattice/exponential comparison on the full represented upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section
set_option maxHeartbeats 2000000

def upperLatticeRotationAnchor : Scalar :=
  ⟨ofQComplex ⟨0,latticeRotationCrossRadius.val/2⟩,ofQComplex_valid _⟩

theorem upperLatticeRotationAnchor_upper : InUpperHalfPlane upperLatticeRotationAnchor.val := by
  refine ⟨0,?_⟩
  change 0<latticeRotationCrossRadius.val/2
  rw [Rat.div_def]
  exact Rat.mul_pos latticeRotationCrossRadius.property (by decide +kernel)

theorem upperLatticeRotationAnchor_local : Small (sub upperLatticeRotationAnchor.val pairedZeroScalar.val) latticeRotationCrossRadius.val := by
  let R := latticeRotationCrossRadius.val
  have hp : 0<R := latticeRotationCrossRadius.property
  have hs : Small upperLatticeRotationAnchor.val R := by
    refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    · change -R≤0; grind only
    · change 0≤R; exact Rat.le_of_lt hp
    · change -R≤R/2; grind only
    · change R/2≤R; grind only
  have he : upperLatticeRotationAnchor.val.Equiv (sub upperLatticeRotationAnchor.val pairedZeroScalar.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := upperLatticeRotationAnchor.property) (hright := sub_valid upperLatticeRotationAnchor.property pairedZeroScalar.property)
    let A := gridScalarValue upperLatticeRotationAnchor
    change A=A-0
    grind only
  exact Small.congr upperLatticeRotationAnchor.property
    (sub_valid upperLatticeRotationAnchor.property pairedZeroScalar.property) he hs


theorem upperLatticeRotationAnchor_error_zero :
    (latticeRotationCrossErrorMap.eval upperLatticeRotationAnchor
      (latticeRotationCross_upper_mem upperLatticeRotationAnchor upperLatticeRotationAnchor_upper)).val.Equiv zero :=
  latticeRotationCross_local_zero upperLatticeRotationAnchor upperLatticeRotationAnchor_local

theorem latticeRotationCross_upper_zero (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (latticeRotationCrossErrorMap.eval z (latticeRotationCross_upper_mem z hz)).val.Equiv zero :=
  homogeneous_segment_zero latticeRotationCrossErrorMap latticeRotationCrossCoefficientMap
    latticeRotationCrossErrorMap_holomorphic latticeRotationCrossCoefficientMap_holomorphic
    latticeRotationCrossCoefficient_mem latticeRotationCrossError_equation
    upperLatticeRotationAnchor z
    (latticeRotationCross_upper_mem upperLatticeRotationAnchor upperLatticeRotationAnchor_upper)
    (latticeRotationCross_upper_mem z hz)
    (fun t => latticeRotationCross_upper_mem _
      (representedAffine_upper_mem upperLatticeRotationAnchor z upperLatticeRotationAnchor_upper hz t))
    upperLatticeRotationAnchor_error_zero

theorem latticeRotationCross_upper_identity (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (mul (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_upper_mem z hz).1).val
      (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)).val).Equiv
      (latticeRotationCrossNumeratorMap.eval z (latticeRotationCross_upper_mem z hz).2).val := by
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (latticeRotationCrossErrorMap.eval z (latticeRotationCross_upper_mem z hz)).property)
    (hright := ofQComplex_valid _) (latticeRotationCross_upper_zero z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_upper_mem z hz).1).property
      (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)).property)
    (hright := (latticeRotationCrossNumeratorMap.eval z (latticeRotationCross_upper_mem z hz).2).property)
  let D := gridScalarValue (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_upper_mem z hz).1)
  let E := gridScalarValue (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z))
  let N := gridScalarValue (latticeRotationCrossNumeratorMap.eval z (latticeRotationCross_upper_mem z hz).2)
  change D*E+ -N=0 at hh
  change D*E=N
  grind only

theorem latticeRotationCross_upper_denominator_nonzero (z : Scalar) (hz : InUpperHalfPlane z.val) :
    NonzeroBoxSearch.Nonzero
      (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_upper_mem z hz).1) := by
  intro hzero
  let hu := compose_inner_mem (latticeRotationCross_upper_mem z hz).1
  let u := normalizedLatticeTangentMap.eval z hu
  let e := latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_upper_mem z hz).1).property e.property)
    (hright := (latticeRotationCrossNumeratorMap.eval z (latticeRotationCross_upper_mem z hz).2).property)
    (latticeRotationCross_upper_identity z hz)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_upper_mem z hz).1).property)
    (hright := ofQComplex_valid _) hzero
  let U := gridScalarValue u
  let E := gridScalarValue e
  let I := gridScalarValue latticeImaginaryUnit
  change (1+(-I)*U)*E=1+I*U at hh
  change 1+(-I)*U=0 at hd
  have hbad : (1:ScalarAlgebra.Value)+1=0 := by grind only
  have htwo := rationalPole_add_values QComplex.one QComplex.one
  have hc : QComplex.add QComplex.one QComplex.one=⟨2,0⟩ := by decide +kernel
  rw [hc] at htwo
  change gridScalarValue (rationalRectangleScalar ⟨2,0⟩)=1+1 at htwo
  have he : (ofQComplex ⟨2,0⟩).Equiv zero := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := ofQComplex_valid _) (hright := ofQComplex_valid _)
    change gridScalarValue (rationalRectangleScalar ⟨2,0⟩)=0
    exact htwo.trans hbad
  have hb := ((compareAt_overlap_iff _ _ 0 0).mp (he 0)).1.1
  change (2:Rat)≤0 at hb
  grind only

end
end ComputableAnalysis.ModularForms
