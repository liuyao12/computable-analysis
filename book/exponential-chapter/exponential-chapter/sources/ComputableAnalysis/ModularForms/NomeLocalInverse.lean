import ComputableAnalysis.ModularForms.NomeLogarithmChart

/-! Constructed holomorphic inverse coordinates for the nome. The logarithm
chart is divided by the actual nonzero slope; the upper-half-plane restriction
is open and contains the original nome. No inverse identity is assumed. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private def scalarClass (z : Scalar) := ComplexRawQuotient.ofRaw z.val z.property

theorem nomeSlope_nonzero : NonzeroBoxSearch.Nonzero nomeSlope := by
  intro h
  have ho := (compareAt_overlap_iff _ _ 0 0).mp (h 0)
  have hp := (GeometricPiRotation.halfPi_bounds 0).1
  have hi := ho.1.2
  simp only [nomeSlope, scaleRat, mulI, ofRealRaw, QBox.scaleRat,
    if_pos (show (0:Rat)≤4 by decide +kernel)] at hi
  change 4*(GeometricPiRotation.halfPi.compute 0).lo ≤ 0 at hi
  grind only

def nomeInverseSlope : Scalar := RepresentedReciprocal.inverse nomeSlope nomeSlope_nonzero

def nomeLocalLift (a : Scalar) (ha : InUpperHalfPlane a.val) : DomainFunctions.Map :=
  compose (affine ⟨zero,ofQComplex_valid _⟩ nomeInverseSlope) (nomeLogarithmChart a ha)

def nomeLocalLift_holomorphic (a : Scalar) (ha : InUpperHalfPlane a.val) :
    Holomorphic (nomeLocalLift a ha) :=
  (DomainFunctions.affine_holomorphic ⟨zero,ofQComplex_valid _⟩ nomeInverseSlope).compose
    (nomeLogarithmChart_holomorphic a ha)

theorem nomeLocalLift_center_mem (a : Scalar) (ha : InUpperHalfPlane a.val) :
    (nomeLocalLift a ha).domain (nome.eval a ha) :=
  ⟨nomeLogarithmChart_center_mem a ha, trivial⟩

theorem nomeLocalLift_center (a : Scalar) (ha : InUpperHalfPlane a.val) :
    ((nomeLocalLift a ha).eval (nome.eval a ha) (nomeLocalLift_center_mem a ha)).val.Equiv a.val := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid nomeInverseSlope.property nomeSlope.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.inverse_mul nomeSlope nomeSlope_nonzero)
  have hc := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((nomeLogarithmChart a ha).eval (nome.eval a ha) (nomeLogarithmChart_center_mem a ha)).property)
    (hright := (nomeExponentMap.eval a ha).property) (nomeLogarithmChart_center a ha)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((nomeLocalLift a ha).eval (nome.eval a ha) (nomeLocalLift_center_mem a ha)).property)
    (hright := a.property)
  let R := scalarClass nomeInverseSlope
  let S := scalarClass nomeSlope
  let A := scalarClass a
  let L := scalarClass ((nomeLogarithmChart a ha).eval (nome.eval a ha) (nomeLogarithmChart_center_mem a ha))
  change R*S=1 at hi
  change L=S*A at hc
  change 0+R*L=A
  grind only

/-- Restrict the constructed lift to the open set where its value lies in the
upper half plane, and compose with the actual nome. -/
def nomeLocalRoundTrip (a : Scalar) (ha : InUpperHalfPlane a.val) : DomainFunctions.Map :=
  compose nome (nomeLocalLift a ha)

def nomeLocalRoundTrip_holomorphic (a : Scalar) (ha : InUpperHalfPlane a.val) :
    Holomorphic (nomeLocalRoundTrip a ha) :=
  nome_holomorphic.compose (nomeLocalLift_holomorphic a ha)

theorem nomeLocalRoundTrip_center_mem (a : Scalar) (ha : InUpperHalfPlane a.val) :
    (nomeLocalRoundTrip a ha).domain (nome.eval a ha) :=
  ⟨nomeLocalLift_center_mem a ha,
    (upperOpenData.invariant a ((nomeLocalLift a ha).eval (nome.eval a ha) (nomeLocalLift_center_mem a ha))
      (equiv_symm (nomeLocalLift_center a ha))).mp ha⟩

/-- The constructed local inverse is a right inverse for the actual nome. -/
theorem nomeLocalRoundTrip_identity (a : Scalar) (ha : InUpperHalfPlane a.val)
    (q : Scalar) (hq : (nomeLocalRoundTrip a ha).domain q) :
    ((nomeLocalRoundTrip a ha).eval q hq).val.Equiv q.val := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid nomeSlope.property nomeInverseSlope.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse nomeSlope nomeSlope_nonzero)
  have he : (nomeExponentMap.eval ((nomeLocalLift a ha).eval q hq.1) hq.2).val.Equiv
      ((nomeLogarithmChart a ha).eval q hq.1.1).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (nomeExponentMap.eval ((nomeLocalLift a ha).eval q hq.1) hq.2).property)
      (hright := ((nomeLogarithmChart a ha).eval q hq.1.1).property)
    let S := scalarClass nomeSlope
    let R := scalarClass nomeInverseSlope
    let L := scalarClass ((nomeLogarithmChart a ha).eval q hq.1.1)
    change S*R=1 at hi
    change S*(0+R*L)=L
    grind only
  exact equiv_trans ((nomeLocalRoundTrip a ha).eval q hq).property
    (entireExponentialValue ((nomeLogarithmChart a ha).eval q hq.1.1)).property q.property
    (entireExponentialValue_congr _ _ he) (nomeLogarithmChart_exponential a ha q hq.1.1)

end ComputableAnalysis.ModularForms
