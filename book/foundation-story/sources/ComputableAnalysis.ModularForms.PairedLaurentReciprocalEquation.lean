import ComputableAnalysis.ModularForms.PairedRiccatiConstantSeparation

/-! Actual reciprocal regularization of the lattice kernel near its zero pole. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def pairedPoleDenominator (z : Scalar) (hz : LocalODE.interior (1/4) z) : Scalar :=
  scalarSum ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
    (scalarProduct z (pairedRegularPartMap.eval z hz))

theorem pairedPoleDenominator_error (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (hs : Small z.val (1/32)) :
    Small (sub (pairedPoleDenominator z hz).val (ofQComplex QComplex.one)) (1/16) := by
  have hr := pairedRegularPart_bound z (LocalODE.interior_bound _ z hz)
    (1/32) (by decide +kernel) (by decide +kernel) hs
  have hb := Small.mul z.property (pairedRegularPartMap.eval z hz).property
    (by decide +kernel : (0:Rat)≤1/32) (by decide +kernel : (0:Rat)≤32*(1/32)) hs hr
  have he : (mul z.val (pairedRegularPartMap.eval z hz).val).Equiv
      (sub (pairedPoleDenominator z hz).val (ofQComplex QComplex.one)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid z.property (pairedRegularPartMap.eval z hz).property)
      (hright := sub_valid (pairedPoleDenominator z hz).property (ofQComplex_valid _))
    let Z := gridScalarValue z
    let S := gridScalarValue (pairedRegularPartMap.eval z hz)
    change Z*S=(1+Z*S)-1
    grind only
  have ht : 2*(1/32:Rat)*(32*(1/32))=1/16 := by decide +kernel
  rw [ht] at hb
  exact Small.congr (mul_valid z.property (pairedRegularPartMap.eval z hz).property)
    (sub_valid (pairedPoleDenominator z hz).property (ofQComplex_valid _)) he hb

theorem pairedPoleDenominator_nonzero (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (hs : Small z.val (1/32)) : NonzeroBoxSearch.Nonzero (pairedPoleDenominator z hz) := by
  intro he
  have hb := pairedPoleDenominator_error z hz hs
  have ht : (sub (pairedPoleDenominator z hz).val (ofQComplex QComplex.one)).Equiv
      (ofQComplex ⟨-1,0⟩) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedPoleDenominator z hz).property (ofQComplex_valid _))
      (hright := ofQComplex_valid _)
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (pairedPoleDenominator z hz).property) (hright := ofQComplex_valid _) he
    let D := gridScalarValue (pairedPoleDenominator z hz)
    change D=0 at hv
    change D-1= -1
    rw [hv]
    grind only
  have h := Small.congr (sub_valid (pairedPoleDenominator z hz).property (ofQComplex_valid _))
    (ofQComplex_valid _) ht hb
  have hh := h.1 0 0
  change -(1/16:Rat)≤ -1 at hh
  grind only

def pairedPoleReciprocal (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (hs : Small z.val (1/32)) : Scalar :=
  scalarProduct z (RepresentedReciprocal.inverse (pairedPoleDenominator z hz)
    (pairedPoleDenominator_nonzero z hz hs))

theorem pairedPoleReciprocal_center (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (hs : Small z.val (1/32)) (he : z.val.Equiv zero) :
    (pairedPoleReciprocal z hz hs).val.Equiv zero := by
  let r := RepresentedReciprocal.inverse (pairedPoleDenominator z hz) (pairedPoleDenominator_nonzero z hz hs)
  exact equiv_trans (pairedPoleReciprocal z hz hs).property (mul_valid (ofQComplex_valid _) r.property)
    (ofQComplex_valid _) (mul_equiv z.property (ofQComplex_valid _) r.property r.property he
      (equiv_refl _ r.property)) (zero_mul_equiv r.val r.property)

theorem pairedZeroLaurent_mul_poleReciprocal (z : Scalar) (hz : pairedZeroLaurentMap.domain z)
    (hs : Small z.val (1/32)) :
    (mul (pairedZeroLaurentMap.eval z hz).val (pairedPoleReciprocal z hz.1 hs).val).Equiv
      (ofQComplex QComplex.one) := by
  let r := RepresentedReciprocal.inverse (pairedPoleDenominator z hz.1)
    (pairedPoleDenominator_nonzero z hz.1 hs)
  let i := RepresentedReciprocal.inverse z hz.2
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property i.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse z hz.2)
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedPoleDenominator z hz.1).property r.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (pairedPoleDenominator z hz.1) (pairedPoleDenominator_nonzero z hz.1 hs))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (pairedZeroLaurentMap.eval z hz).property (pairedPoleReciprocal z hz.1 hs).property)
    (hright := ofQComplex_valid _)
  let Z := gridScalarValue z
  let S := gridScalarValue (pairedRegularPartMap.eval z hz.1)
  let I := gridScalarValue i
  let R := gridScalarValue r
  change Z*I=1 at hi
  change (1+Z*S)*R=1 at hr
  change (I+S)*(Z*R)=1
  grind only

theorem pairedZeroLaurent_near_pole_nonzero (z : Scalar) (hz : pairedZeroLaurentMap.domain z)
    (hs : Small z.val (1/32)) : NonzeroBoxSearch.Nonzero (pairedZeroLaurentMap.eval z hz) :=
  RepresentedReciprocal.nonzero_of_inverse _ _ (pairedZeroLaurent_mul_poleReciprocal z hz hs)

def pairedLaurentReciprocalMap : DomainFunctions.Map :=
  compose ReciprocalHolomorphic.function pairedZeroLaurentMap

def pairedLaurentReciprocalMap_holomorphic : Holomorphic pairedLaurentReciprocalMap :=
  ReciprocalHolomorphic.holomorphic.compose pairedZeroLaurentMap_holomorphic

theorem pairedLaurentReciprocal_near_pole_mem (z : Scalar) (hz : pairedZeroLaurentMap.domain z)
    (hs : Small z.val (1/32)) : pairedLaurentReciprocalMap.domain z :=
  ⟨hz,pairedZeroLaurent_near_pole_nonzero z hz hs⟩

theorem pairedLaurentReciprocal_pole_agreement (z : Scalar) (hz : pairedZeroLaurentMap.domain z)
    (hs : Small z.val (1/32)) :
    (pairedLaurentReciprocalMap.eval z (pairedLaurentReciprocal_near_pole_mem z hz hs)).val.Equiv
      (pairedPoleReciprocal z hz.1 hs).val :=
  RepresentedReciprocal.inverse_unique (pairedZeroLaurentMap.eval z hz)
    (pairedZeroLaurent_near_pole_nonzero z hz hs) (pairedPoleReciprocal z hz.1 hs)
    (pairedZeroLaurent_mul_poleReciprocal z hz hs)

theorem pairedZeroLaurent_riccati_identity (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    (add (pairedZeroLaurentMap_holomorphic.derivative z hz).val
      (mul (pairedZeroLaurentMap.eval z hz).val (pairedZeroLaurentMap.eval z hz).val)).Equiv
      pairedRiccatiCenterConstant.val := by
  have hp := pairedZeroLaurentMap_global_agreement z hz
  have hd := pairedZeroLaurentMap_global_derivative_agreement z hz
  have hh := add_equiv hd
    (mul_equiv (pairedZeroLaurentMap.eval z hz).property
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedZeroLaurentMap_global_mem z hz)).property
      (pairedZeroLaurentMap.eval z hz).property
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedZeroLaurentMap_global_mem z hz)).property hp hp)
  exact equiv_trans
    (add_valid (pairedZeroLaurentMap_holomorphic.derivative z hz).property
      (mul_valid (pairedZeroLaurentMap.eval z hz).property (pairedZeroLaurentMap.eval z hz).property))
    (add_valid (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (pairedZeroLaurentMap_global_mem z hz)).property
      (mul_valid (pairedGlobalOffPoleAssemblyMap.eval z (pairedZeroLaurentMap_global_mem z hz)).property
        (pairedGlobalOffPoleAssemblyMap.eval z (pairedZeroLaurentMap_global_mem z hz)).property))
    pairedRiccatiCenterConstant.property hh
    (pairedGlobalOffPoleAssemblyMap_riccati_identity z (pairedZeroLaurentMap_global_mem z hz))

theorem pairedLaurentReciprocal_differential_identity (z : Scalar) (hz : pairedLaurentReciprocalMap.domain z) :
    (pairedLaurentReciprocalMap_holomorphic.derivative z hz).val.Equiv
      (sub (ofQComplex QComplex.one)
        (mul pairedRiccatiCenterConstant.val
          (mul (pairedLaurentReciprocalMap.eval z hz).val (pairedLaurentReciprocalMap.eval z hz).val))) := by
  let hl := compose_inner_mem hz
  let p := pairedZeroLaurentMap.eval z hl
  let hn := compose_outer_mem hz
  let r := RepresentedReciprocal.inverse p hn
  let d := pairedZeroLaurentMap_holomorphic.derivative z hl
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid p.property r.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse p hn)
  have hc := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid d.property (mul_valid p.property p.property))
    (hright := pairedRiccatiCenterConstant.property) (pairedZeroLaurent_riccati_identity z hl)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedLaurentReciprocalMap_holomorphic.derivative z hz).property)
    (hright := sub_valid (ofQComplex_valid _) (mul_valid pairedRiccatiCenterConstant.property
      (mul_valid (pairedLaurentReciprocalMap.eval z hz).property (pairedLaurentReciprocalMap.eval z hz).property)))
  let P := gridScalarValue p
  let R := gridScalarValue r
  let D := gridScalarValue d
  let C := gridScalarValue pairedRiccatiCenterConstant
  change P*R=1 at hi
  change D+P*P=C at hc
  change -(R*R)*D=1-C*(R*R)
  have hm : (P*P)*(R*R)=(P*R)*(P*R) := by grind only
  rw [hi] at hm
  grind only

def pairedRegularizedLaurentReciprocalMap : DomainFunctions.Map :=
  productOn pairedPoleReciprocalMap (entireIntegerShiftMap 0) (fun _ _ => trivial)

def pairedRegularizedLaurentReciprocalMap_holomorphic : Holomorphic pairedRegularizedLaurentReciprocalMap :=
  pairedPoleReciprocalMap_holomorphic.productOn (entireIntegerShiftMap_holomorphic 0) (fun _ _ => trivial)

theorem pairedRegularizedLaurentReciprocal_value (z : Scalar) (hz : LocalODE.interior (1/32) z) :
    (pairedRegularizedLaurentReciprocalMap.eval z hz).val.Equiv
      (pairedPoleReciprocal z (pairedPoleExtension_room z hz) (LocalODE.interior_bound _ z hz)).val := by
  let r := pairedPoleReciprocalMap.eval z hz
  have he := mul_equiv r.property r.property (integerShiftScalar z 0).property z.property
    (equiv_refl _ r.property) (integerShiftScalar_zero_equiv z)
  exact equiv_trans (pairedRegularizedLaurentReciprocalMap.eval z hz).property
    (mul_valid r.property z.property)
    (pairedPoleReciprocal z (pairedPoleExtension_room z hz) (LocalODE.interior_bound _ z hz)).property
    he (mul_comm_equiv r.val z.val r.property z.property)

theorem pairedRegularizedLaurentReciprocal_center (z : Scalar) (hz : LocalODE.interior (1/32) z)
    (he : z.val.Equiv zero) : (pairedRegularizedLaurentReciprocalMap.eval z hz).val.Equiv zero :=
  equiv_trans (pairedRegularizedLaurentReciprocalMap.eval z hz).property
    (pairedPoleReciprocal z (pairedPoleExtension_room z hz) (LocalODE.interior_bound _ z hz)).property
    (ofQComplex_valid _) (pairedRegularizedLaurentReciprocal_value z hz)
    (pairedPoleReciprocal_center z (pairedPoleExtension_room z hz) (LocalODE.interior_bound _ z hz) he)

theorem pairedRegularizedLaurentReciprocal_punctured_agreement (z : Scalar)
    (hz : LocalODE.interior (1/32) z) (hn : NonzeroBoxSearch.Nonzero z) :
    (pairedRegularizedLaurentReciprocalMap.eval z hz).val.Equiv
      (pairedLaurentReciprocalMap.eval z
        (pairedLaurentReciprocal_near_pole_mem z ⟨pairedPoleExtension_room z hz,hn⟩
          (LocalODE.interior_bound _ z hz))).val :=
  equiv_trans (pairedRegularizedLaurentReciprocalMap.eval z hz).property
    (pairedPoleReciprocal z (pairedPoleExtension_room z hz) (LocalODE.interior_bound _ z hz)).property
    (pairedLaurentReciprocalMap.eval z
      (pairedLaurentReciprocal_near_pole_mem z ⟨pairedPoleExtension_room z hz,hn⟩
        (LocalODE.interior_bound _ z hz))).property
    (pairedRegularizedLaurentReciprocal_value z hz)
    (equiv_symm (pairedLaurentReciprocal_pole_agreement z ⟨pairedPoleExtension_room z hz,hn⟩
      (LocalODE.interior_bound _ z hz)))

theorem pairedPoleReciprocalMap_center (z : Scalar) (hz : LocalODE.interior (1/32) z)
    (he : z.val.Equiv zero) : (pairedPoleReciprocalMap.eval z hz).val.Equiv (ofQComplex QComplex.one) := by
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz)).property)
    (hright := ofQComplex_valid _) (pairedPoleExtensionMap_zero z (pairedPoleExtension_room z hz) he)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz)).property
      (pairedPoleReciprocalMap.eval z hz).property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz))
      (pairedPoleExtension_nonzero z hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedPoleReciprocalMap.eval z hz).property) (hright := ofQComplex_valid _)
  let D := gridScalarValue (pairedPoleExtensionMap.eval z (pairedPoleExtension_room z hz))
  let I := gridScalarValue (pairedPoleReciprocalMap.eval z hz)
  change D=1 at hd
  change D*I=1 at hi
  change I=1
  rw [hd] at hi
  grind only

theorem pairedRegularizedLaurentReciprocal_derivative_center (z : Scalar)
    (hz : LocalODE.interior (1/32) z) (he : z.val.Equiv zero) :
    (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).val.Equiv
      (ofQComplex QComplex.one) := by
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedPoleReciprocalMap.eval z hz).property) (hright := ofQComplex_valid _)
    (pairedPoleReciprocalMap_center z hz he)
  have hz0 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerShiftScalar z 0).property) (hright := ofQComplex_valid _)
    (equiv_trans (integerShiftScalar z 0).property z.property (ofQComplex_valid _)
      (integerShiftScalar_zero_equiv z) he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).property)
    (hright := ofQComplex_valid _)
  let D := gridScalarValue (pairedPoleReciprocalMap_holomorphic.derivative z hz)
  let Z := gridScalarValue (integerShiftScalar z 0)
  let I := gridScalarValue (pairedPoleReciprocalMap.eval z hz)
  change I=1 at hr
  change Z=0 at hz0
  change D*Z+I*1=1
  rw [hr,hz0]
  grind only

theorem pairedRegularizedLaurentReciprocal_derivative_punctured (z : Scalar)
    (hz : LocalODE.interior (1/32) z) (hn : NonzeroBoxSearch.Nonzero z) :
    (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).val.Equiv
      (sub (ofQComplex QComplex.one) (mul pairedRiccatiCenterConstant.val
        (mul (pairedRegularizedLaurentReciprocalMap.eval z hz).val
          (pairedRegularizedLaurentReciprocalMap.eval z hz).val))) := by
  let hl := pairedLaurentReciprocal_near_pole_mem z ⟨pairedPoleExtension_room z hz,hn⟩
    (LocalODE.interior_bound _ z hz)
  have hd := pairedRegularizedLaurentReciprocalMap_holomorphic.derivative_equiv_on_overlap
    pairedLaurentReciprocalMap_holomorphic
    (fun w hw hr => pairedRegularizedLaurentReciprocal_punctured_agreement w hw (compose_inner_mem hr).2)
    z hz hl
  have he := pairedRegularizedLaurentReciprocal_punctured_agreement z hz hn
  have hm := mul_equiv pairedRiccatiCenterConstant.property pairedRiccatiCenterConstant.property
    (mul_valid (pairedLaurentReciprocalMap.eval z hl).property (pairedLaurentReciprocalMap.eval z hl).property)
    (mul_valid (pairedRegularizedLaurentReciprocalMap.eval z hz).property (pairedRegularizedLaurentReciprocalMap.eval z hz).property)
    (equiv_refl _ pairedRiccatiCenterConstant.property)
    (mul_equiv (pairedLaurentReciprocalMap.eval z hl).property (pairedRegularizedLaurentReciprocalMap.eval z hz).property
      (pairedLaurentReciprocalMap.eval z hl).property (pairedRegularizedLaurentReciprocalMap.eval z hz).property
      (equiv_symm he) (equiv_symm he))
  exact equiv_trans (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).property
    (pairedLaurentReciprocalMap_holomorphic.derivative z hl).property
    (sub_valid (ofQComplex_valid _) (mul_valid pairedRiccatiCenterConstant.property
      (mul_valid (pairedRegularizedLaurentReciprocalMap.eval z hz).property (pairedRegularizedLaurentReciprocalMap.eval z hz).property))) hd
    (equiv_trans (pairedLaurentReciprocalMap_holomorphic.derivative z hl).property
      (sub_valid (ofQComplex_valid _) (mul_valid pairedRiccatiCenterConstant.property
        (mul_valid (pairedLaurentReciprocalMap.eval z hl).property (pairedLaurentReciprocalMap.eval z hl).property)))
      (sub_valid (ofQComplex_valid _) (mul_valid pairedRiccatiCenterConstant.property
        (mul_valid (pairedRegularizedLaurentReciprocalMap.eval z hz).property (pairedRegularizedLaurentReciprocalMap.eval z hz).property)))
      (pairedLaurentReciprocal_differential_identity z hl)
      (FunctionTheory.sub_congr (equiv_refl _ (ofQComplex_valid _)) hm))

theorem pairedRegularizedLaurentReciprocal_differential_identity (z : Scalar)
    (hz : LocalODE.interior (1/32) z) :
    (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).val.Equiv
      (sub (ofQComplex QComplex.one) (mul pairedRiccatiCenterConstant.val
        (mul (pairedRegularizedLaurentReciprocalMap.eval z hz).val
          (pairedRegularizedLaurentReciprocalMap.eval z hz).val))) := by
  classical
  by_cases he : z.val.Equiv zero
  · have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (pairedRegularizedLaurentReciprocalMap.eval z hz).property) (hright := ofQComplex_valid _)
      (pairedRegularizedLaurentReciprocal_center z hz he)
    have hr : (ofQComplex QComplex.one).Equiv
        (sub (ofQComplex QComplex.one) (mul pairedRiccatiCenterConstant.val
          (mul (pairedRegularizedLaurentReciprocalMap.eval z hz).val
            (pairedRegularizedLaurentReciprocalMap.eval z hz).val))) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := ofQComplex_valid _)
        (hright := sub_valid (ofQComplex_valid _) (mul_valid pairedRiccatiCenterConstant.property
          (mul_valid (pairedRegularizedLaurentReciprocalMap.eval z hz).property
            (pairedRegularizedLaurentReciprocalMap.eval z hz).property)))
      let W := gridScalarValue (pairedRegularizedLaurentReciprocalMap.eval z hz)
      let C := gridScalarValue pairedRiccatiCenterConstant
      change W=0 at hv
      change 1=1-C*(W*W)
      rw [hv]
      grind only
    exact equiv_trans (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).property
      (ofQComplex_valid _)
      (sub_valid (ofQComplex_valid _) (mul_valid pairedRiccatiCenterConstant.property
        (mul_valid (pairedRegularizedLaurentReciprocalMap.eval z hz).property
          (pairedRegularizedLaurentReciprocalMap.eval z hz).property)))
      (pairedRegularizedLaurentReciprocal_derivative_center z hz he) hr
  · exact pairedRegularizedLaurentReciprocal_derivative_punctured z hz he

end ComputableAnalysis.ModularForms
