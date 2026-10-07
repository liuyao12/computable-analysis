import ComputableAnalysis.ModularForms.PairedPartialFractionQuotient
import ComputableAnalysis.ModularForms.PairedInverseBound

/-! Bounds on individual reciprocal factors from an actual inverse of their product. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def scalarProduct (u v : Scalar) : Scalar :=
  ⟨mul u.val v.val,mul_valid u.property v.property⟩

theorem factorReciprocal_identity (u v : Scalar)
    (hu : NonzeroBoxSearch.Nonzero u)
    (hp : NonzeroBoxSearch.Nonzero (scalarProduct u v)) :
    (RepresentedReciprocal.inverse u hu).val.Equiv
      (mul v.val (RepresentedReciprocal.inverse (scalarProduct u v) hp).val) := by
  let P := RepresentedReciprocal.inverse (scalarProduct u v) hp
  apply RepresentedReciprocal.inverse_unique u hu ⟨mul v.val P.val,mul_valid v.property P.property⟩
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (scalarProduct u v).property P.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse (scalarProduct u v) hp)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid u.property (mul_valid v.property P.property))
    (hright := ofQComplex_valid _)
  let U := ComplexRawQuotient.ofRaw u.val u.property
  let V := ComplexRawQuotient.ofRaw v.val v.property
  let I := ComplexRawQuotient.ofRaw P.val P.property
  change (U*V)*I=1 at hi
  change U*(V*I)=1
  grind only

theorem factorReciprocal_bound (u v : Scalar)
    (hu : NonzeroBoxSearch.Nonzero u)
    (hp : NonzeroBoxSearch.Nonzero (scalarProduct u v))
    (A D : Rat) (hA : 0≤A) (hD : 0≤D)
    (hv : Small v.val A)
    (hi : Small (RepresentedReciprocal.inverse (scalarProduct u v) hp).val D) :
    Small (RepresentedReciprocal.inverse u hu).val (2*A*D) := by
  exact Small.congr (mul_valid v.property (RepresentedReciprocal.inverse (scalarProduct u v) hp).property)
    (RepresentedReciprocal.inverse u hu).property (equiv_symm (factorReciprocal_identity u v hu hp))
    (Small.mul v.property (RepresentedReciprocal.inverse (scalarProduct u v) hp).property hA hD hv hi)

theorem pairedFactor_product (z a : Scalar) :
    (scalarProduct (pairedMinus z a) (pairedPlus z a)).val.Equiv
      (pairedProduct z a).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct (pairedMinus z a) (pairedPlus z a)).property)
    (hright := (pairedProduct z a).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  change (Z-A)*(Z+A)=Z*Z-A*A
  grind only

theorem pairedMinusReciprocal_bound (z a : Scalar)
    (hm : NonzeroBoxSearch.Nonzero (pairedMinus z a))
    (hp : NonzeroBoxSearch.Nonzero (pairedPlus z a))
    (R A D : Rat) (hR : 0≤R) (hA : 0≤A) (hD : 0≤D)
    (hz : Small z.val R) (ha : Small a.val A)
    (hi : Small (RepresentedReciprocal.inverse (pairedProduct z a)
      (pairedProduct_nonzero z a hm hp)).val D) :
    Small (RepresentedReciprocal.inverse (pairedMinus z a) hm).val (2*(R+A)*D) := by
  let P := scalarProduct (pairedMinus z a) (pairedPlus z a)
  have hP : NonzeroBoxSearch.Nonzero P :=
    (NonzeroBoxSearch.nonzero_congr P (pairedProduct z a) (pairedFactor_product z a)).mpr
      (pairedProduct_nonzero z a hm hp)
  have he := RepresentedReciprocal.inverse_congr (pairedProduct z a) P
    (pairedProduct_nonzero z a hm hp) hP (equiv_symm (pairedFactor_product z a))
  have hI := Small.congr
    (RepresentedReciprocal.inverse (pairedProduct z a) (pairedProduct_nonzero z a hm hp)).property
    (RepresentedReciprocal.inverse P hP).property he hi
  exact factorReciprocal_bound (pairedMinus z a) (pairedPlus z a) hm hP
    (R+A) D (Rat.add_nonneg hR hA) hD (LocalODE.small_add hz ha) hI

theorem pairedPlusReciprocal_bound (z a : Scalar)
    (hm : NonzeroBoxSearch.Nonzero (pairedMinus z a))
    (hp : NonzeroBoxSearch.Nonzero (pairedPlus z a))
    (R A D : Rat) (hR : 0≤R) (hA : 0≤A) (hD : 0≤D)
    (hz : Small z.val R) (ha : Small a.val A)
    (hi : Small (RepresentedReciprocal.inverse (pairedProduct z a)
      (pairedProduct_nonzero z a hm hp)).val D) :
    Small (RepresentedReciprocal.inverse (pairedPlus z a) hp).val (2*(R+A)*D) := by
  let P := scalarProduct (pairedPlus z a) (pairedMinus z a)
  have heP : P.val.Equiv (pairedProduct z a).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := P.property)
      (hright := (pairedProduct z a).property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let A := ComplexRawQuotient.ofRaw a.val a.property
    change (Z+A)*(Z-A)=Z*Z-A*A
    grind only
  have hP : NonzeroBoxSearch.Nonzero P :=
    (NonzeroBoxSearch.nonzero_congr P (pairedProduct z a) heP).mpr
      (pairedProduct_nonzero z a hm hp)
  have he := RepresentedReciprocal.inverse_congr (pairedProduct z a) P
    (pairedProduct_nonzero z a hm hp) hP (equiv_symm heP)
  have hI := Small.congr
    (RepresentedReciprocal.inverse (pairedProduct z a) (pairedProduct_nonzero z a hm hp)).property
    (RepresentedReciprocal.inverse P hP).property he hi
  exact factorReciprocal_bound (pairedPlus z a) (pairedMinus z a) hp hP
    (R+A) D (Rat.add_nonneg hR hA) hD
    (LocalODE.small_add hz (SeriesLimitLaws.small_neg ha)) hI

end ComputableAnalysis.ModularForms
