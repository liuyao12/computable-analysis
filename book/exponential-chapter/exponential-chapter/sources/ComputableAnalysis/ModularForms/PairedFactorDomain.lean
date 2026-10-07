import ComputableAnalysis.ModularForms.PairedRegularPart

/-! Actual inverse products justify the individual nonzero factor domains. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem factor_nonzero_of_product (u v : Scalar)
    (hp : NonzeroBoxSearch.Nonzero (scalarProduct u v)) : NonzeroBoxSearch.Nonzero u := by
  let P := RepresentedReciprocal.inverse (scalarProduct u v) hp
  apply RepresentedReciprocal.nonzero_of_inverse u ⟨mul v.val P.val,mul_valid v.property P.property⟩
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

theorem factor_right_nonzero_of_product (u v : Scalar)
    (hp : NonzeroBoxSearch.Nonzero (scalarProduct u v)) : NonzeroBoxSearch.Nonzero v := by
  have he : (scalarProduct v u).val.Equiv (scalarProduct u v).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (scalarProduct v u).property) (hright := (scalarProduct u v).property)
    let U := ComplexRawQuotient.ofRaw u.val u.property
    let V := ComplexRawQuotient.ofRaw v.val v.property
    change V*U=U*V
    grind only
  exact factor_nonzero_of_product v u
    ((NonzeroBoxSearch.nonzero_congr (scalarProduct v u) (scalarProduct u v) he).mpr hp)

theorem pairedFactors_nonzero (z a : Scalar) (hp : NonzeroBoxSearch.Nonzero (pairedProduct z a)) :
    NonzeroBoxSearch.Nonzero (pairedMinus z a) ∧ NonzeroBoxSearch.Nonzero (pairedPlus z a) := by
  have hprod := (NonzeroBoxSearch.nonzero_congr
    (scalarProduct (pairedMinus z a) (pairedPlus z a)) (pairedProduct z a) (pairedFactor_product z a)).mpr hp
  exact ⟨factor_nonzero_of_product _ _ hprod,factor_right_nonzero_of_product _ _ hprod⟩

theorem pairedSeriesDomain_factors (z : Scalar) (hd : PairedSeriesDomain z) (n : Nat) :
    NonzeroBoxSearch.Nonzero (pairedMinus z (boundaryIntegerScalar (n+1))) ∧
      NonzeroBoxSearch.Nonzero (pairedPlus z (boundaryIntegerScalar (n+1))) := by
  have he : (pairedProduct z (boundaryIntegerScalar (n+1))).val.Equiv
      (pairedLiteralDenominator z (pairedIntegerSquare (n+1))).val :=
    FunctionTheory.sub_congr (equiv_refl _ (mul_valid z.property z.property))
      (rationalRealSquare_equiv ((n+1:Nat):Rat))
  exact pairedFactors_nonzero z (boundaryIntegerScalar (n+1))
    ((NonzeroBoxSearch.nonzero_congr _ _ he).mpr (hd n))

theorem pairedSmallDisk_factors (z : Scalar) (hz : Small z.val (1/4)) (n : Nat) :
    NonzeroBoxSearch.Nonzero (pairedMinus z (boundaryIntegerScalar (n+1))) ∧
      NonzeroBoxSearch.Nonzero (pairedPlus z (boundaryIntegerScalar (n+1))) :=
  pairedSeriesDomain_factors z (pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz) n

end ComputableAnalysis.ModularForms
