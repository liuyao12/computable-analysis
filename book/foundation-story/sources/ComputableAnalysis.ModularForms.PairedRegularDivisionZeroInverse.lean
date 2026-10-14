import ComputableAnalysis.ModularForms.PairedRegularDivisionProductDerivative

/-! Exact rational inverse values of the regular-division denominators at zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem rationalRealProduct_equiv (a b : Rat) :
    (mul (ofQComplex ⟨a,0⟩) (ofQComplex ⟨b,0⟩)).Equiv (ofQComplex ⟨a*b,0⟩) := by
  have h := qcomplexLeftMul_equiv_mul_ofQComplex (⟨a,0⟩ : QComplex) (ofQComplex_valid ⟨b,0⟩)
  have hq := qcomplexLeftMul_ofQComplex (⟨a,0⟩ : QComplex) ⟨b,0⟩
  have he : QComplex.mul (⟨a,0⟩ : QComplex) ⟨b,0⟩=⟨a*b,0⟩ := by
    simp [QComplex.mul,Rat.mul_zero,Rat.zero_mul,Rat.sub_eq_add_neg,Rat.add_zero,Rat.neg_zero]
  rw [he] at hq
  exact equiv_trans (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))
    (qcomplexLeftMul_valid _ (ofQComplex_valid _)) (ofQComplex_valid _) (equiv_symm h) hq

theorem pairedSmallDiskLiteralInverse_at_zero (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (he : z.val.Equiv zero) (n : Nat) :
    ((pairedSmallDiskLiteralInverseMap n).eval z hz).val.Equiv
      (ofQComplex ⟨-reciprocalSquare (n+1),0⟩) := by
  let t := pairedIntegerSquare (n+1)
  have hd : (pairedLiteralDenominator z t).val.Equiv (ofQComplex ⟨-t,0⟩) := by
    have hzero := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := ofQComplex_valid _) he
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (pairedLiteralDenominator z t).property) (hright := ofQComplex_valid _)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let T := ComplexRawQuotient.ofQComplex ⟨t,0⟩
    change Z=0 at hzero
    change Z*Z-T= -T
    grind only
  have ht : (-t)*(-reciprocalSquare (n+1))=1 := by
    have h := Rat.mul_inv_cancel (pairedIntegerSquare (n+1)) (Rat.ne_of_gt (pairedIntegerSquare_pos _ (by omega)))
    dsimp [t]; unfold pairedIntegerSquare reciprocalSquare at *
    grind only
  have hp := rationalRealProduct_equiv (-t) (-reciprocalSquare (n+1))
  rw [ht] at hp
  apply RepresentedReciprocal.inverse_unique (pairedLiteralDenominator z t)
    ((pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ z hz)) n)
    ⟨ofQComplex ⟨-reciprocalSquare (n+1),0⟩,ofQComplex_valid _⟩
  exact equiv_trans (mul_valid (pairedLiteralDenominator z t).property (ofQComplex_valid _))
    (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
    (mul_equiv (pairedLiteralDenominator z t).property (ofQComplex_valid _) (ofQComplex_valid _) (ofQComplex_valid _)
      hd (equiv_refl _ (ofQComplex_valid _))) hp

end ComputableAnalysis.ModularForms
