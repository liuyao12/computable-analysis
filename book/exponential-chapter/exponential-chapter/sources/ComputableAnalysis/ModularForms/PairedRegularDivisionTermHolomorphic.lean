import ComputableAnalysis.ModularForms.PairedRegularDivisionContinuity

/-! Holomorphic actual regular-division terms on the chart through zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedSquareInputMap : DomainFunctions.Map :=
  productOn (affine ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩)
    (affine ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩) (fun _ _ => trivial)

def pairedSquareInputMap_holomorphic : Holomorphic pairedSquareInputMap :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩).productOn
    (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩) (fun _ _ => trivial)

def pairedLiteralDenominatorMap (t : Rat) : DomainFunctions.Map where
  domain _ := True
  eval z _ := pairedLiteralDenominator z t
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ he := FunctionTheory.sub_congr
    (mul_equiv z.property w.property z.property w.property he he) (equiv_refl _ (ofQComplex_valid _))

def pairedLiteralDenominatorMap_holomorphic (t : Rat) : Holomorphic (pairedLiteralDenominatorMap t) := by
  let f := affine ⟨ofQComplex ⟨-t,0⟩,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
  let hf := (affine_holomorphic ⟨ofQComplex ⟨-t,0⟩,ofQComplex_valid _⟩
    ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩).compose pairedSquareInputMap_holomorphic
  apply hf.transfer (pairedLiteralDenominatorMap t) (fun _ _ => ⟨trivial,trivial⟩)
    ⟨(fun _ _ => unitError),(fun _ _ _ _ => trivial)⟩
  intro z hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((compose f pairedSquareInputMap).eval z ⟨trivial,trivial⟩).property)
    (hright := (pairedLiteralDenominator z t).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let T := ComplexRawQuotient.ofQComplex ⟨t,0⟩
  change (-T)+1*((0+1*Z)*(0+1*Z))=Z*Z-T
  grind only

def pairedSmallDiskLiteralInverseMap (n : Nat) : DomainFunctions.Map where
  domain := LocalODE.interior (1/4)
  eval z hz := RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare (n+1)))
    ((pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ z hz)) n)
  domain_congr := pairedRegularDivisionMap.domain_congr
  eval_congr z w hz hw he := RepresentedReciprocal.inverse_congr _ _ _ _
    (FunctionTheory.sub_congr (mul_equiv z.property w.property z.property w.property he he)
      (equiv_refl _ (ofQComplex_valid _)))

def pairedSmallDiskLiteralInverseMap_holomorphic (n : Nat) : Holomorphic (pairedSmallDiskLiteralInverseMap n) := by
  let hf := ReciprocalHolomorphic.holomorphic.compose
    (pairedLiteralDenominatorMap_holomorphic (pairedIntegerSquare (n+1)))
  apply hf.transfer (pairedSmallDiskLiteralInverseMap n)
    (fun z hz => ⟨trivial,(pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ z hz)) n⟩)
    ⟨LocalODE.interiorRadius (1/4),LocalODE.interiorRadius_inside (1/4)⟩
  intro z hz
  exact equiv_refl _ ((pairedSmallDiskLiteralInverseMap n).eval z hz).property

def pairedRegularDivisionTermMap (n : Nat) : DomainFunctions.Map :=
  sumOn (pairedSmallDiskLiteralInverseMap n) (pairedSmallDiskLiteralInverseMap n)
    (fun (_ : Scalar) (hz : LocalODE.interior (1/4) _) => hz)

def pairedRegularDivisionTermMap_holomorphic (n : Nat) : Holomorphic (pairedRegularDivisionTermMap n) :=
  (pairedSmallDiskLiteralInverseMap_holomorphic n).sumOn (pairedSmallDiskLiteralInverseMap_holomorphic n)
    (fun (_ : Scalar) (hz : LocalODE.interior (1/4) _) => hz)

theorem pairedRegularDivisionTermMap_eval (n : Nat) (z : Scalar) (hz : LocalODE.interior (1/4) z) :
    ((pairedRegularDivisionTermMap n).eval z hz).val.Equiv
      (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((pairedRegularDivisionTermMap n).eval z hz).property)
    (hright := (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).property)
  let I := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval z hz).val
    ((pairedSmallDiskLiteralInverseMap n).eval z hz).property
  change I+I=ComplexRawQuotient.scaleRat 2 I
  have h := ComplexRawQuotient.add_scaleRat 1 1 I
  rw [ComplexRawQuotient.scaleRat_one] at h
  simpa only [show (1:Rat)+1=2 by decide +kernel] using h

end ComputableAnalysis.ModularForms
