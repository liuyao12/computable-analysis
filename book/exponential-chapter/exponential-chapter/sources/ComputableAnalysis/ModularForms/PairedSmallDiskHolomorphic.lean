import ComputableAnalysis.ModularForms.PairedFactorDomain

/-! Holomorphic individual paired terms across the zero pole of the full series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def smallDiskShift (z : Scalar) (n : Nat) (plus : Bool) : Scalar :=
  if plus then pairedPlus z (boundaryIntegerScalar (n+1)) else pairedMinus z (boundaryIntegerScalar (n+1))

theorem smallDiskShift_nonzero (z : Scalar) (hz : Small z.val (1/4)) (n : Nat) (plus : Bool) :
    NonzeroBoxSearch.Nonzero (smallDiskShift z n plus) := by
  cases plus with
  | false => exact (pairedSmallDisk_factors z hz n).1
  | true => exact (pairedSmallDisk_factors z hz n).2

theorem smallDiskShift_congr (z w : Scalar) (he : z.val.Equiv w.val) (n : Nat) (plus : Bool) :
    (smallDiskShift z n plus).val.Equiv (smallDiskShift w n plus).val := by
  cases plus with
  | false => exact FunctionTheory.sub_congr he (equiv_refl _ (boundaryIntegerScalar (n+1)).property)
  | true => exact add_equiv he (equiv_refl _ (boundaryIntegerScalar (n+1)).property)

def smallDiskShiftConstant (n : Nat) (plus : Bool) : Scalar :=
  if plus then boundaryIntegerScalar (n+1) else
    ⟨neg (boundaryIntegerScalar (n+1)).val,neg_valid (boundaryIntegerScalar (n+1)).property⟩

def smallDiskShiftAffine (n : Nat) (plus : Bool) : DomainFunctions.Map :=
  affine (smallDiskShiftConstant n plus) ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩

theorem smallDiskShiftAffine_agreement (z : Scalar) (n : Nat) (plus : Bool) :
    ((smallDiskShiftAffine n plus).eval z trivial).val.Equiv (smallDiskShift z n plus).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((smallDiskShiftAffine n plus).eval z trivial).property)
    (hright := (smallDiskShift z n plus).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let C := ComplexRawQuotient.ofRaw (boundaryIntegerScalar (n+1)).val (boundaryIntegerScalar (n+1)).property
  cases plus with
  | false => change (-C)+1*Z=Z-C; grind only
  | true => change C+1*Z=Z+C; grind only

def smallDiskShiftMap (n : Nat) (plus : Bool) : DomainFunctions.Map where
  domain := LocalODE.interior (1/4)
  eval z hz := RepresentedReciprocal.inverse (smallDiskShift z n plus)
    (smallDiskShift_nonzero z (LocalODE.interior_bound _ z hz) n plus)
  domain_congr z w he := by
    constructor
    · rintro ⟨r,hr,hrq,hz⟩
      exact ⟨r,hr,hrq,Small.congr z.property w.property he hz⟩
    · rintro ⟨r,hr,hrq,hw⟩
      exact ⟨r,hr,hrq,Small.congr w.property z.property (equiv_symm he) hw⟩
  eval_congr z w hz hw he := RepresentedReciprocal.inverse_congr _ _ _ _ (smallDiskShift_congr z w he n plus)

def smallDiskShiftMap_holomorphic (n : Nat) (plus : Bool) : DomainFunctions.Holomorphic (smallDiskShiftMap n plus) := by
  have h := ReciprocalHolomorphic.holomorphic.compose
    (affine_holomorphic (smallDiskShiftConstant n plus) ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩)
  apply h.transfer (smallDiskShiftMap n plus)
    (fun z hz => ⟨trivial,(NonzeroBoxSearch.nonzero_congr _ _ (smallDiskShiftAffine_agreement z n plus)).mpr
      (smallDiskShift_nonzero z (LocalODE.interior_bound _ z hz) n plus)⟩)
    ⟨LocalODE.interiorRadius (1/4),LocalODE.interiorRadius_inside (1/4)⟩
  intro z hz
  exact RepresentedReciprocal.inverse_congr _ _ _ _ (smallDiskShiftAffine_agreement z n plus)

def pairedSmallDiskTermMap (n : Nat) : DomainFunctions.Map :=
  sumOn (smallDiskShiftMap n false) (smallDiskShiftMap n true)
    (fun (z : Scalar) (hz : LocalODE.interior (1/4) z) => hz)

def pairedSmallDiskTermMap_holomorphic (n : Nat) : DomainFunctions.Holomorphic (pairedSmallDiskTermMap n) :=
  (smallDiskShiftMap_holomorphic n false).sumOn (smallDiskShiftMap_holomorphic n true)
    (fun (z : Scalar) (hz : LocalODE.interior (1/4) z) => hz)

theorem pairedSmallDiskTermMap_eval (n : Nat) (z : Scalar)
    (hz : (pairedSmallDiskTermMap n).domain z) :
    ((pairedSmallDiskTermMap n).eval z hz).val.Equiv
      (pairedFullTerm z (pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel)
        (LocalODE.interior_bound _ z hz)) n).val := by
  let a := boundaryIntegerScalar (n+1)
  let hm := smallDiskShift_nonzero z (LocalODE.interior_bound _ z hz) n false
  let hp := smallDiskShift_nonzero z (LocalODE.interior_bound _ z hz) n true
  let hd := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ z hz)
  have hi := RepresentedReciprocal.inverse_congr (pairedProduct z a)
    (pairedLiteralDenominator z (pairedIntegerSquare (n+1))) (pairedProduct_nonzero z a hm hp) (hd n)
    (FunctionTheory.sub_congr (equiv_refl _ (mul_valid z.property z.property))
      (rationalRealSquare_equiv ((n+1:Nat):Rat)))
  have hq := mul_equiv (add_valid z.property z.property) (add_valid z.property z.property)
    (RepresentedReciprocal.inverse _ (pairedProduct_nonzero z a hm hp)).property
    (RepresentedReciprocal.inverse _ (hd n)).property (equiv_refl _ (add_valid z.property z.property)) hi
  exact equiv_trans ((pairedSmallDiskTermMap n).eval z hz).property (pairedQuotient z a hm hp).property
    (pairedFullTerm z hd n).property (pairedReciprocal_quotient z a hm hp) hq

end ComputableAnalysis.ModularForms
