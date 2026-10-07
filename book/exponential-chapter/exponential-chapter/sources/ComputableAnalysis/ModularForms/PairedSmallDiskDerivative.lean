import ComputableAnalysis.ModularForms.PairedSmallDiskHolomorphic

/-! Summable bounds and a represented derivative series for the regular part at zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedProductInverse_bound_of_factors (z : Scalar)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n)
    (hm : NonzeroBoxSearch.Nonzero (pairedMinus z (boundaryIntegerScalar n)))
    (hp : NonzeroBoxSearch.Nonzero (pairedPlus z (boundaryIntegerScalar n))) :
    Small (RepresentedReciprocal.inverse (pairedProduct z (boundaryIntegerScalar n))
      (pairedProduct_nonzero z (boundaryIntegerScalar n)
        hm hp)).val
      (4*(1/pairedIntegerSquare n)) := by
  let a := boundaryIntegerScalar n
  have he : (pairedProduct z a).val.Equiv
      (pairedLiteralDenominator z (pairedIntegerSquare n)).val :=
    FunctionTheory.sub_congr (equiv_refl _ (mul_valid z.property z.property))
      (rationalRealSquare_equiv (n:Rat))
  have hd := pairedIntegerDenominator_nonzero z R n hR hsmall hn hlarge
  have hc : 0≤1/pairedIntegerSquare n := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (pairedIntegerSquare_pos n hn))
  have hct : pairedIntegerSquare n*(1/pairedIntegerSquare n)=1 := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (pairedIntegerSquare_pos n hn))
  have hi := pairedLiteralInverse_bound z R (1/pairedIntegerSquare n) (pairedIntegerSquare n)
    hR hc hsmall (pairedInteger_normalization R n hn hlarge) hct hd
  let hprod := pairedProduct_nonzero z a hm
    hp
  exact Small.congr (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare n)) hd).property
    (RepresentedReciprocal.inverse (pairedProduct z a) hprod).property
    (RepresentedReciprocal.inverse_congr _ _ hd hprod (equiv_symm he)) hi

private theorem smallDiskInteger_large (n : Nat) :
    16*(1/4:Rat)*(1/4)≤pairedIntegerSquare (n+1) := by
  have hp : (1:Rat)≤((n+1:Nat):Rat) := by exact_mod_cast (show 1≤n+1 by omega)
  have h1 := Rat.mul_le_mul_of_nonneg_right hp (show (0:Rat)≤1 by decide)
  have h2 := Rat.mul_le_mul_of_nonneg_left hp (Rat.natCast_nonneg (a := n+1))
  unfold pairedIntegerSquare
  grind only

theorem smallDiskShiftInverse_bound (z : Scalar) (hz : Small z.val (1/4))
    (n : Nat) (plus : Bool) :
    Small (RepresentedReciprocal.inverse (smallDiskShift z n plus)
      (smallDiskShift_nonzero z hz n plus)).val (16*(1/((n+1:Nat):Rat))) := by
  have hm := (pairedSmallDisk_factors z hz n).1
  have hp := (pairedSmallDisk_factors z hz n).2
  have hi := pairedProductInverse_bound_of_factors z (1/4) (by decide +kernel) hz
    (n+1) (by omega) (smallDiskInteger_large n) hm hp
  have hc : 0≤4*(1/pairedIntegerSquare (n+1)) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt
      (Rat.inv_pos.mpr (pairedIntegerSquare_pos (n+1) (by omega))))
  have hRn : (1/4:Rat)≤((n+1:Nat):Rat) := by
    have h : (1:Rat)≤((n+1:Nat):Rat) := by exact_mod_cast (show 1≤n+1 by omega)
    grind only
  have hb : 2*((1/4:Rat)+((n+1:Nat):Rat))*(4*(1/pairedIntegerSquare (n+1)))≤
      16*(1/((n+1:Nat):Rat)) := by
    have h := integerBoundaryRate_le (1/4) (n+1) (by omega) hRn
    grind only
  cases plus with
  | false => exact (pairedMinusReciprocal_bound z (boundaryIntegerScalar (n+1)) hm hp
      (1/4) ((n+1:Nat):Rat) (4*(1/pairedIntegerSquare (n+1)))
      (by decide +kernel) Rat.natCast_nonneg hc hz (boundaryIntegerScalar_small _) hi).mono hb
  | true => exact (pairedPlusReciprocal_bound z (boundaryIntegerScalar (n+1)) hm hp
      (1/4) ((n+1:Nat):Rat) (4*(1/pairedIntegerSquare (n+1)))
      (by decide +kernel) Rat.natCast_nonneg hc hz (boundaryIntegerScalar_small _) hi).mono hb

def pairedSmallDiskDerivativeTerm (z : Scalar) (hz : Small z.val (1/4)) (n : Nat) : Scalar :=
  DomainFunctions.scalarSum
    (ReciprocalDifference.derivative (smallDiskShift z n false) (smallDiskShift_nonzero z hz n false))
    (ReciprocalDifference.derivative (smallDiskShift z n true) (smallDiskShift_nonzero z hz n true))

theorem pairedSmallDiskDerivativeTerm_bound (z : Scalar) (hz : Small z.val (1/4)) (n : Nat) :
    Small (pairedSmallDiskDerivativeTerm z hz n).val (1024*reciprocalSquare (n+1)) := by
  let I := RepresentedReciprocal.inverse (smallDiskShift z n false) (smallDiskShift_nonzero z hz n false)
  let J := RepresentedReciprocal.inverse (smallDiskShift z n true) (smallDiskShift_nonzero z hz n true)
  have hM : 0≤16*(1/((n+1:Nat):Rat)) := by
    have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  have hm := smallDiskShiftInverse_bound z hz n false
  have hp := smallDiskShiftInverse_bound z hz n true
  have h := LocalODE.small_add
    (SeriesLimitLaws.small_neg (Small.mul I.property I.property hM hM hm hm))
    (SeriesLimitLaws.small_neg (Small.mul J.property J.property hM hM hp hp))
  apply h.mono
  rw [pairedDerivative_reciprocalSquare_eq_inverse_product (n+1) (by omega),Rat.div_def,Rat.one_mul]
  grind only

theorem pairedSmallDiskDerivativeTerm_congr (z w : Scalar)
    (hz : Small z.val (1/4)) (hw : Small w.val (1/4)) (he : z.val.Equiv w.val) (n : Nat) :
    (pairedSmallDiskDerivativeTerm z hz n).val.Equiv (pairedSmallDiskDerivativeTerm w hw n).val :=
  add_equiv
    (ReciprocalDifference.derivative_congr _ _ _ _ (smallDiskShift_congr z w he n false))
    (ReciprocalDifference.derivative_congr _ _ _ _ (smallDiskShift_congr z w he n true))

theorem smallDiskShiftMap_derivative (n : Nat) (plus : Bool) (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    ((smallDiskShiftMap_holomorphic n plus).derivative z hz).val.Equiv
      (ReciprocalDifference.derivative (smallDiskShift z n plus)
        (smallDiskShift_nonzero z (LocalODE.interior_bound _ z hz) n plus)).val := by
  let ha := (NonzeroBoxSearch.nonzero_congr _ _ (smallDiskShiftAffine_agreement z n plus)).mpr
    (smallDiskShift_nonzero z (LocalODE.interior_bound _ z hz) n plus)
  let I := RepresentedReciprocal.inverse ((smallDiskShiftAffine n plus).eval z trivial) ha
  let J := RepresentedReciprocal.inverse (smallDiskShift z n plus)
    (smallDiskShift_nonzero z (LocalODE.interior_bound _ z hz) n plus)
  have hi := RepresentedReciprocal.inverse_congr _ _ ha
    (smallDiskShift_nonzero z (LocalODE.interior_bound _ z hz) n plus)
    (smallDiskShiftAffine_agreement z n plus)
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := I.property) (hright := J.property) hi
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((smallDiskShiftMap_holomorphic n plus).derivative z hz).property)
    (hright := (ReciprocalDifference.derivative (smallDiskShift z n plus)
      (smallDiskShift_nonzero z (LocalODE.interior_bound _ z hz) n plus)).property)
  let U := ComplexRawQuotient.ofRaw I.val I.property
  let V := ComplexRawQuotient.ofRaw J.val J.property
  change U=V at hq
  change (-(U*U))*1= -(V*V)
  grind only

theorem pairedSmallDiskTermMap_derivative (n : Nat) (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    ((pairedSmallDiskTermMap_holomorphic n).derivative z hz).val.Equiv
      (pairedSmallDiskDerivativeTerm z (LocalODE.interior_bound _ z hz) n).val :=
  add_equiv (smallDiskShiftMap_derivative n false z hz) (smallDiskShiftMap_derivative n true z hz)

def pairedSmallDiskTermMap_hasDerivativeAt (n : Nat) (z : Scalar)
    (hz : LocalODE.interior (1/4) z) : DomainFunctions.HasDerivativeAt (pairedSmallDiskTermMap n) z hz
      (pairedSmallDiskDerivativeTerm z (LocalODE.interior_bound _ z hz) n) :=
  ((pairedSmallDiskTermMap_holomorphic n).atPoint z hz).congrDerivative
    (pairedSmallDiskTermMap_derivative n z hz)

def pairedSmallDiskDerivativeValue (z : Scalar) (hz : Small z.val (1/4)) : ComplexRaw :=
  inverseSquareSeriesValue (fun n => (pairedSmallDiskDerivativeTerm z hz n).val)
    (fun n => (pairedSmallDiskDerivativeTerm z hz n).property) 1024

theorem pairedSmallDiskDerivativeValue_valid (z : Scalar) (hz : Small z.val (1/4)) :
    (pairedSmallDiskDerivativeValue z hz).Valid :=
  inverseSquareSeriesValue_valid _ _ 1024 (pairedSmallDiskDerivativeTerm_bound z hz)

theorem pairedSmallDiskDerivativeValue_close (z : Scalar) (hz : Small z.val (1/4)) (N : Nat) :
    Small (sub (pairedSmallDiskDerivativeValue z hz)
      (ScalarSeries.block (fun n => (pairedSmallDiskDerivativeTerm z hz n).val) 0 (N+1)))
      (((1024:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) :=
  inverseSquareSeriesValue_close _ _ 1024 (pairedSmallDiskDerivativeTerm_bound z hz) N

theorem pairedSmallDiskDerivativeValue_congr (z w : Scalar)
    (hz : Small z.val (1/4)) (hw : Small w.val (1/4)) (he : z.val.Equiv w.val) :
    (pairedSmallDiskDerivativeValue z hz).Equiv (pairedSmallDiskDerivativeValue w hw) :=
  inverseSquareSeriesValue_congr _ _ _ _ 1024
    (pairedSmallDiskDerivativeTerm_bound z hz) (pairedSmallDiskDerivativeTerm_bound w hw)
    (pairedSmallDiskDerivativeTerm_congr z w hz hw he)

end ComputableAnalysis.ModularForms
