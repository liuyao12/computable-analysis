import ComputableAnalysis.ModularForms.PairedGlobalOffPolePrefixes

/-! Decaying boundary reciprocals on the full pole-excluded domain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory NonzeroBoxSearch

theorem globalBoundaryMinus_nonzero (z : Scalar) (hz : pairedOffPoleDomain z) (n : Nat) :
    Nonzero (pairedMinus z (boundaryIntegerScalar n)) :=
  (nonzero_congr _ _ (integerShiftScalar_minus z n)).mp
    (pairedOffPoleDomain_integer_nonzero z hz (-(n:Int)))

theorem globalBoundaryPlus_nonzero (z : Scalar) (hz : pairedOffPoleDomain z) (n : Nat) :
    Nonzero (pairedPlus z (boundaryIntegerScalar n)) :=
  (nonzero_congr _ _ (integerShiftScalar_plus z n)).mp
    (pairedOffPoleDomain_integer_nonzero z hz (n:Int))

theorem globalBoundaryPairedInverse_bound (z : Scalar) (hz : pairedOffPoleDomain z)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) :
    Small (RepresentedReciprocal.inverse (pairedProduct z (boundaryIntegerScalar n))
      (pairedProduct_nonzero z (boundaryIntegerScalar n)
        (globalBoundaryMinus_nonzero z hz n) (globalBoundaryPlus_nonzero z hz n))).val
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
  let hp := pairedProduct_nonzero z a (globalBoundaryMinus_nonzero z hz n)
    (globalBoundaryPlus_nonzero z hz n)
  exact Small.congr (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare n)) hd).property
    (RepresentedReciprocal.inverse (pairedProduct z a) hp).property
    (RepresentedReciprocal.inverse_congr _ _ hd hp (equiv_symm he)) hi

theorem globalIntegerBoundaryMinus_bound (z : Scalar) (hz : pairedOffPoleDomain z)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) :
    Small (RepresentedReciprocal.inverse (pairedMinus z (boundaryIntegerScalar n))
      (globalBoundaryMinus_nonzero z hz n)).val
      (8*(R+(n:Rat))*(1/pairedIntegerSquare n)) := by
  have hc : 0≤1/pairedIntegerSquare n := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (pairedIntegerSquare_pos n hn))
  have h := pairedMinusReciprocal_bound z (boundaryIntegerScalar n)
    (globalBoundaryMinus_nonzero z hz n) (globalBoundaryPlus_nonzero z hz n)
    R (n:Rat) (4*(1/pairedIntegerSquare n)) hR Rat.natCast_nonneg
    (Rat.mul_nonneg (by decide) hc) hsmall (boundaryIntegerScalar_small n)
    (globalBoundaryPairedInverse_bound z hz R hR hsmall n hn hlarge)
  rw [show (2:Rat)*(R+(n:Rat))*(4*(1/pairedIntegerSquare n))=
    8*(R+(n:Rat))*(1/pairedIntegerSquare n) by grind only] at h
  exact h

theorem globalIntegerBoundaryPlus_bound (z : Scalar) (hz : pairedOffPoleDomain z)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) :
    Small (RepresentedReciprocal.inverse (pairedPlus z (boundaryIntegerScalar n))
      (globalBoundaryPlus_nonzero z hz n)).val
      (8*(R+(n:Rat))*(1/pairedIntegerSquare n)) := by
  have hc : 0≤1/pairedIntegerSquare n := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (pairedIntegerSquare_pos n hn))
  have h := pairedPlusReciprocal_bound z (boundaryIntegerScalar n)
    (globalBoundaryMinus_nonzero z hz n) (globalBoundaryPlus_nonzero z hz n)
    R (n:Rat) (4*(1/pairedIntegerSquare n)) hR Rat.natCast_nonneg
    (Rat.mul_nonneg (by decide) hc) hsmall (boundaryIntegerScalar_small n)
    (globalBoundaryPairedInverse_bound z hz R hR hsmall n hn hlarge)
  rw [show (2:Rat)*(R+(n:Rat))*(4*(1/pairedIntegerSquare n))=
    8*(R+(n:Rat))*(1/pairedIntegerSquare n) by grind only] at h
  exact h

theorem globalOffPoleIntegerReciprocal_plus_bound (z : Scalar) (hz : pairedOffPoleDomain z)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) (hRn : R≤(n:Rat)) :
    Small (globalOffPoleIntegerReciprocal z hz (n:Int)).val (16*(1/(n:Rat))) := by
  have he := RepresentedReciprocal.inverse_congr
    (pairedPlus z (boundaryIntegerScalar n)) (integerShiftScalar z (n:Int))
    (globalBoundaryPlus_nonzero z hz n) (pairedOffPoleDomain_integer_nonzero z hz (n:Int))
    (equiv_symm (integerShiftScalar_plus z n))
  exact Small.congr (RepresentedReciprocal.inverse (pairedPlus z (boundaryIntegerScalar n))
    (globalBoundaryPlus_nonzero z hz n)).property (globalOffPoleIntegerReciprocal z hz (n:Int)).property he
    ((globalIntegerBoundaryPlus_bound z hz R hR hsmall n hn hlarge).mono (integerBoundaryRate_le R n hn hRn))

theorem globalOffPoleIntegerReciprocal_minus_bound (z : Scalar) (hz : pairedOffPoleDomain z)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) (hRn : R≤(n:Rat)) :
    Small (globalOffPoleIntegerReciprocal z hz (-(n:Int))).val (16*(1/(n:Rat))) := by
  have he := RepresentedReciprocal.inverse_congr
    (pairedMinus z (boundaryIntegerScalar n)) (integerShiftScalar z (-(n:Int)))
    (globalBoundaryMinus_nonzero z hz n) (pairedOffPoleDomain_integer_nonzero z hz (-(n:Int)))
    (equiv_symm (integerShiftScalar_minus z n))
  exact Small.congr (RepresentedReciprocal.inverse (pairedMinus z (boundaryIntegerScalar n))
    (globalBoundaryMinus_nonzero z hz n)).property (globalOffPoleIntegerReciprocal z hz (-(n:Int))).property he
    ((globalIntegerBoundaryMinus_bound z hz R hR hsmall n hn hlarge).mono (integerBoundaryRate_le R n hn hRn))

end ComputableAnalysis.ModularForms
