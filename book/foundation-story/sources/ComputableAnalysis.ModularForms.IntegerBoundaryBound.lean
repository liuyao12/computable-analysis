import ComputableAnalysis.ModularForms.FactorReciprocalBound
import ComputableAnalysis.ModularForms.PairedUpperDomain

/-! Decaying bounds on the actual reciprocals at positive and negative integer shifts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def boundaryIntegerScalar (n : Nat) : Scalar :=
  ⟨ofQComplex ⟨(n:Rat),0⟩,ofQComplex_valid _⟩

theorem boundaryIntegerScalar_small (n : Nat) :
    Small (boundaryIntegerScalar n).val (n:Rat) := by
  have hn : (0:Rat)≤(n:Rat) := Rat.natCast_nonneg
  refine ⟨?_,?_,?_,?_⟩
  · intro k l; change -(n:Rat)≤(n:Rat); grind only
  · intro k l; exact Rat.le_refl
  · intro k l; change -(n:Rat)≤0; grind only
  · intro k l; exact hn

theorem boundaryPairedInverse_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) :
    Small (RepresentedReciprocal.inverse (pairedProduct z (boundaryIntegerScalar n))
      (pairedProduct_nonzero z (boundaryIntegerScalar n)
        (upperShiftMinus_nonzero z hz (n:Rat)) (upperShiftPlus_nonzero z hz (n:Rat)))).val
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
  let hp := pairedProduct_nonzero z a (upperShiftMinus_nonzero z hz (n:Rat))
    (upperShiftPlus_nonzero z hz (n:Rat))
  exact Small.congr (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare n)) hd).property
    (RepresentedReciprocal.inverse (pairedProduct z a) hp).property
    (RepresentedReciprocal.inverse_congr _ _ hd hp (equiv_symm he)) hi

theorem integerBoundaryMinus_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) :
    Small (RepresentedReciprocal.inverse (pairedMinus z (boundaryIntegerScalar n))
      (upperShiftMinus_nonzero z hz (n:Rat))).val
      (8*(R+(n:Rat))*(1/pairedIntegerSquare n)) := by
  have hc : 0≤1/pairedIntegerSquare n := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (pairedIntegerSquare_pos n hn))
  have h := pairedMinusReciprocal_bound z (boundaryIntegerScalar n)
    (upperShiftMinus_nonzero z hz (n:Rat)) (upperShiftPlus_nonzero z hz (n:Rat))
    R (n:Rat) (4*(1/pairedIntegerSquare n)) hR Rat.natCast_nonneg
    (Rat.mul_nonneg (by decide) hc) hsmall (boundaryIntegerScalar_small n)
    (boundaryPairedInverse_bound z hz R hR hsmall n hn hlarge)
  rw [show (2:Rat)*(R+(n:Rat))*(4*(1/pairedIntegerSquare n))=
    8*(R+(n:Rat))*(1/pairedIntegerSquare n) by grind only] at h
  exact h

theorem integerBoundaryPlus_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R : Rat) (hR : 0≤R) (hsmall : Small z.val R) (n : Nat) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) :
    Small (RepresentedReciprocal.inverse (pairedPlus z (boundaryIntegerScalar n))
      (upperShiftPlus_nonzero z hz (n:Rat))).val
      (8*(R+(n:Rat))*(1/pairedIntegerSquare n)) := by
  have hc : 0≤1/pairedIntegerSquare n := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (pairedIntegerSquare_pos n hn))
  have h := pairedPlusReciprocal_bound z (boundaryIntegerScalar n)
    (upperShiftMinus_nonzero z hz (n:Rat)) (upperShiftPlus_nonzero z hz (n:Rat))
    R (n:Rat) (4*(1/pairedIntegerSquare n)) hR Rat.natCast_nonneg
    (Rat.mul_nonneg (by decide) hc) hsmall (boundaryIntegerScalar_small n)
    (boundaryPairedInverse_bound z hz R hR hsmall n hn hlarge)
  rw [show (2:Rat)*(R+(n:Rat))*(4*(1/pairedIntegerSquare n))=
    8*(R+(n:Rat))*(1/pairedIntegerSquare n) by grind only] at h
  exact h

theorem integerBoundaryRate_le (R : Rat) (n : Nat) (hn : 0<n)
    (hR : R≤(n:Rat)) :
    8*(R+(n:Rat))*(1/pairedIntegerSquare n)≤16*(1/(n:Rat)) := by
  have hp : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  have hs := pairedIntegerSquare_pos n hn
  have hc : 0≤1/pairedIntegerSquare n := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr hs)
  have hm := Rat.mul_le_mul_of_nonneg_right
    (show (8:Rat)*(R+(n:Rat))≤16*(n:Rat) by grind only) hc
  have hi := Rat.mul_inv_cancel (n:Rat) (Rat.ne_of_gt hp)
  have hj := Rat.mul_inv_cancel (pairedIntegerSquare n) (Rat.ne_of_gt hs)
  simp only [pairedIntegerSquare,Rat.div_def,Rat.one_mul] at hm hj ⊢
  have he : (n:Rat)*(n:Rat)*(n:Rat)⁻¹=(n:Rat) := by
    calc
      _ = (n:Rat)*((n:Rat)*(n:Rat)⁻¹) := Rat.mul_assoc _ _ _
      _ = (n:Rat) := by rw [hi,Rat.mul_one]
  have he3 : (n:Rat)*(n:Rat)*(n:Rat)⁻¹*((n:Rat)*(n:Rat))⁻¹=(n:Rat)*((n:Rat)*(n:Rat))⁻¹ := by rw [he]
  have hk' : (n:Rat)*((n:Rat)*(n:Rat))⁻¹=(n:Rat)⁻¹ := by
    calc
      _ = ((n:Rat)*(n:Rat)*(n:Rat)⁻¹)*((n:Rat)*(n:Rat))⁻¹ := he3.symm
      _ = ((n:Rat)*(n:Rat)*((n:Rat)*(n:Rat))⁻¹)*(n:Rat)⁻¹ := by grind only
      _ = (n:Rat)⁻¹ := by rw [hj,Rat.one_mul]
  have hm' : (16:Rat)*(n:Rat)*((n:Rat)*(n:Rat))⁻¹=16*(n:Rat)⁻¹ := by
    rw [Rat.mul_assoc,hk']
  rw [hm'] at hm
  exact hm

end ComputableAnalysis.ModularForms
