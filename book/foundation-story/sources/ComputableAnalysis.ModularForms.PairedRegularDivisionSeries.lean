import ComputableAnalysis.ModularForms.PairedSmallDiskDerivative

/-! A convergent series for the regular part divided by its argument. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedRegularDivisionTerm (z : Scalar) (hz : Small z.val (1/4)) (n : Nat) : Scalar :=
  let hd := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz
  let i := RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare (n+1))) (hd n)
  ⟨scaleRat 2 i.val,scaleRat_valid i.property⟩

theorem pairedRegularDivisionTerm_bound (z : Scalar) (hz : Small z.val (1/4)) (n : Nat) :
    Small (pairedRegularDivisionTerm z hz n).val (8*reciprocalSquare (n+1)) := by
  have hp : (1:Rat)≤((n+1:Nat):Rat) := by exact_mod_cast (show 1≤n+1 by omega)
  have hsq := Rat.mul_le_mul_of_nonneg_left hp (Rat.natCast_nonneg (a := n+1))
  have hl : 16*(1/4:Rat)*(1/4)≤pairedIntegerSquare (n+1) := by
    unfold pairedIntegerSquare; grind only
  let hd := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz
  have hc : 0≤1/pairedIntegerSquare (n+1) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (pairedIntegerSquare_pos _ (by omega)))
  have ht : pairedIntegerSquare (n+1)*(1/pairedIntegerSquare (n+1))=1 := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (pairedIntegerSquare_pos _ (by omega)))
  have hb := pairedLiteralInverse_bound z (1/4) (1/pairedIntegerSquare (n+1)) (pairedIntegerSquare (n+1))
    (by decide +kernel) hc hz (pairedInteger_normalization (1/4) (n+1) (by omega) hl) ht (hd n)
  have hs := LocalODE.small_scale (show (0:Rat)≤2 by decide) hb
  rw [show (2:Rat)*(4*(1/pairedIntegerSquare (n+1)))=8*(1/pairedIntegerSquare (n+1)) by grind only] at hs
  simpa only [pairedRegularDivisionTerm,reciprocalSquare,pairedIntegerSquare,Rat.div_def,Rat.one_mul] using hs

def pairedRegularDivisionValue (z : Scalar) (hz : Small z.val (1/4)) : ComplexRaw :=
  inverseSquareSeriesValue (fun n => (pairedRegularDivisionTerm z hz n).val)
    (fun n => (pairedRegularDivisionTerm z hz n).property) 8

theorem pairedRegularDivisionValue_valid (z : Scalar) (hz : Small z.val (1/4)) :
    (pairedRegularDivisionValue z hz).Valid :=
  inverseSquareSeriesValue_valid _ _ 8 (pairedRegularDivisionTerm_bound z hz)

theorem pairedRegularDivisionValue_close (z : Scalar) (hz : Small z.val (1/4)) (N : Nat) :
    Small (sub (pairedRegularDivisionValue z hz)
      (ScalarSeries.block (fun n => (pairedRegularDivisionTerm z hz n).val) 0 (N+1)))
      (8*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close _ _ 8 (pairedRegularDivisionTerm_bound z hz) N

theorem pairedRegularDivisionTerm_product (z : Scalar) (hz : Small z.val (1/4)) (n : Nat) :
    (mul z.val (pairedRegularDivisionTerm z hz n).val).Equiv
      (pairedFullTerm z (pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz) n).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid z.property (pairedRegularDivisionTerm z hz n).property)
    (hright := (pairedFullTerm z (pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz) n).property)
  let hd := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse
    (pairedLiteralDenominator z (pairedIntegerSquare (n+1))) (hd n)).val
    (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare (n+1))) (hd n)).property
  change Z*ComplexRawQuotient.scaleRat 2 I = (Z+Z)*I
  rw [ComplexRawQuotient.mul_scaleRat,ComplexRawQuotient.scaleRat_mul]
  have htwo : ComplexRawQuotient.scaleRat 2 Z=Z+Z := by
    have h := ComplexRawQuotient.add_scaleRat 1 1 Z
    rw [ComplexRawQuotient.scaleRat_one] at h
    simpa only [show (1:Rat)+1=2 by decide +kernel] using h.symm
  rw [htwo]

end ComputableAnalysis.ModularForms
