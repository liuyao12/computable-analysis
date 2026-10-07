import ComputableAnalysis.ModularForms.PairedDerivativePeriodicity

/-! The actual regular part of the reciprocal series near its zero pole. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedSmallDisk_domain (z : Scalar) (R : Rat) (hR : 0≤R) (hRmax : R≤(1:Rat)/4)
    (hz : Small z.val R) : PairedSeriesDomain z := by
  intro n
  have hn : 0<n+1 := by omega
  have hp : (1:Rat)≤((n+1:Nat):Rat) := by exact_mod_cast (show 1≤n+1 by omega)
  have h1 := Rat.mul_le_mul_of_nonneg_right hp (show (0:Rat)≤1 by decide)
  have h2 := Rat.mul_le_mul_of_nonneg_left hp (Rat.natCast_nonneg (a := n+1))
  have hR2 := Rat.mul_le_mul_of_nonneg_right hRmax hR
  have hR3 := Rat.mul_le_mul_of_nonneg_left hRmax (show (0:Rat)≤1/4 by decide +kernel)
  have hlarge : 16*R*R≤pairedIntegerSquare (n+1) := by unfold pairedIntegerSquare; grind only
  exact pairedIntegerDenominator_nonzero z R (n+1) hR hz hn hlarge

theorem pairedSmallDisk_term_bound (z : Scalar) (R : Rat) (hR : 0≤R) (hRmax : R≤(1:Rat)/4)
    (hz : Small z.val R) (n : Nat) :
    Small (pairedFullTerm z (pairedSmallDisk_domain z R hR hRmax hz) n).val
      (16*R*reciprocalSquare (n+1)) := by
  have hn : 0<n+1 := by omega
  have hp : (1:Rat)≤((n+1:Nat):Rat) := by exact_mod_cast (show 1≤n+1 by omega)
  have h1 := Rat.mul_le_mul_of_nonneg_right hp (show (0:Rat)≤1 by decide)
  have h2 := Rat.mul_le_mul_of_nonneg_left hp (Rat.natCast_nonneg (a := n+1))
  have hR2 := Rat.mul_le_mul_of_nonneg_right hRmax hR
  have hR3 := Rat.mul_le_mul_of_nonneg_left hRmax (show (0:Rat)≤1/4 by decide +kernel)
  have hlarge : 16*R*R≤pairedIntegerSquare (n+1) := by unfold pairedIntegerSquare; grind only
  have h := pairedIntegerQuotient_bound z R (n+1) hR hz hn hlarge (pairedSmallDisk_domain z R hR hRmax hz n)
  simpa only [pairedFullTerm,reciprocalSquare,pairedIntegerSquare,Rat.div_def,Rat.one_mul] using h

private theorem regularSquareBlock_split (k : Nat) : reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem regularSquareBlock_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [regularSquareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only

theorem pairedSmallDisk_prefix_bound (z : Scalar) (R : Rat) (hR : 0≤R) (hRmax : R≤(1:Rat)/4)
    (hz : Small z.val R) (k : Nat) :
    Small (ScalarSeries.block (fun n => (pairedFullTerm z (pairedSmallDisk_domain z R hR hRmax hz) n).val) 0 k)
      (32*R) := by
  have hb (k : Nat) :
      Small (ScalarSeries.block (fun n => (pairedFullTerm z (pairedSmallDisk_domain z R hR hRmax hz) n).val) 0 k)
        (16*R*reciprocalSquareBlock 0 k) := by
    induction k with
    | zero => exact Small.zero (by simp only [reciprocalSquareBlock,Rat.mul_zero]; decide)
    | succ k ih =>
      simp only [ScalarSeries.block.eq_2,Nat.zero_add]
      have h := LocalODE.small_add ih (pairedSmallDisk_term_bound z R hR hRmax hz k)
      apply h.mono
      rw [reciprocalSquareBlock]
      simp only [Nat.zero_add]
      grind only
  apply (hb k).mono
  have h := Rat.mul_le_mul_of_nonneg_left (regularSquareBlock_bound k)
    (Rat.mul_nonneg (show (0:Rat)≤16 by decide) hR)
  grind only

def pairedRegularPart (z : Scalar) (hz : Small z.val (1/4)) : ComplexRaw :=
  pairedSeriesValue z (pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz)

theorem pairedRegularPart_valid (z : Scalar) (hz : Small z.val (1/4)) : (pairedRegularPart z hz).Valid :=
  pairedSeriesValue_valid _ _

theorem pairedRegularPart_bound (z : Scalar) (hz : Small z.val (1/4))
    (R : Rat) (hR : 0≤R) (hRmax : R≤(1:Rat)/4) (hsmall : Small z.val R) :
    Small (pairedRegularPart z hz) (32*R) := by
  let hd := pairedSmallDisk_domain z R hR hRmax hsmall
  let B := pairedInternalBound z
  let p := fun N => ScalarSeries.block (fun n => (pairedFullTerm z hd n).val) 0 (4*B+(N+1))
  have hp (N : Nat) : (p N).Valid := ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hd n).property) 0 _
  apply SeriesLimitLaws.small_of_prefix_bound _ (pairedRegularPart_valid z hz) p hp (32*R)
    (fun N => ((16*B:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) (pairedReciprocalTail_shrinks (16*B))
  · intro N
    exact pairedFullValue_close z hd B (pairedInternalBound_small z) N
  · intro N
    exact pairedSmallDisk_prefix_bound z R hR hRmax hsmall _

theorem pairedRegularPart_congr (z w : Scalar) (hz : Small z.val (1/4)) (hw : Small w.val (1/4))
    (he : z.val.Equiv w.val) : (pairedRegularPart z hz).Equiv (pairedRegularPart w hw) :=
  pairedSeriesValue_congr _ _ _ _ he

theorem pairedRegularPart_zero (z : Scalar) (hz : Small z.val (1/4)) (hzero : z.val.Equiv zero) :
    (pairedRegularPart z hz).Equiv zero := by
  have hz0 := Small.congr (ofQComplex_valid _) z.property (equiv_symm hzero)
    (Small.zero (show (0:Rat)≤0 by decide))
  have h := pairedRegularPart_bound z hz 0 (by decide) (by decide +kernel) hz0
  have h0 : Small (pairedRegularPart z hz) 0 := by simpa only [Rat.mul_zero] using h
  have he : (sub (pairedRegularPart z hz) zero).Equiv (pairedRegularPart z hz) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedRegularPart_valid z hz) (ofQComplex_valid _))
      (hright := pairedRegularPart_valid z hz)
    let S := ComplexRawQuotient.ofRaw (pairedRegularPart z hz) (pairedRegularPart_valid z hz)
    change S-0=S
    grind only
  exact SeriesLimitLaws.equiv_of_small_sub_zero _ _
    (Small.congr (pairedRegularPart_valid z hz)
      (sub_valid (pairedRegularPart_valid z hz) (ofQComplex_valid _)) (equiv_symm he) h0)

theorem pairedRegularPart_upper_identity (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hsmall : Small z.val (1/4)) :
    (sub (upperPairedPartialFractionValue z hz)
      (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).val).Equiv
      (pairedRegularPart z hsmall) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (upperPairedPartialFractionValue_valid z hz)
      (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).property)
    (hright := pairedRegularPart_valid z hsmall)
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).val
    (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPart z hsmall) (pairedRegularPart_valid z hsmall)
  change (I+S)-I=S
  grind only

theorem pairedZeroPole_normalization (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hsmall : Small z.val (1/4)) :
    (sub (mul z.val (upperPairedPartialFractionValue z hz)) (ofQComplex QComplex.one)).Equiv
      (mul z.val (pairedRegularPart z hsmall)) := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse z (upperScalar_nonzero z hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (mul_valid z.property (upperPairedPartialFractionValue_valid z hz)) (ofQComplex_valid _))
    (hright := mul_valid z.property (pairedRegularPart_valid z hsmall))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).val
    (RepresentedReciprocal.inverse z (upperScalar_nonzero z hz)).property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPart z hsmall) (pairedRegularPart_valid z hsmall)
  change Z*I=1 at hi
  change Z*(I+S)-1=Z*S
  grind only

theorem pairedZeroPole_normalization_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R : Rat) (hR : 0≤R) (hRmax : R≤(1:Rat)/4) (hsmall : Small z.val R) :
    Small (sub (mul z.val (upperPairedPartialFractionValue z hz)) (ofQComplex QComplex.one)) (64*R*R) := by
  have hquarter := hsmall.mono hRmax
  have h := Small.mul z.property (pairedRegularPart_valid z hquarter) hR
    (Rat.mul_nonneg (show (0:Rat)≤32 by decide) hR) hsmall
    (pairedRegularPart_bound z hquarter R hR hRmax hsmall)
  have hb := h.mono (show (2:Rat)*R*(32*R)≤64*R*R by grind only)
  exact Small.congr (mul_valid z.property (pairedRegularPart_valid z hquarter))
    (sub_valid (mul_valid z.property (upperPairedPartialFractionValue_valid z hz)) (ofQComplex_valid _))
    (equiv_symm (pairedZeroPole_normalization z hz hquarter)) hb

end ComputableAnalysis.ModularForms
