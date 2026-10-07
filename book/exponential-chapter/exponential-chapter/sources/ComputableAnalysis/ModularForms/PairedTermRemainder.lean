import ComputableAnalysis.ModularForms.PairedReciprocalTermHolomorphic
import ComputableAnalysis.ModularForms.UpperReciprocalRemainder

/-! Uniform quadratic remainder bounds for actual paired reciprocal maps. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerReciprocalMap_remainder_bound (k : Int) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (M H : Rat) (hM : 0≤M) (hH : 0≤H)
    (hIa : Small (upperIntegerReciprocal a ha k).val M)
    (hIz : Small (upperIntegerReciprocal z hz k).val M)
    (hd : Small (sub z.val a.val) H) :
    Small (remainder (integerReciprocalMap k) a ha
      ((integerReciprocalMap_holomorphic k).derivative a ha) z hz) (64*M*M*M*H*H) := by
  have hu : (⟨k,1⟩ : QuadraticOrder163)≠QuadraticOrder163.zero := by
    intro he
    have hy := congrArg QuadraticOrder163.y he
    change (1:Int)=0 at hy
    omega
  have hone : Small (ofQComplex ⟨(1:Rat),0⟩) 1 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro n m; change (-1:Rat)≤1; decide +kernel
    · intro n m; change (1:Rat)≤1; decide +kernel
    · intro n m; change (-1:Rat)≤0; decide +kernel
    · intro n m; change (0:Rat)≤1; decide +kernel
  have h := latticeReciprocal_remainder_bound (⟨k,1⟩ : QuadraticOrder163) hu a z ha hz
    M 1 H hM (by decide +kernel) hH hIa hIz hone hd
  simpa only [integerReciprocalMap,integerReciprocalMap_holomorphic,Rat.mul_one] using h

theorem pairedReciprocalTermMap_remainder_uniform (n : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (M H : Rat) (hM : 0≤M) (hH : 0≤H)
    (hAm : Small (upperIntegerReciprocal a ha (-((n+1:Nat):Int))).val M)
    (hAp : Small (upperIntegerReciprocal a ha ((n+1:Nat):Int)).val M)
    (hZm : Small (upperIntegerReciprocal z hz (-((n+1:Nat):Int))).val M)
    (hZp : Small (upperIntegerReciprocal z hz ((n+1:Nat):Int)).val M)
    (hd : Small (sub z.val a.val) H) :
    Small (remainder (pairedReciprocalTermMap n) a ha
      (upperPairedReciprocalDerivative a ha (n+1)) z hz) (128*M*M*M*H*H) := by
  have hm := integerReciprocalMap_remainder_bound (-((n+1:Nat):Int)) a z ha hz M H hM hH hAm hZm hd
  have hp := integerReciprocalMap_remainder_bound ((n+1:Nat):Int) a z ha hz M H hM hH hAp hZp hd
  have h := (LocalODE.small_add hm hp).mono
    (show (64:Rat)*M*M*M*H*H+64*M*M*M*H*H≤128*M*M*M*H*H by grind only)
  have he := sum_remainder (integerReciprocalMap (-((n+1:Nat):Int)))
    (integerReciprocalMap ((n+1:Nat):Int))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz) a ha
    ((integerReciprocalMap_holomorphic (-((n+1:Nat):Int))).derivative a ha)
    ((integerReciprocalMap_holomorphic ((n+1:Nat):Int)).derivative a ha) z hz
  have vm := DomainFunctions.remainder_valid (integerReciprocalMap (-((n+1:Nat):Int))) a ha
    ((integerReciprocalMap_holomorphic (-((n+1:Nat):Int))).derivative a ha) z hz
  have vp := DomainFunctions.remainder_valid (integerReciprocalMap ((n+1:Nat):Int)) a ha
    ((integerReciprocalMap_holomorphic ((n+1:Nat):Int)).derivative a ha) z hz
  have h0 := Small.congr (add_valid vm vp)
    (DomainFunctions.remainder_valid (pairedReciprocalTermMap n) a ha
      ((pairedReciprocalTermMap_holomorphic n).derivative a ha) z hz) (equiv_symm he) h
  have heD := pairedReciprocalTermMap_derivative n a ha
  have heR : (DomainFunctions.remainder (pairedReciprocalTermMap n) a ha
      ((pairedReciprocalTermMap_holomorphic n).derivative a ha) z hz).Equiv
      (DomainFunctions.remainder (pairedReciprocalTermMap n) a ha
        (upperPairedReciprocalDerivative a ha (n+1)) z hz) := FunctionTheory.sub_congr
    (equiv_refl _ (sub_valid ((pairedReciprocalTermMap n).eval z hz).property
      ((pairedReciprocalTermMap n).eval a ha).property))
    (mul_equiv ((pairedReciprocalTermMap_holomorphic n).derivative a ha).property
      (upperPairedReciprocalDerivative a ha (n+1)).property
      (sub_valid z.property a.property) (sub_valid z.property a.property) heD
      (equiv_refl _ (sub_valid z.property a.property)))
  have h1 := Small.congr (DomainFunctions.remainder_valid (pairedReciprocalTermMap n) a ha
      ((pairedReciprocalTermMap_holomorphic n).derivative a ha) z hz)
    (DomainFunctions.remainder_valid (pairedReciprocalTermMap n) a ha
      (upperPairedReciprocalDerivative a ha (n+1)) z hz) heR h0
  exact h1

theorem pairedReciprocalTermMap_remainder_large (n : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R H : Rat) (hR : 0≤R) (hH : 0≤H)
    (hA : Small a.val R) (hZ : Small z.val R)
    (hlarge : 16*R*R≤pairedIntegerSquare (n+1)) (hRn : R≤((n+1:Nat):Rat))
    (hd : Small (sub z.val a.val) H) :
    Small (remainder (pairedReciprocalTermMap n) a ha
      (upperPairedReciprocalDerivative a ha (n+1)) z hz)
      (524288*reciprocalSquare (n+1)*H*H) := by
  have hn : 0<n+1 := by omega
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast hn
  have hi0 : 0≤(((n+1:Nat):Rat))⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hM : 0≤16*(1/((n+1:Nat):Rat)) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) hi0
  have h := pairedReciprocalTermMap_remainder_uniform n a z ha hz
    (16*(1/((n+1:Nat):Rat))) H hM hH
    (upperIntegerReciprocal_minus_bound a ha R hR hA (n+1) hn hlarge hRn)
    (upperIntegerReciprocal_plus_bound a ha R hR hA (n+1) hn hlarge hRn)
    (upperIntegerReciprocal_minus_bound z hz R hR hZ (n+1) hn hlarge hRn)
    (upperIntegerReciprocal_plus_bound z hz R hR hZ (n+1) hn hlarge hRn) hd
  apply h.mono
  have he := Rat.mul_inv_cancel (((n+1:Nat):Rat)) (Rat.ne_of_gt hp)
  have hn1 : (1:Rat)≤((n+1:Nat):Rat) := by exact_mod_cast (show 1≤n+1 by omega)
  have hi1 : (((n+1:Nat):Rat))⁻¹≤1 := by
    have hm := Rat.mul_le_mul_of_nonneg_right hn1 hi0
    rw [Rat.one_mul,he] at hm
    exact hm
  let i := (((n+1:Nat):Rat))⁻¹
  have his : 0≤i*i := Rat.mul_nonneg hi0 hi0
  have hic : i*i*i≤i*i := by
    have hm := Rat.mul_le_mul_of_nonneg_left hi1 his
    simpa only [Rat.mul_one] using hm
  have hC : 0≤(524288:Rat)*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  calc
    _ = (524288*H*H)*(i*i*i) := by dsimp [i]; rw [Rat.div_def,Rat.one_mul]; grind only
    _ ≤ (524288*H*H)*(i*i) := Rat.mul_le_mul_of_nonneg_left hic hC
    _ = _ := by rw [pairedDerivative_reciprocalSquare_eq_inverse_product (n+1) hn]; dsimp [i]; grind only

theorem pairedReciprocalTail_remainder_bound (B n : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (remainder (pairedReciprocalTermMap (4*B+n)) a ha
      (upperPairedReciprocalDerivative a ha (pairedTailShift B n)) z hz)
      (524288*reciprocalSquare (n+1)*H*H) := by
  have hRn : (B:Rat)≤((pairedTailShift B n):Rat) := by
    exact_mod_cast (show B≤pairedTailShift B n by unfold pairedTailShift; omega)
  have h := pairedReciprocalTermMap_remainder_large (4*B+n) a z ha hz
    (B:Rat) H Rat.natCast_nonneg hH hA hZ (pairedTailShift_large B n) hRn hd
  apply h.mono
  have hs := pairedDerivative_reciprocalSquare_antitone (n+1) (pairedTailShift B n)
    (by omega) (by unfold pairedTailShift; omega)
  have hc : 0≤(524288:Rat)*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  have hm := Rat.mul_le_mul_of_nonneg_left hs hc
  change 524288*reciprocalSquare (pairedTailShift B n)*H*H≤_
  grind only

theorem pairedReciprocalTail_remainder_block_bound (B N k : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => remainder (pairedReciprocalTermMap (4*B+n)) a ha
      (upperPairedReciprocalDerivative a ha (pairedTailShift B n)) z hz) N k)
      (524288*reciprocalSquareBlock N k*H*H) := by
  induction k with
  | zero => exact Small.zero (by simp only [reciprocalSquareBlock,Rat.mul_zero,Rat.zero_mul]; decide +kernel)
  | succ k ih =>
    have h := LocalODE.small_add ih (pairedReciprocalTail_remainder_bound B (N+k) a z ha hz hA hZ H hH hd)
    apply h.mono
    change 524288*reciprocalSquareBlock N k*H*H +
      524288*reciprocalSquare (N+k+1)*H*H≤524288*reciprocalSquareBlock N (k+1)*H*H
    rw [reciprocalSquareBlock]
    grind only

theorem pairedReciprocalTail_remainder_block_tail (B N k : Nat) (hN : 0<N) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => remainder (pairedReciprocalTermMap (4*B+n)) a ha
      (upperPairedReciprocalDerivative a ha (pairedTailShift B n)) z hz) N k)
      (524288*(N:Rat)⁻¹*H*H) := by
  apply (pairedReciprocalTail_remainder_block_bound B N k a z ha hz hA hZ H hH hd).mono
  have hC : 0≤(524288:Rat)*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  have hm := Rat.mul_le_mul_of_nonneg_left (reciprocalSquareBlock_tail N k hN) hC
  grind only

private theorem pairedRemainder_squareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem pairedRemainder_squareBlock_zero_bound (k : Nat) :
    reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [pairedRemainder_squareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    have he : ((1:Nat):Rat)⁻¹=1 := by decide +kernel
    rw [he] at h
    grind only

theorem pairedReciprocalTail_remainder_prefix_bound (B k : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => remainder (pairedReciprocalTermMap (4*B+n)) a ha
      (upperPairedReciprocalDerivative a ha (pairedTailShift B n)) z hz) 0 k)
      (1048576*H*H) := by
  apply (pairedReciprocalTail_remainder_block_bound B 0 k a z ha hz hA hZ H hH hd).mono
  have hC : 0≤(524288:Rat)*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  have hm := Rat.mul_le_mul_of_nonneg_left (pairedRemainder_squareBlock_zero_bound k) hC
  grind only

end ComputableAnalysis.ModularForms
