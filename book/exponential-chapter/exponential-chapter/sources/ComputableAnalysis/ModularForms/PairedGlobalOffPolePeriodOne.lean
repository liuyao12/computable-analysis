import ComputableAnalysis.ModularForms.PairedGlobalOffPoleBoundaryDecay

/-! Period one of the actual infinite lattice value on the full off-pole domain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def globalOffPoleValue (z : Scalar) (hz : pairedOffPoleDomain z) : ComplexRaw :=
  (pairedGlobalOffPoleAssemblyMap.eval z hz).val

theorem globalOffPoleValue_valid (z : Scalar) (hz : pairedOffPoleDomain z) :
    (globalOffPoleValue z hz).Valid := (pairedGlobalOffPoleAssemblyMap.eval z hz).property

theorem globalOffPoleSymmetricPrefix_shift_bound (z : Scalar)
    (hz : pairedOffPoleDomain z) (R : Rat) (hR : 0≤R) (hsmall : Small z.val R)
    (N : Nat) (hN : 0<N) (hRN : R≤(N:Rat))
    (hlarge : 16*R*R≤pairedIntegerSquare N)
    (hlargeSucc : 16*R*R≤pairedIntegerSquare (N+1)) :
    Small (sub (globalOffPoleSymmetricPrefix (integerShiftScalar z 1)
      (pairedOffPoleDomain_shift z hz 1) N) (globalOffPoleSymmetricPrefix z hz N))
      (16*(1/((N+1:Nat):Rat))+16*(1/(N:Rat))) := by
  have hsucc : 0<N+1 := by omega
  have hRs : R≤((N+1:Nat):Rat) := by
    have hn : (N:Rat)≤((N+1:Nat):Rat) := by exact_mod_cast (show N≤N+1 by omega)
    grind only
  have hp := globalOffPoleIntegerReciprocal_plus_bound z hz R hR hsmall (N+1) hsucc hlargeSucc hRs
  have hm := globalOffPoleIntegerReciprocal_minus_bound z hz R hR hsmall N hN hlarge hRN
  have he : ((N+1:Nat):Int)=(N:Int)+1 := by omega
  rw [he] at hp
  have h := LocalODE.small_add hp (SeriesLimitLaws.small_neg hm)
  exact Small.congr (sub_valid (globalOffPoleIntegerReciprocal z hz _).property
      (globalOffPoleIntegerReciprocal z hz _).property)
    (sub_valid (globalOffPoleSymmetricPrefix_valid _ _ N)
      (globalOffPoleSymmetricPrefix_valid z hz N))
    (equiv_symm (globalOffPoleSymmetricPrefix_shift_identity z hz N)) h

private theorem reciprocalRate_nonnegative (C n : Nat) (hn : 0<n) :
    0≤(C:Rat)*((n:Rat))⁻¹ := by
  have hp : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hp))

theorem globalOffPoleValue_period_one (z : Scalar)
    (hz : pairedOffPoleDomain z) :
    (globalOffPoleValue (integerShiftScalar z 1)
      (pairedOffPoleDomain_shift z hz 1)).Equiv (globalOffPoleValue z hz) := by
  let w := integerShiftScalar z 1
  let hw := pairedOffPoleDomain_shift z hz 1
  let B := pairedInternalBound z
  let C := pairedInternalBound w
  let L := 4*B+4*C
  let K := fun N => N+L+1
  let p := fun N => globalOffPoleSymmetricPrefix z hz (K N)
  let q := fun N => globalOffPoleSymmetricPrefix w hw (K N)
  have hp : ∀ N, (p N).Valid := fun N => globalOffPoleSymmetricPrefix_valid z hz _
  have hq : ∀ N, (q N).Valid := fun N => globalOffPoleSymmetricPrefix_valid w hw _
  let eB := fun N => ((16*B:Nat):Rat)*(((N+4*C+1:Nat):Rat))⁻¹
  let eC := fun N => ((16*C:Nat):Rat)*(((N+4*B+1:Nat):Rat))⁻¹
  let d := fun N => (16:Rat)*(((N+L+2:Nat):Rat))⁻¹ +
    (16:Rat)*(((N+L+1:Nat):Rat))⁻¹
  have heB : ShrinksToZero eB :=
    SeriesLimitLaws.shrinks_shift _ (pairedReciprocalTail_shrinks (16*B)) (4*C)
  have heC : ShrinksToZero eC :=
    SeriesLimitLaws.shrinks_shift _ (pairedReciprocalTail_shrinks (16*C)) (4*B)
  have hd : ShrinksToZero d := by
    have h1 := SeriesLimitLaws.shrinks_shift _ (pairedReciprocalTail_shrinks 16) (L+1)
    have h2 := SeriesLimitLaws.shrinks_shift _ (pairedReciprocalTail_shrinks 16) L
    have h := RepresentedCauchySum.sum_shrinks _ _ h1 h2
    simpa only [d,show ((16:Nat):Rat)=16 by decide +kernel,Nat.add_assoc,show (1:Nat)+1=2 by rfl] using h
  have hnB (N : Nat) : 0≤eB N := reciprocalRate_nonnegative _ _ (by omega)
  have hnC (N : Nat) : 0≤eC N := reciprocalRate_nonnegative _ _ (by omega)
  have hnD (N : Nat) : 0≤d N := Rat.add_nonneg
    (reciprocalRate_nonnegative 16 _ (by omega)) (reciprocalRate_nonnegative 16 _ (by omega))
  have hF (N : Nat) : Small (sub (globalOffPoleValue z hz) (p N)) (eB N) := by
    have h := globalOffPoleSymmetricPrefix_close z hz (N+4*C)
    have hk : 4*pairedInternalBound z+(N+4*C+1)=K N := by dsimp [K,L,B]; omega
    rw [hk] at h
    exact h
  have hG (N : Nat) : Small (sub (globalOffPoleValue w hw) (q N)) (eC N) := by
    have h := globalOffPoleSymmetricPrefix_close w hw (N+4*B)
    have hk : 4*pairedInternalBound w+(N+4*B+1)=K N := by dsimp [K,L,C]; omega
    rw [hk] at h
    exact h
  have hD (N : Nat) : Small (sub (q N) (p N)) (d N) := by
    have hk : 0<K N := by dsimp [K]; omega
    have hBk : (B:Rat)≤((K N):Rat) := by
      exact_mod_cast (show B≤K N by dsimp [K,L]; omega)
    have hk1 : pairedTailShift B (N+4*C)=K N := by dsimp [pairedTailShift,K,L]; omega
    have hk2 : pairedTailShift B (N+4*C+1)=K N+1 := by dsimp [pairedTailShift,K,L]; omega
    have hlarge := pairedTailShift_large B (N+4*C)
    have hlargeSucc := pairedTailShift_large B (N+4*C+1)
    rw [hk1] at hlarge
    rw [hk2] at hlargeSucc
    have h := globalOffPoleSymmetricPrefix_shift_bound z hz (B:Rat) Rat.natCast_nonneg
      (pairedInternalBound_small z) (K N) hk hBk hlarge hlargeSucc
    simpa only [d,q,p,w,hw,Rat.div_def,Rat.one_mul,K,Nat.add_assoc,show (1:Nat)+1=2 by rfl] using h
  let E := fun N => eB N+(eC N+d N)
  have hE : ShrinksToZero E := RepresentedCauchySum.sum_shrinks _ _ heB
    (RepresentedCauchySum.sum_shrinks _ _ heC hd)
  apply equiv_symm
  apply RepresentedCauchySum.unique p hp E hE _ _
    (globalOffPoleValue_valid z hz) (globalOffPoleValue_valid w hw)
  · intro N
    exact (hF N).mono (by change eB N≤eB N+(eC N+d N); have := hnC N; have := hnD N; grind only)
  · intro N
    have h := ScalarTopology.small_triangle
      ⟨globalOffPoleValue w hw,globalOffPoleValue_valid w hw⟩
      ⟨q N,hq N⟩ ⟨p N,hp N⟩ (eC N) (d N) (hG N) (hD N)
    exact h.mono (by change eC N+d N≤eB N+(eC N+d N); have := hnB N; grind only)

end ComputableAnalysis.ModularForms
