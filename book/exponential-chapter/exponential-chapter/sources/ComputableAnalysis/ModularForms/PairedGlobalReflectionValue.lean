import ComputableAnalysis.ModularForms.PairedGlobalReflectionPrefixes
import ComputableAnalysis.ModularForms.PairedGlobalOffPolePeriodOne

/-! Reflection of the actual infinite global value from common finite prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem raw_neg_sub_equiv (a b : ComplexRaw) (ha : a.Valid) (hb : b.Valid) :
    (neg (sub a b)).Equiv (sub (neg a) (neg b)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := neg_valid (sub_valid ha hb)) (hright := sub_valid (neg_valid ha) (neg_valid hb))
  rw [ComplexRawQuotient.ofRaw_neg _ (sub_valid ha hb)]
  change -(ComplexRawQuotient.ofRaw a ha-ComplexRawQuotient.ofRaw b hb)=
    ComplexRawQuotient.ofRaw (neg a) (neg_valid ha)-ComplexRawQuotient.ofRaw (neg b) (neg_valid hb)
  rw [ComplexRawQuotient.ofRaw_neg _ ha,ComplexRawQuotient.ofRaw_neg _ hb]
  grind only

theorem globalOffPoleValue_reflection (z : Scalar) (hz : pairedOffPoleDomain z) :
    (globalOffPoleValue (pairedReflectionMap.eval z trivial) (pairedOffPoleDomain_reflection z hz)).Equiv
      (neg (globalOffPoleValue z hz)) := by
  let w := pairedReflectionMap.eval z trivial
  let hw := pairedOffPoleDomain_reflection z hz
  let B := pairedInternalBound z
  let C := pairedInternalBound w
  let K := fun N => 4*B+4*C+N+1
  let p := fun N => globalOffPoleSymmetricPrefix z hz (K N)
  let q := fun N => globalOffPoleSymmetricPrefix w hw (K N)
  let eB := fun N => ((16*B:Nat):Rat)*((N+4*C+1:Nat):Rat)⁻¹
  let eC := fun N => ((16*C:Nat):Rat)*((N+4*B+1:Nat):Rat)⁻¹
  let E := fun N => eB N+eC N
  have heB : ShrinksToZero eB := SeriesLimitLaws.shrinks_shift _ (pairedReciprocalTail_shrinks (16*B)) (4*C)
  have heC : ShrinksToZero eC := SeriesLimitLaws.shrinks_shift _ (pairedReciprocalTail_shrinks (16*C)) (4*B)
  have hn (A n : Nat) : 0≤((A:Nat):Rat)*((n+1:Nat):Rat)⁻¹ := by
    have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hp))
  apply RepresentedCauchySum.unique q (fun N => globalOffPoleSymmetricPrefix_valid w hw (K N)) E
    (RepresentedCauchySum.sum_shrinks _ _ heB heC)
    _ _ (globalOffPoleValue_valid w hw) (neg_valid (globalOffPoleValue_valid z hz))
  · intro N
    have h := globalOffPoleSymmetricPrefix_close w hw (N+4*B)
    have hk : 4*pairedInternalBound w+(N+4*B+1)=K N := by dsimp [K,C]; omega
    rw [hk] at h
    apply h.mono
    have hb := hn (16*B) (N+4*C)
    change eC N≤eB N+eC N
    change 0≤eB N at hb
    grind only
  · intro N
    have h := globalOffPoleSymmetricPrefix_close z hz (N+4*C)
    have hk : 4*pairedInternalBound z+(N+4*C+1)=K N := by dsimp [K,B]; omega
    rw [hk] at h
    have hs := SeriesLimitLaws.small_neg h
    have hdiff : (neg (sub (globalOffPoleValue z hz) (p N))).Equiv
        (sub (neg (globalOffPoleValue z hz)) (q N)) :=
      equiv_trans (neg_valid (sub_valid (globalOffPoleValue_valid z hz)
        (globalOffPoleSymmetricPrefix_valid z hz (K N))))
        (sub_valid (neg_valid (globalOffPoleValue_valid z hz))
          (neg_valid (globalOffPoleSymmetricPrefix_valid z hz (K N))))
        (sub_valid (neg_valid (globalOffPoleValue_valid z hz))
          (globalOffPoleSymmetricPrefix_valid w hw (K N)))
        (raw_neg_sub_equiv _ _ (globalOffPoleValue_valid z hz) (globalOffPoleSymmetricPrefix_valid z hz (K N)))
        (FunctionTheory.sub_congr (equiv_refl _ (neg_valid (globalOffPoleValue_valid z hz)))
          (equiv_symm (globalOffPoleSymmetricPrefix_reflection z hz (K N))))
    apply (Small.congr
      (neg_valid (sub_valid (globalOffPoleValue_valid z hz) (globalOffPoleSymmetricPrefix_valid z hz (K N))))
      (sub_valid (neg_valid (globalOffPoleValue_valid z hz)) (globalOffPoleSymmetricPrefix_valid w hw (K N)))
      hdiff hs).mono
    have hc := hn (16*C) (N+4*B)
    change eB N≤eB N+eC N
    change 0≤eC N at hc
    grind only

end ComputableAnalysis.ModularForms
