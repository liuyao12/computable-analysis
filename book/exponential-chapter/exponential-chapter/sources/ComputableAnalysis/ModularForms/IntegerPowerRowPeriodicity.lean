import ComputableAnalysis.ModularForms.IntegerPowerTranslationPrefixes
import ComputableAnalysis.ModularForms.CMWeightFourTailRate163

/-! Period one of the actual convergent reciprocal-power rows. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem integerPowerRowPrefix_translation_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k B n : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) :
    Small (sub (integerPowerRowPrefix (integerShiftScalar z 1) (integerShiftScalar_upper z hz 1)
      k (4*B+(n+1))) (integerPowerRowPrefix z hz k (4*B+(n+1))))
      (((2*32^k:Nat):Rat)*(((n+1:Nat):Rat))⁻¹) := by
  let N := 4*B+(n+1)
  have bound (m : Nat) (hm : m=N ∨ m=N+1) :
      Small ((integerReciprocalPowerMap (m:Int) k).eval z hz).val
        ((32:Rat)^k*reciprocalSquare (n+1)) ∧
      Small ((integerReciprocalPowerMap (-(m:Int)) k).eval z hz).val
        ((32:Rat)^k*reciprocalSquare (n+1)) := by
    have hi : ∃ j, m=pairedTailShift B j := by
      rcases hm with hm | hm
      · exact ⟨n,by dsimp [N] at hm; unfold pairedTailShift; omega⟩
      · exact ⟨n+1,by dsimp [N] at hm; unfold pairedTailShift; omega⟩
    obtain ⟨j,rfl⟩ := hi
    have h := integerReciprocalPower_boundary_bound z hz (B:Rat) Rat.natCast_nonneg hB
      k (pairedTailShift B j) hk (by unfold pairedTailShift; omega) (pairedTailShift_large B j)
      (by exact_mod_cast (show B≤pairedTailShift B j by unfold pairedTailShift; omega))
    have hmono := Rat.mul_le_mul_of_nonneg_left
      (pairedDerivative_reciprocalSquare_antitone (n+1) (pairedTailShift B j) (by omega)
        (by dsimp [N] at hm; rcases hm with hm | hm <;> omega))
      (Rat.pow_nonneg (a := (32:Rat)) (n := k) (by decide))
    exact ⟨h.1.mono hmono,h.2.mono hmono⟩
  have hb := SeriesLimitLaws.small_sub (bound (N+1) (Or.inr rfl)).1 (bound N (Or.inl rfl)).2
  have he : (sub ((integerReciprocalPowerMap ((N+1:Nat):Int) k).eval z hz).val
      ((integerReciprocalPowerMap (-(N:Int)) k).eval z hz).val).Equiv
      (sub (integerPowerRowPrefix (integerShiftScalar z 1) (integerShiftScalar_upper z hz 1) k N)
        (integerPowerRowPrefix z hz k N)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
    have h := integerPowerRowPrefix_translation_defect z hz k N
    have hi : ((N+1:Nat):Int)=(N:Int)+1 := by omega
    change integerReciprocalPowerClass z hz k ((N+1:Nat):Int)-
      integerReciprocalPowerClass z hz k (-(N:Int))=_
    rw [hi]
    exact h.symm
  have h := Small.congr (sub_valid ((integerReciprocalPowerMap ((N+1:Nat):Int) k).eval z hz).property
      ((integerReciprocalPowerMap (-(N:Int)) k).eval z hz).property)
    (sub_valid (integerPowerRowPrefix_valid _ _ k N) (integerPowerRowPrefix_valid z hz k N)) he hb
  apply h.mono
  have hs := reciprocalSquare_le_reciprocal (n+1) (by omega)
  have hc : ((2*32^k:Nat):Rat)=2*(32:Rat)^k := by
    simp only [Rat.natCast_mul,Rat.natCast_pow,show ((2:Nat):Rat)=2 by decide +kernel,
      show ((32:Nat):Rat)=32 by decide +kernel]
  rw [hc]
  have hm := Rat.mul_le_mul_of_nonneg_left hs
    (Rat.mul_nonneg (by decide : (0:Rat)≤2) (Rat.pow_nonneg (a := (32:Rat)) (n := k) (by decide)))
  rw [Rat.div_def,Rat.one_mul] at hm
  grind only

theorem integerPowerRowAssembly_period_one (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k B : Nat) (hk : 2≤k)
    (hB : Small z.val (B:Rat)) (hBw : Small (integerShiftScalar z 1).val (B:Rat)) :
    (integerPowerRowAssembly (integerShiftScalar z 1) (integerShiftScalar_upper z hz 1) k B).Equiv
      (integerPowerRowAssembly z hz k B) := by
  let w := integerShiftScalar z 1
  let hw := integerShiftScalar_upper z hz 1
  let C := 2*32^k
  have hp n : 0≤(C:Rat)*(((n+1:Nat):Rat))⁻¹ :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr (by
      exact_mod_cast (show 0<n+1 by omega))))
  have rate n : (C:Rat)*(((n+1:Nat):Rat))⁻¹+
      (C:Rat)*(((n+1:Nat):Rat))⁻¹=((2*C:Nat):Rat)*(((n+1:Nat):Rat))⁻¹ := by
    rw [Rat.natCast_mul]
    have ht : ((2:Nat):Rat)=2 := by decide +kernel
    rw [ht]
    grind only
  apply RepresentedCauchySum.unique
    (fun n => integerPowerRowPrefix z hz k (4*B+(n+1)))
    (fun n => integerPowerRowPrefix_valid z hz k (4*B+(n+1)))
    (fun n => ((2*C:Nat):Rat)*(((n+1:Nat):Rat))⁻¹) (pairedReciprocalTail_shrinks (2*C))
    _ _ (integerPowerRowAssembly_valid w hw k B hk hBw)
    (integerPowerRowAssembly_valid z hz k B hk hB) ?_ ?_
  · intro n
    have h := LocalODE.small_add (integerPowerRowAssembly_close w hw k B hk hBw n)
      (integerPowerRowPrefix_translation_bound z hz k B n hk hB)
    have he : (add
        (sub (integerPowerRowAssembly w hw k B) (integerPowerRowPrefix w hw k (4*B+(n+1))))
        (sub (integerPowerRowPrefix w hw k (4*B+(n+1))) (integerPowerRowPrefix z hz k (4*B+(n+1))))).Equiv
        (sub (integerPowerRowAssembly w hw k B) (integerPowerRowPrefix z hz k (4*B+(n+1)))) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
      let S := ComplexRawQuotient.ofRaw (integerPowerRowAssembly w hw k B)
        (integerPowerRowAssembly_valid w hw k B hk hBw)
      let P := ComplexRawQuotient.ofRaw (integerPowerRowPrefix w hw k (4*B+(n+1)))
        (integerPowerRowPrefix_valid w hw k (4*B+(n+1)))
      let Q := ComplexRawQuotient.ofRaw (integerPowerRowPrefix z hz k (4*B+(n+1)))
        (integerPowerRowPrefix_valid z hz k (4*B+(n+1)))
      change (S-P)+(P-Q)=S-Q
      grind only
    have hh := Small.congr
      (add_valid (sub_valid (integerPowerRowAssembly_valid w hw k B hk hBw)
        (integerPowerRowPrefix_valid w hw k (4*B+(n+1))))
        (sub_valid (integerPowerRowPrefix_valid w hw k (4*B+(n+1)))
          (integerPowerRowPrefix_valid z hz k (4*B+(n+1)))))
      (sub_valid (integerPowerRowAssembly_valid w hw k B hk hBw)
        (integerPowerRowPrefix_valid z hz k (4*B+(n+1)))) he h
    change Small _ ((C:Rat)*(((n+1:Nat):Rat))⁻¹+(C:Rat)*(((n+1:Nat):Rat))⁻¹) at hh
    rw [rate] at hh
    exact hh
  · intro n
    have h := integerPowerRowAssembly_close z hz k B hk hB n
    apply h.mono
    rw [← rate]
    have hh := hp n
    grind only

theorem integerReciprocalPowerRowSum_period_one (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k : Nat) (hk : 2≤k) :
    (integerReciprocalPowerRowSum (integerShiftScalar z 1) (integerShiftScalar_upper z hz 1) k hk).val.Equiv
      (integerReciprocalPowerRowSum z hz k hk).val := by
  let w := integerShiftScalar z 1
  let hw := integerShiftScalar_upper z hz 1
  let B := pairedDerivativeCutoff z+pairedDerivativeCutoff w
  have hB : Small z.val (B:Rat) := (pairedDerivativeCutoff_small z).mono (by
    exact_mod_cast (show pairedDerivativeCutoff z≤B by dsimp [B]; omega))
  have hBw : Small w.val (B:Rat) := (pairedDerivativeCutoff_small w).mono (by
    exact_mod_cast (show pairedDerivativeCutoff w≤B by dsimp [B]; omega))
  exact equiv_trans (integerReciprocalPowerRowSum w hw k hk).property
    (integerPowerRowAssembly_valid w hw k B hk hBw) (integerReciprocalPowerRowSum z hz k hk).property
    (integerPowerRowAssembly_cutoff_agreement w hw k (pairedDerivativeCutoff w) B hk (pairedDerivativeCutoff_small w) hBw)
    (equiv_trans (integerPowerRowAssembly_valid w hw k B hk hBw)
      (integerPowerRowAssembly_valid z hz k B hk hB) (integerReciprocalPowerRowSum z hz k hk).property
      (integerPowerRowAssembly_period_one z hz k B hk hB hBw)
      (integerPowerRowAssembly_cutoff_agreement z hz k B (pairedDerivativeCutoff z) hk hB (pairedDerivativeCutoff_small z)))

end ComputableAnalysis.ModularForms
