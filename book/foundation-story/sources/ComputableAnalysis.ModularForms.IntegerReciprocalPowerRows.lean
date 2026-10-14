import ComputableAnalysis.ModularForms.IntegerReciprocalPowerTails
import ComputableAnalysis.ModularForms.PairedGlobalDerivative

/-! Actual integer reciprocal-power rows, quantitative prefixes, and cutoff agreement. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem block_shift (t : Nat → ComplexRaw) (B L : Nat) :
    ScalarSeries.block (fun n => t (B+n)) 0 L=ScalarSeries.block t B L := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [ScalarSeries.block.eq_2,Nat.zero_add,ih]

def integerPowerRowPrefix (z : Scalar) (hz : InUpperHalfPlane z.val) (k N : Nat) : ComplexRaw :=
  add ((integerReciprocalPowerMap 0 k).eval z hz).val
    (ScalarSeries.block (fun n => (upperPairedIntegerPower z hz k (n+1)).val) 0 N)

theorem integerPowerRowPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (k N : Nat) :
    (integerPowerRowPrefix z hz k N).Valid :=
  add_valid ((integerReciprocalPowerMap 0 k).eval z hz).property
    (ScalarSeries.block_valid _ (fun n => (upperPairedIntegerPower z hz k (n+1)).property) 0 N)

def integerPowerRowAssembly (z : Scalar) (hz : InUpperHalfPlane z.val) (k B : Nat) : ComplexRaw :=
  add (integerPowerRowPrefix z hz k (4*B)) (pairedIntegerPowerTailValue z hz k B)

theorem integerPowerRowAssembly_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) :
    (integerPowerRowAssembly z hz k B).Valid :=
  add_valid (integerPowerRowPrefix_valid z hz k (4*B)) (pairedIntegerPowerTailValue_valid z hz k B hk hB)

theorem integerPowerRowAssembly_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (integerPowerRowAssembly z hz k B) (integerPowerRowPrefix z hz k (4*B+(N+1))))
      (((2*32^k:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) := by
  let t := fun n => (upperPairedIntegerPower z hz k (n+1)).val
  have vt n : (t n).Valid := (upperPairedIntegerPower z hz k (n+1)).property
  have ht : (fun n => (pairedIntegerPowerTailTerm z hz k B n).val)=(fun n => t (4*B+n)) := by
    funext n
    unfold pairedIntegerPowerTailTerm
    have hi : pairedTailShift B n=(4*B+n)+1 := by unfold pairedTailShift; omega
    rw [hi]
  have he (L : Nat) : ScalarSeries.block (fun n => (pairedIntegerPowerTailTerm z hz k B n).val) 0 L=
      ScalarSeries.block t (4*B) L := by
    rw [ht]
    exact block_shift t (4*B) L
  have htail := pairedIntegerPowerTailValue_close z hz k B hk hB N
  rw [he] at htail
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := sub_valid (ScalarSeries.block_valid t vt 0 (4*B+(N+1))) (ScalarSeries.block_valid t vt 0 (4*B)))
    (hright := ScalarSeries.block_valid t vt (4*B) (N+1))
    (ScalarSeries.prefix_difference t vt (4*B) (N+1))
  have hident : (sub (pairedIntegerPowerTailValue z hz k B) (ScalarSeries.block t (4*B) (N+1))).Equiv
      (sub (integerPowerRowAssembly z hz k B) (integerPowerRowPrefix z hz k (4*B+(N+1)))) := by
    have vc := ((integerReciprocalPowerMap 0 k).eval z hz).property
    have vl := pairedIntegerPowerTailValue_valid z hz k B hk hB
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid vl (ScalarSeries.block_valid t vt (4*B) (N+1)))
      (hright := sub_valid (integerPowerRowAssembly_valid z hz k B hk hB)
        (integerPowerRowPrefix_valid z hz k (4*B+(N+1))))
    let C := ComplexRawQuotient.ofRaw ((integerReciprocalPowerMap 0 k).eval z hz).val vc
    let L := ComplexRawQuotient.ofRaw (pairedIntegerPowerTailValue z hz k B) vl
    let P := ComplexRawQuotient.ofRaw (ScalarSeries.block t 0 (4*B)) (ScalarSeries.block_valid t vt 0 (4*B))
    let Q := ComplexRawQuotient.ofRaw (ScalarSeries.block t 0 (4*B+(N+1))) (ScalarSeries.block_valid t vt 0 (4*B+(N+1)))
    let T := ComplexRawQuotient.ofRaw (ScalarSeries.block t (4*B) (N+1)) (ScalarSeries.block_valid t vt (4*B) (N+1))
    change Q-P=T at hd
    change L-T=((C+P)+L)-(C+Q)
    generalize C=c,L=l,P=p,Q=q,T=t at hd ⊢
    grind only
  exact Small.congr
    (sub_valid (pairedIntegerPowerTailValue_valid z hz k B hk hB) (ScalarSeries.block_valid t vt (4*B) (N+1)))
    (sub_valid (integerPowerRowAssembly_valid z hz k B hk hB) (integerPowerRowPrefix_valid z hz k (4*B+(N+1)))) hident htail

private theorem inverse_nat_antitone (n m : Nat) (hn : 0<n) (hnm : n≤m) : (m:Rat)⁻¹≤(n:Rat)⁻¹ := by
  have hp : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  have hq : (0:Rat)<(m:Rat) := by exact_mod_cast (show 0<m by omega)
  have hnR : (n:Rat)≤(m:Rat) := by exact_mod_cast hnm
  have hin := Rat.mul_inv_cancel (n:Rat) (Rat.ne_of_gt hp)
  have him := Rat.mul_inv_cancel (m:Rat) (Rat.ne_of_gt hq)
  have h := Rat.mul_le_mul_of_nonneg_right hnR
    (Rat.mul_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hp)) (Rat.le_of_lt (Rat.inv_pos.mpr hq)))
  calc
    (m:Rat)⁻¹ = ((n:Rat)*(n:Rat)⁻¹)*(m:Rat)⁻¹ := by rw [hin,Rat.one_mul]
    _ = (n:Rat)*((n:Rat)⁻¹*(m:Rat)⁻¹) := by grind only
    _ ≤ (m:Rat)*((n:Rat)⁻¹*(m:Rat)⁻¹) := h
    _ = ((m:Rat)*(m:Rat)⁻¹)*(n:Rat)⁻¹ := by grind only
    _ = (n:Rat)⁻¹ := by rw [him,Rat.one_mul]

theorem integerPowerRowAssembly_cutoff_agreement (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B D : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) (hD : Small z.val (D:Rat)) :
    (integerPowerRowAssembly z hz k B).Equiv (integerPowerRowAssembly z hz k D) := by
  apply RepresentedCauchySum.unique
    (fun N => integerPowerRowPrefix z hz k (4*(B+D)+(N+1)))
    (fun N => integerPowerRowPrefix_valid z hz k _)
    (fun N => ((2*32^k:Nat):Rat)*(((N+1:Nat):Rat))⁻¹)
    (pairedReciprocalTail_shrinks (2*32^k)) _ _
    (integerPowerRowAssembly_valid z hz k B hk hB) (integerPowerRowAssembly_valid z hz k D hk hD)
  · intro N
    have h := integerPowerRowAssembly_close z hz k B hk hB (4*D+N)
    rw [show 4*B+(4*D+N+1)=4*(B+D)+(N+1) by omega] at h
    exact h.mono (Rat.mul_le_mul_of_nonneg_left (inverse_nat_antitone (N+1) (4*D+N+1) (by omega) (by omega)) Rat.natCast_nonneg)
  · intro N
    have h := integerPowerRowAssembly_close z hz k D hk hD (4*B+N)
    rw [show 4*D+(4*B+N+1)=4*(B+D)+(N+1) by omega] at h
    exact h.mono (Rat.mul_le_mul_of_nonneg_left (inverse_nat_antitone (N+1) (4*B+N+1) (by omega) (by omega)) Rat.natCast_nonneg)

def integerReciprocalPowerRowSum (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) (hk : 2≤k) : Scalar :=
  ⟨integerPowerRowAssembly z hz k (pairedDerivativeCutoff z),
    integerPowerRowAssembly_valid z hz k _ hk (pairedDerivativeCutoff_small z)⟩

end ComputableAnalysis.ModularForms
