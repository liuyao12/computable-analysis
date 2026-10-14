import ComputableAnalysis.ModularForms.PairedOffPoleTailInverseRemainderBound

/-! Summable quadratic estimates for complete actual off-pole tail term remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPoleTailInverse_difference_identity (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) :
    (sub (pairedOffPoleTailInverse B n z hz).val (pairedOffPoleTailInverse B n a ha).val).Equiv
      (neg (mul (mul (pairedOffPoleTailInverse B n a ha).val
        (sub (mul z.val z.val) (mul a.val a.val))) (pairedOffPoleTailInverse B n z hz).val)) := by
  let k := pairedTailShift B n
  let p := pairedLiteralDenominator a (pairedIntegerSquare k)
  let q := pairedLiteralDenominator z (pairedIntegerSquare k)
  have hk : 0<k := by dsimp [k,pairedTailShift]; omega
  let hp := pairedIntegerDenominator_nonzero a (B:Rat) k Rat.natCast_nonneg
    (LocalODE.interior_bound _ a ha) hk (pairedTailShift_large B n)
  let hq := pairedIntegerDenominator_nonzero z (B:Rat) k Rat.natCast_nonneg
    (LocalODE.interior_bound _ z hz) hk (pairedTailShift_large B n)
  have hd := ReciprocalDifference.difference p q hp hq
  have he : (sub q.val p.val).Equiv (sub (mul z.val z.val) (mul a.val a.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid q.property p.property)
      (hright := sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property))
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let K := ComplexRawQuotient.ofQComplex ⟨pairedIntegerSquare k,0⟩
    change (Z*Z-K)-(A*A-K)=Z*Z-A*A
    grind only
  exact equiv_trans
    (sub_valid (pairedOffPoleTailInverse B n z hz).property (pairedOffPoleTailInverse B n a ha).property)
    (neg_valid (mul_valid (mul_valid (pairedOffPoleTailInverse B n a ha).property (sub_valid q.property p.property))
      (pairedOffPoleTailInverse B n z hz).property))
    (neg_valid (mul_valid (mul_valid (pairedOffPoleTailInverse B n a ha).property
      (sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property)))
      (pairedOffPoleTailInverse B n z hz).property)) hd
    (neg_equiv (mul_equiv
      (mul_valid (pairedOffPoleTailInverse B n a ha).property (sub_valid q.property p.property))
      (mul_valid (pairedOffPoleTailInverse B n a ha).property
        (sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property)))
      (pairedOffPoleTailInverse B n z hz).property (pairedOffPoleTailInverse B n z hz).property
      (mul_equiv (pairedOffPoleTailInverse B n a ha).property (pairedOffPoleTailInverse B n a ha).property
        (sub_valid q.property p.property) (sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property))
        (equiv_refl _ (pairedOffPoleTailInverse B n a ha).property) he)
      (equiv_refl _ (pairedOffPoleTailInverse B n z hz).property)))

theorem pairedOffPoleTailInverse_difference_bound (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (sub (pairedOffPoleTailInverse B n z hz).val (pairedOffPoleTailInverse B n a ha).val)
      (256*(B:Rat)*reciprocalSquare (n+1)*H) := by
  let r := reciprocalSquare (pairedTailShift B n)
  have hr : 0≤r := by
    unfold r reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos
      (by exact_mod_cast (show 0<pairedTailShift B n by unfold pairedTailShift; omega))
      (by exact_mod_cast (show 0<pairedTailShift B n by unfold pairedTailShift; omega))))
  have hM : 0≤4*r := Rat.mul_nonneg (by decide +kernel) hr
  have hD : 0≤4*(B:Rat)*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) hH
  let i := pairedOffPoleTailInverse B n a ha
  let j := pairedOffPoleTailInverse B n z hz
  have hp := Small.mul i.property (sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property))
    hM hD (pairedOffPoleTailInverse_bound B n a ha) (pairedOffPole_squared_difference_bound B a z ha hz H hH hd)
  have hMD : 0≤2*(4*r)*(4*(B:Rat)*H) := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hM) hD
  have hb := SeriesLimitLaws.small_neg (Small.mul
    (mul_valid i.property (sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property)))
    j.property hMD hM hp (pairedOffPoleTailInverse_bound B n z hz))
  have hbound := Small.congr
    (neg_valid (mul_valid (mul_valid i.property (sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property))) j.property))
    (sub_valid j.property i.property)
    (equiv_symm (pairedOffPoleTailInverse_difference_identity B n a z ha hz)) hb
  apply hbound.mono
  have hr1 := pairedDerivative_reciprocalSquare_antitone 1 (pairedTailShift B n)
    (by omega) (by unfold pairedTailShift; omega)
  rw [show reciprocalSquare 1=1 by decide +kernel] at hr1
  have hrs := pairedDerivative_reciprocalSquare_antitone (n+1) (pairedTailShift B n)
    (by omega) (by unfold pairedTailShift; omega)
  have hh := Rat.mul_le_mul_of_nonneg_left hr1 hr
  have hm := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans (by simpa only [Rat.mul_one] using hh) hrs)
    (show 0≤256*(B:Rat)*H from Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) hH)
  dsimp only [r] at hm
  grind only


theorem pairedOffPoleTailTermRemainder_bound (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedOffPoleTailTermRemainder B n a z ha hz).val
      ((1536*(B:Rat)+65536*(B:Rat)*(B:Rat)*(B:Rat))*reciprocalSquare (n+1)*H*H) := by
  have hr : 0≤reciprocalSquare (n+1) := by
    unfold reciprocalSquare
    have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hn hn))
  have hbb : 0≤(B:Rat)*(B:Rat) := Rat.mul_nonneg Rat.natCast_nonneg Rat.natCast_nonneg
  have hC : 0≤128+16384*(B:Rat)*(B:Rat) := by grind only
  have hR : 0≤(128+16384*(B:Rat)*(B:Rat))*reciprocalSquare (n+1)*H*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hC hr) hH) hH
  have hD : 0≤256*(B:Rat)*reciprocalSquare (n+1)*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) hr) hH
  have ha2 := LocalODE.small_add (LocalODE.interior_bound _ a ha) (LocalODE.interior_bound _ a ha)
  have hh2 := LocalODE.small_add hd hd
  have hleft := Small.mul (add_valid a.property a.property)
    (pairedOffPoleTailInverseRemainder B n a z ha hz).property
    (Rat.add_nonneg Rat.natCast_nonneg Rat.natCast_nonneg) hR ha2
    (pairedOffPoleTailInverseRemainder_square_bound B n a z ha hz H hH hd)
  have hright := Small.mul (add_valid (sub_valid z.property a.property) (sub_valid z.property a.property))
    (sub_valid (pairedOffPoleTailInverse B n z hz).property (pairedOffPoleTailInverse B n a ha).property)
    (Rat.add_nonneg hH hH) hD hh2 (pairedOffPoleTailInverse_difference_bound B n a z ha hz H hH hd)
  exact (LocalODE.small_add hleft hright).mono (by grind only)

theorem pairedOffPoleTailTerm_actual_remainder_bound (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder (pairedOffPoleTailTermMap B n) a ha
      (pairedOffPoleTailDerivativeTerm B n a ha) z hz)
      ((1536*(B:Rat)+65536*(B:Rat)*(B:Rat)*(B:Rat))*reciprocalSquare (n+1)*H*H) :=
  Small.congr (pairedOffPoleTailTermRemainder B n a z ha hz).property
    (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (equiv_symm (pairedOffPoleTailTerm_remainder_identity B n a z ha hz))
    (pairedOffPoleTailTermRemainder_bound B n a z ha hz H hH hd)

end ComputableAnalysis.ModularForms
