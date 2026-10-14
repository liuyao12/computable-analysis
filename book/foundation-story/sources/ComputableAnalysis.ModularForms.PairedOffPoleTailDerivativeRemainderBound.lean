import ComputableAnalysis.ModularForms.PairedOffPoleTailDerivativeRemainder

/-! Summable quadratic bounds for the actual first-derivative tail remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailDerivativeRemainderCoefficient (B : Nat) : Nat :=
  768+196608*B*B+6291456*B*B*B*B

theorem pairedOffPoleTailInverse_square_difference_bound (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (sub (mul (pairedOffPoleTailInverse B n z hz).val (pairedOffPoleTailInverse B n z hz).val)
      (mul (pairedOffPoleTailInverse B n a ha).val (pairedOffPoleTailInverse B n a ha).val))
      (4096*(B:Rat)*reciprocalSquare (n+1)*H) := by
  let i := pairedOffPoleTailInverse B n a ha
  let j := pairedOffPoleTailInverse B n z hz
  have hi : Small i.val 4 := (pairedOffPoleTailInverse_bound B n a ha).mono (by
    have h := pairedDerivative_reciprocalSquare_antitone 1 (pairedTailShift B n)
      (by omega) (by unfold pairedTailShift; omega)
    rw [show reciprocalSquare 1=1 by decide +kernel] at h
    grind only)
  have hj : Small j.val 4 := (pairedOffPoleTailInverse_bound B n z hz).mono (by
    have h := pairedDerivative_reciprocalSquare_antitone 1 (pairedTailShift B n)
      (by omega) (by unfold pairedTailShift; omega)
    rw [show reciprocalSquare 1=1 by decide +kernel] at h
    grind only)
  have hc : 0≤reciprocalSquare (n+1) := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos
    (by exact_mod_cast (show 0<n+1 by omega)) (by exact_mod_cast (show 0<n+1 by omega))))
  have hD : 0≤256*(B:Rat)*reciprocalSquare (n+1)*H := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) hc) hH
  have hp := Small.mul (sub_valid j.property i.property) (add_valid j.property i.property)
    hD (show (0:Rat)≤4+4 by decide +kernel)
    (pairedOffPoleTailInverse_difference_bound B n a z ha hz H hH hd) (LocalODE.small_add hj hi)
  have he : (mul (sub j.val i.val) (add j.val i.val)).Equiv
      (sub (mul j.val j.val) (mul i.val i.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid (sub_valid j.property i.property) (add_valid j.property i.property))
      (hright := sub_valid (mul_valid j.property j.property) (mul_valid i.property i.property))
    let I := ComplexRawQuotient.ofRaw i.val i.property
    let J := ComplexRawQuotient.ofRaw j.val j.property
    change (J-I)*(J+I)=J*J-I*I
    grind only
  exact (Small.congr (mul_valid (sub_valid j.property i.property) (add_valid j.property i.property))
    (sub_valid (mul_valid j.property j.property) (mul_valid i.property i.property)) he hp).mono (by grind only)

theorem pairedOffPoleTailDerivativeRemainder_bound (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedOffPoleTailDerivativeRemainder B n a z ha hz).val
      ((pairedOffPoleTailDerivativeRemainderCoefficient B:Rat)*reciprocalSquare (n+1)*H*H) := by
  have hB : (0:Rat)≤(B:Rat) := Rat.natCast_nonneg
  let c := reciprocalSquare (n+1)
  have hc : 0≤c := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos
    (by exact_mod_cast (show 0<n+1 by omega)) (by exact_mod_cast (show 0<n+1 by omega))))
  have hc1 : c≤1 := by
    have h := pairedDerivative_reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
    simpa only [show reciprocalSquare 1=1 by decide +kernel] using h
  let A : Rat := 128+16384*(B:Rat)*(B:Rat)
  have hA : 0≤A := Rat.add_nonneg (by decide +kernel)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hB)
  let i := pairedOffPoleTailInverse B n a ha
  let r := pairedOffPoleTailInverseRemainder B n a z ha hz
  let d : Scalar := ⟨sub (pairedOffPoleTailInverse B n z hz).val i.val,
    sub_valid (pairedOffPoleTailInverse B n z hz).property i.property⟩
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  have hi : Small i.val (4*c) := (pairedOffPoleTailInverse_bound B n a ha).mono
    (Rat.mul_le_mul_of_nonneg_left
      (pairedDerivative_reciprocalSquare_antitone (n+1) (pairedTailShift B n)
        (by omega) (by unfold pairedTailShift; omega)) (by decide +kernel))
  have hi4 : Small i.val 4 := hi.mono (by grind only)
  have hr : Small r.val (A*c*H*H) := pairedOffPoleTailInverseRemainder_square_bound B n a z ha hz H hH hd
  have hR : 0≤A*c*H*H := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hA hc) hH) hH
  have hD0 : 0≤256*(B:Rat)*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hH
  have hD : 0≤256*(B:Rat)*c*H := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hc) hH
  have hdiff : Small d.val (256*(B:Rat)*c*H) := pairedOffPoleTailInverse_difference_bound B n a z ha hz H hH hd
  have hdiff0 : Small d.val (256*(B:Rat)*H) := hdiff.mono (by
    have hm := Rat.mul_le_mul_of_nonneg_left hc1 hD0
    grind only)
  have hir := Small.mul i.property r.property (show (0:Rat)≤4 by decide +kernel) hR hi4 hr
  have hdd := Small.mul d.property d.property hD hD0 hdiff hdiff0
  have hinner := LocalODE.small_add (LocalODE.small_add hir hir) hdd
  have hI2 := Small.mul i.property i.property (Rat.mul_nonneg (by decide +kernel) hc)
    (show (0:Rat)≤4 by decide +kernel) hi hi4
  have hhh := Small.mul h.property h.property hH hH hd hd
  have haa := Small.mul a.property a.property hB hB
    (LocalODE.interior_bound _ a ha) (LocalODE.interior_bound _ a ha)
  have hB2 : 0≤2*(B:Rat)*(B:Rat) := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hB
  have hIR : 0≤2*4*(A*c*H*H) := Rat.mul_nonneg (by decide +kernel) hR
  have hDD : 0≤2*(256*(B:Rat)*c*H)*(256*(B:Rat)*H) := Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) hD) hD0
  have hfirst := Small.mul (mul_valid a.property a.property)
    (add_valid (add_valid (mul_valid i.property r.property) (mul_valid i.property r.property))
      (mul_valid d.property d.property)) hB2 (Rat.add_nonneg (Rat.add_nonneg hIR hIR) hDD) haa hinner
  have hsecond := Small.mul (mul_valid i.property i.property) (mul_valid h.property h.property)
    (by grind only) (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hH) hH) hI2 hhh
  have hF : 0≤4*(B:Rat)*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hH
  have hG : 0≤4096*(B:Rat)*c*H := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hc) hH
  have hthird := Small.mul
    (sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property))
    (sub_valid (mul_valid (pairedOffPoleTailInverse B n z hz).property (pairedOffPoleTailInverse B n z hz).property)
      (mul_valid i.property i.property)) hF hG
    (pairedOffPole_squared_difference_bound B a z ha hz H hH hd)
    (pairedOffPoleTailInverse_square_difference_bound B n a z ha hz H hH hd)
  have hp := LocalODE.small_add (LocalODE.small_add hfirst hsecond) hthird
  have hp2 := LocalODE.small_add hp hp
  have hp4 := LocalODE.small_add hp2 hp2
  apply (SeriesLimitLaws.small_sub (LocalODE.small_add hr hr) hp4).mono
  simp only [pairedOffPoleTailDerivativeRemainderCoefficient,Rat.natCast_add,Rat.natCast_mul,
    show ((768:Nat):Rat)=768 by decide +kernel,show ((196608:Nat):Rat)=196608 by decide +kernel,
    show ((6291456:Nat):Rat)=6291456 by decide +kernel]
  dsimp only [A]
  grind only

theorem pairedOffPoleTailDerivativeTerm_remainder_bound (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder (pairedOffPoleTailDerivativeTermMap B n) a ha
      (pairedOffPoleTailSecondDerivativeTerm B n a ha) z hz)
      ((pairedOffPoleTailDerivativeRemainderCoefficient B:Rat)*reciprocalSquare (n+1)*H*H) :=
  Small.congr (pairedOffPoleTailDerivativeRemainder B n a z ha hz).property
    (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (equiv_symm (pairedOffPoleTailDerivativeTerm_remainder_identity B n a z ha hz))
    (pairedOffPoleTailDerivativeRemainder_bound B n a z ha hz H hH hd)

end ComputableAnalysis.ModularForms
