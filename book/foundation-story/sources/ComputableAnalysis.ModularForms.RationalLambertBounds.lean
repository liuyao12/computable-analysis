import ComputableAnalysis.ModularForms.WideLambertFirstValueRemainder
import ComputableAnalysis.ModularForms.WideLambertThirdValueRemainder
import ComputableAnalysis.ModularForms.WideLambertFifthValueRemainder

/-! Uniform estimates for deriving the three Eisenstein Lambert sums from
rational chart samples. Existing represented sums occur only in proofs. -/
namespace ComputableAnalysis.ModularForms.RationalLambert
open ComplexRaw FunctionTheory RiemannHilbert
set_option maxHeartbeats 1000000

private theorem sub_zero_equiv (z : ComplexRaw) (hz : z.Valid) : (sub z zero).Equiv z := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := sub_valid hz (ofQComplex_valid _)) (hright := hz)
  change ComplexRawQuotient.ofRaw z hz-0=ComplexRawQuotient.ofRaw z hz
  grind only

def comparison (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (k : Nat) : Scalar :=
  if k=1 then wideLambertFirstValue q hq else if k=3 then wideLambertThirdValue q hq else wideLambertFifthValue q hq

def slope (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (k : Nat) : Scalar :=
  if k=1 then wideLambertFirstSlopeValue q hq else if k=3 then wideLambertThirdSlopeValue q hq else wideLambertFifthSlopeValue q hq

theorem slope_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (k : Nat) : Small (slope q hq k).val 2048 := by
  unfold slope
  split
  · have h := wideLambertFirstSlopeValue_close_prefix q hq 0
    have he := sub_zero_equiv _ (wideLambertFirstSlopeValue q hq).property
    exact (Small.congr (sub_valid (wideLambertFirstSlopeValue q hq).property (ofQComplex_valid _))
      (wideLambertFirstSlopeValue q hq).property he h).mono (by decide +kernel)
  · split
    · have h := wideLambertThirdSlopeValue_close_prefix q hq 0
      have he := sub_zero_equiv _ (wideLambertThirdSlopeValue q hq).property
      exact (Small.congr (sub_valid (wideLambertThirdSlopeValue q hq).property (ofQComplex_valid _))
        (wideLambertThirdSlopeValue q hq).property he h).mono (by decide +kernel)
    · have h := wideLambertFifthSlopeValue_close_prefix q hq 0
      have h' : Small (sub (wideLambertFifthSlopeValue q hq).val zero) 2048 := by
        simpa only [ScalarSeries.block,Rat.pow_zero,Rat.mul_one] using h
      exact Small.congr (sub_valid (wideLambertFifthSlopeValue q hq).property (ofQComplex_valid _))
        (wideLambertFifthSlopeValue q hq).property (sub_zero_equiv _ (wideLambertFifthSlopeValue q hq).property) h'

theorem remainder_bound (a z : Scalar) (ha : Small a.val ((1:Rat)/64)) (hz : Small z.val ((1:Rat)/64))
    (k : Nat) (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder (comparison z hz k).val (comparison a ha k).val
      (slope a ha k).val (sub z.val a.val)) (135168*H^2) := by
  unfold comparison slope
  split
  · exact wideLambertFirstValue_remainder_bound a z ha hz H hH hd
  · split
    · exact wideLambertThirdValue_remainder_bound a z ha hz H hH hd
    · exact wideLambertFifthValue_remainder_bound a z ha hz H hH hd

theorem difference_bound (a z : Scalar) (ha : Small a.val ((1:Rat)/64)) (hz : Small z.val ((1:Rat)/64))
    (k : Nat) (H : Rat) (hH : 0≤H) (hH1 : H≤1) (hd : Small (sub z.val a.val) H) :
    Small (sub (comparison z hz k).val (comparison a ha k).val) (139264*H) := by
  let v := sub z.val a.val
  let f := (comparison z hz k).val
  let g := (comparison a ha k).val
  let d := (slope a ha k).val
  have hr := remainder_bound a z ha hz k H hH hd
  have hp := Small.mul (slope a ha k).property (sub_valid z.property a.property) (by decide +kernel : (0:Rat)≤2048)
    hH (slope_bound a ha k) hd
  have hs := LocalODE.small_add hp hr
  have he := SeriesLimitLaws.add_difference (sub f g) (mul d v)
    (sub_valid (comparison z hz k).property (comparison a ha k).property)
    (mul_valid (slope a ha k).property (sub_valid z.property a.property))
  have hb := Small.congr (add_valid (mul_valid (slope a ha k).property (sub_valid z.property a.property))
    (SeriesLimitLaws.remainder_valid f g d v (comparison z hz k).property (comparison a ha k).property
      (slope a ha k).property (sub_valid z.property a.property)))
    (sub_valid (comparison z hz k).property (comparison a ha k).property) he hs
  apply hb.mono
  rw [Rat.pow_succ H 1,Rat.pow_one]
  have hsq := Rat.mul_le_mul_of_nonneg_right hH1 hH
  have hm := Rat.mul_le_mul_of_nonneg_left hsq (by decide +kernel : (0:Rat)≤135168)
  grind only

theorem triangle (a b c : ComplexRaw) (ha : a.Valid) (hb : b.Valid) (hc : c.Valid)
    (E F : Rat) (hab : Small (sub a b) E) (hbc : Small (sub b c) F) : Small (sub a c) (E+F) := by
  have he : (add (sub a b) (sub b c)).Equiv (sub a c) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid ha hb) (sub_valid hb hc)) (hright := sub_valid ha hc)
    change (ComplexRawQuotient.ofRaw a ha-ComplexRawQuotient.ofRaw b hb)+
      (ComplexRawQuotient.ofRaw b hb-ComplexRawQuotient.ofRaw c hc)=
      ComplexRawQuotient.ofRaw a ha-ComplexRawQuotient.ofRaw c hc
    grind only
  exact Small.congr (add_valid (sub_valid ha hb) (sub_valid hb hc)) (sub_valid ha hc) he
    (LocalODE.small_add hab hbc)

theorem pow_mono (a b : Rat) (ha : 0≤a) (hab : a≤b) (n : Nat) : a^n≤b^n := by
  induction n with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ n ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ha)
      (Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (Rat.le_trans ha hab)))

theorem comparison_tail (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (k : Nat) (hk : k=1 ∨ k=3 ∨ k=5) (N : Nat) :
    Small (sub (comparison q hq k).val (ScalarSeries.block (weightedLambertTerm q (1/64) k) 0 N))
      (8*((1:Rat)/2)^N) := by
  rcases hk with rfl | rfl | rfl
  · have ht := wideLambertFirstValue_close_prefix q hq N
    apply ht.mono
    have hp := pow_mono (1/16) (1/2) (by decide +kernel) (by decide +kernel) N
    have hm := Rat.mul_le_mul_of_nonneg_left hp (by decide +kernel : (0:Rat)≤1/2)
    have hm2 := Rat.mul_le_mul_of_nonneg_right (by decide +kernel : (1/2:Rat)≤8)
      (Rat.pow_nonneg (n := N) (by decide +kernel : (0:Rat)≤1/2))
    exact Rat.le_trans hm hm2
  · have ht := wideLambertThirdValue_close_prefix q hq N
    apply ht.mono
    have hp := pow_mono (1/4) (1/2) (by decide +kernel) (by decide +kernel) N
    have hm := Rat.mul_le_mul_of_nonneg_left hp (by decide +kernel : (0:Rat)≤1/2)
    have hm2 := Rat.mul_le_mul_of_nonneg_right (by decide +kernel : (1/2:Rat)≤8)
      (Rat.pow_nonneg (n := N) (by decide +kernel : (0:Rat)≤1/2))
    exact Rat.le_trans hm hm2
  · have ht := wideLambertFifthValue_close_prefix q hq N
    exact ht.mono (Rat.mul_le_mul_of_nonneg_left (pow_mono (1/8) (1/2) (by decide +kernel) (by decide +kernel) N) (by decide +kernel))

end ComputableAnalysis.ModularForms.RationalLambert
