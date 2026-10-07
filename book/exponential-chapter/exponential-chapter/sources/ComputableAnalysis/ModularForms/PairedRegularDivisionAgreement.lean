import ComputableAnalysis.ModularForms.PairedRegularDivisionPrefixes

/-! Exact multiplication agreement for the actual regular-division sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedRegularDivisionValue_product (z : Scalar) (hz : Small z.val (1/4)) :
    (mul z.val (pairedRegularDivisionValue z hz)).Equiv (pairedRegularPart z hz) := by
  let hd := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz
  let p := fun N => ScalarSeries.block (fun n => (pairedFullTerm z hd n).val) 0 (N+5)
  have hp : ∀ N, (p N).Valid := fun N => ScalarSeries.block_valid _ (fun n => (pairedFullTerm z hd n).property) 0 _
  let e := fun N => (16:Rat)*((N+1:Nat):Rat)⁻¹
  let d := fun N => (8:Rat)*((N+5:Nat):Rat)⁻¹
  have he : ShrinksToZero e := pairedReciprocalTail_shrinks 16
  have hdRate : ShrinksToZero d := SeriesLimitLaws.shrinks_shift _ (pairedReciprocalTail_shrinks 8) 4
  have en (N : Nat) : 0≤e N := Rat.mul_nonneg (by decide)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega))))
  have dn (N : Nat) : 0≤d N := Rat.mul_nonneg (by decide)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+5 by omega))))
  apply RepresentedCauchySum.unique p hp (fun N => e N+d N)
    (RepresentedCauchySum.sum_shrinks _ _ he hdRate) _ _
    (mul_valid z.property (pairedRegularDivisionValue_valid z hz)) (pairedRegularPart_valid z hz)
  · intro N
    let q := ScalarSeries.block (fun n => (pairedRegularDivisionTerm z hz n).val) 0 (N+5)
    have vq : q.Valid := ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionTerm z hz n).property) 0 _
    have hb := pairedRegularDivisionValue_close z hz (N+4)
    have hb' : Small (sub (pairedRegularDivisionValue z hz) q) (d N) := hb
    have hm := Small.mul z.property (sub_valid (pairedRegularDivisionValue_valid z hz) vq)
      (show (0:Rat)≤1/4 by decide +kernel) (dn N) hz hb'
    have hi := pairedRegularDivisionPrefix_product z hz (N+5)
    have hdist : (mul z.val (sub (pairedRegularDivisionValue z hz) q)).Equiv
        (sub (mul z.val (pairedRegularDivisionValue z hz)) (p N)) := by
      have hiq := ComplexRawQuotient.ofRaw_eq_ofRaw
        (hleft := mul_valid z.property vq) (hright := hp N) hi
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := mul_valid z.property (sub_valid (pairedRegularDivisionValue_valid z hz) vq))
        (hright := sub_valid (mul_valid z.property (pairedRegularDivisionValue_valid z hz)) (hp N))
      let Z := ComplexRawQuotient.ofRaw z.val z.property
      let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionValue z hz) (pairedRegularDivisionValue_valid z hz)
      let Q := ComplexRawQuotient.ofRaw q vq
      let P := ComplexRawQuotient.ofRaw (p N) (hp N)
      change Z*Q=P at hiq
      change Z*(T-Q)=Z*T-P
      grind only
    exact (Small.congr (mul_valid z.property (sub_valid (pairedRegularDivisionValue_valid z hz) vq))
      (sub_valid (mul_valid z.property (pairedRegularDivisionValue_valid z hz)) (hp N)) hdist hm).mono
      (by have := en N; have := dn N; change 2*(1/4:Rat)*d N≤e N+d N; grind only)
  · intro N
    have h1 : Small z.val ((1:Nat):Rat) := hz.mono (by decide +kernel)
    have ha := pairedSeriesValue_agrees z hd 1 h1
    have hb := pairedFullValue_close z hd 1 h1 N
    rw [show 4*1+(N+1)=N+5 by omega] at hb
    exact (Small.congr
      (sub_valid (pairedFullValue_valid z hd 1 h1) (hp N))
      (sub_valid (pairedRegularPart_valid z hz) (hp N))
      (FunctionTheory.sub_congr (equiv_symm ha) (equiv_refl _ (hp N))) hb).mono
      (by have := dn N; change e N≤e N+d N; grind only)

theorem pairedRegularDivisionValue_quotient (z : Scalar) (hz : Small z.val (1/4))
    (hn : NonzeroBoxSearch.Nonzero z) :
    (pairedRegularDivisionValue z hz).Equiv
      (mul (RepresentedReciprocal.inverse z hn).val (pairedRegularPart z hz)) := by
  have ht := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (pairedRegularDivisionValue_valid z hz))
    (hright := pairedRegularPart_valid z hz) (pairedRegularDivisionValue_product z hz)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (RepresentedReciprocal.inverse z hn).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse z hn)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := pairedRegularDivisionValue_valid z hz)
    (hright := mul_valid (RepresentedReciprocal.inverse z hn).property (pairedRegularPart_valid z hz))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionValue z hz) (pairedRegularDivisionValue_valid z hz)
  let S := ComplexRawQuotient.ofRaw (pairedRegularPart z hz) (pairedRegularPart_valid z hz)
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hn).val (RepresentedReciprocal.inverse z hn).property
  change Z*T=S at ht
  change Z*I=1 at hi
  change T=I*S
  grind only

end ComputableAnalysis.ModularForms
