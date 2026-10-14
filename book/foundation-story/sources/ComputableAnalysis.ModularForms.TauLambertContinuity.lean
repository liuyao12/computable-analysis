import ComputableAnalysis.ModularForms.TauLambertGeometricVariation

/-! Explicit whole-disk continuity of the actual weighted Lambert sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem block_sub (f g : Nat → ComplexRaw) (hf : ∀ n, (f n).Valid) (hg : ∀ n, (g n).Valid) (N : Nat) :
    (ScalarSeries.block (fun n => sub (f n) (g n)) 0 N).Equiv
      (sub (ScalarSeries.block f 0 N) (ScalarSeries.block g 0 N)) := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := ofQComplex_valid _)
      (hright := sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
    change (0:ComplexRawQuotient.Value)=0-0
    grind only
  | succ N ih =>
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ScalarSeries.block_valid _ (fun n => sub_valid (hf n) (hg n)) 0 N)
      (hright := sub_valid (ScalarSeries.block_valid f hf 0 N) (ScalarSeries.block_valid g hg 0 N)) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ (fun n => sub_valid (hf n) (hg n)) 0 (N+1))
      (hright := sub_valid (ScalarSeries.block_valid f hf 0 (N+1)) (ScalarSeries.block_valid g hg 0 (N+1)))
    simp only [ScalarSeries.block,Nat.zero_add]
    rw [ComplexRawQuotient.ofRaw_add _ _ (ScalarSeries.block_valid _ (fun n => sub_valid (hf n) (hg n)) 0 N)
      (sub_valid (hf N) (hg N)),hi]
    let F := ComplexRawQuotient.ofRaw (ScalarSeries.block f 0 N) (ScalarSeries.block_valid f hf 0 N)
    let G := ComplexRawQuotient.ofRaw (ScalarSeries.block g 0 N) (ScalarSeries.block_valid g hg 0 N)
    let X := ComplexRawQuotient.ofRaw (f N) (hf N)
    let Y := ComplexRawQuotient.ofRaw (g N) (hg N)
    change (F-G)+(X-Y)=(F+X)-(G+Y)
    grind only

/-- The infinite weighted Lambert value has a uniform displacement bound. -/
theorem tauLambertValue_difference_bound (a z : Scalar) (ha : tauEulerNomeDomain a)
    (hz : tauEulerNomeDomain z) (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H) :
    Small (sub (tauLambertValue z hz).val (tauLambertValue a ha).val) (256*H) := by
  let f := weightedLambertTerm z (1/1024) 1
  let g := weightedLambertTerm a (1/1024) 1
  have hf := weightedLambertTerm_valid z (1/1024) 1 (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ z hz)
  have hg := weightedLambertTerm_valid a (1/1024) 1 (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ a ha)
  let p := fun N => sub (ScalarSeries.block f 0 N) (ScalarSeries.block g 0 N)
  have hbound : ∀ N, Small (p N) (256*H) := by
    intro N
    have hterm : ∀ n, Small (sub (f n) (g n)) (2*(64*H)*(8*(1/1024:Rat))^n) := by
      intro n
      have h := weightedLambertOneTerm_geometric_difference_bound a z (1/1024) H
        (by decide +kernel) (by decide +kernel) hH (LocalODE.interior_bound _ a ha)
        (LocalODE.interior_bound _ z hz) hza n
      have he : 128*(8*(1/1024:Rat))^n*H=2*(64*H)*(8*(1/1024:Rat))^n := by grind only
      rw [he] at h
      exact h
    have h := ScalarSeries.block_bound (fun n => sub (f n) (g n)) (64*H) (8*(1/1024))
      (Rat.mul_nonneg (by decide +kernel) hH) (by decide +kernel) (by decide +kernel) hterm 0 N
    have hh := Small.congr (ScalarSeries.block_valid _ (fun n => sub_valid (hf n) (hg n)) 0 N)
      (sub_valid (ScalarSeries.block_valid f hf 0 N) (ScalarSeries.block_valid g hg 0 N))
      (block_sub f g hf hg N) h
    have he : 4*(64*H)*(8*(1/1024:Rat))^0=256*H := by rw [Rat.pow_zero]; grind only
    rw [he] at hh
    exact hh
  have he := SeriesLimitLaws.shrinks_scale _
    (weightedLambertSum_tail_shrinks (1/1024) 1 (by decide +kernel) (by decide +kernel)) 2 (by decide +kernel)
  apply SeriesLimitLaws.small_of_prefix_bound _
    (sub_valid (tauLambertValue z hz).property (tauLambertValue a ha).property)
    p (fun N => sub_valid (ScalarSeries.block_valid f hf 0 N) (ScalarSeries.block_valid g hg 0 N)) _ _ he
  · intro N
    have hzN := weightedLambertSum_close z (1/1024) 1 (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ z hz) (by decide +kernel) N
    have haN := weightedLambertSum_close a (1/1024) 1 (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ a ha) (by decide +kernel) N
    have h := SeriesLimitLaws.small_sub hzN haN
    have heq : (sub (sub (tauLambertValue z hz).val (ScalarSeries.block f 0 N))
        (sub (tauLambertValue a ha).val (ScalarSeries.block g 0 N))).Equiv
        (sub (sub (tauLambertValue z hz).val (tauLambertValue a ha).val) (p N)) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := sub_valid (sub_valid (tauLambertValue z hz).property (ScalarSeries.block_valid f hf 0 N))
          (sub_valid (tauLambertValue a ha).property (ScalarSeries.block_valid g hg 0 N)))
        (hright := sub_valid (sub_valid (tauLambertValue z hz).property (tauLambertValue a ha).property)
          (sub_valid (ScalarSeries.block_valid f hf 0 N) (ScalarSeries.block_valid g hg 0 N)))
      let Z := ComplexRawQuotient.ofRaw (tauLambertValue z hz).val (tauLambertValue z hz).property
      let A := ComplexRawQuotient.ofRaw (tauLambertValue a ha).val (tauLambertValue a ha).property
      let F := ComplexRawQuotient.ofRaw (ScalarSeries.block f 0 N) (ScalarSeries.block_valid f hf 0 N)
      let G := ComplexRawQuotient.ofRaw (ScalarSeries.block g 0 N) (ScalarSeries.block_valid g hg 0 N)
      change (Z-F)-(A-G)=(Z-A)-(F-G)
      grind only
    have hh := Small.congr
      (sub_valid (sub_valid (tauLambertValue z hz).property (ScalarSeries.block_valid f hf 0 N))
        (sub_valid (tauLambertValue a ha).property (ScalarSeries.block_valid g hg 0 N)))
      (sub_valid (sub_valid (tauLambertValue z hz).property (tauLambertValue a ha).property)
        (sub_valid (ScalarSeries.block_valid f hf 0 N) (ScalarSeries.block_valid g hg 0 N))) heq h
    apply hh.mono
    grind only
  · exact hbound

/-- Executable whole-disk continuity modulus for the actual weighted sum. -/
def tauLambertValue_continuous : ContinuousOn tauEulerNomeDomain tauLambertValue where
  delta _ _ eps := divideRadius eps ⟨256,by decide +kernel⟩
  estimate a ha eps z hz hd := by
    have h := tauLambertValue_difference_bound a z ha hz
      (divideRadius eps ⟨256,by decide +kernel⟩).val
      (Rat.le_of_lt (divideRadius eps ⟨256,by decide +kernel⟩).property) hd
    rw [divideRadius_identity eps ⟨256,by decide +kernel⟩] at h
    exact h

end ComputableAnalysis.ModularForms
