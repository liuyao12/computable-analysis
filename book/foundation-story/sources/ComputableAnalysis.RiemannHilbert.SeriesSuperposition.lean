import ComputableAnalysis.RiemannHilbert.CoefficientSeries

/-! Exact addition and arbitrary represented complex scaling of supplied sums. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarSeries
open ComplexRaw FunctionTheory LocalODE

theorem block_add (t u : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (hu : ∀ i, (u i).Valid)
    (N k : Nat) :
    (block (fun i => add (t i) (u i)) N k).Equiv (add (block t N k) (block u N k)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := block_valid _ (fun i => add_valid (ht i) (hu i)) N k)
    (hright := add_valid (block_valid t ht N k) (block_valid u hu N k))
  change ComplexRawQuotient.ofRaw (block (fun i => add (t i) (u i)) N k)
    (block_valid _ (fun i => add_valid (ht i) (hu i)) N k) =
    ComplexRawQuotient.ofRaw (block t N k) (block_valid t ht N k)+
    ComplexRawQuotient.ofRaw (block u N k) (block_valid u hu N k)
  rw [block_image _ (fun i => add_valid (ht i) (hu i)) N k,
    block_image t ht N k, block_image u hu N k]
  have hf : (fun i => ComplexRawQuotient.ofRaw (add (t i) (u i)) (add_valid (ht i) (hu i))) =
      (fun i => ComplexRawQuotient.ofRaw (t i) (ht i)+ComplexRawQuotient.ofRaw (u i) (hu i)) := by
    funext i
    exact ComplexRawQuotient.ofRaw_add _ _ (ht i) (hu i)
  rw [hf]
  exact FiniteProducts.prefix_add _ _ k

theorem block_scale (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid)
    (a : ComplexRaw) (ha : a.Valid) (N k : Nat) :
    (block (fun i => mul a (t i)) N k).Equiv (mul a (block t N k)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := block_valid _ (fun i => mul_valid ha (ht i)) N k)
    (hright := mul_valid ha (block_valid t ht N k))
  change ComplexRawQuotient.ofRaw (block (fun i => mul a (t i)) N k)
    (block_valid _ (fun i => mul_valid ha (ht i)) N k) =
    ComplexRawQuotient.ofRaw a ha*ComplexRawQuotient.ofRaw (block t N k) (block_valid t ht N k)
  rw [block_image _ (fun i => mul_valid ha (ht i)) N k, block_image t ht N k]
  have hf : (fun i => ComplexRawQuotient.ofRaw (mul a (t i)) (mul_valid ha (ht i))) =
      (fun i => ComplexRawQuotient.ofRaw (t i) (ht i)*ComplexRawQuotient.ofRaw a ha) := by
    funext i
    rw [ComplexRawQuotient.ofRaw_mul _ _ ha (ht i), ComplexRawQuotient.mul_comm]
  rw [hf]
  rw [ComplexRawQuotient.mul_comm]
  exact FiniteProducts.prefix_mul _ _ k

theorem value_add (t u : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (hu : ∀ i, (u i).Valid)
    (C D q : Rat) (hC : 0 ≤ C) (hD : 0 ≤ D) (hq : 0 ≤ q) (hlocal : q ≤ (1 : Rat)/2)
    (hT : ∀ i, Small (t i) (2*C*q^i)) (hU : ∀ i, Small (u i) (2*D*q^i)) :
    (value (fun i => add (t i) (u i)) (fun i => add_valid (ht i) (hu i)) (C+D) q).Equiv
      (add (value t ht C q) (value u hu D q)) := by
  have hB : ∀ i, Small (add (t i) (u i)) (2*(C+D)*q^i) := by
    intro i
    have hs := small_add (hT i) (hU i)
    have he : 2*C*q^i+2*D*q^i=2*(C+D)*q^i := by grind
    rw [he] at hs; exact hs
  have htV := value_valid t ht C q hC hq hlocal hT
  have huV := value_valid u hu D q hD hq hlocal hU
  apply RepresentedCauchySum.unique _ (block_valid _ (fun i => add_valid (ht i) (hu i)) 0)
    (fun N => 4*(C+D)*q^N) (tail_bound_shrinks (C+D) q (Rat.add_nonneg hC hD) hq hlocal) _ _
    (value_valid _ _ (C+D) q (Rat.add_nonneg hC hD) hq hlocal hB) (add_valid htV huV)
    (value_close _ _ (C+D) q (Rat.add_nonneg hC hD) hq hlocal hB)
  intro N
  have hp := block_valid t ht 0 N
  have hr := block_valid u hu 0 N
  have hs := small_add (value_close t ht C q hC hq hlocal hT N)
    (value_close u hu D q hD hq hlocal hU N)
  have he : 4*C*q^N+4*D*q^N=4*(C+D)*q^N := by grind
  rw [he] at hs
  have hi := SeriesLimitLaws.addition_difference (value t ht C q) (block t 0 N)
    (value u hu D q) (block u 0 N) htV hp huV hr
  have hs' := Small.congr (add_valid (sub_valid htV hp) (sub_valid huV hr))
    (sub_valid (add_valid htV huV) (add_valid hp hr)) (equiv_symm hi) hs
  exact Small.congr (sub_valid (add_valid htV huV) (add_valid hp hr))
    (sub_valid (add_valid htV huV) (block_valid _ (fun i => add_valid (ht i) (hu i)) 0 N))
    (FunctionTheory.sub_congr (equiv_refl _ (add_valid htV huV))
      (equiv_symm (block_add t u ht hu 0 N))) hs'

theorem value_scale (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid)
    (a : ComplexRaw) (ha : a.Valid) (B C q : Rat) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hlocal : q ≤ (1 : Rat)/2) (haB : Small a B)
    (hT : ∀ i, Small (t i) (2*C*q^i)) :
    (value (fun i => mul a (t i)) (fun i => mul_valid ha (ht i)) (2*B*C) q).Equiv
      (mul a (value t ht C q)) := by
  have hBC : 0 ≤ 2*B*C := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hC
  have hU : ∀ i, Small (mul a (t i)) (2*(2*B*C)*q^i) := by
    intro i
    have hs := Small.mul ha (ht i) hB
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hq)) haB (hT i)
    have he : 2*B*(2*C*q^i)=2*(2*B*C)*q^i := by grind
    rw [he] at hs; exact hs
  have htV := value_valid t ht C q hC hq hlocal hT
  apply RepresentedCauchySum.unique _ (block_valid _ (fun i => mul_valid ha (ht i)) 0)
    (fun N => 4*(2*B*C)*q^N) (tail_bound_shrinks (2*B*C) q hBC hq hlocal) _ _
    (value_valid _ _ (2*B*C) q hBC hq hlocal hU) (mul_valid ha htV)
    (value_close _ _ (2*B*C) q hBC hq hlocal hU)
  intro N
  have hp := block_valid t ht 0 N
  have hs := Small.mul ha (sub_valid htV hp) hB
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hq)) haB
    (value_close t ht C q hC hq hlocal hT N)
  have hi : (sub (mul a (value t ht C q)) (mul a (block t 0 N))).Equiv
      (mul a (sub (value t ht C q) (block t 0 N))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (mul_valid ha htV) (mul_valid ha hp))
      (hright := mul_valid ha (sub_valid htV hp))
    change ComplexRawQuotient.ofRaw a ha*ComplexRawQuotient.ofRaw (value t ht C q) htV-
      ComplexRawQuotient.ofRaw a ha*ComplexRawQuotient.ofRaw (block t 0 N) hp =
      ComplexRawQuotient.ofRaw a ha*(ComplexRawQuotient.ofRaw (value t ht C q) htV-
        ComplexRawQuotient.ofRaw (block t 0 N) hp)
    grind
  have he : 2*B*(4*C*q^N)=4*(2*B*C)*q^N := by grind
  rw [he] at hs
  have hs' := Small.congr (mul_valid ha (sub_valid htV hp))
    (sub_valid (mul_valid ha htV) (mul_valid ha hp)) (equiv_symm hi) hs
  exact Small.congr (sub_valid (mul_valid ha htV) (mul_valid ha hp))
    (sub_valid (mul_valid ha htV) (block_valid _ (fun i => mul_valid ha (ht i)) 0 N))
    (FunctionTheory.sub_congr (equiv_refl _ (mul_valid ha htV)) (equiv_symm (block_scale t ht a ha 0 N))) hs'

end ComputableAnalysis.RiemannHilbert.ScalarSeries
