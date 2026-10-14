import ComputableAnalysis.RiemannHilbert.GeneralSeries
import ComputableAnalysis.RiemannHilbert.SeriesSuperposition

/-! Exact division of a bounded represented power series by its coordinate
after subtracting the constant coefficient. The successor series executes
at zero as well. Its majorant and the factorization follow from finite
prefix identities and explicit shrinking tails, without a completion. -/
namespace ComputableAnalysis.RiemannHilbert.BoundedSeries
open ComplexRaw FunctionTheory LocalODE
set_option autoImplicit false

theorem successor_majorant (c : Nat → ComplexRaw) (C K : Rat)
    (h : ∀ k, Small (c k) (C*K^k)) (k : Nat) :
    Small (c (k+1)) ((C*K)*K^k) := by
  have hs := h (k+1)
  rw [Rat.pow_succ] at hs
  have he : C*(K^k*K)=(C*K)*K^k := by grind only
  rw [he] at hs
  exact hs

theorem successor_prefix (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ k, (c k).Valid) (hz : z.Valid) (N : Nat) :
    (ScalarSeries.block (seriesTerm c z) 0 (N+1)).Equiv
      (add (c 0) (mul z (ScalarSeries.block (seriesTerm (fun k => c (k+1)) z) 0 N))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ScalarSeries.block_valid _ (seriesTerm_valid c z hc hz) 0 (N+1))
    (hright := add_valid (hc 0) (mul_valid hz
      (ScalarSeries.block_valid _ (seriesTerm_valid (fun k => c (k+1)) z (fun k => hc (k+1)) hz) 0 N)))
  change ComplexRawQuotient.ofRaw (ScalarSeries.block (seriesTerm c z) 0 (N+1))
    (ScalarSeries.block_valid _ (seriesTerm_valid c z hc hz) 0 (N+1)) =
    ComplexRawQuotient.ofRaw (c 0) (hc 0)+ComplexRawQuotient.ofRaw z hz*
      ComplexRawQuotient.ofRaw (ScalarSeries.block (seriesTerm (fun k => c (k+1)) z) 0 N)
        (ScalarSeries.block_valid _ (seriesTerm_valid (fun k => c (k+1)) z (fun k => hc (k+1)) hz) 0 N)
  rw [ScalarSeries.prefix_image, ScalarSeries.prefix_image]
  induction N with
  | zero =>
    change 0+ComplexRawQuotient.ofRaw (c 0) (hc 0)*1=
      ComplexRawQuotient.ofRaw (c 0) (hc 0)+ComplexRawQuotient.ofRaw z hz*0
    grind only
  | succ N ih =>
    change FiniteProducts.partialSum (fun k => ComplexRawQuotient.ofRaw (seriesTerm c z k)
      (seriesTerm_valid c z hc hz k)) (N+1)+
      ComplexRawQuotient.ofRaw (c (N+1)) (hc (N+1))*ComplexRawQuotient.ofRaw (power z (N+1)) (power_valid z hz (N+1))=
      ComplexRawQuotient.ofRaw (c 0) (hc 0)+ComplexRawQuotient.ofRaw z hz*
        (FiniteProducts.partialSum (fun k => ComplexRawQuotient.ofRaw (seriesTerm (fun k => c (k+1)) z k)
          (seriesTerm_valid (fun k => c (k+1)) z (fun k => hc (k+1)) hz k)) N+
          ComplexRawQuotient.ofRaw (c (N+1)) (hc (N+1))*ComplexRawQuotient.ofRaw (power z N) (power_valid z hz N))
    have hp : ComplexRawQuotient.ofRaw (power z (N+1)) (power_valid z hz (N+1))=
        ComplexRawQuotient.ofRaw (power z N) (power_valid z hz N)*ComplexRawQuotient.ofRaw z hz := rfl
    rw [ih,hp]
    grind only

theorem sumValue_successor (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ k, (c k).Valid) (hz : z.Valid) (C K R : Rat)
    (hC : 0≤C) (hK : 0≤K) (hR : 0≤R)
    (hb : ∀ k, Small (c k) (C*K^k)) (hzR : Small z R) (hl : 2*K*R≤(1:Rat)/2) :
    (sumValue c z hc hz C K R).Equiv
      (add (c 0) (mul z (sumValue (fun k => c (k+1)) z (fun k => hc (k+1)) hz (C*K) K R))) := by
  let q := 2*K*R
  let t := fun N => ScalarSeries.block (seriesTerm c z) 0 (N+1)
  let u := fun N => ScalarSeries.block (seriesTerm (fun k => c (k+1)) z) 0 N
  let S := sumValue c z hc hz C K R
  let T := sumValue (fun k => c (k+1)) z (fun k => hc (k+1)) hz (C*K) K R
  have hCK := Rat.mul_nonneg hC hK
  have hq : 0≤q := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hK) hR
  have ht : ∀ N, (t N).Valid := fun N => ScalarSeries.block_valid _ (seriesTerm_valid c z hc hz) 0 (N+1)
  have hu : ∀ N, (u N).Valid := fun N => ScalarSeries.block_valid _
    (seriesTerm_valid (fun k => c (k+1)) z (fun k => hc (k+1)) hz) 0 N
  have hS := sumValue_valid c z hc hz C K R hC hK hR hb hzR hl
  have hT := sumValue_valid (fun k => c (k+1)) z (fun k => hc (k+1)) hz (C*K) K R hCK hK hR
    (successor_majorant c C K hb) hzR hl
  let e := fun N => 4*C*q^(N+1)+4*(2*R*(C*K))*q^N
  have he : ShrinksToZero e := RepresentedCauchySum.sum_shrinks _ _
    (SeriesLimitLaws.shrinks_shift _ (tail_bound_shrinks C q hC hq hl) 1)
    (tail_bound_shrinks (2*R*(C*K)) q
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hCK) hq hl)
  apply RepresentedCauchySum.unique t ht e he S (add (c 0) (mul z T)) hS (add_valid (hc 0) (mul_valid hz hT))
  · intro N
    apply (coefficientSum_close c z hc hz C K R hC hK hR hb hzR hl (N+1)).mono
    change 4*C*q^(N+1)≤4*C*q^(N+1)+4*(2*R*(C*K))*q^N
    have hn := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel : (0:Rat)≤8) hR) hCK) (Rat.pow_nonneg hq (n := N))
    grind only
  · intro N
    have hs := Small.mul hz (sub_valid hT (hu N)) hR
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hCK) (Rat.pow_nonneg hq (n := N))) hzR
      (coefficientSum_close (fun k => c (k+1)) z (fun k => hc (k+1)) hz (C*K) K R
        hCK hK hR (successor_majorant c C K hb) hzR hl N)
    have hf : (sub (add (c 0) (mul z T)) (t N)).Equiv (mul z (sub T (u N))) := by
      have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
        (hleft := ht N) (hright := add_valid (hc 0) (mul_valid hz (hu N))) (successor_prefix c z hc hz N)
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := sub_valid (add_valid (hc 0) (mul_valid hz hT)) (ht N))
        (hright := mul_valid hz (sub_valid hT (hu N)))
      change ComplexRawQuotient.ofRaw (c 0) (hc 0)+ComplexRawQuotient.ofRaw z hz*ComplexRawQuotient.ofRaw T hT-
        ComplexRawQuotient.ofRaw (t N) (ht N)=ComplexRawQuotient.ofRaw z hz*
          (ComplexRawQuotient.ofRaw T hT-ComplexRawQuotient.ofRaw (u N) (hu N))
      rw [hp]
      change ComplexRawQuotient.ofRaw (c 0) (hc 0)+ComplexRawQuotient.ofRaw z hz*ComplexRawQuotient.ofRaw T hT-
        (ComplexRawQuotient.ofRaw (c 0) (hc 0)+ComplexRawQuotient.ofRaw z hz*ComplexRawQuotient.ofRaw (u N) (hu N))=
        ComplexRawQuotient.ofRaw z hz*(ComplexRawQuotient.ofRaw T hT-ComplexRawQuotient.ofRaw (u N) (hu N))
      grind only
    apply (Small.congr (mul_valid hz (sub_valid hT (hu N)))
      (sub_valid (add_valid (hc 0) (mul_valid hz hT)) (ht N)) (equiv_symm hf) hs).mono
    change 2*R*(4*(C*K)*q^N)≤4*C*q^(N+1)+4*(2*R*(C*K))*q^N
    have hn := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel : (0:Rat)≤4) hC) (Rat.pow_nonneg hq (n := N+1))
    grind only

end ComputableAnalysis.RiemannHilbert.BoundedSeries
