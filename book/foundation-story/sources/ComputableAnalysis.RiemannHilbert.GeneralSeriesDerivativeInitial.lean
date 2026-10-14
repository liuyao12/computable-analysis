import ComputableAnalysis.RiemannHilbert.GeneralSeriesHolomorphic
namespace ComputableAnalysis.RiemannHilbert.BoundedSeries
open ComplexRaw FunctionTheory LocalODE
set_option maxHeartbeats 400000

/-- Differentiated finite sums at zero retain exactly the linear coefficient. -/
theorem derivativeBlock_zero_succ (c : Nat → ComplexRaw) (hc : ∀ i, (c i).Valid) (N : Nat) :
    (derivativeBlock c zero 0 (N+1)).Equiv (c 1) := by
  induction N with
  | zero =>
    change (add zero (scaleRat 1 (mul (c 1) one))).Equiv (c 1)
    exact equiv_trans (add_valid (ofQComplex_valid _) (scaleRat_valid (mul_valid (hc 1) (ofQComplex_valid _))))
      (scaleRat_valid (mul_valid (hc 1) (ofQComplex_valid _))) (hc 1)
      (zero_add_equiv _ (scaleRat_valid (mul_valid (hc 1) (ofQComplex_valid _))))
      (equiv_trans (scaleRat_valid (mul_valid (hc 1) (ofQComplex_valid _)))
        (mul_valid (hc 1) (ofQComplex_valid _)) (hc 1)
        (scaleRat_one_equiv _ (mul_valid (hc 1) (ofQComplex_valid _))) (mul_one_equiv _ (hc 1)))
  | succ N ih =>
    have ht : (derivativeTerm c zero (N+1)).Equiv zero := by
      have hmul : (mul (c (N+1+1)) (power zero (N+1))).Equiv zero :=
        equiv_trans (mul_valid (hc _) (power_valid zero (ofQComplex_valid _) (N+1)))
          (mul_valid (hc _) (ofQComplex_valid _)) (ofQComplex_valid _)
          (mul_equiv (hc _) (hc _) (power_valid zero (ofQComplex_valid _) (N+1))
            (ofQComplex_valid _) (equiv_refl _ (hc _)) (power_zero_succ N))
          (mul_zero_equiv _ (hc _))
      exact equiv_trans (derivativeTerm_valid c zero hc (ofQComplex_valid _) (N+1))
        (scaleRat_valid (ofQComplex_valid _)) (ofQComplex_valid _)
        (scaleRat_equiv hmul) (scaleRat_zero_equiv ((N+1+1:Nat):Rat))
    rw [derivativeBlock.eq_2]
    simp only [Nat.zero_add]
    exact equiv_trans
      (add_valid (derivativeBlock_valid c zero hc (ofQComplex_valid _) 0 (N+1))
        (derivativeTerm_valid c zero hc (ofQComplex_valid _) (N+1)))
      (add_valid (hc 1) (ofQComplex_valid _)) (hc 1) (add_equiv ih ht) (add_zero_equiv _ (hc 1))

/-- The derivative of the constructed bounded series at zero is its linear coefficient. -/
theorem sumDerivative_zero (c : Nat → ComplexRaw) (hc : ∀ i, (c i).Valid)
    (C K R : Rat) (hC : 0≤C) (hK : 0≤K) (hR : 0≤R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hlocal : 4*K*R≤(1:Rat)/2) :
    (sumDerivative c zero hc (ofQComplex_valid _) C K R).Equiv (c 1) := by
  have hq : 0≤4*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hK) hR
  have ht : ShrinksToZero (derivativeTail C K R) := by
    have h := tail_bound_shrinks (C*K) (4*K*R) (Rat.mul_nonneg hC hK) hq hlocal
    have he : (fun N => 4*(C*K)*(4*K*R)^N)=derivativeTail C K R := by
      funext N
      dsimp [derivativeTail]
      grind only
    rw [he] at h
    exact h
  have hZ := sumDerivative_valid c zero hc (ofQComplex_valid _) C K R hC hK hR hcB
    (Small.zero hR) hlocal
  apply RepresentedCauchySum.unique
    (fun N => derivativeBlock c zero 0 (N+1))
    (fun N => derivativeBlock_valid c zero hc (ofQComplex_valid _) 0 (N+1))
    (fun N => derivativeTail C K R (N+1)) (SeriesLimitLaws.shrinks_shift _ ht 1)
    _ (c 1) hZ (hc 1)
  · intro N
    exact sumDerivative_close_prefix c zero hc (ofQComplex_valid _) C K R hC hK hR hcB
      (Small.zero hR) hlocal (N+1)
  · intro N
    have he := sub_congr (equiv_refl _ (hc 1)) (derivativeBlock_zero_succ c hc N)
    have hz : (sub (c 1) (c 1)).Equiv zero := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := sub_valid (hc 1) (hc 1)) (hright := ofQComplex_valid _)
      change ComplexRawQuotient.ofRaw (c 1) (hc 1)-ComplexRawQuotient.ofRaw (c 1) (hc 1)=(0:ScalarAlgebra.Value)
      grind only
    have hn : 0≤derivativeTail C K R (N+1) :=
      Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC) hK) (Rat.pow_nonneg hq)
    exact Small.congr (ofQComplex_valid _)
      (sub_valid (hc 1) (derivativeBlock_valid c zero hc (ofQComplex_valid _) 0 (N+1)))
      (equiv_symm (equiv_trans (sub_valid (hc 1) (derivativeBlock_valid c zero hc (ofQComplex_valid _) 0 (N+1)))
        (sub_valid (hc 1) (hc 1)) (ofQComplex_valid _) he hz)) (Small.zero hn)
end ComputableAnalysis.RiemannHilbert.BoundedSeries
