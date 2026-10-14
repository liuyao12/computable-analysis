import ComputableAnalysis.RiemannHilbert.GeneralSeriesDerivative

/-! Independent derivative-continuity estimates for supplied coefficient series. -/
namespace ComputableAnalysis.RiemannHilbert.BoundedSeries
open ComplexRaw FunctionTheory LocalODE

theorem derivativeTerm_difference_factor (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid) (n : Nat) :
    (sub (derivativeTerm c z (n+1)) (derivativeTerm c a (n+1))).Equiv
      (scaleRat ((n+2 : Nat) : Rat)
        (mul (c (n+2)) (sub (power z (n+1)) (power a (n+1))))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (derivativeTerm_valid c z hc hz (n+1))
      (derivativeTerm_valid c a hc ha (n+1)))
    (hright := scaleRat_valid (mul_valid (hc (n+2))
      (sub_valid (power_valid z hz (n+1)) (power_valid a ha (n+1)))))
  change ComplexRawQuotient.scaleRat ((n+2 : Nat) : Rat)
      (ComplexRawQuotient.ofRaw (c (n+2)) (hc _)*
       ComplexRawQuotient.ofRaw (power z (n+1)) (power_valid z hz _)) -
    ComplexRawQuotient.scaleRat ((n+2 : Nat) : Rat)
      (ComplexRawQuotient.ofRaw (c (n+2)) (hc _)*
       ComplexRawQuotient.ofRaw (power a (n+1)) (power_valid a ha _)) =
    ComplexRawQuotient.scaleRat ((n+2 : Nat) : Rat)
      (ComplexRawQuotient.ofRaw (c (n+2)) (hc _)*
       (ComplexRawQuotient.ofRaw (power z (n+1)) (power_valid z hz _) -
        ComplexRawQuotient.ofRaw (power a (n+1)) (power_valid a ha _)))
  rw [ScalarAlgebra.scale_natural, ScalarAlgebra.scale_natural, ScalarAlgebra.scale_natural]
  grind

theorem derivativeTerm_difference_bound (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid)
    (C K R H : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hcB : ∀ n, Small (c n) (C*K^n))
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H) (n : Nat) :
    Small (sub (derivativeTerm c z (n+1)) (derivativeTerm c a (n+1)))
      (8*C*K^2*H*(8*K*R)^n) := by
  have hq : 0 ≤ 2*R := Rat.mul_nonneg (by decide) hR
  have hn1 : 0 ≤ ((n+1 : Nat) : Rat) := Rat.le_of_lt ((Rat.natCast_pos).2 (by omega))
  have hn2 : 0 ≤ ((n+2 : Nat) : Rat) := Rat.le_of_lt ((Rat.natCast_pos).2 (by omega))
  have hdB : 0 ≤ 2*((n+1 : Nat) : Rat)*(2*R)^n*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hn1) (Rat.pow_nonneg hq)) hH
  have hs := Small.mul (hc (n+2))
    (sub_valid (power_valid z hz (n+1)) (power_valid a ha (n+1)))
    (Rat.mul_nonneg hC (Rat.pow_nonneg hK)) hdB
    (hcB (n+2))
    (power_difference_bound a z ha hz R H hR hH haR hzR hza n)
  have ht := small_scale hn2 hs
  have hv := Small.congr
    (scaleRat_valid (mul_valid (hc (n+2))
      (sub_valid (power_valid z hz (n+1)) (power_valid a ha (n+1)))))
    (sub_valid (derivativeTerm_valid c z hc hz (n+1))
      (derivativeTerm_valid c a hc ha (n+1)))
    (equiv_symm (derivativeTerm_difference_factor c a z hc ha hz n)) ht
  apply hv.mono
  have hindex : ((n+2 : Nat) : Rat)*((n+1 : Nat) : Rat) ≤ 2*(4 : Rat)^n := by
    rw [← cast_four_pow]
    exact_mod_cast quadratic_index_bound n
  have hconst : 0 ≤ 4*C*K^(n+2)*(2*R)^n*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC)
      (Rat.pow_nonneg hK)) (Rat.pow_nonneg hq)) hH
  have hle := Rat.mul_le_mul_of_nonneg_left hindex hconst
  have hp : (8*K*R)^n = (4 : Rat)^n*K^n*(2*R)^n := by
    have he : 8*K*R = (4*K)*(2*R) := by grind
    rw [he, rational_mul_pow, rational_mul_pow]
  rw [hp]
  simp only [Rat.pow_succ] at hle ⊢
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem derivativeBlock_difference_majorant (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid)
    (C K R H : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hcB : ∀ n, Small (c n) (C*K^n))
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H) (N : Nat) :
    Small (sub (derivativeBlock c z 0 (N+1)) (derivativeBlock c a 0 (N+1)))
      (RationalMajorant.geomTailPartial (8*C*K^2*H) (8*K*R) 0 N) := by
  induction N with
  | zero =>
    have he : (sub (derivativeBlock c z 0 1) (derivativeBlock c a 0 1)).Equiv zero :=
      add_neg_equiv _ (derivativeBlock_valid c z hc hz 0 1)
    exact Small.congr (ofQComplex_valid _) (sub_valid
      (derivativeBlock_valid c z hc hz 0 1)
      (derivativeBlock_valid c a hc ha 0 1)) (equiv_symm he)
      (Small.zero (by change (0 : Rat) ≤ 0; decide))
  | succ N ih =>
    have hs := small_add ih (derivativeTerm_difference_bound c a z hc ha hz
      C K R H hC hK hR hH hcB haR hzR hza N)
    have ht := Small.congr
      (add_valid
        (sub_valid (derivativeBlock_valid c z hc hz 0 (N+1))
          (derivativeBlock_valid c a hc ha 0 (N+1)))
        (sub_valid (derivativeTerm_valid c z hc hz (N+1))
          (derivativeTerm_valid c a hc ha (N+1))))
      (sub_valid
        (add_valid (derivativeBlock_valid c z hc hz 0 (N+1))
          (derivativeTerm_valid c z hc hz (N+1)))
        (add_valid (derivativeBlock_valid c a hc ha 0 (N+1))
          (derivativeTerm_valid c a hc ha (N+1))))
      (equiv_symm (SeriesLimitLaws.addition_difference
        (derivativeBlock c z 0 (N+1)) (derivativeBlock c a 0 (N+1))
        (derivativeTerm c z (N+1)) (derivativeTerm c a (N+1))
        (derivativeBlock_valid c z hc hz 0 (N+1))
        (derivativeBlock_valid c a hc ha 0 (N+1))
        (derivativeTerm_valid c z hc hz (N+1))
        (derivativeTerm_valid c a hc ha (N+1)))) hs
    simpa only [derivativeBlock.eq_2, Nat.zero_add, RationalMajorant.geomTailPartial] using ht

theorem derivativeBlock_difference_bound (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid)
    (C K R H : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hcB : ∀ n, Small (c n) (C*K^n))
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) (N : Nat) :
    Small (sub (derivativeBlock c z 0 (N+1)) (derivativeBlock c a 0 (N+1)))
      (16*C*K^2*H) := by
  have hs := derivativeBlock_difference_majorant c a z hc ha hz C K R H
    hC hK hR hH hcB haR hzR hza N
  apply hs.mono
  have ht := RationalMajorant.geometric_tail_partial_bound
    (C := 8*C*K^2*H) (r := 8*K*R) (N := 0) (k := N)
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hK)) hH)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
  unfold RationalMajorant.geomTailBound at ht
  simp only [Rat.pow_zero, Rat.mul_one] at ht
  grind

theorem sumDerivative_lipschitz (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid)
    (C K R H : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hcB : ∀ n, Small (c n) (C*K^n))
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) :
    Small (sub (sumDerivative c z hc hz C K R)
      (sumDerivative c a hc ha C K R)) (16*C*K^2*H) := by
  have hKR : 0 ≤ K*R := Rat.mul_nonneg hK hR
  have hdLocal : 4*K*R ≤ (1 : Rat)/2 := by grind
  have hDz := sumDerivative_valid c z hc hz C K R hC hK hR hcB hzR hdLocal
  have hDa := sumDerivative_valid c a hc ha C K R hC hK hR hcB haR hdLocal
  have hed := SeriesLimitLaws.shrinks_shift _ (derivativeTail_shrinks C K R hC hK hR hdLocal) 1
  apply SeriesLimitLaws.small_of_prefix_bound _ (sub_valid hDz hDa)
    (fun N => sub (derivativeBlock c z 0 (N+1)) (derivativeBlock c a 0 (N+1)))
    (fun N => sub_valid (derivativeBlock_valid c z hc hz 0 (N+1))
      (derivativeBlock_valid c a hc ha 0 (N+1))) (16*C*K^2*H)
    (fun N => derivativeTail C K R (N+1)+derivativeTail C K R (N+1))
    (RepresentedCauchySum.sum_shrinks _ _ hed hed)
  · intro N
    exact SeriesLimitLaws.difference_close _ _ _ _ hDz hDa
      (derivativeBlock_valid c z hc hz 0 (N+1))
      (derivativeBlock_valid c a hc ha 0 (N+1)) _ _
      (sumDerivative_close_prefix c z hc hz C K R hC hK hR hcB hzR hdLocal (N+1))
      (sumDerivative_close_prefix c a hc ha C K R hC hK hR hcB haR hdLocal (N+1))
  · exact derivativeBlock_difference_bound c a z hc ha hz C K R H
      hC hK hR hH hcB haR hzR hza hlocal

theorem sumDerivative_continuity_error (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid)
    (C K R : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ n, Small (c n) (C*K^n))
    (haR : Small a R) (hzR : Small z R) (hlocal : 8*K*R ≤ (1 : Rat)/2)
    (eps : QPos) (hza : Small (sub z a) (derivativeDelta C K hC hK eps).val) :
    Small (sub (sumDerivative c z hc hz C K R)
      (sumDerivative c a hc ha C K R)) eps.val := by
  have hs := sumDerivative_lipschitz c a z hc ha hz C K R
    (derivativeDelta C K hC hK eps).val hC hK hR
    (Rat.le_of_lt (derivativeDelta C K hC hK eps).property) hcB haR hzR hza hlocal
  apply hs.mono
  have hB : 0 ≤ 16*C*K^2 := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hK)
  have hd : 0 < 16*C*K^2+1 := by grind
  have heq : (derivativeDelta C K hC hK eps).val*(16*C*K^2+1) = eps.val :=
    Rat.div_mul_cancel (Rat.ne_of_gt hd)
  have hh := (derivativeDelta C K hC hK eps).property
  grind

end ComputableAnalysis.RiemannHilbert.BoundedSeries
