import ComputableAnalysis.RiemannHilbert.MonomialDifference
import ComputableAnalysis.RiemannHilbert.LocalSeriesDerivative

/-! Uniform continuity estimates for the constructed derivative series. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

theorem derivativeTerm_difference_factor (b : Nat → ComplexRaw) (initial a z : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid) (ha : a.Valid) (hz : z.Valid) (n : Nat) :
    (sub (derivativeTerm b initial z (n+1)) (derivativeTerm b initial a (n+1))).Equiv
      (scaleRat ((n+2 : Nat) : Rat)
        (mul (coefficient b initial (n+2)) (sub (power z (n+1)) (power a (n+1))))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (derivativeTerm_valid b initial z hb h0 hz (n+1))
      (derivativeTerm_valid b initial a hb h0 ha (n+1)))
    (hright := scaleRat_valid (mul_valid (coefficient_valid b initial hb h0 (n+2))
      (sub_valid (power_valid z hz (n+1)) (power_valid a ha (n+1)))))
  change ComplexRawQuotient.scaleRat ((n+2 : Nat) : Rat)
      (ComplexRawQuotient.ofRaw (coefficient b initial (n+2)) (coefficient_valid b initial hb h0 _)*
       ComplexRawQuotient.ofRaw (power z (n+1)) (power_valid z hz _)) -
    ComplexRawQuotient.scaleRat ((n+2 : Nat) : Rat)
      (ComplexRawQuotient.ofRaw (coefficient b initial (n+2)) (coefficient_valid b initial hb h0 _)*
       ComplexRawQuotient.ofRaw (power a (n+1)) (power_valid a ha _)) =
    ComplexRawQuotient.scaleRat ((n+2 : Nat) : Rat)
      (ComplexRawQuotient.ofRaw (coefficient b initial (n+2)) (coefficient_valid b initial hb h0 _)*
       (ComplexRawQuotient.ofRaw (power z (n+1)) (power_valid z hz _) -
        ComplexRawQuotient.ofRaw (power a (n+1)) (power_valid a ha _)))
  rw [ScalarAlgebra.scale_natural, ScalarAlgebra.scale_natural, ScalarAlgebra.scale_natural]
  grind

theorem derivativeTerm_difference_bound (b : Nat → ComplexRaw) (initial a z : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid) (ha : a.Valid) (hz : z.Valid)
    (M C K R H : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hMK : 2*M ≤ K) (hbB : ∀ n, Small (b n) (M*K^n)) (hinit : Small initial C)
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H) (n : Nat) :
    Small (sub (derivativeTerm b initial z (n+1)) (derivativeTerm b initial a (n+1)))
      (8*C*K^2*H*(8*K*R)^n) := by
  have hq : 0 ≤ 2*R := Rat.mul_nonneg (by decide) hR
  have hn1 : 0 ≤ ((n+1 : Nat) : Rat) := Rat.le_of_lt ((Rat.natCast_pos).2 (by omega))
  have hn2 : 0 ≤ ((n+2 : Nat) : Rat) := Rat.le_of_lt ((Rat.natCast_pos).2 (by omega))
  have hdB : 0 ≤ 2*((n+1 : Nat) : Rat)*(2*R)^n*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hn1) (Rat.pow_nonneg hq)) hH
  have hs := Small.mul (coefficient_valid b initial hb h0 (n+2))
    (sub_valid (power_valid z hz (n+1)) (power_valid a ha (n+1)))
    (Rat.mul_nonneg hC (Rat.pow_nonneg hK)) hdB
    (coefficient_majorant b initial hb h0 M C K hM hC hK hMK hbB hinit (n+2))
    (power_difference_bound a z ha hz R H hR hH haR hzR hza n)
  have ht := small_scale hn2 hs
  have hv := Small.congr
    (scaleRat_valid (mul_valid (coefficient_valid b initial hb h0 (n+2))
      (sub_valid (power_valid z hz (n+1)) (power_valid a ha (n+1)))))
    (sub_valid (derivativeTerm_valid b initial z hb h0 hz (n+1))
      (derivativeTerm_valid b initial a hb h0 ha (n+1)))
    (equiv_symm (derivativeTerm_difference_factor b initial a z hb h0 ha hz n)) ht
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

theorem derivativeBlock_difference_majorant (b : Nat → ComplexRaw) (initial a z : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid) (ha : a.Valid) (hz : z.Valid)
    (M C K R H : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hMK : 2*M ≤ K) (hbB : ∀ n, Small (b n) (M*K^n)) (hinit : Small initial C)
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H) (N : Nat) :
    Small (sub (derivativeBlock b initial z 0 (N+1)) (derivativeBlock b initial a 0 (N+1)))
      (RationalMajorant.geomTailPartial (8*C*K^2*H) (8*K*R) 0 N) := by
  induction N with
  | zero =>
    have he : (sub (derivativeBlock b initial z 0 1) (derivativeBlock b initial a 0 1)).Equiv zero :=
      add_neg_equiv _ (derivativeBlock_valid b initial z hb h0 hz 0 1)
    exact Small.congr (ofQComplex_valid _) (sub_valid
      (derivativeBlock_valid b initial z hb h0 hz 0 1)
      (derivativeBlock_valid b initial a hb h0 ha 0 1)) (equiv_symm he)
      (Small.zero (by change (0 : Rat) ≤ 0; decide))
  | succ N ih =>
    have hs := small_add ih (derivativeTerm_difference_bound b initial a z hb h0 ha hz
      M C K R H hM hC hK hR hH hMK hbB hinit haR hzR hza N)
    have ht := Small.congr
      (add_valid
        (sub_valid (derivativeBlock_valid b initial z hb h0 hz 0 (N+1))
          (derivativeBlock_valid b initial a hb h0 ha 0 (N+1)))
        (sub_valid (derivativeTerm_valid b initial z hb h0 hz (N+1))
          (derivativeTerm_valid b initial a hb h0 ha (N+1))))
      (sub_valid
        (add_valid (derivativeBlock_valid b initial z hb h0 hz 0 (N+1))
          (derivativeTerm_valid b initial z hb h0 hz (N+1)))
        (add_valid (derivativeBlock_valid b initial a hb h0 ha 0 (N+1))
          (derivativeTerm_valid b initial a hb h0 ha (N+1))))
      (equiv_symm (SeriesLimitLaws.addition_difference
        (derivativeBlock b initial z 0 (N+1)) (derivativeBlock b initial a 0 (N+1))
        (derivativeTerm b initial z (N+1)) (derivativeTerm b initial a (N+1))
        (derivativeBlock_valid b initial z hb h0 hz 0 (N+1))
        (derivativeBlock_valid b initial a hb h0 ha 0 (N+1))
        (derivativeTerm_valid b initial z hb h0 hz (N+1))
        (derivativeTerm_valid b initial a hb h0 ha (N+1)))) hs
    simpa only [derivativeBlock.eq_2, Nat.zero_add, RationalMajorant.geomTailPartial] using ht

theorem derivativeBlock_difference_bound (b : Nat → ComplexRaw) (initial a z : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid) (ha : a.Valid) (hz : z.Valid)
    (M C K R H : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hMK : 2*M ≤ K) (hbB : ∀ n, Small (b n) (M*K^n)) (hinit : Small initial C)
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) (N : Nat) :
    Small (sub (derivativeBlock b initial z 0 (N+1)) (derivativeBlock b initial a 0 (N+1)))
      (16*C*K^2*H) := by
  have hs := derivativeBlock_difference_majorant b initial a z hb h0 ha hz M C K R H
    hM hC hK hR hH hMK hbB hinit haR hzR hza N
  apply hs.mono
  have ht := RationalMajorant.geometric_tail_partial_bound
    (C := 8*C*K^2*H) (r := 8*K*R) (N := 0) (k := N)
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hK)) hH)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
  unfold RationalMajorant.geomTailBound at ht
  simp only [Rat.pow_zero, Rat.mul_one] at ht
  grind

theorem sumDerivative_lipschitz (b : Nat → ComplexRaw) (initial a z : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid) (ha : a.Valid) (hz : z.Valid)
    (M C K R H : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hMK : 2*M ≤ K) (hbB : ∀ n, Small (b n) (M*K^n)) (hinit : Small initial C)
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) :
    Small (sub (sumDerivative b initial z hb h0 hz C K R)
      (sumDerivative b initial a hb h0 ha C K R)) (16*C*K^2*H) := by
  have hKR : 0 ≤ K*R := Rat.mul_nonneg hK hR
  have hdLocal : 4*K*R ≤ (1 : Rat)/2 := by grind
  have hDz := sumDerivative_valid b initial z hb h0 hz M C K R hM hC hK hR hMK hbB hinit hzR hdLocal
  have hDa := sumDerivative_valid b initial a hb h0 ha M C K R hM hC hK hR hMK hbB hinit haR hdLocal
  have hed := SeriesLimitLaws.shrinks_shift _ (derivativeTail_shrinks C K R hC hK hR hdLocal) 1
  apply SeriesLimitLaws.small_of_prefix_bound _ (sub_valid hDz hDa)
    (fun N => sub (derivativeBlock b initial z 0 (N+1)) (derivativeBlock b initial a 0 (N+1)))
    (fun N => sub_valid (derivativeBlock_valid b initial z hb h0 hz 0 (N+1))
      (derivativeBlock_valid b initial a hb h0 ha 0 (N+1))) (16*C*K^2*H)
    (fun N => derivativeTail C K R (N+1)+derivativeTail C K R (N+1))
    (RepresentedCauchySum.sum_shrinks _ _ hed hed)
  · intro N
    exact SeriesLimitLaws.difference_close _ _ _ _ hDz hDa
      (derivativeBlock_valid b initial z hb h0 hz 0 (N+1))
      (derivativeBlock_valid b initial a hb h0 ha 0 (N+1)) _ _
      (sumDerivative_close_prefix b initial z hb h0 hz M C K R hM hC hK hR hMK hbB hinit hzR hdLocal (N+1))
      (sumDerivative_close_prefix b initial a hb h0 ha M C K R hM hC hK hR hMK hbB hinit haR hdLocal (N+1))
  · exact derivativeBlock_difference_bound b initial a z hb h0 ha hz M C K R H
      hM hC hK hR hH hMK hbB hinit haR hzR hza hlocal

theorem sumDerivative_continuity_error (b : Nat → ComplexRaw) (initial a z : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid) (ha : a.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hbB : ∀ n, Small (b n) (M*K^n)) (hinit : Small initial C)
    (haR : Small a R) (hzR : Small z R) (hlocal : 8*K*R ≤ (1 : Rat)/2)
    (eps : QPos) (hza : Small (sub z a) (derivativeDelta C K hC hK eps).val) :
    Small (sub (sumDerivative b initial z hb h0 hz C K R)
      (sumDerivative b initial a hb h0 ha C K R)) eps.val := by
  have hs := sumDerivative_lipschitz b initial a z hb h0 ha hz M C K R
    (derivativeDelta C K hC hK eps).val hM hC hK hR
    (Rat.le_of_lt (derivativeDelta C K hC hK eps).property) hMK hbB hinit haR hzR hza hlocal
  apply hs.mono
  have hB : 0 ≤ 16*C*K^2 := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hK)
  have hd : 0 < 16*C*K^2+1 := by grind
  have heq : (derivativeDelta C K hC hK eps).val*(16*C*K^2+1) = eps.val :=
    Rat.div_mul_cancel (Rat.ne_of_gt hd)
  have hh := (derivativeDelta C K hC hK eps).property
  grind

end ComputableAnalysis.RiemannHilbert.LocalODE
