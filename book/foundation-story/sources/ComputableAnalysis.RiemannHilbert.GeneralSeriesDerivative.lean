import ComputableAnalysis.RiemannHilbert.GeneralSeriesRemainder

/-! Actual termwise differentiation for arbitrary supplied bounded coefficients. -/
namespace ComputableAnalysis.RiemannHilbert.BoundedSeries
open ComplexRaw FunctionTheory LocalODE

/-- The proposed derivative is connected to the constructed value function
by a quadratic remainder estimate, for every valid represented neighbor. -/
theorem sum_remainder_bound (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid)
    (C K R H : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hcB : ∀ n, Small (c n) (C*K^n))
    (haR : Small a R) (hzR : Small z R) (hza : Small (sub z a) H)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) :
    Small (SeriesLimitLaws.remainder
      (sumValue c z hc hz C K R)
      (sumValue c a hc ha C K R)
      (sumDerivative c a hc ha C K R) (sub z a)) (16*C*K^2*H^2) := by
  have hKR : 0 ≤ K*R := Rat.mul_nonneg hK hR
  have hvLocal : 2*K*R ≤ (1 : Rat)/2 := by grind
  have hdLocal : 4*K*R ≤ (1 : Rat)/2 := by grind
  let F := sumValue c z hc hz C K R
  let G := sumValue c a hc ha C K R
  let D := sumDerivative c a hc ha C K R
  have hF := sumValue_valid c z hc hz C K R hC hK hR hcB hzR hvLocal
  have hG := sumValue_valid c a hc ha C K R hC hK hR hcB haR hvLocal
  have hD := sumDerivative_valid c a hc ha C K R hC hK hR hcB haR hdLocal
  let p := fun N => valueBlock c z 0 (N+2)
  let q := fun N => valueBlock c a 0 (N+2)
  let r := fun N => slopePrefix c a (N+2)
  have hp := fun N => valueBlock_valid c z hc hz 0 (N+2)
  have hq := fun N => valueBlock_valid c a hc ha 0 (N+2)
  have hr := fun N => slopePrefix_valid _ a (hc) ha (N+2)
  let e := fun N => valueTail C K R (N+2) + valueTail C K R (N+2) +
    2*derivativeTail C K R (N+1)*H
  have hev := SeriesLimitLaws.shrinks_shift _ (tail_bound_shrinks C (2*K*R) hC
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hvLocal) 2
  have hed := SeriesLimitLaws.shrinks_shift _ (derivativeTail_shrinks C K R hC hK hR hdLocal) 1
  have hes := SeriesLimitLaws.shrinks_scale _ hed (2*H) (Rat.mul_nonneg (by decide) hH)
  have he : ShrinksToZero e := by
    have hs := RepresentedCauchySum.sum_shrinks (fun N => valueTail C K R (N+2)+valueTail C K R (N+2))
      (fun N => (2*H)*derivativeTail C K R (N+1))
      (RepresentedCauchySum.sum_shrinks _ _ hev hev) hes
    have heq : e = (fun N => (valueTail C K R (N+2)+valueTail C K R (N+2))+
        (2*H)*derivativeTail C K R (N+1)) := by
      funext N
      dsimp [e]
      grind
    rw [heq]
    exact hs
  apply SeriesLimitLaws.small_of_prefix_bound _ (SeriesLimitLaws.remainder_valid F G D (sub z a)
    hF hG hD (sub_valid hz ha))
    (fun N => SeriesLimitLaws.remainder (p N) (q N) (r N) (sub z a))
    (fun N => SeriesLimitLaws.remainder_valid _ _ _ _ (hp N) (hq N) (hr N) (sub_valid hz ha))
    (16*C*K^2*H^2) e he
  · intro N
    have hFp := sumValue_close_prefix c z hc hz C K R hC hK hR hcB hzR hvLocal (N+2)
    have hGq := sumValue_close_prefix c a hc ha C K R hC hK hR hcB haR hvLocal (N+2)
    have hDr0 := sumDerivative_close_prefix c a hc ha C K R hC hK hR hcB haR hdLocal (N+1)
    have hDr : Small (sub D (r N)) (derivativeTail C K R (N+1)) :=
      Small.congr
        (sub_valid hD (derivativeBlock_valid c a hc ha 0 (N+1)))
        (sub_valid hD (hr N))
        (FunctionTheory.sub_congr (equiv_refl _ hD)
          (equiv_symm (slopePrefix_derivativeBlock c a hc ha (N+1)))) hDr0
    exact SeriesLimitLaws.remainder_close F G D (p N) (q N) (r N) (sub z a)
      hF hG hD (hp N) (hq N) (hr N) (sub_valid hz ha)
      (valueTail C K R (N+2)) (valueTail C K R (N+2)) (derivativeTail C K R (N+1)) H
      (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) hK)
        (Rat.pow_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR))) hH hFp hGq hDr hza
  · intro N
    have hbound := remainderPrefix_bound c a z
      (hc) ha hz C K R H hC hK hR hH
      hcB
      haR hzR hza hlocal N
    exact Small.congr
      (remainderPrefix_valid _ a z (hc) ha hz (N+2))
      (SeriesLimitLaws.remainder_valid _ _ _ _ (hp N) (hq N) (hr N) (sub_valid hz ha))
      (equiv_symm (valuePrefix_remainder_identity c a z hc ha hz (N+2))) hbound


/-- The full epsilon-radius derivative law, at arbitrary represented points
and in every complex direction on the certified disk. -/
theorem sum_derivative_error (c : Nat → ComplexRaw) (a z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (ha : a.Valid) (hz : z.Valid)
    (C K R : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ n, Small (c n) (C*K^n))
    (haR : Small a R) (hzR : Small z R) (hlocal : 8*K*R ≤ (1 : Rat)/2)
    (eps H : QPos) (hH : H.val ≤ (derivativeDelta C K hC hK eps).val)
    (hza : Small (sub z a) H.val) :
    Small (SeriesLimitLaws.remainder
      (sumValue c z hc hz C K R)
      (sumValue c a hc ha C K R)
      (sumDerivative c a hc ha C K R) (sub z a)) (eps.val*H.val) := by
  have hs := sum_remainder_bound c a z hc ha hz C K R H.val
    hC hK hR (Rat.le_of_lt H.property) hcB haR hzR hza hlocal
  apply hs.mono
  have hB : 0 ≤ 16*C*K^2 := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hK)
  have hd : 0 < 16*C*K^2+1 := by grind
  have hmul := Rat.mul_le_mul_of_nonneg_right hH (Rat.le_of_lt hd)
  have heq : (derivativeDelta C K hC hK eps).val*(16*C*K^2+1) = eps.val :=
    Rat.div_mul_cancel (Rat.ne_of_gt hd)
  rw [heq] at hmul
  have hle : (16*C*K^2)*H.val ≤ eps.val := by grind
  have hh := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt H.property)
  simpa only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul, Rat.mul_assoc] using hh

end ComputableAnalysis.RiemannHilbert.BoundedSeries
