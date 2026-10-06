import ComputableAnalysis.RiemannHilbert.SeriesSuperposition

/-! Exact superposition of geometrically bounded represented coefficient sums. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

theorem coefficientSum_add (c d : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hd : ∀ i, (d i).Valid) (hz : z.Valid)
    (C D K R : Rat) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hdB : ∀ i, Small (d i) (D*K^i))
    (hzB : Small z R) (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    (coefficientSum (fun i => add (c i) (d i)) z (fun i => add_valid (hc i) (hd i)) hz (C+D) K R).Equiv
      (add (coefficientSum c z hc hz C K R) (coefficientSum d z hd hz D K R)) := by
  have hq : 0 ≤ 2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have hCD := Rat.add_nonneg hC hD
  have hcdb : ∀ i, Small (add (c i) (d i)) ((C+D)*K^i) := by
    intro i
    have hs := small_add (hcB i) (hdB i)
    have he : C*K^i+D*K^i=(C+D)*K^i := by grind
    rw [he] at hs; exact hs
  have ht := seriesTerm_valid c z hc hz
  have hu := seriesTerm_valid d z hd hz
  have hleft := coefficientSum_valid _ z (fun i => add_valid (hc i) (hd i)) hz
    (C+D) K R hCD hK hR hcdb hzB hlocal
  have hT := seriesTerm_bound c z hc hz C K R hC hK hR hcB hzB
  have hU := seriesTerm_bound d z hd hz D K R hD hK hR hdB hzB
  have hB : ∀ i, Small (add (seriesTerm c z i) (seriesTerm d z i)) (2*(C+D)*(2*K*R)^i) := by
    intro i
    have hs := small_add (hT i) (hU i)
    have he : 2*C*(2*K*R)^i+2*D*(2*K*R)^i=2*(C+D)*(2*K*R)^i := by grind
    rw [he] at hs; exact hs
  have hmiddle := ScalarSeries.value_valid _ (fun i => add_valid (ht i) (hu i))
    (C+D) (2*K*R) hCD hq hlocal hB
  have he := ScalarSeries.value_congr _ _
    (seriesTerm_valid _ z (fun i => add_valid (hc i) (hd i)) hz)
    (fun i => add_valid (ht i) (hu i)) (C+D) (2*K*R) (C+D) (2*K*R)
    hCD hq hCD hq hlocal hlocal
    (seriesTerm_bound _ z (fun i => add_valid (hc i) (hd i)) hz (C+D) K R hCD hK hR hcdb hzB)
    hB (fun i => add_mul_equiv _ _ _ (hc i) (hd i) (power_valid z hz i))
  exact equiv_trans hleft hmiddle
    (add_valid (coefficientSum_valid c z hc hz C K R hC hK hR hcB hzB hlocal)
      (coefficientSum_valid d z hd hz D K R hD hK hR hdB hzB hlocal)) he
    (ScalarSeries.value_add _ _ ht hu C D (2*K*R) hC hD hq hlocal hT hU)

theorem coefficientSum_scale (c : Nat → ComplexRaw) (z a : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hz : z.Valid) (ha : a.Valid)
    (B C K R : Rat) (hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (haB : Small a B) (hcB : ∀ i, Small (c i) (C*K^i))
    (hzB : Small z R) (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    (coefficientSum (fun i => mul a (c i)) z (fun i => mul_valid ha (hc i)) hz (2*B*C) K R).Equiv
      (mul a (coefficientSum c z hc hz C K R)) := by
  have hq : 0 ≤ 2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have hBC : 0 ≤ 2*B*C := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hC
  have hacb : ∀ i, Small (mul a (c i)) ((2*B*C)*K^i) := by
    intro i
    have hs := Small.mul ha (hc i) hB (Rat.mul_nonneg hC (Rat.pow_nonneg hK)) haB (hcB i)
    have he : 2*B*(C*K^i)=(2*B*C)*K^i := by grind
    rw [he] at hs; exact hs
  have ht := seriesTerm_valid c z hc hz
  have hT := seriesTerm_bound c z hc hz C K R hC hK hR hcB hzB
  have hU : ∀ i, Small (mul a (seriesTerm c z i)) (2*(2*B*C)*(2*K*R)^i) := by
    intro i
    have hs := Small.mul ha (ht i) hB
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hq)) haB (hT i)
    have he : 2*B*(2*C*(2*K*R)^i)=2*(2*B*C)*(2*K*R)^i := by grind
    rw [he] at hs; exact hs
  have hleft := coefficientSum_valid _ z (fun i => mul_valid ha (hc i)) hz
    (2*B*C) K R hBC hK hR hacb hzB hlocal
  have hmiddle := ScalarSeries.value_valid _ (fun i => mul_valid ha (ht i)) (2*B*C) (2*K*R)
    hBC hq hlocal hU
  have he := ScalarSeries.value_congr _ _
    (seriesTerm_valid _ z (fun i => mul_valid ha (hc i)) hz)
    (fun i => mul_valid ha (ht i)) (2*B*C) (2*K*R) (2*B*C) (2*K*R)
    hBC hq hBC hq hlocal hlocal
    (seriesTerm_bound _ z (fun i => mul_valid ha (hc i)) hz (2*B*C) K R hBC hK hR hacb hzB)
    hU (fun i => mul_assoc_equiv _ _ _ ha (hc i) (power_valid z hz i))
  exact equiv_trans hleft hmiddle
    (mul_valid ha (coefficientSum_valid c z hc hz C K R hC hK hR hcB hzB hlocal)) he
    (ScalarSeries.value_scale _ ht a ha B C (2*K*R) hB hC hq hlocal haB hT)

end ComputableAnalysis.RiemannHilbert.LocalODE
