import ComputableAnalysis.ModularForms.DiskLambertContinuity

/-! Rational radius independence, uniform continuity, and the old chart bridge. -/
namespace ComputableAnalysis.ModularForms.DiskLambert
open ComplexRaw FunctionTheory RiemannHilbert RationalLambert CauchyTaylor
set_option maxHeartbeats 1000000

theorem atRadius_close_later (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1) (hq : InDisk q r)
    (k N L : Nat) (hL : cutoff r k+N≤L) :
    Small (sub (atRadius q r k) (ofQComplex (finitePrefix q k L))) (tail r k N) := by
  have hc := atRadius_close q r hr hr1 hq k (L-cutoff r k)
  rw [Nat.add_sub_cancel' (show cutoff r k≤L by omega)] at hc
  exact hc.mono (tail_antitone r hr hr1 k N (L-cutoff r k) (by omega))

theorem radius_independent (q : QComplex) (r s : Rat) (hr : 0≤r) (hs : 0≤s) (hr1 : r<1) (hs1 : s<1)
    (hqr : InDisk q r) (hqs : InDisk q s) (k : Nat) : (atRadius q r k).Equiv (atRadius q s k) := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun N => tail r k N+tail s k N)
    (RepresentedCauchySum.sum_shrinks _ _ (tail_shrinks r hr hr1 k) (tail_shrinks s hs hs1 k))
  intro N
  let L := max (cutoff r k) (cutoff s k)+N
  have ha := atRadius_close_later q r hr hr1 hqr k N L (by dsimp [L]; omega)
  have hb := atRadius_close_later q s hs hs1 hqs k N L (by dsimp [L]; omega)
  have h := triangle _ _ _ (atRadius_valid q r hr hr1 hqr k) (ofQComplex_valid _) (atRadius_valid q s hs hs1 hqs k)
    _ _ ha (RepresentedCauchySum.small_sub_symm _ _ _ hb)
  exact h.mono (by grind only)

theorem rational_atRadius (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1) (hq : InDisk q r) (k : Nat) :
    (rationalValue q k).Equiv (atRadius q r k) :=
  radius_independent q (rationalRadius q) r (Rat.le_of_lt (rationalRadius_pos q)) hr
    (rationalRadius_lt_one q (by
      have := rat_square_nonneg_basic (1-r)
      have hh := Rat.mul_pos (show 0<1-r by grind only) (show 0<1+r by grind only)
      change QComplex.normSq q≤r*r at hq
      grind only)) hr1 (rationalRadius_inside q) hq k

theorem atRadius_lipschitz (p q : QComplex) (r : Rat) (hr : 0<r) (hr1 : r<1)
    (hp : InDisk p r) (hq : InDisk q r) (k : Nat) :
    Small (sub (atRadius p r k) (atRadius q r k)) (continuityBound r k*(QComplex.sub p q).normBound) := by
  apply SeriesLimitLaws.small_closed _ _ (fun N => 2*tail r k N)
    (RepresentedCauchySum.twice_shrinks _ (tail_shrinks r (Rat.le_of_lt hr) hr1 k))
  intro N
  let L := cutoff r k+N
  have hc := rational_difference_small _ _ _ (prefix_difference p q r hr hr1 hp hq k L)
  have h1 := triangle _ _ _ (atRadius_valid p r (Rat.le_of_lt hr) hr1 hp k) (ofQComplex_valid _) (ofQComplex_valid _)
    _ _ (atRadius_close p r (Rat.le_of_lt hr) hr1 hp k N) hc
  have h2 := triangle _ _ _ (atRadius_valid p r (Rat.le_of_lt hr) hr1 hp k) (ofQComplex_valid _) (atRadius_valid q r (Rat.le_of_lt hr) hr1 hq k)
    _ _ h1 (RepresentedCauchySum.small_sub_symm _ _ _ (atRadius_close q r (Rat.le_of_lt hr) hr1 hq k N))
  exact h2.mono (by grind only)

theorem rational_lipschitz (p q : QComplex) (r : Rat) (hr : 0<r) (hr1 : r<1)
    (hp : InDisk p r) (hq : InDisk q r) (k : Nat) :
    Small (sub (rationalValue p k) (rationalValue q k)) (continuityBound r k*(QComplex.sub p q).normBound) := by
  have hp1 : QComplex.normSq p<1 := by
    have h := Rat.mul_pos (show 0<1-r by grind only) (show 0<1+r by grind only)
    change QComplex.normSq p≤r*r at hp
    grind only
  have hq1 : QComplex.normSq q<1 := by
    have h := Rat.mul_pos (show 0<1-r by grind only) (show 0<1+r by grind only)
    change QComplex.normSq q≤r*r at hq
    grind only
  exact Small.congr (sub_valid (atRadius_valid p r (Rat.le_of_lt hr) hr1 hp k) (atRadius_valid q r (Rat.le_of_lt hr) hr1 hq k))
    (sub_valid (rationalValue_valid p hp1 k) (rationalValue_valid q hq1 k))
    (FunctionTheory.sub_congr (equiv_symm (rational_atRadius p r (Rat.le_of_lt hr) hr1 hp k))
      (equiv_symm (rational_atRadius q r (Rat.le_of_lt hr) hr1 hq k)))
    (atRadius_lipschitz p q r hr hr1 hp hq k)

theorem rational_legacy_agreement (q : QComplex) (hq : Small (ofQComplex q) ((1:Rat)/64))
    (k : Nat) (hk : k=1 ∨ k=3 ∨ k=5) :
    (rationalValue q k).Equiv (comparison (point q) hq k).val := by
  have coords : -((1:Rat)/64)≤q.re ∧ q.re≤(1:Rat)/64 ∧ -((1:Rat)/64)≤q.im ∧ q.im≤(1:Rat)/64 :=
    ⟨hq.1 0 0,hq.2.1 0 0,hq.2.2.1 0 0,hq.2.2.2 0 0⟩
  have disk : InDisk q (1/32) := by
    have h1 := Rat.mul_nonneg (show 0≤(1:Rat)/64-q.re by grind only) (show 0≤(1:Rat)/64+q.re by grind only)
    have h2 := Rat.mul_nonneg (show 0≤(1:Rat)/64-q.im by grind only) (show 0≤(1:Rat)/64+q.im by grind only)
    dsimp [InDisk,QComplex.normSq]
    grind only
  have hv := atRadius_valid q (1/32) (by decide +kernel) (by decide +kernel) disk k
  have he : (atRadius q (1/32) k).Equiv (comparison (point q) hq k).val := by
    apply SeriesLimitLaws.equiv_of_small_sub_zero
    apply SeriesLimitLaws.small_closed _ 0 (fun N => tail (1/32) k N+8*((1:Rat)/2)^N)
      (RepresentedCauchySum.sum_shrinks _ _ (tail_shrinks (1/32) (by decide +kernel) (by decide +kernel) k)
        (by simpa only [show (4:Rat)*2=8 by decide +kernel] using
          LocalODE.tail_bound_shrinks 2 (1/2) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
    intro N
    let L := cutoff (1/32) k+N
    have ht := comparison_tail (point q) hq k hk L
    have ht' := Small.congr (sub_valid (comparison (point q) hq k).property
      (ScalarSeries.block_valid _ (weightedLambertTerm_valid (point q) (1/64) k (by decide +kernel) (by decide +kernel) hq) 0 L))
      (sub_valid (comparison (point q) hq k).property (ofQComplex_valid _))
      (FunctionTheory.sub_congr (equiv_refl _ (comparison (point q) hq k).property) (prefix_agrees q hq k L)) ht
    have hm := Rat.mul_le_mul_of_nonneg_left (power_antitone (by decide +kernel : (0:Rat)≤1/2)
      (by decide +kernel : (1/2:Rat)≤1) (show N≤L by dsimp [L]; omega)) (by decide +kernel : (0:Rat)≤8)
    have hb := triangle _ _ _ hv (ofQComplex_valid _) (comparison (point q) hq k).property
      _ _ (atRadius_close q (1/32) (by decide +kernel) (by decide +kernel) disk k N)
      (RepresentedCauchySum.small_sub_symm _ _ _ (ht'.mono hm))
    exact hb.mono (by grind only)
  have hq1 : QComplex.normSq q<1 := by change QComplex.normSq q≤(1/32:Rat)*(1/32:Rat) at disk; grind only
  exact equiv_trans (rationalValue_valid q hq1 k) hv (comparison (point q) hq k).property
    (rational_atRadius q (1/32) (by decide +kernel) (by decide +kernel) disk k) he

end ComputableAnalysis.ModularForms.DiskLambert
