import ComputableAnalysis.ModularForms.NomeMomentLimitLinearity

import ComputableAnalysis.ModularForms.NomeMomentRectangleBounds
import ComputableAnalysis.ModularForms.WeightedLambertSeries

/-! Uniform geometric rectangle estimates for actual weighted Lambert factors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem two_pow_ge_one (k : Nat) : 1≤(2:Rat)^k := by
  induction k with
  | zero => rw [Rat.pow_zero]; exact Rat.le_refl
  | succ k ih =>
    rw [Rat.pow_succ]
    have h := Rat.mul_le_mul_of_nonneg_right ih (show (0:Rat)≤2 by decide)
    grind only

/-- The uniform moment guard supplies the ordinary Lambert disk guard. -/
theorem nomeMomentGuard_lambertLocal (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) : 4*r≤(1:Rat)/2 := by
  have h := Rat.mul_le_mul_of_nonneg_left (two_pow_ge_one k)
    (show 0≤4*r from Rat.mul_nonneg (by decide) hr)
  grind only

/-- The same guard controls the weighted Lambert ratio. -/
theorem nomeMomentGuard_lambertRatio (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) : weightedLambertRatio r k≤(1:Rat)/2 := by
  have h := Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤2 by decide) hr)
    (Rat.pow_nonneg (a := (2:Rat)) (n := k) (by decide))
  unfold weightedLambertRatio
  grind only

private theorem nonneg_pow_mono (a b : Rat) (ha : 0≤a) (hab : a≤b) (k : Nat) : a^k≤b^k := by
  have hb := Rat.le_trans ha hab
  induction k with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ k ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ha)
      (Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (n := k) hb))

def weightedLambertRectangleTerm (z : Scalar) (k N m : Nat) : ComplexRaw :=
  scaleRat (((m+1:Nat):Rat)^k) (lambertPositivePrefix (nomePowerScalar z m) N)

theorem weightedLambertRectangleTerm_valid (z : Scalar) (k N m : Nat) :
    (weightedLambertRectangleTerm z k N m).Valid :=
  scaleRat_valid (lambertPositivePrefix_valid _ N)

/-- The weighted geometric truncation has a geometric majorant in the column index. -/
theorem weightedLambertTerm_close_rectangle (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) (N m : Nat) :
    Small (sub (weightedLambertTerm z r k m) (weightedLambertRectangleTerm z k N m))
      (2*(8*r*(4*r)^N)*(weightedLambertRatio r k)^m) := by
  have hl := nomeMomentGuard_lambertLocal r k hr hlocal
  have hR0 := nomePowerRadius_nonneg r hr m
  have hR := nomePowerRadius_le r hr
    (Rat.le_trans (nomeMomentOuterRatio_le r k hr hlocal) (by decide +kernel)) m
  have hbase : 2*nomePowerRadius r m≤4*r := by grind only
  have hpow := nonneg_pow_mono _ _ (Rat.mul_nonneg (by decide) hR0) hbase N
  have htail := lambertPositivePrefix_close (nomePowerScalar z m) (nomePowerRadius r m) hR0
    (nomePowerRadius_local r hr hl m) (nomePowerScalar_small z r hr hz m) N
  have h := represented_prefix_scale_close
    ⟨nomeLambertPower z r m,nomeLambertPower_valid z r hr hl hz m⟩
    ⟨lambertPositivePrefix (nomePowerScalar z m) N,lambertPositivePrefix_valid _ N⟩
    (((m+1:Nat):Rat)^k) _ (Rat.pow_nonneg Rat.natCast_nonneg) htail
  apply h.mono
  have hW := lambertWeight_bound m k
  have hw0 : 0≤(((m+1:Nat):Rat)^k) := Rat.pow_nonneg Rat.natCast_nonneg
  have h1 := Rat.mul_le_mul_of_nonneg_left hpow hw0
  have h2 := Rat.mul_le_mul_of_nonneg_right hW (Rat.pow_nonneg (a := 4*r) (n := N) (Rat.mul_nonneg (by decide) hr))
  have h3 := Rat.mul_le_mul_of_nonneg_right h1
    (Rat.mul_nonneg (show (0:Rat)≤4 by decide) (Rat.mul_nonneg (show (0:Rat)≤2 by decide) hR0))
  have h4 := Rat.mul_le_mul_of_nonneg_right h2
    (Rat.mul_nonneg (show (0:Rat)≤4 by decide) (Rat.mul_nonneg (show (0:Rat)≤2 by decide) hR0))
  rw [Rat.pow_succ (2*nomePowerRadius r m) N]
  unfold weightedLambertRatio
  rw [LocalODE.rational_mul_pow (2*r) ((2:Rat)^k) m]
  have he : nomePowerRadius r m=(2*r)^m*(2*r) := by unfold nomePowerRadius; rw [Rat.pow_succ]
  rw [he] at h3 h4 ⊢
  generalize (((m+1:Nat):Rat)^k)=A at h3 h4 ⊢
  generalize ((2:Rat)^k)^m=B at h3 h4 ⊢
  generalize (2*r)^m=D at h3 h4 ⊢
  generalize (2*(D*(2*r)))^N=E at h3 ⊢
  generalize (4*r)^N=F at h3 h4 ⊢
  clear z hr hlocal hz hl hR0 hR hbase hpow htail h hW hw0 h1 h2 he
  grind only

/-- The vertical error is uniform in the number of columns in the rectangle. -/
theorem weightedLambertPrefix_close_rectangle (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) (N M : Nat) :
    Small (sub (ScalarSeries.block (weightedLambertTerm z r k) 0 M)
      (ScalarSeries.block (weightedLambertRectangleTerm z k N) 0 M)) (4*(8*r*(4*r)^N)) := by
  let t := weightedLambertTerm z r k
  let u := weightedLambertRectangleTerm z k N
  have ht := weightedLambertTerm_valid z r k hr (nomeMomentGuard_lambertLocal r k hr hlocal) hz
  have hu := weightedLambertRectangleTerm_valid z k N
  have hC : 0≤8*r*(4*r)^N := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr)
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hr))
  have h := ScalarSeries.block_bound (fun m => sub (t m) (u m)) _ _ hC
    (weightedLambertRatio_nonneg r k hr) (nomeMomentGuard_lambertRatio r k hr hlocal)
    (weightedLambertTerm_close_rectangle z r k hr hlocal hz N) 0 M
  simp only [Rat.pow_zero,Rat.mul_one] at h
  exact Small.congr (ScalarSeries.block_valid _ (fun m => sub_valid (ht m) (hu m)) 0 M)
    (sub_valid (ScalarSeries.block_valid t ht 0 M) (ScalarSeries.block_valid u hu 0 M))
    (representedBlock_sub t u ht hu 0 M) h

end ComputableAnalysis.ModularForms
