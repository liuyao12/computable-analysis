import ComputableAnalysis.ModularForms.NomeMomentOuterSeries

/-! Quantified horizontal truncation errors for the actual moment rectangles. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem nonneg_pow_mono (a b : Rat) (ha : 0≤a) (hab : a≤b) (k : Nat) :
    a^k≤b^k := by
  have hb := Rat.le_trans ha hab
  induction k with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ k ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ha)
      (Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (n := k) hb))

/-- A uniform error for truncating each moment, independent of its row index. -/
theorem nomeMomentOuterTerm_close (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) (n M : Nat) :
    Small (sub (nomeMomentOuterTerm z r k n)
      (polynomialNomeMomentPrefix (nomePowerScalar z n) k M))
      (8*r*(4*r*(2:Rat)^k)^M) := by
  have hbase := nomeMomentOuterRatio_le r k hr hlocal
  have hR := nomePowerRadius_le r hr (Rat.le_trans hbase (by decide +kernel)) n
  have hR0 := nomePowerRadius_nonneg r hr n
  have hpow0 : 0≤(2:Rat)^k := Rat.pow_nonneg (by decide)
  have hmul := Rat.mul_le_mul_of_nonneg_right hR hpow0
  have hratio : polynomialNomeMomentRatio (nomePowerRadius r n) k≤4*r*(2:Rat)^k := by
    unfold polynomialNomeMomentRatio
    grind only
  have hp := nonneg_pow_mono _ _ (polynomialNomeMomentRatio_nonneg _ k hR0) hratio M
  have hm1 := Rat.mul_le_mul_of_nonneg_left hp (show 0≤4*nomePowerRadius r n from Rat.mul_nonneg (by decide) hR0)
  have hm2 := Rat.mul_le_mul_of_nonneg_right hR
    (Rat.pow_nonneg (a := 4*r*(2:Rat)^k) (n := M) (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr) hpow0))
  apply (polynomialNomeMomentSum_close _ _ k hR0 (nomePowerMomentRatio_le r k hr hlocal n)
    (nomePowerScalar_small z r hr hz n) M).mono
  grind only

/-- The finite outer prefix is approximated by its actual finite moment rectangle. -/
theorem nomeMomentOuterPrefix_close_rectangle (z : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) (N M : Nat) :
    Small (sub (ScalarSeries.block (nomeMomentOuterTerm z r k) 0 N)
      (ScalarSeries.block (fun n => polynomialNomeMomentPrefix (nomePowerScalar z n) k M) 0 N))
      ((N:Rat)*(8*r*(4*r*(2:Rat)^k)^M)) := by
  let t := nomeMomentOuterTerm z r k
  let u := fun n => polynomialNomeMomentPrefix (nomePowerScalar z n) k M
  have ht := nomeMomentOuterTerm_valid z r k hr hlocal hz
  have hu n := polynomialNomeMomentPrefix_valid (nomePowerScalar z n) k M
  have hB : 0≤8*r*(4*r*(2:Rat)^k)^M :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr)
      (Rat.pow_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr) (Rat.pow_nonneg (by decide))))
  have h := ScalarSeries.block_uniform (fun n => sub (t n) (u n)) _ hB 0 N
    (fun n _ => nomeMomentOuterTerm_close z r k hr hlocal hz (0+n) M)
  exact Small.congr (ScalarSeries.block_valid _ (fun n => sub_valid (ht n) (hu n)) 0 N)
    (sub_valid (ScalarSeries.block_valid t ht 0 N) (ScalarSeries.block_valid u hu 0 N))
    (representedBlock_sub t u ht hu 0 N) h

/-- For any fixed number of rows, the horizontal rectangle error tends to zero. -/
theorem nomeMomentRectangleTail_shrinks (r : Rat) (k N : Nat) (hr : 0≤r)
    (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) :
    ShrinksToZero (fun M => (N:Rat)*(8*r*(4*r*(2:Rat)^k)^M)) := by
  have h := LocalODE.tail_bound_shrinks (2*r) (4*r*(2:Rat)^k)
    (Rat.mul_nonneg (by decide) hr)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr) (Rat.pow_nonneg (by decide))) hlocal
  have he : (fun M : Nat => 4*(2*r)*(4*r*(2:Rat)^k)^M)=
      (fun M : Nat => 8*r*(4*r*(2:Rat)^k)^M) := by
    funext M
    grind only
  rw [he] at h
  exact SeriesLimitLaws.shrinks_scale _ h (N:Rat) Rat.natCast_nonneg

end ComputableAnalysis.ModularForms
