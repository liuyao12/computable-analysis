import ComputableAnalysis.ModularForms.SquareContourRadiusDoubling

/-! The actual contour candidate vanishes by proved radius invariance and decay. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem doubledContourRadius_inverse (R : QPos) (n : Nat) :
    1/(doubledContourRadius R n).val=(1/R.val)*((1:Rat)/2)^n := by
  induction n with
  | zero => simp only [doubledContourRadius,Rat.pow_zero,Rat.mul_one]
  | succ n ih =>
    change 1/(2*(doubledContourRadius R n).val)=(1/R.val)*((1:Rat)/2)^(n+1)
    rw [Rat.pow_succ]
    have he : 1/(2*(doubledContourRadius R n).val)=
        (1/(doubledContourRadius R n).val)*((1:Rat)/2) := by
      simp only [Rat.div_def,Rat.inv_mul_rev,Rat.one_mul]
    rw [he,ih]
    grind only

theorem rational_half_geometric_shrinks (C : Rat) (hC : 0≤C) :
    ShrinksToZero (fun n => C*((1:Rat)/2)^n) := by
  intro eps
  refine ⟨RationalMajorant.natRateStage C eps, ?_⟩
  intro n hn
  have hb := Rat.mul_le_mul_of_nonneg_left (RationalMajorant.half_pow_le_one_div_succ n) hC
  have he : C*(1/((n+1:Nat):Rat))=C/((n+1:Nat):Rat) := by
    simp only [Rat.div_def,Rat.one_mul]
  rw [he] at hb
  exact Rat.le_trans hb (RationalMajorant.natRateStage_spec_of_le hC eps hn)

theorem executableSquareContour_zero_bound (c : Scalar) (R : QPos) :
    Small (executableSquareContour c R.val) 0 := by
  let C := 343669760*(1/R.val)
  have hC : 0≤C := Rat.mul_nonneg (by decide +kernel)
    (by rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr R.property))
  apply SeriesLimitLaws.small_closed (executableSquareContour c R.val) 0
    (fun n => C*((1:Rat)/2)^n) (rational_half_geometric_shrinks C hC)
  intro n
  have hb := executableSquareContour_bound c (doubledContourRadius R n).val
    (doubledContourRadius R n).property
  have hs := Small.congr
    (executableSquareContour_valid c (doubledContourRadius R n).val (doubledContourRadius R n).property)
    (executableSquareContour_valid c R.val R.property)
    (executableSquareContour_iterated_doubling c R n) hb
  rw [doubledContourRadius_inverse] at hs
  have he : 343669760*((1/R.val)*((1:Rat)/2)^n)=0+C*((1:Rat)/2)^n := by
    dsimp [C]; grind only
  rw [he] at hs
  exact hs

theorem executableSquareContour_equiv_zero (c : Scalar) (R : QPos) :
    (executableSquareContour c R.val).Equiv zero := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  have h := SeriesLimitLaws.small_sub (executableSquareContour_zero_bound c R)
    (Small.zero (by decide +kernel : (0:Rat)≤0))
  simpa only [Rat.zero_add] using h

theorem pairedSquareContourLimit_equiv_zero (c : Scalar) (R : QPos) :
    (pairedSquareContourLimit c R.val R.property).Equiv zero :=
  equiv_trans (pairedSquareContourLimit_valid c R.val R.property)
    (executableSquareContour_valid c R.val R.property) (ofQComplex_valid _)
    (equiv_symm (executableSquareContour_agreement c R.val R.property))
    (executableSquareContour_equiv_zero c R)

end ComputableAnalysis.ModularForms
