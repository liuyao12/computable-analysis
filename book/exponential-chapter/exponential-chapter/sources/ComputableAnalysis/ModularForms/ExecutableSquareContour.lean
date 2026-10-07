import ComputableAnalysis.ModularForms.PairedSquareContourRefinementRate
import ComputableAnalysis.ModularForms.PairedSquareContourLimitInvariance

/-! An executable interval-name candidate for the actual square density.
Its role as a contour integral or in the Cauchy formula is not asserted here. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem squareContourTail_nonneg (R : Rat) (hR : 0<R) (n : Nat) :
    0≤squareContourTail R n :=
  Rat.mul_nonneg (by decide +kernel) (Rat.mul_nonneg
    (squareDensityLipschitzConstant_nonneg R hR)
    (Rat.pow_nonneg (by decide +kernel)))

def squareContourPrecisionStage (R : Rat) (eps : QPos) : Nat :=
  RationalMajorant.natRateStage (8*squareDensityLipschitzConstant R) eps

theorem squareContourPrecisionStage_spec (R : Rat) (hR : 0<R)
    (eps : QPos) (n : Nat) (hn : squareContourPrecisionStage R eps≤n) :
    squareContourTail R n≤eps.val := by
  have hC : 0≤8*squareDensityLipschitzConstant R :=
    Rat.mul_nonneg (by decide +kernel) (squareDensityLipschitzConstant_nonneg R hR)
  have hb := Rat.mul_le_mul_of_nonneg_left
    (RationalMajorant.half_pow_le_one_div_succ n) hC
  have he : (8*squareDensityLipschitzConstant R)*(1/((n+1:Nat):Rat))=
      (8*squareDensityLipschitzConstant R)/((n+1:Nat):Rat) := by
    rw [Rat.div_def,Rat.div_def,Rat.one_mul]
  rw [he] at hb
  have ht : squareContourTail R n=
      (8*squareDensityLipschitzConstant R)*((1:Rat)/2)^n := by
    unfold squareContourTail
    grind only
  rw [ht]
  exact Rat.le_trans hb (RationalMajorant.natRateStage_spec_of_le hC eps hn)

theorem squareContourTail_shrinks (R : Rat) (hR : 0<R) :
    ShrinksToZero (squareContourTail R) := by
  intro eps
  exact ⟨squareContourPrecisionStage R eps, squareContourPrecisionStage_spec R hR eps⟩

theorem pairedSquareDyadicContour_prefix_error (a : Scalar) (R : Rat)
    (hR : 0<R) (k n : Nat) (hkn : k≤n) :
    Small (sub (pairedSquareDyadicContour a R n).val
      (pairedSquareDyadicContour a R k).val) (squareContourTail R k) := by
  have hb := pairedSquareDyadicContour_refinement_rate a R hR k (n-k)
  rw [Nat.add_sub_of_le hkn] at hb
  exact hb

def executableSquareContour (a : Scalar) (R : Rat) : ComplexRaw :=
  RepresentedCauchySum.value (fun n => (pairedSquareDyadicContour a R n).val)
    (fun n => (pairedSquareDyadicContour a R n).property) (squareContourTail R)

theorem executableSquareContour_valid (a : Scalar) (R : Rat) (hR : 0<R) :
    (executableSquareContour a R).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (squareContourTail_shrinks R hR)
    (pairedSquareDyadicContour_prefix_error a R hR)

theorem executableSquareContour_sample_error (a : Scalar) (R : Rat) (hR : 0<R)
    (n : Nat) : Small (sub (executableSquareContour a R)
      (pairedSquareDyadicContour a R n).val) (squareContourTail R n) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (pairedSquareDyadicContour_prefix_error a R hR) n

theorem executableSquareContour_convergence (a : Scalar) (R : Rat) (hR : 0<R)
    (eps : QPos) (n : Nat) (hn : squareContourPrecisionStage R eps≤n) :
    Small (sub (executableSquareContour a R)
      (pairedSquareDyadicContour a R n).val) eps.val :=
  (executableSquareContour_sample_error a R hR n).mono
    (squareContourPrecisionStage_spec R hR eps n hn)

theorem executableSquareContour_agreement (a : Scalar) (R : Rat) (hR : 0<R) :
    (executableSquareContour a R).Equiv (pairedSquareContourLimit a R hR) := by
  apply pairedSquareContourLimit_unique a R hR
    ⟨executableSquareContour a R,executableSquareContour_valid a R hR⟩
  intro eps
  exact ⟨squareContourPrecisionStage R eps, executableSquareContour_convergence a R hR eps⟩

theorem executableSquareContour_congr (a b : Scalar) (he : a.val.Equiv b.val)
    (R : Rat) (hR : 0<R) :
    (executableSquareContour a R).Equiv (executableSquareContour b R) :=
  equiv_trans (executableSquareContour_valid a R hR)
    (pairedSquareContourLimit_valid a R hR) (executableSquareContour_valid b R hR)
    (executableSquareContour_agreement a R hR)
    (equiv_trans (pairedSquareContourLimit_valid a R hR)
      (pairedSquareContourLimit_valid b R hR) (executableSquareContour_valid b R hR)
      (pairedSquareContourLimit_congr a b he R hR)
      (equiv_symm (executableSquareContour_agreement b R hR)))

theorem executableSquareContour_bound (a : Scalar) (R : Rat) (hR : 0<R) :
    Small (executableSquareContour a R) (343669760*(1/R)) :=
  Small.congr (pairedSquareContourLimit_valid a R hR)
    (executableSquareContour_valid a R hR)
    (equiv_symm (executableSquareContour_agreement a R hR))
    (pairedSquareContourLimit_bound a R hR)

end ComputableAnalysis.ModularForms
