import ComputableAnalysis.ModularForms.PairedRiccatiSquareKernelBound

/-! Bounds for actual squared-kernel contour densities on large squares. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions PDE.CauchyContour

theorem scaledSquareVelocity_coordinate_bound (edge : HalfEdge) (R : Rat) (hR : 0≤R) :
    BoxApproximation.coordinateBound (QComplex.scaleRat R (velocity edge))≤R := by
  cases edge with
  | mk quarter upper =>
    cases quarter <;> cases upper <;>
      unfold velocity rotation orientation QComplex.mul QComplex.scaleRat BoxApproximation.coordinateBound qabs <;>
      simp only [if_true] <;> grind

theorem pairedEntireRiccatiMap_square_density_bound (z : Scalar) (edge : HalfEdge)
    (u R : Rat) (hR : 0<R) :
    Small (mul
      (mul (pairedEntireRiccatiMap.eval z trivial).val
        (mul (ofQComplex (RationalReciprocal.inverse (QComplex.scaleRat R (point edge u))))
          (ofQComplex (RationalReciprocal.inverse (QComplex.scaleRat R (point edge u))))))
      (ofQComplex (QComplex.scaleRat R (velocity edge)))) (42958720*(1/R)) := by
  have hn := Rat.le_of_lt hR
  have hv := (BoxApproximation.rational_small _).mono
    (scaledSquareVelocity_coordinate_bound edge R hn)
  have hi : 0≤(1:Rat)/R := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr hR))
  have hs := Small.mul
    (mul_valid (pairedEntireRiccatiMap.eval z trivial).property
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))) (ofQComplex_valid _)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hi) hi) hn
    (pairedEntireRiccatiMap_square_kernel_bound z edge u R hR) hv
  have hc : R⁻¹*R=1 := Rat.inv_mul_cancel R (Rat.ne_of_gt hR)
  have he : 2*(21479360*(1/R)*(1/R))*R=42958720*(1/R) := by
    simp only [Rat.div_def,Rat.one_mul]
    calc
      2*(21479360*R⁻¹*R⁻¹)*R = (2*21479360)*R⁻¹*(R⁻¹*R) := by grind only
      _ = 42958720*R⁻¹ := by rw [hc]; grind only
  rw [he] at hs
  exact hs

end ComputableAnalysis.ModularForms
