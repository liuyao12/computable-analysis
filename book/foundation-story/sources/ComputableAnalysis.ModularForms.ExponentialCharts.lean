import ComputableAnalysis.ModularForms.ExponentialMajorant

/-! Actual holomorphic exponential-series charts at every positive rational
radius, with exact overlap agreement between all radius choices. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def exponentialRatio (R : QPos) : Rat := 1/(32*R.val)

theorem exponentialRatio_positive (R : QPos) : 0 < exponentialRatio R := by
  unfold exponentialRatio
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.inv_pos.mpr (Rat.mul_pos (by decide +kernel) R.property)

theorem exponentialRatio_local (R : QPos) : 8*exponentialRatio R*R.val ≤ (1 : Rat)/2 := by
  have hp : 0 < 32*R.val := Rat.mul_pos (by decide +kernel) R.property
  have hc := Rat.mul_inv_cancel (32*R.val) (Rat.ne_of_gt hp)
  unfold exponentialRatio
  rw [Rat.div_def, Rat.one_mul]
  grind

def exponentialChart (R : QPos) : CertifiedFunctions.Map :=
  BoundedSeries.seriesMap exponentialCoefficients exponentialCoefficients_valid
    (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val
    (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
    (Rat.le_of_lt (exponentialRatio_positive R)) (Rat.le_of_lt R.property)
    (exponentialCoefficients_small _ (exponentialRatio_positive R)) (exponentialRatio_local R)

def exponentialChart_holomorphic (R : QPos) : CertifiedFunctions.Holomorphic (exponentialChart R) :=
  BoundedSeries.seriesMap_holomorphic exponentialCoefficients exponentialCoefficients_valid
    (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val
    (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
    (Rat.le_of_lt (exponentialRatio_positive R)) (Rat.le_of_lt R.property)
    (exponentialCoefficients_small _ (exponentialRatio_positive R)) (exponentialRatio_local R)

/-- All charts represent the same exponential wherever both are defined. -/
theorem exponentialChart_agreement (R S : QPos) (z w : Scalar)
    (hz : (exponentialChart R).domain z) (hw : (exponentialChart S).domain w)
    (hzw : z.val.Equiv w.val) :
    ((exponentialChart R).eval z).Equiv ((exponentialChart S).eval w) :=
  BoundedSeries.seriesMap_congr exponentialCoefficients exponentialCoefficients
    exponentialCoefficients_valid exponentialCoefficients_valid
    (fun i => equiv_refl _ (exponentialCoefficients_valid i))
    (exponentialBudget (exponentialRatio R)) (exponentialRatio R) R.val
    (exponentialBudget (exponentialRatio S)) (exponentialRatio S) S.val
    (exponentialBudget_nonnegative _ (exponentialRatio_positive R))
    (Rat.le_of_lt (exponentialRatio_positive R)) (Rat.le_of_lt R.property)
    (exponentialBudget_nonnegative _ (exponentialRatio_positive S))
    (Rat.le_of_lt (exponentialRatio_positive S)) (Rat.le_of_lt S.property)
    (exponentialCoefficients_small _ (exponentialRatio_positive R))
    (exponentialCoefficients_small _ (exponentialRatio_positive S))
    (exponentialRatio_local R) (exponentialRatio_local S) z w hz hw hzw

end ComputableAnalysis.ModularForms
