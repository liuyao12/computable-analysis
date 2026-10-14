import ComputableAnalysis.ModularForms.RotationExponentialPrefix
import ComputableAnalysis.ModularForms.ExponentialDerivative

/-! Exact rational imaginary-axis exponential/rotation agreement. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert LocalODE

theorem entireExponential_uniform_rotation (T : Rat) (hT : qabs T ≤ 2) :
    (entireExponentialValue ⟨ofQComplex (RotationSeries.imaginaryAxis T),ofQComplex_valid _⟩).val.Equiv
      (RotationSeries.uniformRotationExpRaw T) := by
  let z : Scalar := ⟨ofQComplex (RotationSeries.imaginaryAxis T),ofQComplex_valid _⟩
  let R := exponentialInputRadius z
  let C := exponentialBudget (exponentialRatio R)
  let q := 2*exponentialRatio R*R.val
  let terms := RotationSeries.uniformRotationTailTerms
  let p := fun n => ofQComplex (RotationSeries.uniformRotationCenter T n)
  let e := fun (n : Nat) => 4*C*q^(terms n)
  let g := centerError (RotationSeries.uniformRotationExpRaw T)
  have hC : 0 ≤ C := exponentialBudget_nonnegative _ (exponentialRatio_positive R)
  have hK := Rat.le_of_lt (exponentialRatio_positive R)
  have hR := Rat.le_of_lt R.property
  have hq : 0 ≤ q := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hK) hR
  have hlocal : q ≤ (1 : Rat)/2 := by
    have h := exponentialRatio_local R
    dsimp [q]
    grind
  have he : ShrinksToZero e := by
    intro eps
    obtain ⟨N,hN⟩ := tail_bound_shrinks C q hC hq hlocal eps
    refine ⟨N,?_⟩
    intro n hn
    exact hN (terms n) (by dsimp [terms,RotationSeries.uniformRotationTailTerms]; omega)
  have hg : ShrinksToZero g := uniform_rotation_prefix_error_shrinks T hT
  have hv := (entireExponentialValue z).property
  have hl := RotationSeries.uniformRotationExpRaw_valid T hT
  apply RepresentedCauchySum.unique p (fun n => ofQComplex_valid _) (fun n => e n+g n)
    (RepresentedCauchySum.sum_shrinks e g he hg) _ _ hv hl
  · intro n
    have hb := BoundedSeries.sumValue_close_prefix exponentialCoefficients z.val
      exponentialCoefficients_valid z.property C _ _ hC hK hR
      (exponentialCoefficients_small _ (exponentialRatio_positive R))
      (interior_bound R.val z (exponentialInputRadius_mem z)) hlocal (terms n)
    rw [BoundedSeries.valueBlock_as_terms] at hb
    have ht := seriesTerm_valid _ _ exponentialCoefficients_valid z.property
    have hp := ScalarSeries.block_valid _ ht 0 (terms n)
    have heq : (ScalarSeries.block (seriesTerm exponentialCoefficients z.val) 0 (terms n)).Equiv (p n) := by
      intro stage
      apply (compareAt_overlap_iff _ _ stage stage).mpr
      rw [uniform_rotation_candidate_compute]
      exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩
    have hs := Small.congr (sub_valid hv hp) (sub_valid hv (ofQComplex_valid _))
      (FunctionTheory.sub_congr (equiv_refl _ hv) heq) hb
    apply hs.mono
    have hn : 0 ≤ g n := centerError_nonnegative _ hl n
    change e n ≤ e n+g n
    grind
  · intro n
    have hb := uniform_rotation_prefix_error T hT n
    apply hb.mono
    have hn : 0 ≤ e n := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC)
      (Rat.pow_nonneg hq)
    change g n ≤ e n+g n
    grind

end ComputableAnalysis.ModularForms
