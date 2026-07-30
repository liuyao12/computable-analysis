import ComputableAnalysis.PiProofs

/-!
# Direct circumference refinement bridge

This module gives the direct chord-path diagnostic a small public interface to
the generic rational-circle midpoint theorem.  It deliberately stops before
the square-root bisection-width budget: that remaining finite rational margin
is stated separately by `PiProofs.AdjacentChordCurvatureMarginCoversFineWidths`.
-/

namespace ComputableAnalysis

namespace PiProofs

/-- The two rational curvature certificates of the doubled circle stage cover
the squared chord at the previous stage.

This is the concrete `circleSamplePoint` form of
`RationalCircle.Stage.midpoint_curvature_certificate_refines_squared_chord_of_refinement`.
It contains no square roots or limit argument.  To obtain the lower-endpoint
refinement of the original circumference algorithm, the two independently
certified square-root bisection widths must still be subtracted; that is the
separate margin condition `AdjacentChordCurvatureMarginCoversFineWidths`. -/
theorem adjacentCurvatureCertificates_refineSquaredChord
    (stage k : Nat) (hstage : 0 < stage) (hk : k < stage) :
    pointSegmentNormSq (circleSamplePoint stage k)
        (circleSamplePoint stage (k + 1)) <=
      sq (curvatureChordLower
            (circleSamplePoint (2 * stage) (2 * k))
            (circleSamplePoint (2 * stage) (2 * k + 1)) +
          curvatureChordLower
            (circleSamplePoint (2 * stage) (2 * k + 1))
            (circleSamplePoint (2 * stage) (2 * k + 2))) := by
  have href : RationalCircle.Stage.RefinesByDoubling
      (rationalCircleStage stage) (rationalCircleStage (2 * stage)) := by
    rfl
  simpa [circleSamplePoint_eq_rationalCircleStage,
    pointSegmentNormSq_eq_rationalCircleSegmentNormSq,
    curvatureChordLower, pointCross_eq_rationalCircleCross,
    RationalCircle.Stage.refineIndex, RationalCircle.Stage.insertedIndex,
    Rat.add_assoc] using
    (RationalCircle.Stage.midpoint_curvature_certificate_refines_squared_chord_of_refinement
      href hstage k hk)

/-- The explicit secant-margin budget holds at the initial one-cell stage.
This is a finite rational normalization check, not a numerical approximation
or a claim about all later stages. -/
theorem adjacentChordSecantMarginCoversFineDyadicBudget_one :
    AdjacentChordSecantMarginCoversFineDyadicBudget 1 := by
  intro k
  have hkzero : k = (⟨0, by omega⟩ : Fin 1) :=
    Fin.ext (by omega)
  subst k
  native_decide

/-- The original square-root lower-chord endpoint refines at the first dyadic
step.  The remaining direct-circumference problem is therefore the uniform
positive-stage margin theorem. -/
theorem adjacentChordLowerRefinesByDoubling_one :
    AdjacentChordLowerRefinesByDoubling 1 :=
  adjacentChordLowerRefinesByDoubling_of_secantMargin 1 (by native_decide)
    (adjacentChordSecantMargin_of_fineDyadicBudget 1 (by native_decide)
      adjacentChordSecantMarginCoversFineDyadicBudget_one)

/-- The same explicit secant-margin calculation succeeds for the two-cell
stage.  The cases are enumerated as rational arithmetic, not sampled
floating-point evidence. -/
theorem adjacentChordSecantMarginCoversFineDyadicBudget_two :
    AdjacentChordSecantMarginCoversFineDyadicBudget 2 := by
  intro k
  have hcases : k.1 = 0 ∨ k.1 = 1 := by omega
  rcases hcases with hzero | hone
  · have hk : k = (⟨0, by omega⟩ : Fin 2) := Fin.ext hzero
    rw [hk]
    simp
    native_decide
  · have hk : k = (⟨1, by omega⟩ : Fin 2) := Fin.ext hone
    rw [hk]
    simp
    native_decide

/-- The original chord endpoint also refines at the two-cell stage. -/
theorem adjacentChordLowerRefinesByDoubling_two :
    AdjacentChordLowerRefinesByDoubling 2 :=
  adjacentChordLowerRefinesByDoubling_of_secantMargin 2 (by native_decide)
    (adjacentChordSecantMargin_of_fineDyadicBudget 2 (by native_decide)
      adjacentChordSecantMarginCoversFineDyadicBudget_two)

end PiProofs

end ComputableAnalysis
