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

end PiProofs

end ComputableAnalysis
