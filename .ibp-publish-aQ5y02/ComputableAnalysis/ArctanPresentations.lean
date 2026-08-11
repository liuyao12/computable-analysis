import ComputableAnalysis.ArctanGeometry
import ComputableAnalysis.PowerSeries

/-!
# Named arctangent presentations

This small naming layer exposes the geometric and alternating-series
algorithms as two explicit presentations of the same intended rational-input
function.  They remain `FunctionRepresentation`s rather than being silently
quotiented: their domains differ, and an equivalence theorem is meaningful
only on their certified common domain.
-/

namespace ComputableAnalysis

/-! Tidy public names for the two primary arctangent presentations.

At a certified rational input, either raw can be turned into a `Real` with
`Real.ofRaw`; once a pointwise agreement theorem is available, `Real.withAlternative`
records the other raw as a verified alternative computation. -/
namespace arctan

/-- Arctangent from geometric sector-area exhaustion.

This is the public dot-qualified presentation; the older
`ArctanGeometry.arctanGeom` remains the implementation-level raw evaluator. -/
def geom : Elementary.Arctan.FunctionRepresentation where
  name := "arctan.geom"
  raw := ArctanGeometry.representation.raw

/-- Arctangent from its alternating power series on `|x| <= 1`.

This is the public dot-qualified presentation; the shorter `arctan` and
`arctanSeries` names remain compatibility aliases for the raw evaluator. -/
def series : Elementary.Arctan.FunctionRepresentation where
  name := "arctan.series"
  raw := Elementary.Arctan.powerSeries.raw

theorem geom_raw_eq : geom.raw = ArctanGeometry.representation.raw := rfl

theorem series_raw_eq : series.raw = Elementary.Arctan.powerSeries.raw := rfl

end arctan

end ComputableAnalysis
