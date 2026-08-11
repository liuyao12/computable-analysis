import ComputableAnalysis.PiProofs

namespace ComputableAnalysis

example (rep : RealRaw)
    (hrep : rep ∈ [piCircleAreaPolygon, piCircumferenceStabilized,
      piCircumferenceReboxed, piCircumferenceFan,
      (4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat),
      piFromArctanIntegralRectangleUnitAtOne, piLeibniz, piNilakantha,
      piMachin, IntegralIdentities.cauchyFullLineIntegral,
      piReciprocalQuarticCompact]) : True := by
  change rep = piCircleAreaPolygon \/
    rep = piCircumferenceStabilized \/
    rep = piCircumferenceReboxed \/
    rep = piCircumferenceFan \/
    rep = ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) \/
    rep = piFromArctanIntegralRectangleUnitAtOne \/
    rep = piLeibniz \/ rep = piNilakantha \/ rep = piMachin \/
    rep = IntegralIdentities.cauchyFullLineIntegral \/
    rep = piReciprocalQuarticCompact at hrep
  trivial

end ComputableAnalysis
