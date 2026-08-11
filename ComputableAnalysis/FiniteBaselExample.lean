import ComputableAnalysis.FiniteBaselCertificate

/-!
# A concrete finite Basel enclosure

This worked certificate instantiates the reciprocal-square interval algorithm
with a rational tolerance.  It is a finite containment statement for later
stages, not Euler's completed Basel identity.
-/

namespace ComputableAnalysis

namespace DirichletSeries

def baselExampleEps : Rat := 1 / 1000

theorem baselExampleEps_pos : 0 < baselExampleEps := by
  native_decide

def baselExampleCertificate : FiniteBaselCertificate baselExampleEps :=
  finiteBaselCertificateOfBudget 1001 baselExampleEps_pos (by native_decide)

theorem baselExampleCertificate_stage :
    baselExampleCertificate.stage = 1001 := by
  rfl

theorem baselExampleCertificate_width_le :
    baselExampleCertificate.interval.width <= baselExampleEps := by
  exact baselExampleCertificate.width_le

theorem baselExampleCertificate_contains_stage_2000 :
    baselExampleCertificate.interval.lo <= (zetaTwoInterval 2000).lo /\
      (zetaTwoInterval 2000).hi <= baselExampleCertificate.interval.hi /\
      (zetaTwoInterval 2000).width <= baselExampleEps := by
  apply baselExampleCertificate.contains_later
  native_decide

theorem baselExampleCertificate_contains_stage_100000 :
    baselExampleCertificate.interval.lo <= (zetaTwoInterval 100000).lo /\
      (zetaTwoInterval 100000).hi <= baselExampleCertificate.interval.hi /\
      (zetaTwoInterval 100000).width <= baselExampleEps := by
  apply baselExampleCertificate.contains_later
  native_decide

theorem zetaTwoPartial_stage16 :
    zetaTwoPartial 16 = 822968714749 / 519437318400 := by
  native_decide

theorem zetaTwoInterval_stage16 :
    zetaTwoInterval 16 =
      { lo := (822968714749 : Rat) / 519437318400,
        hi := (822968714749 : Rat) / 519437318400 + 1 / 16 } := by
  native_decide

def baselRefinedExampleEps : Rat := 1 / 10000

theorem baselRefinedExampleEps_pos : 0 < baselRefinedExampleEps := by
  native_decide

def baselRefinedExampleCertificate : FiniteBaselCertificate baselRefinedExampleEps :=
  finiteBaselCertificateOfBudget 10001 baselRefinedExampleEps_pos (by native_decide)

theorem baselRefinedExampleCertificate_stage :
    baselRefinedExampleCertificate.stage = 10001 := by
  rfl

theorem baselRefinedExampleCertificate_width_le :
    baselRefinedExampleCertificate.interval.width <= baselRefinedExampleEps := by
  exact baselRefinedExampleCertificate.width_le

theorem baselRefinedExampleCertificate_contains_stage_100000 :
    baselRefinedExampleCertificate.interval.lo <= (zetaTwoInterval 100000).lo /\
      (zetaTwoInterval 100000).hi <= baselRefinedExampleCertificate.interval.hi /\
      (zetaTwoInterval 100000).width <= baselRefinedExampleEps := by
  apply baselRefinedExampleCertificate.contains_later
  native_decide

theorem baselRefinedExampleCertificate_contains_stage_200000 :
    baselRefinedExampleCertificate.interval.lo <= (zetaTwoInterval 200000).lo /\
      (zetaTwoInterval 200000).hi <= baselRefinedExampleCertificate.interval.hi /\
      (zetaTwoInterval 200000).width <= baselRefinedExampleEps := by
  apply baselRefinedExampleCertificate.contains_later
  native_decide

def baselHighPrecisionExampleEps : Rat := 1 / 100000

theorem baselHighPrecisionExampleEps_pos : 0 < baselHighPrecisionExampleEps := by
  native_decide

def baselHighPrecisionExampleCertificate :
    FiniteBaselCertificate baselHighPrecisionExampleEps :=
  finiteBaselCertificateOfBudget 100001 baselHighPrecisionExampleEps_pos
    (by native_decide)

theorem baselHighPrecisionExampleCertificate_stage :
    baselHighPrecisionExampleCertificate.stage = 100001 := by
  rfl

theorem baselHighPrecisionExampleCertificate_width_le :
    baselHighPrecisionExampleCertificate.interval.width <=
      baselHighPrecisionExampleEps := by
  exact baselHighPrecisionExampleCertificate.width_le

theorem baselHighPrecisionExampleCertificate_contains_stage_200000 :
    baselHighPrecisionExampleCertificate.interval.lo <=
        (zetaTwoInterval 200000).lo /\
      (zetaTwoInterval 200000).hi <=
        baselHighPrecisionExampleCertificate.interval.hi /\
      (zetaTwoInterval 200000).width <= baselHighPrecisionExampleEps := by
  apply baselHighPrecisionExampleCertificate.contains_later
  native_decide

end DirichletSeries

end ComputableAnalysis
