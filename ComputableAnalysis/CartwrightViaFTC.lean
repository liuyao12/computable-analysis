import ComputableAnalysis.CartwrightIrrationality
import ComputableAnalysis.CartwrightMomentFTC

/-! Closed native FTC route. There is no caller-supplied moment law, integral
certificate or rationality contradiction left as a hypothesis. -/
namespace ComputableAnalysis.CartwrightMoments

theorem lawsViaFTC : MomentLaws where
  zero := zero_viaFTC
  first := first_viaFTC
  recurrence := recurrence_viaFTC

theorem evaluation_viaFTC (n : Nat) : EvaluationStatement n := evaluation_of_laws lawsViaFTC n

theorem piSquared_viaFTC : PiSquaredStatement := piSquared_of_laws lawsViaFTC

end ComputableAnalysis.CartwrightMoments
