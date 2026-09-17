import ComputableAnalysis.CartwrightCalculusData

/-! Native FTC route: one polynomial-trigonometric primitive gives the
moment recurrence. The finite-sum route does not import this module. -/
namespace ComputableAnalysis.CartwrightMoments
open ClosedArctanInverse SinPiIntegral IntervalSelections
open FiniteSampleCalculus RationalSampleLimits
private theorem qsubzero (x : Rat) : x-0=x := by grind

/-- One polynomial-trigonometric primitive replaces the two integrations
by parts. The derivative is a literal finite rational identity. -/
def recurrenceModel (n : Nat) : Model (recurrencePrimitive n) (recurrenceDerivative n) := by
  let f := (frequencyModel.mul (weightModel (n+2))).mul sineModel
  let g := ((Model.const (2*((n+2:Nat):Rat))).mul (weightedCoordinateModel n)).mul cosineModel
  apply (f.sub g).congr
  · intro x q
    change frequencySample q*weight (n+2) x*ClockTrigonometry.s x q-
      (2*((n+2:Nat):Rat)*(x*weight (n+1) x))*ClockTrigonometry.c x q = recurrencePrimitive n x q
    unfold recurrencePrimitive
    grind only
  · intro x q
    change (0*weight (n+2) x+frequencySample q*weightDerivative (n+2) x)*ClockTrigonometry.s x q+
      (frequencySample q*weight (n+2) x)*(frequencySample q*ClockTrigonometry.c x q)-
      ((0*(x*weight (n+1) x)+(2*((n+2:Nat):Rat))*(weight (n+1) x-2*((n+1:Nat):Rat)*x*x*weight n x))*ClockTrigonometry.c x q+
        ((2*((n+2:Nat):Rat))*(x*weight (n+1) x))*(-frequencySample q*ClockTrigonometry.s x q)) = recurrenceDerivative n x q
    unfold recurrenceDerivative recurrenceA recurrenceB sample
    simp only [weightDerivative,weight,Rat.pow_succ,Rat.natCast_add,Rat.natCast_ofNat]
    grind only

def firstModel : Model firstPrimitive firstDerivative := by
  let f := (frequencyModel.mul singleWeightModel).mul sineModel
  let g := ((Model.const 2).mul Model.identity).mul cosineModel
  apply (f.sub g).congr
  · intro x q
    change frequencySample q*(1-x*x)*ClockTrigonometry.s x q-(2*x)*ClockTrigonometry.c x q=firstPrimitive x q
    rfl
  · intro x q
    change (0*(1-x*x)+frequencySample q*(-2*x))*ClockTrigonometry.s x q+
      (frequencySample q*(1-x*x))*(frequencySample q*ClockTrigonometry.c x q)-
      ((0*x+2*1)*ClockTrigonometry.c x q+(2*x)*(-frequencySample q*ClockTrigonometry.s x q))=firstDerivative x q
    unfold firstDerivative sample
    simp only [weight,Rat.pow_succ,Rat.pow_zero]
    grind only

/-- The moment recurrence, obtained by the reusable native FTC. -/
theorem recurrence_viaFTC (n : Nat) : Small (recurrenceSamples n) := by
  have h:=chosen_samples_FTC (recurrenceModel n) (recurrenceSamples n)
    (4+recurrenceA n+recurrenceB n)
    (Rat.add_nonneg (Rat.add_nonneg (by decide) (recurrenceA_nonneg n)) (recurrenceB_nonneg n))
    (recurrence_mesh_error n)
  have ht:=small_add h (recurrence_boundary_small n)
  have he : (fun q => (recurrenceSamples n q-(recurrencePrimitive n 1 q-recurrencePrimitive n 0 q))+
      (recurrencePrimitive n 1 q-recurrencePrimitive n 0 q))=recurrenceSamples n := by funext q;grind
  rw [he] at ht
  exact ht

theorem first_viaFTC : Small firstSamples := by
  have h:=chosen_samples_FTC firstModel firstSamples 6 (by decide) first_mesh_error
  have ht:=small_add h first_boundary_small
  have he : (fun q => (firstSamples q-(firstPrimitive 1 q-firstPrimitive 0 q))+
      (firstPrimitive 1 q-firstPrimitive 0 q))=firstSamples := by funext q;grind
  rw [he] at ht
  exact ht

theorem zero_viaFTC : Close (fun q=>frequencySample q*momentSample 0 q) (fun _=>1) := by
  have h:=chosen_samples_FTC sineModel (fun q=>frequencySample q*momentSample 0 q) 2 (by decide) zero_mesh_error
  have h0 : Close (ClockTrigonometry.s 0) (fun _=>0) := by
    simpa only [Close,qsubzero] using sine_zero_small
  have he:=close_sub sine_one_close h0
  have he' : Close (fun q=>ClockTrigonometry.s 1 q-ClockTrigonometry.s 0 q) (fun _=>1) := by
    simpa only [qsubzero] using he
  exact close_trans h he'


end ComputableAnalysis.CartwrightMoments
