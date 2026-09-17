import ComputableAnalysis.CartwrightIrrationality
import ComputableAnalysis.CartwrightCalculusData
import ComputableAnalysis.FiniteSummationByParts

/-! Direct finite-sum route. The import supplies common polynomial definitions,
sample bounds and local sine/cosine increment estimates; this route does NOT
call the general FTC, its finite_telescope theorem, or the composite primitive
models. Instead it uses exact discrete summation by parts twice. -/
namespace ComputableAnalysis.CartwrightMoments
open ClosedArctanInverse RationalSampleLimits FiniteSampleCalculus FiniteSummationByParts

private theorem constant_bound (c : Rat) (hc : 0≤c) : Bounded (fun (_:Nat)=>c) c :=
  fun _=>by rw [qabs_eq_self_of_nonneg hc];exact Rat.le_refl

/-- Two exact finite product identities, followed by their explicit remainder
bounds, give the same moment recurrence without invoking the general FTC. -/
theorem recurrence_viaFinite (n : Nat) : Small (recurrenceSamples n) := by
  let B : Rat := 2*((n+2:Nat):Rat)
  have hB : 0≤B := Rat.mul_nonneg (by decide) (Rat.natCast_nonneg (a:=n+2))
  have h:=two_products_close (weightModel (n+2)) sineModel
    (weightedCoordinateModel n) cosineModel
    frequencySample (fun _=>B) 2 B (by decide) hB frequency_bound (constant_bound B hB)
    (recurrenceSamples n) (4+recurrenceA n+recurrenceB n)
    (Rat.add_nonneg (Rat.add_nonneg (by decide) (recurrenceA_nonneg n)) (recurrenceB_nonneg n)) ?_
  · have he : (fun q=>frequencySample q*(weight (n+2) 1*ClockTrigonometry.s 1 q-
        weight (n+2) 0*ClockTrigonometry.s 0 q)-B*((1*weight (n+1) 1)*ClockTrigonometry.c 1 q-
        (0*weight (n+1) 0)*ClockTrigonometry.c 0 q))=
        (fun q=>recurrencePrimitive n 1 q-recurrencePrimitive n 0 q) := by
      funext q;unfold recurrencePrimitive;dsimp [B];grind only
    rw [he] at h
    have hsum:=small_add h (recurrence_boundary_small n)
    have hid : (fun q=>(recurrenceSamples n q-(recurrencePrimitive n 1 q-recurrencePrimitive n 0 q))+
        (recurrencePrimitive n 1 q-recurrencePrimitive n 0 q))=recurrenceSamples n := by funext q;grind
    rw [hid] at hsum
    exact hsum
  · intro d q hdq
    have hfun : (fun x=>frequencySample q*(weight (n+2) x*(frequencySample q*ClockTrigonometry.c x q)+
        ClockTrigonometry.s x q*weightDerivative (n+2) x)-
        B*((x*weight (n+1) x)*(-frequencySample q*ClockTrigonometry.s x q)+
          ClockTrigonometry.c x q*(weight (n+1) x-2*((n+1:Nat):Rat)*x*x*weight n x)))=
        (fun x=>recurrenceDerivative n x q) := by
      funext x
      unfold recurrenceDerivative recurrenceA recurrenceB sample
      dsimp [B]
      simp only [weightDerivative,weight,Rat.pow_succ,Rat.natCast_add,Rat.natCast_ofNat]
      grind only
    rw [hfun]
    exact recurrence_mesh_error n d q hdq

theorem first_viaFinite : Small firstSamples := by
  have h:=two_products_close singleWeightModel sineModel Model.identity cosineModel
    frequencySample (fun _=>2) 2 2 (by decide) (by decide) frequency_bound
    (constant_bound 2 (by decide)) firstSamples 6 (by decide) ?_
  · have he : (fun q=>frequencySample q*((1-1*1)*ClockTrigonometry.s 1 q-
        (1-0*0)*ClockTrigonometry.s 0 q)-2*(1*ClockTrigonometry.c 1 q-0*ClockTrigonometry.c 0 q))=
        (fun q=>firstPrimitive 1 q-firstPrimitive 0 q) := by
      funext q;unfold firstPrimitive;grind only
    rw [he] at h
    have hsum:=small_add h first_boundary_small
    have hid : (fun q=>(firstSamples q-(firstPrimitive 1 q-firstPrimitive 0 q))+
        (firstPrimitive 1 q-firstPrimitive 0 q))=firstSamples := by funext q;grind
    rw [hid] at hsum
    exact hsum
  · intro d q hdq
    have hfun : (fun x=>frequencySample q*((1-x*x)*(frequencySample q*ClockTrigonometry.c x q)+
        ClockTrigonometry.s x q*(-2*x))-2*(x*(-frequencySample q*ClockTrigonometry.s x q)+
        ClockTrigonometry.c x q*1))=(fun x=>firstDerivative x q) := by
      funext x;unfold firstDerivative sample
      simp only [weight,Rat.pow_succ,Rat.pow_zero]
      grind only
    rw [hfun]
    exact first_mesh_error d q hdq

theorem zero_viaFinite : Close (fun q=>frequencySample q*momentSample 0 q) (fun _=>1) := by
  have h:=two_products_close (Model.const 1) sineModel (Model.const 0) (Model.const 0)
    (fun _=>1) (fun _=>0) 1 0 (by decide) (by decide)
    (constant_bound 1 (by decide)) (constant_bound 0 (by decide))
    (fun q=>frequencySample q*momentSample 0 q) 2 (by decide) ?_
  · have he : (fun q=>1*(1*ClockTrigonometry.s 1 q-1*ClockTrigonometry.s 0 q)-0*(0*0-0*0))=
        (fun q=>ClockTrigonometry.s 1 q-ClockTrigonometry.s 0 q) := by funext q;grind
    rw [he] at h
    have h0 : Close (ClockTrigonometry.s 0) (fun _=>0) := by
      change Small (fun q=>ClockTrigonometry.s 0 q-0)
      have he : (fun q=>ClockTrigonometry.s 0 q-0)=ClockTrigonometry.s 0 := by funext q;grind
      rw [he];exact sine_zero_small
    have hb:=close_sub sine_one_close h0
    have he : (fun (_:Nat)=>(1:Rat)-0)=(fun (_:Nat)=>1) := by funext q;decide +kernel
    rw [he] at hb
    exact close_trans h hb
  · intro d q hdq
    have hfun : (fun x=>1*(1*(frequencySample q*ClockTrigonometry.c x q)+ClockTrigonometry.s x q*0)-0*(0*0+0*0))=
        (fun x=>frequencySample q*ClockTrigonometry.c x q) := by funext x;grind
    rw [hfun]
    exact zero_mesh_error d q hdq

/-- A fully supplied alternative, not a hypothetical analytic provider. -/
theorem lawsViaFinite : MomentLaws where
  zero := zero_viaFinite
  first := first_viaFinite
  recurrence := recurrence_viaFinite

theorem evaluation_viaFinite (n : Nat) : EvaluationStatement n := evaluation_of_laws lawsViaFinite n

theorem piSquared_viaFinite : PiSquaredStatement := piSquared_of_laws lawsViaFinite

end ComputableAnalysis.CartwrightMoments
