import ComputableAnalysis.SineSquareData
import ComputableAnalysis.CosineSquareFTC

/-! The sine-square endpoint formula, proved by a finite derivative model and
comparison with its own rectangle sums. -/
namespace ComputableAnalysis.SineSquare
open ClosedArctanInverse ClockTrigonometry MonotoneAverage IntervalSelections
open CartwrightMoments FiniteSampleCalculus RationalSampleLimits

def endpointSample (t : Rat) (q : Nat) : Rat := t-CosineSquare.primitiveSample t q

def endpointModel : Model endpointSample sample := by
  apply (Model.identity.add ((Model.const (-1)).mul CosineSquare.primitiveModel)).congr
  · intro t q; unfold endpointSample; grind only
  · intro t q
    change 1+(0*CosineSquare.primitiveSample t q+(-1)*CosineSquare.sample t q)=sample t q
    rw [sample_complement]; grind only

def normalizedEndpointSample (x : Rat) (q : Nat) : Rat := endpointSample (2*x) q/2

theorem normalizedEndpoint_formula (x : Rat) (q : Nat) :
    normalizedEndpointSample x q=x/2-CosineSquare.reciprocalSample q*s (2*x) q*c (2*x) q/2 := by
  unfold normalizedEndpointSample endpointSample CosineSquare.primitiveSample
  simp only [Rat.div_def]; grind only

theorem endpoint_close : Close (fun q=>endpointSample 1 q-endpointSample 0 q) (fun _=>1/2) := by
  have h:=close_sub (close_refl (fun _=>(1:Rat))) CosineSquare.primitive_endpoints_close
  simpa only [endpointSample,show (1:Rat)-1/2=1/2 by decide +kernel,
    show ∀ a b:Rat, (1-a)-(0-b)=1-(a-b) by intros;grind] using h

theorem sumSample_via_FTC : Close sumSample (fun _=>1/2) := by
  have h:=chosen_samples_FTC endpointModel sumSample 1 (by decide +kernel) (by
    intro d q hdq
    simpa only [Rat.one_mul] using mesh_comparison d q hdq)
  exact close_trans h endpoint_close

theorem integral_via_FTC : integral.Equiv (RealRaw.ofRat (1/4)) :=
  normalize_value (equiv_of_close quarterIntegral_valid (RealRaw.ofRat_valid _)
    sumSample (fun _=>1/2) sumSample_mem (rat_mem _) sumSample_via_FTC)

end ComputableAnalysis.SineSquare
