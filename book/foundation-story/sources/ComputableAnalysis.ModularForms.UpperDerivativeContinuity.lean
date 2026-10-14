import ComputableAnalysis.ModularForms.UpperDerivativeContinuityBounds

/-! Effective continuity of the constructed derivative maps. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory DomainFunctions

private theorem rateEventually (e : Nat → Rat) (he : ShrinksToZero e) (eps : QPos) :
    ∃ N, ∀ n, N≤n → decide (e n≤eps.val)=true := by
  obtain ⟨N,hN⟩ := he eps
  exact ⟨N,fun n hn => by simpa using hN n hn⟩

private def rateStage (e : Nat → Rat) (he : ShrinksToZero e) (eps : QPos) : Nat :=
  PrecisionSearch.firstFrom (fun n => decide (e n≤eps.val)) (rateEventually e he eps) 0

private theorem rateStage_spec (e : Nat → Rat) (he : ShrinksToZero e) (eps : QPos) :
    e (rateStage e he eps)≤eps.val := by
  have h := (PrecisionSearch.firstFrom_spec (fun n => decide (e n≤eps.val))
    (rateEventually e he eps) 0).2
  simpa only [rateStage,decide_eq_true_eq] using h

def derivativeWeightFourMap_continuous :
    ContinuousOn derivativeWeightFourMap.domain derivativeWeightFourMap.eval where
  delta a ha eps :=
    let n := rateStage (localDerivativeWeightFourTailRate a ha)
      (localDerivativeWeightFourTailRate_shrinks a ha) (halfError (halfError eps))
    minRadius (upperRadius a ha)
      ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).continuousDerivative.delta
        a ha (halfError eps))
  estimate a ha eps z hz hza := by
    let n := rateStage (localDerivativeWeightFourTailRate a ha)
      (localDerivativeWeightFourTailRate_shrinks a ha) (halfError (halfError eps))
    have hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val :=
      hza.mono (minRadius_left _ _)
    have hf := (upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).continuousDerivative.estimate
      a ha (halfError eps) z hz (hza.mono (minRadius_right _ _))
    have hb := derivativeWeightFourSum_difference_bound a ha z hz hs n (halfError eps).val hf
    apply hb.mono
    have hn := rateStage_spec (localDerivativeWeightFourTailRate a ha)
      (localDerivativeWeightFourTailRate_shrinks a ha) (halfError (halfError eps))
    change localDerivativeWeightFourTailRate a ha n≤(halfError (halfError eps)).val at hn
    have hhalf := halfError_identity eps
    have hquarter := halfError_identity (halfError eps)
    grind only

def derivativeWeightSixMap_continuous :
    ContinuousOn derivativeWeightSixMap.domain derivativeWeightSixMap.eval where
  delta a ha eps :=
    let n := rateStage (localDerivativeWeightSixTailRate a ha)
      (localDerivativeWeightSixTailRate_shrinks a ha) (halfError (halfError eps))
    minRadius (upperRadius a ha)
      ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).continuousDerivative.delta
        a ha (halfError eps))
  estimate a ha eps z hz hza := by
    let n := rateStage (localDerivativeWeightSixTailRate a ha)
      (localDerivativeWeightSixTailRate_shrinks a ha) (halfError (halfError eps))
    have hs : Small (ComplexRaw.sub z.val a.val) (upperRadius a ha).val :=
      hza.mono (minRadius_left _ _)
    have hf := (upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).continuousDerivative.estimate
      a ha (halfError eps) z hz (hza.mono (minRadius_right _ _))
    have hb := derivativeWeightSixSum_difference_bound a ha z hz hs n (halfError eps).val hf
    apply hb.mono
    have hn := rateStage_spec (localDerivativeWeightSixTailRate a ha)
      (localDerivativeWeightSixTailRate_shrinks a ha) (halfError (halfError eps))
    change localDerivativeWeightSixTailRate a ha n≤(halfError (halfError eps)).val at hn
    have hhalf := halfError_identity eps
    have hquarter := halfError_identity (halfError eps)
    grind only

end ComputableAnalysis.ModularForms
