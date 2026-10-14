import ComputableAnalysis.ExponentialComputations.LipschitzIntegral

/-! An executable integral evaluator from justified finite rectangle bounds.
The mathematical witness is used only in proofs; runtime reads finite sums. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert
set_option maxHeartbeats 1000000

private def rectangleTolerance (n : Nat) : QPos :=
  ⟨(1/2:Rat)^n,Rat.pow_pos (by decide +kernel)⟩

def rectangleCandidate (f : FunctionOnInterval) (B : QPos → Integral.Bounds f) : RealRaw where
  compute n := {lo := (B (rectangleTolerance n)).lowerSum,hi := (B (rectangleTolerance n)).upperSum}

/-- Intersect the finite sum boxes. This computation does not read the
endpoint expression used later to justify it. -/
def rectangleValue (f : FunctionOnInterval) (B : QPos → Integral.Bounds f) : RealRaw :=
  RealRaw.prefixStabilize (rectangleCandidate f B) (fun _ => 0)

private theorem rectangleValue_bounds (f : FunctionOnInterval) (B : QPos → Integral.Bounds f)
    (I : RealRaw) (hI : Integral.HasIntegral f I) :
    ∀ k n, ((rectangleValue f B).compute k).lo ≤ (I.compute n).hi ∧
      (I.compute n).lo ≤ ((rectangleValue f B).compute k).hi := by
  intro k
  induction k with
  | zero =>
    intro n
    simpa only [rectangleValue,RealRaw.prefixStabilize,RealRaw.prefixStabilizeCompute,
      rectangleCandidate,QInterval.expand,Rat.sub_self,Rat.sub_eq_add_neg,Rat.add_zero,Rat.neg_zero] using
      hI.bounds (B (rectangleTolerance 0)) n
  | succ k ih =>
    intro n
    have h := hI.bounds (B (rectangleTolerance (k+1))) n
    have hp := ih n
    change maxRat2 _ _ ≤ (I.compute n).hi ∧ (I.compute n).lo ≤ minRat _ _
    simp only [rectangleCandidate,QInterval.expand,Rat.sub_eq_add_neg,Rat.add_zero,Rat.neg_zero]
    unfold maxRat2 minRat
    split <;> split <;> constructor <;> first | exact h.1 | exact h.2 | exact hp.1 | exact hp.2

theorem rectangleValue_valid (f : FunctionOnInterval) (B : QPos → Integral.Bounds f)
    (hgap : ∀ eps, (B eps).upperSum-(B eps).lowerSum ≤ eps.val)
    (I : RealRaw) (hI : Integral.HasIntegral f I) : (rectangleValue f B).Valid := by
  have ho (k : Nat) : ((rectangleValue f B).compute k).lo ≤ ((rectangleValue f B).compute k).hi := by
    have hl : (RealRaw.ofRat ((rectangleValue f B).compute k).lo).Le I := fun _ n => (rectangleValue_bounds f B I hI k n).1
    have hr : I.Le (RealRaw.ofRat ((rectangleValue f B).compute k).hi) := fun n _ => (rectangleValue_bounds f B I hI k n).2
    exact RealRaw.le_trans hI.valid hl hr 0 0
  refine ⟨?_,?_,?_⟩
  · intro n; have h := ho n; change 0≤ _-_; grind only
  · intro n m hnm
    induction hnm with
    | refl => exact ⟨Rat.le_refl,ho n,Rat.le_refl⟩
    | step hnm ih =>
      rename_i k
      have hh := QInterval.intersection_contained_left
        ((rectangleValue f B).compute k)
        (QInterval.expand ((rectangleCandidate f B).compute (k+1)) 0)
      exact ⟨Rat.le_trans ih.1 hh.1,ho (k+1),Rat.le_trans hh.2 ih.2.2⟩
  · intro eps
    let N := RationalMajorant.halfDecayShift 1 eps
    refine ⟨N,fun n hn => ?_⟩
    have h := RealRaw.prefixStabilize_contained_in_current_expand
      (rectangleCandidate f B) (fun _ => 0) n
    have hw := QInterval.width_le_of_contains h
    have hg := hgap (rectangleTolerance n)
    have hb := RationalMajorant.halfDecayShift_spec_of_le (bound := 1) (by decide +kernel) eps hn
    change (1:Rat)*(1/2)^n≤eps.val at hb
    change (B (rectangleTolerance n)).upperSum-(B (rectangleTolerance n)).lowerSum≤(1/2:Rat)^n at hg
    simp only [QInterval.expand_width,Rat.mul_zero,Rat.add_zero] at hw
    change ((rectangleValue f B).compute n).width ≤ _ at hw ⊢
    change ((rectangleCandidate f B).compute n).width ≤ (1/2:Rat)^n at hg
    exact Rat.le_trans hw (Rat.le_trans hg (by simpa only [Rat.one_mul] using hb))

theorem rectangleValue_agrees (f : FunctionOnInterval) (B : QPos → Integral.Bounds f)
    (I : RealRaw) (hI : Integral.HasIntegral f I) : (rectangleValue f B).Equiv I := by
  intro n
  exact (RealRaw.compareAt_overlap_iff _ _ n n).mpr (rectangleValue_bounds f B I hI n n)

theorem rectangleValue_hasIntegral (f : FunctionOnInterval) (B : QPos → Integral.Bounds f)
    (hgap : ∀ eps, (B eps).upperSum-(B eps).lowerSum ≤ eps.val)
    (I : RealRaw) (hI : Integral.HasIntegral f I) : Integral.HasIntegral f (rectangleValue f B) :=
  hI.congr (rectangleValue_valid f B hgap I hI) (RealRaw.equiv_symm (rectangleValue_agrees f B I hI))
end ComputableAnalysis.ExponentialComputations
