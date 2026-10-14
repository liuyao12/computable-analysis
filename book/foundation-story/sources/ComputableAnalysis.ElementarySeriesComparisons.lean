import ComputableAnalysis.ElementarySeriesCoefficients
import ComputableAnalysis.ModularForms.ExponentialConjugatePrefixes

/-! The real-axis sine/cosine series agree with rotation coordinates. The
comparison uses the same finite prefixes and their conjugates. -/
namespace ComputableAnalysis.ElementaryPowerSeries
open ComplexRaw ComplexExponentialApproximation ModularForms
set_option maxHeartbeats 1000000

theorem imaginaryInput (x : Rat) : QComplex.mul ElementaryRational.imaginaryUnit ⟨x,0⟩ = ⟨0,x⟩ := by
  simp [ElementaryRational.imaginaryUnit,QComplex.mul,Rat.sub_eq_add_neg,
    Rat.add_zero,Rat.zero_add,Rat.neg_zero]

theorem imaginaryPrefix_pair (x : Rat) (n : Nat) :
    pairPrefix true ⟨0,x⟩ n = ⟨0,(expPrefix ⟨0,x⟩ n).im⟩ ∧
    pairPrefix false ⟨0,x⟩ n = ⟨(expPrefix ⟨0,x⟩ n).re,0⟩ := by
  have he : QComplex.neg (⟨0,x⟩ : QComplex) = QComplex.conj ⟨0,x⟩ := by
    simp [QComplex.neg,QComplex.conj]
  unfold pairPrefix pair
  rw [he,←rationalExp_prefix_conjugate]
  simp only [if_true,Bool.false_eq_true,if_false,QComplex.scaleRat,QComplex.sub,
    QComplex.add,QComplex.neg,QComplex.conj]
  constructor <;> congr 1 <;> grind only

theorem sineValue_realAxis_agrees (x : Rat) :
    (sineValue ⟨x,0⟩).realPart.Equiv (ElementaryRational.exponentialValue ⟨0,x⟩).imagPart := by
  intro n
  have hs := cauchyStabilize_contains_current
    (pairCandidate_future (QComplex.normBound_nonneg (⟨0,x⟩ : QComplex)) Rat.le_refl true) n
  change (QBox.point (pairPrefix true ⟨0,x⟩ (RationalMajorant.factorialTailStart (QComplex.normBound ⟨0,x⟩)+n))).NestedIn
    ((pairSeries true ⟨0,x⟩).compute n) at hs
  rw [(imaginaryPrefix_pair x _).1] at hs
  have he := exponentialRaw_contains_future_prefix (QComplex.normBound_nonneg (⟨0,x⟩ : QComplex))
    (z := ⟨0,x⟩) Rat.le_refl (Nat.le_refl n)
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  unfold sineValue
  rw [imaginaryInput]
  simp only [realPart,mulI,neg,QBox.neg,Rat.neg_neg]
  exact ⟨Rat.le_trans hs.1.2 he.2.2,Rat.le_trans he.1.2 hs.2.2⟩

theorem cosineValue_realAxis_agrees (x : Rat) :
    (cosineValue ⟨x,0⟩).realPart.Equiv (ElementaryRational.exponentialValue ⟨0,x⟩).realPart := by
  intro n
  have hs := cauchyStabilize_contains_current
    (pairCandidate_future (QComplex.normBound_nonneg (⟨0,x⟩ : QComplex)) Rat.le_refl false) n
  change (QBox.point (pairPrefix false ⟨0,x⟩ (RationalMajorant.factorialTailStart (QComplex.normBound ⟨0,x⟩)+n))).NestedIn
    ((pairSeries false ⟨0,x⟩).compute n) at hs
  rw [(imaginaryPrefix_pair x _).2] at hs
  have he := exponentialRaw_contains_future_prefix (QComplex.normBound_nonneg (⟨0,x⟩ : QComplex))
    (z := ⟨0,x⟩) Rat.le_refl (Nat.le_refl n)
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  unfold cosineValue
  rw [imaginaryInput]
  exact ⟨Rat.le_trans hs.1.1 he.2.1,Rat.le_trans he.1.1 hs.2.1⟩

theorem sine_realAxis_agrees :
    sine.realPartOnRealAxis.AgreeOnOverlap ElementaryRational.sineRadianRotation :=
  fun x _ _ => sineValue_realAxis_agrees x

theorem cosine_realAxis_agrees :
    cosine.realPartOnRealAxis.AgreeOnOverlap ElementaryRational.cosineRadianRotation :=
  fun x _ _ => cosineValue_realAxis_agrees x

end ComputableAnalysis.ElementaryPowerSeries
