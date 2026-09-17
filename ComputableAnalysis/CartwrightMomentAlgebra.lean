import ComputableAnalysis.CartwrightEvaluationData
import ComputableAnalysis.RationalSampleLimits

/-! Algebra shared by all analytic routes. The moment recurrence is its input;
the output is the same native interval-program evaluation statement. -/
namespace ComputableAnalysis.CartwrightMoments
open ClosedArctanInverse CartwrightArithmetic RationalSampleLimits FiniteRationalPowers

structure MomentLaws : Prop where
  zero : Close (fun q=>frequencySample q*momentSample 0 q) (fun _=>1)
  first : Small firstSamples
  recurrence : ∀ n, Small (recurrenceSamples n)

theorem frequency_bound : Bounded frequencySample 2 := by
  intro q
  have h:=frequencySample_bounds q
  rw [qabs_eq_self_of_nonneg (by grind : 0≤frequencySample q)]
  exact h.2

theorem frequencySquare_bound : Bounded (fun q=>frequencySample q*frequencySample q) 4 := by
  have h:=bounded_mul (by decide : (0:Rat)≤2) frequency_bound frequency_bound
  have he : (2:Rat)*2=4 := by decide +kernel
  rw [he] at h
  exact h

theorem scaled_zero_close (h : MomentLaws) : Close (scaledSample 0) (fun _=>1) := by
  have he : scaledSample 0=(fun q=>frequencySample q*momentSample 0 q) := by
    funext q
    simp only [scaledSample,show 2*0+1=1 by decide,Rat.pow_succ,Rat.pow_zero,Rat.one_mul]
  rw [he]
  exact h.zero

theorem scaled_one_close (h : MomentLaws) : Close (scaledSample 1) (fun _=>2) := by
  have h1:=small_bounded_mul (by decide : (0:Rat)≤2) frequency_bound h.first
  have h2:=small_bounded_mul (qabs_nonneg (2:Rat)) (bounded_const 2) h.zero
  have hh:=small_add h1 h2
  have he : (fun q=>frequencySample q*firstSamples q+2*(frequencySample q*momentSample 0 q-1))=
      (fun q=>scaledSample 1 q-2) := by
    funext q
    unfold firstSamples scaledSample
    simp only [show 2*1+1=3 by decide,Rat.pow_succ,Rat.pow_zero]
    grind only
  rw [he] at hh
  exact hh

theorem scaled_recurrence_close (h : MomentLaws) (n : Nat) :
    Close (scaledSample (n+2)) (fun q=>recurrenceA n*scaledSample (n+1) q-
      recurrenceB n*(frequencySample q*frequencySample q)*scaledSample n q) := by
  have hh:=small_bounded_mul (pow_nonneg (by decide : (0:Rat)≤2) (2*n+3))
    (bounded_power (by decide) frequency_bound (2*n+3)) (h.recurrence n)
  have he : (fun q=>frequencySample q^(2*n+3)*recurrenceSamples n q)=
      (fun q=>scaledSample (n+2) q-(recurrenceA n*scaledSample (n+1) q-
        recurrenceB n*(frequencySample q*frequencySample q)*scaledSample n q)) := by
    funext q
    unfold recurrenceSamples scaledSample
    rw [show 2*n+3=(2*n+1)+2 by omega,
      show 2*(n+2)+1=(2*n+1)+4 by omega,show 2*(n+1)+1=(2*n+1)+2 by omega]
    simp only [pow_add,Rat.pow_succ,Rat.pow_zero]
    grind only
  rw [he] at hh
  exact hh

/-- The recurrence determines all evaluations by finite induction. This
lemma is shared; analytic alternatives differ only in how they prove the laws. -/
theorem evaluation_close_pair (h : MomentLaws) (n : Nat) :
    Close (scaledSample n) (fun q=>normalizer n*(polynomialPair (frequencySample q*frequencySample q) n).1) ∧
    Close (scaledSample (n+1)) (fun q=>normalizer (n+1)*(polynomialPair (frequencySample q*frequencySample q) n).2) := by
  induction n with
  | zero =>
    constructor
    · simpa only [polynomialPair,normalizer_zero,Rat.one_mul] using scaled_zero_close h
    · have he : normalizer 1=(2:Rat) := by decide +kernel
      simpa only [polynomialPair,he,Rat.mul_one] using scaled_one_close h
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    have h1:=close_scale (recurrenceA n) ih.2
    have h2:=close_scale (recurrenceB n) (close_bounded_mul ih.1 (by decide : (0:Rat)≤4) frequencySquare_bound)
    have ht:=close_sub h1 h2
    have hr:=scaled_recurrence_close h n
    have hmiddle : (fun q=>recurrenceA n*scaledSample (n+1) q-
        recurrenceB n*(frequencySample q*frequencySample q)*scaledSample n q)=
      (fun q=>recurrenceA n*scaledSample (n+1) q-
        recurrenceB n*((frequencySample q*frequencySample q)*scaledSample n q)) := by funext q;grind
    rw [hmiddle] at hr
    have hh:=close_trans hr ht
    have hnorm : normalizer (n+2)=4*((n+2:Nat):Rat)*((n+1:Nat):Rat)*normalizer n := by
      rw [show n+2=(n+1)+1 by omega,normalizer_step,normalizer_step]
      simp only [Rat.natCast_add,Rat.natCast_ofNat]
      grind only
    have he : (fun q=>recurrenceA n*(normalizer (n+1)*(polynomialPair (frequencySample q*frequencySample q) n).2)-
        recurrenceB n*((frequencySample q*frequencySample q)*(normalizer n*(polynomialPair (frequencySample q*frequencySample q) n).1)))=
      (fun q=>normalizer ((n+1)+1)*(polynomialPair (frequencySample q*frequencySample q) (n+1)).2) := by
      funext q
      change recurrenceA n*(normalizer (n+1)*(polynomialPair (frequencySample q*frequencySample q) n).2)-
        recurrenceB n*((frequencySample q*frequencySample q)*(normalizer n*(polynomialPair (frequencySample q*frequencySample q) n).1))=
        normalizer (n+2)*((2*(n:Rat)+3)*(polynomialPair (frequencySample q*frequencySample q) n).2-
          (frequencySample q*frequencySample q)*(polynomialPair (frequencySample q*frequencySample q) n).1)
      rw [hnorm,normalizer_step]
      unfold recurrenceA recurrenceB
      simp only [Rat.natCast_add,Rat.natCast_ofNat]
      grind only
    rw [he] at hh
    exact hh

theorem evaluation_close (h : MomentLaws) (n : Nat) : Close (scaledSample n) (endpointSample n) :=
  (evaluation_close_pair h n).1

/-- Each analytic route proves this very same proposition. -/
theorem evaluation_of_laws (h : MomentLaws) (n : Nat) : EvaluationStatement n :=
  equiv_of_close (scaledMoment_valid n) (polynomialEndpoint_valid n)
    (scaledSample n) (endpointSample n) (scaledSample_mem n) (endpointSample_mem n) (evaluation_close h n)

end ComputableAnalysis.CartwrightMoments
