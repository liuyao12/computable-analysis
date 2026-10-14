import ComputableAnalysis.ModularForms.PairedSquareContourLimitInvariance

/-! Parameter reversal preserves midpoint averages, by swapping the two
subtrees. This accounts for reversed lower-half-edge sample order. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def reverseInterval (I : QInterval) : QInterval := ⟨1-I.hi,1-I.lo⟩

theorem reverseInterval_midpoint (I : QInterval) :
    (reverseInterval I).midpoint=1-I.midpoint := by
  unfold reverseInterval QInterval.midpoint
  grind only

theorem reverseInterval_bisect (I : QInterval) (r : Bool) :
    reverseInterval (bisectInterval I r)=bisectInterval (reverseInterval I) (!r) := by
  cases r <;> simp [reverseInterval,bisectInterval,QInterval.midpoint]
  all_goals congr 1 <;> grind only

theorem dyadicSampleAverage_reversal (f : Rat → Scalar) (I : QInterval) (n : Nat) :
    (dyadicSampleAverage (fun u => f (1-u)) I n).val.Equiv
      (dyadicSampleAverage f (reverseInterval I) n).val := by
  induction n generalizing I with
  | zero =>
    change (f (1-I.midpoint)).val.Equiv (f (reverseInterval I).midpoint).val
    rw [reverseInterval_midpoint]
    exact equiv_refl _ (f (1-I.midpoint)).property
  | succ n ih =>
    have hl := ih (bisectInterval I false)
    have hr := ih (bisectInterval I true)
    rw [reverseInterval_bisect] at hl hr
    have hs := ComplexRaw.scaleRat_equiv_of_nonneg (by decide +kernel : (0:Rat)≤1/2)
      (add_equiv hl hr)
    have hc : (scaleRat (1/2)
        (add (dyadicSampleAverage f (bisectInterval (reverseInterval I) true) n).val
          (dyadicSampleAverage f (bisectInterval (reverseInterval I) false) n).val)).Equiv
        (dyadicSampleAverage f (reverseInterval I) (n+1)).val := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := scaleRat_valid (add_valid
          (dyadicSampleAverage f (bisectInterval (reverseInterval I) true) n).property
          (dyadicSampleAverage f (bisectInterval (reverseInterval I) false) n).property))
        (hright := (dyadicSampleAverage f (reverseInterval I) (n+1)).property)
      let L := ComplexRawQuotient.ofRaw
        (dyadicSampleAverage f (bisectInterval (reverseInterval I) false) n).val
        (dyadicSampleAverage f (bisectInterval (reverseInterval I) false) n).property
      let R := ComplexRawQuotient.ofRaw
        (dyadicSampleAverage f (bisectInterval (reverseInterval I) true) n).val
        (dyadicSampleAverage f (bisectInterval (reverseInterval I) true) n).property
      change ComplexRawQuotient.scaleRat (1/2) (R+L)=ComplexRawQuotient.scaleRat (1/2) (L+R)
      congr 1
      grind only
    exact equiv_trans (dyadicSampleAverage (fun u => f (1-u)) I (n+1)).property
      (scaleRat_valid (add_valid
        (dyadicSampleAverage f (bisectInterval (reverseInterval I) true) n).property
        (dyadicSampleAverage f (bisectInterval (reverseInterval I) false) n).property))
      (dyadicSampleAverage f (reverseInterval I) (n+1)).property hs hc

end ComputableAnalysis.ModularForms
