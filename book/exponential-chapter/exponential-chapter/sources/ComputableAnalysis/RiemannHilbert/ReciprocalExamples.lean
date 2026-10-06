import ComputableAnalysis.RiemannHilbert.SphereChartIsomorphisms
import ComputableAnalysis.RiemannHilbert.AnalyticExamples

/-! Exact comparison with rational arithmetic and a different, non-singleton
input representation. Runtime examples exercise the actual reciprocal and
sphere chart evaluators. -/
namespace ComputableAnalysis.RiemannHilbert.ReciprocalExamples
open ComplexRaw FunctionTheory NonzeroBoxSearch RepresentedReciprocal SphereCoordinates

def rational (c : QComplex) : Scalar := ⟨ofQComplex c, ofQComplex_valid c⟩

theorem rational_product (c : QComplex) (hc : QComplex.normSq c ≠ 0) :
    (mul (rational c).val (rational (RationalReciprocal.inverse c)).val).Equiv
      (ofQComplex QComplex.one) := by
  have h := RationalReciprocal.raw_mul_constants c (RationalReciprocal.inverse c)
  rw [RationalReciprocal.mul_inverse c hc] at h
  exact h

theorem rational_nonzero (c : QComplex) (hc : QComplex.normSq c ≠ 0) : Nonzero (rational c) :=
  nonzero_of_inverse _ _ (rational_product c hc)

theorem rational_inverse (c : QComplex) (hc : QComplex.normSq c ≠ 0) :
    (inverse (rational c) (rational_nonzero c hc)).val.Equiv
      (ofQComplex (RationalReciprocal.inverse c)) :=
  inverse_unique _ _ _ (rational_product c hc)

def sampleInput : Scalar := rational ⟨2,1⟩

theorem sample_nonzero : Nonzero sampleInput :=
  rational_nonzero ⟨2,1⟩ (by decide +kernel)

def sampleInverse : Scalar := inverse sampleInput sample_nonzero

theorem sampleInverse_value : sampleInverse.val.Equiv (ofQComplex ⟨2/5,-1/5⟩) := by
  have h := rational_inverse ⟨2,1⟩ (by decide +kernel)
  have hc : RationalReciprocal.inverse ⟨2,1⟩ = ⟨2/5,-1/5⟩ := by decide +kernel
  rw [hc] at h
  exact h

def sampleRenamed : Scalar :=
  ⟨mul AnalyticExamples.noisyOne.val sampleInput.val,
    mul_valid AnalyticExamples.noisyOne.property sampleInput.property⟩

theorem sampleRenamed_value : sampleRenamed.val.Equiv sampleInput.val :=
  equiv_trans sampleRenamed.property (mul_valid (ofQComplex_valid _) sampleInput.property) sampleInput.property
    (mul_equiv AnalyticExamples.noisyOne.property (ofQComplex_valid _) sampleInput.property sampleInput.property
      AnalyticExamples.noisyOne_equiv (equiv_refl _ sampleInput.property))
    (one_mul_equiv _ sampleInput.property)

theorem sampleRenamed_nonzero : Nonzero sampleRenamed :=
  (nonzero_congr sampleRenamed sampleInput sampleRenamed_value).2 sample_nonzero

theorem sampleRenamed_inverse :
    (inverse sampleRenamed sampleRenamed_nonzero).val.Equiv (ofQComplex ⟨2/5,-1/5⟩) :=
  equiv_trans (inverse sampleRenamed sampleRenamed_nonzero).property sampleInverse.property (ofQComplex_valid _)
    (inverse_congr sampleRenamed sampleInput sampleRenamed_nonzero sample_nonzero sampleRenamed_value)
    sampleInverse_value

theorem enclosedRational_future (c : QComplex) (k n : Nat) (_hkn : k ≤ n) :
    ((ofQComplex c).compute n).NestedIn
      (QBox.expand ((ofQComplex c).compute k) (RepresentedCauchySum.error k).val) := by
  have hp := (RepresentedCauchySum.error k).property
  change (c.re-(RepresentedCauchySum.error k).val ≤ c.re ∧
    c.im-(RepresentedCauchySum.error k).val ≤ c.im) ∧
    (c.re ≤ c.re+(RepresentedCauchySum.error k).val ∧ c.im ≤ c.im+(RepresentedCauchySum.error k).val)
  grind

def enclosedRational (c : QComplex) : Scalar :=
  ⟨cauchyStabilize (ofQComplex c) (fun n => (RepresentedCauchySum.error n).val),
    cauchyStabilize_valid (fun n => valid_ordered (ofQComplex_valid c) n)
      (ofQComplex_valid c).2.2 (enclosedRational_future c) RepresentedCauchySum.error_shrinks⟩

theorem enclosedRational_value (c : QComplex) : (enclosedRational c).val.Equiv (ofQComplex c) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).2
  have hn := cauchyStabilize_contains_current (enclosedRational_future c) n
  exact hn

def sampleEnclosed : Scalar := enclosedRational ⟨2,1⟩

theorem sampleEnclosed_nonzero : Nonzero sampleEnclosed :=
  (nonzero_congr sampleEnclosed sampleInput (enclosedRational_value ⟨2,1⟩)).2 sample_nonzero

theorem sampleEnclosed_inverse :
    (inverse sampleEnclosed sampleEnclosed_nonzero).val.Equiv (ofQComplex ⟨2/5,-1/5⟩) :=
  equiv_trans (inverse sampleEnclosed sampleEnclosed_nonzero).property sampleInverse.property (ofQComplex_valid _)
    (inverse_congr sampleEnclosed sampleInput sampleEnclosed_nonzero sample_nonzero (enclosedRational_value ⟨2,1⟩))
    sampleInverse_value

def samplePoint : Name := .finite sampleInput
def sampleOtherName : Name := .infinity sampleInverse

theorem samplePoint_agreement : samplePoint ≈ sampleOtherName := mul_inverse sampleInput sample_nonzero

theorem sampleOtherName_mem : finiteDomain sampleOtherName := inverse_nonzero sampleInput sample_nonzero

theorem sampleCoordinate_recovered :
    (finiteCoordinate sampleOtherName sampleOtherName_mem).val.Equiv sampleInput.val :=
  involutive sampleInput sample_nonzero

theorem sample_derivative :
    (ReciprocalDifference.derivative sampleInput sample_nonzero).val.Equiv
      (neg (mul (ofQComplex ⟨2/5,-1/5⟩) (ofQComplex ⟨2/5,-1/5⟩))) :=
  neg_equiv (mul_equiv sampleInverse.property (ofQComplex_valid _) sampleInverse.property (ofQComplex_valid _)
    sampleInverse_value sampleInverse_value)

end ComputableAnalysis.RiemannHilbert.ReciprocalExamples
