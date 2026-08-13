import ComputableAnalysis.FiniteMonotoneSequenceExample

/-!
# Reusable finite monotone-sequence interface

Monotonicity is represented by a successor certificate.  The global finite
order relation is then obtained by induction; no supremum or completed limit
is part of the interface.
-/

namespace ComputableAnalysis

structure FiniteAscendingSequenceCertificate where
  sequence : Nat → Rat
  stage : Nat
  successor_le : ∀ n, sequence n ≤ sequence (n + 1)

theorem FiniteAscendingSequenceCertificate.pair_le
    (certificate : FiniteAscendingSequenceCertificate)
    {a b : Nat} (hab : a ≤ b) :
    certificate.sequence a ≤ certificate.sequence b := by
  exact monotone_of_succ_le certificate.successor_le hab

structure FiniteDescendingSequenceCertificate where
  sequence : Nat → Rat
  stage : Nat
  successor_ge : ∀ n, sequence (n + 1) ≤ sequence n

theorem FiniteDescendingSequenceCertificate.pair_le
    (certificate : FiniteDescendingSequenceCertificate)
    {a b : Nat} (hab : a ≤ b) :
    certificate.sequence b ≤ certificate.sequence a := by
  exact antitone_of_succ_ge certificate.successor_ge hab

def finiteAscendingSequenceCertificate
    (sequence : Nat → Rat) (stage : Nat)
    (successor_le : ∀ n, sequence n ≤ sequence (n + 1)) :
    FiniteAscendingSequenceCertificate where
  sequence := sequence
  stage := stage
  successor_le := successor_le

def finiteDescendingSequenceCertificate
    (sequence : Nat → Rat) (stage : Nat)
    (successor_ge : ∀ n, sequence (n + 1) ≤ sequence n) :
    FiniteDescendingSequenceCertificate where
  sequence := sequence
  stage := stage
  successor_ge := successor_ge

end ComputableAnalysis
