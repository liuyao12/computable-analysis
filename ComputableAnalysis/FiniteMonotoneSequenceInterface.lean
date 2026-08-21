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

/-! A bounded monotone computation is represented by two rational stage
endpoints.  The lower endpoint moves upward, the upper endpoint moves
downward, and a supplied modulus says when their gap is small.  This is the
computable replacement for invoking a supremum of a monotone bounded
sequence. -/
structure MonotoneIntervalCertificate where
  loStage : Nat → Rat
  hiStage : Nat → Rat
  lower_succ : ∀ n, loStage n ≤ loStage (n + 1)
  upper_succ : ∀ n, hiStage (n + 1) ≤ hiStage n
  enclosed : ∀ n, loStage n ≤ hiStage n
  width_shrinks : ∀ eps : QPos, ∃ N : Nat,
    ∀ n, N ≤ n -> hiStage n - loStage n ≤ eps.val

theorem MonotoneIntervalCertificate.lower_pair_le
    (certificate : MonotoneIntervalCertificate)
    {a b : Nat} (hab : a ≤ b) :
    certificate.loStage a ≤ certificate.loStage b := by
  exact monotone_of_succ_le certificate.lower_succ hab

theorem MonotoneIntervalCertificate.upper_pair_ge
    (certificate : MonotoneIntervalCertificate)
    {a b : Nat} (hab : a ≤ b) :
    certificate.hiStage b ≤ certificate.hiStage a := by
  exact antitone_of_succ_ge certificate.upper_succ hab

/-! A finite readout of the bounded monotone computation: at a sufficiently
late stage, the midpoint is an explicit rational representative whose whole
stage interval has the requested width. -/
theorem MonotoneIntervalCertificate.precision_witness
    (certificate : MonotoneIntervalCertificate) (eps : QPos) :
    ∃ N : Nat, ∃ q : Rat,
      certificate.loStage N ≤ q /\
        q ≤ certificate.hiStage N /\
        certificate.hiStage N - certificate.loStage N ≤ eps.val := by
  obtain ⟨N, hN⟩ := certificate.width_shrinks eps
  refine ⟨N, (certificate.loStage N + certificate.hiStage N) / 2, ?_⟩
  have hordered := certificate.enclosed N
  constructor
  · grind
  constructor
  · grind
  · exact hN N (Nat.le_refl N)

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
