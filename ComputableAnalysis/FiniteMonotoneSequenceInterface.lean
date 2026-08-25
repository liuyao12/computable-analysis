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

/-! Turn the endpoint certificate directly into the project's raw-real data.
The construction is deliberately just the two rational endpoints at each
stage; no supremum, completeness axiom, or standard `Real` is involved. -/
def MonotoneIntervalCertificate.toRealRaw
    (certificate : MonotoneIntervalCertificate) : RealRaw where
  compute := fun n =>
    { lo := certificate.loStage n
      hi := certificate.hiStage n }

theorem MonotoneIntervalCertificate.toRealRaw_valid
    (certificate : MonotoneIntervalCertificate) :
    certificate.toRealRaw.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 ≤ certificate.hiStage n - certificate.loStage n
    grind [certificate.enclosed n]
  · intro n m hnm
    change certificate.loStage n ≤ certificate.loStage m /\
      certificate.loStage m ≤ certificate.hiStage m /\
      certificate.hiStage m ≤ certificate.hiStage n
    exact ⟨certificate.lower_pair_le hnm,
      certificate.enclosed m,
      certificate.upper_pair_ge hnm⟩
  · intro eps
    obtain ⟨N, hN⟩ := certificate.width_shrinks eps
    refine ⟨N, ?_⟩
    intro n hn
    change certificate.hiStage n - certificate.loStage n ≤ eps.val
    exact hN n hn

/- The abstract handle is only a certified wrapper around the finite endpoint
   computation.  No new existence principle is introduced at this boundary. -/
def MonotoneIntervalCertificate.toReal
    (certificate : MonotoneIntervalCertificate) : Real :=
  Real.ofRaw certificate.toRealRaw certificate.toRealRaw_valid

theorem MonotoneIntervalCertificate.toReal_preferred_compute
    (certificate : MonotoneIntervalCertificate) (n : Nat) :
    certificate.toReal.compute n =
      { lo := certificate.loStage n, hi := certificate.hiStage n } := by
  rfl

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
