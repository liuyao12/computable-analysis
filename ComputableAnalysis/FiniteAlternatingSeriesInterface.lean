import ComputableAnalysis.Series

/-!
# Reusable finite alternating-series interface

An alternating series is represented by nonnegative decreasing rational term
magnitudes.  The certificate exposes the finite interval between consecutive
partial sums and its explicit width; no completed sum is part of the object.
-/

namespace ComputableAnalysis
namespace Series

structure FiniteAlternatingSeriesCertificate where
  term : Nat → Rat
  stage : Nat
  term_nonneg : ∀ n, 0 ≤ term n
  term_decreasing : ∀ n, term (n + 1) ≤ term n
  intervalValue : QInterval
  interval_eq : intervalValue = alternatingInterval term stage

theorem FiniteAlternatingSeriesCertificate.width_eq
    (certificate : FiniteAlternatingSeriesCertificate) :
    certificate.intervalValue.width =
      certificate.term (2 * certificate.stage) := by
  rw [certificate.interval_eq]
  unfold alternatingInterval evenOddInterval intervalBetween
  rw [partialSum_even_succ]
  have hnonneg := certificate.term_nonneg (2 * certificate.stage)
  have hsum : partialSum certificate.term (2 * certificate.stage) ≤
      partialSum certificate.term (2 * certificate.stage) +
        certificate.term (2 * certificate.stage) := by
    grind
  simp [hsum, QInterval.width]
  grind [Rat.sub_eq_add_neg]

def finiteAlternatingSeriesCertificate
    (term : Nat → Rat) (stage : Nat)
    (term_nonneg : ∀ n, 0 ≤ term n)
    (term_decreasing : ∀ n, term (n + 1) ≤ term n) :
    FiniteAlternatingSeriesCertificate where
  term := term
  stage := stage
  term_nonneg := term_nonneg
  term_decreasing := term_decreasing
  intervalValue := alternatingInterval term stage
  interval_eq := rfl

end Series
end ComputableAnalysis
