import ComputableAnalysis.Basic

/-!
# Reusable finite prime-interval interface

The computable core of a Bertrand-style claim is an explicit prime witness in
a finite interval.  The unrestricted theorem is not inferred from a finite
table of witnesses.
-/

namespace ComputableAnalysis

structure FinitePrimeIntervalCertificate where
  lowerBound : Nat
  upperBound : Nat
  witness : Nat
  witness_prime : BasicPrime witness
  lower_lt : lowerBound < witness
  witness_lt : witness < upperBound

theorem FinitePrimeIntervalCertificate.in_interval
    (certificate : FinitePrimeIntervalCertificate) :
    certificate.lowerBound < certificate.witness /\
      certificate.witness < certificate.upperBound :=
  ⟨certificate.lower_lt, certificate.witness_lt⟩

def finitePrimeIntervalCertificate
    (lowerBound upperBound witness : Nat)
    (witness_prime : BasicPrime witness)
    (lower_lt : lowerBound < witness)
    (witness_lt : witness < upperBound) :
    FinitePrimeIntervalCertificate where
  lowerBound := lowerBound
  upperBound := upperBound
  witness := witness
  witness_prime := witness_prime
  lower_lt := lower_lt
  witness_lt := witness_lt

end ComputableAnalysis
