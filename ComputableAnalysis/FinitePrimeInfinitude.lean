import ComputableAnalysis.Basic

/-!
# A computable infinitude-of-primes certificate

For each finite bound, package Euclid's product-plus-one construction as a
finite witness: a certified basic prime strictly above the bound.  This is the
potential-infinity core of Wiedijk benchmark item 11; no completed infinite
set is introduced.
-/

namespace ComputableAnalysis

structure PrimeUnboundednessCertificate (bound : Nat) where
  witness : Nat
  witness_prime : BasicPrime witness
  bound_lt : bound < witness

def primeUnboundednessCertificate (bound witness : Nat)
    (witness_prime : BasicPrime witness) (bound_lt : bound < witness) :
    PrimeUnboundednessCertificate bound :=
  { witness := witness
    witness_prime := witness_prime
    bound_lt := bound_lt }

theorem primeUnboundednessCertificate_exists (bound : Nat) :
    ∃ certificate : PrimeUnboundednessCertificate bound,
      bound < certificate.witness := by
  rcases exists_basicPrime_gt bound with ⟨p, hp, hbound⟩
  exact ⟨primeUnboundednessCertificate bound p hp hbound, hbound⟩

theorem primeUnboundednessCertificate_stage_eight :
    ∃ certificate : PrimeUnboundednessCertificate 8,
      8 < certificate.witness := by
  exact primeUnboundednessCertificate_exists 8

end ComputableAnalysis
