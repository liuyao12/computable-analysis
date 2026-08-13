import ComputableAnalysis.FiniteBisectionIteration

/-!
# Reusable finite inverse-search interface

An inverse is represented by a finite target bracket.  A monotone rational
map, an input interval, and endpoint inequalities determine a bisection
computation whose output interval contains the requested target preimage.
-/

namespace ComputableAnalysis

structure FiniteInverseSearchCertificate where
  map : Rat → Rat
  target : Rat
  initialInterval : QInterval
  stage : Nat
  ordered : initialInterval.lo ≤ initialInterval.hi
  lower_bracket : map initialInterval.lo ≤ target
  upper_bracket : target ≤ map initialInterval.hi

def FiniteInverseSearchCertificate.output
    (certificate : FiniteInverseSearchCertificate) : QInterval :=
  monotoneTargetBisectionIterate certificate.map certificate.target
    certificate.stage certificate.initialInterval

theorem FiniteInverseSearchCertificate.output_bracket
    (certificate : FiniteInverseSearchCertificate) :
    certificate.map certificate.output.lo ≤ certificate.target /\
      certificate.target ≤ certificate.map certificate.output.hi := by
  exact monotoneBisectionIterate_preserves_target_bracket
    certificate.target certificate.ordered certificate.lower_bracket
    certificate.upper_bracket certificate.stage

theorem FiniteInverseSearchCertificate.output_width
    (certificate : FiniteInverseSearchCertificate) :
    certificate.output.width =
      certificate.initialInterval.width /
        (2 ^ certificate.stage : Rat) := by
  exact monotoneTargetBisectionIterate_width certificate.target certificate.stage

def finiteInverseSearchCertificate
    (map : Rat → Rat) (target : Rat) (initialInterval : QInterval)
    (stage : Nat) (ordered : initialInterval.lo ≤ initialInterval.hi)
    (lower_bracket : map initialInterval.lo ≤ target)
    (upper_bracket : target ≤ map initialInterval.hi) :
    FiniteInverseSearchCertificate where
  map := map
  target := target
  initialInterval := initialInterval
  stage := stage
  ordered := ordered
  lower_bracket := lower_bracket
  upper_bracket := upper_bracket

end ComputableAnalysis
