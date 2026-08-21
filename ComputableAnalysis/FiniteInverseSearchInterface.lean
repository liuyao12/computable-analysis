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

theorem FiniteInverseSearchCertificate.output_midpoint_witness
    (certificate : FiniteInverseSearchCertificate) :
    certificate.map certificate.output.lo ≤ certificate.target /\
      certificate.target ≤ certificate.map certificate.output.hi /\
      certificate.output.lo ≤ certificate.output.midpoint /\
      certificate.output.midpoint ≤ certificate.output.hi := by
  have hbracket := certificate.output_bracket
  have hordered := monotoneTargetBisectionIterate_ordered
    (f := certificate.map) (I := certificate.initialInterval)
    certificate.target certificate.ordered certificate.stage
  have hmid := QInterval.midpoint_mem hordered
  exact ⟨hbracket.1, hbracket.2, hmid.1, hmid.2⟩

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
