import ComputableAnalysis.ComplexInterval

namespace ComputableAnalysis

namespace QBox

/-!
# Finite FTA root-exclusion certificates

This is the finite covering layer above complex-box polynomial evaluation.  A
certificate supplies a rational domain, a finite list of subboxes covering it,
and a proof that every subbox's polynomial image misses zero.  It proves root
exclusion on the supplied domain, without invoking compactness or a global FTA.
-/

structure FiniteRootExclusionCertificate (coeffs : CPoly.Coeffs) where
  domain : QBox
  boxes : List QBox
  cover : ∀ z : QComplex,
    domain.lo <= z → z <= domain.hi →
      ∃ Z, Z ∈ boxes ∧ Z.lo <= z ∧ z <= Z.hi
  misses_zero : ∀ Z, Z ∈ boxes → ¬ QBox.Overlaps (evalPoly coeffs Z) QBox.zero

/-- Every point in the supplied covered domain is excluded as a root. -/
theorem FiniteRootExclusionCertificate.no_root_in_domain
    {coeffs : CPoly.Coeffs}
    (certificate : FiniteRootExclusionCertificate coeffs)
    {z : QComplex}
    (hzlo : certificate.domain.lo <= z)
    (hzhi : z <= certificate.domain.hi) :
    CPoly.eval coeffs z ≠ QComplex.zero := by
  obtain ⟨Z, hZmem, hZlo, hZhi⟩ := certificate.cover z hzlo hzhi
  exact evalPoly_no_root_of_not_overlaps_zero hZlo hZhi
    (certificate.misses_zero Z hZmem)

/-- A finite subdivision certificate with exactly one child retained for
further search.  The certificate records only coverage and sound exclusion of
the other children; it does not assert that the survivor contains a root. -/
structure OneSurvivorCertificate
    (coeffs : CPoly.Coeffs) (parent : QBox) where
  children : List QBox
  survivor : QBox
  survivor_mem : survivor ∈ children
  cover : ∀ z : QComplex,
    parent.lo <= z → z <= parent.hi →
      ∃ child, child ∈ children ∧ child.lo <= z ∧ z <= child.hi
  discard_other : ∀ child, child ∈ children → child ≠ survivor →
    ¬ QBox.Overlaps (evalPoly coeffs child) QBox.zero

/-- Any root in the parent domain must lie in the retained survivor. -/
theorem OneSurvivorCertificate.root_mem_survivor
    {coeffs : CPoly.Coeffs} {parent : QBox}
    (certificate : OneSurvivorCertificate coeffs parent)
    {z : QComplex}
    (hzlo : parent.lo <= z) (hzhi : z <= parent.hi)
    (hzroot : CPoly.eval coeffs z = QComplex.zero) :
    certificate.survivor.lo <= z ∧ z <= certificate.survivor.hi := by
  obtain ⟨child, hchildmem, hchildlo, hchildhi⟩ :=
    certificate.cover z hzlo hzhi
  by_cases heq : child = certificate.survivor
  · simpa [heq] using And.intro hchildlo hchildhi
  · have hno := certificate.discard_other child hchildmem heq
    exact False.elim
      (evalPoly_no_root_of_not_overlaps_zero hchildlo hchildhi hno hzroot)

end QBox

end ComputableAnalysis
