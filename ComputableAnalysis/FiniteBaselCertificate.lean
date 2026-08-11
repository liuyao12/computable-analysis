import ComputableAnalysis.BaselFiniteStrengthening

/-!
# Packaged finite certificates for the Basel evaluator

This module packages one finite reciprocal-square enclosure together with its
precision budget and its finite partial-sum witness.  The later-stage theorem
is only a consequence of rational interval nesting; it does not introduce a
completed zeta value or assert Euler's Basel identity.
-/

namespace ComputableAnalysis

namespace DirichletSeries

/-- A finite, rational certificate for a requested enclosure width. -/
structure FiniteBaselCertificate (eps : Rat) where
  /-- The finite stage at which the certificate is evaluated. -/
  stage : Nat
  /-- The rational interval carried by the certificate. -/
  interval : QInterval
  /-- The carried interval is the standard reciprocal-square interval. -/
  interval_eq : interval = zetaTwoInterval stage
  /-- The carried interval has the requested finite precision. -/
  width_le : interval.width <= eps
  /-- The requested tolerance is positive. -/
  eps_pos : 0 < eps
  /-- A natural-number witness selecting a stage for this tolerance. -/
  denominator_budget : eps.den + 1 <= stage
  /-- The carried interval is ordered. -/
  ordered : interval.lo <= interval.hi
  /-- The stage partial sum is explicitly enclosed by the interval. -/
  partial_mem : interval.lo <= zetaTwoPartial stage /\
    zetaTwoPartial stage <= interval.hi

/-- Build a finite Basel certificate from the denominator/stage budget. -/
def finiteBaselCertificateOfBudget {eps : Rat} (n : Nat)
    (heps : 0 < eps) (hbudget : eps.den + 1 <= n) :
    FiniteBaselCertificate eps :=
  { stage := n
    interval := zetaTwoInterval n
    interval_eq := rfl
    width_le := zetaTwoInterval_width_le_of_denominator_budget heps hbudget
    eps_pos := heps
    denominator_budget := hbudget
    ordered := zetaTwoInterval_ordered n
    partial_mem := by
      change zetaTwoPartial n <= zetaTwoPartial n /\
        zetaTwoPartial n <= (zetaTwoInterval n).hi
      exact ⟨Rat.le_refl, zetaTwoInterval_ordered n⟩ }

theorem finiteBaselCertificateOfBudget_stage {eps : Rat} {n : Nat}
    (heps : 0 < eps) (hbudget : eps.den + 1 <= n) :
    (finiteBaselCertificateOfBudget n heps hbudget).stage = n := by
  rfl

theorem finiteBaselCertificateOfBudget_interval {eps : Rat} {n : Nat}
    (heps : 0 < eps) (hbudget : eps.den + 1 <= n) :
    (finiteBaselCertificateOfBudget n heps hbudget).interval =
      zetaTwoInterval n := by
  rfl

/-- Every later stage remains inside the certificate's finite enclosure and
retains the same requested width budget. -/
theorem FiniteBaselCertificate.contains_later
    {eps : Rat} (certificate : FiniteBaselCertificate eps)
    {m : Nat} (hm : certificate.stage <= m) :
    certificate.interval.lo <= (zetaTwoInterval m).lo /\
      (zetaTwoInterval m).hi <= certificate.interval.hi /\
      (zetaTwoInterval m).width <= eps := by
  rw [certificate.interval_eq]
  have hnest := zetaTwoInterval_nested certificate.stage m hm
  have hwidth : (zetaTwoInterval m).width <= eps := by
    exact zetaTwoInterval_width_le_of_denominator_budget
      certificate.eps_pos (Nat.le_trans certificate.denominator_budget hm)
  exact ⟨hnest.1, hnest.2.2, hwidth⟩

end DirichletSeries

end ComputableAnalysis
