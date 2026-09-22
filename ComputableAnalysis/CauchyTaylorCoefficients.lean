import ComputableAnalysis.CauchyTaylor
import ComputableAnalysis.ComplexMultiplication

/-! Cauchy moments as fixed computable coefficients. The quadrature convergence
certificate here concerns each monomial on the boundary. It does not assume
any expansion of the interior function. -/

namespace ComputableAnalysis.CauchyTaylor

open QComplex
open CertifiedComplexApproximation (rate)

structure Moments (rules : Nat → Rule) where
  bound : Nat → Rat
  nonneg : ∀ k, 0 ≤ bound k
  future : ∀ k i j, i ≤ j →
    normBound (sub (coefficientSample (rules j) k) (coefficientSample (rules i) k)) ≤
      rate (bound k) i

namespace Moments

def coefficient {rules : Nat → Rule} (m : Moments rules) (k : Nat) : ComplexRaw :=
  ComplexRaw.cauchyStabilize
    (CertifiedComplexApproximation.candidate (fun n => coefficientSample (rules n) k))
    (rate (m.bound k))

theorem coefficient_future {rules : Nat → Rule} (m : Moments rules) (k i j : Nat)
    (hij : i ≤ j) :
    (QBox.point (coefficientSample (rules j) k)).NestedIn
      (QBox.expand (QBox.point (coefficientSample (rules i) k)) (rate (m.bound k) i)) := by
  have h := l1_coordinates (m.future k i j hij)
  simp only [QBox.NestedIn, QBox.point, QBox.expand, QComplex.le_def, sub, add, neg] at *
  constructor <;> constructor <;> grind only

theorem coefficient_valid {rules : Nat → Rule} (m : Moments rules) (k : Nat) :
    (m.coefficient k).Valid := by
  apply ComplexRaw.cauchyStabilize_valid (fun _ => QComplex.le_refl _) _
    (m.coefficient_future k) (CertifiedComplexApproximation.rate_shrinks _)
  intro eps
  refine ⟨0, fun n _ => ?_⟩
  have hp := eps.property
  change (coefficientSample (rules n) k).re - (coefficientSample (rules n) k).re ≤ eps.val ∧
    (coefficientSample (rules n) k).im - (coefficientSample (rules n) k).im ≤ eps.val
  constructor <;> grind only

theorem coefficient_contains_sample {rules : Nat → Rule} (m : Moments rules) (k n : Nat) :
    (QBox.point (coefficientSample (rules n) k)).NestedIn ((m.coefficient k).compute n) :=
  ComplexRaw.cauchyStabilize_contains_current (m.coefficient_future k) n

/-- Finite partial sums of the fixed `ComplexRaw` coefficient sequence. -/
def partialSum {rules : Nat → Rule} (m : Moments rules) (z : QComplex) : Nat → ComplexRaw
  | 0 => ComplexRaw.ofQComplex zero
  | N+1 => ComplexRaw.add (m.partialSum z N)
      (ComplexRaw.mul (m.coefficient N) (ComplexRaw.ofQComplex (natPow z N)))

theorem partialSum_valid {rules : Nat → Rule} (m : Moments rules) (z : QComplex) (N : Nat) :
    (m.partialSum z N).Valid := by
  induction N with
  | zero => exact ComplexRaw.ofQComplex_valid zero
  | succ N ih =>
      exact ComplexRaw.add_valid ih (ComplexRaw.mul_valid (m.coefficient_valid N)
        (ComplexRaw.ofQComplex_valid _))

/-- The rational polynomial used by the series evaluator is an actual sample
inside the finite sum of the independently constructed coefficients. -/
theorem partialSum_contains_sample {rules : Nat → Rule} (m : Moments rules)
    (z : QComplex) (N n : Nat) :
    (QBox.point (polynomialSample (rules n) z N)).NestedIn ((m.partialSum z N).compute n) := by
  induction N with
  | zero =>
      rw [polynomialSample_zero]
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | succ N ih =>
      rw [polynomialSample_succ]
      have hc := m.coefficient_contains_sample N n
      have hm := QBox.mul_contains (B := QBox.point (natPow z N)) hc.1 hc.2
        (QComplex.le_refl (natPow z N)) (QComplex.le_refl (natPow z N))
      exact QBox.add_contains ih.1 ih.2 hm.1 hm.2

end Moments

/-- Both the interior Cauchy representation and convergence of its boundary
moments are explicit. No Taylor representation is supplied as a field. -/
structure SeriesCertificate (f : QComplex → ComplexRaw) where
  cauchy : Representation f
  moments : Moments cauchy.rules

namespace SeriesCertificate

def coefficient {f : QComplex → ComplexRaw} (c : SeriesCertificate f) (k : Nat) : ComplexRaw :=
  c.moments.coefficient k

def series {f : QComplex → ComplexRaw} (c : SeriesCertificate f) (z : QComplex) (r : Rat) : ComplexRaw :=
  c.cauchy.series z r

theorem eq_series {f : QComplex → ComplexRaw} (c : SeriesCertificate f)
    {z : QComplex} {r : Rat} (hr : 0 ≤ r) (hr1 : r < 1) (hz : InDisk z r) :
    (f z).Equiv (c.series z r) := c.cauchy.eq_series hr hr1 hz

end SeriesCertificate
end ComputableAnalysis.CauchyTaylor
