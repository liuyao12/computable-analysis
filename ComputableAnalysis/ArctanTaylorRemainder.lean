import ComputableAnalysis.FiniteSecantIntegralOrder
import ComputableAnalysis.Taylor

/-! # Finite arctangent Taylor integration
The geometric identity, quantitative polynomial FTC, and exact integral order
are separate from the Leibniz benchmark and from its finite rectangle proof.
-/
namespace ComputableAnalysis.Taylor.ArctanKernel

/-- The monomial form of the finite geometric remainder numerator. -/
theorem neg_square_pow (x : Rat) (n : Nat) :
    (-(x*x))^n = (-1:Rat)^n * x^(2*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2*(n+1)=2*n+1+1 by omega]
      rw [Rat.pow_succ, ih, Rat.pow_succ, Rat.pow_succ, Rat.pow_succ]
      grind

theorem square_pow (x : Rat) (n : Nat) :
    (x*x)^n = x^(2*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2*(n+1)=2*n+1+1 by omega]
      rw [Rat.pow_succ, ih, Rat.pow_succ, Rat.pow_succ]
      grind

/-- Pointwise power majorant for the exact division remainder. -/
theorem finite_geometric_remainder_bound (x : Rat) (N : Nat) :
    qabs (1/(1+x*x) - kernelPartial x N) ≤ x^(2*N+2) := by
  have h := qabs_kernelRemainder_le_power x N
  have heq := one_div_one_add_square_eq_partial_add_remainder x N
  have hd : 1/(1+x*x) - kernelPartial x N = kernelRemainder x N := by grind
  rw [hd]
  simpa only [square_pow, show 2*(N+1)=2*N+2 by omega] using h

/-- Finite geometric division, with the classical signed power remainder. -/
theorem finite_geometric_identity (x : Rat) (N : Nat) :
    1/(1+x*x) = kernelPartial x N +
      (-1:Rat)^(N+1)*x^(2*N+2)/(1+x*x) := by
  have h := one_div_one_add_square_eq_partial_add_remainder x N
  simpa only [kernelRemainder, remainderNumerator, neg_square_pow,
    show 2*(N+1)=2*N+2 by omega] using h

theorem kernelPartial_succ_monomial (x : Rat) (n : Nat) :
    kernelPartial x (n+1) = kernelPartial x n +
      (-1:Rat)^(n+1)*x^(2*(n+1)) := by
  exact congrArg (fun t => kernelPartial x n + t) (neg_square_pow x (n+1))

private theorem normalized_term (j : Nat) (x : Rat) :
    (-1:Rat)^j*(x^(2*j+1)/((2*j+1:Nat):Rat)) =
      kernelTermIntegralBetween 0 x j := by
  have hz : (0:Rat)^(2*j+1)=0 := by simp [Rat.pow_succ]
  simp only [kernelTermIntegralBetween, hz,
    Rat.natCast_add, Rat.natCast_mul]
  grind [Rat.div_def]

/-- The actual finite primitive has the kernel polynomial as derivative.
The certificate is assembled from the existing normalized-monomial FTC data. -/
def kernelPrimitiveSecantBound : (n : Nat) →
    FinitePolynomial.SecantDerivativeBound 1
      (fun x => kernelPartialIntegralBetween 0 x n)
      (fun x => kernelPartial x n)
  | 0 => by
      have hone : (1:Rat)⁻¹ = 1 := by
        simpa only [Rat.one_mul] using Rat.mul_inv_cancel 1 (by decide)
      simpa [kernelPartialIntegralBetween, kernelPartial, altGeomPartial,
        Rat.sub_eq_add_neg, Rat.div_def, hone, Rat.add_zero, Rat.mul_one]
        using FinitePolynomial.normalizedMonomialSecantBound 1 0 (by decide)
  | n+1 => by
      have D := (kernelPrimitiveSecantBound n).add
        ((FinitePolynomial.normalizedMonomialSecantBound 1 (2*(n+1))
          (by decide)).scaleRat ((-1:Rat)^(n+1)))
      have hf : (fun x => kernelPartialIntegralBetween 0 x n +
          (-1:Rat)^(n+1)*(x^(2*(n+1)+1)/((2*(n+1)+1:Nat):Rat))) =
          (fun x => kernelPartialIntegralBetween 0 x (n+1)) := by
        funext x
        rw [normalized_term]
        rfl
      have hg : (fun x => kernelPartial x n + (-1:Rat)^(n+1)*x^(2*(n+1))) =
          (fun x => kernelPartial x (n+1)) := by
        funext x
        exact (kernelPartial_succ_monomial x n).symm
      rw [hf, hg] at D
      exact D

/-- All-degree finite polynomial FTC order; no special-degree quadrature. -/
theorem kernelPartial_exactCellOrder (n : Nat) :
    Integral.ExactCellOrderPreservation
      (fun x => kernelPartial x n)
      (fun p r => kernelPartialIntegralBetween p r n) 0 1 := by
  have h := (kernelPrimitiveSecantBound n).exactCellOrder
  have heq : (fun p r => kernelPartialIntegralBetween 0 r n -
      kernelPartialIntegralBetween 0 p n) =
      (fun p r => kernelPartialIntegralBetween p r n) := by
    funext p r
    have hsplit := kernelPartialIntegralBetween_split 0 p r n
    grind
  rw [heq] at h
  exact h

end ComputableAnalysis.Taylor.ArctanKernel
