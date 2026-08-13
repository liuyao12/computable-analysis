import ComputableAnalysis.FinitePolynomialCalculus

/-!
# Finite Taylor FTC interface

This packages the endpoint identity for a finite integrated Taylor prefix.
It is the project-native term-by-term integration statement: each stage is a
finite rational polynomial, and extending the stage adds exactly one endpoint
monomial contribution.
-/

namespace ComputableAnalysis

namespace FinitePolynomial

theorem finiteTaylorFTC_step
    (coeffs : Nat -> Rat) (n : Nat) (a b : Rat) :
    integratedTaylorPrefix coeffs (n + 1) b -
        integratedTaylorPrefix coeffs (n + 1) a =
      (integratedTaylorPrefix coeffs n b -
        integratedTaylorPrefix coeffs n a) +
        coeffs n *
          (b ^ (n + 1) / ((n + 1 : Nat) : Rat) -
            a ^ (n + 1) / ((n + 1 : Nat) : Rat)) := by
  exact integratedTaylorPrefix_endpointDifference_succ coeffs n a b

theorem finiteTaylorFTC_prefix
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    integratedTaylorPrefix coeffs terms b -
        integratedTaylorPrefix coeffs terms a =
      (List.range terms).foldl
        (fun acc k => acc + coeffs k *
          (b ^ (k + 1) / ((k + 1 : Nat) : Rat) -
            a ^ (k + 1) / ((k + 1 : Nat) : Rat))) 0 := by
  induction terms with
  | zero => simp [integratedTaylorPrefix, Rat.sub_self]
  | succ terms ih =>
      rw [show terms + 1 = terms + 1 by rfl]
      rw [finiteTaylorFTC_step]
      simp only [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      simpa [integratedTaylorPrefix] using congrArg
        (fun q => q + coeffs terms *
          (b ^ (terms + 1) / ((terms + 1 : Nat) : Rat) -
            a ^ (terms + 1) / ((terms + 1 : Nat) : Rat))) ih

end FinitePolynomial

end ComputableAnalysis
