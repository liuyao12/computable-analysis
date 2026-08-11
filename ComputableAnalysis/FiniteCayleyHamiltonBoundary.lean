import ComputableAnalysis.PeanoBaker

/-!
# A representation-first arbitrary-dimension Cayley--Hamilton boundary

This module does not define a determinant and does not claim the general
Cayley--Hamilton theorem.  It packages the finite certificate that is actually
needed downstream: explicit rational lower coefficients, a monic polynomial
annihilation identity, and the power recurrence that follows from it.

The dimension is completely arbitrary.  Thus a separately checked determinant
or characteristic-polynomial construction can later instantiate this interface
without changing the matrix-power consumer.
-/

namespace ComputableAnalysis
namespace LinearODE

/- The coefficient list is in increasing degree order.  The index argument is
   the first power used by the list, so every definition remains a finite
   recursive rational computation. -/
def matrixPolynomialSum {dimension : Nat} (A : RatMatrix dimension) :
    List Rat → Nat → RatMatrix dimension
  | [], _ => matrixZero dimension
  | coefficient :: coefficients, degree =>
      matrixAdd
        (matrixScale coefficient (matrixPow A degree))
        (matrixPolynomialSum A coefficients (degree + 1))

theorem matrixPolynomialSum_mul_matrixPow {dimension : Nat}
    (A : RatMatrix dimension) (coefficients : List Rat) (degree steps : Nat) :
    matrixMul (matrixPolynomialSum A coefficients degree)
        (matrixPow A steps) =
      matrixPolynomialSum A coefficients (degree + steps) := by
  induction coefficients generalizing degree with
  | nil =>
      simp [matrixPolynomialSum, matrixMul_zero_left]
  | cons coefficient coefficients ih =>
      change matrixMul
          (matrixAdd
            (matrixScale coefficient (matrixPow A degree))
            (matrixPolynomialSum A coefficients (degree + 1)))
          (matrixPow A steps) =
        matrixAdd
          (matrixScale coefficient (matrixPow A (degree + steps)))
          (matrixPolynomialSum A coefficients (degree + steps + 1))
      rw [matrixMul_add_left,
        matrixMul_matrixScale_left, matrixPow_add]
      rw [ih (degree + 1)]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem matrixPolynomialSum_shifted_annihilation {dimension : Nat}
    (A : RatMatrix dimension) (coefficients : List Rat)
    (hannihilates :
      matrixPolynomialSum A (coefficients ++ [1]) 0 = matrixZero dimension)
    (steps : Nat) :
    matrixPolynomialSum A (coefficients ++ [1]) steps = matrixZero dimension := by
  have hmul := congrArg (fun M => matrixMul M (matrixPow A steps)) hannihilates
  rw [matrixPolynomialSum_mul_matrixPow, matrixMul_zero_left] at hmul
  simpa [Nat.zero_add] using hmul

theorem matrixPolynomialSum_append_one {dimension : Nat}
    (A : RatMatrix dimension) (coefficients : List Rat) (degree : Nat) :
    matrixPolynomialSum A (coefficients ++ [1]) degree =
      matrixAdd
        (matrixPolynomialSum A coefficients degree)
        (matrixPow A (degree + coefficients.length)) := by
  induction coefficients generalizing degree with
  | nil =>
      funext i j
      simp [matrixPolynomialSum, matrixAdd, matrixScale, matrixZero]
      grind [Rat.add_zero, Rat.zero_add]
  | cons coefficient coefficients ih =>
      simp only [List.cons_append, List.length_cons]
      dsimp [matrixPolynomialSum]
      change matrixAdd
          (matrixScale coefficient (matrixPow A degree))
          (matrixPolynomialSum A (coefficients ++ [1]) (degree + 1)) =
        matrixAdd
        (matrixAdd
            (matrixScale coefficient (matrixPow A degree))
            (matrixPolynomialSum A coefficients (degree + 1)))
          (matrixPow A (degree + (coefficients.length + 1)))
      rw [ih (degree := degree + 1)]
      rw [show degree + 1 + coefficients.length =
        degree + (coefficients.length + 1) by omega]
      rw [← matrixAdd_assoc]

/-!
The certificate stores exactly the missing arbitrary-dimension input.  The
last coefficient is represented structurally by appending `1`, so the degree
and recurrence order are executable (`coefficients.length`).
-/
structure FiniteCayleyHamiltonCertificate (dimension : Nat) where
  matrix : RatMatrix dimension
  lowerCoefficients : List Rat
  annihilates :
    matrixPolynomialSum matrix (lowerCoefficients ++ [1]) 0 =
      matrixZero dimension

theorem FiniteCayleyHamiltonCertificate.shifted_annihilates
    {dimension : Nat} (certificate : FiniteCayleyHamiltonCertificate dimension)
    (steps : Nat) :
    matrixPolynomialSum certificate.matrix
        (certificate.lowerCoefficients ++ [1]) steps =
      matrixZero dimension := by
  exact matrixPolynomialSum_shifted_annihilation
    certificate.matrix certificate.lowerCoefficients
    certificate.annihilates steps

/-- The finite arbitrary-dimension power recurrence carried by a monic
annihilating-polynomial certificate.

For coefficients `c₀, ..., c₍d₋₁₎`, this is
`A^(n+d) = -∑ cᵢ A^(n+i)`.  No determinant, characteristic-polynomial
construction, completed scalar field, or infinite argument is hidden here. -/
theorem FiniteCayleyHamiltonCertificate.power_recurrence
    {dimension : Nat} (certificate : FiniteCayleyHamiltonCertificate dimension)
    (steps : Nat) :
    matrixPow certificate.matrix
        (steps + certificate.lowerCoefficients.length) =
      matrixScale (-1)
        (matrixPolynomialSum certificate.matrix
          certificate.lowerCoefficients steps) := by
  have hshift := certificate.shifted_annihilates steps
  rw [matrixPolynomialSum_append_one] at hshift
  funext i j
  have hij := congrFun (congrFun hshift i) j
  dsimp [matrixAdd, matrixScale, matrixZero] at hij ⊢
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

end LinearODE
end ComputableAnalysis
