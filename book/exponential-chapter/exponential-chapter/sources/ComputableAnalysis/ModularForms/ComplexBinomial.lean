import ComputableAnalysis.RiemannHilbert.ScalarAlgebra
import ComputableAnalysis.Series

/-! Finite binomial algebra over valid represented complex values. This is
an ingredient for the exponential Cauchy product, not yet an infinite-sum law. -/
namespace ComputableAnalysis.ModularForms.ComplexBinomial
open ComputableAnalysis.RiemannHilbert

private theorem power_succ (x : ScalarAlgebra.Value) (n : Nat) : x^(n+1)=x^n*x := rfl

private theorem combination_pascal_cast (n k : Nat) :
    (FiniteCounting.combination (n+1) (k+1) : ScalarAlgebra.Value) =
      (FiniteCounting.combination n (k+1) : ScalarAlgebra.Value) +
      (FiniteCounting.combination n k : ScalarAlgebra.Value) := by
  rw [FiniteCounting.combination_pascal]
  grind

private theorem combination_outside_cast (n k : Nat) (h : n < k) :
    (FiniteCounting.combination n k : ScalarAlgebra.Value)=0 := by
  rw [FiniteCounting.combination_outside n k h]
  rfl

def binomialTerm (n k : Nat) (x y : ScalarAlgebra.Value) : ScalarAlgebra.Value :=
  (FiniteCounting.combination n k : ScalarAlgebra.Value) * x ^ (n - k) * y ^ k

theorem binomialTerm_succ_succ_of_lt {n k : Nat} (hkn : k < n)
    (x y : ScalarAlgebra.Value) :
    binomialTerm (n + 1) (k + 1) x y =
      x * binomialTerm n (k + 1) x y +
        y * binomialTerm n k x y := by
  unfold binomialTerm
  rw [combination_pascal_cast]
  have hpow₁ : n + 1 - (k + 1) = n - k := by omega
  have hpow₂ : n - (k + 1) + 1 = n - k := by omega
  have hxpow : x * x ^ (n - (k + 1)) =
      x ^ (n - (k + 1) + 1) := by
    rw [power_succ]
    grind [ComplexRawQuotient.mul_comm]
  have hypow : y * y ^ k = y ^ (k + 1) := by
    rw [power_succ]
    grind [ComplexRawQuotient.mul_comm]
  simp only [hpow₁]
  grind [ComplexRawQuotient.mul_add, ComplexRawQuotient.add_mul,
    ComplexRawQuotient.mul_assoc, ComplexRawQuotient.mul_comm]

def binomialSum (n : Nat) (x y : ScalarAlgebra.Value) : Nat -> ScalarAlgebra.Value
  | 0 => 0
  | k + 1 => binomialSum n x y k + binomialTerm n k x y

theorem binomialSum_succ (n k : Nat) (x y : ScalarAlgebra.Value) :
    binomialSum n x y (k + 1) =
      binomialSum n x y k + binomialTerm n k x y := by
  rfl

theorem binomialSum_succ_row {n k : Nat} (hk : k <= n)
    (x y : ScalarAlgebra.Value) :
    binomialSum (n + 1) x y (k + 1) =
      x * binomialSum n x y (k + 1) +
        y * binomialSum n x y k := by
  induction k generalizing n with
  | zero =>
      simp only [binomialSum]
      simp [binomialTerm, FiniteCounting.combination_zero_right]
      rw [power_succ]
      grind [ComplexRawQuotient.mul_assoc, ComplexRawQuotient.mul_comm]
  | succ k ih =>
      have hkn : k < n := by omega
      change binomialSum (n + 1) x y (k + 1) +
          binomialTerm (n + 1) (k + 1) x y =
        x * (binomialSum n x y (k + 1) +
          binomialTerm n (k + 1) x y) +
          y * binomialSum n x y (k + 1)
      rw [ih (by omega), binomialSum_succ,
        binomialTerm_succ_succ_of_lt hkn]
      grind [ComplexRawQuotient.mul_add, ComplexRawQuotient.add_mul, ComplexRawQuotient.mul_assoc, ComplexRawQuotient.mul_comm]

theorem binomialTerm_top (n : Nat) (x y : ScalarAlgebra.Value) :
    binomialTerm n n x y = y ^ n := by
  simp [binomialTerm, FiniteCounting.combination_self]
  grind [ScalarAlgebra.power]

theorem binomialTerm_succ_top (n : Nat) (x y : ScalarAlgebra.Value) :
    binomialTerm (n + 1) (n + 1) x y =
      y * binomialTerm n n x y := by
  rw [binomialTerm_top, binomialTerm_top]
  rw [power_succ]
  grind [ComplexRawQuotient.mul_comm]

theorem binomialSum_extra (n : Nat) (x y : ScalarAlgebra.Value) :
    binomialSum n x y (n + 2) = binomialSum n x y (n + 1) := by
  rw [binomialSum_succ]
  unfold binomialTerm
  rw [combination_outside_cast n (n + 1) (by omega)]
  grind

theorem binomialSum_eq_pow (n : Nat) (x y : ScalarAlgebra.Value) :
    binomialSum n x y (n + 1) = (x + y) ^ n := by
  induction n with
  | zero =>
      simp [binomialSum, binomialTerm,
        FiniteCounting.combination_zero_right]
      grind
  | succ n ih =>
      rw [binomialSum_succ,
        binomialSum_succ_row (n := n) (k := n) (Nat.le_refl n),
        binomialTerm_succ_top, ComplexRawQuotient.add_assoc, ← ComplexRawQuotient.mul_add,
        ← binomialSum_succ, ih]
      rw [power_succ]
      grind [ComplexRawQuotient.mul_add, ComplexRawQuotient.add_mul, ComplexRawQuotient.mul_assoc, ComplexRawQuotient.mul_comm]


end ComputableAnalysis.ModularForms.ComplexBinomial
