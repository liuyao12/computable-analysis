import ComputableAnalysis.FiniteDyadicAMGM

/-!
# Reusable finite AM--GM interface

The certificate is a complete finite dyadic tree of nonnegative rational
leaves.  Its product/average bound is the project-native AM--GM theorem.
-/

namespace ComputableAnalysis

structure FiniteAMGMCertificate (depth : Nat) where
  tree : DyadicAMGM depth

theorem FiniteAMGMCertificate.product_le_average_pow
    {depth : Nat} (certificate : FiniteAMGMCertificate depth) :
    DyadicAMGM.product certificate.tree ≤
      (DyadicAMGM.sum certificate.tree / ((2 ^ depth : Nat) : Rat)) ^
        (2 ^ depth) := by
  exact DyadicAMGM.product_le_average_pow certificate.tree

theorem FiniteAMGMCertificate.product_mul_card_pow_le_sum_pow
    {depth : Nat} (certificate : FiniteAMGMCertificate depth) :
    (((2 ^ depth : Nat) : Rat) ^ (2 ^ depth)) *
        DyadicAMGM.product certificate.tree ≤
      (DyadicAMGM.sum certificate.tree) ^ (2 ^ depth) := by
  exact DyadicAMGM.product_mul_card_pow_le_sum_pow certificate.tree

def finiteAMGMCertificate {depth : Nat} (tree : DyadicAMGM depth) :
    FiniteAMGMCertificate depth :=
  ⟨tree⟩

end ComputableAnalysis
