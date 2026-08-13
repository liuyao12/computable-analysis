import ComputableAnalysis.FiniteCauchySchwarzList

/-!
# Reusable finite Cauchy--Schwarz interface

The certificate records only finite rational folds.  Its proof is the
nonnegative sum-of-squared-minors argument, so no infinite inner product or
completed scalar space is involved.
-/

namespace ComputableAnalysis

structure FiniteCauchySchwarzCertificate where
  leftList : List Rat
  rightList : List Rat
  equal_length : leftList.length = rightList.length

theorem FiniteCauchySchwarzCertificate.inequality
    (certificate : FiniteCauchySchwarzCertificate) :
    (rationalDot certificate.leftList certificate.rightList) ^ 2 ≤
      rationalSumSquares certificate.leftList *
        rationalSumSquares certificate.rightList := by
  exact rationalDot_cauchy_schwarz_of_length_eq certificate.equal_length

theorem FiniteCauchySchwarzCertificate.square_sums_nonneg
    (certificate : FiniteCauchySchwarzCertificate) :
    0 ≤ rationalSumSquares certificate.leftList ∧
      0 ≤ rationalSumSquares certificate.rightList := by
  exact ⟨rationalSumSquares_nonneg _, rationalSumSquares_nonneg _⟩

def finiteCauchySchwarzCertificate (left right : List Rat)
    (equal_length : left.length = right.length) :
    FiniteCauchySchwarzCertificate where
  leftList := left
  rightList := right
  equal_length := equal_length

theorem finiteCauchySchwarzCertificate_inequality
    (left right : List Rat) (equal_length : left.length = right.length) :
    (rationalDot left right) ^ 2 ≤
      rationalSumSquares left * rationalSumSquares right := by
  exact FiniteCauchySchwarzCertificate.inequality
    (finiteCauchySchwarzCertificate left right equal_length)

end ComputableAnalysis
