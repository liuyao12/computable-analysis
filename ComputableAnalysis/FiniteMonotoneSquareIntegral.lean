import ComputableAnalysis.FiniteFTCIntervalRegular
import ComputableAnalysis.FiniteFTCQuartic

/-!
# A finite monotone-integrability bridge for the square

The square on `[0,1]` is nondecreasing by a rational factorization, and its
existing interval-regular integral construction is therefore promoted to the
project's monotone-integrability interface.  The bridge remains finite: the
construction is supplied by the dyadic rational certificate already checked
for the square.
-/

namespace ComputableAnalysis

namespace Integral

theorem exactRat_square_nondecreasing :
    NondecreasingOnInterval
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1) := by
  intro x y hx hy hxy n
  change x * x <= y * y
  have hx0 : 0 <= x := by
    have h := hx.1
    change (0 : Rat) <= x at h
    exact h
  have hy0 : 0 <= y := by
    have h := hy.1
    change (0 : Rat) <= y at h
    exact h
  have hfactor : y * y - x * x = (y - x) * (y + x) := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
  have hsum : 0 <= y + x := Rat.add_nonneg hy0 hx0
  have hprod : 0 <= (y - x) * (y + x) :=
    Rat.mul_nonneg (by grind) hsum
  have hdiff : 0 <= y * y - x * x := by
    rw [hfactor]
    exact hprod
  grind

def exactRat_square_monotone_construction :
    MonotoneConstructionFor
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1) where
  monotone := MonotoneOnInterval.ofNondecreasing exactRat_square_nondecreasing
  construction := exactRat_square_integral_certificate.construction

theorem exactRat_square_monotone_integral_valid :
    (monotoneIntegralFor
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1)
      exactRat_square_monotone_construction).Valid := by
  exact monotoneIntegralFor_valid _ exactRat_square_monotone_construction

theorem exactRat_square_monotone_integral_eq_one_third :
    (monotoneIntegralFor
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1)
      exactRat_square_monotone_construction).Equiv
      (RealRaw.ofRat (1 / 3)) := by
  exact exactRat_square_integral_raw_equiv_one_third

theorem exactRat_cube_nondecreasing :
    NondecreasingOnInterval
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1) := by
  intro x y hx hy hxy n
  change x ^ 3 <= y ^ 3
  have hx0 : 0 <= x := by
    have h := hx.1
    change (0 : Rat) <= x at h
    exact h
  have hy0 : 0 <= y := by
    have h := hy.1
    change (0 : Rat) <= y at h
    exact h
  have hfactor : y ^ 3 - x ^ 3 =
      (y - x) * (y ^ 2 + y * x + x ^ 2) := by
    grind [Rat.pow_succ, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hsum : 0 <= y ^ 2 + y * x + x ^ 2 := by
    exact Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg hy0)
      (Rat.mul_nonneg hy0 hx0)) (Rat.pow_nonneg hx0)
  have hdiff : 0 <= y ^ 3 - x ^ 3 := by
    rw [hfactor]
    exact Rat.mul_nonneg (by grind) hsum
  grind

def exactRat_cube_monotone_construction :
    MonotoneConstructionFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1) where
  monotone := MonotoneOnInterval.ofNondecreasing exactRat_cube_nondecreasing
  construction := exactRat_cube_integral_certificate.construction

theorem exactRat_cube_monotone_integral_valid :
    (monotoneIntegralFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1)
      exactRat_cube_monotone_construction).Valid := by
  exact monotoneIntegralFor_valid _ exactRat_cube_monotone_construction

theorem exactRat_cube_monotone_integral_eq_one_fourth :
    (monotoneIntegralFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1)
      exactRat_cube_monotone_construction).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  exact exactRat_cube_integral_raw_equiv_one_fourth

theorem exactRat_quartic_nondecreasing :
    NondecreasingOnInterval
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1) := by
  intro x y hx hy hxy n
  change x ^ 4 <= y ^ 4
  have hx0 : 0 <= x := by
    have h := hx.1
    change (0 : Rat) <= x at h
    exact h
  have hy0 : 0 <= y := by
    have h := hy.1
    change (0 : Rat) <= y at h
    exact h
  have hfactor : y ^ 4 - x ^ 4 =
      (y - x) * (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3) := by
    grind [Rat.pow_succ, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hsum : 0 <= y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3 := by
    exact Rat.add_nonneg (Rat.add_nonneg
      (Rat.add_nonneg (Rat.pow_nonneg hy0)
        (Rat.mul_nonneg (Rat.pow_nonneg hy0) hx0))
      (Rat.mul_nonneg hy0 (Rat.pow_nonneg hx0))) (Rat.pow_nonneg hx0)
  have hdiff : 0 <= y ^ 4 - x ^ 4 := by
    rw [hfactor]
    exact Rat.mul_nonneg (by grind) hsum
  grind

def exactRat_quartic_monotone_construction :
    MonotoneConstructionFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1) where
  monotone := MonotoneOnInterval.ofNondecreasing exactRat_quartic_nondecreasing
  construction := exactRat_quartic_integral_certificate.construction

theorem exactRat_quartic_monotone_integral_valid :
    (monotoneIntegralFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1)
      exactRat_quartic_monotone_construction).Valid := by
  exact monotoneIntegralFor_valid _ exactRat_quartic_monotone_construction

theorem exactRat_quartic_monotone_integral_eq_one_fifth :
    (monotoneIntegralFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1)
      exactRat_quartic_monotone_construction).Equiv
      (RealRaw.ofRat (1 / 5)) := by
  exact exactRat_quartic_integral_raw_equiv_one_fifth

end Integral

end ComputableAnalysis
