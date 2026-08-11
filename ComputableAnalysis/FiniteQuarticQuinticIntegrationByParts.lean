import ComputableAnalysis.FinitePolynomialIntegrationByParts

/-!
# A finite quartic--quintic integration-by-parts certificate

This is the next worked degree in the finite integration-by-parts ladder.
The two endpoint-weighted sums for `x^4` and `x^5` telescope on every
positive rational grid to the endpoint product `1`.  No completed integral,
limit, or completeness principle is used.
-/

namespace ComputableAnalysis

namespace FiniteQuarticQuinticIntegrationByParts

open FinitePolynomialIntegrationByParts

def quartic (x : Rat) : Rat := x ^ 4

def quintic (x : Rat) : Rat := x ^ 5

def quarticQuinticLeftRightSum (n : Nat) : Rat :=
  finiteRatSum
    (fun k =>
      (quartic (unitGridPoint n (k + 1)) - quartic (unitGridPoint n k)) *
          quintic (unitGridPoint n k) +
        quartic (unitGridPoint n (k + 1)) *
          (quintic (unitGridPoint n (k + 1)) - quintic (unitGridPoint n k))) n

def quarticQuinticRightLeftSum (n : Nat) : Rat :=
  finiteRatSum
    (fun k =>
      quartic (unitGridPoint n k) *
          (quintic (unitGridPoint n (k + 1)) - quintic (unitGridPoint n k)) +
        (quartic (unitGridPoint n (k + 1)) - quartic (unitGridPoint n k)) *
          quintic (unitGridPoint n (k + 1))) n

theorem quarticQuinticLeftRightSum_eq_endpoint_difference (n : Nat) :
    quarticQuinticLeftRightSum n =
      quartic (unitGridPoint n n) * quintic (unitGridPoint n n) -
        quartic (unitGridPoint n 0) * quintic (unitGridPoint n 0) := by
  unfold quarticQuinticLeftRightSum
  calc
    finiteRatSum
        (fun k =>
          (quartic (unitGridPoint n (k + 1)) - quartic (unitGridPoint n k)) *
              quintic (unitGridPoint n k) +
            quartic (unitGridPoint n (k + 1)) *
              (quintic (unitGridPoint n (k + 1)) - quintic (unitGridPoint n k))) n =
      finiteRatSum
          (fun k => (quartic (unitGridPoint n (k + 1)) -
            quartic (unitGridPoint n k)) * quintic (unitGridPoint n k)) n +
        finiteRatSum
          (fun k => quartic (unitGridPoint n (k + 1)) *
            (quintic (unitGridPoint n (k + 1)) - quintic (unitGridPoint n k))) n :=
      finiteRatSum_add _ _ _
    _ = quartic (unitGridPoint n n) * quintic (unitGridPoint n n) -
        quartic (unitGridPoint n 0) * quintic (unitGridPoint n 0) :=
      finiteRatSum_ibp_left_right quartic quintic (unitGridPoint n) n

theorem quarticQuinticRightLeftSum_eq_endpoint_difference (n : Nat) :
    quarticQuinticRightLeftSum n =
      quartic (unitGridPoint n n) * quintic (unitGridPoint n n) -
        quartic (unitGridPoint n 0) * quintic (unitGridPoint n 0) := by
  unfold quarticQuinticRightLeftSum
  calc
    finiteRatSum
        (fun k =>
          quartic (unitGridPoint n k) *
              (quintic (unitGridPoint n (k + 1)) - quintic (unitGridPoint n k)) +
            (quartic (unitGridPoint n (k + 1)) - quartic (unitGridPoint n k)) *
              quintic (unitGridPoint n (k + 1))) n =
      finiteRatSum
          (fun k => quartic (unitGridPoint n k) *
            (quintic (unitGridPoint n (k + 1)) - quintic (unitGridPoint n k))) n +
        finiteRatSum
          (fun k => (quartic (unitGridPoint n (k + 1)) -
            quartic (unitGridPoint n k)) * quintic (unitGridPoint n (k + 1))) n :=
      finiteRatSum_add _ _ _
    _ = quartic (unitGridPoint n n) * quintic (unitGridPoint n n) -
        quartic (unitGridPoint n 0) * quintic (unitGridPoint n 0) :=
      finiteRatSum_ibp_right_left quartic quintic (unitGridPoint n) n

theorem quarticQuinticLeftRightSum_eq_one {n : Nat} (hn : 0 < n) :
    quarticQuinticLeftRightSum n = 1 := by
  rw [quarticQuinticLeftRightSum_eq_endpoint_difference n]
  rw [unitGridPoint_self hn, unitGridPoint_zero]
  native_decide

theorem quarticQuinticRightLeftSum_eq_one {n : Nat} (hn : 0 < n) :
    quarticQuinticRightLeftSum n = 1 := by
  rw [quarticQuinticRightLeftSum_eq_endpoint_difference n]
  rw [unitGridPoint_self hn, unitGridPoint_zero]
  native_decide

theorem quarticQuinticLeftRightSum_stage4 :
    quarticQuinticLeftRightSum 4 = 1 := by
  exact quarticQuinticLeftRightSum_eq_one (by native_decide)

theorem quarticQuinticRightLeftSum_stage4 :
    quarticQuinticRightLeftSum 4 = 1 := by
  exact quarticQuinticRightLeftSum_eq_one (by native_decide)

end FiniteQuarticQuinticIntegrationByParts

end ComputableAnalysis
