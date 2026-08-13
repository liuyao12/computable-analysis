import ComputableAnalysis.FinitePolynomialCalculus

/-!
# Finite half-period sine integral certificates

The target is the normalized identity
`pi * integral_0^(1/2) sin (pi*x) dx = 1`.
At a finite stage we replace `pi` by a rational enclosure center and `sin`
by its finite Taylor polynomial.  After the change of variable `u = pi*x`,
the displayed quantity is simply the finite primitive of the sine prefix at
`u = pi/2`.  This file records that computable finite layer only; it does not
assert a completed integral or an attained classical limit.
-/

namespace ComputableAnalysis

namespace FiniteSineIntegral

def halfAnglePrefix (piApprox : Rat) (terms : Nat) : Rat :=
  FinitePolynomial.integratedTaylorPrefix
    FormalPowerSeries.sinCoeff terms (piApprox / 2)

theorem halfAnglePrefix_zero (piApprox : Rat) :
    halfAnglePrefix piApprox 0 = 0 := by
  rfl

theorem halfAnglePrefix_succ (piApprox : Rat) (terms : Nat) :
    halfAnglePrefix piApprox (terms + 1) =
      halfAnglePrefix piApprox terms +
        FormalPowerSeries.sinCoeff terms *
          (piApprox / 2) ^ (terms + 1) / ((terms + 1 : Nat) : Rat) := by
  unfold halfAnglePrefix
  rw [FinitePolynomial.integratedTaylorPrefix]
  simp only
  congr 1
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem halfAnglePrefix_endpointDifference_succ
    (terms : Nat) (a b : Rat) :
    FinitePolynomial.integratedTaylorPrefix
        FormalPowerSeries.sinCoeff (terms + 1) b -
        FinitePolynomial.integratedTaylorPrefix
          FormalPowerSeries.sinCoeff (terms + 1) a =
      (FinitePolynomial.integratedTaylorPrefix
          FormalPowerSeries.sinCoeff terms b -
        FinitePolynomial.integratedTaylorPrefix
          FormalPowerSeries.sinCoeff terms a) +
        FormalPowerSeries.sinCoeff terms *
          (b ^ (terms + 1) / ((terms + 1 : Nat) : Rat) -
            a ^ (terms + 1) / ((terms + 1 : Nat) : Rat)) := by
  exact FinitePolynomial.integratedTaylorPrefix_endpointDifference_succ
    FormalPowerSeries.sinCoeff terms a b

theorem halfAnglePrefix_stage_four :
    halfAnglePrefix (355 / 113) 4 =
      (61359934175 : Rat) / 62610186624 := by
  native_decide

theorem halfAnglePrefix_stage_six :
    halfAnglePrefix (355 / 113) 6 =
      (19204433374786925 : Rat) / 19187267352044544 := by
  native_decide

theorem halfAnglePrefix_stage_six_near_one :
    qabs (halfAnglePrefix (355 / 113) 6 - 1) <=
      1 / 1000 := by
  rw [halfAnglePrefix_stage_six]
  native_decide

theorem halfAnglePrefix_stage_eight :
    halfAnglePrefix (355 / 113) 8 =
      (54879146292205975874675 : Rat) /
        54880496567289519243264 := by
  native_decide

theorem halfAnglePrefix_stage_eight_near_one :
    qabs (halfAnglePrefix (355 / 113) 8 - 1) <=
      1 / 10000 := by
  rw [halfAnglePrefix_stage_eight]
  native_decide

theorem halfAnglePrefix_stage_ten :
    halfAnglePrefix (355 / 113) 10 =
      (50455402547884936862792346025 : Rat) /
        50455372368075830727641137152 := by
  native_decide

theorem halfAnglePrefix_stage_ten_near_one :
    qabs (halfAnglePrefix (355 / 113) 10 - 1) <=
      1 / 1000000 := by
  rw [halfAnglePrefix_stage_ten]
  native_decide

end FiniteSineIntegral

end ComputableAnalysis
