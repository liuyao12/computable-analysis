import ComputableAnalysis.FinitePolynomialCalculus
import ComputableAnalysis.RotationTaylorBridge

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

/-! The finite sine primitive is exactly the complement of the matching
cosine prefix.  This is the algebraic change-of-variable identity behind the
later interval evaluator; no infinite series or completed integral is used. -/

theorem halfAnglePrefix_cosine_complement (piApprox : Rat) (terms : Nat) :
    halfAnglePrefix piApprox terms =
      1 - FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
        (terms + 1) (piApprox / 2) := by
  induction terms with
  | zero =>
      change 0 = 1 - (1 + 0)
      grind
  | succ terms ih =>
      rw [halfAnglePrefix_succ, ih]
      have hleft := FinitePolynomial.taylorPrefix_succ
        FormalPowerSeries.cosCoeff terms (piApprox / 2)
      have hright := FinitePolynomial.taylorPrefix_succ
        FormalPowerSeries.cosCoeff (terms + 1) (piApprox / 2)
      rw [hleft]
      rw [show terms + 1 + 1 = (terms + 1) + 1 by omega, hright]
      rw [FormalPowerSeries.cosCoeff]
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.sub_eq_add_neg]

/-! A rotation-scheduled version uses the even Taylor prefixes already covered
by the factorial rotation evaluator.  The extra `+1` is precisely the finite
primitive needed to turn cosine back into sine. -/

def halfPeriodSineRaw (piApprox : Rat) : RealRaw :=
  RealRaw.one - RotationSeries.rotationCosRaw (piApprox / 2)

theorem halfPeriodSineRaw_valid (piApprox : Rat) :
    (halfPeriodSineRaw piApprox).Valid := by
  unfold halfPeriodSineRaw
  exact RealRaw.sub_valid (RealRaw.ofRat_valid 1)
    (RotationSeries.rotationCosRaw_valid (piApprox / 2))

theorem halfPeriodSineRaw_compute (piApprox : Rat) (stage : Nat) :
    (halfPeriodSineRaw piApprox).compute stage =
      RealRaw.subCompute RealRaw.one
        (RotationSeries.rotationCosRaw (piApprox / 2)) stage := by
  rfl

theorem halfPeriodSineRaw_width_le_geometric (piApprox : Rat) (stage : Nat) :
    ((halfPeriodSineRaw piApprox).compute stage).width <=
      (8 * RotationSeries.rotationTailMagnitude (piApprox / 2) 0) *
        ((1 : Rat) / 2) ^ stage := by
  rw [halfPeriodSineRaw, RealRaw.sub_width]
  have hone : (RealRaw.one.compute stage).width = 0 := by
    simp [RealRaw.one, RealRaw.ofRat, RealRaw.ofRat_compute,
      QInterval.width]
    grind
  rw [hone, Rat.zero_add]
  exact RotationSeries.rotationCosRaw_width_le_geometric (piApprox / 2) stage

theorem halfPeriodSineRaw_reaches_of_positive_tolerance
    (piApprox : Rat) (eps : QPos) :
    ∃ stage : Nat, ((halfPeriodSineRaw piApprox).compute stage).width <= eps.val := by
  rcases (halfPeriodSineRaw_valid piApprox).2.2 eps with ⟨N, hN⟩
  exact ⟨N, hN N (Nat.le_refl N)⟩

theorem halfPeriodSineRaw_contains_halfAnglePrefix
    (piApprox : Rat) (stage : Nat) :
    ((halfPeriodSineRaw piApprox).compute (stage + 1)).ContainsInterval
      { lo := halfAnglePrefix piApprox
          (2 * (RotationSeries.rotationTailStart (piApprox / 2) + stage) + 1),
        hi := halfAnglePrefix piApprox
          (2 * (RotationSeries.rotationTailStart (piApprox / 2) + stage) + 1) } := by
  unfold halfPeriodSineRaw
  change (RealRaw.subCompute RealRaw.one
      (RotationSeries.rotationCosRaw (piApprox / 2)) (stage + 1)).ContainsInterval _
  unfold RealRaw.subCompute
  rw [RotationSeries.rotationCosRaw_compute]
  unfold QInterval.ContainsInterval
  have hprefix := halfAnglePrefix_cosine_complement piApprox
    (2 * (RotationSeries.rotationTailStart (piApprox / 2) + stage) + 1)
  rw [hprefix]
  rw [RotationSeries.cosinePrefix_eq_taylorPrefix]
  have hradius : 0 <= RotationSeries.rotationTailRadius
      (piApprox / 2) (stage + 1) := by
    unfold RotationSeries.rotationTailRadius
    unfold RotationSeries.rotationTailMagnitude
    exact Rat.mul_nonneg (by native_decide)
      (RationalMajorant.factorialTailTerm_nonneg
        (qabs_nonneg (piApprox / 2)) _)
  dsimp [RealRaw.one, RealRaw.ofRat]
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem halfAnglePrefix_rotation_complement (piApprox : Rat) (stage : Nat) :
    halfAnglePrefix piApprox (2 * stage + 1) =
      1 - LinearODE.RotationSystem.cosinePrefix
        (piApprox / 2) (stage + 1) := by
  rw [halfAnglePrefix_cosine_complement]
  rw [RotationSeries.cosinePrefix_eq_taylorPrefix]
  have hterms : 2 * stage + 1 + 1 = 2 * (stage + 1) := by omega
  rw [hterms]

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
