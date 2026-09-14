import ComputableAnalysis.GeometricSineResidual
import ComputableAnalysis.ForwardEndpointApproximation
import ComputableAnalysis.SinPiIntegral

/-!
# Derivative of the existing geometric sin(pi*x) evaluator

The inverse certificate is the same data required to define the public sine
and cosine programs. No differentiability or trigonometric comparison is
assumed about it. Its certified forward equation is used with finite clock
and circle-coordinate estimates.
-/

namespace ComputableAnalysis
namespace GeometricSineDerivative

open ArctanGeometry IntegralIdentities SinPiIntegral
open GeometricRotationODE GeometricSineSecant

abbrev OnHalf (x : Rat) : Prop := 0 <= x ∧ x <= (1 : Rat)/2

private theorem doubled_in_quadrant {x : Rat} (hx : OnHalf x) :
    RationalCircle.GeometricTrig.firstQuadrantBranch (2*x) := by
  change 0 <= 2*x ∧ 2*x <= 1
  constructor
  · exact Rat.mul_nonneg (by decide) hx.1
  · have hm := Rat.mul_le_mul_of_nonneg_left hx.2 (by decide : (0 : Rat) <= 2)
    have hc : (2 : Rat)*(1/2)=1 := by decide +kernel
    rw [hc] at hm
    exact hm

def slope (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x) : RealRaw :=
  B.tangentAt (2*x) (doubled_in_quadrant hx)

theorem slope_valid (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x) :
    (slope B x hx).Valid := B.tangentAt_valid _ _

theorem slope_unit (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x)
    (n : Nat) : subintervalOf ((slope B x hx).compute n) 0 1 :=
  B.tangentAt_stays_in_unitSlope _ _ n

def angle (x : Rat) : RealRaw := RealRaw.scaleRat (x/2) piCircleArea

theorem angle_valid (x : Rat) : (angle x).Valid :=
  RealRaw.scaleRat_valid CauchyPi.piCircleArea_valid

private theorem branch_lower (B : ArctanInverseBisection) :
    B.branch.function.lower = 0 := B.branch_is_geometric.1

private theorem branch_upper (B : ArctanInverseBisection) :
    B.branch.function.upper = 1 := B.branch_is_geometric.2.1

private theorem branch_domain (B : ArctanInverseBisection) {u : Rat}
    (hu : inDomainInterval B.branch.function.lower B.branch.function.upper u) :
    0 <= u ∧ u <= 1 := by
  simpa only [inDomainInterval, branch_lower, branch_upper] using hu

/-- The forward equation for precisely the inverse used by the public sine. -/
theorem slope_forward_angle (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x) :
    (B.branch.continuous.applyRealRaw (slope B x hx) (slope_valid B x hx)
      (B.tangentAt_stays_in_source (2*x) (doubled_in_quadrant hx))).Equiv
        (angle x) := by
  let target := B.targetAt (2*x) (doubled_in_quadrant hx)
  have htarget : target.value.Equiv (angle x) := by
    have hscale : (2*x)/4 = x/2 := by
      simp only [Rat.div_def]
      grind
    simpa only [RationalCircle.GeometricTrig.halfQuarterTurnRaw, hscale, angle]
      using B.targetAt_halfQuarterTurn_equiv (2*x) (doubled_in_quadrant hx)
  exact RealRaw.equiv_trans
    (B.branch.continuous.applyRealRaw_valid (slope B x hx) (slope_valid B x hx)
      (B.tangentAt_stays_in_source (2*x) (doubled_in_quadrant hx)))
    target.value_valid (angle_valid x)
    (B.bisectionAt (2*x) (doubled_in_quadrant hx)).forward_equiv_target htarget

private theorem branch_point_equiv_rectangle
    (B : ArctanInverseBisection) (u : Rat)
    (hu : inDomainInterval B.branch.function.lower B.branch.function.upper u) :
    ({ compute := B.branch.function.compute u hu } : RealRaw).Equiv
      (arctanIntegralRectangleRaw u) := by
  have hug := branch_domain B hu
  have hP : ({ compute := B.branch.function.compute u hu } : RealRaw).Valid :=
    B.branch.function.valid_on u (B.branch.function.defined_on u hu)
  have hPG : ({ compute := B.branch.function.compute u hu } : RealRaw).Equiv
      (arctanGeom u) := B.branch_is_geometric.2.2 u hu hug
  exact RealRaw.equiv_trans hP (arctanGeom_valid_on_unit hug.1 hug.2)
    (arctanIntegralRectangleRaw_valid hug.1 hug.2) hPG
    (RealRaw.equiv_symm (arctanIntegralRectangleRaw_equiv_arctanGeom hug.1))

private theorem angle_contains_scaled
    {x p : Rat} (hx : OnHalf x) (n : Nat)
    (hp0 : (piCircleArea.compute n).lo <= p)
    (hp1 : p <= (piCircleArea.compute n).hi) :
    ((angle x).compute n).lo <= (x/2)*p ∧
      (x/2)*p <= ((angle x).compute n).hi := by
  have hscale : 0 <= x/2 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hx.1 (by decide +kernel)
  change (RealRaw.scaleRatCompute (x/2) piCircleArea n).lo <= _ ∧
    _ <= (RealRaw.scaleRatCompute (x/2) piCircleArea n).hi
  simp only [RealRaw.scaleRatCompute, if_pos hscale]
  exact ⟨Rat.mul_le_mul_of_nonneg_left hp0 hscale,
    Rat.mul_le_mul_of_nonneg_left hp1 hscale⟩

/-- Uniform over all rational points in a late inverse box and all selections
from the existing arctangent and pi outputs.  No runtime schedule is changed. -/
theorem slope_clock_close
    (B : ArctanInverseBisection) (x : Rat) (hx : OnHalf x) (eps : QPos) :
    ∃ N : Nat, ∀ n : Nat, N <= n -> ∀ u a p : Rat,
      ((slope B x hx).compute n).lo <= u ->
      u <= ((slope B x hx).compute n).hi ->
      (arctanIntegralRectangleCompute u n).lo <= a ->
      a <= (arctanIntegralRectangleCompute u n).hi ->
      (piCircleArea.compute n).lo <= p -> p <= (piCircleArea.compute n).hi ->
      qabs (a-(x/2)*p) <= eps.val := by
  have h := ForwardEndpointApproximation.eventually_close
    B.branch.continuous (slope B x hx) (slope_valid B x hx)
    (B.tangentAt_stays_in_source (2*x) (doubled_in_quadrant hx))
    (angle x) (angle_valid x) (slope_forward_angle B x hx)
    arctanIntegralRectangleRaw
    (fun u hu => let h := branch_domain B hu
                 arctanIntegralRectangleRaw_valid h.1 h.2)
    (branch_point_equiv_rectangle B)
    (by
      intro eps
      refine ⟨4*(eps.val.den+1), ?_⟩
      intro u hu n hn
      have hug := branch_domain B hu
      exact arctanIntegralRectangleCompute_width_le_eps_of_precision
        hug.1 hug.2 eps n hn) eps
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn u a p hu0 hu1 ha0 ha1 hp0 hp1
  have hscaled := angle_contains_scaled hx n hp0 hp1
  exact hN n hn u hu0 hu1 a ((x/2)*p) ha0 ha1 hscaled.1 hscaled.2

end GeometricSineDerivative
end ComputableAnalysis
