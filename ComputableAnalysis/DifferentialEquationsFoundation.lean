import ComputableAnalysis.Differential
import ComputableAnalysis.ScalarODEUniqueness
import ComputableAnalysis.PeanoBaker
import ComputableAnalysis.GeometricRotationODE
import ComputableAnalysis.RotationPeanoBakerBridge
import ComputableAnalysis.StableRotationDerivative
import ComputableAnalysis.RotationCalculus
import ComputableAnalysis.RotationDerivative
import ComputableAnalysis.FiniteRotationQuarterTurnExample

/-!
# Finite differential-equations foundation

This scoped entry point collects rational interval derivatives, scalar and
vector linear-ODE uniqueness, finite Peano--Baker products, and the concrete
rotation example.  It exposes finite trajectory certificates without
introducing a completed trajectory space.
-/

namespace ComputableAnalysis.LinearODE

/-! Public finite uniqueness and variation-of-constants entry points.  These
are the exact sampled statements used before a mesh/tail provider is added;
they quantify only over rational vectors and finite indices. -/
theorem effectiveDiscreteRecurrence_unique
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (candidate : Nat -> RatVector dimension)
    (hsolution : system.SolvesRecurrence initial candidate) :
    forall n, candidate n = system.trajectory initial n := by
  exact DiscreteLinearSystem.solvesRecurrence_eq_trajectory
    system initial candidate hsolution

theorem effectiveDiscreteVariationOfConstants
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (n : Nat) :
    system.trajectory initial n =
      vectorAdd
        (matrixApply (chronologicalStepProduct system.step 0 n) initial)
        (system.trajectory (vectorZero dimension) n) := by
  exact DiscreteLinearSystem.trajectory_eq_transition_add_zeroInitial
    system initial n

/-! The Duhamel form is the version consumed by an inhomogeneous ODE
provider: the finite forcing response is an explicit sum of transported
forcing samples. -/
theorem effectiveDiscreteVariationOfConstants_duhamel
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (n : Nat) :
    system.trajectory initial n =
      vectorAdd
        (matrixApply (chronologicalStepProduct system.step 0 n) initial)
        (DiscreteLinearSystem.duhamelSum system n) := by
  exact DiscreteLinearSystem.trajectory_eq_transition_add_duhamelSum
    system initial n

end ComputableAnalysis.LinearODE
