import ComputableAnalysis.HydrogenAnnularPhysicalGridDistance
import ComputableAnalysis.HydrogenAnnularCompletedGraph

/-! Physical identification of the ORIGINAL annular grid limits. Independent
physical integral/sampling constructions are compared with the original grids
in actual completed norm. Uniqueness then transfers the ORIGINAL compact-test
closed graph membership; the graph is not replaced by a physical image graph. -/
namespace ComputableAnalysis.HydrogenAnnularPhysicalGraph
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions HydrogenRadialEnvelope
open ComputableCoefficient QuotientBridge HydrogenCoupling HydrogenCircularSolidSpinors
open CartesianSpinorCauchyFamily (Family Equivalent)
open CartesianSpinorCauchyPairing (squaredDistance)
open FiniteCartesianVolume (content)
set_option autoImplicit false
set_option maxHeartbeats 4000000
attribute [local irreducible] HydrogenAnnularCubeSource.data HydrogenAnnularCubeSource.mass
  HydrogenAnnularCubeAction.data HydrogenAnnularCubeAction.mass

theorem distance_budget (R : QPos) (n : Nat) :
    content (HydrogenAnnularCubeSource.box R)*(8*(HydrogenAnnularGridConvergence.tolerance n).val*
      (HydrogenAnnularGridConvergence.tolerance n).val)≤
    HydrogenAnnularGridConvergence.errorRadius R n*HydrogenAnnularGridConvergence.errorRadius R n := by
  rw [HydrogenAnnularPhysicalGridDistance.box_eq R]
  let V:=content (HydrogenAnnularGlobalAccuracy.enclosingBox R)
  let a:=(HydrogenAnnularGridConvergence.tolerance n).val
  have hV : 0≤V := FiniteCartesianVolume.content_nonnegative _ (CartesianAnnularTargetSupport.enclosing_ordered R)
  have hVV:=Rat.mul_nonneg hV hV
  have hC : 8*V≤(8*(V+1))*(8*(V+1)) := by grind only
  have ha:=Rat.le_of_lt (HydrogenAnnularGridConvergence.tolerance n).property
  have hs:=Rat.mul_le_mul_of_nonneg_right hC (Rat.mul_nonneg ha ha)
  change V*(8*a*a)≤(8*(V+1)*a)*(8*(V+1)*a)
  grind only

variable (S : Side) (m N : Nat) (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero)
  (hN : 0<N ∨ S=Side.minus) (e R : QPos)

theorem source_grid_names : Equivalent
    (CartesianPhysicalEmbedding.state (HydrogenAnnularCubeSource.data S m N A hn e R))
    (HydrogenAnnularCompletedGraph.source S m N A hn e R) := by
  apply CartesianSpinorCauchyCompletionComparison.unique (HydrogenAnnularGridConvergence.sourceSequence S m N A hn e R)
    _ _ (HydrogenAnnularGridConvergence.errorRadius R) (HydrogenAnnularGridConvergence.errorRadius R)
    (HydrogenAnnularGridConvergence.errorRadius_shrinks R) (HydrogenAnnularGridConvergence.errorRadius_shrinks R)
    (HydrogenAnnularGridConvergence.errorRadius_nonnegative R) (HydrogenAnnularGridConvergence.errorRadius_nonnegative R)
  · intro n
    exact RealRaw.le_trans (y:=RealRaw.ofRat _) (RealRaw.ofRat_valid _)
      (HydrogenAnnularPhysicalGridDistance.source_bound S m N A hn e R (HydrogenAnnularGridConvergence.tolerance n))
      (fun _ _=>distance_budget R n)
  · exact HydrogenAnnularCompletedGraph.source_converges S m N A hn e R

theorem action_grid_names : Equivalent
    (CartesianPhysicalEmbedding.state (HydrogenAnnularCubeAction.data S m N A hn hN e R))
    (HydrogenAnnularCompletedGraph.action S m N A hn e R) := by
  apply CartesianSpinorCauchyCompletionComparison.unique (HydrogenAnnularGridConvergence.actionSequence S m N A hn e R)
    _ _ (HydrogenAnnularGridConvergence.errorRadius R) (HydrogenAnnularGridConvergence.errorRadius R)
    (HydrogenAnnularGridConvergence.errorRadius_shrinks R) (HydrogenAnnularGridConvergence.errorRadius_shrinks R)
    (HydrogenAnnularGridConvergence.errorRadius_nonnegative R) (HydrogenAnnularGridConvergence.errorRadius_nonnegative R)
  · intro n
    exact RealRaw.le_trans (y:=RealRaw.ofRat _) (RealRaw.ofRat_valid _)
      (HydrogenAnnularPhysicalGridDistance.action_bound S m N A hn hN e R (HydrogenAnnularGridConvergence.tolerance n))
      (fun _ _=>distance_budget R n)
  · exact HydrogenAnnularCompletedGraph.action_converges S m N A hn e R

theorem source_original_names : Equivalent (HydrogenAnnularCompletedGraph.source S m N A hn e R)
    (HydrogenAnnularSourcePhysicalSampling.state S m N A hn hN false e R) :=
  CartesianSpinorCauchyFamily.equivalent_trans
    (CartesianSpinorCauchyFamily.equivalent_symm (source_grid_names S m N A hn e R))
    (HydrogenAnnularCubeSource.physical_names S m N A hn hN e R)

theorem action_original_names : Equivalent (HydrogenAnnularCompletedGraph.action S m N A hn e R)
    (HydrogenAnnularActionPhysicalSampling.state S m N A hn hN false e R) :=
  CartesianSpinorCauchyFamily.equivalent_trans
    (CartesianSpinorCauchyFamily.equivalent_symm (action_grid_names S m N A hn hN e R))
    (HydrogenAnnularCubeAction.physical_names S m N A hn hN e R)

/-- The ORIGINAL physical annular source and independently differentiated
action belong to the ORIGINAL compact-test closed graph. -/
theorem in_closed_graph : CartesianCutoffGraphClosure.InGraph (A.alpha hn)
    (HydrogenAnnularSourcePhysicalSampling.state S m N A hn hN false e R)
    (HydrogenAnnularActionPhysicalSampling.state S m N A hn hN false e R) :=
  CartesianCutoffGraphClosure.names (A.alpha hn) (HydrogenAnnularCompletedGraph.in_closed_graph S m N A hn e R)
    (source_original_names S m N A hn hN e R) (action_original_names S m N A hn hN e R)

end ComputableAnalysis.HydrogenAnnularPhysicalGraph
