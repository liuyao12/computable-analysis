import ComputableAnalysis.HydrogenAnnularPhysicalGraph
import ComputableAnalysis.HydrogenAnnularActionDistance

/-! Remove both computed annular cutoffs in the ORIGINAL compact-test
closed Dirac graph. The true source/action distance estimates and the proved
physical/grid identification supply every approximation. The resulting
nonzero normalized eigenpairs use the previously derived energies; no
self-adjointness or unrestricted spectral classification is assumed. -/
namespace ComputableAnalysis.HydrogenOriginalClosedGraph
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions HydrogenRadialEnvelope
open ComputableCoefficient QuotientBridge HydrogenCoupling HydrogenCircularSolidSpinors
open CartesianSpinorCauchyFamily (Family Equivalent)
open CartesianSpinorCauchyPairing (squaredDistance squaredNorm)
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local irreducible] HydrogenPolynomialPhysicalEmbedding.source HydrogenPolynomialPhysicalEmbedding.action
  HydrogenAnnularSourcePhysicalSampling.state HydrogenAnnularActionPhysicalSampling.state

variable (S : Side) (m N : Nat) (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero)
  (hN : 0<N ∨ S=Side.minus)

/-- The tolerance is an actual squared norm budget, not an unproved
interpretation of a pointwise cutoff error. -/
def tolerance (n : Nat) : QPos :=
  ⟨RawLimit.allowance n*RawLimit.allowance n,Rat.mul_pos (RawLimit.allowance_pos n) (RawLimit.allowance_pos n)⟩
def innerRadius (n : Nat) : QPos := HydrogenJointAnnularActionApproximation.innerRadius S m N A hn (tolerance n)
def outerRadius (n : Nat) : QPos := HydrogenJointAnnularActionApproximation.outerRadius S m N A hn (tolerance n)
def annularSource (n : Nat) : Family := HydrogenAnnularSourcePhysicalSampling.state S m N A hn hN false
  (innerRadius S m N A hn n) (outerRadius S m N A hn n)
def annularAction (n : Nat) : Family := HydrogenAnnularActionPhysicalSampling.state S m N A hn hN false
  (innerRadius S m N A hn n) (outerRadius S m N A hn n)

theorem annular_in_graph (n : Nat) : CartesianCutoffGraphClosure.InGraph (A.alpha hn)
    (annularSource S m N A hn hN n) (annularAction S m N A hn hN n) :=
  HydrogenAnnularPhysicalGraph.in_closed_graph S m N A hn hN (innerRadius S m N A hn n) (outerRadius S m N A hn n)

theorem source_distance (hA : A.squared.preferred.Le (RealRaw.ofRat (1/4))) (n : Nat) :
    (squaredDistance (annularSource S m N A hn hN n) (HydrogenPolynomialPhysicalEmbedding.source S m N A hn hN)).real.preferred.Le
      (RealRaw.ofRat (RawLimit.allowance n*RawLimit.allowance n)) :=
  le_congr (CartesianSpinorCauchyTriangle.symmetric _ _) (Value.equiv_refl (Value.rational _))
    (HydrogenAnnularActionDistance.requested_joint_distance S m N A hn hN hA (tolerance n)).1

theorem action_distance (hA : A.squared.preferred.Le (RealRaw.ofRat (1/4))) (n : Nat) :
    (squaredDistance (annularAction S m N A hn hN n) (HydrogenPolynomialPhysicalEmbedding.action S m N A hn hN)).real.preferred.Le
      (RealRaw.ofRat (RawLimit.allowance n*RawLimit.allowance n)) :=
  le_congr (CartesianSpinorCauchyTriangle.symmetric _ _) (Value.equiv_refl (Value.rational _))
    (HydrogenAnnularActionDistance.requested_joint_distance S m N A hn hN hA (tolerance n)).2

/-- The original noncompact physical source and its ORIGINAL differentiated
action lie in the original norm-closed compact-test relation. -/
theorem in_closed_graph (hA : A.squared.preferred.Le (RealRaw.ofRat (1/4))) :
    CartesianCutoffGraphClosure.InGraph (A.alpha hn) (HydrogenPolynomialPhysicalEmbedding.source S m N A hn hN)
      (HydrogenPolynomialPhysicalEmbedding.action S m N A hn hN) :=
  CartesianCutoffGraphClosure.closed (A.alpha hn) _ _ (annularSource S m N A hn hN) (annularAction S m N A hn hN)
    RawLimit.allowance (fun n=>Rat.le_of_lt (RawLimit.allowance_pos n)) RawLimit.allowance_shrinks
    (annular_in_graph S m N A hn hN) (source_distance S m N A hn hN hA) (action_distance S m N A hn hN hA)

/-- An actual normalized nonzero eigenpair in the ORIGINAL closed relation.
The energy and differential equation were constructed independently, and
the graph membership above is obtained from genuine original test pairs. -/
theorem eigenpair (hA : A.squared.preferred.Le (RealRaw.ofRat (1/4))) :
    CartesianCutoffGraphClosure.InGraph (A.alpha hn) (HydrogenPolynomialPhysicalEmbedding.source S m N A hn hN)
      (CartesianSpinorCauchyRealScaling.scale (HydrogenPolynomialCartesian.energy m N A)
        (HydrogenPolynomialPhysicalEmbedding.source S m N A hn hN)) ∧
    (squaredNorm (HydrogenPolynomialPhysicalEmbedding.source S m N A hn hN)).real.preferred.Equiv (RealRaw.ofRat 1) ∧
    ¬Equivalent (HydrogenPolynomialPhysicalEmbedding.source S m N A hn hN) (CartesianSpinorCauchyFamily.constant []) :=
  ⟨CartesianCutoffGraphClosure.names (A.alpha hn) (in_closed_graph S m N A hn hN hA)
      (CartesianSpinorCauchyFamily.equivalent_refl _) (HydrogenPolynomialPhysicalEmbedding.equation S m N A hn hN),
    HydrogenPolynomialPhysicalEmbedding.norm_one S m N A hn hN,HydrogenPolynomialPhysicalEmbedding.nonzero S m N A hn hN⟩

include hN in
theorem independent_samplers (hA : A.squared.preferred.Le (RealRaw.ofRat (1/4)))
    {U V : CartesianSpinorSquareIntegral.Field} {I J : Value}
    (T : CartesianPhysicalSampling.Data U I) (P : CartesianPhysicalSampling.Data V J)
    (hU : ∀ X hX k,((HydrogenPolynomialCartesianGraph.field S m N A hn).values X hX k).val.Equiv (U X hX k).val)
    (hV : ∀ X hX k,(CartesianDiracGraph.action (A.alpha hn) (HydrogenPolynomialCartesianGraph.field S m N A hn) X hX k).val.Equiv (V X hX k).val) :
    CartesianCutoffGraphClosure.InGraph (A.alpha hn) (CartesianPhysicalEmbedding.state T) (CartesianPhysicalEmbedding.state P) :=
  CartesianCutoffGraphClosure.names (A.alpha hn) (in_closed_graph S m N A hn hN hA)
    (HydrogenPolynomialPhysicalEmbedding.source_names S m N A hn hN T hU)
    (HydrogenPolynomialPhysicalEmbedding.action_names S m N A hn hN P hV)

end ComputableAnalysis.HydrogenOriginalClosedGraph
