import ComputableAnalysis.CartesianDiracActionUnique
import ComputableAnalysis.HydrogenOriginalClosedGraph

/-! Uniqueness of the ORIGINAL closed Dirac action on the actual normalized
hydrogen states. The spectral energies retain their constructed differential
equation and graph-membership proofs. No self-adjointness or spectral
exhaustion is inferred from single-valuedness. -/
namespace ComputableAnalysis.HydrogenDiracActionUnique
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions HydrogenRadialEnvelope
open ComputableCoefficient QuotientBridge HydrogenCoupling HydrogenCircularSolidSpinors
open CartesianSpinorCauchyFamily (Family Equivalent)
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local irreducible] HydrogenPolynomialPhysicalEmbedding.source HydrogenPolynomialPhysicalEmbedding.action

variable (S : Side) (m N : Nat) (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero)
  (hN : 0<N ∨ S=Side.minus)

/-- Any original closed-graph action at an independently named hydrogen
source equals its independently differentiated physical Dirac action. -/
theorem differentiated_action (hA : A.squared.preferred.Le (RealRaw.ofRat (1/4)))
    {F G : Family} (hFG : CartesianCutoffGraphClosure.InGraph (A.alpha hn) F G)
    (hF : Equivalent F (HydrogenPolynomialPhysicalEmbedding.source S m N A hn hN)) :
    Equivalent G (HydrogenPolynomialPhysicalEmbedding.action S m N A hn hN) :=
  CartesianDiracActionUnique.equivalent_sources (A.alpha hn) hFG
    (HydrogenOriginalClosedGraph.in_closed_graph S m N A hn hN hA) hF

/-- The derived spectral energy determines the UNIQUE closed-graph action,
even when the source and action computations use independent names. -/
theorem energy_action (hA : A.squared.preferred.Le (RealRaw.ofRat (1/4)))
    {F G : Family} (hFG : CartesianCutoffGraphClosure.InGraph (A.alpha hn) F G)
    (hF : Equivalent F (HydrogenPolynomialPhysicalEmbedding.source S m N A hn hN)) :
    Equivalent G (CartesianSpinorCauchyRealScaling.scale (HydrogenPolynomialCartesian.energy m N A) F) :=
  CartesianSpinorCauchyFamily.equivalent_trans
    (CartesianDiracActionUnique.equivalent_sources (A.alpha hn) hFG
      (HydrogenOriginalClosedGraph.eigenpair S m N A hn hN hA).1 hF)
    (CartesianSpinorCauchyRealScaling.names _ _ _ _ (Value.equiv_refl _)
      (CartesianSpinorCauchyFamily.equivalent_symm hF))

include hN in
/-- Arbitrary justified samplers for the ACTUAL source and differentiated
action yield the same stationary eigenstate equation. Their graph membership
and source agreement are constructed, not supplied as target conclusions. -/
theorem independent_samplers (hA : A.squared.preferred.Le (RealRaw.ofRat (1/4)))
    {U V : CartesianSpinorSquareIntegral.Field} {I J : Value}
    (T : CartesianPhysicalSampling.Data U I) (P : CartesianPhysicalSampling.Data V J)
    (hU : ∀ X hX k,((HydrogenPolynomialCartesianGraph.field S m N A hn).values X hX k).val.Equiv (U X hX k).val)
    (hV : ∀ X hX k,(CartesianDiracGraph.action (A.alpha hn) (HydrogenPolynomialCartesianGraph.field S m N A hn) X hX k).val.Equiv (V X hX k).val) :
    Equivalent (CartesianPhysicalEmbedding.state P)
      (CartesianSpinorCauchyRealScaling.scale (HydrogenPolynomialCartesian.energy m N A)
        (CartesianPhysicalEmbedding.state T)) :=
  energy_action S m N A hn hN hA
    (HydrogenOriginalClosedGraph.independent_samplers S m N A hn hN hA T P hU hV)
    (CartesianSpinorCauchyFamily.equivalent_symm
      (HydrogenPolynomialPhysicalEmbedding.source_names S m N A hn hN T hU))

end ComputableAnalysis.HydrogenDiracActionUnique
