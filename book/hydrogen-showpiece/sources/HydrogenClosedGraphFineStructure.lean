import ComputableAnalysis.HydrogenOriginalClosedGraph
import ComputableAnalysis.HydrogenRegularGraphFineStructure

/-! Fine-structure inequalities attached to actual normalized nonzero
eigenpairs in the ORIGINAL compact-test closed relation. The witnesses are
the constructed physical hydrogen states, not eigenstates postulated from
the radical formula. Full self-adjointness and spectral exhaustion remain
separate from these existence and quantitative comparison theorems. -/
namespace ComputableAnalysis.HydrogenClosedGraphFineStructure
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions HydrogenRadialEnvelope
open ComputableCoefficient QuotientBridge HydrogenCoupling HydrogenCircularSolidSpinors
open CartesianSpinorCauchyFamily (Family Equivalent)
open CartesianSpinorCauchyPairing (squaredNorm)
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local irreducible] HydrogenPolynomialPhysicalEmbedding.source

def HasNormalizedEigenpair (alpha E : Value) : Prop := ∃ F : Family,
  CartesianCutoffGraphClosure.InGraph alpha F (CartesianSpinorCauchyRealScaling.scale E F) ∧
  (squaredNorm F).real.preferred.Equiv (RealRaw.ofRat 1) ∧
  ¬Equivalent F (CartesianSpinorCauchyFamily.constant [])

variable (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero)

/-- Actual physical witnesses for the two adjacent angular channels. -/
theorem levels (m : Nat) (hu : A.squared.preferred.Le (RealRaw.ofRat (1/4))) :
    HasNormalizedEigenpair (A.alpha hn) (HydrogenQuantizedParameters.energy (m+1) (Nat.zero_lt_succ m) 1 A) ∧
    HasNormalizedEigenpair (A.alpha hn) (HydrogenQuantizedParameters.energy (m+2) (Nat.zero_lt_succ (m+1)) 0 A) :=
  ⟨⟨HydrogenPolynomialPhysicalEmbedding.source .plus m 1 A hn (Or.inl (by decide +kernel)),
      HydrogenOriginalClosedGraph.eigenpair .plus m 1 A hn (Or.inl (by decide +kernel)) hu⟩,
    ⟨HydrogenPolynomialPhysicalEmbedding.source .minus (m+1) 0 A hn (Or.inr rfl),
      HydrogenOriginalClosedGraph.eigenpair .minus (m+1) 0 A hn (Or.inr rfl) hu⟩⟩

theorem gap_identity (m : Nat) :
    (HydrogenPolynomialSplitting.gap A (m+1) (Nat.zero_lt_succ m)).real.preferred.Equiv
      (Value.sub (HydrogenQuantizedParameters.energy (m+2) (Nat.zero_lt_succ (m+1)) 0 A)
        (HydrogenQuantizedParameters.energy (m+1) (Nat.zero_lt_succ m) 1 A)).real.preferred :=
  Value.equiv_refl _

theorem two_p (hu : A.squared.preferred.Le (RealRaw.ofRat (1/4))) :
    HasNormalizedEigenpair (A.alpha hn) (HydrogenQuantizedParameters.energy 1 (by decide +kernel) 1 A) ∧
    HasNormalizedEigenpair (A.alpha hn) (HydrogenQuantizedParameters.energy 2 (by decide +kernel) 0 A) ∧
    (Value.neg (HydrogenCircularRemainder.cubic A)).real.preferred.Le
      (HydrogenPolynomialSplitting.remainder A 1 (by decide +kernel) (1/32)).real.preferred ∧
    (HydrogenPolynomialSplitting.remainder A 1 (by decide +kernel) (1/32)).real.preferred.Le
      (HydrogenCircularRemainder.cubic A).real.preferred :=
  ⟨(levels A hn 0 hu).1,(levels A hn 0 hu).2,
    (HydrogenPolynomialSplitting.two_p_remainder_bound A hn hu).1,(HydrogenPolynomialSplitting.two_p_remainder_bound A hn hu).2⟩

theorem three_d (hu : A.squared.preferred.Le (RealRaw.ofRat (1/16))) :
    HasNormalizedEigenpair (A.alpha hn) (HydrogenQuantizedParameters.energy 2 (by decide +kernel) 1 A) ∧
    HasNormalizedEigenpair (A.alpha hn) (HydrogenQuantizedParameters.energy 3 (by decide +kernel) 0 A) ∧
    (Value.neg (Value.mul (Value.rational (1/64)) (HydrogenCircularRemainder.cubic A))).real.preferred.Le
      (HydrogenPolynomialSplitting.remainder A 2 (by decide +kernel) (1/324)).real.preferred ∧
    (HydrogenPolynomialSplitting.remainder A 2 (by decide +kernel) (1/324)).real.preferred.Le
      (Value.mul (Value.rational (1/64)) (HydrogenCircularRemainder.cubic A)).real.preferred := by
  have hA : A.squared.preferred.Le (RealRaw.ofRat (1/4)) :=
    RealRaw.le_trans (y:=RealRaw.ofRat (1/16)) (RealRaw.ofRat_valid _) hu
      (fun _ _=>by change (1:Rat)/16≤1/4;decide +kernel)
  exact ⟨(levels A hn 1 hA).1,(levels A hn 1 hA).2,
    (HydrogenPolynomialSplitting.three_remainder_bound A hn hu).1,(HydrogenPolynomialSplitting.three_remainder_bound A hn hu).2⟩

abbrev ratio := HydrogenRegularGraphFineStructure.ratio
abbrev ratioApproximation := HydrogenRegularGraphFineStructure.ratioApproximation

theorem ratio_remainder_bound (hu : A.squared.preferred.Le (RealRaw.ofRat (1/128))) :
    HasNormalizedEigenpair (A.alpha hn) (HydrogenQuantizedParameters.energy 1 (by decide +kernel) 1 A) ∧
    HasNormalizedEigenpair (A.alpha hn) (HydrogenQuantizedParameters.energy 2 (by decide +kernel) 0 A) ∧
    HasNormalizedEigenpair (A.alpha hn) (HydrogenQuantizedParameters.energy 2 (by decide +kernel) 1 A) ∧
    HasNormalizedEigenpair (A.alpha hn) (HydrogenQuantizedParameters.energy 3 (by decide +kernel) 0 A) ∧
    (Value.neg (Value.mul (Value.rational 8) A.value)).real.preferred.Le
      (Value.sub (ratio A hn) (Value.rational (8/81))).real.preferred ∧
    (Value.sub (ratio A hn) (Value.rational (8/81))).real.preferred.Le (Value.mul (Value.rational 8) A.value).real.preferred := by
  have hA : A.squared.preferred.Le (RealRaw.ofRat (1/4)) :=
    RealRaw.le_trans (y:=RealRaw.ofRat (1/128)) (RealRaw.ofRat_valid _) hu
      (fun _ _=>by change (1:Rat)/128≤1/4;decide +kernel)
  exact ⟨(levels A hn 0 hA).1,(levels A hn 0 hA).2,(levels A hn 1 hA).1,(levels A hn 1 hA).2,
    (HydrogenRegularGraphFineStructure.ratio_remainder_bound A hn hu).1,
    (HydrogenRegularGraphFineStructure.ratio_remainder_bound A hn hu).2⟩

theorem ratio_approximation_spec (eps : QPos) :
    (RealRaw.ofRat (ratioApproximation A eps).lo).Le (ratio A hn).real.preferred ∧
    (ratio A hn).real.preferred.Le (RealRaw.ofRat (ratioApproximation A eps).hi) ∧
    (ratioApproximation A eps).width≤eps.val :=
  HydrogenRegularGraphFineStructure.ratio_approximation_spec A hn eps

theorem ratio_names (B : Coupling) (hB : ¬B.squared.preferred.Equiv RealRaw.zero)
    (hAB : A.squared.preferred.Equiv B.squared.preferred) :
    (ratio A hn).real.preferred.Equiv (ratio B hB).real.preferred :=
  HydrogenRegularGraphFineStructure.ratio_names A B hn hB hAB

end ComputableAnalysis.HydrogenClosedGraphFineStructure
