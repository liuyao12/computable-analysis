import ComputableAnalysis.HydrogenRegularIntegrableEnergy
import ComputableAnalysis.HydrogenRegularOrigin
import ComputableAnalysis.HydrogenPolynomialUnitRadial

/-! Exact positive-gap eigenstate classification for the stated regular
differentiable radial graph restriction. Eigenstates are defined by actual
functions, derivatives, boundary behavior, source/action square integrals
and the genuine Dirac equation, independently of any proposed energy list.
Completed-space self-adjoint operator and angular completeness are separate. -/
namespace ComputableAnalysis.HydrogenRegularGraphSpectrum
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions HydrogenRadialEnvelope
open ComputableCoefficient QuotientBridge HydrogenCoupling HydrogenCircularSolidSpinors RadialDiracOperator
set_option autoImplicit false
set_option maxHeartbeats 2000000
local instance regularGraphSpectrumRing : Lean.Grind.CommRing ComplexRawQuotient.Value := ComplexRawQuotient.instCommRingValue

def HasEigenstate (S : Side) (k : Nat) (hk : 0<k) (A : Coupling)
    (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (e : Value) : Prop :=
  ∃ U : Field,RadialDiracRegularIntegrabilityQuantization.Nontrivial U ∧
    HydrogenRadialGraph.RegularGraphDomain (A.alpha hn) (HydrogenPolynomialRadial.angular S k)
      (HydrogenQuantizedParameters.exponent k hk A) U ∧
    HydrogenRadialCartesian.Equations U (A.alpha hn) (HydrogenPolynomialRadial.angular S k) e

theorem equations_energy_names (alpha k e f : Value) (U : Field) (h : e.real.preferred.Equiv f.real.preferred)
    (hU : HydrogenRadialCartesian.Equations U alpha k e) : HydrogenRadialCartesian.Equations U alpha k f := by
  have he := quotient_eq h
  intro r hr
  have hG := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid r.property (U.slopes r hr 0).property)
    (hright := (HydrogenRadialLinear.firstRight alpha k e r (U.values r hr 0) (U.values r hr 1)).property) (hU r hr).1
  have hF := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid r.property (U.slopes r hr 1).property)
    (hright := (HydrogenRadialLinear.secondRight alpha k e r (U.values r hr 0) (U.values r hr 1)).property) (hU r hr).2
  change q r*q (U.slopes r hr 0)= -(quotient k*q (U.values r hr 0))+
    (quotient alpha+quotient (Value.add e (Value.rational 1))*q r)*q (U.values r hr 1) at hG
  change q r*q (U.slopes r hr 1)=quotient k*q (U.values r hr 1)-
    (quotient alpha+quotient (Value.sub e (Value.rational 1))*q r)*q (U.values r hr 0) at hF
  simp only [quotient_add,quotient_sub,quotient_one] at hG hF
  rw [he] at hG hF
  constructor
  · apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := mul_valid r.property (U.slopes r hr 0).property)
      (hright := (HydrogenRadialLinear.firstRight alpha k f r (U.values r hr 0) (U.values r hr 1)).property)
    change q r*q (U.slopes r hr 0)= -(quotient k*q (U.values r hr 0))+
      (quotient alpha+quotient (Value.add f (Value.rational 1))*q r)*q (U.values r hr 1)
    simpa only [quotient_add,quotient_one] using hG
  · apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := mul_valid r.property (U.slopes r hr 1).property)
      (hright := (HydrogenRadialLinear.secondRight alpha k f r (U.values r hr 0) (U.values r hr 1)).property)
    change q r*q (U.slopes r hr 1)=quotient k*q (U.values r hr 1)-
      (quotient alpha+quotient (Value.sub f (Value.rational 1))*q r)*q (U.values r hr 0)
    simpa only [quotient_sub,quotient_one] using hF

theorem energy_names (S : Side) (k : Nat) (hk : 0<k) (A : Coupling)
    (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (e f : Value) (h : e.real.preferred.Equiv f.real.preferred) :
    HasEigenstate S k hk A hn e ↔ HasEigenstate S k hk A hn f := by
  constructor
  · rintro ⟨U,hNZ,hDom,hU⟩
    exact ⟨U,hNZ,hDom,equations_energy_names _ _ _ _ U h hU⟩
  · rintro ⟨U,hNZ,hDom,hU⟩
    exact ⟨U,hNZ,hDom,equations_energy_names _ _ _ _ U (RealRaw.equiv_symm h) hU⟩

/-- A nontrivial actual eigenstate in the stated regular graph domain
has one of the admissible exact energy values. Origin vanishing, positive
decay, dispersion, quantization and degree are all derived. -/
theorem energy_of_eigenstate (S : Side) (k : Nat) (hk : 0<k) (A : Coupling)
    (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (e : Value) (he : e.real.preferred.Pos)
    (hGap : (HydrogenRegularIntegrableEnergy.gap e).real.preferred.Pos)
    (hState : HasEigenstate S k hk A hn e) :
    ∃ N : Nat,HydrogenRegularIntegrableEnergy.Admissible S N ∧
      e.real.preferred.Equiv (HydrogenQuantizedParameters.energy k hk N A).real.preferred := by
  obtain ⟨U,hNZ,hDom,hU⟩ := hState
  obtain ⟨I,hI⟩ := hDom.2.2.1
  obtain ⟨N,hN,hE,_⟩ := HydrogenRegularIntegrableEnergy.energy_of_square_integral S k hk A hn e he hGap U hU
    (HydrogenRegularOrigin.graph_vanishes _ _ _ U hDom) hNZ I hI
  exact ⟨N,hN,hE⟩

/-- The independent unit-normalized polynomial constructions provide a
genuine graph-domain eigenstate at every admissible degree, including the
negative-channel ground state. No norm or boundary role is assumed. -/
theorem eigenstate_of_degree (S : Side) (k : Nat) (hk : 0<k) (N : Nat) (A : Coupling)
    (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (hN : HydrogenRegularIntegrableEnergy.Admissible S N) :
    HasEigenstate S k hk A hn (HydrogenQuantizedParameters.energy k hk N A) := by
  let U := HydrogenPolynomialUnitRadial.field S k hk N A hn
  let P := HydrogenPolynomialUnitRadial.parameters S k hk N A hn
  have hNZ : RadialDiracRegularIntegrabilityQuantization.Nontrivial U := by
    obtain ⟨r,hr,hR⟩ := HydrogenPolynomialUnitRadial.nontrivial_rational S k hk N A hn
    refine ⟨rationalRadius r,rationalRadius_positive r hr,?_⟩
    intro hZero
    exact hR hZero.1
  refine ⟨U,hNZ,HydrogenPolynomialUnitRadial.mem_regularGraphDomain S k hk N A hn hN,?_⟩
  intro r hr
  exact RadialDiracPolynomialFunctions.equations P.exponent P.decay (A.alpha hn) (HydrogenPolynomialRadial.angular S k)
    (HydrogenQuantizedParameters.energy k hk N A) (fun j => (P.p j,P.q j)) P.degree
    (HydrogenPolynomialUnitRadial.packet S k hk N A hn hN) r hr

/-- Exact eigenstate classification on the positive energy gap for the
stated radial graph restriction. The energy list is a theorem, not part of
the eigenstate definition. -/
theorem eigenstate_iff (S : Side) (k : Nat) (hk : 0<k) (A : Coupling)
    (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (e : Value) (he : e.real.preferred.Pos)
    (hGap : (HydrogenRegularIntegrableEnergy.gap e).real.preferred.Pos) :
    HasEigenstate S k hk A hn e ↔ ∃ N : Nat,HydrogenRegularIntegrableEnergy.Admissible S N ∧
      e.real.preferred.Equiv (HydrogenQuantizedParameters.energy k hk N A).real.preferred := by
  constructor
  · exact energy_of_eigenstate S k hk A hn e he hGap
  · rintro ⟨N,hN,hE⟩
    exact (energy_names S k hk A hn e _ hE).2 (eigenstate_of_degree S k hk N A hn hN)

theorem coupling_names (S : Side) (k : Nat) (hk : 0<k) (A B : Coupling)
    (hA : ¬A.squared.preferred.Equiv RealRaw.zero) (hB : ¬B.squared.preferred.Equiv RealRaw.zero)
    (hAB : A.squared.preferred.Equiv B.squared.preferred) (e : Value) (he : e.real.preferred.Pos)
    (hGap : (HydrogenRegularIntegrableEnergy.gap e).real.preferred.Pos) :
    HasEigenstate S k hk A hA e ↔ HasEigenstate S k hk B hB e := by
  rw [eigenstate_iff S k hk A hA e he hGap,eigenstate_iff S k hk B hB e he hGap]
  constructor
  · rintro ⟨N,hN,hE⟩
    exact ⟨N,hN,Value.equiv_trans hE (HydrogenQuantizedParameters.energy_input_agreement k hk N A B hAB)⟩
  · rintro ⟨N,hN,hE⟩
    exact ⟨N,hN,Value.equiv_trans hE (HydrogenQuantizedParameters.energy_input_agreement k hk N B A (RealRaw.equiv_symm hAB))⟩

end ComputableAnalysis.HydrogenRegularGraphSpectrum
