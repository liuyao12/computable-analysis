import ComputableAnalysis.HydrogenCircularBohrSpectrum

/-! Actual circular-state energy differences and their inverse-square
transition law with complete finite-coupling remainders. These are energy
positions; no emission probabilities or spectral completeness are asserted. -/
namespace ComputableAnalysis.HydrogenBohrTransitions
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
open ComputableCoefficient QuotientBridge HydrogenCoupling HydrogenCircularBohr HydrogenCircularBohrSpectrum
set_option autoImplicit false
set_option maxHeartbeats 2000000
local instance : Lean.Grind.CommRing ComplexRawQuotient.Value := ComplexRawQuotient.instCommRingValue
local instance (n : Nat) : OfNat ComplexRawQuotient.Value n :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).ofNat n

def gap (A : Coupling) (m n : Nat) (hm : 0<m) (hn : 0<n) : Value := Value.sub (energy A n hn) (energy A m hm)
def leadingGap (A : Coupling) (m n : Nat) : Value := Value.sub (leading A m) (leading A n)
def residual (A : Coupling) (m n : Nat) (hm : 0<m) (hn : 0<n) : Value := Value.sub (gap A m n hm hn) (leadingGap A m n)

theorem residual_identity (A : Coupling) (m n : Nat) (hm : 0<m) (hn : 0<n) :
    (residual A m n hm hn).real.preferred.Equiv (Value.sub (remainder A m hm) (remainder A n hn)).real.preferred := by
  apply raw_equiv_of_quotient_eq
  simp only [residual,gap,leadingGap,HydrogenCircularBohr.remainder,binding,quotient_sub]
  grind only

private theorem sub_order (a b c d : Value) (hab : a.real.preferred.Le b.real.preferred)
    (hcd : c.real.preferred.Le d.real.preferred) : (Value.sub a d).real.preferred.Le (Value.sub b c).real.preferred := by
  intro i j
  have h := RealRaw.le_sub_le_sub hab hcd i j
  change (a.real.compute i).lo-(d.real.compute i).hi≤(b.real.compute j).hi-(c.real.compute j).lo at h
  change (a.real.compute i).lo+ -(d.real.compute i).hi≤(b.real.compute j).hi+ -(c.real.compute j).lo
  simpa only [Rat.sub_eq_add_neg] using h

/-- Both separate level errors are retained. The signed interval is sharper
than replacing them by the sum of two absolute errors. -/
theorem residual_bounds (A : Coupling) (m n : Nat) (hm : 0<m) (hn : 0<n) :
    (Value.neg (errorBound A n)).real.preferred.Le (residual A m n hm hn).real.preferred ∧
      (residual A m n hm hn).real.preferred.Le (errorBound A m).real.preferred := by
  have hM := remainder_bounds A m hm
  have hN := remainder_bounds A n hn
  have hL := sub_order (Value.rational 0) (remainder A m hm) (remainder A n hn) (errorBound A n) hM.1 hN.2
  have hU := sub_order (remainder A m hm) (errorBound A m) (Value.rational 0) (remainder A n hn) hM.2 hN.1
  have hLeft : (Value.sub (Value.rational 0) (errorBound A n)).real.preferred.Equiv (Value.neg (errorBound A n)).real.preferred := by
    apply Value.equiv_of_samples _ _ 0
    intro j hj s hs
    exact Rat.zero_add _
  have hRight : (Value.sub (errorBound A m) (Value.rational 0)).real.preferred.Equiv (errorBound A m).real.preferred := by
    apply Value.equiv_of_samples _ _ 0
    intro j hj s hs
    change (errorBound A m).sample s+ -(0:Rat)=(errorBound A m).sample s
    simp only [Rat.neg_zero,Rat.add_zero]
  exact ⟨le_congr hLeft (RealRaw.equiv_symm (residual_identity A m n hm hn)) hL,
    le_congr (RealRaw.equiv_symm (residual_identity A m n hm hn)) hRight hU⟩

theorem leading_formula (A : Coupling) (m n : Nat) : (leadingGap A m n).real.preferred.Equiv
    (Value.mul (Value.rational (leadingCoefficient m-leadingCoefficient n)) A.value).real.preferred := by
  have h0 : (leadingGap A m n).real.preferred.Equiv
      (Value.sub (Value.mul (Value.rational (leadingCoefficient m)) A.value)
        (Value.mul (Value.rational (leadingCoefficient n)) A.value)).real.preferred := by
    apply raw_equiv_of_quotient_eq
    simp only [leadingGap,quotient_sub,quotient_eq (HydrogenCircularBohrSpectrum.leading_formula A m),
      quotient_eq (HydrogenCircularBohrSpectrum.leading_formula A n)]
  apply Value.equiv_trans h0
  apply Value.equiv_of_samples _ _ 0
  intro j hj s hs
  change leadingCoefficient m*A.value.sample s+ -(leadingCoefficient n*A.value.sample s)=
    (leadingCoefficient m-leadingCoefficient n)*A.value.sample s
  grind only

/-- Inverse-square transition energies with explicit global finite-coupling
bounds. Both principal indices are arbitrary positive natural numbers. -/
theorem transition_bounds (A : Coupling) (m n : Nat) (hm : 0<m) (hn : 0<n) :
    (Value.neg (Value.mul (Value.rational (errorCoefficient n)) (Value.mul A.value A.value))).real.preferred.Le
      (Value.sub (gap A m n hm hn) (Value.mul (Value.rational (leadingCoefficient m-leadingCoefficient n)) A.value)).real.preferred ∧
    (Value.sub (gap A m n hm hn) (Value.mul (Value.rational (leadingCoefficient m-leadingCoefficient n)) A.value)).real.preferred.Le
      (Value.mul (Value.rational (errorCoefficient m)) (Value.mul A.value A.value)).real.preferred := by
  have hR : (residual A m n hm hn).real.preferred.Equiv
      (Value.sub (gap A m n hm hn) (Value.mul (Value.rational (leadingCoefficient m-leadingCoefficient n)) A.value)).real.preferred := by
    apply raw_equiv_of_quotient_eq
    simp only [residual,quotient_sub,quotient_eq (leading_formula A m n)]
  have h := residual_bounds A m n hm hn
  exact ⟨le_congr (RationalLimits.neg_equiv (error_formula A n)) hR h.1,
    le_congr hR (error_formula A m) h.2⟩

/-- Actual regular radial eigenstates realize both endpoints of the gap. -/
theorem state_pair (A : Coupling) (m n : Nat) (hm : 0<m) (hn : 0<n)
    (hA : ¬A.squared.preferred.Equiv RealRaw.zero) :
    HydrogenRegularGraphSpectrum.HasEigenstate .minus m hm A hA (energy A m hm) ∧
      HydrogenRegularGraphSpectrum.HasEigenstate .minus n hn A hA (energy A n hn) :=
  ⟨has_eigenstate A m hm hA,has_eigenstate A n hn hA⟩

theorem gap_names (A B : Coupling) (m n : Nat) (hm : 0<m) (hn : 0<n)
    (hAB : A.squared.preferred.Equiv B.squared.preferred) :
    (gap A m n hm hn).real.preferred.Equiv (gap B m n hm hn).real.preferred := by
  apply raw_equiv_of_quotient_eq
  simp only [gap,quotient_sub,quotient_eq (energy_names A n hn B hAB),quotient_eq (energy_names A m hm B hAB)]

/-- Executable requested absolute-accuracy enclosure of the actual energy gap. -/
def approximation (A : Coupling) (m n : Nat) (hm : 0<m) (hn : 0<n) (eps : QPos) : QInterval :=
  let g := gap A m n hm hn
  g.real.compute (widthStageFrom g.real eps 0)

theorem approximation_spec (A : Coupling) (m n : Nat) (hm : 0<m) (hn : 0<n) (eps : QPos) :
    (RealRaw.ofRat (approximation A m n hm hn eps).lo).Le (gap A m n hm hn).real.preferred ∧
      (gap A m n hm hn).real.preferred.Le (RealRaw.ofRat (approximation A m n hm hn eps).hi) ∧
      (approximation A m n hm hn eps).width≤eps.val := by
  let g := gap A m n hm hn
  let N := widthStageFrom g.real eps 0
  exact ⟨(fun _ j => RealRaw.le_refl g.real.preferred g.real.valid N j),
    (fun i _ => RealRaw.le_refl g.real.preferred g.real.valid i N),(widthStageFrom_spec g.real eps 0).2⟩

end ComputableAnalysis.HydrogenBohrTransitions
