import ComputableAnalysis.HydrogenRegularGraphSpectrum
import ComputableAnalysis.HydrogenPolynomialCartesian
import ComputableAnalysis.ComputableCoefficientErrorBounds

/-! The inverse-square binding-energy law for the constructed circular Dirac
states. Energies are dimensionless and the coupling is symbolic. Exact
identities precede the global finite-coupling remainder inequalities. -/
namespace ComputableAnalysis.HydrogenCircularBohr
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions HydrogenRadialEnvelope
open ComputableCoefficient QuotientBridge HydrogenCoupling HydrogenCircularComputations PositiveRootArithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
local instance : Lean.Grind.CommRing ComplexRawQuotient.Value := ComplexRawQuotient.instCommRingValue
local instance (n : Nat) : OfNat ComplexRawQuotient.Value n :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).ofNat n

variable (A : Coupling) (n : Nat) (hn : 0<n)

def inverse : Value := Value.rational (1/(n:Rat))
def energy : Value := Value.mul (exponent n hn A) (inverse n)
def scaledCoupling : Value := Value.mul A.value (Value.mul (inverse n) (inverse n))
def binding : Value := Value.sub (Value.rational 1) (energy A n hn)
def leading : Value := Value.mul (Value.rational (1/2)) (scaledCoupling A n)
def remainder : Value := Value.sub (binding A n hn) (leading A n)
def errorBound : Value := Value.mul (Value.rational (1/2)) (Value.mul (scaledCoupling A n) (scaledCoupling A n))

private theorem q_one : quotient (Value.rational 1)=(1 : ComplexRawQuotient.Value) := by
  apply ComplexRawQuotient.ofRaw_eq_ofRaw
  intro j
  apply (ComplexRaw.compareAt_overlap_iff _ _ j j).2
  simp [scalar,Value.rational,ComplexRaw.ofRealRaw,ComplexRaw.ofQComplex,
    QComplex.ofRat,QBox.Overlaps,QComplex.le_def]
  change (1:Rat)≤1 ∧ (1:Rat)≤1
  exact ⟨Rat.le_refl,Rat.le_refl⟩

private theorem inverse_positive (hn : 0<n) : (0:Rat)<1/(n:Rat) :=
  Rat.mul_pos (by decide +kernel) (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hn))

theorem inverse_identity (hn : 0<n) :
    (Value.mul (Value.rational (n:Rat)) (inverse n)).real.preferred.Equiv (RealRaw.ofRat 1) := by
  apply Value.equiv_of_samples _ (Value.rational 1) 0
  intro j hj s hs
  change (n:Rat)*(1/(n:Rat))=1
  rw [Rat.div_def,Rat.one_mul]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.mpr hn))

theorem energy_positive (j : Nat) : 0<((energy A n hn).real.compute j).lo := by
  cases n with
  | zero => omega
  | succ m => exact upper_energy_positive m A j

theorem energy_nonnegative : (RealRaw.ofRat 0).Le (energy A n hn).real.preferred :=
  Order.nonnegative_of_literal _ (fun j => Rat.le_of_lt (energy_positive A n hn j))

theorem energy_upper : (energy A n hn).real.preferred.Le (RealRaw.ofRat 1) := by
  intro i j
  have hE := exponent_upper n hn A i 0
  have hI := inverse_positive n hn
  have hM := Rat.mul_le_mul_of_nonneg_right hE (Rat.le_of_lt hI)
  have hUnit := Rat.mul_inv_cancel (n:Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr hn))
  change ((energy A n hn).real.compute i).lo≤1
  have hInv : ∀ k,0≤((inverse n).real.compute k).lo := fun _ => Rat.le_of_lt hI
  rw [energy,mul_compute_nonnegative (exponent n hn A) (inverse n) (exponent_nonnegative n hn A) hInv i]
  change ((exponent n hn A).real.compute i).lo*(1/(n:Rat))≤1
  change ((exponent n hn A).real.compute i).lo≤(n:Rat) at hE
  change ((exponent n hn A).real.compute i).lo*(1/(n:Rat))≤(n:Rat)*(1/(n:Rat)) at hM
  simpa only [Rat.div_def,Rat.one_mul,hUnit] using hM

/-- The positive constructed energy has square \(1-\alpha^2/n^2\).
This is the exact circular Dirac energy relation, derived from the indicial law. -/
theorem dispersion :
    (Value.add (Value.mul (energy A n hn) (energy A n hn)) (scaledCoupling A n)).real.preferred.Equiv
      (RealRaw.ofRat 1) := by
  have hE := quotient_eq (indicial n hn A)
  have hI := quotient_eq (y:=Value.rational 1) (inverse_identity n hn)
  apply raw_equiv_of_quotient_eq (y:=Value.rational 1)
  simp only [energy,scaledCoupling,quotient_add,quotient_mul,q_one] at hE hI ⊢
  change quotient (exponent n hn A)*quotient (exponent n hn A)+quotient A.value=
    quotient (Value.rational (n:Rat))*quotient (Value.rational (n:Rat)) at hE
  grind only

theorem scaled_nonnegative (hn : 0<n) : (RealRaw.ofRat 0).Le (scaledCoupling A n).real.preferred :=
  Order.mul_nonnegative A.value (Value.mul (inverse n) (inverse n))
    (Order.nonnegative_of_literal _ (fun j => (A.bounded_interval j).1))
    (Order.mul_nonnegative (inverse n) (inverse n)
      (fun _ _ => Rat.le_of_lt (inverse_positive n hn)) (fun _ _ => Rat.le_of_lt (inverse_positive n hn)))

theorem binding_nonnegative : (RealRaw.ofRat 0).Le (binding A n hn).real.preferred := by
  intro i j
  have h := energy_upper A n hn j 0
  change ((energy A n hn).real.compute j).lo≤1 at h
  change (0:Rat)≤1+ -((energy A n hn).real.compute j).lo
  grind only

theorem binding_decomposition :
    (Value.add (binding A n hn) (Value.mul (energy A n hn) (binding A n hn))).real.preferred.Equiv
      (scaledCoupling A n).real.preferred := by
  have h := quotient_eq (y:=Value.rational 1) (dispersion A n hn)
  apply raw_equiv_of_quotient_eq
  simp only [binding,quotient_add,quotient_sub,quotient_mul,q_one] at h ⊢
  grind only

theorem binding_upper : (binding A n hn).real.preferred.Le (scaledCoupling A n).real.preferred := by
  have hp := Order.mul_nonnegative (energy A n hn) (binding A n hn)
    (energy_nonnegative A n hn) (binding_nonnegative A n hn)
  have h := RealRaw.le_add_le_add (RealRaw.le_refl (binding A n hn).real.preferred (binding A n hn).real.valid) hp
  have h0 : (Value.add (binding A n hn) (Value.rational 0)).real.preferred.Equiv (binding A n hn).real.preferred := by
    apply Value.equiv_of_samples _ _ 0
    intro j hj s hs
    exact Rat.add_zero _
  exact le_congr h0 (binding_decomposition A n hn) h

/-- Exact algebraic remainder: the error in the inverse-square leading
term is one half of the squared actual binding energy. -/
theorem remainder_identity : (remainder A n hn).real.preferred.Equiv
    (Value.mul (Value.rational (1/2)) (Value.mul (binding A n hn) (binding A n hn))).real.preferred := by
  have hSquare : (Value.sub (Value.add (binding A n hn) (binding A n hn)) (scaledCoupling A n)).real.preferred.Equiv
      (Value.mul (binding A n hn) (binding A n hn)).real.preferred := by
    have hd := quotient_eq (y:=Value.rational 1) (dispersion A n hn)
    apply raw_equiv_of_quotient_eq
    simp only [binding,quotient_add,quotient_sub,quotient_mul,q_one] at hd ⊢
    grind only
  have hHalf : (remainder A n hn).real.preferred.Equiv
      (Value.mul (Value.rational (1/2))
        (Value.sub (Value.add (binding A n hn) (binding A n hn)) (scaledCoupling A n))).real.preferred := by
    apply Value.equiv_of_samples _ _ 0
    intro j hj s hs
    change (binding A n hn).sample s+ -((1/2:Rat)*(scaledCoupling A n).sample s)=
      (1/2:Rat)*((binding A n hn).sample s+(binding A n hn).sample s+ -(scaledCoupling A n).sample s)
    grind only [Rat.div_def]
  exact Value.equiv_trans hHalf (Value.mul_congr (Value.equiv_refl (Value.rational (1/2))) hSquare)

/-- Global finite-coupling inverse-square error bound; no auxiliary rational
coupling cap, truncation schedule or expansion premise is supplied. -/
theorem remainder_bounds : (RealRaw.ofRat 0).Le (remainder A n hn).real.preferred ∧
    (remainder A n hn).real.preferred.Le (errorBound A n).real.preferred := by
  have hb := binding_nonnegative A n hn
  have hx := scaled_nonnegative A n hn
  have hh : (RealRaw.ofRat 0).Le (Value.rational (1/2)).real.preferred := fun _ _ => by change (0:Rat)≤1/2;decide +kernel
  have hNN := Order.mul_nonnegative (Value.rational (1/2)) (Value.mul (binding A n hn) (binding A n hn)) hh
    (Order.mul_nonnegative _ _ hb hb)
  have hSq := Order.mul_mono_nonnegative (binding A n hn) (scaledCoupling A n) (binding A n hn) (scaledCoupling A n)
    hb hx hb hx (binding_upper A n hn) (binding_upper A n hn)
  have hU := Order.mul_mono_left (Value.rational (1/2)) _ _ hh hSq
  exact ⟨le_congr (Value.equiv_refl (Value.rational 0)) (RealRaw.equiv_symm (remainder_identity A n hn)) hNN,
    le_congr (RealRaw.equiv_symm (remainder_identity A n hn)) (Value.equiv_refl (errorBound A n)) hU⟩

/-- The energy is that of an actual constructed regular radial Dirac
state, rather than a formula imposed as a spectral assumption. -/
theorem quantized_agreement (hA : ¬A.squared.preferred.Equiv RealRaw.zero) :
    (energy A n hn).real.preferred.Equiv (HydrogenQuantizedParameters.energy n hn 0 A).real.preferred := by
  cases n with
  | zero => omega
  | succ m => exact RealRaw.equiv_symm (HydrogenQuantizedParameters.degree_zero_agreement A m hA)

theorem has_eigenstate (hA : ¬A.squared.preferred.Equiv RealRaw.zero) :
    HydrogenRegularGraphSpectrum.HasEigenstate .minus n hn A hA (energy A n hn) :=
  (HydrogenRegularGraphSpectrum.energy_names .minus n hn A hA (energy A n hn)
    (HydrogenQuantizedParameters.energy n hn 0 A) (quantized_agreement A n hn hA)).2
    (HydrogenRegularGraphSpectrum.eigenstate_of_degree .minus n hn 0 A hA (Or.inr rfl))

theorem energy_names (B : Coupling) (hAB : A.squared.preferred.Equiv B.squared.preferred) :
    (energy A n hn).real.preferred.Equiv (energy B n hn).real.preferred :=
  Value.mul_congr (exponent_congr n hn A B hAB) (Value.equiv_refl (inverse n))

end ComputableAnalysis.HydrogenCircularBohr
