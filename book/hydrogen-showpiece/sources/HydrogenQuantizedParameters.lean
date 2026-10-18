import ComputableAnalysis.HydrogenCircularComputations
import ComputableAnalysis.ComputableCoefficientPositiveSquareUnique
import ComputableAnalysis.HydrogenCircularNormAgreement

/-! Computed Dirac--Coulomb parameters at arbitrary radial degree. Square
roots and reciprocals are constructed from the symbolic coupling. Dispersion
and quantization are proved consequences, and their positive-energy solution
is unique. No experimental constants or assumed spectral formula occur. -/
namespace ComputableAnalysis.HydrogenQuantizedParameters
open ComputableCoefficient QuotientBridge PositiveRootArithmetic HydrogenCoupling
set_option autoImplicit false
set_option maxHeartbeats 1000000
local instance quantizedRing : Lean.Grind.CommRing ComplexRawQuotient.Value := ComplexRawQuotient.instCommRingValue
local instance quantizedHPow : HPow ComplexRawQuotient.Value Nat ComplexRawQuotient.Value :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).npow
local instance quantizedOfNat (n : Nat) : OfNat ComplexRawQuotient.Value n :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).ofNat n
local instance quantizedNatCast : NatCast ComplexRawQuotient.Value :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).natCast

variable (k : Nat) (hk : 0<k) (N : Nat) (A : Coupling)

abbrev exponent := HydrogenCircularComputations.exponent

def shifted : Value := Value.add (Value.rational (N:Rat)) (exponent k hk A)
theorem shifted_positive (n : Nat) : 0<((shifted k hk N A).real.compute n).lo := by
  have hs := HydrogenCircularComputations.exponent_positive k hk A n
  have hN : (0:Rat)≤(N:Rat) := Rat.natCast_nonneg
  change 0<(N:Rat)+((exponent k hk A).real.compute n).lo
  grind only

def denominatorSquared : Value := Value.add (Value.mul (shifted k hk N A) (shifted k hk N A)) A.value
theorem denominator_squared_positive : (denominatorSquared k hk N A).real.preferred.Pos := by
  refine ⟨0,?_⟩
  change 0<((Value.mul (shifted k hk N A) (shifted k hk N A)).real.compute 0).lo+(A.value.real.compute 0).lo
  rw [mul_compute_nonnegative _ _ (fun n => Rat.le_of_lt (shifted_positive k hk N A n))
    (fun n => Rat.le_of_lt (shifted_positive k hk N A n)) 0]
  have ht := Rat.mul_pos (shifted_positive k hk N A 0) (shifted_positive k hk N A 0)
  have hu := (A.bounded_interval 0).1
  change 0≤(A.value.real.compute 0).lo at hu
  grind only

def denominator : Value := fromPositive (denominatorSquared k hk N A) (denominator_squared_positive k hk N A)
theorem denominator_positive (n : Nat) : 0<((denominator k hk N A).real.compute n).lo := fromPositive_positive _ _ n
def inverse : Value := Value.positiveInv (denominator k hk N A) 0 (denominator_positive k hk N A 0)
theorem inverse_positive (n : Nat) : 0<((inverse k hk N A).real.compute n).lo :=
  Order.positiveInv_zero_positive _ (denominator_positive k hk N A 0) n

def energy : Value := Value.mul (shifted k hk N A) (inverse k hk N A)
def decay (hn : ¬A.squared.preferred.Equiv RealRaw.zero) : Value := Value.mul (A.alpha hn) (inverse k hk N A)

theorem energy_positive (n : Nat) : 0<((energy k hk N A).real.compute n).lo := by
  change 0<((Value.mul (shifted k hk N A) (inverse k hk N A)).real.compute n).lo
  rw [mul_compute_nonnegative _ _ (fun n => Rat.le_of_lt (shifted_positive k hk N A n))
    (fun n => Rat.le_of_lt (inverse_positive k hk N A n)) n]
  exact Rat.mul_pos (shifted_positive k hk N A n) (inverse_positive k hk N A n)

theorem decay_positive (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (n : Nat) :
    0<((decay k hk N A hn).real.compute n).lo := by
  change 0<((Value.mul (A.alpha hn) (inverse k hk N A)).real.compute n).lo
  rw [mul_compute_nonnegative _ _ (fun n => Rat.le_of_lt (A.alpha_positive hn n))
    (fun n => Rat.le_of_lt (inverse_positive k hk N A n)) n]
  exact Rat.mul_pos (A.alpha_positive hn n) (inverse_positive k hk N A n)

theorem denominator_square : (Value.mul (denominator k hk N A) (denominator k hk N A)).real.preferred.Equiv
    (denominatorSquared k hk N A).real.preferred := fromPositive_square _ _

theorem inverse_square_identity : (Value.mul (denominatorSquared k hk N A)
    (Value.mul (inverse k hk N A) (inverse k hk N A))).real.preferred.Equiv (RealRaw.ofRat 1) := by
  have hs := quotient_eq (denominator_square k hk N A)
  have hi := quotient_eq (y := Value.rational 1) (positiveInv_identity (denominator k hk N A) 0 (denominator_positive k hk N A 0))
  simp only [quotient_mul,quotient_one] at hs hi
  change quotient (denominator k hk N A)*quotient (inverse k hk N A)=1 at hi
  have h := congrArg (fun z : ComplexRawQuotient.Value => z*z) hi
  apply raw_equiv_of_quotient_eq (y := Value.rational 1)
  simp only [quotient_mul,quotient_one]
  rw [←hs]
  grind only

theorem laws (hn : ¬A.squared.preferred.Equiv RealRaw.zero) :
    (Value.add (Value.mul (decay k hk N A hn) (decay k hk N A hn))
      (Value.mul (energy k hk N A) (energy k hk N A))).real.preferred.Equiv (RealRaw.ofRat 1) ∧
    (Value.mul (decay k hk N A hn) (shifted k hk N A)).real.preferred.Equiv
      (Value.mul (A.alpha hn) (energy k hk N A)).real.preferred := by
  have hi := quotient_eq (y := Value.rational 1) (inverse_square_identity k hk N A)
  have ha := quotient_eq (A.alpha_square hn)
  simp only [denominatorSquared,quotient_mul,quotient_add,quotient_one] at hi ha
  constructor
  · apply raw_equiv_of_quotient_eq (y := Value.rational 1)
    simp only [decay,energy,quotient_mul,quotient_add,quotient_one]
    grind only
  · apply raw_equiv_of_quotient_eq
    simp only [decay,energy,quotient_mul]
    grind only

theorem energy_weighted_square : (Value.mul (Value.mul (energy k hk N A) (energy k hk N A))
    (denominatorSquared k hk N A)).real.preferred.Equiv
      (Value.mul (shifted k hk N A) (shifted k hk N A)).real.preferred := by
  have hi := quotient_eq (y := Value.rational 1) (inverse_square_identity k hk N A)
  simp only [quotient_mul,quotient_one] at hi
  apply raw_equiv_of_quotient_eq
  simp only [energy,quotient_mul]
  grind only

/-- Positive dispersion and quantization laws determine the energy value;
the closed-form computation is a conclusion of these laws. -/
theorem energy_unique (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (e l : Value)
    (he : e.real.preferred.Pos)
    (hD : (Value.add (Value.mul l l) (Value.mul e e)).real.preferred.Equiv (RealRaw.ofRat 1))
    (hQ : (Value.mul l (shifted k hk N A)).real.preferred.Equiv (Value.mul (A.alpha hn) e).real.preferred) :
    e.real.preferred.Equiv (energy k hk N A).real.preferred := by
  have hd := quotient_eq (y := Value.rational 1) hD
  have hq := quotient_eq hQ
  have ha := quotient_eq (A.alpha_square hn)
  have hi := quotient_eq (y := Value.rational 1) (inverse_square_identity k hk N A)
  simp only [quotient_add,quotient_mul,quotient_one] at hd hq ha
  simp only [denominatorSquared,quotient_add,quotient_mul,quotient_one] at hi
  have hSq : (Value.mul e e).real.preferred.Equiv
      (Value.mul (energy k hk N A) (energy k hk N A)).real.preferred := by
    apply raw_equiv_of_quotient_eq
    simp only [energy,quotient_mul]
    have hCross := congrArg (fun z : ComplexRawQuotient.Value => z*z) hq
    grind only
  obtain ⟨n,hn'⟩ := he
  apply PositiveSquareUnique.unique e (energy k hk N A) n _ hSq
  have hp := energy_positive k hk N A n
  change 0<(e.real.compute n).lo+((energy k hk N A).real.compute n).lo
  change 0<(e.real.compute n).lo at hn'
  grind only

theorem energy_input_agreement (B : Coupling) (hAB : A.squared.preferred.Equiv B.squared.preferred) :
    (energy k hk N A).real.preferred.Equiv (energy k hk N B).real.preferred := by
  have hs := add_congr (Value.equiv_refl (Value.rational (N:Rat))) (HydrogenCircularComputations.exponent_congr k hk A B hAB)
  have hd := add_congr (Value.mul_congr hs hs) (A.value_equiv B hAB)
  have hr := fromPositive_equiv _ _ (denominator_squared_positive k hk N A) (denominator_squared_positive k hk N B) hd
  exact Value.mul_congr hs (positiveInv_congr hr 0 0 (denominator_positive k hk N A 0) (denominator_positive k hk N B 0))

theorem inverse_input_agreement (B : Coupling) (hAB : A.squared.preferred.Equiv B.squared.preferred) :
    (inverse k hk N A).real.preferred.Equiv (inverse k hk N B).real.preferred := by
  have hs := add_congr (Value.equiv_refl (Value.rational (N:Rat))) (HydrogenCircularComputations.exponent_congr k hk A B hAB)
  have hd := add_congr (Value.mul_congr hs hs) (A.value_equiv B hAB)
  have hr := fromPositive_equiv _ _ (denominator_squared_positive k hk N A) (denominator_squared_positive k hk N B) hd
  exact positiveInv_congr hr 0 0 (denominator_positive k hk N A 0) (denominator_positive k hk N B 0)

theorem decay_input_agreement (hn : ¬A.squared.preferred.Equiv RealRaw.zero)
    (B : Coupling) (hB : ¬B.squared.preferred.Equiv RealRaw.zero)
    (hAB : A.squared.preferred.Equiv B.squared.preferred) :
    (decay k hk N A hn).real.preferred.Equiv (decay k hk N B hB).real.preferred :=
  Value.mul_congr (HydrogenCircularNorm.alpha_agreement A B hn hB hAB) (inverse_input_agreement k hk N A B hAB)

/-- The previous degree-one circular energy is the same exact computation. -/
theorem degree_one_agreement : (energy k hk 1 A).real.preferred.Equiv
    (HydrogenCircularComputations.lowerEnergy k hk A).real.preferred := by
  have hShift : (shifted k hk 1 A).real.preferred.Equiv (HydrogenCircularComputations.shifted k hk A).real.preferred := by
    apply raw_equiv_of_quotient_eq
    have hOne : quotient (Value.rational ((1:Nat):Rat))=1 := rfl
    simp only [shifted,HydrogenCircularComputations.shifted,quotient_add,quotient_one,hOne]
    grind only
  have hDen : (denominatorSquared k hk 1 A).real.preferred.Equiv (HydrogenCircularComputations.denominatorSquared k hk A).real.preferred :=
    add_congr (Value.mul_congr hShift hShift) (Value.equiv_refl A.value)
  have hr := fromPositive_equiv _ _ (denominator_squared_positive k hk 1 A)
    (HydrogenCircularComputations.denominator_squared_positive k hk A) hDen
  exact Value.mul_congr hShift (positiveInv_congr hr 0 0 (denominator_positive k hk 1 A 0)
    (HydrogenCircularComputations.denominator_positive k hk A 0))

theorem degree_zero_agreement (j : Nat) (hn : ¬A.squared.preferred.Equiv RealRaw.zero) :
    (energy (j+1) (Nat.zero_lt_succ j) 0 A).real.preferred.Equiv
      (HydrogenCircularComputations.upperEnergy j A).real.preferred := by
  have hL := HydrogenCircularComputations.upper_laws j A hn
  have hShift : (shifted (j+1) (Nat.zero_lt_succ j) 0 A).real.preferred.Equiv (exponent (j+1) (Nat.zero_lt_succ j) A).real.preferred := by
    apply raw_equiv_of_quotient_eq
    have hz : quotient (Value.rational ((0:Nat):Rat))=0 := rfl
    simp only [shifted,quotient_add,hz]
    grind only
  have hQ := Value.mul_congr (Value.equiv_refl (HydrogenCircularComputations.upperDecay j A hn)) hShift
  have hQuant := RealRaw.equiv_trans
    (Value.mul (HydrogenCircularComputations.upperDecay j A hn) (shifted (j+1) (Nat.zero_lt_succ j) 0 A)).real.valid
    (Value.mul (HydrogenCircularComputations.upperDecay j A hn) (exponent (j+1) (Nat.zero_lt_succ j) A)).real.valid
    (Value.mul (A.alpha hn) (HydrogenCircularComputations.upperEnergy j A)).real.valid hQ hL.2
  exact RealRaw.equiv_symm (energy_unique (j+1) (Nat.zero_lt_succ j) 0 A hn _ _
    ⟨0,HydrogenCircularComputations.upper_energy_positive j A 0⟩ hL.1 hQuant)

theorem decay_unique (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (e l : Value)
    (hl : l.real.preferred.Pos)
    (hD : (Value.add (Value.mul l l) (Value.mul e e)).real.preferred.Equiv (RealRaw.ofRat 1))
    (hE : e.real.preferred.Equiv (energy k hk N A).real.preferred) :
    l.real.preferred.Equiv (decay k hk N A hn).real.preferred := by
  have hOld := quotient_eq (y := Value.rational 1) hD
  have hNew := quotient_eq (y := Value.rational 1) (laws k hk N A hn).1
  have he := quotient_eq hE
  simp only [quotient_add,quotient_mul,quotient_one] at hOld hNew
  have hSq : (Value.mul l l).real.preferred.Equiv
      (Value.mul (decay k hk N A hn) (decay k hk N A hn)).real.preferred := by
    apply raw_equiv_of_quotient_eq
    simp only [quotient_mul]
    rw [he] at hOld
    grind only
  obtain ⟨n,hn'⟩ := hl
  apply PositiveSquareUnique.unique l (decay k hk N A hn) n _ hSq
  have hp := decay_positive k hk N A hn n
  change 0<(l.real.compute n).lo+((decay k hk N A hn).real.compute n).lo
  change 0<(l.real.compute n).lo at hn'
  grind only

theorem decay_zero_agreement (j : Nat) (hn : ¬A.squared.preferred.Equiv RealRaw.zero) :
    (decay (j+1) (Nat.zero_lt_succ j) 0 A hn).real.preferred.Equiv
      (HydrogenCircularComputations.upperDecay j A hn).real.preferred :=
  RealRaw.equiv_symm (decay_unique (j+1) (Nat.zero_lt_succ j) 0 A hn _ _
    ⟨0,HydrogenCircularComputations.upper_decay_positive j A hn 0⟩
    (HydrogenCircularComputations.upper_laws j A hn).1 (RealRaw.equiv_symm (degree_zero_agreement A j hn)))

end ComputableAnalysis.HydrogenQuantizedParameters
