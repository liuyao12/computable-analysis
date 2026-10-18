import ComputableAnalysis.HydrogenPolynomialRadial
import ComputableAnalysis.HydrogenCircularRemainder

/-! The fine-structure gaps of the general constructed polynomial family
agree with the existing exact rationalized splittings. Their explicit energy
remainders are transported to these actual radial-solution energies. -/
namespace ComputableAnalysis.HydrogenPolynomialSplitting
open ComputableCoefficient QuotientBridge HydrogenCoupling
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable (A : Coupling)

def gap (k : Nat) (hk : 0<k) : Value := Value.sub
  (HydrogenQuantizedParameters.energy (k+1) (Nat.zero_lt_succ k) 0 A)
  (HydrogenQuantizedParameters.energy k hk 1 A)

theorem gap_agreement (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (k : Nat) (hk : 0<k) :
    (gap A k hk).real.preferred.Equiv (HydrogenCircularSplitting.splitting k hk A).real.preferred := by
  apply raw_equiv_of_quotient_eq
  simp only [gap,HydrogenCircularSplitting.splitting,quotient_sub]
  rw [quotient_eq (HydrogenQuantizedParameters.degree_zero_agreement A k hn),
    quotient_eq (HydrogenQuantizedParameters.degree_one_agreement k hk A)]

def remainder (k : Nat) (hk : 0<k) (c : Rat) : Value :=
  Value.sub (gap A k hk) (Value.mul (Value.mul A.value A.value) (Value.rational c))

theorem remainder_agreement (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (k : Nat) (hk : 0<k) (c : Rat) :
    (remainder A k hk c).real.preferred.Equiv (HydrogenCircularRemainder.remainder A k hk c).real.preferred := by
  apply raw_equiv_of_quotient_eq
  simp only [remainder,HydrogenCircularRemainder.remainder,quotient_sub]
  rw [quotient_eq (gap_agreement A hn k hk)]

theorem two_p_remainder_bound (hn : ¬A.squared.preferred.Equiv RealRaw.zero)
    (hu : A.squared.preferred.Le (RealRaw.ofRat (1/4))) :
    (Value.neg (HydrogenCircularRemainder.cubic A)).real.preferred.Le (remainder A 1 (by decide +kernel) (1/32)).real.preferred ∧
    (remainder A 1 (by decide +kernel) (1/32)).real.preferred.Le (HydrogenCircularRemainder.cubic A).real.preferred := by
  have hE := RealRaw.equiv_symm (remainder_agreement A hn 1 (by decide +kernel) (1/32))
  have hB := HydrogenCircularRemainder.two_p_remainder_bound A hu
  exact ⟨le_congr (Value.equiv_refl _) hE hB.1,le_congr hE (Value.equiv_refl _) hB.2⟩

theorem three_remainder_bound (hn : ¬A.squared.preferred.Equiv RealRaw.zero)
    (hu : A.squared.preferred.Le (RealRaw.ofRat (1/16))) :
    (Value.neg (Value.mul (Value.rational (1/64)) (HydrogenCircularRemainder.cubic A))).real.preferred.Le
      (remainder A 2 (by decide +kernel) (1/324)).real.preferred ∧
    (remainder A 2 (by decide +kernel) (1/324)).real.preferred.Le
      (Value.mul (Value.rational (1/64)) (HydrogenCircularRemainder.cubic A)).real.preferred := by
  have hE := RealRaw.equiv_symm (remainder_agreement A hn 2 (by decide +kernel) (1/324))
  have hB := HydrogenCircularRemainder.circular_three_remainder_bound A hu
  exact ⟨le_congr (Value.equiv_refl _) hE hB.1,le_congr hE (Value.equiv_refl _) hB.2⟩

end ComputableAnalysis.HydrogenPolynomialSplitting
