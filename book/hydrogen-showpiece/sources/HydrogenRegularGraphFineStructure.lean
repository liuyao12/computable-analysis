import ComputableAnalysis.HydrogenRegularGraphSpectrum
import ComputableAnalysis.HydrogenPolynomialSplitting
import ComputableAnalysis.ComputableCoefficientPowerOrder

/-! Fine-structure differences and their exact ratio belong to genuine
eigenstates of the stated regular radial graph problem. Complete finite-
coupling remainder bounds are transported to the actual quotient of gaps. -/
namespace ComputableAnalysis.HydrogenRegularGraphFineStructure
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions HydrogenRadialEnvelope
open ComputableCoefficient QuotientBridge HydrogenCoupling HydrogenCircularSolidSpinors
set_option autoImplicit false
set_option maxHeartbeats 2000000
local instance regularFineRing : Lean.Grind.CommRing ComplexRawQuotient.Value := ComplexRawQuotient.instCommRingValue
local instance regularFineNatCast : NatCast ComplexRawQuotient.Value :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).natCast
local instance regularFineOfNat (n : Nat) : OfNat ComplexRawQuotient.Value n :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).ofNat n

theorem level_states (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (k : Nat) (hk : 0<k) :
    HydrogenRegularGraphSpectrum.HasEigenstate .plus k hk A hn (HydrogenQuantizedParameters.energy k hk 1 A) ∧
      HydrogenRegularGraphSpectrum.HasEigenstate .minus (k+1) (Nat.zero_lt_succ k) A hn
        (HydrogenQuantizedParameters.energy (k+1) (Nat.zero_lt_succ k) 0 A) :=
  ⟨HydrogenRegularGraphSpectrum.eigenstate_of_degree .plus k hk 1 A hn (Or.inl (by decide +kernel)),
    HydrogenRegularGraphSpectrum.eigenstate_of_degree .minus (k+1) (Nat.zero_lt_succ k) 0 A hn (Or.inr rfl)⟩

theorem gap_positive (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (k : Nat) (hk : 0<k) :
    (HydrogenPolynomialSplitting.gap A k hk).real.preferred.Pos := by
  have hAlpha : (A.alpha hn).real.preferred.Pos := ⟨0,A.alpha_positive hn 0⟩
  have hSquare := PowerOrder.product_positive (A.alpha hn) (A.alpha hn) hAlpha hAlpha
  have hValue := PositiveRealLogDerivative.positive_of_equiv (Value.mul (A.alpha hn) (A.alpha hn)).real.valid A.value.real.valid
    (A.alpha_square hn) hSquare
  have hProduct := PowerOrder.product_positive (Value.mul A.value A.value) (HydrogenCircularSplitting.coefficient k hk A)
    (PowerOrder.product_positive A.value A.value hValue hValue)
    ⟨0,HydrogenCircularSplitting.coefficient_positive k hk A 0⟩
  have hGap := Value.equiv_trans (HydrogenPolynomialSplitting.gap_agreement A hn k hk)
    (HydrogenCircularSplitting.splitting_identity k hk A)
  exact PositiveRealLogDerivative.positive_of_equiv
    (Value.mul (Value.mul A.value A.value) (HydrogenCircularSplitting.coefficient k hk A)).real.valid
    (HydrogenPolynomialSplitting.gap A k hk).real.valid (RealRaw.equiv_symm hGap) hProduct

theorem ratio_identity (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero) :
    (HydrogenPolynomialSplitting.gap A 2 (by decide +kernel)).real.preferred.Equiv
      (Value.mul (HydrogenCircularRatio.ratio A) (HydrogenPolynomialSplitting.gap A 1 (by decide +kernel))).real.preferred := by
  have h2 := quotient_eq (HydrogenPolynomialSplitting.gap_agreement A hn 2 (by decide +kernel))
  have h1 := quotient_eq (HydrogenPolynomialSplitting.gap_agreement A hn 1 (by decide +kernel))
  have hOld := quotient_eq (HydrogenCircularTwoPAgreement.splitting_agreement A)
  have hRatio := quotient_eq (HydrogenCircularRatio.ratio_identity A)
  apply raw_equiv_of_quotient_eq
  simp only [quotient_mul] at hRatio ⊢
  rw [h2,h1]
  rw [← hOld] at hRatio
  exact hRatio

def ratio (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero) : Value := Value.mul
  (HydrogenPolynomialSplitting.gap A 2 (by decide +kernel))
  ((HydrogenPolynomialSplitting.gap A 1 (by decide +kernel)).inverse
    (PositiveRootArithmetic.positive_nonzero _ (gap_positive A hn 1 (by decide +kernel))))

/-- The actual quotient of two genuine level gaps agrees exactly with
the independently regularized ratio computation, at every nonzero coupling. -/
theorem ratio_agreement (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero) :
    (ratio A hn).real.preferred.Equiv (HydrogenCircularRatio.ratio A).real.preferred := by
  have hRatio := quotient_eq (ratio_identity A hn)
  have hInv := quotient_eq (y := Value.rational 1) (Value.mul_inverse
    (HydrogenPolynomialSplitting.gap A 1 (by decide +kernel))
    (PositiveRootArithmetic.positive_nonzero _ (gap_positive A hn 1 (by decide +kernel))))
  apply raw_equiv_of_quotient_eq
  simp only [ratio,quotient_mul,quotient_one] at hRatio hInv ⊢
  grind only

theorem ratio_names (A B : Coupling) (hA : ¬A.squared.preferred.Equiv RealRaw.zero)
    (hB : ¬B.squared.preferred.Equiv RealRaw.zero) (hAB : A.squared.preferred.Equiv B.squared.preferred) :
    (ratio A hA).real.preferred.Equiv (ratio B hB).real.preferred :=
  Value.equiv_trans (ratio_agreement A hA)
    (Value.equiv_trans (HydrogenCircularRatio.ratio_congr A B hAB) (RealRaw.equiv_symm (ratio_agreement B hB)))

/-- The regularized arithmetic evaluator supplies a literal finite box for
the actual quotient, avoiding subtraction of close energy enclosures. -/
def ratioApproximation (A : Coupling) (eps : QPos) : QInterval :=
  let r := HydrogenCircularRatio.ratio A
  r.real.compute (widthStageFrom r.real eps 0)

theorem ratio_approximation_spec (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero) (eps : QPos) :
    (RealRaw.ofRat (ratioApproximation A eps).lo).Le (ratio A hn).real.preferred ∧
      (ratio A hn).real.preferred.Le (RealRaw.ofRat (ratioApproximation A eps).hi) ∧
      (ratioApproximation A eps).width≤eps.val := by
  let r := HydrogenCircularRatio.ratio A
  let N := widthStageFrom r.real eps 0
  have hNames := ratio_agreement A hn
  have hLower : (RealRaw.ofRat (r.real.compute N).lo).Le r.real.preferred := fun _ j => RealRaw.le_refl _ r.real.valid N j
  have hUpper : r.real.preferred.Le (RealRaw.ofRat (r.real.compute N).hi) := fun j _ => RealRaw.le_refl _ r.real.valid j N
  refine ⟨RealRaw.le_trans r.real.valid hLower
    (RealRaw.le_of_equiv r.real.valid (ratio A hn).real.valid (RealRaw.equiv_symm hNames)),
    RealRaw.le_trans r.real.valid (RealRaw.le_of_equiv (ratio A hn).real.valid r.real.valid hNames) hUpper,?_⟩
  exact (widthStageFrom_spec r.real eps 0).2

theorem two_p (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero)
    (hu : A.squared.preferred.Le (RealRaw.ofRat (1/4))) :
    HydrogenRegularGraphSpectrum.HasEigenstate .plus 1 (by decide +kernel) A hn (HydrogenQuantizedParameters.energy 1 (by decide +kernel) 1 A) ∧
      HydrogenRegularGraphSpectrum.HasEigenstate .minus 2 (by decide +kernel) A hn (HydrogenQuantizedParameters.energy 2 (by decide +kernel) 0 A) ∧
      (Value.neg (HydrogenCircularRemainder.cubic A)).real.preferred.Le (HydrogenPolynomialSplitting.remainder A 1 (by decide +kernel) (1/32)).real.preferred ∧
      (HydrogenPolynomialSplitting.remainder A 1 (by decide +kernel) (1/32)).real.preferred.Le (HydrogenCircularRemainder.cubic A).real.preferred :=
  ⟨(level_states A hn 1 (by decide +kernel)).1,(level_states A hn 1 (by decide +kernel)).2,
    (HydrogenPolynomialSplitting.two_p_remainder_bound A hn hu).1,(HydrogenPolynomialSplitting.two_p_remainder_bound A hn hu).2⟩

theorem three_d (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero)
    (hu : A.squared.preferred.Le (RealRaw.ofRat (1/16))) :
    HydrogenRegularGraphSpectrum.HasEigenstate .plus 2 (by decide +kernel) A hn (HydrogenQuantizedParameters.energy 2 (by decide +kernel) 1 A) ∧
      HydrogenRegularGraphSpectrum.HasEigenstate .minus 3 (by decide +kernel) A hn (HydrogenQuantizedParameters.energy 3 (by decide +kernel) 0 A) ∧
      (Value.neg (Value.mul (Value.rational (1/64)) (HydrogenCircularRemainder.cubic A))).real.preferred.Le
        (HydrogenPolynomialSplitting.remainder A 2 (by decide +kernel) (1/324)).real.preferred ∧
      (HydrogenPolynomialSplitting.remainder A 2 (by decide +kernel) (1/324)).real.preferred.Le
        (Value.mul (Value.rational (1/64)) (HydrogenCircularRemainder.cubic A)).real.preferred :=
  ⟨(level_states A hn 2 (by decide +kernel)).1,(level_states A hn 2 (by decide +kernel)).2,
    (HydrogenPolynomialSplitting.three_remainder_bound A hn hu).1,(HydrogenPolynomialSplitting.three_remainder_bound A hn hu).2⟩

/-- Explicit error for the actual quotient of the two eigenvalue gaps,
with its nonzero denominator proved and all finite-coupling error retained. -/
theorem ratio_remainder_bound (A : Coupling) (hn : ¬A.squared.preferred.Equiv RealRaw.zero)
    (hu : A.squared.preferred.Le (RealRaw.ofRat (1/128))) :
    (Value.neg (Value.mul (Value.rational 8) A.value)).real.preferred.Le
        (Value.sub (ratio A hn) (Value.rational (8/81))).real.preferred ∧
      (Value.sub (ratio A hn) (Value.rational (8/81))).real.preferred.Le (Value.mul (Value.rational 8) A.value).real.preferred := by
  have hError : (Value.sub (ratio A hn) (Value.rational (8/81))).real.preferred.Equiv
      (HydrogenCircularRemainder.ratioError A).real.preferred := by
    apply raw_equiv_of_quotient_eq
    simp only [HydrogenCircularRemainder.ratioError,quotient_sub,quotient_eq (ratio_agreement A hn)]
  have hBound := HydrogenCircularRemainder.ratio_bound A hu
  exact ⟨le_congr (Value.equiv_refl _) (RealRaw.equiv_symm hError) hBound.1,
    le_congr (RealRaw.equiv_symm hError) (Value.equiv_refl _) hBound.2⟩

end ComputableAnalysis.HydrogenRegularGraphFineStructure
