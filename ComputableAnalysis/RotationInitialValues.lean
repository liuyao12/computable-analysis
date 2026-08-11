import ComputableAnalysis.RotationDerivative

/-!
# Initial data for the common-prefix rotation system

The common factorial-prefix sine and cosine evaluators already have literal
rational epsilon--delta derivative certificates.  This module adds their
finite initial-value calculation: at the rational zero input every omitted
factorial box contains the exact centers `1` and `0`.  It then packages the
two derivative certificates and those initial values as the candidate for the
rotation initial-value problem.  No continuous ODE uniqueness theorem is used
or assumed here.
-/

namespace ComputableAnalysis
namespace RotationSeries

private theorem zero_pow_rat_succ (m : Nat) : (0 : Rat) ^ (m + 1) = 0 := by
  induction m with
  | zero => native_decide
  | succ m ih =>
      rw [Rat.pow_succ, ih, Rat.zero_mul]

private theorem cosineCoefficient_zero (k : Nat) :
    LinearODE.RotationSystem.cosineCoefficient (0 : Rat) k =
      if k = 0 then 1 else 0 := by
  cases k with
  | zero =>
      native_decide
  | succ k =>
      simp only [if_neg (Nat.succ_ne_zero k)]
      unfold LinearODE.RotationSystem.cosineCoefficient
      have hpow : (0 : Rat) ^ (2 * (k + 1)) = 0 := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          zero_pow_rat_succ]
      rw [Rat.div_def, hpow, Rat.zero_mul, Rat.zero_mul]

private theorem sineCoefficient_zero (k : Nat) :
    LinearODE.RotationSystem.sineCoefficient (0 : Rat) k = 0 := by
  unfold LinearODE.RotationSystem.sineCoefficient
  have hpow : (0 : Rat) ^ (2 * k + 1) = 0 := by
    exact zero_pow_rat_succ (2 * k)
  rw [Rat.div_def, hpow, Rat.zero_mul, Rat.zero_mul]

private theorem cosinePrefix_zero_of_pos :
    forall m : Nat, 0 < m -> LinearODE.RotationSystem.cosinePrefix (0 : Rat) m = 1
  | 0, h => by omega
  | 1, _ => by
      simp [LinearODE.RotationSystem.cosinePrefix, cosineCoefficient_zero]
      exact Rat.zero_add _
  | m + 2, _ => by
      rw [LinearODE.RotationSystem.cosinePrefix]
      have hprev := cosinePrefix_zero_of_pos (m + 1) (by omega)
      rw [hprev, cosineCoefficient_zero]
      simp
      exact Rat.add_zero _

private theorem sinePrefix_zero (m : Nat) :
    LinearODE.RotationSystem.sinePrefix (0 : Rat) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [LinearODE.RotationSystem.sinePrefix, ih, sineCoefficient_zero]
      exact Rat.zero_add 0

private theorem uniformRotationTailStart_eq_five_for_initial :
    uniformRotationTailStart = 5 := by native_decide

private theorem uniformRotationCenter_zero (n : Nat) :
    uniformRotationCenter (0 : Rat) n = { re := 1, im := 0 } := by
  unfold uniformRotationCenter complexPrefix
  have hpos : 0 < uniformRotationTailStart + n := by
    rw [uniformRotationTailStart_eq_five_for_initial]
    omega
  rw [cosinePrefix_zero_of_pos _ hpos, sinePrefix_zero]

/-- At zero, every common-prefix cosine box contains the exact rational value
one; therefore the represented evaluator is equivalent to `1`. -/
theorem uniformRotationCosOnTwo_zero_equiv_one :
    (PartialRealFunRaw.apply uniformRotationCosOnTwo.raw uniformRotationCosOnTwo.valid_on
      (0 : Rat)
      (uniformRotationCosOnTwo.defined_on 0 (by constructor <;> native_decide))).Equiv
      (RealRaw.ofRat 1) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    { lo := (uniformRotationCenter (0 : Rat) n).re - uniformRotationTailRadius n,
      hi := (uniformRotationCenter (0 : Rat) n).re + uniformRotationTailRadius n }
    { lo := 1, hi := 1 }
  rw [uniformRotationCenter_zero]
  have hradius : 0 <= uniformRotationTailRadius n := by
    unfold uniformRotationTailRadius uniformRotationTailMagnitude
    exact Rat.mul_nonneg (by native_decide)
      (RationalMajorant.factorialTailTerm_nonneg (by native_decide) _)
  constructor <;> grind [QInterval.Overlaps, Rat.sub_eq_add_neg]

/-- At zero, every common-prefix sine box contains the exact rational value
zero; therefore the represented evaluator is equivalent to `0`. -/
theorem uniformRotationSinOnTwo_zero_equiv_zero :
    (PartialRealFunRaw.apply uniformRotationSinOnTwo.raw uniformRotationSinOnTwo.valid_on
      (0 : Rat)
      (uniformRotationSinOnTwo.defined_on 0 (by constructor <;> native_decide))).Equiv
      (RealRaw.ofRat 0) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    { lo := (uniformRotationCenter (0 : Rat) n).im - uniformRotationTailRadius n,
      hi := (uniformRotationCenter (0 : Rat) n).im + uniformRotationTailRadius n }
    { lo := 0, hi := 0 }
  rw [uniformRotationCenter_zero]
  have hradius : 0 <= uniformRotationTailRadius n := by
    unfold uniformRotationTailRadius uniformRotationTailMagnitude
    exact Rat.mul_nonneg (by native_decide)
      (RationalMajorant.factorialTailTerm_nonneg (by native_decide) _)
  constructor <;> grind [QInterval.Overlaps, Rat.sub_eq_add_neg]

/-- The explicit negative-sine evaluator is pointwise equivalent to the raw
negation of the common-prefix sine evaluator.  It supplies the sign link in
the coordinatewise rotation-system certificate. -/
theorem uniformRotationNegSinOnTwo_equiv_neg_sin
    (x : Rat)
    (hxSin : inDomainInterval uniformRotationSinOnTwo.lower
      uniformRotationSinOnTwo.upper x)
    (hxNeg : inDomainInterval uniformRotationNegSinOnTwo.lower
      uniformRotationNegSinOnTwo.upper x) :
    (-(PartialRealFunRaw.apply uniformRotationSinOnTwo.raw
      uniformRotationSinOnTwo.valid_on x
      (uniformRotationSinOnTwo.defined_on x hxSin))).Equiv
    (PartialRealFunRaw.apply uniformRotationNegSinOnTwo.raw
      uniformRotationNegSinOnTwo.valid_on x
      (uniformRotationNegSinOnTwo.defined_on x hxNeg)) := by
  change (RealRaw.neg (ComplexRaw.imagPart (uniformRotationExpRaw x))).Equiv
    (RealRaw.neg (ComplexRaw.imagPart (uniformRotationExpRaw x)))
  apply RealRaw.equiv_refl
  change (-2 : Rat) <= x /\ x <= 2 at hxSin
  have hx : (-2 : Rat) <= x /\ x <= 2 := hxSin
  exact RealRaw.neg_valid (ComplexRaw.imagPart_valid
    (uniformRotationExpRaw_valid x (qabs_le_of_neg_le_le hx.1 hx.2)))

/-- A coordinatewise initial-value certificate for the rotation system.  The
negative sine evaluator is kept explicit because it is the literal derivative
target of the common-prefix cosine computation. -/
structure RotationDerivativeInitialCertificate
    (cosine sine negativeSine : FunctionOnInterval) where
  sine_derivative : HasDerivativeOnInterval sine cosine
  cosine_derivative : HasDerivativeOnInterval cosine negativeSine
  negative_sine :
    forall x
      (hxSin : inDomainInterval sine.lower sine.upper x)
      (hxNeg : inDomainInterval negativeSine.lower negativeSine.upper x),
      (-(PartialRealFunRaw.apply sine.raw sine.valid_on x
        (sine.defined_on x hxSin))).Equiv
      (PartialRealFunRaw.apply negativeSine.raw negativeSine.valid_on x
        (negativeSine.defined_on x hxNeg))
  initial : Rat
  initial_in_cosine : inDomainInterval cosine.lower cosine.upper initial
  initial_in_sine : inDomainInterval sine.lower sine.upper initial
  cosine_initial :
    (PartialRealFunRaw.apply cosine.raw cosine.valid_on initial
      (cosine.defined_on initial initial_in_cosine)).Equiv (RealRaw.ofRat 1)
  sine_initial :
    (PartialRealFunRaw.apply sine.raw sine.valid_on initial
      (sine.defined_on initial initial_in_sine)).Equiv (RealRaw.ofRat 0)

/-- The common-prefix factorial coordinates satisfy the rotation initial-value
problem on `[-2,2]`: `S' = C`, `C' = -S`, `C(0)=1`, and `S(0)=0`.  This is an
initial-value *candidate*; identifying it with a geometric rotation still
requires the separate represented-input/uniqueness bridge. -/
def uniformRotationOnTwo_rotationInitialCertificate :
    RotationDerivativeInitialCertificate uniformRotationCosOnTwo
      uniformRotationSinOnTwo uniformRotationNegSinOnTwo where
  sine_derivative := uniformRotationSinOnTwo_hasDerivativeOnInterval
  cosine_derivative := uniformRotationCosOnTwo_hasDerivativeOnInterval
  negative_sine := uniformRotationNegSinOnTwo_equiv_neg_sin
  initial := 0
  initial_in_cosine := by constructor <;> native_decide
  initial_in_sine := by constructor <;> native_decide
  cosine_initial := uniformRotationCosOnTwo_zero_equiv_one
  sine_initial := uniformRotationSinOnTwo_zero_equiv_zero

end RotationSeries
end ComputableAnalysis
