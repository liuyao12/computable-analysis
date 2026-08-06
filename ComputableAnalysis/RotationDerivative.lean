import ComputableAnalysis.RotationTaylorBridge
import ComputableAnalysis.RotationCalculus
import ComputableAnalysis.IntervalQuotient

namespace ComputableAnalysis
namespace RotationSeries

private theorem uniform_rotation_tail_start_for_derivative (n : Nat) :
    (2 : Rat) <= (((uniformRotationTailTerms n + 1 : Nat) : Rat) / 2) := by
  let s := uniformRotationTailStart
  have hs := RationalMajorant.factorialTailStart_satisfies (2 : Rat)
  have hmono := RationalMajorant.factorialTailStart_mono (2 : Rat) s (s + 2 * n)
    (by simpa [s, uniformRotationTailStart] using hs)
  change (2 : Rat) <= (((2 * (s + n) + 1 : Nat) : Rat) / 2)
  have hterms : s + (s + 2 * n) + 1 = 2 * (s + n) + 1 := by omega
  rw [hterms] at hmono
  exact hmono

private theorem rat_pow_add_for_derivative (q : Rat) (m n : Nat) :
    q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero =>
      rw [show m + 0 = m by omega, Rat.pow_zero, Rat.mul_one]
  | succ n ih =>
      rw [show m + (n + 1) = m + n + 1 by omega,
        Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc]

private theorem half_pow_twice_le_for_derivative (n : Nat) :
    ((1 : Rat) / 2) ^ (2 * n) <= ((1 : Rat) / 2) ^ n := by
  rw [show 2 * n = n + n by omega, rat_pow_add_for_derivative]
  have hhalf0 : (0 : Rat) <= 1 / 2 := by native_decide
  have hhalf1 : (1 : Rat) / 2 <= 1 := by native_decide
  have hpow0 : 0 <= ((1 : Rat) / 2) ^ n := Rat.pow_nonneg hhalf0
  have hpow1 : ((1 : Rat) / 2) ^ n <= 1 := by
    induction n with
    | zero =>
        rw [Rat.pow_zero]
        exact Rat.le_refl
    | succ n ih =>
        rw [Rat.pow_succ]
        calc
          ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) <=
              ((1 : Rat) / 2) ^ n * 1 :=
            Rat.mul_le_mul_of_nonneg_left hhalf1 (Rat.pow_nonneg hhalf0)
          _ = ((1 : Rat) / 2) ^ n := by rw [Rat.mul_one]
          _ <= 1 := ih (Rat.pow_nonneg hhalf0)
  calc
    ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) ^ n <=
        ((1 : Rat) / 2) ^ n * 1 :=
      Rat.mul_le_mul_of_nonneg_left hpow1 hpow0
    _ = ((1 : Rat) / 2) ^ n := by rw [Rat.mul_one]

private theorem uniformRotationTailMagnitude_nonneg_for_derivative (n : Nat) :
    0 <= uniformRotationTailMagnitude n := by
  unfold uniformRotationTailMagnitude
  exact RationalMajorant.factorialTailTerm_nonneg (by native_decide) _

private theorem uniformRotationTailMagnitude_le_geometric_for_derivative
    (n : Nat) :
    uniformRotationTailMagnitude n <=
      uniformRotationTailMagnitude 0 * ((1 : Rat) / 2) ^ n := by
  have htail := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := (2 : Rat)) (N := uniformRotationTailTerms 0)
    (by native_decide) (uniform_rotation_tail_start_for_derivative 0) (2 * n)
  have hterms : uniformRotationTailTerms n = uniformRotationTailTerms 0 + 2 * n := by
    unfold uniformRotationTailTerms
    omega
  unfold uniformRotationTailMagnitude
  rw [hterms]
  calc
    RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms 0 + 2 * n) <=
        RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms 0) *
          ((1 : Rat) / 2) ^ (2 * n) := htail
    _ <= RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms 0) *
          ((1 : Rat) / 2) ^ n :=
      Rat.mul_le_mul_of_nonneg_left (half_pow_twice_le_for_derivative n)
        (RationalMajorant.factorialTailTerm_nonneg (by native_decide) _)

def uniformRotationQuotientTailTolerance (h : Rat) (hh : h ≠ 0) (n : Nat) : QPos :=
  { val := (precisionAtStage n).val * qabs h / 48
    property := by
      rw [Rat.div_def]
      exact Rat.mul_pos
        (Rat.mul_pos (precisionAtStage n).property (qabs_pos_of_ne hh))
        ((Rat.inv_pos).2 (by native_decide)) }

def uniformRotationQuotientPrecision (h : Rat) (hh : h ≠ 0) (n : Nat) : Nat :=
  RationalMajorant.halfDecayShift (uniformRotationTailMagnitude 0)
    (uniformRotationQuotientTailTolerance h hh n)

def uniformRotationSinDerivativeEvalPrecision (h : Rat) (n : Nat) : Nat :=
  if hh : h = 0 then 0 else uniformRotationQuotientPrecision h hh n

private theorem uniformRotationSinDerivativeEvalPrecision_of_ne
    (h : Rat) (hh : h ≠ 0) (n : Nat) :
    uniformRotationSinDerivativeEvalPrecision h n =
      uniformRotationQuotientPrecision h hh n := by
  simp [uniformRotationSinDerivativeEvalPrecision, hh]

theorem uniformRotationTailMagnitude_le_quotientTolerance
    (h : Rat) (hh : h ≠ 0) (n : Nat) :
    uniformRotationTailMagnitude (uniformRotationQuotientPrecision h hh n) <=
      (uniformRotationQuotientTailTolerance h hh n).val := by
  let eps := uniformRotationQuotientTailTolerance h hh n
  let stage := uniformRotationQuotientPrecision h hh n
  have hbound : 0 <= uniformRotationTailMagnitude 0 :=
    uniformRotationTailMagnitude_nonneg_for_derivative 0
  have htail := uniformRotationTailMagnitude_le_geometric_for_derivative stage
  have hshift := RationalMajorant.halfDecayShift_spec hbound eps
  exact Rat.le_trans htail hshift

def uniformRotationSinDerivativeStepPrecision (n : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift (68 : Rat) (precisionAtStage n)

theorem uniformRotationSinDerivative_finite_error_le_half_precision
    {h : Rat} (n : Nat)
    (hsmall : qabs h <=
      1 / ((uniformRotationSinDerivativeStepPrecision n : Nat) : Rat)) :
    qabs h * 34 <= (precisionAtStage n).val / 2 := by
  let shift : Nat := RationalMajorant.halfDecayShift (68 : Rat)
    (precisionAtStage n)
  have hsmall' : qabs h <= 1 / (((2 ^ shift : Nat) : Rat)) := by
    simpa [uniformRotationSinDerivativeStepPrecision, shift] using hsmall
  have hscaled : qabs h * 68 <= 1 / (((2 ^ shift : Nat) : Rat)) * 68 :=
    Rat.mul_le_mul_of_nonneg_right hsmall' (by native_decide)
  have hgeometric : (68 : Rat) * ((1 : Rat) / 2) ^ shift <=
      (precisionAtStage n).val := by
    simpa [shift] using RationalMajorant.halfDecayShift_spec
      (by native_decide : (0 : Rat) <= 68) (precisionAtStage n)
  have hsixtyEight : qabs h * 68 <= (precisionAtStage n).val := by
    calc
      qabs h * 68 <= 1 / (((2 ^ shift : Nat) : Rat)) * 68 := hscaled
      _ = 68 * ((1 : Rat) / 2) ^ shift := by
        rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
        grind [Rat.mul_comm]
      _ <= (precisionAtStage n).val := hgeometric
  calc
    qabs h * 34 = (qabs h * 68) / 2 := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (precisionAtStage n).val / 2 :=
      Rat.mul_le_mul_of_nonneg_right hsixtyEight (Rat.le_of_lt
        ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2)))

private theorem uniformRotation_tail_transport_budgets
    {h t : Rat} (hh : h ≠ 0) (habs : qabs h <= 4)
    (eps : QPos) (ht : t <= eps.val * qabs h / 48) :
    8 * t / qabs h + 4 * t <= eps.val / 2 /\
      16 * t / qabs h <= eps.val /\
      8 * t <= eps.val := by
  have hApos : 0 < qabs h := qabs_pos_of_ne hh
  have hAinv0 : 0 <= (qabs h)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hApos)
  have hcancel : qabs h * (qabs h)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ (Rat.ne_of_gt hApos)
  have htdiv : t / qabs h <= eps.val / 48 := by
    calc
      t / qabs h <= (eps.val * qabs h / 48) / qabs h :=
        Rat.mul_le_mul_of_nonneg_right ht hAinv0
      _ = eps.val / 48 := by
        rw [Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have heps0 : 0 <= eps.val := Rat.le_of_lt eps.property
  have hsmall : t <= eps.val / 12 := by
    calc
      t <= eps.val * qabs h / 48 := ht
      _ <= eps.val * 4 / 48 := by
        rw [Rat.div_def, Rat.div_def]
        exact Rat.mul_le_mul_of_nonneg_right
          (Rat.mul_le_mul_of_nonneg_left habs heps0)
          (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide)))
      _ = eps.val / 12 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have height : 8 * t / qabs h <= eps.val / 6 := by
    calc
      8 * t / qabs h = 8 * (t / qabs h) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc]
      _ <= 8 * (eps.val / 48) :=
        Rat.mul_le_mul_of_nonneg_left htdiv (by native_decide)
      _ = eps.val / 6 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hfour : 4 * t <= eps.val / 3 := by
    calc
      4 * t <= 4 * (eps.val / 12) :=
        Rat.mul_le_mul_of_nonneg_left hsmall (by native_decide)
      _ = eps.val / 3 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hsixteen : 16 * t / qabs h <= eps.val := by
    calc
      16 * t / qabs h = 16 * (t / qabs h) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc]
      _ <= 16 * (eps.val / 48) :=
        Rat.mul_le_mul_of_nonneg_left htdiv (by native_decide)
      _ = eps.val / 3 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= eps.val := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have heightDirect : 8 * t <= eps.val := by
    calc
      8 * t <= 8 * (eps.val / 12) :=
        Rat.mul_le_mul_of_nonneg_left hsmall (by native_decide)
      _ = eps.val * 2 / 3 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= eps.val := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  exact ⟨by
    calc
      8 * t / qabs h + 4 * t <= eps.val / 6 + eps.val / 3 :=
        rat_add_le_add height hfour
      _ = eps.val / 2 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm], hsixteen, heightDirect⟩

/-- The common-prefix sine evaluator has derivative the common-prefix cosine
evaluator on the bounded rational chart `[-2,2]`.  The proof combines the
finite Taylor secant estimate with a step-aware factorial-tail stage, so no
completion or ambient analytic limit principle occurs here. -/
def uniformRotationSinOnTwo_hasDerivativeOnInterval :
    HasDerivativeOnInterval uniformRotationSinOnTwo uniformRotationCosOnTwo where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := uniformRotationSinDerivativeStepPrecision
  evalPrecision := fun _x h n => uniformRotationSinDerivativeEvalPrecision h n
  close := by
    intro x h n hx hxh _hdx hh hsmall
    have hx' : (-2 : Rat) <= x /\ x <= 2 := by
      simpa [uniformRotationSinOnTwo, inDomainInterval] using hx
    have hxh' : (-2 : Rat) <= x + h /\ x + h <= 2 := by
      simpa [uniformRotationSinOnTwo, inDomainInterval] using hxh
    have hqx : qabs x <= 2 := qabs_le_of_neg_le_le hx'.1 hx'.2
    have hqxh : qabs (x + h) <= 2 := qabs_le_of_neg_le_le hxh'.1 hxh'.2
    have habs : qabs h <= 4 := by
      calc
        qabs h = qabs ((x + h) - x) := by
          congr 1
          grind [Rat.sub_eq_add_neg]
        _ <= qabs (x + h) + qabs x := qabs_sub_le _ _
        _ <= 2 + 2 := rat_add_le_add hqxh hqx
        _ = 4 := by native_decide
    let eps : QPos := precisionAtStage n
    let stage : Nat := uniformRotationQuotientPrecision h hh n
    have hstage : uniformRotationSinDerivativeEvalPrecision h n = stage := by
      dsimp [stage]
      exact uniformRotationSinDerivativeEvalPrecision_of_ne h hh n
    have htail : uniformRotationTailMagnitude stage <=
        eps.val * qabs h / 48 := by
      dsimp [stage, eps]
      simpa [uniformRotationQuotientTailTolerance] using
        uniformRotationTailMagnitude_le_quotientTolerance h hh n
    have hfinite : qabs h * 34 <= eps.val / 2 := by
      dsimp [eps]
      exact uniformRotationSinDerivative_finite_error_le_half_precision n hsmall
    have htransport := uniformRotation_tail_transport_budgets hh habs eps htail
    have hbudget :
        qabs h * 34 + 2 * uniformRotationTailRadius stage / qabs h +
            uniformRotationTailRadius stage <= eps.val := by
      calc
        qabs h * 34 + 2 * uniformRotationTailRadius stage / qabs h +
            uniformRotationTailRadius stage =
            qabs h * 34 +
              (8 * uniformRotationTailMagnitude stage / qabs h +
                4 * uniformRotationTailMagnitude stage) := by
              unfold uniformRotationTailRadius
              grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
        _ <= eps.val / 2 + eps.val / 2 :=
          rat_add_le_add hfinite htransport.1
        _ = eps.val := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]
    have hquotientWidth :
        4 * uniformRotationTailRadius stage / qabs h <= eps.val := by
      calc
        4 * uniformRotationTailRadius stage / qabs h =
            16 * uniformRotationTailMagnitude stage / qabs h := by
              unfold uniformRotationTailRadius
              grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
        _ <= eps.val := htransport.2.1
    have hderivativeWidth :
        2 * uniformRotationTailRadius stage <= eps.val := by
      calc
        2 * uniformRotationTailRadius stage =
            8 * uniformRotationTailMagnitude stage := by
              unfold uniformRotationTailRadius
              grind [Rat.mul_assoc]
        _ <= eps.val := htransport.2.2
    have hcenter := uniformRotationSinCenter_secant_error_le_thirty_four
      hh hqx hqxh stage
    rw [hstage]
    change QInterval.NearAt
      (QInterval.differenceQuotient
        (QInterval.around ((uniformRotationCenter (x + h) stage).im)
          (uniformRotationTailRadius stage))
        (QInterval.around ((uniformRotationCenter x stage).im)
          (uniformRotationTailRadius stage)) h)
      (QInterval.around ((uniformRotationCenter x stage).re)
        (uniformRotationTailRadius stage)) eps
    exact QInterval.around_differenceQuotient_near_around
      ((uniformRotationCenter x stage).im)
      ((uniformRotationCenter (x + h) stage).im)
      ((uniformRotationCenter x stage).re)
      (uniformRotationTailRadius stage) h (qabs h * 34) eps hh
      (by
        unfold uniformRotationTailRadius
        exact Rat.mul_nonneg (by native_decide)
          (uniformRotationTailMagnitude_nonneg_for_derivative stage))
      hcenter hbudget hquotientWidth hderivativeWidth

end RotationSeries
end ComputableAnalysis
