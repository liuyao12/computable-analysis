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

/-- A tail selected below `eps * |h| / 48` pays the three symmetric-box
quotient budgets on the bounded rotation chart.  It is reused by both
coordinate derivative certificates. -/
theorem uniformRotation_tail_transport_budgets
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

open FinitePolynomial

private theorem qabs_signed_odd_factorial_for_cosine (n : Nat) :
    qabs (((-1 : Rat) ^ (n + 1)) / factorialRat (2 * n + 1)) =
      FormalPowerSeries.expCoeff (2 * n + 1) := by
  unfold FormalPowerSeries.expCoeff
  rw [Rat.div_def, qabs_mul]
  have hsign : qabs ((-1 : Rat) ^ (n + 1)) = 1 := by
    rw [RationalMajorant.qabs_pow_eq_pow_qabs]
    have hminus : qabs (-1 : Rat) = 1 := by native_decide
    rw [hminus]
    induction n with
    | zero => rfl
    | succ n ih => rw [show n + 1 + 1 = (n + 1) + 1 by omega,
      Rat.pow_succ, ih, Rat.mul_one]
  rw [hsign, Rat.one_mul]
  calc
    qabs (factorialRat (2 * n + 1))⁻¹ =
        (factorialRat (2 * n + 1))⁻¹ :=
      qabs_eq_self_of_nonneg (Rat.le_of_lt ((Rat.inv_pos).2
        (RationalMajorant.factorialRat_pos _)))
    _ = 1 / factorialRat (2 * n + 1) := by
      rw [Rat.div_def, Rat.one_mul]

private def cosinePrefixSecantCoefficient : Nat -> Rat
  | 0 => 0
  | 1 => 0
  | n + 2 =>
      cosinePrefixSecantCoefficient (n + 1) +
        qabs (FormalPowerSeries.expCoeff (2 * n + 1)) *
          powerSecantErrorBound 2 (2 * n + 2)

private structure CosinePrefixSecantData (n : Nat) where
  bound : SecantDerivativeBound 2
    (fun x => LinearODE.RotationSystem.cosinePrefix x n)
    (fun x => -LinearODE.RotationSystem.sinePrefix x (n - 1))
  errorCoefficient_eq : bound.errorCoefficient = cosinePrefixSecantCoefficient n

private def cosinePrefixSecantData : (n : Nat) -> CosinePrefixSecantData n
  | 0 => by
      let B : SecantDerivativeBound 2
          (fun x => LinearODE.RotationSystem.cosinePrefix x 0)
          (fun x => -LinearODE.RotationSystem.sinePrefix x (0 - 1)) := by
        simpa [LinearODE.RotationSystem.cosinePrefix,
          LinearODE.RotationSystem.sinePrefix] using
          SecantDerivativeBound.constant 2 0
      exact { bound := B, errorCoefficient_eq := rfl }
  | 1 => by
      let B : SecantDerivativeBound 2
          (fun x => LinearODE.RotationSystem.cosinePrefix x 1)
          (fun x => -LinearODE.RotationSystem.sinePrefix x (1 - 1)) :=
        { errorCoefficient := 0
          errorCoefficient_nonneg := by native_decide
          error_bound := by
            intro x h hh hx hxh
            have hcos : LinearODE.RotationSystem.cosinePrefix x 1 = 1 := by
              simpa [LinearODE.RotationSystem.cosinePrefix,
                LinearODE.RotationSystem.cosineCoefficient, factorialRat, factorial] using
                (show (0 : Rat) + 1 / 1 = 1 by native_decide)
            have hcos' : LinearODE.RotationSystem.cosinePrefix (x + h) 1 = 1 := by
              simpa [LinearODE.RotationSystem.cosinePrefix,
                LinearODE.RotationSystem.cosineCoefficient, factorialRat, factorial] using
                (show (0 : Rat) + 1 / 1 = 1 by native_decide)
            have hsin : LinearODE.RotationSystem.sinePrefix x (1 - 1) = 0 := by
              rfl
            rw [hcos, hcos', hsin]
            rw [Rat.sub_self, Rat.div_def, Rat.zero_mul]
            have hzero : qabs (0 : Rat) = 0 := by native_decide
            rw [show (0 : Rat) - -0 = 0 by grind [Rat.sub_eq_add_neg], hzero,
              Rat.mul_zero]
            exact Rat.le_refl
        }
      exact {
        bound := B
        errorCoefficient_eq := by
          change 0 = 0
          rfl
      }
  | n + 2 => by
      let F := cosinePrefixSecantData (n + 1)
      let G := SecantDerivativeBound.scaleRat
        (((-1 : Rat) ^ (n + 1)) / factorialRat (2 * n + 1))
        (normalizedMonomialSecantBound 2 (2 * n + 1) (by native_decide))
      let H := F.bound.add G
      have hsource :
          (fun x => LinearODE.RotationSystem.cosinePrefix x (n + 1) +
            ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
              (x ^ (2 * n + 1 + 1) / ((2 * n + 1 + 1 : Nat) : Rat))) =
          fun x => LinearODE.RotationSystem.cosinePrefix x (n + 2) := by
        funext x
        change LinearODE.RotationSystem.cosinePrefix x (n + 1) +
            ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
              (x ^ (2 * n + 1 + 1) / ((2 * n + 1 + 1 : Nat) : Rat)) =
          LinearODE.RotationSystem.cosinePrefix x (n + 1) +
            LinearODE.RotationSystem.cosineCoefficient x (n + 1)
        congr 1
        unfold LinearODE.RotationSystem.cosineCoefficient
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
        have hfac : factorialRat ((2 * n + 1) + 1) =
            (((2 * n + 1 + 1 : Nat) : Rat)) * factorialRat (2 * n + 1) :=
          FormalPowerSeries.factorialRat_succ (2 * n + 1)
        rw [hfac]
        rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
        grind [Rat.mul_assoc, Rat.mul_comm]
      have htarget :
          (fun x => -LinearODE.RotationSystem.sinePrefix x (n + 1 - 1) +
            ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
              x ^ (2 * n + 1)) =
          fun x => -LinearODE.RotationSystem.sinePrefix x (n + 1) := by
        funext x
        rw [show n + 1 - 1 = n by omega]
        change -LinearODE.RotationSystem.sinePrefix x n +
            ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
              x ^ (2 * n + 1) =
          -(LinearODE.RotationSystem.sinePrefix x n +
            LinearODE.RotationSystem.sineCoefficient x n)
        unfold LinearODE.RotationSystem.sineCoefficient
        rw [Rat.pow_succ]
        grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
      have hcoeff : H.errorCoefficient = cosinePrefixSecantCoefficient (n + 2) := by
        dsimp [H, G, SecantDerivativeBound.add, SecantDerivativeBound.scaleRat,
          normalizedMonomialSecantBound]
        rw [F.errorCoefficient_eq, qabs_signed_odd_factorial_for_cosine]
        rw [cosinePrefixSecantCoefficient]
        have hexp : 0 <= FormalPowerSeries.expCoeff (2 * n + 1) := by
          unfold FormalPowerSeries.expCoeff
          rw [Rat.div_def, Rat.one_mul]
          exact Rat.le_of_lt ((Rat.inv_pos).2
            (RationalMajorant.factorialRat_pos _))
        rw [qabs_eq_self_of_nonneg hexp]
      let B : SecantDerivativeBound 2
          (fun x => LinearODE.RotationSystem.cosinePrefix x (n + 2))
          (fun x => -LinearODE.RotationSystem.sinePrefix x (n + 1)) :=
        { errorCoefficient := cosinePrefixSecantCoefficient (n + 2)
          errorCoefficient_nonneg := by
            unfold cosinePrefixSecantCoefficient
            apply Rat.add_nonneg
            · rw [← F.errorCoefficient_eq]
              exact F.bound.errorCoefficient_nonneg
            · exact Rat.mul_nonneg (qabs_nonneg _)
                (powerSecantErrorBound_nonneg (by native_decide) _)
          error_bound := by
            intro x h hh hx hxh
            have hH := H.error_bound x h hh hx hxh
            have hH' :
                qabs
                  ((LinearODE.RotationSystem.cosinePrefix (x + h) (n + 1) +
                      ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                        ((x + h) ^ (2 * n + 1 + 1) /
                          ((2 * n + 1 + 1 : Nat) : Rat)) -
                    (LinearODE.RotationSystem.cosinePrefix x (n + 1) +
                      ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                        (x ^ (2 * n + 1 + 1) /
                          ((2 * n + 1 + 1 : Nat) : Rat))) ) / h +
                    LinearODE.RotationSystem.sinePrefix x (n + 1)) <=
                  qabs h * H.errorCoefficient := by
              calc
                qabs
                    ((LinearODE.RotationSystem.cosinePrefix (x + h) (n + 1) +
                        ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                          ((x + h) ^ (2 * n + 1 + 1) /
                            ((2 * n + 1 + 1 : Nat) : Rat)) -
                      (LinearODE.RotationSystem.cosinePrefix x (n + 1) +
                        ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                          (x ^ (2 * n + 1 + 1) /
                            ((2 * n + 1 + 1 : Nat) : Rat))) ) / h +
                      LinearODE.RotationSystem.sinePrefix x (n + 1)) =
                    qabs
                      ((LinearODE.RotationSystem.cosinePrefix (x + h) (n + 1) +
                          ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                            ((x + h) ^ (2 * n + 1 + 1) /
                              ((2 * n + 1 + 1 : Nat) : Rat)) -
                        (LinearODE.RotationSystem.cosinePrefix x (n + 1) +
                          ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                            (x ^ (2 * n + 1 + 1) /
                              ((2 * n + 1 + 1 : Nat) : Rat))) ) / h -
                        (-LinearODE.RotationSystem.sinePrefix x (n + 1 - 1) +
                          ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                            x ^ (2 * n + 1))) := by
                        rw [congrFun htarget x]
                        grind [Rat.sub_eq_add_neg]
                _ <= qabs h * H.errorCoefficient := hH
            have hsourceX :
                LinearODE.RotationSystem.cosinePrefix x (n + 2) =
                  LinearODE.RotationSystem.cosinePrefix x (n + 1) +
                    ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                      (x ^ (2 * n + 1 + 1) /
                        ((2 * n + 1 + 1 : Nat) : Rat)) :=
              (congrFun hsource x).symm
            have hsourceXH :
                LinearODE.RotationSystem.cosinePrefix (x + h) (n + 2) =
                  LinearODE.RotationSystem.cosinePrefix (x + h) (n + 1) +
                    ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                      ((x + h) ^ (2 * n + 1 + 1) /
                        ((2 * n + 1 + 1 : Nat) : Rat)) :=
              (congrFun hsource (x + h)).symm
            have heq :
                qabs
                  ((LinearODE.RotationSystem.cosinePrefix (x + h) (n + 2) -
                      LinearODE.RotationSystem.cosinePrefix x (n + 2)) / h +
                    LinearODE.RotationSystem.sinePrefix x (n + 1)) =
                qabs
                  ((LinearODE.RotationSystem.cosinePrefix (x + h) (n + 1) +
                      ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                        ((x + h) ^ (2 * n + 1 + 1) /
                          ((2 * n + 1 + 1 : Nat) : Rat)) -
                    (LinearODE.RotationSystem.cosinePrefix x (n + 1) +
                      ((-1 : Rat) ^ (n + 1) / factorialRat (2 * n + 1)) *
                        (x ^ (2 * n + 1 + 1) /
                          ((2 * n + 1 + 1 : Nat) : Rat))) ) / h +
                    LinearODE.RotationSystem.sinePrefix x (n + 1)) := by
              rw [hsourceX, hsourceXH]
            calc
              qabs
                  ((LinearODE.RotationSystem.cosinePrefix (x + h) (n + 2) -
                      LinearODE.RotationSystem.cosinePrefix x (n + 2)) / h -
                    (-LinearODE.RotationSystem.sinePrefix x (n + 1))) =
                qabs
                  ((LinearODE.RotationSystem.cosinePrefix (x + h) (n + 2) -
                      LinearODE.RotationSystem.cosinePrefix x (n + 2)) / h +
                    LinearODE.RotationSystem.sinePrefix x (n + 1)) := by
                      grind [Rat.sub_eq_add_neg]
              _ <=
                  qabs h * H.errorCoefficient := by
                    rw [heq]
                    exact hH'
              _ = qabs h * cosinePrefixSecantCoefficient (n + 2) := by
                    rw [hcoeff] }
      exact { bound := B, errorCoefficient_eq := rfl }

private def cosinePrefixSecantBound (n : Nat) := (cosinePrefixSecantData n).bound

private theorem cosinePrefixSecantBound_errorCoefficient (n : Nat) :
    (cosinePrefixSecantBound n).errorCoefficient = cosinePrefixSecantCoefficient n :=
  (cosinePrefixSecantData n).errorCoefficient_eq

private theorem cosinePrefixSecantCoefficient_succ_le_exp (n : Nat) :
    cosinePrefixSecantCoefficient (n + 1) <=
      expTaylorPrefixSecantCoefficient (2 * n + 1) := by
  induction n with
  | zero => native_decide
  | succ n ih =>
      have hstep :
          cosinePrefixSecantCoefficient (n + 2) <=
            expTaylorPrefixSecantCoefficient (2 * n + 2) := by
        rw [cosinePrefixSecantCoefficient,
          show 2 * n + 2 = (2 * n + 1) + 1 by omega,
          expTaylorPrefixSecantCoefficient]
        exact rat_add_le_add ih Rat.le_refl
      have hnext :
          expTaylorPrefixSecantCoefficient (2 * n + 2) <=
            expTaylorPrefixSecantCoefficient (2 * (n + 1) + 1) := by
        have hterm : 0 <=
            qabs (FormalPowerSeries.expCoeff (2 * n + 2)) *
              powerSecantErrorBound 2 (2 * n + 2 + 1) :=
          Rat.mul_nonneg (qabs_nonneg _)
            (powerSecantErrorBound_nonneg (by native_decide) _)
        calc
          expTaylorPrefixSecantCoefficient (2 * n + 2) =
              expTaylorPrefixSecantCoefficient (2 * n + 2) + 0 := by
                rw [Rat.add_zero]
          _ <= expTaylorPrefixSecantCoefficient (2 * n + 2) +
              qabs (FormalPowerSeries.expCoeff (2 * n + 2)) *
                powerSecantErrorBound 2 (2 * n + 2 + 1) :=
              rat_add_le_add (Rat.le_refl) hterm
          _ = expTaylorPrefixSecantCoefficient ((2 * n + 2) + 1) := by rfl
          _ = expTaylorPrefixSecantCoefficient (2 * (n + 1) + 1) := by
              rw [show (2 * n + 2) + 1 = 2 * (n + 1) + 1 by omega]
      exact Rat.le_trans hstep hnext

private theorem cosinePrefixSecantCoefficient_le_thirty_four (n : Nat) :
    cosinePrefixSecantCoefficient n <= 34 := by
  cases n with
  | zero => native_decide
  | succ n =>
      exact Rat.le_trans (cosinePrefixSecantCoefficient_succ_le_exp n)
        (expTaylorPrefixSecantCoefficient_le_thirty_four _)

/-- A finite cosine prefix has secant error at most `34 |h|` relative to the
preceding negative sine prefix.  The one omitted sine term is handled
separately when this bound is transported to the common raw evaluator. -/
theorem cosinePrefix_secant_error_le_thirty_four
    {x h : Rat} (hh : h ≠ 0) (hx : qabs x <= 2)
    (hxh : qabs (x + h) <= 2) (n : Nat) :
    qabs
      (((LinearODE.RotationSystem.cosinePrefix (x + h) n -
          LinearODE.RotationSystem.cosinePrefix x n) / h) +
        LinearODE.RotationSystem.sinePrefix x (n - 1)) <=
      qabs h * 34 := by
  have hfinite := (cosinePrefixSecantBound n).error_bound x h hh hx hxh
  rw [cosinePrefixSecantBound_errorCoefficient] at hfinite
  calc
    qabs
        (((LinearODE.RotationSystem.cosinePrefix (x + h) n -
            LinearODE.RotationSystem.cosinePrefix x n) / h) +
          LinearODE.RotationSystem.sinePrefix x (n - 1)) <=
        qabs h * cosinePrefixSecantCoefficient n := by
          simpa [Rat.sub_eq_add_neg] using hfinite
    _ <= qabs h * 34 := Rat.mul_le_mul_of_nonneg_left
      (cosinePrefixSecantCoefficient_le_thirty_four n) (qabs_nonneg _)

private def uniformRotationCosDerivativeEdgeMagnitude (n : Nat) : Rat :=
  RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms n - 1)

private theorem uniformRotationTailStart_eq_five : uniformRotationTailStart = 5 := by
  native_decide

private theorem rat_pow_add_for_cosine (q : Rat) (m n : Nat) :
    q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero =>
      rw [show m + 0 = m by omega, Rat.pow_zero, Rat.mul_one]
  | succ n ih =>
      rw [show m + (n + 1) = m + n + 1 by omega,
        Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc]

private theorem half_pow_twice_le_for_cosine (n : Nat) :
    ((1 : Rat) / 2) ^ (2 * n) <= ((1 : Rat) / 2) ^ n := by
  rw [show 2 * n = n + n by omega]
  rw [rat_pow_add_for_cosine]
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

private theorem uniformRotationCosDerivativeEdgeMagnitude_nonneg (n : Nat) :
    0 <= uniformRotationCosDerivativeEdgeMagnitude n := by
  unfold uniformRotationCosDerivativeEdgeMagnitude
  exact RationalMajorant.factorialTailTerm_nonneg (by native_decide) _

private theorem uniformRotationCosDerivativeEdgeMagnitude_le_geometric
    (n : Nat) :
    uniformRotationCosDerivativeEdgeMagnitude n <=
      uniformRotationCosDerivativeEdgeMagnitude 0 * ((1 : Rat) / 2) ^ n := by
  have hstart : (2 : Rat) <=
      (((uniformRotationTailTerms 0 - 1 + 1 : Nat) : Rat) / 2) := by
    native_decide
  have htail := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := (2 : Rat)) (N := uniformRotationTailTerms 0 - 1)
    (by native_decide) hstart (2 * n)
  have hterms : uniformRotationTailTerms n - 1 =
      (uniformRotationTailTerms 0 - 1) + 2 * n := by
    unfold uniformRotationTailTerms
    rw [uniformRotationTailStart_eq_five]
    omega
  unfold uniformRotationCosDerivativeEdgeMagnitude
  rw [hterms]
  calc
    RationalMajorant.factorialTailTerm 2
        ((uniformRotationTailTerms 0 - 1) + 2 * n) <=
        RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms 0 - 1) *
          ((1 : Rat) / 2) ^ (2 * n) := htail
    _ <= RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms 0 - 1) *
          ((1 : Rat) / 2) ^ n :=
      Rat.mul_le_mul_of_nonneg_left (half_pow_twice_le_for_cosine n)
        (RationalMajorant.factorialTailTerm_nonneg (by native_decide) _)

private theorem uniformRotationCosDerivative_edge_le
    {x : Rat} (hx : qabs x <= 2) (n : Nat) :
    qabs
      (LinearODE.RotationSystem.sinePrefix x (uniformRotationTailStart + n) -
        LinearODE.RotationSystem.sinePrefix x
          (uniformRotationTailStart + n - 1)) <=
      uniformRotationCosDerivativeEdgeMagnitude n := by
  have hterms : uniformRotationTailStart + n =
      (uniformRotationTailStart + n - 1) + 1 := by
    rw [uniformRotationTailStart_eq_five]
    omega
  have hdiff :
      LinearODE.RotationSystem.sinePrefix x (uniformRotationTailStart + n) -
        LinearODE.RotationSystem.sinePrefix x
          (uniformRotationTailStart + n - 1) =
      LinearODE.RotationSystem.sineCoefficient x
        (uniformRotationTailStart + n - 1) := by
    rw [hterms, LinearODE.RotationSystem.sinePrefix]
    grind [Rat.sub_eq_add_neg]
  rw [hdiff]
  have hcoord := congrArg QComplex.im
    (expTerm_imaginary_odd x (uniformRotationTailStart + n - 1))
  have hcoord' :
      (ComplexSeries.expTerm (imaginaryAxis x)
        (2 * (uniformRotationTailStart + n - 1) + 1)).im =
        LinearODE.RotationSystem.sineCoefficient x
          (uniformRotationTailStart + n - 1) := by
    simpa using hcoord
  rw [← hcoord', expTerm_imaginary_odd_im_abs]
  have hmajorant := RationalMajorant.factorialTailTerm_mono
    (qabs_nonneg x) hx (2 * (uniformRotationTailStart + n - 1) + 1)
  unfold uniformRotationCosDerivativeEdgeMagnitude
  calc
    RationalMajorant.factorialTailTerm (qabs x)
        (2 * (uniformRotationTailStart + n - 1) + 1) <=
        RationalMajorant.factorialTailTerm 2
          (2 * (uniformRotationTailStart + n - 1) + 1) := hmajorant
    _ = RationalMajorant.factorialTailTerm 2
          (uniformRotationTailTerms n - 1) := by
          congr 2
          unfold uniformRotationTailTerms
          rw [uniformRotationTailStart_eq_five]
          omega

/-- The finite common-stage cosine secant differs from the same-stage
negative sine center by the uniform `34 |h|` error plus its one explicit
dropped sine term. -/
theorem uniformRotationCosCenter_secant_error_le_thirty_four_plus_edge
    {x h : Rat} (hh : h ≠ 0) (hx : qabs x <= 2)
    (hxh : qabs (x + h) <= 2) (n : Nat) :
    qabs
      (((uniformRotationCenter (x + h) n).re -
          (uniformRotationCenter x n).re) / h +
        (uniformRotationCenter x n).im) <=
      qabs h * 34 + uniformRotationCosDerivativeEdgeMagnitude n := by
  let terms := uniformRotationTailStart + n
  have hfinite := cosinePrefix_secant_error_le_thirty_four
    (x := x) (h := h) hh hx hxh terms
  have hedge := uniformRotationCosDerivative_edge_le (x := x) hx n
  change qabs
      (((LinearODE.RotationSystem.cosinePrefix (x + h) terms -
          LinearODE.RotationSystem.cosinePrefix x terms) / h +
        LinearODE.RotationSystem.sinePrefix x terms)) <= _
  have hsplit :
      ((LinearODE.RotationSystem.cosinePrefix (x + h) terms -
          LinearODE.RotationSystem.cosinePrefix x terms) / h +
        LinearODE.RotationSystem.sinePrefix x terms) =
      (((LinearODE.RotationSystem.cosinePrefix (x + h) terms -
          LinearODE.RotationSystem.cosinePrefix x terms) / h +
        LinearODE.RotationSystem.sinePrefix x (terms - 1)) +
        (LinearODE.RotationSystem.sinePrefix x terms -
          LinearODE.RotationSystem.sinePrefix x (terms - 1))) := by
        grind [Rat.sub_eq_add_neg]
  rw [hsplit]
  calc
    qabs
        (((LinearODE.RotationSystem.cosinePrefix (x + h) terms -
            LinearODE.RotationSystem.cosinePrefix x terms) / h +
          LinearODE.RotationSystem.sinePrefix x (terms - 1)) +
          (LinearODE.RotationSystem.sinePrefix x terms -
            LinearODE.RotationSystem.sinePrefix x (terms - 1))) <=
        qabs
          ((LinearODE.RotationSystem.cosinePrefix (x + h) terms -
            LinearODE.RotationSystem.cosinePrefix x terms) / h +
          LinearODE.RotationSystem.sinePrefix x (terms - 1)) +
          qabs (LinearODE.RotationSystem.sinePrefix x terms -
            LinearODE.RotationSystem.sinePrefix x (terms - 1)) :=
      qabs_add_le _ _
    _ <= qabs h * 34 + uniformRotationCosDerivativeEdgeMagnitude n :=
      rat_add_le_add hfinite hedge

private theorem uniformRotationCosOnTwo_compute_around_for_cosine
    (x : Rat) (hx : inDomainInterval (-2 : Rat) 2 x) (n : Nat) :
    uniformRotationCosOnTwo.compute x hx n =
      QInterval.around ((uniformRotationCenter x n).re)
        (uniformRotationTailRadius n) := by
  rfl

private theorem uniformRotationNegSinOnTwo_compute_around_for_cosine
    (x : Rat) (hx : inDomainInterval (-2 : Rat) 2 x) (n : Nat) :
    uniformRotationNegSinOnTwo.compute x hx n =
      QInterval.around (-((uniformRotationCenter x n).im))
        (uniformRotationTailRadius n) := by
  unfold FunctionOnInterval.compute uniformRotationNegSinOnTwo
    RealRaw.neg RealRaw.negCompute ComplexRaw.imagPart uniformRotationExpRaw
    uniformRotationBox QInterval.around
  dsimp
  congr 1 <;> grind [Rat.sub_eq_add_neg]
private theorem half_pow_le_one_for_cosine (n : Nat) :
    ((1 : Rat) / 2) ^ n <= 1 := by
  have hhalf0 : (0 : Rat) <= 1 / 2 := by native_decide
  have hhalf1 : (1 : Rat) / 2 <= 1 := by native_decide
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
        _ <= 1 := ih

private theorem half_pow_antitone_for_cosine {m n : Nat} (hnm : n <= m) :
    ((1 : Rat) / 2) ^ m <= ((1 : Rat) / 2) ^ n := by
  obtain ⟨d, hmd⟩ := Nat.exists_eq_add_of_le hnm
  rw [hmd, rat_pow_add_for_cosine]
  have hnonneg : 0 <= ((1 : Rat) / 2) ^ n :=
    Rat.pow_nonneg (by native_decide)
  calc
    ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) ^ d <=
        ((1 : Rat) / 2) ^ n * 1 :=
      Rat.mul_le_mul_of_nonneg_left (half_pow_le_one_for_cosine d) hnonneg
    _ = ((1 : Rat) / 2) ^ n := by rw [Rat.mul_one]

private theorem uniformRotationTailMagnitude_le_geometric_for_cosine
    (n : Nat) :
    uniformRotationTailMagnitude n <=
      uniformRotationTailMagnitude 0 * ((1 : Rat) / 2) ^ n := by
  have hstart : (2 : Rat) <=
      (((uniformRotationTailTerms 0 + 1 : Nat) : Rat) / 2) := by
    native_decide
  have htail := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := (2 : Rat)) (N := uniformRotationTailTerms 0)
    (by native_decide) hstart (2 * n)
  have hterms : uniformRotationTailTerms n = uniformRotationTailTerms 0 + 2 * n := by
    unfold uniformRotationTailTerms
    rw [uniformRotationTailStart_eq_five]
    omega
  unfold uniformRotationTailMagnitude
  rw [hterms]
  calc
    RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms 0 + 2 * n) <=
        RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms 0) *
          ((1 : Rat) / 2) ^ (2 * n) := htail
    _ <= RationalMajorant.factorialTailTerm 2 (uniformRotationTailTerms 0) *
          ((1 : Rat) / 2) ^ n :=
      Rat.mul_le_mul_of_nonneg_left (half_pow_twice_le_for_cosine n)
        (RationalMajorant.factorialTailTerm_nonneg (by native_decide) _)

/-- The non-quotient tolerance reserved for the final sine term dropped by a
finite cosine derivative. -/
def uniformRotationCosDerivativeEdgeTolerance (n : Nat) : QPos :=
  { val := (precisionAtStage n).val / 3
    property := by
      rw [Rat.div_def]
      exact Rat.mul_pos (precisionAtStage n).property
        ((Rat.inv_pos).2 (by native_decide)) }

def uniformRotationCosDerivativeEdgePrecision (n : Nat) : Nat :=
  RationalMajorant.halfDecayShift (uniformRotationCosDerivativeEdgeMagnitude 0)
    (uniformRotationCosDerivativeEdgeTolerance n)

def uniformRotationCosQuotientTailTolerance
    (h : Rat) (hh : h ≠ 0) (n : Nat) : QPos :=
  { val := (precisionAtStage n).val * qabs h / 96
    property := by
      rw [Rat.div_def]
      exact Rat.mul_pos
        (Rat.mul_pos (precisionAtStage n).property (qabs_pos_of_ne hh))
        ((Rat.inv_pos).2 (by native_decide)) }

def uniformRotationCosQuotientPrecision (h : Rat) (hh : h ≠ 0) (n : Nat) : Nat :=
  RationalMajorant.halfDecayShift (uniformRotationTailMagnitude 0)
    (uniformRotationCosQuotientTailTolerance h hh n)

/-- A common evaluator stage which simultaneously controls the divided
factorial tails and the finite-cosine dropped edge term. -/
def uniformRotationCosDerivativeEvalPrecision (h : Rat) (n : Nat) : Nat :=
  if hh : h = 0 then 0 else
    max (uniformRotationCosQuotientPrecision h hh n)
      (uniformRotationCosDerivativeEdgePrecision n)

private theorem uniformRotationCosDerivativeEvalPrecision_of_ne
    (h : Rat) (hh : h ≠ 0) (n : Nat) :
    uniformRotationCosDerivativeEvalPrecision h n =
      max (uniformRotationCosQuotientPrecision h hh n)
        (uniformRotationCosDerivativeEdgePrecision n) := by
  simp [uniformRotationCosDerivativeEvalPrecision, hh]

private theorem uniformRotationTailMagnitude_nonneg_for_cosine (n : Nat) :
    0 <= uniformRotationTailMagnitude n := by
  unfold uniformRotationTailMagnitude
  exact RationalMajorant.factorialTailTerm_nonneg (by native_decide) _

theorem uniformRotationTailMagnitude_le_cosQuotientTolerance
    (h : Rat) (hh : h ≠ 0) (n : Nat) :
    uniformRotationTailMagnitude (uniformRotationCosDerivativeEvalPrecision h n) <=
      (uniformRotationCosQuotientTailTolerance h hh n).val := by
  let qstage := uniformRotationCosQuotientPrecision h hh n
  let estage := uniformRotationCosDerivativeEdgePrecision n
  let stage := max qstage estage
  have hstage : uniformRotationCosDerivativeEvalPrecision h n = stage := by
    dsimp [stage, qstage, estage]
    exact uniformRotationCosDerivativeEvalPrecision_of_ne h hh n
  rw [hstage]
  have hgeo := uniformRotationTailMagnitude_le_geometric_for_cosine stage
  have hpow := half_pow_antitone_for_cosine (Nat.le_max_left qstage estage)
  have hscaled : uniformRotationTailMagnitude 0 * ((1 : Rat) / 2) ^ stage <=
      uniformRotationTailMagnitude 0 * ((1 : Rat) / 2) ^ qstage :=
    Rat.mul_le_mul_of_nonneg_left hpow
      (uniformRotationTailMagnitude_nonneg_for_cosine 0)
  have hshift := RationalMajorant.halfDecayShift_spec
    (uniformRotationTailMagnitude_nonneg_for_cosine 0)
    (uniformRotationCosQuotientTailTolerance h hh n)
  exact Rat.le_trans hgeo (Rat.le_trans hscaled hshift)

theorem uniformRotationCosDerivativeEdge_le_tolerance
    (h : Rat) (hh : h ≠ 0) (n : Nat) :
    uniformRotationCosDerivativeEdgeMagnitude
        (uniformRotationCosDerivativeEvalPrecision h n) <=
      (uniformRotationCosDerivativeEdgeTolerance n).val := by
  let qstage := uniformRotationCosQuotientPrecision h hh n
  let estage := uniformRotationCosDerivativeEdgePrecision n
  let stage := max qstage estage
  have hstage : uniformRotationCosDerivativeEvalPrecision h n = stage := by
    dsimp [stage, qstage, estage]
    exact uniformRotationCosDerivativeEvalPrecision_of_ne h hh n
  rw [hstage]
  have hgeo := uniformRotationCosDerivativeEdgeMagnitude_le_geometric stage
  have hpow := half_pow_antitone_for_cosine (Nat.le_max_right qstage estage)
  have hscaled : uniformRotationCosDerivativeEdgeMagnitude 0 *
      ((1 : Rat) / 2) ^ stage <=
      uniformRotationCosDerivativeEdgeMagnitude 0 * ((1 : Rat) / 2) ^ estage :=
    Rat.mul_le_mul_of_nonneg_left hpow
      (uniformRotationCosDerivativeEdgeMagnitude_nonneg 0)
  have hshift := RationalMajorant.halfDecayShift_spec
    (uniformRotationCosDerivativeEdgeMagnitude_nonneg 0)
    (uniformRotationCosDerivativeEdgeTolerance n)
  exact Rat.le_trans hgeo (Rat.le_trans hscaled hshift)

def uniformRotationCosDerivativeStepPrecision (n : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift (102 : Rat) (precisionAtStage n)

theorem uniformRotationCosDerivative_finite_error_le_third_precision
    {h : Rat} (n : Nat)
    (hsmall : qabs h <=
      1 / ((uniformRotationCosDerivativeStepPrecision n : Nat) : Rat)) :
    qabs h * 34 <= (precisionAtStage n).val / 3 := by
  let shift : Nat := RationalMajorant.halfDecayShift (102 : Rat)
    (precisionAtStage n)
  have hsmall' : qabs h <= 1 / (((2 ^ shift : Nat) : Rat)) := by
    simpa [uniformRotationCosDerivativeStepPrecision, shift] using hsmall
  have hscaled : qabs h * 102 <= 1 / (((2 ^ shift : Nat) : Rat)) * 102 :=
    Rat.mul_le_mul_of_nonneg_right hsmall' (by native_decide)
  have hgeometric : (102 : Rat) * ((1 : Rat) / 2) ^ shift <=
      (precisionAtStage n).val := by
    simpa [shift] using RationalMajorant.halfDecayShift_spec
      (by native_decide : (0 : Rat) <= 102) (precisionAtStage n)
  have hfull : qabs h * 102 <= (precisionAtStage n).val := by
    calc
      qabs h * 102 <= 1 / (((2 ^ shift : Nat) : Rat)) * 102 := hscaled
      _ = 102 * ((1 : Rat) / 2) ^ shift := by
        rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
        grind [Rat.mul_comm]
      _ <= (precisionAtStage n).val := hgeometric
  calc
    qabs h * 34 = (qabs h * 102) / 3 := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (precisionAtStage n).val / 3 :=
      Rat.mul_le_mul_of_nonneg_right hfull (Rat.le_of_lt
        ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 3)))

/-- The common-prefix cosine evaluator has derivative the common-prefix
negative-sine evaluator on `[-2,2]`.  Its stage takes the maximum of a
step-aware tail shift and an ordinary edge-term shift, avoiding any appeal to
real-number completeness. -/
def uniformRotationCosOnTwo_hasDerivativeOnInterval :
    HasDerivativeOnInterval uniformRotationCosOnTwo uniformRotationNegSinOnTwo where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := uniformRotationCosDerivativeStepPrecision
  evalPrecision := fun _x h n => uniformRotationCosDerivativeEvalPrecision h n
  close := by
    intro x h n hx hxh _hdx hh hsmall
    have hx' : (-2 : Rat) <= x /\ x <= 2 := by
      simpa [uniformRotationCosOnTwo, inDomainInterval] using hx
    have hxh' : (-2 : Rat) <= x + h /\ x + h <= 2 := by
      simpa [uniformRotationCosOnTwo, inDomainInterval] using hxh
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
    let stage : Nat := uniformRotationCosDerivativeEvalPrecision h n
    have hstage : uniformRotationCosDerivativeEvalPrecision h n = stage := rfl
    have htail : uniformRotationTailMagnitude stage <=
        eps.val * qabs h / 96 := by
      dsimp [stage, eps]
      simpa [uniformRotationCosQuotientTailTolerance] using
        uniformRotationTailMagnitude_le_cosQuotientTolerance h hh n
    have hedge : uniformRotationCosDerivativeEdgeMagnitude stage <= eps.val / 3 := by
      dsimp [stage, eps]
      simpa [uniformRotationCosDerivativeEdgeTolerance] using
        uniformRotationCosDerivativeEdge_le_tolerance h hh n
    have hfinite : qabs h * 34 <= eps.val / 3 := by
      dsimp [eps]
      exact uniformRotationCosDerivative_finite_error_le_third_precision n hsmall
    let epsHalf : QPos :=
      { val := eps.val / 2
        property := by
          rw [Rat.div_def]
          exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide)) }
    have htailHalf : uniformRotationTailMagnitude stage <=
        epsHalf.val * qabs h / 48 := by
      dsimp [epsHalf]
      calc
        uniformRotationTailMagnitude stage <= eps.val * qabs h / 96 := htail
        _ = (eps.val / 2) * qabs h / 48 := by
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]
    have htransport := uniformRotation_tail_transport_budgets
      hh habs epsHalf htailHalf
    have hbudget :
        (qabs h * 34 + uniformRotationCosDerivativeEdgeMagnitude stage) +
          2 * uniformRotationTailRadius stage / qabs h +
            uniformRotationTailRadius stage <= eps.val := by
      have htailBudget :
          8 * uniformRotationTailMagnitude stage / qabs h +
            4 * uniformRotationTailMagnitude stage <= epsHalf.val / 2 :=
        htransport.1
      calc
        (qabs h * 34 + uniformRotationCosDerivativeEdgeMagnitude stage) +
            2 * uniformRotationTailRadius stage / qabs h +
              uniformRotationTailRadius stage =
            (qabs h * 34 + uniformRotationCosDerivativeEdgeMagnitude stage) +
              (8 * uniformRotationTailMagnitude stage / qabs h +
                4 * uniformRotationTailMagnitude stage) := by
              unfold uniformRotationTailRadius
              grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
        _ <= (eps.val / 3 + eps.val / 3) + epsHalf.val / 2 :=
          rat_add_le_add (rat_add_le_add hfinite hedge) htailBudget
        _ <= eps.val := by
          dsimp [epsHalf]
          have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hquotientWidth :
        4 * uniformRotationTailRadius stage / qabs h <= eps.val := by
      have hhalfwidth :
          16 * uniformRotationTailMagnitude stage / qabs h <= epsHalf.val :=
        htransport.2.1
      calc
        4 * uniformRotationTailRadius stage / qabs h =
            16 * uniformRotationTailMagnitude stage / qabs h := by
              unfold uniformRotationTailRadius
              grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
        _ <= epsHalf.val := hhalfwidth
        _ <= eps.val := by
          dsimp [epsHalf]
          have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hderivativeWidth :
        2 * uniformRotationTailRadius stage <= eps.val := by
      have hhalfwidth : 8 * uniformRotationTailMagnitude stage <= epsHalf.val :=
        htransport.2.2
      calc
        2 * uniformRotationTailRadius stage =
            8 * uniformRotationTailMagnitude stage := by
              unfold uniformRotationTailRadius
              grind [Rat.mul_assoc]
        _ <= epsHalf.val := hhalfwidth
        _ <= eps.val := by
          dsimp [epsHalf]
          have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    have hcenter := uniformRotationCosCenter_secant_error_le_thirty_four_plus_edge
      hh hqx hqxh stage
    rw [hstage]
    unfold intervalNearAtPrecision
    rw [uniformRotationCosOnTwo_compute_around_for_cosine (x + h) hxh stage,
      uniformRotationCosOnTwo_compute_around_for_cosine x hx stage,
      uniformRotationNegSinOnTwo_compute_around_for_cosine x _hdx stage]
    change QInterval.NearAt
      (QInterval.differenceQuotient
        (QInterval.around ((uniformRotationCenter (x + h) stage).re)
          (uniformRotationTailRadius stage))
        (QInterval.around ((uniformRotationCenter x stage).re)
          (uniformRotationTailRadius stage)) h)
      (QInterval.around (-((uniformRotationCenter x stage).im))
        (uniformRotationTailRadius stage)) eps
    exact QInterval.around_differenceQuotient_near_around
      ((uniformRotationCenter x stage).re)
      ((uniformRotationCenter (x + h) stage).re)
      (-((uniformRotationCenter x stage).im))
      (uniformRotationTailRadius stage) h
      (qabs h * 34 + uniformRotationCosDerivativeEdgeMagnitude stage) eps hh
      (by
        unfold uniformRotationTailRadius
        exact Rat.mul_nonneg (by native_decide)
          (uniformRotationTailMagnitude_nonneg_for_cosine stage))
      (by simpa [Rat.sub_eq_add_neg] using hcenter)
      hbudget hquotientWidth hderivativeWidth


end RotationSeries
end ComputableAnalysis
