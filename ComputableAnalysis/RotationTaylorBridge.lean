import ComputableAnalysis.FinitePolynomialCalculus
import ComputableAnalysis.RotationSeries

/-!
# Finite Taylor bridge for rotation prefixes

The common bounded rotation evaluator uses the explicit even/odd factorial
prefixes from the finite Peano--Baker calculation.  This module identifies
those finite rational polynomials with the project-wide formal sine and cosine
Taylor streams.  It is deliberately finite: attaching the evaluator tail to a
finite secant estimate is the subsequent analytic step.
-/

namespace ComputableAnalysis

namespace RotationSeries

open FinitePolynomial

/-- Dividing a factorial term by its next rational index is exactly the next
factorial term.  Keeping this elementary rational identity separate makes the
two-step sine/cosine recurrence readable. -/
private theorem div_div_factorialRat_succ (a : Rat) (n : Nat) :
    (a / factorialRat n) / ((n + 1 : Nat) : Rat) =
      a / factorialRat (n + 1) := by
  rw [FormalPowerSeries.factorialRat_succ,
    Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm]

private theorem neg_div_eq_neg_div (a b : Rat) :
    -a / b = -(a / b) := by
  rw [Rat.div_def, Rat.neg_mul, Rat.div_def]

private theorem neg_div_div_factorialRat_succ (a : Rat) (n : Nat) :
    -(a / factorialRat n) / ((n + 1 : Nat) : Rat) =
      -a / factorialRat (n + 1) := by
  rw [neg_div_eq_neg_div, neg_div_eq_neg_div,
    div_div_factorialRat_succ]

/-- The formal sine/cosine coefficient streams have the expected alternating
factorial closed forms.  This is proved by their two-step rational recurrence,
not by an analytic trigonometric identity. -/
theorem trigCoefficient_closed (k : Nat) :
    FormalPowerSeries.sinCoeff (2 * k) = 0 /\
      FormalPowerSeries.cosCoeff (2 * k) =
        ((-1 : Rat) ^ k) / factorialRat (2 * k) /\
      FormalPowerSeries.sinCoeff (2 * k + 1) =
        ((-1 : Rat) ^ k) / factorialRat (2 * k + 1) /\
      FormalPowerSeries.cosCoeff (2 * k + 1) = 0 := by
  induction k with
  | zero => native_decide
  | succ k ih =>
      rcases ih with ⟨hsinEven, hcosEven, hsinOdd, hcosOdd⟩
      have hsinEven' : FormalPowerSeries.sinCoeff (2 * (k + 1)) = 0 := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          FormalPowerSeries.sinCoeff, hcosOdd]
        rw [Rat.div_def]
        exact Rat.zero_mul _
      have hcosEven' : FormalPowerSeries.cosCoeff (2 * (k + 1)) =
          ((-1 : Rat) ^ (k + 1)) / factorialRat (2 * (k + 1)) := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          FormalPowerSeries.cosCoeff, hsinOdd]
        rw [neg_div_div_factorialRat_succ, Rat.pow_succ]
        grind [Rat.neg_mul, Rat.mul_neg, Rat.mul_assoc, Rat.mul_comm]
      have hsinOdd' : FormalPowerSeries.sinCoeff (2 * (k + 1) + 1) =
          ((-1 : Rat) ^ (k + 1)) / factorialRat (2 * (k + 1) + 1) := by
        rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
          FormalPowerSeries.sinCoeff, hcosEven']
        rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
          div_div_factorialRat_succ, Rat.pow_succ]
      have hcosOdd' : FormalPowerSeries.cosCoeff (2 * (k + 1) + 1) = 0 := by
        rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
          FormalPowerSeries.cosCoeff, hsinEven']
        rw [Rat.div_def]
        exact Rat.zero_mul _
      exact ⟨hsinEven', hcosEven', hsinOdd', hcosOdd'⟩

/-- The finite Peano--Baker sine prefix is exactly the even-length Taylor
prefix of the formal sine stream.  The zero even coefficient is retained in
the Taylor presentation, so both sides have the same finite terms. -/
theorem sinePrefix_eq_taylorPrefix (T : Rat) (n : Nat) :
    LinearODE.RotationSystem.sinePrefix T n =
      FinitePolynomial.taylorPrefix FormalPowerSeries.sinCoeff (2 * n) T := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [LinearODE.RotationSystem.sinePrefix, ih]
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        FinitePolynomial.taylorPrefix_succ,
        FinitePolynomial.taylorPrefix_succ]
      have hcoeff := trigCoefficient_closed n
      rw [hcoeff.1, hcoeff.2.2.1]
      unfold LinearODE.RotationSystem.sineCoefficient
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The finite Peano--Baker cosine prefix is exactly the matching even-length
Taylor prefix of the formal cosine stream. -/
theorem cosinePrefix_eq_taylorPrefix (T : Rat) (n : Nat) :
    LinearODE.RotationSystem.cosinePrefix T n =
      FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff (2 * n) T := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [LinearODE.RotationSystem.cosinePrefix, ih]
      have hcoeff := trigCoefficient_closed n
      unfold LinearODE.RotationSystem.cosineCoefficient
      calc
        FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff (2 * n) T +
            (T ^ (2 * n) / factorialRat (2 * n)) * (-1) ^ n =
            FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff (2 * n) T +
              FormalPowerSeries.cosCoeff (2 * n) * T ^ (2 * n) := by
              rw [hcoeff.2.1]
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ =
            FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff (2 * n + 1) T := by
              exact (FinitePolynomial.taylorPrefix_succ
                FormalPowerSeries.cosCoeff (2 * n) T).symm
        _ = FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff (2 * n + 1) T +
            FormalPowerSeries.cosCoeff (2 * n + 1) * T ^ (2 * n + 1) := by
              rw [hcoeff.2.2.2]
              rw [Rat.zero_mul, Rat.add_zero]
        _ = FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
            ((2 * n + 1) + 1) T := by
              exact (FinitePolynomial.taylorPrefix_succ
                FormalPowerSeries.cosCoeff (2 * n + 1) T).symm
        _ = FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
            (2 * (n + 1)) T := by
              have hterms : (2 * n + 1) + 1 = 2 * (n + 1) := by omega
              rw [hterms]

/-- The coefficient-shift derivative of the finite sine prefix is the
matching finite cosine prefix.  This is an equality of rational polynomials;
the tail-enclosed derivative theorem needs an additional quotient budget. -/
theorem sinePrefixShift_eq_cosinePrefix (T : Rat) (n : Nat) :
    FinitePolynomial.taylorPrefixShift FormalPowerSeries.sinCoeff (2 * n) T =
      LinearODE.RotationSystem.cosinePrefix T n := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        FinitePolynomial.taylorPrefixShift_succ_eq_of_coefficientShift
          FormalPowerSeries.sinCoeff_hasCoefficientShift]
      rw [cosinePrefix_eq_taylorPrefix]
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        FinitePolynomial.taylorPrefix_succ FormalPowerSeries.cosCoeff (2 * n + 1) T]
      rw [(trigCoefficient_closed n).2.2.2]
      rw [Rat.zero_mul, Rat.add_zero]

/-- The imaginary center of the common bounded rotation evaluator is its
identified finite sine Taylor prefix. -/
theorem uniformRotationCenter_im_eq_sineTaylorPrefix (T : Rat) (n : Nat) :
    (uniformRotationCenter T n).im =
      FinitePolynomial.taylorPrefix FormalPowerSeries.sinCoeff
        (2 * (uniformRotationTailStart + n)) T := by
  unfold uniformRotationCenter complexPrefix
  exact sinePrefix_eq_taylorPrefix T (uniformRotationTailStart + n)

/-- The real center of the common bounded rotation evaluator is its
identified finite cosine Taylor prefix. -/
theorem uniformRotationCenter_re_eq_cosineTaylorPrefix (T : Rat) (n : Nat) :
    (uniformRotationCenter T n).re =
      FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
        (2 * (uniformRotationTailStart + n)) T := by
  unfold uniformRotationCenter complexPrefix
  exact cosinePrefix_eq_taylorPrefix T (uniformRotationTailStart + n)

/-- At every fixed common factorial stage, the rational sine-center secant
has the precise Taylor--Lagrange error supplied by the finite polynomial
calculus.  The coefficient still depends on the finite stage; bounding it
uniformly and transporting the evaluator tails are separate next steps. -/
theorem uniformRotationSinCenter_secant_error
    {x h : Rat} (hh : h ≠ 0) (hx : qabs x <= 2)
    (hxh : qabs (x + h) <= 2) (n : Nat) :
    qabs
      (((uniformRotationCenter (x + h) n).im -
          (uniformRotationCenter x n).im) / h -
        (uniformRotationCenter x n).re) <=
      qabs h *
        (FinitePolynomial.taylorPrefixSecantBound 2
          FormalPowerSeries.sinCoeff (by native_decide)
          (2 * (uniformRotationTailStart + n))).errorCoefficient := by
  let terms := 2 * (uniformRotationTailStart + n)
  have hfinite :=
    (FinitePolynomial.taylorPrefixSecantBound 2
      FormalPowerSeries.sinCoeff (by native_decide) terms).error_bound
      x h hh hx hxh
  have hshift := sinePrefixShift_eq_cosinePrefix x
    (uniformRotationTailStart + n)
  change qabs
      (((uniformRotationCenter (x + h) n).im -
          (uniformRotationCenter x n).im) / h -
        (uniformRotationCenter x n).re) <= _
  rw [uniformRotationCenter_im_eq_sineTaylorPrefix,
    uniformRotationCenter_im_eq_sineTaylorPrefix,
    uniformRotationCenter_re_eq_cosineTaylorPrefix]
  have hshift' : FinitePolynomial.taylorPrefixShift FormalPowerSeries.sinCoeff
      terms x = FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff terms x := by
    dsimp [terms]
    calc
      FinitePolynomial.taylorPrefixShift FormalPowerSeries.sinCoeff
          (2 * (uniformRotationTailStart + n)) x =
          LinearODE.RotationSystem.cosinePrefix x (uniformRotationTailStart + n) := hshift
      _ = FinitePolynomial.taylorPrefix FormalPowerSeries.cosCoeff
          (2 * (uniformRotationTailStart + n)) x :=
            cosinePrefix_eq_taylorPrefix x _
  rw [← hshift']
  simpa [terms] using hfinite

/-- The absolute value of the even factorial coefficient is exactly the
matching exponential coefficient.  This lets a finite sine secant budget use
the already checked factorial majorant without referring to a summed sine. -/
private theorem qabs_signed_even_factorial (n : Nat) :
    qabs (((-1 : Rat) ^ n) / factorialRat (2 * n)) =
      FormalPowerSeries.expCoeff (2 * n) := by
  unfold FormalPowerSeries.expCoeff
  rw [Rat.div_def, qabs_mul]
  have hsign : qabs ((-1 : Rat) ^ n) = 1 := by
    rw [RationalMajorant.qabs_pow_eq_pow_qabs]
    have hminus : qabs (-1 : Rat) = 1 := by native_decide
    rw [hminus]
    induction n with
    | zero => rfl
    | succ n ih => rw [Rat.pow_succ, ih, Rat.mul_one]
  rw [hsign, Rat.one_mul]
  calc
    qabs (factorialRat (2 * n))⁻¹ = (factorialRat (2 * n))⁻¹ :=
      qabs_eq_self_of_nonneg (Rat.le_of_lt ((Rat.inv_pos).2
        (RationalMajorant.factorialRat_pos _)))
    _ = 1 / factorialRat (2 * n) := by
      rw [Rat.div_def, Rat.one_mul]

/-- The accumulated error budget for the odd finite sine prefix.  It has one
summand for each even exponential coefficient and is therefore a sub-budget
of the factorial exponential secant coefficient. -/
private def sinePrefixSecantCoefficient : Nat -> Rat
  | 0 => 0
  | n + 1 =>
      sinePrefixSecantCoefficient n +
        qabs (FormalPowerSeries.expCoeff (2 * n)) *
          powerSecantErrorBound 2 (2 * n + 1)

/-- A finite sine/cosine prefix together with the deliberately chosen error
coefficient.  Recording the equality in the data avoids relying on the
proof-term presentation of the generic Taylor bound. -/
private structure SinePrefixSecantData (n : Nat) where
  bound : SecantDerivativeBound 2
    (fun x => LinearODE.RotationSystem.sinePrefix x n)
    (fun x => LinearODE.RotationSystem.cosinePrefix x n)
  errorCoefficient_eq : bound.errorCoefficient = sinePrefixSecantCoefficient n

private def sinePrefixSecantData : (n : Nat) -> SinePrefixSecantData n
  | 0 => by
      let B : SecantDerivativeBound 2
          (fun x => LinearODE.RotationSystem.sinePrefix x 0)
          (fun x => LinearODE.RotationSystem.cosinePrefix x 0) := by
        simpa [LinearODE.RotationSystem.sinePrefix,
          LinearODE.RotationSystem.cosinePrefix] using
          SecantDerivativeBound.constant 2 0
      exact { bound := B, errorCoefficient_eq := rfl }
  | n + 1 => by
      let F := sinePrefixSecantData n
      let G := SecantDerivativeBound.scaleRat
        (((-1 : Rat) ^ n) / factorialRat (2 * n))
        (normalizedMonomialSecantBound 2 (2 * n) (by native_decide))
      let H := F.bound.add G
      have hsource :
          (fun x => LinearODE.RotationSystem.sinePrefix x n +
            ((-1 : Rat) ^ n / factorialRat (2 * n)) *
              (x ^ (2 * n + 1) / ((2 * n + 1 : Nat) : Rat))) =
          fun x => LinearODE.RotationSystem.sinePrefix x (n + 1) := by
        funext x
        simp only [LinearODE.RotationSystem.sinePrefix,
          LinearODE.RotationSystem.sineCoefficient]
        rw [show 2 * n + 1 = (2 * n) + 1 by omega,
          FormalPowerSeries.factorialRat_succ]
        rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
        grind [Rat.mul_assoc, Rat.mul_comm]
      have htarget :
          (fun x => LinearODE.RotationSystem.cosinePrefix x n +
            ((-1 : Rat) ^ n / factorialRat (2 * n)) * x ^ (2 * n)) =
          fun x => LinearODE.RotationSystem.cosinePrefix x (n + 1) := by
        funext x
        simp only [LinearODE.RotationSystem.cosinePrefix,
          LinearODE.RotationSystem.cosineCoefficient]
        grind [Rat.mul_assoc, Rat.mul_comm]
      have hcoeff : H.errorCoefficient = sinePrefixSecantCoefficient (n + 1) := by
        dsimp [H, G, SecantDerivativeBound.add, SecantDerivativeBound.scaleRat,
          normalizedMonomialSecantBound]
        rw [F.errorCoefficient_eq, qabs_signed_even_factorial]
        rw [sinePrefixSecantCoefficient]
        have hexp : 0 <= FormalPowerSeries.expCoeff (2 * n) := by
          unfold FormalPowerSeries.expCoeff
          rw [Rat.div_def, Rat.one_mul]
          exact Rat.le_of_lt ((Rat.inv_pos).2
            (RationalMajorant.factorialRat_pos _))
        rw [qabs_eq_self_of_nonneg hexp]
      let B : SecantDerivativeBound 2
          (fun x => LinearODE.RotationSystem.sinePrefix x (n + 1))
          (fun x => LinearODE.RotationSystem.cosinePrefix x (n + 1)) :=
        { errorCoefficient := sinePrefixSecantCoefficient (n + 1)
          errorCoefficient_nonneg := by
            unfold sinePrefixSecantCoefficient
            apply Rat.add_nonneg
            · rw [← F.errorCoefficient_eq]
              exact F.bound.errorCoefficient_nonneg
            · exact Rat.mul_nonneg (qabs_nonneg _)
                (powerSecantErrorBound_nonneg (by native_decide) _)
          error_bound := by
            intro x h hh hx hxh
            have hH := H.error_bound x h hh hx hxh
            have hleft :
                qabs
                  ((LinearODE.RotationSystem.sinePrefix (x + h) (n + 1) -
                      LinearODE.RotationSystem.sinePrefix x (n + 1)) / h -
                    LinearODE.RotationSystem.cosinePrefix x (n + 1)) =
                  qabs
                    ((LinearODE.RotationSystem.sinePrefix (x + h) n +
                        ((-1 : Rat) ^ n / factorialRat (2 * n)) *
                          ((x + h) ^ (2 * n + 1) / ((2 * n + 1 : Nat) : Rat)) -
                      (LinearODE.RotationSystem.sinePrefix x n +
                        ((-1 : Rat) ^ n / factorialRat (2 * n)) *
                          (x ^ (2 * n + 1) / ((2 * n + 1 : Nat) : Rat))) ) / h -
                      (LinearODE.RotationSystem.cosinePrefix x n +
                        ((-1 : Rat) ^ n / factorialRat (2 * n)) * x ^ (2 * n))) := by
                  rw [← congrFun hsource (x + h), ← congrFun hsource x,
                    ← congrFun htarget x]
            calc
              qabs
                  ((LinearODE.RotationSystem.sinePrefix (x + h) (n + 1) -
                      LinearODE.RotationSystem.sinePrefix x (n + 1)) / h -
                    LinearODE.RotationSystem.cosinePrefix x (n + 1)) <=
                  qabs h * H.errorCoefficient := by
                    rw [hleft]
                    exact hH
              _ = qabs h * sinePrefixSecantCoefficient (n + 1) := by
                    rw [hcoeff] }
      exact { bound := B, errorCoefficient_eq := rfl }

private def sinePrefixSecantBound (n : Nat) := (sinePrefixSecantData n).bound

private theorem sinePrefixSecantBound_errorCoefficient (n : Nat) :
    (sinePrefixSecantBound n).errorCoefficient = sinePrefixSecantCoefficient n :=
  (sinePrefixSecantData n).errorCoefficient_eq

private theorem sinePrefixSecantCoefficient_le_exp (n : Nat) :
    sinePrefixSecantCoefficient n <=
      expTaylorPrefixSecantCoefficient (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep :
          sinePrefixSecantCoefficient (n + 1) <=
            expTaylorPrefixSecantCoefficient (2 * n + 1) := by
        rw [sinePrefixSecantCoefficient,
          show 2 * n + 1 = (2 * n) + 1 by omega,
          expTaylorPrefixSecantCoefficient]
        exact rat_add_le_add ih Rat.le_refl
      have hnext :
          expTaylorPrefixSecantCoefficient (2 * n + 1) <=
            expTaylorPrefixSecantCoefficient (2 * (n + 1)) := by
        have hterm : 0 <=
            qabs (FormalPowerSeries.expCoeff (2 * n + 1)) *
              powerSecantErrorBound 2 (2 * n + 1 + 1) :=
          Rat.mul_nonneg (qabs_nonneg _)
            (powerSecantErrorBound_nonneg (by native_decide) _)
        calc
          expTaylorPrefixSecantCoefficient (2 * n + 1) =
              expTaylorPrefixSecantCoefficient (2 * n + 1) + 0 := by
                rw [Rat.add_zero]
          _ <= expTaylorPrefixSecantCoefficient (2 * n + 1) +
              qabs (FormalPowerSeries.expCoeff (2 * n + 1)) *
                powerSecantErrorBound 2 (2 * n + 1 + 1) :=
              rat_add_le_add (Rat.le_refl) hterm
          _ = expTaylorPrefixSecantCoefficient ((2 * n + 1) + 1) := by
              rfl
          _ = expTaylorPrefixSecantCoefficient (2 * (n + 1)) := by
              have hterms : (2 * n + 1) + 1 = 2 * (n + 1) := by omega
              rw [hterms]
      exact Rat.le_trans hstep hnext

private theorem sinePrefixSecantCoefficient_le_thirty_four (n : Nat) :
    sinePrefixSecantCoefficient n <= 34 :=
  Rat.le_trans (sinePrefixSecantCoefficient_le_exp n)
    (expTaylorPrefixSecantCoefficient_le_thirty_four _)

/-- Every finite sine center in the common bounded rotation schedule has the
single rational secant budget `34 |h|`.  This is a finite-prefix theorem: the
separate evaluator-tail budget after dividing by `h` is still required before
claiming `sin' = cos`. -/
theorem uniformRotationSinCenter_secant_error_le_thirty_four
    {x h : Rat} (hh : h ≠ 0) (hx : qabs x <= 2)
    (hxh : qabs (x + h) <= 2) (n : Nat) :
    qabs
      (((uniformRotationCenter (x + h) n).im -
          (uniformRotationCenter x n).im) / h -
        (uniformRotationCenter x n).re) <=
      qabs h * 34 := by
  let terms := uniformRotationTailStart + n
  have hfinite := (sinePrefixSecantBound terms).error_bound x h hh hx hxh
  rw [sinePrefixSecantBound_errorCoefficient] at hfinite
  change qabs
      ((LinearODE.RotationSystem.sinePrefix (x + h) terms -
          LinearODE.RotationSystem.sinePrefix x terms) / h -
        LinearODE.RotationSystem.cosinePrefix x terms) <= _
  calc
    qabs
        ((LinearODE.RotationSystem.sinePrefix (x + h) terms -
            LinearODE.RotationSystem.sinePrefix x terms) / h -
          LinearODE.RotationSystem.cosinePrefix x terms) <=
        qabs h * sinePrefixSecantCoefficient terms := hfinite
    _ <= qabs h * 34 := Rat.mul_le_mul_of_nonneg_left
      (sinePrefixSecantCoefficient_le_thirty_four terms) (qabs_nonneg _)

end RotationSeries

end ComputableAnalysis
