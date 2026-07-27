import ComputableAnalysis.FTC
import ComputableAnalysis.FunctionDomains
import ComputableAnalysis.IntegralIdentities

/-!
# A certified logarithmic-series value

This module starts the logarithm layer with the concrete value
`logTwoSeries = 1 - 1/2 + 1/3 - ...`.  The construction is entirely finite
rational arithmetic: its `n`th box is enclosed by two adjacent alternating
partial sums.  Later in this module, a finite right-mesh/Darboux comparison
identifies it with the literal reciprocal integral at two, without invoking a
general FTC or completed-real construction.
-/

namespace ComputableAnalysis

namespace Logarithm

/-- Reciprocation reverses the positive rational order.  This finite lemma is
the only order calculation needed for the interval evaluator of `1/x`. -/
private theorem one_div_antitone_of_pos {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : a ≠ 0 := Rat.ne_of_gt ha
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have habpos : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        have hcancel : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hbne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= b := hab
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        have hcancel : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hane
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact habpos

/-- Interval evaluation of the positive reciprocal kernel on `[1,2]`. -/
def oneOverXOneTwoEvalInterval (I : QInterval) : QInterval :=
  { lo := 1 / I.hi, hi := 1 / I.lo }

private theorem oneOverXOneTwoEvalInterval_width
    {I : QInterval} (hI : subintervalOf I 1 2) :
    (oneOverXOneTwoEvalInterval I).width =
      I.width * (1 / (I.lo * I.hi)) := by
  rcases hI with ⟨hlo, _hord, _hhi⟩
  have hlopos : 0 < I.lo := by grind
  have hhipos : 0 < I.hi := by grind
  have hlone : I.lo ≠ 0 := Rat.ne_of_gt hlopos
  have hhine : I.hi ≠ 0 := Rat.ne_of_gt hhipos
  unfold oneOverXOneTwoEvalInterval QInterval.width
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have hlocancel : I.lo * I.lo⁻¹ = 1 := Rat.mul_inv_cancel I.lo hlone
  have hhicancel : I.hi * I.hi⁻¹ = 1 := Rat.mul_inv_cancel I.hi hhine
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The positive reciprocal kernel is interval-regular on `[1,2]`.

This is a literal rational certificate: an input interval of width at most
`1/(n+1)` is mapped to a reciprocal interval of no greater width.  It uses no
topological space, no completed real line, and no analytic import. -/
def oneOverXOnOneTwo_intervalRegular :
    IntervalRegularOn
      (RatFun.oneOverXOnPositiveInterval 1 2 (by native_decide)) := by
  refine
    { evalInterval := fun I _ _ => oneOverXOneTwoEvalInterval I
      inputPrecision := fun n => n + 1
      inputPrecision_pos := by
        intro n
        omega
      output_width := ?_
      contains_point_values := ?_ }
  · intro I hI n hwidth
    change (1 : Rat) <= I.lo /\ I.lo <= I.hi /\ I.hi <= 2 at hI
    rcases hI with ⟨hlo, hord, hhi⟩
    have hlopos : 0 < I.lo := by grind
    have hhipos : 0 < I.hi := by grind
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hprod_ge_one : 1 <= I.lo * I.hi := by
      calc
        (1 : Rat) = 1 * 1 := by native_decide
        _ <= I.lo * 1 := Rat.mul_le_mul_of_nonneg_right hlo (by native_decide)
        _ <= I.lo * I.hi := Rat.mul_le_mul_of_nonneg_left
          (Rat.le_trans hlo hord) (Rat.le_of_lt hlopos)
    have hrecip_le_one : 1 / (I.lo * I.hi) <= 1 := by
      have h := one_div_antitone_of_pos
        (a := (1 : Rat)) (b := I.lo * I.hi) (by native_decide) hprod_ge_one
      calc
        1 / (I.lo * I.hi) <= 1 / (1 : Rat) := h
        _ = 1 := by native_decide
    constructor
    · rw [oneOverXOneTwoEvalInterval_width ⟨hlo, hord, hhi⟩]
      have hrecip_nonneg : 0 <= 1 / (I.lo * I.hi) := by
        rw [Rat.div_def, Rat.one_mul]
        exact Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos hlopos hhipos))
      exact Rat.mul_nonneg hwidth_nonneg hrecip_nonneg
    · rw [oneOverXOneTwoEvalInterval_width ⟨hlo, hord, hhi⟩]
      calc
        I.width * (1 / (I.lo * I.hi)) <= I.width * 1 :=
          Rat.mul_le_mul_of_nonneg_left hrecip_le_one hwidth_nonneg
        _ = I.width := by grind
        _ <= 1 / (((n + 1 : Nat) : Rat)) := hwidth
  · intro I hI x hx n hxlo hxhi
    change (1 : Rat) <= I.lo /\ I.lo <= I.hi /\ I.hi <= 2 at hI
    rcases hI with ⟨hlo, _hord, _hhi⟩
    change (1 : Rat) <= x /\ x <= 2 at hx
    have hxpos : 0 < x := by grind
    change (oneOverXOneTwoEvalInterval I).ContainsInterval
      ((RatFun.oneOverXOnPositiveInterval 1 2 (by native_decide)).compute x hx n)
    rw [RatFun.oneOverXOnPositiveInterval_compute_eq 1 2
      (by native_decide) x hx n]
    unfold oneOverXOneTwoEvalInterval QInterval.ContainsInterval
    constructor
    · exact one_div_antitone_of_pos hxpos hxhi
    · exact one_div_antitone_of_pos (by grind) hxlo

/-- The reciprocal kernel `x ↦ 1/x` on `[1,2]` satisfies the project's
literal epsilon--delta continuity definition. -/
theorem oneOverXOnOneTwo_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn
      (RatFun.oneOverXOnPositiveInterval 1 2 (by native_decide)) :=
  oneOverXOnOneTwo_intervalRegular.epsilonDeltaContinuous

/-- The translated positive reciprocal kernel.  Its unit-interval integral is
the constructive candidate for `∫_1^2 dx/x`, under the affine substitution
`x = 1 + t`. -/
def logTwoKernel (t : Rat) : Rat :=
  1 / (1 + t)

/-- The left-endpoint Stieltjes sum for the square substitution `t = x^2`
on a uniform unit mesh.  Its limiting target is the reciprocal integral
`∫₀¹ dt / (1+t)`, but this definition is only a finite rational computation. -/
def logTwoSquareMeshStieltjesSum (meshStage terms : Nat) : Rat :=
  leftStieltjesSum
    (fun k => logTwoKernel
      (unitMeshPath meshStage k * unitMeshPath meshStage k))
    (fun k => unitMeshPath meshStage k * unitMeshPath meshStage k)
    terms

/-- The ordinary left-mesh sum which results from the formal substitution
`dt = 2x dx`.  It is kept separate from the Stieltjes sum so the finite
corner correction is visible rather than hidden in a limit argument. -/
def logTwoSquareMeshWeightedSum (meshStage : Nat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      logTwoSquareMeshWeightedSum meshStage terms +
        2 * unitMeshPath meshStage terms *
          logTwoKernel
            (unitMeshPath meshStage terms * unitMeshPath meshStage terms) *
          (1 / (meshStage : Rat))

/-- The exact finite correction in the square-substitution formula.  Each
cell carries the `dx²` part of `(x + dx)² - x²`. -/
def logTwoSquareMeshCorrection (meshStage : Nat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      logTwoSquareMeshCorrection meshStage terms +
        logTwoKernel
          (unitMeshPath meshStage terms * unitMeshPath meshStage terms) *
          ((1 / (meshStage : Rat)) * (1 / (meshStage : Rat)))

/-- The finite square-substitution identity.  It is the literal rational
version of `∫₀¹ dt/(1+t) = 2∫₀¹ x/(1+x²) dx`; the named correction is still
present at finite mesh size and will later be bounded by `1 / n`. -/
theorem logTwoSquareMesh_substitution_identity
    (meshStage terms : Nat) :
    logTwoSquareMeshStieltjesSum meshStage terms =
      logTwoSquareMeshWeightedSum meshStage terms +
        logTwoSquareMeshCorrection meshStage terms := by
  induction terms with
  | zero =>
      simp [logTwoSquareMeshStieltjesSum, logTwoSquareMeshWeightedSum,
        logTwoSquareMeshCorrection, leftStieltjesSum, Rat.zero_add]
  | succ terms ih =>
      change logTwoSquareMeshStieltjesSum meshStage terms +
          logTwoKernel
            (unitMeshPath meshStage terms * unitMeshPath meshStage terms) *
            (unitMeshPath meshStage (terms + 1) * unitMeshPath meshStage (terms + 1) -
              unitMeshPath meshStage terms * unitMeshPath meshStage terms) = _
      rw [ih,
        logTwoSquareMeshWeightedSum, logTwoSquareMeshCorrection]
      have hstep := unitMeshPath_step meshStage terms
      have hnext :
          unitMeshPath meshStage (terms + 1) =
            unitMeshPath meshStage terms + 1 / (meshStage : Rat) := by
        grind [Rat.sub_eq_add_neg]
      rw [hnext]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Positivity of the translated reciprocal kernel on the nonnegative ray. -/
theorem logTwoKernel_nonnegative {t : Rat} (ht : 0 <= t) :
    0 <= logTwoKernel t := by
  unfold logTwoKernel
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.le_of_lt ((Rat.inv_pos).2 (by grind))

/-- The translated reciprocal kernel never exceeds one on the nonnegative
ray.  This elementary bound gives the explicit square-substitution error
rate below. -/
theorem logTwoKernel_le_one {t : Rat} (ht : 0 <= t) :
    logTwoKernel t <= 1 := by
  have hden : 0 < 1 + t := by grind
  have h := one_div_antitone_of_pos (a := (1 : Rat)) (b := 1 + t)
    (by native_decide) (by grind)
  calc
    logTwoKernel t = 1 / (1 + t) := rfl
    _ <= 1 / (1 : Rat) := h
    _ = 1 := by native_decide

/-- On the nonnegative ray the translated reciprocal kernel is
nonincreasing.  This is the order half of the square-block comparison; its
Lipschitz estimate will bound the remaining difference within each block. -/
theorem logTwoKernel_antitone_nonnegative {s t : Rat}
    (hs : 0 <= s) (hst : s <= t) :
    logTwoKernel t <= logTwoKernel s := by
  unfold logTwoKernel
  exact one_div_antitone_of_pos (a := 1 + s) (b := 1 + t)
    (by grind) (by grind)

private theorem logTwoSquareMeshCorrection_nonnegative
    (meshStage terms : Nat) :
    0 <= logTwoSquareMeshCorrection meshStage terms := by
  cases meshStage with
  | zero =>
      induction terms with
      | zero =>
          exact Rat.le_refl
      | succ terms ih =>
          rw [logTwoSquareMeshCorrection]
          rw [show ((0 : Nat) : Rat) = 0 by native_decide]
          have hzero : 1 / (0 : Rat) = 0 := by native_decide
          rw [hzero]
          simpa only [Rat.zero_mul, Rat.mul_zero, Rat.add_zero] using ih
  | succ meshStage =>
      induction terms with
      | zero =>
          simp [logTwoSquareMeshCorrection]
      | succ terms ih =>
          rw [logTwoSquareMeshCorrection]
          apply Rat.add_nonneg ih
          apply Rat.mul_nonneg
          · apply logTwoKernel_nonnegative
            exact Rat.mul_nonneg (unitMeshPath_nonnegative (meshStage + 1) terms)
              (unitMeshPath_nonnegative (meshStage + 1) terms)
          · exact Rat.mul_nonneg
              (by simpa [Rat.div_def, Rat.one_mul] using
                Rat.le_of_lt ((Rat.inv_pos).2
                  ((Rat.natCast_pos).2 (Nat.succ_pos meshStage))))
              (by simpa [Rat.div_def, Rat.one_mul] using
                Rat.le_of_lt ((Rat.inv_pos).2
                  ((Rat.natCast_pos).2 (Nat.succ_pos meshStage))))

private theorem logTwoSquareMeshCorrection_le_terms_meshSquare
    (meshStage terms : Nat) (hmesh : 0 < meshStage) :
    logTwoSquareMeshCorrection meshStage terms <=
      (terms : Rat) * ((1 / (meshStage : Rat)) * (1 / (meshStage : Rat))) := by
  induction terms with
  | zero =>
      simp [logTwoSquareMeshCorrection]
  | succ terms ih =>
      rw [logTwoSquareMeshCorrection]
      have hsq_nonneg : 0 <=
          (1 / (meshStage : Rat)) * (1 / (meshStage : Rat)) := by
        exact Rat.mul_nonneg
          (by simpa [Rat.div_def, Rat.one_mul] using
            Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hmesh)))
          (by simpa [Rat.div_def, Rat.one_mul] using
            Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hmesh)))
      have hkernel :
          logTwoKernel
            (unitMeshPath meshStage terms * unitMeshPath meshStage terms) <= 1 :=
        logTwoKernel_le_one
          (Rat.mul_nonneg (unitMeshPath_nonnegative meshStage terms)
            (unitMeshPath_nonnegative meshStage terms))
      calc
        logTwoSquareMeshCorrection meshStage terms +
            logTwoKernel
              (unitMeshPath meshStage terms * unitMeshPath meshStage terms) *
              ((1 / (meshStage : Rat)) * (1 / (meshStage : Rat))) <=
            (terms : Rat) *
              ((1 / (meshStage : Rat)) * (1 / (meshStage : Rat))) +
            logTwoKernel
              (unitMeshPath meshStage terms * unitMeshPath meshStage terms) *
              ((1 / (meshStage : Rat)) * (1 / (meshStage : Rat))) :=
          Rat.add_le_add_right.mpr ih
        _ <= (terms : Rat) *
              ((1 / (meshStage : Rat)) * (1 / (meshStage : Rat))) +
            1 * ((1 / (meshStage : Rat)) * (1 / (meshStage : Rat))) :=
          Rat.add_le_add_left.mpr
            (Rat.mul_le_mul_of_nonneg_right hkernel hsq_nonneg)
        _ = ((terms + 1 : Nat) : Rat) *
              ((1 / (meshStage : Rat)) * (1 / (meshStage : Rat))) := by
          rw [Rat.natCast_add]
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]

/-- On an `n`-cell unit mesh, the finite square-substitution correction is
between zero and `1/n`.  This supplies a computable rate for the later
change-of-variables bridge, without invoking a general substitution theorem. -/
theorem logTwoSquareMeshCorrection_le_one_div
    (meshStage : Nat) (hmesh : 0 < meshStage) :
    0 <= logTwoSquareMeshCorrection meshStage meshStage /\
      logTwoSquareMeshCorrection meshStage meshStage <= 1 / (meshStage : Rat) := by
  constructor
  · exact logTwoSquareMeshCorrection_nonnegative meshStage meshStage
  · calc
      logTwoSquareMeshCorrection meshStage meshStage <=
          (meshStage : Rat) *
            ((1 / (meshStage : Rat)) * (1 / (meshStage : Rat))) :=
        logTwoSquareMeshCorrection_le_terms_meshSquare meshStage meshStage hmesh
      _ = 1 / (meshStage : Rat) := by
        have hne : (meshStage : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hmesh)
        rw [Rat.div_def, Rat.one_mul]
        have hcancel : (meshStage : Rat) * (meshStage : Rat)⁻¹ = 1 :=
          Rat.mul_inv_cancel _ hne
        grind [Rat.mul_assoc, Rat.mul_comm]

/-- The pullback of the translated reciprocal kernel along the square map.
Its unit-interval integral is the finite-mesh target twice the integral of
x/(1+x²) in the arctangent--logarithm route. -/
def logTwoSquarePullback (x : Rat) : Rat :=
  2 * x * logTwoKernel (x * x)

/-- The first strip in the arctangent integration-by-parts route: the
rational kernel `x/(1+x²)`, expressed through the already certified positive
reciprocal kernel. -/
def arctanLogKernel (x : Rat) : Rat :=
  x * logTwoKernel (x * x)

theorem logTwoSquarePullback_eq_two_mul_arctanLogKernel (x : Rat) :
    logTwoSquarePullback x = 2 * arctanLogKernel x := by
  unfold logTwoSquarePullback arctanLogKernel
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- Exact rational factorization of the pullback difference.  It is the
finite algebra behind the Lipschitz certificate below. -/
private theorem logTwoSquarePullback_difference (s t : Rat) :
    logTwoSquarePullback s - logTwoSquarePullback t =
      (2 * (s - t) * (1 - s * t)) /
        ((1 + s * s) * (1 + t * t)) := by
  have hspos : 0 < 1 + s * s := by
    have hsq := RationalCircle.Stage.ratSquare_nonneg s
    grind
  have htpos : 0 < 1 + t * t := by
    have hsq := RationalCircle.Stage.ratSquare_nonneg t
    grind
  have hsne : 1 + s * s ≠ 0 := Rat.ne_of_gt hspos
  have htne : 1 + t * t ≠ 0 := Rat.ne_of_gt htpos
  unfold logTwoSquarePullback logTwoKernel
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have hscancel : (1 + s * s) * (1 + s * s)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hsne
  have htcancel : (1 + t * t) * (1 + t * t)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ htne
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The square pullback is two-Lipschitz on the unit interval.  This is a
literal rational inequality, so its integral can use the same finite
Lipschitz--Darboux construction as the reciprocal endpoint. -/
theorem logTwoSquarePullback_lipschitz_on_unit :
    Integral.LipschitzOnUnit logTwoSquarePullback 2 := by
  constructor
  · native_decide
  · intro s t hs0 hs1 ht0 ht1
    let d : Rat := (1 + s * s) * (1 + t * t)
    have hsone : 1 <= 1 + s * s := by
      have hsq := RationalCircle.Stage.ratSquare_nonneg s
      grind
    have htone : 1 <= 1 + t * t := by
      have hsq := RationalCircle.Stage.ratSquare_nonneg t
      grind
    have hdpos : 0 < d := by
      dsimp [d]
      exact Rat.mul_pos (by grind) (by grind)
    have hdone : 1 <= d := by
      dsimp [d]
      have hsnonneg : 0 <= 1 + s * s := Rat.le_trans (by native_decide) hsone
      calc
        1 = 1 * 1 := by native_decide
        _ <= (1 + s * s) * 1 :=
          Rat.mul_le_mul_of_nonneg_right hsone (by native_decide)
        _ <= (1 + s * s) * (1 + t * t) :=
          Rat.mul_le_mul_of_nonneg_left htone hsnonneg
    have hdinv0 : 0 <= d⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hdpos)
    have hdinv : d⁻¹ <= 1 := by
      apply Rat.le_of_mul_le_mul_right (c := d)
      · calc
          d⁻¹ * d = d * d⁻¹ := by rw [Rat.mul_comm]
          _ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdpos)
          _ <= 1 * d := by simpa using hdone
      · exact hdpos
    have hproduct0 : 0 <= s * t := Rat.mul_nonneg hs0 ht0
    have hproduct : s * t <= 1 := by
      calc
        s * t <= 1 * t :=
          Rat.mul_le_mul_of_nonneg_right hs1 ht0
        _ <= 1 * 1 :=
          Rat.mul_le_mul_of_nonneg_left ht1 (by native_decide)
        _ = 1 := by native_decide
    have hfactor0 : 0 <= 1 - s * t := by grind
    have hfactor : 1 - s * t <= 1 := by grind
    have hfactorTimes : (1 - s * t) * d⁻¹ <= 1 := by
      calc
        (1 - s * t) * d⁻¹ <= 1 * d⁻¹ :=
          Rat.mul_le_mul_of_nonneg_right hfactor hdinv0
        _ <= 1 * 1 :=
          Rat.mul_le_mul_of_nonneg_left hdinv (by native_decide)
        _ = 1 := by native_decide
    rw [logTwoSquarePullback_difference]
    change qabs ((2 * (s - t) * (1 - s * t)) / d) <=
      2 * qabs (t - s)
    rw [Rat.div_def, qabs_mul, qabs_mul,
      qabs_eq_self_of_nonneg hfactor0,
      qabs_eq_self_of_nonneg hdinv0]
    have htwo : qabs (2 : Rat) = 2 := by native_decide
    rw [qabs_mul, htwo]
    calc
      2 * qabs (s - t) * (1 - s * t) * d⁻¹ =
          2 * qabs (s - t) * ((1 - s * t) * d⁻¹) := by
        rw [Rat.mul_assoc]
      _ <= 2 * qabs (s - t) * 1 :=
        Rat.mul_le_mul_of_nonneg_left hfactorTimes
          (Rat.mul_nonneg (by native_decide) (qabs_nonneg _))
      _ = 2 * qabs (t - s) := by
        have hneg : s - t = -(t - s) := by
          grind [Rat.sub_eq_add_neg]
        rw [hneg, qabs_neg, Rat.mul_one]

/-- The first integration-by-parts kernel is one-Lipschitz on the unit
interval.  Rather than repeat a denominator estimate, this divides the
already checked two-Lipschitz square-pullback bound by its exact factor two. -/
theorem arctanLogKernel_lipschitz_on_unit :
    Integral.LipschitzOnUnit arctanLogKernel 1 := by
  constructor
  · native_decide
  · intro s t hs0 hs1 ht0 ht1
    have hpull := logTwoSquarePullback_lipschitz_on_unit.2
      s t hs0 hs1 ht0 ht1
    have hdiff : logTwoSquarePullback s - logTwoSquarePullback t =
        2 * (arctanLogKernel s - arctanLogKernel t) := by
      rw [logTwoSquarePullback_eq_two_mul_arctanLogKernel,
        logTwoSquarePullback_eq_two_mul_arctanLogKernel]
      grind [Rat.sub_eq_add_neg, Rat.mul_add]
    rw [hdiff, qabs_mul] at hpull
    have htwo : qabs (2 : Rat) = 2 := by native_decide
    rw [htwo] at hpull
    apply Rat.le_of_mul_le_mul_left (c := (2 : Rat))
    · simpa [Rat.one_mul] using hpull
    · native_decide

/-- The complementary rational strip in the arctangent integration-by-parts
route.  Its later identification with the integral of `arctan` needs the
separate finite Fubini/product-derivative certificate; at this point it is
only the literal rational kernel that complements `x/(1+x^2)`. -/
def arctanComplementKernel (x : Rat) : Rat :=
  (1 - x) * logTwoKernel (x * x)

/-- Exact rational factorization of the complementary-strip difference. -/
private theorem arctanComplementKernel_difference (s t : Rat) :
    arctanComplementKernel s - arctanComplementKernel t =
      ((t - s) * (1 + s + t - s * t)) /
        ((1 + s * s) * (1 + t * t)) := by
  have hspos : 0 < 1 + s * s := by
    have hsq := RationalCircle.Stage.ratSquare_nonneg s
    grind
  have htpos : 0 < 1 + t * t := by
    have hsq := RationalCircle.Stage.ratSquare_nonneg t
    grind
  have hsne : 1 + s * s ≠ 0 := Rat.ne_of_gt hspos
  have htne : 1 + t * t ≠ 0 := Rat.ne_of_gt htpos
  unfold arctanComplementKernel logTwoKernel
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have hscancel : (1 + s * s) * (1 + s * s)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hsne
  have htcancel : (1 + t * t) * (1 + t * t)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ htne
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The complementary rational strip is three-Lipschitz on the unit
interval.  This certificate is a direct finite denominator estimate. -/
theorem arctanComplementKernel_lipschitz_on_unit :
    Integral.LipschitzOnUnit arctanComplementKernel 3 := by
  constructor
  · native_decide
  · intro s t hs0 hs1 ht0 ht1
    let d : Rat := (1 + s * s) * (1 + t * t)
    let c : Rat := 1 + s + t - s * t
    have hsone : 1 <= 1 + s * s := by
      have hsq := RationalCircle.Stage.ratSquare_nonneg s
      grind
    have htone : 1 <= 1 + t * t := by
      have hsq := RationalCircle.Stage.ratSquare_nonneg t
      grind
    have hdpos : 0 < d := by
      dsimp [d]
      exact Rat.mul_pos (by grind) (by grind)
    have hdone : 1 <= d := by
      dsimp [d]
      have hsnonneg : 0 <= 1 + s * s := Rat.le_trans (by native_decide) hsone
      calc
        1 = 1 * 1 := by native_decide
        _ <= (1 + s * s) * 1 :=
          Rat.mul_le_mul_of_nonneg_right hsone (by native_decide)
        _ <= (1 + s * s) * (1 + t * t) :=
          Rat.mul_le_mul_of_nonneg_left htone hsnonneg
    have hdinv0 : 0 <= d⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hdpos)
    have hdinv : d⁻¹ <= 1 := by
      apply Rat.le_of_mul_le_mul_right (c := d)
      · calc
          d⁻¹ * d = d * d⁻¹ := by rw [Rat.mul_comm]
          _ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdpos)
          _ <= 1 * d := by simpa using hdone
      · exact hdpos
    have hproduct0 : 0 <= s * t := Rat.mul_nonneg hs0 ht0
    have hproduct : s * t <= 1 := by
      calc
        s * t <= 1 * t :=
          Rat.mul_le_mul_of_nonneg_right hs1 ht0
        _ <= 1 * 1 :=
          Rat.mul_le_mul_of_nonneg_left ht1 (by native_decide)
        _ = 1 := by native_decide
    have hc0 : 0 <= c := by
      dsimp [c]
      have hrest : 0 <= 1 - s * t := by grind
      grind [Rat.sub_eq_add_neg]
    have hc : c <= 3 := by
      dsimp [c]
      calc
        1 + s + t - s * t <= 1 + s + t := by
          have : 0 <= s * t := hproduct0
          grind [Rat.sub_eq_add_neg]
        _ <= 1 + 1 + 1 := by
          exact rat_add_le_add
            (Rat.add_le_add_left.mpr hs1) ht1
        _ = 3 := by native_decide
    have hctimes : c * d⁻¹ <= 3 := by
      calc
        c * d⁻¹ <= 3 * d⁻¹ :=
          Rat.mul_le_mul_of_nonneg_right hc hdinv0
        _ <= 3 * 1 :=
          Rat.mul_le_mul_of_nonneg_left hdinv (by native_decide)
        _ = 3 := by native_decide
    rw [arctanComplementKernel_difference]
    change qabs ((t - s) * c / d) <= 3 * qabs (t - s)
    rw [Rat.div_def, qabs_mul, qabs_mul,
      qabs_eq_self_of_nonneg hc0,
      qabs_eq_self_of_nonneg hdinv0]
    calc
      qabs (t - s) * c * d⁻¹ = qabs (t - s) * (c * d⁻¹) := by
        rw [Rat.mul_assoc]
      _ <= qabs (t - s) * 3 :=
        Rat.mul_le_mul_of_nonneg_left hctimes (qabs_nonneg _)
      _ = 3 * qabs (t - s) := by rw [Rat.mul_comm]

/-- The two rational strips add pointwise to the usual arctangent kernel. -/
theorem arctanComplementKernel_add_arctanLogKernel (x : Rat) :
    arctanComplementKernel x + arctanLogKernel x =
      1 / (1 + x * x) := by
  unfold arctanComplementKernel arctanLogKernel logTwoKernel
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- A deliberately slack version of the existing two-Lipschitz arctangent
kernel certificate.  It lets the exact four-Lipschitz sum box be compared to
the sharper existing two-Lipschitz box by their common finite Riemann sum. -/
private theorem arctanKernel_lipschitz_on_unit_four :
    Integral.LipschitzOnUnit (fun x : Rat => 1 / (1 + x * x)) 4 := by
  constructor
  · native_decide
  · intro s t hs0 hs1 ht0 ht1
    have htwo := IntegralIdentities.oneOverOnePlusSquare_lipschitz_on_unit.2
      s t hs0 hs1 ht0 ht1
    calc
      qabs ((1 / (1 + s * s)) - (1 / (1 + t * t))) <=
          2 * qabs (t - s) := htwo
      _ <= 4 * qabs (t - s) := by
        have habs : 0 <= qabs (t - s) := qabs_nonneg _
        exact Rat.mul_le_mul_of_nonneg_right (by native_decide) habs

/-- A local finite-fold congruence lemma used to put square-substitution sums
in the same literal mesh normal form as the Darboux constructor. -/
private theorem finiteFoldl_eq_of_pointwise
    (f g : Rat -> Nat -> Rat)
    (h : ∀ total k, f total k = g total k)
    (xs : List Nat) (initial : Rat) :
    xs.foldl f initial = xs.foldl g initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl]
      rw [h initial x]
      exact ih (g initial x)

private theorem logTwoSquareMeshWeightedSum_eq_foldl
    (meshStage terms : Nat) :
    logTwoSquareMeshWeightedSum meshStage terms =
      (List.range terms).foldl
        (fun total k =>
          total + 2 * unitMeshPath meshStage k *
            logTwoKernel (unitMeshPath meshStage k * unitMeshPath meshStage k) *
            (1 / (meshStage : Rat))) 0 := by
  induction terms with
  | zero =>
      rfl
  | succ terms ih =>
      rw [logTwoSquareMeshWeightedSum, ih, List.range_succ,
        List.foldl_append]
      rfl

/-- The weighted square-substitution mesh is exactly the ordinary uniform
left Riemann sum for the square pullback. -/
theorem logTwoSquareMeshWeightedSum_eq_uniformLeftEndpoint
    (meshStage : Nat) :
    logTwoSquareMeshWeightedSum meshStage meshStage =
      IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        logTwoSquarePullback meshStage := by
  rw [logTwoSquareMeshWeightedSum_eq_foldl]
  unfold IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
  apply finiteFoldl_eq_of_pointwise
  intro total k
  unfold logTwoSquarePullback
  simp only [unitMeshPath]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The certified unit-interval integral representation of the square
pullback.  It has literal finite Lipschitz--Darboux boxes and does not use a
substitution axiom. -/
def logTwoSquarePullbackIntegral : RealRaw :=
  Integral.integralFor
    (FunctionOnInterval.exactRat logTwoSquarePullback 0 1)
    (IntegralIdentities.LipschitzDyadic.construction logTwoSquarePullback 2
      logTwoSquarePullback_lipschitz_on_unit)

theorem logTwoSquarePullbackIntegral_valid :
    logTwoSquarePullbackIntegral.Valid :=
  Integral.integralFor_valid
    (FunctionOnInterval.exactRat logTwoSquarePullback 0 1)
    (IntegralIdentities.LipschitzDyadic.construction logTwoSquarePullback 2
      logTwoSquarePullback_lipschitz_on_unit)

theorem logTwoSquarePullbackIntegral_compute_eq (stage : Nat) :
    logTwoSquarePullbackIntegral.compute stage =
      IntegralIdentities.LipschitzDyadic.compute logTwoSquarePullback 2 stage :=
  rfl

/-- A literal certified integral for the first arctangent--logarithm
integration-by-parts strip.  It uses the same finite Lipschitz--Darboux
algorithm as the square pullback, with its sharper unit Lipschitz constant. -/
def arctanLogKernelIntegral : RealRaw :=
  Integral.integralFor
    (FunctionOnInterval.exactRat arctanLogKernel 0 1)
    (IntegralIdentities.LipschitzDyadic.construction arctanLogKernel 1
      arctanLogKernel_lipschitz_on_unit)

theorem arctanLogKernelIntegral_valid :
    arctanLogKernelIntegral.Valid :=
  Integral.integralFor_valid
    (FunctionOnInterval.exactRat arctanLogKernel 0 1)
    (IntegralIdentities.LipschitzDyadic.construction arctanLogKernel 1
      arctanLogKernel_lipschitz_on_unit)

theorem arctanLogKernelIntegral_compute_eq (stage : Nat) :
    arctanLogKernelIntegral.compute stage =
      IntegralIdentities.LipschitzDyadic.compute arctanLogKernel 1 stage :=
  rfl

/-- A literal certified integral for the rational strip complementary to
`x/(1+x^2)`.  It is intentionally named as a strip rather than as an
arctangent integral: the later finite Fubini/product-derivative proof is what
will identify it with \(\int_0^1\arctan(x)\,dx\). -/
def arctanComplementKernelIntegral : RealRaw :=
  Integral.integralFor
    (FunctionOnInterval.exactRat arctanComplementKernel 0 1)
    (IntegralIdentities.LipschitzDyadic.construction arctanComplementKernel 3
      arctanComplementKernel_lipschitz_on_unit)

theorem arctanComplementKernelIntegral_valid :
    arctanComplementKernelIntegral.Valid :=
  Integral.integralFor_valid
    (FunctionOnInterval.exactRat arctanComplementKernel 0 1)
    (IntegralIdentities.LipschitzDyadic.construction arctanComplementKernel 3
      arctanComplementKernel_lipschitz_on_unit)

theorem arctanComplementKernelIntegral_compute_eq (stage : Nat) :
    arctanComplementKernelIntegral.compute stage =
      IntegralIdentities.LipschitzDyadic.compute arctanComplementKernel 3 stage :=
  rfl

/-- The literal finite triangular mesh behind the iterated integral of the
arctangent kernel.  At this point it is named for the kernel rather than for
`arctan`: identifying its growing inner sums with arctangent is the separate
effective-FTC/product-derivative step. -/
def arctanKernelTriangleCandidateCompute (stage : Nat) : QInterval :=
  let mesh := 2 ^ stage
  let sum := IntegralIdentities.LipschitzDyadic.uniformTriangleRightSum
    (fun x : Rat => 1 / (1 + x * x)) mesh mesh
  { lo := sum, hi := sum }

/-- The direct, unnormalized triangular mesh computation. -/
def arctanKernelTriangleCandidate : RealRaw where
  compute := arctanKernelTriangleCandidateCompute

theorem arctanKernelTriangleCandidateCompute_width (stage : Nat) :
    (arctanKernelTriangleCandidateCompute stage).width = 0 := by
  unfold arctanKernelTriangleCandidateCompute
  simp only [QInterval.width]
  grind [Rat.sub_eq_add_neg]

theorem arctanKernelTriangleCandidate_widthsShrink :
    RealRaw.WidthsShrinkToZero arctanKernelTriangleCandidate.compute := by
  intro eps
  refine ⟨0, ?_⟩
  intro stage _
  rw [show arctanKernelTriangleCandidate.compute stage =
      arctanKernelTriangleCandidateCompute stage by rfl,
    arctanKernelTriangleCandidateCompute_width]
  exact Rat.le_of_lt eps.property

/-- The triangle reindexing theorem places the direct mesh calculation inside
the certified complementary-strip box at every common dyadic stage. -/
theorem arctanKernelTriangleCandidate_overlaps_complementKernelIntegral
    (stage : Nat) :
    QInterval.Overlaps
      (arctanKernelTriangleCandidate.compute stage)
      (arctanComplementKernelIntegral.compute stage) := by
  have hmesh : 0 < 2 ^ stage :=
    Nat.pow_pos (by omega : 0 < 2)
  have htriangle :=
    IntegralIdentities.LipschitzDyadic.uniformTriangleRightSum_eq_complementUniformLeftEndpointSum
      (fun x : Rat => 1 / (1 + x * x)) (2 ^ stage) hmesh
  have hcontains :=
    IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
      arctanComplementKernel_lipschitz_on_unit stage
  unfold arctanKernelTriangleCandidate
    arctanKernelTriangleCandidateCompute
  dsimp only
  rw [arctanComplementKernelIntegral_compute_eq, htriangle]
  exact ⟨hcontains.2, hcontains.1⟩

theorem arctanKernelTriangleCandidate_equiv_complementKernelIntegral :
    arctanKernelTriangleCandidate.Equiv arctanComplementKernelIntegral := by
  intro stage
  apply (RealRaw.compareAt_overlap_iff
    arctanKernelTriangleCandidate arctanComplementKernelIntegral stage stage).2
  exact arctanKernelTriangleCandidate_overlaps_complementKernelIntegral stage

/-- The public rational radius covering the complementary-strip Darboux box.
It is also the visible convergence rate for the direct triangular mesh. -/
def arctanKernelTriangleStabilizationRadius (stage : Nat) : Rat :=
  6 * (1 / (((2 ^ stage : Nat) : Rat)))

theorem arctanKernelTriangleStabilizationRadius_eq_complementKernelIntegral_width
    (stage : Nat) :
    arctanKernelTriangleStabilizationRadius stage =
      (arctanComplementKernelIntegral.compute stage).width := by
  unfold arctanKernelTriangleStabilizationRadius
  rw [arctanComplementKernelIntegral_compute_eq,
    IntegralIdentities.LipschitzDyadic.compute_width]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem arctanKernelTriangleStabilizationRadius_covers_complementKernelIntegral
    (stage : Nat) :
    (arctanComplementKernelIntegral.compute stage).width <=
      arctanKernelTriangleStabilizationRadius stage := by
  rw [arctanKernelTriangleStabilizationRadius_eq_complementKernelIntegral_width]
  exact Rat.le_refl

theorem arctanKernelTriangleStabilizationRadius_shrinks :
    ShrinksToZero arctanKernelTriangleStabilizationRadius := by
  intro eps
  obtain ⟨N, hN⟩ := arctanComplementKernelIntegral_valid.2.2 eps
  refine ⟨N, ?_⟩
  intro stage hstage
  rw [arctanKernelTriangleStabilizationRadius_eq_complementKernelIntegral_width]
  exact hN stage hstage

/-- A valid direct-only raw representative of the finite triangular mesh.
Runtime evaluation reads only rational triangle sums and the public radius;
the complementary-strip integral is used only to certify the enclosure. -/
def arctanKernelTriangleRaw : RealRaw :=
  RealRaw.prefixStabilize arctanKernelTriangleCandidate
    arctanKernelTriangleStabilizationRadius

theorem arctanKernelTriangleRaw_valid : arctanKernelTriangleRaw.Valid := by
  unfold arctanKernelTriangleRaw
  exact RealRaw.prefixStabilize_valid
    arctanKernelTriangleCandidate_widthsShrink
    arctanComplementKernelIntegral_valid
    arctanKernelTriangleCandidate_equiv_complementKernelIntegral
    arctanKernelTriangleStabilizationRadius_covers_complementKernelIntegral
    arctanKernelTriangleStabilizationRadius_shrinks

theorem arctanKernelTriangleRaw_equiv_complementKernelIntegral :
    arctanKernelTriangleRaw.Equiv arctanComplementKernelIntegral := by
  unfold arctanKernelTriangleRaw
  exact RealRaw.prefixStabilize_equiv_anchor
    arctanComplementKernelIntegral_valid
    arctanKernelTriangleCandidate_equiv_complementKernelIntegral
    arctanKernelTriangleStabilizationRadius_covers_complementKernelIntegral

/-- The raw sum of the two literal strip integrals is, stage by stage, the
four-Lipschitz Darboux box for the arctangent kernel.  This is the finite
additivity bridge that precedes any claim about the integral of arctangent. -/
theorem arctanStripIntegrals_add_compute_eq_arctanKernel (stage : Nat) :
    (arctanComplementKernelIntegral + arctanLogKernelIntegral).compute stage =
      IntegralIdentities.LipschitzDyadic.compute
        (fun x : Rat => 1 / (1 + x * x)) 4 stage := by
  change
    { lo := (arctanComplementKernelIntegral.compute stage).lo +
        (arctanLogKernelIntegral.compute stage).lo,
      hi := (arctanComplementKernelIntegral.compute stage).hi +
        (arctanLogKernelIntegral.compute stage).hi } =
      IntegralIdentities.LipschitzDyadic.compute
        (fun x : Rat => 1 / (1 + x * x)) 4 stage
  rw [arctanComplementKernelIntegral_compute_eq,
    arctanLogKernelIntegral_compute_eq]
  symm
  have hadd := IntegralIdentities.LipschitzDyadic.compute_add
    arctanComplementKernel arctanLogKernel 3 1 stage
  have hkernel : (fun x : Rat =>
      arctanComplementKernel x + arctanLogKernel x) =
      (fun x : Rat => 1 / (1 + x * x)) := by
    funext x
    exact arctanComplementKernel_add_arctanLogKernel x
  rw [hkernel] at hadd
  exact hadd

/-- The two-strip sum agrees with the already certified arctangent-kernel
integral.  Both finite boxes contain the same literal uniform left Riemann
sum; no abstract integral-linearity or completeness principle is used. -/
theorem arctanStripIntegrals_add_equiv_arctanKernelIntegral :
    (arctanComplementKernelIntegral + arctanLogKernelIntegral).Equiv
      IntegralIdentities.arctanKernelLipschitzIntegral := by
  apply RealRaw.sameStageOverlap_equiv
  intro stage
  apply (RealRaw.compareAt_overlap_iff
    (arctanComplementKernelIntegral + arctanLogKernelIntegral)
    IntegralIdentities.arctanKernelLipschitzIntegral stage stage).mpr
  rw [arctanStripIntegrals_add_compute_eq_arctanKernel,
    IntegralIdentities.arctanKernelLipschitzIntegral_compute_eq]
  have hfour :=
    IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
      arctanKernel_lipschitz_on_unit_four stage
  have htwo :=
    IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
      IntegralIdentities.oneOverOnePlusSquare_lipschitz_on_unit stage
  exact ⟨Rat.le_trans hfour.1 htwo.2, Rat.le_trans htwo.1 hfour.2⟩

/-- Stage by stage, the existing square-pullback boxes are exactly twice the
boxes for the first arctangent--logarithm strip.  Thus this bridge is a
finite interval equality, not a later appeal to integral linearity. -/
theorem logTwoSquarePullbackIntegral_compute_eq_two_arctanLogKernelIntegral
    (stage : Nat) :
    logTwoSquarePullbackIntegral.compute stage =
      RealRaw.scaleRatCompute 2 arctanLogKernelIntegral stage := by
  rw [logTwoSquarePullbackIntegral_compute_eq]
  unfold RealRaw.scaleRatCompute
  have htwo : 0 <= (2 : Rat) := by native_decide
  simp only [if_pos htwo]
  rw [arctanLogKernelIntegral_compute_eq]
  have hscale := IntegralIdentities.LipschitzDyadic.compute_natScale
    arctanLogKernel 1 2 stage
  have hfunction : (fun x => ((2 : Nat) : Rat) * arctanLogKernel x) =
      logTwoSquarePullback := by
    funext x
    exact (logTwoSquarePullback_eq_two_mul_arctanLogKernel x).symm
  rw [hfunction] at hscale
  simpa using hscale

theorem logTwoSquarePullbackIntegral_width (stage : Nat) :
    (logTwoSquarePullbackIntegral.compute stage).width =
      4 * (1 / (((2 ^ stage : Nat) : Rat))) := by
  rw [logTwoSquarePullbackIntegral_compute_eq,
    IntegralIdentities.LipschitzDyadic.compute_width]
  have hfour : (2 : Rat) * ((2 : Nat) : Rat) = 4 := by native_decide
  rw [hfour]

/-- At every dyadic stage, the exact weighted square-substitution sum lies in
the corresponding certified pullback-integral box. -/
theorem logTwoSquarePullbackIntegral_contains_weightedMesh
    (stage : Nat) :
    (logTwoSquarePullbackIntegral.compute stage).ContainsInterval
      { lo := logTwoSquareMeshWeightedSum (2 ^ stage) (2 ^ stage),
        hi := logTwoSquareMeshWeightedSum (2 ^ stage) (2 ^ stage) } := by
  rw [logTwoSquarePullbackIntegral_compute_eq,
    logTwoSquareMeshWeightedSum_eq_uniformLeftEndpoint]
  exact IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
    logTwoSquarePullback_lipschitz_on_unit stage

/-- The direct finite square-Stieltjes candidate.  Its radius covers both the
finite square-substitution correction and the later square-block comparison
with the reciprocal mesh. -/
def logTwoSquareStieltjesCandidateCompute (stage : Nat) : QInterval :=
  let meshStage := 2 ^ stage
  let sum := logTwoSquareMeshStieltjesSum meshStage meshStage
  QInterval.expand { lo := sum, hi := sum }
    (4 * (1 / (meshStage : Rat)))

def logTwoSquareStieltjesCandidate : RealRaw where
  compute := logTwoSquareStieltjesCandidateCompute

theorem logTwoSquareStieltjesCandidateCompute_width (stage : Nat) :
    (logTwoSquareStieltjesCandidateCompute stage).width =
      8 * (1 / (((2 ^ stage : Nat) : Rat))) := by
  unfold logTwoSquareStieltjesCandidateCompute
  rw [QInterval.expand_width]
  simp only [QInterval.width]
  have hzero :
      logTwoSquareMeshStieltjesSum (2 ^ stage) (2 ^ stage) -
        logTwoSquareMeshStieltjesSum (2 ^ stage) (2 ^ stage) = 0 := by
    grind [Rat.sub_eq_add_neg]
  rw [hzero]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The wider candidate still has an executable shrink modulus: its width is
twice the certified pullback-integral width at the same dyadic stage. -/
theorem logTwoSquareStieltjesCandidate_widthsShrink :
    RealRaw.WidthsShrinkToZero logTwoSquareStieltjesCandidate.compute := by
  intro eps
  let half : QPos := ⟨eps.val / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property
      ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))⟩
  obtain ⟨N, hN⟩ :=
    (IntegralIdentities.LipschitzDyadic.compute_widthsShrink
      (f := logTwoSquarePullback) 2) half
  refine ⟨N, ?_⟩
  intro stage hstage
  rw [show logTwoSquareStieltjesCandidate.compute stage =
      logTwoSquareStieltjesCandidateCompute stage by rfl,
    logTwoSquareStieltjesCandidateCompute_width]
  have hmesh_pos : 0 < ((2 ^ stage : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hmesh_inv_nonneg : 0 <= 1 / (((2 ^ stage : Nat) : Rat)) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 hmesh_pos)
  calc
    8 * (1 / (((2 ^ stage : Nat) : Rat)) ) =
        2 * (IntegralIdentities.LipschitzDyadic.compute
          logTwoSquarePullback 2 stage).width := by
      rw [IntegralIdentities.LipschitzDyadic.compute_width]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= 2 * half.val :=
      Rat.mul_le_mul_of_nonneg_left (hN stage hstage)
        (by native_decide)
    _ = eps.val := by
      dsimp [half]
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The finite Stieltjes candidate overlaps the certified pullback-integral
box at every dyadic stage.  The witness is the exact weighted mesh sum; no
general substitution theorem is used in this proof. -/
theorem logTwoSquareStieltjesCandidate_overlaps_pullbackIntegral
    (stage : Nat) :
    QInterval.Overlaps
      (logTwoSquareStieltjesCandidate.compute stage)
      (logTwoSquarePullbackIntegral.compute stage) := by
  let meshStage := 2 ^ stage
  let stieltjes := logTwoSquareMeshStieltjesSum meshStage meshStage
  let weighted := logTwoSquareMeshWeightedSum meshStage meshStage
  let correction := logTwoSquareMeshCorrection meshStage meshStage
  let radius := 4 * (1 / (meshStage : Rat))
  have hmesh_pos : 0 < meshStage := Nat.pow_pos (by omega : 0 < 2)
  have hmesh_inv_nonneg : 0 <= 1 / (meshStage : Rat) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2
      ((Rat.natCast_pos).2 hmesh_pos))
  have hidentity : stieltjes = weighted + correction := by
    exact logTwoSquareMesh_substitution_identity meshStage meshStage
  have hcorrection : 0 <= correction /\ correction <= radius := by
    constructor
    · exact (logTwoSquareMeshCorrection_le_one_div meshStage
        hmesh_pos).1
    · calc
        correction <= 1 / (meshStage : Rat) :=
          (logTwoSquareMeshCorrection_le_one_div meshStage
            hmesh_pos).2
        _ <= 4 * (1 / (meshStage : Rat)) :=
          by
            simpa using
              (Rat.mul_le_mul_of_nonneg_right
                (by native_decide : (1 : Rat) <= 4) hmesh_inv_nonneg)
        _ = radius := by rfl
  have hweighted :
      (logTwoSquarePullbackIntegral.compute stage).lo <= weighted /\
        weighted <= (logTwoSquarePullbackIntegral.compute stage).hi := by
    simpa [weighted] using
      logTwoSquarePullbackIntegral_contains_weightedMesh stage
  unfold logTwoSquareStieltjesCandidate
    logTwoSquareStieltjesCandidateCompute
  dsimp only
  unfold QInterval.expand
  change stieltjes - radius <=
      (logTwoSquarePullbackIntegral.compute stage).hi /\
    (logTwoSquarePullbackIntegral.compute stage).lo <= stieltjes + radius
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem logTwoSquareStieltjesCandidate_equiv_pullbackIntegral :
    logTwoSquareStieltjesCandidate.Equiv logTwoSquarePullbackIntegral := by
  intro stage
  apply (RealRaw.compareAt_overlap_iff
    logTwoSquareStieltjesCandidate logTwoSquarePullbackIntegral stage stage).2
  exact logTwoSquareStieltjesCandidate_overlaps_pullbackIntegral stage

/-- The public radius covering the pullback-integral box at every stage. -/
def logTwoSquareStieltjesStabilizationRadius (stage : Nat) : Rat :=
  4 * (1 / (((2 ^ stage : Nat) : Rat)))

theorem logTwoSquareStieltjesStabilizationRadius_covers_pullbackIntegral
    (stage : Nat) :
    (logTwoSquarePullbackIntegral.compute stage).width <=
      logTwoSquareStieltjesStabilizationRadius stage := by
  unfold logTwoSquareStieltjesStabilizationRadius
  rw [logTwoSquarePullbackIntegral_width]
  exact Rat.le_refl

theorem logTwoSquareStieltjesStabilizationRadius_shrinks :
    ShrinksToZero logTwoSquareStieltjesStabilizationRadius := by
  intro eps
  obtain ⟨N, hN⟩ := logTwoSquarePullbackIntegral_valid.2.2 eps
  refine ⟨N, ?_⟩
  intro stage hstage
  unfold logTwoSquareStieltjesStabilizationRadius
  rw [← logTwoSquarePullbackIntegral_width]
  exact hN stage hstage

/-- A valid direct-only raw evaluator for the square substitution.  Runtime
evaluation reads only finite Stieltjes sums and rational radii; the
Lipschitz integral is used only as its proof-side anchor. -/
def logTwoSquareStieltjesRaw : RealRaw :=
  RealRaw.prefixStabilize logTwoSquareStieltjesCandidate
    logTwoSquareStieltjesStabilizationRadius

theorem logTwoSquareStieltjesRaw_valid :
    logTwoSquareStieltjesRaw.Valid := by
  unfold logTwoSquareStieltjesRaw
  exact RealRaw.prefixStabilize_valid
    logTwoSquareStieltjesCandidate_widthsShrink
    logTwoSquarePullbackIntegral_valid
    logTwoSquareStieltjesCandidate_equiv_pullbackIntegral
    logTwoSquareStieltjesStabilizationRadius_covers_pullbackIntegral
    logTwoSquareStieltjesStabilizationRadius_shrinks

theorem logTwoSquareStieltjesRaw_equiv_pullbackIntegral :
    logTwoSquareStieltjesRaw.Equiv logTwoSquarePullbackIntegral := by
  unfold logTwoSquareStieltjesRaw
  exact RealRaw.prefixStabilize_equiv_anchor
    logTwoSquarePullbackIntegral_valid
    logTwoSquareStieltjesCandidate_equiv_pullbackIntegral
    logTwoSquareStieltjesStabilizationRadius_covers_pullbackIntegral

private theorem logTwoKernel_difference_mul_denominator
    {s t : Rat} (hs0 : 0 <= s) (ht0 : 0 <= t) :
    (logTwoKernel s - logTwoKernel t) * ((1 + s) * (1 + t)) = t - s := by
  have hspos : 0 < 1 + s := by grind
  have htpos : 0 < 1 + t := by grind
  have hsne : 1 + s ≠ 0 := Rat.ne_of_gt hspos
  have htne : 1 + t ≠ 0 := Rat.ne_of_gt htpos
  have hscancel : (1 + s) * (1 + s)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hsne
  have htcancel : (1 + t) * (1 + t)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ htne
  unfold logTwoKernel
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- `t ↦ 1/(1+t)` is 1-Lipschitz on the unit interval.  The proof is a
finite denominator calculation: the product `(1+s)(1+t)` is at least one. -/
theorem logTwoKernel_lipschitz_on_unit
    (s t : Rat)
    (hs0 : 0 <= s) (_hs1 : s <= 1)
    (ht0 : 0 <= t) (_ht1 : t <= 1) :
    qabs (logTwoKernel s - logTwoKernel t) <= qabs (t - s) := by
  have hspos : 0 < 1 + s := by grind
  have htpos : 0 < 1 + t := by grind
  have hprod : 1 <= (1 + s) * (1 + t) := by
    calc
      (1 : Rat) = 1 * 1 := by native_decide
      _ <= (1 + s) * 1 := Rat.mul_le_mul_of_nonneg_right
        (by grind) (by native_decide)
      _ <= (1 + s) * (1 + t) := Rat.mul_le_mul_of_nonneg_left
        (by grind) (Rat.le_of_lt hspos)
  have hprod0 : 0 <= (1 + s) * (1 + t) :=
    Rat.le_trans (by native_decide) hprod
  have hqprod : 1 <= qabs ((1 + s) * (1 + t)) := by
    rw [qabs_eq_self_of_nonneg hprod0]
    exact hprod
  have hmul := logTwoKernel_difference_mul_denominator hs0 ht0
  calc
    qabs (logTwoKernel s - logTwoKernel t) =
        qabs (logTwoKernel s - logTwoKernel t) * 1 := by
      rw [Rat.mul_one]
    _ <= qabs (logTwoKernel s - logTwoKernel t) *
          qabs ((1 + s) * (1 + t)) :=
      Rat.mul_le_mul_of_nonneg_left hqprod (qabs_nonneg _)
    _ = qabs ((logTwoKernel s - logTwoKernel t) *
          ((1 + s) * (1 + t))) := by
      exact (qabs_mul _ _).symm
    _ = qabs (t - s) := by rw [hmul]

/-- On an ordered unit interval, the loss in the reciprocal kernel is at most
the horizontal displacement.  This one-sided form packages the monotonicity
and Lipschitz facts needed for a finite square-block Riemann comparison. -/
theorem logTwoKernel_drop_le_step {s t : Rat}
    (hs0 : 0 <= s) (hs1 : s <= 1)
    (hst : s <= t) (ht1 : t <= 1) :
    logTwoKernel s - logTwoKernel t <= t - s := by
  have hdrop0 : 0 <= logTwoKernel s - logTwoKernel t := by
    grind [logTwoKernel_antitone_nonnegative hs0 hst]
  have hstep0 : 0 <= t - s := by
    grind [Rat.sub_eq_add_neg]
  have hlip := logTwoKernel_lipschitz_on_unit s t hs0 hs1
    (Rat.le_trans hs0 hst) ht1
  simpa only [qabs_eq_self_of_nonneg hdrop0,
    qabs_eq_self_of_nonneg hstep0] using hlip

/-- The finite rational Lipschitz certificate used by the unit-interval
Darboux integral construction for the logarithmic kernel. -/
def logTwoKernel_lipschitz : Integral.LipschitzOnUnit logTwoKernel 1 :=
  ⟨by native_decide, fun s t hs0 hs1 ht0 ht1 => by
    simpa using logTwoKernel_lipschitz_on_unit s t hs0 hs1 ht0 ht1⟩

/-- A uniform left sum truncated at an arbitrary number of cells.  The square
change-of-variables comparison below groups this prefix into the blocks whose
endpoints are the square-mesh breakpoints. -/
private def logTwoUniformLeftPrefix (meshStage terms : Nat) : Rat :=
  (List.range terms).foldl
    (fun (total : Rat) (j : Nat) =>
      total + (1 / ((meshStage * meshStage : Nat) : Rat)) *
        logTwoKernel ((j : Rat) / ((meshStage * meshStage : Nat) : Rat))) 0

/-- The uniform left sum on the `k`th square block.  Its finite index set is
`k², ..., (k+1)²-1`, written by its offsets `0, ..., 2k`. -/
private def logTwoUniformLeftSquareBlock (meshStage k : Nat) : Rat :=
  (List.range (2 * k + 1)).foldl
    (fun (total : Rat) (offset : Nat) =>
      total + (1 / ((meshStage * meshStage : Nat) : Rat)) *
        logTwoKernel (((k * k + offset : Nat) : Rat) /
          ((meshStage * meshStage : Nat) : Rat))) 0

/-- The same uniform prefix, enumerated square block by square block. -/
private def logTwoUniformLeftSquareBlocks (meshStage : Nat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      logTwoUniformLeftSquareBlocks meshStage terms +
        logTwoUniformLeftSquareBlock meshStage terms

/-- Adding a finite sequence of rational summands commutes with changing the
initial accumulator to the left.  This small finite-fold lemma keeps the
square-block reindexing below entirely algebraic. -/
private theorem logTwo_foldl_add_initial (g : Nat -> Rat)
    (xs : List Nat) (initial : Rat) :
    xs.foldl (fun total x => total + g x) initial =
      initial + xs.foldl (fun total x => total + g x) 0 := by
  induction xs generalizing initial with
  | nil =>
      change initial = initial + 0
      grind
  | cons x xs ih =>
      change xs.foldl (fun total x => total + g x) (initial + g x) =
        initial + xs.foldl (fun total x => total + g x) (0 + g x)
      rw [ih (initial + g x)]
      rw [show (0 : Rat) + g x = g x by grind, ih (g x)]
      grind [Rat.add_assoc]

/-- A finite list of summands bounded above by a constant has the expected
constant-times-length upper bound. -/
private theorem foldl_add_le_length_mul
    (xs : List Nat) (term : Nat -> Rat) (c : Rat)
    (hterm : forall i, i ∈ xs -> term i <= c) :
    xs.foldl (fun total i => total + term i) 0 <= (xs.length : Rat) * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hrest : xs.foldl (fun total i => total + term i) 0 <=
          (xs.length : Rat) * c :=
        ih (fun i hi => hterm i (List.mem_cons_of_mem x hi))
      have hx : term x <= c := hterm x (by simp)
      simp only [List.length_cons]
      rw [Rat.natCast_add]
      have hone : ((1 : Nat) : Rat) = 1 := by native_decide
      rw [hone]
      calc
        (x :: xs).foldl (fun total i => total + term i) 0 =
            xs.foldl (fun total i => total + term i) (term x) := by
              simp only [List.foldl, Rat.zero_add]
        _ = term x + xs.foldl (fun total i => total + term i) 0 :=
          logTwo_foldl_add_initial term xs (term x)
        _ <= c + (xs.length : Rat) * c := rat_add_le_add hx hrest
        _ = ((xs.length : Rat) + 1) * c := by
          grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm]

/-- The lower counterpart of `foldl_add_le_length_mul`. -/
private theorem length_mul_le_foldl_add
    (xs : List Nat) (term : Nat -> Rat) (c : Rat)
    (hterm : forall i, i ∈ xs -> c <= term i) :
    (xs.length : Rat) * c <= xs.foldl (fun total i => total + term i) 0 := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hrest : (xs.length : Rat) * c <=
          xs.foldl (fun total i => total + term i) 0 :=
        ih (fun i hi => hterm i (List.mem_cons_of_mem x hi))
      have hx : c <= term x := hterm x (by simp)
      simp only [List.length_cons]
      rw [Rat.natCast_add]
      have hone : ((1 : Nat) : Rat) = 1 := by native_decide
      rw [hone]
      calc
        ((xs.length : Rat) + 1) * c = c + (xs.length : Rat) * c := by
          grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm]
        _ <= term x + xs.foldl (fun total i => total + term i) 0 :=
          rat_add_le_add hx hrest
        _ = xs.foldl (fun total i => total + term i) (term x) :=
          (logTwo_foldl_add_initial term xs (term x)).symm
        _ = (x :: xs).foldl (fun total i => total + term i) 0 := by
          simp only [List.foldl, Rat.zero_add]

/-- Exact finite reindexing of a uniform `n²`-mesh into the `n` square-image
blocks.  This is the discrete common-refinement skeleton of the remaining
square-substitution comparison. -/
private theorem logTwoUniformLeftPrefix_eq_squareBlocks
    (meshStage terms : Nat) :
    logTwoUniformLeftPrefix meshStage (terms * terms) =
      logTwoUniformLeftSquareBlocks meshStage terms := by
  induction terms with
  | zero =>
      simp [logTwoUniformLeftPrefix, logTwoUniformLeftSquareBlocks]
  | succ terms ih =>
      have hsq : (terms + 1) * (terms + 1) =
          terms * terms + (2 * terms + 1) := by
        calc
          (terms + 1) * (terms + 1) = terms * (terms + 1) + (terms + 1) := by
            simpa using Nat.succ_mul terms (terms + 1)
          _ = (terms * terms + terms) + (terms + 1) := by rw [Nat.mul_succ]
          _ = terms * terms + (2 * terms + 1) := by omega
      unfold logTwoUniformLeftPrefix
      rw [hsq, List.range_add, List.foldl_append]
      change (List.map (fun x => terms * terms + x)
          (List.range (2 * terms + 1))).foldl _
          (logTwoUniformLeftPrefix meshStage (terms * terms)) =
        logTwoUniformLeftSquareBlocks meshStage (terms + 1)
      rw [logTwo_foldl_add_initial]
      rw [ih]
      simp only [List.foldl_map]
      rfl

/-- At a square number of cells, the ordinary uniform left sum is exactly the
sum of the explicitly enumerated square-image blocks.  This is the finite
common-refinement equality which will let the square Stieltjes mesh be
compared with the reciprocal integral without a change-of-variables axiom. -/
theorem logTwoUniformLeftSquareBlocks_eq_uniformLeftEndpoint
    (meshStage : Nat) :
    logTwoUniformLeftSquareBlocks meshStage meshStage =
      IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        logTwoKernel (meshStage * meshStage) := by
  rw [← logTwoUniformLeftPrefix_eq_squareBlocks]
  rfl

/-- A nonnegative rational fraction of two natural numbers is at most one
when its numerator does not exceed its positive denominator. -/
private theorem natCast_div_le_one {a b : Nat}
    (hb : 0 < b) (hab : a <= b) :
    (a : Rat) / (b : Rat) <= 1 := by
  have hbpos : 0 < (b : Rat) := (Rat.natCast_pos).2 hb
  have hbne : (b : Rat) ≠ 0 := Rat.ne_of_gt hbpos
  apply Rat.le_of_mul_le_mul_right (c := (b : Rat))
  · calc
      ((a : Rat) / (b : Rat)) * (b : Rat) = (a : Rat) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (b : Rat) := by exact_mod_cast hab
      _ = 1 * (b : Rat) := by grind
  · exact hbpos

/-- The displacement of a point inside a square-image mesh block is bounded
by twice the original mesh width.  This is the quantitative input that makes
the eventual common-refinement error shrink. -/
private theorem natCast_div_square_le_two_div {l n : Nat}
    (hn : 0 < n) (hl : l <= 2 * n) :
    (l : Rat) / ((n * n : Nat) : Rat) <= 2 / (n : Rat) := by
  let N : Rat := (n : Rat)
  have hNpos : 0 < N := by
    dsimp [N]
    exact (Rat.natCast_pos).2 hn
  have hNne : N ≠ 0 := Rat.ne_of_gt hNpos
  have hNNpos : 0 < N * N := Rat.mul_pos hNpos hNpos
  rw [Rat.natCast_mul]
  change (l : Rat) / (N * N) <= 2 / N
  apply Rat.le_of_mul_le_mul_right (c := N * N)
  · calc
      ((l : Rat) / (N * N)) * (N * N) = (l : Rat) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= 2 * N := by
        dsimp [N]
        exact_mod_cast hl
      _ = (2 / N) * (N * N) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact hNNpos

/-- Division by a positive natural denominator preserves the order of natural
numerators after their rational embedding. -/
private theorem natCast_div_mono {a b d : Nat}
    (hd : 0 < d) (hab : a <= b) :
    (a : Rat) / (d : Rat) <= (b : Rat) / (d : Rat) := by
  rw [Rat.div_def, Rat.div_def]
  apply Rat.mul_le_mul_of_nonneg_right
  · exact_mod_cast hab
  · exact Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hd))

/-- A point enumerated in the `k`th square block remains in the unit interval.
The proof uses only the finite index inequality
`k² + l < (k+1)² ≤ n²`. -/
private theorem squareBlock_index_le_square
    {n k l : Nat} (hk : k < n) (hl : l < 2 * k + 1) :
    k * k + l <= n * n := by
  have hstep : (k + 1) * (k + 1) =
      k * k + (2 * k + 1) := by
    calc
      (k + 1) * (k + 1) = k * (k + 1) + (k + 1) := by
        simpa using Nat.succ_mul k (k + 1)
      _ = (k * k + k) + (k + 1) := by rw [Nat.mul_succ]
      _ = k * k + (2 * k + 1) := by omega
  have hblock : k * k + l < (k + 1) * (k + 1) := by
    rw [hstep]
    omega
  have hk1 : k + 1 <= n := Nat.succ_le_of_lt hk
  have hsquare : (k + 1) * (k + 1) <= n * n :=
    Nat.mul_le_mul hk1 hk1
  exact Nat.le_trans (Nat.le_of_lt hblock) hsquare

/-- The square-block coordinate at offset `l`. -/
private def squareBlockPoint (n k l : Nat) : Rat :=
  ((k * k + l : Nat) : Rat) / ((n * n : Nat) : Rat)

/-- The square left endpoint and every uniform subcell point in its block are
ordered points of `[0,1]`, with a displacement of at most `2/n`. -/
private theorem squareBlockPoint_bounds
    {n k l : Nat} (hn : 0 < n) (hk : k < n) (hl : l < 2 * k + 1) :
    0 <= squareBlockPoint n k 0 /\
      squareBlockPoint n k 0 <= squareBlockPoint n k l /\
      squareBlockPoint n k l <= 1 /\
      squareBlockPoint n k l - squareBlockPoint n k 0 <= 2 / (n : Rat) := by
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  have hindex : k * k + l <= n * n := squareBlock_index_le_square hk hl
  have hzero : k * k <= k * k + l := by omega
  have hlbound : l <= 2 * n := by
    have htwo : 2 * k + 1 <= 2 * n := by omega
    omega
  constructor
  · unfold squareBlockPoint
    rw [Rat.div_def]
    exact Rat.mul_nonneg
      (by exact_mod_cast (Nat.zero_le (k * k)))
      (Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hnn)))
  constructor
  · unfold squareBlockPoint
    exact natCast_div_mono hnn hzero
  constructor
  · unfold squareBlockPoint
    exact natCast_div_le_one hnn hindex
  · unfold squareBlockPoint
    simp only [Nat.add_zero]
    have hdiff :
        ((k * k + l : Nat) : Rat) / ((n * n : Nat) : Rat) -
          ((k * k : Nat) : Rat) / ((n * n : Nat) : Rat) =
          (l : Rat) / ((n * n : Nat) : Rat) := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.natCast_add]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hdiff]
    exact natCast_div_square_le_two_div hn hlbound

/-- The uniform rectangles inside a square block lie below the square left
rectangle, because the reciprocal kernel is nonincreasing. -/
private theorem logTwoUniformLeftSquareBlock_le_leftCell
    (n k : Nat) (hn : 0 < n) (hk : k < n) :
    logTwoUniformLeftSquareBlock n k <=
      ((2 * k + 1 : Nat) : Rat) *
        ((1 / ((n * n : Nat) : Rat)) *
          logTwoKernel (squareBlockPoint n k 0)) := by
  let h : Rat := 1 / ((n * n : Nat) : Rat)
  let a : Rat := squareBlockPoint n k 0
  let term : Nat -> Rat := fun l => h * logTwoKernel (squareBlockPoint n k l)
  let c : Rat := h * logTwoKernel a
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  have hcoeff : 0 <= h := by
    dsimp [h]
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hnn))
  have hterm : forall l, l ∈ List.range (2 * k + 1) -> term l <= c := by
    intro l hl
    have hlindex : l < 2 * k + 1 := List.mem_range.mp hl
    have hpoint := squareBlockPoint_bounds hn hk hlindex
    have hkernel : logTwoKernel (squareBlockPoint n k l) <=
        logTwoKernel (squareBlockPoint n k 0) :=
      logTwoKernel_antitone_nonnegative hpoint.1 hpoint.2.1
    dsimp [term, c, h, a]
    exact Rat.mul_le_mul_of_nonneg_left hkernel hcoeff
  have hsum := foldl_add_le_length_mul (List.range (2 * k + 1)) term c hterm
  simpa [logTwoUniformLeftSquareBlock, term, c, h, a, squareBlockPoint] using hsum

/-- Conversely, the reciprocal kernel can lose at most `2/n` over a square
block, so its uniform rectangles dominate the correspondingly lowered square
left rectangle. -/
private theorem leftCell_minus_twoDiv_le_logTwoUniformLeftSquareBlock
    (n k : Nat) (hn : 0 < n) (hk : k < n) :
    ((2 * k + 1 : Nat) : Rat) *
        ((1 / ((n * n : Nat) : Rat)) *
          (logTwoKernel (squareBlockPoint n k 0) - 2 / (n : Rat))) <=
      logTwoUniformLeftSquareBlock n k := by
  let h : Rat := 1 / ((n * n : Nat) : Rat)
  let a : Rat := squareBlockPoint n k 0
  let term : Nat -> Rat := fun l => h * logTwoKernel (squareBlockPoint n k l)
  let c : Rat := h * (logTwoKernel a - 2 / (n : Rat))
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  have hcoeff : 0 <= h := by
    dsimp [h]
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hnn))
  have hterm : forall l, l ∈ List.range (2 * k + 1) -> c <= term l := by
    intro l hl
    have hlindex : l < 2 * k + 1 := List.mem_range.mp hl
    have hpoint := squareBlockPoint_bounds hn hk hlindex
    have hdrop := logTwoKernel_drop_le_step hpoint.1
      (Rat.le_trans hpoint.2.1 hpoint.2.2.1)
      hpoint.2.1 hpoint.2.2.1
    have hkernel : logTwoKernel (squareBlockPoint n k 0) - 2 / (n : Rat) <=
        logTwoKernel (squareBlockPoint n k l) := by
      grind [Rat.sub_eq_add_neg]
    dsimp [term, c, h, a]
    exact Rat.mul_le_mul_of_nonneg_left hkernel hcoeff
  have hsum := length_mul_le_foldl_add (List.range (2 * k + 1)) term c hterm
  simpa [logTwoUniformLeftSquareBlock, term, c, h, a, squareBlockPoint] using hsum

/-- The product of two `2/n` block bounds has the square-mesh denominator. -/
private theorem two_div_mul_two_div_eq_four_div_square
    (n : Nat) :
    (2 / (n : Rat)) * (2 / (n : Rat)) =
      4 / ((n * n : Nat) : Rat) := by
  simp only [Rat.div_def, Rat.natCast_mul, Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- A square left rectangle and its corresponding uniform block differ by a
nonnegative amount at most `4/n²`. -/
private theorem leftCell_sub_logTwoUniformLeftSquareBlock_bounds
    (n k : Nat) (hn : 0 < n) (hk : k < n) :
    let cell := ((2 * k + 1 : Nat) : Rat) *
      ((1 / ((n * n : Nat) : Rat)) * logTwoKernel (squareBlockPoint n k 0))
    0 <= cell - logTwoUniformLeftSquareBlock n k /\
      cell - logTwoUniformLeftSquareBlock n k <= 4 / ((n * n : Nat) : Rat) := by
  dsimp only
  let M : Rat := ((2 * k + 1 : Nat) : Rat)
  let h : Rat := 1 / ((n * n : Nat) : Rat)
  let a : Rat := squareBlockPoint n k 0
  let B : Rat := logTwoUniformLeftSquareBlock n k
  let d : Rat := 2 / (n : Rat)
  have hupper : B <= M * (h * logTwoKernel a) := by
    dsimp [M, h, a, B]
    exact logTwoUniformLeftSquareBlock_le_leftCell n k hn hk
  have hlower : M * (h * (logTwoKernel a - d)) <= B := by
    dsimp [M, h, a, B, d]
    exact leftCell_minus_twoDiv_le_logTwoUniformLeftSquareBlock n k hn hk
  have hnonneg : 0 <= M * (h * logTwoKernel a) - B := by
    grind [Rat.sub_eq_add_neg]
  have hinter : M * (h * logTwoKernel a) - B <= M * (h * d) := by
    have hid : M * (h * logTwoKernel a) - M * (h * d) =
        M * (h * (logTwoKernel a - d)) := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [← hid] at hlower
    grind [Rat.sub_eq_add_neg]
  have hMle : 2 * k + 1 <= 2 * n := by omega
  have hwidth : M * h <= d := by
    dsimp [M, h, d]
    simpa [Rat.div_def, Rat.mul_assoc] using
      (natCast_div_square_le_two_div hn hMle)
  have hdnonneg : 0 <= d := by
    dsimp [d]
    rw [Rat.div_def]
    exact Rat.le_of_lt (Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)))
  have hbudget : M * (h * d) <= d * d := by
    calc
      M * (h * d) = (M * h) * d := by rw [Rat.mul_assoc]
      _ <= d * d := Rat.mul_le_mul_of_nonneg_right hwidth hdnonneg
  dsimp [M, h, a, B, d] at hnonneg hinter hbudget ⊢
  constructor
  · exact hnonneg
  · calc
      ((2 * k + 1 : Nat) : Rat) *
          ((1 / ((n * n : Nat) : Rat)) * logTwoKernel (squareBlockPoint n k 0)) -
          logTwoUniformLeftSquareBlock n k <=
          ((2 * k + 1 : Nat) : Rat) *
            ((1 / ((n * n : Nat) : Rat)) * (2 / (n : Rat))) := hinter
      _ <= (2 / (n : Rat)) * (2 / (n : Rat)) := hbudget
      _ = 4 / ((n * n : Nat) : Rat) :=
        two_div_mul_two_div_eq_four_div_square n

/-- The square of a uniform source-mesh coordinate is its corresponding
square-block left endpoint. -/
private theorem unitMeshPath_square_eq_squareBlockPoint
    (n k : Nat) :
    unitMeshPath n k * unitMeshPath n k = squareBlockPoint n k 0 := by
  unfold unitMeshPath squareBlockPoint
  simp only [Nat.add_zero, Rat.div_def, Rat.natCast_mul, Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The image under `x ↦ x²` of one source-mesh cell has width
`(2k+1)/n²`. -/
private theorem unitMeshPath_square_increment_eq_squareBlockWidth
    (n k : Nat) :
    unitMeshPath n (k + 1) * unitMeshPath n (k + 1) -
        unitMeshPath n k * unitMeshPath n k =
      ((2 * k + 1 : Nat) : Rat) / ((n * n : Nat) : Rat) := by
  unfold unitMeshPath
  simp only [Rat.div_def, Rat.natCast_add, Rat.natCast_mul, Rat.inv_mul_rev]
  have htwo : ((2 : Nat) : Rat) = 2 := by native_decide
  have hone : ((1 : Nat) : Rat) = 1 := by native_decide
  rw [htwo, hone]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The recursive square-Stieltjes sum adds exactly the left rectangle of its
next square block. -/
private theorem logTwoSquareMeshStieltjesSum_succ_eq_leftCell
    (n k : Nat) :
    logTwoSquareMeshStieltjesSum n (k + 1) =
      logTwoSquareMeshStieltjesSum n k +
        ((2 * k + 1 : Nat) : Rat) *
          ((1 / ((n * n : Nat) : Rat)) *
            logTwoKernel (squareBlockPoint n k 0)) := by
  unfold logTwoSquareMeshStieltjesSum
  rw [leftStieltjesSum]
  have hbase := unitMeshPath_square_eq_squareBlockPoint n k
  have hwidth := unitMeshPath_square_increment_eq_squareBlockWidth n k
  rw [hbase] at hwidth ⊢
  rw [hwidth]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- Up through any first `m` square blocks, the square Stieltjes sum is above
the corresponding uniform left sum and differs from it by at most one
`4/n²` budget per block. -/
private theorem logTwoSquareMesh_sub_uniformSquareBlocks_bounds
    (n m : Nat) (hn : 0 < n) (hmn : m <= n) :
    0 <= logTwoSquareMeshStieltjesSum n m -
        logTwoUniformLeftSquareBlocks n m /\
      logTwoSquareMeshStieltjesSum n m -
          logTwoUniformLeftSquareBlocks n m <=
        (m : Rat) * (4 / ((n * n : Nat) : Rat)) := by
  induction m generalizing n with
  | zero =>
      simp [logTwoSquareMeshStieltjesSum, leftStieltjesSum,
        logTwoUniformLeftSquareBlocks]
      grind [Rat.sub_eq_add_neg]
  | succ m ih =>
      have hmle : m <= n := Nat.le_trans (Nat.le_succ m) hmn
      have hmk : m < n := by omega
      have hprev := ih n hn hmle
      have hcell := leftCell_sub_logTwoUniformLeftSquareBlock_bounds n m hn hmk
      let P : Rat := logTwoSquareMeshStieltjesSum n m
      let Q : Rat := logTwoUniformLeftSquareBlocks n m
      let C : Rat := ((2 * m + 1 : Nat) : Rat) *
        ((1 / ((n * n : Nat) : Rat)) * logTwoKernel (squareBlockPoint n m 0))
      let B : Rat := logTwoUniformLeftSquareBlock n m
      let e : Rat := 4 / ((n * n : Nat) : Rat)
      have hprev' : 0 <= P - Q /\ P - Q <= (m : Rat) * e := by
        dsimp [P, Q, e]
        exact hprev
      have hcell' : 0 <= C - B /\ C - B <= e := by
        dsimp [C, B, e]
        exact hcell
      rw [logTwoSquareMeshStieltjesSum_succ_eq_leftCell,
        logTwoUniformLeftSquareBlocks]
      change 0 <= (P + C) - (Q + B) /\
        (P + C) - (Q + B) <= ((m + 1 : Nat) : Rat) * e
      have hsplit : (P + C) - (Q + B) = (P - Q) + (C - B) := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      rw [hsplit]
      constructor
      · exact Rat.add_nonneg hprev'.1 hcell'.1
      · calc
          (P - Q) + (C - B) <= (m : Rat) * e + e :=
            rat_add_le_add hprev'.2 hcell'.2
          _ = ((m + 1 : Nat) : Rat) * e := by
            rw [Rat.natCast_add]
            have hone : ((1 : Nat) : Rat) = 1 := by native_decide
            rw [hone]
            grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm]

/-- Summing the `4/n²` block budgets over all `n` blocks yields the explicit
`4/n` common-refinement budget. -/
private theorem nat_mul_four_div_square_eq_four_div
    (n : Nat) (hn : 0 < n) :
    (n : Rat) * (4 / ((n * n : Nat) : Rat)) = 4 / (n : Rat) := by
  let N : Rat := (n : Rat)
  have hNpos : 0 < N := by
    dsimp [N]
    exact (Rat.natCast_pos).2 hn
  have hNne : N ≠ 0 := Rat.ne_of_gt hNpos
  have hcancel : N * N⁻¹ = 1 := Rat.mul_inv_cancel N hNne
  simp only [Rat.div_def, Rat.natCast_mul, Rat.inv_mul_rev]
  change N * (4 * (N⁻¹ * N⁻¹)) = 4 * N⁻¹
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The literal square Stieltjes sum and the ordinary uniform left Riemann
sum for `t ↦ 1/(1+t)` have a finite, explicitly shrinking common-refinement
comparison.  This is the analytic half of the square-substitution bridge. -/
theorem logTwoSquareMesh_sub_uniformLeftEndpoint_bounds
    (n : Nat) (hn : 0 < n) :
    0 <= logTwoSquareMeshStieltjesSum n n -
        IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          logTwoKernel (n * n) /\
      logTwoSquareMeshStieltjesSum n n -
          IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
            logTwoKernel (n * n) <= 4 / (n : Rat) := by
  have h := logTwoSquareMesh_sub_uniformSquareBlocks_bounds n n hn
    (Nat.le_refl n)
  rw [logTwoUniformLeftSquareBlocks_eq_uniformLeftEndpoint] at h
  constructor
  · exact h.1
  · calc
      logTwoSquareMeshStieltjesSum n n -
          IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
            logTwoKernel (n * n) <=
          (n : Rat) * (4 / ((n * n : Nat) : Rat)) := h.2
      _ = 4 / (n : Rat) := nat_mul_four_div_square_eq_four_div n hn

/-- The actual finite lower/upper Darboux box for the translated reciprocal
kernel.  It evaluates only rational function values on a dyadic mesh. -/
def logTwoDarbouxCompute (stage : Nat) : QInterval :=
  IntegralIdentities.LipschitzDyadic.compute logTwoKernel 1 stage

theorem logTwoDarbouxCompute_width (stage : Nat) :
    (logTwoDarbouxCompute stage).width =
      2 * (1 / (((2 ^ stage : Nat) : Rat))) := by
  simpa [logTwoDarbouxCompute] using
    (IntegralIdentities.LipschitzDyadic.compute_width
      (f := logTwoKernel) 1 stage)

/-- A certified raw real from literal midpoint-refined Lipschitz--Darboux
rectangles for `t ↦ 1/(1+t)` on `[0,1]`.  Its stage-`n` box has exact width
`2/2^n`; the later logarithm bridge proves it equivalent to the alternating
series representation. -/
def logTwoDarbouxRaw : RealRaw :=
  IntegralIdentities.LipschitzDyadic.raw logTwoKernel 1

theorem logTwoDarbouxRaw_valid : logTwoDarbouxRaw.Valid := by
  simpa [logTwoDarbouxRaw] using
    (IntegralIdentities.LipschitzDyadic.raw_valid logTwoKernel_lipschitz)

/-- The domain-aware construction behind `logTwoDarbouxRaw`.  Unlike a bare
existence interface, its boxes are the finite rectangles in
`logTwoDarbouxCompute`. -/
def logTwoDarbouxConstruction :
    Integral.ConstructionFor (FunctionOnInterval.exactRat logTwoKernel 0 1) :=
  IntegralIdentities.LipschitzDyadic.construction logTwoKernel 1
    logTwoKernel_lipschitz

/-- The constructive definite-integral raw for the translated reciprocal
kernel.  Its agreement with `logTwoSeries` is proved later as an explicit
finite mesh comparison, rather than hidden in this definition. -/
def logTwoReciprocalIntegral : RealRaw :=
  Integral.integralFor (FunctionOnInterval.exactRat logTwoKernel 0 1)
    logTwoDarbouxConstruction

theorem logTwoReciprocalIntegral_valid : logTwoReciprocalIntegral.Valid :=
  Integral.integralFor_valid (FunctionOnInterval.exactRat logTwoKernel 0 1)
    logTwoDarbouxConstruction

theorem logTwoReciprocalIntegral_compute_eq (stage : Nat) :
    logTwoReciprocalIntegral.compute stage = logTwoDarbouxCompute stage :=
  rfl

/-- The reciprocal integral sampled at twice a stage uses the `n²`-mesh when
the square Stieltjes computation uses the `n=2^stage` source mesh. -/
def logTwoSquareMeshStageSchedule : RealRaw.StageSchedule where
  stage := fun n => 2 * n
  monotone := by
    intro i j hij
    exact Nat.mul_le_mul_left 2 hij
  cofinal := by
    intro target
    refine ⟨target, ?_⟩
    omega

def logTwoReciprocalSquareScheduled : RealRaw :=
  RealRaw.schedule logTwoSquareMeshStageSchedule logTwoReciprocalIntegral

theorem logTwoReciprocalSquareScheduled_valid :
    logTwoReciprocalSquareScheduled.Valid :=
  RealRaw.schedule_valid logTwoReciprocalIntegral
    logTwoReciprocalIntegral_valid logTwoSquareMeshStageSchedule

theorem logTwoReciprocalSquareScheduled_contains_uniformLeftEndpoint
    (stage : Nat) :
    (logTwoReciprocalSquareScheduled.compute stage).ContainsInterval
      { lo := IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          logTwoKernel ((2 ^ stage) * (2 ^ stage))
        hi := IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          logTwoKernel ((2 ^ stage) * (2 ^ stage)) } := by
  change (logTwoReciprocalIntegral.compute (2 * stage)).ContainsInterval _
  rw [logTwoReciprocalIntegral_compute_eq]
  have h := IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
    logTwoKernel_lipschitz (2 * stage)
  have hpow : (2 ^ stage) * (2 ^ stage) = 2 ^ (2 * stage) := by
    rw [show 2 * stage = stage + stage by omega, Nat.pow_add]
  simpa [logTwoDarbouxCompute, hpow] using h

/-- The widened direct square-Stieltjes candidate overlaps the reciprocal
integral sampled on the matching square mesh.  The witness is the ordinary
uniform left sum, and the exact `4/n` block budget supplies the overlap. -/
theorem logTwoSquareStieltjesCandidate_overlaps_reciprocalSquareScheduled
    (stage : Nat) :
    QInterval.Overlaps
      (logTwoSquareStieltjesCandidate.compute stage)
      (logTwoReciprocalSquareScheduled.compute stage) := by
  let meshStage := 2 ^ stage
  let stieltjes := logTwoSquareMeshStieltjesSum meshStage meshStage
  let uniform := IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
    logTwoKernel (meshStage * meshStage)
  let radius := 4 * (1 / (meshStage : Rat))
  have hmesh_pos : 0 < meshStage := Nat.pow_pos (by omega : 0 < 2)
  have hbound : 0 <= stieltjes - uniform /\
      stieltjes - uniform <= radius := by
    simpa [stieltjes, uniform, radius, Rat.div_def] using
      (logTwoSquareMesh_sub_uniformLeftEndpoint_bounds meshStage hmesh_pos)
  have huniform :
      (logTwoReciprocalSquareScheduled.compute stage).lo <= uniform /\
        uniform <= (logTwoReciprocalSquareScheduled.compute stage).hi := by
    simpa [uniform] using
      logTwoReciprocalSquareScheduled_contains_uniformLeftEndpoint stage
  have hradius0 : 0 <= radius := by
    dsimp [radius]
    apply Rat.mul_nonneg
    · exact (by native_decide : (0 : Rat) <= 4)
    · rw [Rat.div_def, Rat.one_mul]
      exact Rat.le_of_lt ((Rat.inv_pos).2
        ((Rat.natCast_pos).2 hmesh_pos))
  unfold logTwoSquareStieltjesCandidate
    logTwoSquareStieltjesCandidateCompute
  dsimp only
  unfold QInterval.expand
  change stieltjes - radius <=
      (logTwoReciprocalSquareScheduled.compute stage).hi /\
    (logTwoReciprocalSquareScheduled.compute stage).lo <= stieltjes + radius
  constructor
  · have hleft : stieltjes - radius <= uniform := by
      grind [Rat.sub_eq_add_neg]
    exact Rat.le_trans hleft huniform.2
  · have hright : uniform <= stieltjes := by
      grind [Rat.sub_eq_add_neg]
    exact Rat.le_trans huniform.1
      (Rat.le_trans hright (by grind [Rat.sub_eq_add_neg]))

theorem logTwoSquareStieltjesCandidate_equiv_reciprocalSquareScheduled :
    logTwoSquareStieltjesCandidate.Equiv
      logTwoReciprocalSquareScheduled := by
  intro stage
  apply (RealRaw.compareAt_overlap_iff
    logTwoSquareStieltjesCandidate logTwoReciprocalSquareScheduled stage stage).2
  exact logTwoSquareStieltjesCandidate_overlaps_reciprocalSquareScheduled stage

/-- The reciprocal integral's doubled-stage boxes are narrower than the
public `4/2^stage` stabilization radius of the direct Stieltjes evaluator. -/
theorem logTwoSquareStieltjesStabilizationRadius_covers_reciprocalSquareScheduled
    (stage : Nat) :
    (logTwoReciprocalSquareScheduled.compute stage).width <=
      logTwoSquareStieltjesStabilizationRadius stage := by
  let meshStage := 2 ^ stage
  have hmesh_pos : 0 < meshStage := Nat.pow_pos (by omega : 0 < 2)
  have htwo_le : 2 <= 2 * meshStage := by omega
  have hsmall : (2 : Rat) / ((meshStage * meshStage : Nat) : Rat) <=
      2 / (meshStage : Rat) :=
    natCast_div_square_le_two_div hmesh_pos htwo_le
  have hinv_nonneg : 0 <= 1 / (meshStage : Rat) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2
      ((Rat.natCast_pos).2 hmesh_pos))
  have hfour : 2 / (meshStage : Rat) <=
      4 * (1 / (meshStage : Rat)) := by
    simpa [Rat.div_def] using
      (Rat.mul_le_mul_of_nonneg_right
        (by native_decide : (2 : Rat) <= 4) hinv_nonneg)
  have hpow : (2 ^ stage) * (2 ^ stage) = 2 ^ (2 * stage) := by
    rw [show 2 * stage = stage + stage by omega, Nat.pow_add]
  change (logTwoReciprocalIntegral.compute (2 * stage)).width <= _
  rw [logTwoReciprocalIntegral_compute_eq, logTwoDarbouxCompute_width,
    ← hpow]
  unfold logTwoSquareStieltjesStabilizationRadius
  simpa [meshStage, Rat.div_def] using Rat.le_trans hsmall hfour

/-- The direct stabilized Stieltjes evaluator is also certified by the
reciprocal integral, using exactly the same finite runtime computation. -/
theorem logTwoSquareStieltjesRaw_equiv_reciprocalSquareScheduled :
    logTwoSquareStieltjesRaw.Equiv logTwoReciprocalSquareScheduled := by
  unfold logTwoSquareStieltjesRaw
  exact RealRaw.prefixStabilize_equiv_anchor
    logTwoReciprocalSquareScheduled_valid
    logTwoSquareStieltjesCandidate_equiv_reciprocalSquareScheduled
    logTwoSquareStieltjesStabilizationRadius_covers_reciprocalSquareScheduled

/-- The square-substitution Stieltjes evaluator and the ordinary reciprocal
integral are equivalent raw reals.  The right side is scheduled only inside
the proof; its public evaluator remains the original integral algorithm. -/
theorem logTwoSquareStieltjesRaw_equiv_reciprocalIntegral :
    logTwoSquareStieltjesRaw.Equiv logTwoReciprocalIntegral := by
  have hsquare : logTwoSquareStieltjesRaw.Equiv
      logTwoReciprocalSquareScheduled :=
    logTwoSquareStieltjesRaw_equiv_reciprocalSquareScheduled
  have hschedule : logTwoReciprocalIntegral.Equiv
      logTwoReciprocalSquareScheduled :=
    RealRaw.schedule_equiv logTwoReciprocalIntegral
      logTwoReciprocalIntegral_valid logTwoSquareMeshStageSchedule
  exact RealRaw.equiv_trans logTwoSquareStieltjesRaw_valid
    logTwoReciprocalSquareScheduled_valid logTwoReciprocalIntegral_valid
    hsquare (RealRaw.equiv_symm hschedule)

/-- The certified square-pullback integral is the ordinary reciprocal
integral for `log 2`.  This is the project's first checked finite
change-of-variables theorem, specialized to the square map. -/
theorem logTwoSquarePullbackIntegral_equiv_reciprocalIntegral :
    logTwoSquarePullbackIntegral.Equiv logTwoReciprocalIntegral := by
  exact RealRaw.equiv_trans logTwoSquarePullbackIntegral_valid
    logTwoSquareStieltjesRaw_valid logTwoReciprocalIntegral_valid
    (RealRaw.equiv_symm logTwoSquareStieltjesRaw_equiv_pullbackIntegral)
    logTwoSquareStieltjesRaw_equiv_reciprocalIntegral

/-- The first arctangent integration-by-parts strip evaluates to `log 2`:
the literal certified integral of `x/(1+x²)` on the unit interval, multiplied
by two, agrees with the existing reciprocal-integral logarithm.  This is the
non-circular logarithmic half of the later formula for the integral of
`arctan`; the complementary `∫ arctan` strip and the global FTC/product rule
remain separate work. -/
theorem two_arctanLogKernelIntegral_equiv_logTwoReciprocalIntegral :
    (RealRaw.scaleRat 2 arctanLogKernelIntegral).Equiv
      logTwoReciprocalIntegral := by
  have hpull : (RealRaw.scaleRat 2 arctanLogKernelIntegral).Equiv
      logTwoSquarePullbackIntegral := by
    intro stage
    apply (RealRaw.compareAt_overlap_iff
      (RealRaw.scaleRat 2 arctanLogKernelIntegral)
      logTwoSquarePullbackIntegral stage stage).2
    change QInterval.Overlaps
      (RealRaw.scaleRatCompute 2 arctanLogKernelIntegral stage)
      (logTwoSquarePullbackIntegral.compute stage)
    rw [← logTwoSquarePullbackIntegral_compute_eq_two_arctanLogKernelIntegral]
    unfold QInterval.Overlaps
    have hordered := RealRaw.interval_order_of_valid
      logTwoSquarePullbackIntegral logTwoSquarePullbackIntegral_valid stage
    exact ⟨hordered, hordered⟩
  exact RealRaw.equiv_trans
    (RealRaw.scaleRat_valid_of_nonneg (by native_decide)
      arctanLogKernelIntegral_valid)
    logTwoSquarePullbackIntegral_valid logTwoReciprocalIntegral_valid hpull
    logTwoSquarePullbackIntegral_equiv_reciprocalIntegral

/-- One paired update of the alternating harmonic enclosure for `log 2`.

The first component is the upper endpoint and the second the lower endpoint.
At the `i`th update, the negative term has denominator `2*i+2` and the next
positive term has denominator `2*i+3`. -/
def logTwoStep (state : Rat × Rat) (i : Nat) : Rat × Rat :=
  let lo := state.1 - 1 / (2 * (i : Rat) + 2)
  let hi := lo + 1 / (2 * (i : Rat) + 3)
  (hi, lo)

/-- Paired partial-sum state for the logarithmic alternating series. -/
def logTwoState (n : Nat) : Rat × Rat :=
  (List.range n).foldl logTwoStep (1, 0)

/-- Lower endpoint of the `n`th alternating-harmonic enclosure. -/
def logTwoLo (n : Nat) : Rat :=
  (logTwoState n).2

/-- Upper endpoint of the `n`th alternating-harmonic enclosure. -/
def logTwoHi (n : Nat) : Rat :=
  (logTwoState n).1

/-- The rational interval at stage `n` for the alternating-harmonic
presentation of `log 2`. -/
def logTwoCompute (n : Nat) : QInterval :=
  { lo := logTwoLo n, hi := logTwoHi n }

theorem logTwoState_succ (n : Nat) :
    logTwoState (n + 1) = logTwoStep (logTwoState n) n := by
  unfold logTwoState
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The finite harmonic sum, kept as a recursive rational computation so that
the conversion of the alternating logarithm enclosure to Riemann sums stays
entirely algebraic. -/
def harmonicSum : Nat -> Rat
  | 0 => 0
  | n + 1 => harmonicSum n + 1 / ((n + 1 : Nat) : Rat)

theorem harmonicSum_succ (n : Nat) :
    harmonicSum (n + 1) = harmonicSum n + 1 / ((n + 1 : Nat) : Rat) :=
  rfl

theorem logTwo_width_eq (n : Nat) :
    (logTwoCompute n).width = 1 / ((2 * n + 1 : Nat) : Rat) := by
  cases n with
  | zero =>
      native_decide
  | succ n =>
      unfold logTwoCompute logTwoLo logTwoHi
      rw [logTwoState_succ]
      simp [logTwoStep]
      have hden :
          2 * ((n : Rat) + 1) + 1 = 2 * (n : Rat) + 3 := by
        grind
      rw [hden]
      grind [QInterval.width, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem logTwoHi_eq_logTwoLo_add_remainder (n : Nat) :
    logTwoHi n = logTwoLo n + 1 / ((2 * n + 1 : Nat) : Rat) := by
  have hwidth := logTwo_width_eq n
  change logTwoHi n - logTwoLo n = 1 / ((2 * n + 1 : Nat) : Rat) at hwidth
  grind [Rat.sub_eq_add_neg]

theorem logTwoLo_succ (n : Nat) :
    logTwoLo (n + 1) =
      logTwoLo n + 1 / ((2 * n + 1 : Nat) : Rat) -
        1 / ((2 * n + 2 : Nat) : Rat) := by
  unfold logTwoLo
  rw [logTwoState_succ]
  simp [logTwoStep]
  have hhi := logTwoHi_eq_logTwoLo_add_remainder n
  change (logTwoState n).1 - 1 / (2 * (n : Rat) + 2) = _
  change (logTwoState n).1 =
    (logTwoState n).2 + 1 / ((2 * n + 1 : Nat) : Rat) at hhi
  have hden1 : 2 * (n : Rat) + 1 = ((2 * n + 1 : Nat) : Rat) := by
    exact_mod_cast (by rfl : 2 * n + 1 = 2 * n + 1)
  rw [hden1]
  rw [hhi]

private theorem one_div_nat_succ_eq_two_half_terms (n : Nat) :
    1 / ((n + 1 : Nat) : Rat) =
      1 / ((2 * n + 2 : Nat) : Rat) +
        1 / ((2 * n + 2 : Nat) : Rat) := by
  have hden : ((2 * n + 2 : Nat) : Rat) =
      2 * ((n + 1 : Nat) : Rat) := by
    exact_mod_cast (by omega : 2 * n + 2 = 2 * (n + 1))
  rw [hden]
  simp only [Rat.div_def, Rat.one_mul, Rat.inv_mul_rev]
  have hhalf : (2 : Rat)⁻¹ + (2 : Rat)⁻¹ = 1 := by native_decide
  calc
    ((n + 1 : Nat) : Rat)⁻¹ = ((n + 1 : Nat) : Rat)⁻¹ * 1 :=
      (Rat.mul_one _).symm
    _ = ((n + 1 : Nat) : Rat)⁻¹ * ((2 : Rat)⁻¹ + (2 : Rat)⁻¹) := by
      rw [hhalf]
    _ = ((n + 1 : Nat) : Rat)⁻¹ * (2 : Rat)⁻¹ +
          ((n + 1 : Nat) : Rat)⁻¹ * (2 : Rat)⁻¹ := by
      rw [Rat.mul_add]

private theorem harmonicSum_double_succ (n : Nat) :
    harmonicSum (2 * (n + 1)) =
      harmonicSum (2 * n) + 1 / ((2 * n + 1 : Nat) : Rat) +
        1 / ((2 * n + 2 : Nat) : Rat) := by
  have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  rw [hindex, harmonicSum_succ, harmonicSum_succ]

/-- The tail of a finite harmonic sum, written as an explicit finite list
sum.  It is the combinatorial reindexing that turns `H_(2n)-H_n` into a
right-endpoint reciprocal sum. -/
private theorem harmonicSum_add_sub_eq_tail (n m : Nat) :
    harmonicSum (n + m) - harmonicSum n =
      (List.range m).foldl
        (fun acc k => acc + 1 / ((n + k + 1 : Nat) : Rat)) 0 := by
  induction m with
  | zero =>
      simp
      grind [Rat.sub_eq_add_neg]
  | succ m ih =>
      have hindex : n + (m + 1) = (n + m) + 1 := by omega
      rw [hindex, harmonicSum_succ]
      calc
        harmonicSum (n + m) + 1 / ((n + m + 1 : Nat) : Rat) -
            harmonicSum n =
          (harmonicSum (n + m) - harmonicSum n) +
            1 / ((n + m + 1 : Nat) : Rat) := by
              grind [Rat.sub_eq_add_neg]
        _ = (List.range m).foldl
              (fun acc k => acc + 1 / ((n + k + 1 : Nat) : Rat)) 0 +
            1 / ((n + m + 1 : Nat) : Rat) := by rw [ih]
        _ = (List.range (m + 1)).foldl
              (fun acc k => acc + 1 / ((n + k + 1 : Nat) : Rat)) 0 := by
              simp only [List.range_succ, List.foldl_append, List.foldl_cons,
                List.foldl_nil]

/-- The finite right-endpoint reciprocal sum on the uniform `n`-mesh of
`[0,1]`, after cancellation of the mesh factor. -/
def logTwoRightRiemann (n : Nat) : Rat :=
  (List.range n).foldl
    (fun acc k => acc + 1 / ((n + k + 1 : Nat) : Rat)) 0

/-- One right-mesh rectangle for `logTwoKernel` simplifies to the matching
reciprocal-harmonic term.  Positivity of the mesh count is exactly what makes
the cancellation constructive. -/
private theorem logTwo_rightRiemann_term (n k : Nat) (hn : 0 < n) :
    (1 / (n : Rat)) *
        logTwoKernel (((k + 1 : Nat) : Rat) / (n : Rat)) =
      1 / ((n + k + 1 : Nat) : Rat) := by
  let N : Rat := (n : Rat)
  let K : Rat := ((k + 1 : Nat) : Rat)
  have hsum : ((n + k + 1 : Nat) : Rat) = N + K := by
    dsimp [N, K]
    exact_mod_cast (by omega : n + k + 1 = n + (k + 1))
  unfold logTwoKernel
  rw [hsum]
  change (1 / N) * (1 / (1 + K / N)) = 1 / (N + K)
  have hNpos : 0 < N := by
    dsimp [N]
    exact (Rat.natCast_pos).2 hn
  have hNne : N ≠ 0 := Rat.ne_of_gt hNpos
  have hden : 1 + K / N = (N + K) / N := by
    rw [Rat.div_def, Rat.div_def]
    have hcancel : N * N⁻¹ = 1 := Rat.mul_inv_cancel N hNne
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  rw [hden]
  simp only [Rat.div_def, Rat.one_mul, Rat.inv_mul_rev, Rat.inv_inv]
  rw [← Rat.mul_assoc, Rat.inv_mul_cancel N hNne, Rat.one_mul]

/-- Finite left folds agree when their update functions agree pointwise. -/
private theorem foldl_eq_of_pointwise
    (f g : Rat -> Nat -> Rat)
    (h : ∀ acc k, f acc k = g acc k)
    (xs : List Nat) (acc : Rat) :
    xs.foldl f acc = xs.foldl g acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl]
      rw [h acc x]
      exact ih (g acc x)

/-- The literal uniform right Riemann sum for `logTwoKernel` on `[0,1]`.
It deliberately retains both the mesh width and the kernel evaluation, so
that the bridge from the alternating series has a transparent integral form. -/
def logTwoKernelRightRiemann (n : Nat) : Rat :=
  (List.range n).foldl
    (fun acc k =>
      acc + (1 / (n : Rat)) *
        logTwoKernel (((k + 1 : Nat) : Rat) / (n : Rat))) 0

/-- On a positive mesh, the literal right Riemann sum has the reciprocal
harmonic normal form obtained by cancelling the mesh factor. -/
theorem logTwoKernelRightRiemann_eq_logTwoRightRiemann
    (n : Nat) (hn : 0 < n) :
    logTwoKernelRightRiemann n = logTwoRightRiemann n := by
  unfold logTwoKernelRightRiemann logTwoRightRiemann
  apply foldl_eq_of_pointwise
  intro acc k
  rw [logTwo_rightRiemann_term n k hn]

theorem harmonicSum_double_sub_eq_logTwoRightRiemann (n : Nat) :
    harmonicSum (2 * n) - harmonicSum n = logTwoRightRiemann n := by
  rw [show 2 * n = n + n by omega]
  exact harmonicSum_add_sub_eq_tail n n

/-- The lower alternating-harmonic endpoint is the finite reciprocal sum
`H_(2n) - H_n`.  This is the exact algebraic normal form used to connect the
logarithm series with right-endpoint Riemann sums for `t ↦ 1/(1+t)`. -/
theorem logTwoLo_eq_harmonicSum_sub (n : Nat) :
    logTwoLo n = harmonicSum (2 * n) - harmonicSum n := by
  induction n with
  | zero => native_decide
  | succ n ih =>
      rw [logTwoLo_succ, ih, harmonicSum_double_succ, harmonicSum_succ]
      rw [one_div_nat_succ_eq_two_half_terms]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- The lower series endpoint is exactly the finite uniform right Riemann sum
for the translated reciprocal kernel.  The later logarithm theorem compares
that mesh with the literal nested Lipschitz--Darboux boxes. -/
theorem logTwoLo_eq_logTwoRightRiemann (n : Nat) :
    logTwoLo n = logTwoRightRiemann n := by
  rw [logTwoLo_eq_harmonicSum_sub,
    harmonicSum_double_sub_eq_logTwoRightRiemann]

/-- The alternating-series lower endpoint is exactly a literal uniform right
Riemann sum for `t ↦ 1/(1+t)`.  This is an equality of finite rational
computations, before the remaining comparison with the dyadic Darboux boxes. -/
theorem logTwoLo_eq_logTwoKernelRightRiemann
    (n : Nat) (hn : 0 < n) :
    logTwoLo n = logTwoKernelRightRiemann n := by
  rw [logTwoLo_eq_logTwoRightRiemann,
    logTwoKernelRightRiemann_eq_logTwoRightRiemann n hn]

theorem logTwoLo_mono_succ (n : Nat) :
    logTwoLo n <= logTwoLo (n + 1) := by
  unfold logTwoLo
  rw [logTwoState_succ]
  simp [logTwoStep]
  have hterm :
      1 / (2 * (n : Rat) + 2) <=
        (logTwoState n).1 - (logTwoState n).2 := by
    change 1 / (2 * (n : Rat) + 2) <= (logTwoCompute n).width
    rw [logTwo_width_eq]
    have hden :
        ((2 * n + 2 : Nat) : Rat) = 2 * (n : Rat) + 2 := by
      exact_mod_cast (by rfl : 2 * n + 2 = 2 * n + 2)
    rw [← hden]
    exact FTC.one_div_nat_antitone
      (by omega : 0 < 2 * n + 1)
      (by omega : 0 < 2 * n + 2)
      (by omega : 2 * n + 1 <= 2 * n + 2)
  grind [Rat.sub_eq_add_neg]

theorem logTwoHi_anti_succ (n : Nat) :
    logTwoHi (n + 1) <= logTwoHi n := by
  unfold logTwoHi
  rw [logTwoState_succ]
  simp [logTwoStep]
  have hterm :
      1 / (2 * (n : Rat) + 3) <=
        1 / (2 * (n : Rat) + 2) := by
    have hden3 :
        ((2 * n + 3 : Nat) : Rat) = 2 * (n : Rat) + 3 := by
      exact_mod_cast (by rfl : 2 * n + 3 = 2 * n + 3)
    have hden2 :
        ((2 * n + 2 : Nat) : Rat) = 2 * (n : Rat) + 2 := by
      exact_mod_cast (by rfl : 2 * n + 2 = 2 * n + 2)
    rw [← hden3, ← hden2]
    exact FTC.one_div_nat_antitone
      (by omega : 0 < 2 * n + 2)
      (by omega : 0 < 2 * n + 3)
      (by omega : 2 * n + 2 <= 2 * n + 3)
  grind [Rat.sub_eq_add_neg]

theorem logTwoLo_mono {n m : Nat} (hnm : n <= m) :
    logTwoLo n <= logTwoLo m := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step _ ih => exact Rat.le_trans ih (logTwoLo_mono_succ _)

theorem logTwoHi_anti {n m : Nat} (hnm : n <= m) :
    logTwoHi m <= logTwoHi n := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step _ ih => exact Rat.le_trans (logTwoHi_anti_succ _) ih

theorem logTwoCompute_ordered (n : Nat) :
    (logTwoCompute n).lo <= (logTwoCompute n).hi := by
  have hwidth := logTwo_width_eq n
  have hpos : 0 < 1 / ((2 * n + 1 : Nat) : Rat) :=
    one_div_nat_pos (by omega : 0 < 2 * n + 1)
  change logTwoHi n - logTwoLo n = 1 / ((2 * n + 1 : Nat) : Rat) at hwidth
  change logTwoLo n <= logTwoHi n
  grind [Rat.sub_eq_add_neg]

theorem logTwoCompute_nested (n m : Nat) (hnm : n <= m) :
    (logTwoCompute n).lo <= (logTwoCompute m).lo /\
      (logTwoCompute m).lo <= (logTwoCompute m).hi /\
      (logTwoCompute m).hi <= (logTwoCompute n).hi := by
  constructor
  · exact logTwoLo_mono hnm
  · constructor
    · exact logTwoCompute_ordered m
    · exact logTwoHi_anti hnm

theorem logTwoCompute_widths_shrink :
    RealRaw.WidthsShrinkToZero logTwoCompute := by
  intro eps
  let N : Nat := eps.val.den + 1
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  refine ⟨N, ?_⟩
  intro n hn
  rw [logTwo_width_eq]
  have hsmallN : 1 / (N : Rat) <= eps.val := by
    dsimp [N]
    exact FTC.one_div_den_succ_le_of_pos eps.property
  calc
    1 / ((2 * n + 1 : Nat) : Rat) <= 1 / (N : Rat) :=
      FTC.one_div_nat_antitone hNpos
        (by omega : 0 < 2 * n + 1)
        (by omega : N <= 2 * n + 1)
    _ <= eps.val := hsmallN

theorem logTwoCompute_valid : RealRaw.ValidCompute logTwoCompute := by
  constructor
  · intro n
    rw [logTwo_width_eq]
    exact Rat.le_of_lt (one_div_nat_pos (by omega : 0 < 2 * n + 1))
  · constructor
    · exact logTwoCompute_nested
    · exact logTwoCompute_widths_shrink

/-- A certified raw real for the logarithmic series
`log 2 = 1 - 1/2 + 1/3 - ...`.

Its validity and the displayed `O(1/n)` rate are finite rational proofs.  The
separate theorem later in this module identifies this raw value with the
literal finite reciprocal integral at two by rational mesh comparison. -/
def logTwoSeries : RealRaw where
  compute := logTwoCompute
  rate := .power
    1 1 1 (by omega)
    (by
      intro n hn
      rw [logTwo_width_eq, Rat.pow_one]
      exact FTC.one_div_nat_antitone hn
        (by omega : 0 < 2 * n + 1)
        (by omega : n <= 2 * n + 1))

theorem logTwoSeries_valid : logTwoSeries.Valid :=
  logTwoCompute_valid

/-- The displayed rate certificate for the logarithmic series is
`width(logTwoSeries[n]) <= 1/n` for every positive stage. -/
theorem logTwoSeries_width_le_one_div (n : Nat) (hn : 0 < n) :
    (logTwoSeries.compute n).width <= 1 / (n : Rat) := by
  rw [show logTwoSeries.compute n = logTwoCompute n by rfl, logTwo_width_eq]
  exact FTC.one_div_nat_antitone hn
    (by omega : 0 < 2 * n + 1)
    (by omega : n <= 2 * n + 1)

/-- At a dyadic mesh size, the alternating-series lower endpoint is literally
enclosed by the finite Darboux integral box.  The proof combines the exact
harmonic-to-right-Riemann identity with the generic finite Riemann/Darboux
comparison; no limiting real number is introduced here. -/
theorem logTwoDarbouxCompute_contains_dyadicSeriesLower (stage : Nat) :
    (logTwoDarbouxCompute stage).ContainsInterval
      { lo := logTwoLo (2 ^ stage), hi := logTwoLo (2 ^ stage) } := by
  have h := IntegralIdentities.LipschitzDyadic.compute_contains_uniformRightEndpointSum
      (f := logTwoKernel) (L := 1) logTwoKernel_lipschitz stage
  have hpow : 0 < 2 ^ stage := Nat.pow_pos (by omega : 0 < 2)
  rw [logTwoLo_eq_logTwoKernelRightRiemann (2 ^ stage) hpow]
  simpa [logTwoDarbouxCompute,
    IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum,
    logTwoKernelRightRiemann] using h

private theorem logTwoDarbouxCompute_nested
    (n m : Nat) (hnm : n <= m) :
    (logTwoDarbouxCompute n).lo <= (logTwoDarbouxCompute m).lo /\
      (logTwoDarbouxCompute m).lo <= (logTwoDarbouxCompute m).hi /\
      (logTwoDarbouxCompute m).hi <= (logTwoDarbouxCompute n).hi := by
  simpa [logTwoDarbouxCompute] using
    (IntegralIdentities.LipschitzDyadic.compute_nested
      (f := logTwoKernel) (L := 1) logTwoKernel_lipschitz n m hnm)

private theorem succ_le_two_pow (n : Nat) : n + 1 <= 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 2 * (n + 1) := by omega
        _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by
          rw [Nat.pow_succ]
          omega

/-- The alternating harmonic construction of `log 2` and the literal
Lipschitz--Darboux integral of `1/x` on `[1,2]` are the same raw real.

For arbitrary requested stages, compare both nested algorithms at a common
dyadic refinement.  The finite enclosure above places the series box inside
the integral box there; the elementary bound `k + 1 <= 2^k` makes that mesh
cofinal.  Thus the equality is an overlap proof between rational interval
algorithms, not an appeal to completeness or a general FTC axiom. -/
theorem logTwoSeries_equiv_logTwoReciprocalIntegral :
    logTwoSeries.Equiv logTwoReciprocalIntegral := by
  apply RealRaw.equiv_of_le_of_ge
  · intro n m
    let k := n + m + 1
    have hmk : m <= k := by
      dsimp [k]
      omega
    have hnpow : n <= 2 ^ k := by
      exact Nat.le_trans (by dsimp [k]; omega) (succ_le_two_pow k)
    have hseries := logTwoCompute_nested n (2 ^ k) hnpow
    have hdarboux := logTwoDarbouxCompute_nested m k hmk
    have hcontain := logTwoDarbouxCompute_contains_dyadicSeriesLower k
    change logTwoLo n <= (logTwoDarbouxCompute m).hi
    exact Rat.le_trans hseries.1
      (Rat.le_trans hcontain.2 hdarboux.2.2)
  · intro n m
    let k := n + m + 1
    have hnk : n <= k := by
      dsimp [k]
      omega
    have hmpow : m <= 2 ^ k := by
      exact Nat.le_trans (by dsimp [k]; omega) (succ_le_two_pow k)
    have hdarboux := logTwoDarbouxCompute_nested n k hnk
    have hseries := logTwoCompute_nested m (2 ^ k) hmpow
    have hcontain := logTwoDarbouxCompute_contains_dyadicSeriesLower k
    change (logTwoDarbouxCompute n).lo <= logTwoHi m
    exact Rat.le_trans hdarboux.1
      (Rat.le_trans hcontain.1
        (Rat.le_trans hseries.2.1 hseries.2.2))

end Logarithm

end ComputableAnalysis
