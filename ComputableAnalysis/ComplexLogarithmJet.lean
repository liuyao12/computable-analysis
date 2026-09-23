import ComputableAnalysis.ComplexLogarithmApproximation
import ComputableAnalysis.RepresentedHolomorphicJet

/-!
# Represented first jet of the local complex logarithm

The value component is the checked `log(1+w)` evaluator on the closed
rational half-ball.  Its derivative component is computed independently from
the geometric series

`1 - w + w^2 - w^3 + ...`.

Both computations use finite rational-complex prefixes, explicit geometric
tail radii, and finite-prefix stabilization.  Their common finite first jet
is therefore executable at every stage.  The coefficient-shift theorem from
`ComplexLogarithmApproximation` identifies the second prefix as the formal
derivative of the first.
-/

namespace ComputableAnalysis
namespace ComplexLogarithmJet

private def half : Rat := (1 : Rat) / 2

/-- The `n`th geometric-series term for `1/(1+w)`. -/
def derivativeTerm (w : QComplex) (n : Nat) : QComplex :=
  QComplex.scaleRat (FormalPowerSeries.altSign n) (QComplex.pow w n)

/-- A finite block of derivative-series terms beginning at `start`. -/
def derivativeTailPartial (w : QComplex) (start : Nat) : Nat -> QComplex
  | 0 => QComplex.zero
  | terms + 1 =>
      QComplex.add (derivativeTailPartial w start terms)
        (derivativeTerm w (start + terms))

/-- The first `terms` geometric-series terms for `1/(1+w)`. -/
def derivativePrefix (w : QComplex) (terms : Nat) : QComplex :=
  derivativeTailPartial w 0 terms

theorem derivativeTailPartial_add
    (w : QComplex) (start first later : Nat) :
    derivativeTailPartial w start (first + later) =
      QComplex.add (derivativeTailPartial w start first)
        (derivativeTailPartial w (start + first) later) := by
  induction later with
  | zero =>
      rw [Nat.add_zero]
      exact (QComplex.add_zero_cert _).symm
  | succ later ih =>
      rw [Nat.add_succ, derivativeTailPartial, ih,
        derivativeTailPartial]
      rw [show start + (first + later) = (start + first) + later by omega]
      exact QComplex.add_assoc_cert _ _ _

theorem derivativePrefix_add (w : QComplex) (first later : Nat) :
    derivativePrefix w (first + later) =
      QComplex.add (derivativePrefix w first)
        (derivativeTailPartial w first later) := by
  simpa [derivativePrefix, Nat.zero_add] using
    derivativeTailPartial_add w 0 first later

private theorem altSign_succ (n : Nat) :
    FormalPowerSeries.altSign (n + 1) =
      -FormalPowerSeries.altSign n := by
  have hreverse : FormalPowerSeries.altSign n =
      -FormalPowerSeries.altSign (n + 1) := by
    unfold FormalPowerSeries.altSign
    split <;> split
    all_goals first | decide +kernel | omega
  rw [hreverse, Rat.neg_neg]

theorem derivativeTerm_succ (w : QComplex) (n : Nat) :
    derivativeTerm w (n + 1) =
      QComplex.neg (QComplex.mul w (derivativeTerm w n)) := by
  unfold derivativeTerm
  rw [altSign_succ, QComplex.pow]
  cases w with
  | mk re im =>
      cases hpower : QComplex.pow { re := re, im := im } n with
      | mk powerRe powerIm =>
        simp only [QComplex.scaleRat, QComplex.mul, QComplex.neg]
        congr 1 <;>
          grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
            Rat.neg_mul, Rat.mul_neg, Rat.neg_neg,
            Rat.sub_eq_add_neg]

theorem derivativePrefix_succ (w : QComplex) (n : Nat) :
    derivativePrefix w (n + 1) =
      QComplex.add (derivativePrefix w n) (derivativeTerm w n) := by
  unfold derivativePrefix
  rw [derivativeTailPartial]
  congr 2
  omega

private theorem mul_sub_cert (x y z : QComplex) :
    QComplex.mul x (QComplex.sub y z) =
      QComplex.sub (QComplex.mul x y) (QComplex.mul x z) := by
  cases x
  cases y
  cases z
  simp [QComplex.mul, QComplex.sub, QComplex.add, QComplex.neg]
  constructor <;>
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
      Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.sub_eq_add_neg]

/-- Exact finite geometric-series identity
`(1+w) * S_n = 1 - (-w)^n`. -/
theorem one_add_mul_derivativePrefix (w : QComplex) (n : Nat) :
    QComplex.mul (QComplex.add QComplex.one w) (derivativePrefix w n) =
      QComplex.sub QComplex.one (derivativeTerm w n) := by
  induction n with
  | zero =>
      cases w
      simp [derivativePrefix, derivativeTailPartial, derivativeTerm,
        FormalPowerSeries.altSign, QComplex.pow, QComplex.mul,
        QComplex.scaleRat, QComplex.add, QComplex.sub, QComplex.neg,
        QComplex.zero, QComplex.one]
      grind
  | succ n ih =>
      rw [derivativePrefix_succ, QComplex.mul_add_cert, ih,
        derivativeTerm_succ]
      cases w with
      | mk re im =>
          cases hterm : derivativeTerm { re := re, im := im } n with
          | mk termRe termIm =>
              simp [QComplex.mul, QComplex.add, QComplex.sub, QComplex.neg,
                QComplex.one]
              constructor <;>
                grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
                  Rat.neg_mul, Rat.mul_neg, Rat.neg_neg,
                  Rat.sub_eq_add_neg]

private theorem altSign_abs (n : Nat) :
    qabs (FormalPowerSeries.altSign n) = 1 := by
  unfold FormalPowerSeries.altSign
  split <;> decide +kernel

/-- Each derivative term is dominated by the corresponding half-geometric
term on the logarithm chart. -/
theorem derivativeTerm_normBound_le {w : QComplex}
    (hw : QComplex.normBound w <= half) (n : Nat) :
    QComplex.normBound (derivativeTerm w n) <= half ^ n := by
  unfold derivativeTerm
  rw [QComplex.normBound_scaleRat, altSign_abs, Rat.one_mul]
  exact QComplex.normBound_pow_le (by decide +kernel) hw n

/-- Finite derivative tails are bounded by a finite geometric majorant. -/
theorem derivativeTailPartial_normBound_le {w : QComplex}
    (hw : QComplex.normBound w <= half) (start terms : Nat) :
    QComplex.normBound (derivativeTailPartial w start terms) <=
      RationalMajorant.geomTailPartial 1 half start terms := by
  induction terms with
  | zero =>
      change QComplex.normBound QComplex.zero <= 0
      rw [QComplex.normBound_zero]
      exact Rat.le_refl
  | succ terms ih =>
      rw [derivativeTailPartial, RationalMajorant.geomTailPartial]
      calc
        QComplex.normBound
            (QComplex.add (derivativeTailPartial w start terms)
              (derivativeTerm w (start + terms))) <=
          QComplex.normBound (derivativeTailPartial w start terms) +
            QComplex.normBound (derivativeTerm w (start + terms)) :=
              QComplex.normBound_add_le _ _
        _ <= RationalMajorant.geomTailPartial 1 half start terms +
            half ^ (start + terms) :=
          rat_add_le_add ih (derivativeTerm_normBound_le hw (start + terms))
        _ = RationalMajorant.geomTailPartial 1 half start terms +
            1 * half ^ (start + terms) := by rw [Rat.one_mul]

/-- Uniform derivative-tail radius after `stage` terms. -/
def derivativeStageRadius (stage : Nat) : Rat :=
  RationalMajorant.geomTailBound 1 half stage

theorem derivativeTailPartial_normBound_le_stageRadius {w : QComplex}
    (hw : QComplex.normBound w <= half) (start terms : Nat) :
    QComplex.normBound (derivativeTailPartial w start terms) <=
      derivativeStageRadius start := by
  exact Rat.le_trans (derivativeTailPartial_normBound_le hw start terms)
    (RationalMajorant.geometric_tail_partial_bound
      (by decide +kernel : (0 : Rat) <= 1)
      (by decide +kernel : (0 : Rat) <= half)
      (by exact Rat.le_refl))

theorem derivativeStageRadius_eq_two_mul_half_pow (stage : Nat) :
    derivativeStageRadius stage = 2 * half ^ stage := by
  unfold derivativeStageRadius RationalMajorant.geomTailBound
  rw [Rat.mul_one]

private theorem half_pow_antitone {first later : Nat}
    (h : first <= later) : half ^ later <= half ^ first := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      exact Rat.le_refl
  | succ extra ih =>
      rw [show first + (extra + 1) = (first + extra) + 1 by omega,
        Rat.pow_succ]
      have hnonneg : 0 <= half ^ (first + extra) :=
        Rat.pow_nonneg (by decide +kernel)
      have hstep : half ^ (first + extra) * half <=
          half ^ (first + extra) := by
        calc
          half ^ (first + extra) * half <=
              half ^ (first + extra) * 1 :=
            Rat.mul_le_mul_of_nonneg_left (by decide +kernel) hnonneg
          _ = half ^ (first + extra) := Rat.mul_one _
      exact Rat.le_trans hstep ih

theorem derivativeStageRadius_shrinks :
    ShrinksToZero derivativeStageRadius := by
  intro eps
  let start := RationalMajorant.halfDecayShift 2 eps
  refine ⟨start, ?_⟩
  intro stage hstage
  rw [derivativeStageRadius_eq_two_mul_half_pow]
  calc
    2 * half ^ stage <= 2 * half ^ start :=
      Rat.mul_le_mul_of_nonneg_left (half_pow_antitone hstage)
        (by decide +kernel)
    _ = 2 * ((1 : Rat) / 2) ^ start := by rfl
    _ <= eps.val :=
      RationalMajorant.halfDecayShift_spec (by decide +kernel) eps

/-- Direct exact derivative-prefix candidates. -/
def derivativeDirectCandidate (w : QComplex) : ComplexRaw where
  compute := fun stage => QBox.point (derivativePrefix w stage)

/-- Executable represented derivative series for the local logarithm. -/
def derivativeRawAt (w : QComplex) : ComplexRaw :=
  ComplexRaw.cauchyStabilize (derivativeDirectCandidate w)
    derivativeStageRadius

private theorem derivativeDirectCandidate_ordered (w : QComplex) :
    forall stage, ((derivativeDirectCandidate w).compute stage).Ordered := by
  intro stage
  exact QComplex.le_refl _

private theorem derivativeDirectCandidate_shrinks (w : QComplex) :
    ComplexRaw.WidthsShrinkToZero (derivativeDirectCandidate w).compute := by
  intro eps
  refine ⟨0, ?_⟩
  intro stage _
  constructor <;>
    simpa [derivativeDirectCandidate, QBox.point, QBox.width, QBox.height,
      Rat.sub_self] using Rat.le_of_lt eps.property

private theorem derivativeDirectCandidate_future {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    forall first later, first <= later ->
      ((derivativeDirectCandidate w).compute later).NestedIn
        (QBox.expand ((derivativeDirectCandidate w).compute first)
          (derivativeStageRadius first)) := by
  intro first later hfl
  let extra := later - first
  have hlater : later = first + extra := by
    dsimp [extra]
    omega
  have hprefix := derivativePrefix_add w first extra
  rw [← hlater] at hprefix
  change (QBox.point (derivativePrefix w later)).NestedIn
    (QBox.expand (QBox.point (derivativePrefix w first))
      (derivativeStageRadius first))
  rw [hprefix]
  exact ComplexExponentialApproximation.point_add_error_nested_expand _ _
    (derivativeTailPartial_normBound_le_stageRadius hw first extra)

theorem derivativeRawAt_contains_prefix {w : QComplex}
    (hw : QComplex.normBound w <= half) (stage : Nat) :
    (QBox.point (derivativePrefix w stage)).NestedIn
      ((derivativeRawAt w).compute stage) := by
  exact ComplexRaw.cauchyStabilize_contains_current
    (derivativeDirectCandidate_future hw) stage

theorem derivativeRawAt_valid {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    (derivativeRawAt w).Valid := by
  apply ComplexRaw.cauchyStabilize_valid
  · exact derivativeDirectCandidate_ordered w
  · exact derivativeDirectCandidate_shrinks w
  · exact derivativeDirectCandidate_future hw
  · exact derivativeStageRadius_shrinks

/-! ## Identification of the derivative series with the exact reciprocal -/

theorem one_add_normSq_pos {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    0 < QComplex.normSq (QComplex.add QComplex.one w) := by
  let denominator := QComplex.add QComplex.one w
  have habsRe : qabs w.re <= half := by
    exact Rat.le_trans
      (show qabs w.re <= QComplex.normBound w by
        unfold QComplex.normBound
        have him := qabs_nonneg w.im
        grind) hw
  have hreLower : half <= denominator.re := by
    have hneg := neg_qabs_le_self w.re
    have hnegHalf : -half <= -qabs w.re := Rat.neg_le_neg habsRe
    dsimp [denominator]
    simp only [QComplex.add, QComplex.one]
    calc
      half = 1 + (-half) := by
        unfold half
        decide +kernel
      _ <= 1 + w.re := Rat.add_le_add_left.mpr
        (Rat.le_trans hnegHalf hneg)
  have hreNonneg : 0 <= denominator.re := by
    exact Rat.le_trans (by decide +kernel : (0 : Rat) <= half) hreLower
  have hreSquare : half * half <= denominator.re * denominator.re := by
    calc
      half * half <= denominator.re * half :=
        Rat.mul_le_mul_of_nonneg_right hreLower
          (by decide +kernel : (0 : Rat) <= half)
      _ <= denominator.re * denominator.re :=
        Rat.mul_le_mul_of_nonneg_left hreLower hreNonneg
  have himSquare : 0 <= denominator.im * denominator.im :=
    rat_square_nonneg_basic _
  have hlower : (1 : Rat) / 4 <= QComplex.normSq denominator := by
    unfold QComplex.normSq
    have hhalfSquare : half * half = (1 : Rat) / 4 := by
      unfold half
      decide +kernel
    rw [← hhalfSquare]
    have hadd : denominator.re * denominator.re <=
        denominator.re * denominator.re + denominator.im * denominator.im := by
      grind
    exact Rat.le_trans hreSquare hadd
  grind

theorem one_add_normSq_ne_zero {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    QComplex.normSq (QComplex.add QComplex.one w) ≠ 0 :=
  Rat.ne_of_gt (one_add_normSq_pos hw)

theorem inverse_one_add_normBound_le_eight {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    QComplex.normBound
        (QComplex.inverse (QComplex.add QComplex.one w)) <= 8 := by
  let denominator := QComplex.add QComplex.one w
  have hdenNorm : QComplex.normBound denominator <= (3 : Rat) / 2 := by
    calc
      QComplex.normBound denominator <=
          QComplex.normBound QComplex.one + QComplex.normBound w :=
        QComplex.normBound_add_le _ _
      _ <= 1 + half := by
        have hone : QComplex.normBound QComplex.one = 1 := by decide +kernel
        rw [hone]
        exact Rat.add_le_add_left.mpr hw
      _ = (3 : Rat) / 2 := by
        unfold half
        decide +kernel
  have hnormSqLower : (1 : Rat) / 4 <= QComplex.normSq denominator := by
    have hpos := one_add_normSq_pos hw
    let re := denominator.re
    have habsRe : qabs w.re <= half := by
      exact Rat.le_trans
        (show qabs w.re <= QComplex.normBound w by
          unfold QComplex.normBound
          have him := qabs_nonneg w.im
          grind) hw
    have hreLower : half <= re := by
      have hneg := neg_qabs_le_self w.re
      have hnegHalf : -half <= -qabs w.re := Rat.neg_le_neg habsRe
      dsimp [re, denominator]
      simp only [QComplex.add, QComplex.one]
      calc
        half = 1 + (-half) := by
          unfold half
          decide +kernel
        _ <= 1 + w.re := Rat.add_le_add_left.mpr
          (Rat.le_trans hnegHalf hneg)
    have hreNonneg : 0 <= re :=
      Rat.le_trans (by decide +kernel : (0 : Rat) <= half) hreLower
    have hreSquare : half * half <= re * re := by
      calc
        half * half <= re * half :=
          Rat.mul_le_mul_of_nonneg_right hreLower
            (by decide +kernel : (0 : Rat) <= half)
        _ <= re * re := Rat.mul_le_mul_of_nonneg_left hreLower hreNonneg
    have himSquare : 0 <= denominator.im * denominator.im :=
      rat_square_nonneg_basic _
    unfold QComplex.normSq
    have hhalfSquare : half * half = (1 : Rat) / 4 := by
      unfold half
      decide +kernel
    rw [← hhalfSquare]
    have hadd : re * re <= re * re + denominator.im * denominator.im := by
      grind
    exact Rat.le_trans hreSquare hadd
  have hinvNormSq : (QComplex.normSq denominator)⁻¹ <= 4 := by
    have h := Rat.inv_antitone_of_pos
      (a := (1 : Rat) / 4) (b := QComplex.normSq denominator)
      (by decide +kernel) hnormSqLower
    have hquarterInv : ((1 : Rat) / 4)⁻¹ = 4 := by decide +kernel
    rw [hquarterInv] at h
    exact h
  rw [QComplex.normBound_inverse_eq denominator (one_add_normSq_pos hw)]
  calc
    QComplex.normBound denominator * (QComplex.normSq denominator)⁻¹ <=
        ((3 : Rat) / 2) * (QComplex.normSq denominator)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hdenNorm
        (Rat.le_of_lt ((Rat.inv_pos).2 (one_add_normSq_pos hw)))
    _ <= ((3 : Rat) / 2) * 4 :=
      Rat.mul_le_mul_of_nonneg_left hinvNormSq (by decide +kernel)
    _ <= 8 := by decide +kernel

private theorem one_sub_one_sub (x : QComplex) :
    QComplex.sub QComplex.one (QComplex.sub QComplex.one x) = x := by
  cases x
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.one]
  constructor <;> grind [Rat.sub_eq_add_neg]

private theorem add_sub_cancel (x y : QComplex) :
    QComplex.add y (QComplex.sub x y) = x := by
  cases x
  cases y
  simp [QComplex.sub, QComplex.add, QComplex.neg]
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc,
    Rat.add_comm]

/-- Exact remainder formula comparing a finite geometric prefix with the
rational inverse of `1+w`. -/
theorem inverse_sub_derivativePrefix {w : QComplex}
    (hw : QComplex.normBound w <= half) (stage : Nat) :
    QComplex.sub (QComplex.inverse (QComplex.add QComplex.one w))
        (derivativePrefix w stage) =
      QComplex.mul (QComplex.inverse (QComplex.add QComplex.one w))
        (derivativeTerm w stage) := by
  let denominator := QComplex.add QComplex.one w
  let inverse := QComplex.inverse denominator
  have hright : QComplex.mul denominator inverse = QComplex.one :=
    QComplex.mul_inverse_of_normSq_ne_zero denominator
      (one_add_normSq_ne_zero hw)
  have hleft : QComplex.mul inverse denominator = QComplex.one := by
    rw [QComplex.mul_comm_cert]
    exact hright
  have hprefix := one_add_mul_derivativePrefix w stage
  change QComplex.sub inverse (derivativePrefix w stage) =
    QComplex.mul inverse (derivativeTerm w stage)
  calc
    QComplex.sub inverse (derivativePrefix w stage) =
        QComplex.sub (QComplex.mul inverse QComplex.one)
          (QComplex.mul inverse
            (QComplex.mul denominator (derivativePrefix w stage))) := by
      rw [QComplex.mul_one_cert, ← QComplex.mul_assoc_cert,
        hleft, QComplex.one_mul_cert]
    _ = QComplex.mul inverse
          (QComplex.sub QComplex.one
            (QComplex.mul denominator (derivativePrefix w stage))) :=
      (mul_sub_cert _ _ _).symm
    _ = QComplex.mul inverse (derivativeTerm w stage) := by
      rw [hprefix, one_sub_one_sub]

theorem inverse_sub_derivativePrefix_normBound_le {w : QComplex}
    (hw : QComplex.normBound w <= half) (stage : Nat) :
    QComplex.normBound
        (QComplex.sub (QComplex.inverse (QComplex.add QComplex.one w))
          (derivativePrefix w stage)) <=
      8 * half ^ stage := by
  rw [inverse_sub_derivativePrefix hw stage]
  calc
    QComplex.normBound
        (QComplex.mul (QComplex.inverse (QComplex.add QComplex.one w))
          (derivativeTerm w stage)) <=
      QComplex.normBound
          (QComplex.inverse (QComplex.add QComplex.one w)) *
        QComplex.normBound (derivativeTerm w stage) :=
      QComplex.normBound_mul_le _ _
    _ <= 8 * QComplex.normBound (derivativeTerm w stage) :=
      Rat.mul_le_mul_of_nonneg_right
        (inverse_one_add_normBound_le_eight hw)
        (QComplex.normBound_nonneg _)
    _ <= 8 * half ^ stage :=
      Rat.mul_le_mul_of_nonneg_left
        (derivativeTerm_normBound_le hw stage) (by decide +kernel)

/-- A wider proof-only radius that encloses the exact reciprocal. -/
def inverseStageRadius (stage : Nat) : Rat := 8 * half ^ stage

theorem derivativeStageRadius_le_inverseStageRadius (stage : Nat) :
    derivativeStageRadius stage <= inverseStageRadius stage := by
  rw [derivativeStageRadius_eq_two_mul_half_pow]
  unfold inverseStageRadius
  exact Rat.mul_le_mul_of_nonneg_right (by decide +kernel)
    (Rat.pow_nonneg (by decide +kernel))

theorem inverseStageRadius_shrinks : ShrinksToZero inverseStageRadius := by
  intro eps
  let start := RationalMajorant.halfDecayShift 8 eps
  refine ⟨start, ?_⟩
  intro stage hstage
  unfold inverseStageRadius
  calc
    8 * half ^ stage <= 8 * half ^ start :=
      Rat.mul_le_mul_of_nonneg_left (half_pow_antitone hstage)
        (by decide +kernel)
    _ = 8 * ((1 : Rat) / 2) ^ start := by rfl
    _ <= eps.val :=
      RationalMajorant.halfDecayShift_spec (by decide +kernel) eps

def inverseWideRawAt (w : QComplex) : ComplexRaw :=
  ComplexRaw.cauchyStabilize (derivativeDirectCandidate w)
    inverseStageRadius

private theorem derivativeDirectCandidate_future_inverseRadius
    {w : QComplex} (hw : QComplex.normBound w <= half) :
    forall first later, first <= later ->
      ((derivativeDirectCandidate w).compute later).NestedIn
        (QBox.expand ((derivativeDirectCandidate w).compute first)
          (inverseStageRadius first)) := by
  intro first later hfl
  have hnarrow := derivativeDirectCandidate_future hw first later hfl
  exact QBox.nested_trans hnarrow
    (QBox.expand_mono_radius _
      (derivativeStageRadius_le_inverseStageRadius first))

theorem inverseWideRawAt_valid {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    (inverseWideRawAt w).Valid := by
  apply ComplexRaw.cauchyStabilize_valid
  · exact derivativeDirectCandidate_ordered w
  · exact derivativeDirectCandidate_shrinks w
  · exact derivativeDirectCandidate_future_inverseRadius hw
  · exact inverseStageRadius_shrinks

theorem derivativeRawAt_equiv_inverseWideRawAt {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    (derivativeRawAt w).Equiv (inverseWideRawAt w) := by
  exact ComplexRaw.cauchyStabilize_equiv_of_common_candidate
    (derivativeDirectCandidate_ordered w)
    (derivativeDirectCandidate_future hw)
    (derivativeDirectCandidate_future_inverseRadius hw)

private theorem inverse_point_in_expanded_candidate {w : QComplex}
    (hw : QComplex.normBound w <= half) (stage : Nat) :
    (QBox.point (QComplex.inverse (QComplex.add QComplex.one w))).NestedIn
      (QBox.expand ((derivativeDirectCandidate w).compute stage)
        (inverseStageRadius stage)) := by
  have herror := inverse_sub_derivativePrefix_normBound_le hw stage
  have heq : QComplex.inverse (QComplex.add QComplex.one w) =
      QComplex.add (derivativePrefix w stage)
        (QComplex.sub (QComplex.inverse (QComplex.add QComplex.one w))
          (derivativePrefix w stage)) := by
    exact (add_sub_cancel _ _).symm
  change (QBox.point (QComplex.inverse (QComplex.add QComplex.one w))).NestedIn
    (QBox.expand (QBox.point (derivativePrefix w stage))
      (inverseStageRadius stage))
  rw [heq]
  exact ComplexExponentialApproximation.point_add_error_nested_expand _ _
    herror

theorem inverseWideRawAt_equiv_inverse {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    (inverseWideRawAt w).Equiv
      (ComplexRaw.ofQComplex
        (QComplex.inverse (QComplex.add QComplex.one w))) := by
  intro stage
  apply (ComplexRaw.compareAt_overlap_iff _ _ stage stage).2
  have hcontains := ComplexRaw.cauchyStabilize_contains_external
    (candidate := derivativeDirectCandidate w)
    (radius := inverseStageRadius)
    (external := fun _ =>
      QBox.point (QComplex.inverse (QComplex.add QComplex.one w)))
    (fun first _later _ => inverse_point_in_expanded_candidate hw first)
    stage stage (Nat.le_refl stage)
  change QBox.Overlaps ((inverseWideRawAt w).compute stage)
    (QBox.point (QComplex.inverse (QComplex.add QComplex.one w)))
  exact ⟨hcontains.1, hcontains.2⟩

/-- The independently stabilized derivative series represents the exact
rational-complex reciprocal `1/(1+w)`. -/
theorem derivativeRawAt_equiv_inverse {w : QComplex}
    (hw : QComplex.normBound w <= half) :
    (derivativeRawAt w).Equiv
      (ComplexRaw.ofQComplex
        (QComplex.inverse (QComplex.add QComplex.one w))) := by
  exact ComplexRaw.equiv_trans
    (derivativeRawAt_valid hw)
    (inverseWideRawAt_valid hw)
    (ComplexRaw.ofQComplex_valid _)
    (derivativeRawAt_equiv_inverseWideRawAt hw)
    (inverseWideRawAt_equiv_inverse hw)

/-! ## The represented logarithm first jet -/

/-- A rational input in the closed local logarithm half-ball. -/
structure HalfBallInput where
  offset : QComplex
  normBound_le : QComplex.normBound offset <= half

/-- The represented value and independently computed derivative series. -/
def representedJet (input : HalfBallInput) :
    RepresentedHolomorphicJet.FirstJet where
  value := ComplexLogarithmApproximation.logOnePlusRawAt input.offset
  derivative := derivativeRawAt input.offset

theorem representedJet_valid (input : HalfBallInput) :
    (representedJet input).Valid :=
  ⟨ComplexLogarithmApproximation.logOnePlusRawAt_valid input.normBound_le,
    derivativeRawAt_valid input.normBound_le⟩

/-- The derivative component of the represented logarithm jet is
extensionally the exact reciprocal `1/(1+w)`. -/
theorem representedJet_derivative_equiv_inverse (input : HalfBallInput) :
    (representedJet input).derivative.Equiv
      (ComplexRaw.ofQComplex
        (QComplex.inverse (QComplex.add QComplex.one input.offset))) :=
  derivativeRawAt_equiv_inverse input.normBound_le

/-- Exact finite value/derivative data at one truncation stage. -/
def finiteJetAtStage (input : HalfBallInput) (stage : Nat) :
    HolomorphicJet.FirstJet where
  value := ComplexLogarithmApproximation.logPrefix input.offset stage
  derivative := derivativePrefix input.offset stage

theorem finiteJetAtStage_value_contained
    (input : HalfBallInput) (stage : Nat) :
    (QBox.point (finiteJetAtStage input stage).value).NestedIn
      ((representedJet input).value.compute stage) := by
  exact ComplexLogarithmApproximation.logOnePlusRawAt_contains_prefix
    input.normBound_le stage

theorem finiteJetAtStage_derivative_contained
    (input : HalfBallInput) (stage : Nat) :
    (QBox.point (finiteJetAtStage input stage).derivative).NestedIn
      ((representedJet input).derivative.compute stage) := by
  exact derivativeRawAt_contains_prefix input.normBound_le stage

/-- Packaged finite power-series certificate for the local logarithm jet. -/
structure Certificate (input : HalfBallInput) : Prop where
  valid : (representedJet input).Valid
  derivativeEquivReciprocal :
    (representedJet input).derivative.Equiv
      (ComplexRaw.ofQComplex
        (QComplex.inverse (QComplex.add QComplex.one input.offset)))
  coefficientDerivative :
    FormalPowerSeries.coefficientShift
        ComplexLogarithmApproximation.logOnePlusCoefficients =
      ComplexLogarithmApproximation.reciprocalOnePlusCoefficients
  valueContained : forall stage,
    (QBox.point (finiteJetAtStage input stage).value).NestedIn
      ((representedJet input).value.compute stage)
  derivativeContained : forall stage,
    (QBox.point (finiteJetAtStage input stage).derivative).NestedIn
      ((representedJet input).derivative.compute stage)
  valueTailShrinks :
    ShrinksToZero ComplexLogarithmApproximation.stageRadius
  derivativeTailShrinks : ShrinksToZero derivativeStageRadius

theorem certificate (input : HalfBallInput) : Certificate input where
  valid := representedJet_valid input
  derivativeEquivReciprocal :=
    representedJet_derivative_equiv_inverse input
  coefficientDerivative :=
    ComplexLogarithmApproximation.coefficientShift_logOnePlusCoefficients
  valueContained := finiteJetAtStage_value_contained input
  derivativeContained := finiteJetAtStage_derivative_contained input
  valueTailShrinks := ComplexLogarithmApproximation.stageRadius_shrinks
  derivativeTailShrinks := derivativeStageRadius_shrinks

end ComplexLogarithmJet
end ComputableAnalysis
