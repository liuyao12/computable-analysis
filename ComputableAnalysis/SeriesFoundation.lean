import ComputableAnalysis.PowerSeries
import ComputableAnalysis.Series
import ComputableAnalysis.FirstYearCalculus
import ComputableAnalysis.FiniteTaylorFTCInterface
import ComputableAnalysis.FinitePolynomialCalculus
import ComputableAnalysis.FiniteSineIntegral
import ComputableAnalysis.FiniteFourierFoundation
import ComputableAnalysis.FiniteFourierOrthogonality
import ComputableAnalysis.FiniteFourierEnergy
import ComputableAnalysis.EffectiveFourierSeries
import ComputableAnalysis.EffectiveFourierTail
import ComputableAnalysis.FiniteNBallVolume
import ComputableAnalysis.FiniteGaussianIntegral

/-!
# Finite series and Fourier foundation

This scoped entry point collects the rational coefficient, finite-prefix,
Fourier-tail, Gaussian-prefix, and finite ball-volume interfaces.  It exposes
computable series certificates without importing the full benchmark catalogue
or introducing a completed function space.
-/

namespace ComputableAnalysis

/-! A series certificate packages exactly the data needed to turn rational
    partial sums into a valid `realRaw`: a nonnegative tail bound, a one-step
    refinement inequality, and an explicit tail budget.  The partial sums
    need not have a named convergence rate. -/
structure RationalSeriesCertificate where
  partialSum : Nat -> Rat
  remainder : Nat -> Rat
  remainder_nonneg : forall n, 0 <= remainder n
  refinement : forall n,
    qabs (partialSum (n + 1) - partialSum n) + remainder (n + 1) <= remainder n
  tail_budget : RealRaw.WidthsShrinkToZero (fun n =>
    ({ lo := 0, hi := remainder n } : QInterval))

def RationalSeriesCertificate.raw (S : RationalSeriesCertificate) : RealRaw where
  compute := fun n =>
    { lo := S.partialSum n - S.remainder n
      hi := S.partialSum n + S.remainder n }

theorem RationalSeriesCertificate.raw_valid
    (S : RationalSeriesCertificate) : S.raw.Valid := by
  unfold RealRaw.Valid RealRaw.ValidCompute RationalSeriesCertificate.raw
  constructor
  · intro n
    simp [QInterval.width, RationalSeriesCertificate.raw]
    grind [S.remainder_nonneg n]
  constructor
  · intro n m hnm
    have hstep : forall j,
        S.partialSum j - S.remainder j <=
            S.partialSum (j + 1) - S.remainder (j + 1) ∧
        S.partialSum (j + 1) + S.remainder (j + 1) <=
            S.partialSum j + S.remainder j := by
      intro j
      have href := S.refinement j
      have hleft := neg_qabs_le_self (S.partialSum (j + 1) - S.partialSum j)
      have hright := self_le_qabs (S.partialSum (j + 1) - S.partialSum j)
      constructor <;> grind [Rat.sub_eq_add_neg]
    induction m generalizing n with
    | zero =>
        have hn : n = 0 := by omega
        subst n
        simp [QInterval.width]
        grind [S.remainder_nonneg 0]
    | succ m ih =>
        by_cases hnm' : n <= m
        · have hprev := ih n hnm'
          have hs := hstep m
          exact ⟨Rat.le_trans hprev.1 hs.1,
            (by
              have hnonneg := S.remainder_nonneg (m + 1)
              grind),
            Rat.le_trans hs.2 hprev.2.2⟩
        · have hn : n = m + 1 := by omega
          subst n
          have hnonneg := S.remainder_nonneg (m + 1)
          dsimp
          grind
  · intro eps
    let half : QPos := ⟨eps.val / 2, by grind [eps.property]⟩
    obtain ⟨N, hN⟩ := S.tail_budget half
    refine ⟨N, ?_⟩
    intro n hn
    have htail := hN n hn
    have htail' : S.remainder n <= half.val := by
      dsimp [QInterval.width] at htail
      grind
    simp only [QInterval.width, RationalSeriesCertificate.raw]
    calc
      S.partialSum n + S.remainder n -
          (S.partialSum n - S.remainder n) <= 2 * half.val := by
        grind
      _ = eps.val := by
        dsimp [half]
        have htwo : (2 : Rat) ≠ 0 := by native_decide
        grind [Rat.mul_assoc, Rat.mul_comm,
          Rat.inv_mul_cancel (2 : Rat) htwo]

theorem RationalSeriesCertificate.raw_compute_interval
    (S : RationalSeriesCertificate) (n : Nat) :
    (S.raw.compute n).lo = S.partialSum n - S.remainder n ∧
    (S.raw.compute n).hi = S.partialSum n + S.remainder n := by
  simp [RationalSeriesCertificate.raw]

theorem RationalSeriesCertificate.raw_width
    (S : RationalSeriesCertificate) (n : Nat) :
    (S.raw.compute n).width = 2 * S.remainder n := by
  simp [RationalSeriesCertificate.raw, QInterval.width]
  grind [Rat.sub_eq_add_neg]

theorem RationalSeriesCertificate.raw_precision_witness
    (S : RationalSeriesCertificate) (eps : QPos) :
    ∃ N : Nat, ∀ n, N ≤ n ->
      (S.raw.compute n).width ≤ eps.val := by
  exact (S.raw_valid).2.2 eps

/-! Certificate addition is the basic termwise-series closure.  The tail
    budgets are split between the two summands, while the rational triangle
    inequality proves the one-step refinement. -/
def RationalSeriesCertificate.add
    (S T : RationalSeriesCertificate) : RationalSeriesCertificate where
  partialSum := fun n => S.partialSum n + T.partialSum n
  remainder := fun n => S.remainder n + T.remainder n
  remainder_nonneg := by
    intro n
    exact Rat.add_nonneg (S.remainder_nonneg n) (T.remainder_nonneg n)
  refinement := by
    intro n
    have hs := S.refinement n
    have ht := T.refinement n
    have hdiff :
        (S.partialSum (n + 1) + T.partialSum (n + 1)) -
            (S.partialSum n + T.partialSum n) =
          (S.partialSum (n + 1) - S.partialSum n) +
            (T.partialSum (n + 1) - T.partialSum n) := by
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
        Rat.add_left_comm]
    rw [hdiff]
    calc
      qabs (S.partialSum (n + 1) - S.partialSum n +
          (T.partialSum (n + 1) - T.partialSum n)) +
          (S.remainder (n + 1) + T.remainder (n + 1)) <=
        qabs (S.partialSum (n + 1) - S.partialSum n) +
          qabs (T.partialSum (n + 1) - T.partialSum n) +
            (S.remainder (n + 1) + T.remainder (n + 1)) := by
        exact (Rat.add_le_add_right
          (c := S.remainder (n + 1) + T.remainder (n + 1))).2
          (qabs_add_le _ _)
      _ <= S.remainder n + T.remainder n := by
        grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
  tail_budget := by
    intro eps
    let half : QPos := ⟨eps.val / 2, by grind [eps.property]⟩
    obtain ⟨NS, hS⟩ := S.tail_budget half
    obtain ⟨NT, hT⟩ := T.tail_budget half
    refine ⟨max NS NT, ?_⟩
    intro n hn
    have hNS : NS ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hNT : NT ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    have hs := hS n hNS
    have ht := hT n hNT
    simp only [QInterval.width] at hs ht ⊢
    grind

theorem RationalSeriesCertificate.add_raw_valid
    (S T : RationalSeriesCertificate) :
    (S.add T).raw.Valid := by
  exact (S.add T).raw_valid

theorem RationalSeriesCertificate.add_raw_precision_witness
    (S T : RationalSeriesCertificate) (eps : QPos) :
    ∃ N : Nat, ∀ n, N ≤ n ->
      ((S.add T).raw.compute n).width ≤ eps.val := by
  exact (S.add T).raw_precision_witness eps

/-! The geometric prefix is the first concrete client of the generic
    certificate.  Its remainder is written as a rational gap to the closed
    endpoint formula; the generic constructor then supplies the symmetric
    interval representation. -/
def geometricSeriesCertificate
    {r : Rat} (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) : RationalSeriesCertificate where
  partialSum := Series.geometricSum r
  remainder := fun n => 1 / (1 - r) - Series.geometricSum r n
  remainder_nonneg := by
    intro n
    have hsum := Series.geometricSum_le_inv_one_sub hr0 hr1 n
    grind
  refinement := by
    intro n
    rw [Series.geometricSum_succ]
    have hpow : 0 <= r ^ n := Rat.pow_nonneg hr0
    have hcancel : Series.geometricSum r n + r ^ n -
        Series.geometricSum r n = r ^ n := by grind
    rw [hcancel, qabs_eq_self_of_nonneg hpow]
    have hden : 0 < 1 - r := by grind
    grind [Rat.div_def, Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
      Rat.mul_assoc, Rat.mul_comm]
  tail_budget := by
    intro eps
    obtain ⟨N, hN⟩ :=
      (Series.geometricRaw_valid_of_le_half hr0 hrhalf hr1).2.2 eps
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN n hn
    have h' : 1 / (1 - r) - Series.geometricSum r n <= eps.val := by
      simpa [Series.geometricRaw, QInterval.width,
        Rat.sub_eq_add_neg, Rat.add_comm, Rat.add_left_comm, Rat.add_assoc] using h
    simp only [QInterval.width]
    grind

theorem geometricSeriesCertificate_raw_equiv_geometricRaw
    {r : Rat} (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) :
    (geometricSeriesCertificate hr0 hrhalf hr1).raw.Equiv
      (Series.geometricRaw r hr0 hr1) := by
  intro n
  have hsum := Series.geometricSum_le_inv_one_sub hr0 hr1 n
  apply (RealRaw.compareAt_overlap_iff
    (geometricSeriesCertificate hr0 hrhalf hr1).raw
    (Series.geometricRaw r hr0 hr1) n n).2
  simp only [RationalSeriesCertificate.raw, geometricSeriesCertificate,
    Series.geometricRaw]
  constructor
  · change Series.geometricSum r n -
      (1 / (1 - r) - Series.geometricSum r n) <=
        1 / (1 - r)
    grind
  · change Series.geometricSum r n <=
      Series.geometricSum r n +
        (1 / (1 - r) - Series.geometricSum r n)
    grind

/-! The alternating-series interval is another concrete client.  We retain
    the even partial sum as the center and the next term as a symmetric
    rational radius; the decrease proof supplies the nesting inequality. -/
def alternatingSeriesCertificate (S : Series.AlternatingRaw) :
    RationalSeriesCertificate where
  partialSum := fun n => Series.partialSum S.term (2 * n)
  remainder := fun n => S.term (2 * n)
  remainder_nonneg := by
    intro n
    exact S.term_nonneg _
  refinement := by
    intro n
    have hstep := Series.partialSum_even_step S.term n
    have hdec₁ := S.term_decreasing (2 * n)
    have hdec₂ := S.term_decreasing (2 * n + 1)
    have hdiff :
        Series.partialSum S.term (2 * (n + 1)) -
            Series.partialSum S.term (2 * n) =
          S.term (2 * n) - S.term (2 * n + 1) := by
      rw [hstep]
      grind [Rat.sub_eq_add_neg]
    have hnonneg : 0 <= S.term (2 * n) - S.term (2 * n + 1) := by
      grind
    rw [hdiff, qabs_eq_self_of_nonneg hnonneg]
    grind
  tail_budget := by
    intro eps
    obtain ⟨N, hN⟩ := S.term_shrinks eps
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN (2 * n) (by omega)
    simp only [QInterval.width] at h ⊢
    grind

theorem alternatingSeriesCertificate_raw_precision_witness
    (S : Series.AlternatingRaw) (eps : QPos) :
    ∃ N : Nat, ∀ n, N ≤ n ->
      ((alternatingSeriesCertificate S).raw.compute n).width ≤ eps.val := by
  exact (alternatingSeriesCertificate S).raw_precision_witness eps

theorem alternatingSeriesCertificate_raw_equiv_alternatingRaw
    (S : Series.AlternatingRaw) :
    (alternatingSeriesCertificate S).raw.Equiv S.toRealRaw := by
  intro n
  have hinterval := Series.AlternatingRaw.interval_eq_endpoints S n
  apply (RealRaw.compareAt_overlap_iff
    (alternatingSeriesCertificate S).raw S.toRealRaw n n).2
  have hcompute : S.toRealRaw.compute n = S.interval n := rfl
  rw [hcompute, hinterval]
  simp only [RationalSeriesCertificate.raw, alternatingSeriesCertificate,
    Series.AlternatingRaw.toRealRaw]
  constructor
  · have hnonneg := S.term_nonneg (2 * n)
    have hle : Series.partialSum S.term (2 * n) <=
        Series.partialSum S.term (2 * n + 1) := by
      rw [Series.partialSum_even_succ]
      grind
    grind
  · have hnonneg := S.term_nonneg (2 * n)
    grind

/-! The named Leibniz client keeps the π construction discoverable from the
    generic interface. -/
def leibnizSeriesCertificate : RationalSeriesCertificate :=
  alternatingSeriesCertificate Series.AlternatingRaw.leibnizAlternatingRaw

theorem leibnizSeriesCertificate_raw_equiv_leibnizAlternatingRaw :
    leibnizSeriesCertificate.raw.Equiv
      Series.AlternatingRaw.leibnizAlternatingRaw.toRealRaw := by
  exact alternatingSeriesCertificate_raw_equiv_alternatingRaw
    Series.AlternatingRaw.leibnizAlternatingRaw

theorem leibnizSeriesCertificate_raw_width (n : Nat) :
    (leibnizSeriesCertificate.raw.compute n).width =
      2 / ((4 * n + 1 : Nat) : Rat) := by
  rw [leibnizSeriesCertificate, RationalSeriesCertificate.raw_width]
  simp [alternatingSeriesCertificate,
    Series.AlternatingRaw.leibnizAlternatingRaw, Series.leibnizTerm]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc,
    Rat.add_comm, Rat.add_left_comm]

theorem leibnizSeriesCertificate_raw_precision_witness (eps : QPos) :
    ∃ N : Nat, ∀ n, N ≤ n ->
      (leibnizSeriesCertificate.raw.compute n).width ≤ eps.val := by
  exact leibnizSeriesCertificate.raw_precision_witness eps

/-! The same adapter names the rational sine Taylor computation.  Its tail
    radius is the factorial majorant already used by the sine chapter. -/
def sineSeriesCertificate (x : Rat) (hx : qabs x <= 2) :
    RationalSeriesCertificate :=
  alternatingSeriesCertificate (Series.AlternatingRaw.sineAlternatingRaw x hx)

theorem sineSeriesCertificate_raw_equiv_sineAlternatingRaw
    (x : Rat) (hx : qabs x <= 2) :
    (sineSeriesCertificate x hx).raw.Equiv
      (Series.AlternatingRaw.sineAlternatingRaw x hx).toRealRaw := by
  exact alternatingSeriesCertificate_raw_equiv_alternatingRaw _

theorem sineSeriesCertificate_raw_width
    (x : Rat) (hx : qabs x <= 2) (n : Nat) :
    ((sineSeriesCertificate x hx).raw.compute n).width =
      2 * RationalMajorant.factorialTailTerm (qabs x) (4 * n + 1) := by
  rw [sineSeriesCertificate, RationalSeriesCertificate.raw_width]
  simp [alternatingSeriesCertificate,
    Series.AlternatingRaw.sineAlternatingRaw,
    Series.sineTermMagnitude_eq_factorialTailTerm]
  congr 1
  grind

/-! The same certificate pattern for complex-valued series.  The refinement
    field is rectangular-box nesting, since a complex remainder has separate
    real and imaginary budgets. -/
structure ComplexSeriesCertificate where
  partialSum : Nat -> QComplex
  remainder : Nat -> Rat
  remainder_nonneg : forall n, 0 <= remainder n
  refinement : forall n,
    (QBox.expand (QBox.point (partialSum (n + 1))) (remainder (n + 1))).NestedIn
      (QBox.expand (QBox.point (partialSum n)) (remainder n))
  tail_budget : RealRaw.WidthsShrinkToZero (fun n =>
    ({ lo := 0, hi := remainder n } : QInterval))

def ComplexSeriesCertificate.raw (S : ComplexSeriesCertificate) : ComplexRaw where
  compute := fun n => QBox.expand (QBox.point (S.partialSum n)) (S.remainder n)

theorem ComplexSeriesCertificate.raw_valid
    (S : ComplexSeriesCertificate) : S.raw.Valid := by
  unfold ComplexRaw.Valid ComplexRaw.ValidCompute ComplexSeriesCertificate.raw
  constructor
  · intro n
    simp [QBox.expand, QBox.point, QBox.width, QBox.height]
    exact ⟨by grind [S.remainder_nonneg n], by grind [S.remainder_nonneg n]⟩
  constructor
  · intro n m hnm
    induction m generalizing n with
    | zero =>
        have hn : n = 0 := by omega
        subst n
        simp
    | succ m ih =>
        by_cases hnm' : n <= m
        · have hprev := ih n hnm'
          have hs := S.refinement m
          simp [QBox.NestedIn, QBox.expand, QBox.point, QComplex.le_def] at hs
          exact ⟨Rat.le_trans hprev.1 hs.1.1,
            Rat.le_trans hs.2.1 hprev.2.1,
            Rat.le_trans hprev.2.2.1 hs.1.2,
            Rat.le_trans hs.2.2 hprev.2.2.2⟩
        · have hn : n = m + 1 := by omega
          subst n
          simp
  · intro eps
    let half : QPos := ⟨eps.val / 2, by grind [eps.property]⟩
    obtain ⟨N, hN⟩ := S.tail_budget half
    refine ⟨N, ?_⟩
    intro n hn
    have htail := hN n hn
    dsimp [QInterval.width] at htail
    have htail' : S.remainder n <= half.val := by grind
    simp [QBox.expand, QBox.point, QBox.width, QBox.height]
    constructor <;> calc
      _ <= 2 * half.val := by grind
      _ = eps.val := by
        dsimp [half]
        have htwo : (2 : Rat) ≠ 0 := by native_decide
        grind [Rat.mul_assoc, Rat.mul_comm,
          Rat.inv_mul_cancel (2 : Rat) htwo]

theorem ComplexSeriesCertificate.raw_compute_box
    (S : ComplexSeriesCertificate) (n : Nat) :
    S.raw.compute n =
      QBox.expand (QBox.point (S.partialSum n)) (S.remainder n) := by
  rfl

theorem ComplexSeriesCertificate.raw_width
    (S : ComplexSeriesCertificate) (n : Nat) :
    (S.raw.compute n).width = 2 * S.remainder n := by
  simp [ComplexSeriesCertificate.raw, QBox.expand, QBox.point, QBox.width]
  grind [Rat.sub_eq_add_neg]

theorem ComplexSeriesCertificate.raw_height
    (S : ComplexSeriesCertificate) (n : Nat) :
    (S.raw.compute n).height = 2 * S.remainder n := by
  simp [ComplexSeriesCertificate.raw, QBox.expand, QBox.point, QBox.height]
  grind [Rat.sub_eq_add_neg]

theorem ComplexSeriesCertificate.raw_precision_witness
    (S : ComplexSeriesCertificate) (eps : QPos) :
    ∃ N : Nat, ∀ n, N ≤ n ->
      (S.raw.compute n).width ≤ eps.val ∧
        (S.raw.compute n).height ≤ eps.val := by
  exact (S.raw_valid).2.2 eps

/-! A finite complex coefficient prefix has the same termwise primitive
constructor as the rational polynomial layer.  The coefficient stream and
the evaluation point are rational-complex, while division by the natural
index remains a rational scalar operation. -/
def complexFinitePrimitiveTerm
    (coefficients : Nat -> QComplex) (z : QComplex) (k : Nat) : QComplex :=
  QComplex.scaleRat (1 / (((k + 1 : Nat) : Rat)))
    (QComplex.mul (coefficients k) (QComplex.pow z (k + 1)))

def complexFinitePrimitivePrefix
    (coefficients : Nat -> QComplex) (z : QComplex) (terms : Nat) : QComplex :=
  (List.range terms).foldl
    (fun acc k => QComplex.add acc
      (complexFinitePrimitiveTerm coefficients z k)) QComplex.zero

def complexPrimitiveCoefficients (coefficients : Nat -> QComplex) : Nat -> QComplex
  | 0 => QComplex.zero
  | k + 1 =>
      QComplex.scaleRat (1 / (((k + 1 : Nat) : Rat))) (coefficients k)

def complexCoefficientDerivative (coefficients : Nat -> QComplex) : Nat -> QComplex :=
  fun k => QComplex.scaleRat (((k + 1 : Nat) : Rat)) (coefficients (k + 1))

private theorem qcomplex_scaleRat_nat_inv (k : Nat) (z : QComplex) :
    QComplex.scaleRat (((k + 1 : Nat) : Rat))
        (QComplex.scaleRat (1 / (((k + 1 : Nat) : Rat))) z) = z := by
  rw [QComplex.scaleRat_scaleRat]
  have hk : (((k + 1 : Nat) : Rat)) ≠ 0 := by
    exact FormalPowerSeries.natCast_succ_ne_zero k
  have hcancel :
      (((k + 1 : Nat) : Rat)) * (1 / (((k + 1 : Nat) : Rat))) = 1 := by
    rw [Rat.div_def]
    simp only [Rat.one_mul]
    rw [Rat.mul_comm]
    exact Rat.inv_mul_cancel _ hk
  rw [hcancel]
  cases z <;> simp [QComplex.scaleRat]

theorem complexCoefficientDerivative_primitiveCoefficients
    (coefficients : Nat -> QComplex) :
    complexCoefficientDerivative (complexPrimitiveCoefficients coefficients) =
      coefficients := by
  funext k
  cases k with
  | zero =>
      simpa [complexCoefficientDerivative, complexPrimitiveCoefficients] using
        qcomplex_scaleRat_nat_inv 0 (coefficients 0)
  | succ k =>
      simpa [complexCoefficientDerivative, complexPrimitiveCoefficients,
        Rat.natCast_add] using
        qcomplex_scaleRat_nat_inv (k + 1) (coefficients (k + 1))

theorem complexFinitePrimitivePrefix_succ
    (coefficients : Nat -> QComplex) (z : QComplex) (terms : Nat) :
    complexFinitePrimitivePrefix coefficients z (terms + 1) =
      QComplex.add
        (complexFinitePrimitivePrefix coefficients z terms)
        (complexFinitePrimitiveTerm coefficients z terms) := by
  simp [complexFinitePrimitivePrefix, List.range_succ, List.foldl_append]

private theorem qcomplex_sub_add_sub (a b c d : QComplex) :
    QComplex.sub (QComplex.add a b) (QComplex.add c d) =
      QComplex.add (QComplex.sub a c) (QComplex.sub b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero] <;>
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem qcomplex_scale_mul_sub (r : Rat) (c z w : QComplex) :
    QComplex.sub (QComplex.scaleRat r (QComplex.mul c z))
        (QComplex.scaleRat r (QComplex.mul c w)) =
      QComplex.scaleRat r (QComplex.mul c (QComplex.sub z w)) := by
  cases r <;> cases c <;> cases z <;> cases w <;>
    simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.scaleRat,
      QComplex.mul] <;>
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.add_left_comm]

theorem complexFinitePrimitivePrefix_endpointDifference
    (coefficients : Nat -> QComplex) (z w : QComplex) (terms : Nat) :
    QComplex.sub
        (complexFinitePrimitivePrefix coefficients z terms)
        (complexFinitePrimitivePrefix coefficients w terms) =
      (List.range terms).foldl
        (fun acc k => QComplex.add acc
          (QComplex.scaleRat (1 / (((k + 1 : Nat) : Rat)))
            (QComplex.mul (coefficients k)
              (QComplex.sub (QComplex.pow z (k + 1))
                (QComplex.pow w (k + 1)))))) QComplex.zero := by
  induction terms with
  | zero =>
      simp [complexFinitePrimitivePrefix, QComplex.sub, QComplex.add,
        QComplex.neg, QComplex.zero, Rat.zero_add, Rat.add_zero]
  | succ terms ih =>
      rw [complexFinitePrimitivePrefix_succ, complexFinitePrimitivePrefix_succ]
      rw [qcomplex_sub_add_sub]
      rw [ih]
      have hterm :
          QComplex.sub (complexFinitePrimitiveTerm coefficients z terms)
              (complexFinitePrimitiveTerm coefficients w terms) =
            QComplex.scaleRat (1 / (((terms + 1 : Nat) : Rat)))
              (QComplex.mul (coefficients terms)
                (QComplex.sub (QComplex.pow z (terms + 1))
                  (QComplex.pow w (terms + 1)))) := by
        unfold complexFinitePrimitiveTerm
        exact qcomplex_scale_mul_sub _ _ _ _
      rw [hterm]
      simp [List.range_succ, List.foldl_append]

/-! Project-facing names for the finite termwise-FTC bridge.  These are exact
rational identities for finite prefixes; convergence and tail transport are
separate certificates. -/
theorem effectiveFiniteTaylorFTC_prefix
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    FinitePolynomial.integratedTaylorPrefix coeffs terms b -
        FinitePolynomial.integratedTaylorPrefix coeffs terms a =
      (List.range terms).foldl
        (fun acc k => acc + coeffs k *
          (b ^ (k + 1) / ((k + 1 : Nat) : Rat) -
            a ^ (k + 1) / ((k + 1 : Nat) : Rat))) 0 := by
  exact FinitePolynomial.finiteTaylorFTC_prefix coeffs terms a b

/-! The complex exponential and trigonometric primitive laws are exported
alongside the finite Taylor law.  They concern only rational-complex prefixes
and therefore do not invoke a completed complex function space. -/
theorem effectiveExpIntegratedPartial_eq_expPartial_sub_one
    (z : QComplex) (n : Nat) :
    ComplexSeries.expIntegratedPartial z n =
      QComplex.sub (ComplexSeries.expPartial z (n + 1)) QComplex.one := by
  exact ComplexSeries.expIntegratedPartial_eq_expPartial_sub_one z n

theorem effectiveSinIntegratedPartial_eq_one_sub_cosPartial
    (z : QComplex) (n : Nat) :
    ComplexSeries.sinIntegratedPartial z n =
      QComplex.sub QComplex.one (ComplexSeries.cosPartial z (n + 1)) := by
  exact ComplexSeries.sinIntegratedPartial_eq_one_sub_cosPartial z n

theorem effectiveCosIntegratedPartial_eq_sinPartial
    (z : QComplex) (n : Nat) :
    ComplexSeries.cosIntegratedPartial z n =
      ComplexSeries.sinPartial z n := by
  exact ComplexSeries.cosIntegratedPartial_eq_sinPartial z n

end ComputableAnalysis
