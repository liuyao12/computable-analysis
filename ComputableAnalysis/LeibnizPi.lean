import ComputableAnalysis.AlternatingRemainder
import ComputableAnalysis.PiProofs

/-!
# Leibniz's computation of geometric π

`piCircleArea` is the existing geometric π (four times geometric arctangent
at one). The series below is an alternative interval computation, not a new
canonical constant. `N` in `leibnizPartial N` is inclusive.
-/
namespace ComputableAnalysis

/-- `4 ∑ k=0..N, (-1)^k/(2k+1)`, evaluated with rational recursion. -/
def leibnizPartial (N : Nat) : Rat :=
  4 * Series.partialSum Series.leibnizTerm (N+1)

/-- Identification with the existing exact term-integrated polynomial. -/
theorem leibnizPartial_eq_integratedPolynomial (N : Nat) :
    leibnizPartial N = 4*Taylor.ArctanKernel.kernelPartialIntegralAtOne N := by
  rw [Taylor.ArctanKernel.kernelPartialIntegralAtOne_eq_series_partialSum]
  rfl

theorem leibnizPartial_zero : leibnizPartial 0 = 4 := by
  rw [leibnizPartial_eq_integratedPolynomial]
  change (4:Rat)*1=4
  exact Rat.mul_one _

theorem leibnizPartial_succ (N : Nat) :
    leibnizPartial (N+1) = leibnizPartial N +
      4*((-1:Rat)^(N+1)/(2*((N+1:Nat):Rat)+1)) := by
  rw [leibnizPartial_eq_integratedPolynomial,
    leibnizPartial_eq_integratedPolynomial,
    Taylor.ArctanKernel.kernelPartialIntegralAtOne]
  unfold Taylor.ArctanKernel.kernelTermIntegralAtOne
  grind

/-- First omitted term in the inclusive Leibniz sum. -/
def leibnizRadius (N : Nat) : Rat := 4/(2*(N:Rat)+3)

/-- The reusable alternating-interval evaluator, scaled by four. -/
def leibnizRaw : RealRaw :=
  (4:Nat) * Series.AlternatingRaw.leibnizAlternatingRaw.toRealRaw

theorem leibnizRaw_valid : leibnizRaw.Valid :=
  RealRaw.natScale_valid 4 Series.AlternatingRaw.leibnizAlternatingRaw_valid

/-- Exact correspondence with the repository's older fold-based evaluator. -/
theorem leibnizRaw_compute_eq_piLeibniz (n : Nat) :
    leibnizRaw.compute n = piLeibniz.compute n := by
  have h : Series.AlternatingRaw.leibnizAlternatingRaw.toRealRaw.compute n =
      leibnizSeries.compute n := by
    rw [PiProofs.LeibnizValidity.leibnizSeries_compute_eq_kernelPartialIntegralInterval]
    change Series.AlternatingRaw.leibnizAlternatingRaw.interval n = _
    rw [Series.AlternatingRaw.interval_eq_endpoints]
    cases n with
    | zero =>
        have hone : Series.partialSum Series.leibnizTerm 1 = 1 :=
          (Taylor.ArctanKernel.kernelPartialIntegralAtOne_eq_series_partialSum 0).symm
        change ({lo := 0, hi := Series.partialSum Series.leibnizTerm 1} : QInterval) =
          {lo := 0, hi := 1}
        rw [hone]
    | succ n =>
        simp only [PiProofs.LeibnizValidity.lowerKernelPartialAtStage,
          PiProofs.LeibnizValidity.upperKernelPartialAtStage,
          Taylor.ArctanKernel.kernelPartialIntegralAtOne_eq_series_partialSum,
          Series.AlternatingRaw.leibnizAlternatingRaw]
        congr 1 <;> congr 1 <;> omega
  change ({lo := 4*_, hi := 4*_} : QInterval) = {lo := 4*_, hi := 4*_}
  rw [h]

/-- Explicit rational convergence budget for the literal evaluator. -/
theorem leibnizRaw_width_le (n : Nat) (hn : 0 < n) :
    (leibnizRaw.compute n).width ≤ 4/(n:Rat) := by
  rw [leibnizRaw_compute_eq_piLeibniz]
  exact PiProofs.piLeibniz_compute_width_le_four_div n hn

/-- The computational route uses the existing finite mesh invariant and
vanishing rational mesh error, without derivative or FTC certificates. -/
theorem leibnizRaw_equiv_geom : leibnizRaw.Equiv piCircleArea := by
  have hunit := RealRaw.equiv_trans PiProofs.leibnizSeriesValid
    (ArctanGeometry.arctanIntegralRectangleRaw_valid (x := (1:Rat))
      (by decide) (by decide)) ArctanGeometry.arctanGeom_one_valid
    PiProofs.leibnizEqualsRectangleRawAtOne_finiteRiemannBridge
    (ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom (by decide))
  have h := RealRaw.natScale_equiv 4 hunit
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  rw [leibnizRaw_compute_eq_piLeibniz,
    ← ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  exact (RealRaw.compareAt_overlap_iff _ _ n n).1 (h n)

/-- A literal evaluator box is inside the classical remainder enclosure
as soon as it includes the requested prefix. -/
theorem leibnizRaw_compute_remainder (N m : Nat) (hm : N+1 ≤ 2*m) :
    leibnizPartial N - leibnizRadius N ≤ (leibnizRaw.compute m).lo ∧
    (leibnizRaw.compute m).hi ≤ leibnizPartial N + leibnizRadius N := by
  have h := Series.AlternatingRaw.leibnizAlternatingRaw.interval_remainder (N+1) m hm
  have ht : 4*Series.leibnizTerm (N+1) = leibnizRadius N := by
    simp only [Series.leibnizTerm, leibnizRadius, Rat.natCast_add]
    grind [Rat.div_def]
  have hl := Rat.mul_le_mul_of_nonneg_left h.1 (show (0:Rat) ≤ 4 by decide)
  have hu := Rat.mul_le_mul_of_nonneg_left h.2 (show (0:Rat) ≤ 4 by decide)
  change leibnizPartial N - leibnizRadius N ≤
    4*(Series.AlternatingRaw.leibnizAlternatingRaw.interval m).lo ∧
    4*(Series.AlternatingRaw.leibnizAlternatingRaw.interval m).hi ≤
    leibnizPartial N + leibnizRadius N
  dsimp [leibnizPartial, Series.AlternatingRaw.leibnizAlternatingRaw] at hl hu ht ⊢
  constructor <;> grind

/-- All-stage geometric overlap with the inclusive partial sum and its
first-omitted-term radius. The geometric stage and series index are independent. -/
theorem leibniz_geom_remainder_of_equiv
    (hgeom : leibnizRaw.Equiv piCircleArea) (N stage : Nat) :
    (piCircleArea.compute stage).lo ≤ leibnizPartial N + leibnizRadius N ∧
    leibnizPartial N - leibnizRadius N ≤ (piCircleArea.compute stage).hi := by
  have h := RealRaw.allStagesOverlap_of_equiv leibnizRaw_valid
    (show piCircleArea.Valid from PiProofs.AreaLoopValidity.areaValid)
    hgeom (N+1) stage
  have ho := (RealRaw.compareAt_overlap_iff _ _ (N+1) stage).1 h
  have hr := leibnizRaw_compute_remainder N (N+1) (by omega)
  exact ⟨Rat.le_trans ho.2 hr.2, Rat.le_trans hr.1 ho.1⟩

theorem leibniz_geom_remainder (N stage : Nat) :
    (piCircleArea.compute stage).lo ≤ leibnizPartial N + leibnizRadius N ∧
    leibnizPartial N - leibnizRadius N ≤ (piCircleArea.compute stage).hi :=
  leibniz_geom_remainder_of_equiv leibnizRaw_equiv_geom N stage

/-- The classical absolute remainder bound, in exact raw-order form. -/
theorem pi_leibniz_remainder (N : Nat) :
    (RealRaw.ofRat (leibnizPartial N - leibnizRadius N)).Le piCircleArea ∧
    piCircleArea.Le (RealRaw.ofRat (leibnizPartial N + leibnizRadius N)) := by
  exact ⟨fun _ stage => (leibniz_geom_remainder N stage).2,
    fun stage _ => (leibniz_geom_remainder N stage).1⟩

/-- The requested computational invariant at every stage. -/
theorem leibniz_stagewise_overlap (N : Nat) :
    (piCircleArea.compute N).lo ≤ leibnizPartial N + 4/(2*(N:Rat)+3) ∧
    leibnizPartial N - 4/(2*(N:Rat)+3) ≤ (piCircleArea.compute N).hi :=
  leibniz_geom_remainder N N

/-- Geometric π equals the Leibniz alternating series. -/
theorem pi_eq_leibniz : piCircleArea.Equiv leibnizRaw :=
  RealRaw.equiv_symm leibnizRaw_equiv_geom

end ComputableAnalysis
