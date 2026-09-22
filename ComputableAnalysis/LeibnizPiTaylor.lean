import ComputableAnalysis.LeibnizPi
import ComputableAnalysis.ArctanTaylorRemainder

/-! # The independent FTC proof of Leibniz's formula

Finite geometric division bounds the kernel between consecutive polynomials.
The quantitative monomial FTC integrates these bounds on every rational cell.
The existing geometric rectangle/exhaustion comparison then identifies π.
This route does not invoke the finite-Riemann bridge used by `pi_eq_leibniz`.
-/
namespace ComputableAnalysis

/-- The calculus proof: integrate the all-degree finite geometric bounds. -/
theorem leibnizRaw_equiv_geom_taylor : leibnizRaw.Equiv piCircleArea := by
  have h := PiProofs.leibnizEqArea_of_kernelPartialExactCellOrderPreservation
    Taylor.ArctanKernel.kernelPartial_exactCellOrder
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  rw [leibnizRaw_compute_eq_piLeibniz]
  exact (RealRaw.compareAt_overlap_iff _ _ n n).1 (h n)

/-- The same public equality, proved through polynomial FTC and integral order. -/
theorem pi_eq_leibniz_taylor : piCircleArea.Equiv leibnizRaw :=
  RealRaw.equiv_symm leibnizRaw_equiv_geom_taylor

/-- Integrated remainder after the inclusive finite arctangent polynomial.
The integral value is the existing geometric arctangent, not a series definition. -/
def arctanTaylorRemainderRaw (N : Nat) : RealRaw :=
  ArctanGeometry.arctanGeom 1 -
    RealRaw.ofRat (Taylor.ArctanKernel.kernelPartialIntegralAtOne N)

theorem arctanTaylorRemainderRaw_valid (N : Nat) :
    (arctanTaylorRemainderRaw N).Valid :=
  RealRaw.sub_valid (ArctanGeometry.arctanGeom_valid_on_unit
    (by decide) (by decide)) (RealRaw.ofRat_valid _)

/-- `A(1) = sum_{k=0}^N (-1)^k/(2k+1) + R_N`. -/
theorem arctan_taylor_integrated (N : Nat) :
    (ArctanGeometry.arctanGeom 1).Equiv
      (RealRaw.ofRat (Taylor.ArctanKernel.kernelPartialIntegralAtOne N) +
        arctanTaylorRemainderRaw N) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have h := RealRaw.interval_order_of_valid (ArctanGeometry.arctanGeom 1)
    (ArctanGeometry.arctanGeom_valid_on_unit (by decide) (by decide)) n
  change ((ArctanGeometry.arctanGeom 1).compute n).lo ≤
      Taylor.ArctanKernel.kernelPartialIntegralAtOne N +
        (((ArctanGeometry.arctanGeom 1).compute n).hi -
          Taylor.ArctanKernel.kernelPartialIntegralAtOne N) ∧
    Taylor.ArctanKernel.kernelPartialIntegralAtOne N +
      (((ArctanGeometry.arctanGeom 1).compute n).lo -
        Taylor.ArctanKernel.kernelPartialIntegralAtOne N) ≤
      ((ArctanGeometry.arctanGeom 1).compute n).hi
  constructor <;> grind

/-- `|R_N| ≤ 1/(2N+3)`, expressed by the foundation's exact raw order. -/
theorem arctan_taylor_remainder_bound (N : Nat) :
    (RealRaw.ofRat (-(1/(2*(N:Rat)+3)))).Le (arctanTaylorRemainderRaw N) ∧
    (arctanTaylorRemainderRaw N).Le (RealRaw.ofRat (1/(2*(N:Rat)+3))) := by
  have hb : ∀ stage,
      ((ArctanGeometry.arctanGeom 1).compute stage).lo ≤
        Taylor.ArctanKernel.kernelPartialIntegralAtOne N + 1/(2*(N:Rat)+3) ∧
      Taylor.ArctanKernel.kernelPartialIntegralAtOne N - 1/(2*(N:Rat)+3) ≤
        ((ArctanGeometry.arctanGeom 1).compute stage).hi := by
    intro stage
    have h := leibniz_geom_remainder_of_equiv leibnizRaw_equiv_geom_taylor N stage
    rw [← ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute stage] at h
    change 4*((ArctanGeometry.arctanGeom 1).compute stage).lo ≤
        leibnizPartial N + leibnizRadius N ∧
      leibnizPartial N - leibnizRadius N ≤
        4*((ArctanGeometry.arctanGeom 1).compute stage).hi at h
    rw [Taylor.ArctanKernel.kernelPartialIntegralAtOne_eq_series_partialSum]
    dsimp [leibnizPartial, leibnizRadius] at h
    constructor <;> grind [Rat.div_def]
  constructor
  · intro i j
    have h := (hb j).2
    change -(1/(2*(N:Rat)+3)) ≤
      ((ArctanGeometry.arctanGeom 1).compute j).hi -
        Taylor.ArctanKernel.kernelPartialIntegralAtOne N
    grind
  · intro i j
    have h := (hb i).1
    change ((ArctanGeometry.arctanGeom 1).compute i).lo -
        Taylor.ArctanKernel.kernelPartialIntegralAtOne N ≤ 1/(2*(N:Rat)+3)
    grind

end ComputableAnalysis
