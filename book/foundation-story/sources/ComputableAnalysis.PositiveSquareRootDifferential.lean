import ComputableAnalysis.RepresentedPositiveSquareRoot
import ComputableAnalysis.DifferentialReciprocal

/-!
# Finite secant calculus for the positive square root

This module isolates the rational algebra behind differentiation of the
positive square-root chart.  If positive rational roots `u` and `v` represent
radicands `u^2` and `v^2`, their exact secant is `1/(u+v)`.  A common positive
lower margin then gives an explicit error coefficient for comparison with
`1/(2*u)`.  Later represented-input work only has to pay the rational
bisection widths around these exact identities.
-/

namespace ComputableAnalysis
namespace PositiveSquareRootDifferential

/-- Explicit stage making the rational square-root bisection budget no larger
than a requested positive rational tolerance. -/
def approximationPrecision (bound : Nat) (eps : QPos) : Nat :=
  (bound + 1) * (eps.val.den + 1)

theorem approximationBudget_at_precision_le
    (bound : Nat) (eps : QPos) :
    RepresentedPositiveSquareRoot.PositiveInput.approximationBudget bound
        (approximationPrecision bound eps) <= eps.val := by
  let C : Nat := bound + 1
  let D : Nat := eps.val.den + 1
  have hC : 0 < C := by dsimp [C]; omega
  have hD : 0 < D := by dsimp [D]; omega
  have hCD : 0 < C * D := Nat.mul_pos hC hD
  have hden : C * D <= C * D + 1 := by omega
  have hone := FTC.one_div_nat_antitone hCD (by omega : 0 < C * D + 1) hden
  have hscaled := Rat.mul_le_mul_of_nonneg_left hone
    (Rat.natCast_nonneg : 0 <= (C : Rat))
  have hCne : (C : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hC)
  have hDne : (D : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hD)
  have hcancel : (C : Rat) / ((C * D : Nat) : Rat) = 1 / (D : Rat) := by
    rw [show ((C * D : Nat) : Rat) = (C : Rat) * (D : Rat) by
      exact_mod_cast rfl]
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel, Rat.inv_mul_cancel]
  have hfirst :
      RepresentedPositiveSquareRoot.PositiveInput.approximationBudget bound
          (approximationPrecision bound eps) <= 1 / (D : Rat) := by
    change (C : Rat) / (((C * D + 1 : Nat) : Rat)) <= 1 / (D : Rat)
    calc
      (C : Rat) / (((C * D + 1 : Nat) : Rat)) <=
          (C : Rat) / ((C * D : Nat) : Rat) := by
        simpa [Rat.div_def] using hscaled
      _ = 1 / (D : Rat) := hcancel
  exact Rat.le_trans hfirst (by
    dsimp [D]
    exact FTC.one_div_den_succ_le_of_pos eps.property)

def secant (u v : Rat) : Rat :=
  (v - u) / (sq v - sq u)

def derivative (u : Rat) : Rat :=
  1 / (2 * u)

def errorCoefficient (margin : Rat) : Rat :=
  1 / (8 * margin ^ 3)

theorem square_sub_square (u v : Rat) :
    sq v - sq u = (v - u) * (v + u) := by
  unfold sq
  grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
    Rat.mul_assoc, Rat.mul_comm]

/-- Exact rational square-root secant identity. -/
theorem secant_eq_one_div_add
    {u v : Rat} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) :
    secant u v = 1 / (u + v) := by
  have hdiff : v - u ≠ 0 := by grind [Rat.sub_eq_add_neg]
  have hsum : 0 < v + u := by grind
  have hsumne : v + u ≠ 0 := Rat.ne_of_gt hsum
  unfold secant
  rw [square_sub_square, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel (v - u) hdiff,
    Rat.inv_mul_cancel (v - u) hdiff,
    Rat.mul_inv_cancel (v + u) hsumne,
    Rat.inv_mul_cancel (v + u) hsumne]

theorem secant_sub_derivative
    {u v : Rat} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) :
    secant u v - derivative u =
      -(sq v - sq u) *
        (2 * u * ((u + v) * (u + v)))⁻¹ := by
  have hune : u ≠ 0 := Rat.ne_of_gt hu
  have hsum : 0 < u + v := by grind
  have hsumne : u + v ≠ 0 := Rat.ne_of_gt hsum
  rw [secant_eq_one_div_add hu hv huv]
  unfold derivative
  rw [square_sub_square, Rat.div_def, Rat.div_def, Rat.one_mul,
    Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg, Rat.mul_inv_cancel u hune,
    Rat.inv_mul_cancel u hune,
    Rat.mul_inv_cancel (u + v) hsumne,
    Rat.inv_mul_cancel (u + v) hsumne]

theorem errorCoefficient_nonneg {margin : Rat} (hmargin : 0 < margin) :
    0 <= errorCoefficient margin := by
  unfold errorCoefficient
  rw [Rat.div_def]
  exact Rat.mul_nonneg (by decide +kernel)
    (Rat.le_of_lt ((Rat.inv_pos).2
      (Rat.mul_pos (by decide +kernel) (Rat.pow_pos hmargin))))

/-- Quantitative positive-square-root secant bound.

The error is linear in the radicand displacement, with the explicit uniform
coefficient `1/(8*margin^3)` on roots bounded below by `margin`. -/
theorem secant_error_le
    {margin u v : Rat}
    (hmargin : 0 < margin) (hmu : margin <= u) (hmv : margin <= v)
    (huv : u ≠ v) :
    qabs (secant u v - derivative u) <=
      errorCoefficient margin * qabs (sq v - sq u) := by
  have hu : 0 < u := by grind
  have hv : 0 < v := by grind
  have hsum : 0 < u + v := by grind
  have hsumLower : 2 * margin <= u + v := by grind
  have hsum0 : 0 <= u + v := Rat.le_of_lt hsum
  have hm0 : 0 <= margin := Rat.le_of_lt hmargin
  have hsumSquare :
      (2 * margin) * (2 * margin) <= (u + v) * (u + v) := by
    exact rat_mul_le_mul_of_nonneg
      (Rat.mul_nonneg (by decide +kernel) hm0) hsumLower
      (Rat.mul_nonneg (by decide +kernel) hm0) hsumLower
  have hu0 : 0 <= u := Rat.le_of_lt hu
  have hdenLower :
      8 * margin ^ 3 <= 2 * u * ((u + v) * (u + v)) := by
    have hleft :
        2 * margin * ((2 * margin) * (2 * margin)) <=
          2 * u * ((2 * margin) * (2 * margin)) := by
      exact Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_left hmu (by decide +kernel))
        (Rat.mul_nonneg
          (Rat.mul_nonneg (by decide +kernel) hm0)
          (Rat.mul_nonneg (by decide +kernel) hm0))
    have hright :
        2 * u * ((2 * margin) * (2 * margin)) <=
          2 * u * ((u + v) * (u + v)) :=
      Rat.mul_le_mul_of_nonneg_left hsumSquare
        (Rat.mul_nonneg (by decide +kernel) hu0)
    calc
      8 * margin ^ 3 =
          2 * margin * ((2 * margin) * (2 * margin)) := by
        simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= 2 * u * ((2 * margin) * (2 * margin)) := hleft
      _ <= 2 * u * ((u + v) * (u + v)) := hright
  have hmarginCube : 0 < 8 * margin ^ 3 :=
    Rat.mul_pos (by decide +kernel) (Rat.pow_pos hmargin)
  have hdenPos : 0 < 2 * u * ((u + v) * (u + v)) :=
    Rat.mul_pos (Rat.mul_pos (by decide +kernel) hu)
      (Rat.mul_pos hsum hsum)
  have hinvLe :
      (2 * u * ((u + v) * (u + v)))⁻¹ <=
        (8 * margin ^ 3)⁻¹ :=
    Rat.inv_antitone_of_pos hmarginCube hdenLower
  rw [secant_sub_derivative hu hv huv, qabs_mul, qabs_neg]
  rw [qabs_eq_self_of_nonneg
    (Rat.le_of_lt ((Rat.inv_pos).2 hdenPos))]
  unfold errorCoefficient
  rw [Rat.div_def, Rat.one_mul]
  simpa [Rat.mul_comm] using
    (Rat.mul_le_mul_of_nonneg_right hinvLe
      (qabs_nonneg (sq v - sq u)))

/-! ## Width-aware approximate roots -/

/-- The square of the midpoint of a rational square-root certificate misses
the radicand by at most the width of the squared certificate interval. -/
theorem midpoint_square_residual_le
    {q : Rat} {I : QInterval} (hI : SqrtIntervalSpec q I) :
    qabs (sq I.midpoint - q) <= I.width * (I.hi + I.lo) := by
  have hmid := QInterval.midpoint_mem hI.2.1
  have hmid0 : 0 <= I.midpoint := Rat.le_trans hI.1 hmid.1
  have hlo : sq I.lo <= sq I.midpoint :=
    sq_le_sq_of_nonneg_le hI.1 hmid.1
  have hhi : sq I.midpoint <= sq I.hi :=
    sq_le_sq_of_nonneg_le hmid0 hmid.2
  have hgap := qabs_sub_le_of_common_bounds
    hlo hhi hI.2.2.1 hI.2.2.2
  rw [sq_sub_factor] at hgap
  simpa only [QInterval.width] using hgap

/-- The difference between the squared-midpoint displacement and the true
radicand displacement is controlled entirely by the two finite bisection
widths. -/
theorem midpoint_square_displacement_residual_le
    {q r : Rat} {I J : QInterval}
    (hI : SqrtIntervalSpec q I) (hJ : SqrtIntervalSpec r J) :
    qabs ((sq J.midpoint - sq I.midpoint) - (r - q)) <=
      J.width * (J.hi + J.lo) + I.width * (I.hi + I.lo) := by
  have hrewrite :
      (sq J.midpoint - sq I.midpoint) - (r - q) =
        (sq J.midpoint - r) + -(sq I.midpoint - q) := by
    grind [Rat.sub_eq_add_neg]
  rw [hrewrite]
  calc
    qabs ((sq J.midpoint - r) + -(sq I.midpoint - q)) <=
        qabs (sq J.midpoint - r) + qabs (-(sq I.midpoint - q)) :=
      qabs_add_le _ _
    _ = qabs (sq J.midpoint - r) + qabs (sq I.midpoint - q) := by
      rw [qabs_neg]
    _ <= J.width * (J.hi + J.lo) + I.width * (I.hi + I.lo) :=
      rat_add_le_add (midpoint_square_residual_le hJ)
        (midpoint_square_residual_le hI)

/-- Exact algebra for a secant formed from approximate square roots.

The first numerator term is the usual square-root curvature error.  The
second is the finite residual saying that the squared rational witnesses need
not equal their represented radicands exactly. -/
theorem approximate_secant_error_identity
    {q r u v : Rat} (hu : u ≠ 0) (hqr : r - q ≠ 0) :
    ((v - u) / (r - q) - derivative u) =
      (-(v - u) * (v - u) +
        ((sq v - sq u) - (r - q))) *
          (2 * u * (r - q))⁻¹ := by
  unfold derivative sq
  rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have htwoU : 2 * u ≠ 0 := by
    intro hzero
    have htwo : (2 : Rat) ≠ 0 := by decide +kernel
    grind
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg, Rat.mul_inv_cancel, Rat.inv_mul_cancel]

/-- Quantitative form of `approximate_secant_error_identity`.  It separates
the curvature term `|v-u|^2` from the squared-root residual, and displays the
`1/|r-q|` magnification that the represented evaluator schedule must pay. -/
theorem approximate_secant_error_le
    {q r u v rootLower : Rat}
    (hrootLower : 0 < rootLower) (hroot : rootLower <= u)
    (hqr : r - q ≠ 0) :
    qabs (((v - u) / (r - q)) - derivative u) <=
      (1 / (2 * rootLower)) * qabs (1 / (r - q)) *
        (qabs (v - u) * qabs (v - u) +
          qabs ((sq v - sq u) - (r - q))) := by
  have hu : 0 < u := by grind
  have hune : u ≠ 0 := Rat.ne_of_gt hu
  have hnum := qabs_add_le
    (-(v - u) * (v - u)) ((sq v - sq u) - (r - q))
  rw [qabs_mul, qabs_neg] at hnum
  have htwoLower : 0 < 2 * rootLower :=
    Rat.mul_pos (by decide +kernel) hrootLower
  have htwoU : 0 < 2 * u := Rat.mul_pos (by decide +kernel) hu
  have hden : 2 * rootLower <= 2 * u :=
    Rat.mul_le_mul_of_nonneg_left hroot (by decide +kernel)
  have hinv : (2 * u)⁻¹ <= (2 * rootLower)⁻¹ :=
    Rat.inv_antitone_of_pos htwoLower hden
  have hstep0 : 0 <= qabs ((r - q)⁻¹) := qabs_nonneg _
  have hnum0 :
      0 <= qabs (v - u) * qabs (v - u) +
        qabs ((sq v - sq u) - (r - q)) :=
    Rat.add_nonneg
      (Rat.mul_nonneg (qabs_nonneg _) (qabs_nonneg _))
      (qabs_nonneg _)
  rw [approximate_secant_error_identity hune hqr, qabs_mul,
    Rat.inv_mul_rev, qabs_mul]
  rw [qabs_eq_self_of_nonneg
    (Rat.le_of_lt ((Rat.inv_pos).2 htwoU))]
  rw [show qabs ((r - q)⁻¹) * (2 * u)⁻¹ =
      (2 * u)⁻¹ * qabs ((r - q)⁻¹) by
    exact Rat.mul_comm _ _]
  calc
    qabs (-(v - u) * (v - u) + ((sq v - sq u) - (r - q))) *
          ((2 * u)⁻¹ * qabs ((r - q)⁻¹)) <=
        (qabs (v - u) * qabs (v - u) +
          qabs ((sq v - sq u) - (r - q))) *
          ((2 * u)⁻¹ * qabs ((r - q)⁻¹)) :=
      Rat.mul_le_mul_of_nonneg_right hnum
        (Rat.mul_nonneg
          (Rat.le_of_lt ((Rat.inv_pos).2 htwoU)) hstep0)
    _ <= (qabs (v - u) * qabs (v - u) +
          qabs ((sq v - sq u) - (r - q))) *
          ((2 * rootLower)⁻¹ * qabs ((r - q)⁻¹)) := by
      exact Rat.mul_le_mul_of_nonneg_left
        (Rat.mul_le_mul_of_nonneg_right hinv hstep0) hnum0
    _ = (1 / (2 * rootLower)) * qabs (1 / (r - q)) *
          (qabs (v - u) * qabs (v - u) +
            qabs ((sq v - sq u) - (r - q))) := by
      rw [Rat.div_def, Rat.one_mul, Rat.div_def, Rat.one_mul]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Complete finite width-aware secant estimate for two rational
square-root certificates.  This is the exact-model bridge needed before
choosing an evaluator stage as a function of the nonzero rational step. -/
theorem sqrtCertificate_approximate_secant_error_le
    {q r rootLower margin : Rat} {I J : QInterval}
    (hrootLower : 0 < rootLower)
    (hmargin : 0 < margin)
    (hI : SqrtIntervalSpec q I) (hJ : SqrtIntervalSpec r J)
    (hmq : sq margin <= q) (hmr : sq margin <= r)
    (hroot : rootLower <= I.midpoint)
    (hqr : r - q ≠ 0) :
    qabs (((J.midpoint - I.midpoint) / (r - q)) -
        derivative I.midpoint) <=
      (1 / (2 * rootLower)) * qabs (1 / (r - q)) *
        ((margin⁻¹ * qabs (r - q) + I.width + J.width) *
            (margin⁻¹ * qabs (r - q) + I.width + J.width) +
          (J.width * (J.hi + J.lo) +
            I.width * (I.hi + I.lo))) := by
  let distanceBound :=
    margin⁻¹ * qabs (r - q) + I.width + J.width
  have hdist : qabs (J.midpoint - I.midpoint) <= distanceBound := by
    exact RepresentedPositiveSquareRoot.sqrtCertificate_midpoint_lipschitz
      hmargin hI hJ hmq hmr
  have hdist0 : 0 <= distanceBound :=
    Rat.le_trans (qabs_nonneg _) hdist
  have hsquare :
      qabs (J.midpoint - I.midpoint) *
          qabs (J.midpoint - I.midpoint) <=
        distanceBound * distanceBound :=
    rat_mul_le_mul_of_nonneg (qabs_nonneg _) hdist
      (qabs_nonneg _) hdist
  have hresidual := midpoint_square_displacement_residual_le hI hJ
  have hsum :
      qabs (J.midpoint - I.midpoint) *
            qabs (J.midpoint - I.midpoint) +
          qabs ((sq J.midpoint - sq I.midpoint) - (r - q)) <=
        distanceBound * distanceBound +
          (J.width * (J.hi + J.lo) +
            I.width * (I.hi + I.lo)) :=
    rat_add_le_add hsquare hresidual
  have houter0 :
      0 <= (1 / (2 * rootLower)) * qabs (1 / (r - q)) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.mul_nonneg
      (Rat.le_of_lt ((Rat.inv_pos).2
        (Rat.mul_pos (by decide +kernel) hrootLower)))
      (qabs_nonneg _)
  exact Rat.le_trans
    (approximate_secant_error_le hrootLower hroot hqr)
    (Rat.mul_le_mul_of_nonneg_left hsum houter0)

/-- Specialization to the guarded bisection boxes actually used by two
represented positive inputs.  The lower root margin is `margin/2`; every
other term in the bound is a literal rational field of the two finite
certificates at the common shifted stage. -/
theorem shiftedApproximation_secant_error_le
    {bound : Nat} {margin : Rat}
    (A B : RepresentedPositiveSquareRoot.PositiveInput bound margin)
    (n : Nat)
    (hcenters :
      (B.raw.compute
          (n + RepresentedPositiveSquareRoot.PositiveInput.guardShift
            bound margin)).midpoint -
        (A.raw.compute
          (n + RepresentedPositiveSquareRoot.PositiveInput.guardShift
            bound margin)).midpoint ≠ 0) :
    let stage := n +
      RepresentedPositiveSquareRoot.PositiveInput.guardShift bound margin
    let I := RepresentedPositiveSquareRoot.PositiveInput.approximation A stage
    let J := RepresentedPositiveSquareRoot.PositiveInput.approximation B stage
    let q := (A.raw.compute stage).midpoint
    let r := (B.raw.compute stage).midpoint
    qabs (((J.midpoint - I.midpoint) / (r - q)) -
        derivative I.midpoint) <=
      (1 / (2 * (margin / 2))) * qabs (1 / (r - q)) *
        ((margin⁻¹ * qabs (r - q) + I.width + J.width) *
            (margin⁻¹ * qabs (r - q) + I.width + J.width) +
          (J.width * (J.hi + J.lo) +
            I.width * (I.hi + I.lo))) := by
  dsimp only
  let stage := n +
    RepresentedPositiveSquareRoot.PositiveInput.guardShift bound margin
  let I := RepresentedPositiveSquareRoot.PositiveInput.approximation A stage
  let J := RepresentedPositiveSquareRoot.PositiveInput.approximation B stage
  have hhalf : 0 < margin / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_pos A.margin_pos
      ((Rat.inv_pos).2 (by decide +kernel))
  have hspecA : SqrtIntervalSpec (A.raw.compute stage).midpoint I :=
    RepresentedPositiveSquareRoot.PositiveInput.approximation_spec A stage
  have hspecB : SqrtIntervalSpec (B.raw.compute stage).midpoint J :=
    RepresentedPositiveSquareRoot.PositiveInput.approximation_spec B stage
  have hroot : margin / 2 <= I.midpoint := by
    have hlo :=
      RepresentedPositiveSquareRoot.PositiveInput.half_margin_le_shifted_approximation_lo
        A n
    have hmid := QInterval.midpoint_mem hspecA.2.1
    exact Rat.le_trans hlo hmid.1
  exact sqrtCertificate_approximate_secant_error_le
    hhalf A.margin_pos hspecA hspecB
    (A.margin_sq_le_center stage) (B.margin_sq_le_center stage)
    hroot hcenters

end PositiveSquareRootDifferential
end ComputableAnalysis
