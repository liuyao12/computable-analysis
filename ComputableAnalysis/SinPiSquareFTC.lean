import ComputableAnalysis.SinPiIntegral
import ComputableAnalysis.FiniteSinePrefixFTC
import ComputableAnalysis.ArctanEffectiveFTC

/-!
# The squared-sine test function

This file records the first product-valued non-polynomial integrand.  The
pointwise square is built from the same arctangent/nested-radical sine
representation as the half-interval sine integral; no real-number product or
Lebesgue integral is introduced.
-/

namespace ComputableAnalysis

namespace SinPiIntegral

/-! The finite polynomial rung is already a complete effective-FTC theorem.
Expose it here as the algebraic shadow of the nested-radical target, so that
the later tail-transport proof has a fixed, checked predecessor. -/

def finiteSineSquarePrefixRaw : RealFunRaw :=
  FiniteSinePrefix.sineTaylorPrefixThreeSquareRaw

def finiteSineSquarePrefixPrimitiveRaw : RealFunRaw :=
  FiniteSinePrefix.sineTaylorPrefixThreeSquarePrimitiveRaw

/-! Tangent-chart endpoint algebra for the true squared-sine target.  With
`u = tan(pi*x/2)`, the normalized density is
`8*u^2/(1+u^2)^3`.  Its primitive splits into the existing arctangent kernel
and an exact rational correction. -/

def tangentSquareDensity (u : Rat) : Rat :=
  (8 * u * u) / (1 + u * u) ^ 3

def tangentSquareRationalPart (u : Rat) : Rat :=
  -((2 * u) / (1 + u * u) ^ 2) + u / (1 + u * u)

def tangentSquareChartFactor (u : Rat) : Rat :=
  u / (1 + u * u)

def tangentSquareRationalDerivative (u : Rat) : Rat :=
  (-1 + 6 * u * u - u ^ 4) / (1 + u * u) ^ 3

theorem tangentSquareDensity_decomposition (u : Rat) :
    tangentSquareDensity u =
      1 / (1 + u * u) + tangentSquareRationalDerivative u := by
  unfold tangentSquareDensity tangentSquareRationalDerivative
  have hden : 1 + u * u > 0 := by
    have hsq : 0 <= u * u := by
      exact rat_square_nonneg_basic u
    grind
  have hdenne : 1 + u * u ≠ 0 := Rat.ne_of_gt hden
  rw [Rat.div_def, Rat.div_def]
  have hpow : (1 + u * u) ^ 3 =
      (1 + u * u) * (1 + u * u) * (1 + u * u) := by
    simp [Rat.pow_succ]
  rw [hpow]
  have hcancel : (1 + u * u)⁻¹ * (1 + u * u) = 1 :=
    Rat.inv_mul_cancel _ hdenne
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

theorem tangentSquareDensity_eq_two_factor_mul_tangentPullbackDensity
    (u : Rat) :
    tangentSquareDensity u =
      2 * tangentSquareChartFactor u * tangentPullbackDensity u := by
  unfold tangentSquareDensity tangentSquareChartFactor tangentPullbackDensity
  have hden : 1 + u * u ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos u)
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg, Rat.mul_inv_cancel _ hden]

theorem tangentSquareChartFactor_bounds
    {u : Rat} (hu0 : 0 <= u) (hu1 : u <= 1) :
    0 <= tangentSquareChartFactor u /\ tangentSquareChartFactor u <= 1 := by
  unfold tangentSquareChartFactor
  have hsq : 0 <= u * u := rat_square_nonneg_basic u
  have hden : 0 < 1 + u * u := by grind
  have hinv : 0 <= (1 + u * u)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hden)
  constructor
  · exact Rat.mul_nonneg hu0 hinv
  · rw [Rat.div_def]
    have hne : 1 + u * u ≠ 0 := Rat.ne_of_gt hden
    have hcancel : (1 + u * u)⁻¹ * (1 + u * u) = 1 :=
      Rat.inv_mul_cancel _ hne
    apply Rat.le_of_mul_le_mul_right (c := 1 + u * u)
    · rw [Rat.mul_assoc, hcancel]
      have hmul := Rat.mul_le_mul_of_nonneg_left hu1 hu0
      grind
    · exact hden

theorem tangentSquareDensity_lipschitz_on_unit :
    Integral.LipschitzOnUnit tangentSquareDensity 64 := by
  constructor
  · native_decide
  · intro s t hs0 hs1 ht0 ht1
    let p : Rat -> Rat := tangentSquareChartFactor
    let d : Rat -> Rat := tangentPullbackDensity
    have hp := IntegralIdentities.coordinate_integralKernel_lipschitz_on_unit.2
      s t hs0 hs1 ht0 ht1
    have hps := tangentSquareChartFactor_bounds hs0 hs1
    have hpt := tangentSquareChartFactor_bounds ht0 ht1
    have hd := tangentPullbackDensity_lipschitz_on_unit.2
      s t hs0 hs1 ht0 ht1
    have hD : forall u : Rat, 0 <= u -> u <= 1 ->
        0 <= d u /\ d u <= 4 := by
      intro u hu0 hu1
      unfold d tangentPullbackDensity
      have hpf := tangentSquareChartFactor_bounds hu0 hu1
      have hsq : 0 <= u * u := rat_square_nonneg_basic u
      have hden : 0 < 1 + u * u := by grind
      have hinv : 0 <= (1 / (1 + u * u) : Rat) := by
        simpa [Rat.div_def] using Rat.le_of_lt ((Rat.inv_pos).2 hden)
      have hp0 : 0 <= u * (1 / (1 + u * u)) := by
        simpa [tangentSquareChartFactor, Rat.div_def, Rat.mul_assoc] using hpf.1
      have hp1 : u * (1 / (1 + u * u)) <= 1 := by
        simpa [tangentSquareChartFactor, Rat.div_def, Rat.mul_assoc] using hpf.2
      constructor
      · exact Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) hp0) hinv
      · have hinv1 : (1 / (1 + u * u) : Rat) <= 1 := by
          rw [Rat.div_def]
          have hne : 1 + u * u ≠ 0 := Rat.ne_of_gt hden
          apply Rat.le_of_mul_le_mul_right (c := 1 + u * u)
          · rw [Rat.mul_assoc, Rat.inv_mul_cancel _ hne]
            grind
          · exact hden
        have hprod := Rat.mul_le_mul_of_nonneg_right hp1 hinv
        have hprod' : u * (1 / (1 + u * u)) * (1 / (1 + u * u)) <= 1 := by
          calc
            u * (1 / (1 + u * u)) * (1 / (1 + u * u)) <=
                1 * (1 / (1 + u * u)) := by simpa [Rat.mul_assoc] using hprod
            _ <= 1 := by simpa using hinv1
        simpa [Rat.mul_assoc] using Rat.mul_le_mul_of_nonneg_left hprod'
          (by native_decide : (0 : Rat) <= 4)
    have hds := hD s hs0 hs1
    have hdt := hD t ht0 ht1
    have hsplit :
        tangentSquareDensity s - tangentSquareDensity t =
          2 * (p s * (d s - d t) + (p s - p t) * d t) := by
      rw [tangentSquareDensity_eq_two_factor_mul_tangentPullbackDensity,
        tangentSquareDensity_eq_two_factor_mul_tangentPullbackDensity]
      dsimp [p, d]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
        Rat.sub_eq_add_neg]
    have hsum :
        qabs (p s * (d s - d t) + (p s - p t) * d t) <=
          p s * qabs (d s - d t) + qabs (p s - p t) * d t := by
      calc
        qabs (p s * (d s - d t) + (p s - p t) * d t) <=
            qabs (p s * (d s - d t)) + qabs ((p s - p t) * d t) :=
          qabs_add_le _ _
        _ = qabs (p s) * qabs (d s - d t) +
            qabs (p s - p t) * qabs (d t) := by
          simp only [qabs_mul]
        _ = p s * qabs (d s - d t) +
            qabs (p s - p t) * d t := by
          rw [qabs_eq_self_of_nonneg hps.1,
            qabs_eq_self_of_nonneg hdt.1]
    have hterm1 :
        p s * qabs (d s - d t) <= p s * (20 * qabs (t - s)) :=
      Rat.mul_le_mul_of_nonneg_left
        (by simpa [d] using hd) hps.1
    have hterm2 :
        qabs (p s - p t) * d t <= (3 * qabs (t - s)) * d t :=
      Rat.mul_le_mul_of_nonneg_right
        (by simpa [p, tangentSquareChartFactor,
          ArctanGeometry.integralKernel, Rat.div_def, Rat.mul_assoc] using hp) hdt.1
    calc
      qabs (tangentSquareDensity s - tangentSquareDensity t) =
          qabs (2 * (p s * (d s - d t) + (p s - p t) * d t)) := by rw [hsplit]
      _ = qabs (2 : Rat) *
          qabs (p s * (d s - d t) + (p s - p t) * d t) := by rw [qabs_mul]
      _ <= 2 * (20 * qabs (t - s) + 3 * qabs (t - s) * 4) := by
        rw [show qabs (2 : Rat) = 2 by native_decide]
        have hsum'' :
            p s * (20 * qabs (t - s)) +
                3 * qabs (t - s) * d t <=
              20 * qabs (t - s) + 3 * qabs (t - s) * 4 := by
          have h1 : p s * (20 * qabs (t - s)) <=
              20 * qabs (t - s) := by
            simpa [p] using Rat.mul_le_mul_of_nonneg_right hps.2
              (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 20)
                (qabs_nonneg (t - s)))
          have h2 := Rat.mul_le_mul_of_nonneg_left hdt.2
            (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 3)
              (qabs_nonneg (t - s)))
          exact rat_add_le_add h1 h2
        have hsum' := rat_add_le_add hterm1 hterm2
        have hbound := Rat.le_trans hsum hsum'
        have hbound' := Rat.le_trans hbound hsum''
        exact Rat.mul_le_mul_of_nonneg_left hbound'
          (by native_decide : (0 : Rat) <= 2)
      _ = 64 * qabs (t - s) := by grind

/-! The first local certificate for the tangent-square effective FTC.  The
cell box is deliberately conservative: its center is the exact rational
density at the left endpoint and its padding is the proved Lipschitz constant
times the cell width. -/

def tangentSquareDensityRaw : RealFunRaw :=
  RealFunRaw.exact tangentSquareDensity

theorem tangentSquareDensityRaw_valid : tangentSquareDensityRaw.Valid :=
  RealFunRaw.exact_valid _

def tangentSquareCellBound (C : RationalSubinterval 0 1) : QInterval :=
  { lo := tangentSquareDensity C.lower - 64 * C.width,
    hi := tangentSquareDensity C.lower + 64 * C.width }

theorem tangentSquareCellBound_ordered
    (C : RationalSubinterval 0 1) :
    0 <= (tangentSquareCellBound C).width := by
  unfold tangentSquareCellBound QInterval.width
  have hw : 0 <= C.width := by
    unfold RationalSubinterval.width
    grind [C.ordered]
  grind

theorem tangentSquareCellBound_contains_density
    (C : RationalSubinterval 0 1) {x : Rat}
    (hx : C.contains x) :
    (tangentSquareCellBound C).ContainsInterval
      (tangentSquareDensityRaw.compute x 0) := by
  have hC0 : 0 <= C.lower := C.lower_mem
  have hC1 : C.upper <= 1 := C.upper_mem
  have hxa : 0 <= x := Rat.le_trans hC0 hx.1
  have hxb : x <= 1 := Rat.le_trans hx.2 hC1
  have hLip := tangentSquareDensity_lipschitz_on_unit.2
    C.lower x hC0 (Rat.le_trans C.ordered hC1) hxa hxb
  have hdist : qabs (x - C.lower) <= C.width := by
    rw [qabs_eq_self_of_nonneg (by grind [hx.1])]
    calc
      x - C.lower <= C.upper - C.lower := by grind [hx.2]
      _ = C.width := by rfl
  have hdiff : qabs (tangentSquareDensity x -
      tangentSquareDensity C.lower) <= 64 * C.width := by
    have hLip' : qabs (tangentSquareDensity x -
        tangentSquareDensity C.lower) <= 64 * qabs (x - C.lower) := by
      have hneg : tangentSquareDensity C.lower - tangentSquareDensity x =
          -(tangentSquareDensity x - tangentSquareDensity C.lower) := by
        grind
      rw [hneg, qabs_neg] at hLip
      exact hLip
    exact Rat.le_trans hLip'
      (Rat.mul_le_mul_of_nonneg_left hdist (by native_decide))
  unfold tangentSquareCellBound QInterval.ContainsInterval
  change tangentSquareDensity C.lower - 64 * C.width <=
      tangentSquareDensity x /\
    tangentSquareDensity x <= tangentSquareDensity C.lower + 64 * C.width
  have hlow := neg_qabs_le_self
    (tangentSquareDensity x - tangentSquareDensity C.lower)
  have hhigh := self_le_qabs
    (tangentSquareDensity x - tangentSquareDensity C.lower)
  constructor <;> grind [Rat.sub_eq_add_neg]

def tangentSquarePartition (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (128 * (eps.val.den + 1))
    (by omega) (by native_decide)

theorem tangentSquarePartition_cell_strict
    (eps : QPos) {k : Nat}
    (hk : k < (tangentSquarePartition eps).pieces) :
    ((tangentSquarePartition eps).cell k hk).lower <
      ((tangentSquarePartition eps).cell k hk).upper := by
  have hpos : 0 < mesh 0 1 (128 * (eps.val.den + 1)) := by
    change 0 < mesh 0 1 (128 * (eps.val.den + 1))
    unfold mesh
    rw [if_neg (by omega : 128 * (eps.val.den + 1) ≠ 0)]
    rw [Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 (Rat.natCast_pos.mpr (by omega)))
  have hw : 0 < ((tangentSquarePartition eps).cell k hk).width := by
    change 0 < ((RationalPartition.uniform 0 1
      (128 * (eps.val.den + 1)) (by omega) (by native_decide)).cell k hk).width
    rw [RationalPartition.uniform_cell_width 0 1
      (128 * (eps.val.den + 1)) (by omega) (by native_decide) k hk]
    exact hpos
  unfold RationalSubinterval.width at hw
  exact by grind

theorem tangentSquareUniformBoundSum_width_le (eps : QPos) :
    ((tangentSquarePartition eps).boundIntegralSum
      (fun k hk => tangentSquareCellBound
        ((tangentSquarePartition eps).cell k hk))).width <= eps.val := by
  let P := tangentSquarePartition eps
  have hbound : forall k (hk : k < P.pieces),
      (tangentSquareCellBound (P.cell k hk)).width <=
        128 * mesh 0 1 P.pieces := by
    intro k hk
    have hcell : (P.cell k hk).width = mesh 0 1 P.pieces := by
      change ((RationalPartition.uniform 0 1
        (128 * (eps.val.den + 1)) (by omega) (by native_decide)).cell k hk).width =
        mesh 0 1 (128 * (eps.val.den + 1))
      rw [RationalPartition.uniform_cell_width 0 1
        (128 * (eps.val.den + 1)) (by omega) (by native_decide) k hk]
    rw [show (tangentSquareCellBound (P.cell k hk)).width =
      128 * (P.cell k hk).width by
        unfold tangentSquareCellBound QInterval.width
        grind [Rat.sub_eq_add_neg]]
    rw [hcell]
    exact Rat.le_refl
  have hsum := RationalPartition.uniform_boundIntegralSum_width_le
    P.pieces P.positive (show (0 : Rat) <= 1 by native_decide)
    (fun k hk => tangentSquareCellBound (P.cell k hk))
    (128 * mesh 0 1 P.pieces) hbound
  change ((P.boundIntegralSum
    (fun k hk => tangentSquareCellBound (P.cell k hk))).width <=
    (1 - 0) * (128 * mesh 0 1 P.pieces)) at hsum
  change ((P.boundIntegralSum
    (fun k hk => tangentSquareCellBound (P.cell k hk))).width <= eps.val)
  have hmesh : mesh 0 1 P.pieces =
      1 / (((128 * (eps.val.den + 1) : Nat) : Rat)) := by
    change mesh 0 1 (128 * (eps.val.den + 1)) = _
    unfold mesh
    rw [if_neg (by omega : 128 * (eps.val.den + 1) ≠ 0)]
    rw [Rat.div_def, Rat.natCast_mul, Rat.natCast_add]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hone : 1 / (((eps.val.den + 1 : Nat) : Rat)) <= eps.val :=
    FTC.one_div_den_succ_le_of_pos eps.property
  rw [hmesh] at hsum
  have hsum' :
      (P.boundIntegralSum
        (fun k hk => tangentSquareCellBound (P.cell k hk))).width <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    calc
      (P.boundIntegralSum
          (fun k hk => tangentSquareCellBound (P.cell k hk))).width <=
          (1 - 0) *
            (128 * (1 / (((128 * (eps.val.den + 1) : Nat) : Rat)))) := by
              simpa using hsum
      _ = 1 / (((eps.val.den + 1 : Nat) : Rat)) := by
        rw [Rat.natCast_mul, Rat.natCast_add, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  exact Rat.le_trans hsum' hone

/-! The independent dyadic anchor for the squared tangent-chart density.  This
is deliberately separate from the nested-radical candidate: the latter is
related to this object only by a proved overlap theorem. -/

def tangentSquareDensityOnUnit : FunctionOnInterval :=
  FunctionOnInterval.exactRat tangentSquareDensity 0 1

def tangentSquareIntegral : RealRaw :=
  Integral.integralFor tangentSquareDensityOnUnit
    (IntegralIdentities.LipschitzDyadic.construction
      tangentSquareDensity 64 tangentSquareDensity_lipschitz_on_unit)

theorem tangentSquareIntegral_valid :
    tangentSquareIntegral.Valid := by
  exact Integral.integralFor_valid tangentSquareDensityOnUnit
    (IntegralIdentities.LipschitzDyadic.construction
      tangentSquareDensity 64 tangentSquareDensity_lipschitz_on_unit)

theorem tangentSquareIntegral_compute (stage : Nat) :
    tangentSquareIntegral.compute stage =
      IntegralIdentities.LipschitzDyadic.compute
        tangentSquareDensity 64 stage := rfl

theorem tangentSquareDensity_eq_circleSin_sq_mul_chartJacobian (u : Rat) :
    tangentSquareDensity u =
      RationalCircle.Trigonometry.sin u *
          RationalCircle.Trigonometry.sin u *
          (2 / (1 + u * u)) := by
  rw [RationalCircle.Trigonometry.sin_eq]
  have hden : 1 + u * u ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos u)
  rw [tangentSquareDensity, Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg, Rat.mul_inv_cancel _ hden]

theorem tangentSquareRationalPart_zero :
    tangentSquareRationalPart 0 = 0 := by
  native_decide

theorem tangentSquareRationalPart_one :
    tangentSquareRationalPart 1 = 0 := by
  native_decide

private theorem rat_eq_of_mul_eq_mul_pos_square
    {a b c : Rat} (hc : 0 < c) (h : a * c = b * c) : a = b := by
  have hcne : c ≠ 0 := Rat.ne_of_gt hc
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem tangentSquareRationalPart_difference_identity
    (p r : Rat) :
    tangentSquareRationalPart r - tangentSquareRationalPart p =
      -((r - p) * (p * r + 1) * (p * r - p - r - 1) *
        (p * r + p + r - 1)) /
        ((1 + p * p) ^ 2 * (1 + r * r) ^ 2) := by
  have hp : 0 < 1 + p * p := by
    have h := rat_square_nonneg_basic p
    grind
  have hr : 0 < 1 + r * r := by
    have h := rat_square_nonneg_basic r
    grind
  let A : Rat := 1 + p * p
  let B : Rat := 1 + r * r
  let W : Rat := r - p
  have hprod : 0 < A * A * B * B := by
    exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos hp hp) hr) hr
  apply rat_eq_of_mul_eq_mul_pos_square (c := A * A * B * B) hprod
  rw [tangentSquareRationalPart, tangentSquareRationalPart]
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have hAne : A ≠ 0 := Rat.ne_of_gt hp
  have hBne : B ≠ 0 := Rat.ne_of_gt hr
  have hA_cancel : A⁻¹ * A = 1 := Rat.inv_mul_cancel A hAne
  have hB_cancel : B⁻¹ * B = 1 := Rat.inv_mul_cancel B hBne
  have hA2_cancel : (A * A)⁻¹ * (A * A) = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.mul_pos hp hp))
  have hB2_cancel : (B * B)⁻¹ * (B * B) = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.mul_pos hr hr))
  have hR1 :
      (2 * r * (B * B)⁻¹) * (A * A * B * B) = 2 * r * (A * A) := by
    rw [Rat.inv_mul_rev]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hR2 :
      (r * B⁻¹) * (A * A * B * B) = r * (A * A * B) := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hP1 :
      (2 * p * (A * A)⁻¹) * (A * A * B * B) = 2 * p * (B * B) := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hP2 :
      (p * A⁻¹) * (A * A * B * B) = p * (A * B * B) := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hApow : (1 + p * p) ^ 2 = A * A := by
    dsimp [A]
    simp [Rat.pow_succ]
  have hBpow : (1 + r * r) ^ 2 = B * B := by
    dsimp [B]
    simp [Rat.pow_succ]
  rw [hApow, hBpow]
  have hAinv : (1 + p * p)⁻¹ = A⁻¹ := by rfl
  have hBinv : (1 + r * r)⁻¹ = B⁻¹ := by rfl
  rw [hAinv, hBinv]
  change
    ((-(2 * r * (B * B)⁻¹) + r * B⁻¹) -
      (-(2 * p * (A * A)⁻¹) + p * A⁻¹)) *
        (A * A * B * B) =
      (-(W * (p * r + 1) * (p * r - p - r - 1) *
        (p * r + p + r - 1)) * (A * A * (B * B))⁻¹) *
        (A * A * B * B)
  have hleft :
      ((-(2 * r * (B * B)⁻¹) + r * B⁻¹) -
        (-(2 * p * (A * A)⁻¹) + p * A⁻¹)) *
          (A * A * B * B) =
        (-(2 * r * (A * A)) + r * (A * A * B)) -
          (-(2 * p * (B * B)) + p * (A * B * B)) := by
    grind [Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg]
  rw [hleft]
  rw [Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

private theorem tangentSquareRationalPart_secant_error_polynomial
    (p r : Rat) :
    -((p * r + 1) * (p * r - p - r - 1) *
        (p * r + p + r - 1)) * (1 + p * p) -
        (-1 + 6 * p * p - p ^ 4) * (1 + r * r) ^ 2 =
      (r - p) *
        (p ^ 4 * r ^ 3 - p ^ 4 * r - 6 * p ^ 3 * r ^ 2 - 2 * p ^ 3 -
          6 * p ^ 2 * r ^ 3 - 6 * p ^ 2 * r + 2 * p * r ^ 2 + 6 * p +
          r ^ 3 + 3 * r) := by
  simp [Rat.pow_succ]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

private theorem tangentSquareRationalPart_secant_identity
    {p r : Rat} (hpr : p < r) :
    (tangentSquareRationalPart r - tangentSquareRationalPart p) /
        (r - p) =
      -((p * r + 1) * (p * r - p - r - 1) *
        (p * r + p + r - 1)) /
        ((1 + p * p) ^ 2 * (1 + r * r) ^ 2) := by
  have hW : 0 < r - p := by grind
  apply rat_eq_of_mul_eq_mul_pos_square (c := r - p) hW
  rw [tangentSquareRationalPart_difference_identity]
  rw [Rat.div_def, Rat.div_def]
  have hWne : r - p ≠ 0 := Rat.ne_of_gt hW
  have hWcancel : (r - p)⁻¹ * (r - p) = 1 :=
    Rat.inv_mul_cancel _ hWne
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg, Rat.inv_mul_rev]

private theorem rat_inv_square_mul_cube {a : Rat} (ha : 0 < a) :
    (a ^ 2)⁻¹ * a ^ 3 = a := by
  have hcancel : (a ^ 2)⁻¹ * a ^ 2 = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.pow_pos ha))
  rw [show a ^ 3 = a ^ 2 * a by simp [Rat.pow_succ, Rat.mul_assoc]]
  rw [← Rat.mul_assoc, hcancel, Rat.one_mul]

private theorem rat_unit_pow_bounds {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (n : Nat) : (0 <= x ^ n) ∧ (x ^ n <= 1) := by
  induction n with
  | zero => simp only [Rat.pow_zero]; constructor <;> native_decide
  | succ n ih =>
      rw [Rat.pow_succ]
      constructor
      · exact Rat.mul_nonneg ih.1 hx0
      · calc
          x ^ n * x <= 1 * x :=
            Rat.mul_le_mul_of_nonneg_right ih.2 hx0
          _ <= 1 := by grind

private theorem rat_unit_mul_bounds {a b : Rat}
    (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1) :
    (0 <= a * b) ∧ (a * b <= 1) := by
  constructor
  · exact Rat.mul_nonneg ha0 hb0
  · calc
      a * b <= 1 * b := Rat.mul_le_mul_of_nonneg_right ha1 hb0
      _ <= 1 := by grind

private theorem rat_one_le_pow {a : Rat} (ha : 1 <= a) (n : Nat) :
    1 <= a ^ n := by
  induction n with
  | zero => rw [Rat.pow_zero]; native_decide
  | succ n ih =>
      have h := rat_mul_le_mul_of_nonneg
        (a := 1) (b := a ^ n) (c := 1) (d := a)
        (by native_decide) ih (by native_decide) ha
      simpa [Rat.pow_succ] using h

private theorem tangentSquareRationalDerivative_difference_polynomial
    (p r : Rat) :
    (-1 + 6 * r * r - r ^ 4) * (1 + p * p) ^ 3 -
        (-1 + 6 * p * p - p ^ 4) * (1 + r * r) ^ 3 =
      (r - p) * (p + r) *
        (p ^ 4 * r ^ 4 - 6 * p ^ 4 * r ^ 2 + p ^ 4 -
          6 * p ^ 2 * r ^ 4 - 20 * p ^ 2 * r ^ 2 + 2 * p ^ 2 +
          r ^ 4 + 2 * r ^ 2 + 9) := by
  simp [Rat.pow_succ]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

private theorem tangentSquareRationalDerivative_polynomial_qabs_le
    {p r : Rat} (hp0 : 0 <= p) (hp1 : p <= 1)
    (hr0 : 0 <= r) (hr1 : r <= 1) :
    qabs (p ^ 4 * r ^ 4 - 6 * p ^ 4 * r ^ 2 + p ^ 4 -
      6 * p ^ 2 * r ^ 4 - 20 * p ^ 2 * r ^ 2 + 2 * p ^ 2 +
      r ^ 4 + 2 * r ^ 2 + 9) <= 48 := by
  have hp2 := rat_unit_pow_bounds hp0 hp1 2
  have hp4 := rat_unit_pow_bounds hp0 hp1 4
  have hr2 := rat_unit_pow_bounds hr0 hr1 2
  have hr4 := rat_unit_pow_bounds hr0 hr1 4
  have h1 := rat_unit_mul_bounds hp4.1 hp4.2 hr4.1 hr4.2
  have h2 := rat_unit_mul_bounds hp4.1 hp4.2 hr2.1 hr2.2
  have h3 := hp4
  have h4 := rat_unit_mul_bounds hp2.1 hp2.2 hr4.1 hr4.2
  have h5 := rat_unit_mul_bounds hp2.1 hp2.2 hr2.1 hr2.2
  have h6 := hp2
  have h7 := hr4
  have h8 := hr2
  apply qabs_le_of_neg_le_le <;> grind

private theorem tangentSquareRationalDerivative_difference_identity
    (p r : Rat) :
    tangentSquareRationalDerivative r - tangentSquareRationalDerivative p =
      ((r - p) * (p + r) *
        (p ^ 4 * r ^ 4 - 6 * p ^ 4 * r ^ 2 + p ^ 4 -
          6 * p ^ 2 * r ^ 4 - 20 * p ^ 2 * r ^ 2 + 2 * p ^ 2 +
          r ^ 4 + 2 * r ^ 2 + 9)) /
        ((1 + p * p) ^ 3 * (1 + r * r) ^ 3) := by
  have hp : 0 < 1 + p * p := by
    have h := rat_square_nonneg_basic p
    grind
  have hr : 0 < 1 + r * r := by
    have h := rat_square_nonneg_basic r
    grind
  let A : Rat := 1 + p * p
  let B : Rat := 1 + r * r
  let Dp : Rat := -1 + 6 * p * p - p ^ 4
  let Dr : Rat := -1 + 6 * r * r - r ^ 4
  let Q : Rat := p ^ 4 * r ^ 4 - 6 * p ^ 4 * r ^ 2 + p ^ 4 -
    6 * p ^ 2 * r ^ 4 - 20 * p ^ 2 * r ^ 2 + 2 * p ^ 2 +
    r ^ 4 + 2 * r ^ 2 + 9
  have hA : 0 < A := hp
  have hB : 0 < B := hr
  have hprod : 0 < A ^ 3 * B ^ 3 :=
    Rat.mul_pos (Rat.pow_pos hA) (Rat.pow_pos hB)
  have hA3 : (A ^ 3)⁻¹ * A ^ 3 = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.pow_pos hA))
  have hB3 : (B ^ 3)⁻¹ * B ^ 3 = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.pow_pos hB))
  have hfirst : (Dr * (B ^ 3)⁻¹) * (A ^ 3 * B ^ 3) = Dr * A ^ 3 := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hsecond : (Dp * (A ^ 3)⁻¹) * (A ^ 3 * B ^ 3) = Dp * B ^ 3 := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hdist (X Y Z : Rat) : (X - Y) * Z = X * Z - Y * Z := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
  rw [tangentSquareRationalDerivative, tangentSquareRationalDerivative]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  change (Dr * (B ^ 3)⁻¹ - Dp * (A ^ 3)⁻¹) =
    ((r - p) * (p + r) * Q) * (A ^ 3 * B ^ 3)⁻¹
  apply rat_eq_of_mul_eq_mul_pos_square hprod
  rw [hdist, hfirst, hsecond]
  have hright :
      ((r - p) * (p + r) * Q) * (A ^ 3 * B ^ 3)⁻¹ *
          (A ^ 3 * B ^ 3) = (r - p) * (p + r) * Q := by
    have hcancel : (A ^ 3 * B ^ 3)⁻¹ * (A ^ 3 * B ^ 3) = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hprod)
    grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hright]
  dsimp [A, B, Dp, Dr, Q] at *
  exact tangentSquareRationalDerivative_difference_polynomial p r

private theorem tangentSquareRationalDerivative_lipschitz_on_unit
    {p r : Rat} (hp0 : 0 <= p) (hp1 : p <= 1)
    (hr0 : 0 <= r) (hr1 : r <= 1) :
    qabs (tangentSquareRationalDerivative r -
      tangentSquareRationalDerivative p) <= 96 * qabs (r - p) := by
  have hdenpos : 0 < (1 + p * p) ^ 3 * (1 + r * r) ^ 3 := by
    have hp : 0 < 1 + p * p := by
      have h := rat_square_nonneg_basic p
      grind
    have hr : 0 < 1 + r * r := by
      have h := rat_square_nonneg_basic r
      grind
    exact Rat.mul_pos (Rat.pow_pos hp) (Rat.pow_pos hr)
  have hdenone : 1 <= (1 + p * p) ^ 3 * (1 + r * r) ^ 3 := by
    have hpone : 1 <= 1 + p * p := by
      have h := rat_square_nonneg_basic p
      grind
    have hrone : 1 <= 1 + r * r := by
      have h := rat_square_nonneg_basic r
      grind
    have hp3 := rat_one_le_pow hpone 3
    have hr3 := rat_one_le_pow hrone 3
    have h := rat_mul_le_mul_of_nonneg
      (a := 1) (b := (1 + p * p) ^ 3)
      (c := 1) (d := (1 + r * r) ^ 3)
      (by native_decide) hp3 (by native_decide) hr3
    simpa using h
  have hinv0 : (0 : Rat) <=
      ((1 + p * p) ^ 3 * (1 + r * r) ^ 3)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
  have hinvle : ((1 + p * p) ^ 3 * (1 + r * r) ^ 3)⁻¹ <= (1 : Rat) := by
    apply Rat.le_of_mul_le_mul_right
      (c := ((1 + p * p) ^ 3 * (1 + r * r) ^ 3 : Rat))
    · rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt hdenpos)]
      simpa using hdenone
    · exact hdenpos
  have hsum : qabs (p + r) <= 2 := by
    apply qabs_le_of_neg_le_le <;> grind
  have hpoly := tangentSquareRationalDerivative_polynomial_qabs_le
    hp0 hp1 hr0 hr1
  rw [tangentSquareRationalDerivative_difference_identity, Rat.div_def]
  rw [qabs_mul, qabs_mul, qabs_mul]
  have hdenabs : qabs ((1 + p * p) ^ 3 * (1 + r * r) ^ 3)⁻¹ <= 1 := by
    rw [qabs_eq_self_of_nonneg hinv0]
    exact hinvle
  calc
    qabs (r - p) * qabs (p + r) * qabs
          (p ^ 4 * r ^ 4 - 6 * p ^ 4 * r ^ 2 + p ^ 4 -
            6 * p ^ 2 * r ^ 4 - 20 * p ^ 2 * r ^ 2 + 2 * p ^ 2 +
            r ^ 4 + 2 * r ^ 2 + 9) *
          qabs ((1 + p * p) ^ 3 * (1 + r * r) ^ 3)⁻¹ <=
        qabs (r - p) * 2 * 48 * 1 := by
      calc
        qabs (r - p) * qabs (p + r) * qabs
              (p ^ 4 * r ^ 4 - 6 * p ^ 4 * r ^ 2 + p ^ 4 -
                6 * p ^ 2 * r ^ 4 - 20 * p ^ 2 * r ^ 2 + 2 * p ^ 2 +
                r ^ 4 + 2 * r ^ 2 + 9) *
              qabs ((1 + p * p) ^ 3 * (1 + r * r) ^ 3)⁻¹ =
            (qabs (r - p) * qabs (p + r)) *
              (qabs (p ^ 4 * r ^ 4 - 6 * p ^ 4 * r ^ 2 + p ^ 4 -
                6 * p ^ 2 * r ^ 4 - 20 * p ^ 2 * r ^ 2 + 2 * p ^ 2 +
                r ^ 4 + 2 * r ^ 2 + 9) *
                qabs ((1 + p * p) ^ 3 * (1 + r * r) ^ 3)⁻¹) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= (qabs (r - p) * 2) *
              (qabs (p ^ 4 * r ^ 4 - 6 * p ^ 4 * r ^ 2 + p ^ 4 -
                6 * p ^ 2 * r ^ 4 - 20 * p ^ 2 * r ^ 2 + 2 * p ^ 2 +
                r ^ 4 + 2 * r ^ 2 + 9) *
                qabs ((1 + p * p) ^ 3 * (1 + r * r) ^ 3)⁻¹) := by
          exact Rat.mul_le_mul_of_nonneg_right
            (Rat.mul_le_mul_of_nonneg_left hsum (qabs_nonneg (r - p)))
            (Rat.mul_nonneg (qabs_nonneg _) (qabs_nonneg _))
        _ <= (qabs (r - p) * 2) *
              (48 * qabs ((1 + p * p) ^ 3 * (1 + r * r) ^ 3)⁻¹) := by
          exact Rat.mul_le_mul_of_nonneg_left
            (Rat.mul_le_mul_of_nonneg_right hpoly (qabs_nonneg _))
            (Rat.mul_nonneg (qabs_nonneg _) (by native_decide))
        _ <= (qabs (r - p) * 2) * (48 * 1) := by
          exact Rat.mul_le_mul_of_nonneg_left
            (Rat.mul_le_mul_of_nonneg_left hdenabs (by native_decide))
            (Rat.mul_nonneg (qabs_nonneg _) (by native_decide))
        _ = qabs (r - p) * 2 * 48 * 1 := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = 96 * qabs (r - p) := by
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem tangentSquareRationalPart_secant_polynomial_qabs_le
    {p r : Rat} (hp0 : 0 <= p) (hp1 : p <= 1)
    (hr0 : 0 <= r) (hr1 : r <= 1) :
    qabs (p ^ 4 * r ^ 3 - p ^ 4 * r - 6 * p ^ 3 * r ^ 2 - 2 * p ^ 3 -
      6 * p ^ 2 * r ^ 3 - 6 * p ^ 2 * r + 2 * p * r ^ 2 + 6 * p +
      r ^ 3 + 3 * r) <= 34 := by
  have hp2 := rat_unit_pow_bounds hp0 hp1 2
  have hp3 := rat_unit_pow_bounds hp0 hp1 3
  have hp4 := rat_unit_pow_bounds hp0 hp1 4
  have hr2 := rat_unit_pow_bounds hr0 hr1 2
  have hr3 := rat_unit_pow_bounds hr0 hr1 3
  have h1 := rat_unit_mul_bounds hp4.1 hp4.2 hr3.1 hr3.2
  have h2 := rat_unit_mul_bounds hp4.1 hp4.2 hr0 hr1
  have h3 := rat_unit_mul_bounds hp3.1 hp3.2 hr2.1 hr2.2
  have h4 := hp3
  have h5 := rat_unit_mul_bounds hp2.1 hp2.2 hr3.1 hr3.2
  have h6 := rat_unit_mul_bounds hp2.1 hp2.2 hr0 hr1
  have h7 := rat_unit_mul_bounds hp0 hp1 hr2.1 hr2.2
  have h8 := hr3
  have h9 := hr0
  apply qabs_le_of_neg_le_le
  · grind
  · grind

private theorem tangentSquareRationalPart_secant_error_cleared
    {p r : Rat} (hpr : p < r) :
    ((tangentSquareRationalPart r - tangentSquareRationalPart p) /
        (r - p) - tangentSquareRationalDerivative p) *
        ((1 + p * p) ^ 3 * (1 + r * r) ^ 2) =
      (r - p) *
        (p ^ 4 * r ^ 3 - p ^ 4 * r - 6 * p ^ 3 * r ^ 2 - 2 * p ^ 3 -
          6 * p ^ 2 * r ^ 3 - 6 * p ^ 2 * r + 2 * p * r ^ 2 + 6 * p +
          r ^ 3 + 3 * r) := by
  have hp : 0 < 1 + p * p := by
    have h := rat_square_nonneg_basic p
    grind
  have hr : 0 < 1 + r * r := by
    have h := rat_square_nonneg_basic r
    grind
  let A : Rat := 1 + p * p
  let B : Rat := 1 + r * r
  let K : Rat := (p * r + 1) * (p * r - p - r - 1) *
    (p * r + p + r - 1)
  let D : Rat := -1 + 6 * p * p - p ^ 4
  let P : Rat :=
    p ^ 4 * r ^ 3 - p ^ 4 * r - 6 * p ^ 3 * r ^ 2 - 2 * p ^ 3 -
      6 * p ^ 2 * r ^ 3 - 6 * p ^ 2 * r + 2 * p * r ^ 2 + 6 * p +
      r ^ 3 + 3 * r
  have hA : 0 < A := by exact hp
  have hB : 0 < B := by exact hr
  have hA2 : (A ^ 2)⁻¹ * A ^ 2 = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.pow_pos hA))
  have hB2 : (B ^ 2)⁻¹ * B ^ 2 = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.pow_pos hB))
  have hA3 : (A ^ 3)⁻¹ * A ^ 3 = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.pow_pos hA))
  have hA23 : (A ^ 2)⁻¹ * A ^ 3 = A :=
    rat_inv_square_mul_cube hA
  have hprod : 0 < A ^ 3 * B ^ 2 :=
    Rat.mul_pos (Rat.pow_pos hA) (Rat.pow_pos hB)
  have hfirst : (-K * (A ^ 2 * B ^ 2)⁻¹) * (A ^ 3 * B ^ 2) = -K * A := by
    rw [Rat.inv_mul_rev]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hsecond : (D * (A ^ 3)⁻¹) * (A ^ 3 * B ^ 2) = D * B ^ 2 := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  rw [tangentSquareRationalPart_secant_identity hpr,
    tangentSquareRationalDerivative]
  rw [Rat.div_def, Rat.div_def]
  change (-K * (A ^ 2 * B ^ 2)⁻¹ - D * (A ^ 3)⁻¹) *
      (A ^ 3 * B ^ 2) = (r - p) * P
  have hdist (X Y Z : Rat) : (X - Y) * Z = X * Z - Y * Z := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
  rw [hdist]
  rw [hfirst, hsecond]
  dsimp [A, B, K, D, P] at *
  exact tangentSquareRationalPart_secant_error_polynomial p r

private theorem tangentSquareRationalPart_secant_error_qabs_le
    {p r : Rat} (hp0 : 0 <= p) (hp1 : p <= 1)
    (hpr : p < r) (hr1 : r <= 1) :
    qabs ((tangentSquareRationalPart r - tangentSquareRationalPart p) /
        (r - p) - tangentSquareRationalDerivative p) <=
      34 * (r - p) := by
  have hprle : p <= r := by grind
  have hr0 : 0 <= r := Rat.le_trans hp0 hprle
  have hW : 0 < r - p := by grind
  have hC0 : 0 < (1 + p * p) ^ 3 * (1 + r * r) ^ 2 := by
    have hp' : 0 < 1 + p * p := by
      have h := rat_square_nonneg_basic p
      grind
    have hr' : 0 < 1 + r * r := by
      have h := rat_square_nonneg_basic r
      grind
    exact Rat.mul_pos (Rat.pow_pos hp') (Rat.pow_pos hr')
  have hA1 : 1 <= 1 + p * p := by
    have h := rat_square_nonneg_basic p
    grind
  have hB1 : 1 <= 1 + r * r := by
    have h := rat_square_nonneg_basic r
    grind
  have hC1 : 1 <= (1 + p * p) ^ 3 * (1 + r * r) ^ 2 := by
    have hA3 := rat_one_le_pow hA1 3
    have hB2 := rat_one_le_pow hB1 2
    have h := rat_mul_le_mul_of_nonneg
      (a := 1) (b := (1 + p * p) ^ 3)
      (c := 1) (d := (1 + r * r) ^ 2)
      (by native_decide) hA3 (by native_decide) hB2
    simpa using h
  have hcleared := tangentSquareRationalPart_secant_error_cleared hpr
  have hP := tangentSquareRationalPart_secant_polynomial_qabs_le
    hp0 hp1 hr0 hr1
  have hq :
      qabs ((tangentSquareRationalPart r - tangentSquareRationalPart p) /
        (r - p) - tangentSquareRationalDerivative p) *
          ((1 + p * p) ^ 3 * (1 + r * r) ^ 2) =
        qabs ((r - p) *
          (p ^ 4 * r ^ 3 - p ^ 4 * r - 6 * p ^ 3 * r ^ 2 - 2 * p ^ 3 -
            6 * p ^ 2 * r ^ 3 - 6 * p ^ 2 * r + 2 * p * r ^ 2 + 6 * p +
            r ^ 3 + 3 * r)) := by
    calc
      qabs ((tangentSquareRationalPart r - tangentSquareRationalPart p) /
          (r - p) - tangentSquareRationalDerivative p) *
            ((1 + p * p) ^ 3 * (1 + r * r) ^ 2) =
          qabs (((tangentSquareRationalPart r - tangentSquareRationalPart p) /
            (r - p) - tangentSquareRationalDerivative p) *
            ((1 + p * p) ^ 3 * (1 + r * r) ^ 2)) := by
              rw [qabs_mul, qabs_eq_self_of_nonneg (Rat.le_of_lt hC0)]
      _ = qabs ((r - p) *
          (p ^ 4 * r ^ 3 - p ^ 4 * r - 6 * p ^ 3 * r ^ 2 - 2 * p ^ 3 -
            6 * p ^ 2 * r ^ 3 - 6 * p ^ 2 * r + 2 * p * r ^ 2 + 6 * p +
            r ^ 3 + 3 * r)) := by rw [hcleared]
  calc
    qabs ((tangentSquareRationalPart r - tangentSquareRationalPart p) /
        (r - p) - tangentSquareRationalDerivative p) <=
      qabs ((tangentSquareRationalPart r - tangentSquareRationalPart p) /
        (r - p) - tangentSquareRationalDerivative p) *
          ((1 + p * p) ^ 3 * (1 + r * r) ^ 2) := by
            have h := Rat.mul_le_mul_of_nonneg_left
              hC1 (qabs_nonneg
                ((tangentSquareRationalPart r - tangentSquareRationalPart p) /
                  (r - p) - tangentSquareRationalDerivative p))
            grind
    _ = qabs ((r - p) *
        (p ^ 4 * r ^ 3 - p ^ 4 * r - 6 * p ^ 3 * r ^ 2 - 2 * p ^ 3 -
          6 * p ^ 2 * r ^ 3 - 6 * p ^ 2 * r + 2 * p * r ^ 2 + 6 * p +
          r ^ 3 + 3 * r)) := hq
    _ = qabs (r - p) * qabs
        (p ^ 4 * r ^ 3 - p ^ 4 * r - 6 * p ^ 3 * r ^ 2 - 2 * p ^ 3 -
          6 * p ^ 2 * r ^ 3 - 6 * p ^ 2 * r + 2 * p * r ^ 2 + 6 * p +
          r ^ 3 + 3 * r) := by rw [qabs_mul]
    _ <= 34 * (r - p) := by
      rw [qabs_eq_self_of_nonneg (Rat.le_of_lt hW)]
      calc
        (r - p) * qabs
            (p ^ 4 * r ^ 3 - p ^ 4 * r - 6 * p ^ 3 * r ^ 2 - 2 * p ^ 3 -
              6 * p ^ 2 * r ^ 3 - 6 * p ^ 2 * r + 2 * p * r ^ 2 + 6 * p +
              r ^ 3 + 3 * r) <=
            (r - p) * 34 :=
          Rat.mul_le_mul_of_nonneg_left hP (Rat.le_of_lt hW)
        _ = 34 * (r - p) := Rat.mul_comm _ _

theorem tangentSquareRationalPart_difference_qabs_le
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    qabs (tangentSquareRationalPart r - tangentSquareRationalPart p) <=
      8 * (r - p) := by
  have hW : 0 <= r - p := by grind
  have hpr0 : 0 <= p * r := Rat.mul_nonneg hp0 (Rat.le_trans hp0 hpr)
  have hp1 : p <= 1 := Rat.le_trans hpr hr1
  have hpr1' : p * r <= 1 := by
    have h := Rat.mul_le_mul_of_nonneg_left hr1 hp0
    grind
  have hA0 : 0 <= p * r + 1 := by grind
  have hA2 : p * r + 1 <= 2 := by grind
  have hB0 : -2 <= p * r - p - r - 1 := by
    have hprod : 0 <= (1 - p) * (1 - r) := by
      exact Rat.mul_nonneg (by grind) (by grind)
    grind [Rat.mul_add, Rat.add_mul]
  have hB2 : p * r - p - r - 1 <= 2 := by grind
  have hC0 : -2 <= p * r + p + r - 1 := by grind
  have hC2 : p * r + p + r - 1 <= 2 := by grind
  have hDpos : 0 < (1 + p * p) ^ 2 * (1 + r * r) ^ 2 := by
    have hpden : 0 < 1 + p * p := by
      have h := rat_square_nonneg_basic p
      grind
    have hrden : 0 < 1 + r * r := by
      have h := rat_square_nonneg_basic r
      grind
    have hp2 : 0 < (1 + p * p) ^ 2 := by
      simpa [Rat.pow_succ] using Rat.mul_pos hpden hpden
    have hr2 : 0 < (1 + r * r) ^ 2 := by
      simpa [Rat.pow_succ] using Rat.mul_pos hrden hrden
    exact Rat.mul_pos hp2 hr2
  have hDone : 1 <= (1 + p * p) ^ 2 * (1 + r * r) ^ 2 := by
    have hpden : 1 <= (1 + p * p) ^ 2 := by
      have h := rat_square_nonneg_basic p
      have hone : 1 <= 1 + p * p := by grind
      calc
        1 = (1 : Rat) * 1 := by native_decide
        _ <= (1 + p * p) * 1 := Rat.mul_le_mul_of_nonneg_right hone (by native_decide)
        _ <= (1 + p * p) * (1 + p * p) :=
          Rat.mul_le_mul_of_nonneg_left hone (by grind)
        _ = (1 + p * p) ^ 2 := by simp [Rat.pow_succ]
    have hrden : 1 <= (1 + r * r) ^ 2 := by
      have h := rat_square_nonneg_basic r
      have hone : 1 <= 1 + r * r := by grind
      calc
        1 = (1 : Rat) * 1 := by native_decide
        _ <= (1 + r * r) * 1 := Rat.mul_le_mul_of_nonneg_right hone (by native_decide)
        _ <= (1 + r * r) * (1 + r * r) :=
          Rat.mul_le_mul_of_nonneg_left hone (by grind)
        _ = (1 + r * r) ^ 2 := by simp [Rat.pow_succ]
    calc
      1 = (1 : Rat) * 1 := by native_decide
      _ <= (1 + p * p) ^ 2 * 1 := by
        exact Rat.mul_le_mul_of_nonneg_right hpden (by native_decide)
      _ <= (1 + p * p) ^ 2 * (1 + r * r) ^ 2 :=
        Rat.mul_le_mul_of_nonneg_left hrden (by
          exact Rat.le_trans (by native_decide) hpden)
  have hDinv : (0 : Rat) <= ((1 + p * p) ^ 2 * (1 + r * r) ^ 2)⁻¹ := by
    exact Rat.le_of_lt ((Rat.inv_pos).2 hDpos)
  have hDinv_le : ((1 + p * p) ^ 2 * (1 + r * r) ^ 2)⁻¹ <= (1 : Rat) := by
    apply Rat.le_of_mul_le_mul_right
      (c := ((1 + p * p) ^ 2 * (1 + r * r) ^ 2 : Rat))
    · rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt hDpos)]
      simpa using hDone
    · exact hDpos
  rw [tangentSquareRationalPart_difference_identity, Rat.div_def]
  rw [qabs_mul, qabs_neg, qabs_mul, qabs_mul, qabs_mul,
    qabs_eq_self_of_nonneg hW]
  have hAabs : qabs (p * r + 1) <= 2 := by
    rw [qabs_eq_self_of_nonneg hA0]
    exact hA2
  have hBabs : qabs (p * r - p - r - 1) <= 2 :=
    qabs_le_of_neg_le_le hB0 hB2
  have hCabs : qabs (p * r + p + r - 1) <= 2 :=
    qabs_le_of_neg_le_le hC0 hC2
  have hDabs : qabs ((1 + p * p) ^ 2 * (1 + r * r) ^ 2)⁻¹ <= 1 := by
    rw [qabs_eq_self_of_nonneg hDinv]
    exact hDinv_le
  calc
    (r - p) * qabs (p * r + 1) *
        qabs (p * r - p - r - 1) *
        qabs (p * r + p + r - 1) *
        qabs ((1 + p * p) ^ 2 * (1 + r * r) ^ 2)⁻¹ <=
      (r - p) * 2 * 2 * 2 * 1 := by
        have hrest0 : 0 <=
            qabs (p * r - p - r - 1) *
              qabs (p * r + p + r - 1) *
              qabs ((1 + p * p) ^ 2 * (1 + r * r) ^ 2)⁻¹ := by
          exact Rat.mul_nonneg (Rat.mul_nonneg
            (qabs_nonneg _) (qabs_nonneg _)) (qabs_nonneg _)
        have hW2 : 0 <= (r - p) * 2 :=
          Rat.mul_nonneg hW (by native_decide)
        have hW22 : 0 <= (r - p) * 2 * 2 :=
          Rat.mul_nonneg hW2 (by native_decide)
        have hW222 : 0 <= (r - p) * 2 * 2 * 2 :=
          Rat.mul_nonneg hW22 (by native_decide)
        calc
          (r - p) * qabs (p * r + 1) *
              qabs (p * r - p - r - 1) *
              qabs (p * r + p + r - 1) *
              qabs ((1 + p * p) ^ 2 * (1 + r * r) ^ 2)⁻¹ <=
            (r - p) * 2 *
              qabs (p * r - p - r - 1) *
              qabs (p * r + p + r - 1) *
              qabs ((1 + p * p) ^ 2 * (1 + r * r) ^ 2)⁻¹ := by
                simpa [Rat.mul_assoc] using
                  Rat.mul_le_mul_of_nonneg_left
                    (Rat.mul_le_mul_of_nonneg_right hAabs hrest0) hW
          _ <= (r - p) * 2 * 2 *
              qabs (p * r + p + r - 1) *
              qabs ((1 + p * p) ^ 2 * (1 + r * r) ^ 2)⁻¹ := by
                simpa [Rat.mul_assoc] using
                  Rat.mul_le_mul_of_nonneg_left
                    (Rat.mul_le_mul_of_nonneg_right hBabs
                    (Rat.mul_nonneg (qabs_nonneg _)
                        (qabs_nonneg _))) hW2
          _ <= (r - p) * 2 * 2 * 2 *
              qabs ((1 + p * p) ^ 2 * (1 + r * r) ^ 2)⁻¹ := by
                simpa [Rat.mul_assoc] using
                  Rat.mul_le_mul_of_nonneg_left
                    (Rat.mul_le_mul_of_nonneg_right hCabs
                      (qabs_nonneg _))
                    hW22
          _ <= (r - p) * 2 * 2 * 2 * 1 := by
                simpa [Rat.mul_assoc] using
                  Rat.mul_le_mul_of_nonneg_left hDabs
                    hW222
    _ = 8 * (r - p) := by grind

def tangentSquareCorrectionRaw : RealFunRaw :=
  RealFunRaw.exact tangentSquareRationalPart

theorem tangentSquareCorrectionRaw_valid : tangentSquareCorrectionRaw.Valid :=
  RealFunRaw.exact_valid _

def tangentSquareCorrectionDerivativeRaw : RealFunRaw :=
  RealFunRaw.exact tangentSquareRationalDerivative

theorem tangentSquareCorrectionDerivativeRaw_valid :
    tangentSquareCorrectionDerivativeRaw.Valid :=
  RealFunRaw.exact_valid _

def tangentSquareCorrectionCommonBound
    (C : RationalSubinterval 0 1) : QInterval :=
  { lo := tangentSquareRationalDerivative C.lower - 96 * C.width,
    hi := tangentSquareRationalDerivative C.lower + 96 * C.width }

theorem tangentSquareCorrectionCommonBound_ordered
    (C : RationalSubinterval 0 1) :
    0 <= (tangentSquareCorrectionCommonBound C).width := by
  unfold tangentSquareCorrectionCommonBound QInterval.width
  have hw : 0 <= C.width := by
    unfold RationalSubinterval.width
    grind [C.ordered]
  grind

theorem tangentSquareCorrectionCommonBound_contains_derivative
    (C : RationalSubinterval 0 1) {x : Rat}
    (hx : C.contains x) :
    (tangentSquareCorrectionCommonBound C).ContainsInterval
      (tangentSquareCorrectionDerivativeRaw.compute x 0) := by
  have hC0 : 0 <= C.lower := C.lower_mem
  have hC1 : C.upper <= 1 := C.upper_mem
  have hxa : 0 <= x := Rat.le_trans hC0 hx.1
  have hxb : x <= 1 := Rat.le_trans hx.2 hC1
  have hLip := tangentSquareRationalDerivative_lipschitz_on_unit
    hC0 (Rat.le_trans C.ordered hC1) hxa hxb
  have hdist : qabs (x - C.lower) <= C.width := by
    rw [qabs_eq_self_of_nonneg (by grind [hx.1])]
    calc
      x - C.lower <= C.upper - C.lower := by grind [hx.2]
      _ = C.width := by rfl
  have hdiff : qabs (tangentSquareRationalDerivative x -
      tangentSquareRationalDerivative C.lower) <= 96 * C.width := by
    have hLip' : qabs (tangentSquareRationalDerivative x -
        tangentSquareRationalDerivative C.lower) <= 96 * qabs (x - C.lower) := by
      exact hLip
    exact Rat.le_trans hLip'
      (Rat.mul_le_mul_of_nonneg_left hdist (by native_decide))
  unfold tangentSquareCorrectionCommonBound QInterval.ContainsInterval
  change tangentSquareRationalDerivative C.lower - 96 * C.width <=
      tangentSquareRationalDerivative x /\
    tangentSquareRationalDerivative x <=
      tangentSquareRationalDerivative C.lower + 96 * C.width
  have hlow := neg_qabs_le_self
    (tangentSquareRationalDerivative x - tangentSquareRationalDerivative C.lower)
  have hhigh := self_le_qabs
    (tangentSquareRationalDerivative x - tangentSquareRationalDerivative C.lower)
  constructor <;> grind [Rat.sub_eq_add_neg]

def tangentSquareCorrectionBound : QInterval :=
  { lo := -8, hi := 8 }

theorem tangentSquareCorrectionBound_ordered :
    0 <= tangentSquareCorrectionBound.width := by
  native_decide

theorem tangentSquareCorrectionBound_contains_endpoint
    (C : RationalSubinterval 0 1) (n : Nat)
    (hstrict : C.lower < C.upper) :
    (C.scaleBound tangentSquareCorrectionBound).ContainsInterval
      (endpointDifferenceInterval tangentSquareCorrectionRaw
        C.lower C.upper n) := by
  have hwidth : 0 <= C.width := by
    unfold RationalSubinterval.width
    grind [C.ordered]
  have hqabs := tangentSquareRationalPart_difference_qabs_le
    C.lower_mem C.ordered C.upper_mem
  have hwEq : C.width = C.upper - C.lower := rfl
  have hprimitive :
      endpointDifferenceInterval tangentSquareCorrectionRaw
        C.lower C.upper n =
        { lo := tangentSquareRationalPart C.upper -
            tangentSquareRationalPart C.lower,
          hi := tangentSquareRationalPart C.upper -
            tangentSquareRationalPart C.lower } := by
    unfold endpointDifferenceInterval tangentSquareCorrectionRaw
      RealFunRaw.exact
    rfl
  rw [hprimitive]
  unfold RationalSubinterval.scaleBound tangentSquareCorrectionBound
    QInterval.scaleByRat
  simp only [if_pos hwidth]
  unfold QInterval.ContainsInterval
  have hlow := neg_qabs_le_self
    (tangentSquareRationalPart C.upper -
      tangentSquareRationalPart C.lower)
  have hhigh := self_le_qabs
    (tangentSquareRationalPart C.upper -
      tangentSquareRationalPart C.lower)
  constructor <;> grind [Rat.sub_eq_add_neg]

def tangentSquareCorrectionCenteredBound
    (C : RationalSubinterval 0 1) : QInterval :=
  { lo := tangentSquareRationalDerivative C.lower - 34 * C.width,
    hi := tangentSquareRationalDerivative C.lower + 34 * C.width }

theorem tangentSquareCorrectionCenteredBound_ordered
    (C : RationalSubinterval 0 1) :
    0 <= (tangentSquareCorrectionCenteredBound C).width := by
  unfold tangentSquareCorrectionCenteredBound QInterval.width
  have hwidth : 0 <= C.width := by
    unfold RationalSubinterval.width
    grind [C.ordered]
  grind

theorem tangentSquareCorrectionCenteredBound_contains_endpoint
    (C : RationalSubinterval 0 1) (n : Nat)
    (hstrict : C.lower < C.upper) :
    (C.scaleBound (tangentSquareCorrectionCenteredBound C)).ContainsInterval
      (endpointDifferenceInterval tangentSquareCorrectionRaw
        C.lower C.upper n) := by
  have hwidth : 0 < C.width := by
    unfold RationalSubinterval.width at *
    grind
  have hsec0 := tangentSquareRationalPart_secant_error_qabs_le
    C.lower_mem (Rat.le_trans C.ordered C.upper_mem) hstrict C.upper_mem
  have hwEq : C.width = C.upper - C.lower := rfl
  have hsec :
      qabs ((tangentSquareRationalPart C.upper -
        tangentSquareRationalPart C.lower) / C.width -
        tangentSquareRationalDerivative C.lower) <= 34 * C.width := by
    simpa only [hwEq] using hsec0
  have htransport :
      tangentSquareRationalPart C.upper - tangentSquareRationalPart C.lower -
          C.width * tangentSquareRationalDerivative C.lower =
        C.width *
          ((tangentSquareRationalPart C.upper -
            tangentSquareRationalPart C.lower) / C.width -
            tangentSquareRationalDerivative C.lower) := by
    rw [Rat.div_def]
    have hcancel : C.width⁻¹ * C.width = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hwidth)
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.sub_eq_add_neg]
  have herr :
      qabs (tangentSquareRationalPart C.upper -
        tangentSquareRationalPart C.lower -
          C.width * tangentSquareRationalDerivative C.lower) <=
        34 * C.width * C.width := by
    rw [htransport, qabs_mul,
      qabs_eq_self_of_nonneg (Rat.le_of_lt hwidth)]
    have h := Rat.mul_le_mul_of_nonneg_left hsec
      (Rat.le_of_lt hwidth)
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hprimitive :
      endpointDifferenceInterval tangentSquareCorrectionRaw
        C.lower C.upper n =
        { lo := tangentSquareRationalPart C.upper -
            tangentSquareRationalPart C.lower,
          hi := tangentSquareRationalPart C.upper -
            tangentSquareRationalPart C.lower } := by
    unfold endpointDifferenceInterval tangentSquareCorrectionRaw
      RealFunRaw.exact
    rfl
  rw [hprimitive]
  unfold RationalSubinterval.scaleBound
    tangentSquareCorrectionCenteredBound QInterval.scaleByRat
  simp only [if_pos (Rat.le_of_lt hwidth)]
  unfold QInterval.ContainsInterval
  have hlow := neg_qabs_le_self
    (tangentSquareRationalPart C.upper - tangentSquareRationalPart C.lower -
      C.width * tangentSquareRationalDerivative C.lower)
  have hhigh := self_le_qabs
    (tangentSquareRationalPart C.upper - tangentSquareRationalPart C.lower -
      C.width * tangentSquareRationalDerivative C.lower)
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem tangentSquareCorrectionCommonBound_contains_endpoint
    (C : RationalSubinterval 0 1) (n : Nat)
    (hstrict : C.lower < C.upper) :
    (C.scaleBound (tangentSquareCorrectionCommonBound C)).ContainsInterval
      (endpointDifferenceInterval tangentSquareCorrectionRaw
        C.lower C.upper n) := by
  have hcenter := tangentSquareCorrectionCenteredBound_contains_endpoint
    C n hstrict
  have hw : 0 < C.width := by
    unfold RationalSubinterval.width at *
    grind
  unfold QInterval.ContainsInterval at hcenter ⊢
  unfold RationalSubinterval.scaleBound tangentSquareCorrectionCenteredBound
    QInterval.scaleByRat at hcenter
  unfold RationalSubinterval.scaleBound tangentSquareCorrectionCommonBound
    QInterval.scaleByRat at ⊢
  simp only [if_pos (Rat.le_of_lt hw)] at hcenter ⊢
  have hleft : C.width *
      (tangentSquareRationalDerivative C.lower - 96 * C.width) <=
      C.width *
        (tangentSquareRationalDerivative C.lower - 34 * C.width) := by
    have hcoef : tangentSquareRationalDerivative C.lower - 96 * C.width <=
        tangentSquareRationalDerivative C.lower - 34 * C.width := by
      grind [Rat.sub_eq_add_neg]
    exact Rat.mul_le_mul_of_nonneg_left hcoef (Rat.le_of_lt hw)
  have hright : C.width *
      (tangentSquareRationalDerivative C.lower + 34 * C.width) <=
      C.width *
        (tangentSquareRationalDerivative C.lower + 96 * C.width) := by
    have hcoef : tangentSquareRationalDerivative C.lower + 34 * C.width <=
        tangentSquareRationalDerivative C.lower + 96 * C.width := by
      grind
    exact Rat.mul_le_mul_of_nonneg_left hcoef (Rat.le_of_lt hw)
  exact ⟨Rat.le_trans hleft hcenter.1, Rat.le_trans hcenter.2 hright⟩

def tangentSquareCorrectionCenteredPartition (eps : QPos) :
    RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (68 * (eps.val.den + 1))
    (by omega) (by native_decide)

theorem tangentSquareCorrectionCenteredPartition_cell_strict
    (eps : QPos) {k : Nat}
    (hk : k < (tangentSquareCorrectionCenteredPartition eps).pieces) :
    ((tangentSquareCorrectionCenteredPartition eps).cell k hk).lower <
      ((tangentSquareCorrectionCenteredPartition eps).cell k hk).upper := by
  have hpos : 0 < mesh 0 1 (68 * (eps.val.den + 1)) := by
    change 0 < mesh 0 1 (68 * (eps.val.den + 1))
    unfold mesh
    rw [if_neg (by omega : 68 * (eps.val.den + 1) ≠ 0)]
    rw [Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 (Rat.natCast_pos.mpr (by omega)))
  have hw : 0 <
      ((tangentSquareCorrectionCenteredPartition eps).cell k hk).width := by
    change 0 < ((RationalPartition.uniform 0 1
      (68 * (eps.val.den + 1)) (by omega) (by native_decide)).cell k hk).width
    rw [RationalPartition.uniform_cell_width 0 1
      (68 * (eps.val.den + 1)) (by omega) (by native_decide) k hk]
    exact hpos
  unfold RationalSubinterval.width at hw
  exact by grind

theorem tangentSquareCorrectionCenteredUniformBoundSum_width_le
    (eps : QPos) :
    ((tangentSquareCorrectionCenteredPartition eps).boundIntegralSum
      (fun k hk =>
        (tangentSquareCorrectionCenteredPartition eps).cell k hk |>.scaleBound
          (tangentSquareCorrectionCenteredBound
            ((tangentSquareCorrectionCenteredPartition eps).cell k hk)))).width <=
      eps.val := by
  let P := tangentSquareCorrectionCenteredPartition eps
  have hbound : forall k (hk : k < P.pieces),
      ((P.cell k hk).scaleBound
          (tangentSquareCorrectionCenteredBound (P.cell k hk))).width <=
        68 * mesh 0 1 P.pieces * (P.cell k hk).width := by
    intro k hk
    have hcell : (P.cell k hk).width = mesh 0 1 P.pieces := by
      change ((RationalPartition.uniform 0 1
        (68 * (eps.val.den + 1)) (by omega) (by native_decide)).cell k hk).width =
        mesh 0 1 (68 * (eps.val.den + 1))
      rw [RationalPartition.uniform_cell_width 0 1
        (68 * (eps.val.den + 1)) (by omega) (by native_decide) k hk]
    have hw : 0 <= (P.cell k hk).width := by
      unfold RationalSubinterval.width
      grind [P.cell k hk |>.ordered]
    unfold RationalSubinterval.scaleBound
      tangentSquareCorrectionCenteredBound QInterval.scaleByRat
    simp only [if_pos hw]
    unfold QInterval.width
    rw [hcell]
    grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]
  have hsum := RationalPartition.uniform_boundIntegralSum_width_le
    P.pieces P.positive (show (0 : Rat) <= 1 by native_decide)
    (fun k hk =>
      (P.cell k hk).scaleBound
        (tangentSquareCorrectionCenteredBound (P.cell k hk)))
    (68 * mesh 0 1 P.pieces * mesh 0 1 P.pieces) (by
      intro k hk
      have h := hbound k hk
      have hcell' : (P.cell k hk).width = mesh 0 1 P.pieces := by
        change ((RationalPartition.uniform 0 1
          (68 * (eps.val.den + 1)) (by omega) (by native_decide)).cell k hk).width =
          mesh 0 1 (68 * (eps.val.den + 1))
        rw [RationalPartition.uniform_cell_width 0 1
          (68 * (eps.val.den + 1)) (by omega) (by native_decide) k hk]
      rw [hcell'] at h
      exact h)
  change ((P.boundIntegralSum
    (fun k hk =>
      (P.cell k hk).scaleBound
        (tangentSquareCorrectionCenteredBound (P.cell k hk)))).width <=
    (1 - 0) * (68 * mesh 0 1 P.pieces * mesh 0 1 P.pieces)) at hsum
  change ((P.boundIntegralSum
    (fun k hk =>
      (P.cell k hk).scaleBound
        (tangentSquareCorrectionCenteredBound (P.cell k hk)))).width <=
    eps.val)
  have hmesh : mesh 0 1 P.pieces =
      1 / (((68 * (eps.val.den + 1) : Nat) : Rat)) := by
    change mesh 0 1 (68 * (eps.val.den + 1)) = _
    unfold mesh
    rw [if_neg (by omega : 68 * (eps.val.den + 1) ≠ 0)]
    rw [Rat.div_def, Rat.natCast_mul, Rat.natCast_add]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hone : 1 / (((eps.val.den + 1 : Nat) : Rat)) <= eps.val :=
    FTC.one_div_den_succ_le_of_pos eps.property
  rw [hmesh] at hsum
  have hmesh0 : 0 <=
      (1 / (((68 * (eps.val.den + 1) : Nat) : Rat))) := by
    have hn : 0 < 68 * (eps.val.den + 1) := by omega
    exact Rat.le_of_lt (one_div_nat_pos hn)
  have hmesh_le_one :
      1 / (((68 * (eps.val.den + 1) : Nat) : Rat)) <= 1 := by
    have h := FTC.one_div_nat_antitone
      (n := 1) (m := 68 * (eps.val.den + 1))
      (by native_decide) (by omega) (by omega)
    have hone : (1 : Rat)⁻¹ = 1 := by native_decide
    simpa [Rat.div_def, hone] using h
  have hNpos : 0 < (((68 * (eps.val.den + 1) : Nat) : Rat)) :=
    (Rat.natCast_pos).2 (by omega)
  have hscaled :
      68 * (1 / (((68 * (eps.val.den + 1) : Nat) : Rat))) *
          (1 / (((68 * (eps.val.den + 1) : Nat) : Rat))) <=
    68 * (1 / (((68 * (eps.val.den + 1) : Nat) : Rat))) := by
    have h := Rat.mul_le_mul_of_nonneg_left hmesh_le_one
      (Rat.mul_nonneg (show (0 : Rat) <= 68 by native_decide) hmesh0)
    simpa [Rat.mul_assoc] using h
  have h68mesh :
    68 * (1 / (((68 * (eps.val.den + 1) : Nat) : Rat))) =
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    rw [Rat.div_def, Rat.div_def, Rat.natCast_mul, Rat.natCast_add]
    have hNpos' : 0 < (eps.val.den : Rat) + 1 := by
      have hnonneg : 0 <= (eps.val.den : Rat) := Rat.natCast_nonneg
      grind
    have hden : (68 : Rat) * ((eps.val.den : Rat) + 1) ≠ 0 :=
      Rat.ne_of_gt (Rat.mul_pos (by native_decide) hNpos')
    have hden' : (eps.val.den : Rat) + 1 ≠ 0 := Rat.ne_of_gt hNpos'
    rw [Rat.inv_mul_rev]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
  have hsum' :
      (P.boundIntegralSum
        (fun k hk =>
          (P.cell k hk).scaleBound
            (tangentSquareCorrectionCenteredBound (P.cell k hk)))).width <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    calc
      (P.boundIntegralSum
          (fun k hk =>
            (P.cell k hk).scaleBound
              (tangentSquareCorrectionCenteredBound (P.cell k hk)))).width <=
          (1 - 0) *
            (68 * (1 / (((68 * (eps.val.den + 1) : Nat) : Rat))) *
              (1 / (((68 * (eps.val.den + 1) : Nat) : Rat)))) := by
                simpa using hsum
      _ <= 68 * (1 / (((68 * (eps.val.den + 1) : Nat) : Rat))) := by
        have honezero : (1 - 0 : Rat) = 1 := by grind
        rw [honezero]
        simpa [Rat.one_mul, Rat.mul_assoc] using hscaled
      _ = 1 / (((eps.val.den + 1 : Nat) : Rat)) := h68mesh
  exact Rat.le_trans hsum' hone

/- The tangent-coordinate primitive is the arctangent geometry evaluator plus
the rational correction from the decomposition above.  The correction is
kept as an exact rational function, so this is a genuine computable function
object rather than only a symbolic antiderivative. -/
def tangentSquareRationalPrimitive (u : Rat) : Rat :=
  tangentSquareRationalPart u

def tangentSquarePrimitiveOnUnit : RealFunRaw :=
  RealFunRaw.add IntegralIdentities.arctanGeomOnUnit.toRealFunRaw
    (RealFunRaw.exact tangentSquareRationalPrimitive)

theorem tangentSquarePrimitiveOnUnit_valid :
    tangentSquarePrimitiveOnUnit.Valid := by
  apply RealFunRaw.add_valid
  · exact FunctionOnInterval.toRealFunRaw_valid IntegralIdentities.arctanGeomOnUnit
  · exact RealFunRaw.exact_valid tangentSquareRationalPrimitive

theorem endpointDifferenceInterval_add_contains
    (F G : RealFunRaw) (p r : Rat) (n : Nat) :
    (QInterval.addInterval
      (endpointDifferenceInterval F p r n)
      (endpointDifferenceInterval G p r n)).ContainsInterval
      (endpointDifferenceInterval (RealFunRaw.add F G) p r n) := by
  unfold endpointDifferenceInterval RealFunRaw.add
    QInterval.addInterval QInterval.ContainsInterval
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

def tangentSquareCombinedDerivativeRaw : RealFunRaw :=
  RealFunRaw.add Integral.arctanKernelRaw tangentSquareCorrectionDerivativeRaw

theorem tangentSquareCombinedDerivativeRaw_valid :
    tangentSquareCombinedDerivativeRaw.Valid := by
  apply RealFunRaw.add_valid
  · exact RealFunRaw.exact_valid _
  · exact tangentSquareCorrectionDerivativeRaw_valid

theorem tangentSquareCombinedDerivativeRaw_compute_eq_density
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    tangentSquareCombinedDerivativeRaw.compute x n =
      tangentSquareDensityRaw.compute x n := by
  unfold tangentSquareCombinedDerivativeRaw tangentSquareDensityRaw
    RealFunRaw.add Integral.arctanKernelRaw
    tangentSquareCorrectionDerivativeRaw RealFunRaw.exact
  change QInterval.mk
      (1 / (1 + x * x) + tangentSquareRationalDerivative x)
      (1 / (1 + x * x) + tangentSquareRationalDerivative x) =
    QInterval.mk (tangentSquareDensity x) (tangentSquareDensity x)
  rw [tangentSquareDensity_decomposition]

def tangentSquareCombinedDerivativeCellControl
    (C : RationalSubinterval 0 1) (δ η : QPos) (N : Nat)
    (hC : 0 < C.width) (hη : η.val = C.width * δ.val / 3)
    (hN : 256 * (η.val.den + 1) <= N) :
    CandidateDerivativeCellControl
      (RealFunRaw.add Integral.arctanPrimitiveRaw tangentSquareCorrectionRaw)
      tangentSquareCombinedDerivativeRaw C := by
  exact {
    bound := fun _ => QInterval.addInterval
      (Integral.arctanKernelPaddedBound C δ.val N)
      (tangentSquareCorrectionCommonBound C)
    derivativeEvalPrecision := fun _ => 0
    endpointPrecision := fun _ => N
    primitive_domain_lower := by
      unfold RealFunRaw.add Integral.arctanPrimitiveRaw
        tangentSquareCorrectionRaw RealFunRaw.exact
      exact ⟨⟨C.lower_mem, Rat.le_trans C.ordered C.upper_mem⟩, trivial⟩
    primitive_domain_upper := by
      unfold RealFunRaw.add Integral.arctanPrimitiveRaw
        tangentSquareCorrectionRaw RealFunRaw.exact
      exact ⟨⟨Rat.le_trans C.lower_mem C.ordered, C.upper_mem⟩, trivial⟩
    candidate_domain_on := fun _ _ => by
      constructor <;> trivial
    bound_ordered := fun _ => by
      unfold QInterval.addInterval QInterval.width
      have ha := Integral.arctanKernelPaddedBound_ordered C δ.val
        (Rat.le_of_lt δ.property) N
      have hc := tangentSquareCorrectionCommonBound_ordered C
      change 0 <=
        ((Integral.arctanKernelPaddedBound C δ.val N).hi +
            (tangentSquareCorrectionCommonBound C).hi) -
          ((Integral.arctanKernelPaddedBound C δ.val N).lo +
            (tangentSquareCorrectionCommonBound C).lo)
      unfold QInterval.width at ha hc
      grind [Rat.sub_eq_add_neg]
    candidate_contained := fun _ x hx => by
      have ha := Integral.arctanKernelPaddedBound_contains C δ.val
        (Rat.le_of_lt δ.property) N hx
      have hc := tangentSquareCorrectionCommonBound_contains_derivative C hx
      have hadd := QInterval.addInterval_contains ha hc
      simpa [tangentSquareCombinedDerivativeRaw, RealFunRaw.add,
        Integral.arctanKernelRaw, tangentSquareCorrectionDerivativeRaw,
        RealFunRaw.exact, QInterval.addInterval] using hadd
    endpoint_difference_contained := fun _ => by
      have ha := Integral.arctanKernelPaddedBound_local_endpoint_contains
        C δ η N hC hη hN
      have hstrict : C.lower < C.upper := by
        unfold RationalSubinterval.width at hC
        grind
      have hc := tangentSquareCorrectionCommonBound_contains_endpoint
        C N hstrict
      have hadd := QInterval.addInterval_contains ha hc
      have hsum := hadd.trans (endpointDifferenceInterval_add_contains
        Integral.arctanPrimitiveRaw tangentSquareCorrectionRaw
        C.lower C.upper N)
      have hscale :
          C.scaleBound (QInterval.addInterval
            (Integral.arctanKernelPaddedBound C δ.val N)
            (tangentSquareCorrectionCommonBound C)) =
          QInterval.addInterval
            (C.scaleBound (Integral.arctanKernelPaddedBound C δ.val N))
            (C.scaleBound (tangentSquareCorrectionCommonBound C)) := by
        unfold RationalSubinterval.scaleBound QInterval.scaleByRat
          QInterval.addInterval
        simp only [if_pos (Rat.le_of_lt hC)]
        apply (QInterval.mk.injEq _ _ _ _).mpr
        constructor <;> grind [Rat.mul_add]
      rw [hscale]
      exact hsum }

def tangentSquareFTCPartition (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (256 * (eps.val.den + 1))
    (by omega) (by native_decide)

def tangentSquareFTCPadding (eps : QPos) : QPos :=
  { val := eps.val / 64
    property := by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide)) }

def tangentSquareFTCStageBudget (eps : QPos) : QPos :=
  let P := tangentSquareFTCPartition eps
  let δ := tangentSquareFTCPadding eps
  { val := mesh 0 1 P.pieces * δ.val / 3
    property := by
      have hP : 0 < P.pieces := P.positive
      have hmesh : 0 < mesh 0 1 P.pieces := by
        unfold mesh
        rw [if_neg (Nat.ne_of_gt hP), Rat.div_def]
        exact Rat.mul_pos (by native_decide)
          ((Rat.inv_pos).2 (by exact_mod_cast hP))
      rw [Rat.div_def]
      exact Rat.mul_pos (Rat.mul_pos hmesh δ.property)
        ((Rat.inv_pos).2 (by native_decide)) }

theorem tangentSquareFTCStageBudget_le (eps : QPos) :
    (tangentSquareFTCStageBudget eps).val <= eps.val := by
  dsimp [tangentSquareFTCStageBudget]
  let P := tangentSquareFTCPartition eps
  have hpieces : 0 < P.pieces := P.positive
  have hmesh : mesh 0 1 P.pieces <= 1 := by
    unfold mesh
    rw [if_neg (Nat.ne_of_gt hpieces), Rat.div_def]
    have hden : (1 : Rat) <= (P.pieces : Rat) := by
      exact_mod_cast hpieces
    have hpos : 0 < (P.pieces : Rat) := by
      exact_mod_cast hpieces
    apply Rat.le_of_mul_le_mul_right (c := (P.pieces : Rat))
    · have hc := Rat.inv_mul_cancel _ (Rat.ne_of_gt hpos)
      grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hpos
  have hδ : (tangentSquareFTCPadding eps).val = eps.val / 64 := rfl
  have hδnonneg : 0 <= (tangentSquareFTCPadding eps).val :=
    Rat.le_of_lt (tangentSquareFTCPadding eps).property
  have hprod := Rat.mul_le_mul_of_nonneg_right hmesh hδnonneg
  dsimp [tangentSquareFTCPadding] at hprod ⊢
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

private theorem den_add_one_ge_of_pos_le_inv
    {q r : Rat} (hq : 0 < q) (hr : 0 < r) (hqr : q <= 1 / r) :
    r <= ((q.den + 1 : Nat) : Rat) := by
  let d : Rat := ((q.den + 1 : Nat) : Rat)
  have hd : 0 < d := by
    dsimp [d]
    exact Rat.natCast_pos.mpr (Nat.succ_pos q.den)
  have hden := FTC.one_div_den_succ_le_of_pos hq
  have hle : 1 / d <= 1 / r := Rat.le_trans hden hqr
  have h1 := Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt hd)
  have h2 := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hr)
  have hdne : d ≠ 0 := Rat.ne_of_gt hd
  have hrne : r ≠ 0 := Rat.ne_of_gt hr
  rw [Rat.div_def, Rat.div_def] at h2
  simp only [Rat.one_mul] at h2
  have h2' : r * (d * d⁻¹) ≤ r * (r⁻¹ * d) := by
    simpa [Rat.mul_assoc, Rat.mul_comm] using h2
  have hdd : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
  have hrr : r * r⁻¹ = 1 := Rat.mul_inv_cancel r hrne
  calc
    r = r * (d * d⁻¹) := by rw [hdd, Rat.mul_one]
    _ ≤ r * (r⁻¹ * d) := h2'
    _ = d := by rw [← Rat.mul_assoc, hrr, Rat.one_mul]

def tangentSquareFTCEndpointStage (eps : QPos) : Nat :=
  256 * ((tangentSquareFTCStageBudget eps).val.den + 1)

theorem tangentSquareEndpointStage_ge (n : Nat) :
    n <= tangentSquareFTCEndpointStage (precisionAtStage n) := by
  by_cases hn : n = 0
  · simp [hn, tangentSquareFTCEndpointStage]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let eps := precisionAtStage n
    let η := tangentSquareFTCStageBudget eps
    have hηpos : 0 < η.val := η.property
    have hnrpos : 0 < (n : Rat) / 256 := by
      rw [Rat.div_def]
      exact Rat.mul_pos (by exact_mod_cast hnpos)
        ((Rat.inv_pos).2 (by native_decide))
    have hηle : η.val <= 1 / ((n : Rat) / 256) := by
      have hle := tangentSquareFTCStageBudget_le eps
      have hle' : η.val <= 1 / (n : Rat) := by
        simpa [η, eps, precisionAtStage, hn] using hle
      have hnR : (n : Rat) ≠ 0 := by exact_mod_cast hn
      have hn256 : (n : Rat) * (256 : Rat)⁻¹ ≠ 0 := by
        intro hzero
        rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
        · exact hnR hzero
        · exact (by native_decide : (256 : Rat)⁻¹ ≠ 0) hzero
      have hstep : 1 / (n : Rat) <= 1 / ((n : Rat) / 256) := by
        rw [Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      exact Rat.le_trans hle' hstep
    have hden := den_add_one_ge_of_pos_le_inv hηpos hnrpos hηle
    dsimp [tangentSquareFTCEndpointStage, η]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hden (by native_decide : (0 : Rat) <= 256)
    have h256 : (256 : Rat) ≠ 0 := by native_decide
    have hid : (n : Rat) = 256 * ((n : Rat) / 256) := by
      rw [Rat.div_def]
      calc
        (n : Rat) = (n : Rat) * ((256 : Rat) * (256 : Rat)⁻¹) := by
          grind [Rat.mul_inv_cancel]
        _ = 256 * ((n : Rat) * (256 : Rat)⁻¹) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    have hscaled' : (n : Rat) <=
        256 * ((η.val.den + 1 : Nat) : Rat) := by
      rw [hid]
      exact hscaled
    have hnat : n <= 256 * (η.val.den + 1) := by
      exact_mod_cast hscaled'
    change n <= 256 * (η.val.den + 1)
    exact hnat

theorem tangentSquareFTC_endpoint_width_le (eps : QPos) :
    (endpointDifferenceInterval
      (RealFunRaw.add Integral.arctanPrimitiveRaw tangentSquareCorrectionRaw)
      0 1 (tangentSquareFTCEndpointStage eps)).width <= eps.val := by
  let η := tangentSquareFTCStageBudget eps
  let N := tangentSquareFTCEndpointStage eps
  have hN : 256 * (η.val.den + 1) = N := by rfl
  have hNrect : 4 * (η.val.den + 1) <= N := by
    rw [← hN]
    omega
  have hzero := ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
    (x := (0 : Rat)) (by native_decide) (by native_decide) η N hNrect
  have hone := ArctanGeometry.arctanIntegralRectangleCompute_width_le_eps_of_precision
    (x := (1 : Rat)) (by native_decide) (by native_decide) η N hNrect
  have hsum :
      (ArctanGeometry.arctanIntegralRectangleCompute 0 N).width +
        (ArctanGeometry.arctanIntegralRectangleCompute 1 N).width <=
      2 * η.val := by
    have h := rat_add_le_add hzero hone
    grind
  have hη : 2 * η.val <= eps.val := by
    dsimp [η, tangentSquareFTCStageBudget]
    have hpieces : 0 < (tangentSquareFTCPartition eps).pieces :=
      (tangentSquareFTCPartition eps).positive
    have hmesh1 : mesh 0 1 (tangentSquareFTCPartition eps).pieces <= 1 := by
      change mesh 0 1 (256 * (eps.val.den + 1)) <= 1
      unfold mesh
      rw [if_neg (by omega : 256 * (eps.val.den + 1) ≠ 0), Rat.div_def]
      rw [Rat.natCast_mul, Rat.natCast_add]
      have hden : (1 : Rat) <=
          (256 : Rat) * ((eps.val.den + 1 : Nat) : Rat) := by
        have hd : (1 : Rat) <= ((eps.val.den + 1 : Nat) : Rat) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le eps.val.den))
        grind
      apply Rat.le_of_mul_le_mul_right
        (c := (256 : Rat) * ((eps.val.den + 1 : Nat) : Rat))
      · have hcancel :
            ((256 : Rat) * ((eps.val.den + 1 : Nat) : Rat))⁻¹ *
              (256 * ((eps.val.den + 1 : Nat) : Rat)) = 1 :=
          Rat.inv_mul_cancel _ (Rat.ne_of_gt
            (Rat.mul_pos (by native_decide)
              (Rat.natCast_pos.mpr (by omega))))
        grind [Rat.mul_assoc, Rat.mul_comm]
      · exact Rat.mul_pos (by native_decide)
          (Rat.natCast_pos.mpr (by omega))
    have hmesh : 0 <= mesh 0 1 (tangentSquareFTCPartition eps).pieces :=
      mesh_nonneg_of_le (tangentSquareFTCPartition eps).positive
        (by native_decide)
    have hδ : 0 <= (tangentSquareFTCPadding eps).val :=
      Rat.le_of_lt (tangentSquareFTCPadding eps).property
    have hprodle := Rat.mul_le_mul_of_nonneg_right hmesh1 hδ
    have hinv3 : 0 <= (3 : Rat)⁻¹ :=
      Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide))
    have hscaled := Rat.mul_le_mul_of_nonneg_right hprodle hinv3
    dsimp [tangentSquareFTCPadding] at hscaled ⊢
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  have hzeroCompute :
      (RealFunRaw.add Integral.arctanPrimitiveRaw tangentSquareCorrectionRaw).compute
          0 (tangentSquareFTCEndpointStage eps) =
        Integral.arctanPrimitiveRaw.compute 0
          (tangentSquareFTCEndpointStage eps) := by
    simp [RealFunRaw.add, Integral.arctanPrimitiveRaw,
      tangentSquareCorrectionRaw, RealFunRaw.exact,
      tangentSquareRationalPart_zero,
      ArctanGeometry.arctanIntegralRectangleRaw,
      ArctanGeometry.arctanIntegralRectangleCompute,
      ArctanGeometry.integralSumInterval]
    constructor <;> grind
  have honeCompute :
      (RealFunRaw.add Integral.arctanPrimitiveRaw tangentSquareCorrectionRaw).compute
          1 (tangentSquareFTCEndpointStage eps) =
        Integral.arctanPrimitiveRaw.compute 1
          (tangentSquareFTCEndpointStage eps) := by
    simp [RealFunRaw.add, Integral.arctanPrimitiveRaw,
      tangentSquareCorrectionRaw, RealFunRaw.exact,
      tangentSquareRationalPart_one,
      ArctanGeometry.arctanIntegralRectangleRaw,
      ArctanGeometry.arctanIntegralRectangleCompute,
      ArctanGeometry.integralSumInterval]
    constructor <;> grind
  rw [endpointDifferenceInterval_width]
  rw [hzeroCompute, honeCompute]
  change (ArctanGeometry.arctanIntegralRectangleCompute 0 N).width +
      (ArctanGeometry.arctanIntegralRectangleCompute 1 N).width <= eps.val
  exact Rat.le_trans hsum hη

def tangentSquareFTC_cellControl (eps : QPos) {k : Nat}
    (hk : k < (tangentSquareFTCPartition eps).pieces) :
    CandidateDerivativeCellControl
      (RealFunRaw.add Integral.arctanPrimitiveRaw tangentSquareCorrectionRaw)
      tangentSquareCombinedDerivativeRaw
      ((tangentSquareFTCPartition eps).cell k hk) := by
  let P := tangentSquareFTCPartition eps
  let δ := tangentSquareFTCPadding eps
  let η := tangentSquareFTCStageBudget eps
  let N := tangentSquareFTCEndpointStage eps
  let C := P.cell k hk
  have hcell : C.width = mesh 0 1 P.pieces := by
    dsimp [C]
    exact RationalPartition.uniform_cell_width 0 1 P.pieces
      P.positive (by native_decide) k hk
  have hC : 0 < C.width := by
    rw [hcell]
    change 0 < mesh 0 1 (256 * (eps.val.den + 1))
    unfold mesh
    have hpieces : 0 < 256 * (eps.val.den + 1) := by omega
    rw [if_neg (Nat.ne_of_gt hpieces), Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 (by exact_mod_cast P.positive))
  have hη : η.val = C.width * δ.val / 3 := by
    dsimp [η, tangentSquareFTCStageBudget, δ]
    change mesh 0 1 P.pieces * δ.val / 3 = C.width * δ.val / 3
    rw [hcell]
  have hN : 256 * (η.val.den + 1) <= N := by
    dsimp [N, tangentSquareFTCEndpointStage]
    exact Nat.le_refl _
  simpa [P, δ, η, N, C] using
    tangentSquareCombinedDerivativeCellControl C δ η N hC hη hN

theorem tangentSquareFTC_riemann_width_le (eps : QPos) :
    ((tangentSquareFTCPartition eps).boundIntegralSum
      (fun k hk =>
        (tangentSquareFTC_cellControl eps hk).bound 0)).width <= eps.val := by
  let P := tangentSquareFTCPartition eps
  let δ := tangentSquareFTCPadding eps
  let W := mesh 0 1 P.pieces
  let E : Rat := W + W * W + 2 * δ.val + 192 * W
  have hsum := RationalPartition.uniform_boundIntegralSum_width_le
    P.pieces P.positive (by native_decide : (0 : Rat) <= 1)
      (fun k hk => (tangentSquareFTC_cellControl eps hk).bound 0) E (by
        intro k hk
        let C := P.cell k hk
        have hcell : C.width = W := by
          dsimp [C, W, P]
          exact RationalPartition.uniform_cell_width 0 1
            (tangentSquareFTCPartition eps).pieces
            (tangentSquareFTCPartition eps).positive
            (by native_decide) k hk
        change (QInterval.addInterval
            (Integral.arctanKernelPaddedBound C δ.val 0)
            (tangentSquareCorrectionCommonBound C)).width <= E
        unfold E
        rw [QInterval.addInterval_width]
        unfold Integral.arctanKernelPaddedBound
          tangentSquareCorrectionCommonBound QInterval.width
        rw [hcell]
        grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm])
  have hW0 : 0 <= W := by
    dsimp [W]
    exact mesh_nonneg_of_le P.positive (by native_decide)
  have hWformula : W =
      1 / (256 * ((eps.val.den + 1 : Nat) : Rat)) := by
    change mesh 0 1 (256 * (eps.val.den + 1)) =
      1 / (256 * ((eps.val.den + 1 : Nat) : Rat))
    unfold mesh
    rw [if_neg (by omega : 256 * (eps.val.den + 1) ≠ 0), Rat.div_def,
      Rat.natCast_mul,
      Rat.natCast_add]
    simp [Rat.div_def]
    grind
  have hW1 : W <= 1 := by
    rw [hWformula]
    have hden : (1 : Rat) <=
        (256 : Rat) * ((eps.val.den + 1 : Nat) : Rat) := by
      have hdn : (1 : Rat) <= ((eps.val.den + 1 : Nat) : Rat) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le eps.val.den))
      grind
    have hpos : 0 < (256 : Rat) *
        ((eps.val.den + 1 : Nat) : Rat) :=
      Rat.mul_pos (by native_decide) (Rat.natCast_pos.mpr (by omega))
    apply Rat.le_of_mul_le_mul_right (c :=
      (256 : Rat) * ((eps.val.den + 1 : Nat) : Rat))
    · have hc := Rat.inv_mul_cancel _ (Rat.ne_of_gt hpos)
      grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hpos
  have hWsq : W * W <= W :=
    by simpa using (Rat.mul_le_mul_of_nonneg_left hW1 hW0)
  have hWle : W <= eps.val / 256 := by
    rw [hWformula]
    have hone := FTC.one_div_den_succ_le_of_pos eps.property
    have hinv : 0 <= (256 : Rat)⁻¹ :=
      Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide))
    have hmul := Rat.mul_le_mul_of_nonneg_right hone hinv
    simpa [Rat.div_def, Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm]
      using hmul
  have hδ : δ.val = eps.val / 64 := by rfl
  have hE : E <= eps.val := by
    dsimp [E]
    rw [hδ]
    have hW194 := Rat.mul_le_mul_of_nonneg_left hWle
      (by native_decide : (0 : Rat) <= 194)
    have hWsq' := Rat.le_trans hWsq hWle
    have heps : 0 <= eps.val := Rat.le_of_lt eps.property
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.div_def]
  have hE' : (1 - 0) * E <= eps.val := by
    have hzero : (1 : Rat) - 0 = 1 := by native_decide
    rw [hzero, Rat.one_mul]
    exact hE
  exact Rat.le_trans hsum hE'

/- The effective local certificate uses the finite arctangent rectangle
primitive.  The geometric arctangent evaluator remains the separate value
anchor used below. -/
def tangentSquareEffectivePrimitiveOnUnit : RealFunRaw :=
  RealFunRaw.add Integral.arctanPrimitiveRaw tangentSquareCorrectionRaw

theorem tangentSquareEffectivePrimitiveOnUnit_valid :
    tangentSquareEffectivePrimitiveOnUnit.Valid := by
  apply RealFunRaw.add_valid
  · exact Integral.arctanPrimitiveRaw_valid
  · exact tangentSquareCorrectionRaw_valid

def tangentSquareEffectiveCandidateFTC :
    CandidateDerivativeFTC tangentSquareEffectivePrimitiveOnUnit
      tangentSquareCombinedDerivativeRaw 0 1 where
  primitive_domain_lower := by
    unfold tangentSquareEffectivePrimitiveOnUnit RealFunRaw.add
    exact ⟨⟨by native_decide, by native_decide⟩, trivial⟩
  primitive_domain_upper := by
    unfold tangentSquareEffectivePrimitiveOnUnit RealFunRaw.add
    exact ⟨⟨by native_decide, by native_decide⟩, trivial⟩
  choosePartition := tangentSquareFTCPartition
  chooseEndpointPrecision := tangentSquareFTCEndpointStage
  chooseBoundStage := fun _ => 0
  cellControl := fun eps k hk => tangentSquareFTC_cellControl eps hk
  riemann_width := tangentSquareFTC_riemann_width_le
  endpoint_width := tangentSquareFTC_endpoint_width_le
  overlap := by
    intro eps
    apply RationalPartition.boundIntegralSum_overlaps_endpointDifference
      (tangentSquareFTCPartition eps) tangentSquareEffectivePrimitiveOnUnit
      (tangentSquareFTCEndpointStage eps)
      tangentSquareEffectivePrimitiveOnUnit_valid
    · intro i hi
      have hleft := (tangentSquareFTCPartition eps).monotone
        0 i (Nat.zero_le _) hi
      have hright := (tangentSquareFTCPartition eps).monotone
        i (tangentSquareFTCPartition eps).pieces hi (Nat.le_refl _)
      rw [(tangentSquareFTCPartition eps).left_endpoint] at hleft
      rw [(tangentSquareFTCPartition eps).right_endpoint] at hright
      unfold tangentSquareEffectivePrimitiveOnUnit RealFunRaw.add
      exact ⟨⟨hleft, hright⟩, trivial⟩
    · intro k hk
      exact (tangentSquareFTC_cellControl eps hk).endpoint_difference_contained 0

theorem tangentSquareEffectiveCandidateFTC_equiv_endpoint :
    tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw :=
  candidateDerivativeFTC tangentSquareEffectiveCandidateFTC

/-! The bounded integral produced by the effective FTC certificate is now a
user-facing raw real.  Its first theorem is the effective FTC itself; later
theorems identify its endpoint with the geometric quarter-turn anchor. -/
def tangentSquareEffectiveIntegralRaw : RealRaw :=
  tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.boundedIntegralRaw

theorem tangentSquareEffectiveCandidate_width_nonneg (n : Nat) :
    0 <= (tangentSquareEffectiveIntegralRaw.compute n).width := by
  let eps := precisionAtStage n
  let P := tangentSquareFTCPartition eps
  let bound : (k : Nat) -> k < P.pieces -> QInterval := fun k hk =>
    (tangentSquareFTC_cellControl eps hk).bound 0
  have hmesh : 0 <= mesh 0 1 P.pieces :=
    mesh_nonneg_of_le P.positive (by native_decide)
  have hcell : forall k, k ∈ List.range P.pieces ->
      0 <= (P.boundIntegralTerm bound k).width := by
    intro k hk
    have hklt : k < P.pieces := List.mem_range.mp hk
    have hcellwidth : (P.cell k hklt).width = mesh 0 1 P.pieces := by
      exact RationalPartition.uniform_cell_width 0 1 P.pieces
        P.positive (by native_decide) k hklt
    simp only [RationalPartition.boundIntegralTerm, dif_pos hklt]
    unfold RationalSubinterval.scaleBound
    rw [QInterval.scaleByRat_width_of_nonneg]
    · exact Rat.mul_nonneg
        (by
          rw [hcellwidth]
          exact hmesh)
        ((tangentSquareFTC_cellControl eps hklt).bound_ordered 0)
    · dsimp [RationalSubinterval.width]
      change 0 <= (P.cell k hklt).width
      rw [hcellwidth]
      exact hmesh
  unfold tangentSquareEffectiveIntegralRaw DerivativeBoundFTC.boundedIntegralRaw
    DerivativeBoundFTC.boundedIntegralCompute DerivativeBoundFTC.boundedIntegralInterval
  change 0 <= (P.boundIntegralSum bound).width
  unfold RationalPartition.boundIntegralSum
  rw [RationalPartition.addInterval_fold_width]
  have hfold : forall (xs : List Nat) (initial : Rat),
      0 <= initial ->
      (forall k, k ∈ xs -> 0 <= (P.boundIntegralTerm bound k).width) ->
      0 <= xs.foldl
        (fun total k => total + (P.boundIntegralTerm bound k).width) initial := by
    intro xs
    induction xs with
    | nil =>
        intro initial hinit hterms
        simpa using hinit
    | cons k xs ih =>
        intro initial hinit hterms
        apply ih (initial + (P.boundIntegralTerm bound k).width)
        · exact Rat.add_nonneg hinit (hterms k (by simp))
        · intro j hj
          exact hterms j (by simp [hj])
  have h := hfold (List.range P.pieces) 0 (by native_decide) hcell
  have hzero : ({lo := 0, hi := 0} : QInterval).width = 0 := by
    unfold QInterval.width
    grind
  grind

private theorem tangentSquareWidthsShrink_of_natOverSuccBound
    {compute : Nat -> QInterval} {C : Nat}
    (hbound : forall n,
      (compute n).width <= (C : Rat) / (((n + 1 : Nat) : Rat))) :
    RealRaw.WidthsShrinkToZero compute := by
  intro eps
  refine ⟨C * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (C : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (C : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega : C * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          have hcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          have hcancel : B * B⁻¹ = 1 := Rat.mul_inv_cancel B hBne
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hABpos
  exact Rat.le_trans (hbound n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

theorem tangentSquareEffectiveCandidate_width_le_two_over_succ (n : Nat) :
    (tangentSquareEffectiveIntegralRaw.compute n).width <=
      (2 : Rat) / (((n + 1 : Nat) : Rat)) := by
  have hriemann := tangentSquareFTC_riemann_width_le (precisionAtStage n)
  have hprecision : (precisionAtStage n).val <=
      (2 : Rat) / (((n + 1 : Nat) : Rat)) := by
    by_cases hn : n = 0
    · simp [precisionAtStage, hn]
      native_decide
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hnR : (n : Rat) ≠ 0 := by exact_mod_cast hn
      have hprec_eq : (precisionAtStage n).val = 1 / (n : Rat) := by
        simp [precisionAtStage, hn]
      rw [hprec_eq]
      have hn1 : (n + 1 : Nat) ≠ 0 := by omega
      have hmulpos : 0 < (n : Rat) * ((n + 1 : Nat) : Rat) :=
        Rat.mul_pos (by exact_mod_cast hnpos)
          (by exact_mod_cast (Nat.succ_pos n))
      apply Rat.le_of_mul_le_mul_right
        (c := (n : Rat) * ((n + 1 : Nat) : Rat))
      · calc
          (1 / (n : Rat)) * ((n : Rat) * ((n + 1 : Nat) : Rat)) =
              ((n + 1 : Nat) : Rat) := by
            grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm,
              Rat.mul_inv_cancel]
          _ <= 2 * (n : Rat) := by
            exact_mod_cast (by omega : n + 1 <= 2 * n)
          _ = (2 / ((n + 1 : Nat) : Rat)) *
              ((n : Rat) * ((n + 1 : Nat) : Rat)) := by
            grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm,
              Rat.mul_inv_cancel]
      · exact hmulpos
  exact Rat.le_trans hriemann hprecision

theorem tangentSquareEffectiveCandidate_widths_shrink_to_zero :
    RealRaw.WidthsShrinkToZero tangentSquareEffectiveIntegralRaw.compute := by
  apply tangentSquareWidthsShrink_of_natOverSuccBound
  exact tangentSquareEffectiveCandidate_width_le_two_over_succ

theorem tangentSquareEffectiveIntegralRaw_equiv_endpoint :
    tangentSquareEffectiveIntegralRaw.Equiv
      tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw :=
  tangentSquareEffectiveCandidateFTC_equiv_endpoint

theorem tangentSquareEffectivePrimitive_endpointDifference_compute_eq (n : Nat) :
    endpointDifferenceCompute tangentSquareEffectivePrimitiveOnUnit 0 1 n =
      ((ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)) -
        ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat)).compute n := by
  simp only [endpointDifferenceCompute, endpointDifferenceInterval,
    tangentSquareEffectivePrimitiveOnUnit, RealFunRaw.add,
    Integral.arctanPrimitiveRaw, tangentSquareCorrectionRaw, RealFunRaw.exact,
    tangentSquareRationalPart_one, tangentSquareRationalPart_zero]
  change _ = QInterval.mk
    (((ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)).compute n).lo -
      ((ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat)).compute n).hi)
    (((ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)).compute n).hi -
      ((ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat)).compute n).lo)
  congr 1 <;> grind

theorem tangentSquareEffectivePrimitive_endpointDifference_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute tangentSquareEffectivePrimitiveOnUnit 0 1) := by
  have hsub :
      (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat) -
        ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat)).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanIntegralRectangleRaw_valid
        (by native_decide) (by native_decide))
      (ArctanGeometry.arctanIntegralRectangleRaw_valid
        (by native_decide) (by native_decide))
  have hcompute :
      endpointDifferenceCompute tangentSquareEffectivePrimitiveOnUnit 0 1 =
        (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat) -
          ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat)).compute := by
    funext n
    exact tangentSquareEffectivePrimitive_endpointDifference_compute_eq n
  rw [hcompute]
  exact hsub

theorem tangentSquareEffectivePrimitive_endpointDifference_equiv_arctan :
    (endpointDifferenceRaw tangentSquareEffectivePrimitiveOnUnit 0 1
      tangentSquareEffectivePrimitive_endpointDifference_valid).Equiv
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)) := by
  have hendpoint :
      (endpointDifferenceRaw tangentSquareEffectivePrimitiveOnUnit 0 1
        tangentSquareEffectivePrimitive_endpointDifference_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using
      tangentSquareEffectivePrimitive_endpointDifference_valid
  have hrect1 :
      (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat)).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) :=
    ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom (by native_decide)
  have hrect0 :
      (ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat)).Equiv
        (ArctanGeometry.arctanGeom (0 : Rat)) :=
    ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom (by native_decide)
  have hsub :
      (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat) -
        ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat)).Equiv
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)) :=
    RealRaw.sub_equiv
      (ArctanGeometry.arctanIntegralRectangleRaw_valid (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide))
      (ArctanGeometry.arctanIntegralRectangleRaw_valid (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide))
      hrect1 hrect0
  have hcompute :
      endpointDifferenceCompute tangentSquareEffectivePrimitiveOnUnit 0 1 =
        (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat) -
          ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat)).compute := by
    funext n
    exact tangentSquareEffectivePrimitive_endpointDifference_compute_eq n
  apply RealRaw.equiv_trans hendpoint
    (RealRaw.sub_valid
      (ArctanGeometry.arctanIntegralRectangleRaw_valid (by native_decide) (by native_decide))
      (ArctanGeometry.arctanIntegralRectangleRaw_valid (by native_decide) (by native_decide)))
    (RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide)))
    (by
      apply RealRaw.sameStageOverlap_equiv
      intro n
      apply (RealRaw.compareAt_overlap_iff
        (endpointDifferenceRaw tangentSquareEffectivePrimitiveOnUnit 0 1
          tangentSquareEffectivePrimitive_endpointDifference_valid)
        (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat) -
          ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat)) n n).2
      change QInterval.Overlaps
        (endpointDifferenceCompute tangentSquareEffectivePrimitiveOnUnit 0 1 n)
        ((ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat) -
          ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat)).compute n)
      rw [tangentSquareEffectivePrimitive_endpointDifference_compute_eq n]
      have horder := RealRaw.interval_order_of_valid
        (ArctanGeometry.arctanIntegralRectangleRaw (1 : Rat) -
          ArctanGeometry.arctanIntegralRectangleRaw (0 : Rat))
        (RealRaw.sub_valid
          (ArctanGeometry.arctanIntegralRectangleRaw_valid (by native_decide) (by native_decide))
          (ArctanGeometry.arctanIntegralRectangleRaw_valid (by native_decide) (by native_decide))) n
      exact ⟨horder, horder⟩)
    hsub

theorem tangentSquareEffectivePrimitive_endpointDifference_equiv_halfQuarterTurn :
    (endpointDifferenceRaw tangentSquareEffectivePrimitiveOnUnit 0 1
      tangentSquareEffectivePrimitive_endpointDifference_valid).Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  have heff :
      (endpointDifferenceRaw tangentSquareEffectivePrimitiveOnUnit 0 1
        tangentSquareEffectivePrimitive_endpointDifference_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat) -
          ArctanGeometry.arctanGeom (0 : Rat)) :=
    tangentSquareEffectivePrimitive_endpointDifference_equiv_arctan
  have heffValid :
      (endpointDifferenceRaw tangentSquareEffectivePrimitiveOnUnit 0 1
        tangentSquareEffectivePrimitive_endpointDifference_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using
      tangentSquareEffectivePrimitive_endpointDifference_valid
  have hsubValid :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide))
  have hgeomOne : (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide)
  have hquarterValid :
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)).Valid := by
    change (RealRaw.scaleRat ((1 : Rat) / 4) piCircleArea).Valid
    exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
      CauchyPi.piCircleArea_valid
  have hsubToOne :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) :=
    IntegralIdentities.arctanGeom_one_sub_zero_equiv
  have honeToQuarter :
      (ArctanGeometry.arctanGeom (1 : Rat)).Equiv
        (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) :=
    ArctanGeometry.arctanGeom_one_equiv_piCircleArea_quarter
  have heffToOne :
      (endpointDifferenceRaw tangentSquareEffectivePrimitiveOnUnit 0 1
        tangentSquareEffectivePrimitive_endpointDifference_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) :=
    RealRaw.equiv_trans heffValid hsubValid hgeomOne heff hsubToOne
  exact RealRaw.equiv_trans heffValid hgeomOne hquarterValid
    heffToOne honeToQuarter

def tangentSquareEffectiveEndpointAnchor : RealRaw :=
  endpointDifferenceRaw tangentSquareEffectivePrimitiveOnUnit 0 1
    tangentSquareEffectivePrimitive_endpointDifference_valid

theorem tangentSquareEffectiveEndpointAnchor_valid :
    tangentSquareEffectiveEndpointAnchor.Valid := by
  simpa [tangentSquareEffectiveEndpointAnchor, endpointDifferenceRaw,
    RealRaw.Valid] using
    tangentSquareEffectivePrimitive_endpointDifference_valid

theorem tangentSquareEffectiveIntegralRaw_equiv_endpointAnchor :
    tangentSquareEffectiveIntegralRaw.Equiv
      tangentSquareEffectiveEndpointAnchor := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    tangentSquareEffectiveIntegralRaw tangentSquareEffectiveEndpointAnchor n n).2
  change QInterval.Overlaps
    (tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.boundedIntegralInterval
      (precisionAtStage n))
    (endpointDifferenceInterval tangentSquareEffectivePrimitiveOnUnit 0 1 n)
  exact CandidateDerivativeFTC.canonical_overlap_of_endpoint_stage_ge
    tangentSquareEffectiveCandidateFTC tangentSquareEffectivePrimitiveOnUnit_valid
    tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.primitive_domain_lower
    tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.primitive_domain_upper
    (by
      intro m
      simpa [tangentSquareEffectiveCandidateFTC] using
        tangentSquareEndpointStage_ge m) n

def tangentSquareEffectiveIntegralReboxed : RealRaw :=
  RealRaw.anchorRebox tangentSquareEffectiveIntegralRaw
    tangentSquareEffectiveEndpointAnchor

theorem tangentSquareEffectiveIntegralReboxed_valid :
    tangentSquareEffectiveIntegralReboxed.Valid := by
  apply RealRaw.anchorRebox_valid
    tangentSquareEffectiveCandidate_width_nonneg
    tangentSquareEffectiveCandidate_widths_shrink_to_zero
    tangentSquareEffectiveEndpointAnchor_valid
    tangentSquareEffectiveIntegralRaw_equiv_endpointAnchor

theorem tangentSquareEffectiveIntegralReboxed_equiv_anchor :
    tangentSquareEffectiveIntegralReboxed.Equiv
      tangentSquareEffectiveEndpointAnchor := by
  exact RealRaw.anchorRebox_equiv_anchor
    tangentSquareEffectiveEndpointAnchor_valid

theorem tangentSquareEffectiveIntegralRaw_equiv_reboxed :
    tangentSquareEffectiveIntegralRaw.Equiv
      tangentSquareEffectiveIntegralReboxed := by
  exact RealRaw.candidate_equiv_anchorRebox
    tangentSquareEffectiveEndpointAnchor_valid
    tangentSquareEffectiveIntegralRaw_equiv_endpointAnchor

theorem tangentSquareEffectiveEndpointCandidate_widths_shrink :
    RealRaw.WidthsShrinkToZero
      tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw.compute := by
  intro eps
  let N : Nat := eps.val.den + 1
  refine ⟨N, ?_⟩
  intro n hn
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  have hnpos : 0 < n := Nat.lt_of_lt_of_le hNpos hn
  have hnm : eps.val.den + 1 <= n := by
    simpa [N] using hn
  have hanti := FTC.one_div_nat_antitone
    (n := eps.val.den + 1) (m := n)
    (by omega) (by exact hnpos) hnm
  have hden := FTC.one_div_den_succ_le_of_pos eps.property
  have hbound : 1 / (n : Rat) <= eps.val := by
    exact Rat.le_trans hanti hden
  have hwidth := tangentSquareFTC_endpoint_width_le
    (precisionAtStage n)
  change (endpointDifferenceInterval tangentSquareEffectivePrimitiveOnUnit 0 1
    (tangentSquareFTCEndpointStage (precisionAtStage n))).width <= eps.val
  have hprecision :
      (precisionAtStage n).val = 1 / (n : Rat) := by
    simp [precisionAtStage, Nat.ne_of_gt hnpos]
  rw [hprecision] at hwidth
  exact Rat.le_trans hwidth hbound

def tangentSquareEffectiveEndpointStabilized : RealRaw :=
  RealRaw.prefixStabilize
    tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.endpointRaw
    (fun n => tangentSquareEffectiveEndpointAnchor.compute n |>.width)

theorem tangentSquareEffectiveEndpointStabilized_valid :
    tangentSquareEffectiveEndpointStabilized.Valid := by
  apply RealRaw.prefixStabilize_valid
    tangentSquareEffectiveEndpointCandidate_widths_shrink
    tangentSquareEffectiveEndpointAnchor_valid
  · apply DerivativeBoundFTC.endpointRaw_equiv_endpointDifference
      tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC
      tangentSquareEffectivePrimitiveOnUnit_valid
      tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.primitive_domain_lower
      tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.primitive_domain_upper
      tangentSquareEffectivePrimitive_endpointDifference_valid
  · intro n
    exact Rat.le_refl
  · intro eps
    obtain ⟨N, hN⟩ := tangentSquareEffectiveEndpointAnchor_valid.2.2 eps
    refine ⟨N, hN⟩

theorem tangentSquareEffectiveEndpointStabilized_equiv_anchor :
    tangentSquareEffectiveEndpointStabilized.Equiv
      tangentSquareEffectiveEndpointAnchor := by
  apply RealRaw.prefixStabilize_equiv_anchor
    tangentSquareEffectiveEndpointAnchor_valid
  · apply DerivativeBoundFTC.endpointRaw_equiv_endpointDifference
      tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC
      tangentSquareEffectivePrimitiveOnUnit_valid
      tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.primitive_domain_lower
      tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.primitive_domain_upper
      tangentSquareEffectivePrimitive_endpointDifference_valid
  · intro n
    exact Rat.le_refl

theorem tangentSquareEffectiveEndpointStabilized_equiv_halfQuarterTurn :
    tangentSquareEffectiveEndpointStabilized.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  have hanchorQuarter :
      tangentSquareEffectiveEndpointAnchor.Equiv
        (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
    simpa [tangentSquareEffectiveEndpointAnchor] using
      tangentSquareEffectivePrimitive_endpointDifference_equiv_halfQuarterTurn
  exact RealRaw.equiv_trans
    tangentSquareEffectiveEndpointStabilized_valid
    tangentSquareEffectiveEndpointAnchor_valid
    (by
      change (RealRaw.scaleRat ((1 : Rat) / 4) piCircleArea).Valid
      exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
        CauchyPi.piCircleArea_valid)
    tangentSquareEffectiveEndpointStabilized_equiv_anchor hanchorQuarter

/-! The tangent-chart route is now exposed as a complete proof-facing
certificate interface.  The finite derivative certificate and the endpoint
anchor are already constructed above; the two validity fields are retained
explicitly because a scheduled raw computation becomes a public RealRaw
only after its nesting and shrinking have been proved. -/

structure TangentSquareEffectiveFTCData where
  integral_valid : tangentSquareEffectiveIntegralReboxed.Valid
  endpoint_valid :
    tangentSquareEffectiveEndpointStabilized.Valid
  integral_equiv_stabilized_endpoint :
    tangentSquareEffectiveIntegralReboxed.Equiv
      tangentSquareEffectiveEndpointStabilized
  endpoint_stage_ge :
    forall n,
      n <= tangentSquareEffectiveCandidateFTC.chooseEndpointPrecision
        (precisionAtStage n)

theorem TangentSquareEffectiveFTCData.canonical_overlap
    (D : TangentSquareEffectiveFTCData) (n : Nat) :
    QInterval.Overlaps
      (tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.boundedIntegralInterval
        (precisionAtStage n))
      (endpointDifferenceInterval tangentSquareEffectivePrimitiveOnUnit 0 1 n) :=
  CandidateDerivativeFTC.canonical_overlap_of_endpoint_stage_ge
    tangentSquareEffectiveCandidateFTC tangentSquareEffectivePrimitiveOnUnit_valid
    tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.primitive_domain_lower
    tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC.primitive_domain_upper
    D.endpoint_stage_ge n

def TangentSquareEffectiveFTCData.integralRaw
    (_D : TangentSquareEffectiveFTCData) : RealRaw :=
  tangentSquareEffectiveIntegralReboxed

def TangentSquareEffectiveFTCData.endpointRaw
    (_D : TangentSquareEffectiveFTCData) : RealRaw :=
  tangentSquareEffectiveEndpointStabilized

theorem TangentSquareEffectiveFTCData.integral_equiv_endpoint
    (D : TangentSquareEffectiveFTCData) :
    D.integralRaw.Equiv D.endpointRaw := by
  exact D.integral_equiv_stabilized_endpoint

theorem TangentSquareEffectiveFTCData.endpoint_equiv_halfQuarterTurn
    (D : TangentSquareEffectiveFTCData) :
    D.endpointRaw.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  let H := tangentSquareEffectiveCandidateFTC.toDerivativeBoundFTC
  have hendpoint :
      D.endpointRaw.Equiv
        (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) :=
    tangentSquareEffectiveEndpointStabilized_equiv_halfQuarterTurn
  exact hendpoint

theorem TangentSquareEffectiveFTCData.integral_equiv_halfQuarterTurn
    (D : TangentSquareEffectiveFTCData) :
    D.integralRaw.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  exact RealRaw.equiv_trans D.integral_valid
    D.endpoint_valid
    (by
      change (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)).Valid
      change (RealRaw.scaleRat ((1 : Rat) / 4) piCircleArea).Valid
      exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
        CauchyPi.piCircleArea_valid)
    D.integral_equiv_stabilized_endpoint
    tangentSquareEffectiveEndpointStabilized_equiv_halfQuarterTurn

theorem tangentSquareEffectiveFTCData : TangentSquareEffectiveFTCData where
  integral_valid := tangentSquareEffectiveIntegralReboxed_valid
  endpoint_valid := tangentSquareEffectiveEndpointStabilized_valid
  integral_equiv_stabilized_endpoint := by
    exact RealRaw.equiv_trans tangentSquareEffectiveIntegralReboxed_valid
      tangentSquareEffectiveEndpointAnchor_valid
      tangentSquareEffectiveEndpointStabilized_valid
      tangentSquareEffectiveIntegralReboxed_equiv_anchor
      (RealRaw.equiv_symm tangentSquareEffectiveEndpointStabilized_equiv_anchor)
  endpoint_stage_ge := by
    intro n
    simpa [tangentSquareEffectiveCandidateFTC] using
      tangentSquareEndpointStage_ge n

theorem tangentSquareEffectiveFTC_integral_equiv_halfQuarterTurn :
    tangentSquareEffectiveFTCData.integralRaw.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) :=
  TangentSquareEffectiveFTCData.integral_equiv_halfQuarterTurn
    tangentSquareEffectiveFTCData

/-! The two tangent-square integrals are independent computations.  The
effective-FTC computation uses scheduled derivative boxes, while
`tangentSquareIntegral` uses the direct Lipschitz dyadic construction.  The
only required bridge is therefore a finite, stagewise overlap certificate;
no identification of their internal sums is assumed. -/

structure TangentSquareIntegralEffectiveFTCOverlap where
  overlap : forall n,
    QInterval.Overlaps
      (tangentSquareIntegral.compute n)
      (tangentSquareEffectiveFTCData.integralRaw.compute n)

theorem TangentSquareIntegralEffectiveFTCOverlap.to_equiv
    (h : TangentSquareIntegralEffectiveFTCOverlap) :
    tangentSquareIntegral.Equiv
      tangentSquareEffectiveFTCData.integralRaw := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    tangentSquareIntegral tangentSquareEffectiveFTCData.integralRaw n n).2
  exact h.overlap n

theorem TangentSquareIntegralEffectiveFTCOverlap.to_halfQuarterTurn
    (h : TangentSquareIntegralEffectiveFTCOverlap) :
    tangentSquareIntegral.Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  exact RealRaw.equiv_trans tangentSquareIntegral_valid
    tangentSquareEffectiveFTCData.integral_valid
    (by
      change (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)).Valid
      change (RealRaw.scaleRat ((1 : Rat) / 4) piCircleArea).Valid
      exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
        CauchyPi.piCircleArea_valid)
    h.to_equiv tangentSquareEffectiveFTC_integral_equiv_halfQuarterTurn

theorem tangentSquareEffectivePrimitive_endpoint_contains
    (C : RationalSubinterval 0 1) (δ η : QPos) (N : Nat)
    (hC : 0 < C.width) (hη : η.val = C.width * δ.val / 3)
    (hN : 256 * (η.val.den + 1) <= N) :
    QInterval.ContainsInterval
      (QInterval.addInterval
        (C.scaleBound (Integral.arctanKernelPaddedBound C δ.val N))
        (C.scaleBound tangentSquareCorrectionBound))
      (endpointDifferenceInterval tangentSquareEffectivePrimitiveOnUnit
        C.lower C.upper N) := by
  have harctan := Integral.arctanKernelPaddedBound_local_endpoint_contains
    C δ η N hC hη hN
  have hstrict : C.lower < C.upper := by
    unfold RationalSubinterval.width at hC
    grind
  have hcorrection := tangentSquareCorrectionBound_contains_endpoint
    C N hstrict
  have hsum := QInterval.addInterval_contains harctan hcorrection
  exact hsum.trans (endpointDifferenceInterval_add_contains
    Integral.arctanPrimitiveRaw tangentSquareCorrectionRaw C.lower C.upper N)

theorem tangentSquareEffectivePrimitive_centered_endpoint_contains
    (C : RationalSubinterval 0 1) (δ η : QPos) (N : Nat)
    (hC : 0 < C.width) (hη : η.val = C.width * δ.val / 3)
    (hN : 256 * (η.val.den + 1) <= N) :
    QInterval.ContainsInterval
      (QInterval.addInterval
        (C.scaleBound (Integral.arctanKernelPaddedBound C δ.val N))
        (C.scaleBound (tangentSquareCorrectionCenteredBound C)))
      (endpointDifferenceInterval tangentSquareEffectivePrimitiveOnUnit
        C.lower C.upper N) := by
  have harctan := Integral.arctanKernelPaddedBound_local_endpoint_contains
    C δ η N hC hη hN
  have hstrict : C.lower < C.upper := by
    unfold RationalSubinterval.width at hC
    grind
  have hcorrection := tangentSquareCorrectionCenteredBound_contains_endpoint
    C N hstrict
  have hsum := QInterval.addInterval_contains harctan hcorrection
  exact hsum.trans (endpointDifferenceInterval_add_contains
    Integral.arctanPrimitiveRaw tangentSquareCorrectionRaw C.lower C.upper N)

theorem tangentSquareRationalPrimitive_zero :
    tangentSquareRationalPrimitive 0 = 0 := by
  simp [tangentSquareRationalPrimitive, tangentSquareRationalPart_zero]

theorem tangentSquareRationalPrimitive_one :
    tangentSquareRationalPrimitive 1 = 0 := by
  simp [tangentSquareRationalPrimitive, tangentSquareRationalPart_one]

theorem tangentSquarePrimitiveOnUnit_endpointDifference_compute_eq (n : Nat) :
    endpointDifferenceCompute tangentSquarePrimitiveOnUnit 0 1 n =
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).compute n := by
  simp only [endpointDifferenceCompute, endpointDifferenceInterval,
    tangentSquarePrimitiveOnUnit, RealFunRaw.add, RealFunRaw.exact]
  rw [IntegralIdentities.arctanGeomOnUnit_toRealFunRaw_compute_one n,
    IntegralIdentities.arctanGeomOnUnit_toRealFunRaw_compute_zero n,
    tangentSquareRationalPrimitive_one,
    tangentSquareRationalPrimitive_zero]
  change _ = QInterval.mk
    (((ArctanGeometry.arctanGeom (1 : Rat)).compute n).lo -
      ((ArctanGeometry.arctanGeom (0 : Rat)).compute n).hi)
    (((ArctanGeometry.arctanGeom (1 : Rat)).compute n).hi -
      ((ArctanGeometry.arctanGeom (0 : Rat)).compute n).lo)
  congr 1 <;> grind

theorem tangentSquarePrimitiveOnUnit_endpointDifference_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute tangentSquarePrimitiveOnUnit 0 1) := by
  have hsub :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (0 : Rat)) (by native_decide) (by native_decide))
  have hcompute :
      endpointDifferenceCompute tangentSquarePrimitiveOnUnit 0 1 =
        (ArctanGeometry.arctanGeom (1 : Rat) -
          ArctanGeometry.arctanGeom (0 : Rat)).compute := by
    funext n
    exact tangentSquarePrimitiveOnUnit_endpointDifference_compute_eq n
  rw [hcompute]
  exact hsub

theorem tangentSquarePrimitiveOnUnit_endpointDifference_equiv_arctan :
    (endpointDifferenceRaw tangentSquarePrimitiveOnUnit 0 1
      tangentSquarePrimitiveOnUnit_endpointDifference_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat) -
          ArctanGeometry.arctanGeom (0 : Rat)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (endpointDifferenceRaw tangentSquarePrimitiveOnUnit 0 1
      tangentSquarePrimitiveOnUnit_endpointDifference_valid)
    (ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)) n n).2
  change QInterval.Overlaps
    (endpointDifferenceCompute tangentSquarePrimitiveOnUnit 0 1 n)
    ((ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)).compute n)
  rw [tangentSquarePrimitiveOnUnit_endpointDifference_compute_eq n]
  have hvalid :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (1 : Rat)) (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit
        (x := (0 : Rat)) (by native_decide) (by native_decide))
  have horder := RealRaw.interval_order_of_valid
    (ArctanGeometry.arctanGeom (1 : Rat) -
      ArctanGeometry.arctanGeom (0 : Rat)) hvalid n
  exact ⟨horder, horder⟩

theorem tangentSquarePrimitiveOnUnit_endpointDifference_equiv_halfQuarterTurn :
    (endpointDifferenceRaw tangentSquarePrimitiveOnUnit 0 1
      tangentSquarePrimitiveOnUnit_endpointDifference_valid).Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  have hendpoint :
      (endpointDifferenceRaw tangentSquarePrimitiveOnUnit 0 1
        tangentSquarePrimitiveOnUnit_endpointDifference_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using
      tangentSquarePrimitiveOnUnit_endpointDifference_valid
  have hsub :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Valid :=
    RealRaw.sub_valid
      (ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide))
      (ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide))
  have hquarter :
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)).Valid := by
    change (RealRaw.scaleRat ((1 : Rat) / 4) piCircleArea).Valid
    exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
      CauchyPi.piCircleArea_valid
  have hgeom : (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide)
  have hsub_to_geom :
      (ArctanGeometry.arctanGeom (1 : Rat) -
        ArctanGeometry.arctanGeom (0 : Rat)).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) :=
    IntegralIdentities.arctanGeom_one_sub_zero_equiv
  have hgeom_to_quarter :
      (ArctanGeometry.arctanGeom (1 : Rat)).Equiv
        (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) :=
    ArctanGeometry.arctanGeom_one_equiv_piCircleArea_quarter
  have hendpoint_to_geom :
      (endpointDifferenceRaw tangentSquarePrimitiveOnUnit 0 1
        tangentSquarePrimitiveOnUnit_endpointDifference_valid).Equiv
        (ArctanGeometry.arctanGeom (1 : Rat)) :=
    RealRaw.equiv_trans hendpoint hsub hgeom
      tangentSquarePrimitiveOnUnit_endpointDifference_equiv_arctan
      hsub_to_geom
  exact RealRaw.equiv_trans hendpoint hgeom hquarter
    hendpoint_to_geom hgeom_to_quarter

theorem finiteSineSquarePrefix_effectiveFTC_equiv_endpoint :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_endpoint

theorem finiteSineSquarePrefix_effectiveFTC_equiv_value :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (6389 / 161280)) := by
  exact FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_value

def sinPiOnHalfRaw (S : ArctanSinPiConstruction) : RealFunRaw where
  domain := fun x => 0 <= x /\ x <= (1 : Rat) / 2
  compute := fun x n =>
    if hx : 0 <= x /\ x <= (1 : Rat) / 2 then
      (sinPiRawOfArctan S.inverse x hx).compute n
    else
      { lo := 0, hi := 0 }

def sinPiSquareOnHalf (S : ArctanSinPiConstruction) : RealFunRaw :=
  RealFunRaw.mul (sinPiOnHalfRaw S) (sinPiOnHalfRaw S)

def rationalSquareInterval (I : QInterval) : QInterval :=
  { lo := I.lo * I.lo, hi := I.hi * I.hi }

def rationalOneMinusSquareInterval (I : QInterval) : QInterval :=
  { lo := 1 - I.hi * I.hi, hi := 1 - I.lo * I.lo }

/-! Signed interval squares.  The earlier `rationalSquareInterval` is the
nonnegative specialization used by the sine boxes.  Cosine crosses zero on
the full half-period, so its square enclosure must split at zero. -/
def rationalSquareIntervalSigned (I : QInterval) : QInterval :=
  if 0 <= I.lo then
    { lo := I.lo * I.lo, hi := I.hi * I.hi }
  else if 0 <= I.hi then
    { lo := 0, hi := max (I.lo * I.lo) (I.hi * I.hi) }
  else
    { lo := I.hi * I.hi, hi := I.lo * I.lo }

def rationalOneMinusSquareIntervalSigned (I : QInterval) : QInterval :=
  { lo := 1 - (rationalSquareIntervalSigned I).hi,
    hi := 1 - (rationalSquareIntervalSigned I).lo }

theorem rationalSquareIntervalSigned_contains
    {I : QInterval} {q : Rat}
    (hI : I.lo <= I.hi) (hq : I.lo <= q ∧ q <= I.hi) :
    (rationalSquareIntervalSigned I).lo <= q * q ∧
      q * q <= (rationalSquareIntervalSigned I).hi := by
  have hsquare_mono {a b : Rat} (ha : 0 <= a) (hab : a <= b) :
      a * a <= b * b := by
    have hb : 0 <= b := Rat.le_trans ha hab
    exact Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_left hab ha)
      (Rat.mul_le_mul_of_nonneg_right hab hb)
  by_cases hlo : 0 <= I.lo
  · simp [rationalSquareIntervalSigned, hlo]
    have hq0 : 0 <= q := Rat.le_trans hlo hq.1
    constructor
    · have h := Rat.mul_le_mul_of_nonneg_right hq.1
        (Rat.add_nonneg hq0 hlo)
      grind [Rat.mul_add, Rat.add_mul]
    · have h := Rat.mul_le_mul_of_nonneg_right hq.2
        (Rat.add_nonneg hq0 (Rat.le_trans hlo hI))
      grind [Rat.mul_add, Rat.add_mul]
  · by_cases hhi : 0 <= I.hi
    · simp [rationalSquareIntervalSigned, hlo, hhi]
      have hqlo : I.lo <= q := hq.1
      have hqhi : q <= I.hi := hq.2
      by_cases hq0 : 0 <= q
      · constructor
        · exact Rat.mul_nonneg hq0 hq0
        · have h1 := Rat.mul_le_mul_of_nonneg_left hqhi hq0
          have h2 := Rat.mul_le_mul_of_nonneg_right hqhi hhi
          have hsq : q * q <= I.hi * I.hi := by
            exact Rat.le_trans h1 (by simpa [Rat.mul_comm] using h2)
          rw [Rat.max_def]
          split <;> grind
      · have hqneg : q < 0 := Rat.not_le.mp hq0
        constructor
        · have h := hsquare_mono (by grind : 0 <= -q) (by grind : -q <= -q)
          grind [Rat.mul_add, Rat.add_mul]
        · have hsq : q * q <= I.lo * I.lo := by
            have h := hsquare_mono (by grind : 0 <= -q)
              (by grind : -q <= -I.lo)
            grind [Rat.mul_add, Rat.add_mul]
          rw [Rat.max_def]
          split <;> grind
    · simp [rationalSquareIntervalSigned, hlo, hhi]
      have hq0 : q < 0 := by grind [Rat.not_le.mp hhi]
      constructor
      · have h := hsquare_mono (by grind : 0 <= -I.hi)
          (by grind : -I.hi <= -q)
        grind [Rat.mul_add, Rat.add_mul]
      · have h := hsquare_mono (by grind : 0 <= -q)
          (by grind : -q <= -I.lo)
        grind [Rat.mul_add, Rat.add_mul]

theorem rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle_signed
    {S C : QInterval} {s c : Rat}
    (hS : subintervalOf S 0 1)
    (hC : subintervalOf C (-1) 1)
    (hs : S.lo <= s ∧ s <= S.hi)
    (hc : C.lo <= c ∧ c <= C.hi)
    (hcircle : s * s + c * c = 1) :
    QInterval.Overlaps (rationalSquareInterval S)
      (rationalOneMinusSquareIntervalSigned C) := by
  have hsquare := rationalSquareIntervalSigned_contains hC.2.1 hc
  have hsquareS : S.lo * S.lo <= s * s ∧
      s * s <= S.hi * S.hi := by
    have h := rationalSquareIntervalSigned_contains hS.2.1 hs
    simpa [rationalSquareIntervalSigned, hS.1] using h
  unfold rationalOneMinusSquareIntervalSigned QInterval.Overlaps
  change S.lo * S.lo <=
      1 - (rationalSquareIntervalSigned C).lo ∧
    1 - (rationalSquareIntervalSigned C).hi <= S.hi * S.hi
  constructor
  · calc
      S.lo * S.lo <= s * s := hsquareS.1
      _ = 1 - c * c := by grind
      _ <= 1 - (rationalSquareIntervalSigned C).lo := by grind [hsquare.2]
  · calc
      1 - (rationalSquareIntervalSigned C).hi <= 1 - c * c := by
        grind [hsquare.1]
      _ = s * s := by grind
      _ <= S.hi * S.hi := hsquareS.2

/- The raw equal-dyadic square candidate.  Its validity/nesting certificate
is intentionally separate: this definition is only the finite algorithm. -/
def dyadicNestedRadicalSquareLeftSum (n : Nat) : QInterval :=
  let N := 2 ^ n
  let h := mesh 0 ((1 : Rat) / 2) N
  (List.range N).foldl
    (fun acc k =>
      QInterval.addInterval acc
        (QInterval.scaleByRat h
          (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k))))
    { lo := 0, hi := 0 }

/- The same finite rectangle sum, using the public sine-square evaluator at
each dyadic sample.  The transport theorem below is deliberately stated at
the interval level: a specialized table only has to overlap these samples. -/
def dyadicPublicSquareLeftSum
    (S : ArctanSinPiConstruction) (n : Nat) : QInterval :=
  let N := 2 ^ n
  let h := mesh 0 ((1 : Rat) / 2) N
  (List.range N).foldl
    (fun acc k =>
      QInterval.addInterval acc
        (QInterval.scaleByRat h
          ((sinPiSquareOnHalf S).compute
            (leftPoint 0 ((1 : Rat) / 2) N k) n)))
    { lo := 0, hi := 0 }

/- A finite family of overlapping square-sample boxes gives overlapping
rectangle sums.  This is the reusable finite part of the square route; no
limit, completeness principle, or equality of the two evaluators is used. -/
theorem dyadicPublicSquareLeftSum_overlap_of_sample_overlaps
    (S : ArctanSinPiConstruction) (n : Nat)
    (hsamples : forall k, k < 2 ^ n ->
      QInterval.Overlaps
        ((sinPiSquareOnHalf S).compute
          (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n)
        (rationalSquareInterval
          (dyadicNestedRadicalStageSinAt n k))) :
    QInterval.Overlaps
      (dyadicPublicSquareLeftSum S n)
      (dyadicNestedRadicalSquareLeftSum n) := by
  unfold dyadicPublicSquareLeftSum dyadicNestedRadicalSquareLeftSum
  have hmesh : 0 <= mesh 0 ((1 : Rat) / 2) (2 ^ n) := by
    exact mesh_nonneg_of_le (Nat.pow_pos (by omega)) (by native_decide)
  have hfold : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < 2 ^ n) ->
      forall (accG accH : QInterval), QInterval.Overlaps accG accH ->
      QInterval.Overlaps
        (xs.foldl
          (fun acc k =>
            QInterval.addInterval acc
              (QInterval.scaleByRat
                (mesh 0 ((1 : Rat) / 2) (2 ^ n))
                ((sinPiSquareOnHalf S).compute
                  (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n))) accG)
        (xs.foldl
          (fun acc k =>
            QInterval.addInterval acc
              (QInterval.scaleByRat
                (mesh 0 ((1 : Rat) / 2) (2 ^ n))
                (rationalSquareInterval
                  (dyadicNestedRadicalStageSinAt n k)))) accH) := by
    intro xs
    induction xs with
    | nil =>
        intro _ accG accH hover
        exact hover
    | cons k ks ih =>
        intro hmem
        have hk : k < 2 ^ n := hmem k (by simp)
        have hks : forall j, j ∈ ks -> j < 2 ^ n := by
          intro j hj
          exact hmem j (by simp [hj])
        intro accG accH hover
        have hsample := hsamples k hk
        have hstep : QInterval.Overlaps
            (QInterval.addInterval accG
              (QInterval.scaleByRat
                (mesh 0 ((1 : Rat) / 2) (2 ^ n))
                ((sinPiSquareOnHalf S).compute
                  (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n)))
            (QInterval.addInterval accH
              (QInterval.scaleByRat
                (mesh 0 ((1 : Rat) / 2) (2 ^ n))
                (rationalSquareInterval
                  (dyadicNestedRadicalStageSinAt n k)))) := by
          unfold QInterval.addInterval QInterval.scaleByRat
          unfold QInterval.Overlaps at hover hsample ⊢
          constructor
          · have hscaled :
                mesh 0 ((1 : Rat) / 2) (2 ^ n) *
                    ((sinPiSquareOnHalf S).compute
                      (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n).lo <=
                mesh 0 ((1 : Rat) / 2) (2 ^ n) *
                    (rationalSquareInterval
                      (dyadicNestedRadicalStageSinAt n k)).hi :=
              Rat.mul_le_mul_of_nonneg_left hsample.1 hmesh
            grind
          · have hscaled :
                mesh 0 ((1 : Rat) / 2) (2 ^ n) *
                    (rationalSquareInterval
                      (dyadicNestedRadicalStageSinAt n k)).lo <=
                mesh 0 ((1 : Rat) / 2) (2 ^ n) *
                    ((sinPiSquareOnHalf S).compute
                      (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n).hi :=
              Rat.mul_le_mul_of_nonneg_left hsample.2 hmesh
            grind
        simpa using ih hks _ _ hstep
  exact hfold (List.range (2 ^ n))
    (by intro k hk; exact List.mem_range.mp hk)
    { lo := 0, hi := 0 } { lo := 0, hi := 0 } (by
      simp [QInterval.Overlaps])

theorem dyadicPublicSquareLeftSum_width_le_of_stage
    (S : ArctanSinPiConstruction) (n : Nat) (eps : Rat)
    (hstage : forall k, k < 2 ^ n ->
      ((sinPiSquareOnHalf S).compute
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n).width <= eps) :
    (dyadicPublicSquareLeftSum S n).width <= (1 / 2 : Rat) * eps := by
  let N := 2 ^ n
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.pow_pos (by omega)
  have hmesh : 0 <= mesh 0 ((1 : Rat) / 2) N :=
    mesh_nonneg_of_le hN (by native_decide)
  have hsum := RationalPartition.rat_add_fold_le_length_mul (List.range N)
    (fun k =>
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
        ((sinPiSquareOnHalf S).compute
          (leftPoint 0 ((1 : Rat) / 2) N k) n)).width)
    (mesh 0 ((1 : Rat) / 2) N * eps) (by
      intro k hk
      have hklt : k < N := List.mem_range.mp hk
      rw [QInterval.scaleByRat_width_of_nonneg hmesh]
      exact Rat.mul_le_mul_of_nonneg_left
        (hstage k (by simpa [N] using hklt)) hmesh)
  calc
    (dyadicPublicSquareLeftSum S n).width =
        (List.range N).foldl
          (fun total k => total +
            (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
              ((sinPiSquareOnHalf S).compute
                (leftPoint 0 ((1 : Rat) / 2) N k) n)).width) 0 := by
      unfold dyadicPublicSquareLeftSum
      rw [RationalPartition.addInterval_fold_width]
      have hzero : ({ lo := 0, hi := 0 } : QInterval).width = 0 := by
        unfold QInterval.width
        grind
      rw [hzero]
      simp [N]
      grind
    _ <= (N : Rat) * (mesh 0 ((1 : Rat) / 2) N * eps) := by
      simpa using hsum
    _ = (1 / 2 : Rat) * eps := by
      have hmesh_total := natCast_mul_mesh_eq_sub
        (a := (0 : Rat)) (b := (1 : Rat) / 2) hN
      rw [show (N : Rat) * (mesh 0 ((1 : Rat) / 2) N * eps) =
        ((N : Rat) * mesh 0 ((1 : Rat) / 2) N) * eps by
          grind [Rat.mul_assoc]]
      rw [hmesh_total]
      rw [show (1 / 2 : Rat) - 0 = 1 / 2 by grind]

theorem sinPiSquareOnHalf_valid (S : ArctanSinPiConstruction) :
    (sinPiSquareOnHalf S).Valid := by
  have hvalid : (sinPiOnHalfRaw S).Valid := by
    intro x hx
    change RealRaw.ValidCompute
      (fun n => if h : 0 <= x /\ x <= (1 : Rat) / 2 then
        (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 })
    split
    · exact S.sin_valid x hx
    · rename_i hfalse
      exact False.elim (hfalse hx)
  apply RealFunRaw.mul_valid_of_nonneg_bounded
    hvalid hvalid
  · intro x hx
    refine ⟨1, by native_decide, ?_⟩
    intro n
    change 0 <= (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
      (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).lo /\
      (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
        (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).hi <= 1
    split
    · exact S.sinPiRawOfArctan_bounds hx n
    · rename_i hfalse
      exact False.elim (hfalse hx)
  · intro x hx
    refine ⟨1, by native_decide, ?_⟩
    intro n
    change 0 <= (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
      (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).lo /\
      (if h : 0 <= x /\ x <= (1 : Rat) / 2 then
        (sinPiRawOfArctan S.inverse x h).compute n else { lo := 0, hi := 0 }).hi <= 1
    split
    · exact S.sinPiRawOfArctan_bounds hx n
    · rename_i hfalse
      exact False.elim (hfalse hx)

theorem dyadicPublicSquareLeftSum_ordered
    (S : ArctanSinPiConstruction) (n : Nat) :
    0 <= (dyadicPublicSquareLeftSum S n).width := by
  let N := 2 ^ n
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.pow_pos (by omega)
  have hmesh : 0 <= mesh 0 ((1 : Rat) / 2) N :=
    mesh_nonneg_of_le hN (by native_decide)
  have hcell : forall k, k ∈ List.range N ->
      0 <= (QInterval.scaleByRat
        (mesh 0 ((1 : Rat) / 2) N)
        ((sinPiSquareOnHalf S).compute
          (leftPoint 0 ((1 : Rat) / 2) N k) n)).width := by
    intro k hk
    have hklt : k < N := List.mem_range.mp hk
    have hleft := leftPoint_monotone hN (by native_decide :
      (0 : Rat) <= (1 : Rat) / 2) (Nat.zero_le k)
    have hright :
        leftPoint 0 ((1 : Rat) / 2) N k <=
          leftPoint 0 ((1 : Rat) / 2) N N :=
      leftPoint_monotone hN (by native_decide)
        (Nat.le_of_lt hklt)
    let x := leftPoint 0 ((1 : Rat) / 2) N k
    have hx : 0 <= x /\ x <= (1 : Rat) / 2 := by
      exact ⟨by simpa [x, N, leftPoint_zero] using hleft,
        by simpa [x, N, leftPoint_endpoint hN] using hright⟩
    have hsamplevalid := sinPiSquareOnHalf_valid S x ⟨hx, hx⟩
    rw [QInterval.scaleByRat_width_of_nonneg hmesh]
    exact Rat.mul_nonneg hmesh
      (hsamplevalid.1 n)
  unfold dyadicPublicSquareLeftSum
  rw [RationalPartition.addInterval_fold_width]
  have hzero : ({ lo := 0, hi := 0 } : QInterval).width = 0 := by
    unfold QInterval.width
    grind
  rw [hzero]
  have hfold : forall (xs : List Nat) (initial : Rat),
      0 <= initial ->
      (forall k, k ∈ xs ->
        0 <= (QInterval.scaleByRat
          (mesh 0 ((1 : Rat) / 2) N)
          ((sinPiSquareOnHalf S).compute
            (leftPoint 0 ((1 : Rat) / 2) N k) n)).width) ->
      0 <= xs.foldl
        (fun total k => total +
          (QInterval.scaleByRat
            (mesh 0 ((1 : Rat) / 2) N)
            ((sinPiSquareOnHalf S).compute
              (leftPoint 0 ((1 : Rat) / 2) N k) n)).width) initial := by
    intro xs
    induction xs with
    | nil =>
        intro initial hinit hterms
        simpa using hinit
    | cons k xs ih =>
        intro initial hinit hterms
        apply ih (initial +
          (QInterval.scaleByRat
            (mesh 0 ((1 : Rat) / 2) N)
            ((sinPiSquareOnHalf S).compute
              (leftPoint 0 ((1 : Rat) / 2) N k) n)).width)
        · exact Rat.add_nonneg hinit (hterms k (by simp))
        · intro j hj
          exact hterms j (by simp [hj])
  simpa only [Rat.zero_add] using
    hfold (List.range N) 0 (by native_decide) hcell

theorem dyadicNestedRadicalSquareStage_width_le
    (n k : Nat) (hk : k < 2 ^ n) :
    (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k)).width <=
      2 / ((n + 1 : Nat) : Rat) := by
  have hbounds := dyadicNestedRadicalTableAt_bounds n n k (by omega)
  have hwidth := dyadicNestedRadicalStageSinAt_width_le n k hk
  have hbounds' : subintervalOf
      (dyadicNestedRadicalStageSinAt n k) 0 1 := by
    change subintervalOf (dyadicNestedRadicalTableAt n n k).1 0 1
    exact hbounds.1
  unfold rationalSquareInterval QInterval.width at *
  dsimp only at *
  have hfactor :
      (dyadicNestedRadicalStageSinAt n k).hi *
          (dyadicNestedRadicalStageSinAt n k).hi -
          (dyadicNestedRadicalStageSinAt n k).lo *
            (dyadicNestedRadicalStageSinAt n k).lo =
        ((dyadicNestedRadicalStageSinAt n k).hi -
          (dyadicNestedRadicalStageSinAt n k).lo) *
          ((dyadicNestedRadicalStageSinAt n k).hi +
            (dyadicNestedRadicalStageSinAt n k).lo) := by
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.sub_eq_add_neg]
  rw [hfactor]
  have hsum :
      (dyadicNestedRadicalStageSinAt n k).hi +
          (dyadicNestedRadicalStageSinAt n k).lo <= 2 := by
    have hlo1 :
        (dyadicNestedRadicalStageSinAt n k).lo <= 1 :=
      Rat.le_trans hbounds'.2.1 hbounds'.2.2
    have hsum' := rat_add_le_add hbounds'.2.2 hlo1
    grind
  have hgap : 0 <=
      (dyadicNestedRadicalStageSinAt n k).hi -
        (dyadicNestedRadicalStageSinAt n k).lo := by
    have h := (Rat.add_le_add_left (c :=
      -(dyadicNestedRadicalStageSinAt n k).lo)).2 hbounds'.2.1
    have hzero :
        -(dyadicNestedRadicalStageSinAt n k).lo +
            (dyadicNestedRadicalStageSinAt n k).lo = 0 := by
      grind
    rw [hzero] at h
    simpa [Rat.sub_eq_add_neg, Rat.add_comm] using h
  have hscaled := Rat.mul_le_mul_of_nonneg_left hsum hgap
  calc
    ((dyadicNestedRadicalStageSinAt n k).hi -
        (dyadicNestedRadicalStageSinAt n k).lo) *
        ((dyadicNestedRadicalStageSinAt n k).hi +
          (dyadicNestedRadicalStageSinAt n k).lo) <=
        2 * (dyadicNestedRadicalStageSinAt n k).width := by
          simpa [QInterval.width, Rat.mul_comm] using hscaled
    _ <= 2 / ((n + 1 : Nat) : Rat) := by
      have hwidth' := Rat.mul_le_mul_of_nonneg_left
        (by simpa [QInterval.width, Rat.div_def] using hwidth)
        (by native_decide : (0 : Rat) <= 2)
      simpa [QInterval.width, Rat.div_def] using hwidth'

theorem dyadicNestedRadicalSquareStage_ordered
    (n k : Nat) (hk : k < 2 ^ n) :
    0 <= (rationalSquareInterval
      (dyadicNestedRadicalStageSinAt n k)).width := by
  have hbounds : subintervalOf
      (dyadicNestedRadicalStageSinAt n k) 0 1 := by
    change subintervalOf (dyadicNestedRadicalTableAt n n k).1 0 1
    exact (dyadicNestedRadicalTableAt_bounds n n k (by omega)).1
  unfold rationalSquareInterval QInterval.width
  have hgap : 0 <=
      (dyadicNestedRadicalStageSinAt n k).hi -
        (dyadicNestedRadicalStageSinAt n k).lo := by
    have h := (Rat.add_le_add_left (c :=
      -(dyadicNestedRadicalStageSinAt n k).lo)).2 hbounds.2.1
    have hzero :
        -(dyadicNestedRadicalStageSinAt n k).lo +
            (dyadicNestedRadicalStageSinAt n k).lo = 0 := by
      grind
    rw [hzero] at h
    simpa [Rat.sub_eq_add_neg, Rat.add_comm] using h
  have hsum :
      0 <= (dyadicNestedRadicalStageSinAt n k).hi +
        (dyadicNestedRadicalStageSinAt n k).lo := by
    exact Rat.add_nonneg
      (Rat.le_trans hbounds.1 hbounds.2.1) hbounds.1
  have hfactor :
      (dyadicNestedRadicalStageSinAt n k).hi *
          (dyadicNestedRadicalStageSinAt n k).hi -
          (dyadicNestedRadicalStageSinAt n k).lo *
            (dyadicNestedRadicalStageSinAt n k).lo =
        ((dyadicNestedRadicalStageSinAt n k).hi -
          (dyadicNestedRadicalStageSinAt n k).lo) *
          ((dyadicNestedRadicalStageSinAt n k).hi +
            (dyadicNestedRadicalStageSinAt n k).lo) := by
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.sub_eq_add_neg]
  rw [hfactor]
  exact Rat.mul_nonneg hgap hsum

theorem dyadicNestedRadicalSquareLeftSum_ordered
    (n : Nat) :
    0 <= (dyadicNestedRadicalSquareLeftSum n).width := by
  have hmesh : 0 <= mesh 0 ((1 : Rat) / 2) (2 ^ n) :=
    mesh_nonneg_of_le (Nat.pow_pos (by omega)) (by native_decide)
  have hcell : forall k, k ∈ List.range (2 ^ n) ->
      0 <= (QInterval.scaleByRat
        (mesh 0 ((1 : Rat) / 2) (2 ^ n))
        (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k))).width := by
    intro k hk
    rw [QInterval.scaleByRat_width_of_nonneg hmesh]
    exact Rat.mul_nonneg hmesh
      (dyadicNestedRadicalSquareStage_ordered n k (List.mem_range.mp hk))
  unfold dyadicNestedRadicalSquareLeftSum
  rw [RationalPartition.addInterval_fold_width]
  have hzero : ({ lo := 0, hi := 0 } : QInterval).width = 0 := by
    unfold QInterval.width
    grind
  rw [hzero]
  have hfold : forall (xs : List Nat) (initial : Rat),
      0 <= initial ->
      (forall k, k ∈ xs ->
        0 <= (QInterval.scaleByRat
          (mesh 0 ((1 : Rat) / 2) (2 ^ n))
          (rationalSquareInterval
            (dyadicNestedRadicalStageSinAt n k))).width) ->
      0 <= xs.foldl
        (fun total k => total +
          (QInterval.scaleByRat
            (mesh 0 ((1 : Rat) / 2) (2 ^ n))
            (rationalSquareInterval
              (dyadicNestedRadicalStageSinAt n k))).width) initial := by
    intro xs
    induction xs with
    | nil =>
        intro initial hinit hterms
        simpa using hinit
    | cons k xs ih =>
        intro initial hinit hterms
        apply ih (initial +
          (QInterval.scaleByRat
            (mesh 0 ((1 : Rat) / 2) (2 ^ n))
            (rationalSquareInterval
              (dyadicNestedRadicalStageSinAt n k))).width)
        · exact Rat.add_nonneg hinit (hterms k (by simp))
        · intro j hj
          exact hterms j (by simp [hj])
  simpa only [Rat.zero_add] using
    hfold (List.range (2 ^ n)) 0 (by native_decide) hcell

theorem dyadicNestedRadicalSquareLeftSum_width_le_of_stage
    (n : Nat) (eps : Rat)
    (hstage : forall k, k < 2 ^ n ->
      (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k)).width <= eps) :
    (dyadicNestedRadicalSquareLeftSum n).width <= (1 / 2 : Rat) * eps := by
  let N := 2 ^ n
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.pow_pos (by omega)
  have hmesh : 0 <= mesh 0 ((1 : Rat) / 2) N :=
    mesh_nonneg_of_le hN (by native_decide)
  have hsum := RationalPartition.rat_add_fold_le_length_mul (List.range N)
    (fun k =>
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
        (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k))).width)
    (mesh 0 ((1 : Rat) / 2) N * eps) (by
      intro k hk
      have hklt : k < N := List.mem_range.mp hk
      rw [QInterval.scaleByRat_width_of_nonneg hmesh]
      exact Rat.mul_le_mul_of_nonneg_left
        (hstage k (by simpa [N] using hklt)) hmesh)
  calc
    (dyadicNestedRadicalSquareLeftSum n).width =
        (List.range N).foldl
          (fun total k => total +
            (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
              (rationalSquareInterval
                (dyadicNestedRadicalStageSinAt n k))).width) 0 := by
      unfold dyadicNestedRadicalSquareLeftSum
      rw [RationalPartition.addInterval_fold_width]
      have hzero : ({ lo := 0, hi := 0 } : QInterval).width = 0 := by
        unfold QInterval.width
        grind
      rw [hzero]
      simp [N]
      grind
    _ <= (N : Rat) * (mesh 0 ((1 : Rat) / 2) N * eps) := by
      simpa using hsum
    _ = (1 / 2 : Rat) * eps := by
      have hmesh_total := natCast_mul_mesh_eq_sub
        (a := (0 : Rat)) (b := (1 : Rat) / 2) hN
      rw [show (N : Rat) * (mesh 0 ((1 : Rat) / 2) N * eps) =
        ((N : Rat) * mesh 0 ((1 : Rat) / 2) N) * eps by
          grind [Rat.mul_assoc]]
      rw [hmesh_total]
      rw [show (1 / 2 : Rat) - 0 = 1 / 2 by grind]

theorem dyadicNestedRadicalSquareLeftSum_width_le
    (n : Nat) :
    (dyadicNestedRadicalSquareLeftSum n).width <=
      1 / ((n + 1 : Nat) : Rat) := by
  have h := dyadicNestedRadicalSquareLeftSum_width_le_of_stage n
    (2 / ((n + 1 : Nat) : Rat))
    (fun k hk => dyadicNestedRadicalSquareStage_width_le n k hk)
  have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 :=
    Rat.mul_inv_cancel 2 (by native_decide)
  simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, htwo] using h

def dyadicNestedRadicalSquareIntegralRaw : RealRaw where
  compute := dyadicNestedRadicalSquareLeftSum

theorem dyadicNestedRadicalSquareIntegralRaw_widths_shrink :
    RealRaw.WidthsShrinkToZero
      dyadicNestedRadicalSquareIntegralRaw.compute := by
  change RealRaw.WidthsShrinkToZero dyadicNestedRadicalSquareLeftSum
  exact shrinksToZero_of_natOverSuccBound
    (fun n => dyadicNestedRadicalSquareLeftSum_width_le n)

theorem dyadicNestedRadicalSquareIntegralRaw_equiv_of_overlap
    (anchor : RealRaw)
    (hoverlap : forall n,
      QInterval.Overlaps
        (dyadicNestedRadicalSquareLeftSum n) (anchor.compute n)) :
    dyadicNestedRadicalSquareIntegralRaw.Equiv anchor := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  exact (RealRaw.compareAt_overlap_iff
    dyadicNestedRadicalSquareIntegralRaw anchor n n).2 (hoverlap n)

/-! The remaining square change-of-variables certificate is represented by a
rational common witness at every finite stage.  The four inequalities are the
complete proof obligation for transporting the squared dyadic sum to the
tangent-square anchor; no exact value of either integral is included here. -/
structure DyadicNestedRadicalSquareTangentCommonWitness where
  witness : Nat -> Rat
  candidate_lo_le : forall n,
    (dyadicNestedRadicalSquareLeftSum n).lo <= witness n
  witness_le_candidate_hi : forall n,
    witness n <= (dyadicNestedRadicalSquareLeftSum n).hi
  tangent_lo_le : forall n,
    (tangentSquareIntegral.compute n).lo <= witness n
  witness_le_tangent_hi : forall n,
    witness n <= (tangentSquareIntegral.compute n).hi

/- A stagewise overlap is equivalently packaged by choosing the larger lower
endpoint.  Keeping this constructor next to the four inequalities makes the
square route match the public sine transport API. -/
def DyadicNestedRadicalSquareTangentCommonWitness.of_overlap
    (hoverlap : forall n,
      QInterval.Overlaps
        (dyadicNestedRadicalSquareLeftSum n)
        (tangentSquareIntegral.compute n)) :
    DyadicNestedRadicalSquareTangentCommonWitness where
  witness := fun n => max
    (dyadicNestedRadicalSquareLeftSum n).lo
    (tangentSquareIntegral.compute n).lo
  candidate_lo_le := by
    intro n
    rw [Rat.max_def]
    split <;> grind
  witness_le_candidate_hi := by
    intro n
    have hover := hoverlap n
    unfold QInterval.Overlaps at hover
    have hleft :
        (dyadicNestedRadicalSquareLeftSum n).lo <=
          (dyadicNestedRadicalSquareLeftSum n).hi := by
      have hwidth := dyadicNestedRadicalSquareLeftSum_ordered n
      change 0 <=
        (dyadicNestedRadicalSquareLeftSum n).hi -
          (dyadicNestedRadicalSquareLeftSum n).lo at hwidth
      grind
    rw [Rat.max_def]
    split <;> grind
  tangent_lo_le := by
    intro n
    rw [Rat.max_def]
    split <;> grind
  witness_le_tangent_hi := by
    intro n
    have hover := hoverlap n
    unfold QInterval.Overlaps at hover
    have hright :
        (tangentSquareIntegral.compute n).lo <=
          (tangentSquareIntegral.compute n).hi := by
      have hwidth := tangentSquareIntegral_valid.1 n
      change 0 <=
        (tangentSquareIntegral.compute n).hi -
          (tangentSquareIntegral.compute n).lo at hwidth
      grind
    rw [Rat.max_def]
    split <;> grind

theorem DyadicNestedRadicalSquareTangentCommonWitness.to_overlap
    (h : DyadicNestedRadicalSquareTangentCommonWitness) (n : Nat) :
    QInterval.Overlaps
      (dyadicNestedRadicalSquareLeftSum n)
      (tangentSquareIntegral.compute n) := by
  unfold QInterval.Overlaps
  exact ⟨Rat.le_trans (h.candidate_lo_le n)
      (h.witness_le_tangent_hi n),
    Rat.le_trans (h.tangent_lo_le n)
      (h.witness_le_candidate_hi n)⟩

theorem DyadicNestedRadicalSquareTangentCommonWitness.to_equiv
    (h : DyadicNestedRadicalSquareTangentCommonWitness) :
    dyadicNestedRadicalSquareIntegralRaw.Equiv tangentSquareIntegral := by
  exact dyadicNestedRadicalSquareIntegralRaw_equiv_of_overlap
    tangentSquareIntegral h.to_overlap

/-! A direct public-to-anchor transport certificate.  Stagewise overlap is
not transitive, so the public sine-square table cannot obtain an equivalence
to the tangent anchor merely by passing through the nested table.  What is
needed is the stronger, and very concrete, containment certificate below:
each nested interval must lie inside its public counterpart.  The common
witness for the nested route then becomes a common witness for the public
route without introducing any real-number argument. -/
structure DyadicPublicSquareTangentCommonWitness
    (S : ArctanSinPiConstruction) where
  witness : Nat -> Rat
  candidate_lo_le : forall n,
    (dyadicPublicSquareLeftSum S n).lo <= witness n
  witness_le_candidate_hi : forall n,
    witness n <= (dyadicPublicSquareLeftSum S n).hi
  tangent_lo_le : forall n,
    (tangentSquareIntegral.compute n).lo <= witness n
  witness_le_tangent_hi : forall n,
    witness n <= (tangentSquareIntegral.compute n).hi

/- A shared witness is the weakest direct three-way certificate used by the
public route: one rational point lies in the public, nested, and tangent
intervals at every stage.  It avoids assuming that either overlap relation
can be composed transitively. -/
structure DyadicPublicSquareTangentSharedWitness
    (S : ArctanSinPiConstruction) where
  witness : Nat -> Rat
  public_lo_le : forall n,
    (dyadicPublicSquareLeftSum S n).lo <= witness n
  witness_le_public_hi : forall n,
    witness n <= (dyadicPublicSquareLeftSum S n).hi
  nested_lo_le : forall n,
    (dyadicNestedRadicalSquareLeftSum n).lo <= witness n
  witness_le_nested_hi : forall n,
    witness n <= (dyadicNestedRadicalSquareLeftSum n).hi
  tangent_lo_le : forall n,
    (tangentSquareIntegral.compute n).lo <= witness n
  witness_le_tangent_hi : forall n,
    witness n <= (tangentSquareIntegral.compute n).hi

def DyadicPublicSquareTangentSharedWitness.to_public_common_witness
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentSharedWitness S) :
    DyadicPublicSquareTangentCommonWitness S where
  witness := h.witness
  candidate_lo_le := h.public_lo_le
  witness_le_candidate_hi := h.witness_le_public_hi
  tangent_lo_le := h.tangent_lo_le
  witness_le_tangent_hi := h.witness_le_tangent_hi

def DyadicPublicSquareTangentSharedWitness.to_nested_common_witness
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentSharedWitness S) :
    DyadicNestedRadicalSquareTangentCommonWitness where
  witness := h.witness
  candidate_lo_le := h.nested_lo_le
  witness_le_candidate_hi := h.witness_le_nested_hi
  tangent_lo_le := h.tangent_lo_le
  witness_le_tangent_hi := h.witness_le_tangent_hi

structure DyadicPublicSquareTangentTransportWitness
    (S : ArctanSinPiConstruction) where
  nested_tangent : DyadicNestedRadicalSquareTangentCommonWitness
  public_contains_nested : forall n,
    (dyadicPublicSquareLeftSum S n).ContainsInterval
      (dyadicNestedRadicalSquareLeftSum n)

def DyadicPublicSquareTangentTransportWitness.to_public_common_witness
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentTransportWitness S) :
    DyadicPublicSquareTangentCommonWitness S where
  witness := h.nested_tangent.witness
  candidate_lo_le := by
    intro n
    exact Rat.le_trans (h.public_contains_nested n).1
      (h.nested_tangent.candidate_lo_le n)
  witness_le_candidate_hi := by
    intro n
    exact Rat.le_trans (h.nested_tangent.witness_le_candidate_hi n)
      (h.public_contains_nested n).2
  tangent_lo_le := h.nested_tangent.tangent_lo_le
  witness_le_tangent_hi := h.nested_tangent.witness_le_tangent_hi

theorem DyadicPublicSquareTangentCommonWitness.to_overlap
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentCommonWitness S) (n : Nat) :
    QInterval.Overlaps
      (dyadicPublicSquareLeftSum S n)
      (tangentSquareIntegral.compute n) := by
  unfold QInterval.Overlaps
  exact ⟨Rat.le_trans (h.candidate_lo_le n)
      (h.witness_le_tangent_hi n),
    Rat.le_trans (h.tangent_lo_le n)
      (h.witness_le_candidate_hi n)⟩

theorem DyadicPublicSquareTangentTransportWitness.to_public_overlap
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentTransportWitness S) :
    forall n, QInterval.Overlaps
      (dyadicPublicSquareLeftSum S n)
      (tangentSquareIntegral.compute n) := by
  intro n
  exact h.to_public_common_witness.to_overlap n

/- Prefix stabilization is the direct-only implementation of the missing
cross-stage nesting proof.  The anchor is a proof-side object; the stabilized
evaluator itself reads only the square candidate and the rational widths. -/
def dyadicNestedRadicalSquareIntegralRaw_stabilized
    (anchor : RealRaw) : RealRaw :=
  RealRaw.prefixStabilize dyadicNestedRadicalSquareIntegralRaw
    (fun n => (anchor.compute n).width)

theorem dyadicNestedRadicalSquareIntegralRaw_stabilized_width_le
    (anchor : RealRaw) (n : Nat) :
    ((dyadicNestedRadicalSquareIntegralRaw_stabilized anchor).compute n).width <=
      (dyadicNestedRadicalSquareIntegralRaw.compute n).width +
        2 * (anchor.compute n).width := by
  exact RealRaw.prefixStabilize_width_le_current_expand
    dyadicNestedRadicalSquareIntegralRaw
    (fun n => (anchor.compute n).width) n

theorem dyadicNestedRadicalSquareIntegralRaw_stabilized_valid_of_overlap
    {anchor : RealRaw} (hanchor : anchor.Valid)
    (hover : dyadicNestedRadicalSquareIntegralRaw.Equiv anchor) :
    (dyadicNestedRadicalSquareIntegralRaw_stabilized anchor).Valid := by
  apply RealRaw.prefixStabilize_valid
    dyadicNestedRadicalSquareIntegralRaw_widths_shrink hanchor hover
  · intro n
    exact Rat.le_refl
  · exact hanchor.2.2

theorem dyadicNestedRadicalSquareIntegralRaw_stabilized_equiv_anchor_of_overlap
    {anchor : RealRaw} (hanchor : anchor.Valid)
    (hover : dyadicNestedRadicalSquareIntegralRaw.Equiv anchor) :
    (dyadicNestedRadicalSquareIntegralRaw_stabilized anchor).Equiv anchor := by
  apply RealRaw.prefixStabilize_equiv_anchor hanchor hover
  intro n
  exact Rat.le_refl

/-! The concrete common-anchor interface for the `sin²` target.  The only
remaining evaluator-specific proposition is the overlap hypothesis below;
once it is supplied, validity and equivalence of the stabilized dyadic
integral are automatic consequences of the finite width certificate. -/

theorem dyadicNestedRadicalSquareIntegralRaw_stabilized_valid_of_tangentSquareIntegral_overlap
    (hover : dyadicNestedRadicalSquareIntegralRaw.Equiv tangentSquareIntegral) :
    (dyadicNestedRadicalSquareIntegralRaw_stabilized tangentSquareIntegral).Valid := by
  exact dyadicNestedRadicalSquareIntegralRaw_stabilized_valid_of_overlap
    tangentSquareIntegral_valid hover

theorem dyadicNestedRadicalSquareIntegralRaw_stabilized_equiv_tangentSquareIntegral
    (hover : dyadicNestedRadicalSquareIntegralRaw.Equiv tangentSquareIntegral) :
    (dyadicNestedRadicalSquareIntegralRaw_stabilized tangentSquareIntegral).Equiv
      tangentSquareIntegral := by
  exact dyadicNestedRadicalSquareIntegralRaw_stabilized_equiv_anchor_of_overlap
    tangentSquareIntegral_valid hover

theorem dyadicNestedRadicalSquareIntegralRaw_stabilized_equiv_value_of_anchor
    (hover : dyadicNestedRadicalSquareIntegralRaw.Equiv tangentSquareIntegral)
    (hvalue : tangentSquareIntegral.Equiv (RealRaw.ofRat (1 / 4))) :
    (dyadicNestedRadicalSquareIntegralRaw_stabilized tangentSquareIntegral).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  exact RealRaw.equiv_trans
    (dyadicNestedRadicalSquareIntegralRaw_stabilized_valid_of_tangentSquareIntegral_overlap
      hover)
    tangentSquareIntegral_valid (RealRaw.ofRat_valid _)
    (dyadicNestedRadicalSquareIntegralRaw_stabilized_equiv_tangentSquareIntegral
      hover)
    hvalue

theorem DyadicNestedRadicalSquareTangentCommonWitness.stabilized_equiv_value
    (h : DyadicNestedRadicalSquareTangentCommonWitness)
    (hvalue : tangentSquareIntegral.Equiv (RealRaw.ofRat (1 / 4))) :
    (dyadicNestedRadicalSquareIntegralRaw_stabilized
      tangentSquareIntegral).Equiv (RealRaw.ofRat (1 / 4)) := by
  exact dyadicNestedRadicalSquareIntegralRaw_stabilized_equiv_value_of_anchor
    h.to_equiv hvalue

/- The finite rational-circle identity used by the future primitive proof.
   Keeping this as an algebraic theorem makes the intended `sin²` route
   explicit before any interval-level cosine transport is added. -/
theorem rationalCircleSin_sq_eq_one_sub_cos_sq (u : Rat) :
    rationalCircleSin u * rationalCircleSin u =
      1 - rationalCircleCos u * rationalCircleCos u := by
  have h := rationalCircleSin_sq_add_cos_sq u
  grind

/-! A box-level form of the circle identity.  It is intentionally stated for
rational witness values: the later nested-radical transport supplies such
witnesses through its tangent-box overlap certificates. -/

theorem rationalSquareInterval_overlap_of_interval_overlap
    {I J : QInterval}
    (hI : subintervalOf I 0 1)
    (hJ : subintervalOf J 0 1)
    (hover : QInterval.Overlaps I J) :
    QInterval.Overlaps (rationalSquareInterval I)
      (rationalSquareInterval J) := by
  have hIlo : 0 <= I.lo := hI.1
  have hJlo : 0 <= J.lo := hJ.1
  have hIhi : I.hi <= 1 := hI.2.2
  have hJhi : J.hi <= 1 := hJ.2.2
  have hIorder : I.lo <= I.hi := hI.2.1
  have hJorder : J.lo <= J.hi := hJ.2.1
  have hsquare_mono {a b : Rat} (ha : 0 <= a) (hab : a <= b) :
      a * a <= b * b := by
    have hb : 0 <= b := Rat.le_trans ha hab
    exact Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_left hab ha)
      (Rat.mul_le_mul_of_nonneg_right hab hb)
  unfold rationalSquareInterval QInterval.Overlaps
  constructor
  · exact hsquare_mono hIlo hover.1
  · exact hsquare_mono hJlo hover.2

theorem rationalSquareInterval_mul_self_eq
    {I : QInterval} (hI : subintervalOf I 0 1) :
    QBox.mulRealInterval I.lo I.hi I.lo I.hi =
      rationalSquareInterval I := by
  have horder : I.lo <= I.hi := hI.2.1
  unfold rationalSquareInterval
  exact QBox.mulRealInterval_self_of_nonneg hI.1 horder

theorem sinPiSquareOnHalf_compute_of_mem
    (S : ArctanSinPiConstruction) {x : Rat}
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    (sinPiSquareOnHalf S).compute x n =
      QBox.mulRealInterval
        ((sinPiRawOfArctan S.inverse x hx).compute n).lo
        ((sinPiRawOfArctan S.inverse x hx).compute n).hi
        ((sinPiRawOfArctan S.inverse x hx).compute n).lo
        ((sinPiRawOfArctan S.inverse x hx).compute n).hi := by
  change QBox.mulRealInterval
      ((sinPiOnHalfRaw S).compute x n).lo
      ((sinPiOnHalfRaw S).compute x n).hi
      ((sinPiOnHalfRaw S).compute x n).lo
      ((sinPiOnHalfRaw S).compute x n).hi = _
  rw [show (sinPiOnHalfRaw S).compute x n =
      (sinPiRawOfArctan S.inverse x hx).compute n by
        simp [sinPiOnHalfRaw, hx]]

theorem sinPiSquare_sample_overlap_of_sine_and_table_overlap
    (S : ArctanSinPiConstruction) {x : Rat}
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat)
    {T : QInterval}
    (hT : subintervalOf T 0 1)
    (hsample : QInterval.Overlaps
      ((sinPiRawOfArctan S.inverse x hx).compute n) T) :
    QInterval.Overlaps
      ((sinPiSquareOnHalf S).compute x n)
      (rationalSquareInterval T) := by
  have hS : subintervalOf
      ((sinPiRawOfArctan S.inverse x hx).compute n) 0 1 := by
    have hb := S.sinPiRawOfArctan_bounds hx n
    have hv := S.sin_valid x hx
    have ho := RealRaw.interval_order_of_valid
      (x := (sinPiRawOfArctan S.inverse x hx)) hv n
    exact ⟨hb.1, ho, hb.2⟩
  rw [sinPiSquareOnHalf_compute_of_mem S hx n,
    rationalSquareInterval_mul_self_eq hS]
  exact rationalSquareInterval_overlap_of_interval_overlap
    hS hT hsample

theorem sinPiSquare_nestedRadicalStage_sample_overlap_of_canonical_box_search
    (S : ArctanSinPiConstruction)
    {n k : Nat} (hk : k < 2 ^ n) (m : Nat) (u : Rat)
    (hsearch : rationalTangentWitnessBoxSearch
      (dyadicTangentBox S.inverse hk)
      (dyadicNestedRadicalStageSinAt n k) m = some u) :
    QInterval.Overlaps
      ((sinPiSquareOnHalf S).compute
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n)
      (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k)) := by
  have hsin :=
    arctanSinPi_nestedRadicalStage_sample_overlap_of_canonical_box_search
      S.inverse hk m u hsearch
  exact sinPiSquare_sample_overlap_of_sine_and_table_overlap S
    (dyadicHalfDomain hk) n
    (by
      change subintervalOf
        (dyadicNestedRadicalTableAt n n k).1 0 1
      exact (dyadicNestedRadicalTableAt_bounds n n k
        (Nat.le_of_lt hk)).1)
    (by simpa [sinPiSquareOnHalf, sinPiOnHalfRaw] using hsin)

/- A successful finite tangent-box search at every dyadic sample is enough to
assemble the entire square-sum overlap.  The search family remains explicit:
each member supplies its own finite search depth and rational witness. -/
theorem dyadicPublicSquareLeftSum_overlap_of_canonical_search_family
    (S : ArctanSinPiConstruction)
    (hsearch : forall (n k : Nat) (hk : k < 2 ^ n),
      ∃ m u,
        rationalTangentWitnessBoxSearch
          (dyadicTangentBox S.inverse hk)
          (dyadicNestedRadicalStageSinAt n k) m = some u) :
    forall n,
      QInterval.Overlaps
        (dyadicPublicSquareLeftSum S n)
        (dyadicNestedRadicalSquareLeftSum n) := by
  intro n
  apply dyadicPublicSquareLeftSum_overlap_of_sample_overlaps S n
  intro k hk
  obtain ⟨m, u, hmu⟩ := hsearch n k hk
  exact sinPiSquare_nestedRadicalStage_sample_overlap_of_canonical_box_search
    S hk m u hmu

/- The geometric form of the remaining obligation.  At positive samples it
asks only for overlap of the rational-circle sine image with the nested
radical box; the zero sample is discharged by the exact endpoint search. -/
theorem dyadicPublicSquareLeftSum_overlap_of_rational_circle_overlap_family
    (S : ArctanSinPiConstruction)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hover : forall (n k : Nat) (hk : k < 2 ^ n),
      0 < k ->
      QInterval.Overlaps
        (rationalCircleSinInterval (dyadicTangentBox S.inverse hk))
        (dyadicNestedRadicalStageSinAt n k)) :
    forall n,
      QInterval.Overlaps
        (dyadicPublicSquareLeftSum S n)
        (dyadicNestedRadicalSquareLeftSum n) := by
  apply dyadicPublicSquareLeftSum_overlap_of_canonical_search_family S
  intro n k hk
  by_cases hkzero : k = 0
  · subst k
    obtain ⟨u, hu⟩ := canonical_dyadic_zero_search S.inverse ht0 n
    have hzero : dyadicNestedRadicalStageSinAt n 0 =
        ({ lo := 0, hi := 0 } : QInterval) := by
      change (dyadicNestedRadicalTableAt n n 0).1 = _
      exact dyadicNestedRadicalTableAt_zero_sin n n
    exact ⟨0, u, by simpa [hzero] using hu⟩
  · exact canonical_dyadic_search_of_overlap_of_interior S.inverse hk
      (by omega) (hover n k hk (by omega))

/- Named proof data for the remaining geometric step.  Keeping the family as
a structure makes the positive-sample obligation easy to instantiate and
prevents downstream developments from depending on the internal theorem
argument order. -/
structure DyadicSquareCircleOverlapFamily
    (S : ArctanSinPiConstruction) where
  endpoint_zero :
    (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero
  positive_overlap : forall (n k : Nat) (hk : k < 2 ^ n),
    0 < k ->
    QInterval.Overlaps
      (rationalCircleSinInterval (dyadicTangentBox S.inverse hk))
      (dyadicNestedRadicalStageSinAt n k)

def DyadicSquareCircleOverlapFamily.of_halfAngle_certificate_family
    (S : ArctanSinPiConstruction)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hcertificate : forall (n k : Nat) (hk : k < 2 ^ n),
      0 < k -> CanonicalDyadicHalfAngleCertificate S.inverse n k hk) :
    DyadicSquareCircleOverlapFamily S where
  endpoint_zero := ht0
  positive_overlap := by
    intro n k hk hpos
    exact canonical_dyadic_overlap_of_halfAngle_outer_tangent
      S.inverse hk
      (hcertificate n k hk hpos).cosineBox_subinterval
      (hcertificate n k hk hpos).outer_tangent_contains
      (hcertificate n k hk hpos).sine_nonneg
      (hcertificate n k hk hpos).cosine_nonneg
      (hcertificate n k hk hpos).circle_identity
      (hcertificate n k hk hpos).sine_contains
      (hcertificate n k hk hpos).cosine_contains

/- Precision-aware geometric proofs naturally produce certificates for every
   evaluator precision.  The native-precision bridge in `SinPiIntegral`
   packages that family into the stage-indexed form used by this module. -/
def DyadicSquareCircleOverlapFamily.of_precision_halfAngle_certificate_family
    (S : ArctanSinPiConstruction)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hcertificate : forall (precision n k : Nat) (hk : k < 2 ^ n),
      0 < k -> CanonicalDyadicHalfAngleCertificateAt S.inverse precision n k hk) :
    DyadicSquareCircleOverlapFamily S := by
  exact DyadicSquareCircleOverlapFamily.of_halfAngle_certificate_family S ht0
    (canonical_dyadic_halfAngle_certificate_family_of_precision_family
      S.inverse hcertificate)

theorem DyadicSquareCircleOverlapFamily.of_branch_certificate_family
    (S : ArctanSinPiConstruction)
    (family : DyadicNestedRadicalBranchCertificateFamily S.inverse) :
    DyadicSquareCircleOverlapFamily S := by
  exact {
    endpoint_zero := family.endpoint_zero
    positive_overlap := by
      intro n k hk hpos
      exact family.rational_circle_overlap n n k hk
  }

theorem DyadicSquareCircleOverlapFamily.to_square_sum_overlap
    {S : ArctanSinPiConstruction}
    (certificate : DyadicSquareCircleOverlapFamily S) :
    forall n,
      QInterval.Overlaps
        (dyadicPublicSquareLeftSum S n)
        (dyadicNestedRadicalSquareLeftSum n) := by
  exact dyadicPublicSquareLeftSum_overlap_of_rational_circle_overlap_family
    S certificate.endpoint_zero certificate.positive_overlap

/- The intended geometric interface: the existing canonical half-angle
certificate family is enough to drive the square-sum transport. -/
theorem dyadicPublicSquareLeftSum_overlap_of_halfAngle_certificate_family
    (S : ArctanSinPiConstruction)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (hcertificate : forall (n k : Nat) (hk : k < 2 ^ n),
      0 < k -> CanonicalDyadicHalfAngleCertificate S.inverse n k hk) :
    forall n,
      QInterval.Overlaps
        (dyadicPublicSquareLeftSum S n)
        (dyadicNestedRadicalSquareLeftSum n) := by
  apply dyadicPublicSquareLeftSum_overlap_of_canonical_search_family S
  intro n k hk
  exact canonical_dyadic_search_of_halfAngle_certificate_family
    S.inverse ht0 hcertificate n k hk

theorem dyadicPublicSquareLeftSum_overlap_of_branch_certificate_family
    (S : ArctanSinPiConstruction)
    (family : DyadicNestedRadicalBranchCertificateFamily S.inverse) :
    forall n,
      QInterval.Overlaps
        (dyadicPublicSquareLeftSum S n)
        (dyadicNestedRadicalSquareLeftSum n) := by
  exact (DyadicSquareCircleOverlapFamily.of_branch_certificate_family S family).to_square_sum_overlap

theorem square_sample_overlap_of_sine_sample_overlap
    {I J : QInterval}
    (hI : subintervalOf I 0 1)
    (hJ : subintervalOf J 0 1)
    (hover : QInterval.Overlaps I J) :
    QInterval.Overlaps
      (QBox.mulRealInterval I.lo I.hi I.lo I.hi)
      (QBox.mulRealInterval J.lo J.hi J.lo J.hi) := by
  rw [rationalSquareInterval_mul_self_eq hI,
    rationalSquareInterval_mul_self_eq hJ]
  exact rationalSquareInterval_overlap_of_interval_overlap hI hJ hover

theorem rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle
    {S C : QInterval} {s c : Rat}
    (hS : subintervalOf S 0 1) (hC : subintervalOf C 0 1)
    (hs : S.lo <= s ∧ s <= S.hi) (hc : C.lo <= c ∧ c <= C.hi)
    (hcircle : s * s + c * c = 1) :
    QInterval.Overlaps (rationalSquareInterval S)
      (rationalOneMinusSquareInterval C) := by
  have hSlo : 0 <= S.lo := hS.1
  have hChi : C.hi <= 1 := hC.2.2
  have hs0 : 0 <= s := Rat.le_trans hSlo hs.1
  have hc0 : 0 <= c := Rat.le_trans hC.1 hc.1
  have Shi0 : 0 <= S.hi := Rat.le_trans hSlo hS.2.1
  have Clo0 : 0 <= C.lo := hC.1
  have Chi0 : 0 <= C.hi := Rat.le_trans Clo0 hC.2.1
  have hSsq_lo : S.lo * S.lo <= s * s := by
    have h := Rat.mul_le_mul_of_nonneg_right hs.1
      (Rat.add_nonneg hs0 hSlo)
    grind [Rat.mul_add, Rat.add_mul]
  have hSsq_hi : s * s <= S.hi * S.hi := by
    have h := Rat.mul_le_mul_of_nonneg_right hs.2
      (Rat.add_nonneg hs0 Shi0)
    grind [Rat.mul_add, Rat.add_mul]
  have hCsq_lo : C.lo * C.lo <= c * c := by
    have h := Rat.mul_le_mul_of_nonneg_right hc.1
      (Rat.add_nonneg hc0 Clo0)
    grind [Rat.mul_add, Rat.add_mul]
  have hCsq_hi : c * c <= C.hi * C.hi := by
    have h := Rat.mul_le_mul_of_nonneg_right hc.2
      (Rat.add_nonneg hc0 Chi0)
    grind [Rat.mul_add, Rat.add_mul]
  have hsquare_mem :
      S.lo * S.lo <= s * s ∧ s * s <= S.hi * S.hi :=
    ⟨hSsq_lo, hSsq_hi⟩
  have hcomplement_mem :
      1 - C.hi * C.hi <= 1 - c * c ∧
        1 - c * c <= 1 - C.lo * C.lo := by
    constructor <;> grind
  unfold rationalSquareInterval rationalOneMinusSquareInterval
    QInterval.Overlaps
  change S.lo * S.lo <= 1 - C.lo * C.lo ∧
    1 - C.hi * C.hi <= S.hi * S.hi
  constructor
  · calc
      S.lo * S.lo <= s * s := hsquare_mem.1
      _ = 1 - c * c := by grind
      _ <= 1 - C.lo * C.lo := hcomplement_mem.2
  · calc
      1 - C.hi * C.hi <= 1 - c * c := hcomplement_mem.1
      _ = s * s := by grind
      _ <= S.hi * S.hi := hsquare_mem.2

/-! A square-aware variant of the finite tangent search.  The existing search
checks only the sine box; this predicate checks both circle coordinates, so a
successful result can be consumed by the square/complement transport above. -/

def rationalTangentSquareWitnessAdmissibleBool
    (U S C : QInterval) (u : Rat) : Bool :=
  (U.lo <= u) && (u <= U.hi) &&
    (S.lo <= rationalCircleSin u) &&
    (rationalCircleSin u <= S.hi) &&
    (C.lo <= rationalCircleCos u) &&
    (rationalCircleCos u <= C.hi)

def rationalTangentSquareWitnessSearchList
    (U S C : QInterval) : List Rat -> Option Rat
  | [] => none
  | u :: us =>
      if rationalTangentSquareWitnessAdmissibleBool U S C u then some u
      else rationalTangentSquareWitnessSearchList U S C us

theorem rationalTangentSquareWitnessSearchList_sound
    {U S C : QInterval} {us : List Rat} {u : Rat}
    (h : rationalTangentSquareWitnessSearchList U S C us = some u) :
    rationalTangentSquareWitnessAdmissibleBool U S C u = true := by
  induction us with
  | nil => simp [rationalTangentSquareWitnessSearchList] at h
  | cons v vs ih =>
      simp only [rationalTangentSquareWitnessSearchList] at h
      split at h
      · cases h
        assumption
      · exact ih h

theorem rationalTangentSquareWitnessSearchList_complete
    {U S C : QInterval} {us : List Rat} {u : Rat}
    (hmem : u ∈ us)
    (hadm : rationalTangentSquareWitnessAdmissibleBool U S C u = true) :
    ∃ v, rationalTangentSquareWitnessSearchList U S C us = some v := by
  induction us with
  | nil => simp at hmem
  | cons q qs ih =>
      simp only [List.mem_cons] at hmem
      simp only [rationalTangentSquareWitnessSearchList]
      split
      · exact ⟨q, rfl⟩
      · rcases hmem with rfl | hmem
        · contradiction
        · exact ih hmem

def rationalTangentSquareWitnessSearch
    (U S C : QInterval) (m : Nat) : Option Rat :=
  rationalTangentSquareWitnessSearchList U S C
    (rationalTangentWitnessBoxGrid U m)

theorem rationalTangentSquareWitnessSearch_complete_of_grid_candidate
    {U S C : QInterval} (m k : Nat) (hk : k <= 2 ^ m)
    (hadm : rationalTangentSquareWitnessAdmissibleBool U S C
      (U.lo + U.width * ((k : Rat) / ((2 ^ m : Nat) : Rat))) = true) :
    ∃ v, rationalTangentSquareWitnessSearch U S C m = some v := by
  apply rationalTangentSquareWitnessSearchList_complete
    (u := U.lo + U.width * ((k : Rat) / ((2 ^ m : Nat) : Rat)))
  · unfold rationalTangentWitnessBoxGrid
    let N := 2 ^ m
    have hk' : k < N + 1 := by dsimp [N]; omega
    apply List.mem_map.mpr
    exact ⟨k, by simpa using hk', rfl⟩
  · exact hadm

/-! Package the executable side of the squared-sine witness search.  The
geometric proof may choose a different grid depth and index at each requested
stage; once those finite choices are certified admissible, the search itself
is available uniformly.  This structure contains no limit object and does not
claim that the witnesses have already been constructed. -/
structure RationalTangentSquareWitnessCandidateFamily
    (U S C : QInterval) where
  gridDepth : Nat -> Nat
  gridIndex : Nat -> Nat
  gridIndex_le : forall n, gridIndex n <= 2 ^ gridDepth n
  admissible : forall n,
    rationalTangentSquareWitnessAdmissibleBool U S C
      (U.lo + U.width *
        ((gridIndex n : Rat) / ((2 ^ gridDepth n : Nat) : Rat))) = true

theorem RationalTangentSquareWitnessCandidateFamily.search_exists
    {U S C : QInterval}
    (h : RationalTangentSquareWitnessCandidateFamily U S C) :
    forall n, ∃ v, rationalTangentSquareWitnessSearch U S C
      (h.gridDepth n) = some v := by
  intro n
  exact rationalTangentSquareWitnessSearch_complete_of_grid_candidate
    (h.gridDepth n) (h.gridIndex n) (h.gridIndex_le n) (h.admissible n)

theorem rationalTangentSquareWitnessSearch_sound
    {U S C : QInterval} {m : Nat} {u : Rat}
    (h : rationalTangentSquareWitnessSearch U S C m = some u) :
    U.lo <= u /\ u <= U.hi /\
      S.lo <= rationalCircleSin u /\ rationalCircleSin u <= S.hi /\
      C.lo <= rationalCircleCos u /\ rationalCircleCos u <= C.hi := by
  have hb := rationalTangentSquareWitnessSearchList_sound h
  simp only [rationalTangentSquareWitnessAdmissibleBool,
    Bool.and_eq_true] at hb
  refine ⟨of_decide_eq_true hb.1.1.1.1.1,
    of_decide_eq_true hb.1.1.1.1.2,
    of_decide_eq_true hb.1.1.1.2,
    of_decide_eq_true hb.1.1.2,
    of_decide_eq_true hb.1.2,
    of_decide_eq_true hb.2⟩

theorem square_overlap_of_rationalTangentSquareWitnessSearch
    {U S C : QInterval} {m : Nat} {u : Rat}
    (hsearch : rationalTangentSquareWitnessSearch U S C m = some u)
    (hS : subintervalOf S 0 1)
    (hC : subintervalOf C 0 1) :
    QInterval.Overlaps (rationalSquareInterval S)
      (rationalOneMinusSquareInterval C) := by
  have hs := rationalTangentSquareWitnessSearch_sound hsearch
  apply rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle
    hS hC
  · exact ⟨hs.2.2.1, hs.2.2.2.1⟩
  · exact ⟨hs.2.2.2.2.1, hs.2.2.2.2.2⟩
  · exact rationalCircleSin_sq_add_cos_sq _

theorem signed_square_overlap_of_rationalTangentSquareWitnessSearch
    {U S C : QInterval} {m : Nat} {u : Rat}
    (hsearch : rationalTangentSquareWitnessSearch U S C m = some u)
    (hS : subintervalOf S 0 1)
    (hC : subintervalOf C (-1) 1) :
    QInterval.Overlaps (rationalSquareInterval S)
      (rationalOneMinusSquareIntervalSigned C) := by
  have hs := rationalTangentSquareWitnessSearch_sound hsearch
  apply rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle_signed
    hS hC
  · exact ⟨hs.2.2.1, hs.2.2.2.1⟩
  · exact ⟨hs.2.2.2.2.1, hs.2.2.2.2.2⟩
  · exact rationalCircleSin_sq_add_cos_sq _

/-! Consume a stagewise candidate family at the interval level.  The search
family supplies the finite rational witness, while the two adapters below
turn its soundness into the square-overlap facts used by the integral
transport.  The family itself remains the place where geometric construction
data is supplied. -/
theorem RationalTangentSquareWitnessCandidateFamily.square_overlap
    {U S C : QInterval}
    (h : RationalTangentSquareWitnessCandidateFamily U S C)
    (hS : subintervalOf S 0 1) (hC : subintervalOf C 0 1) :
    forall n : Nat, QInterval.Overlaps (rationalSquareInterval S)
      (rationalOneMinusSquareInterval C) := by
  intro n
  obtain ⟨v, hv⟩ := h.search_exists n
  exact square_overlap_of_rationalTangentSquareWitnessSearch hv hS hC

theorem RationalTangentSquareWitnessCandidateFamily.signed_square_overlap
    {U S C : QInterval}
    (h : RationalTangentSquareWitnessCandidateFamily U S C)
    (hS : subintervalOf S 0 1) (hC : subintervalOf C (-1) 1) :
    forall n : Nat, QInterval.Overlaps (rationalSquareInterval S)
      (rationalOneMinusSquareIntervalSigned C) := by
  intro n
  obtain ⟨v, hv⟩ := h.search_exists n
  exact signed_square_overlap_of_rationalTangentSquareWitnessSearch hv hS hC

/-! The integral-facing form allows all three rational boxes to vary with the
requested stage.  This is the schedule used by an eventual equal-dyadic
transport; the preceding fixed-box family remains convenient for local
regression examples. -/
structure RationalTangentSquareWitnessSchedule where
  tangentBox : Nat -> QInterval
  sineBox : Nat -> QInterval
  cosineBox : Nat -> QInterval
  gridDepth : Nat -> Nat
  gridIndex : Nat -> Nat
  gridIndex_le : forall n, gridIndex n <= 2 ^ gridDepth n
  admissible : forall n,
    rationalTangentSquareWitnessAdmissibleBool (tangentBox n)
      (sineBox n) (cosineBox n)
      ((tangentBox n).lo + (tangentBox n).width *
        ((gridIndex n : Rat) / ((2 ^ gridDepth n : Nat) : Rat))) = true

theorem RationalTangentSquareWitnessSchedule.search_exists
    (h : RationalTangentSquareWitnessSchedule) :
    forall n, ∃ v, rationalTangentSquareWitnessSearch (h.tangentBox n)
      (h.sineBox n) (h.cosineBox n) (h.gridDepth n) = some v := by
  intro n
  exact rationalTangentSquareWitnessSearch_complete_of_grid_candidate
    (U := h.tangentBox n) (S := h.sineBox n) (C := h.cosineBox n)
    (h.gridDepth n) (h.gridIndex n) (h.gridIndex_le n) (h.admissible n)

theorem RationalTangentSquareWitnessSchedule.square_overlap
    (h : RationalTangentSquareWitnessSchedule)
    (hS : forall n, subintervalOf (h.sineBox n) 0 1)
    (hC : forall n, subintervalOf (h.cosineBox n) 0 1) :
    forall n, QInterval.Overlaps
      (rationalSquareInterval (h.sineBox n))
      (rationalOneMinusSquareInterval (h.cosineBox n)) := by
  intro n
  obtain ⟨v, hv⟩ := h.search_exists n
  exact square_overlap_of_rationalTangentSquareWitnessSearch hv
    (hS n) (hC n)

theorem RationalTangentSquareWitnessSchedule.signed_square_overlap
    (h : RationalTangentSquareWitnessSchedule)
    (hS : forall n, subintervalOf (h.sineBox n) 0 1)
    (hC : forall n, subintervalOf (h.cosineBox n) (-1) 1) :
    forall n, QInterval.Overlaps
      (rationalSquareInterval (h.sineBox n))
      (rationalOneMinusSquareIntervalSigned (h.cosineBox n)) := by
  intro n
  obtain ⟨v, hv⟩ := h.search_exists n
  exact signed_square_overlap_of_rationalTangentSquareWitnessSearch hv
    (hS n) (hC n)

/-! The equal-dyadic integral needs the same finite contract cell by cell.
This family therefore indexes the three boxes and the finite grid choice by
`(n,k)`, with the proof `hk : k < 2^n` retained as ordinary domain data. -/
structure RationalTangentSquareWitnessCellFamily where
  tangentBox : (n k : Nat) -> k < 2 ^ n -> QInterval
  sineBox : (n k : Nat) -> k < 2 ^ n -> QInterval
  cosineBox : (n k : Nat) -> k < 2 ^ n -> QInterval
  gridDepth : (n k : Nat) -> k < 2 ^ n -> Nat
  gridIndex : (n k : Nat) -> k < 2 ^ n -> Nat
  gridIndex_le : forall (n k : Nat) (hk : k < 2 ^ n),
    gridIndex n k hk <= 2 ^ gridDepth n k hk
  admissible : forall (n k : Nat) (hk : k < 2 ^ n),
    rationalTangentSquareWitnessAdmissibleBool
      (tangentBox n k hk) (sineBox n k hk) (cosineBox n k hk)
      ((tangentBox n k hk).lo + (tangentBox n k hk).width *
        ((gridIndex n k hk : Rat) /
          ((2 ^ gridDepth n k hk : Nat) : Rat))) = true
  sine_subinterval : forall (n k : Nat) (hk : k < 2 ^ n),
    subintervalOf (sineBox n k hk) 0 1
  cosine_subinterval : forall (n k : Nat) (hk : k < 2 ^ n),
    subintervalOf (cosineBox n k hk) (-1) 1

theorem RationalTangentSquareWitnessCellFamily.search_exists
    (h : RationalTangentSquareWitnessCellFamily) (n k : Nat)
    (hk : k < 2 ^ n) :
    ∃ v, rationalTangentSquareWitnessSearch (h.tangentBox n k hk)
      (h.sineBox n k hk) (h.cosineBox n k hk)
      (h.gridDepth n k hk) = some v := by
  exact rationalTangentSquareWitnessSearch_complete_of_grid_candidate
    (U := h.tangentBox n k hk) (S := h.sineBox n k hk)
    (C := h.cosineBox n k hk) (h.gridDepth n k hk)
    (h.gridIndex n k hk) (h.gridIndex_le n k hk)
    (h.admissible n k hk)

theorem RationalTangentSquareWitnessCellFamily.square_overlap
    (h : RationalTangentSquareWitnessCellFamily) (n k : Nat)
    (hk : k < 2 ^ n) :
    QInterval.Overlaps (rationalSquareInterval (h.sineBox n k hk))
      (rationalOneMinusSquareIntervalSigned (h.cosineBox n k hk)) := by
  obtain ⟨v, hv⟩ := h.search_exists n k hk
  exact signed_square_overlap_of_rationalTangentSquareWitnessSearch hv
    (h.sine_subinterval n k hk) (h.cosine_subinterval n k hk)

theorem dyadicNestedRadicalStageSinAt_subinterval
    (n k : Nat) (hk : k < 2 ^ n) :
    subintervalOf (dyadicNestedRadicalStageSinAt n k) 0 1 := by
  simpa [dyadicNestedRadicalStageSinAt, dyadicNestedRadicalStageTable] using
    (dyadicNestedRadicalTableAt_bounds n n k (Nat.le_of_lt hk)).1

theorem dyadicNestedRadicalStageCosAt_subinterval
    (n k : Nat) (hk : k < 2 ^ n) :
    subintervalOf (dyadicNestedRadicalStageTable n k).2 (-1) 1 := by
  simpa [dyadicNestedRadicalStageTable] using
    (dyadicNestedRadicalTableAt_bounds n n k (Nat.le_of_lt hk)).2

theorem dyadicNestedRadicalStage_square_complement_overlap_of_search_family
    (U : Nat → Nat → QInterval)
    (hsearch : ∀ (n k : Nat) (hk : k < 2 ^ n),
      ∃ m u, rationalTangentSquareWitnessSearch (U n k)
        (dyadicNestedRadicalStageSinAt n k)
        (dyadicNestedRadicalStageTable n k).2 m = some u)
    :
    ∀ (n k : Nat) (hk : k < 2 ^ n),
      QInterval.Overlaps
        (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k))
        (rationalOneMinusSquareIntervalSigned
          (dyadicNestedRadicalStageTable n k).2) := by
  intro n k hk
  obtain ⟨m, u, hmu⟩ := hsearch n k hk
  exact signed_square_overlap_of_rationalTangentSquareWitnessSearch hmu
    (dyadicNestedRadicalStageSinAt_subinterval n k hk)
    (dyadicNestedRadicalStageCosAt_subinterval n k hk)

/-! A concrete square-aware search checkpoint.  At the first nonzero dyadic
sample, the same rational witness used by the sine search also certifies the
cosine enclosure, so the square/complement transport can be checked directly.
This is a regression anchor for the later uniform witness family. -/
theorem rationalTangentSquareWitnessSearch_stage_one_demo :
    rationalTangentSquareWitnessSearch
      ({ lo := 0, hi := 1 } : QInterval)
      (dyadicNestedRadicalStageSinAt 1 1)
      (dyadicNestedRadicalStageTable 1 1).2 8 = some ((103 : Rat) / 256) := by
  native_decide

theorem dyadicNestedRadicalStage_one_square_complement_overlap :
    QInterval.Overlaps
      (rationalSquareInterval (dyadicNestedRadicalStageSinAt 1 1))
      (rationalOneMinusSquareInterval
        (dyadicNestedRadicalStageTable 1 1).2) := by
  have hsearch := rationalTangentSquareWitnessSearch_stage_one_demo
  have hS : subintervalOf (dyadicNestedRadicalStageSinAt 1 1) 0 1 := by
    unfold subintervalOf
    constructor
    · native_decide
    constructor <;> native_decide
  have hC : subintervalOf (dyadicNestedRadicalStageTable 1 1).2 0 1 := by
    unfold subintervalOf
    constructor
    · native_decide
    constructor <;> native_decide
  exact square_overlap_of_rationalTangentSquareWitnessSearch hsearch hS hC

/-! The next dyadic level is checked at a finer finite grid.  These two
checkpoints cover the interior samples at `k = 1` and `k = 2`; they are
deliberately executable facts, not an approximation claim for all stages. -/
theorem rationalTangentSquareWitnessSearch_stage_two_left_demo :
    rationalTangentSquareWitnessSearch
      ({ lo := 0, hi := 1 } : QInterval)
      (dyadicNestedRadicalStageSinAt 2 1)
      (dyadicNestedRadicalStageTable 2 1).2 16 =
        some ((1581 : Rat) / 8192) := by
  native_decide

theorem dyadicNestedRadicalStage_two_left_square_complement_overlap :
    QInterval.Overlaps
      (rationalSquareInterval (dyadicNestedRadicalStageSinAt 2 1))
      (rationalOneMinusSquareInterval
        (dyadicNestedRadicalStageTable 2 1).2) := by
  have hsearch := rationalTangentSquareWitnessSearch_stage_two_left_demo
  have hS : subintervalOf (dyadicNestedRadicalStageSinAt 2 1) 0 1 := by
    unfold subintervalOf
    constructor
    · native_decide
    constructor <;> native_decide
  have hC : subintervalOf (dyadicNestedRadicalStageTable 2 1).2 0 1 := by
    unfold subintervalOf
    constructor
    · native_decide
    constructor <;> native_decide
  exact square_overlap_of_rationalTangentSquareWitnessSearch hsearch hS hC

theorem rationalTangentSquareWitnessSearch_stage_two_middle_demo :
    rationalTangentSquareWitnessSearch
      ({ lo := 0, hi := 1 } : QInterval)
      (dyadicNestedRadicalStageSinAt 2 2)
      (dyadicNestedRadicalStageTable 2 2).2 16 =
        some ((27135 : Rat) / 65536) := by
  native_decide

theorem dyadicNestedRadicalStage_two_middle_square_complement_overlap :
    QInterval.Overlaps
      (rationalSquareInterval (dyadicNestedRadicalStageSinAt 2 2))
      (rationalOneMinusSquareInterval
        (dyadicNestedRadicalStageTable 2 2).2) := by
  have hsearch := rationalTangentSquareWitnessSearch_stage_two_middle_demo
  have hS : subintervalOf (dyadicNestedRadicalStageSinAt 2 2) 0 1 := by
    unfold subintervalOf
    constructor
    · native_decide
    constructor <;> native_decide
  have hC : subintervalOf (dyadicNestedRadicalStageTable 2 2).2 0 1 := by
    unfold subintervalOf
    constructor
    · native_decide
    constructor <;> native_decide
  exact square_overlap_of_rationalTangentSquareWitnessSearch hsearch hS hC

theorem CanonicalDyadicHalfAngleCertificateAt.to_square_complement_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    {precision depth k : Nat} {hk : k < 2 ^ depth}
    (h : CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    QInterval.Overlaps
      (rationalSquareInterval
        (dyadicNestedRadicalTableAt precision depth k).1)
      (rationalOneMinusSquareInterval h.cosineBox) := by
  exact rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle
    (dyadicNestedRadicalTableAt_bounds precision depth k
      (Nat.le_of_lt hk)).1
    h.cosineBox_subinterval h.sine_contains h.cosine_contains
    h.circle_identity

theorem canonical_dyadic_certificate_at_of_rational_witness_square_overlap
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} (hk : k < 2 ^ depth)
    (u : Rat) (hu0 : 0 <= u) (hu1 : u <= 1)
    (hsine : (dyadicNestedRadicalTableAt precision depth k).1.lo <=
        rationalCircleSin u /\
      rationalCircleSin u <=
        (dyadicNestedRadicalTableAt precision depth k).1.hi)
    (houter : (dyadicTangentBoxAt B precision depth k hk).ContainsInterval
      (rationalHalfAngleTangentInterval
        ((dyadicNestedRadicalTableAt precision depth k).1)
        { lo := rationalCircleCos u, hi := rationalCircleCos u })) :
    QInterval.Overlaps
      (rationalSquareInterval
        (dyadicNestedRadicalTableAt precision depth k).1)
      (rationalOneMinusSquareInterval
        ({ lo := rationalCircleCos u, hi := rationalCircleCos u } : QInterval)) := by
  let h := canonical_dyadic_certificate_at_of_rational_witness
    B hk u hu0 hu1 hsine houter
  exact h.to_square_complement_overlap

/-! The same transport target, named at a dyadic nested-radical sample.  The
remaining witness-search proof only has to supply the two interval-membership
facts and the rational circle equation. -/

def dyadicNestedRadicalStageCosAt (n k : Nat) : QInterval :=
  (dyadicNestedRadicalStageTable n k).2

theorem dyadicNestedRadicalStage_square_complement_overlap
    {n k : Nat} (_hk : k <= 2 ^ n) (s c : Rat)
    (hS : subintervalOf (dyadicNestedRadicalStageSinAt n k) 0 1)
    (hC : subintervalOf (dyadicNestedRadicalStageCosAt n k) 0 1)
    (hs : (dyadicNestedRadicalStageSinAt n k).lo <= s ∧
      s <= (dyadicNestedRadicalStageSinAt n k).hi)
    (hc : (dyadicNestedRadicalStageCosAt n k).lo <= c ∧
      c <= (dyadicNestedRadicalStageCosAt n k).hi)
    (hcircle : s * s + c * c = 1) :
    QInterval.Overlaps
      (rationalSquareInterval (dyadicNestedRadicalStageSinAt n k))
      (rationalOneMinusSquareInterval
        (dyadicNestedRadicalStageCosAt n k)) := by
  exact rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle
    hS hC hs hc hcircle

/-! The square evaluator inherits an explicit finite modulus from the raw-real
product estimate.  This is the quantitative input for synchronizing the
square samples with the nested-radical sine boxes. -/
theorem sinPiSquareOnHalf_compute_width_le
    (S : ArctanSinPiConstruction) {x : Rat}
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    ((sinPiSquareOnHalf S).compute x n).width <=
      2 * ((sinPiOnHalfRaw S).compute x n).width := by
  have hvalid : (sinPiOnHalfRaw S).Valid := by
    intro y hy
    change RealRaw.ValidCompute
      (fun k => if h : 0 <= y /\ y <= (1 : Rat) / 2 then
        (sinPiRawOfArctan S.inverse y h).compute k else { lo := 0, hi := 0 })
    split
    · exact S.sin_valid y hy
    · rename_i hfalse
      exact False.elim (hfalse hy)
  let X : RealRaw := { compute := (sinPiOnHalfRaw S).compute x }
  have hX : X.Valid := by
    simpa [X, RealRaw.Valid, RealFunRaw.applyCompute] using hvalid x hx
  have hbound : forall k,
      0 <= (X.compute k).lo /\ (X.compute k).hi <= 1 := by
    intro k
    change 0 <= ((sinPiOnHalfRaw S).compute x k).lo /\
      ((sinPiOnHalfRaw S).compute x k).hi <= 1
    simpa [sinPiOnHalfRaw, hx] using S.sinPiRawOfArctan_bounds hx k
  have h := RealRaw.mul_width_le_of_nonneg_bounded
    hX hX (Bx := 1) (By := 1) hbound hbound n
  change (QBox.mulRealInterval
      ((sinPiOnHalfRaw S).compute x n).lo
      ((sinPiOnHalfRaw S).compute x n).hi
      ((sinPiOnHalfRaw S).compute x n).lo
      ((sinPiOnHalfRaw S).compute x n).hi).width <=
    1 * ((sinPiOnHalfRaw S).compute x n).width +
      1 * ((sinPiOnHalfRaw S).compute x n).width at h
  change (QBox.mulRealInterval
      ((sinPiOnHalfRaw S).compute x n).lo
      ((sinPiOnHalfRaw S).compute x n).hi
      ((sinPiOnHalfRaw S).compute x n).lo
      ((sinPiOnHalfRaw S).compute x n).hi).width <=
    2 * ((sinPiOnHalfRaw S).compute x n).width
  calc
    _ <= 1 * ((sinPiOnHalfRaw S).compute x n).width +
        1 * ((sinPiOnHalfRaw S).compute x n).width := h
    _ = 2 * ((sinPiOnHalfRaw S).compute x n).width := by
      have htwo : (2 : Rat) = 1 + 1 := by native_decide
      rw [htwo, Rat.add_mul]

theorem dyadicPublicSquareLeftSum_width_le_of_sine_stage
    (S : ArctanSinPiConstruction) (n : Nat) (eps : Rat)
    (hstage : forall k, k < 2 ^ n ->
      ((sinPiOnHalfRaw S).compute
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n).width <= eps) :
    (dyadicPublicSquareLeftSum S n).width <= eps := by
  have hsquare : forall k, k < 2 ^ n ->
      ((sinPiSquareOnHalf S).compute
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) n).width <= 2 * eps := by
    intro k hk
    exact Rat.le_trans
      (sinPiSquareOnHalf_compute_width_le S (by
        have hN : 0 < 2 ^ n := Nat.pow_pos (by omega)
        have hleft := leftPoint_monotone hN (by native_decide :
          (0 : Rat) <= (1 : Rat) / 2) (Nat.zero_le k)
        have hright := leftPoint_monotone hN (by native_decide :
          (0 : Rat) <= (1 : Rat) / 2) (by omega : k <= 2 ^ n)
        rw [leftPoint_zero] at hleft
        rw [leftPoint_endpoint hN] at hright
        exact ⟨by simpa using hleft, by simpa using hright⟩) n)
      (Rat.mul_le_mul_of_nonneg_left (hstage k hk)
        (by native_decide : (0 : Rat) <= 2))
  have h := dyadicPublicSquareLeftSum_width_le_of_stage S n (2 * eps)
    hsquare
  calc
    (dyadicPublicSquareLeftSum S n).width <= (1 / 2 : Rat) * (2 * eps) := h
    _ = eps := by
      have htwo : (2 : Rat) = 1 + 1 := by native_decide
      rw [htwo, Rat.add_mul]
      simp only [Rat.one_mul]
      rw [Rat.div_def]
      have hden : (1 + 1 : Rat) ≠ 0 := by native_decide
      grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel (1 + 1) hden]

theorem dyadicPublicSquareLeftSum_width_le_of_sine_regular
    (S : ArctanSinPiConstruction)
    (hsine : IntervalRegularOn S.onHalf) (n : Nat) :
    (dyadicPublicSquareLeftSum S n).width <=
      1 / ((n + 1 : Nat) : Rat) := by
  apply dyadicPublicSquareLeftSum_width_le_of_sine_stage S n
    (1 / ((n + 1 : Nat) : Rat))
  intro k hk
  let x := leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k
  have hN : 0 < 2 ^ n := Nat.pow_pos (by omega)
  have hleft := leftPoint_monotone hN (by native_decide :
    (0 : Rat) <= (1 : Rat) / 2) (Nat.zero_le k)
  have hright := leftPoint_monotone hN (by native_decide :
    (0 : Rat) <= (1 : Rat) / 2) (by omega : k <= 2 ^ n)
  rw [leftPoint_zero] at hleft
  rw [leftPoint_endpoint hN] at hright
  have hx : 0 <= x /\ x <= (1 : Rat) / 2 := by
    exact ⟨by simpa [x] using hleft, by simpa [x] using hright⟩
  let I : QInterval := { lo := x, hi := x }
  have hI : subintervalOf I S.onHalf.lower S.onHalf.upper := by
    unfold subintervalOf
    simpa [I, ArctanSinPiConstruction.onHalf] using
      (show (0 : Rat) <= x /\ x <= (1 : Rat) / 2 from hx)
  have hsmall : I.width <=
      1 / ((hsine.inputPrecision n : Nat) : Rat) := by
    have hpos : 0 < ((hsine.inputPrecision n : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (hsine.inputPrecision_pos n)
    have hright : 0 <
        1 / ((hsine.inputPrecision n : Nat) : Rat) := by
      rw [Rat.div_def]
      exact Rat.mul_pos (by native_decide) ((Rat.inv_pos).2 hpos)
    unfold QInterval.width
    dsimp [I]
    grind [Rat.le_of_lt hright]
  have houtput := hsine.output_width I hI n hsmall
  have hcontains := hsine.contains_point_values I hI x
    (S.onHalf.defined_on x hx) n (by simp [I]) (by simp [I])
  have hpointwidth : (S.onHalf.compute x (S.onHalf.defined_on x hx) n).width <=
      (hsine.evalInterval I hI n).width :=
    QInterval.width_le_of_contains hcontains
  have hsinewidth :
      (S.onHalf.compute x (S.onHalf.defined_on x hx) n).width <=
        1 / ((n + 1 : Nat) : Rat) :=
    Rat.le_trans hpointwidth houtput.2
  change ((sinPiRawOfArctan S.inverse x hx).compute n).width <=
    1 / ((n + 1 : Nat) : Rat) at hsinewidth
  simpa [x, sinPiOnHalfRaw, ArctanSinPiConstruction.onHalf, hx] using hsinewidth

/-! Package the public finite sums as a raw candidate while keeping the
cross-stage nesting obligation explicit. -/
def dyadicPublicSquareIntegralRaw
    (S : ArctanSinPiConstruction) : RealRaw where
  compute := dyadicPublicSquareLeftSum S

/- The square-circle certificate already controls every finite rectangle sum.
    Since the nested square raw is defined by those same sums, the result is
    an actual raw-real equivalence; no limit or completeness argument is
    needed at this transport step. -/
theorem DyadicSquareCircleOverlapFamily.to_public_equiv_nested
    {S : ArctanSinPiConstruction}
    (certificate : DyadicSquareCircleOverlapFamily S) :
    (dyadicPublicSquareIntegralRaw S).Equiv
      dyadicNestedRadicalSquareIntegralRaw := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (dyadicPublicSquareIntegralRaw S)
    dyadicNestedRadicalSquareIntegralRaw n n).2
  change QInterval.Overlaps
    (dyadicPublicSquareLeftSum S n)
    (dyadicNestedRadicalSquareLeftSum n)
  exact certificate.to_square_sum_overlap n

theorem DyadicPublicSquareTangentTransportWitness.to_public_equiv
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentTransportWitness S) :
    (dyadicPublicSquareIntegralRaw S).Equiv tangentSquareIntegral := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  exact (RealRaw.compareAt_overlap_iff
    (dyadicPublicSquareIntegralRaw S) tangentSquareIntegral n n).2
    (h.to_public_overlap n)

theorem DyadicPublicSquareTangentSharedWitness.to_public_equiv
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentSharedWitness S) :
    (dyadicPublicSquareIntegralRaw S).Equiv tangentSquareIntegral := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  exact (RealRaw.compareAt_overlap_iff
    (dyadicPublicSquareIntegralRaw S) tangentSquareIntegral n n).2
    (h.to_public_common_witness.to_overlap n)

theorem dyadicPublicSquareIntegralRaw_widths_shrink
    (S : ArctanSinPiConstruction)
    (hsine : IntervalRegularOn S.onHalf) :
    RealRaw.WidthsShrinkToZero
      (dyadicPublicSquareIntegralRaw S).compute := by
  change RealRaw.WidthsShrinkToZero (dyadicPublicSquareLeftSum S)
  exact shrinksToZero_of_natOverSuccBound
    (fun n => dyadicPublicSquareLeftSum_width_le_of_sine_regular S hsine n)

def dyadicPublicSquareIntegralRaw_stabilized
    (S : ArctanSinPiConstruction) (anchor : RealRaw) : RealRaw :=
  RealRaw.prefixStabilize (dyadicPublicSquareIntegralRaw S)
    (fun n => (anchor.compute n).width)

theorem dyadicPublicSquareIntegralRaw_stabilized_width_le
    (S : ArctanSinPiConstruction) (anchor : RealRaw) (n : Nat) :
    ((dyadicPublicSquareIntegralRaw_stabilized S anchor).compute n).width <=
      ((dyadicPublicSquareIntegralRaw S).compute n).width +
        2 * (anchor.compute n).width := by
  exact RealRaw.prefixStabilize_width_le_current_expand
    (dyadicPublicSquareIntegralRaw S)
    (fun n => (anchor.compute n).width) n

theorem dyadicPublicSquareIntegralRaw_stabilized_valid_of_overlap
    (S : ArctanSinPiConstruction)
    (hsine : IntervalRegularOn S.onHalf)
    {anchor : RealRaw} (hanchor : anchor.Valid)
    (hover : (dyadicPublicSquareIntegralRaw S).Equiv anchor) :
    (dyadicPublicSquareIntegralRaw_stabilized S anchor).Valid := by
  apply RealRaw.prefixStabilize_valid
    (dyadicPublicSquareIntegralRaw_widths_shrink S hsine)
    hanchor hover
  · intro n
    exact Rat.le_refl
  · exact hanchor.2.2

theorem dyadicPublicSquareIntegralRaw_stabilized_equiv_anchor_of_overlap
    (S : ArctanSinPiConstruction)
    {anchor : RealRaw} (hanchor : anchor.Valid)
    (hover : (dyadicPublicSquareIntegralRaw S).Equiv anchor) :
    (dyadicPublicSquareIntegralRaw_stabilized S anchor).Equiv anchor := by
  apply RealRaw.prefixStabilize_equiv_anchor hanchor hover
  intro n
  exact Rat.le_refl

theorem dyadicPublicSquareIntegralRaw_stabilized_equiv_value_of_anchor
    (S : ArctanSinPiConstruction)
    (hsine : IntervalRegularOn S.onHalf)
    {anchor : RealRaw} (hanchor : anchor.Valid)
    (hover : (dyadicPublicSquareIntegralRaw S).Equiv anchor)
    (hvalue : anchor.Equiv (RealRaw.ofRat (1 / 4))) :
    (dyadicPublicSquareIntegralRaw_stabilized S anchor).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  exact RealRaw.equiv_trans
    (dyadicPublicSquareIntegralRaw_stabilized_valid_of_overlap
      S hsine hanchor hover)
    hanchor (RealRaw.ofRat_valid _)
    (dyadicPublicSquareIntegralRaw_stabilized_equiv_anchor_of_overlap
      S hanchor hover)
    hvalue

theorem DyadicPublicSquareTangentTransportWitness.stabilized_equiv_value
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentTransportWitness S)
    (hsine : IntervalRegularOn S.onHalf)
    (hvalue : tangentSquareIntegral.Equiv (RealRaw.ofRat (1 / 4))) :
    (dyadicPublicSquareIntegralRaw_stabilized S tangentSquareIntegral).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  exact dyadicPublicSquareIntegralRaw_stabilized_equiv_value_of_anchor
    S hsine tangentSquareIntegral_valid h.to_public_equiv hvalue

theorem DyadicPublicSquareTangentSharedWitness.stabilized_equiv_value
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentSharedWitness S)
    (hsine : IntervalRegularOn S.onHalf)
    (hvalue : tangentSquareIntegral.Equiv (RealRaw.ofRat (1 / 4))) :
    (dyadicPublicSquareIntegralRaw_stabilized S tangentSquareIntegral).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  exact dyadicPublicSquareIntegralRaw_stabilized_equiv_value_of_anchor
    S hsine tangentSquareIntegral_valid h.to_public_equiv hvalue

theorem DyadicPublicSquareTangentSharedWitness.stabilized_valid
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentSharedWitness S)
    (hsine : IntervalRegularOn S.onHalf) :
    (dyadicPublicSquareIntegralRaw_stabilized S tangentSquareIntegral).Valid := by
  exact dyadicPublicSquareIntegralRaw_stabilized_valid_of_overlap
    S hsine tangentSquareIntegral_valid h.to_public_equiv

/- The stabilized public evaluator is equivalent to its valid tangent-square
   anchor.  This is the representation edge consumed by later value and FTC
   proofs; it is stronger than merely recording validity. -/
theorem DyadicPublicSquareTangentSharedWitness.stabilized_equiv_tangentSquare
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentSharedWitness S) :
    (dyadicPublicSquareIntegralRaw_stabilized S tangentSquareIntegral).Equiv
      tangentSquareIntegral := by
  exact dyadicPublicSquareIntegralRaw_stabilized_equiv_anchor_of_overlap
    S tangentSquareIntegral_valid h.to_public_equiv

/- The stabilized public evaluator is the valid representative used for
   transitive transport to the quarter-turn anchor. -/
theorem DyadicPublicSquareTangentTransportWitness.to_public_equiv_halfQuarterTurn
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentTransportWitness S)
    (hsine : IntervalRegularOn S.onHalf)
    (hbridge : tangentSquareIntegral.Equiv
      tangentSquareEffectiveFTCData.integralRaw) :
    (dyadicPublicSquareIntegralRaw_stabilized S tangentSquareIntegral).Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  have hstable :
      (dyadicPublicSquareIntegralRaw_stabilized S tangentSquareIntegral).Equiv
        tangentSquareEffectiveFTCData.integralRaw :=
    RealRaw.equiv_trans
      (dyadicPublicSquareIntegralRaw_stabilized_valid_of_overlap
        S hsine tangentSquareIntegral_valid h.to_public_equiv)
      tangentSquareIntegral_valid tangentSquareEffectiveFTCData.integral_valid
      (dyadicPublicSquareIntegralRaw_stabilized_equiv_anchor_of_overlap
        S tangentSquareIntegral_valid h.to_public_equiv)
      hbridge
  exact RealRaw.equiv_trans
    (dyadicPublicSquareIntegralRaw_stabilized_valid_of_overlap
      S hsine tangentSquareIntegral_valid h.to_public_equiv)
    tangentSquareEffectiveFTCData.integral_valid
    (by
      change (RealRaw.scaleRat ((1 : Rat) / 4) piCircleArea).Valid
      exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
        CauchyPi.piCircleArea_valid)
    hstable
    tangentSquareEffectiveFTC_integral_equiv_halfQuarterTurn

theorem DyadicPublicSquareTangentSharedWitness.to_public_equiv_halfQuarterTurn
    {S : ArctanSinPiConstruction}
    (h : DyadicPublicSquareTangentSharedWitness S)
    (hsine : IntervalRegularOn S.onHalf)
    (hbridge : tangentSquareIntegral.Equiv
      tangentSquareEffectiveFTCData.integralRaw) :
    (dyadicPublicSquareIntegralRaw_stabilized S tangentSquareIntegral).Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  have hstable :
      (dyadicPublicSquareIntegralRaw_stabilized S tangentSquareIntegral).Equiv
        tangentSquareEffectiveFTCData.integralRaw :=
    RealRaw.equiv_trans
      (dyadicPublicSquareIntegralRaw_stabilized_valid_of_overlap
        S hsine tangentSquareIntegral_valid h.to_public_equiv)
      tangentSquareIntegral_valid tangentSquareEffectiveFTCData.integral_valid
      (dyadicPublicSquareIntegralRaw_stabilized_equiv_anchor_of_overlap
        S tangentSquareIntegral_valid h.to_public_equiv)
      hbridge
  exact RealRaw.equiv_trans
    (dyadicPublicSquareIntegralRaw_stabilized_valid_of_overlap
      S hsine tangentSquareIntegral_valid h.to_public_equiv)
    tangentSquareEffectiveFTCData.integral_valid
    (by
      change (RealRaw.scaleRat ((1 : Rat) / 4) piCircleArea).Valid
      exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
        CauchyPi.piCircleArea_valid)
    hstable
    tangentSquareEffectiveFTC_integral_equiv_halfQuarterTurn

def sinPiSquareOnHalfFunctionOnInterval
    (S : ArctanSinPiConstruction) : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
    compute := fun x _ => (sinPiSquareOnHalf S).compute x }
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := by
    intro x hx
    exact hx
  valid_on := by
    intro x hx
    exact sinPiSquareOnHalf_valid S x ⟨hx, hx⟩

def sinPiSquareFTCStageSchedule : RealRaw.StageSchedule where
  stage := fun n => 2 * n + 1
  monotone := by
    intro n m hnm
    omega
  cofinal := by
    intro target
    refine ⟨target, ?_⟩
    omega

def sinPiSquareOnHalfScheduledFunctionOnInterval
    (S : ArctanSinPiConstruction) : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
    compute := fun x _ =>
      fun n => (sinPiSquareOnHalf S).compute x
        (sinPiSquareFTCStageSchedule.stage n) }
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := by
    intro x hx
    exact hx
  valid_on := by
    intro x hx
    change RealRaw.ValidCompute
      (fun n => (sinPiSquareOnHalf S).compute x
        (sinPiSquareFTCStageSchedule.stage n))
    exact RealRaw.schedule_valid
      { compute := (sinPiSquareOnHalf S).compute x }
      (sinPiSquareOnHalf_valid S x ⟨hx, hx⟩)
      sinPiSquareFTCStageSchedule

theorem sinPiSquareOnHalfScheduled_compute_of_mem
    (S : ArctanSinPiConstruction) {x : Rat}
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    (sinPiSquareOnHalfScheduledFunctionOnInterval S).compute x
      (by exact hx) n =
      (sinPiSquareOnHalf S).compute x
      (sinPiSquareFTCStageSchedule.stage n) := by
  rfl

theorem sinPiSquareOnHalfScheduled_compute_width_le
    (S : ArctanSinPiConstruction) {x : Rat}
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    ((sinPiSquareOnHalfScheduledFunctionOnInterval S).compute x
      (by exact hx) n).width <=
      2 * ((sinPiOnHalfRaw S).compute x
        (sinPiSquareFTCStageSchedule.stage n)).width := by
  rw [sinPiSquareOnHalfScheduled_compute_of_mem S hx n]
  exact sinPiSquareOnHalf_compute_width_le S hx
    (sinPiSquareFTCStageSchedule.stage n)


/-! The inverse-search monotonicity obligation is kept as finite data.  It is
the exact missing property needed to turn ordered angle inputs into ordered
tangent boxes; no extensional inverse-function axiom is introduced. -/

structure TangentMonotonicityCertificate
    (B : IntegralIdentities.ArctanInverseBisection) where
  weak_order : forall (s t : Rat)
    (hs : RationalCircle.GeometricTrig.firstQuadrantBranch s)
    (ht : RationalCircle.GeometricTrig.firstQuadrantBranch t),
    s <= t -> forall n,
      (B.tangentRaw.compute s hs n).lo <=
        (B.tangentRaw.compute t ht n).hi

theorem TangentMonotonicityCertificate.tangent_nondecreasing
    {B : IntegralIdentities.ArctanInverseBisection}
    (C : TangentMonotonicityCertificate B) :
    NondecreasingOnInterval (IntegralIdentities.tangentOnUnit B) := by
  intro s t hs ht hst n
  change 0 <= s /\ s <= 1 at hs
  change 0 <= t /\ t <= 1 at ht
  exact C.weak_order s t hs ht hst n

/-! Monotonicity is inherited from the sine evaluator at the interval level.
The hypothesis is intentionally the existing weak interval monotonicity
(`lower` at the left sample is below `upper` at the right sample), which is
exactly what the monotone Darboux interface asks for. -/

theorem sinPiSquareOnHalf_nondecreasing_of_sine_nondecreasing
    (S : ArctanSinPiConstruction)
    (hsine : NondecreasingOnInterval S.onHalf) :
    NondecreasingOnInterval (sinPiSquareOnHalfFunctionOnInterval S) := by
  intro x y hx hy hxy n
  have hsin := hsine x y hx hy hxy n
  have hboundsx := S.sinPiRawOfArctan_bounds hx n
  have hboundsy := S.sinPiRawOfArctan_bounds hy n
  change ((sinPiSquareOnHalf S).compute x n).lo <=
    ((sinPiSquareOnHalf S).compute y n).hi
  rw [sinPiSquareOnHalf_compute_of_mem S hx n,
    sinPiSquareOnHalf_compute_of_mem S hy n]
  have horderx := RealRaw.interval_order_of_valid
    { compute := (sinPiRawOfArctan S.inverse x hx).compute }
    (S.sin_valid x hx) n
  have hordery := RealRaw.interval_order_of_valid
    { compute := (sinPiRawOfArctan S.inverse y hy).compute }
    (S.sin_valid y hy) n
  rw [QBox.mulRealInterval_self_of_nonneg hboundsx.1 horderx,
    QBox.mulRealInterval_self_of_nonneg hboundsy.1 hordery]
  change
    ((sinPiRawOfArctan S.inverse x hx).compute n).lo *
        ((sinPiRawOfArctan S.inverse x hx).compute n).lo <=
      ((sinPiRawOfArctan S.inverse y hy).compute n).hi *
        ((sinPiRawOfArctan S.inverse y hy).compute n).hi
  have hxy' :
      ((sinPiRawOfArctan S.inverse x hx).compute n).lo <=
        ((sinPiRawOfArctan S.inverse y hy).compute n).hi := by
    exact hsin
  have hsq := Rat.mul_le_mul_of_nonneg_left hxy' hboundsx.1
  have hyhi0 : 0 <=
      ((sinPiRawOfArctan S.inverse y hy).compute n).hi :=
    Rat.le_trans hboundsy.1 hordery
  have hsq' := Rat.mul_le_mul_of_nonneg_right hxy' hyhi0
  grind [Rat.pow_succ]

theorem sinPiSquareOnHalf_nondecreasing_of_tangent_certificate
    (S : ArctanSinPiConstruction)
    (C : TangentMonotonicityCertificate S.inverse) :
    NondecreasingOnInterval (sinPiSquareOnHalfFunctionOnInterval S) := by
  exact sinPiSquareOnHalf_nondecreasing_of_sine_nondecreasing S
    (S.onHalf_nondecreasing_of_tangent_nondecreasing
      C.tangent_nondecreasing)

def unitClampInterval (I : QInterval) : QInterval :=
  QInterval.intersection I { lo := 0, hi := 1 }

theorem unitClampInterval_contains
    {I K : QInterval}
    (hI : I.ContainsInterval K)
    (hK : subintervalOf K 0 1) :
    (unitClampInterval I).ContainsInterval K := by
  unfold unitClampInterval
  apply QInterval.intersection_contains hI
  exact ⟨hK.1, hK.2.2⟩

theorem unitClampInterval_subinterval_of_contains
    {I K : QInterval}
    (hIorder : I.lo <= I.hi)
    (hK : subintervalOf K 0 1)
    (hI : I.ContainsInterval K) :
    subintervalOf (unitClampInterval I) 0 1 := by
  have hKorder : K.lo <= K.hi := hK.2.1
  have hover : I.Overlaps ({ lo := 0, hi := 1 } : QInterval) := by
    unfold QInterval.Overlaps
    have hI' := hI
    unfold QInterval.ContainsInterval at hI'
    have hK' := hK
    unfold subintervalOf at hK'
    grind
  have hord : (unitClampInterval I).lo <=
      (unitClampInterval I).hi := by
    exact QInterval.intersection_ordered_of_overlaps hIorder
      (by native_decide) hover
  change 0 <= max I.lo 0 /\ max I.lo 0 <= min I.hi 1 /\ min I.hi 1 <= 1
  change max I.lo 0 <= min I.hi 1 at hord
  grind

theorem unitClampInterval_width_le
    {I : QInterval} :
    (unitClampInterval I).width <= I.width := by
  unfold unitClampInterval
  exact QInterval.width_le_of_contains
    (QInterval.intersection_contained_left I { lo := 0, hi := 1 })

theorem unitSquareInterval_width_le_two_mul
    {J : QInterval} (hJ : subintervalOf J 0 1) :
    (QBox.mulRealInterval J.lo J.hi J.lo J.hi).width <=
      2 * J.width := by
  have horder : J.lo <= J.hi := hJ.2.1
  have hsq := QBox.mulRealInterval_self_of_nonneg hJ.1 horder
  rw [hsq]
  unfold QInterval.width
  have hsum : J.hi + J.lo <= 2 := by grind [hJ.2.2]
  have hgap : 0 <= J.hi - J.lo := by
    grind
  have hfactor : J.hi * J.hi - J.lo * J.lo =
      (J.hi - J.lo) * (J.hi + J.lo) := by
    grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg]
  rw [hfactor]
  have hmul := Rat.mul_le_mul_of_nonneg_left hsum hgap
  grind [Rat.mul_comm]

theorem unitClampSquare_width_le_two_mul_of_contains
    {E K : QInterval}
    (hEorder : E.lo <= E.hi)
    (hK : subintervalOf K 0 1)
    (hcontains : E.ContainsInterval K) :
    (QBox.mulRealInterval (unitClampInterval E).lo
      (unitClampInterval E).hi (unitClampInterval E).lo
      (unitClampInterval E).hi).width <= 2 * E.width := by
  have hJsub : subintervalOf (unitClampInterval E) 0 1 :=
    unitClampInterval_subinterval_of_contains hEorder hK hcontains
  have hsq := unitSquareInterval_width_le_two_mul hJsub
  have hclamp := unitClampInterval_width_le (I := E)
  have hJwidth : (unitClampInterval E).width <= E.width := hclamp
  exact Rat.le_trans hsq
    (Rat.mul_le_mul_of_nonneg_left hJwidth
      (by native_decide : (0 : Rat) <= 2))

theorem unitClampSquare_width_le_of_contains
    {E K : QInterval} {n : Nat}
    (hEorder : E.lo <= E.hi)
    (hEwidth : E.width <= 1 / (((2 * n + 2 : Nat) : Nat) : Rat))
    (hK : subintervalOf K 0 1)
    (hcontains : E.ContainsInterval K) :
    (QBox.mulRealInterval (unitClampInterval E).lo
      (unitClampInterval E).hi (unitClampInterval E).lo
      (unitClampInterval E).hi).width <=
      1 / ((n + 1 : Nat) : Rat) := by
  have htwo := unitClampSquare_width_le_two_mul_of_contains
    hEorder hK hcontains
  have hscaled := Rat.mul_le_mul_of_nonneg_left hEwidth
    (by native_decide : (0 : Rat) <= 2)
  calc
    (QBox.mulRealInterval (unitClampInterval E).lo
        (unitClampInterval E).hi (unitClampInterval E).lo
        (unitClampInterval E).hi).width <= 2 * E.width := htwo
    _ <= 2 * (1 / (((2 * n + 2 : Nat) : Nat) : Rat)) := hscaled
    _ = 1 / ((n + 1 : Nat) : Rat) := by
      have hcast : (((2 * n + 2 : Nat) : Nat) : Rat) =
          2 * ((n + 1 : Nat) : Rat) := by
        rw [Rat.natCast_add, Rat.natCast_add, Rat.natCast_mul]
        grind
      rw [hcast, Rat.div_def, Rat.div_def]
      have hne : ((n + 1 : Nat) : Rat) ≠ 0 := by
        exact Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega))
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem unitSquareInterval_contains_of_contains
    {E K : QInterval}
    (hE : subintervalOf E 0 1)
    (hK : subintervalOf K 0 1)
    (hcontains : E.ContainsInterval K) :
    QBox.mulRealInterval E.lo E.hi E.lo E.hi |>.ContainsInterval
      (QBox.mulRealInterval K.lo K.hi K.lo K.hi) := by
  rw [rationalSquareInterval_mul_self_eq hE,
    rationalSquareInterval_mul_self_eq hK]
  unfold rationalSquareInterval QInterval.ContainsInterval
  have hsquare_mono {a b : Rat} (ha : 0 <= a) (hab : a <= b) :
      a * a <= b * b := by
    have hb : 0 <= b := Rat.le_trans ha hab
    exact Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_left hab ha)
      (Rat.mul_le_mul_of_nonneg_right hab hb)
  exact ⟨hsquare_mono hE.1 hcontains.1,
    hsquare_mono (Rat.le_trans hK.1 hK.2.1) hcontains.2⟩

def sinPiSquareClampedInterval
    (S : ArctanSinPiConstruction)
    (hsine : IntervalRegularOn S.onHalf)
    (I : QInterval) (hI : subintervalOf I 0 ((1 : Rat) / 2))
    (n : Nat) : QInterval :=
  if _hsmall : I.width <=
      1 / ((hsine.inputPrecision (2 * n + 1) : Nat) : Rat) then
    let E := hsine.evalInterval I hI (2 * n + 1)
    QBox.mulRealInterval
      (unitClampInterval E).lo (unitClampInterval E).hi
      (unitClampInterval E).lo (unitClampInterval E).hi
  else
    { lo := 0, hi := 1 }

theorem sinPiSquareClampedInterval_of_small
    (S : ArctanSinPiConstruction)
    (hsine : IntervalRegularOn S.onHalf)
    (I : QInterval) (hI : subintervalOf I 0 ((1 : Rat) / 2))
    (n : Nat)
    (hsmall : I.width <=
      1 / ((hsine.inputPrecision (2 * n + 1) : Nat) : Rat)) :
    sinPiSquareClampedInterval S hsine I hI n =
      QBox.mulRealInterval
        (unitClampInterval (hsine.evalInterval I hI (2 * n + 1))).lo
        (unitClampInterval (hsine.evalInterval I hI (2 * n + 1))).hi
        (unitClampInterval (hsine.evalInterval I hI (2 * n + 1))).lo
        (unitClampInterval (hsine.evalInterval I hI (2 * n + 1))).hi := by
  simp [sinPiSquareClampedInterval, hsmall]

theorem sinPiSquareClampedInterval_of_large
    (S : ArctanSinPiConstruction)
    (hsine : IntervalRegularOn S.onHalf)
    (I : QInterval) (hI : subintervalOf I 0 ((1 : Rat) / 2))
    (n : Nat)
    (hlarge : ¬ I.width <=
      1 / ((hsine.inputPrecision (2 * n + 1) : Nat) : Rat)) :
    sinPiSquareClampedInterval S hsine I hI n = { lo := 0, hi := 1 } := by
  simp [sinPiSquareClampedInterval, hlarge]

def sinPiSquareScheduled_intervalRegular
    (S : ArctanSinPiConstruction)
    (hsine : IntervalRegularOn S.onHalf) :
    IntervalRegularOn
      (sinPiSquareOnHalfScheduledFunctionOnInterval S) := by
  refine
    { evalInterval := fun I hI n =>
        sinPiSquareClampedInterval S hsine I hI n
      inputPrecision := fun n => hsine.inputPrecision
        (sinPiSquareFTCStageSchedule.stage n)
      inputPrecision_pos := by
        intro n
        exact hsine.inputPrecision_pos _
      output_width := ?_
      contains_point_values := ?_ }
  · intro I hI n hsmall
    have hI' : subintervalOf I 0 ((1 : Rat) / 2) := by
      simpa [sinPiSquareOnHalfScheduledFunctionOnInterval] using hI
    have hI_sine : subintervalOf I S.onHalf.lower S.onHalf.upper := by
      simpa [ArctanSinPiConstruction.onHalf] using hI'
    have hEwidth := hsine.output_width I hI_sine
      (sinPiSquareFTCStageSchedule.stage n) hsmall
    have hKsub : subintervalOf
        (S.onHalf.compute I.lo (S.onHalf.defined_on I.lo
          ⟨hI'.1, Rat.le_trans hI'.2.1 hI'.2.2⟩)
          (sinPiSquareFTCStageSchedule.stage n)) 0 1 := by
      change subintervalOf
        ((sinPiRawOfArctan S.inverse I.lo
          ⟨hI'.1, Rat.le_trans hI'.2.1 hI'.2.2⟩).compute
          (sinPiSquareFTCStageSchedule.stage n)) 0 1
      have hbounds := S.sinPiRawOfArctan_bounds
        ⟨hI'.1, Rat.le_trans hI'.2.1 hI'.2.2⟩
        (sinPiSquareFTCStageSchedule.stage n)
      have horder := RealRaw.interval_order_of_valid
        (sinPiRawOfArctan S.inverse I.lo
          ⟨hI'.1, Rat.le_trans hI'.2.1 hI'.2.2⟩)
        (S.sin_valid I.lo
          ⟨hI'.1, Rat.le_trans hI'.2.1 hI'.2.2⟩)
        (sinPiSquareFTCStageSchedule.stage n)
      exact ⟨hbounds.1, horder, hbounds.2⟩
    have hEcontains := hsine.contains_point_values I hI_sine I.lo
      (S.onHalf.defined_on I.lo
        ⟨hI'.1, Rat.le_trans hI'.2.1 hI'.2.2⟩)
      (sinPiSquareFTCStageSchedule.stage n)
      (by exact Rat.le_refl) hI'.2.1
    have hEorder :
        (hsine.evalInterval I hI_sine
          (sinPiSquareFTCStageSchedule.stage n)).lo <=
          (hsine.evalInterval I hI_sine
            (sinPiSquareFTCStageSchedule.stage n)).hi := by
      exact Rat.le_trans hEcontains.1
        (Rat.le_trans hKsub.2.1 hEcontains.2)
    have hwidth := unitClampSquare_width_le_of_contains
      hEorder hEwidth.2 hKsub hEcontains
    have hJsub : subintervalOf
        (unitClampInterval (hsine.evalInterval I hI_sine
          (sinPiSquareFTCStageSchedule.stage n))) 0 1 :=
      unitClampInterval_subinterval_of_contains hEorder hKsub hEcontains
    have hwidth_nonneg : 0 <=
        (QBox.mulRealInterval
          (unitClampInterval (hsine.evalInterval I hI_sine
            (sinPiSquareFTCStageSchedule.stage n))).lo
          (unitClampInterval (hsine.evalInterval I hI_sine
            (sinPiSquareFTCStageSchedule.stage n))).hi
          (unitClampInterval (hsine.evalInterval I hI_sine
            (sinPiSquareFTCStageSchedule.stage n))).lo
          (unitClampInterval (hsine.evalInterval I hI_sine
            (sinPiSquareFTCStageSchedule.stage n))).hi).width := by
      have hself := QBox.mulRealInterval_self_of_nonneg
        hJsub.1 hJsub.2.1
      rw [hself]
      change 0 <=
        (unitClampInterval (hsine.evalInterval I hI_sine
          (sinPiSquareFTCStageSchedule.stage n))).hi *
            (unitClampInterval (hsine.evalInterval I hI_sine
              (sinPiSquareFTCStageSchedule.stage n))).hi -
          (unitClampInterval (hsine.evalInterval I hI_sine
            (sinPiSquareFTCStageSchedule.stage n))).lo *
            (unitClampInterval (hsine.evalInterval I hI_sine
              (sinPiSquareFTCStageSchedule.stage n))).lo
      have hlo : 0 <=
          (unitClampInterval (hsine.evalInterval I hI_sine
            (sinPiSquareFTCStageSchedule.stage n))).lo := hJsub.1
      have hgap : 0 <=
          (unitClampInterval (hsine.evalInterval I hI_sine
            (sinPiSquareFTCStageSchedule.stage n))).hi -
            (unitClampInterval (hsine.evalInterval I hI_sine
              (sinPiSquareFTCStageSchedule.stage n))).lo := by
        grind [hJsub.2.1]
      have hsum : 0 <=
          (unitClampInterval (hsine.evalInterval I hI_sine
            (sinPiSquareFTCStageSchedule.stage n))).hi +
            (unitClampInterval (hsine.evalInterval I hI_sine
              (sinPiSquareFTCStageSchedule.stage n))).lo := by
        have hhi := Rat.le_trans hlo hJsub.2.1
        exact Rat.add_nonneg hhi hlo
      have hfactor :
          (unitClampInterval (hsine.evalInterval I hI_sine
            (sinPiSquareFTCStageSchedule.stage n))).hi *
              (unitClampInterval (hsine.evalInterval I hI_sine
                (sinPiSquareFTCStageSchedule.stage n))).hi -
              (unitClampInterval (hsine.evalInterval I hI_sine
                (sinPiSquareFTCStageSchedule.stage n))).lo *
                  (unitClampInterval (hsine.evalInterval I hI_sine
                    (sinPiSquareFTCStageSchedule.stage n))).lo =
            ((unitClampInterval (hsine.evalInterval I hI_sine
              (sinPiSquareFTCStageSchedule.stage n))).hi -
                (unitClampInterval (hsine.evalInterval I hI_sine
                  (sinPiSquareFTCStageSchedule.stage n))).lo) *
              ((unitClampInterval (hsine.evalInterval I hI_sine
                (sinPiSquareFTCStageSchedule.stage n))).hi +
                (unitClampInterval (hsine.evalInterval I hI_sine
                  (sinPiSquareFTCStageSchedule.stage n))).lo) := by
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg]
      rw [hfactor]
      exact Rat.mul_nonneg hgap hsum
    change I.width <=
      1 / ((hsine.inputPrecision (2 * n + 1) : Nat) : Rat) at hsmall
    rw [sinPiSquareClampedInterval_of_small S hsine I hI' n hsmall]
    exact ⟨hwidth_nonneg, hwidth⟩
  · intro I hI x hx n hxlo hxhi
    have hI' : subintervalOf I 0 ((1 : Rat) / 2) := by
      simpa [sinPiSquareOnHalfScheduledFunctionOnInterval] using hI
    have hx' : 0 <= x /\ x <= (1 : Rat) / 2 := by
      simpa [sinPiSquareOnHalfScheduledFunctionOnInterval,
        inDomainInterval] using hx
    have hI_sine : subintervalOf I S.onHalf.lower S.onHalf.upper := by
      simpa [ArctanSinPiConstruction.onHalf] using hI'
    by_cases hsmall : I.width <=
      1 / ((hsine.inputPrecision
        (sinPiSquareFTCStageSchedule.stage n) : Nat) : Rat)
    · have hKsub : subintervalOf
          ((S.onHalf.compute x (S.onHalf.defined_on x hx')
            (sinPiSquareFTCStageSchedule.stage n))) 0 1 := by
        change subintervalOf
          ((sinPiRawOfArctan S.inverse x hx').compute
            (sinPiSquareFTCStageSchedule.stage n)) 0 1
        have hbounds := S.sinPiRawOfArctan_bounds hx'
          (sinPiSquareFTCStageSchedule.stage n)
        have horder := RealRaw.interval_order_of_valid
          (sinPiRawOfArctan S.inverse x hx')
          (S.sin_valid x hx') (sinPiSquareFTCStageSchedule.stage n)
        exact ⟨hbounds.1, horder, hbounds.2⟩
      have hEcontains := hsine.contains_point_values I hI' x
        (S.onHalf.defined_on x hx')
        (sinPiSquareFTCStageSchedule.stage n) hxlo hxhi
      have hEorder :
          (hsine.evalInterval I hI
            (sinPiSquareFTCStageSchedule.stage n)).lo <=
            (hsine.evalInterval I hI
              (sinPiSquareFTCStageSchedule.stage n)).hi := by
        exact Rat.le_trans hEcontains.1
          (Rat.le_trans hKsub.2.1 hEcontains.2)
      have hclamp := unitClampInterval_contains hEcontains hKsub
      have hsq := unitSquareInterval_contains_of_contains
        (unitClampInterval_subinterval_of_contains hEorder hKsub hEcontains)
        hKsub hclamp
      rw [sinPiSquareClampedInterval_of_small S hsine I hI' n hsmall]
      change QInterval.ContainsInterval _
        ((sinPiSquareOnHalfScheduledFunctionOnInterval S).compute x _ n)
      rw [sinPiSquareOnHalfScheduled_compute_of_mem S hx' n]
      simpa [sinPiSquareOnHalf_compute_of_mem S hx',
        FunctionOnInterval.compute,
        ArctanSinPiConstruction.onHalf,
        sinPiSquareFTCStageSchedule] using hsq
    · rw [sinPiSquareClampedInterval_of_large S hsine I hI' n hsmall]
      change QInterval.ContainsInterval { lo := 0, hi := 1 }
        ((sinPiSquareOnHalfScheduledFunctionOnInterval S).compute x _ n)
      rw [sinPiSquareOnHalfScheduled_compute_of_mem S hx' n]
      rw [sinPiSquareOnHalf_compute_of_mem S hx']
      have hbounds := S.sinPiRawOfArctan_bounds hx'
        (sinPiSquareFTCStageSchedule.stage n)
      have horder := RealRaw.interval_order_of_valid
        (sinPiRawOfArctan S.inverse x hx')
        (S.sin_valid x hx') (sinPiSquareFTCStageSchedule.stage n)
      have hself := QBox.mulRealInterval_self_of_nonneg
        hbounds.1 horder
      rw [hself]
      unfold QInterval.ContainsInterval
      constructor
      · exact Rat.mul_nonneg hbounds.1 hbounds.1
      · have hhi_nonneg : 0 <=
            ((sinPiRawOfArctan S.inverse x hx').compute
              (sinPiSquareFTCStageSchedule.stage n)).hi :=
          Rat.le_trans hbounds.1 horder
        have hstep := Rat.mul_le_mul_of_nonneg_left
          hbounds.2 hhi_nonneg
        grind

theorem sinPiSquareScheduled_nondecreasing_of_sine_nondecreasing
    (S : ArctanSinPiConstruction)
    (hsine : NondecreasingOnInterval S.onHalf) :
    NondecreasingOnInterval
      (sinPiSquareOnHalfScheduledFunctionOnInterval S) := by
  intro x y hx hy hxy n
  have hx' : 0 <= x /\ x <= (1 : Rat) / 2 := by
    simpa [sinPiSquareOnHalfScheduledFunctionOnInterval,
      inDomainInterval] using hx
  have hy' : 0 <= y /\ y <= (1 : Rat) / 2 := by
    simpa [sinPiSquareOnHalfScheduledFunctionOnInterval,
      inDomainInterval] using hy
  have hmono := sinPiSquareOnHalf_nondecreasing_of_sine_nondecreasing
    S hsine
  change ((sinPiSquareOnHalf S).compute x
      (sinPiSquareFTCStageSchedule.stage n)).lo <=
    ((sinPiSquareOnHalf S).compute y
      (sinPiSquareFTCStageSchedule.stage n)).hi
  exact hmono x y hx' hy' hxy
    (sinPiSquareFTCStageSchedule.stage n)

def sinPiSquareScheduledMonotoneIntegral
    (S : ArctanSinPiConstruction)
    (hsine : NondecreasingOnInterval S.onHalf)
    (hregular : IntervalRegularOn
      (sinPiSquareOnHalfScheduledFunctionOnInterval S))
    (hinterval :
      (sinPiSquareOnHalfScheduledFunctionOnInterval S).lower <=
        (sinPiSquareOnHalfScheduledFunctionOnInterval S).upper)
    (schedule : Integral.MonotoneDarbouxSchedule
      (sinPiSquareOnHalfScheduledFunctionOnInterval S) hregular
      (sinPiSquareScheduled_nondecreasing_of_sine_nondecreasing S hsine)
      hinterval) : RealRaw :=
  Integral.monotoneDarbouxScheduleIntegralFor schedule

theorem sinPiSquareScheduledMonotoneIntegral_valid
    (S : ArctanSinPiConstruction)
    (hsine : NondecreasingOnInterval S.onHalf)
    (hregular : IntervalRegularOn
      (sinPiSquareOnHalfScheduledFunctionOnInterval S))
    (hinterval :
      (sinPiSquareOnHalfScheduledFunctionOnInterval S).lower <=
        (sinPiSquareOnHalfScheduledFunctionOnInterval S).upper)
    (schedule : Integral.MonotoneDarbouxSchedule
      (sinPiSquareOnHalfScheduledFunctionOnInterval S) hregular
      (sinPiSquareScheduled_nondecreasing_of_sine_nondecreasing S hsine)
      hinterval) :
    (sinPiSquareScheduledMonotoneIntegral S hsine hregular hinterval schedule).Valid := by
  exact Integral.monotoneDarbouxScheduleIntegralFor_valid schedule

theorem sinPiSquareScheduledMonotoneIntegral_equiv_value
    (S : ArctanSinPiConstruction)
    (hsine : NondecreasingOnInterval S.onHalf)
    (hregular : IntervalRegularOn
      (sinPiSquareOnHalfScheduledFunctionOnInterval S))
    (hinterval :
      (sinPiSquareOnHalfScheduledFunctionOnInterval S).lower <=
        (sinPiSquareOnHalfScheduledFunctionOnInterval S).upper)
    (schedule : Integral.MonotoneDarbouxSchedule
      (sinPiSquareOnHalfScheduledFunctionOnInterval S) hregular
      (sinPiSquareScheduled_nondecreasing_of_sine_nondecreasing S hsine)
      hinterval)
    (endpoint : RealRaw) (hendpoint : endpoint.Valid)
    (hFTC :
      (sinPiSquareScheduledMonotoneIntegral S hsine hregular hinterval schedule).Equiv
        endpoint)
    (hvalue : endpoint.Equiv (RealRaw.ofRat (1 / 4))) :
    (sinPiSquareScheduledMonotoneIntegral S hsine hregular hinterval schedule).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  exact RealRaw.equiv_trans
    (sinPiSquareScheduledMonotoneIntegral_valid S hsine hregular hinterval schedule)
    hendpoint (RealRaw.ofRat_valid _) hFTC hvalue

/-! Once interval regularity and sine monotonicity are supplied, the public
monotone-Darboux integral for the squared evaluator is a concrete `RealRaw`.
The schedule is proof-relevant; no completed-real integral is hidden here. -/

def sinPiSquareMonotoneIntegral
    (S : ArctanSinPiConstruction)
    (hsine : NondecreasingOnInterval S.onHalf)
    (hregular : IntervalRegularOn (sinPiSquareOnHalfFunctionOnInterval S))
    (hinterval :
      (sinPiSquareOnHalfFunctionOnInterval S).lower <=
        (sinPiSquareOnHalfFunctionOnInterval S).upper)
    (schedule : Integral.MonotoneDarbouxSchedule
      (sinPiSquareOnHalfFunctionOnInterval S) hregular
      (sinPiSquareOnHalf_nondecreasing_of_sine_nondecreasing S hsine)
      hinterval) : RealRaw :=
  Integral.monotoneDarbouxScheduleIntegralFor schedule

theorem sinPiSquareMonotoneIntegral_valid
    (S : ArctanSinPiConstruction)
    (hsine : NondecreasingOnInterval S.onHalf)
    (hregular : IntervalRegularOn (sinPiSquareOnHalfFunctionOnInterval S))
    (hinterval :
      (sinPiSquareOnHalfFunctionOnInterval S).lower <=
        (sinPiSquareOnHalfFunctionOnInterval S).upper)
    (schedule : Integral.MonotoneDarbouxSchedule
      (sinPiSquareOnHalfFunctionOnInterval S) hregular
      (sinPiSquareOnHalf_nondecreasing_of_sine_nondecreasing S hsine)
      hinterval) :
    (sinPiSquareMonotoneIntegral S hsine hregular hinterval schedule).Valid := by
  exact Integral.monotoneDarbouxScheduleIntegralFor_valid schedule

theorem sinPiSquareMonotoneIntegral_equiv_value
    (S : ArctanSinPiConstruction)
    (hsine : NondecreasingOnInterval S.onHalf)
    (hregular : IntervalRegularOn (sinPiSquareOnHalfFunctionOnInterval S))
    (hinterval :
      (sinPiSquareOnHalfFunctionOnInterval S).lower <=
        (sinPiSquareOnHalfFunctionOnInterval S).upper)
    (schedule : Integral.MonotoneDarbouxSchedule
      (sinPiSquareOnHalfFunctionOnInterval S) hregular
      (sinPiSquareOnHalf_nondecreasing_of_sine_nondecreasing S hsine)
      hinterval)
    (endpoint : RealRaw) (hendpoint : endpoint.Valid)
    (hFTC :
      (sinPiSquareMonotoneIntegral S hsine hregular hinterval schedule).Equiv
        endpoint)
    (hvalue : endpoint.Equiv (RealRaw.ofRat (1 / 4))) :
    (sinPiSquareMonotoneIntegral S hsine hregular hinterval schedule).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  exact RealRaw.equiv_trans
    (sinPiSquareMonotoneIntegral_valid S hsine hregular hinterval schedule)
    hendpoint (RealRaw.ofRat_valid _) hFTC hvalue

/-!
## The effective-FTC acceptance interface

The structure below is deliberately the concrete subgoal for the squared-sine
application.  It does not postulate an analytic primitive: an inhabitant must
provide a computable primitive and the finite local endpoint controls required
by `EffectiveDerivativeBoundFTC`.  Once those data exist, the generic closure
theorem supplies the FTC equivalence.
-/

structure SinPiSquareEffectiveFTCData
    (S : ArctanSinPiConstruction) where
  primitive : RealFunRaw
  certificate :
    EffectiveDerivativeBoundFTC primitive (sinPiSquareOnHalf S) 0 ((1 : Rat) / 2)
  integral_valid :
    certificate.toDerivativeBoundFTC.boundedIntegralRaw.Valid
  endpoint_valid :
    certificate.toDerivativeBoundFTC.endpointRaw.Valid

def SinPiSquareEffectiveFTCData.integralRaw
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S) : RealRaw :=
  D.certificate.toDerivativeBoundFTC.boundedIntegralRaw

def SinPiSquareEffectiveFTCData.endpointRaw
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S) : RealRaw :=
  D.certificate.toDerivativeBoundFTC.endpointRaw

theorem SinPiSquareEffectiveFTCData.integral_equiv_endpoint
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S) :
    D.integralRaw.Equiv D.endpointRaw := by
  exact effectiveDerivativeBoundFTC D.certificate

theorem SinPiSquareEffectiveFTCData.endpoint_equiv_of_value
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S)
    (hvalue : D.endpointRaw.Equiv (RealRaw.ofRat (1 / 4))) :
    D.integralRaw.Equiv (RealRaw.ofRat (1 / 4)) := by
  exact RealRaw.equiv_trans
    D.integral_valid D.endpoint_valid (RealRaw.ofRat_valid _)
    D.integral_equiv_endpoint hvalue

theorem SinPiSquareEffectiveFTCData.integral_equiv_public_stabilized
    {S : ArctanSinPiConstruction}
    (D : SinPiSquareEffectiveFTCData S)
    (hsine : IntervalRegularOn S.onHalf)
    (hvalue : D.endpointRaw.Equiv (RealRaw.ofRat (1 / 4)))
    (hshared : DyadicPublicSquareTangentSharedWitness S)
    (hanchor_value : tangentSquareIntegral.Equiv (RealRaw.ofRat (1 / 4))) :
    D.integralRaw.Equiv
      (dyadicPublicSquareIntegralRaw_stabilized S tangentSquareIntegral) := by
  have hD : D.integralRaw.Valid := D.integral_valid
  have hq : (RealRaw.ofRat (1 / 4)).Valid := RealRaw.ofRat_valid _
  have hpublic :
      (dyadicPublicSquareIntegralRaw_stabilized S tangentSquareIntegral).Valid :=
    DyadicPublicSquareTangentSharedWitness.stabilized_valid hshared hsine
  exact RealRaw.equiv_of_common_anchor hD hpublic hq
    (D.endpoint_equiv_of_value hvalue)
    (DyadicPublicSquareTangentSharedWitness.stabilized_equiv_value
      hshared hsine hanchor_value)

end SinPiIntegral

end ComputableAnalysis
