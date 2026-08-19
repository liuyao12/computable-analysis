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

theorem dyadicNestedRadicalSquareLeftSum_width_le
    (n : Nat) :
    (dyadicNestedRadicalSquareLeftSum n).width <=
      1 / ((n + 1 : Nat) : Rat) := by
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
    (mesh 0 ((1 : Rat) / 2) N *
      (2 / ((n + 1 : Nat) : Rat))) (by
      intro k hk
      have hklt : k < N := List.mem_range.mp hk
      rw [QInterval.scaleByRat_width_of_nonneg hmesh]
      exact Rat.mul_le_mul_of_nonneg_left
        (dyadicNestedRadicalSquareStage_width_le n k
          (by simpa [N] using hklt)) hmesh)
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
    _ <= (N : Rat) * (mesh 0 ((1 : Rat) / 2) N *
      (2 / ((n + 1 : Nat) : Rat))) := by simpa using hsum
    _ = 1 / ((n + 1 : Nat) : Rat) := by
      have hmesh_total := natCast_mul_mesh_eq_sub
        (a := (0 : Rat)) (b := (1 : Rat) / 2) hN
      rw [show (N : Rat) *
          (mesh 0 ((1 : Rat) / 2) N *
            (2 / ((n + 1 : Nat) : Rat))) =
          ((N : Rat) * mesh 0 ((1 : Rat) / 2) N) *
            (2 / ((n + 1 : Nat) : Rat)) by
          grind [Rat.mul_assoc]]
      rw [hmesh_total]
      have hden : ((n + 1 : Nat) : Rat) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero n)
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hden]

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

/- Prefix stabilization is the direct-only implementation of the missing
cross-stage nesting proof.  The anchor is a proof-side object; the stabilized
evaluator itself reads only the square candidate and the rational widths. -/
def dyadicNestedRadicalSquareIntegralRaw_stabilized
    (anchor : RealRaw) : RealRaw :=
  RealRaw.prefixStabilize dyadicNestedRadicalSquareIntegralRaw
    (fun n => (anchor.compute n).width)

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

end SinPiIntegral

end ComputableAnalysis
