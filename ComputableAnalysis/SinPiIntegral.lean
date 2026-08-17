import ComputableAnalysis.IntegralIdentities
import ComputableAnalysis.CauchyPi

/-!
# The half-interval integral of `sin (pi * x)`

This file is the proof-facing entry point for the first nontrivial
trigonometric integral.  The circle layer uses normalized quarter-turns: its
input `t` denotes the angle `t * pi / 2`.  Consequently the requested
function `sin (pi * x)` is obtained at a rational input by evaluating the
circle sine at `2 * x`; no real-valued argument and no primitive real `pi` are
used by the evaluator.

The final equality is intentionally expressed through an effective FTC
certificate.  The certificate is where the finite interval bounds,
monotonicity/turning-point analysis, and endpoint calculation belong.  This
keeps the theorem constructive: the dyadic integral algorithm is a raw
algorithm, while the FTC certificate identifies its value.
-/

namespace ComputableAnalysis

namespace RationalCircle

namespace GeometricTrig

/-- The normalized circle sine reparameterized as `sin (pi * x)`.

The input is rational and is only interpreted through the quarter-turn
parameter `2*x`.  In particular, this definition does not ask for a real
number named `pi` at a rational input.
-/
def sinPiRawOfConstruction
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) :
    PartialRealFunRaw where
  definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
  compute := fun x hx n =>
    C.sinFunctionRaw.compute (2 * x) (hdefined x hx.1 hx.2) n

theorem sinPiRawOfConstruction_valid
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) :
    forall x hx,
      RealRaw.ValidCompute
        ((sinPiRawOfConstruction C hdefined).compute x hx) := by
  intro x hx
  exact C.sinFunctionRaw_valid (2 * x) (hdefined x hx.1 hx.2)

end GeometricTrig

end RationalCircle

namespace SinPiIntegral

open RationalCircle.GeometricTrig

/-!
## The expected endpoint value

The integral certificate below is independent of which certified pi
implementation is preferred.  For the displayed value `1 / pi`, we use the
circle-area pi raw and invert its positive rational boxes.  This is an
interval operation, not division in Mathlib's real numbers.
-/

private theorem piCircleArea_interval_bounds (n : Nat) :
    2 <= (piCircleArea.compute n).lo /\
    (piCircleArea.compute n).hi <= 4 := by
  have hnest := (CauchyPi.piCircleArea_valid).2.1 0 n (Nat.zero_le n)
  have hlo : 2 <= (piCircleArea.compute n).lo := by
    simpa [piCircleArea_compute_zero] using hnest.1
  have hhi : (piCircleArea.compute n).hi <= 4 := by
    simpa [piCircleArea_compute_zero] using hnest.2.2
  exact ⟨hlo, hhi⟩

private theorem piCircleArea_interval_positive (n : Nat) :
    0 < (piCircleArea.compute n).lo := by
  have htwo : (0 : Rat) < 2 := by native_decide
  grind [piCircleArea_interval_bounds n]

private theorem one_div_antitone_pos_local {a b : Rat}
    (ha : 0 < a) (hab : a <= b) : 1 / b <= 1 / a := by
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · have hane : a ≠ 0 := Rat.ne_of_gt ha
    have hb : 0 < b := by grind
    have hbne : b ≠ 0 := Rat.ne_of_gt hb
    calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hbne]
      _ <= b := by grind
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hane]
  · exact Rat.mul_pos ha (by grind)

private theorem reciprocalPi_compute (n : Nat) :
    (QInterval.inv (piCircleArea.compute n)) =
      { lo := 1 / (piCircleArea.compute n).hi,
        hi := 1 / (piCircleArea.compute n).lo } := by
  simp [QInterval.inv, piCircleArea_interval_positive]

def reciprocalPiRaw : RealRaw where
  compute := fun n => QInterval.inv (piCircleArea.compute n)

theorem reciprocalPiRaw_valid : reciprocalPiRaw.Valid := by
  constructor
  · intro n
    change 0 <= (QInterval.inv (piCircleArea.compute n)).width
    rw [reciprocalPi_compute n]
    have hlo := piCircleArea_interval_positive n
    have hhi : 0 < (piCircleArea.compute n).hi := by
      grind [RealRaw.interval_order_of_valid piCircleArea
        CauchyPi.piCircleArea_valid n]
    have hreciplo : 0 < 1 / (piCircleArea.compute n).hi := by
      rw [Rat.div_def]
      exact Rat.mul_pos (by native_decide)
        ((Rat.inv_pos).2 hhi)
    have hreciphi : 0 < 1 / (piCircleArea.compute n).lo := by
      rw [Rat.div_def]
      exact Rat.mul_pos (by native_decide)
        ((Rat.inv_pos).2 hlo)
    have horder := RealRaw.interval_order_of_valid piCircleArea
      CauchyPi.piCircleArea_valid n
    have hrecip_order := one_div_antitone_pos_local hlo horder
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      change (QInterval.inv (piCircleArea.compute n)).lo <=
        (QInterval.inv (piCircleArea.compute m)).lo /\
        (QInterval.inv (piCircleArea.compute m)).lo <=
          (QInterval.inv (piCircleArea.compute m)).hi /\
        (QInterval.inv (piCircleArea.compute m)).hi <=
          (QInterval.inv (piCircleArea.compute n)).hi
      rw [reciprocalPi_compute n, reciprocalPi_compute m]
      have hvalid := CauchyPi.piCircleArea_valid
      have hnested := hvalid.2.1 n m hnm
      have hloN := piCircleArea_interval_positive n
      have hloM := piCircleArea_interval_positive m
      have hhiN := RealRaw.interval_order_of_valid piCircleArea hvalid n
      have hhiM := RealRaw.interval_order_of_valid piCircleArea hvalid m
      constructor
      · exact one_div_antitone_pos_local
          (a := (piCircleArea.compute m).hi)
          (b := (piCircleArea.compute n).hi) (by grind) hnested.2.2
      · constructor
        · exact one_div_antitone_pos_local
            (a := (piCircleArea.compute m).lo)
            (b := (piCircleArea.compute m).hi) hloM hhiM
        · exact one_div_antitone_pos_local
            (a := (piCircleArea.compute n).lo)
            (b := (piCircleArea.compute m).lo) hloN hnested.1
    · intro eps
      let wide : QPos :=
        { val := 4 * eps.val
          property := by exact Rat.mul_pos (by native_decide) eps.property }
      obtain ⟨N, hN⟩ := CauchyPi.piCircleArea_valid.2.2 wide
      refine ⟨N, ?_⟩
      intro n hn
      change (QInterval.inv (piCircleArea.compute n)).width <= eps.val
      rw [reciprocalPi_compute n]
      have hvalid := CauchyPi.piCircleArea_valid
      have hbounds := piCircleArea_interval_bounds n
      have hlo := piCircleArea_interval_positive n
      have hhi := RealRaw.interval_order_of_valid piCircleArea hvalid n
      have hwidth := hN n hn
      have hprod : 4 <=
          (piCircleArea.compute n).lo * (piCircleArea.compute n).hi := by
        have hlow := hbounds.1
        have horder := RealRaw.interval_order_of_valid piCircleArea
          hvalid n
        have hhigh : 2 <= (piCircleArea.compute n).hi := by grind
        calc
          (4 : Rat) = 2 * 2 := by native_decide
          _ <= (piCircleArea.compute n).lo * 2 := by
            exact Rat.mul_le_mul_of_nonneg_right hlow (by native_decide)
          _ <= (piCircleArea.compute n).lo *
              (piCircleArea.compute n).hi := by
            exact Rat.mul_le_mul_of_nonneg_left hhigh
              (by grind [piCircleArea_interval_bounds n])
      change 1 / (piCircleArea.compute n).lo -
        1 / (piCircleArea.compute n).hi <= eps.val
      rw [show (1 / (piCircleArea.compute n).lo) -
          (1 / (piCircleArea.compute n).hi) =
          ((piCircleArea.compute n).hi -
            (piCircleArea.compute n).lo) /
            ((piCircleArea.compute n).lo *
              (piCircleArea.compute n).hi) by
        rw [Rat.div_def, Rat.div_def, Rat.div_def]
        have hlo_ne : (piCircleArea.compute n).lo ≠ 0 :=
          Rat.ne_of_gt hlo
        have hhi_ne : (piCircleArea.compute n).hi ≠ 0 :=
          Rat.ne_of_gt (by grind)
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_rev,
          Rat.mul_inv_cancel _ hlo_ne, Rat.mul_inv_cancel _ hhi_ne]]
      have hwidth_nonneg : 0 <= (piCircleArea.compute n).width := by
        exact hvalid.1 n
      have hden := one_div_antitone_pos_local (by native_decide : (0 : Rat) < 4)
        hprod
      have hden' :
          ((piCircleArea.compute n).lo * (piCircleArea.compute n).hi)⁻¹ <=
            (1 / 4 : Rat) := by
        simpa [Rat.div_def] using hden
      calc
        ((piCircleArea.compute n).hi - (piCircleArea.compute n).lo) /
            ((piCircleArea.compute n).lo * (piCircleArea.compute n).hi) <=
            (piCircleArea.compute n).width * (1 / 4) := by
              rw [Rat.div_def]
              exact Rat.mul_le_mul_of_nonneg_left hden' hwidth_nonneg
        _ <= wide.val * (1 / 4) := by
              exact Rat.mul_le_mul_of_nonneg_right hwidth
                (by native_decide)
        _ = (4 * eps.val) / 4 := by
          dsimp [wide]
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ = eps.val := by
          rw [Rat.div_def]
          grind

/-!
## Executable dyadic inverse traces

The inverse step is not a classical inverse-function axiom.  A concrete
search records one left/right decision at each stage.  The interval itself is
then generated by rational midpoint arithmetic; the only analytic field is
that the forward interval image overlaps the requested target.
-/

/-- The rational interval selected by a finite left/right bisection path. -/
def dyadicCell (a b : Rat) (path : Nat -> Bool) : Nat -> QInterval
  | 0 => { lo := a, hi := b }
  | n + 1 =>
      let previous := dyadicCell a b path n
      let midpoint := (previous.lo + previous.hi) / 2
      if path n then
        { lo := previous.lo, hi := midpoint }
      else
        { lo := midpoint, hi := previous.hi }

/-- A fully executable inverse trace for a monotone interval branch.

`path` is the actual finite search trace.  `value_overlaps` is the one
function-specific obligation: the forward interval image of every selected
cell must overlap the target box.  The remaining fields ensure that this
trace is a valid shrinking raw interval and stays in the source branch.
-/
structure DyadicInverseTrace
    (I : InvertibleFunctionOnInterval)
    (y : InRangeRaw I) where
  path : Nat -> Bool
  cell_valid : RealRaw.ValidCompute (dyadicCell I.function.lower I.function.upper path)
  cell_in_source : forall n,
    subintervalOf
      (dyadicCell I.function.lower I.function.upper path n)
      I.function.lower I.function.upper
  value_overlaps : forall n,
    QInterval.Overlaps
      (I.continuous.regular.evalInterval
        (dyadicCell I.function.lower I.function.upper path n)
        (cell_in_source n) n)
      (y.value.compute n)

/-- Turn an executable dyadic trace into the inverse-search interface. -/
def DyadicInverseTrace.toSearch
    {I : InvertibleFunctionOnInterval} {y : InRangeRaw I}
    (h : DyadicInverseTrace I y) : InverseBisectionSearch I y where
  compute_preimage := dyadicCell I.function.lower I.function.upper h.path
  valid_preimage := h.cell_valid
  preimage_subinterval := h.cell_in_source
  value_overlaps := h.value_overlaps

theorem DyadicInverseTrace.toSearch_compute_preimage
    {I : InvertibleFunctionOnInterval} {y : InRangeRaw I}
    (h : DyadicInverseTrace I y) (n : Nat) :
    (h.toSearch.compute_preimage n) =
      dyadicCell I.function.lower I.function.upper h.path n :=
  rfl

/-- The arctangent inverse package obtained once every target has an
executable dyadic trace.  This is the exact assembly point for the
arctangent-defined sine construction: no choice of an inverse is taken. -/
def arctanInverseBisectionOfDyadicTraces
    (branch : InvertibleFunctionOnInterval)
    (branch_is_geometric : branch.function =
      IntegralIdentities.arctanGeomOnUnit)
    (targetAt : forall t : RationalCircle.GeometricTrig.QuarterTurn,
      RationalCircle.GeometricTrig.firstQuadrantBranch t -> InRangeRaw branch)
    (targetAt_equiv_halfQuarterTurn :
      forall t ht, (targetAt t ht).value.Equiv
        (RationalCircle.GeometricTrig.halfQuarterTurnRaw t))
    (traceAt : forall y : InRangeRaw branch,
      DyadicInverseTrace branch y) :
    IntegralIdentities.ArctanInverseBisection where
  branch := branch
  branch_is_geometric := branch_is_geometric
  targetAt := targetAt
  targetAt_equiv_halfQuarterTurn := targetAt_equiv_halfQuarterTurn
  bisectionAt := fun y => (traceAt y).toSearch

/-- The rational circle parametrization used after the inverse-arctangent
search.  For a half-angle slope `u`, its imaginary coordinate is
`2*u/(1+u^2)`. -/
def rationalCircleSin (u : Rat) : Rat :=
  (2 * u) / (1 + u * u)

def rationalCircleSinInterval (U : QInterval) : QInterval :=
  { lo := rationalCircleSin U.lo, hi := rationalCircleSin U.hi }

private theorem rationalCircleSin_den_pos {u : Rat} (hu : 0 <= u) :
    0 < 1 + u * u := by
  have hsq : 0 <= u * u := Rat.mul_nonneg hu hu
  grind

private theorem rat_eq_of_mul_eq_mul_pos_local {a b c : Rat}
    (hc : 0 < c) (h : a * c = b * c) : a = b := by
  have hcne : c ≠ 0 := Rat.ne_of_gt hc
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem rationalCircleSin_sub_formula {a b : Rat}
    (ha : 0 <= a) (hb : 0 <= b) :
    rationalCircleSin b - rationalCircleSin a =
      (2 * (b - a) * (1 - a * b)) /
        ((1 + a * a) * (1 + b * b)) := by
  let da : Rat := 1 + a * a
  let db : Rat := 1 + b * b
  have hda : 0 < da := by
    dsimp [da]
    exact rationalCircleSin_den_pos ha
  have hdb : 0 < db := by
    dsimp [db]
    exact rationalCircleSin_den_pos hb
  have hprod : 0 < da * db := Rat.mul_pos hda hdb
  apply rat_eq_of_mul_eq_mul_pos_local (c := da * db) hprod
  unfold rationalCircleSin
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hda_ne : da ≠ 0 := Rat.ne_of_gt hda
  have hdb_ne : db ≠ 0 := Rat.ne_of_gt hdb
  have hda_cancel : da⁻¹ * da = 1 := Rat.inv_mul_cancel da hda_ne
  have hdb_cancel : db⁻¹ * db = 1 := Rat.inv_mul_cancel db hdb_ne
  have hleft :
      (2 * b * db⁻¹ - 2 * a * da⁻¹) * (da * db) =
        2 * b * da - 2 * a * db := by
    calc
      (2 * b * db⁻¹ - 2 * a * da⁻¹) * (da * db) =
            (2 * b * db⁻¹) * (da * db) -
            (2 * a * da⁻¹) * (da * db) := by
              grind [Rat.sub_eq_add_neg, Rat.add_mul]
      _ = 2 * b * da - 2 * a * db := by
        have h1 : (2 * b * db⁻¹) * (da * db) = 2 * b * da := by
          calc
            (2 * b * db⁻¹) * (da * db) =
                2 * b * da * (db⁻¹ * db) := by
                  grind [Rat.mul_assoc, Rat.mul_comm]
            _ = 2 * b * da := by rw [hdb_cancel, Rat.mul_one]
        have h2 : (2 * a * da⁻¹) * (da * db) = 2 * a * db := by
          calc
            (2 * a * da⁻¹) * (da * db) =
                2 * a * db * (da⁻¹ * da) := by
                  grind [Rat.mul_assoc, Rat.mul_comm]
            _ = 2 * a * db := by rw [hda_cancel, Rat.mul_one]
        rw [h1, h2]
  have hright :
      (2 * (b - a) * (1 - a * b) * (da * db)⁻¹) * (da * db) =
        2 * (b - a) * (1 - a * b) := by
    calc
      (2 * (b - a) * (1 - a * b) * (da * db)⁻¹) * (da * db) =
          2 * (b - a) * (1 - a * b) *
            ((da * db)⁻¹ * (da * db)) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
      _ = 2 * (b - a) * (1 - a * b) := by
        have hcancel : (da * db)⁻¹ * (da * db) = 1 :=
          Rat.inv_mul_cancel (da * db) (Rat.ne_of_gt hprod)
        rw [hcancel, Rat.mul_one]
  rw [hleft, hright]
  dsimp [da, db]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

private theorem rationalCircleSin_mono {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hb : b <= 1) :
    rationalCircleSin a <= rationalCircleSin b := by
  have hb0 : 0 <= b := Rat.le_trans ha hab
  have hprod : a * b <= 1 := by
    have h1 := Rat.mul_le_mul_of_nonneg_right hb ha
    have h2 := Rat.mul_le_mul_of_nonneg_left hab (Rat.le_of_lt (by native_decide : (0 : Rat) < 1))
    grind
  have hba : 0 <= b - a := by grind
  have hnum : 0 <= 2 * (b - a) * (1 - a * b) := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by native_decide) hba) (by grind)
  have hden : 0 < (1 + a * a) * (1 + b * b) :=
    Rat.mul_pos (rationalCircleSin_den_pos ha)
      (rationalCircleSin_den_pos hb0)
  have hdiff : 0 <= rationalCircleSin b - rationalCircleSin a := by
    rw [rationalCircleSin_sub_formula ha hb0, Rat.div_def]
    exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))
  grind [Rat.sub_eq_add_neg]

private theorem rationalCircleSin_width_le {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hb : b <= 1) :
    rationalCircleSin b - rationalCircleSin a <= 2 * (b - a) := by
  have hb0 : 0 <= b := Rat.le_trans ha hab
  have hba : 0 <= b - a := by grind
  have habprod : a * b <= 1 := by
    have h := Rat.mul_le_mul_of_nonneg_right hb ha
    grind
  have hden : 0 < (1 + a * a) * (1 + b * b) :=
    Rat.mul_pos (rationalCircleSin_den_pos ha)
      (rationalCircleSin_den_pos hb0)
  have hden_one : 1 <= (1 + a * a) * (1 + b * b) := by
    have haa : 0 <= a * a := Rat.mul_nonneg ha ha
    have hbb : 0 <= b * b := Rat.mul_nonneg hb0 hb0
    have hsum : 0 <= a * a + b * b + (a * a) * (b * b) := by
      exact Rat.add_nonneg (Rat.add_nonneg haa hbb)
        (Rat.mul_nonneg haa hbb)
    grind [Rat.mul_add, Rat.add_mul]
  rw [rationalCircleSin_sub_formula ha hb0]
  apply Rat.le_of_mul_le_mul_right (c :=
    (1 + a * a) * (1 + b * b))
  · rw [Rat.div_def]
    let D : Rat := (1 + a * a) * (1 + b * b)
    let N : Rat := 2 * (b - a) * (1 - a * b)
    have hD : D = (1 + a * a) * (1 + b * b) := rfl
    have hcancel : D⁻¹ * D = 1 :=
      Rat.inv_mul_cancel D (Rat.ne_of_gt hden)
    have hNnonneg : 0 <= N := by
      dsimp [N]
      exact Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) hba) (by grind)
    have hNle : N <= 2 * (b - a) := by
      dsimp [N]
      have hp : 0 <= a * b := Rat.mul_nonneg ha hb0
      have hfactor : 1 - a * b <= 1 := by
        grind only [Rat.sub_eq_add_neg]
      exact (by
        calc
          2 * (b - a) * (1 - a * b) <=
              2 * (b - a) * 1 := by
            exact Rat.mul_le_mul_of_nonneg_left hfactor
              (Rat.mul_nonneg (by native_decide) hba)
          _ = 2 * (b - a) := by simp)
    calc
      (N * D⁻¹) * D = N := by
        rw [Rat.mul_assoc, hcancel, Rat.mul_one]
      _ <= 2 * (b - a) * 1 := by simpa using hNle
      _ <= 2 * (b - a) * D := by
        exact Rat.mul_le_mul_of_nonneg_left hden_one
          (Rat.mul_nonneg (by native_decide) hba)
  · exact hden

private theorem rationalCircleSinInterval_valid
    (u : Nat -> QInterval)
    (hu : RealRaw.ValidCompute u)
    (hubounds : forall n, 0 <= (u n).lo /\ (u n).hi <= 1) :
    RealRaw.ValidCompute (fun n => rationalCircleSinInterval (u n)) := by
  constructor
  · intro n
    have horder : (u n).lo <= (u n).hi := by
      have := hu.1 n
      grind [QInterval.width]
    have hmono := rationalCircleSin_mono
      (hubounds n).1 horder (hubounds n).2
    change rationalCircleSin (u n).hi - rationalCircleSin (u n).lo >= 0
    grind
  constructor
  · intro n m hnm
    have hn := hu.2.1 n m hnm
    have hnl := hubounds n
    have hml := hubounds m
    have hlo := rationalCircleSin_mono hnl.1 hn.1
      (Rat.le_trans hn.2.1 hml.2)
    have hmid := rationalCircleSin_mono hml.1 hn.2.1 hml.2
    have hhi := rationalCircleSin_mono
      (Rat.le_trans hml.1 hn.2.1) hn.2.2 hnl.2
    exact ⟨hlo, hmid, hhi⟩
  · intro eps
    have htwo_pos : 0 < (2 : Rat) := by native_decide
    let half : QPos := ⟨eps.val / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 htwo_pos)⟩
    obtain ⟨N, hN⟩ := hu.2.2 half
    refine ⟨N, ?_⟩
    intro n hn
    have horder : (u n).lo <= (u n).hi := by
      have := hu.1 n
      grind [QInterval.width]
    have hw := rationalCircleSin_width_le
      (hubounds n).1 horder (hubounds n).2
    have hsmall := hN n hn
    have hscaled := Rat.mul_le_mul_of_nonneg_left hsmall
      (by native_decide : (0 : Rat) <= 2)
    change rationalCircleSin (u n).hi - rationalCircleSin (u n).lo <= eps.val
    have hhalf : 2 * half.val = eps.val := by
      dsimp [half]
      rw [Rat.div_def]
      have htwo : (2 : Rat) ≠ 0 := by native_decide
      grind [Rat.mul_assoc, Rat.mul_comm]
    calc
      rationalCircleSin (u n).hi - rationalCircleSin (u n).lo <=
          2 * ((u n).hi - (u n).lo) := hw
      _ <= 2 * half.val := hscaled
      _ = eps.val := hhalf

/-! The real-coordinate companion used by the primitive. -/

def rationalCircleCos (u : Rat) : Rat :=
  (1 - u * u) / (1 + u * u)

def rationalCircleCosInterval (U : QInterval) : QInterval :=
  { lo := rationalCircleCos U.hi, hi := rationalCircleCos U.lo }

private theorem rationalCircleCos_sub_formula {a b : Rat}
    (ha : 0 <= a) (hb : 0 <= b) :
    rationalCircleCos a - rationalCircleCos b =
      (2 * (b - a) * (a + b)) /
        ((1 + a * a) * (1 + b * b)) := by
  let da : Rat := 1 + a * a
  let db : Rat := 1 + b * b
  have hda : 0 < da := by
    dsimp [da]
    exact rationalCircleSin_den_pos ha
  have hdb : 0 < db := by
    dsimp [db]
    exact rationalCircleSin_den_pos hb
  have hprod : 0 < da * db := Rat.mul_pos hda hdb
  apply rat_eq_of_mul_eq_mul_pos_local (c := da * db) hprod
  unfold rationalCircleCos
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hda_ne : da ≠ 0 := Rat.ne_of_gt hda
  have hdb_ne : db ≠ 0 := Rat.ne_of_gt hdb
  have hda_cancel : da⁻¹ * da = 1 := Rat.inv_mul_cancel da hda_ne
  have hdb_cancel : db⁻¹ * db = 1 := Rat.inv_mul_cancel db hdb_ne
  have hleft :
      ((1 - a * a) * da⁻¹ - (1 - b * b) * db⁻¹) * (da * db) =
        (1 - a * a) * db - (1 - b * b) * da := by
    calc
      ((1 - a * a) * da⁻¹ - (1 - b * b) * db⁻¹) * (da * db) =
          ((1 - a * a) * da⁻¹) * (da * db) -
            ((1 - b * b) * db⁻¹) * (da * db) := by
              grind [Rat.sub_eq_add_neg, Rat.add_mul]
      _ = (1 - a * a) * db - (1 - b * b) * da := by
        have h1 : ((1 - a * a) * da⁻¹) * (da * db) =
            (1 - a * a) * db := by
          calc
            ((1 - a * a) * da⁻¹) * (da * db) =
                (1 - a * a) * db * (da⁻¹ * da) := by
                  grind [Rat.mul_assoc, Rat.mul_comm]
            _ = (1 - a * a) * db := by rw [hda_cancel, Rat.mul_one]
        have h2 : ((1 - b * b) * db⁻¹) * (da * db) =
            (1 - b * b) * da := by
          calc
            ((1 - b * b) * db⁻¹) * (da * db) =
                (1 - b * b) * da * (db⁻¹ * db) := by
                  grind [Rat.mul_assoc, Rat.mul_comm]
            _ = (1 - b * b) * da := by rw [hdb_cancel, Rat.mul_one]
        rw [h1, h2]
  have hright :
      (2 * (b - a) * (a + b) * (da * db)⁻¹) * (da * db) =
        2 * (b - a) * (a + b) := by
    rw [Rat.mul_assoc, Rat.inv_mul_cancel (da * db) (Rat.ne_of_gt hprod),
      Rat.mul_one]
  rw [hleft, hright]
  dsimp [da, db]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

private theorem rationalCircleCos_mono {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hb : b <= 1) :
    rationalCircleCos b <= rationalCircleCos a := by
  have hb0 : 0 <= b := Rat.le_trans ha hab
  have hdiff := rationalCircleCos_sub_formula ha hb0
  have hba : 0 <= b - a := by grind
  have hsum : 0 <= a + b := by grind
  have hden : 0 < (1 + a * a) * (1 + b * b) :=
    Rat.mul_pos (rationalCircleSin_den_pos ha)
      (rationalCircleSin_den_pos hb0)
  have hnum : 0 <= 2 * (b - a) * (a + b) := by
    exact Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) hba) hsum
  have hinv : 0 <= ((1 + a * a) * (1 + b * b))⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hden)
  have hdiff_nonneg : 0 <= rationalCircleCos a - rationalCircleCos b := by
    rw [hdiff, Rat.div_def]
    exact Rat.mul_nonneg hnum hinv
  grind [Rat.sub_eq_add_neg]

private theorem rationalCircleCos_width_le {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hb : b <= 1) :
    rationalCircleCos a - rationalCircleCos b <= 4 * (b - a) := by
  have hb0 : 0 <= b := Rat.le_trans ha hab
  have hden : 0 < (1 + a * a) * (1 + b * b) :=
    Rat.mul_pos (rationalCircleSin_den_pos ha)
      (rationalCircleSin_den_pos hb0)
  have hden_one : 1 <= (1 + a * a) * (1 + b * b) := by
    have haa : 0 <= a * a := Rat.mul_nonneg ha ha
    have hbb : 0 <= b * b := Rat.mul_nonneg hb0 hb0
    have hA : 1 <= 1 + a * a := by grind
    have hB : 1 <= 1 + b * b := by grind
    have hA0 : 0 <= 1 + a * a := by grind
    calc
      (1 : Rat) = 1 * 1 := by native_decide
      _ <= (1 + a * a) * 1 :=
        Rat.mul_le_mul_of_nonneg_right hA (by native_decide)
      _ <= (1 + a * a) * (1 + b * b) :=
        Rat.mul_le_mul_of_nonneg_left hB hA0
  rw [rationalCircleCos_sub_formula ha hb0]
  apply Rat.le_of_mul_le_mul_right
    (c := (1 + a * a) * (1 + b * b))
  · rw [Rat.div_def]
    have hba : 0 <= b - a := by grind
    have hsum : 0 <= a + b := by grind
    have hnum : 0 <= 2 * (b - a) * (a + b) := by
      exact Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) hba) hsum
    have hsum_le : a + b <= 2 := by grind
    have hsumD : a + b <= 2 *
        ((1 + a * a) * (1 + b * b)) := by
      calc
        a + b <= 2 := hsum_le
        _ <= 2 * ((1 + a * a) * (1 + b * b)) := by
          simpa using Rat.mul_le_mul_of_nonneg_left hden_one
            (by native_decide : (0 : Rat) <= 2)
    have hnum_le : 2 * (b - a) * (a + b) <=
        4 * (b - a) * ((1 + a * a) * (1 + b * b)) := by
      calc
        2 * (b - a) * (a + b) <=
            2 * (b - a) * (2 *
              ((1 + a * a) * (1 + b * b))) := by
          exact Rat.mul_le_mul_of_nonneg_left hsumD
            (Rat.mul_nonneg (by native_decide) hba)
        _ = 4 * (b - a) * ((1 + a * a) * (1 + b * b)) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    calc
      (2 * (b - a) * (a + b) *
          ((1 + a * a) * (1 + b * b))⁻¹) *
          ((1 + a * a) * (1 + b * b)) =
          2 * (b - a) * (a + b) := by
            rw [Rat.mul_assoc,
              Rat.inv_mul_cancel _ (Rat.ne_of_gt hden), Rat.mul_one]
      _ <= 4 * (b - a) * ((1 + a * a) * (1 + b * b)) := hnum_le
  · exact hden

private theorem rationalCircleCosInterval_valid
    (u : Nat -> QInterval)
    (hu : RealRaw.ValidCompute u)
    (hubounds : forall n, 0 <= (u n).lo /\ (u n).hi <= 1) :
    RealRaw.ValidCompute (fun n => rationalCircleCosInterval (u n)) := by
  constructor
  · intro n
    have horder := RealRaw.interval_order_of_valid
      { compute := u } hu n
    have hmono := rationalCircleCos_mono
      (hubounds n).1 horder (hubounds n).2
    change 0 <= rationalCircleCos (u n).lo - rationalCircleCos (u n).hi
    grind [Rat.sub_eq_add_neg]
  constructor
  · intro n m hnm
    have hn := hu.2.1 n m hnm
    have hnl := hubounds n
    have hml := hubounds m
    have hcosLo := rationalCircleCos_mono
      (by grind [RealRaw.interval_order_of_valid { compute := u } hu m])
      hn.2.2 hnl.2
    have hcosMid := rationalCircleCos_mono hml.1
      (RealRaw.interval_order_of_valid { compute := u } hu m) hml.2
    have hcosHi := rationalCircleCos_mono hnl.1 hn.1
      (by grind [hml.2, RealRaw.interval_order_of_valid { compute := u } hu m])
    exact ⟨hcosLo, hcosMid, hcosHi⟩
  · intro eps
    obtain ⟨N, hN⟩ := hu.2.2 ⟨eps.val / 4, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by native_decide))⟩
    refine ⟨N, ?_⟩
    intro n hn
    have horder := RealRaw.interval_order_of_valid { compute := u } hu n
    have hw := hN n hn
    have hcos := rationalCircleCos_width_le
      (hubounds n).1 horder (hubounds n).2
    have hscaled := Rat.mul_le_mul_of_nonneg_left hw
      (by native_decide : (0 : Rat) <= 4)
    change rationalCircleCos (u n).lo - rationalCircleCos (u n).hi <= eps.val
    calc
      rationalCircleCos (u n).lo - rationalCircleCos (u n).hi <=
          4 * ((u n).hi - (u n).lo) := hcos
      _ <= 4 * (eps.val / 4) := hscaled
      _ = eps.val := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]

/-- `sin(pi*x)` from the arctangent inverse, on rational `x` in `[0,1/2]`.

The computation first recovers the half-angle slope by certified bisection,
then applies the rational circle formula. -/
def sinPiRawOfArctan
    (B : IntegralIdentities.ArctanInverseBisection)
    (x : Rat)
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) : RealRaw where
  compute := fun n =>
    rationalCircleSinInterval
      ((B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by native_decide) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2 (by native_decide : (0 : Rat) <= 2)
            have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
            rw [hhalf] at h
            exact h) n))

/-- The arctangent-backed pointwise sine evaluator.  The validity field is
the finite interval proof that the monotone rational formula transports the
inverse boxes. -/
structure ArctanSinPiConstruction where
  inverse : IntegralIdentities.ArctanInverseBisection
  sin_valid : forall x hx,
    RealRaw.ValidCompute
      ((sinPiRawOfArctan inverse x hx).compute)

/-- Build the sine construction from the inverse search and its finite
first-quadrant range proof.  The validity of the circle-coordinate evaluator
is discharged by `rationalCircleSinInterval_valid`; it is not an additional
analytic axiom. -/
def ArctanSinPiConstruction.ofInverse
    (B : IntegralIdentities.ArctanInverseBisection)
    (slope_bounded : forall x (hx : 0 <= x /\ x <= (1 : Rat) / 2) n,
      0 <= (B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by native_decide) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2
              (by native_decide : (0 : Rat) <= 2)
            have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
            rw [hhalf] at h
            exact h) n).lo /\
      (B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by native_decide) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2
              (by native_decide : (0 : Rat) <= 2)
            have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
            rw [hhalf] at h
            exact h) n).hi <= 1) :
    ArctanSinPiConstruction where
  inverse := B
  sin_valid := by
    intro x hx
    apply rationalCircleSinInterval_valid
    · exact B.tangentRaw_valid (2 * x) _
    · exact slope_bounded x hx

theorem arctanInverse_slope_bounded
    (B : IntegralIdentities.ArctanInverseBisection)
    (x : Rat) (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    0 <= (B.tangentRaw.compute (2 * x)
      (by
        change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
        constructor
        · exact Rat.mul_nonneg (by native_decide) hx.1
        · have h := Rat.mul_le_mul_of_nonneg_left hx.2
            (by native_decide : (0 : Rat) <= 2)
          have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
          rw [hhalf] at h
          exact h) n).lo /\
      (B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by native_decide) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2
              (by native_decide : (0 : Rat) <= 2)
            have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
            rw [hhalf] at h
            exact h) n).hi <= 1 := by
  let ht : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x) := by
    change 0 <= 2 * x /\ 2 * x <= 1
    constructor
    · exact Rat.mul_nonneg (by native_decide) hx.1
    · have h := Rat.mul_le_mul_of_nonneg_left hx.2
        (by native_decide : (0 : Rat) <= 2)
      have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
      rw [hhalf] at h
      exact h
  have hs := B.tangentAt_stays_in_unitSlope (2 * x) ht n
  change 0 <= ((B.tangentAt (2 * x) ht).compute n).lo /\
    ((B.tangentAt (2 * x) ht).compute n).hi <= 1
  exact ⟨hs.1, hs.2.2⟩

def ArctanSinPiConstruction.canonical
    (B : IntegralIdentities.ArctanInverseBisection) :
    ArctanSinPiConstruction :=
  ArctanSinPiConstruction.ofInverse B
    (fun x hx n => arctanInverse_slope_bounded B x hx n)

/-! The explicit cosine coordinate and the primitive target. -/

/-- `cos (pi*x)` from the same inverse slope boxes used by `sinPiRaw`. -/
def cosPiRawOfArctan
    (B : IntegralIdentities.ArctanInverseBisection)
    (x : Rat)
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) : RealRaw where
  compute := fun n =>
    rationalCircleCosInterval
      ((B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by native_decide) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2
              (by native_decide : (0 : Rat) <= 2)
            have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
            rw [hhalf] at h
            exact h) n))

theorem cosPiRawOfArctan_valid
    (B : IntegralIdentities.ArctanInverseBisection)
    (x : Rat) (hx : 0 <= x /\ x <= (1 : Rat) / 2) :
    (cosPiRawOfArctan B x hx).Valid := by
  apply rationalCircleCosInterval_valid
  · exact B.tangentRaw_valid (2 * x) _
  · exact fun n => arctanInverse_slope_bounded B x hx n

def cosPiOnHalf
    (B : IntegralIdentities.ArctanInverseBisection) : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
    compute := fun x hx => (cosPiRawOfArctan B x hx).compute
  }
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact cosPiRawOfArctan_valid B x hx

theorem rationalCircleCos_bounds {u : Rat}
    (hu : 0 <= u) (hu1 : u <= 1) :
    0 <= rationalCircleCos u /\ rationalCircleCos u <= 1 := by
  have hleft := rationalCircleCos_mono hu hu1 (by native_decide)
  have hright := rationalCircleCos_mono (by native_decide : (0 : Rat) <= 0)
    hu hu1
  have hcos0 : rationalCircleCos 0 = 1 := by native_decide
  have hcos1 : rationalCircleCos 1 = 0 := by native_decide
  constructor
  · simpa [hcos1] using hleft
  · simpa [hcos0] using hright

theorem cosPiRawOfArctan_zero_equiv_one_of_tangent_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero) :
    (cosPiRawOfArctan B 0
      ⟨by native_decide, by native_decide⟩).Equiv RealRaw.one := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (cosPiRawOfArctan B 0 ⟨by native_decide, by native_decide⟩)
    RealRaw.one n n).2
  have hT : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Valid :=
    B.tangentAt_valid 0 RationalCircle.GeometricTrig.firstQuadrantBranch_zero
  have hbounds := B.tangentAt_stays_in_unitSlope 0
    RationalCircle.GeometricTrig.firstQuadrantBranch_zero n
  have hzero := (RealRaw.compareAt_overlap_iff
    (B.tangentAt 0 RationalCircle.GeometricTrig.firstQuadrantBranch_zero)
    RealRaw.zero n n).1 (ht n)
  simp [RealRaw.zero, RealRaw.ofRat] at hzero
  let ht0 : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * 0) := by
    dsimp [RationalCircle.GeometricTrig.firstQuadrantBranch,
      RationalCircle.GeometricTrig.unitIntervalBranch]
    constructor <;> native_decide
  have hbounds' : subintervalOf (B.tangentRaw.compute (2 * 0) ht0 n) 0 1 := by
    simpa [IntegralIdentities.ArctanInverseBisection.tangentRaw,
      IntegralIdentities.ArctanInverseBisection.tangentAt] using hbounds
  change QInterval.Overlaps
    (rationalCircleCosInterval (B.tangentRaw.compute (2 * 0) ht0 n))
    { lo := 1, hi := 1 }
  simp only [rationalCircleCosInterval]
  have hlo : ((B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).compute n).lo = 0 := by
    apply Rat.le_antisymm
    · exact hzero.1
    · exact hbounds.1
  have hlo' : (B.tangentRaw.compute (2 * 0) ht0 n).lo = 0 := by
    simpa [IntegralIdentities.ArctanInverseBisection.tangentRaw,
      IntegralIdentities.ArctanInverseBisection.tangentAt] using hlo
  rw [hlo']
  have hcos := rationalCircleCos_bounds
    (by grind [hbounds'.1, hbounds'.2.1]) hbounds'.2.2
  have hcos0 : rationalCircleCos 0 = 1 := by native_decide
  rw [hcos0]
  unfold QInterval.Overlaps
  change rationalCircleCos (B.tangentRaw.compute (2 * 0) ht0 n).hi <= 1 /\
    (1 : Rat) <= 1
  exact ⟨hcos.2, by native_decide⟩

theorem cosPiRawOfArctan_half_equiv_zero_of_tangent_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht : (B.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealRaw.one) :
    (cosPiRawOfArctan B (1 / 2)
      ⟨by native_decide, by native_decide⟩).Equiv RealRaw.zero := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (cosPiRawOfArctan B (1 / 2) ⟨by native_decide, by native_decide⟩)
    RealRaw.zero n n).2
  have hT : (B.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Valid :=
    B.tangentAt_valid 1 RationalCircle.GeometricTrig.firstQuadrantBranch_one
  have hbounds := B.tangentAt_stays_in_unitSlope 1
    RationalCircle.GeometricTrig.firstQuadrantBranch_one n
  have hone := (RealRaw.compareAt_overlap_iff
    (B.tangentAt 1 RationalCircle.GeometricTrig.firstQuadrantBranch_one)
    RealRaw.one n n).1 (ht n)
  simp [RealRaw.one, RealRaw.ofRat] at hone
  let htHalf : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * (1 / 2)) := by
    dsimp [RationalCircle.GeometricTrig.firstQuadrantBranch,
      RationalCircle.GeometricTrig.unitIntervalBranch]
    constructor <;> native_decide
  have htwo : (2 : Rat) * (1 / 2) = 1 := by native_decide
  have hbounds' : subintervalOf
      (B.tangentRaw.compute (2 * (1 / 2)) htHalf n) 0 1 := by
    simpa [htwo, IntegralIdentities.ArctanInverseBisection.tangentRaw,
      IntegralIdentities.ArctanInverseBisection.tangentAt] using hbounds
  have hone' : 1 <= (B.tangentRaw.compute (2 * (1 / 2)) htHalf n).hi := by
    simpa [htwo, IntegralIdentities.ArctanInverseBisection.tangentRaw,
      IntegralIdentities.ArctanInverseBisection.tangentAt] using hone.2
  have hhi : (B.tangentRaw.compute (2 * (1 / 2)) htHalf n).hi = 1 := by
    apply Rat.le_antisymm
    · exact hbounds'.2.2
    · exact hone'
  have hcos : 0 <= rationalCircleCos
      (B.tangentRaw.compute (2 * (1 / 2)) htHalf n).lo :=
    (rationalCircleCos_bounds hbounds'.1 (by grind [hbounds'.2.1])).1
  change QInterval.Overlaps
    (rationalCircleCosInterval
      (B.tangentRaw.compute (2 * (1 / 2)) htHalf n))
    { lo := 0, hi := 0 }
  simp only [rationalCircleCosInterval]
  rw [hhi]
  have hcos1 : rationalCircleCos 1 = 0 := by native_decide
  rw [hcos1]
  unfold QInterval.Overlaps
  change (0 : Rat) <= 0 /\ 0 <=
    rationalCircleCos (B.tangentRaw.compute (2 * (1 / 2)) htHalf n).lo
  exact ⟨by native_decide, hcos⟩

def reciprocalPiFunRaw : RealFunRaw where
  domain := fun x => 0 <= x /\ x <= (1 : Rat) / 2
  compute := fun _ n => reciprocalPiRaw.compute n

theorem reciprocalPiFunRaw_valid : reciprocalPiFunRaw.Valid := by
  intro _ _
  exact reciprocalPiRaw_valid

theorem reciprocalPiRaw_bounds (n : Nat) :
    0 <= (reciprocalPiRaw.compute n).lo /\
    (reciprocalPiRaw.compute n).hi <= 1 := by
  change 0 <= (QInterval.inv (piCircleArea.compute n)).lo /\
    (QInterval.inv (piCircleArea.compute n)).hi <= 1
  rw [reciprocalPi_compute n]
  have hpi := piCircleArea_interval_bounds n
  have hpos : 0 < (piCircleArea.compute n).lo :=
    piCircleArea_interval_positive n
  constructor
  · exact Rat.le_of_lt (by
      rw [Rat.div_def]
      exact Rat.mul_pos (by native_decide)
        ((Rat.inv_pos).2 (by grind [RealRaw.interval_order_of_valid
          piCircleArea CauchyPi.piCircleArea_valid n])))
  · have h1 : (1 : Rat) <= (piCircleArea.compute n).lo := by
      grind [hpi.1]
    have hone := one_div_antitone_pos_local (a := (1 : Rat))
        (b := (piCircleArea.compute n).lo) (by native_decide) h1
    have honeone : (1 : Rat) / 1 = 1 := by native_decide
    rw [honeone] at hone
    exact hone

def oneMinusCosFunRaw
    (B : IntegralIdentities.ArctanInverseBisection) : RealFunRaw where
  domain := fun x => 0 <= x /\ x <= (1 : Rat) / 2
  compute := fun x n =>
    if hx : 0 <= x /\ x <= (1 : Rat) / 2 then
      let C := (cosPiRawOfArctan B x hx).compute n
      { lo := 1 - C.hi, hi := 1 - C.lo }
    else
      { lo := 0, hi := 0 }

theorem oneMinusCosFunRaw_valid
  (B : IntegralIdentities.ArctanInverseBisection) :
    (oneMinusCosFunRaw B).Valid := by
  intro x hx
  change 0 <= x /\ x <= (1 : Rat) / 2 at hx
  let C : RealRaw := cosPiRawOfArctan B x hx
  have hC : C.Valid := cosPiRawOfArctan_valid B x hx
  have horder : forall n, (C.compute n).lo <= (C.compute n).hi :=
    fun n => RealRaw.interval_order_of_valid C hC n
  have hbounds : forall n, 0 <= (C.compute n).lo /\
      (C.compute n).hi <= 1 := by
    intro n
    have ht := arctanInverse_slope_bounded B x hx n
    have htarg : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x) := by
      change 0 <= 2 * x /\ 2 * x <= 1
      constructor
      · exact Rat.mul_nonneg (by native_decide) hx.1
      · have h := Rat.mul_le_mul_of_nonneg_left hx.2
          (by native_decide : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
        rw [hhalf] at h
        exact h
    have htv := B.tangentRaw_valid (2 * x) htarg
    have hto := RealRaw.interval_order_of_valid
      { compute := B.tangentRaw.compute (2 * x) htarg } htv n
    have hlo := rationalCircleCos_bounds ht.1 (by grind [ht.2])
    have hhi := rationalCircleCos_bounds (by grind [ht.1]) ht.2
    exact ⟨hhi.1, hlo.2⟩
  change RealRaw.ValidCompute ((oneMinusCosFunRaw B).compute x)
  simp only [oneMinusCosFunRaw, dif_pos hx]
  change RealRaw.ValidCompute (fun n =>
    { lo := 1 - (C.compute n).hi, hi := 1 - (C.compute n).lo })
  constructor
  · intro n
    change 0 <= (1 - (C.compute n).lo) - (1 - (C.compute n).hi)
    grind [hbounds n]
  constructor
  · intro n m hnm
    have hn := hC.2.1 n m hnm
    constructor
    · grind [hn.2.2]
    · constructor
      · grind [horder m]
      · grind [hn.1]
  · intro eps
    obtain ⟨N, hN⟩ := hC.2.2 eps
    refine ⟨N, ?_⟩
    intro n hn
    have hwidth := hN n hn
    change (1 - (C.compute n).lo) - (1 - (C.compute n).hi) <= eps.val
    change (C.compute n).hi - (C.compute n).lo <= eps.val at hwidth
    grind

theorem oneMinusCosFunRaw_bounds
    (B : IntegralIdentities.ArctanInverseBisection)
    {x : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    0 <= ((oneMinusCosFunRaw B).compute x n).lo /\
      ((oneMinusCosFunRaw B).compute x n).hi <= 1 := by
  simp only [oneMinusCosFunRaw, dif_pos hx]
  have ht := arctanInverse_slope_bounded B x hx n
  have htarg : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x) := by
    change 0 <= 2 * x /\ 2 * x <= 1
    constructor
    · exact Rat.mul_nonneg (by native_decide) hx.1
    · have h := Rat.mul_le_mul_of_nonneg_left hx.2
        (by native_decide : (0 : Rat) <= 2)
      have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
      rw [hhalf] at h
      exact h
  have htv := B.tangentRaw_valid (2 * x) htarg
  have hto := RealRaw.interval_order_of_valid
    { compute := B.tangentRaw.compute (2 * x) htarg } htv n
  have hlo := rationalCircleCos_bounds ht.1 (by grind [ht.2])
  have hhi := rationalCircleCos_bounds (by grind [ht.1]) ht.2
  change 0 <= 1 - ((cosPiRawOfArctan B x _).compute n).hi /\
    1 - ((cosPiRawOfArctan B x _).compute n).lo <= 1
  simpa [cosPiRawOfArctan, rationalCircleCosInterval] using
    (And.intro (by grind [hhi.2]) (by grind [hlo.1]))

def primitiveRawOfArctan
    (B : IntegralIdentities.ArctanInverseBisection) : RealFunRaw :=
  RealFunRaw.mul reciprocalPiFunRaw (oneMinusCosFunRaw B)

theorem primitiveRawOfArctan_valid
    (B : IntegralIdentities.ArctanInverseBisection) :
    (primitiveRawOfArctan B).Valid := by
  apply RealFunRaw.mul_valid_of_nonneg_bounded
    reciprocalPiFunRaw_valid (oneMinusCosFunRaw_valid B)
  · intro x _
    refine ⟨1, by native_decide, ?_⟩
    intro n
    exact reciprocalPiRaw_bounds n
  · intro x hx
    refine ⟨1, by native_decide, ?_⟩
    intro n
    change 0 <= x /\ x <= (1 : Rat) / 2 at hx
    have ht := arctanInverse_slope_bounded B x hx n
    have htarg : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x) := by
      change 0 <= 2 * x /\ 2 * x <= 1
      constructor
      · exact Rat.mul_nonneg (by native_decide) hx.1
      · have h := Rat.mul_le_mul_of_nonneg_left hx.2
          (by native_decide : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
        rw [hhalf] at h
        exact h
    have htv := B.tangentRaw_valid (2 * x) htarg
    have hto := RealRaw.interval_order_of_valid
      { compute := B.tangentRaw.compute (2 * x) htarg } htv n
    have hlo := rationalCircleCos_bounds ht.1 (by grind [ht.2])
    have hhi := rationalCircleCos_bounds (by grind [ht.1]) ht.2
    simp only [oneMinusCosFunRaw, dif_pos hx]
    change 0 <= 1 - ((cosPiRawOfArctan B x _).compute n).hi /\
      1 - ((cosPiRawOfArctan B x _).compute n).lo <= 1
    simpa [cosPiRawOfArctan, rationalCircleCosInterval] using
      (And.intro (by grind [hhi.2]) (by grind [hlo.1]))

theorem primitiveRawOfArctan_bounds
    (B : IntegralIdentities.ArctanInverseBisection)
    {x : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    0 <= ((primitiveRawOfArctan B).compute x n).lo /\
      ((primitiveRawOfArctan B).compute x n).hi <= 1 := by
  have hR := reciprocalPiRaw_bounds n
  have hM := oneMinusCosFunRaw_bounds B hx n
  have hRorder := RealRaw.interval_order_of_valid reciprocalPiRaw
    reciprocalPiRaw_valid n
  have hMvalid := oneMinusCosFunRaw_valid B x hx
  have hMorder := RealRaw.interval_order_of_valid
    { compute := (oneMinusCosFunRaw B).compute x } hMvalid n
  change 0 <= (QBox.mulRealInterval
      (reciprocalPiRaw.compute n).lo (reciprocalPiRaw.compute n).hi
      ((oneMinusCosFunRaw B).compute x n).lo
      ((oneMinusCosFunRaw B).compute x n).hi).lo /\
    (QBox.mulRealInterval
      (reciprocalPiRaw.compute n).lo (reciprocalPiRaw.compute n).hi
      ((oneMinusCosFunRaw B).compute x n).lo
      ((oneMinusCosFunRaw B).compute x n).hi).hi <= 1
  rw [QBox.mulRealInterval_of_nonneg hR.1 hRorder hM.1 hMorder]
  constructor
  · exact Rat.mul_nonneg hR.1 hM.1
  · have hMhi0 : 0 <= ((oneMinusCosFunRaw B).compute x n).hi := by
      grind
    calc
      (reciprocalPiRaw.compute n).hi *
          ((oneMinusCosFunRaw B).compute x n).hi <=
          1 * ((oneMinusCosFunRaw B).compute x n).hi :=
        Rat.mul_le_mul_of_nonneg_right hR.2 hMhi0
      _ <= 1 := by simpa using hM.2

private theorem primitive_mul_zero_equiv (R : RealRaw) (hR : R.Valid)
    (hRnonneg : forall n, 0 <= (R.compute n).lo) :
    (R * RealRaw.zero).Equiv RealRaw.zero := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff (R * RealRaw.zero) RealRaw.zero n n).2
  have horder := RealRaw.interval_order_of_valid R hR n
  change QInterval.Overlaps
    (QBox.mulRealInterval (R.compute n).lo (R.compute n).hi 0 0)
    { lo := 0, hi := 0 }
  rw [QBox.mulRealInterval_of_nonneg (hRnonneg n) horder
    (by native_decide) (by native_decide)]
  simp [QInterval.Overlaps]

private theorem one_sub_one_equiv_zero (C : RealRaw) (hC : C.Valid)
    (hCeq : C.Equiv RealRaw.one) :
    (RealRaw.one - C).Equiv RealRaw.zero := by
  have hone : RealRaw.one.Valid := by
    change RealRaw.ValidCompute (fun _ : Nat => { lo := 1, hi := 1 })
    exact RealRaw.ofRat_valid 1
  have hzero : RealRaw.zero.Valid := by
    change RealRaw.ValidCompute (fun _ : Nat => { lo := 0, hi := 0 })
    exact RealRaw.ofRat_valid 0
  have hsub : (RealRaw.one - C).Valid := RealRaw.sub_valid hone hC
  have hself : (RealRaw.one - RealRaw.one).Equiv RealRaw.zero := by
    apply RealRaw.sameStageOverlap_equiv
    intro n
    apply (RealRaw.compareAt_overlap_iff
      (RealRaw.one - RealRaw.one) RealRaw.zero n n).2
    change QInterval.Overlaps
      (RealRaw.subCompute RealRaw.one RealRaw.one n)
      (RealRaw.zero.compute n)
    simp [RealRaw.subCompute, RealRaw.one, RealRaw.zero,
      RealRaw.ofRat, QInterval.Overlaps]
    constructor <;> native_decide
  exact RealRaw.equiv_trans hsub
    (RealRaw.sub_valid hone hone) hzero
    (RealRaw.sub_equiv hone hone hC hone
      (RealRaw.equiv_refl RealRaw.one hone) hCeq) hself

private theorem primitive_product_zero_equiv
    (R M : RealRaw) (hR : R.Valid) (hM : M.Valid)
    (hRb : forall n, 0 <= (R.compute n).lo /\ (R.compute n).hi <= 1)
    (hMb : forall n, 0 <= (M.compute n).lo /\ (M.compute n).hi <= 1)
    (hMzero : M.Equiv RealRaw.zero) :
    (R * M).Equiv RealRaw.zero := by
  have hzero : RealRaw.zero.Valid := by
    change RealRaw.ValidCompute (fun _ : Nat => { lo := 0, hi := 0 })
    exact RealRaw.ofRat_valid 0
  have hprod : (R * M).Equiv (R * RealRaw.zero) := by
    apply RealRaw.mul_equiv_of_nonneg hR hR hM hzero
      (fun n => (hRb n).1) (fun n => (hRb n).1)
      (fun n => (hMb n).1)
      (fun n => by change 0 <= 0; native_decide)
      (RealRaw.equiv_refl R hR) hMzero
  have hpvalid : (R * M).Valid :=
    RealRaw.mul_valid_of_nonneg_bounded hR hM
      (Bx := (1 : Rat)) (By := (1 : Rat))
      (by native_decide) (by native_decide) hRb hMb
  have hzvalid : (R * RealRaw.zero).Valid :=
    RealRaw.mul_valid_of_nonneg_bounded hR hzero
      (Bx := (1 : Rat)) (By := (1 : Rat))
      (by native_decide) (by native_decide) hRb
      (fun n => by change 0 <= 0 /\ 0 <= 1; native_decide)
  exact RealRaw.equiv_trans hpvalid hzvalid hzero hprod
    (primitive_mul_zero_equiv R hR (fun n => (hRb n).1))

/-- The left endpoint of the canonical primitive is zero once the geometric
cosine evaluator supplies its endpoint law.  This is the finite interval
algebra needed by the final FTC certificate; no completed real is involved. -/
theorem primitiveRawOfArctan_zero_equiv_of_cosine_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (hc : (cosPiRawOfArctan B 0
      ⟨by native_decide, by native_decide⟩).Equiv RealRaw.one) :
    ({ compute := (primitiveRawOfArctan B).compute 0 } : RealRaw).Equiv
      RealRaw.zero := by
  let R : RealRaw := reciprocalPiRaw
  let M : RealRaw := { compute := (oneMinusCosFunRaw B).compute 0 }
  have hR : R.Valid := by simpa [R] using reciprocalPiRaw_valid
  have hRb : forall n, 0 <= (R.compute n).lo /\ (R.compute n).hi <= 1 := by
    intro n
    simpa [R] using reciprocalPiRaw_bounds n
  have hM : M.Valid := by
    change RealRaw.ValidCompute ((oneMinusCosFunRaw B).compute 0)
    exact oneMinusCosFunRaw_valid B 0
      (by native_decide : (0 : Rat) <= 0 /\ (0 : Rat) <= 1 / 2)
  have hMb : forall n, 0 <= (M.compute n).lo /\ (M.compute n).hi <= 1 := by
    intro n
    simpa [M] using oneMinusCosFunRaw_bounds B
      (by native_decide : (0 : Rat) <= 0 /\ (0 : Rat) <= 1 / 2) n
  have hC : (cosPiRawOfArctan B 0
      ⟨by native_decide, by native_decide⟩).Valid :=
    cosPiRawOfArctan_valid B 0 ⟨by native_decide, by native_decide⟩
  have hMzero : M.Equiv RealRaw.zero := by
    apply RealRaw.sameStageOverlap_equiv
    intro n
    apply (RealRaw.compareAt_overlap_iff M RealRaw.zero n n).2
    change QInterval.Overlaps
      (if hx : (0 : Rat) <= 0 /\ (0 : Rat) <= 1 / 2 then
        { lo := 1 - ((cosPiRawOfArctan B 0 hx).compute n).hi,
          hi := 1 - ((cosPiRawOfArctan B 0 hx).compute n).lo }
       else { lo := 0, hi := 0 })
      { lo := 0, hi := 0 }
    rw [dif_pos (by native_decide : (0 : Rat) <= 0 /\ (0 : Rat) <= 1 / 2)]
    have hc_n := (RealRaw.compareAt_overlap_iff
      (cosPiRawOfArctan B 0 ⟨by native_decide, by native_decide⟩)
      RealRaw.one n n).1 (hc n)
    simp [RealRaw.one, RealRaw.ofRat] at hc_n
    change QInterval.Overlaps
      { lo := 1 - ((cosPiRawOfArctan B 0 _).compute n).hi,
        hi := 1 - ((cosPiRawOfArctan B 0 _).compute n).lo }
      { lo := 0, hi := 0 }
    unfold QInterval.Overlaps at hc_n ⊢
    constructor <;> grind
  have hprod : (R * M).Equiv RealRaw.zero :=
    primitive_product_zero_equiv R M hR hM hRb hMb hMzero
  change (R * M).Equiv RealRaw.zero
  exact hprod

private theorem primitive_half_product_equiv
    (R M : RealRaw) (hR : R.Valid) (hM : M.Valid)
    (hRb : forall n, 0 <= (R.compute n).lo /\ (R.compute n).hi <= 1)
    (hMb : forall n, 0 <= (M.compute n).lo /\ (M.compute n).hi <= 1)
    (hMone : M.Equiv RealRaw.one) :
    (R * M).Equiv R := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff (R * M) R n n).2
  have hRorder := RealRaw.interval_order_of_valid R hR n
  have hMorder := RealRaw.interval_order_of_valid M hM n
  have hm := (RealRaw.compareAt_overlap_iff M RealRaw.one n n).1 (hMone n)
  simp [RealRaw.one, RealRaw.ofRat] at hm
  change QInterval.Overlaps
    (QBox.mulRealInterval (R.compute n).lo (R.compute n).hi
      (M.compute n).lo (M.compute n).hi)
    (R.compute n)
  rw [QBox.mulRealInterval_of_nonneg (hRb n).1 hRorder
    (hMb n).1 hMorder]
  unfold QInterval.Overlaps
  constructor
  · calc
      (R.compute n).lo * (M.compute n).lo <=
          (R.compute n).lo * 1 :=
        Rat.mul_le_mul_of_nonneg_left hm.1 (hRb n).1
      _ <= (R.compute n).hi := by simpa using hRorder
  · calc
      (R.compute n).lo <= (R.compute n).hi * 1 := by simpa using hRorder
      _ <= (R.compute n).hi * (M.compute n).hi :=
        Rat.mul_le_mul_of_nonneg_left hm.2 (by grind)

/-- The right endpoint of the canonical primitive is the reciprocal-pi raw
number once the cosine evaluator supplies its quarter-turn endpoint law. -/
theorem primitiveRawOfArctan_half_equiv_of_cosine_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (hc : (cosPiRawOfArctan B (1 / 2)
      ⟨by native_decide, by native_decide⟩).Equiv RealRaw.zero) :
    ({ compute := (primitiveRawOfArctan B).compute (1 / 2) } : RealRaw).Equiv
      reciprocalPiRaw := by
  let R : RealRaw := reciprocalPiRaw
  let M : RealRaw := { compute := (oneMinusCosFunRaw B).compute (1 / 2) }
  have hR : R.Valid := by simpa [R] using reciprocalPiRaw_valid
  have hRb : forall n, 0 <= (R.compute n).lo /\ (R.compute n).hi <= 1 := by
    intro n
    simpa [R] using reciprocalPiRaw_bounds n
  have hM : M.Valid := by
    change RealRaw.ValidCompute ((oneMinusCosFunRaw B).compute (1 / 2))
    exact oneMinusCosFunRaw_valid B (1 / 2)
      (by native_decide : (0 : Rat) <= 1 / 2 /\ (1 : Rat) / 2 <= 1 / 2)
  have hMb : forall n, 0 <= (M.compute n).lo /\ (M.compute n).hi <= 1 := by
    intro n
    simpa [M] using oneMinusCosFunRaw_bounds B
      (by native_decide : (0 : Rat) <= 1 / 2 /\ (1 : Rat) / 2 <= 1 / 2) n
  have hMone : M.Equiv RealRaw.one := by
    apply RealRaw.sameStageOverlap_equiv
    intro n
    apply (RealRaw.compareAt_overlap_iff M RealRaw.one n n).2
    change QInterval.Overlaps
      (if hx : (0 : Rat) <= 1 / 2 /\ (1 : Rat) / 2 <= 1 / 2 then
        { lo := 1 - ((cosPiRawOfArctan B (1 / 2) hx).compute n).hi,
          hi := 1 - ((cosPiRawOfArctan B (1 / 2) hx).compute n).lo }
       else { lo := 0, hi := 0 })
      { lo := 1, hi := 1 }
    rw [dif_pos (by native_decide : (0 : Rat) <= 1 / 2 /\ (1 : Rat) / 2 <= 1 / 2)]
    have hc_n := (RealRaw.compareAt_overlap_iff
      (cosPiRawOfArctan B (1 / 2) ⟨by native_decide, by native_decide⟩)
      RealRaw.zero n n).1 (hc n)
    simp [RealRaw.zero, RealRaw.ofRat] at hc_n
    change QInterval.Overlaps
      { lo := 1 - ((cosPiRawOfArctan B (1 / 2) _).compute n).hi,
        hi := 1 - ((cosPiRawOfArctan B (1 / 2) _).compute n).lo }
      { lo := 1, hi := 1 }
    unfold QInterval.Overlaps at hc_n ⊢
    constructor <;> grind
  have hpvalid : (R * M).Valid :=
    RealRaw.mul_valid_of_nonneg_bounded hR hM
      (Bx := (1 : Rat)) (By := (1 : Rat))
      (by native_decide) (by native_decide) hRb hMb
  have hprod : (R * M).Equiv R :=
    primitive_half_product_equiv R M hR hM hRb hMb hMone
  change (R * M).Equiv R
  exact hprod

/-- Package the arctangent-backed evaluator as the interval function consumed
by the equal-dyadic integral operator. -/
def ArctanSinPiConstruction.onHalf
    (S : ArctanSinPiConstruction) : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
    compute := fun x hx => (sinPiRawOfArctan S.inverse x hx).compute
  }
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact S.sin_valid x hx

def ArctanSinPiConstruction.halfIntegral
    (S : ArctanSinPiConstruction)
    (c : Integral.Construction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2)) : RealRaw :=
  Integral.integral S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2) c

theorem ArctanSinPiConstruction.halfIntegral_valid
    (S : ArctanSinPiConstruction)
    (c : Integral.Construction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2)) :
    (S.halfIntegral c).Valid := by
  exact FTC.integral_valid_of_construction c

/-- Static-dyadic FTC bridge for the arctangent-backed sine evaluator.

This is the final theorem-facing assembly point: a primitive `F`, a finite
static-dyadic FTC certificate, and the endpoint schedule agreement identify
the actual equal-dyadic integral with `F(1/2)-F(0)`. -/
theorem ArctanSinPiConstruction.halfIntegral_equiv_endpoint_of_staticFTC
    (S : ArctanSinPiConstruction)
    (F : RealFunRaw)
    (h : StaticDyadicEffectiveFTC F S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (c : Integral.Construction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2))
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (endpoint : FTC.EndpointScheduleAgreement F 0 ((1 : Rat) / 2)
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC)) :
    (S.halfIntegral c).Equiv
      (endpointDifferenceRaw F 0 ((1 : Rat) / 2) endpoint.endpoint_valid) := by
  exact FTC.staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
    h c hplan endpoint

/-- The complete proof object needed to identify the half-period integral with
the expected reciprocal-pi value.  The primitive and its static-dyadic FTC
certificate are intentionally fields: they are the analytic work, while the
endpoint target and the computable value `reciprocalPiRaw` are now fixed by
the project. -/
structure HalfIntegralReciprocalPiCertificate
    (S : ArctanSinPiConstruction) where
  primitive : RealFunRaw
  ftc : StaticDyadicEffectiveFTC primitive S.onHalf.toRealFunRaw
    0 ((1 : Rat) / 2)
  integral : Integral.Construction S.onHalf.toRealFunRaw
    0 ((1 : Rat) / 2)
  integral_plan : integral.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC ftc
  endpoint : FTC.EndpointScheduleAgreement primitive 0 ((1 : Rat) / 2)
    (FTC.endpointRawOfEffectiveFTC ftc.toEffectiveFTC)
  endpoint_equiv_reciprocalPi :
    endpointDifferenceRaw primitive 0 ((1 : Rat) / 2)
      endpoint.endpoint_valid |>.Equiv reciprocalPiRaw

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi
    (S : ArctanSinPiConstruction)
    (h : HalfIntegralReciprocalPiCertificate S) :
    (S.halfIntegral h.integral).Equiv reciprocalPiRaw := by
  have hinterval :=
    S.halfIntegral_equiv_endpoint_of_staticFTC h.primitive h.ftc h.integral
      h.integral_plan h.endpoint
  have hendpointValid :
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2)
        h.endpoint.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using h.endpoint.endpoint_valid
  exact RealRaw.equiv_trans (S.halfIntegral_valid h.integral)
    hendpointValid
    reciprocalPiRaw_valid hinterval h.endpoint_equiv_reciprocalPi

/-! The theorem-facing certificate uses the primitive constructed above,
rather than allowing an unrelated primitive to be supplied.  This is the
canonical `sin (pi*x)` statement: the remaining analytic obligations are
exactly the finite FTC certificate and the endpoint computation for this
primitive. -/

def ArctanSinPiConstruction.canonicalPrimitive
    (S : ArctanSinPiConstruction) : RealFunRaw :=
  primitiveRawOfArctan S.inverse

theorem ArctanSinPiConstruction.canonicalPrimitive_valid
    (S : ArctanSinPiConstruction) :
    S.canonicalPrimitive.Valid := by
  exact primitiveRawOfArctan_valid S.inverse

theorem ArctanSinPiConstruction.canonicalPrimitive_domain_zero
    (S : ArctanSinPiConstruction) :
    S.canonicalPrimitive.domain 0 := by
  exact ⟨⟨by native_decide, by native_decide⟩,
    ⟨by native_decide, by native_decide⟩⟩

theorem ArctanSinPiConstruction.canonicalPrimitive_domain_half
    (S : ArctanSinPiConstruction) :
    S.canonicalPrimitive.domain ((1 : Rat) / 2) := by
  exact ⟨⟨by native_decide, by native_decide⟩,
    ⟨by native_decide, by native_decide⟩⟩

private theorem sub_zero_equiv (R : RealRaw) (hR : R.Valid) :
    (R - RealRaw.zero).Equiv R := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff (R - RealRaw.zero) R n n).2
  have horder := RealRaw.interval_order_of_valid R hR n
  change QInterval.Overlaps
    { lo := (R.compute n).lo - 0, hi := (R.compute n).hi - 0 }
    (R.compute n)
  simp [QInterval.Overlaps]
  constructor <;> grind

/-- Generic endpoint algebra for the computable primitive layer.  Once the
endpoint values are certified as `0` and a raw value `R`, the endpoint
difference is automatically equivalent to `R`; this theorem is independent
of the analytic proof that establishes those endpoint laws. -/
theorem endpointDifference_equiv_of_endpoint_equiv
    {F : RealFunRaw} {a b : Rat}
    (hF : F.Valid) (ha : F.domain a) (hb : F.domain b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    {R : RealRaw} (hR : R.Valid)
    (hA : (F.apply hF a ha).Equiv RealRaw.zero)
    (hB : (F.apply hF b hb).Equiv R) :
    (endpointDifferenceRaw F a b hendpoint).Equiv R := by
  let A : RealRaw := F.apply hF a ha
  let B : RealRaw := F.apply hF b hb
  have hAval : A.Valid := by
    simpa [A, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF a ha
  have hBval : B.Valid := by
    simpa [B, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF b hb
  have hzero : RealRaw.zero.Valid := by
    unfold RealRaw.zero
    exact RealRaw.ofRat_valid 0
  have hsub : (B - A).Equiv (R - RealRaw.zero) :=
    RealRaw.sub_equiv hBval hR hAval hzero hB hA
  have hsubvalid : (B - A).Valid := RealRaw.sub_valid hBval hAval
  have htargetvalid : (R - RealRaw.zero).Valid :=
    RealRaw.sub_valid hR hzero
  change (B - A).Equiv R
  exact RealRaw.equiv_trans hsubvalid htargetvalid hR hsub
    (sub_zero_equiv R hR)

/-- The canonical primitive's endpoint difference is the reciprocal-pi raw
number once the two geometric cosine endpoint laws are supplied.  This is the
last finite endpoint-algebra bridge before the dyadic FTC certificate. -/
theorem primitiveRawOfArctan_endpointDifference_equiv_of_cosine_endpoints
    (B : IntegralIdentities.ArctanInverseBisection)
    (hc0 : (cosPiRawOfArctan B 0
      ⟨by native_decide, by native_decide⟩).Equiv RealRaw.one)
    (hcHalf : (cosPiRawOfArctan B (1 / 2)
      ⟨by native_decide, by native_decide⟩).Equiv RealRaw.zero)
    (hendpoint :
      RealRaw.ValidCompute
        (endpointDifferenceCompute (primitiveRawOfArctan B)
          0 ((1 : Rat) / 2))) :
    (endpointDifferenceRaw (primitiveRawOfArctan B) 0 ((1 : Rat) / 2)
      hendpoint).Equiv reciprocalPiRaw := by
  have hF : (primitiveRawOfArctan B).Valid :=
    primitiveRawOfArctan_valid B
  have ha : (primitiveRawOfArctan B).domain 0 := by
    simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
      oneMinusCosFunRaw] <;> native_decide
  have hb : (primitiveRawOfArctan B).domain ((1 : Rat) / 2) := by
    simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
      oneMinusCosFunRaw] <;> native_decide
  have hA : ((primitiveRawOfArctan B).apply hF 0 ha).Equiv
      RealRaw.zero := by
    change ({ compute := (primitiveRawOfArctan B).compute 0 } : RealRaw).Equiv
      RealRaw.zero
    exact primitiveRawOfArctan_zero_equiv_of_cosine_endpoint B hc0
  have hB : ((primitiveRawOfArctan B).apply hF ((1 : Rat) / 2) hb).Equiv
      reciprocalPiRaw := by
    change ({ compute := (primitiveRawOfArctan B).compute ((1 : Rat) / 2) } :
      RealRaw).Equiv reciprocalPiRaw
    exact primitiveRawOfArctan_half_equiv_of_cosine_endpoint B hcHalf
  exact endpointDifference_equiv_of_endpoint_equiv
    hF ha hb hendpoint reciprocalPiRaw_valid hA hB

theorem primitiveRawOfArctan_endpointDifference_equiv_of_cosine_endpoints'
    (B : IntegralIdentities.ArctanInverseBisection)
    (hc0 : (cosPiRawOfArctan B 0
      ⟨by native_decide, by native_decide⟩).Equiv RealRaw.one)
    (hcHalf : (cosPiRawOfArctan B (1 / 2)
      ⟨by native_decide, by native_decide⟩).Equiv RealRaw.zero) :
    (endpointDifferenceRaw (primitiveRawOfArctan B) 0 ((1 : Rat) / 2)
      (endpointDifference_valid_of_fun_valid
        (primitiveRawOfArctan_valid B)
        (by
          simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
            oneMinusCosFunRaw] <;> native_decide)
        (by
          simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
            oneMinusCosFunRaw] <;> native_decide))).Equiv reciprocalPiRaw := by
  apply primitiveRawOfArctan_endpointDifference_equiv_of_cosine_endpoints
    B hc0 hcHalf

/-- Same endpoint bridge with the inverse-search endpoint laws exposed
directly.  These are the two finite inverse facts needed at normalized angles
`0` and `1`; the circle-coordinate endpoint laws are then automatic. -/
theorem primitiveRawOfArctan_endpointDifference_equiv_of_tangent_endpoints
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (ht1 : (B.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealRaw.one) :
    (endpointDifferenceRaw (primitiveRawOfArctan B) 0 ((1 : Rat) / 2)
      (endpointDifference_valid_of_fun_valid
        (primitiveRawOfArctan_valid B)
        (by
          simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
            oneMinusCosFunRaw] <;> native_decide)
        (by
          simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
            oneMinusCosFunRaw] <;> native_decide))).Equiv reciprocalPiRaw := by
  apply primitiveRawOfArctan_endpointDifference_equiv_of_cosine_endpoints'
    B
    (cosPiRawOfArctan_zero_equiv_one_of_tangent_endpoint B ht0)
    (cosPiRawOfArctan_half_equiv_zero_of_tangent_endpoint B ht1)

structure CanonicalHalfIntegralReciprocalPiCertificate
    (S : ArctanSinPiConstruction) where
  ftc : StaticDyadicEffectiveFTC
    S.canonicalPrimitive S.onHalf.toRealFunRaw
    0 ((1 : Rat) / 2)
  integral : Integral.Construction S.onHalf.toRealFunRaw
    0 ((1 : Rat) / 2)
  integral_plan : integral.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC ftc
  endpoint : FTC.EndpointScheduleAgreement
    S.canonicalPrimitive 0 ((1 : Rat) / 2)
    (FTC.endpointRawOfEffectiveFTC ftc.toEffectiveFTC)
  endpoint_equiv_reciprocalPi :
  endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
      endpoint.endpoint_valid |>.Equiv reciprocalPiRaw

/-- Assemble the canonical certificate once the finite FTC data, endpoint
schedule, and the two inverse-search endpoint laws are available. -/
def CanonicalHalfIntegralReciprocalPiCertificate.ofTangentEndpoints
    (S : ArctanSinPiConstruction)
    (ftc : StaticDyadicEffectiveFTC
      S.canonicalPrimitive S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (integral : Integral.Construction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (integral_plan : integral.plan =
      FTC.integralPlanOfStaticDyadicEffectiveFTC ftc)
    (endpoint : FTC.EndpointScheduleAgreement
      S.canonicalPrimitive 0 ((1 : Rat) / 2)
      (FTC.endpointRawOfEffectiveFTC ftc.toEffectiveFTC))
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (ht1 : (S.inverse.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealRaw.one) :
    CanonicalHalfIntegralReciprocalPiCertificate S where
  ftc := ftc
  integral := integral
  integral_plan := integral_plan
  endpoint := endpoint
  endpoint_equiv_reciprocalPi := by
    simpa [ArctanSinPiConstruction.canonicalPrimitive] using
      primitiveRawOfArctan_endpointDifference_equiv_of_tangent_endpoints
        S.inverse ht0 ht1

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_canonical
    (S : ArctanSinPiConstruction)
    (h : CanonicalHalfIntegralReciprocalPiCertificate S) :
    (S.halfIntegral h.integral).Equiv reciprocalPiRaw := by
  have hinterval :=
    S.halfIntegral_equiv_endpoint_of_staticFTC
      S.canonicalPrimitive h.ftc h.integral h.integral_plan h.endpoint
  have hendpointValid :
      (endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
        h.endpoint.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using h.endpoint.endpoint_valid
  exact RealRaw.equiv_trans
    (S.halfIntegral_valid h.integral)
    hendpointValid reciprocalPiRaw_valid hinterval
    h.endpoint_equiv_reciprocalPi

theorem rationalCircleSinInterval_formula (U : QInterval) :
    rationalCircleSinInterval U =
      { lo := rationalCircleSin U.lo, hi := rationalCircleSin U.hi } :=
  rfl

/-!
## The rational tangent-chart pullback

For the public function `sin (pi*x)` on `[0,1/2]`, write
`u = tan (pi*x/2)`.  The finite change-of-variables calculation is then

`sin (pi*x) dx = (1/pi) * (4*u/(1+u^2)^2) du`.

The following definitions deliberately contain no real-valued `pi`: the
factor `1/pi` is represented separately by `reciprocalPiRaw`.  The rational
part is suitable for the existing Lipschitz--dyadic constructor.
-/

def tangentPullbackDensity (u : Rat) : Rat :=
  4 * (u * (1 / (1 + u * u))) * (1 / (1 + u * u))

def tangentPullbackPrimitive (u : Rat) : Rat :=
  2 * (u * u) / (1 + u * u)

theorem tangentPullbackPrimitive_endpoint_difference (p r : Rat) :
    tangentPullbackPrimitive r - tangentPullbackPrimitive p =
      (r - p) *
        (2 * (r + p) *
          ((1 + p * p) * (1 + r * r))⁻¹) := by
  have hpSquare := rat_square_nonneg_basic p
  have hrSquare := rat_square_nonneg_basic r
  have hp : 0 < 1 + p * p := by grind
  have hr : 0 < 1 + r * r := by grind
  have hpne : 1 + p * p ≠ 0 := Rat.ne_of_gt hp
  have hrne : 1 + r * r ≠ 0 := Rat.ne_of_gt hr
  rw [tangentPullbackPrimitive, tangentPullbackPrimitive]
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg, Rat.inv_mul_rev,
    Rat.mul_inv_cancel _ hpne, Rat.mul_inv_cancel _ hrne]

private theorem tangentPullbackDensity_lipschitz_difference
    {s t : Rat} (hs0 : 0 <= s) (hs1 : s <= 1)
    (ht0 : 0 <= t) (ht1 : t <= 1) :
    qabs (tangentPullbackDensity s - tangentPullbackDensity t) <=
      20 * qabs (t - s) := by
  let k : Rat -> Rat := fun x => 1 / (1 + x * x)
  let p : Rat -> Rat := fun x => x * k x
  have hk := IntegralIdentities.oneOverOnePlusSquare_lipschitz_on_unit.2
    s t hs0 hs1 ht0 ht1
  have hp := IntegralIdentities.coordinate_integralKernel_lipschitz_on_unit.2
    s t hs0 hs1 ht0 ht1
  have hks0 : 0 <= k s := by
    dsimp [k]
    have hsq := rat_square_nonneg_basic s
    have hden : 0 < 1 + s * s := by grind
    simpa [Rat.div_def] using Rat.le_of_lt ((Rat.inv_pos).2 hden)
  have hkt0 : 0 <= k t := by
    dsimp [k]
    have hsq := rat_square_nonneg_basic t
    have hden : 0 < 1 + t * t := by grind
    simpa [Rat.div_def] using Rat.le_of_lt ((Rat.inv_pos).2 hden)
  have hks1 : k s <= 1 := by
    dsimp [k]
    apply Rat.le_of_mul_le_mul_right (c := 1 + s * s)
    · rw [Rat.div_def]
      have hne : 1 + s * s ≠ 0 := by
        have hsq := rat_square_nonneg_basic s
        grind
      have hcancel : (1 + s * s)⁻¹ * (1 + s * s) = 1 :=
        Rat.inv_mul_cancel _ hne
      calc
        1 * (1 + s * s)⁻¹ * (1 + s * s) = 1 := by
          simpa using hcancel
        _ <= 1 * (1 + s * s) := by
          have hsq := rat_square_nonneg_basic s
          grind
    · have hsq := rat_square_nonneg_basic s
      grind
  have hkt1 : k t <= 1 := by
    dsimp [k]
    apply Rat.le_of_mul_le_mul_right (c := 1 + t * t)
    · rw [Rat.div_def]
      have hne : 1 + t * t ≠ 0 := by
        have hsq := rat_square_nonneg_basic t
        grind
      have hcancel : (1 + t * t)⁻¹ * (1 + t * t) = 1 :=
        Rat.inv_mul_cancel _ hne
      calc
        1 * (1 + t * t)⁻¹ * (1 + t * t) = 1 := by
          simpa using hcancel
        _ <= 1 * (1 + t * t) := by
          have hsq := rat_square_nonneg_basic t
          grind
    · have hsq := rat_square_nonneg_basic t
      grind
  have hps0 : 0 <= p s := by
    dsimp [p]
    exact Rat.mul_nonneg hs0 hks0
  have hpt0 : 0 <= p t := by
    dsimp [p]
    exact Rat.mul_nonneg ht0 hkt0
  have hps1 : p s <= 1 := by
    dsimp [p]
    have := Rat.mul_le_mul_of_nonneg_left hks1 hs0
    exact Rat.le_trans this (by simpa using hs1)
  have hsplit :
      tangentPullbackDensity s - tangentPullbackDensity t =
        4 * (p s * (k s - k t) + (p s - p t) * k t) := by
    simp [tangentPullbackDensity, p, k]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]
  have hsumAbs :
      qabs (p s * (k s - k t) + (p s - p t) * k t) <=
        p s * qabs (k s - k t) + qabs (p s - p t) * k t := by
    calc
      qabs (p s * (k s - k t) + (p s - p t) * k t) <=
          qabs (p s * (k s - k t)) + qabs ((p s - p t) * k t) :=
        qabs_add_le _ _
      _ = qabs (p s) * qabs (k s - k t) +
          qabs (p s - p t) * qabs (k t) := by
        simp only [qabs_mul]
      _ = p s * qabs (k s - k t) + qabs (p s - p t) * k t := by
        have hsp : qabs (s * k s) = s * k s := by
          rw [qabs_mul, qabs_eq_self_of_nonneg hs0,
            qabs_eq_self_of_nonneg hks0]
        have hktAbs : qabs (k t) = k t :=
          qabs_eq_self_of_nonneg hkt0
        simp only [p]
        rw [hsp, hktAbs]
  have hfour : qabs (4 : Rat) = 4 := by native_decide
  have hterm1 : p s * qabs (k s - k t) <=
      p s * (2 * qabs (t - s)) := by
    exact Rat.mul_le_mul_of_nonneg_left
      (by simpa [k] using hk) hps0
  have hterm2 : qabs (p s - p t) * k t <=
      (3 * qabs (t - s)) * k t := by
    exact Rat.mul_le_mul_of_nonneg_right
      (by simpa [p, k, ArctanGeometry.integralKernel] using hp) hkt0
  have hterm1' : p s * qabs (k s - k t) <= 2 * qabs (t - s) := by
    calc
      p s * qabs (k s - k t) <=
          p s * (2 * qabs (t - s)) := hterm1
      _ <= 1 * (2 * qabs (t - s)) := by
        exact Rat.mul_le_mul_of_nonneg_right hps1
          (Rat.mul_nonneg (by native_decide) (qabs_nonneg _))
      _ = 2 * qabs (t - s) := by grind
  have hterm2' : qabs (p s - p t) * k t <= 3 * qabs (t - s) := by
    calc
      qabs (p s - p t) * k t <=
          (3 * qabs (t - s)) * k t := hterm2
      _ <= (3 * qabs (t - s)) * 1 := by
        exact Rat.mul_le_mul_of_nonneg_left hkt1
          (Rat.mul_nonneg (by native_decide) (qabs_nonneg _))
      _ = 3 * qabs (t - s) := by grind
  have hsum := rat_add_le_add hterm1' hterm2'
  calc
    qabs (tangentPullbackDensity s - tangentPullbackDensity t) =
        qabs (4 : Rat) *
          qabs (p s * (k s - k t) + (p s - p t) * k t) := by
      rw [hsplit, qabs_mul]
    _ = 4 * qabs (p s * (k s - k t) + (p s - p t) * k t) := by rw [hfour]
    _ <= 4 * (p s * qabs (k s - k t) + qabs (p s - p t) * k t) :=
      Rat.mul_le_mul_of_nonneg_left hsumAbs (by native_decide)
    _ <= 4 * (2 * qabs (t - s) + 3 * qabs (t - s)) :=
      Rat.mul_le_mul_of_nonneg_left (rat_add_le_add hterm1' hterm2')
        (by native_decide)
    _ = 20 * qabs (t - s) := by grind

theorem tangentPullbackDensity_lipschitz_on_unit :
    Integral.LipschitzOnUnit tangentPullbackDensity 20 := by
  constructor
  · native_decide
  · intro s t hs0 hs1 ht0 ht1
    exact tangentPullbackDensity_lipschitz_difference hs0 hs1 ht0 ht1

theorem tangentPullbackPrimitive_zero :
    tangentPullbackPrimitive 0 = 0 := by native_decide

theorem tangentPullbackPrimitive_one :
    tangentPullbackPrimitive 1 = 1 := by native_decide

/-- The tangent-chart density as an exact rational function on `[0,1]`. -/
def tangentPullbackDensityOnUnit : FunctionOnInterval :=
  FunctionOnInterval.exactRat tangentPullbackDensity 0 1

/-- The concrete dyadic Lipschitz integral of the rational tangent-chart
density.  Every stage is a finite rational Darboux computation; no completed
real integral is imported or used. -/
def tangentPullbackIntegral : RealRaw :=
  Integral.integralFor tangentPullbackDensityOnUnit
    (IntegralIdentities.LipschitzDyadic.construction
      tangentPullbackDensity 20 tangentPullbackDensity_lipschitz_on_unit)

theorem tangentPullbackIntegral_valid :
    tangentPullbackIntegral.Valid := by
  exact Integral.integralFor_valid tangentPullbackDensityOnUnit
    (IntegralIdentities.LipschitzDyadic.construction
      tangentPullbackDensity 20 tangentPullbackDensity_lipschitz_on_unit)

theorem tangentPullbackIntegral_compute (stage : Nat) :
    tangentPullbackIntegral.compute stage =
      IntegralIdentities.LipschitzDyadic.compute
        tangentPullbackDensity 20 stage := rfl

theorem tangentPullbackPrimitive_unit_endpoint_difference :
    tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0 = 1 := by
  rw [tangentPullbackPrimitive_one, tangentPullbackPrimitive_zero]
  native_decide

/-- `sin (pi*x)` as a function on the rational interval `[0,1/2]`. -/
def sinPiOnHalf
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) :
    FunctionOnInterval where
  raw := sinPiRawOfConstruction C hdefined
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := by
    intro x hx
    exact hx
  valid_on := by
    intro x hx
    exact sinPiRawOfConstruction_valid C hdefined x hx

/-- The equal-dyadic-subdivision integral of `sin (pi*x)` on `[0,1/2]`.

The caller supplies the usual interval-sum certificate.  This is the
computable value before any identification with a closed expression.
-/
def halfIntegral
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (c : Integral.Construction
      (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)) : RealRaw :=
  Integral.integral
    (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2) c

theorem halfIntegral_valid
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (c : Integral.Construction
      (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)) :
    (halfIntegral C hdefined c).Valid := by
  exact FTC.integral_valid_of_construction c

/--
The exact reusable conclusion of the elementary sine-integral argument.

`F` is the computable primitive (normally the represented function
`-cos(pi*x)/pi`) and `hftc` is an effective, static-dyadic FTC certificate
for its derivative, which is the `sinPiOnHalf` evaluator.  The theorem does
not invoke Mathlib's real numbers: equality is `RealRaw.Equiv`, and the
certificate is made from finite rational interval computations.

The endpoint raw is deliberately returned by the theorem.  Once the
project's reciprocal-`pi` representation is connected to the endpoint, the
same theorem immediately yields the familiar notation
`integral = 1/pi`; the scaled form `pi * integral = 1` is obtained from the
corresponding endpoint identity without changing the integral algorithm.
-/
structure HalfIntegralFTCCertificate
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) where
  primitive : RealFunRaw
  primitive_valid : primitive.Valid
  endpoint_valid :
    RealRaw.ValidCompute
      (endpointDifferenceCompute primitive 0 ((1 : Rat) / 2))
  integral : Integral.Construction
    (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)
  /-- The integral is computed by the project's fixed equal-dyadic plan. -/
  integral_plan : integral.plan = Integral.staticDyadicPlan
  ftc : DefiniteIntegralEqualsEndpointDifference
    primitive (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)
    integral endpoint_valid

theorem halfIntegral_equiv_endpoint
    {C : FunctionRawConstruction}
    {hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)}
    (h : HalfIntegralFTCCertificate C hdefined) :
    (halfIntegral C hdefined h.integral).Equiv
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2) h.endpoint_valid) :=
  h.ftc

end SinPiIntegral

end ComputableAnalysis
