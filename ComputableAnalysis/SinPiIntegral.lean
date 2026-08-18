import ComputableAnalysis.IntegralIdentities
import ComputableAnalysis.CauchyPi
import ComputableAnalysis.Calculus
import ComputableAnalysis.TrigSpecialValues

/-!
# The half-interval integral of `sin (pi * x)`

This file is the proof-facing entry point for the first nontrivial
trigonometric integral.  The project has one public sine convention:
`sin (pi * x)`.  The circle layer has an internal normalized coordinate `t`
for a quarter-turn; on the public half-period we pass `t = 2 * x`.  This is
an implementation coordinate, not a second definition of sine.  No
real-valued argument and no primitive real `pi` are used by the evaluator.

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
open RationalCircle.GeometricTrig.SpecialAngles

/-- The first nontrivial dyadic sample has its certified nested-radical value.

At `x = 1/4`, the public notation `sin (pi*x)` invokes the normalized circle
input `2*x = 1/2`.  The special-angle certificate identifies that sample with
the existing positive square-root representation of `1/2`; no value of a
completed standard real is used. -/
theorem sinPiRawOfConstruction_quarter_equiv_of_specialAngle
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (hspecial : SpecialAngleValueTargets C) :
    let hxquarter : (sinPiRawOfConstruction C hdefined).definedAt (1 / 4) := by
      exact ⟨by native_decide, by native_decide⟩
    ({ compute :=
        (sinPiRawOfConstruction C hdefined).compute
          (1 / 4) hxquarter } : RealRaw).Equiv
      sinFortyFiveValue := by
  dsimp
  rcases hspecial.sin_forty_five with ⟨ht, hvalue⟩
  have harg : (2 : Rat) * (1 / 4) = 1 / 2 := by native_decide
  change
    ({ compute := C.sinFunctionRaw.compute (2 * (1 / 4)) _ } : RealRaw).Equiv
      sinFortyFiveValue
  have hq : C.sinFunctionRaw.definedAt (2 * (1 / 4)) :=
    hdefined (1 / 4) (by native_decide) (by native_decide)
  change
    ({ compute := C.sinFunctionRaw.compute (2 * (1 / 4)) hq } : RealRaw).Equiv
      sinFortyFiveValue
  have hcompute :
      C.sinFunctionRaw.compute (2 * (1 / 4)) hq =
        C.sinFunctionRaw.compute (1 / 2) ht := by
    congr 1
  rw [hcompute]
  exact hvalue

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

theorem dyadicCell_width (a b : Rat) (path : Nat -> Bool) :
    forall n, (dyadicCell a b path n).width =
      (b - a) / (((2 ^ n : Nat) : Rat)) := by
  intro n
  induction n with
  | zero =>
      simp [dyadicCell, QInterval.width]
      rw [Rat.div_def]
      grind
  | succ n ih =>
      simp only [dyadicCell]
      split <;> simp only [QInterval.width]
      · change ((dyadicCell a b path n).lo +
          (dyadicCell a b path n).hi) / 2 -
            (dyadicCell a b path n).lo = _
        rw [show ((dyadicCell a b path n).lo +
            (dyadicCell a b path n).hi) / 2 -
              (dyadicCell a b path n).lo =
            ((dyadicCell a b path n).hi -
              (dyadicCell a b path n).lo) / 2 by
                grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]]
        have ih' : (dyadicCell a b path n).hi -
            (dyadicCell a b path n).lo =
            (b - a) / (((2 ^ n : Nat) : Rat)) := by
          simpa [QInterval.width] using ih
        rw [ih']
        rw [Rat.div_def]
        have htwo : (2 : Rat) ≠ 0 := by native_decide
        rw [show ((2 ^ (n + 1) : Nat) : Rat) =
          2 * ((2 ^ n : Nat) : Rat) by
            rw [Nat.pow_succ, Rat.natCast_mul,
              show ((2 : Nat) : Rat) = 2 by native_decide]
            exact Rat.mul_comm _ _]
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ htwo]
      · change (dyadicCell a b path n).hi -
          ((dyadicCell a b path n).lo +
            (dyadicCell a b path n).hi) / 2 = _
        rw [show (dyadicCell a b path n).hi -
            ((dyadicCell a b path n).lo +
              (dyadicCell a b path n).hi) / 2 =
            ((dyadicCell a b path n).hi -
              (dyadicCell a b path n).lo) / 2 by
                grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]]
        have ih' : (dyadicCell a b path n).hi -
            (dyadicCell a b path n).lo =
            (b - a) / (((2 ^ n : Nat) : Rat)) := by
          simpa [QInterval.width] using ih
        rw [ih']
        rw [Rat.div_def]
        have htwo : (2 : Rat) ≠ 0 := by native_decide
        rw [show ((2 ^ (n + 1) : Nat) : Rat) =
          2 * ((2 ^ n : Nat) : Rat) by
            rw [Nat.pow_succ, Rat.natCast_mul,
              show ((2 : Nat) : Rat) = 2 by native_decide]
            exact Rat.mul_comm _ _]
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ htwo]

theorem dyadicCell_step_subinterval (a b : Rat) (path : Nat -> Bool) (n : Nat)
    (hordered : (dyadicCell a b path n).lo <=
      (dyadicCell a b path n).hi) :
    subintervalOf (dyadicCell a b path (n + 1))
      (dyadicCell a b path n).lo (dyadicCell a b path n).hi := by
  simp only [dyadicCell]
  split <;> simp only [subintervalOf]
  · constructor
    · grind
    constructor <;> grind
  · constructor
    · grind
    constructor <;> grind

theorem dyadicCell_subinterval_of_source
    (a b : Rat) (path : Nat -> Bool) (hab : a <= b) :
    forall n, subintervalOf (dyadicCell a b path n) a b := by
  intro n
  induction n with
  | zero =>
      change a <= a /\ a <= b /\ b <= b
      exact ⟨Rat.le_refl, hab, Rat.le_refl⟩
  | succ n ih =>
      have hordered : (dyadicCell a b path n).lo <=
          (dyadicCell a b path n).hi := ih.2.1
      have hstep := dyadicCell_step_subinterval a b path n hordered
      constructor
      · exact Rat.le_trans ih.1 hstep.1
      constructor
      · exact hstep.2.1
      · exact Rat.le_trans hstep.2.2 ih.2.2

private theorem dyadicCell_subinterval_of_cell
    (a b : Rat) (path : Nat -> Bool) (hab : a <= b) :
    forall n m, n <= m ->
      subintervalOf (dyadicCell a b path m)
        (dyadicCell a b path n).lo (dyadicCell a b path n).hi := by
  intro n m
  induction m generalizing n with
  | zero =>
      intro hnm
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      exact ⟨Rat.le_refl, (by
        have h := dyadicCell_subinterval_of_source a b path hab 0
        exact h.2.1), Rat.le_refl⟩
  | succ m ih =>
      intro hnm
      by_cases hEq : n = m + 1
      · subst n
        exact ⟨Rat.le_refl, (by
          have h := dyadicCell_subinterval_of_source a b path hab (m + 1)
          exact h.2.1), Rat.le_refl⟩
      · have hnm' : n <= m := by omega
        have ih' := ih n hnm'
        have hordered : (dyadicCell a b path m).lo <=
            (dyadicCell a b path m).hi := by
          have h := dyadicCell_subinterval_of_source a b path hab m
          exact h.2.1
        have hstep := dyadicCell_step_subinterval a b path m hordered
        constructor
        · exact Rat.le_trans ih'.1 hstep.1
        constructor
        · exact hstep.2.1
        · exact Rat.le_trans hstep.2.2 ih'.2.2

set_option maxHeartbeats 5000000 in
theorem dyadicCell_valid_of_width_le_one
    (a b : Rat) (path : Nat -> Bool) (hab : a <= b)
    (hwidth : b - a <= 1) :
    RealRaw.ValidCompute (dyadicCell a b path) := by
  have hbound : forall n,
      (dyadicCell a b path n).width <=
        1 / (((n + 1 : Nat) : Rat)) := by
    intro n
    rw [dyadicCell_width]
    have hpow : (n + 1 : Nat) <= 2 ^ n := by
      induction n with
      | zero => omega
      | succ n ih =>
          calc
            n + 1 + 1 <= 2 * (n + 1) := by omega
            _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
            _ = 2 ^ (n + 1) := by
              rw [Nat.pow_succ]
              omega
    have hdenpos : 0 < ((n + 1 : Nat) : Rat) := by
      exact_mod_cast (Nat.succ_pos n)
    have hpowpos : 0 < ((2 ^ n : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
    have hnum : 0 <= b - a := by grind
    have hone :
        1 / ((2 ^ n : Nat) : Rat) <=
          1 / ((n + 1 : Nat) : Rat) :=
      FTC.one_div_nat_antitone
        (Nat.succ_pos n) (Nat.pow_pos (by omega : 0 < 2)) hpow
    have hone_nonneg : 0 <=
        1 / ((n + 1 : Nat) : Rat) := by
      simpa [Rat.div_def] using
        (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))
    calc
      (b - a) / ((2 ^ n : Nat) : Rat) =
          (b - a) * (1 / ((2 ^ n : Nat) : Rat)) := by
            simp [Rat.div_def]
      _ <= (b - a) * (1 / ((n + 1 : Nat) : Rat)) :=
        Rat.mul_le_mul_of_nonneg_left hone hnum
      _ <= 1 * (1 / ((n + 1 : Nat) : Rat)) :=
        Rat.mul_le_mul_of_nonneg_right hwidth hone_nonneg
      _ = 1 / ((n + 1 : Nat) : Rat) := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hs := (dyadicCell_subinterval_of_source a b path hab n).2.1
    rw [dyadicCell_width]
    exact Rat.mul_nonneg (by grind)
      (Rat.le_of_lt ((Rat.inv_pos).2
        ((Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2)))))
  · intro n m hnm
    have hcell := dyadicCell_subinterval_of_cell a b path hab n m hnm
    exact ⟨hcell.1, hcell.2.1, hcell.2.2⟩
  · apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    exact hbound n

/-- The dyadic cell selected by a known rational preimage witness. -/
def dyadicWitnessCell (a b z : Rat) : Nat -> QInterval
  | 0 => { lo := a, hi := b }
  | n + 1 =>
      let previous := dyadicWitnessCell a b z n
      let midpoint := (previous.lo + previous.hi) / 2
      if z <= midpoint then
        { lo := previous.lo, hi := midpoint }
      else
        { lo := midpoint, hi := previous.hi }

/-- The executable left/right decisions for the witness-driven bisection. -/
def dyadicWitnessPath (a b z : Rat) (n : Nat) : Bool :=
  if z <= ((dyadicWitnessCell a b z n).lo +
      (dyadicWitnessCell a b z n).hi) / 2 then true else false

private theorem dyadicMidpoint_mem {l r : Rat} (h : l <= r) :
    l <= (l + r) / 2 /\ (l + r) / 2 <= r := by
  have htwo : (2 : Rat) > 0 := by native_decide
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
    · rw [Rat.div_def]
      have hc : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by native_decide
      grind [Rat.mul_assoc, Rat.mul_comm]
    · exact htwo
  · apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
    · rw [Rat.div_def]
      have hc : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by native_decide
      grind [Rat.mul_assoc, Rat.mul_comm]
    · exact htwo

theorem dyadicCell_dyadicWitnessPath_eq (a b z : Rat) :
    forall n, dyadicCell a b (dyadicWitnessPath a b z) n =
      dyadicWitnessCell a b z n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [dyadicCell, dyadicWitnessCell, ih, dyadicWitnessPath]
      split <;> simp_all

theorem dyadicWitnessCell_source (a b z : Rat) (hab : a <= b)
    (hz : a <= z) (hz' : z <= b) :
    forall n, subintervalOf (dyadicWitnessCell a b z n) a b := by
  intro n
  induction n with
  | zero =>
      exact ⟨Rat.le_refl, hab, Rat.le_refl⟩
  | succ n ih =>
      simp only [dyadicWitnessCell]
      have hmid := dyadicMidpoint_mem ih.2.1
      split
      · constructor
        · exact ih.1
        constructor
        · exact hmid.1
        · exact Rat.le_trans hmid.2 ih.2.2
      · constructor
        · exact Rat.le_trans ih.1 hmid.1
        constructor
        · exact hmid.2
        · exact ih.2.2

theorem dyadicWitnessCell_contains (a b z : Rat) (hab : a <= b)
    (hz : a <= z) (hz' : z <= b) :
    forall n, (dyadicWitnessCell a b z n).lo <= z /\
      z <= (dyadicWitnessCell a b z n).hi := by
  intro n
  induction n with
  | zero => exact ⟨hz, hz'⟩
  | succ n ih =>
      simp only [dyadicWitnessCell]
      have hsource := dyadicWitnessCell_source a b z hab hz hz' n
      have hmid := dyadicMidpoint_mem hsource.2.1
      split
      · constructor
        · exact ih.1
        · assumption
      · constructor
        · have hnot : ¬z <=
              ((dyadicWitnessCell a b z n).lo +
                (dyadicWitnessCell a b z n).hi) / 2 := by
            assumption
          exact Rat.le_of_lt ((Rat.not_le).1 hnot)
        · change z <= (dyadicWitnessCell a b z n).hi
          exact ih.2

theorem dyadicCell_dyadicWitnessPath_contains
    (a b z : Rat) (hab : a <= b)
    (hz : a <= z) (hz' : z <= b) :
    forall n, (dyadicCell a b (dyadicWitnessPath a b z) n).lo <= z /\
      z <= (dyadicCell a b (dyadicWitnessPath a b z) n).hi := by
  intro n
  rw [dyadicCell_dyadicWitnessPath_eq]
  exact dyadicWitnessCell_contains a b z hab hz hz' n

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

/-- Build the standard interval fields of a dyadic trace once its path and
forward-image overlap proof have been supplied.  In the arctangent branch
the source is [0,1], so the width hypothesis is discharged by arithmetic;
the only remaining search-specific field is value_overlaps. -/
def DyadicInverseTrace.ofPath
    {I : InvertibleFunctionOnInterval} {y : InRangeRaw I}
    (path : Nat -> Bool)
    (hsource : I.function.lower <= I.function.upper)
    (hwidth : I.function.upper - I.function.lower <= 1)
    (value_overlaps : forall n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (dyadicCell I.function.lower I.function.upper path n)
          (dyadicCell_subinterval_of_source
            I.function.lower I.function.upper path hsource n)
          n)
        (y.value.compute n)) :
    DyadicInverseTrace I y where
  path := path
  cell_valid := dyadicCell_valid_of_width_le_one
    I.function.lower I.function.upper path hsource hwidth
  cell_in_source := dyadicCell_subinterval_of_source
    I.function.lower I.function.upper path hsource
  value_overlaps := value_overlaps

/-- Construct a complete dyadic inverse trace from a rational preimage
witness.  This is the constructive finite core used by special-angle
certificates: the witness is kept inside every cell, and interval regularity
transports its forward raw value to the target box. -/
def DyadicInverseTrace.ofRationalWitness
    {I : InvertibleFunctionOnInterval} {y : InRangeRaw I}
    (z : Rat)
    (hz : inDomainInterval I.function.lower I.function.upper z)
    (hwidth : I.function.upper - I.function.lower <= 1)
    (hvalue :
      ({ compute := I.function.compute z hz } : RealRaw).Equiv y.value) :
    DyadicInverseTrace I y := by
  apply DyadicInverseTrace.ofPath
    (dyadicWitnessPath I.function.lower I.function.upper z)
    I.source_ordered hwidth
  intro n
  let C := dyadicCell I.function.lower I.function.upper
    (dyadicWitnessPath I.function.lower I.function.upper z) n
  have hCsource := dyadicCell_subinterval_of_source
    I.function.lower I.function.upper
    (dyadicWitnessPath I.function.lower I.function.upper z)
    I.source_ordered n
  have hCcontains := dyadicCell_dyadicWitnessPath_contains
    I.function.lower I.function.upper z I.source_ordered hz.1 hz.2 n
  have houter := I.continuous.regular.contains_point_values
    C hCsource z hz n hCcontains.1 hCcontains.2
  have hzvalid : ({ compute := I.function.compute z hz } : RealRaw).Valid := by
    exact I.function.valid_on z (I.function.defined_on z hz)
  have heq := RealRaw.sameStageOverlap_of_equiv
    hzvalid y.value_valid hvalue n
  have hover := (RealRaw.compareAt_overlap_iff
    ({ compute := I.function.compute z hz } : RealRaw) y.value n n).1 heq
  change QInterval.Overlaps
    (I.continuous.regular.evalInterval C hCsource n)
    (y.value.compute n)
  unfold QInterval.ContainsInterval at houter
  unfold QInterval.Overlaps at hover ⊢
  change
    (I.function.compute z hz n).lo <= (y.value.compute n).hi /\
      (y.value.compute n).lo <= (I.function.compute z hz n).hi at hover
  change
    (I.continuous.regular.evalInterval C hCsource n).lo <=
        (I.function.compute z hz n).lo /\
      (I.function.compute z hz n).hi <=
        (I.continuous.regular.evalInterval C hCsource n).hi at houter
  constructor
  · exact Rat.le_trans houter.1 hover.1
  · exact Rat.le_trans hover.2 houter.2

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

/--
Build the inverse-search package from rational preimage witnesses.

This is the strongest fully executable shortcut currently available: for each
normalized first-quadrant target, a rational slope witness is supplied and is
then kept inside every selected dyadic cell.  The constructor does not choose
an inverse or appeal to a completed real line; the witness family is the
finite search data.  The general arctangent branch still needs a separate
construction of such witnesses (or an equivalent target-directed search).
-/
def arctanInverseBisectionOfRationalWitnesses
    (branch : InvertibleFunctionOnInterval)
    (branch_is_geometric : branch.function =
      IntegralIdentities.arctanGeomOnUnit)
    (targetAt : forall t : RationalCircle.GeometricTrig.QuarterTurn,
      RationalCircle.GeometricTrig.firstQuadrantBranch t -> InRangeRaw branch)
    (targetAt_equiv_halfQuarterTurn :
      forall t ht, (targetAt t ht).value.Equiv
        (RationalCircle.GeometricTrig.halfQuarterTurnRaw t))
    (targetWitness : forall _y : InRangeRaw branch, Rat)
    (targetWitness_in_domain : forall y : InRangeRaw branch,
      inDomainInterval branch.function.lower branch.function.upper
        (targetWitness y))
    (targetWitness_equiv : forall y : InRangeRaw branch,
      ({ compute := branch.function.compute
          (targetWitness y) (targetWitness_in_domain y) } : RealRaw).Equiv
        y.value)
    (source_width : branch.function.upper - branch.function.lower <= 1) :
    IntegralIdentities.ArctanInverseBisection := by
  apply arctanInverseBisectionOfDyadicTraces branch branch_is_geometric
    targetAt targetAt_equiv_halfQuarterTurn
  intro y
  exact DyadicInverseTrace.ofRationalWitness
    (targetWitness y)
    (targetWitness_in_domain y)
    source_width
    (targetWitness_equiv y)

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

/-- The circle-coordinate evaluator has an explicit rational modulus: on the
unit slope interval, changing the slope box by width `w` changes the sine
box by at most `2*w`. -/
theorem rationalCircleSinInterval_width_le
    {U : QInterval} (hU : subintervalOf U 0 1) :
    0 <= (rationalCircleSinInterval U).width /\
      (rationalCircleSinInterval U).width <= 2 * U.width := by
  have hsin := rationalCircleSin_width_le hU.1 hU.2.1 hU.2.2
  have hmono := rationalCircleSin_mono hU.1 hU.2.1 hU.2.2
  unfold rationalCircleSinInterval QInterval.width
  constructor
  · grind
  · exact hsin

theorem rationalCircleSin_difference_le_qabs
    {a b : Rat} (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1) :
    qabs (rationalCircleSin a - rationalCircleSin b) <=
      2 * qabs (a - b) := by
  by_cases hab : a <= b
  · have hsin := rationalCircleSin_width_le ha0 hab hb1
    have hmono := rationalCircleSin_mono ha0 hab hb1
    have hdiff : 0 <= rationalCircleSin b - rationalCircleSin a := by
      have hnon : 0 <= 2 * (b - a) := by
        exact Rat.mul_nonneg (by native_decide) (by grind)
      grind
    rw [show rationalCircleSin a - rationalCircleSin b =
        -(rationalCircleSin b - rationalCircleSin a) by
          grind [Rat.sub_eq_add_neg], qabs_neg,
      qabs_eq_self_of_nonneg hdiff]
    rw [show qabs (a - b) = b - a by
      rw [show a - b = -(b - a) by grind [Rat.sub_eq_add_neg], qabs_neg,
        qabs_eq_self_of_nonneg (by grind : 0 <= b - a)]]
    exact hsin
  · have hba : b <= a := by grind
    have hsin := rationalCircleSin_width_le hb0 hba ha1
    have hmono := rationalCircleSin_mono hb0 hba ha1
    have hdiff : 0 <= rationalCircleSin a - rationalCircleSin b := by
      have hnon : 0 <= 2 * (a - b) := by
        exact Rat.mul_nonneg (by native_decide) (by grind)
      grind
    rw [qabs_eq_self_of_nonneg hdiff]
    rw [show qabs (a - b) = a - b by
      exact qabs_eq_self_of_nonneg (by grind)]
    exact hsin

theorem rationalCircleSinInterval_near_of_near
    {U V : QInterval} (hU : subintervalOf U 0 1)
    (hV : subintervalOf V 0 1) (eps : QPos)
    (hnear : QInterval.NearAt U V eps) :
    QInterval.NearAt (rationalCircleSinInterval U)
      (rationalCircleSinInterval V)
      { val := 2 * eps.val
        property := Rat.mul_pos (by native_decide) eps.property } := by
  have hUwidth := rationalCircleSinInterval_width_le hU
  have hVwidth := rationalCircleSinInterval_width_le hV
  have hleft :
      rationalCircleSin U.lo <= rationalCircleSin V.hi + 2 * eps.val := by
    by_cases huv : U.lo <= V.hi
    · have hmono := rationalCircleSin_mono hU.1 huv hV.2.2
      grind
    · have hdiff : V.hi <= U.lo := by grind
      have hVhi0 : 0 <= V.hi := Rat.le_trans hV.1 hV.2.1
      have hUlo1 : U.lo <= 1 := Rat.le_trans hU.2.1 hU.2.2
      have hq := rationalCircleSin_difference_le_qabs
        hVhi0 hV.2.2 hU.1 hUlo1
          (a := V.hi) (b := U.lo)
      have hdelta : U.lo - V.hi <= eps.val := by grind [hnear.1]
      rw [show qabs (V.hi - U.lo) = U.lo - V.hi by
        rw [show V.hi - U.lo = -(U.lo - V.hi) by grind [Rat.sub_eq_add_neg],
          qabs_neg, qabs_eq_self_of_nonneg (by grind)]] at hq
      have hq' : qabs (rationalCircleSin U.lo -
          rationalCircleSin V.hi) <= 2 * (U.lo - V.hi) := by
        simpa [show rationalCircleSin U.lo - rationalCircleSin V.hi =
          -(rationalCircleSin V.hi - rationalCircleSin U.lo) by
            grind [Rat.sub_eq_add_neg], qabs_neg] using hq
      have hself := self_le_qabs
        (rationalCircleSin U.lo - rationalCircleSin V.hi)
      grind
  have hright :
      rationalCircleSin V.lo <= rationalCircleSin U.hi + 2 * eps.val := by
    by_cases huv : V.lo <= U.hi
    · have hmono := rationalCircleSin_mono hV.1 huv hU.2.2
      grind
    · have hdiff : U.hi <= V.lo := by grind
      have hUhi0 : 0 <= U.hi := Rat.le_trans hU.1 hU.2.1
      have hVlo1 : V.lo <= 1 := Rat.le_trans hV.2.1 hV.2.2
      have hq := rationalCircleSin_difference_le_qabs
        hUhi0 hU.2.2 hV.1 hVlo1
          (a := U.hi) (b := V.lo)
      have hdelta : V.lo - U.hi <= eps.val := by grind [hnear.2.1]
      rw [show qabs (U.hi - V.lo) = V.lo - U.hi by
        rw [show U.hi - V.lo = -(V.lo - U.hi) by grind [Rat.sub_eq_add_neg],
          qabs_neg, qabs_eq_self_of_nonneg (by grind)]] at hq
      have hq' : qabs (rationalCircleSin V.lo -
          rationalCircleSin U.hi) <= 2 * (V.lo - U.hi) := by
        simpa [show rationalCircleSin V.lo - rationalCircleSin U.hi =
          -(rationalCircleSin U.hi - rationalCircleSin V.lo) by
            grind [Rat.sub_eq_add_neg], qabs_neg] using hq
      have hself := self_le_qabs
        (rationalCircleSin V.lo - rationalCircleSin U.hi)
      grind
  unfold QInterval.NearAt rationalCircleSinInterval
  dsimp
  change rationalCircleSin U.lo <=
      rationalCircleSin V.hi + 2 * eps.val /\
    rationalCircleSin V.lo <=
      rationalCircleSin U.hi + 2 * eps.val /\
    rationalCircleSin U.hi - rationalCircleSin U.lo <= 2 * eps.val /\
    rationalCircleSin V.hi - rationalCircleSin V.lo <= 2 * eps.val
  constructor
  · exact hleft
  constructor
  · exact hright
  constructor
  · have hwidth := hUwidth.2
    have hsmall := hnear.2.2.1
    have hwidth' : rationalCircleSin U.hi - rationalCircleSin U.lo <=
        2 * U.width := by
      simpa [rationalCircleSinInterval, QInterval.width] using hwidth
    grind
  · have hwidth := hVwidth.2
    have hsmall := hnear.2.2.2
    have hwidth' : rationalCircleSin V.hi - rationalCircleSin V.lo <=
        2 * V.width := by
      simpa [rationalCircleSinInterval, QInterval.width] using hwidth
    grind

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

theorem rationalCircleCosInterval_width_le
    {U : QInterval} (hU : subintervalOf U 0 1) :
    0 <= (rationalCircleCosInterval U).width /\
      (rationalCircleCosInterval U).width <= 4 * U.width := by
  have hcos := rationalCircleCos_width_le hU.1 hU.2.1 hU.2.2
  have hmono := rationalCircleCos_mono hU.1 hU.2.1 hU.2.2
  unfold rationalCircleCosInterval QInterval.width
  constructor
  · grind
  · simpa using hcos

theorem rationalCircleCos_difference_le_qabs
    {a b : Rat} (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1) :
    qabs (rationalCircleCos a - rationalCircleCos b) <=
      4 * qabs (a - b) := by
  by_cases hab : a <= b
  · have hcos := rationalCircleCos_width_le ha0 hab hb1
    have hmono := rationalCircleCos_mono ha0 hab hb1
    have hdiff : 0 <= rationalCircleCos a - rationalCircleCos b := by
      grind
    rw [qabs_eq_self_of_nonneg hdiff]
    rw [show qabs (a - b) = b - a by
      rw [show a - b = -(b - a) by grind [Rat.sub_eq_add_neg], qabs_neg,
        qabs_eq_self_of_nonneg (by grind : 0 <= b - a)]]
    exact hcos
  · have hba : b <= a := by grind
    have hcos := rationalCircleCos_width_le hb0 hba ha1
    have hmono := rationalCircleCos_mono hb0 hba ha1
    have hdiff : 0 <= rationalCircleCos b - rationalCircleCos a := by
      grind
    rw [show rationalCircleCos a - rationalCircleCos b =
        -(rationalCircleCos b - rationalCircleCos a) by
          grind [Rat.sub_eq_add_neg], qabs_neg,
      qabs_eq_self_of_nonneg hdiff]
    rw [show qabs (a - b) = a - b by
      exact qabs_eq_self_of_nonneg (by grind)]
    exact hcos

theorem rationalCircleCosInterval_near_of_near
    {U V : QInterval} (hU : subintervalOf U 0 1)
    (hV : subintervalOf V 0 1) (eps : QPos)
    (hnear : QInterval.NearAt U V eps) :
    QInterval.NearAt (rationalCircleCosInterval U)
      (rationalCircleCosInterval V)
      { val := 4 * eps.val
        property := Rat.mul_pos (by native_decide)
          (eps.property) } := by
  have hUwidth := rationalCircleCosInterval_width_le hU
  have hVwidth := rationalCircleCosInterval_width_le hV
  have hleft :
      rationalCircleCos U.hi <= rationalCircleCos V.lo + 4 * eps.val := by
    by_cases huv : V.lo <= U.hi
    · have hmono := rationalCircleCos_mono hV.1 huv hU.2.2
      grind
    · have hdiff : U.hi <= V.lo := by grind
      have hUhi0 : 0 <= U.hi := Rat.le_trans hU.1 hU.2.1
      have hVlo1 : V.lo <= 1 := Rat.le_trans hV.2.1 hV.2.2
      have hq := rationalCircleCos_difference_le_qabs
        hUhi0 hU.2.2 hV.1 hVlo1
          (a := U.hi) (b := V.lo)
      have hdelta : V.lo - U.hi <= eps.val := by grind [hnear.2.1]
      rw [show qabs (U.hi - V.lo) = V.lo - U.hi by
        rw [show U.hi - V.lo = -(V.lo - U.hi) by grind [Rat.sub_eq_add_neg],
          qabs_neg, qabs_eq_self_of_nonneg (by grind)]] at hq
      have hself := self_le_qabs
        (rationalCircleCos U.hi - rationalCircleCos V.lo)
      grind
  have hright :
      rationalCircleCos V.hi <= rationalCircleCos U.lo + 4 * eps.val := by
    by_cases huv : U.lo <= V.hi
    · have hmono := rationalCircleCos_mono hU.1 huv hV.2.2
      grind
    · have hdiff : V.hi <= U.lo := by grind
      have hVhi0 : 0 <= V.hi := Rat.le_trans hV.1 hV.2.1
      have hUlo1 : U.lo <= 1 := Rat.le_trans hU.2.1 hU.2.2
      have hq := rationalCircleCos_difference_le_qabs
        hVhi0 hV.2.2 hU.1 hUlo1
          (a := V.hi) (b := U.lo)
      have hdelta : U.lo - V.hi <= eps.val := by grind [hnear.1]
      rw [show qabs (V.hi - U.lo) = U.lo - V.hi by
        rw [show V.hi - U.lo = -(U.lo - V.hi) by grind [Rat.sub_eq_add_neg],
          qabs_neg, qabs_eq_self_of_nonneg (by grind)]] at hq
      have hself := self_le_qabs
        (rationalCircleCos V.hi - rationalCircleCos U.lo)
      grind
  unfold QInterval.NearAt rationalCircleCosInterval
  dsimp
  change rationalCircleCos U.hi <=
      rationalCircleCos V.lo + 4 * eps.val /\
    rationalCircleCos V.hi <=
      rationalCircleCos U.lo + 4 * eps.val /\
    rationalCircleCos U.lo - rationalCircleCos U.hi <= 4 * eps.val /\
    rationalCircleCos V.lo - rationalCircleCos V.hi <= 4 * eps.val
  constructor
  · exact hleft
  constructor
  · exact hright
  constructor
  · have hwidth := hUwidth.2
    have hsmall := hnear.2.2.1
    have hwidth' : rationalCircleCos U.lo - rationalCircleCos U.hi <=
        4 * U.width := by
      simpa [rationalCircleCosInterval, QInterval.width] using hwidth
    grind
  · have hwidth := hVwidth.2
    have hsmall := hnear.2.2.2
    have hwidth' : rationalCircleCos V.lo - rationalCircleCos V.hi <=
        4 * V.width := by
      simpa [rationalCircleCosInterval, QInterval.width] using hwidth
    grind

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

theorem cosPiRawOfArctan_near_of_tangent_near
    (B : IntegralIdentities.ArctanInverseBisection)
    {x y : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2)
    (hy : 0 <= y /\ y <= (1 : Rat) / 2)
    (htx : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x))
    (hty : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * y))
    (n : Nat) (eps : QPos)
    (hnear : QInterval.NearAt
      ((IntegralIdentities.tangentOnUnit B).compute (2 * x) htx n)
      ((IntegralIdentities.tangentOnUnit B).compute (2 * y) hty n)
      eps) :
    QInterval.NearAt
      ((cosPiRawOfArctan B x hx).compute n)
      ((cosPiRawOfArctan B y hy).compute n)
      { val := 4 * eps.val
        property := Rat.mul_pos (by native_decide)
          eps.property } := by
  have hUx : subintervalOf
      ((IntegralIdentities.tangentOnUnit B).compute (2 * x) htx n) 0 1 :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      B (2 * x) htx n
  have hUy : subintervalOf
      ((IntegralIdentities.tangentOnUnit B).compute (2 * y) hty n) 0 1 :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      B (2 * y) hty n
  change QInterval.NearAt
    (rationalCircleCosInterval
      ((IntegralIdentities.tangentOnUnit B).compute (2 * x) htx n))
    (rationalCircleCosInterval
      ((IntegralIdentities.tangentOnUnit B).compute (2 * y) hty n)) _
  exact rationalCircleCosInterval_near_of_near hUx hUy
    eps hnear

theorem oneMinusCosFunRaw_near_of_tangent_near
    (B : IntegralIdentities.ArctanInverseBisection)
    {x y : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2)
    (hy : 0 <= y /\ y <= (1 : Rat) / 2)
    (htx : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x))
    (hty : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * y))
    (n : Nat) (eps : QPos)
    (hnear : QInterval.NearAt
      ((IntegralIdentities.tangentOnUnit B).compute (2 * x) htx n)
      ((IntegralIdentities.tangentOnUnit B).compute (2 * y) hty n)
      eps) :
    QInterval.NearAt
      ((oneMinusCosFunRaw B).compute x n)
      ((oneMinusCosFunRaw B).compute y n)
      { val := 4 * eps.val
        property := Rat.mul_pos (by native_decide)
          eps.property } := by
  have hcos := cosPiRawOfArctan_near_of_tangent_near
    B hx hy htx hty n eps hnear
  simp only [oneMinusCosFunRaw, dif_pos hx, dif_pos hy]
  change QInterval.NearAt
    { lo := 1 - ((cosPiRawOfArctan B x hx).compute n).hi
      hi := 1 - ((cosPiRawOfArctan B x hx).compute n).lo }
    { lo := 1 - ((cosPiRawOfArctan B y hy).compute n).hi
      hi := 1 - ((cosPiRawOfArctan B y hy).compute n).lo } _
  unfold QInterval.NearAt QInterval.width at hcos ⊢
  rcases hcos with ⟨hxy, hyx, hwidthx, hwidthy⟩
  constructor
  · grind
  constructor
  · grind
  constructor <;> grind

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

def oneMinusCosOnHalf
    (B : IntegralIdentities.ArctanInverseBisection) : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
    compute := fun x _hx => (oneMinusCosFunRaw B).compute x
  }
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := by
    intro _ hx
    exact hx
  valid_on := by
    intro x hx
    exact oneMinusCosFunRaw_valid B x hx

theorem oneMinusCosOnHalf_valid
    (B : IntegralIdentities.ArctanInverseBisection) :
  (oneMinusCosOnHalf B).raw.Valid := by
  intro x hx
  change RealRaw.ValidCompute ((oneMinusCosFunRaw B).compute x)
  exact oneMinusCosFunRaw_valid B x hx

set_option maxHeartbeats 1000000 in
def oneMinusCosOnHalf_effectiveModulus
    (B : IntegralIdentities.ArctanInverseBisection)
    (tangentModulus : EffectiveModulusFor
      (IntegralIdentities.tangentOnUnit B)) :
    EffectiveModulusFor (oneMinusCosOnHalf B) where
  inputPrecision := fun n =>
    2 * tangentModulus.inputPrecision (4 * (n + 1))
  evalPrecision := fun n =>
    tangentModulus.evalPrecision (4 * (n + 1))
  close := by
    intro x y n hx hy hclose
    change 0 <= x /\ x <= (1 : Rat) / 2 at hx
    change 0 <= y /\ y <= (1 : Rat) / 2 at hy
    let m := 4 * (n + 1)
    have hscale :
        4 * (precisionAtStage m).val <= (precisionAtStage n).val := by
      cases n with
      | zero => native_decide
      | succ n =>
          have hrec := one_div_antitone_pos_local
            (a := ((n + 1 : Nat) : Rat))
            (b := ((n + 2 : Nat) : Rat))
            ((Rat.natCast_pos).2 (Nat.succ_pos n))
            (Rat.natCast_le_natCast.2 (by omega))
          have heq :
              4 * (1 / (((4 * (n + 2) : Nat) : Rat))) =
                1 / (((n + 2 : Nat) : Rat)) := by
            rw [Rat.natCast_mul, Rat.div_def, Rat.div_def]
            have hn : ((n + 2 : Nat) : Rat) ≠ 0 :=
              Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega))
            grind [Rat.mul_assoc, Rat.mul_comm,
              Rat.mul_inv_cancel _ hn]
          dsimp [m, precisionAtStage]
          rw [heq]
          exact hrec
    have hx' : 0 <= 2 * x /\ 2 * x <= 1 := by
      constructor
      · exact Rat.mul_nonneg (by native_decide) hx.1
      · have h := Rat.mul_le_mul_of_nonneg_left hx.2
          (by native_decide : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
        simpa [oneMinusCosOnHalf, hhalf] using h
    have hy' : 0 <= 2 * y /\ 2 * y <= 1 := by
      constructor
      · exact Rat.mul_nonneg (by native_decide) hy.1
      · have h := Rat.mul_le_mul_of_nonneg_left hy.2
          (by native_decide : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
        simpa [oneMinusCosOnHalf, hhalf] using h
    have hinput : qabs (2 * y - 2 * x) <=
        1 / ((tangentModulus.inputPrecision m : Nat) : Rat) := by
      have hmul := Rat.mul_le_mul_of_nonneg_left hclose
        (by native_decide : (0 : Rat) <= 2)
      rw [show 2 * y - 2 * x = 2 * (y - x) by grind, qabs_mul]
      have htwo : qabs (2 : Rat) = 2 := by native_decide
      rw [htwo]
      have hmul' : 2 * qabs (y - x) <=
          2 * (1 / ((2 * tangentModulus.inputPrecision m : Nat) : Rat)) := by
        simpa [m, Rat.natCast_mul, Rat.mul_comm] using hmul
      calc
        2 * qabs (y - x) <=
            2 * (1 / ((2 * tangentModulus.inputPrecision m : Nat) : Rat)) := hmul'
        _ = 1 / ((tangentModulus.inputPrecision m : Nat) : Rat) := by
          rw [Rat.natCast_mul, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel]
    have htangent := tangentModulus.close
      (2 * x) (2 * y) m hx' hy' hinput
    have honeMinus := oneMinusCosFunRaw_near_of_tangent_near
      B hx hy
      (by exact hx') (by exact hy')
      (tangentModulus.evalPrecision m) (precisionAtStage m) htangent
    change QInterval.NearAt
      ((oneMinusCosOnHalf B).compute x hx (tangentModulus.evalPrecision m))
      ((oneMinusCosOnHalf B).compute y hy (tangentModulus.evalPrecision m))
      (precisionAtStage n)
    change QInterval.NearAt
      ((oneMinusCosFunRaw B).compute x (tangentModulus.evalPrecision m))
      ((oneMinusCosFunRaw B).compute y (tangentModulus.evalPrecision m))
      (precisionAtStage n)
    change QInterval.NearAt
      ((oneMinusCosFunRaw B).compute x (tangentModulus.evalPrecision m))
      ((oneMinusCosFunRaw B).compute y (tangentModulus.evalPrecision m))
      (precisionAtStage n)
    unfold QInterval.NearAt QInterval.width at honeMinus ⊢
    rcases honeMinus with ⟨hxy, hyx, hwidthx, hwidthy⟩
    constructor <;> grind

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

/-- The endpoint-form computable integral for the canonical sine primitive.
This is the exact value supplied by the finite FTC route; unlike a classical
real integral, it is an explicit `RealRaw` endpoint computation. -/
def canonicalSineEndpointIntegral
    (S : ArctanSinPiConstruction) : RealRaw :=
  endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
    (endpointDifference_valid_of_fun_valid
      S.canonicalPrimitive_valid
      S.canonicalPrimitive_domain_zero
      S.canonicalPrimitive_domain_half)

theorem canonicalSineEndpointIntegral_valid
    (S : ArctanSinPiConstruction) :
    (canonicalSineEndpointIntegral S).Valid := by
  exact endpointDifference_valid_of_fun_valid
    S.canonicalPrimitive_valid
    S.canonicalPrimitive_domain_zero
    S.canonicalPrimitive_domain_half

theorem canonicalSineEndpointIntegral_equiv_reciprocalPi
    (S : ArctanSinPiConstruction)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (ht1 : (S.inverse.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealRaw.one) :
    (canonicalSineEndpointIntegral S).Equiv reciprocalPiRaw := by
  simpa [canonicalSineEndpointIntegral,
    ArctanSinPiConstruction.canonicalPrimitive] using
    primitiveRawOfArctan_endpointDifference_equiv_of_tangent_endpoints
      S.inverse ht0 ht1

theorem ArctanSinPiConstruction.halfIntegral_equiv_canonicalSineEndpointIntegral
    (S : ArctanSinPiConstruction)
    (h : StaticDyadicEffectiveFTC S.canonicalPrimitive
      S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2))
    (c : Integral.Construction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (endpoint : FTC.EndpointScheduleAgreement S.canonicalPrimitive
      0 ((1 : Rat) / 2)
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC)) :
    (S.halfIntegral c).Equiv (canonicalSineEndpointIntegral S) := by
  have hinterval :=
    S.halfIntegral_equiv_endpoint_of_staticFTC
      S.canonicalPrimitive h c hplan endpoint
  simpa [canonicalSineEndpointIntegral, endpointDifferenceRaw] using hinterval

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

private theorem tangentPullback_secant_polynomial (p r : Rat) :
    2 * (r + p) * (1 + p * p) -
        4 * p * (1 + r * r) =
      2 * (r - p) * (1 - p * p - 2 * p * r) := by
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

/-! The local secant identity is the finite FTC calculation used by the
dyadic proof.  It compares the secant slope of the primitive with the
pullback density at the left endpoint; no limiting real number is involved. -/

theorem tangentPullbackPrimitive_secant_identity
    {p r : Rat} (hpr : p < r) :
    (tangentPullbackPrimitive r - tangentPullbackPrimitive p) / (r - p) -
        tangentPullbackDensity p =
      2 * (r - p) * (1 - p * p - 2 * p * r) /
        ((1 + p * p) * (1 + p * p) * (1 + r * r)) := by
  have hpSquare := rat_square_nonneg_basic p
  have hrSquare := rat_square_nonneg_basic r
  have hp : 0 < 1 + p * p := by grind
  have hr : 0 < 1 + r * r := by grind
  have hwidth : 0 < r - p := by grind
  have hpne : 1 + p * p ≠ 0 := Rat.ne_of_gt hp
  have hrne : 1 + r * r ≠ 0 := Rat.ne_of_gt hr
  rw [tangentPullbackPrimitive_endpoint_difference]
  rw [tangentPullbackDensity]
  let A : Rat := 1 + p * p
  let B : Rat := 1 + r * r
  let W : Rat := r - p
  have hprod : 0 < W * (A * A * B) := by
    dsimp [W, A, B]
    exact Rat.mul_pos hwidth (Rat.mul_pos (Rat.mul_pos hp hp) hr)
  apply rat_eq_of_mul_eq_mul_pos_local (c := W * (A * A * B)) hprod
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hwidthne : r - p ≠ 0 := Rat.ne_of_gt hwidth
  have hAne : A ≠ 0 := by dsimp [A]; exact hpne
  have hBne : B ≠ 0 := by dsimp [B]; exact hrne
  have hWne : W ≠ 0 := by dsimp [W]; exact hwidthne
  have hA_cancel : A⁻¹ * A = 1 := Rat.inv_mul_cancel A hAne
  have hB_cancel : B⁻¹ * B = 1 := Rat.inv_mul_cancel B hBne
  have hW_cancel : W⁻¹ * W = 1 := Rat.inv_mul_cancel W hWne
  have hAB_cancel : (A * B)⁻¹ * (A * A * B) = A := by
    rw [Rat.inv_mul_rev]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_rev]
  have hA2_cancel : A⁻¹ * A⁻¹ * (A * A * B) = B := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hD_cancel : (A * A * B)⁻¹ * (A * A * B) = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hp hp) hr))
  change
    ((W * (2 * (r + p) * (A * B)⁻¹) * W⁻¹ -
      4 * (p * (1 * A⁻¹)) * (1 * A⁻¹)) * (W * (A * A * B))) =
      (2 * W * (1 - p * p - 2 * p * r) * (A * A * B)⁻¹) *
        (W * (A * A * B))
  have hterm1 :
      (W * (2 * (r + p) * (A * B)⁻¹) * W⁻¹) *
          (W * (A * A * B)) = W * (2 * (r + p) * A) := by
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]
  have hterm2 :
      (4 * (p * (1 * A⁻¹)) * (1 * A⁻¹)) *
          (W * (A * A * B)) = 4 * p * W * B := by
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]
  have hpoly :
      2 * (r + p) * A - 4 * p * B =
        2 * W * (1 - p * p - 2 * p * r) := by
    simpa [A, B, W] using tangentPullback_secant_polynomial p r
  calc
    (W * (2 * (r + p) * (A * B)⁻¹) * W⁻¹ -
        4 * (p * (1 * A⁻¹)) * (1 * A⁻¹)) * (W * (A * A * B)) =
      W * (2 * (r + p) * A - 4 * p * B) := by
        calc
          _ = (W * (2 * (r + p) * (A * B)⁻¹) * W⁻¹) *
                (W * (A * A * B)) -
              (4 * (p * (1 * A⁻¹)) * (1 * A⁻¹)) *
                (W * (A * A * B)) := by
                  grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add,
                    Rat.mul_assoc, Rat.mul_comm]
          _ = W * (2 * (r + p) * A) - 4 * p * W * B := by
            rw [hterm1, hterm2]
          _ = W * (2 * (r + p) * A - 4 * p * B) := by
            grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add,
              Rat.mul_assoc, Rat.mul_comm]
    _ = 2 * W * W * (1 - p * p - 2 * p * r) := by
      rw [hpoly]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (2 * W * (1 - p * p - 2 * p * r) * (A * A * B)⁻¹) *
        (W * (A * A * B)) := by
      calc
        2 * W * W * (1 - p * p - 2 * p * r) =
            2 * W * (1 - p * p - 2 * p * r) *
              (W * ((A * A * B)⁻¹ * (A * A * B))) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
        _ = 2 * W * (1 - p * p - 2 * p * r) *
              (W * (A * A * B)⁻¹ * (A * A * B)) := by
                rw [hD_cancel]
                grind [Rat.mul_assoc, Rat.mul_comm]
        _ = (2 * W * (1 - p * p - 2 * p * r) * (A * A * B)⁻¹) *
              (W * (A * A * B)) := by
                grind [Rat.mul_assoc, Rat.mul_comm]

theorem tangentPullbackPrimitive_secant_error_le
    {p r : Rat} (hp0 : 0 <= p) (hpr : p < r) (hr1 : r <= 1) :
    qabs ((tangentPullbackPrimitive r - tangentPullbackPrimitive p) /
      (r - p) - tangentPullbackDensity p) <= 4 * qabs (r - p) := by
  have hp1 : p <= 1 := Rat.le_trans (Rat.le_of_lt hpr) hr1
  have hp2nonneg : 0 <= p * p := rat_square_nonneg_basic p
  have hr0 : 0 <= r := Rat.le_trans hp0 (Rat.le_of_lt hpr)
  have hr2nonneg : 0 <= r * r := rat_square_nonneg_basic r
  have hp2le : p * p <= 1 := by
    calc
      p * p <= p * 1 := Rat.mul_le_mul_of_nonneg_left hp1 hp0
      _ = p := by grind
      _ <= 1 := hp1
  have hprle : p * r <= 1 := by
    calc
      p * r <= 1 * r := Rat.mul_le_mul_of_nonneg_right hp1 hr0
      _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hr1 (by native_decide)
      _ = 1 := by native_decide
  have hKlo : -2 <= 1 - p * p - 2 * p * r := by grind
  have hprnonneg : 0 <= p * r := Rat.mul_nonneg hp0 hr0
  have hKhi : 1 - p * p - 2 * p * r <= 2 := by grind
  have hKabs : qabs (1 - p * p - 2 * p * r) <= 2 :=
    qabs_le_of_neg_le_le hKlo hKhi
  let A : Rat := 1 + p * p
  let B : Rat := 1 + r * r
  let D : Rat := A * A * B
  have hAone : 1 <= A := by dsimp [A]; grind
  have hBone : 1 <= B := by dsimp [B]; grind
  have hDpos : 0 < D := by
    exact Rat.mul_pos (Rat.mul_pos (by grind) (by grind)) (by grind)
  have hDone : 1 <= D := by
    have hAA : 1 <= A * A := by
      calc
        1 = (1 : Rat) * 1 := by native_decide
        _ <= A * 1 := Rat.mul_le_mul_of_nonneg_right hAone (by native_decide)
        _ <= A * A := Rat.mul_le_mul_of_nonneg_left hAone (by grind)
    calc
      1 = (1 : Rat) * 1 := by native_decide
      _ <= (A * A) * 1 := Rat.mul_le_mul_of_nonneg_right hAA (by native_decide)
      _ <= (A * A) * B := Rat.mul_le_mul_of_nonneg_left hBone (by grind)
      _ = D := rfl
  have hDne : D ≠ 0 := Rat.ne_of_gt hDpos
  have hDinv0 : 0 <= D⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hDpos)
  have hDinvle : D⁻¹ <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := D)
    · rw [Rat.inv_mul_cancel _ hDne]
      grind
    · exact hDpos
  have hqabsW : qabs (r - p) = r - p := by
    exact qabs_eq_self_of_nonneg (by grind)
  have hqabsDinv : qabs D⁻¹ = D⁻¹ :=
    qabs_eq_self_of_nonneg hDinv0
  have hDdef : D = (1 + p * p) * (1 + p * p) * (1 + r * r) := by
    rfl
  rw [tangentPullbackPrimitive_secant_identity hpr]
  rw [← hDdef, Rat.div_def, qabs_mul, qabs_mul, qabs_mul]
  rw [hqabsW, hqabsDinv]
  have hqabsTwo : qabs (2 : Rat) = 2 := by native_decide
  rw [hqabsTwo]
  calc
      2 * (r - p) * qabs (1 - p * p - 2 * p * r) * D⁻¹ <=
          2 * (r - p) * 2 * D⁻¹ := by
            exact Rat.mul_le_mul_of_nonneg_right
              (Rat.mul_le_mul_of_nonneg_left hKabs
                (Rat.mul_nonneg (by native_decide) (by grind))) hDinv0
      _ <= 2 * (r - p) * 2 * 1 := by
        exact Rat.mul_le_mul_of_nonneg_left hDinvle
          (Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) (by grind))
            (by native_decide))
      _ = 4 * (r - p) := by grind

theorem tangentPullback_rectangle_error_le
    {p r : Rat} (hp0 : 0 <= p) (hpr : p < r) (hr1 : r <= 1) :
    qabs ((r - p) * tangentPullbackDensity p -
      (tangentPullbackPrimitive r - tangentPullbackPrimitive p)) <=
        4 * ((r - p) * (r - p)) := by
  have hwidth : 0 < r - p := by grind
  have hwidthne : r - p ≠ 0 := Rat.ne_of_gt hwidth
  have hsec := tangentPullbackPrimitive_secant_error_le hp0 hpr hr1
  have hrewrite :
      (r - p) * tangentPullbackDensity p -
          (tangentPullbackPrimitive r - tangentPullbackPrimitive p) =
        -((r - p) *
          ((tangentPullbackPrimitive r - tangentPullbackPrimitive p) /
            (r - p) - tangentPullbackDensity p)) := by
    rw [Rat.div_def]
    have hcancel : (r - p)⁻¹ * (r - p) = 1 :=
      Rat.inv_mul_cancel _ hwidthne
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]
  rw [hrewrite, qabs_neg, qabs_mul]
  rw [qabs_eq_self_of_nonneg (by grind : 0 <= r - p)]
  calc
    (r - p) * qabs
        ((tangentPullbackPrimitive r - tangentPullbackPrimitive p) /
          (r - p) - tangentPullbackDensity p) <=
        (r - p) * (4 * qabs (r - p)) :=
      Rat.mul_le_mul_of_nonneg_left hsec (by grind)
    _ = 4 * ((r - p) * (r - p)) := by
      rw [qabs_eq_self_of_nonneg (by grind : 0 <= r - p)]
      grind

/-! A prefix form of the finite dyadic telescope.  This keeps the exact
rectangle computation and the primitive endpoint difference in the same
rational expression; the eventual sum estimate can therefore be proved by
induction on the finite mesh rather than by invoking a completed integral. -/

def tangentPullbackRectangleError (p r : Rat) : Rat :=
  (r - p) * tangentPullbackDensity p -
    (tangentPullbackPrimitive r - tangentPullbackPrimitive p)

def tangentPullbackRectangleErrorPrefix (mesh : Nat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      tangentPullbackRectangleErrorPrefix mesh terms +
        tangentPullbackRectangleError
          ((terms : Rat) / (mesh : Rat))
          (((Nat.succ terms : Nat) : Rat) / (mesh : Rat))

theorem tangentPullbackRectangleErrorPrefix_telescope
    {mesh : Nat} (hmesh : 0 < mesh) :
    forall terms,
      IntegralIdentities.LipschitzDyadic.uniformLeftPrefixSum
          tangentPullbackDensity mesh terms -
          (tangentPullbackPrimitive ((terms : Nat) / (mesh : Rat)) -
            tangentPullbackPrimitive 0) =
        tangentPullbackRectangleErrorPrefix mesh terms
  | 0 => by
      have hzero : (0 : Rat) / (mesh : Rat) = 0 := by
        rw [Rat.div_def]
        grind
      change 0 - (tangentPullbackPrimitive ((0 : Rat) / (mesh : Rat)) -
        tangentPullbackPrimitive 0) = 0
      rw [hzero]
      grind
  | terms + 1 => by
      have hmeshRat : (mesh : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 hmesh)
      rw [IntegralIdentities.LipschitzDyadic.uniformLeftPrefixSum,
        tangentPullbackRectangleErrorPrefix]
      have hsplit :
          (IntegralIdentities.LipschitzDyadic.uniformLeftPrefixSum
              tangentPullbackDensity mesh terms +
            (1 / (mesh : Rat)) *
              tangentPullbackDensity ((terms : Rat) / (mesh : Rat)) -
            (tangentPullbackPrimitive ((terms + 1 : Nat) / (mesh : Rat)) -
              tangentPullbackPrimitive 0)) =
          (IntegralIdentities.LipschitzDyadic.uniformLeftPrefixSum
              tangentPullbackDensity mesh terms -
            (tangentPullbackPrimitive ((terms : Rat) / (mesh : Rat)) -
              tangentPullbackPrimitive 0)) +
          ((1 / (mesh : Rat)) *
              tangentPullbackDensity ((terms : Rat) / (mesh : Rat)) -
            (tangentPullbackPrimitive ((terms + 1 : Nat) / (mesh : Rat)) -
              tangentPullbackPrimitive ((terms : Rat) / (mesh : Rat)))) := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]
      rw [hsplit, tangentPullbackRectangleErrorPrefix_telescope hmesh terms]
      have hwidth :
          (((terms + 1 : Nat) : Rat) / (mesh : Rat)) -
              ((terms : Rat) / (mesh : Rat)) =
            1 / (mesh : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.add_mul, Rat.mul_add,
          Rat.sub_eq_add_neg, Rat.mul_inv_cancel _ hmeshRat]
      dsimp [tangentPullbackRectangleError]
      rw [hwidth]

theorem tangentPullbackRectangleErrorPrefix_abs_le
    {mesh : Nat} (hmesh : 0 < mesh) :
    forall terms, terms <= mesh ->
      qabs (tangentPullbackRectangleErrorPrefix mesh terms) <=
        4 * (((terms : Rat) / (mesh : Rat)) * (1 / (mesh : Rat)))
  | 0, _ => by
      simp [tangentPullbackRectangleErrorPrefix, qabs]
      grind
  | terms + 1, hterms => by
      have hmeshRat : (mesh : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 hmesh)
      have htermsLe : terms <= mesh := Nat.le_trans (Nat.le_succ terms) hterms
      have hprev := tangentPullbackRectangleErrorPrefix_abs_le hmesh terms htermsLe
      rw [tangentPullbackRectangleErrorPrefix]
      have htermsLt : terms < mesh := Nat.lt_of_succ_le hterms
      have hp0 : 0 <= (terms : Rat) / (mesh : Rat) := by
        rw [Rat.div_def]
        exact Rat.mul_nonneg (by exact_mod_cast Nat.zero_le terms)
          (Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hmesh)))
      have hr1 : ((Nat.succ terms : Nat) : Rat) / (mesh : Rat) <= 1 := by
        rw [Rat.div_def]
        have hcast : ((Nat.succ terms : Nat) : Rat) <= (mesh : Rat) := by
          exact_mod_cast hterms
        have hinv0 : 0 <= (mesh : Rat)⁻¹ :=
          Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hmesh))
        calc
          ((Nat.succ terms : Nat) : Rat) * (mesh : Rat)⁻¹ <=
              (mesh : Rat) * (mesh : Rat)⁻¹ :=
            Rat.mul_le_mul_of_nonneg_right hcast hinv0
          _ = 1 := Rat.mul_inv_cancel _ hmeshRat
      have hpr : (terms : Rat) / (mesh : Rat) <
          ((Nat.succ terms : Nat) : Rat) / (mesh : Rat) := by
        rw [Rat.div_def, Rat.div_def]
        have hpos : 0 < (mesh : Rat)⁻¹ :=
          (Rat.inv_pos).2 ((Rat.natCast_pos).2 hmesh)
        exact Rat.mul_lt_mul_of_pos_right
          (by exact_mod_cast (Nat.lt_succ_self terms)) hpos
      have hcell := tangentPullback_rectangle_error_le hp0 hpr hr1
      have hwidth :
          ((Nat.succ terms : Nat) : Rat) / (mesh : Rat) -
              (terms : Rat) / (mesh : Rat) =
            1 / (mesh : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.add_mul, Rat.mul_add,
          Rat.sub_eq_add_neg, Rat.mul_inv_cancel _ hmeshRat]
      have hcell' :
          qabs (tangentPullbackRectangleError
            ((terms : Rat) / (mesh : Rat))
            (((Nat.succ terms : Nat) : Rat) / (mesh : Rat))) <=
            4 * ((1 / (mesh : Rat)) * (1 / (mesh : Rat))) := by
        dsimp [tangentPullbackRectangleError] at hcell ⊢
        rw [hwidth] at hcell ⊢
        exact hcell
      calc
        qabs (tangentPullbackRectangleErrorPrefix mesh terms +
            tangentPullbackRectangleError
              ((terms : Rat) / (mesh : Rat))
              (((Nat.succ terms : Nat) : Rat) / (mesh : Rat))) <=
            qabs (tangentPullbackRectangleErrorPrefix mesh terms) +
              qabs (tangentPullbackRectangleError
                ((terms : Rat) / (mesh : Rat))
                (((Nat.succ terms : Nat) : Rat) / (mesh : Rat))) :=
          qabs_add_le _ _
        _ <= 4 * (((terms : Rat) / (mesh : Rat)) * (1 / (mesh : Rat))) +
              4 * ((1 / (mesh : Rat)) * (1 / (mesh : Rat))) :=
          rat_add_le_add hprev hcell'
        _ = 4 * ((((Nat.succ terms : Nat) : Rat) / (mesh : Rat)) *
            (1 / (mesh : Rat))) := by
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
            Rat.sub_eq_add_neg, Rat.mul_inv_cancel _ hmeshRat]

theorem tangentPullback_uniformLeftEndpointSum_error_le
    {mesh : Nat} (hmesh : 0 < mesh) :
    qabs
        (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          tangentPullbackDensity mesh -
          (tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0)) <=
      4 / (mesh : Rat) := by
  have htel := tangentPullbackRectangleErrorPrefix_telescope hmesh mesh
  rw [IntegralIdentities.LipschitzDyadic.uniformLeftPrefixSum_at_mesh] at htel
  have habs := tangentPullbackRectangleErrorPrefix_abs_le hmesh mesh
    (Nat.le_refl mesh)
  have hmeshRat : (mesh : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hmesh)
  have hunit : (mesh : Rat) / (mesh : Rat) = 1 := by
    rw [Rat.div_def, Rat.mul_inv_cancel _ hmeshRat]
  rw [hunit] at htel
  rw [htel]
  calc
    qabs (tangentPullbackRectangleErrorPrefix mesh mesh) <=
        4 * (((mesh : Rat) / (mesh : Rat)) * (1 / (mesh : Rat))) := habs
    _ = 4 / (mesh : Rat) := by
      rw [Rat.div_def, Rat.mul_inv_cancel _ hmeshRat]
      grind [Rat.mul_assoc]

private theorem tangentPullback_uniformSum_foldl_eq
    (f : Rat -> Rat) {mesh : Nat} (hmesh : 0 < mesh) :
    forall (xs : List Nat) (initial : Rat),
      xs.foldl
          (fun total (k : Nat) =>
            total + ComputableAnalysis.mesh 0 1 mesh *
              f (leftPoint 0 1 mesh k)) initial =
        xs.foldl
          (fun total (k : Nat) =>
            total + (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat))) initial
  | [], initial => rfl
  | k :: rest, initial => by
      have hmeshRat : (mesh : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 hmesh)
      have hmeshEq : ComputableAnalysis.mesh 0 1 mesh =
          (mesh : Rat)⁻¹ := by
        unfold ComputableAnalysis.mesh
        rw [if_neg (Nat.ne_of_gt hmesh), Rat.div_def]
        grind
      have hstep :
          ComputableAnalysis.mesh 0 1 mesh * f (leftPoint 0 1 mesh k) =
            (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat)) := by
        rw [hmeshEq]
        simp only [leftPoint]
        rw [hmeshEq, Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      change
        rest.foldl
            (fun total (k : Nat) => total +
              (ComputableAnalysis.mesh 0 1 mesh) * f (leftPoint 0 1 mesh k))
            (initial + ComputableAnalysis.mesh 0 1 mesh *
              f (leftPoint 0 1 mesh k)) =
          rest.foldl
            (fun total (k : Nat) => total +
              (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat)))
            (initial + (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat)))
      rw [hstep]
      exact tangentPullback_uniformSum_foldl_eq f hmesh rest
        (initial + (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat)))

theorem tangentPullback_riemannLeftExact_eq_uniformLeftEndpointSum
    {mesh : Nat} (hmesh : 0 < mesh) :
    riemannLeftExact tangentPullbackDensity 0 1 mesh =
      IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        tangentPullbackDensity mesh := by
  unfold riemannLeftExact
  rw [tangentPullback_uniformSum_foldl_eq tangentPullbackDensity hmesh
    (List.range mesh) (0 : Rat)]
  rfl

theorem tangentPullback_riemannLeftExact_stage_error_le (stage : Nat) :
    qabs
        (riemannLeftExact tangentPullbackDensity 0 1 (2 ^ stage) -
          (tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0)) <=
      4 / (((2 ^ stage : Nat) : Rat)) := by
  have hmesh : 0 < 2 ^ stage := Nat.pow_pos (by omega : 0 < 2)
  rw [tangentPullback_riemannLeftExact_eq_uniformLeftEndpointSum hmesh]
  exact tangentPullback_uniformLeftEndpointSum_error_le hmesh

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

/-- The rational tangent-chart integral is already identified with its exact
endpoint difference.  This is a genuine stage-by-stage overlap proof: the
left rectangles miss the primitive telescope by at most `4 / 2^n`, while the
Lipschitz Darboux box has margin `20 / 2^n`. -/
theorem tangentPullbackIntegral_equiv_one :
    tangentPullbackIntegral.Equiv (RealRaw.ofRat 1) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    tangentPullbackIntegral (RealRaw.ofRat 1) n n).2
  rw [tangentPullbackIntegral_compute]
  simp only [RealRaw.ofRat_compute]
  unfold QInterval.Overlaps
  dsimp
  have hmesh : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
  have hmargin :=
    IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum_margin
      tangentPullbackDensity_lipschitz_on_unit n
  have herror := tangentPullback_uniformLeftEndpointSum_error_le hmesh
  have hendpoint := tangentPullbackPrimitive_unit_endpoint_difference
  have hlow :
      -(4 / (((2 ^ n : Nat) : Rat))) <=
        IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
            tangentPullbackDensity (2 ^ n) - 1 := by
    have hq := neg_qabs_le_self
      (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        tangentPullbackDensity (2 ^ n) - 1)
    have hneg := Rat.neg_le_neg herror
    exact Rat.le_trans (by simpa [hendpoint] using hneg) hq
  have hhigh :
      IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          tangentPullbackDensity (2 ^ n) - 1 <=
        4 / (((2 ^ n : Nat) : Rat)) := by
    have hq := self_le_qabs
      (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        tangentPullbackDensity (2 ^ n) - 1)
    exact Rat.le_trans hq (by simpa [hendpoint] using herror)
  constructor <;> grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

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

theorem ArctanSinPiConstruction.sinPiOnHalf_near_of_tangent_near
    (S : ArctanSinPiConstruction)
    {x y : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2)
    (hy : 0 <= y /\ y <= (1 : Rat) / 2)
    (htx : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x))
    (hty : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * y))
    (evalStage : Nat) (eps : QPos)
    (hnear : QInterval.NearAt
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * x)
        htx evalStage)
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * y)
        hty evalStage) eps) :
    QInterval.NearAt
      (S.onHalf.compute x hx evalStage)
      (S.onHalf.compute y hy evalStage)
      { val := 2 * eps.val
        property := Rat.mul_pos (by native_decide) eps.property } := by
  have hUx : subintervalOf
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * x)
        htx evalStage) 0 1 :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      S.inverse (2 * x) htx evalStage
  have hUy : subintervalOf
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * y)
        hty evalStage) 0 1 :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      S.inverse (2 * y) hty evalStage
  change QInterval.NearAt
    (rationalCircleSinInterval
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * x)
        htx evalStage))
    (rationalCircleSinInterval
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * y)
        hty evalStage)) _
  exact rationalCircleSinInterval_near_of_near hUx hUy
    eps hnear

/-- Effective modulus for the public `sin (pi*x)` evaluator.  The factor two
in the input schedule accounts for the reparameterization `t = 2*x`; the
second factor two in the output budget is the rational-circle sine Lipschitz
bound.  This is still a finite interval theorem: no classical real sine is
used. -/
def ArctanSinPiConstruction.sinPiOnHalf_effectiveModulus
    (S : ArctanSinPiConstruction)
    (tangentModulus : EffectiveModulusFor
      (IntegralIdentities.tangentOnUnit S.inverse)) :
    EffectiveModulusFor S.onHalf where
  inputPrecision := fun n =>
    2 * tangentModulus.inputPrecision (2 * (n + 1))
  evalPrecision := fun n =>
    tangentModulus.evalPrecision (2 * (n + 1))
  close := by
    intro x y n hx hy hclose
    let m := 2 * (n + 1)
    have hscale :
        2 * (precisionAtStage m).val <= (precisionAtStage n).val := by
      cases n with
      | zero => native_decide
      | succ n =>
          have hrec := one_div_antitone_pos_local
            (a := ((n + 1 : Nat) : Rat))
            (b := ((n + 2 : Nat) : Rat))
            ((Rat.natCast_pos).2 (by omega))
            (Rat.natCast_le_natCast.2 (by omega))
          have heq :
              2 * (1 / (((2 * (n + 2) : Nat) : Rat))) =
                1 / (((n + 2 : Nat) : Rat)) := by
            rw [Rat.natCast_mul, Rat.div_def, Rat.div_def]
            have hn : ((n + 2 : Nat) : Rat) ≠ 0 :=
              Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega))
            grind [Rat.mul_assoc, Rat.mul_comm,
              Rat.mul_inv_cancel _ hn]
          dsimp [m, precisionAtStage]
          rw [heq]
          exact hrec
    have hx' : 0 <= 2 * x /\ 2 * x <= 1 := by
      have hx0 : 0 <= x := hx.1
      have hxhalf : x <= (1 : Rat) / 2 := hx.2
      constructor
      · exact Rat.mul_nonneg (by native_decide) hx0
      · have h := Rat.mul_le_mul_of_nonneg_left hxhalf
          (by native_decide : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
        rw [hhalf] at h
        exact h
    have hy' : 0 <= 2 * y /\ 2 * y <= 1 := by
      have hy0 : 0 <= y := hy.1
      have hyhalf : y <= (1 : Rat) / 2 := hy.2
      constructor
      · exact Rat.mul_nonneg (by native_decide) hy0
      · have h := Rat.mul_le_mul_of_nonneg_left hyhalf
          (by native_decide : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by native_decide
        rw [hhalf] at h
        exact h
    have hinput : qabs (2 * y - 2 * x) <=
        1 / ((tangentModulus.inputPrecision m : Nat) : Rat) := by
      have hmul := Rat.mul_le_mul_of_nonneg_left hclose
        (by native_decide : (0 : Rat) <= 2)
      rw [show 2 * y - 2 * x = 2 * (y - x) by grind, qabs_mul]
      have htwo : qabs (2 : Rat) = 2 := by native_decide
      rw [htwo]
      have hmul' : 2 * qabs (y - x) <=
          2 * (1 / ((2 * tangentModulus.inputPrecision m : Nat) : Rat)) := by
        simpa [m, Rat.natCast_mul, Rat.mul_comm] using hmul
      calc
        2 * qabs (y - x) <=
            2 * (1 / ((2 * tangentModulus.inputPrecision m : Nat) : Rat)) := hmul'
        _ = 1 / ((tangentModulus.inputPrecision m : Nat) : Rat) := by
          rw [Rat.natCast_mul, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel]
    have htangent := tangentModulus.close
      (2 * x) (2 * y) m hx' hy' hinput
    have hsin := S.sinPiOnHalf_near_of_tangent_near
      hx hy hx' hy' (tangentModulus.evalPrecision m)
      (precisionAtStage m) htangent
    change QInterval.NearAt
      (S.onHalf.compute x hx (tangentModulus.evalPrecision m))
      (S.onHalf.compute y hy (tangentModulus.evalPrecision m))
      (precisionAtStage n)
    unfold QInterval.NearAt QInterval.width at hsin ⊢
    rcases hsin with ⟨hxy, hyx, hwidthx, hwidthy⟩
    constructor <;> grind

/-! Monotonicity also transports through the same finite circle map.  This is
the bridge needed by the endpoint Darboux constructor: the inverse search
supplies a monotone tangent branch, and the rational formula
`2*u/(1+u^2)` is monotone on the certified unit-slope interval. -/

theorem ArctanSinPiConstruction.onHalf_nondecreasing_of_tangent_nondecreasing
    (S : ArctanSinPiConstruction)
  (htangent : NondecreasingOnInterval
      (IntegralIdentities.tangentOnUnit S.inverse)) :
    NondecreasingOnInterval S.onHalf := by
  intro x y hx hy hxy n
  change 0 <= x ∧ x <= (1 : Rat) / 2 at hx
  change 0 <= y ∧ y <= (1 : Rat) / 2 at hy
  have hx' : 0 <= 2 * x /\ 2 * x <= 1 := by
    constructor
    · exact Rat.mul_nonneg (by native_decide) hx.1
    · have h := Rat.mul_le_mul_of_nonneg_left hx.2
        (by native_decide : (0 : Rat) <= 2)
      rw [show (2 : Rat) * (1 / 2) = 1 by native_decide] at h
      exact h
  have hy' : 0 <= 2 * y /\ 2 * y <= 1 := by
    constructor
    · exact Rat.mul_nonneg (by native_decide) hy.1
    · have h := Rat.mul_le_mul_of_nonneg_left hy.2
        (by native_decide : (0 : Rat) <= 2)
      rw [show (2 : Rat) * (1 / 2) = 1 by native_decide] at h
      exact h
  have htan := htangent (2 * x) (2 * y) hx' hy'
    (Rat.mul_le_mul_of_nonneg_left hxy
      (by native_decide : (0 : Rat) <= 2)) n
  have hUx :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      S.inverse (2 * x) hx' n
  have hUy :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      S.inverse (2 * y) hy' n
  change (rationalCircleSinInterval
      (S.inverse.tangentRaw.compute (2 * x) _ n)).lo <=
    (rationalCircleSinInterval
      (S.inverse.tangentRaw.compute (2 * y) _ n)).hi
  exact rationalCircleSin_mono hUx.1 htan hUy.2.2

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

/-- A dyadic sample replacement computes the same public sine integral.

The replacement `g` may use a specialized evaluator—for example, nested
radicals at dyadic angles—because the equal-dyadic algorithm never reads its
values away from the left endpoints of its finite meshes.  Agreement is still
required at every finite stage and every sample point, so this is a
constructive algorithm-transport theorem rather than an extensional claim
about an unrepresented real function. -/
theorem halfIntegral_equiv_of_dyadic_sample_replacement
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (c : Integral.Construction
      (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.Construction g 0 ((1 : Rat) / 2))
    (hplan : c.plan = cg.plan)
    (hsamples : forall n k,
      k < (c.plan n).subdivisions ->
      (sinPiOnHalf C hdefined).toRealFunRaw.compute
        (leftPoint 0 ((1 : Rat) / 2) (c.plan n).subdivisions k)
        (c.plan n).evalPrecision =
      g.compute
        (leftPoint 0 ((1 : Rat) / 2) (c.plan n).subdivisions k)
        (c.plan n).evalPrecision) :
    (halfIntegral C hdefined c).Equiv
      (Integral.integral g 0 ((1 : Rat) / 2) cg) := by
  exact Integral.integral_equiv_of_plan_and_samples c cg hplan hsamples

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

/-- Final value theorem for the public `sin (pi*x)` half-interval integral.

The finite FTC certificate identifies the fixed equal-dyadic integral with the
primitive's endpoint difference; an independent computable endpoint theorem
may then identify that difference with `reciprocalPiRaw`.  This composition is
the theorem-facing result and uses only `RealRaw.Equiv`. -/
theorem halfIntegral_equiv_reciprocalPi_of_FTC
    {C : FunctionRawConstruction}
    {hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)}
    (h : HalfIntegralFTCCertificate C hdefined)
    (hendpoint :
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2)
        h.endpoint_valid).Equiv reciprocalPiRaw) :
    (halfIntegral C hdefined h.integral).Equiv reciprocalPiRaw := by
  have hintegral := halfIntegral_valid C hdefined h.integral
  have hendpointValid :
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2)
        h.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using h.endpoint_valid
  exact RealRaw.equiv_trans hintegral hendpointValid
    reciprocalPiRaw_valid (halfIntegral_equiv_endpoint h) hendpoint

/-- Preferred-API version of the same final assembly.  Once the sine evaluator
has an interval-regularity proof, a monotone Darboux schedule supplies the
equal-mesh integral directly through `ConstructionFor`; the remaining FTC and
endpoint facts are ordinary `RealRaw.Equiv` certificates. -/
theorem ArctanSinPiConstruction.monotoneScheduleIntegral_equiv_reciprocalPi
    (S : ArctanSinPiConstruction)
    (hregular : IntervalRegularOn S.onHalf)
    (hmonotone : NondecreasingOnInterval S.onHalf)
    (hinterval : S.onHalf.lower <= S.onHalf.upper)
    (schedule : ComputableAnalysis.Integral.MonotoneDarbouxSchedule
      S.onHalf hregular hmonotone hinterval)
    (hFTC :
      (ComputableAnalysis.Integral.monotoneDarbouxScheduleIntegralFor schedule).Equiv
        (endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
          (endpointDifference_valid_of_fun_valid
            S.canonicalPrimitive_valid
            S.canonicalPrimitive_domain_zero
            S.canonicalPrimitive_domain_half)))
    (hendpoint :
      (endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
        (endpointDifference_valid_of_fun_valid
          S.canonicalPrimitive_valid
          S.canonicalPrimitive_domain_zero
          S.canonicalPrimitive_domain_half)).Equiv reciprocalPiRaw) :
    (ComputableAnalysis.Integral.monotoneDarbouxScheduleIntegralFor schedule).Equiv
      reciprocalPiRaw := by
  have hintegral :=
    ComputableAnalysis.Integral.monotoneDarbouxScheduleIntegralFor_valid schedule
  have hendpointValid :
      (endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
        (endpointDifference_valid_of_fun_valid
          S.canonicalPrimitive_valid
          S.canonicalPrimitive_domain_zero
          S.canonicalPrimitive_domain_half)).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using
      (endpointDifference_valid_of_fun_valid
        S.canonicalPrimitive_valid
        S.canonicalPrimitive_domain_zero
        S.canonicalPrimitive_domain_half)
  exact RealRaw.equiv_trans hintegral hendpointValid
    reciprocalPiRaw_valid hFTC hendpoint

/-- The theorem-facing specialization once the inverse branch has supplied
monotonicity and the two finite endpoint laws.  This keeps the analytic
certificate small at the call site: the circle monotonicity transport and the
reciprocal-pi endpoint algebra are assembled here. -/
theorem ArctanSinPiConstruction.monotoneScheduleIntegral_equiv_reciprocalPi_of_tangent_nondecreasing
    (S : ArctanSinPiConstruction)
    (htangent : NondecreasingOnInterval
      (IntegralIdentities.tangentOnUnit S.inverse))
    (hregular : IntervalRegularOn S.onHalf)
    (hinterval : S.onHalf.lower <= S.onHalf.upper)
    (schedule : ComputableAnalysis.Integral.MonotoneDarbouxSchedule
      S.onHalf hregular
      (S.onHalf_nondecreasing_of_tangent_nondecreasing htangent)
      hinterval)
    (hFTC :
      (ComputableAnalysis.Integral.monotoneDarbouxScheduleIntegralFor schedule).Equiv
        (endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
          (endpointDifference_valid_of_fun_valid
            S.canonicalPrimitive_valid
            S.canonicalPrimitive_domain_zero
            S.canonicalPrimitive_domain_half)))
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealRaw.zero)
    (ht1 : (S.inverse.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealRaw.one) :
    (ComputableAnalysis.Integral.monotoneDarbouxScheduleIntegralFor schedule).Equiv
      reciprocalPiRaw := by
  apply S.monotoneScheduleIntegral_equiv_reciprocalPi
    hregular
    (S.onHalf_nondecreasing_of_tangent_nondecreasing htangent)
    hinterval schedule hFTC
  simpa [canonicalSineEndpointIntegral] using
    (canonicalSineEndpointIntegral_equiv_reciprocalPi S ht0 ht1)

end SinPiIntegral

end ComputableAnalysis
