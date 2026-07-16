import ComputableAnalysis.ComplexInterval
import ComputableAnalysis.FTC
import ComputableAnalysis.Polynomial

namespace ComputableAnalysis

/-!
# Algebraic functions

This file collects algebraic-function algorithms.  In particular, square root
is treated here as the algebraic function cut out by `w^2 = z`; the rational
input algorithm below is the real branch on nonnegative rational inputs.
-/

namespace Polynomial

/-- One Newton step for a rational polynomial at a rational point.

The step is partial: if `p' x = 0`, Newton's method is not defined at `x`, so
the algorithm returns `none`. -/
def newtonStep? (coeffs : List Rat) (x : Rat) : Option Rat :=
  let slope := eval (derivative coeffs) x
  if slope = 0 then none else some (x - eval coeffs x / slope)

/-- The `n`th rational Newton iterate from `seed`, stopping if a derivative
vanishes along the way. -/
def newtonIterate? (coeffs : List Rat) : Nat -> Rat -> Option Rat
  | 0, seed => some seed
  | n + 1, seed =>
      match newtonIterate? coeffs n seed with
      | none => none
      | some x => newtonStep? coeffs x

/-- The `n`th Newton iterate, displayed as an exact point interval when the
iteration is defined.  This is deliberately not claimed to be a valid
`RealRaw`; convergence and certification require separate hypotheses. -/
def newtonPointInterval? (coeffs : List Rat) (seed : Rat) (n : Nat) :
    Option QInterval :=
  (newtonIterate? coeffs n seed).map fun x => { lo := x, hi := x }

end Polynomial

namespace CPoly

def derivative : Coeffs -> Coeffs
  | [] => []
  | _ :: cs =>
      cs.zipIdx.map fun (c, i) =>
        QComplex.scaleRat ((i + 1 : Nat) : Rat) c

def ofRatCoeffs (coeffs : List Rat) : Coeffs :=
  coeffs.map QComplex.ofRat

/-- One complex Newton step for a polynomial with rational-complex
coefficients at a rational-complex point. -/
def newtonStep? (coeffs : Coeffs) (z : QComplex) : Option QComplex :=
  let slope := eval (derivative coeffs) z
  match QComplex.div? (eval coeffs z) slope with
  | none => none
  | some correction => some (QComplex.sub z correction)

/-- The `n`th rational-complex Newton iterate from `seed`, stopping if the
derivative vanishes along the way. -/
def newtonIterate? (coeffs : Coeffs) : Nat -> QComplex -> Option QComplex
  | 0, seed => some seed
  | n + 1, seed =>
      match newtonIterate? coeffs n seed with
      | none => none
      | some z => newtonStep? coeffs z

def newtonIterateFromRatPoly? (coeffs : List Rat) (seed : QComplex)
    (n : Nat) : Option QComplex :=
  newtonIterate? (ofRatCoeffs coeffs) n seed

/-- The `n`th complex Newton iterate as an exact point box, when defined.
As with the rational version, this is a computational trace, not a validity
certificate. -/
def newtonPointBox? (coeffs : Coeffs) (seed : QComplex) (n : Nat) :
    Option QBox :=
  (newtonIterate? coeffs n seed).map QBox.point

end CPoly

namespace BiPoly

/-- Bivariate complex polynomials.  The outer list is in `z`; each inner
polynomial is in `w`. -/
abbrev Coeffs := List CPoly.Coeffs

def eval (P : Coeffs) (z w : QComplex) : QComplex :=
  P.foldr (fun row acc => QComplex.add (CPoly.eval row w) (QComplex.mul z acc)) QComplex.zero

def evalBox (P : Coeffs) (Z W : QBox) : QBox :=
  P.foldr (fun row acc => QBox.add (QBox.evalPoly row W) (QBox.mul Z acc)) QBox.zero

def onCurve (P : Coeffs) (z w : QComplex) : Prop :=
  eval P z w = QComplex.zero

/-- `w^2 - z`, viewed as an equation for square-root branches. -/
def sqrtEquation : Coeffs :=
  [[QComplex.zero, QComplex.zero, QComplex.one], [QComplex.ofRat (-1)]]

end BiPoly

namespace AlgebraicFunction

/-- A raw algebraic-function branch.  The branch is computational; the equation
records the algebraic relation it is intended to satisfy. -/
structure Raw where
  equation : BiPoly.Coeffs
  branch : FunctionRaw

namespace Raw

def domain (f : Raw) : QComplex -> Prop := f.branch.domain

def evalRaw (f : Raw) (z : QComplex) (hz : f.domain z) : ComplexRaw :=
  f.branch.evalRaw z hz

/-- Certification target: the computed boxes for the branch satisfy the
equation at every requested precision.  The input is exact rational-complex;
the output is a box. -/
def SatisfiesEquation (f : Raw) : Prop :=
  forall z (hz : f.domain z) n,
    let Z := QBox.point z
    let W := f.branch.compute z hz n
    let eps : QPos := if hn : n = 0 then
      { val := 1, property := by native_decide }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }
    QBox.Overlaps (BiPoly.evalBox f.equation Z W) (QBox.zeroAround eps)

/-- Agreement of algebraic branches is still agreement of their underlying
raw functions on the common domain. -/
def AgreeOnCommonDomain (f g : Raw) : Prop :=
  FunctionRaw.AgreeOnCommonDomain f.branch g.branch

end Raw

/-- Target shape for a square-root branch: a domain, a raw algorithm, and the
equation `w^2 = z`. -/
def sqrtBranch (branch : FunctionRaw) : Raw where
  equation := BiPoly.sqrtEquation
  branch := branch

end AlgebraicFunction

def sq (x : Rat) : Rat := x * x
def maxRat (a b : Rat) : Rat := if a <= b then b else a
def sqrtUpperBound (q : Rat) : Rat := maxRat 1 q

def sqrtBisectStep (q : Rat) (I : QInterval) : QInterval :=
  let m := I.midpoint
  if sq m <= q then { lo := m, hi := I.hi } else { lo := I.lo, hi := m }

def sqrtBisect (q : Rat) : Nat -> QInterval -> QInterval
  | 0, I => I
  | n + 1, I => sqrtBisect q n (sqrtBisectStep q I)

def sqrtFuel (q : Rat) (eps : QPos) : Nat := eps.val.den + (sqrtUpperBound q).den + 8

def sqrtApprox? (q : Rat) (eps : QPos) : Option QInterval :=
  if q < 0 then none else some (sqrtBisect q (sqrtFuel q eps) { lo := 0, hi := sqrtUpperBound q })

def sqrtDomain (q : Rat) : Prop := ¬ q < 0

def sqrtStageEps (n : Nat) : QPos :=
  if hn : n = 0 then
    { val := 1, property := by native_decide }
  else
    { val := (1 / (n : Rat)), property := by
        rw [Rat.div_def, Rat.one_mul]
        exact (Rat.inv_pos).2
          ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn)) }

theorem one_div_natCast_den_eq (n : Nat) (hn : n ≠ 0) :
    (1 / (n : Rat)).den = n := by
  rw [Rat.div_def]
  rw [Rat.inv_def]
  change (1 * Rat.divInt 1 (n : Int)).den = n
  rw [Rat.one_mul]
  change (Rat.divInt 1 (Int.ofNat n)).den = n
  rw [Rat.divInt.eq_1]
  change (mkRat 1 n).den = n
  simp [mkRat, Rat.normalize_eq, hn]

theorem sqrtStageEps_den_eq (n : Nat) (hn : n ≠ 0) :
    (sqrtStageEps n).val.den = n := by
  simp [sqrtStageEps, hn]
  exact one_div_natCast_den_eq n hn

theorem sqrtFuel_sqrtStageEps_eq (q : Rat) (n : Nat) (hn : n ≠ 0) :
    sqrtFuel q (sqrtStageEps n) = n + (sqrtUpperBound q).den + 8 := by
  unfold sqrtFuel
  rw [sqrtStageEps_den_eq n hn]

def sqrtApproxOnDomain (q : Rat) (_h : sqrtDomain q) (n : Nat) : QInterval :=
  sqrtBisect q (sqrtFuel q (sqrtStageEps n)) { lo := 0, hi := sqrtUpperBound q }

def sqrtPartialRaw : PartialRealFunRaw where
  definedAt := sqrtDomain
  compute := sqrtApproxOnDomain

def sqrtCompute? (q : Rat) : Option (Nat -> QInterval) :=
  if hneg : q < 0 then
    none
  else
    some (sqrtPartialRaw.compute q hneg)

def sqrtCertified? (q : Rat) : Prop :=
  Exists fun compute : Nat -> QInterval =>
    sqrtCompute? q = some compute /\ RealRaw.ValidCompute compute

def sqrtRaw (q : Rat) (h : sqrtDomain q) : RealRaw where
  compute := fun n => sqrtApproxOnDomain q h n

def sqrtReal (q : Rat) (h : sqrtDomain q)
    (hvalid : (sqrtRaw q h).Valid) : Real :=
  Real.ofRaw (sqrtRaw q h) hvalid

namespace Rat

def sqrt (q : Rat) : Option (Nat -> QInterval) := sqrtCompute? q

end Rat

namespace RealRaw

def Nonnegative (x : RealRaw) : Prop :=
  forall eps, 0 <= (x.compute eps).hi

structure SqrtDomain (x : RealRaw) where
  valid : x.Valid
  nonnegative : x.Nonnegative

/-- Real square root as a partial operation target.

Unlike rational input, arbitrary computable-real nonnegativity is not generally
decidable, so the domain proof is an explicit argument.  The implementation of
the algorithm and the theorem that it computes a square root are later work.
-/
def sqrt (x : RealRaw) (_h : SqrtDomain x) : Prop :=
  Exists fun y : RealRaw => y.Valid

end RealRaw

def SqrtIntervalSpec (q : Rat) (I : QInterval) : Prop := 0 <= I.lo /\ I.lo <= I.hi /\ sq I.lo <= q /\ q <= sq I.hi

private theorem sqrtUpperBound_nonneg {q : Rat} (hq : 0 <= q) :
    0 <= sqrtUpperBound q := by
  unfold sqrtUpperBound maxRat
  by_cases hle : (1 : Rat) <= q
  case pos => simp [hle, hq]
  case neg => simpa [hle] using (by native_decide : (0 : Rat) <= 1)

private theorem sqrtUpperBound_sq_ge {q : Rat} (hq : 0 <= q) :
    q <= sq (sqrtUpperBound q) := by
  unfold sqrtUpperBound maxRat
  by_cases hle : (1 : Rat) <= q
  case pos =>
    simp [hle, sq]
    calc
      q = q * 1 := by grind
      _ <= q * q := Rat.mul_le_mul_of_nonneg_left hle hq
  case neg =>
    simp [hle, sq]
    have hqle : q <= 1 := by grind
    simpa using hqle

private theorem sqrtInitialSpec {q : Rat} (hq : 0 <= q) :
    SqrtIntervalSpec q { lo := 0, hi := sqrtUpperBound q } := by
  unfold SqrtIntervalSpec
  constructor
  case left => simp
  case right =>
    constructor
    case left => exact sqrtUpperBound_nonneg hq
    case right =>
      constructor
      case left => simpa [sq] using hq
      case right => exact sqrtUpperBound_sq_ge hq

private theorem midpoint_le_hi {I : QInterval} (h : I.lo <= I.hi) :
    I.midpoint <= I.hi := by
  unfold QInterval.midpoint
  have h2b : I.lo + I.hi <= 2 * I.hi := by grind
  calc
    (I.lo + I.hi) / 2 <= (2 * I.hi) / 2 := by
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right h2b
        (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2)))
    _ = I.hi := by
      rw [Rat.div_def]
      have hne : (2 : Rat) != 0 := by native_decide
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem lo_le_midpoint {I : QInterval} (h : I.lo <= I.hi) :
    I.lo <= I.midpoint := by
  unfold QInterval.midpoint
  have h2a : 2 * I.lo <= I.lo + I.hi := by grind
  calc
    I.lo = (2 * I.lo) / 2 := by
      rw [Rat.div_def]
      have hne : (2 : Rat) != 0 := by native_decide
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ <= (I.lo + I.hi) / 2 := by
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right h2a
        (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2)))

private theorem midpoint_nonneg {I : QInterval}
    (hlo : 0 <= I.lo) (hle : I.lo <= I.hi) :
    0 <= I.midpoint := by
  exact Rat.le_trans hlo (lo_le_midpoint hle)

theorem sqrtBisectStep_width_eq_half (q : Rat) (I : QInterval) :
    (sqrtBisectStep q I).width = I.width / 2 := by
  unfold sqrtBisectStep QInterval.width QInterval.midpoint
  by_cases h : sq ((I.lo + I.hi) / 2) <= q
  · simp [h]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  · simp [h]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]

theorem sqrtBisect_width_eq (q : Rat) (fuel : Nat) (I : QInterval) :
    (sqrtBisect q fuel I).width =
      I.width / (((2 ^ fuel : Nat) : Rat)) := by
  induction fuel generalizing I with
  | zero =>
      simp [sqrtBisect]
      rw [Rat.div_def]
      grind [Rat.mul_inv_cancel]
  | succ fuel ih =>
      simp [sqrtBisect]
      rw [ih]
      rw [sqrtBisectStep_width_eq_half]
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      have hpow :
          (((2 ^ (fuel + 1) : Nat) : Rat)) =
            (((2 ^ fuel : Nat) : Rat)) * 2 := by
        exact_mod_cast (by simpa using (Nat.pow_succ 2 fuel))
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem sqrtApproxOnDomain_width_eq
    (q : Rat) (h : sqrtDomain q) (n : Nat) :
    (sqrtApproxOnDomain q h n).width =
      sqrtUpperBound q /
        (((2 ^ sqrtFuel q (sqrtStageEps n) : Nat) : Rat)) := by
  unfold sqrtApproxOnDomain
  rw [sqrtBisect_width_eq]
  simp [QInterval.width]
  rw [Rat.div_def]
  grind [Rat.mul_inv_cancel]

theorem sqrtApproxOnDomain_width_eq_positive_stage
    (q : Rat) (h : sqrtDomain q) (n : Nat) (hn : n ≠ 0) :
    (sqrtApproxOnDomain q h n).width =
      sqrtUpperBound q /
        (((2 ^ (n + (sqrtUpperBound q).den + 8) : Nat) : Rat)) := by
  rw [sqrtApproxOnDomain_width_eq]
  rw [sqrtFuel_sqrtStageEps_eq q n hn]

theorem sqrtStageEps_den_mono {n m : Nat} (hnm : n <= m) :
    (sqrtStageEps n).val.den <= (sqrtStageEps m).val.den := by
  by_cases hm0 : m = 0
  · have hn0 : n = 0 := by omega
    simp [sqrtStageEps, hn0, hm0]
  · by_cases hn0 : n = 0
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      rw [sqrtStageEps_den_eq m hm0]
      simp [sqrtStageEps, hn0]
      exact hmpos
    · rw [sqrtStageEps_den_eq n hn0, sqrtStageEps_den_eq m hm0]
      exact hnm

theorem sqrtFuel_sqrtStageEps_mono
    (q : Rat) {n m : Nat} (hnm : n <= m) :
    sqrtFuel q (sqrtStageEps n) <= sqrtFuel q (sqrtStageEps m) := by
  unfold sqrtFuel
  have hden := sqrtStageEps_den_mono hnm
  omega

theorem sqrtBisectStep_contains
    (q : Rat) {I : QInterval} (hI : I.lo <= I.hi) :
    I.ContainsInterval (sqrtBisectStep q I) := by
  unfold QInterval.ContainsInterval sqrtBisectStep QInterval.midpoint
  by_cases h : sq ((I.lo + I.hi) / 2) <= q
  · simp [h]
    exact lo_le_midpoint hI
  · simp [h]
    exact midpoint_le_hi hI

theorem sqrtBisectStep_spec {q : Rat} {I : QInterval}
    (hI : SqrtIntervalSpec q I) :
    SqrtIntervalSpec q (sqrtBisectStep q I) := by
  have hlo : 0 <= I.lo := hI.1
  have hlohi : I.lo <= I.hi := hI.2.1
  have hloSq : sq I.lo <= q := hI.2.2.1
  have hhiSq : q <= sq I.hi := hI.2.2.2
  have hlom : I.lo <= I.midpoint := lo_le_midpoint hlohi
  have hmhi : I.midpoint <= I.hi := midpoint_le_hi hlohi
  have hmnonneg : 0 <= I.midpoint := midpoint_nonneg hlo hlohi
  unfold sqrtBisectStep
  by_cases htest : sq I.midpoint <= q
  case pos =>
    simp [htest, SqrtIntervalSpec, hmnonneg, hmhi, hhiSq]
  case neg =>
    have hqle : q <= sq I.midpoint := by grind
    simp [htest, SqrtIntervalSpec, hlo, hlom, hloSq, hqle]

theorem sqrtBisect_spec (q : Rat) :
    forall fuel I, SqrtIntervalSpec q I ->
      SqrtIntervalSpec q (sqrtBisect q fuel I)
  | 0, _I, hI => hI
  | fuel + 1, I, hI =>
      sqrtBisect_spec q fuel (sqrtBisectStep q I) (sqrtBisectStep_spec hI)

private theorem qinterval_contains_refl (I : QInterval) :
    I.ContainsInterval I := by
  unfold QInterval.ContainsInterval
  exact ⟨Rat.le_refl, Rat.le_refl⟩

private theorem qinterval_contains_trans {I J K : QInterval}
    (hIJ : I.ContainsInterval J) (hJK : J.ContainsInterval K) :
    I.ContainsInterval K := by
  unfold QInterval.ContainsInterval at *
  exact ⟨Rat.le_trans hIJ.1 hJK.1, Rat.le_trans hJK.2 hIJ.2⟩

theorem sqrtBisect_succ_right (q : Rat) (fuel : Nat) (I : QInterval) :
    sqrtBisect q (fuel + 1) I = sqrtBisectStep q (sqrtBisect q fuel I) := by
  induction fuel generalizing I with
  | zero => rfl
  | succ fuel ih =>
      simpa [sqrtBisect] using ih (sqrtBisectStep q I)

theorem sqrtBisect_step_refines_of_spec
    {q : Rat} {I : QInterval} (hI : SqrtIntervalSpec q I) (fuel : Nat) :
    (sqrtBisect q fuel I).ContainsInterval
      (sqrtBisect q (fuel + 1) I) := by
  rw [sqrtBisect_succ_right]
  exact sqrtBisectStep_contains q (sqrtBisect_spec q fuel I hI).2.1

theorem sqrtBisect_contains_of_le_fuel
    {q : Rat} {I : QInterval} (hI : SqrtIntervalSpec q I)
    {fuel₁ fuel₂ : Nat} (hle : fuel₁ <= fuel₂) :
    (sqrtBisect q fuel₁ I).ContainsInterval
      (sqrtBisect q fuel₂ I) := by
  induction hle with
  | refl =>
      exact qinterval_contains_refl (sqrtBisect q fuel₁ I)
  | step hle ih =>
      rename_i k
      exact qinterval_contains_trans ih
        (sqrtBisect_step_refines_of_spec hI k)

theorem sqrtApproxOnDomain_spec (q : Rat) (h : sqrtDomain q) (n : Nat) :
    SqrtIntervalSpec q (sqrtApproxOnDomain q h n) := by
  have hq : 0 <= q := by
    unfold sqrtDomain at h
    grind
  unfold sqrtApproxOnDomain
  exact sqrtBisect_spec q _ _ (sqrtInitialSpec hq)

theorem le_of_sq_le_sq_of_nonneg_right {a b : Rat}
    (hb : 0 <= b) (h : sq a <= sq b) : a <= b := by
  by_cases hab : a <= b
  case pos => exact hab
  case neg =>
    have hba : b < a := by grind
    have hapos : 0 < a := by grind
    have hblea : b <= a := by grind
    have h1 : b * a < a * a := Rat.mul_lt_mul_of_pos_right hba hapos
    have h0 : b * b <= b * a := Rat.mul_le_mul_of_nonneg_left hblea hb
    unfold sq at h
    grind

theorem SqrtIntervalSpec.lo_le_of_sq_le
    {q r : Rat} {I : QInterval}
    (hI : SqrtIntervalSpec q I) (hr : 0 <= r) (hqr : q <= sq r) :
    I.lo <= r :=
  le_of_sq_le_sq_of_nonneg_right hr (Rat.le_trans hI.2.2.1 hqr)

theorem SqrtIntervalSpec.le_hi_of_sq_le
    {q r : Rat} {I : QInterval}
    (hI : SqrtIntervalSpec q I) (hrq : sq r <= q) :
    r <= I.hi := by
  have hhi_nonneg : 0 <= I.hi := Rat.le_trans hI.1 hI.2.1
  exact le_of_sq_le_sq_of_nonneg_right hhi_nonneg
    (Rat.le_trans hrq hI.2.2.2)

def sqrtIntervalSpecBool (q : Rat) (I : QInterval) : Bool := decide (0 <= I.lo /\ I.lo <= I.hi /\ sq I.lo <= q /\ q <= sq I.hi)

def sqrtApproxOk? (q : Rat) (eps : QPos) : Option Bool :=
  match sqrtApprox? q eps with | none => none | some I => some (I.widthOk eps && sqrtIntervalSpecBool q I)

def SqrtRealRawSpec (q : Rat) (x : RealRaw) : Prop := x.Valid /\ forall eps, SqrtIntervalSpec q (x.compute eps)

theorem sqrtRaw_stage_spec (q : Rat) (h : sqrtDomain q) (n : Nat) :
    SqrtIntervalSpec q ((sqrtRaw q h).compute n) := by
  simpa [sqrtRaw] using sqrtApproxOnDomain_spec q h n

def SqrtRawSpec (q : Rat) (h : sqrtDomain q) : Prop :=
  SqrtRealRawSpec q (sqrtRaw q h)

def sqrtWidthConstant (q : Rat) : Nat :=
  (sqrtUpperBound q).num.natAbs + 1

private theorem rat_le_num_natAbs_succ (q : Rat) :
    q <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
  by_cases hqpos : 0 < q
  · have hdenpos : 0 < ((q.den : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
    apply Rat.le_of_mul_le_mul_right (c := ((q.den : Nat) : Rat))
    · rw [Rat.mul_comm q ((q.den : Nat) : Rat), rat_den_mul_self]
      have hnumpos : 0 < q.num := rat_num_pos_of_pos hqpos
      have hnum_nonneg : 0 <= q.num := Int.le_of_lt hnumpos
      have hcast : (((q.num.natAbs : Nat) : Rat)) = (q.num : Rat) := by
        exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
      calc
        (q.num : Rat) = ((q.num.natAbs : Nat) : Rat) := by rw [hcast]
        _ <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
          exact_mod_cast (Nat.le_succ q.num.natAbs)
        _ <= (((q.num.natAbs + 1 : Nat) : Rat)) *
            ((q.den : Nat) : Rat) := by
          exact_mod_cast (Nat.le_mul_of_pos_right (q.num.natAbs + 1)
            (Nat.pos_of_ne_zero q.den_nz))
    · exact hdenpos
  · have hqnonpos : q <= 0 := by grind
    have hzero : (0 : Rat) <= (((q.num.natAbs + 1 : Nat) : Rat)) :=
      Rat.natCast_nonneg
    exact Rat.le_trans hqnonpos hzero

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

theorem sqrtApproxOnDomain_width_le_nat_over_succ
    (q : Rat) (h : sqrtDomain q) (n : Nat) :
    (sqrtApproxOnDomain q h n).width <=
      (sqrtWidthConstant q : Rat) / (((n + 1 : Nat) : Rat)) := by
  let B : Rat := sqrtUpperBound q
  let C : Nat := sqrtWidthConstant q
  let fuel : Nat := sqrtFuel q (sqrtStageEps n)
  have hBC : B <= (C : Rat) := by
    dsimp [B, C, sqrtWidthConstant]
    exact rat_le_num_natAbs_succ (sqrtUpperBound q)
  have hfuel_ge : n <= fuel := by
    dsimp [fuel]
    by_cases hn : n = 0
    · omega
    · rw [sqrtFuel_sqrtStageEps_eq q n hn]
      omega
  have hsucc_pow : n + 1 <= 2 ^ fuel := by
    exact Nat.le_trans (succ_le_two_pow n)
      (Nat.pow_le_pow_right (by omega : 0 < 2) hfuel_ge)
  have hden_pos : 0 < (((2 ^ fuel : Nat) : Rat)) := by
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hone_den_nonneg : 0 <= 1 / (((2 ^ fuel : Nat) : Rat)) := by
    rw [Rat.div_def]
    exact Rat.le_of_lt (Rat.mul_pos (by native_decide : (0 : Rat) < 1)
      ((Rat.inv_pos).2 hden_pos))
  have hone :
      (1 / (((2 ^ fuel : Nat) : Rat))) <=
        1 / (((n + 1 : Nat) : Rat)) := by
    exact FTC.one_div_nat_antitone (Nat.succ_pos n)
      (Nat.pow_pos (by omega : 0 < 2)) hsucc_pow
  rw [sqrtApproxOnDomain_width_eq]
  dsimp [B, fuel] at *
  calc
    sqrtUpperBound q /
        (((2 ^ sqrtFuel q (sqrtStageEps n) : Nat) : Rat)) =
        B * (1 / (((2 ^ fuel : Nat) : Rat))) := by
      dsimp [B, fuel]
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (C : Rat) * (1 / (((2 ^ fuel : Nat) : Rat))) := by
      exact Rat.mul_le_mul_of_nonneg_right hBC hone_den_nonneg
    _ <= (C : Rat) * (1 / (((n + 1 : Nat) : Rat))) := by
      exact Rat.mul_le_mul_of_nonneg_left hone Rat.natCast_nonneg
    _ = (sqrtWidthConstant q : Rat) / (((n + 1 : Nat) : Rat)) := by
      dsimp [C, sqrtWidthConstant]
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem widthsShrink_of_natOverSuccBound_local
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
      exact_mod_cast (by omega :
        C * (eps.val.den + 1) <= n + 1)
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

theorem sqrtApproxOnDomain_widthsShrink
    (q : Rat) (h : sqrtDomain q) :
    RealRaw.WidthsShrinkToZero (sqrtApproxOnDomain q h) :=
  widthsShrink_of_natOverSuccBound_local
    (sqrtApproxOnDomain_width_le_nat_over_succ q h)

theorem sqrtApproxOnDomain_ordered (q : Rat) (h : sqrtDomain q) (n : Nat) :
    0 <= (sqrtApproxOnDomain q h n).width := by
  have hspec := sqrtApproxOnDomain_spec q h n
  unfold SqrtIntervalSpec at hspec
  unfold QInterval.width
  grind

theorem sqrtApproxOnDomain_contains_of_le
    (q : Rat) (h : sqrtDomain q) {n m : Nat} (hnm : n <= m) :
    (sqrtApproxOnDomain q h n).ContainsInterval
      (sqrtApproxOnDomain q h m) := by
  have hq : 0 <= q := by
    unfold sqrtDomain at h
    grind
  unfold sqrtApproxOnDomain
  exact sqrtBisect_contains_of_le_fuel (sqrtInitialSpec hq)
    (sqrtFuel_sqrtStageEps_mono q hnm)

theorem sqrtApproxOnDomain_nested
    (q : Rat) (h : sqrtDomain q) :
    forall n m, n <= m ->
      (sqrtApproxOnDomain q h n).lo <=
        (sqrtApproxOnDomain q h m).lo /\
      (sqrtApproxOnDomain q h m).lo <=
        (sqrtApproxOnDomain q h m).hi /\
      (sqrtApproxOnDomain q h m).hi <=
        (sqrtApproxOnDomain q h n).hi := by
  intro n m hnm
  have hcontains := sqrtApproxOnDomain_contains_of_le q h hnm
  have hspecm := sqrtApproxOnDomain_spec q h m
  unfold QInterval.ContainsInterval at hcontains
  exact ⟨hcontains.1, hspecm.2.1, hcontains.2⟩

theorem sqrtApproxOnDomain_valid (q : Rat) (h : sqrtDomain q) :
    RealRaw.ValidCompute (sqrtApproxOnDomain q h) := by
  exact ⟨sqrtApproxOnDomain_ordered q h,
    sqrtApproxOnDomain_nested q h,
    sqrtApproxOnDomain_widthsShrink q h⟩

theorem sqrtRaw_valid (q : Rat) (h : sqrtDomain q) :
    (sqrtRaw q h).Valid := by
  simpa [sqrtRaw] using sqrtApproxOnDomain_valid q h

theorem sqrtRaw_spec (q : Rat) (h : sqrtDomain q) :
    SqrtRawSpec q h :=
  ⟨sqrtRaw_valid q h, sqrtRaw_stage_spec q h⟩

theorem sqrtCertified_of_domain (q : Rat) (h : sqrtDomain q) :
    sqrtCertified? q := by
  unfold sqrtCertified? sqrtCompute?
  simp
  refine ⟨sqrtPartialRaw.compute q h, ?_, ?_⟩
  · exact ⟨h, rfl⟩
  · exact sqrtApproxOnDomain_valid q h

theorem sq_le_sq_of_nonneg_le {a b : Rat} (ha : 0 <= a) (hab : a <= b) :
    sq a <= sq b := by
  have hb : 0 <= b := Rat.le_trans ha hab
  unfold sq
  calc
    a * a <= b * a := Rat.mul_le_mul_of_nonneg_right hab ha
    _ <= b * b := Rat.mul_le_mul_of_nonneg_left hab hb

theorem sq_qabs (x : Rat) :
    sq (qabs x) = sq x := by
  unfold qabs sq
  by_cases hneg : x < 0
  case pos =>
    simp [hneg]
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
  case neg =>
    simp [hneg]

theorem sq_sub_factor (lo hi : Rat) :
    sq hi - sq lo = (hi - lo) * (hi + lo) := by
  unfold sq
  grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.sub_eq_add_neg]

theorem sq_lt_sq_of_nonneg_lt {a b : Rat} (ha : 0 <= a) (hab : a < b) :
    sq a < sq b := by
  have hdiff : 0 < sq b - sq a := by
    rw [sq_sub_factor]
    exact Rat.mul_pos (by grind) (by grind)
  grind

theorem sqrt_spec_sq_gap_le_stage_bound {q r : Rat} {x : RealRaw}
    (hx : SqrtRealRawSpec q x)
    (hover : x.SameStageOverlap (RealRaw.ofRat r))
    (n : Nat) :
    qabs (sq r - q) <=
      (x.compute n).width * (2 * (x.compute 0).hi + 1) := by
  have hspec := hx.2 n
  have hr : (x.compute n).lo <= r /\ r <= (x.compute n).hi := by
    have h := (RealRaw.compareAt_overlap_iff x (RealRaw.ofRat r) n n).1
      (hover n)
    simpa [RealRaw.ofRat, QInterval.Overlaps] using h
  have hsq_lo_r : sq (x.compute n).lo <= sq r :=
    sq_le_sq_of_nonneg_le hspec.1 hr.1
  have hr_nonneg : 0 <= r := Rat.le_trans hspec.1 hr.1
  have hsq_r_hi : sq r <= sq (x.compute n).hi :=
    sq_le_sq_of_nonneg_le hr_nonneg hr.2
  have hgapStage :
      qabs (sq r - q) <= sq (x.compute n).hi - sq (x.compute n).lo :=
    qabs_sub_le_of_common_bounds
      hsq_lo_r hsq_r_hi hspec.2.2.1 hspec.2.2.2
  have hnest := hx.1.2.1 0 n (Nat.zero_le n)
  have hsum :
      (x.compute n).hi + (x.compute n).lo <=
        2 * (x.compute 0).hi + 1 := by
    have hlo_le_hi0 : (x.compute n).lo <= (x.compute 0).hi :=
      Rat.le_trans hspec.2.1 hnest.2.2
    have hhi_le_hi0 : (x.compute n).hi <= (x.compute 0).hi := hnest.2.2
    grind
  have hwidth_nonneg : 0 <= (x.compute n).hi - (x.compute n).lo := by
    simpa [QInterval.width] using hx.1.1 n
  have hprod :
      sq (x.compute n).hi - sq (x.compute n).lo <=
        (x.compute n).width * (2 * (x.compute 0).hi + 1) := by
    rw [sq_sub_factor, QInterval.width]
    exact Rat.mul_le_mul_of_nonneg_left hsum hwidth_nonneg
  exact Rat.le_trans hgapStage hprod

theorem eq_of_qabs_sub_le_width_mul_of_valid {a b C : Rat} {x : RealRaw}
    (hx : x.Valid) (hCpos : 0 < C)
    (hbound : forall n, qabs (a - b) <= (x.compute n).width * C) :
    a = b := by
  by_cases hEq : a = b
  case pos => exact hEq
  case neg =>
    exfalso
    let gap : Rat := qabs (a - b)
    have hdiff_ne : Not (a - b = 0) := by
      intro hzero
      apply hEq
      grind
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      exact qabs_pos_of_ne hdiff_ne
    have htwoCpos : 0 < 2 * C := by grind
    have hepsPos : 0 < gap / (2 * C) := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap_pos ((Rat.inv_pos).2 htwoCpos)
    obtain ⟨N, hsmall⟩ := hx.2.2
      { val := gap / (2 * C), property := hepsPos }
    let n : Nat := N
    have hboundN : gap <= (x.compute n).width * C := by
      dsimp [gap]
      exact hbound n
    have hsmallN : (x.compute n).width <= gap / (2 * C) :=
      hsmall n (Nat.le_refl n)
    have hmul :
        (x.compute n).width * C <= (gap / (2 * C)) * C :=
      Rat.mul_le_mul_of_nonneg_right hsmallN (Rat.le_of_lt hCpos)
    have hgapLe : gap <= (gap / (2 * C)) * C :=
      Rat.le_trans hboundN hmul
    have hhalf : (gap / (2 * C)) * C = gap / 2 := by
      rw [Rat.div_def, Rat.div_def]
      have h2Cne : (2 * C : Rat) != 0 := by grind
      have h2ne : (2 : Rat) != 0 := by native_decide
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hgapLeHalf : gap <= gap / 2 := by
      rw [hhalf] at hgapLe
      exact hgapLe
    have hhalfLt : gap / 2 < gap := by
      have htwo : (0 : Rat) < 2 := by native_decide
      rw [Rat.div_lt_iff htwo]
      grind
    have hgapLtHalf : gap < gap / 2 :=
      Rat.lt_of_le_of_ne hgapLeHalf (Rat.ne_of_gt hhalfLt)
    grind

theorem sq_eq_of_sqrt_spec_equiv_rat {q r : Rat} {x : RealRaw}
    (hx : SqrtRealRawSpec q x)
    (heq : x.Equiv (RealRaw.ofRat r)) :
    sq r = q := by
  let C : Rat := 2 * (x.compute 0).hi + 1
  have hspec0 := hx.2 0
  have hhi0_nonneg : 0 <= (x.compute 0).hi :=
    Rat.le_trans hspec0.1 hspec0.2.1
  have hCpos : 0 < C := by
    dsimp [C]
    grind
  have hratValid : (RealRaw.ofRat r).Valid := by
    simpa [RealRaw.ofRat] using RealRaw.ofRat_valid r
  have hover := RealRaw.sameStageOverlap_of_equiv hx.1 hratValid heq
  exact eq_of_qabs_sub_le_width_mul_of_valid hx.1 hCpos (by
    intro n
    dsimp [C]
    exact sqrt_spec_sq_gap_le_stage_bound hx hover n)

/-- Squaring as an exact rational interval function.  This is the forward map
for the first concrete inverse-function example: its inverse on the
nonnegative unit interval is the existing square-root bisection algorithm. -/
def squareRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ _ => { lo := sq x, hi := sq x }

theorem squareRaw_valid (x : Rat) (hx : squareRaw.definedAt x) :
    RealRaw.ValidCompute (squareRaw.compute x hx) := by
  simpa [squareRaw] using RealRaw.ofRat_valid (sq x)

/-- The exact squaring function restricted to the nonnegative unit interval. -/
def squareOnUnit : FunctionOnInterval where
  raw := squareRaw
  lower := 0
  upper := 1
  defined_on := by
    intro _ _
    trivial
  valid_on := by
    intro x hx
    exact squareRaw_valid x hx

/-- Endpoint evaluation is an enclosure for squaring on a nonnegative input
interval. -/
def squareUnitEvalInterval (I : QInterval) : QInterval :=
  { lo := sq I.lo, hi := sq I.hi }

theorem squareUnitEvalInterval_width (I : QInterval) :
    (squareUnitEvalInterval I).width = I.width * (I.hi + I.lo) := by
  unfold squareUnitEvalInterval QInterval.width sq
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem squareUnit_interval_width_scale (w : Rat) (n : Nat)
    (hn : n ≠ 0)
    (hw : w <= 1 / ((2 * n : Nat) : Rat)) :
    2 * w <= 1 / (n : Rat) := by
  calc
    2 * w <= 2 * (1 / ((2 * n : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hw (by native_decide)
    _ = 1 / (n : Rat) := by
      rw [Rat.div_def]
      rw [show ((2 * n : Nat) : Rat) = (2 : Rat) * (n : Rat) by
        exact Rat.natCast_mul 2 n]
      have htwo : (2 : Rat) ≠ 0 := by native_decide
      have hn' : (n : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn))
      rw [Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- Squaring is interval-regular on `[0,1]`, with a direct rational modulus.
The zero stage is exact on zero-width input boxes, matching the raw-real
precision convention. -/
def squareOnUnit_intervalRegular : IntervalRegularOn squareOnUnit := by
  refine
    { evalInterval := fun I _ _ => squareUnitEvalInterval I
      inputPrecision := fun n => 2 * n
      inputPrecision_pos := by
        intro n hn
        omega
      output_width := ?_
      contains_point_values := ?_ }
  · intro I hI n hwidth
    rcases hI with ⟨hlo, hord, hhi⟩
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hsum_nonneg : 0 <= I.hi + I.lo := by
      have hhi_nonneg : 0 <= I.hi := Rat.le_trans hlo hord
      exact Rat.add_nonneg hhi_nonneg hlo
    have hsum_le_two : I.hi + I.lo <= 2 := by
      change (0 : Rat) <= I.lo at hlo
      change I.hi <= 1 at hhi
      grind
    constructor
    · rw [squareUnitEvalInterval_width]
      exact Rat.mul_nonneg hwidth_nonneg hsum_nonneg
    · rw [squareUnitEvalInterval_width]
      calc
        I.width * (I.hi + I.lo) <= I.width * 2 :=
          Rat.mul_le_mul_of_nonneg_left hsum_le_two hwidth_nonneg
        _ = 2 * I.width := by grind [Rat.mul_comm]
        _ <= 1 / (n : Rat) := by
          by_cases hn : n = 0
          · subst n
            have hinvzero : 1 / ((2 * (0 : Nat) : Nat) : Rat) = 0 := by
              native_decide
            rw [hinvzero] at hwidth
            have hzero : I.width = 0 := Rat.le_antisymm hwidth hwidth_nonneg
            rw [hzero]
            native_decide
          · exact squareUnit_interval_width_scale I.width n hn hwidth
  · intro I hI x hx n hxlo hxhi
    rcases hI with ⟨hIlo, hord, hIhi⟩
    change (0 : Rat) <= I.lo at hIlo
    have hlo_nonneg : 0 <= I.lo := hIlo
    have hx_nonneg : 0 <= x := Rat.le_trans hlo_nonneg hxlo
    have hlo_sq : sq I.lo <= sq x :=
      sq_le_sq_of_nonneg_le hlo_nonneg hxlo
    have hhi_sq : sq x <= sq I.hi :=
      sq_le_sq_of_nonneg_le hx_nonneg hxhi
    change squareUnitEvalInterval I |>.ContainsInterval
      (squareOnUnit.compute x hx n)
    simpa [squareUnitEvalInterval, squareOnUnit, squareRaw] using
      And.intro hlo_sq hhi_sq

/-- The concrete continuous squaring map used by the unit square-root
inverse example. -/
def squareOnUnit_continuous : ContinuousFunctionOnInterval where
  function := squareOnUnit
  regular := squareOnUnit_intervalRegular

/-- The square map on the unit interval satisfies the project's literal
rational epsilon--delta continuity predicate, without a topology import. -/
theorem squareOnUnit_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn squareOnUnit :=
  squareOnUnit_intervalRegular.epsilonDeltaContinuous

theorem squareOnUnit_nondecreasing : NondecreasingOnInterval squareOnUnit := by
  intro x y hx hy hxy _
  have hx_nonneg : 0 <= x := hx.1
  have hsq : sq x <= sq y := sq_le_sq_of_nonneg_le hx_nonneg hxy
  simpa [squareOnUnit, squareRaw] using hsq

/-- On `[0,1]`, a separation of `1/(n+1)` in the input strictly separates the
exact output boxes after squaring.  This is the nondecreasing effective
inverse-separation certificate. -/
def squareOnUnit_effectiveInverseSeparation :
    EffectiveInverseSeparation squareOnUnit where
  kind := .nondecreasing
  inputPrecision := fun n => n + 1
  inputPrecision_pos := fun n => Nat.succ_pos n
  outputPrecision := fun _ => 0
  separated := by
    intro x y hx hy n hsep
    have hx_nonneg : 0 <= x := hx.1
    have hstep_pos : 0 < (1 / (((n + 1 : Nat) : Rat))) :=
      one_div_nat_pos (Nat.succ_pos n)
    have hxy : x < y := by
      grind
    have hsq : sq x < sq y := sq_lt_sq_of_nonneg_lt hx_nonneg hxy
    simpa [squareOnUnit, squareRaw] using hsq

/-- The unit-interval square map supplies the constructive data required by
the monotone inverse-function interface. -/
def squareOnUnit_invertible : InvertibleFunctionOnInterval where
  continuous := squareOnUnit_continuous
  monotone := MonotoneOnInterval.ofNondecreasing squareOnUnit_nondecreasing
  separation := squareOnUnit_effectiveInverseSeparation
  orientation := trivial

namespace Rat

def IsNatSquare (n : Nat) : Prop :=
  Exists fun k : Nat => k * k = n

/-- An integer square, stated in a way that exposes the finite search:
negative integers are excluded, and otherwise one searches natural squares up to
`z.natAbs`. -/
def IsIntSquare (z : Int) : Prop :=
  0 <= z /\ IsNatSquare z.natAbs

/-- A rational square.  We do not require the witness to be nonnegative:
if `r^2 = q`, then the nonnegative square-root value is `|r|`. -/
def IsSquare (q : Rat) : Prop :=
  Exists fun r : Rat => sq r = q

def NotSquare (q : Rat) : Prop :=
  ¬ IsSquare q

/-- Finite normal-form criterion: a reduced rational is a square precisely when
its numerator and denominator are squares. -/
def IsSquareInLowestTerms (q : Rat) : Prop :=
  IsIntSquare q.num /\ IsNatSquare q.den

/-- Finite normal-form nonsquare criterion.

For a reduced rational, it is enough for either the numerator or the denominator
to fail the finite square test.  Requiring both to be nonsquares is a useful
sufficient special case, but not necessary: `2 / 9` and `4 / 3` are already
nonsquares. -/
def IsNonSquareInLowestTerms (q : Rat) : Prop :=
  ¬ IsIntSquare q.num ∨ ¬ IsNatSquare q.den

theorem sq_num (r : Rat) : (sq r).num = r.num * r.num := by
  unfold sq
  unfold HMul.hMul instHMul Mul.mul Rat.instMul Rat.mul
  simp [r.reduced]
  rfl

theorem sq_den (r : Rat) : (sq r).den = r.den * r.den := by
  unfold sq
  unfold HMul.hMul instHMul Mul.mul Rat.instMul Rat.mul
  simp [r.reduced]
  rfl

theorem sq_num_nonneg (r : Rat) : 0 <= (sq r).num := by
  rw [sq_num]
  rw [← Int.natAbs_mul_self]
  exact Int.natCast_nonneg _

theorem sq_num_isIntSquare (r : Rat) : IsIntSquare (sq r).num := by
  constructor
  · exact sq_num_nonneg r
  · refine ⟨r.num.natAbs, ?_⟩
    rw [sq_num]
    simp [Int.natAbs_mul]

theorem sq_den_isNatSquare (r : Rat) : IsNatSquare (sq r).den := by
  refine ⟨r.den, ?_⟩
  rw [sq_den]

/-- Euclid's normal-form observation: when a reduced rational is a square, its
normalized numerator and denominator are squares. -/
theorem isSquareInLowestTerms_of_isSquare {q : Rat} :
    IsSquare q -> IsSquareInLowestTerms q := by
  intro hq
  rcases hq with ⟨r, hr⟩
  rw [← hr]
  exact ⟨sq_num_isIntSquare r, sq_den_isNatSquare r⟩

theorem isSquare_of_isSquareInLowestTerms {q : Rat} :
    IsSquareInLowestTerms q -> IsSquare q := by
  intro hs
  rcases hs.1 with ⟨hnum_nonneg, hnum_square⟩
  rcases hnum_square with ⟨a, ha⟩
  rcases hs.2 with ⟨b, hb⟩
  have haRat : (a : Rat) * (a : Rat) = (q.num : Rat) := by
    have haInt : ((a * a : Nat) : Int) = q.num := by
      rw [ha]
      exact Int.natAbs_of_nonneg hnum_nonneg
    exact_mod_cast haInt
  have hbRat : (b : Rat) * (b : Rat) = (q.den : Rat) := by
    exact_mod_cast hb
  have hb_ne_zero : b ≠ 0 := by
    intro hb0
    apply q.den_nz
    rw [← hb]
    simp [hb0]
  have hbRat_ne_zero : (b : Rat) ≠ 0 := by
    exact_mod_cast hb_ne_zero
  refine Exists.intro ((a : Rat) / (b : Rat)) ?_
  apply rat_eq_of_den_mul_eq_num (q := q)
  rw [← hbRat, ← haRat]
  unfold sq
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel, Rat.inv_mul_cancel]

theorem square_iff_lowest_terms_square (q : Rat) :
    IsSquare q ↔ IsSquareInLowestTerms q :=
  ⟨isSquareInLowestTerms_of_isSquare, isSquare_of_isSquareInLowestTerms⟩

/-- Contrapositive form used for irrational square roots: if either normalized
part is not a square, then the rational is not a rational square. -/
theorem notSquare_of_nonSquareInLowestTerms {q : Rat} :
    IsNonSquareInLowestTerms q -> NotSquare q := by
  intro hns hsq
  have hs := isSquareInLowestTerms_of_isSquare hsq
  cases hns with
  | inl hnum => exact hnum hs.1
  | inr hden => exact hden hs.2

theorem notSquare_iff_lowest_terms_nonsquare (q : Rat) :
    NotSquare q ↔ IsNonSquareInLowestTerms q := by
  constructor
  · intro hn
    classical
    by_cases hnum : IsIntSquare q.num
    · right
      intro hden
      exact hn (isSquare_of_isSquareInLowestTerms ⟨hnum, hden⟩)
    · left
      exact hnum
  · exact notSquare_of_nonSquareInLowestTerms

theorem integer_square_criterion (z : Int) :
    IsSquare (z : Rat) ↔ IsIntSquare z := by
  exact Iff.trans (square_iff_lowest_terms_square (z : Rat)) (by
    unfold IsSquareInLowestTerms
    constructor
    · intro h
      simpa using h.1
    · intro hz
      constructor
      · simpa using hz
      · refine ⟨1, ?_⟩
        simp)

theorem square_root_denominator_bound (q r : Rat) (hr : sq r = q) :
    r.den <= q.den := by
  rw [← hr, sq_den]
  exact Nat.le_mul_of_pos_right r.den (Nat.pos_of_ne_zero r.den_nz)

end Rat

/-- General theorem target for rational square roots:
if `q` is a rational square, then the computable real produced by the rational
sqrt algorithm for `q` is rational.  The expected rational representative is
`|r|`, since the sqrt algorithm computes the nonnegative root. -/
theorem sqrt_rational_of_square
    (q r : Rat) (hq : sqrtDomain q) (h : SqrtRawSpec q hq)
    (hr : sq r = q) :
    (sqrtReal q hq h.1).Equiv (Real.ofRat (qabs r)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hI := h.2 n
  have habs_nonneg : 0 <= qabs r := qabs_nonneg r
  have hq_le_sq : q <= sq (qabs r) := by
    rw [sq_qabs, hr]
    exact Rat.le_refl
  have hsq_le_q : sq (qabs r) <= q := by
    rw [sq_qabs, hr]
    exact Rat.le_refl
  have hlo : ((sqrtRaw q hq).compute n).lo <= qabs r :=
    SqrtIntervalSpec.lo_le_of_sq_le hI habs_nonneg hq_le_sq
  have hhi : qabs r <= ((sqrtRaw q hq).compute n).hi :=
    SqrtIntervalSpec.le_hi_of_sq_le hI hsq_le_q
  exact (RealRaw.compareAt_overlap_iff (sqrtRaw q hq)
    (RealRaw.ofRat (qabs r)) n n).2
    (by simpa [RealRaw.ofRat, QInterval.Overlaps] using And.intro hlo hhi)

/-- Equivalently: for nonnegative rational input, the rational sqrt algorithm
produces a rational computable real exactly for rational-square inputs. -/
theorem sqrt_rational_iff_square
    (q : Rat) (hq : sqrtDomain q) (h : SqrtRawSpec q hq) :
    Real.Rational (sqrtReal q hq h.1) ↔ Rat.IsSquare q := by
  constructor
  case mp =>
    intro hrational
    rcases hrational with ⟨r, heq⟩
    refine Exists.intro r ?_
    have heqRaw : (sqrtRaw q hq).Equiv (RealRaw.ofRat r) := by
      simpa [sqrtReal, Real.ofRat, Real.Equiv, Real.ofRaw] using heq
    exact sq_eq_of_sqrt_spec_equiv_rat h heqRaw
  case mpr =>
    intro hsquare
    rcases hsquare with ⟨r, hr⟩
    refine Exists.intro (qabs r) ?_
    exact sqrt_rational_of_square q r hq h hr

/-- Lowest-terms version of the classification: the rationality of the
computable real `sqrt(q)` is determined by whether the normalized numerator and
denominator of `q` are both squares. -/
theorem sqrt_rational_iff_lowest_terms_square
    (q : Rat) (hq : sqrtDomain q) (h : SqrtRawSpec q hq) :
    Real.Rational (sqrtReal q hq h.1) ↔
      Rat.IsSquareInLowestTerms q := by
  exact Iff.trans (sqrt_rational_iff_square q hq h)
    (Rat.square_iff_lowest_terms_square q)

end ComputableAnalysis
