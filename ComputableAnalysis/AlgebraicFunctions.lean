import ComputableAnalysis.ComplexInterval
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
  | n + 1, I => sqrtBisectStep q (sqrtBisect q n I)

def sqrtInitialWidthBound (q : Rat) : Nat :=
  (qabs (sqrtUpperBound q)).num.natAbs + 1

def dyadicFuel (target : Nat) : Nat :=
  if target <= 1 then
    1
  else
    1 + dyadicFuel ((target + 1) / 2)
termination_by target
decreasing_by omega

theorem dyadicFuel_pos (target : Nat) : 0 < dyadicFuel target := by
  unfold dyadicFuel
  by_cases h : target <= 1
  case pos => simp [h]
  case neg =>
    simp [h]
    omega

theorem dyadicFuel_mono (a b : Nat) (h : a <= b) :
    dyadicFuel a <= dyadicFuel b := by
  unfold dyadicFuel
  by_cases hb : b <= 1
  case pos =>
    have ha : a <= 1 := by omega
    simp [ha, hb]
  case neg =>
    by_cases ha : a <= 1
    case pos =>
      simp [ha, hb]
    case neg =>
      simp [ha, hb]
      have hhalf : (a + 1) / 2 <= (b + 1) / 2 := by omega
      exact dyadicFuel_mono ((a + 1) / 2) ((b + 1) / 2) hhalf
termination_by b
decreasing_by omega

theorem dyadicFuel_bound (target : Nat) :
    target < 2 ^ dyadicFuel target := by
  unfold dyadicFuel
  by_cases hsmall : target <= 1
  case pos =>
    simp [hsmall]
    omega
  case neg =>
    simp [hsmall]
    have hhalf_lt : (target + 1) / 2 < target := by omega
    have ihhalf := dyadicFuel_bound ((target + 1) / 2)
    rw [show 1 + dyadicFuel ((target + 1) / 2) =
      dyadicFuel ((target + 1) / 2) + 1 by omega]
    rw [Nat.pow_succ]
    calc
      target <= 2 * ((target + 1) / 2) := by omega
      _ < 2 * 2 ^ dyadicFuel ((target + 1) / 2) := by omega
      _ = 2 ^ dyadicFuel ((target + 1) / 2) * 2 := by omega
termination_by target
decreasing_by omega

def sqrtFuel (q : Rat) (eps : QPos) : Nat :=
  dyadicFuel (eps.val.den * sqrtInitialWidthBound q)

def sqrtStageFuel (q : Rat) (n : Nat) : Nat :=
  dyadicFuel ((n + 1) * sqrtInitialWidthBound q)

def sqrtApprox? (q : Rat) (eps : QPos) : Option QInterval :=
  if q < 0 then none else some (sqrtBisect q (sqrtFuel q eps) { lo := 0, hi := sqrtUpperBound q })

def sqrtDomain (q : Rat) : Prop := ¬ q < 0

def sqrtApproxOnDomain (q : Rat) (_h : sqrtDomain q) (n : Nat) : QInterval :=
  sqrtBisect q (sqrtStageFuel q n) { lo := 0, hi := sqrtUpperBound q }

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

private theorem sqrtBisectStep_contains {q : Rat} {I : QInterval}
    (hI : I.lo <= I.hi) : I.ContainsInterval (sqrtBisectStep q I) := by
  have hlom : I.lo <= I.midpoint := lo_le_midpoint hI
  have hmhi : I.midpoint <= I.hi := midpoint_le_hi hI
  unfold QInterval.ContainsInterval sqrtBisectStep
  by_cases htest : sq I.midpoint <= q
  case pos => simp [htest, hlom]
  case neg => simp [htest, hmhi]

private theorem containsInterval_trans {A B C : QInterval}
    (hAB : A.ContainsInterval B) (hBC : B.ContainsInterval C) :
    A.ContainsInterval C := by
  unfold QInterval.ContainsInterval at *
  grind

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
      sqrtBisectStep_spec (sqrtBisect_spec q fuel I hI)

theorem sqrtBisectStep_width (q : Rat) (I : QInterval) :
    (sqrtBisectStep q I).width = I.width / 2 := by
  unfold sqrtBisectStep
  change (if sq I.midpoint <= q then
      ({ lo := I.midpoint, hi := I.hi } : QInterval)
    else
      ({ lo := I.lo, hi := I.midpoint } : QInterval)).width =
    I.width / 2
  by_cases h : sq I.midpoint <= q
  case pos =>
    simp [QInterval.width, QInterval.midpoint]
    rw [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  case neg =>
    simp [QInterval.width, QInterval.midpoint]
    rw [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]

theorem sqrtBisect_width (q : Rat) :
    forall fuel I,
      (sqrtBisect q fuel I).width = I.width / ((2 : Rat) ^ fuel)
  | 0, I => by
      simp [sqrtBisect]
      rw [Rat.div_def]
      grind
  | fuel + 1, I => by
      unfold sqrtBisect
      rw [sqrtBisectStep_width q (sqrtBisect q fuel I)]
      rw [sqrtBisect_width q fuel I]
      rw [Rat.div_def, Rat.div_def]
      rw [Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem sqrtBisect_contains_of_le (q : Rat) {I : QInterval}
    (hI : SqrtIntervalSpec q I) {n m : Nat} (hnm : n <= m) :
    (sqrtBisect q n I).ContainsInterval (sqrtBisect q m I) := by
  induction hnm with
  | refl =>
      unfold QInterval.ContainsInterval
      constructor <;> exact Rat.le_refl
  | step hle ih =>
      rename_i k
      have hspec_k : SqrtIntervalSpec q (sqrtBisect q k I) :=
        sqrtBisect_spec q k I hI
      have hstep :
          (sqrtBisect q k I).ContainsInterval
            (sqrtBisect q (k + 1) I) := by
        change (sqrtBisect q k I).ContainsInterval
          (sqrtBisectStep q (sqrtBisect q k I))
        exact sqrtBisectStep_contains hspec_k.2.1
      exact containsInterval_trans ih hstep

theorem sqrtStageFuel_mono (q : Rat) {n m : Nat} (hnm : n <= m) :
    sqrtStageFuel q n <= sqrtStageFuel q m := by
  unfold sqrtStageFuel
  exact dyadicFuel_mono _ _
    (Nat.mul_le_mul_right _ (Nat.succ_le_succ hnm))

theorem sqrtStageFuel_pos (q : Rat) (n : Nat) :
    0 < sqrtStageFuel q n := by
  unfold sqrtStageFuel
  exact dyadicFuel_pos _

private theorem rat_nonneg_lt_numNatAbs_succ {r : Rat} (hr : 0 <= r) :
    r < ((r.num.natAbs + 1 : Nat) : Rat) := by
  have hdenpos : 0 < (r.den : Rat) :=
    (Rat.natCast_pos).2 (Nat.pos_of_ne_zero r.den_nz)
  have hdenge : (1 : Rat) <= (r.den : Rat) := by
    have h : 1 <= r.den :=
      Nat.succ_le_of_lt (Nat.pos_of_ne_zero r.den_nz)
    exact_mod_cast h
  have hrden : r <= (r.den : Rat) * r := by
    calc
      r = 1 * r := by grind
      _ <= (r.den : Rat) * r :=
        Rat.mul_le_mul_of_nonneg_right hdenge hr
  have hnum_nonneg : 0 <= r.num := by
    by_cases hrzero : r = 0
    case pos =>
      rw [hrzero]
      native_decide
    case neg =>
      have hrpos : 0 < r := by grind
      exact Int.le_of_lt (rat_num_pos_of_pos hrpos)
  have hnumcast : ((r.num.natAbs : Nat) : Rat) = (r.num : Rat) := by
    exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
  have hle : r <= ((r.num.natAbs : Nat) : Rat) := by
    calc
      r <= (r.den : Rat) * r := hrden
      _ = (r.num : Rat) := rat_den_mul_self r
      _ = ((r.num.natAbs : Nat) : Rat) := by rw [hnumcast]
  have hlt :
      ((r.num.natAbs : Nat) : Rat) <
        ((r.num.natAbs + 1 : Nat) : Rat) := by
    exact_mod_cast Nat.lt_succ_self r.num.natAbs
  grind

private theorem rat_le_qabs (r : Rat) : r <= qabs r := by
  unfold qabs
  by_cases hneg : r < 0
  case pos => simp [hneg]; grind
  case neg => simp [hneg]

theorem sqrtUpperBound_lt_initialWidthBound {q : Rat} (hq : 0 <= q) :
    sqrtUpperBound q < (sqrtInitialWidthBound q : Rat) := by
  unfold sqrtInitialWidthBound
  have hU_nonneg : 0 <= sqrtUpperBound q := sqrtUpperBound_nonneg hq
  have hle : sqrtUpperBound q <= qabs (sqrtUpperBound q) := rat_le_qabs _
  have hlt :=
    rat_nonneg_lt_numNatAbs_succ (qabs_nonneg (sqrtUpperBound q))
  grind

private theorem nat_lt_two_pow_self {n : Nat} (hn : 0 < n) : n < 2 ^ n := by
  induction n with
  | zero => contradiction
  | succ n ih =>
      cases n with
      | zero => native_decide
      | succ n =>
          have hpos : 0 < n + 1 := Nat.succ_pos n
          have ih' : n + 1 < 2 ^ (n + 1) := ih hpos
          calc
            n + 1 + 1 <= 2 * (n + 1) := by omega
            _ < 2 * 2 ^ (n + 1) := by omega
            _ = 2 ^ (n + 1 + 1) := by
              rw [Nat.pow_succ]
              omega

private theorem nat_cast_two_pow (n : Nat) :
    ((2 ^ n : Nat) : Rat) = (2 : Rat) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ]
      change ((2 ^ (n + 1) : Nat) : Rat) = (2 : Rat) ^ n * 2
      rw [show (2 : Rat) ^ n = ((2 ^ n : Nat) : Rat) from Eq.symm ih]
      exact_mod_cast Nat.pow_succ 2 n

private theorem rat_nat_lt_two_pow_self {n : Nat} (hn : 0 < n) :
    (n : Rat) < (2 : Rat) ^ n := by
  have hnat := nat_lt_two_pow_self hn
  have hcast : (n : Rat) < ((2 ^ n : Nat) : Rat) := by
    exact_mod_cast hnat
  simpa [nat_cast_two_pow n] using hcast

private theorem div_lt_one_div_nat_of_mul_lt {U : Rat} {D t : Nat}
    (hD : 0 < D) (ht : (D : Rat) * U < (2 : Rat) ^ t) :
    U / ((2 : Rat) ^ t) < (1 : Rat) / (D : Rat) := by
  have hpowpos : 0 < (2 : Rat) ^ t :=
    Rat.pow_pos (by native_decide : (0 : Rat) < 2)
  have hDpos : 0 < (D : Rat) := (Rat.natCast_pos).2 hD
  rw [Rat.div_lt_iff hpowpos]
  rw [Rat.div_def]
  refine Rat.lt_of_mul_lt_mul_left (c := (D : Rat)) ?h ?hc
  case h =>
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  case hc =>
    exact Rat.le_of_lt hDpos

theorem sqrtStage_width_lt_one_div {q : Rat} (hq : 0 <= q)
    {N : Nat} (hN : 0 < N) :
    sqrtUpperBound q / ((2 : Rat) ^ sqrtStageFuel q N) <
      (1 : Rat) / (N : Rat) := by
  let U := sqrtUpperBound q
  let B := sqrtInitialWidthBound q
  let target := (N + 1) * sqrtInitialWidthBound q
  let t := sqrtStageFuel q N
  have hBpos : 0 < B := by
    dsimp [B, sqrtInitialWidthBound]
    exact Nat.succ_pos _
  have hBgt : U < (B : Rat) := by
    dsimp [U, B]
    exact sqrtUpperBound_lt_initialWidthBound hq
  have hNratpos : 0 < (N : Rat) := (Rat.natCast_pos).2 hN
  have hNU_lt_NB : (N : Rat) * U < (N : Rat) * (B : Rat) :=
    Rat.mul_lt_mul_of_pos_left hBgt hNratpos
  have hNB_le_target : (N : Rat) * (B : Rat) <= (target : Rat) := by
    dsimp [target, B]
    have hnat :
        N * sqrtInitialWidthBound q <=
          (N + 1) * sqrtInitialWidthBound q := by
      exact Nat.mul_le_mul_right _ (Nat.le_succ N)
    exact_mod_cast hnat
  have htarget_lt_pow_nat : target < 2 ^ t := by
    dsimp [target, t, sqrtStageFuel]
    exact dyadicFuel_bound ((N + 1) * sqrtInitialWidthBound q)
  have htarget_lt_pow : (target : Rat) < (2 : Rat) ^ t := by
    have hcast : (target : Rat) < ((2 ^ t : Nat) : Rat) := by
      exact_mod_cast htarget_lt_pow_nat
    simpa [nat_cast_two_pow t] using hcast
  have hNU_lt_pow : (N : Rat) * U < (2 : Rat) ^ t := by grind
  change U / ((2 : Rat) ^ t) < (1 : Rat) / (N : Rat)
  exact div_lt_one_div_nat_of_mul_lt hN hNU_lt_pow

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

theorem sqrtApproxOnDomain_width_lt_one_div
    (q : Rat) (h : sqrtDomain q) {N : Nat} (hN : 0 < N) :
    (sqrtApproxOnDomain q h N).width < (1 : Rat) / (N : Rat) := by
  have hq : 0 <= q := by
    unfold sqrtDomain at h
    grind
  unfold sqrtApproxOnDomain
  rw [sqrtBisect_width]
  change (sqrtUpperBound q - 0) / ((2 : Rat) ^ sqrtStageFuel q N) <
    (1 : Rat) / (N : Rat)
  have hzero : sqrtUpperBound q - 0 = sqrtUpperBound q := by
    grind [Rat.sub_eq_add_neg]
  rw [hzero]
  exact sqrtStage_width_lt_one_div hq hN

theorem sqrtApproxOnDomain_precisionValidCompute
    (q : Rat) (h : sqrtDomain q) :
    RealRaw.PrecisionValidCompute (sqrtApproxOnDomain q h) := by
  have hq : 0 <= q := by
    unfold sqrtDomain at h
    grind
  constructor
  · intro n
    have hspec := sqrtApproxOnDomain_spec q h n
    have hle : (sqrtApproxOnDomain q h n).lo <=
        (sqrtApproxOnDomain q h n).hi := hspec.2.1
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hfuel : sqrtStageFuel q n <= sqrtStageFuel q m :=
        sqrtStageFuel_mono q hnm
      have hcontains :=
        sqrtBisect_contains_of_le q (sqrtInitialSpec hq) hfuel
      have hspec_m := sqrtApproxOnDomain_spec q h m
      unfold sqrtApproxOnDomain at hcontains hspec_m ⊢
      constructor
      · exact hcontains.1
      · constructor
        · exact hspec_m.2.1
        · exact hcontains.2
    · intro N hN
      exact sqrtApproxOnDomain_width_lt_one_div q h hN

theorem sqrtPartialRaw_precisionValid
    (q : Rat) (h : sqrtPartialRaw.definedAt q) :
    RealRaw.PrecisionValidCompute (sqrtPartialRaw.compute q h) := by
  simpa [sqrtPartialRaw] using sqrtApproxOnDomain_precisionValidCompute q h

theorem sqrtPartialRaw_valid
    (q : Rat) (h : sqrtPartialRaw.definedAt q) :
    RealRaw.ValidCompute (sqrtPartialRaw.compute q h) :=
  RealRaw.validCompute_of_precisionValidCompute
    (sqrtPartialRaw_precisionValid q h)

theorem sqrtRaw_precisionValid (q : Rat) (h : sqrtDomain q) :
    (sqrtRaw q h).PrecisionValid := by
  simpa [RealRaw.PrecisionValid, sqrtRaw] using
    sqrtApproxOnDomain_precisionValidCompute q h

theorem sqrtRaw_valid (q : Rat) (h : sqrtDomain q) :
    (sqrtRaw q h).Valid :=
  RealRaw.valid_of_precisionValid (sqrtRaw_precisionValid q h)

theorem sqrtRaw_spec (q : Rat) (h : sqrtDomain q) : SqrtRawSpec q h := by
  constructor
  · exact sqrtRaw_valid q h
  · exact sqrtRaw_stage_spec q h

theorem sqrtDomain_of_nonneg {q : Rat} (hq : 0 <= q) : sqrtDomain q := by
  unfold sqrtDomain
  grind

theorem sqrtRaw_valid_of_nonneg (q : Rat) (hq : 0 <= q) :
    (sqrtRaw q (sqrtDomain_of_nonneg hq)).Valid :=
  sqrtRaw_valid q (sqrtDomain_of_nonneg hq)

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
