import Init.Grind.Ordered.Rat

/-!
# Basic raw computable real and complex foundation

This file is the low-level substrate: rational intervals and boxes, raw real
and complex algorithms, validity and equivalence, rational coercions, raw
function representations, and the basic arithmetic operations on raw
algorithms.
-/

namespace ComputableAnalysis

abbrev QPos := {q : Rat // 0 < q}

theorem one_div_nat_pos {n : Nat} (hn : 0 < n) : 0 < 1 / (n : Rat) := by
  rw [Rat.div_def, Rat.one_mul]
  exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)

structure QInterval where
  lo : Rat
  hi : Rat
deriving Repr, DecidableEq

namespace QInterval

def width (I : QInterval) : Rat := I.hi - I.lo
def midpoint (I : QInterval) : Rat := (I.lo + I.hi) / 2
def Overlaps (I J : QInterval) : Prop := I.lo <= J.hi /\ J.lo <= I.hi
def CloseAt (I J : QInterval) (eps : QPos) : Prop :=
  Overlaps I J /\ I.width <= eps.val /\ J.width <= eps.val
/-- `outer.ContainsInterval inner` says the rational interval `outer` encloses
the whole rational interval `inner`. -/
def ContainsInterval (outer inner : QInterval) : Prop :=
  outer.lo <= inner.lo /\ inner.hi <= outer.hi
def overlaps (I J : QInterval) : Bool := decide (I.lo <= J.hi /\ J.lo <= I.hi)
def closeAt (I J : QInterval) (eps : QPos) : Bool :=
  decide (I.lo <= J.hi /\ J.lo <= I.hi /\ I.width <= eps.val /\ J.width <= eps.val)
def widthOk (I : QInterval) (eps : QPos) : Bool := decide (0 <= I.width /\ I.width <= eps.val)

/-- The smallest rational interval containing both input intervals. -/
def hull (I J : QInterval) : QInterval :=
  { lo := min I.lo J.lo, hi := max I.hi J.hi }

/-- The common part of two rational intervals.  Unlike `hull`, this is only
ordered when the two inputs have a common subinterval; clients prove that
fact explicitly rather than silently replacing an empty intersection. -/
def intersection (I J : QInterval) : QInterval :=
  { lo := max I.lo J.lo, hi := min I.hi J.hi }

theorem hull_contains_left (I J : QInterval) : (hull I J).ContainsInterval I := by
  unfold ContainsInterval hull
  grind

theorem hull_contains_right (I J : QInterval) : (hull I J).ContainsInterval J := by
  unfold ContainsInterval hull
  grind

theorem hull_least {K I J : QInterval}
    (hI : K.ContainsInterval I) (hJ : K.ContainsInterval J) :
    K.ContainsInterval (hull I J) := by
  unfold ContainsInterval hull at *
  grind

theorem intersection_contains
    {I J K : QInterval}
    (hI : I.ContainsInterval K) (hJ : J.ContainsInterval K) :
    (intersection I J).ContainsInterval K := by
  unfold ContainsInterval intersection at *
  grind

theorem intersection_contained_left (I J : QInterval) :
    I.lo <= (intersection I J).lo /\
      (intersection I J).hi <= I.hi := by
  unfold intersection
  grind

theorem intersection_contained_right (I J : QInterval) :
    J.lo <= (intersection I J).lo /\
      (intersection I J).hi <= J.hi := by
  unfold intersection
  grind

theorem width_le_of_contains {outer inner : QInterval}
    (h : outer.ContainsInterval inner) :
    inner.width <= outer.width := by
  change outer.lo <= inner.lo /\ inner.hi <= outer.hi at h
  change inner.hi - inner.lo <= outer.hi - outer.lo
  grind [Rat.sub_eq_add_neg]

theorem hull_width_le_add_of_overlaps
    {I J : QInterval}
    (hI : 0 <= I.width) (hJ : 0 <= J.width)
    (hover : I.Overlaps J) :
    (hull I J).width <= I.width + J.width := by
  unfold width hull Overlaps at *
  grind [Rat.sub_eq_add_neg]

def inv (I : QInterval) : QInterval :=
  if 0 < I.lo then
    { lo := 1 / I.hi, hi := 1 / I.lo }
  else if I.hi < 0 then
    { lo := 1 / I.hi, hi := 1 / I.lo }
  else
    { lo := -1, hi := 1 }

def decimalScale (digits : Nat) : Int :=
  Int.ofNat (10 ^ digits)

def zeroPad (digits : Nat) (s : String) : String :=
  String.ofList (List.replicate (digits - s.length) '0') ++ s

/-- Decimal display helper for `#eval!` output.  This is only presentation;
the stored interval remains rational. -/
def ratDecimal (digits : Nat) (q : Rat) : String :=
  let qpos := if q < 0 then -q else q
  let scale := decimalScale digits
  let scaled := Int.ediv (qpos.num * scale) (Int.ofNat qpos.den)
  let whole := Int.ediv scaled scale
  let frac := Int.emod scaled scale
  let sign := if q < 0 then "-" else ""
  sign ++ toString whole ++
    if digits = 0 then "" else "." ++ zeroPad digits (toString frac)

def decimal (digits : Nat) (I : QInterval) : String :=
  "[" ++ ratDecimal digits I.lo ++ ", " ++ ratDecimal digits I.hi ++
    "] width=" ++ ratDecimal digits I.width

def trimDecimalString (s : String) : String :=
  let chars := s.toList
  if chars.contains '.' then
    let trimmed := chars.reverse.dropWhile (fun c => c = '0')
    let trimmed := trimmed.dropWhile (fun c => c = '.')
    let out := String.ofList trimmed.reverse
    if out = "-0" then "0" else out
  else
    s

def ratDecimalCompact (digits : Nat) (q : Rat) : String :=
  trimDecimalString (ratDecimal digits q)

def ensureDecimalPoint (s : String) : String :=
  if s.toList.contains '.' then s else s ++ ".0"

def decimalExactAt (digits : Nat) (q : Rat) : Bool :=
  Int.emod (q.num * decimalScale digits) (Int.ofNat q.den) = 0

def scaledDecimalFixed (digits : Nat) (scaled : Int) : String :=
  let scale := decimalScale digits
  let scaledAbs := if scaled < 0 then -scaled else scaled
  let whole := Int.ediv scaledAbs scale
  let frac := Int.emod scaledAbs scale
  let sign := if scaled < 0 then "-" else ""
  sign ++ toString whole ++
    if digits = 0 then "" else "." ++ zeroPad digits (toString frac)

def floorDecimalFixed (digits : Nat) (q : Rat) : String :=
  scaledDecimalFixed digits
    (Int.ediv (q.num * decimalScale digits) (Int.ofNat q.den))

def ceilDecimalFixed (digits : Nat) (q : Rat) : String :=
  scaledDecimalFixed digits
    (-Int.ediv (-(q.num * decimalScale digits)) (Int.ofNat q.den))

def firstDifferingPrefixLength : List Char -> List Char -> Nat -> Nat
  | [], _, i => i
  | _, [], i => i
  | a :: as, b :: bs, i =>
      if a = b then
        firstDifferingPrefixLength as bs (i + 1)
      else
        i + 1

def digitsForDenAux (den : Nat) : Nat -> Nat -> Nat
  | 0, d => d
  | fuel + 1, d =>
      if den <= 10 ^ d then
        d
      else
        digitsForDenAux den fuel (d + 1)

def digitsForDen (den : Nat) : Nat :=
  digitsForDenAux den den 0

def boundedDigitsForDen (budget den : Nat) : Nat :=
  Nat.min budget (digitsForDen den)

def decimalPlacesInPrefixAux : List Char -> Bool -> Nat -> Nat
  | [], _seenDecimal, d => d
  | c :: cs, seenDecimal, d =>
      if c = '.' then
        decimalPlacesInPrefixAux cs true d
      else if seenDecimal then
        decimalPlacesInPrefixAux cs true (d + 1)
      else
        decimalPlacesInPrefixAux cs false d

def decimalPlacesInPrefix (s : String) (n : Nat) : Nat :=
  decimalPlacesInPrefixAux (s.toList.take n) false 0

def endpointDisplayDigits (lo hi : Rat) : Nat :=
  let width := hi - lo
  let highDigits := digitsForDen width.den
  let lower := ratDecimal highDigits lo
  let upper := ratDecimal highDigits hi
  let n := firstDifferingPrefixLength lower.toList upper.toList 0
  Nat.max 2 (decimalPlacesInPrefix lower n + 1)

def endpointDecimalsToFirstDifference (lo hi : Rat) : String × String :=
  let digits := endpointDisplayDigits lo hi
  let lower := ratDecimal digits lo
  let upper := ratDecimal digits hi
  let lower := trimDecimalString lower
  let upper := trimDecimalString upper
  let lower := if lo < 0 && lower = "0" && !decimalExactAt digits lo then "-0" else lower
  let upper := if hi < 0 && upper = "0" && !decimalExactAt digits hi then "-0" else upper
  let lower :=
    if decimalExactAt digits lo then lower else ensureDecimalPoint lower ++ "..."
  let upper :=
    if decimalExactAt digits hi then upper else ensureDecimalPoint upper ++ "..."
  (lower, upper)

def digitString (d : Nat) : String := toString d

def digitsString : List Nat -> String
  | [] => ""
  | d :: ds => digitString d ++ digitsString ds

def findRemainder (r : Nat) : List Nat -> Nat -> Option Nat
  | [], _ => none
  | s :: seen, i =>
      if r = s then
        some i
      else
        findRemainder r seen (i + 1)

def repeatingFractionAux (den : Nat) : Nat -> Nat -> List Nat -> List Nat -> String
  | 0, _rem, _seen, digits => digitsString digits ++ "..."
  | fuel + 1, rem, seen, digits =>
      if rem = 0 then
        digitsString digits
      else
        match findRemainder rem seen 0 with
        | some i =>
            digitsString (digits.take i) ++ "(" ++ digitsString (digits.drop i) ++ ")"
        | none =>
            let rem10 := rem * 10
            let digit := rem10 / den
            let rem' := rem10 % den
            repeatingFractionAux den fuel rem' (seen ++ [rem]) (digits ++ [digit])

def ratRepeatingDecimal (q : Rat) : String :=
  let den := q.den
  let numAbs := q.num.natAbs
  let whole := numAbs / den
  let rem := numAbs % den
  let sign := if q < 0 then "-" else ""
  let frac := repeatingFractionAux den (den + 1) rem [] []
  if frac = "" then
    sign ++ toString whole
  else
    sign ++ toString whole ++ "." ++ frac

def scientificNormalizeAux : Nat -> Rat -> Int -> Rat × Int
  | 0, q, e => (q, e)
  | fuel + 1, q, e =>
      if 10 <= q then
        scientificNormalizeAux fuel (q / 10) (e + 1)
      else if q < 1 then
        scientificNormalizeAux fuel (q * 10) (e - 1)
      else
        (q, e)

def scientificDecimal (q : Rat) : String :=
  if q = 0 then
    "0"
  else
    let qpos := if q < 0 then -q else q
    let normalized := scientificNormalizeAux 10000 qpos 0
    let sign := if q < 0 then "-" else ""
    sign ++ ratDecimalCompact 3 normalized.1 ++ "e" ++ toString normalized.2

def fixedWidthDecimalDigits (exponent : Int) : Nat :=
  if exponent < 0 then
    Int.toNat (-exponent) + 3
  else
    3

def widthDecimal (q : Rat) : String :=
  if q = 0 then
    "0"
  else
    let qpos := if q < 0 then -q else q
    let normalized := scientificNormalizeAux 10000 qpos 0
    if -6 <= normalized.2 && normalized.2 <= 12 then
      ratDecimalCompact (fixedWidthDecimalDigits normalized.2) q
    else
      scientificDecimal q

def display (I : QInterval) : String :=
  if I.lo = I.hi then
    let q := I.lo
    "[" ++ ratRepeatingDecimal q ++ ", " ++ ratRepeatingDecimal q ++ "] width=0"
  else
    let endpoints := endpointDecimalsToFirstDifference I.lo I.hi
    "[" ++ endpoints.1 ++ ", " ++ endpoints.2 ++ "] width=" ++
      widthDecimal I.width

end QInterval

def qabs (x : Rat) : Rat := if x < 0 then -x else x

theorem qabs_nonneg (x : Rat) : 0 <= qabs x := by
  unfold qabs
  by_cases hneg : x < 0
  · simp [hneg]
    grind
  · simp [hneg]
    grind

theorem qabs_pos_of_ne {x : Rat} (hx : Not (x = 0)) :
    0 < qabs x := by
  unfold qabs
  by_cases hneg : x < 0
  · simp [hneg]
    grind
  · simp [hneg]
    grind

theorem qabs_sub_le_of_common_bounds {lo hi a b : Rat}
    (ha_lo : lo <= a) (ha_hi : a <= hi)
    (hb_lo : lo <= b) (hb_hi : b <= hi) :
    qabs (a - b) <= hi - lo := by
  unfold qabs
  by_cases hneg : a - b < 0
  · simp [hneg]
    grind
  · simp [hneg]
    grind

private theorem rat_intCast_eq_divInt_one (num : Int) :
    (num : Rat) = Rat.divInt num (1 : Int) := by
  change (num : Rat) = Rat.divInt num (Int.ofNat 1)
  rw [Rat.divInt.eq_1]
  change Rat.ofInt num = mkRat num 1
  rw [←Rat.normalize_self (Rat.ofInt num)]
  rfl

private theorem rat_natCast_eq_divInt_one (den : Nat) :
    (den : Rat) = Rat.divInt (den : Int) (1 : Int) := by
  rw [←Rat.intCast_natCast den]
  exact rat_intCast_eq_divInt_one (den : Int)

theorem rat_den_mul_self (q : Rat) : (q.den : Rat) * q = (q.num : Rat) := by
  cases q with
  | mk' num den den_nz reduced =>
    change (den : Rat) *
      ({ num := num, den := den, den_nz := den_nz, reduced := reduced } : Rat) = (num : Rat)
    rw [Rat.mk_eq_divInt]
    rw [rat_natCast_eq_divInt_one den, rat_intCast_eq_divInt_one num]
    rw [Rat.divInt_mul_divInt]
    have hdenInt : (den : Int) ≠ 0 := by exact_mod_cast den_nz
    rw [Int.mul_comm (den : Int) num]
    change Rat.divInt (num * (den : Int)) (1 * (den : Int)) = Rat.divInt num 1
    rw [Rat.divInt_mul_right (n := num) (d := 1) hdenInt]

theorem rat_eq_of_den_mul_eq_num {q s : Rat}
    (hs : (q.den : Rat) * s = (q.num : Rat)) :
    s = q := by
  have hdenpos : 0 < (q.den : Rat) :=
    (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
  refine Rat.le_antisymm ?_ ?_
  · apply Rat.le_of_mul_le_mul_right (c := (q.den : Rat))
    · rw [Rat.mul_comm s (q.den : Rat), hs]
      rw [Rat.mul_comm q (q.den : Rat), rat_den_mul_self]
      exact Rat.le_refl
    · exact hdenpos
  · apply Rat.le_of_mul_le_mul_right (c := (q.den : Rat))
    · rw [Rat.mul_comm s (q.den : Rat), hs]
      rw [Rat.mul_comm q (q.den : Rat), rat_den_mul_self]
      exact Rat.le_refl
    · exact hdenpos

theorem rat_num_pos_of_pos {q : Rat} (hq : 0 < q) : 0 < q.num := by
  unfold LT.lt Rat.instLT Rat.blt at hq
  simp at hq
  by_cases hnum : q.num = 0
  · simp [hnum] at hq
  · by_cases hneg : q.num < 0
    · omega
    · omega

def ShrinksToZero (width : Nat -> Rat) : Prop :=
  forall eps : QPos, Exists fun N : Nat =>
    forall n, N <= n -> width n <= eps.val

namespace RealRaw

def WidthsShrinkToZero (compute : Nat -> QInterval) : Prop :=
  forall eps : QPos, Exists fun N : Nat =>
    forall n : Nat, N <= n -> (compute n).width <= eps.val

/-- A raw real algorithm is valid when every stage is an ordered interval,
later stages nest inside earlier stages, and widths tend to zero.  No fixed
speed such as `1/n` is part of this definition. -/
def ValidCompute (compute : Nat -> QInterval) : Prop :=
  (forall n, 0 <= (compute n).width) /\
  (forall n m, n <= m ->
    (compute n).lo <= (compute m).lo /\
    (compute m).lo <= (compute m).hi /\
    (compute m).hi <= (compute n).hi) /\
  WidthsShrinkToZero compute

/-- Optional convergence-rate metadata for a raw interval algorithm.

This is deliberately not another kind of real number. It is just information
attached to a concrete algorithm: eventually the width is bounded either by
`constant / n^power` or by `constant * ratio^n`. `RealRaw` definitions may
leave the rate as `unknown` until a useful bound has been proved. -/
inductive Rate (compute : Nat -> QInterval) where
  | unknown
  | power
      (start : Nat)
      (constant : Rat)
      (power : Nat)
      (power_pos : 0 < power)
      (width_le : forall n : Nat, start <= n ->
        (compute n).width <= constant / (n : Rat) ^ power)
  | geometric
      (start : Nat)
      (constant : Rat)
      (ratio : Rat)
      (ratio_nonneg : 0 <= ratio)
      (ratio_lt_one : ratio < 1)
      (width_le : forall n : Nat, start <= n ->
        (compute n).width <= constant * ratio ^ n)

end RealRaw

/-- Raw interval algorithm for a real number approximation.

At stage `n : Nat`, `compute n` returns two rational endpoints.  A proof of
`RealRaw.ValidCompute compute`, defined just above, says using only rational
inequalities that:

* every interval is ordered;
* later stages are nested inside earlier stages;
* for every positive rational tolerance, all sufficiently late stages have
  width at most that tolerance.

The data here is intentionally tiny: the computation itself plus optional
rate metadata.  Validity is the separate proposition `x.Valid`, so public
algorithms can stay visibly raw while proofs attach the needed certificate. -/
structure RealRaw where
  compute : Nat -> QInterval
  rate : RealRaw.Rate compute := .unknown

namespace RealRaw

def Valid (x : RealRaw) : Prop := ValidCompute x.compute

/-- A cofinal schedule of requested stages.

The schedule may skip stages, but it must move monotonically forward and
eventually pass every requested stage. -/
structure StageSchedule where
  stage : Nat -> Nat
  monotone : forall i j, i <= j -> stage i <= stage j
  cofinal : forall target : Nat, Exists fun k : Nat => target <= (stage k)

namespace StageSchedule

def id : StageSchedule where
  stage := fun n => n + 1
  monotone := by
    intro i j hij
    exact Nat.succ_le_succ hij
  cofinal := by
    intro target
    refine ⟨target, ?_⟩
    omega
end StageSchedule

inductive CompareAt where
  | less
  | greater
  | overlap
deriving Repr, DecidableEq

namespace CompareAt

def display : CompareAt -> String
  | .less => "less"
  | .greater => "greater"
  | .overlap => "overlap"

end CompareAt

def compareIntervals (X Y : QInterval) : CompareAt :=
  if X.hi < Y.lo then
    .less
  else if Y.hi < X.lo then
    .greater
  else
    .overlap

theorem compareIntervals_overlap_iff (X Y : QInterval) :
    Iff (compareIntervals X Y = .overlap) (QInterval.Overlaps X Y) := by
  unfold compareIntervals QInterval.Overlaps
  by_cases hxy : X.hi < Y.lo
  case pos =>
    rw [if_pos hxy]
    constructor
    case mp => intro h; cases h
    case mpr => grind
  case neg =>
    rw [if_neg hxy]
    by_cases hyx : Y.hi < X.lo
    case pos =>
      rw [if_pos hyx]
      constructor
      case mp => intro h; cases h
      case mpr => grind
    case neg =>
      rw [if_neg hyx]
      constructor
      case mp => grind
      case mpr => intro _; rfl

def compareAt (x y : RealRaw) (nx : Nat) (ny : Nat := nx) : CompareAt :=
  compareIntervals (x.compute nx) (y.compute ny)

theorem compareAt_overlap_iff (x y : RealRaw) (nx ny : Nat) :
    Iff (compareAt x y nx ny = .overlap)
      (QInterval.Overlaps (x.compute nx) (y.compute ny)) :=
  compareIntervals_overlap_iff (x.compute nx) (y.compute ny)

def SameStageOverlap (x y : RealRaw) : Prop :=
  forall n, compareAt x y n = .overlap

/-- Equality of raw real algorithms.

Two raw representatives are equivalent when their interval computations
overlap at every common stage. Stage schedules are a proof technique rather
than part of the definition. -/
def Equiv (x y : RealRaw) : Prop :=
  x.SameStageOverlap y

/-- Exact order of raw reals, expressed directly through rational interval
approximations.

This is deliberately not the executable interval comparison `compareAt`.
It says that every rational lower approximation to `x` is at most every
rational upper approximation to `y`.  For valid shrinking representatives,
this is the order relation that survives changes of representative and is the
right primitive for exact convexity. -/
def Le (x y : RealRaw) : Prop :=
  forall n m, (x.compute n).lo <= (y.compute m).hi

theorem sameStageOverlap_equiv {x y : RealRaw} :
    x.SameStageOverlap y -> x.Equiv y := by
  intro h
  exact h

def schedule (sigma : StageSchedule) (x : RealRaw) : RealRaw where
  compute := fun n => x.compute (sigma.stage n)


/-- Stronger than `Equiv`: every interval produced by one raw algorithm
overlaps every interval produced by the other, even at different stages. -/
def AllStagesOverlap (x y : RealRaw) : Prop :=
  forall n m, compareAt x y n m = .overlap

theorem allStagesOverlap_equiv {x y : RealRaw} :
    x.AllStagesOverlap y -> x.Equiv y := by
  intro h
  exact sameStageOverlap_equiv (fun n => h n n)

def StrongEquiv (x y : RealRaw) : Prop :=
  x.AllStagesOverlap y /\ x.Valid /\ y.Valid

def decimalAt (x : RealRaw) (digits : Nat) (n : Nat) : String :=
  QInterval.decimal digits (x.compute n)

def displayAt (x : RealRaw) (n : Nat) : String :=
  QInterval.display (x.compute n)

end RealRaw

end ComputableAnalysis

namespace ComputableAnalysis

private theorem rat_lt_trans {a b c : Rat} (hab : a < b) (hbc : b < c) :
    a < c := by
  apply Rat.lt_of_le_of_ne (Rat.le_trans (Rat.le_of_lt hab) (Rat.le_of_lt hbc))
  intro hac
  rw [hac] at hab
  exact Rat.ne_of_lt hbc (Rat.le_antisymm (Rat.le_of_lt hbc) (Rat.le_of_lt hab))

namespace RealRaw

theorem interval_order_of_valid (x : RealRaw) (hx : x.Valid) (n : Nat) :
    (x.compute n).lo <= (x.compute n).hi := by
  have hwidth := hx.1 n
  grind [QInterval.width, Rat.sub_eq_add_neg]

/-- Rebox a shrinking interval algorithm against a verified nested anchor.

At stage `n` this takes the intersection of the first `n + 1` hulls of the
candidate interval and the corresponding anchor interval.  Every operation is
finite rational `min`/`max` arithmetic.  This is useful when a natural
algorithm has a width modulus and stagewise overlap proof, but its own endpoint
monotonicity has not yet been established. -/
def anchorReboxCompute
    (candidate anchor : Nat -> QInterval) : Nat -> QInterval
  | 0 => QInterval.hull (candidate 0) (anchor 0)
  | n + 1 => QInterval.intersection
      (anchorReboxCompute candidate anchor n)
      (QInterval.hull (candidate (n + 1)) (anchor (n + 1)))

def anchorRebox (candidate anchor : RealRaw) : RealRaw where
  compute := anchorReboxCompute candidate.compute anchor.compute

private theorem anchorReboxCompute_contains_anchor
    {candidate anchor : Nat -> QInterval}
    (hanchor_nested : forall n m, n <= m ->
      (anchor n).lo <= (anchor m).lo /\
        (anchor m).lo <= (anchor m).hi /\
        (anchor m).hi <= (anchor n).hi) :
    forall n, (anchorReboxCompute candidate anchor n).ContainsInterval (anchor n) := by
  intro n
  induction n with
  | zero =>
      exact QInterval.hull_contains_right (candidate 0) (anchor 0)
  | succ n ih =>
      apply QInterval.intersection_contains
      · have hnested := hanchor_nested n (n + 1) (Nat.le_succ n)
        exact ⟨Rat.le_trans ih.1 hnested.1,
          Rat.le_trans hnested.2.2 ih.2⟩
      · exact QInterval.hull_contains_right
          (candidate (n + 1)) (anchor (n + 1))

private theorem anchorReboxCompute_contained_in_current_hull
    (candidate anchor : Nat -> QInterval) :
    forall n, (QInterval.hull (candidate n) (anchor n)).ContainsInterval
      (anchorReboxCompute candidate anchor n) := by
  intro n
  induction n with
  | zero =>
      exact ⟨Rat.le_refl, Rat.le_refl⟩
  | succ n _ih =>
      exact QInterval.intersection_contained_right
        (anchorReboxCompute candidate anchor n)
        (QInterval.hull (candidate (n + 1)) (anchor (n + 1)))

private theorem anchorReboxCompute_step_nested
    (candidate anchor : Nat -> QInterval) (n : Nat) :
    (anchorReboxCompute candidate anchor n).lo <=
        (anchorReboxCompute candidate anchor (n + 1)).lo /\
      (anchorReboxCompute candidate anchor (n + 1)).hi <=
        (anchorReboxCompute candidate anchor n).hi :=
  QInterval.intersection_contained_left
    (anchorReboxCompute candidate anchor n)
    (QInterval.hull (candidate (n + 1)) (anchor (n + 1)))

theorem anchorRebox_contains_anchor
    {candidate anchor : RealRaw}
    (hanchor : anchor.Valid) :
    forall n, (anchorRebox candidate anchor).compute n |>.ContainsInterval
      (anchor.compute n) := by
  exact anchorReboxCompute_contains_anchor hanchor.2.1

theorem anchorRebox_valid
    {candidate anchor : RealRaw}
    (hcandidate_ordered : forall n, 0 <= (candidate.compute n).width)
    (hcandidate_shrinks : WidthsShrinkToZero candidate.compute)
    (hanchor : anchor.Valid)
    (hover : candidate.Equiv anchor) :
    (anchorRebox candidate anchor).Valid := by
  have hcontains := anchorRebox_contains_anchor (candidate := candidate)
    (anchor := anchor) hanchor
  have hcurrent := anchorReboxCompute_contained_in_current_hull
    candidate.compute anchor.compute
  have hstep := anchorReboxCompute_step_nested
    candidate.compute anchor.compute
  constructor
  · intro n
    have hanchor_ordered := interval_order_of_valid anchor hanchor n
    have hcontain := hcontains n
    unfold QInterval.ContainsInterval at hcontain
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      induction hnm with
      | refl =>
          have hordered := interval_order_of_valid anchor hanchor n
          have hcontain := hcontains n
          unfold QInterval.ContainsInterval at hcontain
          exact ⟨Rat.le_refl, by
            have hleft :
                ((anchorRebox candidate anchor).compute n).lo <=
                  ((anchorRebox candidate anchor).compute n).hi := by
              change ((anchorRebox candidate anchor).compute n).lo <=
                (anchor.compute n).lo /\
                (anchor.compute n).hi <=
                  ((anchorRebox candidate anchor).compute n).hi at hcontain
              exact Rat.le_trans hcontain.1
                (Rat.le_trans hordered hcontain.2)
            exact ⟨hleft, Rat.le_refl⟩⟩
      | step hnm ih =>
          rename_i k
          have hnext := hstep k
          have hordered := interval_order_of_valid anchor hanchor (k + 1)
          have hcontain := hcontains (k + 1)
          have hnext_ordered :
                ((anchorRebox candidate anchor).compute (k + 1)).lo <=
                ((anchorRebox candidate anchor).compute (k + 1)).hi := by
            change ((anchorRebox candidate anchor).compute (k + 1)).lo <=
              (anchor.compute (k + 1)).lo /\
              (anchor.compute (k + 1)).hi <=
                ((anchorRebox candidate anchor).compute (k + 1)).hi at hcontain
            exact Rat.le_trans hcontain.1
              (Rat.le_trans hordered hcontain.2)
          exact ⟨Rat.le_trans ih.1 hnext.1,
            ⟨hnext_ordered, Rat.le_trans hnext.2 ih.2.2⟩⟩
    · intro eps
      let half : QPos := ⟨eps.val / 2, by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))⟩
      obtain ⟨Nc, hNc⟩ := hcandidate_shrinks half
      obtain ⟨Na, hNa⟩ := hanchor.2.2 half
      refine ⟨Nat.max Nc Na, ?_⟩
      intro n hn
      have hcn : Nc <= n := Nat.le_trans (Nat.le_max_left _ _) hn
      have han : Na <= n := Nat.le_trans (Nat.le_max_right _ _) hn
      have hcandidate_width := hNc n hcn
      have hanchor_width := hNa n han
      have hcurrent_n := hcurrent n
      have hcurrent_width :
          ((anchorRebox candidate anchor).compute n).width <=
            (QInterval.hull (candidate.compute n) (anchor.compute n)).width := by
        exact QInterval.width_le_of_contains hcurrent_n
      have hhulled_width :
          (QInterval.hull (candidate.compute n) (anchor.compute n)).width <=
            (candidate.compute n).width + (anchor.compute n).width := by
        have hover_n := (compareAt_overlap_iff candidate anchor n n).1 (hover n)
        exact QInterval.hull_width_le_add_of_overlaps
          (hcandidate_ordered n) (hanchor.1 n) hover_n
      change ((anchorRebox candidate anchor).compute n).width <= eps.val
      calc
        ((anchorRebox candidate anchor).compute n).width <=
            (QInterval.hull (candidate.compute n) (anchor.compute n)).width :=
          hcurrent_width
        _ <= (candidate.compute n).width + (anchor.compute n).width :=
          hhulled_width
        _ <= half.val + half.val :=
          by grind
        _ = eps.val := by
          dsimp [half]
          rw [Rat.div_def]
          grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem anchorRebox_equiv_anchor
    {candidate anchor : RealRaw}
    (hanchor : anchor.Valid) :
    (anchorRebox candidate anchor).Equiv anchor := by
  intro n
  apply (compareAt_overlap_iff (anchorRebox candidate anchor) anchor n n).2
  have hcontain := anchorRebox_contains_anchor (candidate := candidate)
    (anchor := anchor) hanchor n
  have hordered := interval_order_of_valid anchor hanchor n
  exact ⟨Rat.le_trans hcontain.1 hordered,
    Rat.le_trans hordered hcontain.2⟩

theorem candidate_equiv_anchorRebox
    {candidate anchor : RealRaw}
    (hanchor : anchor.Valid)
    (hover : candidate.Equiv anchor) :
    candidate.Equiv (anchorRebox candidate anchor) := by
  intro n
  have hcandidate_anchor :=
    (compareAt_overlap_iff candidate anchor n n).1 (hover n)
  have hcontains := anchorRebox_contains_anchor (candidate := candidate)
    (anchor := anchor) hanchor n
  apply (compareAt_overlap_iff candidate (anchorRebox candidate anchor) n n).2
  exact ⟨Rat.le_trans hcandidate_anchor.1 hcontains.2,
    Rat.le_trans hcontains.1 hcandidate_anchor.2⟩

theorem validCompute_stage_eq_of_zero_width
    {compute : Nat -> QInterval}
    (hvalid : RealRaw.ValidCompute compute)
    (hzero : forall n, (compute n).width = 0)
    (n m : Nat) :
    compute n = compute m := by
  have hpoint : forall k, (compute k).lo = (compute k).hi := by
    intro k
    have hwidth := hzero k
    have hordered : (compute k).lo <= (compute k).hi := by
      have hnonneg := hvalid.1 k
      grind [QInterval.width, Rat.sub_eq_add_neg]
    exact Rat.le_antisymm hordered (by
      grind [QInterval.width, Rat.sub_eq_add_neg])
  rcases Nat.le_total n m with hnm | hmn
  · have hnest := hvalid.2.1 n m hnm
    have hlo : (compute n).lo = (compute m).lo := by
      exact Rat.le_antisymm hnest.1 (by
        have hn := hpoint n
        have hm := hpoint m
        grind)
    have hhi : (compute n).hi = (compute m).hi := by
      have hn := hpoint n
      have hm := hpoint m
      grind
    cases hnI : compute n
    cases hmI : compute m
    simp [hnI, hmI] at hlo hhi ⊢
    exact ⟨hlo, hhi⟩
  · have hnest := hvalid.2.1 m n hmn
    have hlo : (compute n).lo = (compute m).lo := by
      exact Rat.le_antisymm (by
        have hn := hpoint n
        have hm := hpoint m
        grind) hnest.1
    have hhi : (compute n).hi = (compute m).hi := by
      have hn := hpoint n
      have hm := hpoint m
      grind
    cases hnI : compute n
    cases hmI : compute m
    simp [hnI, hmI] at hlo hhi ⊢
    exact ⟨hlo, hhi⟩

theorem stage_eq_of_valid_zero_width
    (x : RealRaw) (hx : x.Valid)
    (hzero : forall n, (x.compute n).width = 0)
    (n m : Nat) :
    x.compute n = x.compute m :=
  validCompute_stage_eq_of_zero_width hx hzero n m

theorem sameStageOverlap_refl (x : RealRaw) (hx : x.Valid) :
    x.SameStageOverlap x := by
  intro n
  have h := interval_order_of_valid x hx n
  exact (compareAt_overlap_iff x x n n).2 ⟨h, h⟩

theorem equiv_refl (x : RealRaw) (hx : x.Valid) : x.Equiv x :=
  sameStageOverlap_equiv (sameStageOverlap_refl x hx)

theorem equiv_symm {x y : RealRaw} : x.Equiv y -> y.Equiv x := by
  intro h n
  have hover := (compareAt_overlap_iff x y n n).1 (h n)
  exact (compareAt_overlap_iff y x n n).2 ⟨hover.2, hover.1⟩

theorem allStagesOverlap_refl (x : RealRaw) (hx : x.Valid) :
    x.AllStagesOverlap x := by
  intro n m
  rcases Nat.le_total n m with hnm | hmn
  · have hnest := hx.2.1 n m hnm
    apply (compareAt_overlap_iff x x n m).2
    constructor
    · exact Rat.le_trans hnest.1 hnest.2.1
    · exact Rat.le_trans hnest.2.1 hnest.2.2
  · have hnest := hx.2.1 m n hmn
    apply (compareAt_overlap_iff x x n m).2
    constructor
    · exact Rat.le_trans hnest.2.1 hnest.2.2
    · exact Rat.le_trans hnest.1 hnest.2.1

theorem schedule_valid (x : RealRaw) (hx : x.Valid)
    (sigma : StageSchedule) :
    (schedule sigma x).Valid := by
  constructor
  · intro n
    exact hx.1 (sigma.stage n)
  · constructor
    · intro n m hnm
      exact hx.2.1 (sigma.stage n) (sigma.stage m)
        (sigma.monotone n m hnm)
    · intro eps
      obtain ⟨N, hN⟩ := hx.2.2 eps
      obtain ⟨k, hk⟩ := sigma.cofinal N
      refine ⟨k, ?_⟩
      intro n hkn
      exact hN (sigma.stage n)
        (Nat.le_trans hk (sigma.monotone k n hkn))

theorem schedule_equiv (x : RealRaw) (hx : x.Valid)
    (sigma : StageSchedule) :
    x.Equiv (schedule sigma x) := by
  intro n
  exact allStagesOverlap_refl x hx n (sigma.stage n)

theorem allStagesOverlap_symm {x y : RealRaw} :
    x.AllStagesOverlap y -> y.AllStagesOverlap x := by
  intro h n m
  have hover := (compareAt_overlap_iff x y m n).1 (h m n)
  exact (compareAt_overlap_iff y x n m).2 ⟨hover.2, hover.1⟩

theorem strongEquiv_refl (x : RealRaw) (hx : x.Valid) : x.StrongEquiv x :=
  ⟨allStagesOverlap_refl x hx, hx, hx⟩

theorem strongEquiv_symm {x y : RealRaw} :
    x.StrongEquiv y -> y.StrongEquiv x := by
  intro h
  exact ⟨allStagesOverlap_symm h.1, h.2.2, h.2.1⟩

/-- Unfold equivalence back to the same-stage overlap predicate. -/
theorem sameStageOverlap_of_equiv {x y : RealRaw}
    (_hx : x.Valid) (_hy : y.Valid) :
    x.Equiv y -> x.SameStageOverlap y := by
  intro hxy
  exact hxy

theorem allStagesOverlap_of_sameStageOverlap {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) :
    x.SameStageOverlap y -> x.AllStagesOverlap y := by
  intro hxy n m
  rcases Nat.le_total n m with hnm | hmn
  · have hxnest := hx.2.1 n m hnm
    have hxy_m := (compareAt_overlap_iff x y m m).1 (hxy m)
    apply (compareAt_overlap_iff x y n m).2
    constructor
    · exact Rat.le_trans hxnest.1 hxy_m.1
    · exact Rat.le_trans hxy_m.2 hxnest.2.2
  · have hynest := hy.2.1 m n hmn
    have hxy_n := (compareAt_overlap_iff x y n n).1 (hxy n)
    apply (compareAt_overlap_iff x y n m).2
    constructor
    · exact Rat.le_trans hxy_n.1 hynest.2.2
    · exact Rat.le_trans hynest.1 hxy_n.2

/-- For certified/nested raw algorithms, same-stage equivalence implies
all-stages overlap. -/
theorem allStagesOverlap_of_equiv {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) :
    x.Equiv y -> x.AllStagesOverlap y :=
  fun hxy => allStagesOverlap_of_sameStageOverlap hx hy
    (sameStageOverlap_of_equiv hx hy hxy)

theorem equiv_iff_allStagesOverlap {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) :
    x.Equiv y ↔ x.AllStagesOverlap y :=
  ⟨allStagesOverlap_of_equiv hx hy, RealRaw.allStagesOverlap_equiv⟩

theorem le_refl (x : RealRaw) (hx : x.Valid) : x.Le x := by
  intro n m
  have hover := (compareAt_overlap_iff x x n m).1
    (allStagesOverlap_refl x hx n m)
  exact hover.1

theorem le_of_equiv {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) :
    x.Equiv y -> x.Le y := by
  intro hxy n m
  have hall := allStagesOverlap_of_equiv hx hy hxy
  have hover := (compareAt_overlap_iff x y n m).1 (hall n m)
  exact hover.1

theorem equiv_of_le_of_ge {x y : RealRaw}
    (hxy : x.Le y) (hyx : y.Le x) :
    x.Equiv y := by
  intro n
  apply (compareAt_overlap_iff x y n n).2
  exact ⟨hxy n n, hyx n n⟩

theorem equiv_iff_le_and_ge {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) :
    x.Equiv y ↔ x.Le y /\ y.Le x := by
  constructor
  · intro hxy
    exact ⟨le_of_equiv hx hy hxy, le_of_equiv hy hx (equiv_symm hxy)⟩
  · intro h
    exact equiv_of_le_of_ge h.1 h.2

theorem le_trans {x y z : RealRaw}
    (hy : y.Valid) :
    x.Le y -> y.Le z -> x.Le z := by
  intro hxy hyz n m
  by_cases hgood : (x.compute n).lo <= (z.compute m).hi
  · exact hgood
  · exfalso
    have hgap : 0 < (x.compute n).lo - (z.compute m).hi := by
      rw [←Rat.lt_iff_sub_pos]
      simpa [Rat.not_le] using hgood
    have htwo : (0 : Rat) < 2 := by
      exact (Rat.natCast_pos).2 (by omega : 0 < (2 : Nat))
    have hgapHalfPos : 0 < ((x.compute n).lo - (z.compute m).hi) / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap ((Rat.inv_pos).2 htwo)
    obtain ⟨k, hk⟩ := hy.2.2
      { val := ((x.compute n).lo - (z.compute m).hi) / 2,
        property := hgapHalfPos }
    have hxyk := hxy n k
    have hyzk := hyz k m
    have hsmall :
        (y.compute k).width <=
          ((x.compute n).lo - (z.compute m).hi) / 2 :=
      hk k (Nat.le_refl k)
    have hgap_le_width :
        (x.compute n).lo - (z.compute m).hi <= (y.compute k).width := by
      grind [QInterval.width, Rat.sub_eq_add_neg]
    have hhalf_lt :
        ((x.compute n).lo - (z.compute m).hi) / 2 <
          (x.compute n).lo - (z.compute m).hi := by
      rw [Rat.div_lt_iff htwo]
      grind
    have hgap_le_half :
        (x.compute n).lo - (z.compute m).hi <=
          ((x.compute n).lo - (z.compute m).hi) / 2 :=
      Rat.le_trans hgap_le_width hsmall
    have hne :
        (x.compute n).lo - (z.compute m).hi ≠
      ((x.compute n).lo - (z.compute m).hi) / 2 := by
      intro heq
      rw [←heq] at hhalf_lt
      exact Rat.lt_irrefl hhalf_lt
    have hgap_lt_half :
        (x.compute n).lo - (z.compute m).hi <
          ((x.compute n).lo - (z.compute m).hi) / 2 :=
      Rat.lt_of_le_of_ne hgap_le_half hne
    exact Rat.lt_irrefl (rat_lt_trans hgap_lt_half hhalf_lt)

private theorem equiv_trans_left {x y z : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid)
    (hxy : x.SameStageOverlap y) (hyz : y.SameStageOverlap z)
    (n : Nat) : (x.compute n).lo <= (z.compute n).hi := by
  by_cases hgood : (x.compute n).lo <= (z.compute n).hi
  · exact hgood
  · exfalso
    have hgap : 0 < (x.compute n).lo - (z.compute n).hi := by
      rw [←Rat.lt_iff_sub_pos]
      simpa [Rat.not_le] using hgood
    have hthree : (0 : Rat) < 3 := by
      exact (Rat.natCast_pos).2 (by omega : 0 < (3 : Nat))
    have hgapThirdPos : 0 < ((x.compute n).lo - (z.compute n).hi) / 3 := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap ((Rat.inv_pos).2 hthree)
    obtain ⟨M, hsmall⟩ := hy.2.2
      { val := ((x.compute n).lo - (z.compute n).hi) / 3,
        property := hgapThirdPos }
    let m : Nat := max n M
    have hnm : n <= m := by
      dsimp [m]
      exact Nat.le_max_left n M
    have hMle : M <= m := by
      dsimp [m]
      exact Nat.le_max_right n M
    have hxNest := hx.2.1 n m hnm
    have hzNest := hz.2.1 n m hnm
    have hxyM := (compareAt_overlap_iff x y m m).1 (hxy m)
    have hyzM := (compareAt_overlap_iff y z m m).1 (hyz m)
    have hySmallLe :
        (y.compute m).width <= ((x.compute n).lo - (z.compute n).hi) / 3 :=
      hsmall m hMle
    have hyGapLe :
        (x.compute n).lo - (z.compute n).hi <= (y.compute m).width := by
      grind [QInterval.width, QInterval.Overlaps]
    have hthirdLt : ((x.compute n).lo - (z.compute n).hi) / 3 <
        (x.compute n).lo - (z.compute n).hi := by
      rw [Rat.div_lt_iff hthree]
      grind
    have hgapLeThird : (x.compute n).lo - (z.compute n).hi <=
        ((x.compute n).lo - (z.compute n).hi) / 3 :=
      Rat.le_trans hyGapLe hySmallLe
    have hgapLtThird : (x.compute n).lo - (z.compute n).hi <
        ((x.compute n).lo - (z.compute n).hi) / 3 :=
      Rat.lt_of_le_of_ne hgapLeThird (Rat.ne_of_gt hthirdLt)
    exact Rat.lt_irrefl (rat_lt_trans hgapLtThird hthirdLt)

theorem equiv_trans {x y z : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    x.Equiv y -> y.Equiv z -> x.Equiv z := by
  intro hxy hyz
  have hxySame := sameStageOverlap_of_equiv hx hy hxy
  have hyzSame := sameStageOverlap_of_equiv hy hz hyz
  apply sameStageOverlap_equiv
  intro n
  apply (compareAt_overlap_iff x z n n).2
  constructor
  · exact equiv_trans_left hx hy hz hxySame hyzSame n
  · exact equiv_trans_left hz hy hx
      (sameStageOverlap_of_equiv hz hy (equiv_symm hyz))
      (sameStageOverlap_of_equiv hy hx (equiv_symm hxy)) n

theorem equiv_of_schedule_equiv {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid)
    (sigma tau : StageSchedule) :
    (schedule sigma x).Equiv (schedule tau y) -> x.Equiv y := by
  intro hscheduled
  have hsx : (schedule sigma x).Valid := schedule_valid x hx sigma
  have hty : (schedule tau y).Valid := schedule_valid y hy tau
  exact equiv_trans hx hsx hy
    (schedule_equiv x hx sigma)
    (equiv_trans hsx hty hy hscheduled
      (equiv_symm (schedule_equiv y hy tau)))

end RealRaw

end ComputableAnalysis

namespace ComputableAnalysis

private theorem rat_sub_self (q : Rat) : q - q = 0 := by
  cases q
  simp [Rat.sub_def]

namespace RealRaw

theorem ofRat_valid (q : Rat) : ValidCompute (fun _ : Nat => { lo := q, hi := q }) := by
  constructor
  · intro n
    show 0 <= q - q
    rw [rat_sub_self]
    exact Rat.le_refl
  · constructor
    · intro n m h
      simp
    · intro eps
      exact ⟨0, by
        intro n _hn
        show q - q <= eps.val
        rw [rat_sub_self]
        exact Rat.le_of_lt eps.property⟩

def ofRat (q : Rat) : RealRaw where
  compute := fun _ => { lo := q, hi := q }

instance : Coe Rat RealRaw where
  coe := ofRat

instance (n : Nat) : OfNat RealRaw n where
  ofNat := ofRat n

@[simp]
theorem ofRat_compute (q : Rat) (n : Nat) :
    (ofRat q).compute n = { lo := q, hi := q } := rfl

@[simp]
theorem coe_rat_compute (q : Rat) (n : Nat) :
    ((q : RealRaw).compute n) = { lo := q, hi := q } := rfl

theorem ofRat_equiv_self (q : Rat) : (ofRat q).Equiv (ofRat q) :=
  equiv_refl (ofRat q) (ofRat_valid q)

/-- A raw computable real is irrational when it is not equivalent to any
rational coercion.  This is most useful for valid raw algorithms, where
`Equiv` has the expected same-stage and transitive behavior. -/
def Irrational (x : RealRaw) : Prop :=
  forall q : Rat, ¬ x.Equiv (ofRat q)

def interval (x : RealRaw) (n : Nat) : QInterval := x.compute n
def midpoint (x : RealRaw) (n : Nat) : Rat := (x.compute n).midpoint

end RealRaw

/-- A certified handle for a defined real number.

This is the concrete project-facing layer above `RealRaw`: it records a chosen
valid raw algorithm, together with any alternative raw algorithms already proved
valid and equivalent to it.  The structure keeps computation first-class while
still tracking the equivalence class it is meant to represent.
-/
structure Real where
  preferred : RealRaw
  valid : preferred.Valid
  alternatives : List RealRaw := []
  alternative_valid : forall rep, List.Mem rep alternatives -> rep.Valid := by
    intro rep h
    cases h
  coherent : forall rep, List.Mem rep alternatives -> rep.Equiv preferred := by
    intro rep h
    cases h

namespace Real

def ofRaw (x : RealRaw) (h : x.Valid) : Real where
  preferred := x
  valid := h
  alternatives := []
  alternative_valid := by
    intro rep hrep
    cases hrep
  coherent := by
    intro rep hrep
    cases hrep

def ofRat (q : Rat) : Real :=
  ofRaw (RealRaw.ofRat q) (RealRaw.ofRat_valid q)

def compute (x : Real) (n : Nat) : QInterval :=
  x.preferred.compute n

def rate (x : Real) : RealRaw.Rate x.preferred.compute :=
  x.preferred.rate

def representations (x : Real) : List RealRaw :=
  x.preferred :: x.alternatives

def withAlternative (x : Real) (rep : RealRaw) (hvalid : rep.Valid)
    (h : rep.Equiv x.preferred) : Real where
  preferred := x.preferred
  valid := x.valid
  alternatives := rep :: x.alternatives
  alternative_valid := by
    intro candidate hc
    cases hc with
    | head => exact hvalid
    | tail _ hc => exact x.alternative_valid candidate hc
  coherent := by
    intro candidate hc
    cases hc with
    | head => exact h
    | tail _ hc => exact x.coherent candidate hc

def Equiv (x y : Real) : Prop :=
  x.preferred.Equiv y.preferred

theorem equiv_refl (x : Real) : x.Equiv x :=
  RealRaw.equiv_refl x.preferred x.valid

theorem equiv_symm {x y : Real} : x.Equiv y -> y.Equiv x :=
  RealRaw.equiv_symm

theorem equiv_trans {x y z : Real} : x.Equiv y -> y.Equiv z -> x.Equiv z :=
  RealRaw.equiv_trans x.valid y.valid z.valid

/-- A computable real is rational when it is equivalent to some rational real. -/
def Rational (x : Real) : Prop :=
  Exists fun q : Rat => x.Equiv (ofRat q)

/-- A computable real is irrational when it is not equivalent to any rational
real.  This is the public mathematical notion; the corresponding
`RealRaw.Irrational` predicate is the representative-level helper. -/
def Irrational (x : Real) : Prop :=
  forall q : Rat, ¬ x.Equiv (ofRat q)

theorem irrational_iff_preferred_irrational (x : Real) :
    x.Irrational ↔ x.preferred.Irrational :=
  Iff.rfl

structure Representation (x : Real) where
  raw : RealRaw
  valid : raw.Valid
  agrees : raw.Equiv x.preferred

def preferredRepresentation (x : Real) : Representation x where
  raw := x.preferred
  valid := x.valid
  agrees := RealRaw.equiv_refl x.preferred x.valid

def alternativeRepresentation {x : Real} (rep : RealRaw)
    (h : List.Mem rep x.alternatives) : Representation x where
  raw := rep
  valid := x.alternative_valid rep h
  agrees := x.coherent rep h

def computeUsing {x : Real} (rep : Representation x) (n : Nat) : QInterval :=
  rep.raw.compute n

theorem representation_same_real {x : Real} (rep : Representation x) :
    (Real.ofRaw rep.raw rep.valid).Equiv x :=
  rep.agrees

end Real

/-- Raw real-valued function on rational inputs.

A single-variable function representation is a domain together with a stage
algorithm `x, n ↦ [a, b]`.  Validity is pointwise: for each fixed rational
`x` in the domain, the sequence in `n` is a raw real.

The computation field remains total on rationals so existing total-function
machinery can use it directly.  The attached domain records where the
representation is intended to be interpreted, and the optional rate metadata
may depend on a proof that the input lies in that domain.
-/
structure RealFunRaw where
  domain : Rat -> Prop := fun _ => True
  compute : Rat -> Nat -> QInterval
  rate : (x : Rat) -> domain x -> RealRaw.Rate (compute x) := fun _ _ => .unknown

namespace RealFunRaw

def entire : Rat -> Prop := fun _ => True

def applyCompute (f : RealFunRaw) (x : Rat) : Nat -> QInterval :=
  f.compute x

def exact (f : Rat -> Rat) : RealFunRaw where
  domain := entire
  compute := fun x _ => { lo := f x, hi := f x }

def Valid (f : RealFunRaw) : Prop :=
  forall x, f.domain x -> RealRaw.ValidCompute (applyCompute f x)

theorem exact_valid (f : Rat -> Rat) : (exact f).Valid := by
  intro x _hx
  exact RealRaw.ofRat_valid (f x)

theorem validAt {f : RealFunRaw} (h : f.Valid)
    {x : Rat} (hx : f.domain x) :
    RealRaw.ValidCompute (f.applyCompute x) :=
  h x hx

def apply (f : RealFunRaw) (_h : f.Valid) (x : Rat) (hx : f.domain x) : RealRaw where
  compute := applyCompute f x
  rate := f.rate x hx

end RealFunRaw

structure RealFunCert where
  raw : RealFunRaw
  valid : raw.Valid

/-- A partial rational-input real-valued function.

This is the proof-relevant version of the same `x, n ↦ [a, b]` notion: the
computation is only available together with a proof that the input is in the
domain, so undefined points cannot be assigned placeholder values.  Validity is
again pointwise in the input.
-/
structure PartialRealFunRaw where
  definedAt : Rat -> Prop
  compute : (x : Rat) -> definedAt x -> Nat -> QInterval
  rate :
    (x : Rat) -> (h : definedAt x) ->
      RealRaw.Rate (compute x h) := fun _ _ => .unknown

namespace PartialRealFunRaw

def evalRaw (f : PartialRealFunRaw)
    (x : Rat) (h : f.definedAt x) : RealRaw where
  compute := f.compute x h
  rate := f.rate x h

/-- Two partial rational-input real functions agree where both are defined.

This is the function-representation version of raw-real equality: at each
rational input in the common domain, the two output interval algorithms are
equivalent.  We do not make this a global equivalence relation, because
different representations may have different natural domains. -/
def AgreeOnOverlap (f g : PartialRealFunRaw) : Prop :=
  forall x hx hg, (f.evalRaw x hx).Equiv (g.evalRaw x hg)

def AgreeOnOverlapAllStages (f g : PartialRealFunRaw) : Prop :=
  forall x hx hg, (f.evalRaw x hx).AllStagesOverlap (g.evalRaw x hg)

theorem agreeOnOverlap_of_allStages {f g : PartialRealFunRaw} :
    f.AgreeOnOverlapAllStages g -> f.AgreeOnOverlap g := by
  intro h x hx hg
  exact RealRaw.allStagesOverlap_equiv (h x hx hg)
def apply (f : PartialRealFunRaw)
    (_validOnDomain : forall x h, RealRaw.ValidCompute (f.compute x h))
    (x : Rat) (h : f.definedAt x) : RealRaw where
  compute := f.compute x h
  rate := f.rate x h

def eval? (f : PartialRealFunRaw) (decideDomain : (x : Rat) -> Decidable (f.definedAt x))
    (x : Rat) (n : Nat) : Option QInterval :=
  haveI := decideDomain x
  if h : f.definedAt x then some (f.compute x h n) else none

end PartialRealFunRaw

structure EffectiveContinuous (f : RealFunRaw) where
  inputRadius : Nat -> QPos
  good : forall x y n,
    qabs (y - x) <= (inputRadius n).val ->
    qabs ((f.compute y n).midpoint - (f.compute x n).midpoint) <= (1 / (n : Rat))

structure EffectiveDerivativeExact (f g : Rat -> Rat) where
  stepRadius : QPos -> QPos
  good : forall x h eps,
    0 < h -> h <= (stepRadius eps).val ->
    qabs (((f (x + h) - f x) / h) - g x) <= eps.val

end ComputableAnalysis

namespace ComputableAnalysis

structure QComplex where
  re : Rat
  im : Rat
deriving Repr, DecidableEq

namespace QComplex

/-- Coordinatewise order on rational complex points.  This is a bookkeeping
order for rectangular boxes, not the field order of a number system. -/
instance : LE QComplex where
  le z w := z.re <= w.re /\ z.im <= w.im

@[simp] theorem le_def (z w : QComplex) :
    z <= w ↔ z.re <= w.re /\ z.im <= w.im := Iff.rfl

theorem le_refl (z : QComplex) : z <= z :=
  ⟨Rat.le_refl, Rat.le_refl⟩

instance decidableLE (z w : QComplex) : Decidable (z <= w) := by
  change Decidable (z.re <= w.re /\ z.im <= w.im)
  infer_instance

theorem le_trans {z w u : QComplex} (hzw : z <= w) (hwu : w <= u) : z <= u :=
  ⟨Rat.le_trans hzw.1 hwu.1, Rat.le_trans hzw.2 hwu.2⟩

theorem le_antisymm {z w : QComplex} (hzw : z <= w) (hwz : w <= z) : z = w := by
  cases z
  cases w
  simp at hzw hwz ⊢
  exact ⟨Rat.le_antisymm hzw.1 hwz.1, Rat.le_antisymm hzw.2 hwz.2⟩

def ofRat (q : Rat) : QComplex := { re := q, im := 0 }
def zero : QComplex := { re := 0, im := 0 }
def one : QComplex := { re := 1, im := 0 }
def add (z w : QComplex) : QComplex := { re := z.re + w.re, im := z.im + w.im }
def neg (z : QComplex) : QComplex := { re := -z.re, im := -z.im }
def sub (z w : QComplex) : QComplex := add z (neg w)
def scaleRat (r : Rat) (z : QComplex) : QComplex :=
  { re := r * z.re, im := r * z.im }
def mul (z w : QComplex) : QComplex := { re := z.re * w.re - z.im * w.im, im := z.re * w.im + z.im * w.re }
def coordDist (z w : QComplex) : Rat := max (qabs (z.re - w.re)) (qabs (z.im - w.im))
def normSq (z : QComplex) : Rat := z.re * z.re + z.im * z.im
def inv? (z : QComplex) : Option QComplex :=
  let n := normSq z
  if n = 0 then
    none
  else
    some { re := z.re / n, im := -z.im / n }
def div? (z w : QComplex) : Option QComplex := (inv? w).map (mul z)

instance : OfNat QComplex n where
  ofNat := ofRat n

instance : HAdd QComplex QComplex QComplex where
  hAdd := add

instance : Neg QComplex where
  neg := neg

instance : HSub QComplex QComplex QComplex where
  hSub := sub

instance : HMul QComplex QComplex QComplex where
  hMul := mul

end QComplex

structure QBox where
  lo : QComplex
  hi : QComplex
deriving Repr, DecidableEq

namespace QBox

def width (B : QBox) : Rat := B.hi.re - B.lo.re
def height (B : QBox) : Rat := B.hi.im - B.lo.im
def center (B : QBox) : QComplex := { re := (B.lo.re + B.hi.re) / 2, im := (B.lo.im + B.hi.im) / 2 }

/-- A rational box is ordered when its lower endpoint is below its upper
endpoint in the coordinatewise order on rational complex points. -/
def Ordered (B : QBox) : Prop := B.lo <= B.hi

/-- `inner` is nested in `outer` when both endpoints are contained
coordinatewise. -/
def NestedIn (inner outer : QBox) : Prop :=
  outer.lo <= inner.lo /\ inner.hi <= outer.hi

def Overlaps (A B : QBox) : Prop := A.lo <= B.hi /\ B.lo <= A.hi

instance overlapsDecidable (A B : QBox) : Decidable (Overlaps A B) := by
  unfold Overlaps
  infer_instance

def overlaps (A B : QBox) : Bool := decide (Overlaps A B)
def widthHeightOk (B : QBox) (eps : QPos) : Bool := decide (0 <= B.width /\ B.width <= eps.val /\ 0 <= B.height /\ B.height <= eps.val)

theorem ordered_iff_width_height_nonneg (B : QBox) :
    B.Ordered ↔ 0 <= B.width /\ 0 <= B.height := by
  unfold Ordered width height
  simp [Rat.sub_eq_add_neg]
  grind

private def displayEndpointStrings (lo hi : Rat) : String × String :=
  if lo = hi then
    let s := QInterval.ratRepeatingDecimal lo
    (s, s)
  else
    QInterval.endpointDecimalsToFirstDifference lo hi

private def displayHasLeadingMinus (s : String) : Bool :=
  match s.toList with
  | '-' :: _ => true
  | _ => false

private def displayStripLeadingMinus (s : String) : String :=
  match s.toList with
  | '-' :: chars => String.ofList chars
  | _ => s

private def displaySignedImag (s : String) : String :=
  if displayHasLeadingMinus s then
    " - i " ++ displayStripLeadingMinus s
  else
    " + i " ++ s

private def displayComplexFromStrings (re im : String) : String :=
  re ++ displaySignedImag im

def display (B : QBox) : String :=
  let re := displayEndpointStrings B.lo.re B.hi.re
  let im := displayEndpointStrings B.lo.im B.hi.im
  let lo := displayComplexFromStrings re.1 im.1
  let hi := displayComplexFromStrings re.2 im.2
  let width := displayComplexFromStrings
    (QInterval.widthDecimal B.width) (QInterval.widthDecimal B.height)
  "[" ++ lo ++ ", " ++ hi ++ "] width = " ++ width

end QBox

namespace ComplexRaw

def WidthsShrinkToZero (compute : Nat -> QBox) : Prop :=
  forall eps : QPos, Exists fun N : Nat =>
    forall n : Nat, N <= n ->
      (compute n).width <= eps.val /\ (compute n).height <= eps.val

/-- A raw complex algorithm is valid when every stage is an ordered rational
box, later boxes nest inside earlier boxes, and both coordinate widths tend to
zero.  No fixed speed such as `1/n` is part of this definition. -/
def ValidCompute (compute : Nat -> QBox) : Prop :=
  (forall n, 0 <= (compute n).width /\ 0 <= (compute n).height) /\
  (forall n m, n <= m ->
    (compute n).lo.re <= (compute m).lo.re /\
    (compute m).hi.re <= (compute n).hi.re /\
    (compute n).lo.im <= (compute m).lo.im /\
    (compute m).hi.im <= (compute n).hi.im) /\
  WidthsShrinkToZero compute

/-- Optional convergence-rate metadata for a raw complex-box algorithm.

The bound applies to both coordinate widths.  As for `RealRaw.Rate`, this is
metadata on the algorithm, not a second kind of complex number. -/
inductive Rate (compute : Nat -> QBox) where
  | unknown
  | power
      (start : Nat)
      (constant : Rat)
      (power : Nat)
      (power_pos : 0 < power)
      (width_height_le : forall n : Nat, start <= n ->
        (compute n).width <= constant / (n : Rat) ^ power /\
        (compute n).height <= constant / (n : Rat) ^ power)
  | geometric
      (start : Nat)
      (constant : Rat)
      (ratio : Rat)
      (ratio_nonneg : 0 <= ratio)
      (ratio_lt_one : ratio < 1)
      (width_height_le : forall n : Nat, start <= n ->
        (compute n).width <= constant * ratio ^ n /\
        (compute n).height <= constant * ratio ^ n)

end ComplexRaw

/-- Raw box-sequence algorithm for a complex number. -/
structure ComplexRaw where
  compute : Nat -> QBox
  rate : ComplexRaw.Rate compute := .unknown

namespace ComplexRaw

def Valid (z : ComplexRaw) : Prop := ValidCompute z.compute

theorem valid_ordered {compute : Nat -> QBox}
    (h : ValidCompute compute) (n : Nat) : (compute n).Ordered :=
  (QBox.ordered_iff_width_height_nonneg (compute n)).2 (h.1 n)

theorem valid_nestedIn {compute : Nat -> QBox}
    (h : ValidCompute compute) {n m : Nat} (hnm : n <= m) :
    QBox.NestedIn (compute m) (compute n) := by
  have hnest := h.2.1 n m hnm
  exact ⟨⟨hnest.1, hnest.2.2.1⟩, ⟨hnest.2.1, hnest.2.2.2⟩⟩

structure CompareAt where
  left : Bool
  right : Bool
  below : Bool
  above : Bool
deriving Repr, DecidableEq

namespace CompareAt

def overlap : CompareAt :=
  { left := false, right := false, below := false, above := false }

private def appendDirection (s direction : String) (present : Bool) : String :=
  if present then
    if s = "" then direction else s ++ ", " ++ direction
  else
    s

def directions (c : CompareAt) : String :=
  appendDirection
    (appendDirection
      (appendDirection
        (appendDirection "" "left" c.left)
        "right" c.right)
      "below" c.below)
    "above" c.above

def display (c : CompareAt) : String :=
  if c = overlap then
    "overlap"
  else
    "separated(" ++ directions c ++ ")"

end CompareAt

def compareBoxes (A B : QBox) : CompareAt :=
  { left := decide (A.hi.re < B.lo.re),
    right := decide (B.hi.re < A.lo.re),
    below := decide (A.hi.im < B.lo.im),
    above := decide (B.hi.im < A.lo.im) }

theorem compareBoxes_overlap_iff (A B : QBox) :
    Iff (compareBoxes A B = .overlap) (QBox.Overlaps A B) := by
  unfold compareBoxes QBox.Overlaps
  simp [CompareAt.overlap]
  grind

def compareAt (z w : ComplexRaw) (nz : Nat) (nw : Nat := nz) : CompareAt :=
  compareBoxes (z.compute nz) (w.compute nw)

theorem compareAt_overlap_iff (z w : ComplexRaw) (nz nw : Nat) :
    Iff (compareAt z w nz nw = .overlap)
      (QBox.Overlaps (z.compute nz) (w.compute nw)) :=
  compareBoxes_overlap_iff (z.compute nz) (w.compute nw)

/-- Same-stage overlap of complex-box computations. -/
def SameStageOverlap (z w : ComplexRaw) : Prop :=
  forall n, compareAt z w n = .overlap

/--
Two raw complex representatives are equivalent when their box computations
overlap at every common stage.
-/
def Equiv (z w : ComplexRaw) : Prop :=
  z.SameStageOverlap w

theorem sameStageOverlap_equiv {z w : ComplexRaw} :
    z.SameStageOverlap w -> z.Equiv w := by
  intro h
  exact h

/-- Stronger than `Equiv`: every box of one raw algorithm overlaps every box
of the other, even at different stages. -/
def AllStagesOverlap (z w : ComplexRaw) : Prop :=
  forall n m, compareAt z w n m = .overlap

theorem allStagesOverlap_equiv {z w : ComplexRaw} :
    z.AllStagesOverlap w -> z.Equiv w := by
  intro h
  exact sameStageOverlap_equiv (fun n => h n n)

theorem equiv_refl (z : ComplexRaw) (hz : z.Valid) : z.Equiv z := by
  apply sameStageOverlap_equiv
  intro eps
  have hwidth : 0 <= (z.compute eps).width := (hz.1 eps).1
  have hheight : 0 <= (z.compute eps).height := (hz.1 eps).2
  have hre : (z.compute eps).lo.re <= (z.compute eps).hi.re := by
    unfold QBox.width at hwidth
    grind [Rat.sub_eq_add_neg]
  have him : (z.compute eps).lo.im <= (z.compute eps).hi.im := by
    unfold QBox.height at hheight
    grind [Rat.sub_eq_add_neg]
  exact (compareAt_overlap_iff z z eps eps).2
    ⟨⟨hre, him⟩, ⟨hre, him⟩⟩

theorem equiv_symm {z w : ComplexRaw} : z.Equiv w -> w.Equiv z := by
  intro h n
  have hover := (compareAt_overlap_iff z w n n).1 (h n)
  exact (compareAt_overlap_iff w z n n).2 ⟨hover.2, hover.1⟩

theorem sameStageOverlap_of_equiv {z w : ComplexRaw}
    (_hz : z.Valid) (_hw : w.Valid) :
    z.Equiv w -> z.SameStageOverlap w := by
  intro hzw
  exact hzw

theorem allStagesOverlap_of_sameStageOverlap {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid) :
    z.SameStageOverlap w -> z.AllStagesOverlap w := by
  intro hzw n m
  rcases Nat.le_total n m with hnm | hmn
  · have hznest := hz.2.1 n m hnm
    have hzw_m := (compareAt_overlap_iff z w m m).1 (hzw m)
    apply (compareAt_overlap_iff z w n m).2
    exact ⟨
      ⟨Rat.le_trans hznest.1 hzw_m.1.1,
        Rat.le_trans hznest.2.2.1 hzw_m.1.2⟩,
      ⟨Rat.le_trans hzw_m.2.1 hznest.2.1,
        Rat.le_trans hzw_m.2.2 hznest.2.2.2⟩⟩
  · have hwnest := hw.2.1 m n hmn
    have hzw_n := (compareAt_overlap_iff z w n n).1 (hzw n)
    apply (compareAt_overlap_iff z w n m).2
    exact ⟨
      ⟨Rat.le_trans hzw_n.1.1 hwnest.2.1,
        Rat.le_trans hzw_n.1.2 hwnest.2.2.2⟩,
      ⟨Rat.le_trans hwnest.1 hzw_n.2.1,
        Rat.le_trans hwnest.2.2.1 hzw_n.2.2⟩⟩

theorem allStagesOverlap_of_equiv {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid) :
    z.Equiv w -> z.AllStagesOverlap w :=
  fun hzw => allStagesOverlap_of_sameStageOverlap hz hw
    (sameStageOverlap_of_equiv hz hw hzw)

theorem equiv_iff_allStagesOverlap {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid) :
    z.Equiv w ↔ z.AllStagesOverlap w :=
  ⟨allStagesOverlap_of_equiv hz hw, ComplexRaw.allStagesOverlap_equiv⟩

private theorem equiv_trans_re_left {x y z : ComplexRaw}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid)
    (hxy : x.SameStageOverlap y) (hyz : y.SameStageOverlap z)
    (n : Nat) : (x.compute n).lo.re <= (z.compute n).hi.re := by
  by_cases hgood : (x.compute n).lo.re <= (z.compute n).hi.re
  · exact hgood
  · exfalso
    have hgap : 0 < (x.compute n).lo.re - (z.compute n).hi.re := by
      rw [←Rat.lt_iff_sub_pos]
      simpa [Rat.not_le] using hgood
    have hthree : (0 : Rat) < 3 := by
      exact (Rat.natCast_pos).2 (by omega : 0 < (3 : Nat))
    have hgapThirdPos :
        0 < ((x.compute n).lo.re - (z.compute n).hi.re) / 3 := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap ((Rat.inv_pos).2 hthree)
    obtain ⟨M, hsmall⟩ := hy.2.2
      { val := ((x.compute n).lo.re - (z.compute n).hi.re) / 3,
        property := hgapThirdPos }
    let m : Nat := max n M
    have hnm : n <= m := by
      dsimp [m]
      exact Nat.le_max_left n M
    have hMle : M <= m := by
      dsimp [m]
      exact Nat.le_max_right n M
    have hxNest := hx.2.1 n m hnm
    have hzNest := hz.2.1 n m hnm
    have hxyM := (compareAt_overlap_iff x y m m).1 (hxy m)
    have hyzM := (compareAt_overlap_iff y z m m).1 (hyz m)
    have hySmallLe :
        (y.compute m).width <=
          ((x.compute n).lo.re - (z.compute n).hi.re) / 3 :=
      (hsmall m hMle).1
    have hyGapLe :
        (x.compute n).lo.re - (z.compute n).hi.re <=
          (y.compute m).width := by
      grind [QBox.width, QBox.Overlaps, QComplex.le_def, Rat.sub_eq_add_neg]
    have hthirdLt :
        ((x.compute n).lo.re - (z.compute n).hi.re) / 3 <
          (x.compute n).lo.re - (z.compute n).hi.re := by
      rw [Rat.div_lt_iff hthree]
      grind
    have hgapLeThird :
        (x.compute n).lo.re - (z.compute n).hi.re <=
          ((x.compute n).lo.re - (z.compute n).hi.re) / 3 :=
      Rat.le_trans hyGapLe hySmallLe
    have hgapLtThird :
        (x.compute n).lo.re - (z.compute n).hi.re <
          ((x.compute n).lo.re - (z.compute n).hi.re) / 3 :=
      Rat.lt_of_le_of_ne hgapLeThird (Rat.ne_of_gt hthirdLt)
    exact Rat.lt_irrefl (rat_lt_trans hgapLtThird hthirdLt)

private theorem equiv_trans_im_left {x y z : ComplexRaw}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid)
    (hxy : x.SameStageOverlap y) (hyz : y.SameStageOverlap z)
    (n : Nat) : (x.compute n).lo.im <= (z.compute n).hi.im := by
  by_cases hgood : (x.compute n).lo.im <= (z.compute n).hi.im
  · exact hgood
  · exfalso
    have hgap : 0 < (x.compute n).lo.im - (z.compute n).hi.im := by
      rw [←Rat.lt_iff_sub_pos]
      simpa [Rat.not_le] using hgood
    have hthree : (0 : Rat) < 3 := by
      exact (Rat.natCast_pos).2 (by omega : 0 < (3 : Nat))
    have hgapThirdPos :
        0 < ((x.compute n).lo.im - (z.compute n).hi.im) / 3 := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap ((Rat.inv_pos).2 hthree)
    obtain ⟨M, hsmall⟩ := hy.2.2
      { val := ((x.compute n).lo.im - (z.compute n).hi.im) / 3,
        property := hgapThirdPos }
    let m : Nat := max n M
    have hnm : n <= m := by
      dsimp [m]
      exact Nat.le_max_left n M
    have hMle : M <= m := by
      dsimp [m]
      exact Nat.le_max_right n M
    have hxNest := hx.2.1 n m hnm
    have hzNest := hz.2.1 n m hnm
    have hxyM := (compareAt_overlap_iff x y m m).1 (hxy m)
    have hyzM := (compareAt_overlap_iff y z m m).1 (hyz m)
    have hySmallLe :
        (y.compute m).height <=
          ((x.compute n).lo.im - (z.compute n).hi.im) / 3 :=
      (hsmall m hMle).2
    have hyGapLe :
        (x.compute n).lo.im - (z.compute n).hi.im <=
          (y.compute m).height := by
      grind [QBox.height, QBox.Overlaps, QComplex.le_def, Rat.sub_eq_add_neg]
    have hthirdLt :
        ((x.compute n).lo.im - (z.compute n).hi.im) / 3 <
          (x.compute n).lo.im - (z.compute n).hi.im := by
      rw [Rat.div_lt_iff hthree]
      grind
    have hgapLeThird :
        (x.compute n).lo.im - (z.compute n).hi.im <=
          ((x.compute n).lo.im - (z.compute n).hi.im) / 3 :=
      Rat.le_trans hyGapLe hySmallLe
    have hgapLtThird :
        (x.compute n).lo.im - (z.compute n).hi.im <
          ((x.compute n).lo.im - (z.compute n).hi.im) / 3 :=
      Rat.lt_of_le_of_ne hgapLeThird (Rat.ne_of_gt hthirdLt)
    exact Rat.lt_irrefl (rat_lt_trans hgapLtThird hthirdLt)

theorem equiv_trans {x y z : ComplexRaw}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    x.Equiv y -> y.Equiv z -> x.Equiv z := by
  intro hxy hyz
  have hxySame := sameStageOverlap_of_equiv hx hy hxy
  have hyzSame := sameStageOverlap_of_equiv hy hz hyz
  have hyxSame := sameStageOverlap_of_equiv hy hx (equiv_symm hxy)
  have hzySame := sameStageOverlap_of_equiv hz hy (equiv_symm hyz)
  apply sameStageOverlap_equiv
  intro n
  apply (compareAt_overlap_iff x z n n).2
  exact ⟨
    ⟨equiv_trans_re_left hx hy hz hxySame hyzSame n,
      equiv_trans_im_left hx hy hz hxySame hyzSame n⟩,
    ⟨equiv_trans_re_left hz hy hx hzySame hyxSame n,
      equiv_trans_im_left hz hy hx hzySame hyxSame n⟩⟩

def ofQComplex (z : QComplex) : ComplexRaw where compute := fun _ => { lo := z, hi := z }

theorem ofQComplex_valid (z : QComplex) :
    (ofQComplex z).Valid := by
  constructor
  · intro n
    constructor
    · show 0 <= z.re - z.re
      grind
    · show 0 <= z.im - z.im
      grind
  · constructor
    · intro n m hnm
      simp [ofQComplex]
    · intro eps
      exact ⟨0, by
        intro n hn
        constructor
        · show ((ofQComplex z).compute n).width <= eps.val
          simp [ofQComplex, QBox.width]
          have hzero : z.re - z.re = 0 := by grind
          rw [hzero]
          exact Rat.le_of_lt eps.property
        · show ((ofQComplex z).compute n).height <= eps.val
          simp [ofQComplex, QBox.height]
          have hzero : z.im - z.im = 0 := by grind
          rw [hzero]
          exact Rat.le_of_lt eps.property⟩

def center (z : ComplexRaw) (n : Nat) : QComplex := (z.compute n).center

/-- Embed a raw real interval algorithm as a raw complex-box algorithm on the
real axis. -/
def ofRealRaw (x : RealRaw) : ComplexRaw where
  compute := fun n =>
    let I := x.compute n
    { lo := { re := I.lo, im := 0 },
      hi := { re := I.hi, im := 0 } }

instance : Coe RealRaw ComplexRaw where
  coe := ofRealRaw

theorem ofRealRaw_valid (x : RealRaw) (hx : x.Valid) :
    (ofRealRaw x).Valid := by
  constructor
  · intro n
    constructor
    · exact hx.1 n
    · simp [ofRealRaw, QBox.height, Rat.sub_eq_add_neg]
      grind
  · constructor
    · intro n m hnm
      have hnest := hx.2.1 n m hnm
      exact ⟨hnest.1, hnest.2.2, by simp [ofRealRaw], by simp [ofRealRaw]⟩
    · intro eps
      obtain ⟨N, hN⟩ := hx.2.2 eps
      exact ⟨N, by
        intro n hn
        constructor
        · exact hN n hn
        · have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          simp [ofRealRaw, QBox.height, Rat.sub_eq_add_neg]
          grind
      ⟩
theorem coe_realRaw_valid (x : RealRaw) (hx : x.Valid) :
    ((x : ComplexRaw).Valid) :=
  ofRealRaw_valid x hx

theorem ofRealRaw_equiv_of_equiv {x y : RealRaw}
    (_hx : x.Valid) (_hy : y.Valid) (h : x.Equiv y) :
    (ofRealRaw x).Equiv (ofRealRaw y) := by
  intro n
  have hstage := (RealRaw.compareAt_overlap_iff x y n n).1 (h n)
  exact (compareAt_overlap_iff (ofRealRaw x) (ofRealRaw y)
    n n).2
    ⟨⟨hstage.1, by simp [ofRealRaw]⟩,
      ⟨hstage.2, by simp [ofRealRaw]⟩⟩
theorem coe_realRaw_equiv_of_equiv {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (h : x.Equiv y) :
    (x : ComplexRaw).Equiv (y : ComplexRaw) :=
  ofRealRaw_equiv_of_equiv hx hy h

end ComplexRaw

/-- A raw representation of a partial complex-valued function on rational
complex inputs.  The domain belongs to the representation, so branch choices
and local charts can carry their natural domains. -/
structure FunctionRaw where
  domain : QComplex -> Prop
  compute : (z : QComplex) -> domain z -> Nat -> QBox
  rate :
    (z : QComplex) -> (hz : domain z) ->
      ComplexRaw.Rate (compute z hz) := fun _ _ => .unknown

namespace FunctionRaw

/-!
Function representations do not need their own global rate layer.  The function
layer keeps domain and representation data; the numeric output layer is still a
`RealRaw` or `ComplexRaw`, whose optional `rate` field carries any shrinking
rate metadata.
-/

def entire : QComplex -> Prop := fun _ => True

def evalRaw (f : FunctionRaw) (z : QComplex) (hz : f.domain z) : ComplexRaw where
  compute := f.compute z hz
  rate := f.rate z hz

/-- Restrict a complex-valued raw function to the real axis and keep the real
coordinate. -/
def realPartOnRealAxis (f : FunctionRaw) : PartialRealFunRaw where
  definedAt := fun x => f.domain (QComplex.ofRat x)
  compute := fun x hx n =>
    let B := f.compute (QComplex.ofRat x) hx n
    { lo := B.lo.re, hi := B.hi.re }

/-- Two raw function representations agree on their common domain when their
computed complex numbers are equivalent at every rational complex point where
both representations are defined.

This is intentionally not made into a global equivalence relation: for
arbitrary domains, agreement-on-overlap is not transitive without extra
domain/extension hypotheses. -/
def AgreeOnCommonDomain (f g : FunctionRaw) : Prop :=
  forall z (hf : f.domain z) (hg : g.domain z), (f.evalRaw z hf).Equiv (g.evalRaw z hg)

/-- Short alias for `AgreeOnCommonDomain`. -/
def Compatible (f g : FunctionRaw) : Prop := AgreeOnCommonDomain f g

end FunctionRaw

structure ComplexCert where
  raw : ComplexRaw
  valid : raw.Valid

/-- A certified handle for a defined complex number.

This is the concrete project-facing layer above `ComplexRaw`: it records a
chosen valid box algorithm, together with any alternative box algorithms already
proved equivalent to it.
-/
structure Complex where
  preferred : ComplexCert
  alternatives : List ComplexCert := []
  coherent : forall rep, rep ∈ alternatives -> rep.raw.Equiv preferred.raw := by
    intro rep h
    cases h

namespace Complex

def ofCert (z : ComplexCert) : Complex where
  preferred := z
  alternatives := []
  coherent := by
    intro rep h
    cases h

def ofRaw (z : ComplexRaw) (h : z.Valid) : Complex :=
  ofCert { raw := z, valid := h }

def ofQComplex (z : QComplex) : Complex :=
  ofRaw (ComplexRaw.ofQComplex z) (ComplexRaw.ofQComplex_valid z)

def ofReal (x : Real) : Complex :=
  ofRaw (ComplexRaw.ofRealRaw x.preferred)
    (ComplexRaw.ofRealRaw_valid x.preferred x.valid)

def compute (z : Complex) (n : Nat) : QBox :=
  z.preferred.raw.compute n

def rate (z : Complex) : ComplexRaw.Rate z.preferred.raw.compute :=
  z.preferred.raw.rate

def representations (z : Complex) : List ComplexCert :=
  z.preferred :: z.alternatives

def withAlternative (z : Complex) (rep : ComplexCert)
    (h : rep.raw.Equiv z.preferred.raw) : Complex where
  preferred := z.preferred
  alternatives := rep :: z.alternatives
  coherent := by
    intro candidate hc
    cases hc with
    | head => exact h
    | tail _ hc => exact z.coherent candidate hc

def Equiv (z w : Complex) : Prop :=
  z.preferred.raw.Equiv w.preferred.raw

theorem equiv_refl (z : Complex) : z.Equiv z :=
  ComplexRaw.equiv_refl z.preferred.raw z.preferred.valid

theorem equiv_symm {z w : Complex} : z.Equiv w -> w.Equiv z :=
  ComplexRaw.equiv_symm

theorem equiv_trans {z w u : Complex} : z.Equiv w -> w.Equiv u -> z.Equiv u :=
  ComplexRaw.equiv_trans z.preferred.valid w.preferred.valid u.preferred.valid

structure Representation (z : Complex) where
  cert : ComplexCert
  agrees : cert.raw.Equiv z.preferred.raw

def preferredRepresentation (z : Complex) : Representation z where
  cert := z.preferred
  agrees := ComplexRaw.equiv_refl z.preferred.raw z.preferred.valid

def alternativeRepresentation {z : Complex} (rep : ComplexCert)
    (h : rep ∈ z.alternatives) : Representation z where
  cert := rep
  agrees := z.coherent rep h

def computeUsing {z : Complex} (rep : Representation z) (n : Nat) : QBox :=
  rep.cert.raw.compute n

theorem representation_same_complex {z : Complex} (rep : Representation z) :
    (Complex.ofCert rep.cert).Equiv z :=
  rep.agrees

end Complex

end ComputableAnalysis

namespace ComputableAnalysis

def minRat (a b : Rat) : Rat := if a <= b then a else b
def maxRat2 (a b : Rat) : Rat := if a <= b then b else a

def min4 (a b c d : Rat) : Rat := minRat (minRat a b) (minRat c d)
def max4 (a b c d : Rat) : Rat := maxRat2 (maxRat2 a b) (maxRat2 c d)

namespace QBox

def point (z : QComplex) : QBox := { lo := z, hi := z }

def zero : QBox := point QComplex.zero

def ofRealInterval (I : QInterval) : QBox :=
  { lo := { re := I.lo, im := 0 }, hi := { re := I.hi, im := 0 } }

def add (A B : QBox) : QBox :=
  { lo := QComplex.add A.lo B.lo, hi := QComplex.add A.hi B.hi }

def neg (A : QBox) : QBox :=
  { lo := { re := -A.hi.re, im := -A.hi.im },
    hi := { re := -A.lo.re, im := -A.lo.im } }

def sub (A B : QBox) : QBox := add A (neg B)

def mulRealInterval (a b c d : Rat) : QInterval :=
  let p1 := a * c
  let p2 := a * d
  let p3 := b * c
  let p4 := b * d
  { lo := min4 p1 p2 p3 p4, hi := max4 p1 p2 p3 p4 }

theorem mulRealInterval_self_of_nonneg {a b : Rat}
    (ha0 : 0 <= a) (hab : a <= b) :
    mulRealInterval a b a b = { lo := a * a, hi := b * b } := by
  have hb0 : 0 <= b := by grind
  have h12 : a * a <= a * b := Rat.mul_le_mul_of_nonneg_left hab ha0
  have h13 : a * a <= b * a := by
    simpa [Rat.mul_comm] using Rat.mul_le_mul_of_nonneg_left hab ha0
  have h34 : b * a <= b * b := by
    simpa [Rat.mul_comm] using Rat.mul_le_mul_of_nonneg_left hab hb0
  have h24 : a * b <= b * b := Rat.mul_le_mul_of_nonneg_right hab hb0
  unfold mulRealInterval min4 max4 minRat maxRat2
  simp [h12, h13, h34, h24]

def mul (A B : QBox) : QBox :=
  let rr := mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re
  let ii := mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im
  let ri := mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im
  let ir := mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re
  { lo := { re := rr.lo - ii.hi, im := ri.lo + ir.lo },
    hi := { re := rr.hi - ii.lo, im := ri.hi + ir.hi } }

def scaleRat (r : Rat) (A : QBox) : QBox :=
  if 0 <= r then
    { lo := { re := r * A.lo.re, im := r * A.lo.im },
      hi := { re := r * A.hi.re, im := r * A.hi.im } }
  else
    { lo := { re := r * A.hi.re, im := r * A.hi.im },
      hi := { re := r * A.lo.re, im := r * A.lo.im } }

end QBox

end ComputableAnalysis

namespace ComputableAnalysis

namespace RealRaw

def zero : RealRaw := ofRat 0
def one : RealRaw := ofRat 1

def addCompute (x y : RealRaw) : Nat -> QInterval :=
  fun n =>
    let X := x.compute n
    let Y := y.compute n
    { lo := X.lo + Y.lo, hi := X.hi + Y.hi }

def negCompute (x : RealRaw) : Nat -> QInterval :=
  fun n =>
    let X := x.compute n
    { lo := -X.hi, hi := -X.lo }

def subCompute (x y : RealRaw) : Nat -> QInterval :=
  fun n =>
    let X := x.compute n
    let Y := y.compute n
    { lo := X.lo - Y.hi, hi := X.hi - Y.lo }

def scaleRatCompute (r : Rat) (x : RealRaw) : Nat -> QInterval :=
  fun n =>
    let X := x.compute n
    if 0 <= r then
      { lo := r * X.lo, hi := r * X.hi }
    else
      { lo := r * X.hi, hi := r * X.lo }

def mulCompute (x y : RealRaw) : Nat -> QInterval :=
  fun n =>
    let X := x.compute n
    let Y := y.compute n
    QBox.mulRealInterval X.lo X.hi Y.lo Y.hi

def add (x y : RealRaw) : RealRaw where
  compute := addCompute x y

def neg (x : RealRaw) : RealRaw where
  compute := negCompute x

def sub (x y : RealRaw) : RealRaw where
  compute := subCompute x y

def scaleRat (r : Rat) (x : RealRaw) : RealRaw where
  compute := scaleRatCompute r x

def mul (x y : RealRaw) : RealRaw where
  compute := mulCompute x y

def scaleRatNonneg (r : Rat) (_hr : 0 <= r) (x : RealRaw) : RealRaw where
  compute := fun n =>
    let X := x.compute n
    { lo := r * X.lo, hi := r * X.hi }

instance : HAdd RealRaw RealRaw RealRaw where
  hAdd := add

instance : Neg RealRaw where
  neg := neg

instance : HSub RealRaw RealRaw RealRaw where
  hSub := sub

instance : HMul RealRaw RealRaw RealRaw where
  hMul := mul

instance : HMul Rat RealRaw RealRaw where
  hMul := scaleRat

instance : HMul Nat RealRaw RealRaw where
  hMul n x := scaleRat (n : Rat) x

instance : HMul Int RealRaw RealRaw where
  hMul n x := scaleRat (n : Rat) x

def AddCertifies (x y : RealRaw) : Prop :=
  RealRaw.ValidCompute (addCompute x y)

def NegCertifies (x : RealRaw) : Prop :=
  RealRaw.ValidCompute (negCompute x)

def ScaleRatCertifies (r : Rat) (x : RealRaw) : Prop :=
  RealRaw.ValidCompute (scaleRatCompute r x)

private theorem half_pos {q : Rat} (hq : 0 < q) : 0 < q / 2 := by
  rw [Rat.div_def]
  exact Rat.mul_pos hq ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))

private theorem add_halves (q : Rat) : q / 2 + q / 2 = q := by
  rw [Rat.div_def]
  have hne : (2 : Rat) != 0 := by native_decide
  grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.mul_assoc,
    Rat.mul_comm, Rat.mul_inv_cancel]

private theorem valid_width_order
    {compute : Nat -> QInterval}
    (h : RealRaw.ValidCompute compute) (n : Nat) :
    (compute n).lo <= (compute n).hi := by
  have hn := h.2.1 n n (Nat.le_refl n)
  exact hn.2.1

theorem addCompute_valid {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) :
    RealRaw.ValidCompute (addCompute x y) := by
  constructor
  · intro n
    have hxord := valid_width_order hx n
    have hyord := valid_width_order hy n
    unfold addCompute QInterval.width
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hxnm := hx.2.1 n m hnm
      have hynm := hy.2.1 n m hnm
      unfold addCompute
      constructor
      · grind
      · constructor
        · grind
        · grind
    · intro eps
      let eps2 : QPos := ⟨eps.val / 2, half_pos eps.property⟩
      obtain ⟨Nx, hNx⟩ := hx.2.2 eps2
      obtain ⟨Ny, hNy⟩ := hy.2.2 eps2
      refine ⟨Nat.max Nx Ny, ?_⟩
      intro n hn
      have hnx : Nx <= n := Nat.le_trans (Nat.le_max_left Nx Ny) hn
      have hny : Ny <= n := Nat.le_trans (Nat.le_max_right Nx Ny) hn
      have hxeps := hNx n hnx
      have hyeps := hNy n hny
      unfold addCompute QInterval.width
      change
        (x.compute n).hi + (y.compute n).hi -
          ((x.compute n).lo + (y.compute n).lo) <= eps.val
      calc
        (x.compute n).hi + (y.compute n).hi -
            ((x.compute n).lo + (y.compute n).lo)
            <= eps2.val + eps2.val := by
          have hxeps' :
              (x.compute n).hi - (x.compute n).lo <= eps2.val := by
            simpa [QInterval.width] using hxeps
          have hyeps' :
              (y.compute n).hi - (y.compute n).lo <= eps2.val := by
            simpa [QInterval.width] using hyeps
          grind [Rat.sub_eq_add_neg]
        _ = eps.val := add_halves eps.val

theorem negCompute_valid {x : RealRaw}
    (hx : x.Valid) : RealRaw.ValidCompute (negCompute x) := by
  constructor
  · intro n
    have hxord := valid_width_order hx n
    unfold negCompute QInterval.width
    change 0 <= -(x.compute n).lo - -(x.compute n).hi
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hxnm := hx.2.1 n m hnm
      unfold negCompute
      constructor
      · exact Rat.neg_le_neg hxnm.2.2
      · constructor
        · exact Rat.neg_le_neg hxnm.2.1
        · exact Rat.neg_le_neg hxnm.1
    · intro eps
      obtain ⟨N, hN⟩ := hx.2.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      have hxeps := hN n hn
      unfold negCompute QInterval.width
      change -(x.compute n).lo - -(x.compute n).hi <= eps.val
      have hxeps' :
          (x.compute n).hi - (x.compute n).lo <= eps.val := by
        simpa [QInterval.width] using hxeps
      grind [Rat.sub_eq_add_neg]

theorem subCompute_valid {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) :
    RealRaw.ValidCompute (subCompute x y) := by
  constructor
  · intro n
    have hxord := valid_width_order hx n
    have hyord := valid_width_order hy n
    unfold subCompute QInterval.width
    change 0 <=
      ((x.compute n).hi - (y.compute n).lo) -
        ((x.compute n).lo - (y.compute n).hi)
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hxnm := hx.2.1 n m hnm
      have hynm := hy.2.1 n m hnm
      unfold subCompute
      constructor
      · grind [Rat.sub_eq_add_neg]
      · constructor
        · grind [Rat.sub_eq_add_neg]
        · grind [Rat.sub_eq_add_neg]
    · intro eps
      let eps2 : QPos := ⟨eps.val / 2, half_pos eps.property⟩
      obtain ⟨Nx, hNx⟩ := hx.2.2 eps2
      obtain ⟨Ny, hNy⟩ := hy.2.2 eps2
      refine ⟨Nat.max Nx Ny, ?_⟩
      intro n hn
      have hnx : Nx <= n := Nat.le_trans (Nat.le_max_left Nx Ny) hn
      have hny : Ny <= n := Nat.le_trans (Nat.le_max_right Nx Ny) hn
      have hxeps := hNx n hnx
      have hyeps := hNy n hny
      unfold subCompute QInterval.width
      change
        ((x.compute n).hi - (y.compute n).lo) -
          ((x.compute n).lo - (y.compute n).hi) <= eps.val
      calc
        ((x.compute n).hi - (y.compute n).lo) -
            ((x.compute n).lo - (y.compute n).hi)
            <= eps2.val + eps2.val := by
          have hxeps' :
              (x.compute n).hi - (x.compute n).lo <= eps2.val := by
            simpa [QInterval.width] using hxeps
          have hyeps' :
              (y.compute n).hi - (y.compute n).lo <= eps2.val := by
            simpa [QInterval.width] using hyeps
          grind [Rat.sub_eq_add_neg]
        _ = eps.val := add_halves eps.val

private theorem mul_width_shrink
    {compute : Nat -> QInterval} (h : RealRaw.ValidCompute compute)
    {r : Rat} (hr : 0 <= r) :
    RealRaw.WidthsShrinkToZero
      (fun n => { lo := r * (compute n).lo,
                  hi := r * (compute n).hi }) := by
  by_cases hr0 : r = 0
  · intro eps
    refine ⟨0, ?_⟩
    intro n _hn
    unfold QInterval.width
    simp [hr0]
    grind [Rat.sub_eq_add_neg, Rat.le_of_lt eps.property]
  · have hrpos : 0 < r := by grind
    intro eps
    let scaled : QPos :=
      ⟨eps.val / r, by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hrpos)⟩
    obtain ⟨N, hN⟩ := h.2.2 scaled
    refine ⟨N, ?_⟩
    intro n hn
    have hw := hN n hn
    unfold QInterval.width
    have hw' : (compute n).hi - (compute n).lo <= scaled.val := by
      simpa [QInterval.width] using hw
    calc
      r * (compute n).hi - r * (compute n).lo =
          r * (compute n).width := by
            unfold QInterval.width
            grind [Rat.sub_eq_add_neg, Rat.mul_add]
      _ <= r * scaled.val := by
            exact Rat.mul_le_mul_of_nonneg_left hw' hr
      _ = eps.val := by
            dsimp [scaled]
            rw [Rat.div_def]
            have hrne : r ≠ 0 := Rat.ne_of_gt hrpos
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem scaleRatCompute_valid_of_nonneg {r : Rat} {x : RealRaw}
    (hr : 0 <= r) (hx : x.Valid) :
    RealRaw.ValidCompute (scaleRatCompute r x) := by
  constructor
  · intro n
    have hxord := valid_width_order hx n
    unfold scaleRatCompute QInterval.width
    simp [hr]
    change 0 <= r * (x.compute n).hi - r * (x.compute n).lo
    have hmul :
        r * (x.compute n).lo <= r * (x.compute n).hi :=
      Rat.mul_le_mul_of_nonneg_left hxord hr
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hxnm := hx.2.1 n m hnm
      unfold scaleRatCompute
      simp [hr]
      constructor
      · exact Rat.mul_le_mul_of_nonneg_left hxnm.1 hr
      · constructor
        · exact Rat.mul_le_mul_of_nonneg_left hxnm.2.1 hr
        · exact Rat.mul_le_mul_of_nonneg_left hxnm.2.2 hr
    · intro eps
      obtain ⟨N, hN⟩ := mul_width_shrink hx hr eps
      refine ⟨N, ?_⟩
      intro n hn
      have hwidth := hN n hn
      unfold scaleRatCompute QInterval.width
      simp [hr]
      simpa [QInterval.width] using hwidth

theorem add_valid {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) : (x + y).Valid :=
  addCompute_valid hx hy

theorem neg_valid {x : RealRaw} (hx : x.Valid) : (-x).Valid :=
  negCompute_valid hx

theorem sub_valid {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) : (x - y).Valid :=
  subCompute_valid hx hy

theorem scaleRat_valid_of_nonneg {r : Rat} {x : RealRaw}
    (hr : 0 <= r) (hx : x.Valid) : (scaleRat r x).Valid :=
  scaleRatCompute_valid_of_nonneg hr hx

private theorem scaleRatCompute_neg_eq_scaleRatCompute_neg
    {r : Rat} (hr : ¬ 0 <= r) (x : RealRaw) :
    scaleRatCompute r x = scaleRatCompute (-r) (RealRaw.neg x) := by
  funext n
  have hneg : 0 <= -r := by grind
  simp [scaleRatCompute, RealRaw.neg, negCompute, hr, hneg]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem scaleRatCompute_valid {r : Rat} {x : RealRaw}
    (hx : x.Valid) :
    RealRaw.ValidCompute (scaleRatCompute r x) := by
  by_cases hr : 0 <= r
  · exact scaleRatCompute_valid_of_nonneg hr hx
  · have hneg : 0 <= -r := by grind
    have hvalid :=
      scaleRatCompute_valid_of_nonneg (r := -r) (x := RealRaw.neg x) hneg
        (neg_valid hx)
    rwa [scaleRatCompute_neg_eq_scaleRatCompute_neg hr x]

theorem scaleRat_valid {r : Rat} {x : RealRaw}
    (hx : x.Valid) : (scaleRat r x).Valid :=
  scaleRatCompute_valid hx

private theorem square_mono_nonneg {a b : Rat}
    (ha0 : 0 <= a) (hab : a <= b) : a * a <= b * b := by
  have hb0 : 0 <= b := by grind
  have h1 : a * a <= a * b := Rat.mul_le_mul_of_nonneg_left hab ha0
  have h2 : a * b <= b * b := Rat.mul_le_mul_of_nonneg_right hab hb0
  exact Rat.le_trans h1 h2

theorem mulSelf_valid_of_nonneg_bounded {x : RealRaw}
    (hx : x.Valid) {B : Rat} (hB : 0 < B)
    (hbounds : forall n, 0 <= (x.compute n).lo ∧ (x.compute n).hi <= B) :
    (x * x).Valid := by
  constructor
  · intro n
    have horder := RealRaw.interval_order_of_valid x hx n
    have hnonneg := (hbounds n).1
    have hcompute : ((x * x).compute n) =
        { lo := (x.compute n).lo * (x.compute n).lo,
          hi := (x.compute n).hi * (x.compute n).hi } := by
      change QBox.mulRealInterval
          (x.compute n).lo (x.compute n).hi
          (x.compute n).lo (x.compute n).hi = _
      exact QBox.mulRealInterval_self_of_nonneg hnonneg horder
    rw [hcompute]
    unfold QInterval.width
    have hsquare :
        (x.compute n).lo * (x.compute n).lo <=
          (x.compute n).hi * (x.compute n).hi :=
      square_mono_nonneg hnonneg horder
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have horderN := RealRaw.interval_order_of_valid x hx n
      have horderM := RealRaw.interval_order_of_valid x hx m
      have hnonnegN := (hbounds n).1
      have hnonnegM := (hbounds m).1
      have hnested := hx.2.1 n m hnm
      have hcomputeN : ((x * x).compute n) =
          { lo := (x.compute n).lo * (x.compute n).lo,
            hi := (x.compute n).hi * (x.compute n).hi } := by
        change QBox.mulRealInterval
            (x.compute n).lo (x.compute n).hi
            (x.compute n).lo (x.compute n).hi = _
        exact QBox.mulRealInterval_self_of_nonneg hnonnegN horderN
      have hcomputeM : ((x * x).compute m) =
          { lo := (x.compute m).lo * (x.compute m).lo,
            hi := (x.compute m).hi * (x.compute m).hi } := by
        change QBox.mulRealInterval
            (x.compute m).lo (x.compute m).hi
            (x.compute m).lo (x.compute m).hi = _
        exact QBox.mulRealInterval_self_of_nonneg hnonnegM horderM
      rw [hcomputeN, hcomputeM]
      constructor
      · exact square_mono_nonneg hnonnegN hnested.1
      · constructor
        · exact square_mono_nonneg hnonnegM horderM
        · exact square_mono_nonneg (by grind) hnested.2.2
    · intro eps
      have hdenPos : 0 < (2 : Rat) * B := by
        exact Rat.mul_pos (by native_decide : (0 : Rat) < 2) hB
      let scaled : QPos :=
        ⟨eps.val / ((2 : Rat) * B), by
          rw [Rat.div_def]
          exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hdenPos)⟩
      obtain ⟨N, hN⟩ := hx.2.2 scaled
      refine ⟨N, ?_⟩
      intro n hn
      have horder := RealRaw.interval_order_of_valid x hx n
      have hnonneg := (hbounds n).1
      have hcompute : ((x * x).compute n) =
          { lo := (x.compute n).lo * (x.compute n).lo,
            hi := (x.compute n).hi * (x.compute n).hi } := by
        change QBox.mulRealInterval
            (x.compute n).lo (x.compute n).hi
            (x.compute n).lo (x.compute n).hi = _
        exact QBox.mulRealInterval_self_of_nonneg hnonneg horder
      have hw := hN n hn
      rw [hcompute]
      unfold QInterval.width
      have hw' : (x.compute n).hi - (x.compute n).lo <= scaled.val := by
        simpa [QInterval.width] using hw
      have hsumBound :
          (x.compute n).hi + (x.compute n).lo <= (2 : Rat) * B := by
        have hhiB := (hbounds n).2
        grind
      have hgapNonneg : 0 <= (x.compute n).hi - (x.compute n).lo := by
        grind [Rat.sub_eq_add_neg]
      calc
        (x.compute n).hi * (x.compute n).hi -
            (x.compute n).lo * (x.compute n).lo
            = ((x.compute n).hi - (x.compute n).lo) *
                ((x.compute n).hi + (x.compute n).lo) := by
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
                Rat.mul_assoc, Rat.mul_comm]
        _ <= ((x.compute n).hi - (x.compute n).lo) * ((2 : Rat) * B) := by
              exact Rat.mul_le_mul_of_nonneg_left hsumBound hgapNonneg
        _ <= scaled.val * ((2 : Rat) * B) := by
              exact Rat.mul_le_mul_of_nonneg_right hw' (Rat.le_of_lt hdenPos)
        _ = eps.val := by
              dsimp [scaled]
              rw [Rat.div_def]
              have hne : (2 : Rat) * B ≠ 0 := Rat.ne_of_gt hdenPos
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem le_of_mul_le_mul_pos_left {r a b : Rat}
    (hr : 0 < r) (h : r * a <= r * b) : a <= b := by
  apply Rat.le_of_mul_le_mul_right (c := r)
  · simpa [Rat.mul_comm] using h
  · exact hr

theorem scaleRat_width_of_nonneg {r : Rat} (hr : 0 <= r)
    (x : RealRaw) (n : Nat) :
    ((scaleRat r x).compute n).width = r * (x.compute n).width := by
  unfold scaleRat scaleRatCompute QInterval.width
  simp [hr]
  grind [Rat.sub_eq_add_neg, Rat.mul_add]

/-- Adding rational intervals adds their widths exactly. -/
theorem add_width (x y : RealRaw) (n : Nat) :
    ((x + y).compute n).width =
      (x.compute n).width + (y.compute n).width := by
  change (addCompute x y n).width =
    (x.compute n).width + (y.compute n).width
  unfold addCompute QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- Subtracting rational intervals adds their widths exactly. -/
theorem sub_width (x y : RealRaw) (n : Nat) :
    ((x - y).compute n).width =
      (x.compute n).width + (y.compute n).width := by
  change (subCompute x y n).width =
    (x.compute n).width + (y.compute n).width
  unfold subCompute QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- Natural scaling multiplies an interval width by that natural number. -/
theorem natScale_width (k n : Nat) (x : RealRaw) :
    ((k * x : RealRaw).compute n).width =
      (k : Rat) * (x.compute n).width := by
  change ((scaleRat (k : Rat) x).compute n).width =
    (k : Rat) * (x.compute n).width
  exact scaleRat_width_of_nonneg Rat.natCast_nonneg x n

theorem valid_of_scaleRat_valid_of_pos {r : Rat} {x : RealRaw}
    (hr : 0 < r) (hscale : (scaleRat r x).Valid) : x.Valid := by
  have hr_nonneg : 0 <= r := Rat.le_of_lt hr
  constructor
  · intro n
    have hs := hscale.1 n
    rw [scaleRat_width_of_nonneg hr_nonneg x n] at hs
    have hmul : r * 0 <= r * (x.compute n).width := by
      simpa using hs
    exact le_of_mul_le_mul_pos_left hr hmul
  · constructor
    · intro n m hnm
      have hs := hscale.2.1 n m hnm
      unfold scaleRat scaleRatCompute at hs
      simp [hr_nonneg] at hs
      constructor
      · exact le_of_mul_le_mul_pos_left hr hs.1
      · constructor
        · exact le_of_mul_le_mul_pos_left hr hs.2.1
        · exact le_of_mul_le_mul_pos_left hr hs.2.2
    · intro eps
      let scaled : QPos := ⟨r * eps.val, Rat.mul_pos hr eps.property⟩
      obtain ⟨N, hN⟩ := hscale.2.2 scaled
      refine ⟨N, ?_⟩
      intro n hn
      have hw := hN n hn
      rw [scaleRat_width_of_nonneg hr_nonneg x n] at hw
      have hmul : r * (x.compute n).width <= r * eps.val := by
        simpa [scaled] using hw
      exact le_of_mul_le_mul_pos_left hr hmul

theorem natScale_valid (n : Nat) {x : RealRaw}
    (hx : x.Valid) : (n * x).Valid :=
  scaleRat_valid_of_nonneg (Rat.natCast_nonneg : 0 <= (n : Rat)) hx

theorem valid_of_natScale_valid {n : Nat} {x : RealRaw}
    (hn : 0 < n) (hscale : ((n : Nat) * x : RealRaw).Valid) : x.Valid := by
  change (scaleRat (n : Rat) x).Valid at hscale
  exact valid_of_scaleRat_valid_of_pos
    ((Rat.natCast_pos).2 hn) hscale

theorem scaleRat_equiv_of_nonneg {r : Rat} {x y : RealRaw}
    (hr : 0 <= r) (hxy : x.Equiv y) :
    (scaleRat r x).Equiv (scaleRat r y) := by
  intro n
  have h := (compareAt_overlap_iff x y n n).1 (hxy n)
  apply (compareAt_overlap_iff (scaleRat r x) (scaleRat r y) n n).2
  unfold scaleRat scaleRatCompute
  simp [hr, QInterval.Overlaps]
  exact ⟨Rat.mul_le_mul_of_nonneg_left h.1 hr,
    Rat.mul_le_mul_of_nonneg_left h.2 hr⟩

theorem equiv_of_scaleRat_equiv_of_pos {r : Rat} {x y : RealRaw}
    (hr : 0 < r) (hxy : (scaleRat r x).Equiv (scaleRat r y)) :
    x.Equiv y := by
  have hr_nonneg : 0 <= r := Rat.le_of_lt hr
  intro n
  have h := (compareAt_overlap_iff (scaleRat r x) (scaleRat r y) n n).1
    (hxy n)
  apply (compareAt_overlap_iff x y n n).2
  unfold scaleRat scaleRatCompute at h
  simp [hr_nonneg, QInterval.Overlaps] at h
  exact ⟨le_of_mul_le_mul_pos_left hr h.1,
    le_of_mul_le_mul_pos_left hr h.2⟩

theorem natScale_equiv (n : Nat) {x y : RealRaw}
    (hxy : x.Equiv y) : (n * x).Equiv (n * y) :=
  scaleRat_equiv_of_nonneg (Rat.natCast_nonneg : 0 <= (n : Rat)) hxy

theorem equiv_of_natScale_equiv {n : Nat} {x y : RealRaw}
    (hn : 0 < n) (hxy : ((n : Nat) * x : RealRaw).Equiv (n * y)) :
    x.Equiv y := by
  change (scaleRat (n : Rat) x).Equiv (scaleRat (n : Rat) y) at hxy
  exact equiv_of_scaleRat_equiv_of_pos ((Rat.natCast_pos).2 hn) hxy

theorem neg_equiv {x y : RealRaw}
    (hxy : x.Equiv y) : (-x).Equiv (-y) := by
  intro n
  have h := (compareAt_overlap_iff x y n n).1 (hxy n)
  apply (compareAt_overlap_iff (-x) (-y) n n).2
  change QInterval.Overlaps
    (negCompute x n) (negCompute y n)
  unfold negCompute QInterval.Overlaps
  exact ⟨Rat.neg_le_neg h.2, Rat.neg_le_neg h.1⟩

theorem scaleRat_equiv {r : Rat} {x y : RealRaw}
    (hxy : x.Equiv y) :
    (scaleRat r x).Equiv (scaleRat r y) := by
  by_cases hr : 0 <= r
  · exact scaleRat_equiv_of_nonneg hr hxy
  · have hneg : 0 <= -r := by grind
    have h :=
      scaleRat_equiv_of_nonneg
        (r := -r) (x := RealRaw.neg x) (y := RealRaw.neg y)
        hneg (neg_equiv hxy)
    intro n
    change compareAt (scaleRat r x) (scaleRat r y) n = .overlap
    change compareAt
      { compute := scaleRatCompute r x }
      { compute := scaleRatCompute r y } n = .overlap
    rw [scaleRatCompute_neg_eq_scaleRatCompute_neg hr x,
      scaleRatCompute_neg_eq_scaleRatCompute_neg hr y]
    exact h n

theorem add_equiv {x x' y y' : RealRaw}
    (hx : x.Valid) (hx' : x'.Valid)
    (hy : y.Valid) (hy' : y'.Valid)
    (hxx' : x.Equiv x') (hyy' : y.Equiv y') :
    (x + y).Equiv (x' + y') := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hxSame := (RealRaw.compareAt_overlap_iff x x' n n).1
    (RealRaw.sameStageOverlap_of_equiv hx hx' hxx' n)
  have hySame := (RealRaw.compareAt_overlap_iff y y' n n).1
    (RealRaw.sameStageOverlap_of_equiv hy hy' hyy' n)
  apply (RealRaw.compareAt_overlap_iff (x + y) (x' + y') n n).2
  unfold QInterval.Overlaps at hxSame hySame
  change QInterval.Overlaps (addCompute x y n) (addCompute x' y' n)
  unfold addCompute QInterval.Overlaps
  constructor <;> grind

/-- Addition of valid raw interval representatives is commutative up to
equivalence. -/
theorem add_comm_equiv (x y : RealRaw) (hx : x.Valid) (hy : y.Valid) :
    (x + y).Equiv (y + x) := by
  intro n
  apply (compareAt_overlap_iff (x + y) (y + x) n n).2
  have hxorder := interval_order_of_valid x hx n
  have hyorder := interval_order_of_valid y hy n
  change QInterval.Overlaps
    { lo := (x.compute n).lo + (y.compute n).lo,
      hi := (x.compute n).hi + (y.compute n).hi }
    { lo := (y.compute n).lo + (x.compute n).lo,
      hi := (y.compute n).hi + (x.compute n).hi }
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.add_comm]

/-- Addition of raw interval representatives is associative up to equivalence.

This permits later analytic identities to regroup certified interval
expressions without selecting a completed-real quotient. -/
theorem add_assoc_equiv (x y z : RealRaw)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    ((x + y) + z).Equiv (x + (y + z)) := by
  intro n
  apply (compareAt_overlap_iff ((x + y) + z) (x + (y + z)) n n).2
  have hxorder := interval_order_of_valid x hx n
  have hyorder := interval_order_of_valid y hy n
  have hzorder := interval_order_of_valid z hz n
  change QInterval.Overlaps
    { lo := ((x.compute n).lo + (y.compute n).lo) + (z.compute n).lo,
      hi := ((x.compute n).hi + (y.compute n).hi) + (z.compute n).hi }
    { lo := (x.compute n).lo + ((y.compute n).lo + (z.compute n).lo),
      hi := (x.compute n).hi + ((y.compute n).hi + (z.compute n).hi) }
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.add_assoc]

/-- Scaling a raw real by two agrees with adding it to itself. -/
theorem two_natscale_equiv_add_self (x : RealRaw) (hx : x.Valid) :
    ((2 : Nat) * x).Equiv (x + x) := by
  intro n
  apply (compareAt_overlap_iff ((2 : Nat) * x) (x + x) n n).2
  have hxorder := interval_order_of_valid x hx n
  change QInterval.Overlaps
    (scaleRatCompute (2 : Rat) x n) (addCompute x x n)
  simp [scaleRatCompute, addCompute,
    (by native_decide : (0 : Rat) <= 2), QInterval.Overlaps]
  constructor <;> grind [Rat.add_comm]

/-- Scaling a raw real by four agrees with adding two doubled copies. -/
theorem four_natscale_equiv_add_two_natscale (x : RealRaw) (hx : x.Valid) :
    ((4 : Nat) * x).Equiv (((2 : Nat) * x) + ((2 : Nat) * x)) := by
  intro n
  apply (compareAt_overlap_iff
    ((4 : Nat) * x) (((2 : Nat) * x) + ((2 : Nat) * x)) n n).2
  have hxorder := interval_order_of_valid x hx n
  change QInterval.Overlaps
    (scaleRatCompute (4 : Rat) x n)
    (addCompute (scaleRat (2 : Rat) x) (scaleRat (2 : Rat) x) n)
  simp [scaleRat, scaleRatCompute, addCompute,
    (by native_decide : (0 : Rat) <= 4),
    (by native_decide : (0 : Rat) <= 2), QInterval.Overlaps]
  constructor <;> grind [Rat.add_comm]

theorem zero_add_equiv {x : RealRaw}
    (hx : x.Valid) : (zero + x).Equiv x := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have horder := RealRaw.interval_order_of_valid x hx n
  apply (RealRaw.compareAt_overlap_iff (zero + x) x n n).2
  change QInterval.Overlaps (addCompute zero x n) (x.compute n)
  unfold addCompute zero ofRat QInterval.Overlaps
  constructor <;> grind

theorem add_zero_equiv {x : RealRaw}
    (hx : x.Valid) : (x + zero).Equiv x := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have horder := RealRaw.interval_order_of_valid x hx n
  apply (RealRaw.compareAt_overlap_iff (x + zero) x n n).2
  change QInterval.Overlaps (addCompute x zero n) (x.compute n)
  unfold addCompute zero ofRat QInterval.Overlaps
  constructor <;> grind

theorem sub_equiv {x x' y y' : RealRaw}
    (hx : x.Valid) (hx' : x'.Valid)
    (hy : y.Valid) (hy' : y'.Valid)
    (hxx' : x.Equiv x') (hyy' : y.Equiv y') :
    (x - y).Equiv (x' - y') := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hxSame := (RealRaw.compareAt_overlap_iff x x' n n).1
    (RealRaw.sameStageOverlap_of_equiv hx hx' hxx' n)
  have hySame := (RealRaw.compareAt_overlap_iff y y' n n).1
    (RealRaw.sameStageOverlap_of_equiv hy hy' hyy' n)
  apply (RealRaw.compareAt_overlap_iff (x - y) (x' - y') n n).2
  unfold QInterval.Overlaps at hxSame hySame
  change QInterval.Overlaps (subCompute x y n) (subCompute x' y' n)
  unfold subCompute QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem add_sub_cancel_left_equiv {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) :
    ((x + y) - x).Equiv y := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hxord := RealRaw.interval_order_of_valid x hx n
  have hyord := RealRaw.interval_order_of_valid y hy n
  apply (RealRaw.compareAt_overlap_iff ((x + y) - x) y n n).2
  change QInterval.Overlaps
    { lo := ((x.compute n).lo + (y.compute n).lo) - (x.compute n).hi,
      hi := ((x.compute n).hi + (y.compute n).hi) - (x.compute n).lo }
    (y.compute n)
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem add_sub_cancel_right_equiv {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) :
    ((x + y) - y).Equiv x := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hxord := RealRaw.interval_order_of_valid x hx n
  have hyord := RealRaw.interval_order_of_valid y hy n
  apply (RealRaw.compareAt_overlap_iff ((x + y) - y) x n n).2
  change QInterval.Overlaps
    { lo := ((x.compute n).lo + (y.compute n).lo) - (y.compute n).hi,
      hi := ((x.compute n).hi + (y.compute n).hi) - (y.compute n).lo }
    (x.compute n)
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Adding back a subtracted valid representative recovers the original raw
real up to interval overlap. -/
theorem sub_add_cancel_equiv {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) :
    ((x - y) + y).Equiv x := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hxord := RealRaw.interval_order_of_valid x hx n
  have hyord := RealRaw.interval_order_of_valid y hy n
  apply (RealRaw.compareAt_overlap_iff ((x - y) + y) x n n).2
  change QInterval.Overlaps
    { lo := ((x.compute n).lo - (y.compute n).hi) + (y.compute n).lo,
      hi := ((x.compute n).hi - (y.compute n).lo) + (y.compute n).hi }
    (x.compute n)
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Telescoping for raw interval representatives:
`(y - x) + (z - y)` is equivalent to `z - x`. -/
theorem sub_add_sub_cancel_middle_equiv {x y z : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    ((y - x) + (z - y)).Equiv (z - x) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hxord := RealRaw.interval_order_of_valid x hx n
  have hyord := RealRaw.interval_order_of_valid y hy n
  have hzord := RealRaw.interval_order_of_valid z hz n
  apply (RealRaw.compareAt_overlap_iff ((y - x) + (z - y)) (z - x) n n).2
  change QInterval.Overlaps
    { lo := ((y.compute n).lo - (x.compute n).hi) +
        ((z.compute n).lo - (y.compute n).hi),
      hi := ((y.compute n).hi - (x.compute n).lo) +
        ((z.compute n).hi - (y.compute n).lo) }
    { lo := (z.compute n).lo - (x.compute n).hi,
      hi := (z.compute n).hi - (x.compute n).lo }
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

def Pos (x : RealRaw) : Prop :=
  Exists fun n : Nat => 0 < (x.compute n).lo

def Neg (x : RealRaw) : Prop :=
  Exists fun n : Nat => (x.compute n).hi < 0

def ApartZero (x : RealRaw) : Prop :=
  x.Pos \/ x.Neg

def HasComputableInv (x : RealRaw) : Prop :=
  x.Valid -> ApartZero x -> Exists fun y : RealRaw => y.Valid

end RealRaw

namespace ComplexRaw

def zero : ComplexRaw := ofQComplex QComplex.zero
def one : ComplexRaw := ofQComplex QComplex.one

instance (n : Nat) : OfNat ComplexRaw n where
  ofNat := ofQComplex (QComplex.ofRat n)

def add (z w : ComplexRaw) : ComplexRaw where
  compute := fun eps => QBox.add (z.compute eps) (w.compute eps)

def neg (z : ComplexRaw) : ComplexRaw where
  compute := fun eps => QBox.neg (z.compute eps)

def sub (z w : ComplexRaw) : ComplexRaw :=
  add z (neg w)

def scaleRat (r : Rat) (z : ComplexRaw) : ComplexRaw where
  compute := fun eps => QBox.scaleRat r (z.compute eps)

instance : HAdd ComplexRaw ComplexRaw ComplexRaw where
  hAdd := add

instance : Neg ComplexRaw where
  neg := neg

instance : HSub ComplexRaw ComplexRaw ComplexRaw where
  hSub := sub

instance : HMul Rat ComplexRaw ComplexRaw where
  hMul := scaleRat

instance : HMul Nat ComplexRaw ComplexRaw where
  hMul n z := scaleRat (n : Rat) z

instance : HMul Int ComplexRaw ComplexRaw where
  hMul n z := scaleRat (n : Rat) z

private theorem half_pos_complex {q : Rat} (hq : 0 < q) : 0 < q / 2 := by
  rw [Rat.div_def]
  exact Rat.mul_pos hq ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))

private theorem add_halves_complex (q : Rat) : q / 2 + q / 2 = q := by
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.mul_assoc,
    Rat.mul_comm, Rat.mul_inv_cancel]

private theorem valid_re_order
    {compute : Nat -> QBox}
    (h : ComplexRaw.ValidCompute compute) (n : Nat) :
    (compute n).lo.re <= (compute n).hi.re := by
  have hw := (h.1 n).1
  unfold QBox.width at hw
  grind [Rat.sub_eq_add_neg]

private theorem valid_im_order
    {compute : Nat -> QBox}
    (h : ComplexRaw.ValidCompute compute) (n : Nat) :
    (compute n).lo.im <= (compute n).hi.im := by
  have hh := (h.1 n).2
  unfold QBox.height at hh
  grind [Rat.sub_eq_add_neg]

theorem addCompute_valid {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid) :
    ComplexRaw.ValidCompute (fun n =>
      let Z := z.compute n
      let W := w.compute n
      { lo := QComplex.add Z.lo W.lo, hi := QComplex.add Z.hi W.hi }) := by
  constructor
  · intro n
    have hzre := valid_re_order hz n
    have hwre := valid_re_order hw n
    have hzim := valid_im_order hz n
    have hwim := valid_im_order hw n
    constructor
    · unfold QBox.width QComplex.add
      grind [Rat.sub_eq_add_neg]
    · unfold QBox.height QComplex.add
      grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hznm := hz.2.1 n m hnm
      have hwnm := hw.2.1 n m hnm
      unfold QComplex.add
      constructor
      · grind
      · constructor
        · grind
        · constructor
          · grind
          · grind
    · intro eps
      let eps2 : QPos := ⟨eps.val / 2, half_pos_complex eps.property⟩
      obtain ⟨Nz, hNz⟩ := hz.2.2 eps2
      obtain ⟨Nw, hNw⟩ := hw.2.2 eps2
      refine ⟨Nat.max Nz Nw, ?_⟩
      intro n hn
      have hnz : Nz <= n := Nat.le_trans (Nat.le_max_left Nz Nw) hn
      have hnw : Nw <= n := Nat.le_trans (Nat.le_max_right Nz Nw) hn
      have hzeps := hNz n hnz
      have hweps := hNw n hnw
      constructor
      · unfold QBox.width QComplex.add
        have hzeps' :
            (z.compute n).hi.re - (z.compute n).lo.re <= eps2.val := by
          simpa [QBox.width] using hzeps.1
        have hweps' :
            (w.compute n).hi.re - (w.compute n).lo.re <= eps2.val := by
          simpa [QBox.width] using hweps.1
        calc
          (z.compute n).hi.re + (w.compute n).hi.re -
              ((z.compute n).lo.re + (w.compute n).lo.re)
              <= eps2.val + eps2.val := by
            grind [Rat.sub_eq_add_neg]
          _ = eps.val := add_halves_complex eps.val
      · unfold QBox.height QComplex.add
        have hzeps' :
            (z.compute n).hi.im - (z.compute n).lo.im <= eps2.val := by
          simpa [QBox.height] using hzeps.2
        have hweps' :
            (w.compute n).hi.im - (w.compute n).lo.im <= eps2.val := by
          simpa [QBox.height] using hweps.2
        calc
          (z.compute n).hi.im + (w.compute n).hi.im -
              ((z.compute n).lo.im + (w.compute n).lo.im)
              <= eps2.val + eps2.val := by
            grind [Rat.sub_eq_add_neg]
          _ = eps.val := add_halves_complex eps.val

theorem add_valid {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid) : (add z w).Valid :=
  addCompute_valid hz hw

theorem negCompute_valid {z : ComplexRaw}
    (hz : z.Valid) :
    ComplexRaw.ValidCompute (fun n =>
      let Z := z.compute n
      { lo := { re := -Z.hi.re, im := -Z.hi.im },
        hi := { re := -Z.lo.re, im := -Z.lo.im } }) := by
  constructor
  · intro n
    have hzre := valid_re_order hz n
    have hzim := valid_im_order hz n
    constructor
    · unfold QBox.width
      change 0 <= -(z.compute n).lo.re - -(z.compute n).hi.re
      grind [Rat.sub_eq_add_neg]
    · unfold QBox.height
      change 0 <= -(z.compute n).lo.im - -(z.compute n).hi.im
      grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hznm := hz.2.1 n m hnm
      constructor
      · exact Rat.neg_le_neg hznm.2.1
      · constructor
        · exact Rat.neg_le_neg hznm.1
        · constructor
          · exact Rat.neg_le_neg hznm.2.2.2
          · exact Rat.neg_le_neg hznm.2.2.1
    · intro eps
      obtain ⟨N, hN⟩ := hz.2.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      have hzeps := hN n hn
      constructor
      · unfold QBox.width
        change -(z.compute n).lo.re - -(z.compute n).hi.re <= eps.val
        have hzeps' :
            (z.compute n).hi.re - (z.compute n).lo.re <= eps.val := by
          simpa [QBox.width] using hzeps.1
        grind [Rat.sub_eq_add_neg]
      · unfold QBox.height
        change -(z.compute n).lo.im - -(z.compute n).hi.im <= eps.val
        have hzeps' :
            (z.compute n).hi.im - (z.compute n).lo.im <= eps.val := by
          simpa [QBox.height] using hzeps.2
        grind [Rat.sub_eq_add_neg]

theorem neg_valid {z : ComplexRaw} (hz : z.Valid) : (neg z).Valid :=
  negCompute_valid hz

theorem sub_valid {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid) : (sub z w).Valid :=
  add_valid hz (neg_valid hw)

def mul (z w : ComplexRaw) : ComplexRaw where
  compute := fun eps => QBox.mul (z.compute eps) (w.compute eps)

instance : HMul ComplexRaw ComplexRaw ComplexRaw where
  hMul := mul

def divReal (z : ComplexRaw) (x : RealRaw) : ComplexRaw where
  compute := fun eps =>
    QBox.mul (z.compute eps) (QBox.ofRealInterval ((x.compute eps).inv))

instance : HDiv ComplexRaw RealRaw ComplexRaw where
  hDiv := divReal

def pow (z : ComplexRaw) : Nat -> ComplexRaw
  | 0 => one
  | n + 1 => pow z n * z

instance : Pow ComplexRaw Nat where
  pow := pow

def ApartZero (z : ComplexRaw) : Prop :=
  Exists fun n : Nat =>
    (z.compute n).hi.re < 0 \/ 0 < (z.compute n).lo.re \/
    (z.compute n).hi.im < 0 \/ 0 < (z.compute n).lo.im

def HasComputableInv (z : ComplexRaw) : Prop :=
  z.Valid -> ApartZero z -> Exists fun w : ComplexRaw => w.Valid

def divByApart (_z w : ComplexRaw) : Prop :=
  w.Valid -> ApartZero w -> Exists fun quotient : ComplexRaw => quotient.Valid

end ComplexRaw

end ComputableAnalysis
