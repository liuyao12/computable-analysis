import ComputableAnalysis.AbelianIntegrals
import ComputableAnalysis.Differential
import ComputableAnalysis.FunctionDomains
import ComputableAnalysis.PowerSeries

/-!
# Elementary function representations

This file names particular representations of elementary functions.  The
power-series machinery lives in `PowerSeries.lean`; alternative constructions,
such as Euler limits for `exp` or inverse-abelian-integral constructions for
trig functions, should be added here or in sibling representation files.

The interesting theorems are agreement statements between representations on
their common domains.
-/

namespace ComputableAnalysis

namespace exp

theorem qcomplex_one_pow (n : Nat) :
    QComplex.pow QComplex.one n = QComplex.one := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [QComplex.pow, ih]
      grind [QComplex.mul, QComplex.one]

/-- A positive computable real, witnessed by one rational lower bound that
holds at every stage.  This constructive positivity is the domain condition
for arbitrary-base powers. -/
structure PositiveRealRaw where
  value : RealRaw
  valid : value.Valid
  lower_bound : Rat
  lower_bound_pos : 0 < lower_bound
  lower_bound_le : forall n, lower_bound <= (value.compute n).lo

namespace PositiveRealRaw

/-- Natural powers of a positive raw real, defined by repeated
multiplication. -/
def natPowRaw (value : RealRaw) : Nat -> RealRaw
  | 0 => RealRaw.one
  | n + 1 => natPowRaw value n * value

def natPow (base : PositiveRealRaw) : Nat -> RealRaw :=
  natPowRaw base.value

/-- A uniform rational upper bound obtained from the zeroth interval of a
positive raw real.  Validity makes every later interval lie inside this one. -/
def upperBound (base : PositiveRealRaw) : Rat :=
  (base.value.compute 0).hi

theorem upperBound_pos (base : PositiveRealRaw) : 0 < upperBound base := by
  unfold upperBound
  have hlower := base.lower_bound_le 0
  have horder := RealRaw.interval_order_of_valid base.value base.valid 0
  have hle : base.lower_bound <= (base.value.compute 0).hi :=
    Rat.le_trans hlower horder
  grind [base.lower_bound_pos]

/-- Every stage of a positive raw real is nonnegative and bounded above by
its zeroth-stage upper endpoint. -/
theorem base_bounds (base : PositiveRealRaw) (k : Nat) :
    0 <= (base.value.compute k).lo /\
      (base.value.compute k).hi <= upperBound base := by
  constructor
  · exact Rat.le_trans (Rat.le_of_lt base.lower_bound_pos)
      (base.lower_bound_le k)
  · unfold upperBound
    exact (base.valid.2.1 0 k (Nat.zero_le k)).2.2

/-- Repeated multiplication preserves validity, constructive positivity, and
a uniform rational upper bound.  The proof uses only finite interval product
arithmetic; no completed-real multiplication is involved. -/
theorem natPow_valid_and_bounds (base : PositiveRealRaw) :
    forall n,
      (natPow base n).Valid /\
        forall k,
          base.lower_bound ^ n <= ((natPow base n).compute k).lo /\
            ((natPow base n).compute k).hi <= upperBound base ^ n
  | 0 => by
      constructor
      · simpa [natPow, natPowRaw, RealRaw.one] using
          (RealRaw.ofRat_valid (1 : Rat))
      · intro k
        change base.lower_bound ^ 0 <= (1 : Rat) /\
          (1 : Rat) <= upperBound base ^ 0
        simp
  | n + 1 => by
      rcases natPow_valid_and_bounds base n with ⟨hprevious_valid, hprevious⟩
      have hbase_bounds : forall k,
          0 <= (base.value.compute k).lo /\
            (base.value.compute k).hi <= upperBound base :=
        base_bounds base
      have hprevious_nonneg : forall k,
          0 <= ((natPow base n).compute k).lo := by
        intro k
        exact Rat.le_trans
          (Rat.pow_nonneg (Rat.le_of_lt base.lower_bound_pos))
          (hprevious k).1
      have hpower_valid : (natPow base (n + 1)).Valid := by
        change (natPow base n * base.value).Valid
        exact RealRaw.mul_valid_of_nonneg_bounded
          hprevious_valid base.valid
          (Rat.pow_pos (upperBound_pos base)) (upperBound_pos base)
          (fun k => ⟨hprevious_nonneg k, (hprevious k).2⟩)
          hbase_bounds
      refine ⟨hpower_valid, ?_⟩
      intro k
      have hbase := hbase_bounds k
      have hprevious_bounds := hprevious k
      have hbase_nonneg : 0 <= (base.value.compute k).lo := hbase.1
      have hbase_hi_nonneg : 0 <= (base.value.compute k).hi := by
        have horder := RealRaw.interval_order_of_valid base.value base.valid k
        exact Rat.le_trans hbase_nonneg horder
      have hcompute :
          ((natPow base n * base.value).compute k) =
            { lo := ((natPow base n).compute k).lo * (base.value.compute k).lo,
              hi := ((natPow base n).compute k).hi * (base.value.compute k).hi } := by
        change QBox.mulRealInterval
            ((natPow base n).compute k).lo ((natPow base n).compute k).hi
            (base.value.compute k).lo (base.value.compute k).hi = _
        exact QBox.mulRealInterval_of_nonneg
          (hprevious_nonneg k)
          (RealRaw.interval_order_of_valid
            (natPow base n) hprevious_valid k)
          hbase_nonneg
          (RealRaw.interval_order_of_valid base.value base.valid k)
      change base.lower_bound ^ (n + 1) <=
          ((natPow base n * base.value).compute k).lo /\
        ((natPow base n * base.value).compute k).hi <=
          upperBound base ^ (n + 1)
      rw [hcompute]
      constructor
      · calc
          base.lower_bound ^ (n + 1) =
              base.lower_bound ^ n * base.lower_bound := by
                rw [Rat.pow_succ]
          _ <= ((natPow base n).compute k).lo * base.lower_bound :=
            Rat.mul_le_mul_of_nonneg_right hprevious_bounds.1
              (Rat.le_of_lt base.lower_bound_pos)
          _ <= ((natPow base n).compute k).lo * (base.value.compute k).lo :=
            Rat.mul_le_mul_of_nonneg_left (base.lower_bound_le k)
              (hprevious_nonneg k)
      · calc
          ((natPow base n).compute k).hi * (base.value.compute k).hi <=
              upperBound base ^ n * (base.value.compute k).hi :=
            Rat.mul_le_mul_of_nonneg_right hprevious_bounds.2
              hbase_hi_nonneg
          _ <= upperBound base ^ n * upperBound base :=
            Rat.mul_le_mul_of_nonneg_left hbase.2
              (Rat.pow_nonneg (Rat.le_of_lt (upperBound_pos base)))
          _ = upperBound base ^ (n + 1) := by
            rw [Rat.pow_succ]

theorem natPow_valid (base : PositiveRealRaw) (n : Nat) :
    (natPow base n).Valid :=
  (natPow_valid_and_bounds base n).1

theorem natPow_lower_bound (base : PositiveRealRaw) (n k : Nat) :
    base.lower_bound ^ n <= ((natPow base n).compute k).lo :=
  (natPow_valid_and_bounds base n).2 k |>.1

theorem natPow_upper_bound (base : PositiveRealRaw) (n k : Nat) :
    ((natPow base n).compute k).hi <= upperBound base ^ n :=
  (natPow_valid_and_bounds base n).2 k |>.2

/-- Each repeated-multiplication power is itself a positive raw real. -/
def natPowPositive (base : PositiveRealRaw) (n : Nat) : PositiveRealRaw where
  value := natPow base n
  valid := natPow_valid base n
  lower_bound := base.lower_bound ^ n
  lower_bound_pos := Rat.pow_pos base.lower_bound_pos
  lower_bound_le := natPow_lower_bound base n

end PositiveRealRaw

/-- A verified extension of repeated multiplication from natural to rational
exponents for one positive base.

The `denominator_power` field says that the supplied rational power is the
positive `q`th root of the corresponding natural power.  Negative exponents
are governed by the additive law, so this interface does not conceal a
choice of logarithm or a real-completeness argument. -/
structure RationalPowerExtension (base : PositiveRealRaw) where
  power : Rat -> RealRaw
  power_valid : forall q, (power q).Valid
  power_lower_bound : Rat -> Rat
  power_lower_bound_pos : forall q, 0 < power_lower_bound q
  power_lower_bound_le : forall q n,
    power_lower_bound q <= ((power q).compute n).lo
  zero_equiv_one : (power 0).Equiv RealRaw.one
  natural_equiv_natPow : forall n : Nat,
    (power (n : Rat)).Equiv (PositiveRealRaw.natPow base n)
  add_equiv_mul : forall p q, (power (p + q)).Equiv (power p * power q)
  denominator_power : forall p q : Nat, 0 < q ->
    (PositiveRealRaw.natPowRaw (power ((p : Rat) / (q : Rat))) q).Equiv
      (PositiveRealRaw.natPow base p)

namespace RationalPowerExtension

/-- The rational-input exponential function induced by a rational-power
extension.  It is total on rational inputs and is the representation that
later extends continuously to arbitrary computable-real exponents. -/
def toPartialRealFunRaw {base : PositiveRealRaw}
    (powers : RationalPowerExtension base) : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ => (powers.power x).compute

theorem toPartialRealFunRaw_valid {base : PositiveRealRaw}
    (powers : RationalPowerExtension base) :
    forall x h, RealRaw.ValidCompute (powers.toPartialRealFunRaw.compute x h) := by
  intro x _h
  exact powers.power_valid x

/-- Restrict rational powers to a rational interval for the derivative and
FTC interfaces. -/
def onInterval {base : PositiveRealRaw} (powers : RationalPowerExtension base)
    (a b : Rat) : FunctionOnInterval where
  raw := powers.toPartialRealFunRaw
  lower := a
  upper := b
  defined_on := by
    intro _ _
    trivial
  valid_on := by
    intro x h
    exact powers.toPartialRealFunRaw_valid x h

/-- The topology-free continuity obligation for rational powers as the
exponent varies over a rational interval.  This is deliberately separate from
the root and additive-law fields: a root construction must still prove that
nearby rational exponents give arbitrarily close interval values. -/
def ContinuousInExponent {base : PositiveRealRaw}
    (powers : RationalPowerExtension base) : Prop :=
  forall a b, EpsilonDeltaContinuousOn (powers.onInterval a b)

/-- A direct, rational-step derivative certificate at one rational input.
This is deliberately the pointwise form needed for the characterization of
Euler's number, rather than a hidden appeal to an ambient completed real line. -/
structure HasDerivativeAt (powers : RationalPowerExtension base)
    (x : Rat) (derivative : RealRaw) where
  derivative_valid : derivative.Valid
  stepPrecision : Nat -> Nat
  /-- The interval evaluation stage may depend on the nonzero rational step,
  since quotienting a fixed-width enclosure by a smaller step magnifies its
  uncertainty. -/
  evalPrecision : Rat -> Nat -> Nat
  close :
    forall h n, h ≠ 0 ->
      qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
      intervalNearAtPrecision
        (QInterval.differenceQuotient
          ((powers.power (x + h)).compute (evalPrecision h n))
          ((powers.power x).compute (evalPrecision h n)) h)
        (derivative.compute (evalPrecision h n)) n

/-- The alternative characterization of the Euler base: its rational powers
have derivative `1` at exponent zero. -/
def HasUnitDerivativeAtZero {base : PositiveRealRaw}
    (powers : RationalPowerExtension base) : Prop :=
  Nonempty (HasDerivativeAt powers 0 RealRaw.one)

end RationalPowerExtension

/-- A rational-input exponential representation attached to a positive-base
rational-power extension. -/
structure ExponentialFunction {base : PositiveRealRaw}
    (powers : RationalPowerExtension base) where
  raw : PartialRealFunRaw
  defined_everywhere : forall x, raw.definedAt x
  valid : forall x h, RealRaw.ValidCompute (raw.compute x h)
  agrees_with_rational_powers : forall q,
    (raw.evalRaw q (defined_everywhere q)).Equiv (powers.power q)
  continuous_in_exponent : powers.ContinuousInExponent

namespace ExponentialFunction

/-- Euler's number as the value at `1` of any chosen exponential
representation. -/
def eAtOne {base : PositiveRealRaw} {powers : RationalPowerExtension base}
    (E : ExponentialFunction powers) : RealRaw :=
  E.raw.evalRaw 1 (E.defined_everywhere 1)

/-- The exponential representation on a finite rational interval. -/
def onInterval {base : PositiveRealRaw} {powers : RationalPowerExtension base}
    (E : ExponentialFunction powers) (a b : Rat) : FunctionOnInterval where
  raw := E.raw
  lower := a
  upper := b
  defined_on := by
    intro x _hx
    exact E.defined_everywhere x
  valid_on := E.valid

/-- The analytic milestone `d/dx exp(x) = exp(x)` on a chosen interval. -/
def SolvesSelfDerivativeOn {base : PositiveRealRaw}
    {powers : RationalPowerExtension base} (E : ExponentialFunction powers)
    (a b : Rat) : Prop :=
  Nonempty (SolvesSelfDerivativeOnInterval (E.onInterval a b))

/-- The uniqueness statement connecting the two definitions of `e`: a
positive base whose rational powers have unit derivative at zero must equal
the value at `1` of the chosen exponential. -/
def UnitDerivativeCharacterizesE {base : PositiveRealRaw}
    {powers : RationalPowerExtension base} (E : ExponentialFunction powers) : Prop :=
  forall {candidateBase : PositiveRealRaw}
      (candidate : RationalPowerExtension candidateBase),
    candidate.HasUnitDerivativeAtZero ->
      candidateBase.value.Equiv E.eAtOne

end ExponentialFunction

/-- The power-series representation of exponential, defined on all rational
complex inputs. -/
def ps : FunctionRaw where
  domain := FunctionRaw.entire
  compute := fun z _ => ComplexSeries.expAt z

def eulerFuel (eps : QPos) : Nat := eps.val.den + 1

def eulerCenter (z : QComplex) (eps : QPos) : QComplex :=
  let m := eulerFuel eps
  QComplex.pow (QComplex.add QComplex.one (QComplex.divRat z (m : Rat))) m

theorem eulerCenter_zero (eps : QPos) :
    eulerCenter QComplex.zero eps = QComplex.one := by
  have hbase :
      QComplex.add QComplex.one
        (QComplex.divRat QComplex.zero (eulerFuel eps : Rat)) = QComplex.one := by
    grind [QComplex.add, QComplex.divRat, QComplex.zero, QComplex.one]
  simp [eulerCenter, hbase, qcomplex_one_pow]

def eulerBoxAt (z : QComplex) (eps : QPos) : QBox :=
  ComplexSeries.errorBox (eulerCenter z eps) eps

def eulerAt (z : QComplex) : Nat -> QBox :=
  fun n => eulerBoxAt z (if hn : n = 0 then
      { val := 1, property := by native_decide }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) })

/-- An Euler-limit representation `lim (1 + z / n)^n`. -/
def euler : FunctionRaw where
  domain := FunctionRaw.entire
  compute := fun z _ => eulerAt z

/-- Exponential as inverse to the logarithmic integral `∫_1^x dt/t`.

This is a semantic alias for the `FunctionRaw` obtained after the logarithmic
integral has been constructed and inverted. Unlike `ps` and `euler`, the
actual raw algorithm is not filled in here yet. -/
abbrev InverseLogIntegral := FunctionRaw

def agreesWithEulerLimit (eulerLimit : FunctionRaw) : Prop :=
  FunctionRaw.AgreeOnCommonDomain ps eulerLimit

def agreesWithInverseLogIntegral (integralInverse : InverseLogIntegral) : Prop :=
  FunctionRaw.AgreeOnCommonDomain ps integralInverse

def eulerLimitAgreesWithInverseLogIntegral
    (eulerLimit : FunctionRaw) (integralInverse : InverseLogIntegral) : Prop :=
  FunctionRaw.AgreeOnCommonDomain eulerLimit integralInverse

/-- The three standard constructive representations of exponential agree:
power series, Euler limit, and inverse of the logarithmic integral. -/
def representationsAgree (eulerLimit : FunctionRaw)
    (integralInverse : InverseLogIntegral) : Prop :=
  agreesWithEulerLimit eulerLimit /\
  agreesWithInverseLogIntegral integralInverse /\
  eulerLimitAgreesWithInverseLogIntegral eulerLimit integralInverse

def PowerSeriesEulerEstimate (eulerLimit : FunctionRaw) : Prop :=
  FunctionRaw.AgreeOnCommonDomain ps eulerLimit

def PowerSeriesIntegralInverseEstimate (integralInverse : InverseLogIntegral) : Prop :=
  FunctionRaw.AgreeOnCommonDomain ps integralInverse

def EulerIntegralInverseEstimate
    (eulerLimit : FunctionRaw) (integralInverse : InverseLogIntegral) : Prop :=
  FunctionRaw.AgreeOnCommonDomain eulerLimit integralInverse

theorem representationsAgree_of_estimates
    {eulerLimit : FunctionRaw} {integralInverse : InverseLogIntegral}
    (hpsEuler : PowerSeriesEulerEstimate eulerLimit)
    (hpsIntegral : PowerSeriesIntegralInverseEstimate integralInverse)
    (heulerIntegral : EulerIntegralInverseEstimate eulerLimit integralInverse) :
    representationsAgree eulerLimit integralInverse :=
  ⟨hpsEuler, hpsIntegral, heulerIntegral⟩

/-- The raw computable number `e`, evaluated from a future inverse-log-integral
representation.  The domain proof is explicit because that representation has
not yet been constructed here. -/
def eInverseLogIntegralRaw
    (integralInverse : InverseLogIntegral)
    (h : integralInverse.domain (QComplex.ofRat 1)) : RealRaw :=
  (FunctionRaw.realPartOnRealAxis integralInverse).evalRaw 1 h

/-- Real-axis power-series exponential. -/
def realPowerSeries : PartialRealFunRaw :=
  FunctionRaw.realPartOnRealAxis ps

/-- Real-axis Euler-limit exponential. -/
def realEuler : PartialRealFunRaw :=
  FunctionRaw.realPartOnRealAxis euler

/-- A finite interval branch of exponential built as the inverse of the
logarithmic integral.

The source interval is a positive rational interval for the variable `x` in
`log x = int_1^x dt/t`.  The target side is the rational input variable `y`
for `exp y`.  A global real exponential can later choose such a branch
effectively for each rational `y`; the finite branch is the object needed for
the inverse-function theorem and for local calculus proofs. -/
structure LogIntegralInverseBranch where
  sourceLower : Rat
  sourceUpper : Rat
  sourceLower_pos : 0 < sourceLower
  inputDomain : Rat -> Prop
  logBranch : InvertibleFunctionOnInterval
  same_source_lower : logBranch.function.lower = sourceLower
  same_source_upper : logBranch.function.upper = sourceUpper
  log_is_integral_of_oneOverX : Prop
  inverse : InverseRaw logBranch
  targetValue : (y : Rat) -> inputDomain y -> InRangeRaw logBranch
  targetValue_equiv :
    forall y hy, (targetValue y hy).value.Equiv (RealRaw.ofRat y)

namespace LogIntegralInverseBranch

def kernel (branch : LogIntegralInverseBranch) : FunctionOnInterval :=
  RatFun.oneOverXOnPositiveInterval
    branch.sourceLower branch.sourceUpper branch.sourceLower_pos

def toPartialRealFunRaw (branch : LogIntegralInverseBranch) : PartialRealFunRaw where
  definedAt := branch.inputDomain
  compute := fun y hy n => (branch.inverse.apply (branch.targetValue y hy)).compute n

theorem toPartialRealFunRaw_valid (branch : LogIntegralInverseBranch) :
    forall y hy,
      RealRaw.ValidCompute ((branch.toPartialRealFunRaw).compute y hy) := by
  intro y hy
  exact branch.inverse.apply_valid (branch.targetValue y hy)

theorem log_value_overlaps_target
    (branch : LogIntegralInverseBranch) (y : Rat) (hy : branch.inputDomain y)
    (n : Nat) :
    QInterval.Overlaps
      (branch.logBranch.continuous.regular.evalInterval
        ((branch.toPartialRealFunRaw).compute y hy n)
        (branch.inverse.preimage_subinterval (branch.targetValue y hy) n)
        n)
      ((branch.targetValue y hy).value.compute n) := by
  exact branch.inverse.value_overlaps (branch.targetValue y hy) n

theorem target_equiv_rational
    (branch : LogIntegralInverseBranch) (y : Rat) (hy : branch.inputDomain y) :
    (branch.targetValue y hy).value.Equiv (RealRaw.ofRat y) :=
  branch.targetValue_equiv y hy

end LogIntegralInverseBranch

def fromLogIntegral (branch : LogIntegralInverseBranch) : PartialRealFunRaw :=
  branch.toPartialRealFunRaw

/-- The logarithm function represented by the logarithmic integral branch itself.
It is a `FunctionOnInterval`, hence an instance of the foundational
single-variable function notion: rational input plus stage returns a raw real
interval sequence. -/
def logFromIntegral (branch : LogIntegralInverseBranch) : FunctionOnInterval :=
  branch.logBranch.function

/-- The inverse-log-integral exponential representation is a partial real
function in the sense of Section 1.4. -/
def expFromLogIntegral (branch : LogIntegralInverseBranch) : PartialRealFunRaw :=
  fromLogIntegral branch

def eFromLogIntegralBranchRaw
    (branch : LogIntegralInverseBranch) (h : branch.inputDomain 1) : RealRaw :=
  (fromLogIntegral branch).evalRaw 1 h

theorem eFromLogIntegralBranchRaw_valid
    (branch : LogIntegralInverseBranch) (h : branch.inputDomain 1) :
    RealRaw.Valid (eFromLogIntegralBranchRaw branch h) :=
  branch.toPartialRealFunRaw_valid 1 h

/-- A finite interval of the `exp` input line covered by a log-integral
inverse branch. -/
structure FromLogIntegralOnInterval where
  branch : LogIntegralInverseBranch
  lower : Rat
  upper : Rat
  defined_on : forall y, inDomainInterval lower upper y -> branch.inputDomain y

namespace FromLogIntegralOnInterval

def toFunctionOnInterval (E : FromLogIntegralOnInterval) : FunctionOnInterval where
  raw := fromLogIntegral E.branch
  lower := E.lower
  upper := E.upper
  defined_on := E.defined_on
  valid_on := E.branch.toPartialRealFunRaw_valid

end FromLogIntegralOnInterval

def realPowerSeriesOnInterval (a b : Rat)
    (valid : forall x, inDomainInterval a b x ->
      RealRaw.ValidCompute (realPowerSeries.compute x trivial)) :
    FunctionOnInterval where
  raw := {
    definedAt := inDomainInterval a b
    compute := fun x _hx => realPowerSeries.compute x trivial
  }
  lower := a
  upper := b
  defined_on := fun _ hx => hx
  valid_on := valid

/-- Data reducing the equality between `exp.ps` and the inverse-log-integral
exponential to the constructive uniqueness theorem for `f' = f`, `f(0)=1`.

This is the calculus route: prove each representation solves the same
differential equation with the same initial value, then use the uniqueness
principle. -/
structure PowerSeriesLogIntegralInverseComparison (a b : Rat) where
  ps_valid :
    forall x, inDomainInterval a b x ->
      RealRaw.ValidCompute (realPowerSeries.compute x trivial)
  logInv : FromLogIntegralOnInterval
  ps_solves :
    SolvesSelfDerivativeOnInterval (realPowerSeriesOnInterval a b ps_valid)
  logInv_solves :
    SolvesSelfDerivativeOnInterval logInv.toFunctionOnInterval

theorem powerSeries_equiv_logIntegralInverse_on_interval
    (uniq : SelfDerivativeInitialValueUnique)
    {a b : Rat}
    (comparison : PowerSeriesLogIntegralInverseComparison a b) :
    FunctionOnInterval.Equivalent
      (realPowerSeriesOnInterval a b comparison.ps_valid)
      comparison.logInv.toFunctionOnInterval :=
  uniq
    (realPowerSeriesOnInterval a b comparison.ps_valid)
    comparison.logInv.toFunctionOnInterval
    comparison.ps_solves
    comparison.logInv_solves

/-- Finite product estimate behind the comparison between
`lim (1 + x/n)^n` and the inverse of `int_1^x dt/t`.

This is a rational-only theorem shape: products over small multiplicative
increments should agree with the logarithmic-integral inverse boxes. -/
def EulerProductIntegralEstimate (integralInverse : InverseLogIntegral) : Prop :=
  EulerIntegralInverseEstimate euler integralInverse

end exp

namespace sin

/-- The power-series representation of sine, defined on all rational complex
inputs. -/
def ps : FunctionRaw where
  domain := FunctionRaw.entire
  compute := fun z _ => ComplexSeries.sinAt z

/-- The power-series sine agrees with a
geometric/inverse-abelian-integral representation on the shared branch domain. -/
def agreesWithAbelianInverse (abelianInverse : FunctionRaw) : Prop :=
  FunctionRaw.AgreeOnCommonDomain ps abelianInverse

/-- Same agreement target, when the alternative representation is packaged as
an inverse to an abelian integral. -/
def agreesWithAbelianInverseRep (abelianInverse : AbelianIntegral.InverseRepresentation) : Prop :=
  FunctionRaw.AgreeOnCommonDomain ps abelianInverse.inverse

end sin

namespace cos

/-- The power-series representation of cosine, defined on all rational complex
inputs. -/
def ps : FunctionRaw where
  domain := FunctionRaw.entire
  compute := fun z _ => ComplexSeries.cosAt z

/-- Target shape for the theorem that the power-series cosine agrees with a
geometric/inverse-abelian-integral representation on the shared branch domain. -/
def agreesWithAbelianInverse (abelianInverse : FunctionRaw) : Prop :=
  FunctionRaw.AgreeOnCommonDomain ps abelianInverse

/-- Same agreement target, when the alternative representation is packaged as
an inverse to an abelian integral. -/
def agreesWithAbelianInverseRep (abelianInverse : AbelianIntegral.InverseRepresentation) : Prop :=
  FunctionRaw.AgreeOnCommonDomain ps abelianInverse.inverse

end cos

namespace sinh

def boxAt (z : QComplex) (eps : QPos) : QBox :=
  QBox.scaleRat (1 / 2)
    (QBox.sub
      (ComplexSeries.expBoxAt z eps)
      (ComplexSeries.expBoxAt (QComplex.neg z) eps))

def computeAt (z : QComplex) : Nat -> QBox :=
  fun n => boxAt z (if hn : n = 0 then
      { val := 1, property := by native_decide }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) })

/-- Hyperbolic sine, represented constructively by `(exp z - exp (-z)) / 2`. -/
def fromExp : FunctionRaw where
  domain := FunctionRaw.entire
  compute := fun z _ => computeAt z

def agreesWithPowerSeries (ps : FunctionRaw) : Prop :=
  FunctionRaw.AgreeOnCommonDomain fromExp ps

end sinh

namespace cosh

def boxAt (z : QComplex) (eps : QPos) : QBox :=
  QBox.scaleRat (1 / 2)
    (QBox.add
      (ComplexSeries.expBoxAt z eps)
      (ComplexSeries.expBoxAt (QComplex.neg z) eps))

def computeAt (z : QComplex) : Nat -> QBox :=
  fun n => boxAt z (if hn : n = 0 then
      { val := 1, property := by native_decide }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) })

/-- Hyperbolic cosine, represented constructively by `(exp z + exp (-z)) / 2`. -/
def fromExp : FunctionRaw where
  domain := FunctionRaw.entire
  compute := fun z _ => computeAt z

def agreesWithPowerSeries (ps : FunctionRaw) : Prop :=
  FunctionRaw.AgreeOnCommonDomain fromExp ps

end cosh

end ComputableAnalysis
