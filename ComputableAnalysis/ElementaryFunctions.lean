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
