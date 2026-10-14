import ComputableAnalysis.ExponentialComputations.CompoundLimit
import ComputableAnalysis.ExponentialComputations.RealExponential
import ComputableAnalysis.ModularForms.ExponentialLiftAgreement
import ComputableAnalysis.ExponentialComputations.IntegralLogarithm
import ComputableAnalysis.ExponentialComputations.ComplexFunctions
import ComputableAnalysis.ElementaryRational

/-! One function-level API for proved exponential computations.
An implementation may be registered only after its exact agreement theorem
has been proved. This is a comparison package, not an assumed characterization
or an existence theorem. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert ModularForms

/-! Represented-point computations remain available as derived operations.
The function representations exported below have rational sampling domains. -/

structure Implementation where
  eval : Scalar → Scalar
  agrees : ∀ z, (eval z).val.Equiv (entireExponentialValue z).val

namespace Implementation
/-- Agreement is with a common reference, so callers need no pairwise table. -/
theorem equivalent (f g : Implementation) (z : Scalar) :
    (f.eval z).val.Equiv (g.eval z).val :=
  equiv_trans (f.eval z).property (entireExponentialValue z).property (g.eval z).property
    (f.agrees z) (equiv_symm (g.agrees z))

theorem congr (f : Implementation) (z w : Scalar) (h : z.val.Equiv w.val) :
    (f.eval z).val.Equiv (f.eval w).val :=
  equiv_trans (f.eval z).property (entireExponentialValue z).property (f.eval w).property
    (f.agrees z) (equiv_trans (entireExponentialValue z).property
      (entireExponentialValue w).property (f.eval w).property
      (entireExponentialValue_congr z w h) (equiv_symm (f.agrees w)))

def realEval (f : Implementation) (x : RealInput) : RealInput :=
  ⟨(f.eval (realAxis x)).val.realPart,realPart_valid (f.eval (realAxis x)).property⟩

theorem realEval_agrees (f : Implementation) (x : RealInput) :
    (f.realEval x).val.Equiv (exp x).val := realPart_equiv (f.agrees (realAxis x))
end Implementation

def powerSeries : Implementation :=
  ⟨entireExponentialValue,fun z => equiv_refl _ (entireExponentialValue z).property⟩
def compoundInterest : Implementation := ⟨compoundValue,compoundValue_equiv_powerSeries⟩
def linearODE : Implementation := ⟨MatrixExponential.scalarExponential,scalarExponential_agreement⟩

/-- The bounded-input Taylor construction is covered by the same agreement
network, without narrowing its inputs to rational constants. -/
theorem representedTaylor_agrees {C : Rat} (A : ComplexExponentialLift.BoundedInput C) :
    (ComplexExponentialLift.BoundedInput.exponential A).Equiv
      (powerSeries.eval ⟨A.raw,A.valid⟩).val := equiv_symm (entireExponential_legacy_lift A)

/-- Logarithm computations register one proved agreement, rather than a
pairwise comparison with every existing algorithm. -/
structure LogImplementation where
  eval : PositiveInput → RealInput
  agrees : ∀ x, (eval x).val.Equiv (log x).val

namespace LogImplementation
theorem equivalent (f g : LogImplementation) (x : PositiveInput) :
    (f.eval x).val.Equiv (g.eval x).val :=
  RealRaw.equiv_trans (f.eval x).property (log x).property (g.eval x).property
    (f.agrees x) (RealRaw.equiv_symm (g.agrees x))

theorem congr (f : LogImplementation) (x y : PositiveInput)
    (h : x.val.val.Equiv y.val.val) : (f.eval x).val.Equiv (f.eval y).val :=
  RealRaw.equiv_trans (f.eval x).property (log x).property (f.eval y).property
    (f.agrees x) (RealRaw.equiv_trans (log x).property (log y).property (f.eval y).property
      (log_congr x y h) (RealRaw.equiv_symm (f.agrees y)))

theorem exp_eval (f : LogImplementation) (x : PositiveInput) :
    (exp (f.eval x)).val.Equiv x.val.val :=
  RealRaw.equiv_trans (exp (f.eval x)).property (exp (log x)).property x.val.property
    (exp_congr _ _ (f.agrees x)) (exp_log x)
end LogImplementation

def logarithmContinuation : LogImplementation :=
  ⟨log,fun x => RealRaw.equiv_refl _ (log x).property⟩
def reciprocalIntegral : LogImplementation := ⟨integralLog,integralLog_equiv_log⟩

/-- An independently justified inversion computation joins the same real
exponential API by proving its integral inverse law. -/
theorem real_computation_agrees_of_integral_inverse (f : RealInput → PositiveInput)
    (hinverse : ∀ x, (integralLog (f x)).val.Equiv x.val) (x : RealInput) :
    (f x).val.val.Equiv (exp x).val := exp_unique_of_integralLog x (f x) (hinverse x)

namespace Derived
/-! Explicit names for represented evaluation. Parent names are retained for
compatibility with existing exact theorems and applications. -/
export ComputableAnalysis.ExponentialComputations
  (Implementation powerSeries compoundInterest linearODE representedTaylor_agrees
    LogImplementation logarithmContinuation reciprocalIntegral
    real_computation_agrees_of_integral_inverse)
namespace Implementation
export ComputableAnalysis.ExponentialComputations.Implementation
  (equivalent congr realEval realEval_agrees)
end Implementation
namespace LogImplementation
export ComputableAnalysis.ExponentialComputations.LogImplementation (equivalent congr exp_eval)
end LogImplementation
end Derived

namespace Rational

/-- A rational-complex implementation with proved overlap agreement. -/
abbrev Implementation := ComplexFunctionImplementation ElementaryRational.exponential

def powerSeries : Implementation where
  raw := ElementaryRational.exponential
  valid := ElementaryRational.exponential_valid
  agrees := FunctionRaw.agreeOnCommonDomain_refl _ ElementaryRational.exponential_valid

theorem rational_powerSeries_agrees (z : QComplex) :
    (entireExponentialValue ⟨ofQComplex z,ofQComplex_valid z⟩).val.Equiv
      (ElementaryRational.exponentialValue z) :=
  entireExponential_legacy_rational z (QComplex.normBound z)
    (QComplex.normBound_nonneg z) Rat.le_refl

private def sampleDerived (f : Derived.Implementation) : FunctionRaw where
  domain := FunctionRaw.entire
  compute z _ := (f.eval ⟨ofQComplex z,ofQComplex_valid z⟩).val.compute

private theorem sampleDerived_valid (f : Derived.Implementation) :
    (sampleDerived f).Valid := fun z _ => (f.eval ⟨ofQComplex z,ofQComplex_valid z⟩).property

private def registerDerived (f : Derived.Implementation) : Implementation where
  raw := sampleDerived f
  valid := sampleDerived_valid f
  agrees := by
    intro z _ _
    exact equiv_symm (equiv_trans
      (f.eval ⟨ofQComplex z,ofQComplex_valid z⟩).property
      (entireExponentialValue ⟨ofQComplex z,ofQComplex_valid z⟩).property
      (ElementaryRational.exponentialValue_valid z)
      (f.agrees _) (rational_powerSeries_agrees z))

def compoundInterest : Implementation := registerDerived Derived.compoundInterest
def linearODE : Implementation := registerDerived Derived.linearODE

namespace Implementation
def eval (f : Implementation) (z : QComplex) (hz : f.raw.domain z) : ComplexRaw :=
  f.raw.evalRaw z hz

theorem equivalent (f g : Implementation) : f.raw.AgreeOnCommonDomain g.raw := by
  intro z hz hw
  exact equiv_trans (f.valid z hz) (ElementaryRational.exponential_valid z trivial)
    (g.valid z hw) (equiv_symm (f.agrees z trivial hz)) (g.agrees z trivial hw)
end Implementation

/-- The registry uses the existing overlap relation; no quotient or global
transitivity across arbitrary partial domains is introduced. -/
def exponentialFunction : ComplexFunction :=
  (ElementaryRational.exponentialFunction.withAlternative
    compoundInterest.raw compoundInterest.valid compoundInterest.agrees).withAlternative
    linearODE.raw linearODE.valid linearODE.agrees

def positiveRationalInput (x : Rat) (hx : 0 < x) : PositiveInput :=
  ⟨⟨RealRaw.ofRat x,RealRaw.ofRat_valid x⟩,⟨0,hx⟩⟩

/-- Positive rational logarithm sampled by the actual reciprocal-integral
computation. Represented endpoints are the separate derived operation. -/
def logarithm : PartialRealFunRaw where
  definedAt x := 0 < x
  compute x hx := (integralLog (positiveRationalInput x hx)).val.compute

theorem logarithm_valid : logarithm.Valid :=
  fun x hx => (integralLog (positiveRationalInput x hx)).property

abbrev LogImplementation := PartialRealFunctionImplementation logarithm

def reciprocalIntegral : LogImplementation where
  raw := logarithm
  valid := logarithm_valid
  agrees := PartialRealFunRaw.agreeOnOverlap_refl logarithm logarithm_valid

def logarithmContinuation : LogImplementation where
  raw := {
    definedAt x := 0 < x
    compute x hx := (log (positiveRationalInput x hx)).val.compute }
  valid := fun x hx => (log (positiveRationalInput x hx)).property
  agrees := by
    intro x hx _
    exact integralLog_equiv_log (positiveRationalInput x hx)

namespace LogImplementation
theorem equivalent (f g : LogImplementation)
    (cover : ∀ x, f.raw.definedAt x → g.raw.definedAt x → logarithm.definedAt x) :
    f.raw.AgreeOnOverlap g.raw := by
  intro x hx hy
  let hp := cover x hx hy
  exact RealRaw.equiv_trans (x := f.raw.evalRaw x hx) (y := logarithm.evalRaw x hp)
    (z := g.raw.evalRaw x hy) (f.valid x hx) (logarithm_valid x hp) (g.valid x hy)
    (RealRaw.equiv_symm (f.agrees x hp hx)) (g.agrees x hp hy)
end LogImplementation

def logarithmFunction : PartialRealFunction :=
  (PartialRealFunction.ofRaw logarithm logarithm_valid).withAlternative
    logarithmContinuation.raw logarithmContinuation.valid logarithmContinuation.agrees

end Rational
end ComputableAnalysis.ExponentialComputations
