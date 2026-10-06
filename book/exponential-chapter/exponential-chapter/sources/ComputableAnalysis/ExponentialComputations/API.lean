import ComputableAnalysis.ExponentialComputations.CompoundLimit
import ComputableAnalysis.ExponentialComputations.RealExponential
import ComputableAnalysis.ModularForms.ExponentialLiftAgreement
import ComputableAnalysis.ExponentialComputations.IntegralLogarithm

/-! One function-level API for proved exponential computations.
An implementation may be registered only after its exact agreement theorem
has been proved. This is a comparison package, not an assumed characterization
or an existence theorem. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert ModularForms

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
end ComputableAnalysis.ExponentialComputations
