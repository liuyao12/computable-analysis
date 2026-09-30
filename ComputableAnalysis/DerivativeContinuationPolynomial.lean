import ComputableAnalysis.RealDerivativeContinuation

/-! Every represented-coefficient polynomial has an explicit continuous divided
difference, and so do its iterated derivatives and real-axis restrictions. -/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw Continuation
namespace PolynomialFunction

/-- Build the quotient extension structurally from constants, identity, sums, products. -/
def derivativeContinuation : (p : PolynomialFunction) → (a : ComplexRaw) → a.Valid →
    DerivativeAt p.map a (p.diff.map.eval a)
  | .constant c, a, ha => derivativeAt_constant c.val a c.property ha
  | .input, a, ha => derivativeAt_identity a ha
  | .add p q, a, ha => (p.derivativeContinuation a ha).add (q.derivativeContinuation a ha)
  | .mul p q, a, ha => (p.derivativeContinuation a ha).mul (q.derivativeContinuation a ha)

def differentiable (p : PolynomialFunction) : DifferentiableOn p.map where
  derivative := p.diff.map.eval
  atPoint := fun a ha _ => p.derivativeContinuation a ha
  derivative_congr := fun ha hb _ _ he => p.diff.map.eval_congr ha hb
    (p.diff.entire _) (p.diff.entire _) he

/-- The quotient foundation supplies the full polynomial holomorphic interface.
Derivative continuity follows from differentiability of the formal derivative. -/
def quotientHolomorphic (p : PolynomialFunction) : Holomorphic p.map :=
  p.differentiable.holomorphic
    { radius := fun _ _ _ => ⟨1,by decide⟩
      inside := fun _ _ _ z _ _ => p.entire z }
    (ContinuousOn.ofAtPoint fun a ha hpa =>
      (p.diff.differentiable.continuous.atPoint a ha (p.diff.entire a)).restrict
        (fun z _ => p.diff.entire z) hpa)

/-- Its derivative computation is exactly the formal derivative evaluator. -/
theorem quotientHolomorphic_derivative (p : PolynomialFunction) (a : ComplexRaw) :
    p.quotientHolomorphic.derivative a = p.diff.map.eval a := rfl

def iteratedDerivativeContinuation (p : PolynomialFunction) (n : Nat) (a : ComplexRaw) (ha : a.Valid) :
    DerivativeAt (p.iteratedDiff n).map a ((p.iteratedDiff (n+1)).map.eval a) :=
  (p.iteratedDiff n).derivativeContinuation a ha

/-- Exact derivative identification with the existing analytic polynomial client. -/
theorem continuation_derivative_equiv (p : PolynomialFunction) (a : ComplexRaw) (ha : a.Valid) :
    ((p.derivativeContinuation a ha).quotient a).Equiv (p.holomorphic.derivative a) :=
  equiv_trans ((p.derivativeContinuation a ha).quotient_valid a ha (p.entire a))
    (p.diff.map.valid a ha (p.diff.entire a)) (p.holomorphic.atPoint a ha (p.entire a)).derivative_valid
    (p.derivativeContinuation a ha).value_at (equiv_symm (p.derivative_equiv a ha))

def realDerivativeContinuation (p : PolynomialFunction) (a : RealRaw) (ha : a.Valid) :
    RealFunctionTheory.DerivativeAt p.map.realRestriction a
      (p.diff.map.eval (ofRealRaw a)).realPart :=
  (p.derivativeContinuation (ofRealRaw a) (ofRealRaw_valid a ha)).realRestriction ha

def realDifferentiable (p : PolynomialFunction) : RealFunctionTheory.DifferentiableOn p.map.realRestriction where
  derivative := fun a => (p.diff.map.eval (ofRealRaw a)).realPart
  atPoint := fun a ha _ => p.realDerivativeContinuation a ha
  derivative_congr := fun ha hb _ _ he => realPart_equiv
    (p.diff.map.eval_congr (ofRealRaw_valid _ ha) (ofRealRaw_valid _ hb)
      (p.diff.entire _) (p.diff.entire _) (ofRealRaw_equiv_of_equiv ha hb he))

/-- Real coefficients may be any certified represented numbers, including irrational ones. -/
def ofRealCoefficients (cs : List Real) : PolynomialFunction :=
  ofCoefficients (List.map (fun (c : ComputableAnalysis.Real) => (⟨ofRealRaw c.preferred,ofRealRaw_valid c.preferred c.valid⟩ : Continuation.Point)) cs)

end PolynomialFunction
end ComputableAnalysis.FunctionTheory
