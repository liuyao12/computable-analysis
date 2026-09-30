import Lean
import ComputableAnalysis.DerivativeContinuationPolynomial
import ComputableAnalysis.AlgebraicODE.FuchsContinuation

open Lean Elab Command
open ComputableAnalysis FunctionTheory

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then
      throwError "Unexpected Mathlib import: {mod}"
  for name in [``ContinuousAt.add, ``ContinuousAt.mul, ``ContinuousAt.comp, ``ContinuousAt.restrict,
      ``DerivativeAt.toEstimate, ``DerivativeAt.continuous, ``DerivativeAt.unique,
      ``DerivativeAt.congrPoint, ``DerivativeAt.congrDerivative, ``DerivativeAt.congrMap,
      ``derivativeAt_constant, ``derivativeAt_identity, ``DerivativeAt.add, ``DerivativeAt.mul,
      ``DerivativeAt.comp, ``DifferentiableOn.continuous, ``DifferentiableOn.holomorphic,
      ``DerivativeAt.realRestriction, ``PolynomialFunction.derivativeContinuation,
      ``PolynomialFunction.differentiable, ``PolynomialFunction.quotientHolomorphic,
      ``PolynomialFunction.quotientHolomorphic_derivative, ``PolynomialFunction.iteratedDerivativeContinuation,
      ``PolynomialFunction.continuation_derivative_equiv, ``PolynomialFunction.realDerivativeContinuation,
      ``PolynomialFunction.realDifferentiable, ``PolynomialFunction.ofRealCoefficients,
      ``RealFunctionTheory.Small.congr, ``RealFunctionTheory.Small.sub_self,
      ``RealFunctionTheory.ContinuousAt.congrPoint, ``RealFunctionTheory.ContinuousAt.congrEval,
      ``RealFunctionTheory.ContinuousOn.atPoint, ``RealFunctionTheory.ContinuousOn.ofAtPoint,
      ``RealFunctionTheory.ContinuousOn.congrEval, ``RealFunctionTheory.continuousOn_identity,
      ``RealFunctionTheory.continuousOn_constant,
      ``ContinuousAt.congrPoint, ``ContinuousAt.congrEval,
      ``ContinuousOn.atPoint, ``ContinuousOn.ofAtPoint, ``ContinuousOn.congrEval,
      ``continuousOn_identity, ``HasDerivativeAt.continuous, ``Small.congr, ``HasDerivativeAt.congrPoint,
      ``HasDerivativeAt.congrDerivative, ``affine_remainder,
      ``affine_holomorphic, ``square_remainder, ``Small.mul, ``square_holomorphic,
      ``small_valueBound, ``HasDerivativeAt.local_bound, ``Holomorphic.continuous,
      ``HasDerivativeAt.add, ``HasDerivativeAt.mul, ``HasDerivativeAt.comp,
      ``ContinuousOn.mul, ``ContinuousOn.comp,
      ``Holomorphic.add, ``Holomorphic.mul, ``Holomorphic.comp, ``Holomorphic.congr,
      ``constant_holomorphic, ``identity_holomorphic,
      ``PolynomialFunction.holomorphic, ``PolynomialFunction.hasDerivative,
      ``PolynomialFunction.derivative_equiv, ``PolynomialFunction.derivative_holomorphic,
      ``PolynomialFunction.iterated_hasDerivative, ``PolynomialFunction.ofCoefficients_eval,
      ``PolynomialFunction.ofCoefficients_congr, ``PolynomialFunction.secondOrder_equiv,
      ``PolynomialFunction.secondOrder_holomorphic] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless [``propext, ``Quot.sound, ``Classical.choice].contains ax ||
          (ax.toString.startsWith "_private.ComputableAnalysis.Basic." &&
            (ax.toString.splitOn "._native.native_decide.").length > 1) do
        throwError "Unapproved axiom in {name}: {ax}"
    logInfo m!"AUDIT {name}: {axioms}"
  logInfo "PASS: holomorphic witnesses, representation transport, no Mathlib imports or sorryAx."

-- Arbitrary represented coefficients and inputs: no rational restriction.
example (c b a : ComplexRaw) (hc : c.Valid) (hb : b.Valid) (ha : a.Valid) :
    HasDerivativeAt (affine c b hc hb) a c :=
  (affine_holomorphic c b hc hb).atPoint a ha True.intro

example (a : ComplexRaw) (ha : a.Valid) :
    HasDerivativeAt square a (ComplexRaw.add a a) :=
  square_holomorphic.atPoint a ha True.intro

example : ContinuousOn square.domain (fun a => ComplexRaw.add a a) :=
  square_holomorphic.continuousDerivative

#eval (square.eval (ComplexRaw.ofQComplex ⟨1,1⟩)).compute 0
#eval ((square_holomorphic.atPoint ComplexRaw.zero (ComplexRaw.ofQComplex_valid _) True.intro).delta ⟨1/100, by decide +kernel⟩).val

-- General partial maps: the chain rule keeps the inverse-image domain.
example (f g : FunctionTheory.Map) (hf : Holomorphic f) (hg : Holomorphic g)
    (a : ComplexRaw) (ha : a.Valid) (hfa : f.domain a) (hga : g.domain (f.eval a)) :
    HasDerivativeAt (g.comp f) a (ComplexRaw.mul (hg.derivative (f.eval a)) (hf.derivative a)) :=
  (hg.comp hf).atPoint a ha ⟨hfa,hga⟩

-- Every represented-coefficient polynomial, at every represented input.
example (cs : List Continuation.Point) (a : ComplexRaw) (ha : a.Valid) (n : Nat) :
    HasDerivativeAt ((PolynomialFunction.ofCoefficients cs).iteratedDiff n).map a
      (((PolynomialFunction.ofCoefficients cs).iteratedDiff (n+1)).map.eval a) :=
  (PolynomialFunction.ofCoefficients cs).iterated_hasDerivative n a ha

-- A nontrivial polynomial, checked through four actual derivatives.
def coefficient (r i : Rat) : Continuation.Point :=
  ⟨ComplexRaw.ofQComplex ⟨r,i⟩,ComplexRaw.ofQComplex_valid _⟩
def cubic := PolynomialFunction.ofCoefficients
  [coefficient 1 0,coefficient 0 0,coefficient (-2) 0,coefficient 1 0]
def input := ComplexRaw.ofQComplex ⟨1,1⟩
#guard (cubic.map.eval input).compute 0 == QBox.point ⟨-1,-2⟩
#guard (cubic.diff.map.eval input).compute 0 == QBox.point ⟨-4,2⟩
#guard (cubic.diff.diff.map.eval input).compute 0 == QBox.point ⟨2,6⟩
#guard ((cubic.iteratedDiff 3).map.eval input).compute 0 == QBox.point ⟨6,0⟩
#guard ((cubic.iteratedDiff 4).map.eval input).compute 0 == QBox.point ⟨0,0⟩

-- Outer square after a complex affine inner map exercises both chain factors.
def inner := affine (coefficient 2 1).val (coefficient 1 (-1)).val
  (coefficient 2 1).property (coefficient 1 (-1)).property
def inner_holo := affine_holomorphic (coefficient 2 1).val (coefficient 1 (-1)).val
  (coefficient 2 1).property (coefficient 1 (-1)).property
#guard ((square.comp inner).eval input).compute 0 == QBox.point ⟨0,8⟩
#guard ((square_holomorphic.comp inner_holo).derivative input).compute 0 == QBox.point ⟨4,12⟩
#guard 0 < (((square_holomorphic.comp inner_holo).atPoint input
  (ComplexRaw.ofQComplex_valid _) ⟨True.intro,True.intro⟩).delta ⟨1/100,by decide +kernel⟩).val

-- A derivative at just one point suffices for continuity at that point.
example (f : FunctionTheory.Map) (a d : ComplexRaw) (h : HasDerivativeAt f a d) :
    ContinuousAt f.domain f.eval a := h.continuous

-- Pointwise and whole-domain interfaces share the same exact-value law.
example (f : FunctionTheory.Map) (h : Holomorphic f)
    (a : ComplexRaw) (ha : a.Valid) (hDa : f.domain a) :
    ContinuousAt f.domain f.eval a := h.continuous.atPoint a ha hDa

-- Real identity and arbitrary represented constants: no rational-input restriction.
example (D : RealRaw → Prop) (a : RealRaw) (ha : a.Valid) (hDa : D a) :
    RealFunctionTheory.ContinuousAt D (fun x => x) a :=
  (RealFunctionTheory.continuousOn_identity D).atPoint a ha hDa

example (D : RealRaw → Prop) (c : RealRaw) (hc : c.Valid) :
    RealFunctionTheory.ContinuousOn D (fun _ => c) :=
  RealFunctionTheory.continuousOn_constant D c hc

-- An independent evaluator, with wider finite boxes, keeps continuity.
example : RealFunctionTheory.ContinuousOn (fun _ => True)
    (fun x => (x + x) - x) :=
  (RealFunctionTheory.continuousOn_identity (fun _ => True)).congrEval
    (fun _ hx _ => hx)
    (fun _ hx _ => RealRaw.sub_valid (RealRaw.add_valid hx hx) hx)
    (fun _ hx _ => RealRaw.equiv_symm (RealRaw.add_sub_cancel_left_equiv hx hx))

-- Input-name transport uses the map's genuine domain and evaluator invariance.
example (f : FunctionTheory.Map) (a b : ComplexRaw)
    (h : ContinuousAt f.domain f.eval a) (hb : b.Valid) (hab : a.Equiv b) :
    ContinuousAt f.domain f.eval b :=
  h.congrPoint hb hab f.domain_congr f.valid f.eval_congr

-- Quotient-extension derivatives at arbitrary represented inputs and coefficients.
example (cs : List Continuation.Point) (a : ComplexRaw) (ha : a.Valid) (n : Nat) :
    DerivativeAt ((PolynomialFunction.ofCoefficients cs).iteratedDiff n).map a
      (((PolynomialFunction.ofCoefficients cs).iteratedDiff (n+1)).map.eval a) :=
  (PolynomialFunction.ofCoefficients cs).iteratedDerivativeContinuation n a ha

example (cs : List ComputableAnalysis.Real) (a : RealRaw) (ha : a.Valid) :
    RealFunctionTheory.DerivativeAt (PolynomialFunction.ofRealCoefficients cs).map.realRestriction a
      ((PolynomialFunction.ofRealCoefficients cs).diff.map.eval (ComplexRaw.ofRealRaw a)).realPart :=
  (PolynomialFunction.ofRealCoefficients cs).realDerivativeContinuation a ha

-- The actual quotient computation has a value at its center; no equality test.
def cubicExtension := cubic.derivativeContinuation input (ComplexRaw.ofQComplex_valid _)
#guard (cubicExtension.quotient input).compute 0 == QBox.point ⟨-4,2⟩
#guard (cubicExtension.quotient ComplexRaw.zero).compute 0 == QBox.point ⟨-2,0⟩
#guard 0 < (cubicExtension.quotient_continuous.delta ⟨1/100,by decide +kernel⟩).val
example : (cubicExtension.quotient input).Equiv (cubic.diff.map.eval input) :=
  cubicExtension.value_at
example : (ComplexRaw.sub (cubic.map.eval ComplexRaw.zero) (cubic.map.eval input)).Equiv
    (ComplexRaw.mul (ComplexRaw.sub ComplexRaw.zero input) (cubicExtension.quotient ComplexRaw.zero)) :=
  cubicExtension.factorization ComplexRaw.zero (ComplexRaw.ofQComplex_valid _) (cubic.entire _)

-- Chain rule on explicit quotient computations, including the center.
def squarePolynomial : PolynomialFunction := .mul .input .input
def affinePolynomial : PolynomialFunction := .add
  (.mul (.constant (coefficient 2 1)) .input) (.constant (coefficient 1 (-1)))
def affineExtension := affinePolynomial.derivativeContinuation input (ComplexRaw.ofQComplex_valid _)
def chainExtension := affineExtension.comp (squarePolynomial.derivativeContinuation (affinePolynomial.map.eval input)
  (affinePolynomial.map.valid input (ComplexRaw.ofQComplex_valid _) (affinePolynomial.entire _)))
#guard (chainExtension.quotient input).compute 0 == QBox.point ⟨4,12⟩
#guard (chainExtension.quotient ComplexRaw.zero).compute 0 == QBox.point ⟨5,5⟩

-- New quotient evidence identifies the derivative used by the existing Fuchs client.
example (a : ComplexRaw) (ha : a.Valid) :
    (squarePolynomial.diff.map.eval a).Equiv (square_holomorphic.derivative a) := by
  let h := (squarePolynomial.derivativeContinuation a ha).congrMap
    (g := square) (fun _ => ⟨fun _ => True.intro,fun _ => ⟨True.intro,True.intro⟩⟩)
    (fun z hz _ => ComplexRaw.equiv_refl _ (ComplexRaw.mul_valid hz hz))
  exact h.toEstimate.unique square_holomorphic.openDomain
    (square_holomorphic.atPoint a ha True.intro)

example (f : FunctionTheory.Map) (a b d : ComplexRaw) (h : DerivativeAt f a d)
    (hb : b.Valid) (hab : a.Equiv b) : DerivativeAt f b d := h.congrPoint hb hab

-- Polynomial derivative continuity is derived from the next polynomial's differentiability.
example (p : PolynomialFunction) : Holomorphic p.map := p.quotientHolomorphic
example (p : PolynomialFunction) : ContinuousOn p.map.domain p.quotientHolomorphic.derivative :=
  p.quotientHolomorphic.continuousDerivative
