import Lean
import ComputableAnalysis.HolomorphicPolynomial

open Lean Elab Command
open ComputableAnalysis FunctionTheory

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then
      throwError "Unexpected Mathlib import: {mod}"
  for name in [``Small.congr, ``HasDerivativeAt.congrPoint,
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
