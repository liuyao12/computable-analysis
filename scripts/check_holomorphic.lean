import Lean
import ComputableAnalysis.HolomorphicExamples

open Lean Elab Command
open ComputableAnalysis FunctionTheory

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then
      throwError "Unexpected Mathlib import: {mod}"
  for name in [``Small.congr, ``HasDerivativeAt.congrPoint,
      ``HasDerivativeAt.congrDerivative, ``affine_remainder,
      ``affine_holomorphic, ``square_remainder, ``Small.mul, ``square_holomorphic] do
    let axioms ← collectAxioms name
    if axioms.contains ``sorryAx then throwError "Unfinished proof: {name}"
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
