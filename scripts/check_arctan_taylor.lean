import Lean
import ComputableAnalysis.ArctanTaylorConvergence

open Lean Elab Command
open ComputableAnalysis ArctanTaylor
private partial def closure (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  if !name.toString.startsWith "ComputableAnalysis." then return
  modify (·.insert name)
  if let some info := env.find? name then
    for dep in info.type.getUsedConstants do closure env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do closure env dep

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then throwError "Unexpected Mathlib import: {mod}"
  let roots := [``term_lower_bound, ``not_cauchy, ``not_converges,
    ``partialSum_kernel, ``sample_in_box, ``series_converges,
    ``ConvergesTo.equiv, ``geometric_converges, ``convergence_iff]
  for root in roots do
    let axioms ← collectAxioms root
    if axioms.contains ``sorryAx then throwError "Unfinished proof: {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  let names : NameSet := ((do for root in roots do closure env root).run {}).2
  for required in [``bernoulli, ``partialSum, ``PiProofs.ArctanValidity.validAt,
      ``PiProofs.arctanEqualsGeom_finiteRiemannBridge_on_unit] do
    unless names.contains required do throwError "Missing dependency: {required}"
  liftIO <| IO.FS.createDirAll "tmp"
  liftIO <| IO.FS.writeFile "tmp/arctan-taylor-closure.txt"
    (String.intercalate "\n" ((names.toArray.qsort Name.lt).toList.map Name.toString) ++ "\n")
  logInfo m!"PASS: arctangent Taylor convergence and divergence ({toString names.toArray.size} project declarations)."
  logInfo m!"PASS: no Mathlib imports or sorryAx in arctangent audit."

example : ∃ v, ConvergesTo (partialSum 1) v := (convergence_iff 1).2 (by decide +kernel)
example : ∃ v, ConvergesTo (partialSum (-1)) v := (convergence_iff (-1)).2 (by decide +kernel)
example (v : RealRaw) : ¬ ConvergesTo (partialSum (101/100)) v :=
  not_converges (by decide +kernel) v
example (v : RealRaw) : ¬ ConvergesTo (partialSum (-101/100)) v :=
  not_converges (by decide +kernel) v
#eval (List.range 6).map (fun n => (n,partialSum (1/2) n,partialSum 1 n,partialSum (3/2) n))
