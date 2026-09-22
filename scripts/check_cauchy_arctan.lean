import Lean
import ComputableAnalysis.PDE.CauchyContour

open Lean Elab Command
open ComputableAnalysis.PDE.CauchyContour

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
  let roots := [``raw_equiv_twoPiI, ``raw_valid, ``density_exact,
    ``raw_encloses_taggedSum, ``raw_encloses_stageSum, ``stage_partition_covers,
    ``raw_height_geometric, ``scaledPullback_eq, ``point_avoids_pole,
    ``square_endpoints, ``twoPiI_not_equiv_zero]
  for root in roots do
    let axioms ← collectAxioms root
    if axioms.contains ``sorryAx then throwError "Unfinished proof: {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  let names : NameSet := ((do for root in roots do closure env root).run {}).2
  for required in [``density_exact, ``ComputableAnalysis.CauchyPi.rectangleRaw_equiv_piCircleArea,
      ``ComputableAnalysis.piCircleArea, ``taggedSum_enclosed] do
    unless names.contains required do throwError "Missing dependency: {required}"
  liftIO <| IO.FS.createDirAll "tmp"
  liftIO <| IO.FS.writeFile "tmp/cauchy-arctan-closure.txt"
    (String.intercalate "\n" ((names.toArray.qsort Name.lt).toList.map Name.toString) ++ "\n")
  logInfo m!"PASS: square-pole normalization, all-tag enclosure, geometry and explicit rate ({toString names.toArray.size} project declarations)."
  logInfo m!"PASS: no Mathlib module in the import closure; no sorryAx in audited theorems."

#check raw_equiv_twoPiI
#check raw_encloses_taggedSum
#check scaledPullback_eq
#check raw_height_geometric
#eval (List.range 4).map (fun n => (n, (raw.compute n).display))
