import Lean
import ComputableAnalysis.ComplexAnalysis

open Lean Elab Command
open ComputableAnalysis ComputableAnalysis.ComplexAnalysis

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
  let roots := [``Triangle.subdivide, ``Triangle.cauchy_bound, ``Triangle.cauchy,
    ``Triangle.first_order_bound, ``CauchyData.cauchy, ``CauchyData.contour_valid,
    ``ChainData.cauchy, ``ChainData.contour_valid, ``Square.triangulate,
    ``Square.residue, ``Square.residueContour_valid, ``Square.residue_independent,
    ``SquarePole.contour_equiv_twoPiI, ``SquarePole.contour_independent,
    ``SquarePole.contour_widths_bound, ``square_cauchy,
    ``quadratic_simple_pole_residue, ``quadratic_tags_agree, ``conjugation_nonzero]
  for root in roots do
    let axioms ← collectAxioms root
    if axioms.contains ``sorryAx then throwError "Unfinished proof: {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  let names : NameSet := ((do for root in roots do closure env root).run {}).2
  for required in [``Triangle.subdivide, ``Triangle.affine_zero,
      ``Triangle.model_bound, ``PDE.CauchyContour.raw_equiv_twoPiI,
      ``PDE.CauchyContour.taggedSum_enclosed, ``piCircleArea] do
    unless names.contains required do throwError "Missing dependency: {required}"
  liftIO <| IO.FS.createDirAll "tmp"
  liftIO <| IO.FS.writeFile "tmp/polygonal-cauchy-closure.txt"
    (String.intercalate "\n" ((names.toArray.qsort Name.lt).toList.map Name.toString) ++ "\n")
  logInfo m!"PASS: polygonal Cauchy cancellation and local square residues ({toString names.toArray.size} project declarations)."
  logInfo m!"PASS: no Mathlib module in the import closure; no sorryAx in audited theorems."

#eval (List.range 4).map (fun n => (n, unitTriangle.sum squareFunction n))
#eval (List.range 4).map (fun n => (n, unitTriangle.sum (fun z => ⟨z.re,-z.im⟩) n))
#eval (List.range 3).map (fun n => (n, (SquarePole.contour QComplex.zero 1 SquarePole.midpoints).compute n))
