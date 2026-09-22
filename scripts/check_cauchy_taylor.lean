import Lean
import ComputableAnalysis.CauchyTaylorExamples

open Lean Elab Command
open ComputableAnalysis
open ComputableAnalysis.CauchyTaylor

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
  let roots := [``Disk.eq_series, ``Disk.series_valid, ``Disk.realPart_eq_series,
    ``Disk.imagPart_eq_series, ``Moments.coefficient_valid, ``Moments.partialSum_valid,
    ``Moments.partialSum_contains_sample, ``polynomialSample_eq_prefix,
    ``reciprocal_eq_series, ``reciprocal_coefficients, ``diagonal_point_eq_series]
  for root in roots do
    let axioms ← collectAxioms root
    if axioms.contains ``sorryAx then throwError "Unfinished proof: {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  let names : NameSet := ((do for root in roots do closure env root).run {}).2
  for required in [``kernel_remainder, ``kernel_remainder_disk,
      ``Representation.polynomial_encloses, ``Disk.coordinate_inverse,
      ``ComputableAnalysis.CertifiedComplexApproximation.equiv_anchor] do
    unless names.contains required do throwError "Missing dependency: {required}"
  liftIO <| IO.FS.createDirAll "tmp"
  liftIO <| IO.FS.writeFile "tmp/cauchy-taylor-closure.txt"
    (String.intercalate "\n" ((names.toArray.qsort Name.lt).toList.map Name.toString) ++ "\n")
  logInfo m!"PASS: exact Cauchy-series equality, valid coefficients, arbitrary rational disks ({names.toArray.size} project declarations)."
  logInfo "PASS: no Mathlib module in the import closure; no sorryAx in audited theorems."
  logInfo "SCOPE: Cauchy representation is a hypothesis; differentiability-to-Cauchy and derivative identification remain open."

#check Disk.eq_series
#check Disk.realPart_eq_series
#check Disk.imagPart_eq_series
#check reciprocal_eq_series
#check diagonal_point_eq_series

-- The disk boundary is excluded, and coordinate-diamond membership is not assumed.
example : ¬ InDisk ⟨1, 0⟩ (9/10) := by unfold InDisk; native_decide
example : QComplex.normBound ⟨3/5, 3/5⟩ > 1 := by native_decide
example : (unitDisk reciprocalRule).innerRatio ⟨3/5, 3/5⟩ = 43/50 := by native_decide
example : polynomialSample reciprocalRule ⟨1/2, 0⟩ 4 = ⟨15/8, 0⟩ := by native_decide
example : polynomialSample reciprocalRule ⟨0, 0⟩ 0 = QComplex.zero := by native_decide
