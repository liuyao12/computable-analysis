import Lean
import EulerEvenZeta

open Lean Elab Command

/-- Walk actual elaborated expressions, not source imports or a curated diagram. -/
private partial def eulerDependencyClosure (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  if let some info := env.find? name then
    for dep in info.type.getUsedConstants do eulerDependencyClosure env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do eulerDependencyClosure env dep

set_option maxRecDepth 100000 in
run_cmd do
  let env ← getEnv
  let root := ``EulerBasel.hasSum_reciprocal_squares
  let deps := ((eulerDependencyClosure env root).run {}).2
  for required in [``EulerBasel.product_remainder, ``EulerBasel.product_quadratic_bound,
      ``EulerBasel.coefficient_error, ``Real.tendsto_euler_sin_prod, ``Real.sin_bound] do
    unless deps.contains required do throwError "Missing Euler proof step: {required}"
  for name in deps do
    if name.toString.contains "hasSum_zeta" || name.toString.contains "bernoulliFourier" ||
        name.toString.startsWith "ComputableAnalysis." then
      throwError "Unexpected evaluation shortcut: {name}"
  for mod in env.header.moduleNames do
    if mod == `Mathlib.NumberTheory.ZetaValues then
      throwError "Do not import the pre-existing zeta evaluations"
  let generalRoot := ``EulerEven.hasSum_even_zeta
  let generalDeps := ((eulerDependencyClosure env generalRoot).run {}).2
  for required in [``EulerEven.doubleTerm_summable, ``EulerEven.cotangent_generating,
      ``EulerEven.cotangent_series_identity, ``EulerEven.cotangentSeries_eq_bernoulli,
      ``tendsto_logDeriv_euler_sin_div, ``HasProdLocallyUniformlyOn_euler_sin_prod,
      ``Complex.tendsto_euler_sin_prod, ``bernoulliPowerSeries_mul_exp_sub_one] do
    unless generalDeps.contains required do throwError "Missing general Euler step: {required}"
  for name in generalDeps do
    if name.toString.contains "hasSum_zeta" || name.toString.toLower.contains "fourier" ||
        name.toString.startsWith "ComputableAnalysis." ||
        [``EulerBasel.total_eq, ``EulerBasel.hasSum_reciprocal_squares].contains name then
      throwError "Unexpected shortcut in the general Euler proof: {name}"
  let mut records : Array Json := #[]
  for name in [``EulerBasel.product_remainder, ``EulerBasel.sum_bounds,
      ``EulerBasel.product_quadratic_bound, ``EulerBasel.infinite_product_bound,
      ``EulerBasel.coefficient_error, ``EulerBasel.total_eq, root,
      ``EulerEven.doubleTerm_summable, ``EulerEven.cotangent_generating,
      ``EulerEven.cotangent_series_identity, ``EulerEven.cotangentSeries_eq_bernoulli,
      generalRoot, ``EulerEven.hasSum_four, ``EulerEven.hasSum_six, ``EulerEven.hasSum_eight] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    let some info := env.find? name | throwError "Missing theorem: {name}"
    let type ← liftTermElabM <| Meta.ppExpr info.type
    records := records.push <| Json.mkObj [
      ("name", toJson name.toString), ("type", toJson type.pretty),
      ("axioms", toJson (axioms.toList.map Name.toString))]
  let names := ((generalDeps.toArray.foldl (fun acc n => acc.insert n) deps).toArray.qsort Name.lt).toList.map Name.toString
  let generalNames := (generalDeps.toArray.qsort Name.lt).toList.map Name.toString
  let report := Json.mkObj [
    ("declarations", Json.arr records), ("dependencyCount", toJson names.length),
    ("generalDependencyCount", toJson generalNames.length),
    ("allPositiveEvenValuesProved", toJson true),
    ("mathlibRevision", toJson "51e6992efd06126df61a496bebf8f49482a4e129"),
    ("foundation", toJson "Mathlib real numbers; separate from the native interval foundation"),
    ("checks", Json.mkObj [("noSorryOrCustomAxioms", toJson true),
      ("finiteProductRemainderUsed", toJson true), ("sineProductUsed", toJson true),
      ("coefficientErrorUsed", toJson true), ("noZetaValueShortcut", toJson true),
      ("noNativeBaselShortcut", toJson true),
      ("generalSineProductUsed", toJson true), ("logarithmicDerivativeJustified", toJson true),
      ("doubleSeriesInterchangeJustified", toJson true), ("bernoulliGeneratingFunctionUsed", toJson true),
      ("generalProofDoesNotUseBaselEvaluation", toJson true), ("generalProofHasNoFourier", toJson true)])]
  liftIO <| IO.FS.createDirAll "euler-reports"
  liftIO <| IO.FS.writeFile "euler-reports/proofs.json" report.pretty
  liftIO <| IO.FS.writeFile "euler-reports/dependencies.txt" (String.intercalate "\n" names ++ "\n")
  liftIO <| IO.FS.writeFile "euler-reports/general-dependencies.txt" (String.intercalate "\n" generalNames ++ "\n")
  logInfo m!"PASS: Euler's sine-product proof, {names.length} elaborated dependencies; no previous Basel evaluation or unfinished proof."

#print axioms EulerBasel.hasSum_reciprocal_squares
#check EulerBasel.hasSum_reciprocal_squares

#check EulerEven.hasSum_even_zeta
#print axioms EulerEven.hasSum_even_zeta
