import Lean
import ComputableAnalysis.LeibnizTransmutation

open Lean Elab Command

private partial def closure (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  if (name.toString.splitOn "ComputableAnalysis.").length ≤ 1 then return
  modify (·.insert name)
  if let some info := env.find? name then
    for dep in info.type.getUsedConstants do closure env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do closure env dep

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then throwError "Unexpected Mathlib import: {mod}"
  let names := ((closure env ``ComputableAnalysis.pi_eq_leibniz_transmutation).run {}).2
  for required in [``ComputableAnalysis.RationalGeometry.trapezoid_transmutation,
      ``ComputableAnalysis.RationalGeometry.trapezoid_complement,
      ``ComputableAnalysis.LeibnizTransmutation.sector_cell_transmutation,
      ``ComputableAnalysis.LeibnizTransmutation.areaRaw_equiv_geom,
      ``ComputableAnalysis.Taylor.ArctanKernel.kernelPartial_exactCellOrder] do
    unless names.contains required do throwError "Historical route lost {required}"
  for forbidden in [``ComputableAnalysis.pi_eq_leibniz,
      ``ComputableAnalysis.leibnizRaw_equiv_geom,
      ``ComputableAnalysis.ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom,
      ``ComputableAnalysis.PiProofs.leibnizEqualsRectangleRawAtOne_finiteRiemannBridge] do
    if names.contains forbidden then throwError "Historical route bypassed transmutation through {forbidden}"
  for name in names.toArray do
    if name.toString == "ComputableAnalysis.pi_eq_leibniz_taylor" ||
        name.toString == "ComputableAnalysis.leibnizRaw_equiv_geom_taylor" then
      throwError "Historical route reused the Taylor equality: {name}"
  let geometry := ((closure env ``ComputableAnalysis.LeibnizTransmutation.areaRaw_equiv_geom).run {}).2
  if geometry.contains ``ComputableAnalysis.FinitePolynomial.SecantDerivativeBound ||
      geometry.contains ``ComputableAnalysis.Integral.ExactCellOrderPreservation then
    throwError "Geometric transmutation uses a calculus certificate"
  for root in [``ComputableAnalysis.pi_eq_leibniz_transmutation,
      ``ComputableAnalysis.LeibnizTransmutation.circle_transmutation,
      ``ComputableAnalysis.LeibnizTransmutation.transmuted_integral_series,
      ``ComputableAnalysis.LeibnizTransmutation.transmutation_error_bound,
      ``ComputableAnalysis.LeibnizTransmutation.transmutedIntegralRaw_valid,
      ``ComputableAnalysis.LeibnizTransmutation.geometric_polygon_transmutation,
      ``ComputableAnalysis.LeibnizTransmutation.transformed_curve_expansion] do
    let axioms ← collectAxioms root
    if axioms.contains ``sorryAx then throwError "Unfinished proof: {root}"
  liftIO <| IO.FS.createDirAll "tmp"
  liftIO <| IO.FS.writeFile "tmp/leibniz-transmutation-closure.txt"
    (String.intercalate "\n" ((names.toArray.qsort Name.lt).toList.map Name.toString) ++ "\n")
  logInfo m!"PASS: finite transmutation is an actual dependency; no previous Leibniz equality or old geometry bridge ({names.toArray.size} project declarations)."
  logInfo m!"PASS: no Mathlib module in the import closure."
  logInfo m!"PASS: geometric transmutation has no calculus certificates; power quadrature is shared with the Taylor infrastructure."

#check ComputableAnalysis.pi_eq_leibniz_transmutation
#check ComputableAnalysis.LeibnizTransmutation.circle_transmutation
#check ComputableAnalysis.LeibnizTransmutation.geometric_polygon_transmutation
#check ComputableAnalysis.LeibnizTransmutation.transmutation_error_bound
#check ComputableAnalysis.LeibnizTransmutation.transmuted_integral_series
#print axioms ComputableAnalysis.pi_eq_leibniz_transmutation
#print axioms ComputableAnalysis.LeibnizTransmutation.areaRaw_equiv_geom
#print axioms ComputableAnalysis.LeibnizTransmutation.transmutation_error_bound
#eval (List.range 5).map (fun n => (n,
  (ComputableAnalysis.LeibnizTransmutation.transmutedIntegralRaw.compute n).display,
  ComputableAnalysis.LeibnizTransmutation.transmutationError n))
