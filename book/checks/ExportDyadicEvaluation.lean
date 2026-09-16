import ComputableAnalysis.DyadicCosinePrimitive
import Lean

/-! Proof and numerical-dependency audit for the dyadic evaluation alternative.
The existing three-proof benchmark roots are unchanged. -/
namespace DyadicEvaluationAudit
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def selected : Array Name := #[
  ``ComputableAnalysis.ClockTrigonometry.cosine,
  ``ComputableAnalysis.ClockTrigonometry.cosine_addition,
  ``ComputableAnalysis.ClockTrigonometry.sine_addition,
  ``ComputableAnalysis.ClockTrigonometry.cosine_half_square,
  ``ComputableAnalysis.ClockTrigonometry.sine_half_square,
  ``ComputableAnalysis.ClockTrigonometry.cosine_nonnegative,
  ``ComputableAnalysis.ClockTrigonometry.cosine_endpoint,
  ``ComputableAnalysis.ClockTrigonometry.sine_endpoint,
  ``ComputableAnalysis.HalfAngleRadicals.rootBox,
  ``ComputableAnalysis.HalfAngleRadicals.halfStep,
  ``ComputableAnalysis.HalfAngleRadicals.path,
  ``ComputableAnalysis.DyadicTrigonometry.cosine,
  ``ComputableAnalysis.DyadicTrigonometry.powerCosine,
  ``ComputableAnalysis.DyadicTrigonometry.powerCompute,
  ``ComputableAnalysis.DyadicTrigonometry.powers_valid,
  ``ComputableAnalysis.DyadicTrigonometry.powers_equiv,
  ``ComputableAnalysis.DyadicCosinePrimitive.gridPoint,
  ``ComputableAnalysis.DyadicCosinePrimitive.dyadic_values,
  ``ComputableAnalysis.ClosedCosineIntegral.quarterIntegral_equiv_reciprocalPi,
  ``ComputableAnalysis.DyadicCosineIntegral.fixedMesh,
  ``ComputableAnalysis.DyadicCosineIntegral.fixedMesh_equiv,
  ``ComputableAnalysis.DyadicCosineIntegral.integral,
  ``ComputableAnalysis.DyadicCosineIntegral.integral_valid,
  ``ComputableAnalysis.DyadicCosineIntegral.integral_equiv_reciprocalPi,
  ``ComputableAnalysis.DyadicCosinePrimitive.product,
  ``ComputableAnalysis.DyadicCosinePrimitive.Statement,
  ``ComputableAnalysis.DyadicCosinePrimitive.product_valid,
  ``ComputableAnalysis.DyadicCosinePrimitive.product_eq_one]

def refs (ci : ConstantInfo) : Array Name := ci.type.getUsedConstants ++
  ((ci.value? true).map Expr.getUsedConstants).getD #[]

partial def closure (env : Environment) (pending : List Name)
    (definitionsOnly : Bool := false) (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest definitionsOnly seen else
      let more := match env.find? n with
        | none => []
        | some ci => if definitionsOnly then
            match ci with
            | .defnInfo _ | .opaqueInfo _ =>
              (((ci.value? true).map Expr.getUsedConstants).getD #[]).toList
            | _ => []
          else (refs ci).toList
      closure env (more ++ rest) definitionsOnly (seen.insert n)

def owner (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => ""

run_cmd do
  let env ← getEnv
  let roots := [``ComputableAnalysis.DyadicCosinePrimitive.product_eq_one,
    ``ComputableAnalysis.DyadicCosinePrimitive.product_valid,
    ``ComputableAnalysis.DyadicCosinePrimitive.dyadic_values]
  let mut audits : Array Json := #[]
  for root in roots do
    let deps := closure env [root]
    for dep in deps do
      let m := owner env dep
      if m.startsWith "Mathlib" then throwError "Unexpected Mathlib dependency {dep}"
      if m.startsWith "ComputableAnalysis" && isNoncomputable env dep then
        throwError "Native noncomputable dependency {dep}"
    let axioms ← collectAxioms root
    if axioms.contains `sorryAx then throwError "Admitted proof in {root}"
    audits := audits.push <| Json.mkObj [("root",toJson root.toString),
      ("axioms",toJson (axioms.map Name.toString))]
  let bridge := closure env [``ComputableAnalysis.DyadicCosinePrimitive.dyadic_values]
  for forbidden in [
    `ComputableAnalysis.CosineFTC.fixedMesh_overlaps_endpoint,
    `ComputableAnalysis.CosineFTC.integral_cosPi_viaFTC,
    `ComputableAnalysis.CosineFTC.integral_cosPi_viaInequalities,
    `ComputableAnalysis.ConcaveFTC.integral_equiv_endpoint,
    `ComputableAnalysis.CosinePrimitive.viaFTC,
    `ComputableAnalysis.CosinePrimitive.viaInequalities,
    `ComputableAnalysis.CosinePrimitive.viaMathlib] do
    if bridge.contains forbidden then throwError "Value bridge borrows integral theorem {forbidden}"
  let executable := closure env [``ComputableAnalysis.DyadicCosineIntegral.integral] true
  for forbidden in [
    ``ComputableAnalysis.piCircleArea,
    ``ComputableAnalysis.CosinePrimitive.pi,
    ``ComputableAnalysis.ArctanGeometry.arctanGeom,
    ``ComputableAnalysis.ArctanGeometry.arctanIntegralRectangleCompute,
    ``ComputableAnalysis.ClosedArctanInverse.raw,
    ``ComputableAnalysis.ClosedArctanInverse.provider,
    ``ComputableAnalysis.CosineFTC.endpoint,
    `ComputableAnalysis.HalfAngleRadicals.anchor] do
    if executable.contains forbidden then throwError "Radical numerical definitions reach {forbidden}"
  logInfo "PASS: radical integral numerical definitions do not call pi/arctan/inverse; identity bridge does not borrow the integral theorem"
  let all := closure env (selected.toList ++ [``ComputableAnalysis.CosinePrimitive.pi,
    ``ComputableAnalysis.CosinePrimitive.C,``ComputableAnalysis.Integral.Dovetail.raw])
  let mut nodes : Array Json := #[]
  let mut declarations : Array Json := #[]
  for n in all do
    let some ci := env.find? n | throwError "Missing declaration {n}"
    let k := match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "constant"
    nodes := nodes.push <| Json.mkObj [
      ("id",toJson n.toString),("kind",toJson k), ("module",toJson (owner env n)),
      ("typeRefs",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("bodyRefs",toJson ((((ci.value? true).map Expr.getUsedConstants).getD #[]).map Name.toString))]
    if selected.contains n then
      let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 88
      let value ← if k == "def" then
        match ci.value? true with
        | some v => liftTermElabM do return Json.str ((← Meta.ppExpr v).pretty 88)
        | none => pure Json.null
        else pure Json.null
      declarations := declarations.push <| Json.mkObj [
        ("name",toJson n.toString),("kind",toJson k),("type",toJson ty),
        ("value",value),("ownerModule",toJson (owner env n))]
  IO.FS.createDirAll "comparison/reports"
  IO.FS.writeFile "comparison/reports/dyadic-evaluation.json" ((Json.mkObj [
    ("leanVersion",toJson Lean.versionString),("audits",toJson audits),
    ("declarations",toJson declarations),("nodes",toJson nodes),
    ("checks",Json.mkObj [("noSorryAx",toJson true),("noMathlib",toJson true),
      ("noNativeNoncomputable",toJson true),("bridgeIndependentOfIntegral",toJson true),
      ("radicalDefinitionsPiAndArctanFree",toJson true)])]).compress ++ "\n")
  logInfo m!"Exported {declarations.size} exact declaration cards and {nodes.size} reference nodes"
end DyadicEvaluationAudit
