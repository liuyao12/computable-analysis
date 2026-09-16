import ComputableAnalysis.Cartwright
import MathlibComparison.Cartwright
import ComputableAnalysis.CosinePrimitive
import MathlibComparison.CosinePrimitive
import Lean

/-! Complete-type, dependency, computational-boundary, and size audits.
Curated display declarations are not included in root costs merely because
we display them. Native and Mathlib routes share one arithmetic consumer. -/
namespace CartwrightExport
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Case where
  id : String
  roots : Array Name

def cases : Array Case := #[
  ⟨"laws", #[``ComputableAnalysis.CartwrightMoments.lawsViaFinite,
    ``ComputableAnalysis.CartwrightMoments.lawsViaFTC, ``MathlibComparison.Cartwright.lawsViaMathlib]⟩,
  ⟨"moments", #[``ComputableAnalysis.CartwrightMoments.evaluation_viaFinite,
    ``ComputableAnalysis.CartwrightMoments.evaluation_viaFTC, ``ComputableAnalysis.CartwrightMoments.evaluation_viaMathlib]⟩,
  ⟨"irrationality", #[``ComputableAnalysis.CartwrightMoments.piSquared_viaFinite,
    ``ComputableAnalysis.CartwrightMoments.piSquared_viaFTC, ``ComputableAnalysis.CartwrightMoments.piSquared_viaMathlib]⟩]

def cosineBaselines : Array Name := #[
  ``ComputableAnalysis.CosinePrimitive.viaInequalities,
  ``ComputableAnalysis.CosinePrimitive.viaFTC,
  ``ComputableAnalysis.CosinePrimitive.viaMathlib]

def arithmetic : Array Name := #[
  ``ComputableAnalysis.CartwrightArithmetic.denominator_cleared,
  ``ComputableAnalysis.CartwrightArithmetic.no_positive_small_sequence]

def selected : Array Name := #[
  ``ComputableAnalysis.CartwrightArithmetic.polynomialPair,
  ``ComputableAnalysis.CartwrightArithmetic.polynomialValue,
  ``ComputableAnalysis.CartwrightArithmetic.integerPair,
  ``ComputableAnalysis.CartwrightArithmetic.integerValue,
  ``ComputableAnalysis.CartwrightArithmetic.denominator_cleared,
  ``ComputableAnalysis.CartwrightArithmetic.factorial_tail_lower,
  ``ComputableAnalysis.CartwrightArithmetic.witnessIndex,
  ``ComputableAnalysis.CartwrightArithmetic.factorial_dominates,
  ``ComputableAnalysis.CartwrightArithmetic.integer_obstruction,
  ``ComputableAnalysis.CartwrightArithmetic.no_positive_small_sequence,
  ``ComputableAnalysis.CosinePrimitive.pi,
  ``ComputableAnalysis.CosinePrimitive.pi_compute,
  ``ComputableAnalysis.CartwrightMoments.frequency,
  ``ComputableAnalysis.CartwrightMoments.frequencySample,
  ``ComputableAnalysis.CartwrightMoments.frequencySample_bounds,
  ``ComputableAnalysis.ClockTrigonometry.c,
  ``ComputableAnalysis.ClockTrigonometry.s,
  ``ComputableAnalysis.ClockTrigonometry.cosine,
  ``ComputableAnalysis.ClockTrigonometry.sine,
  ``ComputableAnalysis.CartwrightMoments.weight,
  ``ComputableAnalysis.CartwrightMoments.sample,
  ``ComputableAnalysis.MonotoneAverage.left,
  ``ComputableAnalysis.MonotoneAverage.gap,
  ``ComputableAnalysis.MonotoneAverage.mesh_error,
  ``ComputableAnalysis.MonotoneSampleIntegral.Data,
  ``ComputableAnalysis.MonotoneSampleIntegral.centre,
  ``ComputableAnalysis.MonotoneSampleIntegral.raw,
  ``ComputableAnalysis.MonotoneSampleIntegral.valid,
  ``ComputableAnalysis.CartwrightMoments.data,
  ``ComputableAnalysis.CartwrightMoments.moment,
  ``ComputableAnalysis.CartwrightMoments.moment_valid,
  ``ComputableAnalysis.CartwrightMoments.moment_width,
  ``ComputableAnalysis.CartwrightMoments.sample_evaluation_error,
  ``ComputableAnalysis.CartwrightMoments.sample_decreases,
  ``ComputableAnalysis.CartwrightMoments.lowerBound,
  ``ComputableAnalysis.CartwrightMoments.momentSample_lower,
  ``ComputableAnalysis.CartwrightMoments.moment_positive,
  ``ComputableAnalysis.CartwrightMoments.moment_upper,
  ``ComputableAnalysis.FiniteSampleCalculus.Model,
  ``ComputableAnalysis.FiniteSampleCalculus.Model.local_error,
  ``ComputableAnalysis.FiniteSampleCalculus.Model.mul,
  ``ComputableAnalysis.FiniteSampleCalculus.finite_telescope,
  ``ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC,
  ``ComputableAnalysis.CartwrightMoments.sineModel,
  ``ComputableAnalysis.CartwrightMoments.cosineModel,
  ``ComputableAnalysis.CartwrightMoments.weightDerivative,
  ``ComputableAnalysis.CartwrightMoments.weightModel,
  ``ComputableAnalysis.CartwrightMoments.recurrencePrimitive,
  ``ComputableAnalysis.CartwrightMoments.recurrenceDerivative,
  ``ComputableAnalysis.CartwrightMoments.recurrenceModel,
  ``ComputableAnalysis.CartwrightMoments.recurrence_viaFTC,
  ``ComputableAnalysis.CartwrightMoments.first_viaFTC,
  ``ComputableAnalysis.CartwrightMoments.zero_viaFTC,
  ``ComputableAnalysis.FiniteSummationByParts.cellSum,
  ``ComputableAnalysis.FiniteSummationByParts.product_identity,
  ``ComputableAnalysis.FiniteSummationByParts.quadratic_accumulation,
  ``ComputableAnalysis.FiniteSummationByParts.finite_product_estimate,
  ``ComputableAnalysis.FiniteSummationByParts.two_products_close,
  ``ComputableAnalysis.CartwrightMoments.recurrence_viaFinite,
  ``ComputableAnalysis.CartwrightMoments.first_viaFinite,
  ``ComputableAnalysis.CartwrightMoments.zero_viaFinite,
  ``MathlibComparison.Cartwright.lambda,
  ``MathlibComparison.Cartwright.moment,
  ``MathlibComparison.Cartwright.moment_zero,
  ``MathlibComparison.Cartwright.moment_one,
  ``MathlibComparison.Cartwright.moment_recurrence,
  ``MathlibComparison.Cartwright.moment_represents,
  ``MathlibComparison.Cartwright.moment_samples_tendsto,
  ``MathlibComparison.RealDyadicAverages.rectangle_bounds,
  ``MathlibComparison.RealDyadicAverages.diagonal_tendsto,
  ``MathlibComparison.Cartwright.clock_cosine_represents,
  ``Complex.exp,
  ``Real.cos,
  ``Real.sin,
  ``Real.pi,
  ``Real.hasDerivAt_sin,
  ``Real.hasDerivAt_cos,
  ``intervalIntegral.integral_mono_on,
  ``intervalIntegral.integral_add_adjacent_intervals,
  ``intervalIntegral,
  ``MeasureTheory.integral,
  ``MeasureTheory.lintegral,
  ``intervalIntegral.integral_eq_sub_of_hasDerivAt,
  ``intervalIntegral.integral_mul_deriv_eq_deriv_mul,
  ``MathlibComparison.cosine_represents,
  ``MathlibComparison.piCircleArea_represents,
  ``ComputableAnalysis.RationalSampleLimits.Small,
  ``ComputableAnalysis.RationalSampleLimits.Close,
  ``ComputableAnalysis.CartwrightMoments.MomentLaws,
  ``ComputableAnalysis.CartwrightMoments.MomentLaws.zero,
  ``ComputableAnalysis.CartwrightMoments.MomentLaws.first,
  ``ComputableAnalysis.CartwrightMoments.MomentLaws.recurrence,
  ``ComputableAnalysis.RealRaw.Irrational,
  ``ComputableAnalysis.CartwrightMoments.EvaluationStatement,
  ``ComputableAnalysis.CartwrightMoments.scaledMoment,
  ``ComputableAnalysis.CartwrightMoments.polynomialEndpoint,
  ``ComputableAnalysis.CartwrightMoments.polynomialRawPair,
  ``ComputableAnalysis.CartwrightMoments.polynomialRawPair_mem,
  ``ComputableAnalysis.CartwrightMoments.recurrence_mesh_error,
  ``ComputableAnalysis.CartwrightMoments.first_mesh_error,
  ``ComputableAnalysis.CartwrightMoments.evaluation_close,
  ``ComputableAnalysis.CartwrightMoments.evaluation_of_laws,
  ``ComputableAnalysis.CartwrightMoments.integer_close,
  ``ComputableAnalysis.CartwrightMoments.integer_bounds,
  ``ComputableAnalysis.CartwrightMoments.frequency_not_rational_close,
  ``ComputableAnalysis.CartwrightMoments.PiSquaredStatement,
  ``ComputableAnalysis.CartwrightMoments.piSquared_of_laws]

def refs (ci : ConstantInfo) : Array Name := ci.type.getUsedConstants ++
  ((ci.value? true).map Expr.getUsedConstants).getD #[]

partial def closure (env : Environment) (todo : List Name)
    (definitionsOnly : Bool := false) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest definitionsOnly seen else
      let next := match env.find? n with
        | none => []
        | some ci => if definitionsOnly then
            match ci with
            | .defnInfo _ | .opaqueInfo _ => (((ci.value? true).map Expr.getUsedConstants).getD #[]).toList
            | _ => []
          else (refs ci).toList
      closure env (next ++ rest) definitionsOnly (seen.insert n)

def owner (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => ""

partial def size (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get).get? e then return n
  let n ← match e with
    | .app f a => return 1+(← size f)+(← size a)
    | .lam _ t b _ | .forallE _ t b _ => return 1+(← size t)+(← size b)
    | .letE _ t v b _ => return 1+(← size t)+(← size v)+(← size b)
    | .mdata _ b | .proj _ _ b => return 1+(← size b)
    | _ => pure 1
  modify (·.insert e n)
  return n

def sizes (e : Expr) : Nat × Nat :=
  let (n,m) := (size e).run {}
  (n,m.size)

run_cmd do
  let env ← getEnv
  let rootNames := cases.foldl (fun out c => out ++ c.roots) #[]
  let allSelected := selected ++ rootNames
  let mut reports : Array Json := #[]
  for c in cases do
    let base := (env.find? c.roots[0]!).get!
    for i in [:3] do
      let root := c.roots[i]!
      let ci := (env.find? root).get!
      liftTermElabM do
        unless ← Meta.isDefEq base.type ci.type do throwError "Different complete types: {c.id}, {root}"
      let deps := closure env [root]
      for j in [:3] do
        if i != j && deps.contains c.roots[j]! then throwError "Alternative proof reuse: {root}"
      for n in deps do
        let m := owner env n
        if i < 2 && m.startsWith "Mathlib" then throwError "Native proof reaches Mathlib: {root} -> {n}"
        if m.startsWith "ComputableAnalysis" && isNoncomputable env n then
          throwError "Native-owned noncomputable dependency: {root} -> {n}"
      let axs ← collectAxioms root
      if axs.contains `sorryAx then throwError "Admitted proof: {root}"
      if i == 0 then
        for bad in [``ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC,
            ``ComputableAnalysis.FiniteSampleCalculus.finite_telescope,
            ``ComputableAnalysis.CartwrightMoments.recurrenceModel,
            ``ComputableAnalysis.CartwrightMoments.lawsViaFTC] do
          if deps.contains bad then throwError "Finite route borrows FTC: {bad}"
      if i == 2 then
        for bad in [``ComputableAnalysis.CartwrightMoments.lawsViaFinite,
            ``ComputableAnalysis.CartwrightMoments.lawsViaFTC,
            ``ComputableAnalysis.CartwrightMoments.recurrence_viaFTC,
            ``ComputableAnalysis.CartwrightMoments.recurrence_viaFinite,
            ``ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC,
            `irrational_pi, `Real.pi_irrational, `irrational_pi_sq,
            `MathlibComparison.Cartwright.pi_squared_ne_rat] do
          if deps.contains bad then throwError "Mathlib route bypasses its intended calculus: {bad}"
      let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 100
      reports := reports.push <| Json.mkObj [("case",toJson c.id),("route",toJson (#["direct","ftc","mathlib"])[i]!),
        ("root",toJson root.toString),("type",toJson ty),("axioms",toJson (axs.map Name.toString))]
  let construction := closure env [``ComputableAnalysis.CartwrightMoments.moment] true
  for n in construction do
    if n.toString.startsWith "ComputableAnalysis.CartwrightArithmetic" ||
       n == ``ComputableAnalysis.CartwrightMoments.recurrence_viaFTC ||
       n == ``ComputableAnalysis.CartwrightMoments.evaluation_of_laws ||
       n == ``ComputableAnalysis.CartwrightMoments.piSquared_of_laws then
      throwError "Numerical construction borrows its evaluation: {n}"
  let validity := closure env [``ComputableAnalysis.CartwrightMoments.moment_valid,
    ``ComputableAnalysis.CartwrightMoments.moment_positive,``ComputableAnalysis.CartwrightMoments.moment_upper]
  for bad in [``ComputableAnalysis.CartwrightMoments.evaluation_of_laws,
      ``ComputableAnalysis.CartwrightMoments.recurrence_viaFTC,
      ``ComputableAnalysis.CartwrightMoments.recurrence_viaFinite,
      ``ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC] do
    if validity.contains bad then throwError "Moment validity or positivity borrows evaluation: {bad}"
  for n in closure env arithmetic.toList do
    if n == `Real || n == `ComputableAnalysis.RealRaw || (owner env n).startsWith "Mathlib" then
      throwError "Shared integer boundary reaches analysis: {n}"
  let all := closure env (allSelected ++ cosineBaselines ++ arithmetic).toList
  let mut nodeData : Array Json := #[]
  let mut declarations : Array Json := #[]
  for n in all do
    let some ci := env.find? n | throwError "Missing declaration {n}"
    let kind := match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive" | _ => "constant"
    let ts := sizes ci.type
    let bs := ((ci.value? true).map sizes).getD (0,0)
    let r ← findDeclarationRanges? n
    let range := match r with
      | none => Json.null
      | some r => Json.mkObj [("start",toJson r.range.pos.line),("end",toJson r.range.endPos.line)]
    nodeData := nodeData.push <| Json.mkObj [("id",toJson n.toString),("module",toJson (owner env n)),
      ("name",toJson ((privateToUserName? n).getD n).toString),("kind",toJson kind),
      ("typeRefs",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("bodyRefs",toJson ((((ci.value? true).map Expr.getUsedConstants).getD #[]).map Name.toString)),
      ("typeTree",toJson ts.1),("typeDag",toJson ts.2),("bodyTree",toJson bs.1),("bodyDag",toJson bs.2),("sourceRange",range)]
    if allSelected.contains n then
      let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 88
      let showBody := #[`ComputableAnalysis.CartwrightArithmetic.polynomialPair,
        `ComputableAnalysis.CartwrightArithmetic.integerPair,`ComputableAnalysis.CartwrightArithmetic.witnessIndex,
        `ComputableAnalysis.CartwrightMoments.frequency,`ComputableAnalysis.CartwrightMoments.frequencySample,
        `ComputableAnalysis.CartwrightMoments.weight,`ComputableAnalysis.CartwrightMoments.sample,
        `ComputableAnalysis.MonotoneAverage.left,`ComputableAnalysis.MonotoneSampleIntegral.centre,
        `ComputableAnalysis.MonotoneSampleIntegral.raw,`ComputableAnalysis.CartwrightMoments.moment,
        `ComputableAnalysis.CartwrightMoments.lowerBound,`ComputableAnalysis.CartwrightMoments.recurrencePrimitive,
        `ComputableAnalysis.CartwrightMoments.recurrenceDerivative,`ComputableAnalysis.FiniteSummationByParts.cellSum,
        `ComputableAnalysis.RationalSampleLimits.Small,`ComputableAnalysis.RationalSampleLimits.Close,
        `ComputableAnalysis.CartwrightMoments.EvaluationStatement,`ComputableAnalysis.RealRaw.Irrational,`ComputableAnalysis.CartwrightMoments.PiSquaredStatement,
        `ComputableAnalysis.CartwrightMoments.scaledMoment,`ComputableAnalysis.CartwrightMoments.polynomialEndpoint,
        `ComputableAnalysis.CartwrightMoments.polynomialRawPair,`ComputableAnalysis.CosinePrimitive.pi,
        `MathlibComparison.Cartwright.moment,`MathlibComparison.Cartwright.lambda].contains n
      let value ← if kind == "def" && showBody then
        match ci.value? true with
        | some v => liftTermElabM do return Json.str ((← Meta.ppExpr v).pretty 88)
        | none => pure Json.null
        else pure Json.null
      declarations := declarations.push <| Json.mkObj [("name",toJson n.toString),
        ("kind",toJson kind),("type",toJson ty),("value",value),("ownerModule",toJson (owner env n)),("sourceRange",range)]
  IO.FS.createDirAll "reports"
  IO.FS.writeFile "reports/cartwright-complete.json" ((Json.mkObj [
    ("leanVersion",toJson Lean.versionString),("roots",toJson reports),("nodes",toJson nodeData),
    ("declarations",toJson declarations),("cosineBaselines",toJson (cosineBaselines.map Name.toString)),
    ("arithmetic",toJson (arithmetic.map Name.toString)),
    ("checks",Json.mkObj [("sameCompleteTypes",toJson true),("noAlternativeReuse",toJson true),
      ("noSorryAx",toJson true),("nativeMathlibFree",toJson true),("noNativeNoncomputable",toJson true),
      ("finiteRouteDoesNotCallFTC",toJson true),("mathlibRouteIndependent",toJson true),
      ("numericalConstructionIndependent",toJson true),("validityAndPositivityIndependent",toJson true),
      ("integerBoundaryNoAnalysis",toJson true)])]).compress ++ "\n")
  logInfo m!"PASS: nine closed proof terms; all matched types, independent routes, computational and arithmetic boundaries; {nodeData.size} measured declarations"
end CartwrightExport

-- Small concrete executions validate compilation of the chosen numerical path.
#eval do
  for n in [0,1,2] do
    let box := (ComputableAnalysis.CartwrightMoments.moment n).compute 2
    unless box.lo ≤ box.hi do throw <| IO.userError "Unordered moment output"
  IO.println "PASS: compiled weighted-moment evaluations"
