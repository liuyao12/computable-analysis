import ComputableAnalysis.IntegralApplications
import MathlibComparison.IntegralApplications
import ComputableAnalysis.Cartwright
import MathlibComparison.Cartwright
import Lean

/-! Same-type paired proofs and cumulative cost accounting for two new families.
Display-only declarations never become cost roots merely by being displayed. -/
namespace IntegralPortfolioExport
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Case where
  id : String
  roots : Array Name

def cases : Array Case := #[
  ⟨"wallis-laws", #[``ComputableAnalysis.Wallis.lawsViaFTC, ``MathlibComparison.Wallis.lawsViaMathlib]⟩,
  ⟨"wallis-evaluation", #[``ComputableAnalysis.Wallis.evaluation_viaFTC, ``ComputableAnalysis.Wallis.evaluation_viaMathlib]⟩,
  ⟨"wallis-factorials", #[``ComputableAnalysis.Wallis.factorials_viaFTC, ``ComputableAnalysis.Wallis.factorials_viaMathlib]⟩,
  ⟨"wallis-product", #[``ComputableAnalysis.Wallis.productBounds_viaFTC, ``ComputableAnalysis.Wallis.productBounds_viaMathlib]⟩,
  ⟨"beta-laws", #[``ComputableAnalysis.BetaIntegral.lawsViaFTC, ``MathlibComparison.BetaIntegral.lawsViaMathlib]⟩,
  ⟨"beta-evaluation", #[``ComputableAnalysis.BetaIntegral.evaluation_viaFTC, ``ComputableAnalysis.BetaIntegral.evaluation_viaMathlib]⟩,
  ⟨"beta-factorials", #[``ComputableAnalysis.BetaIntegral.factorial_viaFTC, ``ComputableAnalysis.BetaIntegral.factorial_viaMathlib]⟩,
  ⟨"beta-normalization", #[``ComputableAnalysis.BetaIntegral.normalization_viaFTC, ``ComputableAnalysis.BetaIntegral.normalization_viaMathlib]⟩]

def priorBaselines : Array Name := #[
  ``ComputableAnalysis.CartwrightMoments.piSquared_viaFTC,
  ``ComputableAnalysis.CartwrightMoments.piSquared_viaMathlib]

def arithmetic : Array Name := #[
  ``ComputableAnalysis.Wallis.coefficient_even,
  ``ComputableAnalysis.Wallis.coefficient_odd,
  ``ComputableAnalysis.Wallis.product_step,
  ``ComputableAnalysis.Wallis.upper_ratio,
  ``ComputableAnalysis.BetaIntegral.factorial_value,
  ``ComputableAnalysis.BetaIntegral.normalizer_pos]

def selected : Array Name := #[
  ``ComputableAnalysis.RealRaw,
  ``ComputableAnalysis.QInterval,
  ``ComputableAnalysis.RealRaw.Valid,
  ``ComputableAnalysis.CosinePrimitive.pi,
  ``ComputableAnalysis.CartwrightMoments.frequency,
  ``ComputableAnalysis.ClockTrigonometry.cosine,
  ``ComputableAnalysis.ClockTrigonometry.c,
  ``ComputableAnalysis.MonotoneAverage.left,
  ``ComputableAnalysis.MonotoneSampleIntegral.raw,
  ``ComputableAnalysis.MonotoneSampleIntegral.valid,
  ``ComputableAnalysis.FiniteSampleCalculus.Model,
  ``ComputableAnalysis.FiniteSampleCalculus.Model.local_error,
  ``ComputableAnalysis.FiniteSampleCalculus.Model.mul,
  ``ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC,
  ``ComputableAnalysis.UnitPowerCalculus.modelPower,
  ``ComputableAnalysis.CartwrightMoments.sineModel,
  ``ComputableAnalysis.CartwrightMoments.cosineModel,
  ``ComputableAnalysis.Wallis.sample,
  ``ComputableAnalysis.Wallis.sample_unit,
  ``ComputableAnalysis.Wallis.sample_decreases,
  ``ComputableAnalysis.Wallis.sample_error,
  ``ComputableAnalysis.Wallis.data,
  ``ComputableAnalysis.Wallis.integral,
  ``ComputableAnalysis.Wallis.integral_valid,
  ``ComputableAnalysis.Wallis.integral_width,
  ``ComputableAnalysis.Wallis.mesh_error,
  ``ComputableAnalysis.Wallis.coefficient,
  ``ComputableAnalysis.Wallis.parityFactor,
  ``ComputableAnalysis.Wallis.Statement,
  ``ComputableAnalysis.Wallis.Laws,
  ``ComputableAnalysis.Wallis.primitive,
  ``ComputableAnalysis.Wallis.derivative,
  ``ComputableAnalysis.Wallis.primitiveModel,
  ``ComputableAnalysis.Wallis.recurrence_viaFTC,
  ``ComputableAnalysis.Wallis.evaluation_samples,
  ``ComputableAnalysis.Wallis.evaluation_of_laws,
  ``ComputableAnalysis.Wallis.coefficient_pos,
  ``ComputableAnalysis.Wallis.coefficient_even,
  ``ComputableAnalysis.Wallis.coefficient_odd,
  ``ComputableAnalysis.Wallis.product,
  ``ComputableAnalysis.Wallis.product_zero,
  ``ComputableAnalysis.Wallis.product_step,
  ``ComputableAnalysis.Wallis.upper_ratio,
  ``ComputableAnalysis.Wallis.FactorialStatement,
  ``ComputableAnalysis.Wallis.factorials_of_laws,
  ``ComputableAnalysis.Wallis.ProductBoundsStatement,
  ``ComputableAnalysis.Wallis.product_bounds_of_laws,
  ``ComputableAnalysis.Wallis.integralSample_power_decreases,
  ``ComputableAnalysis.RationalLipschitzIntegral.Data,
  ``ComputableAnalysis.RationalLipschitzIntegral.raw,
  ``ComputableAnalysis.RationalLipschitzIntegral.width,
  ``ComputableAnalysis.RationalLipschitzIntegral.valid,
  ``ComputableAnalysis.RationalLipschitzIntegral.refinement,
  ``ComputableAnalysis.BetaIntegral.integrand,
  ``ComputableAnalysis.BetaIntegral.integrand_unit,
  ``ComputableAnalysis.BetaIntegral.integrand_lipschitz,
  ``ComputableAnalysis.BetaIntegral.data,
  ``ComputableAnalysis.BetaIntegral.integral,
  ``ComputableAnalysis.BetaIntegral.integral_valid,
  ``ComputableAnalysis.BetaIntegral.integral_width,
  ``ComputableAnalysis.BetaIntegral.mesh_error,
  ``ComputableAnalysis.BetaIntegral.value,
  ``ComputableAnalysis.BetaIntegral.Statement,
  ``ComputableAnalysis.BetaIntegral.Laws,
  ``ComputableAnalysis.BetaIntegral.primitive,
  ``ComputableAnalysis.BetaIntegral.derivative,
  ``ComputableAnalysis.BetaIntegral.primitiveModel,
  ``ComputableAnalysis.BetaIntegral.step_viaFTC,
  ``ComputableAnalysis.BetaIntegral.evaluation_samples,
  ``ComputableAnalysis.BetaIntegral.evaluation_of_laws,
  ``ComputableAnalysis.BetaIntegral.factorial_value,
  ``ComputableAnalysis.BetaIntegral.FactorialStatement,
  ``ComputableAnalysis.BetaIntegral.factorial_of_laws,
  ``ComputableAnalysis.BetaIntegral.normalizer,
  ``ComputableAnalysis.BetaIntegral.normalizer_pos,
  ``ComputableAnalysis.BetaIntegral.normalizer_factorial,
  ``ComputableAnalysis.BetaIntegral.NormalizationStatement,
  ``ComputableAnalysis.BetaIntegral.normalization_of_laws,
  ``MathlibComparison.Wallis.moment,
  ``MathlibComparison.Wallis.samples_tendsto,
  ``MathlibComparison.Wallis.integral_samples_tendsto,
  ``MathlibComparison.Wallis.integral_represents,
  ``MathlibComparison.Wallis.change_variable,
  ``MathlibComparison.Wallis.moment_recurrence,
  ``MathlibComparison.BetaIntegral.integrand,
  ``MathlibComparison.BetaIntegral.moment,
  ``MathlibComparison.BetaIntegral.samples_tendsto,
  ``MathlibComparison.BetaIntegral.integral_represents,
  ``MathlibComparison.BetaIntegral.derivative,
  ``MathlibComparison.BetaIntegral.moment_base,
  ``MathlibComparison.BetaIntegral.moment_parts,
  ``MathlibComparison.BetaIntegral.moment_step,
  ``MathlibComparison.RealLipschitzAverages.rectangle_error,
  ``MathlibComparison.RealLipschitzAverages.samples_tendsto,
  ``MathlibComparison.RealDyadicAverages.diagonal_tendsto,
  ``MathlibComparison.Cartwright.cosine_samples_tendsto,
  ``Complex.exp,
  ``Real.cos,
  ``Real.sin,
  ``Real.pi,
  ``Real.hasDerivAt_cos,
  ``Real.hasDerivAt_sin,
  ``MeasureTheory.lintegral,
  ``MeasureTheory.integral,
  ``intervalIntegral,
  ``intervalIntegral.integral_mono_on,
  ``intervalIntegral.integral_add_adjacent_intervals,
  ``intervalIntegral.integral_eq_sub_of_hasDerivAt,
  ``intervalIntegral.integral_mul_deriv_eq_deriv_mul,
  ``integral_cos_pow_aux,
  ``integral_pow]

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
    for i in [:2] do
      let root := c.roots[i]!
      let ci := (env.find? root).get!
      liftTermElabM do
        unless ← Meta.isDefEq base.type ci.type do throwError "Different complete types: {c.id}, {root}"
      let deps := closure env [root]
      for j in [:2] do
        if i != j && deps.contains c.roots[j]! then throwError "Alternative proof reuse: {root}"
      for n in deps do
        let m := owner env n
        if i == 0 && m.startsWith "Mathlib" then throwError "Native proof reaches Mathlib: {root} -> {n}"
        if m.startsWith "ComputableAnalysis" && isNoncomputable env n then
          throwError "Native-owned noncomputable dependency: {root} -> {n}"
      let axs ← collectAxioms root
      if axs.contains `sorryAx then throwError "Admitted proof: {root}"
      if i == 1 then
        for bad in [``ComputableAnalysis.Wallis.lawsViaFTC,
            ``ComputableAnalysis.Wallis.recurrence_viaFTC,
            ``ComputableAnalysis.BetaIntegral.lawsViaFTC,
            ``ComputableAnalysis.BetaIntegral.step_viaFTC,
            ``ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC] do
          if deps.contains bad then throwError "Mathlib route borrows native calculus: {bad}"
      let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 100
      reports := reports.push <| Json.mkObj [("case",toJson c.id),("route",toJson (#["ftc","mathlib"])[i]!),
        ("root",toJson root.toString),("type",toJson ty),("axioms",toJson (axs.map Name.toString))]
  let prerequisiteRoots := [``ComputableAnalysis.Wallis.integral_valid,
    ``ComputableAnalysis.Wallis.integral_width,``ComputableAnalysis.BetaIntegral.integral_valid,
    ``ComputableAnalysis.BetaIntegral.integral_width,
    ``MathlibComparison.Wallis.integral_represents,``MathlibComparison.BetaIntegral.integral_represents]
  for root in prerequisiteRoots do
    let deps := closure env [root]
    for bad in [``ComputableAnalysis.Wallis.evaluation_of_laws,
        ``ComputableAnalysis.Wallis.recurrence_viaFTC,``MathlibComparison.Wallis.moment_recurrence,
        ``ComputableAnalysis.BetaIntegral.evaluation_samples,
  ``ComputableAnalysis.BetaIntegral.evaluation_of_laws,
        ``ComputableAnalysis.BetaIntegral.step_viaFTC,``MathlibComparison.BetaIntegral.moment_step,
        ``ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC] do
      if deps.contains bad then throwError "Validity or quadrature bridge borrows evaluation: {root} -> {bad}"
  for root in [``ComputableAnalysis.Wallis.integral,``ComputableAnalysis.BetaIntegral.integral] do
    let deps := closure env [root] true
    for bad in [``ComputableAnalysis.Wallis.coefficient,``ComputableAnalysis.BetaIntegral.value,
        ``ComputableAnalysis.Wallis.evaluation_of_laws,``ComputableAnalysis.BetaIntegral.evaluation_of_laws] do
      if deps.contains bad then throwError "Numerical construction reads its proposed value: {bad}"
  for n in closure env arithmetic.toList do
    if n == `Real || n == `ComputableAnalysis.RealRaw || (owner env n).startsWith "Mathlib" then
      throwError "Shared arithmetic reaches analysis: {n}"
  let all := closure env (allSelected ++ priorBaselines ++ arithmetic).toList
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
      let showBody := kind == "def" && !(n.toString.endsWith "Model") &&
        !(n.toString.startsWith "FiniteSampleCalculus") &&
        !(n == ``ComputableAnalysis.FiniteSampleCalculus.Model.mul)
      let value ← if showBody then
        match ci.value? true with
        | some v => liftTermElabM do return Json.str ((← Meta.ppExpr v).pretty 88)
        | none => pure Json.null
        else pure Json.null
      declarations := declarations.push <| Json.mkObj [("name",toJson n.toString),
        ("kind",toJson kind),("type",toJson ty),("value",value),("ownerModule",toJson (owner env n)),("sourceRange",range)]
  IO.FS.createDirAll "reports"
  IO.FS.writeFile "reports/integral-portfolio.json" ((Json.mkObj [
    ("leanVersion",toJson Lean.versionString),("roots",toJson reports),("nodes",toJson nodeData),
    ("declarations",toJson declarations),("priorBaselines",toJson (priorBaselines.map Name.toString)),
    ("arithmetic",toJson (arithmetic.map Name.toString)),
    ("checks",Json.mkObj [("sameCompleteTypes",toJson true),("noAlternativeReuse",toJson true),
      ("noSorryAx",toJson true),("nativeMathlibFree",toJson true),("noNativeNoncomputable",toJson true),
      ("mathlibRouteIndependent",toJson true),("numericalConstructionIndependent",toJson true),
      ("validityAndBridgesIndependent",toJson true),("arithmeticNoAnalysis",toJson true)])]).compress ++ "\n")
  logInfo m!"PASS: sixteen closed proof terms in two families; all matched types, independent routes and boundaries; {nodeData.size} measured declarations"
end IntegralPortfolioExport

#eval do
  for n in [0,2] do
    let box := (ComputableAnalysis.Wallis.integral n).compute 1
    unless box.lo ≤ box.hi do throw <| IO.userError "Unordered Wallis output"
  for (m,n) in [(0,0),(0,3),(1,1),(2,3)] do
    let box := (ComputableAnalysis.BetaIntegral.integral m n).compute 3
    let v := ComputableAnalysis.BetaIntegral.value m n
    unless box.lo ≤ v && v ≤ box.hi do throw <| IO.userError "Beta value not enclosed"
  IO.println "PASS: compiled cosine powers and beta quadratures"
