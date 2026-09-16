import ComputableAnalysis.CartwrightDirect
import MathlibComparison.Cartwright
import Lean

/-! Full paired-statement audit and mathematical-map export. It inspects stored
types and bodies, not import lists; no production theorem imports this file. -/
namespace CartwrightAudit
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def moments : Array Name := #[
 ``ComputableAnalysis.CartwrightDirect.moment_viaInequalities,
 ``ComputableAnalysis.CartwrightTheorem.moment_viaFTC,
 ``MathlibComparison.Cartwright.moment_viaMathlib]
def irrationality : Array Name := #[
 ``ComputableAnalysis.CartwrightDirect.pi_squared_viaInequalities,
 ``ComputableAnalysis.CartwrightTheorem.pi_squared_viaFTC,
 ``MathlibComparison.Cartwright.pi_squared_viaMathlib]
def lawRoots : Array Name := #[
 ``ComputableAnalysis.CartwrightDirect.laws,
 ``ComputableAnalysis.CartwrightMomentRecurrence.viaFTC,
 ``MathlibComparison.Cartwright.laws]

def selected : Array Name := #[
 ``ComputableAnalysis.RealRaw.Valid,
 ``ComputableAnalysis.RealRaw.Equiv,
 ``ComputableAnalysis.RealRaw.Irrational,
 ``ComputableAnalysis.CosinePrimitive.pi,
 ``ComputableAnalysis.ClockTrigonometry.cosine,
 ``ComputableAnalysis.CartwrightClockBounds.frequency,
 ``ComputableAnalysis.CartwrightTheorem.lambda,
 ``ComputableAnalysis.CartwrightTheorem.frequency_equiv_lambda,
 ``ComputableAnalysis.CartwrightArithmetic.polynomialPair,
 ``ComputableAnalysis.CartwrightArithmetic.polynomialValue,
 ``ComputableAnalysis.CartwrightArithmetic.integerPair,
 ``ComputableAnalysis.CartwrightArithmetic.integerValue,
 ``ComputableAnalysis.CartwrightArithmetic.denominator_cleared,
 ``ComputableAnalysis.CartwrightArithmetic.witnessIndex,
 ``ComputableAnalysis.CartwrightArithmetic.factorial_tail_lower,
 ``ComputableAnalysis.CartwrightArithmetic.factorial_dominates,
 ``ComputableAnalysis.CartwrightArithmetic.integer_obstruction,
 ``ComputableAnalysis.Integral.nonincreasingDarbouxRange,
 ``ComputableAnalysis.Integral.nonincreasingDarbouxDyadicStage,
 ``ComputableAnalysis.Integral.endpointOrderedNonincreasingDarbouxDyadicStage_contains_of_stage_of_precision_mono,
 ``ComputableAnalysis.CartwrightMoments.weight,
 ``ComputableAnalysis.CartwrightMoments.value,
 ``ComputableAnalysis.CartwrightMoments.sampleStage,
 ``ComputableAnalysis.CartwrightMoments.integral,
 ``ComputableAnalysis.CartwrightMoments.integral_compute,
 ``ComputableAnalysis.CartwrightMoments.stage_width,
 ``ComputableAnalysis.CartwrightMoments.integral_valid,
 ``ComputableAnalysis.CartwrightMoments.integral_bounds,
 ``ComputableAnalysis.CartwrightMoments.positiveBound,
 ``ComputableAnalysis.CartwrightMoments.positiveBound_pos,
 ``ComputableAnalysis.CartwrightMoments.first_stage_positive,
 ``ComputableAnalysis.CartwrightMoments.sample,
 ``ComputableAnalysis.CartwrightMoments.sample_mem,
 ``ComputableAnalysis.CartwrightMoments.sample_positive,
 ``ComputableAnalysis.CartwrightClockBounds.sine_step_error,
 ``ComputableAnalysis.CartwrightClockBounds.cosine_step_error,
 ``ComputableAnalysis.FiniteFirstOrderCalculus.Data,
 ``ComputableAnalysis.FiniteFirstOrderCalculus.Data.error,
 ``ComputableAnalysis.FiniteFirstOrderCalculus.product,
 ``ComputableAnalysis.CartwrightMoments.weightData,
 ``ComputableAnalysis.CartwrightMoments.auxData,
 ``ComputableAnalysis.UniformGridFTC.Certificate,
 ``ComputableAnalysis.UniformGridFTC.Certificate.residual,
 ``ComputableAnalysis.UniformGridFTC.product,
 ``ComputableAnalysis.UniformGridFTC.finite_bound,
 ``ComputableAnalysis.UniformGridFTC.conclusion,
 ``ComputableAnalysis.CartwrightIntegrationByParts.sine_parts_viaFTC,
 ``ComputableAnalysis.CartwrightIntegrationByParts.cosine_parts_viaFTC,
 ``ComputableAnalysis.finiteIntegrationByParts_withVariation,
 ``ComputableAnalysis.CartwrightDirect.discrete_parts,
 ``ComputableAnalysis.CartwrightDirect.sine_parts,
 ``ComputableAnalysis.CartwrightDirect.cosine_parts,
 ``ComputableAnalysis.CartwrightMomentRecurrence.Laws,
 ``ComputableAnalysis.CartwrightMomentRecurrence.laws_of_parts,
 ``ComputableAnalysis.CartwrightEvaluation.polynomialPairRaw,
 ``ComputableAnalysis.CartwrightEvaluation.factor,
 ``ComputableAnalysis.CartwrightEvaluation.evaluated,
 ``ComputableAnalysis.CartwrightTheorem.momentLeft,
 ``ComputableAnalysis.CartwrightTheorem.momentRight,
 ``ComputableAnalysis.CartwrightTheorem.MomentStatement,
 ``ComputableAnalysis.CartwrightTheorem.moment_of_laws,
 ``ComputableAnalysis.CartwrightIrrationality.integer_bounds,
 ``ComputableAnalysis.CartwrightIrrationality.frequency_square_irrational,
 ``ComputableAnalysis.CartwrightTheorem.PiSquaredStatement,
 ``ComputableAnalysis.CartwrightTheorem.pi_squared_of_laws,
 ``MathlibComparison.CartwrightAnalytic.moment,
 ``MathlibComparison.CartwrightAnalytic.sine_parts,
 ``MathlibComparison.CartwrightAnalytic.cosine_parts,
 ``MathlibComparison.CartwrightAnalytic.base_zero,
 ``MathlibComparison.CartwrightAnalytic.base_one,
 ``MathlibComparison.CartwrightAnalytic.recurrence,
 ``MathlibComparison.CartwrightQuadrature.frequency_represents,
 ``MathlibComparison.CartwrightQuadrature.value_represents,
 ``MathlibComparison.CartwrightQuadrature.moment_represents,
 ``MathlibComparison.CartwrightQuadrature.sample_tendsto,
 ``intervalIntegral.integral_mul_deriv_eq_deriv_mul,
 ``intervalIntegral.integral_mono_on,
 ``intervalIntegral.integral_add_adjacent_intervals]

def refs (ci : ConstantInfo) : Array Name := ci.type.getUsedConstants ++
  ((ci.value? true).map Expr.getUsedConstants).getD #[]
partial def closure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n::rest => if seen.contains n then closure env rest seen else
    let next:=match env.find? n with | none=>[] | some ci=>(refs ci).toList
    closure env (next++rest) (seen.insert n)
partial def numericalClosure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n::rest => if seen.contains n then numericalClosure env rest seen else
    let next:=match env.find? n with
      | some (.defnInfo d)=>d.value.getUsedConstants.toList
      | some (.opaqueInfo d)=>d.value.getUsedConstants.toList
      | _=>[]
    numericalClosure env (next++rest) (seen.insert n)
def owner (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with | some i=>env.header.moduleNames[i.toNat]!.toString | none=>""
partial def size (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n:=(←get).get? e then return n
  let n ← match e with
    | .app f a => return 1+(←size f)+(←size a)
    | .lam _ t b _ | .forallE _ t b _ => return 1+(←size t)+(←size b)
    | .letE _ t v b _ => return 1+(←size t)+(←size v)+(←size b)
    | .mdata _ b | .proj _ _ b => return 1+(←size b)
    | _ => pure 1
  modify (·.insert e n)
  return n
def sizes (e : Expr) : Nat × Nat := let (n,m):=(size e).run {}; (n,m.size)
def kind (ci : ConstantInfo) : String := match ci with
  | .thmInfo _=>"theorem" | .defnInfo _=>"def" | .axiomInfo _=>"axiom"
  | .inductInfo _=>"inductive" | .opaqueInfo _=>"opaque" | _=>"constant"

run_cmd do
  let env ← getEnv
  let roots := moments++irrationality
  let mut rows : Array Json := #[]
  let deps := roots.map (fun n=>closure env [n])
  for group in [moments,irrationality] do
    let some first:=env.find? group[0]! | throwError "Missing first theorem"
    for root in group do
      let some ci:=env.find? root | throwError "Missing {root}"
      liftTermElabM do
        unless ←Meta.isDefEq first.type ci.type do throwError "Unequal complete statement: {root}"
  for i in [:6] do
    let root:=roots[i]!;let d:=deps[i]!
    for j in [:3] do
      if j != i%3 then
        for alt in [moments[j]!,irrationality[j]!,lawRoots[j]!] do
          if d.contains alt then throwError "Alternative reuse: {root} -> {alt}"
    let axs ←collectAxioms root
    if axs.contains `sorryAx then throwError "Admitted theorem {root}"
    if i%3<2 then
      for n in d do
        if (owner env n).startsWith "Mathlib" then throwError "Native Mathlib dependency {n}"
        if (owner env n).startsWith "ComputableAnalysis" && isNoncomputable env n then
          throwError "Native noncomputable dependency {n}"
    if i%3==0 then
      for n in [``ComputableAnalysis.UniformGridFTC.conclusion,
          ``ComputableAnalysis.UniformGridFTC.finite_bound,
          ``ComputableAnalysis.UniformGridFTC.product,
          ``ComputableAnalysis.CartwrightIntegrationByParts.sine_parts_viaFTC,
          ``ComputableAnalysis.CartwrightIntegrationByParts.cosine_parts_viaFTC] do
        if d.contains n then throwError "Direct route calls FTC {n}"
      unless d.contains ``ComputableAnalysis.finiteIntegrationByParts_withVariation do
        throwError "Direct route lacks its finite product identity"
    if i%3==1 then
      unless d.contains ``ComputableAnalysis.UniformGridFTC.conclusion do throwError "FTC missing"
    if i%3==2 then
      for n in [``ComputableAnalysis.UniformGridFTC.conclusion,
          ``ComputableAnalysis.CartwrightDirect.discrete_parts] do
        if d.contains n then throwError "Mathlib route borrows native middle {n}"
      for n in [``MathlibComparison.CartwrightQuadrature.moment_represents,
          ``intervalIntegral.integral_mul_deriv_eq_deriv_mul] do
        unless d.contains n do throwError "Mathlib route missing bridge or IBP {n}"
    let some ci:=env.find? root | throwError "Missing {root}"
    let ty ←liftTermElabM do return (←Meta.ppExpr ci.type).pretty 100
    rows:=rows.push <|Json.mkObj [("case",toJson (if i<3 then "moment" else "pi-squared")),
      ("route",toJson (["direct","ftc","mathlib"][i%3]!)),("root",toJson root.toString),
      ("type",toJson ty),("axioms",toJson (axs.map Name.toString))]
  for root in [``ComputableAnalysis.CartwrightMoments.integral_valid,
      ``ComputableAnalysis.CartwrightMoments.first_stage_positive,
      ``ComputableAnalysis.CartwrightMoments.integral_bounds] do
    for n in closure env [root] do
      let s:=n.toString
      if s.startsWith "ComputableAnalysis.CartwrightEvaluation" ||
          s.startsWith "ComputableAnalysis.CartwrightMomentRecurrence" ||
          s.startsWith "ComputableAnalysis.UniformGridFTC" ||
          (owner env n).startsWith "Mathlib" then
        throwError "Independent construction/bounds use their answer: {root} -> {n}"
  for n in numericalClosure env [``ComputableAnalysis.CartwrightMoments.integral] do
    let s:=n.toString
    if s.startsWith "ComputableAnalysis.CartwrightEvaluation" ||
        s.startsWith "ComputableAnalysis.CartwrightIrrationality" ||
        s.startsWith "ComputableAnalysis.CartwrightTheorem" then
      throwError "Numerical program calls its proposed answer {n}"
  for n in closure env [``ComputableAnalysis.CartwrightArithmetic.integer_obstruction,
      ``ComputableAnalysis.CartwrightArithmetic.denominator_cleared] do
    if n==``ComputableAnalysis.RealRaw || (owner env n).startsWith "Mathlib" then
      throwError "Arithmetic boundary crossed by {n}"
  for n in closure env [``MathlibComparison.CartwrightQuadrature.moment_represents] do
    if n==``MathlibComparison.CartwrightAnalytic.recurrence ||
       n==``MathlibComparison.CartwrightAnalytic.sine_parts ||
       n==``MathlibComparison.CartwrightAnalytic.cosine_parts then
      throwError "Quadrature bridge depends on evaluation {n}"
  logInfo "PASS: six closed proof terms, two identical statement families, independent analytic routes and arithmetic boundary"
  let display:=selected++roots++lawRoots
  let all:=closure env display.toList
  let mut nodes : Array Json:=#[]
  let mut declarations : Array Json:=#[]
  for name in all do
    let some ci:=env.find? name | throwError "Missing dependency {name}"
    let ts:=sizes ci.type;let bs:=((ci.value? true).map sizes).getD (0,0)
    let ranges ←findDeclarationRanges? name
    let range:=match ranges with | none=>Json.null | some r=>Json.mkObj [
      ("start",toJson r.range.pos.line),("end",toJson r.range.endPos.line)]
    nodes:=nodes.push <|Json.mkObj [("id",toJson name.toString),("module",toJson (owner env name)),
      ("kind",toJson (kind ci)),("typeRefs",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("bodyRefs",toJson ((((ci.value? true).map Expr.getUsedConstants).getD #[]).map Name.toString)),
      ("typeTree",toJson ts.1),("typeDag",toJson ts.2),("bodyTree",toJson bs.1),("bodyDag",toJson bs.2),
      ("sourceRange",range),("routes",toJson ((List.range 6).filter (fun i=>deps[i]!.contains name)))]
    if display.contains name then
      let ty ←liftTermElabM do return (←Meta.ppExpr ci.type).pretty 88
      let value ←if kind ci=="def" then
        match ci.value? true with
        | some v=>liftTermElabM do return Json.str ((←Meta.ppExpr v).pretty 88)
        | none=>pure Json.null
        else pure Json.null
      declarations:=declarations.push <|Json.mkObj [("name",toJson name.toString),
        ("kind",toJson (kind ci)),("type",toJson ty),("value",value),
        ("ownerModule",toJson (owner env name)),("sourceRange",range)]
  IO.FS.createDirAll "reports"
  IO.FS.writeFile "reports/cartwright-complete.json" ((Json.mkObj [
    ("schemaVersion",toJson (1:Nat)),("leanVersion",toJson Lean.versionString),
    ("roots",toJson rows),("nodes",toJson nodes),("declarations",toJson declarations),
    ("checks",Json.mkObj [("sameCompleteTypes",toJson true),("noSorryAx",toJson true),
      ("independentRoutes",toJson true),("nativeBoundary",toJson true),
      ("constructionIndependentOfEvaluation",toJson true),("arithmeticBoundary",toJson true),
      ("quadratureBridgeIndependent",toJson true),("directDoesNotUseFTC",toJson true)])]).compress++"\n")
  logInfo m!"Exported {nodes.size} dependencies and {declarations.size} mathematical cards"
end CartwrightAudit
