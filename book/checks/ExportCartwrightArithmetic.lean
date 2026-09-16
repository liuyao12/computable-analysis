import ComputableAnalysis.CartwrightArithmetic
import Lean

/-! Audit the checked arithmetic component; no claim about the unfinished
cosine-moment or irrationality client follows from this exporter. -/
namespace CartwrightArithmeticAudit
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def selected : Array Name := #[
  ``ComputableAnalysis.CartwrightArithmetic.polynomialPair,
  ``ComputableAnalysis.CartwrightArithmetic.polynomialValue,
  ``ComputableAnalysis.CartwrightArithmetic.integerPair,
  ``ComputableAnalysis.CartwrightArithmetic.integerValue,
  ``ComputableAnalysis.CartwrightArithmetic.denominator_pair,
  ``ComputableAnalysis.CartwrightArithmetic.denominator_cleared,
  ``ComputableAnalysis.CartwrightArithmetic.factorial_tail_lower,
  ``ComputableAnalysis.CartwrightArithmetic.witnessIndex,
  ``ComputableAnalysis.CartwrightArithmetic.factorial_dominates,
  ``ComputableAnalysis.CartwrightArithmetic.integer_obstruction,
  ``ComputableAnalysis.CartwrightArithmetic.no_positive_small_sequence]

def roots : Array Name := #[
  ``ComputableAnalysis.CartwrightArithmetic.denominator_cleared,
  ``ComputableAnalysis.CartwrightArithmetic.no_positive_small_sequence]

def refs (ci : ConstantInfo) : Array Name := ci.type.getUsedConstants ++
  ((ci.value? true).map Expr.getUsedConstants).getD #[]

partial def closure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
      let next := match env.find? n with | none => [] | some ci => (refs ci).toList
      closure env (next ++ rest) (seen.insert n)

partial def size (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get).get? e then return n
  let n ← match e with
    | .app f a => return 1 + (← size f) + (← size a)
    | .lam _ t b _ | .forallE _ t b _ => return 1 + (← size t) + (← size b)
    | .letE _ t v b _ => return 1 + (← size t) + (← size v) + (← size b)
    | .mdata _ b | .proj _ _ b => return 1 + (← size b)
    | _ => pure 1
  modify (·.insert e n)
  return n

run_cmd do
  let env ← getEnv
  let used := closure env selected.toList
  let mut nodeData : Array Json := #[]
  let mut declarations : Array Json := #[]
  let mut audits : Array Json := #[]
  for root in roots do
    let axs ← collectAxioms root
    if axs.contains `sorryAx then throwError "Admitted arithmetic theorem {root}"
    audits := audits.push <| Json.mkObj [("root",toJson root.toString),
      ("axioms",toJson (axs.map Name.toString))]
  for n in used do
    let some ci := env.find? n | throwError "Missing reference {n}"
    let m := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.toString
      | none => ""
    if m.startsWith "Mathlib" then throwError "Arithmetic reaches Mathlib: {n}"
    if n == `Real || n == `ComputableAnalysis.RealRaw || n == `ComputableAnalysis.Real ||
       n == `ComputableAnalysis.piCircleArea ||
       n.toString.startsWith "ComputableAnalysis.Integral." ||
       n.toString.startsWith "ComputableAnalysis.FTC." ||
       n.toString.startsWith "ComputableAnalysis.ConcaveFTC." ||
       n.toString.startsWith "ComputableAnalysis.CosinePrimitive." ||
       n.toString.startsWith "ComputableAnalysis.ClockTrigonometry." then
      throwError "Arithmetic crossed the intended boundary: {n}"
    if m.startsWith "ComputableAnalysis" && isNoncomputable env n then
      throwError "Noncomputable arithmetic dependency {n}"
    let (bt,bmemo) := (size ((ci.value? true).getD (.sort .zero))).run {}
    let (tt,tmemo) := (size ci.type).run {}
    let range ← findDeclarationRanges? n
    let lines := match range with
      | none => Json.null
      | some r => Json.mkObj [("start",toJson r.range.pos.line),("end",toJson r.range.endPos.line)]
    let kind := match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "constant"
    nodeData := nodeData.push <| Json.mkObj [("id",toJson n.toString),("module",toJson m),
      ("kind",toJson kind),("typeRefs",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("bodyRefs",toJson ((((ci.value? true).map Expr.getUsedConstants).getD #[]).map Name.toString)),
      ("bodyTree",toJson (if (ci.value? true).isSome then bt else 0)),
      ("bodyDag",toJson (if (ci.value? true).isSome then bmemo.size else 0)),
      ("typeTree",toJson tt),("typeDag",toJson tmemo.size),("sourceRange",lines)]
    if selected.contains n then
      let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 88
      let value ← if kind == "def" then
        match ci.value? true with
        | some v => liftTermElabM do return Json.str ((← Meta.ppExpr v).pretty 88)
        | none => pure Json.null
        else pure Json.null
      declarations := declarations.push <| Json.mkObj [("name",toJson n.toString),
        ("kind",toJson kind),("type",toJson ty),("value",value),("ownerModule",toJson m)]
  IO.FS.createDirAll "comparison/reports"
  IO.FS.writeFile "comparison/reports/cartwright-arithmetic.json" ((Json.mkObj [
    ("leanVersion",toJson Lean.versionString),("nodes",toJson nodeData),
    ("declarations",toJson declarations),("audits",toJson audits),
    ("roots",toJson (roots.map Name.toString)),
    ("checks",Json.mkObj [("noSorryAx",toJson true),("noMathlib",toJson true),
      ("noNativeNoncomputable",toJson true),("noIntegralOrComputedRealDependency",toJson true)]),
    ("scope",toJson "Shared arithmetic only. Cosine moment construction, evaluation bridges, and irrationality application not proved here.")]).compress ++ "\n")
  logInfo m!"PASS: {declarations.size} arithmetic declarations; no integrals, computable reals, pi or Mathlib in stored dependencies"
end CartwrightArithmeticAudit

#eval do
  let xs := (List.range 5).map (fun n => ComputableAnalysis.CartwrightArithmetic.integerValue 1 1 n)
  unless xs == [1,1,2,9,61] do throw <| IO.userError "Integer recurrence mismatch"
  IO.println "PASS: integer recurrence smoke evaluation"
