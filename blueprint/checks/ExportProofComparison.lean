import ComputableAnalysis.CosineFTC
import ComputableAnalysis.CosineIntegralViaFTC
import Lean

/-! Measurement tool, not part of the mathematical foundation.
Edges are references in stored declaration types and bodies (including opaque
bodies); imported-but-unused declarations are not dependencies. Counts do not
unfold referenced constants. Expr nodes include implicit arguments and types.
-/
namespace ProofComparisonExport
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def roots : Array Name := #[
  ``ComputableAnalysis.CosineFTC.integral_cosPi_viaInequalities,
  ``ComputableAnalysis.CosineFTC.integral_cosPi_viaFTC]

def supplements : Array Name := #[
  ``ComputableAnalysis.GeometricSineConcavity.sine_concave,
  ``ComputableAnalysis.GeometricSineConcavity.sineDerivative_valid,
  ``ComputableAnalysis.GeometricSineConcavity.sineDerivative_equiv_pi_cosine]

/-- Exact tree size with multiplicity, calculated using memoized subtrees.
The memo size separately counts structurally distinct Expr nodes. -/
partial def treeSize (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get).get? e then return n
  let n ← match e with
    | .app f a => return 1 + (← treeSize f) + (← treeSize a)
    | .lam _ t b _ | .forallE _ t b _ => return 1 + (← treeSize t) + (← treeSize b)
    | .letE _ t v b _ => return 1 + (← treeSize t) + (← treeSize v) + (← treeSize b)
    | .mdata _ b | .proj _ _ b => return 1 + (← treeSize b)
    | _ => pure 1
  modify (·.insert e n)
  return n

def sizes (e : Expr) : Nat × Nat :=
  let (n, memo) := (treeSize e).run {}
  (n, memo.size)

def references (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants).getD #[]

partial def closure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen
    else
      let next := match env.find? n with
        | none => []
        | some ci => (references ci).toList
      closure env (next ++ rest) (seen.insert n)

def kind (ci : ConstantInfo) : String := match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

def strings (xs : Array Name) : Json := toJson (xs.map Name.toString)

def moduleName (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => ""

/-- Synchronous kernel inference/checking of a stored proof, followed by a
kernel definitional-equality check against its claimed type. Dependencies
are loaded, not recursively rechecked. A distinct inert metadata tag per
trial prevents the measurement call from being loop-invariant. One warmup
is discarded. This measures neither tactic elaboration nor import time. -/
def benchmark (n : Name) (trials : Nat := 11) : CoreM (Array Nat) := do
  let .thmInfo th ← getConstInfo n | throwError "Not a theorem: {n}"
  let env ← getEnv
  let mut times := #[]
  for i in [:trials+1] do
    let value := Expr.mdata (KVMap.empty.setNat `measurementTrial i) th.value
    let t0 ← IO.monoNanosNow
    let inferred ← match Kernel.check env {} value with
      | .ok ty => pure ty
      | .error _ => throwError "Kernel recheck failed: {n}"
    match Kernel.isDefEq env {} inferred th.type with
      | .ok true => pure ()
      | _ => throwError "Kernel type comparison failed: {n}"
    let t1 ← IO.monoNanosNow
    if i > 0 then times := times.push (t1-t0)
  return times

run_cmd do
  let env ← getEnv
  let direct := closure env [roots[0]!]
  let ftc := closure env [roots[1]!]
  let all := closure env (roots ++ supplements).toList
  let some di := env.find? roots[0]! | throwError "Missing direct proof"
  let some fi := env.find? roots[1]! | throwError "Missing FTC proof"
  liftTermElabM do
    unless ← Meta.isDefEq di.type fi.type do throwError "Theorem types differ"
  if direct.contains roots[1]! || ftc.contains roots[0]! then
    throwError "Proofs depend on one another"
  if direct.contains `sorryAx || ftc.contains `sorryAx then throwError "Admitted proof"
  let mut nodes : Array Json := #[]
  for n in all do
    let some ci := env.find? n | throwError "Missing dependency {n}"
    let mod := moduleName env n
    let bodyRefs := ((ci.value? true).map Expr.getUsedConstants).getD #[]
    let typeRefs := ci.type.getUsedConstants
    let bodySizes := ((ci.value? true).map sizes).getD (0,0)
    let typeSizes := sizes ci.type
    let range ← findDeclarationRanges? n
    let rangeJson := match range with
      | none => Json.null
      | some r => Json.mkObj [
        ("start",toJson r.selectionRange.pos.line),
        ("end",toJson r.range.endPos.line)]
    nodes := nodes.push <| Json.mkObj [
      ("id",toJson n.toString),
      ("name",toJson ((privateToUserName? n).getD n).toString),
      ("module",toJson mod), ("kind",toJson (kind ci)),
      ("project",toJson (mod.startsWith "ComputableAnalysis")),
      ("direct",toJson (direct.contains n)), ("ftc",toJson (ftc.contains n)),
      ("bodyRefs",strings bodyRefs), ("typeRefs",strings typeRefs),
      ("bodyTreeNodes",toJson bodySizes.1), ("bodyDagNodes",toJson bodySizes.2),
      ("typeTreeNodes",toJson typeSizes.1), ("typeDagNodes",toJson typeSizes.2),
      ("sourceRange",rangeJson)]
  let mut bench : Array Json := #[]
  for n in roots do
    let times ← liftCoreM (benchmark n)
    let axs ← collectAxioms n
    bench := bench.push (Json.mkObj [("root",toJson n.toString),("nanoseconds",toJson times),
      ("axioms",strings axs)])
  let out := Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)), ("leanVersion",toJson Lean.versionString),
    ("roots",strings roots), ("supplements",strings supplements),
    ("sameType",toJson true), ("independentRoots",toJson true),
    ("noSorryAx",toJson true), ("nodes",toJson nodes),
    ("kernelRecheck",toJson bench)]
  let path := (← IO.getEnv "PROOF_COMPARISON_OUTPUT").getD "blueprint/proof-comparison/raw.json"
  IO.FS.writeFile path (out.compress ++ "\n")
  logInfo m!"Exported {nodes.size} actual declaration dependencies to {path}"
end ProofComparisonExport
