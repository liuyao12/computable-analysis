import ComputableAnalysis.ExpProofs
import ComputableAnalysis.Logarithm
import Lean

/-! Documentation export and execution of existing native programs. No new
analytic theorem is asserted. The exact proof sources are fingerprinted by
the reader build; this is not a claimed Mathlib representation bridge. -/
namespace PracticalCoreExport
open Lean Elab Command ComputableAnalysis
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def selected : Array Name := #[
 ``RealRaw, ``RealRaw.Valid, ``RealRaw.Equiv,
 ``expPowerSeriesTerms, ``expPowerSeriesPartialAndTailBound, ``expPowerSeries,
 ``ExpProofs.expPowerSeries_valid, ``ExpProofs.expPowerSeriesRate,
 ``eCompoundInterestStage, ``eCompoundInterest,
 ``ExpProofs.eCompoundInterest_valid,
 ``ExpProofs.ePowerSeries_equiv_eEulerNested,
 ``ExpProofs.eEulerNested_equiv_eCompoundInterest,
 ``ExpProofs.ePowerSeries_equiv_eCompoundInterest,
 ``ExpProofs.uniformExpRaw, ``ExpProofs.uniformExpRaw_valid,
 ``ExpProofs.uniformExpRaw_equiv_expPowerSeries,
 ``ExpProofs.uniformExpOnUnit_hasDerivativeOnInterval,
 ``ExpProofs.uniformExpOnSymmetricUnit_solvesSelfDerivative,
 ``ExpProofs.uniformExpOnUnit_effectiveFTC,
 ``TwoStageCandidateDerivativeFTC.boundedIntegralRaw_equiv_endpointDifference,
 ``ExpProofs.uniformExpOnUnitStabilized,
 ``ExpProofs.uniformExpOnUnitStabilized_valid,
 ``ExpProofs.uniformExpOnUnitStabilizedIntegral_equiv_powerSeries_one_sub_one,
 ``Logarithm.logTwoKernel, ``Logarithm.logTwoDarbouxCompute,
 ``Logarithm.logTwoReciprocalIntegral, ``Logarithm.logTwoReciprocalIntegral_valid,
 ``Logarithm.logTwoLo, ``Logarithm.logTwoRightRiemann,
 ``Logarithm.logTwoCompute, ``Logarithm.logTwoSeries,
 ``Logarithm.logTwoSeries_valid, ``Logarithm.logTwo_width_eq,
 ``Logarithm.logTwoDarbouxCompute_width,
 ``Logarithm.logTwoLo_eq_logTwoRightRiemann,
 ``Logarithm.logTwoSeries_equiv_logTwoReciprocalIntegral,
 ``Logarithm.logTwoSquareMesh_substitution_identity,
 ``Logarithm.logTwoSquareMesh_sub_uniformLeftEndpoint_bounds,
 ``Logarithm.logTwoSquarePullback,
 ``Logarithm.logTwoSquarePullbackIntegral,
 ``Logarithm.logTwoSquarePullbackIntegral_valid,
 ``Logarithm.logTwoSquarePullbackIntegral_equiv_reciprocalIntegral]

def roots : Array Name := #[
 ``ExpProofs.ePowerSeries_equiv_eCompoundInterest,
 ``ExpProofs.uniformExpOnUnitStabilizedIntegral_equiv_powerSeries_one_sub_one,
 ``ExpProofs.uniformExpOnSymmetricUnit_solvesSelfDerivative,
 ``Logarithm.logTwoSeries_equiv_logTwoReciprocalIntegral,
 ``Logarithm.logTwoSquarePullbackIntegral_equiv_reciprocalIntegral]

def refs (ci : ConstantInfo) : Array Name := ci.type.getUsedConstants ++
  ((ci.value? true).map Expr.getUsedConstants).getD #[]
partial def closure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n::rest => if seen.contains n then closure env rest seen else
      let next := match env.find? n with | none => [] | some ci => (refs ci).toList
      closure env (next++rest) (seen.insert n)
def owner (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => ""
run_cmd do
 let env ← getEnv
 let mut audits : Array Json := #[]
 for root in roots do
  let axs ← collectAxioms root
  if axs.contains `sorryAx then throwError "Admitted dependency: {root}"
  let mut tags : Array String := #[]
  for n in closure env [root] do
   let m := owner env n
   if m.startsWith "Mathlib" then throwError "Unexpected Mathlib dependency: {n}"
   if m.startsWith "ComputableAnalysis" && isNoncomputable env n then
    tags := tags.push n.toString
  unless tags.isEmpty do throwError "Native noncomputable dependencies: {tags}"
  audits := audits.push <| Json.mkObj [("root",toJson root.toString),
    ("axioms",toJson (axs.map Name.toString)),("nativeNoncomputableTags",toJson tags)]
 let mut declarations : Array Json := #[]
 let mut nodes : Array Json := #[]
 for n in closure env selected.toList do
  let some ci := env.find? n | throwError "Missing {n}"
  let k := match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive" | _ => "constant"
  nodes := nodes.push <| Json.mkObj [("id",toJson n.toString),("kind",toJson k),
    ("module",toJson (owner env n)),("typeRefs",toJson (ci.type.getUsedConstants.map Name.toString)),
    ("bodyRefs",toJson ((((ci.value? true).map Expr.getUsedConstants).getD #[]).map Name.toString))]
  if selected.contains n then
   let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 90
   let v ← if k == "def" then
    match ci.value? true with
    | some e => liftTermElabM do return Json.str ((← Meta.ppExpr e).pretty 90)
    | none => pure Json.null
    else pure Json.null
   declarations := declarations.push <| Json.mkObj [("name",toJson n.toString),
     ("kind",toJson k),("type",toJson ty),("value",v),("ownerModule",toJson (owner env n))]
 IO.FS.writeFile "practical-core-declarations.json" ((Json.mkObj [
   ("leanVersion",toJson Lean.versionString),("declarations",toJson declarations),
   ("nodes",toJson nodes),("audits",toJson audits),
   ("checks",Json.mkObj [("noSorryAx",toJson true),("nativeMathlibFree",toJson true),
     ("noNativeNoncomputable",toJson true)])]).compress++"\n")
 logInfo m!"PASS: {declarations.size} existing declarations; {roots.size} closed result roots"

def rat (q : Rat) : String := s!"{q.num}/{q.den}"
def row (label : String) (stage : Nat) (X : RealRaw) : Json :=
 let I := X.compute stage
 Json.mkObj [("label",toJson label),("stage",toJson stage),
   ("lower",toJson (rat I.lo)),("upper",toJson (rat I.hi))]
#eval do
 let mut rows : Array Json := #[]
 for x in [(-1 : Rat), 1/10, 1] do
  for stage in [0,4,8] do
   rows := rows.push (row ("E("++rat x++")") stage (expPowerSeries x))
 for n in [7,31,127] do rows := rows.push (row "compound e" n eCompoundInterest)
 for n in [16,64,256] do rows := rows.push (row "alternating log 2" n Logarithm.logTwoSeries)
 for n in [4,6,8] do rows := rows.push (row "reciprocal integral" n Logarithm.logTwoReciprocalIntegral)
 for n in [4,6,8] do rows := rows.push (row "square substitution" n Logarithm.logTwoSquarePullbackIntegral)
 IO.FS.writeFile "practical-core-examples.json" ((Json.mkObj [
   ("execution",toJson "Compiled Lean definitions, exact rational output; no Python numerical evaluator."),
   ("rows",toJson rows)]).compress++"\n")
 IO.println s!"PASS: {rows.size} compiled evaluations"
end PracticalCoreExport
