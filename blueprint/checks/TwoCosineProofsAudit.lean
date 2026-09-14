import ComputableAnalysis.CosineFTC
import ComputableAnalysis.CosineIntegralViaFTC
import Lean

open ComputableAnalysis
open ComputableAnalysis.IntegralIdentities
open ComputableAnalysis.GeometricSineDerivative

-- The two terms inhabit the identical proposition, with identical hypotheses.
example (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    CosineFTC.IntegralCosineStatement B a b ha hb hab :=
  CosineFTC.integral_cosPi_viaInequalities B a b ha hb hab

example (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    CosineFTC.IntegralCosineStatement B a b ha hb hab :=
  CosineFTC.integral_cosPi_viaFTC B a b ha hb hab

example (B : ArctanInverseBisection) :
    CosineFTC.IntegralCosineStatement B 0 (1/2)
      ⟨by decide +kernel, by decide +kernel⟩
      ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel) :=
  CosineFTC.integral_cosPi_viaFTC B _ _ _ _ _

example (B : ArctanInverseBisection) (a : Rat) (ha : OnHalf a) :
    CosineFTC.IntegralCosineStatement B a a ha ha (Rat.le_refl) :=
  CosineFTC.integral_cosPi_viaFTC B a a ha ha (Rat.le_refl)

example (B : ArctanInverseBisection) :
    (GeometricSineConcavity.sineDerivative B (1/4)
      ⟨by decide +kernel, by decide +kernel⟩).Valid :=
  GeometricSineConcavity.sineDerivative_valid B _ _

example (B : ArctanInverseBisection) :
    ExactConcaveOn (CosineFTC.sineFun B) 0 (1/2) :=
  GeometricSineConcavity.sine_concave B

-- Same algorithm: exporting either proof has not changed a single stage.
example (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) (n : Nat) :
    (CosineFTC.integral B a b ha hb hab).compute n =
      Integral.Dovetail.intersectMeshes
        (fun k q => QInterval.expand
          ((CosineFTC.fixedMesh B a b k).compute q) (CosineFTC.error a b k)) n n := rfl

namespace TwoCosineProofsAudit
open Lean Elab Command

/-- Inspect both theorem types and stored bodies, including opaque values. -/
partial def dependencies (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
      if seen.contains n then dependencies env rest seen
      else
        let seen := seen.insert n
        match env.find? n with
        | none => dependencies env rest seen
        | some ci =>
            let body := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
            dependencies env ((ci.type.getUsedConstants ++ body).toList ++ rest) seen

run_cmd do
  let env ← getEnv
  let direct := ``CosineFTC.integral_cosPi_viaInequalities
  let ftc := ``CosineFTC.integral_cosPi_viaFTC
  let some directInfo := env.find? direct | throwError "Direct proof not found"
  let some ftcInfo := env.find? ftc | throwError "FTC proof not found"
  liftTermElabM do
    unless ← Meta.isDefEq directInfo.type ftcInfo.type do
      throwError "The proofs do not have definitionally identical theorem types"
  logInfo "PASS: identical theorem types, including all parameters and hypotheses"
  let dd := dependencies env [direct]
  let fd := dependencies env [ftc]
  for forbidden in [ftc, ``ConcaveFTC.integral_equiv_endpoint,
      ``ConcaveFTC.finite_riemann_overlaps,
      ``GeometricSineConcavity.sine_concave,
      ``GeometricSineConcavity.primitive_concave,
      `ComputableAnalysis.GeometricSineDerivative.sinPi'_eq_pi_cosPi,
      `ComputableAnalysis.GeometricSineDerivative.sinPi_derivative_explicit,
      `sorryAx] do
    if dd.contains forbidden then throwError "Direct proof depends on forbidden declaration {forbidden}"
  for forbidden in [direct, ``CosineFTC.integral_cosPi_equiv_sinPi_endpoints,
      ``CosineFTC.fixedMesh_overlaps_endpoint,
      ``GeometricSineDirectBounds.positive_increment_error,
      ``GeometricSineFiniteBounds.finite_normalized_residual,
      `sorryAx] do
    if fd.contains forbidden then throwError "FTC proof depends on forbidden declaration {forbidden}"
  for required in [``ConcaveFTC.integral_equiv_endpoint,
      ``ConcaveFTC.local_residual_bound,
      ``GeometricSineConcavity.primitive_concave,
      ``GeometricSineConcavity.primitiveDerivativeData] do
    unless fd.contains required do throwError "FTC route does not use required declaration {required}"
  unless dd.contains ``GeometricSineDirectBounds.positive_increment_error do
    throwError "Direct route does not use its finite geometric inequality"
  logInfo "PASS: neither proof uses the other; direct route avoids the sine derivative and concave FTC"
  let derivDeps := dependencies env [``GeometricSineConcavity.sineDerivative_valid]
  for required in [``GeometricSineConcavity.sine_concave,
      ``ConcaveFTC.bracket_compatible, ``ConcaveFTC.derivative_valid] do
    unless derivDeps.contains required do throwError "Computed derivative omits {required}"
  logInfo "PASS: computed derivative validity uses concavity and cross-stage secant compatibility"
  for name in [direct, ftc, ``GeometricSineConcavity.sine_concave,
      ``GeometricSineConcavity.sineDerivative_valid,
      ``GeometricSineConcavity.sineDerivative_equiv_pi_cosine] do
    let axioms ← collectAxioms name
    if axioms.contains `sorryAx then throwError "Admitted proof in {name}"
    logInfo m!"AXIOMS {name}: {axioms.size}\n{axioms}"
  logInfo "PASS: all audited theorems are free of sorryAx"

end TwoCosineProofsAudit
