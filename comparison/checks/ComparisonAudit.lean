import MathlibComparison
import Lean

open ComputableAnalysis MathlibComparison

example (X : RealRaw) (hX : X.Valid) : ∃! r : ℝ, Represents X r :=
  existsUnique_represents X hX

example (X Y : RealRaw) (hX : X.Valid) (hY : Y.Valid) :
    X.Equiv Y ↔ denote X hX = denote Y hY := equiv_iff_denote_eq hX hY

example : Represents (ArctanGeometry.arctanIntegralRectangleRaw 1) (Real.pi/4) := by
  simpa only [Real.arctan_one,Rat.cast_one] using
    (arctan_rectangle_represents (u := 1) (by decide +kernel))

example (B : IntegralIdentities.ArctanInverseBisection) :
    Represents (SinPiIntegral.sinPiRawOfArctan B 0 ⟨by decide +kernel,by decide +kernel⟩) 0 := by
  simpa only [Rat.cast_zero,mul_zero,Real.sin_zero] using
    (sine_represents B 0 ⟨by decide +kernel,by decide +kernel⟩)

example (B : IntegralIdentities.ArctanInverseBisection) :
    Represents (SinPiIntegral.cosPiRawOfArctan B (1/2) ⟨by decide +kernel,by decide +kernel⟩) 0 := by
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,mul_one_div,Real.cos_pi_div_two] using
    (cosine_represents B (1/2) ⟨by decide +kernel,by decide +kernel⟩)

namespace ComparisonAudit
open Lean Elab Command

partial def closure (env : Environment) (pending : List Name) (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
      if seen.contains n then closure env rest seen
      else
        let extra := match env.find? n with
          | none => []
          | some ci => (ci.type.getUsedConstants ++
              ((ci.value? true).map Expr.getUsedConstants).getD #[]).toList
        closure env (extra ++ rest) (seen.insert n)

run_cmd do
  let env ← getEnv
  let roots := [``existsUnique_represents,``equiv_iff_denote_eq,``le_iff_denote_le,
    ``denote_add,``denote_sub,``denote_mul,``denote_scale,
    ``arctan_rectangle_represents,``arctan_geom_represents,
    ``piCircleArea_represents,``reciprocalPi_represents,
    ``slope_arctan,``sine_represents,``cosine_represents,``mathlib_cosine_primitive]
  for n in roots do
    let axs ← collectAxioms n
    if axs.contains `sorryAx then throwError "Unproved dependency in {n}"
    logInfo m!"AXIOMS {n}: {axs.size}\n{axs}"
  logInfo "PASS: 15 comparison results have no sorryAx dependencies"
  for n in [``sine_represents,``cosine_represents,``slope_arctan] do
    let deps := closure env [n]
    for bad in [
        `ComputableAnalysis.CosineFTC.integral_cosPi_viaFTC,
        `ComputableAnalysis.CosineFTC.integral_cosPi_viaInequalities,
        `ComputableAnalysis.CosineFTC.integral_cosPi_equiv_sinPi_endpoints,
        `ComputableAnalysis.GeometricSineDerivative.sinPi_derivative_explicit,
        `ComputableAnalysis.GeometricSineDerivative.sinPi'_eq_pi_cosPi] do
      if deps.contains bad then throwError "Bridge {n} depends on forbidden native conclusion {bad}"
  logInfo "PASS: sine/cosine bridges do not borrow the native derivative or integral conclusions"
  for n in [``RealRaw.equiv_trans,
      ``ArctanGeometry.arctanIntegralRectangleRaw_valid,
      ``SinPiIntegral.sinPiRawOfArctan_valid,``SinPiIntegral.cosPiRawOfArctan_valid] do
    for dep in closure env [n] do
      if let some i := env.getModuleIdxFor? dep then
        let mod := (env.header.moduleNames[i.toNat]!).toString
        if mod.startsWith "Mathlib." || mod == "Mathlib" || mod.startsWith "MathlibComparison" then
          throwError "Native theorem {n} references comparison/library dependency {dep} in {mod}"
  logInfo "PASS: audited native theorem bodies remain Mathlib-independent in the combined environment"

end ComparisonAudit
