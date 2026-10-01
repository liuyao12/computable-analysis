import Lean
import ComputableAnalysis.GammaInteger
import ComputableAnalysis.ZetaIntegerBounds
import ComputableAnalysis.ZeroFromEnclosures

open Lean Elab Command
open ComputableAnalysis

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then
      throwError "Unexpected Mathlib import: {mod}"
  for name in [``GammaInteger.gauss_eq_approx, ``GammaInteger.ratioProduct_bounds,
      ``GammaInteger.ratioProduct_gap, ``GammaInteger.approx_bounds,
      ``GammaInteger.raw_valid, ``GammaInteger.raw_equiv_factorial, ``GammaInteger.gauss_converges,
      ``ZetaReal.zeta_valid, ``ZetaReal.zeta_integer_equiv,
      ``ZetaReal.dirichlet_convergence, ``ZetaIntegerBounds.lower, ``ZetaIntegerBounds.upper,
      ``ZetaIntegerBounds.nonzero, ``ZetaIntegerBounds.antitone,
      ``ZetaIntegerBounds.bounds_of_equiv, ``ZetaIntegerBounds.real_zeta_bounds,
      ``FunctionTheory.ZeroIsolation.reflection_valid,
      ``FunctionTheory.ZeroIsolation.fixed_realPart, ``FunctionTheory.ZeroIsolation.reflected_zero,
      ``FunctionTheory.ZeroIsolation.unique_zero_on_line,
      ``FunctionTheory.ZeroFromEnclosures.equiv_zero_of_ranges,
      ``FunctionTheory.ZeroFromEnclosures.root_is_zero,
      ``FunctionTheory.ZeroFromEnclosures.root_on_line] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless [``propext, ``Quot.sound, ``Classical.choice].contains ax ||
          (ax.toString.startsWith "_private.ComputableAnalysis.Basic." &&
            (ax.toString.splitOn "._native.native_decide.").length > 1) do
        throwError "Unapproved axiom in {name}: {ax}"
    logInfo m!"AUDIT {name}: {axioms}"
  logInfo "PASS: integer zeta bounds, Gauss Gamma limits, exact reflected-zero location; no Mathlib or sorryAx."

-- Actual finite products and the cancelled evaluator, with rational errors.
#guard GammaInteger.gauss 0 1 == 1/2
#guard GammaInteger.gauss 2 1 == 1/12
#guard GammaInteger.approx 2 1 == 1/12
#guard GammaInteger.error 2 1 == 9
#guard ((GammaInteger.raw 2).compute 8).lo ≤ 2
#guard 2 ≤ ((GammaInteger.raw 2).compute 8).hi
#guard ((GammaInteger.raw 2).compute 8).width ≤ 2

-- No restriction to rational input names in the transport and root laws.
example (x : RealRaw) (hx : x.Valid)
    (he : x.Equiv (DirichletSeries.zetaNatRaw 3)) :
    (RealRaw.ofRat (1+1/(2 : Rat)^3)).Le x ∧ x.Le (RealRaw.ofRat 2) :=
  ZetaIntegerBounds.bounds_of_equiv 3 (by omega) x hx he

#guard (FunctionTheory.ZeroIsolation.reflection (ComplexRaw.ofQComplex ⟨2/5,14⟩)).compute 0
  == QBox.point ⟨3/5,14⟩
#guard (FunctionTheory.ZeroIsolation.reflection (ComplexRaw.ofQComplex ⟨1/2,14⟩)).compute 0
  == QBox.point ⟨1/2,14⟩
