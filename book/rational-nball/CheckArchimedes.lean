import Lean
import FiniteBallShellRecurrence
import FiniteBallFormulaInduction

open Lean
run_cmd do
  let names := [
    `ComputableAnalysis.RationalBall.shellGap_mesh,
    `ComputableAnalysis.RationalBall.moment_power_error,
    `ComputableAnalysis.RationalBall.shells_recurrence_estimate,
    `ComputableAnalysis.RationalBall.equalPartition_last,
    `ComputableAnalysis.RationalBall.equalPartition_mesh,
    `ComputableAnalysis.RationalBall.uniform_shells_recurrence_estimate,
    `ComputableAnalysis.RationalBall.shell_disk_inner,
    `ComputableAnalysis.RationalBall.shell_disk_outer,
    `ComputableAnalysis.RationalBall.ballCoeff_even,
    `ComputableAnalysis.RationalBall.ballCoeff_odd,
    `ComputableAnalysis.RationalBall.ballFormula_even,
    `ComputableAnalysis.RationalBall.ballFormula_odd]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Untrusted axioms in {name}: {axioms}"
  logInfo m!"PASS: all {names.length} native Archimedes endpoints use trusted axioms only"
