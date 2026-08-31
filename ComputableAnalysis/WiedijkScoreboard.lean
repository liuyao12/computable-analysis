import ComputableAnalysis.Basic

/-!
# Wiedijk's list: project scope

This module is an index, not a second theorem library.  Proofs live in their
subject modules and the blueprint links directly to them.

An item belongs here only when its mathematical content concerns an infinite
process, a computable real/complex function, or a calculus/analysis theorem.
Routine finite algebra, combinatorics, and elementary geometry are delegated
to Lean or imported directly when needed.
-/

namespace ComputableAnalysis

inductive WiedijkStatus where
  /-- The project has a theorem at its intended computable scope. -/
  | checked
  /-- A finite or certificate-level core exists, but a substantive bridge remains. -/
  | frontier
deriving Repr, DecidableEq

structure WiedijkEntry where
  number : Nat
  name : String
  status : WiedijkStatus
  projectTarget : String
deriving Repr, DecidableEq

/-! The canonical 16-item subset of Freek Wiedijk's benchmark for this
project.  `checked` means checked at the explicitly stated computable target,
not that the unrestricted classical formulation has been imported. -/
def wiedijkAnalysisEntries : List WiedijkEntry := [
  ⟨1, "Irrationality of sqrt 2", .checked,
    "irrationality for the project's computable square-root real"⟩,
  ⟨2, "Fundamental theorem of algebra", .frontier,
    "finite complex root isolation and certified deflation"⟩,
  ⟨9, "Area of a circle", .checked,
    "valid rational area subdivision and agreement of pi computations"⟩,
  ⟨14, "Euler's Basel sum", .frontier,
    "effective partial sums, tails, and geometric-pi identification"⟩,
  ⟨15, "Fundamental theorem of integral calculus", .checked,
    "effective derivative bounds imply a stabilized endpoint-difference integral"⟩,
  ⟨17, "de Moivre's formula", .checked,
    "finite rational-complex rotations and certified powers"⟩,
  ⟨21, "Green's theorem", .frontier,
    "finite polygonal/rectangle identity followed by an effective refinement"⟩,
  ⟨26, "Leibniz series for pi", .checked,
    "alternating rational series with an explicit tail and pi equivalence"⟩,
  ⟨34, "Divergence of the harmonic series", .checked,
    "a computable threshold for every requested rational height"⟩,
  ⟨35, "Taylor's theorem", .checked,
    "finite Taylor identity with an explicit computable remainder bound"⟩,
  ⟨64, "L'Hopital's rule", .frontier,
    "effective quotient/remainder certificate without a completed-real limit"⟩,
  ⟨66, "Sum of a geometric series", .checked,
    "finite prefix identity and explicit shrinking tail"⟩,
  ⟨75, "Mean value theorem", .checked,
    "finite derivative/average enclosure; no attained intermediate point required"⟩,
  ⟨76, "Fourier series", .frontier,
    "finite transforms plus effective tails and reconstruction certificates"⟩,
  ⟨79, "Intermediate value theorem", .checked,
    "branch-local bisection/inverse search for represented targets"⟩,
  ⟨90, "Stirling's formula", .frontier,
    "computable asymptotic ratio with a requested-precision certificate"⟩
]

theorem wiedijkAnalysisEntries_count : wiedijkAnalysisEntries.length = 16 := by
  native_decide

def wiedijkAnalysisNumbers : List Nat :=
  wiedijkAnalysisEntries.map WiedijkEntry.number

theorem wiedijkAnalysisNumbers_distinct :
    wiedijkAnalysisNumbers.Pairwise (fun a b => a ≠ b) := by
  native_decide

end ComputableAnalysis
