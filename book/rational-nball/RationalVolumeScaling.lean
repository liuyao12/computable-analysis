import RationalSimplexLinearAlgebra

/-! Exact rational dilation of oriented determinant volumes. This is an
algebraic theorem for finite simplex presentations. Its connection to a
triangulation-independent axiomatic polytope volume is a separate obligation.
No sphere or curved-region volume is defined here. -/
namespace ComputableAnalysis.RationalSimplex

/-- Expand every coordinate of every vertex by the same rational factor. -/
def dilated {n : Nat} (k : ℚ) (p : Vertices n) : Vertices n :=
  fun v i => k * p v i

theorem edgeMatrix_dilated {n : Nat} (k : ℚ) (p : Vertices n) :
    edgeMatrix (dilated k p) = k • edgeMatrix p := by
  ext i j
  simp [edgeMatrix, dilated, mul_sub]

/-- The sign is retained: no absolute determinant enters the formula. -/
theorem determinantCoefficient_dilation {n : Nat} (k : ℚ) (p : Vertices n) :
    determinantCoefficient (dilated k p) = k^n * determinantCoefficient p := by
  simp only [determinantCoefficient, edgeMatrix_dilated, Matrix.det_smul,
    Fintype.card_fin]
  exact mul_div_assoc _ _ _

/-- A finite oriented simplex presentation has an exactly computable rational
coefficient. This name does not assert geometric triangulation independence. -/
def presentationCoefficient {n : Nat} (pieces : List (Vertices n)) : ℚ :=
  (pieces.map determinantCoefficient).sum

theorem presentationCoefficient_dilation {n : Nat} (k : ℚ)
    (pieces : List (Vertices n)) :
    presentationCoefficient (pieces.map (dilated k)) =
      k^n * presentationCoefficient pieces := by
  induction pieces with
  | nil => simp [presentationCoefficient]
  | cons p ps ih =>
    simpa only [presentationCoefficient, List.map_cons, List.sum_cons,
      determinantCoefficient_dilation, mul_add] using congrArg
      (fun q => k^n * determinantCoefficient p + q) ih

#print axioms determinantCoefficient_dilation
#print axioms presentationCoefficient_dilation
end ComputableAnalysis.RationalSimplex

open Lean
run_cmd do
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env [
    `ComputableAnalysis.RationalSimplex.determinantCoefficient_dilation,
    `ComputableAnalysis.RationalSimplex.presentationCoefficient_dilation]
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  logInfo m!"PASS: {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
