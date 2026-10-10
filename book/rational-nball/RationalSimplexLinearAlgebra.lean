import RationalProofAudit
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Rat.Defs

/-! Rational linear-algebra layer. The coefficient below is an algebraic
expression, not a definition or proof of axiomatic geometric volume.
The chapter derives its geometric meaning independently. -/
namespace ComputableAnalysis.RationalSimplex
open Matrix
abbrev Point (n : Nat) := Fin n → ℚ
abbrev Vertices (n : Nat) := Fin (n+1) → Point n

def edgeMatrix {n : Nat} (p : Vertices n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => p j.succ i - p 0 i

def translated {n : Nat} (p : Vertices n) (b : Point n) : Vertices n :=
  fun k i => p k i + b i

def transformed {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (p : Vertices n) : Vertices n := fun k => A.mulVec (p k)

def determinantCoefficient {n : Nat} (p : Vertices n) : ℚ :=
  (edgeMatrix p).det / (n.factorial : ℚ)

theorem edgeMatrix_translated {n : Nat} (p : Vertices n) (b : Point n) :
    edgeMatrix (translated p b) = edgeMatrix p := by
  ext i j; simp [edgeMatrix, translated]

theorem edgeMatrix_transformed {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (p : Vertices n) : edgeMatrix (transformed A p) = A * edgeMatrix p := by
  ext i j
  simp [edgeMatrix, transformed, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Finset.sum_sub_distrib, mul_sub]

theorem determinantCoefficient_translation {n : Nat}
    (p : Vertices n) (b : Point n) :
    determinantCoefficient (translated p b) = determinantCoefficient p := by
  simp only [determinantCoefficient, edgeMatrix_translated]

theorem determinantCoefficient_linear {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (p : Vertices n) :
    determinantCoefficient (transformed A p) =
      A.det * determinantCoefficient p := by
  simp only [determinantCoefficient, edgeMatrix_transformed, Matrix.det_mul]
  exact mul_div_assoc _ _ _

theorem determinantCoefficient_det_one {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (p : Vertices n) (hA : A.det = 1) :
    determinantCoefficient (transformed A p) = determinantCoefficient p := by
  rw [determinantCoefficient_linear, hA]; simp

#print axioms edgeMatrix_transformed
#print axioms determinantCoefficient_translation
#print axioms determinantCoefficient_linear
#print axioms determinantCoefficient_det_one
end ComputableAnalysis.RationalSimplex

open Lean

run_cmd do
  let env ← Lean.getEnv
  let deps := RationalProofAudit.audit env [`ComputableAnalysis.RationalSimplex.edgeMatrix_transformed, `ComputableAnalysis.RationalSimplex.determinantCoefficient_translation, `ComputableAnalysis.RationalSimplex.determinantCoefficient_linear, `ComputableAnalysis.RationalSimplex.determinantCoefficient_det_one]
  let forbidden := deps.filter fun n => let s := n.toString; s == "Real" || s.startsWith "Real." || s == "Complex" || s.startsWith "Complex." || s.startsWith "MeasureTheory." || s.startsWith "intervalIntegral"
  unless forbidden.isEmpty do throwError "Forbidden scalar/analysis dependencies: {forbidden}"
  logInfo m!"PASS: {deps.size} transitive declaration dependencies; no Mathlib real/complex scalars, measure or integration"
